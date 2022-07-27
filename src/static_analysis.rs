use std::{borrow::Borrow, collections::HashSet, fmt::Display};

use gc::{Finalize, Trace};
use lsp_types::{Diagnostic, DiagnosticSeverity};
use rnix::TextRange;

use crate::{
    error::{EvalError, Located, ValueError},
    eval::{Expr, ExprSource, StringPartSource},
    scope::Scope,
    utils,
};

#[derive(Debug, Trace, Finalize, Clone, PartialEq, Eq)]
pub enum Warning {
    /// The binding with this name is not used
    UnusedBinding(String),
}

impl Display for Warning {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Warning::UnusedBinding(s) => write!(f, "binding {} is unused", s),
        }
    }
}

/// Either a warning or an error to be displayed to the user, without location information
#[derive(Debug, Trace, Finalize, Clone, PartialEq, Eq)]
pub enum AlarmKind {
    /// Something is definitely wrong with the code
    Error(ValueError),
    Warning(Warning),
}

impl Display for AlarmKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            AlarmKind::Error(e) => e.fmt(f),
            AlarmKind::Warning(w) => w.fmt(f),
        }
    }
}

/// Warnings and errors to be displayed to the user
pub type Alarm = Located<AlarmKind>;

impl Alarm {
    /// Converts this alarm to a LSP diagnostic
    pub fn to_diagnostic(&self, code: &str) -> Diagnostic {
        let severity = match self.kind {
            AlarmKind::Warning(_) => DiagnosticSeverity::WARNING,
            AlarmKind::Error(_) => DiagnosticSeverity::ERROR,
        };
        Diagnostic {
            range: utils::range(code, self.range),
            severity: Some(severity),
            message: self.kind.to_string(),
            ..Diagnostic::default()
        }
    }
}

/// If this node is an identifier, should it be a variable name ?
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Ident {
    /// If this node is an identifier, it should be a variable name
    IsVariable,
    /// If this not is an identifier, it is not a variable name
    ///
    /// Example: foo in `bar.foo`
    IsNotVariable,
}

struct Visitor {
    /// set of bindings that must be used
    ///
    /// a binding is a pair of the name and range where the binding was introduced.
    unused: HashSet<(TextRange, String)>,
    /// Errors already found
    alarms: Vec<Alarm>,
}

impl Visitor {
    /// this scope contains bindings that must be used
    fn add_scope(&mut self, scope: &Scope) {
        match scope {
            Scope::Root(_) | Scope::With { .. } | Scope::None => {
                // no binding must be used
                // should probably not happen anyway
            }
            Scope::Let {
                parent: _,
                contents,
            } => self.unused.extend(
                contents
                    .borrow()
                    .iter()
                    .filter(|(name, _)| !name.starts_with("_"))
                    .map(|(name, info)| (info.identifier_range, name.clone())),
            ),
            Scope::FunctionArguments { parent: _, names } => self.unused.extend(
                names
                    .borrow()
                    .iter()
                    .filter(|(name, _)| !name.starts_with("_"))
                    .map(|(name, info)| (info.identifier_range, name.clone())),
            ),
        }
    }

    /// to be called after the node for which one calls add_scope is visited
    fn finish_scope_of(&mut self, node_range: Option<TextRange>, contains_unparsed: bool) {
        let unused_ref = &mut self.unused;
        let alarms_ref = &mut self.alarms;
        if let Some(node_range) = node_range {
            unused_ref.retain(|(range, name)| {
                if node_range.contains_range(*range) {
                    // it is now too late to use this binding, either it's an error or not
                    if !contains_unparsed {
                        alarms_ref.push(Located {
                            range: range.clone(),
                            kind: AlarmKind::Warning(Warning::UnusedBinding((*name).clone())),
                        });
                    }
                    false
                } else {
                    true
                }
            });
        }
    }

    /// If this is an error, maybe report it to self.errors. Otherwise, visit all children of this node
    /// to find evaluation errors and collect diagnostics.
    ///
    /// returns whether one of the children was not parsed correctly
    fn visit_result<T: Borrow<Expr>>(
        &mut self,
        result: &Result<T, EvalError>,
        range: &Option<TextRange>,
        ident_ctx: Ident,
    ) -> bool {
        match result {
            Err(EvalError::Value(err)) => {
                if let Some(range) = range {
                    self.alarms.push(Located {
                        range: range.clone(),
                        kind: AlarmKind::Error(err.clone()),
                    })
                }
                return false;
            }
            Err(EvalError::Internal(_)) => true,
            Ok(v) => self.visit(v.borrow(), ident_ctx),
        }
    }

    /// Visit all children of this node to find evaluation errors and collect
    /// diagnostics to self.errors
    fn visit(&mut self, node: &Expr, ident_ctx: Ident) -> bool {
        use Ident::*;
        let mut nok = false;
        match &node.source {
            ExprSource::AttrSet { definitions } => {
                for i in definitions.iter() {
                    nok |= self.visit_result(i, &node.range, IsVariable)
                }
            }
            ExprSource::LetIn { definitions, body } => {
                self.add_scope(node.scope.as_ref());
                for i in definitions.iter() {
                    nok |= self.visit_result(i, &node.range, IsVariable)
                }
                nok |= self.visit_result(body, &node.range, IsVariable);
                self.finish_scope_of(node.range, nok);
            }
            ExprSource::KeyValuePair { key, value } => {
                nok |= self.visit_result(key, &node.range, IsNotVariable);
                nok |= self.visit_result(value, &node.range, IsVariable);
            }
            ExprSource::Select { from, index } => {
                nok |= self.visit_result(from, &node.range, IsVariable);
                nok |= self.visit_result(index, &node.range, IsNotVariable);
            }
            ExprSource::Lambda { arg, body } => {
                self.add_scope(node.scope.as_ref());
                nok |= self.visit_result(body, &node.range, IsVariable);
                nok |= self.visit_result(arg, &node.range, IsNotVariable);
                self.finish_scope_of(node.range, nok);
            }
            ExprSource::OrDefault { index, default } => {
                nok |= self.visit_result(index, &node.range, IsVariable);
                nok |= self.visit_result(default, &node.range, IsVariable);
            }
            ExprSource::With { inner, body } => {
                nok |= self.visit_result(body, &node.range, IsVariable);
                nok |= self.visit_result(inner, &node.range, IsVariable);
            }
            ExprSource::Assert { condition, body } => {
                nok |= self.visit_result(body, &node.range, IsVariable);
                nok |= self.visit_result(condition, &node.range, IsVariable);
            }
            ExprSource::IfElse {
                condition,
                body,
                else_body,
            } => {
                nok |= self.visit_result(body, &node.range, IsVariable);
                nok |= self.visit_result(else_body, &node.range, IsVariable);
                nok |= self.visit_result(condition, &node.range, IsVariable);
            }
            ExprSource::Pattern { entries, .. } => {
                for i in entries.values() {
                    if let Some(default) = i {
                        nok |= self.visit_result(default, &node.range, IsVariable);
                    }
                }
            }
            ExprSource::String { parts } => {
                for i in parts.iter() {
                    if let StringPartSource::Expression(expr) = i {
                        nok |= self.visit_result(expr, &node.range, IsVariable);
                    }
                }
            }
            ExprSource::List { elements } => {
                for i in elements.iter() {
                    nok |= self.visit_result(i, &node.range, IsVariable);
                }
            }
            ExprSource::Ident { name } => {
                if ident_ctx == IsVariable {
                    if let Some(range) = &node.range {
                        let def = node.scope.get_definition(name);
                        // check that the variable is bound
                        if def.definitely_unbound() {
                            self.alarms.push(Located {
                                range: range.clone(),
                                kind: AlarmKind::Error(ValueError::UnboundIdentifier(name.clone())),
                            });
                        }
                        if let Some(range) = def.binding_identifier_range() {
                            self.unused.remove(&(range, name.clone()));
                        }
                    }
                }
            }
            ExprSource::Literal { .. } => {}
            ExprSource::UnaryInvert { value: inner }
            | ExprSource::UnaryNegate { value: inner }
            | ExprSource::Dynamic { inner }
            | ExprSource::Paren { inner } => {
                nok |= self.visit_result(inner, &node.range, IsVariable)
            }
            ExprSource::BinOp { left, right, .. }
            | ExprSource::BoolAnd { left, right }
            | ExprSource::Apply {
                function: left,
                arg: right,
            }
            | ExprSource::Implication { left, right }
            | ExprSource::BoolOr { left, right } => {
                nok |= self.visit_result(left, &node.range, IsVariable);
                nok |= self.visit_result(right, &node.range, IsVariable);
            }
        }
        return nok;
    }
}
/// Looks for errors in the user code. Attempts to return no false positives.
///
/// Current analysis can detect undefined variables.
pub fn check(node: &Expr) -> Vec<Alarm> {
    let mut visitor = Visitor {
        alarms: Vec::new(),
        unused: Default::default(),
    };
    visitor.visit(node, Ident::IsVariable);

    visitor.alarms
}
