use crate::eval::{Expr, ExprSource};
use crate::value::NixValue;
use gc::{Finalize, Gc, GcCell, Trace};
use rnix::TextRange;
use std::{collections::HashMap, path::PathBuf};

/// Info about a let binding or attrset binding
#[derive(Trace, Finalize, Debug, Clone)]
pub struct LetBindingInfo {
    /// the range of the indentifier creating the binding
    #[unsafe_ignore_trace]
    pub identifier_range: TextRange,
    /// the value bound to this identifier
    pub value: Gc<Expr>,
}

/// Info about a binding as function argument
#[derive(Trace, Finalize, Debug, Clone)]
pub struct ArgBindingInfo {
    /// the range of the indentifier creating the binding
    #[unsafe_ignore_trace]
    pub identifier_range: TextRange,
}

/// A parent Expr's scope is used to provide tooling for its child Exprs.
#[derive(Trace, Finalize, Debug)]
pub enum Scope {
    /// Provided for each file. Used for providing global variables
    ///   and tracking the `import` dependency tree. Also used for detecting
    ///   which file an expression is defined in.
    Root(PathBuf),
    /// Created by `let in` and `rec { }`. All the variable names
    ///   can be derived using static analysis with rnix-parser; we don't need
    ///   to evaluate anything to detect if a variable name is in this scope
    Let {
        parent: Gc<Scope>,
        /// binding name -> (range of the identifier creating the binding, expression of the value)
        contents: GcCell<HashMap<String, LetBindingInfo>>,
    },
    /// Binding introduced as a function argument or function argument pattern
    FunctionArguments {
        parent: Gc<Scope>,
        /// names bound and the range where they were bound
        names: GcCell<HashMap<String, ArgBindingInfo>>,
    },
    /// Binding introduced by `with`
    With {
        /// parent scope
        ///
        /// This is a synctatical relation: bindings introduced by with are always resolved after
        /// other bindings, so this scope might be shadowed by its parent.
        parent: Gc<Scope>,
        /// the expression `e` in `with e;`
        contents: Gc<Expr>,
    },
    /// Used for calculated literals. For example, for the string
    ///   interpolation `"prefix${suffix}"`, the literal `prefix` by itself
    ///   cannot be referenced anywhere except at its definition, so we don't
    ///   need context-aware tooling for it. For `${suffix}`, however, we would
    ///   inherit the parent's scope.
    None,
}

/// How a binding might be defined
#[derive(Debug, Clone)]
pub enum Definition {
    /// Might be either unbound or bound dynamically by `with`
    PossiblyDynamic,
    /// Here is the expression that defines this variable, and the scope containing it
    Expression(LetBindingInfo),
    /// this variable is a formal argument of a function
    Argument(ArgBindingInfo),
    /// this variable is definitely not defined
    Unbound,
    /// builtins always in scope
    Ambient,
}

impl Definition {
    /// If applicable, the range of the identifier where it was bound
    ///
    /// It's not necessarily unique because of `rec { a.b = 1; a.c = 2 }`. Only
    /// one is returned.
    pub fn binding_identifier_range(&self) -> Option<TextRange> {
        match self {
            Definition::Expression(info) => Some(info.identifier_range),
            Definition::Argument(info) => Some(info.identifier_range),
            Definition::Unbound | Definition::Ambient | Definition::PossiblyDynamic => None,
        }
    }

    /// true if there is definitely no binding of this name
    pub fn definitely_unbound(&self) -> bool {
        match self {
            Definition::Unbound => true,
            _ => false,
        }
    }
}

impl Scope {
    /// Finds the Expr of an identifier in the scope.
    ///
    /// This would do two passes up the tree:
    /// 1. Check Scope::Normal and Scope::Root
    /// 2. Check Scope::With, which requires evaluation
    ///
    /// See https://github.com/NixOS/nix/issues/490 for an explanation
    /// of why Nix works this way.
    ///
    /// Examples:
    /// ```plain
    /// nix-repl> let import = 1; in import
    /// 1 # found in Scope::Normal, which we reach before Scope::Root
    /// nix-repl> import
    /// «primop» # found in Scope::Root
    /// nix-repl> with { import = 1; }; import
    /// «primop» # found in Scope::Root, which we reach before Scope::With
    /// ```
    pub fn get(&self, name: &str) -> Option<Gc<Expr>> {
        self.get_let(name) // we haven't yet implemented fallback to a future get_with method
    }

    pub fn get_let(&self, name: &str) -> Option<Gc<Expr>> {
        match self.get_definition(name) {
            Definition::Expression(x) => Some(x.value.clone()),
            _ => None,
        }
    }

    /// how/if this name is defined
    pub fn get_definition(&self, name: &str) -> Definition {
        fn get_definition_rec<'a, 'b>(
            scope: &'a Scope,
            name: &'b str,
            possibly_dynamic: bool,
        ) -> Definition {
            match scope {
                Scope::None | Scope::Root(_) => {
                    fn make_value(value: NixValue) -> Definition {
                        let expr = Gc::new(Expr {
                            range: None,
                            value: GcCell::new(None),
                            source: ExprSource::Literal { value },
                            scope: Gc::new(Scope::None),
                        });
                        let info = LetBindingInfo {
                            identifier_range: TextRange::empty(0.into()),
                            value: expr,
                        };
                        Definition::Expression(info)
                    }
                    match name {
                        "true" => make_value(NixValue::Bool(true)),
                        "false" => make_value(NixValue::Bool(false)),
                        "null" => make_value(NixValue::Null),
                        // list obtained with `nix repl` tab completion
                        "abort"
                        | "__add"
                        | "__addErrorContext"
                        | "__all"
                        | "__any"
                        | "__appendContext"
                        | "__attrNames"
                        | "__attrValues"
                        | "baseNameOf"
                        | "__bitAnd"
                        | "__bitOr"
                        | "__bitXor"
                        | "builtins"
                        | "__catAttrs"
                        | "__ceil"
                        | "__compareVersions"
                        | "__concatLists"
                        | "__concatMap"
                        | "__concatStringsSep"
                        | "__currentSystem"
                        | "__currentTime"
                        | "__deepSeq"
                        | "derivation"
                        | "derivationStrict"
                        | "dirOf"
                        | "__div"
                        | "__elem"
                        | "__elemAt"
                        | "fetchGit"
                        | "fetchMercurial"
                        | "fetchTarball"
                        | "fetchTree"
                        | "__fetchurl"
                        | "__filter"
                        | "__filterSource"
                        | "__findFile"
                        | "__floor"
                        | "__foldl'"
                        | "__fromJSON"
                        | "fromTOML"
                        | "__functionArgs"
                        | "__genericClosure"
                        | "__genList"
                        | "__getAttr"
                        | "__getContext"
                        | "__getEnv"
                        | "__groupBy"
                        | "__hasAttr"
                        | "__hasContext"
                        | "__hashFile"
                        | "__hashString"
                        | "__head"
                        | "import"
                        | "__intersectAttrs"
                        | "__isAttrs"
                        | "__isBool"
                        | "__isFloat"
                        | "__isFunction"
                        | "__isInt"
                        | "__isList"
                        | "isNull"
                        | "__isPath"
                        | "__isString"
                        | "__langVersion"
                        | "__length"
                        | "__lessThan"
                        | "__listToAttrs"
                        | "map"
                        | "__mapAttrs"
                        | "__match"
                        | "__mul"
                        | "__nixPath"
                        | "__nixVersion"
                        | "__parseDrvName"
                        | "__partition"
                        | "__path"
                        | "__pathExists"
                        | "placeholder"
                        | "__readDir"
                        | "__readFile"
                        | "removeAttrs"
                        | "__replaceStrings"
                        | "scopedImport"
                        | "__seq"
                        | "__sort"
                        | "__split"
                        | "__splitVersion"
                        | "__storeDir"
                        | "__storePath"
                        | "__stringLength"
                        | "__sub"
                        | "__substring"
                        | "__tail"
                        | "throw"
                        | "__toFile"
                        | "__toJSON"
                        | "__toPath"
                        | "toString"
                        | "__toXML"
                        | "__tryEval"
                        | "__typeOf"
                        | "__unsafeDiscardOutputDependency"
                        | "__unsafeDiscardStringContext"
                        | "__unsafeGetAttrPos"
                        | "__zipAttrsWith" => Definition::Ambient,
                        _ => {
                            if possibly_dynamic {
                                Definition::PossiblyDynamic
                            } else {
                                Definition::Unbound
                            }
                        }
                    }
                }
                Scope::Let { parent, contents } => match contents.borrow().get(name) {
                    Some(x) => Definition::Expression(x.clone()),
                    None => get_definition_rec(parent, name, possibly_dynamic),
                },
                Scope::FunctionArguments { parent, names } => match names.borrow().get(name) {
                    Some(info) => Definition::Argument(info.clone()),
                    None => get_definition_rec(parent, name, possibly_dynamic),
                },
                Scope::With {
                    parent,
                    contents: _,
                } => {
                    // trying to evaluate the content is not yet implemented
                    get_definition_rec(parent, name, true)
                }
            }
        }
        get_definition_rec(&self, name, false)
    }

    pub fn root_path(&self) -> Option<PathBuf> {
        match &self {
            Scope::None => None,
            Scope::Root(path) => Some(path.clone()),
            Scope::Let { parent, .. } => parent.root_path(),
            Scope::With { parent, .. } => parent.root_path(),
            Scope::FunctionArguments { parent, .. } => parent.root_path(),
        }
    }
}
