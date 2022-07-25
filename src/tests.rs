use eval::Expr;
use gc::Gc;
use rnix::types::Wrapper;
use scope::Scope;
use std::borrow::Borrow;
use value::NixValue;
use crate::static_analysis::{self, Alarm, AlarmKind};

#[cfg(test)]
use maplit::hashmap;
#[cfg(test)]
use serde_json::json;
#[cfg(test)]
use std::time::Duration;
#[cfg(test)]
use stoppable_thread::*;

#[allow(dead_code)]
/// Evaluates a nix code snippet
fn eval(code: &str) -> NixValue {
    let ast = rnix::parse(&code);
    let root = ast.root().inner().unwrap();
    let path = std::env::current_dir().unwrap();
    let out = Expr::parse(root, Gc::new(Scope::Root(path))).unwrap();
    let errors: Vec<Alarm> = static_analysis::check(&out)
        .into_iter()
        .filter(|alarm| matches!(alarm.kind, AlarmKind::Error(_)))
        .collect();
    assert_eq!(errors, Vec::new());
    let tmp = out.eval();
    let val: &NixValue = tmp.as_ref().unwrap().borrow();
    val.clone()
}

#[allow(dead_code)]
/// Returns the alarms found by static_analysis::check.
///
/// As dealing with ranges is cumbersome, returns a map "text matched by the range" => "error text"
/// Also mixes warnings and errors without distinguisher.
/// A shortcut to static_analysis_verbose(code, false)
fn static_analysis(code: &str) -> HashMap<&str, String> {
    static_analysis_verbose(code, false)
}

#[allow(dead_code)]
/// Returns the alarms found by static_analysis::check.
///
/// As dealing with ranges is cumbersome, returns a map "text matched by the range" => "error text"
/// If verbose is true, then the error message also contains a textual representation
/// of the range.
/// Also mixes warnings and errors without distinguisher.
fn static_analysis_verbose(code: &str, verbose: bool) -> HashMap<&str, String> {
    let ast = rnix::parse(&code);
    let root = ast.root().inner().unwrap();
    let path = std::env::current_dir().unwrap();
    let out = Expr::parse(root, Gc::new(Scope::Root(path))).unwrap();
    let errors = static_analysis::check(&out);
    let mut res = HashMap::new();
    for error in errors {
        let range = error.range.start().into()..error.range.end().into();
        let text = code.get(range).unwrap();
        let error_text = if verbose {
            error.to_string()
        } else {
            error.kind.to_string()
        };
        res.insert(text, error_text);
    }
    res
}

use super::*;

#[test]
fn integer_division() {
    let code = "1 / 2";
    assert_eq!(eval(code).as_int().unwrap(), 0);
}

#[test]
fn float_division() {
    let code = "1.0 / 2.0";
    assert_eq!(eval(code).as_float().unwrap(), 0.5);
}

#[test]
fn order_of_operations() {
    let code = "1 + 2 * 3";
    assert_eq!(eval(code).as_int().unwrap(), 7);
}

#[test]
fn eval_let() {
    let code = "let x = 1; in x";
    assert_eq!(eval(code).as_int().unwrap(), 1);
}

#[test]
fn eval_let_sequential() {
    let code = "let x = 1; y = x; in x + y";
    assert_eq!(eval(code).as_int().unwrap(), 2);
}

#[test]
fn div_int_by_float() {
    let code = "1 / 2.0";
    assert_eq!(eval(code).as_float().unwrap(), 0.5);
}

#[test]
fn unbound_simple() {
    let code = "1+x";
    assert_eq!(static_analysis(code), hashmap!{ "x" => "identifier x is unbound".into() });
}

#[test]
fn with_conservative_binding_analysis() {
    let code = "1 + with import <nixpkgs> {}; some_attr";
    assert_eq!(static_analysis(code), hashmap!{});
}

#[test]
fn binding_analysis_ignores_attrset_selection() {
    let code = "1 + rec { x = 1; y = x; }.y";
    assert_eq!(static_analysis(code), hashmap!{});
}

#[test]
fn unbound_attrset() {
    let code = "1 + rec { x = 1; y = x; z = t; }.y";
    assert_eq!(
        static_analysis(code),
        hashmap! {"t" => "identifier t is unbound".into()}
    );
}

#[test]
fn unbound_list() {
    let code = "[ 1 t ]";
    assert_eq!(
        static_analysis(code),
        hashmap! {"t" => "identifier t is unbound".into()}
    );
}

#[test]
fn bound_let() {
    let code = "let x = 1; y = x; in x + y";
    assert_eq!(static_analysis(code), hashmap! {});
}

#[test]
fn bound_builtins() {
    let code = "map";
    assert_eq!(static_analysis(code), hashmap! {});
}

#[test]
fn unbound_let_body() {
    let code = "let x = 1; in x + y";
    assert_eq!(
        static_analysis(code),
        hashmap! {"y" => "identifier y is unbound".into()}
    );
}

#[test]
fn unbound_let_defs() {
    let code = "let x = t; y = u; in x + y";
    assert_eq!(
        static_analysis(code),
        hashmap! {"t" => "identifier t is unbound".into(), "u" => "identifier u is unbound".into()}
    );
}

#[test]
fn bound_let_fixpoint() {
    let code = "let x = x; in x";
    assert_eq!(static_analysis(code), hashmap! {});
}

#[test]
fn bound_let_recursive() {
    let code = "let y = x; x = 1; in x - y";
    assert_eq!(static_analysis(code), hashmap! {});
}

#[test]
fn unbound_function_body() {
    let code = "let f = x: x + y; in f 1";
    assert_eq!(static_analysis(code), hashmap! {"y" => "identifier y is unbound".into()});
}

#[test]
fn unbound_function_body_pattern() {
    let code = "let f = {x}: x + y; in f { x = 1; }";
    assert_eq!(static_analysis(code), hashmap! {"y" => "identifier y is unbound".into()});
}

#[test]
fn unbound_function_pattern_default() {
    let code = "let x = 1; f = {y ? x + z }: x + y; in f {}";
    assert_eq!(static_analysis(code), hashmap! {"z" => "identifier z is unbound".into()});
}

#[test]
fn bound_function_pattern_default_seq() {
    let code = "let x = 1; f = {y ? x, z ? y }: x + y + z; in f {}";
    assert_eq!(static_analysis(code), hashmap! {});
}

#[test]
fn bound_function_at() {
    let code = "let f = {y ? args, ... }@args: { inherit args y; }; in f {}";
    assert_eq!(static_analysis(code), hashmap! {});
}

#[test]
fn bound_function_default_loop() {
    let code = "let f = {y ? y, ... }: y; in f {}";
    assert_eq!(static_analysis(code), hashmap! {});
}

#[test]
fn bound_or_default() {
    let code = "let s = {}; n = 1; in s.a or n";
    assert_eq!(static_analysis(code), hashmap! {});
}

#[test]
fn unbound_or_default() {
    let code = "let s = {}; in s.a or n";
    assert_eq!(static_analysis(code), hashmap! {"n" => "identifier n is unbound".into()});
}

#[test]
fn unbound_or_default_indexed() {
    let code = "in s.a or 1";
    assert_eq!(static_analysis(code), hashmap! {"s" => "identifier s is unbound".into()});
}

#[test]
fn unbound_assert_condition() {
    let code = "assert f; 1";
    assert_eq!(static_analysis(code), hashmap! {"f" => "identifier f is unbound".into()});
}

#[test]
fn unbound_assert_body() {
    let code = "assert true; f";
    assert_eq!(static_analysis(code), hashmap! {"f" => "identifier f is unbound".into()});
}

#[test]
fn unbound_if_condition() {
    let code = "if foo then 1 else {}";
    assert_eq!(static_analysis(code), hashmap! {"foo" => "identifier foo is unbound".into()});
}

#[test]
fn unbound_if_body() {
    let code = "if true then foo else {}";
    assert_eq!(static_analysis(code), hashmap! {"foo" => "identifier foo is unbound".into()});
}

#[test]
fn unbound_if_body_else() {
    let code = "if true then 1 else foo";
    assert_eq!(static_analysis(code), hashmap! {"foo" => "identifier foo is unbound".into()});
}

#[test]
fn bound_let_inherit() {
    let code = "let foo = {a = 1;}; in let inherit (foo) a; in a";
    assert_eq!(static_analysis(code), hashmap! {});
}

#[test]
fn unbound_let_inherit() {
    let code = "let foo = {a = 1;}; in let inherit (bar) a; in a";
    assert_eq!(static_analysis(code), hashmap! {
        "bar" => "identifier bar is unbound".into(),
        "foo" => "binding foo is unused".into()
    });
}

#[test]
fn unbound_let_inherit2() {
    let code = "let foo = {bbbb = 1;}; in let inherit (foo) bbbb; in aaaa";
    assert_eq!(static_analysis(code), hashmap! {
        "aaaa" => "identifier aaaa is unbound".into(),
        "bbbb" => "binding bbbb is unused".into()
    });
}

#[test]
fn unbound_let_inherit3() {
    let code = "let foo = {a = 1;}; in let inherit (foo) a; in a + bar";
    assert_eq!(static_analysis(code), hashmap! {"bar" => "identifier bar is unbound".into()});
}

#[test]
fn unbound_with() {
    let code = "with foo; 1";
    assert_eq!(
        static_analysis(code),
        hashmap! {"foo" => "identifier foo is unbound".into()}
    );
}

#[test]
fn maybe_bound_with() {
    let code = "let inf = x: inf x; in with inf {}; bar";
    assert_eq!(static_analysis(code), hashmap! {});
}

#[test]
fn unbound_string() {
    let code = r#" "foo${bar}baz" "#;
    assert_eq!(static_analysis(code), hashmap! {"bar" => "identifier bar is unbound".into()});
}

#[test]
fn unbound_multiline_string() {
    let code = r#" ''
        foo
        ${bar}
    baz''
"#;
    assert_eq!(static_analysis(code), hashmap! {"bar" => "identifier bar is unbound".into()});
}

#[test]
fn unbound_config() {
    let code = "{config, pkgs, ...}: { config = { services.xserver.enable = lib.mkForce true; }; }";
    assert_eq!(static_analysis(code), hashmap! {
        "lib" => "identifier lib is unbound".into(),
        "config" => "binding config is unused".into(),
        "pkgs" => "binding pkgs is unused".into()
    });
}

#[test]
fn unbound_config2() {
    let code = "{config, pkgs, ...}: { config = { environment.systemPackages = [ (lib.hiPrio pkgs.sl) firefox ]; }";
    assert_eq!(
        static_analysis(code),
        hashmap! {
            "lib" => "identifier lib is unbound".into(),
            "firefox" => "identifier firefox is unbound".into(),
            "config" => "binding config is unused".into(),
        }
    );
}

#[test]
fn maybe_bound_config3() {
    let code = "{config, pkgs, ...}: { config = { environment.systemPackages = with pkgs; [ (lib.hiPrio sl) firefox ]; }";
    assert_eq!(static_analysis(code), hashmap! {
        "config" => "binding config is unused".into(),
    });
}

#[test]
fn unused_binding_simple_lamba() {
    let code = "foo: 1";
    assert_eq!(static_analysis(code), hashmap! {
        "foo" => "binding foo is unused".into(),
    });
}

#[test]
fn unused_binding_pattern_lamba() {
    let code = "{foo}: 1";
    assert_eq!(static_analysis(code), hashmap! {
        "foo" => "binding foo is unused".into(),
    });
}

#[test]
fn unused_binding_pattern_lamba_2() {
    let code = "{foo}@args: foo";
    assert_eq!(static_analysis(code), hashmap! {
        "args" => "binding args is unused".into(),
    });
}

#[test]
fn unused_binding_let() {
    let code = "let foo = 1; in 2";
    assert_eq!(static_analysis(code), hashmap! {
        "foo" => "binding foo is unused".into(),
    });
}

#[test]
fn unused_binding_let2() {
    let code = "let foo.bar = 1; foo.baz = 3; in 2";
    assert_eq!(static_analysis(code), hashmap! {
        "foo" => "binding foo is unused".into(),
    });
}

#[test]
fn unused_binding_shadowing() {
    let code = "let foo = 1; in let foo = 2; in foo";
    assert_eq!(static_analysis_verbose(code, true), hashmap! {
        "foo" => "binding foo is unused at 4..7".into(),
    });
}

#[test]
fn unused_binding_shadowing_lambda() {
    let code = "foo: (foo: foo)";
    assert_eq!(static_analysis_verbose(code, true), hashmap! {
        "foo" => "binding foo is unused at 0..3".into(),
    });
}

#[test]
fn unused_binding_with() {
    let code = "{pkgs, lib}: with pkgs; 1";
    assert_eq!(static_analysis(code), hashmap! {
        "lib" => "binding lib is unused".into(),
    });
}

#[test]
fn used_binding_with() {
    let code = "{pkgs, lib}: with pkgs; lib.makeBinPath [ pkgs.sl ]";
    assert_eq!(static_analysis(code), hashmap! {});
}

#[test]
fn unused_underscore_is_ok() {
    let code = "_: 1";
    assert_eq!(static_analysis(code), hashmap! {});
}

#[test]
fn unused_underscore_is_ok2() {
    let code = "let _unused = 1; in 2";
    assert_eq!(static_analysis(code), hashmap! {});
}

#[test]
fn unused_attrset_is_ok() {
    // this is a design decision that could be revisited
    let code = "let complex = rec { a = 1; b = 2; }; in complex.b";
    assert_eq!(static_analysis(code), hashmap! {});
}

#[test]
fn unused_attrset_is_ok2() {
    // this is a design decision that could be revisited
    let code = "rec { a = 1; b = 2; }";
    assert_eq!(static_analysis(code), hashmap! {});
}

#[test]
fn no_unused_with_unparsed_child() {
    // don't warn about unused bindings when a child is not parsed (it could
    // use the variable)
    let code = "let error = 1; in syntax::${error}\"";
    assert_eq!(static_analysis(code), hashmap! {});
}

#[test]
fn unused_with_unparsed_sibling() {
    // don't warn about unused bindings when a child is not parsed (it could
    // use the variable) but do it when it's only a sibling
    let code = "let error = 1; in ((syntax::error) + (let unused = 2; in 2))";
    assert_eq!(static_analysis(code), hashmap! {
        "unused" => "binding unused is unused".into(),
    });
}


#[cfg(test)]
fn prepare_integration_test(code: &str, filename: &str) -> (Connection, StoppableHandle<()>) {
    let (server, client) = Connection::memory();

    // Manually handle LSP communications here. This is needed in order to not wait
    // indefinetely for a message to be able to exit as soon as the test is finished
    // and the thread is stopped.
    let h = spawn(move |stopped| {
        let mut app = App { files: HashMap::new(), conn: server };

        loop {
            if let Ok(msg) = app.conn.receiver.recv_timeout(Duration::from_millis(100)) {
                match msg {
                    Message::Request(req) => app.handle_request(req),
                    Message::Notification(notification) => {
                        let _ = app.handle_notification(notification);
                    }
                    Message::Response(_) => (),
                }
            }
            if stopped.get() {
                break;
            }
        }
    });

    let open = Notification {
        method: String::from("textDocument/didOpen"),
        params: json!({
            "textDocument": { "uri": filename, "text": code, "version": 1, "languageId": "nix" }
        })
    };
    client.sender.send(open.into()).expect("Cannot send didOpen!");

    (client, h)
}

#[cfg(test)]
fn recv_msg(client: &Connection) -> lsp_server::Message {
    client.receiver.recv_timeout(Duration::new(5, 0)).expect("No message within 5 secs!")
}

#[cfg(test)]
fn expect_diagnostics(client: &Connection) {
    let notf = recv_msg(client);
    if let Message::Notification(x) = notf {
        assert_eq!("textDocument/publishDiagnostics", x.method);
    } else {
        panic!("Expected diagnostics notification!");
    }
}

#[cfg(test)]
fn coerce_response(msg: lsp_server::Message) -> lsp_server::Response {
    if let Message::Response(x) = msg {
        x
    } else {
        panic!("Expected LSP message to be a response!");
    }
}

#[test]
fn test_hover_integration() {
    // Since we transmit content via `textDocument/didOpen`, we can
    // use made-up names for paths here that don't need to exist anywhere.
    let urlpath = "file:///code/default.nix";
    let (client, handle) = prepare_integration_test("(1 + 1)", urlpath);

    let r = Request {
        id: RequestId::from(23),
        method: String::from("textDocument/hover"),
        params: json!({
            "textDocument": {
                "uri": "file:///code/default.nix",
            },
            "position": {
                "line": 0,
                "character": 7
            }
        })
    };
    client.sender.send(r.into()).expect("Cannot send hover notification!");

    expect_diagnostics(&client);

    let msg = recv_msg(&client);
    let hover_json = coerce_response(msg).result.expect("Expected hover response!");
    let hover_value = &hover_json.as_object().unwrap()["contents"]["value"];
    assert_eq!("2", *hover_value.to_string().split("\\n").collect::<Vec<_>>().get(1).unwrap());

    handle.stop().join().expect("Failed to gracefully terminate LSP worker thread!");
}

#[test]
fn test_rename() {
    let urlpath = "file:///code/default.nix";
    let (client, handle) = prepare_integration_test("let a = { b = a; }; in a", urlpath);

    let r = Request {
        id: RequestId::from(23),
        method: String::from("textDocument/rename"),
        params: json!({
            "textDocument": {
                "uri": urlpath
            },
            "position": {
                "line": 0,
                "character": 24,
            },
            "newName": "c",
        })
    };
    client.sender.send(r.into()).expect("Cannot send rename request!");

    expect_diagnostics(&client);
    let msg = recv_msg(&client);

    let response = coerce_response(msg).result.expect("Expected rename response!");
    let changes = &response
        .as_object()
        .unwrap()["changes"]["file:///code/default.nix"]
        .as_array()
        .expect("Changes must be an array!");

    // `let a`, `{ b = a; }`, `in a` is where `a` should be replaced with `c`.
    assert_eq!(3, changes.len());

    let first = changes
        .get(0)
        .expect("Array should have three elements!")
        .as_object()
        .expect("Changes should be objects!");

    assert_eq!("c", first["newText"]);
    assert_eq!(4, first["range"]["start"]["character"]);
    assert_eq!(5, first["range"]["end"]["character"]);
    assert_eq!(0, first["range"]["start"]["line"]);
    assert_eq!(0, first["range"]["end"]["line"]);

    let second = changes
        .get(1)
        .expect("Array should have three elements!")
        .as_object()
        .expect("Changes should be objects!");

    assert_eq!("c", second["newText"]);
    assert_eq!(14, second["range"]["start"]["character"]);
    assert_eq!(15, second["range"]["end"]["character"]);
    assert_eq!(0, second["range"]["start"]["line"]);
    assert_eq!(0, second["range"]["end"]["line"]);

    let third = changes
        .get(2)
        .expect("Array should have three elements!")
        .as_object()
        .expect("Changes should be objects!");

    assert_eq!("c", third["newText"]);
    assert_eq!(23, third["range"]["start"]["character"]);
    assert_eq!(24, third["range"]["end"]["character"]);
    assert_eq!(0, third["range"]["start"]["line"]);
    assert_eq!(0, third["range"]["end"]["line"]);

    handle.stop().join().expect("Failed to gracefully terminate LSP worker thread!");
}

#[test]
fn attrs_simple() {
    let code = "{ x = 1; y = 2; }.x";
    assert_eq!(eval(code).as_int().unwrap(), 1);
}

#[test]
fn attrs_path() {
    let code = "{ x.y.z = 3; }.x.y.z";
    assert_eq!(eval(code).as_int().unwrap(), 3);
}

#[test]
fn attrs_rec() {
    let code = "rec { x = 4; y = x; }.y";
    assert_eq!(eval(code).as_int().unwrap(), 4);
}

#[test]
fn attrs_rec_nested() {
    let code = "rec { x = { b = 1; }; y = x; }.y.b";
    assert_eq!(eval(code).as_int().unwrap(), 1);
}

#[test]
fn attrs_merge() {
    let code = "{ a = { b = 1; }; a.c = 2; }".to_string();
    assert_eq!(eval(&format!("{}.a.b", code)).as_int().unwrap(), 1);
    assert_eq!(eval(&format!("{}.a.c", code)).as_int().unwrap(), 2);
}

#[test]
fn attrs_merge_conflict() {
    let ast = rnix::parse("{ a = { b = 1; c = 3; }; a.c = 2; }");
    let root = ast.root().inner().unwrap();
    let path = std::env::current_dir().unwrap();
    let parse_result = Expr::parse(root, Gc::new(Scope::Root(path)));
    assert!(parse_result.is_err());
}

#[test]
fn attrs_merge_conflict_rec() {
    let ast = rnix::parse("rec { x = { b = 1; }; a = x; a.c = 2; }");
    let root = ast.root().inner().unwrap();
    let path = std::env::current_dir().unwrap();
    let parse_result = Expr::parse(root, Gc::new(Scope::Root(path)));
    assert!(parse_result.is_err());
}

#[test]
fn attrs_merge_conflict_inherit() {
    let ast = rnix::parse("{ inherit ({ a = { b = 1; }; }) a; a.c = 2; }");
    let root = ast.root().inner().unwrap();
    let path = std::env::current_dir().unwrap();
    let parse_result = Expr::parse(root, Gc::new(Scope::Root(path)));
    assert!(parse_result.is_err());
}

#[test]
fn attrs_inherit_from() {
    let code = "{ inherit ({ b = 1; }) b; }.b";
    assert_eq!(eval(code).as_int().unwrap(), 1);
}
