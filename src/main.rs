#![feature(map_first_last)]

extern crate structopt;

mod data;
mod scope;

use std::collections::HashMap;
use std::io::{ self, BufRead };

use structopt::StructOpt;

use scope::Env;
use data::{ shift_left, shift_right, subst };

#[derive(StructOpt)]
#[structopt(name = "kvokeval")]
struct Config {
    /// Print to stdout when a constant has been declared/defined successfully
    #[structopt(short, long)]
    verbose: bool,
}

static mut CFG: Config = Config { verbose: false };

type Vars = HashMap<String, Vec<String>>;


fn equal(a: Vec<String>, b: Vec<String>, scope: &Env, vars: &mut Vars) -> bool {
    if a == b {
        true

    } else {
        let a = reduce_n_times(a.clone(), scope, vars, 0);
        let b = reduce_n_times(b.clone(), scope, vars, 0);// FIXME: fn-typ equal on substitution

        a == b
    }
}


// [AREA] Well-Formedness
//
fn _wf_sgl(scope: &Env, _: &mut (), x: &str) -> bool {
    debug("[canform] typ == x || ?x");

    "typ" == x || scope.contains_item(x)
}

fn _wf_var(scope: &Env, _: &mut (), var: &str) -> bool {
    !scope.contains_item(var)
}

fn _wf_lambda(scope: &Env, _: &mut (), bound: &str, bound_ty: &[String], body: &[String]) -> bool {
    let mut inner_scope = scope.clone();
    inner_scope.insert(bound.to_string(), (bound_ty.to_vec(), None));

    debug("[canform] canform body");

    well_formed(body, &inner_scope)
}

fn _wf_fn_ty(scope: &Env, _: &mut (), bound: &str, source: &[String], target: &[String]) -> bool {
    let mut inner_scope = scope.clone();
    inner_scope.insert(bound.to_string(), (source.to_vec(), None));

    debug("[canform] (canform source) && (canform target)");

    well_formed(source, scope) && well_formed(target, &inner_scope)
}

fn _wf_call(scope: &Env, _out: &mut (), args: &[Vec<String>], fn_name: &str) -> bool {
    debug("[canform] (canform fn_name) && (canform args)");

    well_formed(&[fn_name.to_string()], scope) && args.iter().all(|arg| well_formed(arg, scope))
}

fn well_formed(expr: &[String], scope: &Env) -> bool {
    data::recurse(expr, scope, &mut (), true, _wf_sgl, _wf_var, _wf_lambda, _wf_fn_ty, _wf_call)
}
//
// [END] Well-Formedness


// [AREA] Typechecking
//
fn _tc_sgl((ty, scope): (&[String], &Env), vars: &mut Vars, x: &str) -> bool {
    if ty == &[] as &[String] {
        return true;
    }

    if "typ" == x {
        debug("[??] typ == ty");

        equal(["typ".to_string()].to_vec(), ty.to_vec(), scope, vars)

    } else {
        let actual = &scope.get(x).unwrap().0;

        debug("[??] ty == actual");

        equal(ty.to_vec(), actual.to_vec(), scope, vars)
    }
}

fn _tc_var((ty, scope): (&[String], &Env), vars: &mut Vars, var: &str) -> bool {
    if let Some(old_ty) = vars.get(var) {
        ty == &[] as &[String] || equal(ty.to_vec(), old_ty.to_vec(), scope, vars)

    } else {
        vars.insert(var.to_string(), ty.to_vec());

        true
    }
}

fn _tc_lambda((ty, scope): (&[String], &Env), vars: &mut Vars, bound: &str, bound_ty: &[String], body: &[String]) -> bool {
    let ty = reduce_n_times(ty.to_vec(), scope, vars, 0);

    if let [.., head] = &ty[..] {
        if &head[0..=0] == ">" {
            let ty_bound = &head[1..];

            if let [source, target] = data::split_by_lvl(&ty, 1)[..] {
                let mut source = source.to_vec();
                shift_left(&mut source, 1);

                let mut target = target.to_vec();
                shift_left(&mut target, 1);

                assert!(equal(source.clone(), bound_ty.to_vec(), scope, vars), "domains don't match: {} : {:?} =/= {:?}", bound, source, bound_ty);

                let val_alias = if ty_bound == bound { None } else { Some(vec![ty_bound.to_string()]) };

                let mut inner_scope = scope.clone();
                inner_scope.insert(ty_bound.to_string(), (source.clone(), None));
                inner_scope.insert(bound.to_string(), (source.clone(), val_alias));

                debug("[??] ?? body target");

                typecheck(body, &target, &inner_scope, vars)

            } else {
                panic!["syntax error: `>{}` requires 2 parameters", ty_bound]
            }

        } else {
            panic!["doesn't match: ...> ~~ {:?}", ty]
        }

    } else {
        panic!["doesn't match: ...> ~~ {:?}", ty]
    }
}

fn _tc_fn_ty((ty, scope): (&[String], &Env), vars: &mut Vars, bound: &str, source: &[String], target: &[String]) -> bool {
    assert![equal(["typ".to_string()].to_vec(), ty.to_vec(), scope, vars), "doesn't match: typ ~~ {:?}", ty];

    let mut inner_scope = scope.clone();
    inner_scope.insert(bound.to_string(), (source.to_vec(), None));

    let typ = ["typ".to_string()];

    debug("[??] (?? source typ) && (?? target typ)");

    typecheck(source, &typ, scope, vars) && typecheck(&target, &typ, &inner_scope, vars)
}

fn _tc_call_util(ret_ty: &[String], vars: &mut Vars, scope: &Env, args: &[Vec<String>], fn_ty: &[String]) -> bool {
    let fn_ty = reduce_n_times(fn_ty.to_vec(), scope, vars, 0);

    if let [ref rest @ .., head] = &fn_ty[..] {
        let mut rest = rest.to_vec();
        shift_left(&mut rest, 1);

        if let [source, target] = &data::split_by_lvl(&rest, 0)[..] {
            if let [arg] = &args[..] {
                if head.len() > 1 {
                    let mut inner_scope = scope.clone();
                    inner_scope.insert(head[1..].to_string(), (source.to_vec(), Some(arg.to_vec())));

                    debug("[??] (?? arg source) && (call_util inner_scope ret_ty args[..] target)");

                    typecheck(arg, source, scope, vars) && (ret_ty == &[] as &[String] || equal(ret_ty.to_vec(), target.to_vec(), &inner_scope, vars))

                } else {
                    debug("[??] (?? arg source) && (call_util scope ret_ty args[..] target)");

                    typecheck(arg, source, scope, vars) && (ret_ty == &[] as &[String] || equal(ret_ty.to_vec(), target.to_vec(), scope, vars))
                }

            } else if let [rest_args @ .., arg] = &args[..] {
                if head.len() > 1 {
                    let mut inner_scope = scope.clone();
                    inner_scope.insert(head[1..].to_string(), (source.to_vec(), Some(arg.to_vec())));

                    debug("[??] (?? arg source) && (call_util inner_scope ret_ty args[..] target)");

                    typecheck(arg, source, scope, vars) && _tc_call_util(ret_ty, vars, &inner_scope, rest_args, target)

                } else {
                    debug("[??] (?? arg source) && (call_util scope ret_ty args[..] target)");

                    typecheck(arg, source, scope, vars) && _tc_call_util(ret_ty, vars, scope, rest_args, target)
                }

            } else {
                debug("[??] ret_ty == fn_ty");

                equal(ret_ty.to_vec(), fn_ty, scope, vars)
            }

        } else {
            unreachable!["invalid function type syntax"]// NOTE: Also not checking &head[0..=0] == ">"
        }

    } else {
        panic!["invalid function type: {:?}", fn_ty]
    }
}
fn _tc_call((ty, scope): (&[String], &Env), vars: &mut Vars, args: &[Vec<String>], fn_name: &str) -> bool {
    let fn_ty = scope.get(fn_name).map(|(ty, _)| ty).or(vars.get(fn_name)).cloned().unwrap();

    _tc_call_util(ty, vars, scope, args, &fn_ty)
}

fn typecheck(expr: &[String], ty: &[String], scope: &Env, vars: &mut Vars) -> bool {
    assert![well_formed(expr, scope), "expression isn't well-formed"];

    data::recurse(expr, (ty, scope), vars, true, _tc_sgl, _tc_var, _tc_lambda, _tc_fn_ty, _tc_call)
}
//
// [END] Typechecking


/// Reduces the expression once, provided it's well-formed and well-typed in `scope`.
///
/// # Panics
/// This function panics when the expression isn't well-formed or well-typed.
///
/// # Returns
/// Returns whether the expression can be reduced further.
///
fn reduce(expr: Vec<String>, scope: &Env, vars: &mut Vars) -> (bool, Vec<String>) {
    assert![well_formed(&expr, scope), "expression isn't well-formed"];

    let mut extend_eq_family = None;

    if let Some(reduct) = scope.reduce(&expr) {
        if reduct.len() < expr.len() {
            return (true, reduct);

        } else {
            scope.add_eq(&reduct, expr.clone());

            extend_eq_family = Some(reduct);
        }
    }

    let elems = data::split_by_lvl(&expr, 0);

    let mut ret = vec![];
    let mut can_reduce_more = false;

    for elem in elems {
        match &elem[..] {
            [var] if &var[0..=0] == "?" => ret.push(var.to_string()),
            [x] => {
                if "typ" == x {
                    ret.push("typ".to_string());
                    continue;
                }

                match scope.get(x) {
                    Some((_, Some(val))) => { can_reduce_more = true; ret.extend(val.clone()); },

                    Some((_, None)) => ret.push(x.to_string()),

                    None => unreachable!["undefined constant: {:?}", x],
                }
            },

            [body @ .., head] if &head[0..=0] == "<" => {
                let mut body = body.to_vec();

                shift_left(&mut body, 1);
                let bound = &head[1..];

                if let [.., bound_ty] = data::split_by_lvl(&body, 0)[..] {
                    let mut inner_scope = scope.clone();
                    inner_scope.insert(bound.to_string(), (bound_ty.to_vec(), None));

                    let (more, mut new) = reduce(body[..body.len() - bound_ty.len()].to_vec(), &inner_scope, vars);

                    let mut bound_ty = bound_ty.to_vec();

                    shift_right(&mut new, 1);
                    shift_right(&mut bound_ty, 1);

                    can_reduce_more |= more;

                    ret.extend(new);
                    ret.extend(bound_ty);
                    ret.push(head.to_string());

                } else {
                    panic!["syntax error: `<{}` requires at least 2 parameters", bound]
                }
            },
            [body @ .., head] if &head[0..=0] == ">" => {
                let mut bound = head[1..].to_string();

                if let [source, target] = &data::split_by_lvl(&body, 1)[..] {
                    let mut source = source.to_vec();
                    let mut target = target.to_vec();

                    shift_left(&mut source, 1);
                    shift_left(&mut target, 1);

                    if scope.contains_item(&bound) {
                        bound = scope.gen_fresh(bound);

                        subst(&mut target, &head[1..], bound.clone());
                    }

                    assert![typecheck(&source, &["typ".to_string()], scope, vars), "1st argument of `>{}` must be a type", bound];

                    let (can_a, mut a) = reduce(source.to_vec(), scope, vars);

                    let (can_b, mut b) = if bound.len() > 0 {
                        let mut inner_scope = scope.clone();
                        inner_scope.insert(bound.clone(), (source.to_vec(), None));

                        assert![typecheck(&target, &["typ".to_string()], &inner_scope, vars), "2nd argument of `>{}` must be a type", bound];

                        reduce(target, &inner_scope, vars)

                    } else {
                        assert![typecheck(&target, &["typ".to_string()], scope, vars), "2nd argument of `>{}` must be a function", bound];

                        reduce(target, scope, vars)
                    };

                    can_reduce_more |= can_a || can_b;

                    shift_right(&mut a, 1);
                    shift_right(&mut b, 1);

                    ret.extend(a);
                    ret.extend(b);
                    ret.push(format!(">{}", bound));

                } else {
                    panic!["syntax error: `>{}` requires two parameters", bound]
                }
            },

            [raw_args @ .., func] => {
                if let Some(ty) = vars.get(func) {// TODO: Typecheck?
                    ret.extend(elem.to_vec());

                    continue;
                }

                let (ty, val) = scope.get(func).unwrap();

                let mut args = vec![];

                // Reduce arguments
                //
                for raw_arg in data::split_by_lvl(raw_args, 1) {
                    let mut raw_arg = raw_arg.to_vec();
                    shift_left(&mut raw_arg, 1);

                    let (more, mut arg) = reduce(raw_arg, scope, vars);

                    can_reduce_more |= more;
                    shift_right(&mut arg, 1);

                    args.push(arg);
                }

                if let Some(lambda) = val {
                    let ty_bound = &ty.last().unwrap()[1..];// TODO: Check result type?

                    let (mut source, mut target) = if let [source, target] = &data::split_by_lvl(ty, 1)[..] { (source.to_vec(), target.to_vec()) } else {
                        unreachable!["invalid function type syntax"]
                    };

                    shift_left(&mut source, 1);
                    shift_left(&mut target, 1);

                    let mut arg = args.pop().unwrap();// NOTE: Arguments are ordered bottom->up, that is `args.last()` is the first argument.
                    shift_left(&mut arg, 1);

                    assert![typecheck(&arg, &source, scope, vars), "argument doesn't match lambda's domain"];

                    if let [rest @ .., head] = &lambda[..] {
                        if &head[0..=0] == "<" {
                            let bound = head[1..].to_string();

                            let mut body = vec![];

                            let bound_ty = if let [raw_body @ .., bound_ty] = &data::split_by_lvl(rest, 1)[..] {
                                for item in raw_body {
                                    body.extend(item.into_iter().cloned());
                                }

                                bound_ty.to_vec()

                            } else { unreachable!["invalid lambda syntax"] };

                            shift_left(&mut body, 1);

                            let mut inner_scope = scope.clone();
                            inner_scope.insert(bound, (bound_ty, Some(arg)));

                            let (more, reduced) = reduce(body, &inner_scope, vars);

                            can_reduce_more |= more;
                            ret.extend(reduced);

                            continue;
                        }
                    }

                    // TODO: Typecheck the call?

                    shift_right(&mut arg, 1);

                    for arg in args {
                        ret.extend(arg);
                    }

                    ret.extend(arg);
                    ret.extend(lambda.to_vec());

                } else {
                    for arg in args {
                        ret.extend(arg);
                    }

                    ret.push(func.to_string());
                }
            },

            e => panic!["invalid syntax element: {:?}", e],
        }
    }

    if let Some(repr) = extend_eq_family {
        scope.add_eq(&repr, ret.clone());

    } else if ret.len() > 0 {
        scope.new_eq_class(ret.clone());
        scope.add_eq(&ret, expr);
    }

    (can_reduce_more, ret)
}

/// Reduces the expression `depth`-times, provided it's well-formed and well-typed in `scope`.
/// If `depth == 0`, reductions are performed until the expression cannot be reduced further,
/// or until the counter reaches `usize::MAX`.
///
/// # Panics
/// This function panics when the expression isn't well-formed or well-typed.
///
fn reduce_n_times(expr: Vec<String>, scope: &Env, vars: &mut Vars, mut depth: usize) -> Vec<String> {
    let (mut more, mut ret) = reduce(expr, scope, vars);

    while more && depth != 1 {
        let (new_more, new_ret) = reduce(ret, scope, vars);

        more = new_more;
        ret = new_ret;

        depth = depth.wrapping_sub(1);
    }

    ret
}

fn main() {
    unsafe { CFG = Config::from_args(); }

    let stdin = io::stdin();

    let mut it = stdin.lock().lines().map(|l| l.expect("couldn't read line"));

    let mut scope = Env::new();

    while let Some(line) = it.next() {
        match line.as_ref() {
            "#!show" => {
                let depth: usize = it.next().expect("unexpected EOF").parse().expect(&format!["expected number less than {}", usize::MAX]);

                let mut expr = data::read_expr(&mut it);

                expr = reduce_n_times(expr, &scope, &mut HashMap::new(), depth);

                println!["#out\n{}\n", expr.join("\n")];
            },
            "#!declare" => {
                let mut head = data::read_expr(&mut it);

                assert_eq![1, head.len(), "lvalue can be just an identifier"];

                let head = head.pop().unwrap();
                assert![!scope.contains_item(&head), "already declared: {:?}", head];

                let ty = data::read_expr(&mut it);
                assert![well_formed(&ty, &scope), "cannot form type:\n{}\n", ty.join("\n")];

                if unsafe { CFG.verbose } {
                    println!["#declared\n{}\n", head]
                }

                scope.insert(head, (ty, None));
            },
            "#!define" => {
                let mut lhs = data::read_expr(&mut it);

                if lhs.len() == 1 {
                    let head = lhs.pop().unwrap();

                    assert![scope.contains_item(&head), "not declared: {:?}", head];
                    assert_eq![None, scope.get(&head).unwrap().1, "already defined: {:?}", head];

                    let expr = data::read_expr(&mut it);

                    assert![well_formed(&expr, &scope), "cannot form expression:\n{}\n", expr.join("\n")];

                    let ty = &scope.get(&head).unwrap().0;

                    assert![typecheck(&expr, ty, &scope, &mut HashMap::new()), "value doesn't conform to the corresponding type: {:?}", head];

                    scope.get_mut(&head).unwrap().1 = Some(expr);

                    if unsafe { CFG.verbose } {
                        println!["#defined\n{}\n", head]
                    }

                } else {
                    assert![well_formed(&lhs, &scope), "LHS isn't well-formed"];

                    let mut vars = HashMap::new();

                    assert![typecheck(&lhs, &[], &scope, &mut vars), "LHS isn't well-typed"];

                    let rhs = data::read_expr(&mut it);

                    assert![well_formed(&rhs, &scope), "RHS isn't well-formed"];
                    assert![typecheck(&rhs, &[], &scope, &mut vars), "RHS isn't well-typed"];

                    scope.new_eq_class(lhs.clone());
                    scope.add_eq(&lhs, rhs);

                    if unsafe { CFG.verbose } {
                        println!["#defined\n{}\n", lhs.join("\n")]
                    }
                }
            },

            "??" => {
                let expr = data::read_expr(&mut it);
                let ty = data::read_expr(&mut it);

                let mut vars = HashMap::new();

                if typecheck(&expr, &ty, &scope, &mut vars) {
                    println!["#y\n{}", vars.len()];

                    for (var, ty) in vars {
                        println!["{}\n{}\n", var, ty.join("\n")];
                    }

                } else {
                    println!["#n"];
                }
            },

            _ => panic!["invalid input: {:?}", line],
        }
    }
}

fn debug<D>(msg: D) where D: std::fmt::Display {
    if let Some("1") = option_env!["KVOK_DEBUG"] {
        eprintln!["DEBUG: {}", msg]
    }
}

#[cfg(test)]
mod well_formedness {
    use super::*;

    #[test]
    fn wellformed() {
        let src: &[String] = &[
                "\t\ttyp".into(),
            "\ttyp".into(),
                "\t\ttyp".into(),
            "\ttyp".into(),
            "\ttyp".into(),
        "typ".into(),
        ];

        assert![well_formed(src, &Env::new()), "isn't well-formed"]
    }

    #[test]
    fn not_wellformed_in_func_1() {
        let src: &[String] = &[
                "\t\ttyp".into(),
            "\ttyp".into(),
                "\t\ttyp".into(),
            "\ttyp".into(),
            "\ttyp".into(),
        "a".into(),
        ];

        assert![!well_formed(src, &Env::new()), "isn't well-formed"]
    }

    #[test]
    fn not_wellformed_in_func_2() {
        let src: &[String] = &[
                "\t\ttyp".into(),
            "\ttyp".into(),
                "\t\ttyp".into(),
            "\ta".into(),
            "\ttyp".into(),
        "typ".into(),
        ];

        assert![!well_formed(src, &Env::new()), "isn't well-formed"]
    }

    #[test]
    fn not_wellformed_in_arg() {
        let src: &[String] = &[
                "\t\tb".into(),
            "\ttyp".into(),
                "\t\ttyp".into(),
            "\ta".into(),
            "\ttyp".into(),
        "typ".into(),
        ];

        assert![!well_formed(src, &Env::new()), "isn't well-formed"]
    }
}
