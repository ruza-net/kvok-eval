// [AREA] Expression Operations
//
//- [AREA] Levels
//-
pub fn count_lvl(expr: &str) -> usize {
    let mut count = 0;

    for c in expr.chars() {
        if c != '\t' {
            break;
        }

        count += 1;
    }

    count
}

pub fn max_lvl(expr: &[String]) -> Option<usize> {
    expr.iter().map(|e| count_lvl(e)).max()
}

pub fn shift_right(expr: &mut [String], n: usize) {
    for line in expr {
        *line = format!["{}{}", "\t".repeat(n), line];
    }
}

pub fn shift_left(expr: &mut [String], n: usize) {
    for line in expr {
        assert_eq![line.chars().take(n).collect::<Vec<_>>(), ['\t'].repeat(n), "expression isn't sufficiently indented"];

        *line = line.chars().skip(n).collect();
    }
}

pub fn into_parts(expr: &str) -> (usize, &str) {
    let lvl = count_lvl(expr);

    (lvl, &expr[lvl..])
}
//-
//- [END] Levels

//- [AREA] Substitutions
//-
pub fn contains_var(expr: &[String], name: &str) -> bool {
    let mut found = false;
    let mut found_lvl = 0;

    for line in expr {
        let (lvl, line) = into_parts(line);

        if line == name {
            found = true;
            found_lvl = lvl;

        } else if found && line == &format!(">{}", name) && found_lvl >= lvl {
            found = false;

        } else if found && line == &format!("<{}", name) && found_lvl >= lvl {
            found = false;
        }
    }

    found
}

pub fn subst(expr: &mut [String], old: &str, new: String) {
    for line in expr {
        let (lvl, princ) = into_parts(line);

        if princ == old {
            *line = format!("{}{}", "\t".repeat(lvl), new);
        }
    }
}

// pub fn freshen(expr: &[String], scope: &Scope) -> Vec<String> {
//     let elems = split_by_lvl(expr, 0);
//
//     let mut ret = vec![];
//
//     for elem in elems {
//         match &elem[..] {
//             [x] => {
//                 ret.push(x.to_string());
//             },
//
//             [body @ .., head] if &head[0..=0] == "<" => {
//                 unimplemented!()
//             },
//             [body @ .., head] if &head[0..=0] == ">" => {
//                 let mut bound = head[1..].to_string();
//
//                 if scope.contains_item(&bound) {
//                     eprintln!("{}", bound);
//                     bound = scope.gen_fresh(bound);
//                     eprintln!("{}", bound);
//                 }
//
//                 if let [source, target] = &split_by_lvl(&body, 1)[..] {
//                     let mut source = source.to_vec();
//                     let mut target = target.to_vec();
//
//                     shift_left(&mut source, 1);
//                     shift_left(&mut target, 1);
//
//                     source = freshen(&source, scope);
//
//                     if bound.len() > 0 {
//                         let mut inner_scope = scope.clone();
//                         inner_scope.insert(bound.to_string(), (source.clone(), None));
//
//                         target = freshen(&target, &inner_scope);
//                     }
//
//                     shift_right(&mut source, 1);
//                     shift_right(&mut target, 1);
//
//                     ret.extend(source);
//                     ret.extend(target);
//                     ret.push(format!(">{}", bound));
//
//                 } else {
//                     panic!["syntax error: `>{}` requires two parameters", bound]
//                 }
//             },
//
//             [args @ .., func] => {
//                 unimplemented!()
//             },
//
//             e => panic!["invalid syntax element: {:?}", e],
//         }
//     }
//     // eprintln!("FRESHENED\n{:#?}\n\n", ret);
//     ret
// }

//-
//- [END] Substitutions
//
// [END] Expression Operations

pub fn read_expr<I: Iterator<Item=String>>(it: &mut I) -> Vec<String> {
    let mut ret = vec![];

    while let Some(line) = it.next() {
        if line == "" {
            break;
        }

        ret.push(line);
    }

    ret
}

// [AREA] AST Transformations
//
pub fn split_by_lvl(expr: &[String], lvl: usize) -> Vec<&[String]> {
    let mut start = 0;
    let mut ret = vec![];

    for i in 0..expr.len() {
        let curr_lvl = count_lvl(&expr[i]);

        if curr_lvl == lvl {
            ret.push(&expr[start..=i]);

            start = i + 1;

        } else if curr_lvl < lvl {
            start = i + 1;
        }
    }

    ret
}

pub fn recurse<X, D>(
    expr: &[String],
    data: D,
    default: X,
    on_singleton: fn(D, &str) -> X,
    on_lambda: fn(D, &str, &[String], &[String]) -> X,
    on_func_ty: fn(D, &str, &[String], &[String]) -> X,
    on_call: fn(D, &[Vec<String>], &str) -> X,
) -> X where X: PartialEq, D: Copy {

    let elems = split_by_lvl(expr, 0);

    for elem in elems {
        match &elem[..] {
            [x] => {
                let ret = on_singleton(data, x);

                if default != ret {
                    return ret;
                }
            },

            [body @ .., head] if &head[0..=0] == "<" => {
                let mut body = body.to_vec();

                shift_left(&mut body, 1);
                let bound = &head[1..];

                if let [.., bound_ty] = split_by_lvl(&body, 0)[..] {
                    // NOTE: Permits empty lambda body.
                    //
                    let ret = on_lambda(data, bound, bound_ty, &body[..body.len() - bound_ty.len()]);

                    if default != ret {
                        return ret;
                    }

                } else {
                    panic!["syntax error: `<{}` requires at least 2 parameters", bound]
                }
            },
            [body @ .., head] if &head[0..=0] == ">" => {
                let bound = &head[1..];

                if let [source, target] = split_by_lvl(&body, 1)[..] {
                    let mut source = source.to_vec();
                    let mut target = target.to_vec();

                    shift_left(&mut source, 1);
                    shift_left(&mut target, 1);

                    let ret = on_func_ty(data, bound, &source, &target);

                    if default != ret {
                        return ret;
                    }

                } else {
                    panic!["syntax error: `>{}` requires 2 parameters", bound]
                }
            },

            [raw_args @ .., func] => {
                let mut args: Vec<_> = split_by_lvl(raw_args, 1).into_iter().map(|arg| arg.to_vec()).collect();

                for ref mut arg in args.iter_mut() {
                    shift_left(arg, 1);
                }

                let ret = on_call(data, &args, func);

                if default != ret {
                    return ret;
                }
            },

            e => panic!["invalid syntax element: {:?}", e],
        }
    }

    default
}
//
// [END] AST Transformations