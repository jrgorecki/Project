module TypeCheck

open Absyn
open Env

let rec check e : expr = 
    let rec check : expr * (htype env) -> expr = function
        | (Con(_), AnyT), _
        | (EListC, AnyT), _
        | (Let(F(_,_,_,_), _), AnyT), _
        | (Let(F(_, _, AnyT, _), _), _), _
        | (Let(F(_, (_, AnyT), _, _), _), _), _
        | (Lam((_, AnyT), _), _), _
            -> failwith "Cannot infer the type of a recursive function, lambda binding, or constant."
        | (Op2("::", (he, ht), (te, tt)), ListT(lt)), env 
            -> (check ((he, ht), env), check ((te, tt), env)) |> function
            | (_, ht), (_, tt)
              when (ht <> tt) || (tt <> lt)
                -> failwith "Different list element types are not allowed."
            | (he, ht), (te, tt) 
                -> Op2("::", (he, ht), (te, tt)), lt
        | (Let(b, e2), t), env 
            -> b |> function
            | V(x, e1) 
                -> check (e1, env) |> function
                | _, AnyT -> failwith ("Cannot bind value variable " + x + "as type of AnyT.")
                | e1, t1
                    -> check (e2, (x, t1) :: env) |> function
                    | e2, t2
                        -> Let(V(x, (e1, t1)), (e2, t2)), t2
            | F(f, (x, xt), ft, e1)
                -> check (e1, (f, ArrowT(xt, ft)) :: (x, xt) :: env) |> function
                | e1, t1
                  when t1 = ft && t = ArrowT(xt, ft) 
                    -> check(e2, (f, ArrowT(xt, ft)) :: env) |> function
                    | _, AnyT
                        -> failwith ("Cannot bind function variable " + x + "as type of AnyT.")
                    | e2, t2
                        -> Let(F(f, (x, xt), ft, (e1, t1)), (e2, t2)), t
                | _ -> failwith "Function binding expression is incorrectly typed."
        | (Lam((x, xt), e), t), env
            -> check (e, (x, xt) :: env) |> function
            | ce, ct
              when t = ArrowT(xt, ct)
                -> Lam((x, xt), e), t
            | _ -> failwith "Lambda expression is incorrectly typed."
        | (Call(e2, e1), t), env
            -> (check (e2, env), check (e1, env)) |> function
            | (e2, ArrowT(st, rt)), (e1, t1)
              when t1 = st && t = rt
                -> Call((e2, ArrowT(st, rt)), (e1, t1)), t
            | _ -> failwith "Call expression is incorrectly typed."
        | (If(e, e1, e2), t), env
            -> (check (e, env), check (e1, env), check (e2, env)) |> function
            | (e, BoolT), (e1, t1), (e2, t2)
              when t = t1 && t1 = t2
                -> If((e, BoolT), (e1, t1), (e2, t2)), t
            | _ -> failwith "Conditional expression is incorrectly typed."
        | (Op1("not", e), BoolT), env
            -> check (e, env) |> function
            | ce, BoolT
                -> Op1("not", (ce, BoolT)), BoolT
            | _ -> failwith "Conditional expression is incorrectly typed."
        | (Op1("hd", e), ListT(lt)), env
            -> check (e, env) |> function
            | ce, ct
              when ct = lt
                -> Op1("hd", e), ListT(lt)
            | _ -> failwith "List head application is incorrectly typed."
        | (Op1("tl", e), ListT(lt)), env
            -> check (e, env) |> function
            | ce, ct
              when ct = lt
                -> Op1("tl", e), ListT(lt)
            | _ -> failwith "List tail application is incorrectly typed."
        | (Op1("ise", e), BoolT), env
            -> check (e, env) |> function
            | ce, ListT(ct)
                -> Op1("ise", (ce, ListT(ct))), BoolT
            | _ -> failwith "List equality application is incorrectly typed."
        | (Op1("print", e), UnitT), env
            -> Op1("print", check (e, env)), UnitT
        | (Op2(s, e1, e2), IntT), env
          when s = "+" || s = "-" || s = "*" || s = "/"
            -> (check (e1, env), check (e2, env)) |> function
            | (e1, IntT), (e2, IntT)
                -> Op2(s, (e1, IntT), (e2, IntT)), IntT
            | _ -> failwith "Arithmetic application is incorrectly typed."
        | (Op2(s, e1, e2), BoolT), env
          when s = "<" || s = "<="
            -> (check (e1, env), check (e2, env)) |> function
            | (e1, IntT), (e2, IntT)
                -> Op2(s, (e1, IntT), (e2, IntT)), BoolT
            | _ -> failwith "Range application is incorrectly typed."
        | (Op2(s, e1, e2), BoolT), env
          when s = "=" || s = "<>"
            -> (check (e1, env), check (e2, env)) |> function
            | (e1, t1), (e2, t2)
              when t1 = t2
              && List.contains t1 
                [ BoolT; IntT; UnitT; 
                  ListT(BoolT); 
                  ListT(IntT);
                  ListT(UnitT); ]
                -> Op2(s, (e1, t1), (e2, t2)), BoolT    
            | _ -> failwith "Equality application is incorrectly typed."
        | (Op2(";", e1, e2), t), env
            -> (check (e1, env), check (e2, env)) |> function
            | e1, (e2, t2)
              when t = t2
                -> Op2(";", e1, (e2, t2)), t
            | _ -> failwith "Side effect operation is incorrectly typed."
        | (EListC, t), env
            -> EListC, t
        | (Var(x), _), env
            -> Var(x), lookup env x
        | (Con(v), t), _
            -> Con(v), t
        | _ -> failwith "Expression is malformed."
    check (e, [])


 
