module TypeCheck

open Absyn
open Env

let rec check e : expr = 
    printfn "%A" e
    let rec check : expr * (htype env) -> expr = 
        fun (e, env)
            -> printfn "%A" env; printfn "%A" e; (e, env) |> function
        | (Con(_), AnyT), _
        | (EListC, AnyT), _
        // | (Let(F(_,_,_,_), _), AnyT), _
        | (Let(F(_, _, AnyT, _), _), _), _
        | (Let(F(_, (_, AnyT), _, _), _), _), _
        | (Lam((_, AnyT), _), _), _
            -> failwith "Cannot infer the type of a recursive function, lambda binding, or constant."
        | (Op2("::", (he, ht), (te, tt)), lt), env 
            -> (check ((he, ht), env), check ((te, tt), env)) |> function
            | (_, ht), (_, tt)
              when (ListT(ht) <> tt)
                -> printfn "-- %A, %A, %A" ht tt lt; failwith "Different list element types are not allowed."
            | (he, ht), (te, tt) 
                -> printfn "-- cons types: %A, %A, %A" ht tt ListT(lt); Op2("::", (he, ht), (te, tt)), ListT(ht)
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
                  when t1 = ft || ft = AnyT
                    -> check(e2, (f, ArrowT(xt, t1)) :: env) |> function
                    | _, AnyT
                        -> failwith ("Cannot bind function variable " + x + "as type of AnyT.")
                    | e2, t2
                        -> Let(F(f, (x, xt), t1, (e1, t1)), (e2, t2)), ArrowT(xt, t1)
                | _ -> failwith "Function binding expression is incorrectly typed."
        | (Lam((x, xt), e), t), env
            -> check (e, (x, xt) :: env) |> function
            | ce, ct
              when t = ArrowT(xt, ct)
                -> Lam((x, xt), e), t
            | ce, ct
              when t = AnyT
                -> Lam((x, xt), e), ArrowT(xt, ct) 
            | _ -> failwith "Lambda expression is incorrectly typed."
        | (Call(e2, e1), t), env
            -> (check (e2, env), check (e1, env)) |> function
            | (e2, ArrowT(st, rt)), (e1, t1)
              when t1 = st && (t = rt || t = AnyT)
                -> printfn "-- call types 1: %A, %A, %A" st rt t1; Call((e2, ArrowT(st, rt)), (e1, t1)), rt
            | (e2, ArrowT(st, rt)), (e1, t1)
              when t1 = st && t = AnyT
                -> printfn "-- call types 2: %A, %A, %A" st rt t1; Call((e2, ArrowT(st, rt)), (e1, t1)), rt
            | (_, ArrowT(st, rt)), (_, t1) -> printfn "-- %A, %A, %A" st rt t1; failwith "Call expression is incorrectly typed."
            | _ -> failwith "Call expression is incoreectly typed."
        | (If(e, e1, e2), t), env
            -> (check (e, env), check (e1, env), check (e2, env)) |> function
            | (e, BoolT), (e1, t1), (e2, t2)
              when t1 = t2
                -> If((e, BoolT), (e1, t1), (e2, t2)), t1
            | (_, _), (_, t1), (_, t2) -> printfn "-- %A, %A" t1 t2; failwith "Conditional expression is incorrectly typed."
        | (Op1("not", e), BoolT), env
            -> check (e, env) |> function
            | ce, BoolT
                -> Op1("not", (ce, BoolT)), BoolT
            | _ -> failwith "Not expression is incorrectly typed."
        | (Op1("hd", e), lt), env
            -> (check (e, env), lt) |> function
            | (ce, ListT(ct)), AnyT
                -> printfn "-- head type 1: %A" ct; Op1("hd", (ce, ListT(ct))), ct 
            | (ce, ListT(ct)), ListT(ht)
              when ct = ht || ht = AnyT
                -> printfn "-- head type 2: %A" ct; Op1("hd", (ce, ListT(ct))), ct
            | _ -> failwith "List head application is incorrectly typed."
        | (Op1("tl", e), lt), env
            -> (check (e, env), lt) |> function
            | (ce, ListT(ct)), AnyT
                -> printfn "-- tail type 1: %A" ListT(ct); Op1("tl", (ce, ListT(ct))), ListT(ct)
            | (ce, ListT(ct)), ListT(lt)
              when ListT(ct) = ListT(lt) || lt = AnyT
                -> printfn "-- tail type 2: %A" ListT(ct); Op1("tl", (ce, ListT(ct))), ListT(ct)
            | (_, ct), lt -> printfn "%A, %A" ct lt; failwith "List tail application is incorrectly typed."
        | (Op1("ise", e), BoolT), env
            -> check (e, env) |> function
            | ce, ListT(ct)
                -> Op1("ise", (ce, ListT(ct))), BoolT
            | _ -> failwith "List empty application is incorrectly typed."
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
                  -> t1 |> function
                  | BoolT | IntT | UnitT
                  | ListT(BoolT)
                  | ListT(IntT)
                  | ListT(UnitT)
                      -> Op2(s, (e1, t1), (e2, t2)), BoolT    
                  | _ -> failwith "Equality application is incorrectly typed."
            | _ -> failwith "Equality application is incorrectly typed."
        | (Op2(";", e1, e2), t), env
            -> (check (e1, env), check (e2, env)) |> function
            | e1, (e2, t2)
              when t = t2 || t = AnyT
                -> Op2(";", e1, (e2, t2)), t2
            | _ -> failwith "Side effect operation is incorrectly typed."
        | (EListC, t), env
            -> EListC, t
        | (Var(x), _), env
            -> Var(x), lookup env x
        | (Con(v), t), _
            -> Con(v), t
        | _ -> failwith "Expression is malformed."
    check (e, [])


 
