module TypeCheck

open Absyn

type operator =
    | Cons
    | IsEmpty
    | HeadOf
    | TailOf
    | Print
    | Not
    | IsEqual
    | IsNotEqual
    | Plus
    | Minus
    | Multiply
    | Divide
    | LessThan
    | LessThanOrEqual

let parseop = function
    | "::" -> Cons
    | "ise" -> IsEmpty
    | "hd" -> HeadOf
    | "tl" -> TailOf
    | "print" -> Print
    | "not" -> Not
    | "=" -> IsEqual
    | "<>" -> IsNotEqual
    | "+" -> Plus
    | "-" -> Minus
    | "*" -> Multiply
    | "/" -> Divide
    | "<" -> LessThan
    | "<=" -> LessThanOrEqual
    | _ -> failwith "Bad operator token."

let assigntype = function
    | _ -> AnyT

let hasonefromsets (a, b) sets =
    List.forall (fun (lista, listb) -> 
        List.contains a lista 
        && List.contains b listb) 
        sets

let cando t op = true
     

let rec check : expr -> expr = function
    | e, AnyT -> e, assigntype e
    | e, t -> 
        let cando s = t |> cando (parseop s)
        e |> function 
        | Op1(s, e1) when cando s
            -> Op1(s, check e1), t
        | Op2(s, e1, e2) when cando s
            -> Op2(s, check e1, check e2), t
        | If((e1, BoolT), e2, e3)
          when t = BoolT -> (check e2, check e3) |> function
            | (ce2, ct2), (ce3, ct3) when ct2 = ct3
                -> If((e1, BoolT), (ce2, ct2), (ce3, ct3)), t
            | _ -> failwith "Branch type mismatch."
        | Let(b, e) -> (check e) |> function
            | ce, ct when t = ct
                -> Let(b, (ce, ct)), t
            | _ -> failwith "Binding type mismatch."
        | Lam((s, bt), e) -> 
            let rec checkbinding = function
                | Var(s), t when t <> bt
                    -> failwith "Lambda variable bound to incorrect type."
                | Op1(_, e), _ | Let(_, e), _ | Lam(_, e), _
                    -> checkbinding e
                | Op2(_, e1, e2), _ | Call(e1, e2), _
                    -> checkbinding e1
                    && checkbinding e2
                | If(e1, e2, e3), _
                    -> checkbinding e1
                    && checkbinding e2
                    && checkbinding e3
                | _ -> true
            (check e) |> function
            | ce, ct when t <> ct || not (checkbinding e)
                -> failwith "Malformed lambda expression types."
            | ce, ct -> Lam((s, bt), (ce, ct)), t
        | Call(e1, e2) -> (check e1, check e2) |> function
            | (ce1, ArrowT(it, ot)), (ce2, ct2)
                when ct2 <> it || t <> ot
                -> failwith "Malformed call types."
            | ce1, ce2 -> Call(ce1, ce2), t 
        | e -> e, t


