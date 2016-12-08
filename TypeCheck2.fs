module TypeCheck2

open Absyn

type 'v env = (string * 'v) list

let rec lookup env x =
    match env with 
    | []          -> failwith (x + " not found in environment")
    | (y, v) :: r -> if x = y then v else lookup r x

let rec check : expr -> expr = function
    | Con(_), AnyT
    | EListC, AnyT
    | Let(F(_,_,_,_), _), AnyT
    | Let(F(_, _, AnyT, _), _), _
    | Let(F(_, (_, AnyT), _, _), _), _
    | Lam((_, AnyT), _), _
        -> failwith "Cannot infer the type of a recursive function, lambda binding, or constant."
    | Let(b, e), t -> (check e) |> function
        | 
        
and assign : expr -> expr = function
    | _ -> Con(1), AnyT
