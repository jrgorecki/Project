(* File Project/Inter.fs
*)

module Inter

open Absyn
open Env


(* A runtime value is an integer, a list, or a function closure *)

type value = 
  | Int of int
  | List of value list
  | Closure of string option * string * expr * value env   

let rec toString v t = 
  match (v, t) with
  | (_, AnyT)          -> "value" 
  | (_, ArrowT (_, _)) -> "closure"  
  | (_, UnitT)         -> "null"
  | (Int i, IntT)      -> string i
  | (Int 0, BoolT)     -> "false"
  | (Int 1, BoolT)     -> "true"
  | (List l, ListT t1) -> "[" + listToString l t1 + "]"
  | _ ->  failwith "toString: mismatched type and value"
and listToString l t =
  match l with
  |      [] -> ""
  | v :: [] -> toString v t
  | v :: vs -> (toString v t) + "; " + (listToString vs t)
  
let rec lookup env x =
    match env with 
    | []          -> failwith (x + " not found in environment")
    | (y, v) :: r -> if x = y then v else lookup r x

let test : bool -> value = function
    | false -> Int 0
    | _ ->  Int 1

let set : value -> bool = function
    | Int 0 -> false
    | _ -> true

let stripint : value -> int = function
    | Int v -> v
    | _ -> failwith "Cannot strip non-value type."

let rec eval : expr -> value env -> value = function
    | Con v, t -> t |> function
        | IntT | BoolT | UnitT 
            -> fun _ -> Int v
        | _ -> failwith "Invalid constant value type."
    | Op1("print", e), t -> fun env -> (eval e env, t) |> function
        | Int v, IntT   -> printfn "%i" v; Int 0
        | v, BoolT      -> printfn "%b" (set v); Int 0
        | _, UnitT      -> printfn "()"; Int 0
        | _ -> failwith "Invalid print value."    
    | e, _ -> e |> function
        | EListC
            -> fun _ -> List []
        | Var x
            -> fun env -> lookup env x 
        | Op2(op, e1, e2) -> fun env -> 
            let rec oper = function
                | Int v1, Int v2 -> op |> function
                    | "+"   -> Int (v1 + v2)
                    | "-"   -> Int (v1 - v2)
                    | "*"   -> Int (v1 * v2)
                    | "/" when v2 = 0
                            -> failwith "Division by zero."
                    | "/"   -> Int  (v1  / v2)
                    | "<"   -> test (v1  < v2) 
                    | "<="  -> test (v1 <= v2)
                    | "="   -> test (v1  = v2)
                    | "<>"  -> test (v1 <> v2)
                    | _ -> failwith "Invalid binary arithmetic operation"
                | List s1, List s2 -> op |> function
                    | "="   -> test (List.forall2 
                                (fun v1 v2 -> v1 = v2) 
                                (List.map stripint s1) 
                                (List.map stripint s2))
                    | "<>"  -> test (List.forall2 
                                (fun v1 v2 -> v1 <> v2)
                                (List.map stripint s1)
                                (List.map stripint s2))
                    | _ -> failwith "Invalid binary list operation"
                | Int hd, List tl -> op |> function
                    | "::"  -> List (Int hd :: tl)
                    | _ -> failwith "Invalid binary mixed type operation"
                | _ -> failwith "Invalid binary operation."
            oper (eval e1 env, eval e2 env)
        | If(pe, e1, e2) -> fun env -> eval pe env |> function
            | Int 0 -> eval e2 env
            | _     -> eval e1 env
        | Let(b, e) -> fun env -> b |> function
            | V(s, be) 
                -> eval e ((s, eval be env) :: env)
            | F(s, (x, _), _, e)
                -> Closure(Some s, x, e, env)
        | Lam((x, _), e)
            -> fun env -> Closure(None, x, e, env)
        | Call(e1, e2) -> fun env -> eval e1 env |> function
            | Closure(_, x, e, env) 
                -> eval e ((x, eval e2 env) :: env)
            | _ -> failwith "Invalid call."
        | Op1(op, e) -> fun env ->
            let rec oper e = e |> function
                | Int v -> op |> function
                    | "not"      -> test (not (set e))
                    | _ -> failwith "Invalid unary value operation."
                | List v -> v |> function
                    | h :: t -> op |> function
                        | "hd"  -> h
                        | "tl"  -> List t
                        | "ise" -> test (List.forall 
                                    (fun v -> v = h) 
                                    (h :: t))
                        | _ -> failwith "Invalid unary operation on list."
                    | [] -> failwith "Unary operation on empty list."
                | _ -> failwith "Invalid unary operation."
            oper (eval e env)
        | _ -> failwith "Invalid expression."
      


