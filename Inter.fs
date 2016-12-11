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


(*eval, takes an expression and an environment and returns a value corresponding to the desired behavior of the expr*)
let rec eval (expr:expr) env = 
    match expr with
    | (Op1("not", e ), BoolT) -> let v = eval e env in match v with
                                                        | Int 0 -> Int 1
                                                        | Int _ -> Int 0
                                                        | _ -> failwith "improper usage of 'not'"
    | (Op1("hd", e), t ) -> let v = eval e env in match v with
                                                        | List(h::t) -> h
                                                        | _ -> failwith "improper usage of 'hd'"
    | (Op1("tl", e), ListT(_)) -> let v = eval e env in match v with 
                                                        | List(h::t) ->List( t )
                                                        | List [] -> List []
                                                        | _ -> failwith "tl: not a list" 
    | (Op1("ise", e), BoolT) -> let v = eval e env in match v with 
                                                        | List [] -> Int 1
                                                        | List _ -> Int 0
    | (Op1("print", (e1, typ)), UnitT) -> let v = eval (e1, typ) env in printf(toString v typ)
    | (Op2("+", e1, e2), _) -> let (v1, v2) = (eval e1 env, eval e2 env) in match (v1,v2) with
                                                                                | (Int i1, Int i2) -> Int i1+i2
                                                                                | _ -> failwith "improper vals for addittion"
    | (Op2("-", e1, e2), _) -> let (v1, v2) =  (eval e1 env, eval e2 env) in match (v1,v2) with
                                                                                | (Int i1, Int i2) -> Int i1-i2
                                                                                | _ -> failwith "improper vals for subtraction"
    | (Op2("*", e1, e2), _) -> let (v1, v2) =  (eval e1 env, eval e2 env) in match (v1,v2) with
                                                                                | (Int i1, Int i2) -> Int i1*i2
                                                                                | _ -> failwith "improper vals for multiplication"
    | (Op2("/", e1, e2), _) -> let (v1, v2) =  (eval e1 env, eval e2 env) in match (v1,v2) with
                                                                                | (_, Int 0) -> failwith "Error: divide by zero"
                                                                                | (Int i1, Int i2) -> Int i1/i2
                                                                                | _ -> failwith "improper vals for multiplication"
    | (Op2("=", e1, e2), _) -> let (v1, v2) = (eval e1 env, eval e2 env) in if v1 = v2 then Int 1 else Int 0
    | (Op2("<>", e1, e2), _) -> let (v1, v2) = (eval e1 env, eval e2 env) in if v1 <> v2 then Int 1 else Int 0
    | (Op2("<", e1, e2), _) -> let (v1, v2) = (eval e1 env, eval e2 env) in match (v1,v2) with 
                                                                                | (Int i1, Int i2) -> if i1<i2 then Int 1 else Int 0
                                                                                | _ -> failwith "LessThan: not two ints"
    | (Op2("<=", e1, e2), _) -> let (v1, v2) = (eval e1 env, eval e2 env) in match (v1,v2) with 
                                                                                | (Int i1, Int i2) -> if i1<=i2 then Int 1 else Int 0
                                                                                | _ -> failwith "LessThanOrEqual: not two int"
    | (Op2("::", e1, e2), _) -> let (v1, v2) = (eval (e1, t1) env, eval e2 env) in match (v1, v2) with 
                                                                                        | (v1, List ( l )) ->List( v1::l )//bug: see issue
    | (Op2(";", e1, e2), _) -> eval e1 env ; eval e2 env //not sure about this one
    | (Con(i), _) -> Int i
    | (Var(s), _) -> lookup env s
    | (ElistC, t) -> List([])
    
    //what's left: Call and Let handling