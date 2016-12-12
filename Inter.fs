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