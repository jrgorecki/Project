(* File Project/Env.fs
 *)

module Env

(* Environment operations *)

type 'v env = (string * 'v) list

let rec lookup env x =
    match env with 
    | []          -> failwith (x + " not found in environment")
    | (y, v) :: r -> if x = y then v else lookup r x
