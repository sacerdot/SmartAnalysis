type var = string (* Prolog style *)
type func = string (* Prolog style *)
type rat = int (* should be rational *)

type call = func * var list

type oper = Geq | Leq | Eq | Lt | Gt

type expr = 
   Var of var
 | Rat of rat
 | Plus of expr * expr
 | Minus of expr * expr
 | Mult of rat * expr
 | Div of expr * rat

type pred = var * oper * expr

type eqn = call * (*to_nat:*)bool * expr * call list * pred list

type prog = eqn list

val pp_prog : prog -> string
