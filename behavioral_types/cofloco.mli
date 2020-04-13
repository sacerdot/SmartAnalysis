type var = string (* Prolog style *)
type func = string (* Prolog style *)
type rat = int (* should be rational *)

type fcall = func * var list
type oper = Geq | Leq | Eq | Lt | Gt

type expr = 
   Var of var
 | Rat of rat
 | Plus of expr * expr
 | Minus of expr * expr
 | Mult of rat * expr
 | Div of expr * rat
 | UMinus of expr

type acall = func * expr list

type pred = expr * oper * expr

type eqn = fcall * (*to_nat:*)bool * expr * acall list * pred list

type prog = eqn list

val pp_prog : prog -> string
