type var = string (* Prolog style *)
type func = string (* Prolog style *)
type rat = int (* should be rational *)

(* Head::= Name | Name(Arguments)              *)
(* Arguments ::= Variable | Variable,Arguments *)
type call = func * var list

(* Oper ::=  >= | <= | = | < | > *)
type oper = Geq | Leq | Eq | Lt | Gt

(* LinearExpression ::= Variable | RationalNumber | 
                 LinearExpression + LinearExpression |
                 LinearExpression - LinearExpression |
                 RationalNumber   * LinearExpression |
                 LinearExpression / RationalNumber              *)

type expr = 
   Var of var
 | Rat of rat
 | Plus of expr * expr
 | Minus of expr * expr
 | Mult of rat * expr
 | Div of expr * rat

(* SizeRelation ::= Variable Oper LinearExpression *)
type pred = var * oper * expr

(* Equation::= eq(Head, CostExpression, ListOfCalls, ListOfSizeRelations). *)
(* CostExpression :: = LinearExpression | nat(LinearExpression) *)
(* ListOfCalls ::= [] |[Head|ListOfCalls] *)
(* ListOfSizeRelations ::= [] | [SizeRelation|ListOfSizeRelations] *)
type eqn = call * (*to_nat:*)bool * expr * call list * pred list

type prog = eqn list

let pp_var v = String.capitalize_ascii v

let pp_func f = String.uncapitalize_ascii f

let pp_rat = string_of_int

let pp_call (f,vl) =
 pp_func f ^ "(" ^ String.concat "," (List.map pp_var vl) ^ ")"

let pp_oper =
 function
    Geq -> ">="
  | Leq -> "<="
  | Eq -> "="
  | Lt -> "<"
  | Gt -> ">"

let parens s = "(" ^ s ^ ")"

let rec pp_expr = 
 function
    Var v -> pp_var v
  | Rat r -> pp_rat r
  | Plus(e1,e2) -> parens (pp_expr e1 ^ " + " ^ pp_expr e2)
  | Minus(e1,e2) -> parens (pp_expr e1 ^ " - " ^ pp_expr e2)
  | Mult(e1,e2) -> parens (pp_rat e1 ^ " * " ^ pp_expr e2)
  | Div(e1,e2) -> parens (pp_expr e1 ^ " / " ^ pp_rat e2)

let pp_pred (v,o,e) = pp_var v ^ " " ^ pp_oper o ^ " " ^ pp_expr e

(* Equation::= eq(Head, CostExpression, ListOfCalls, ListOfSizeRelations). *)
(* CostExpression :: = LinearExpression | nat(LinearExpression) *)
(* ListOfCalls ::= [] |[Head|ListOfCalls] *)
(* ListOfSizeRelations ::= [] | [SizeRelation|ListOfSizeRelations] *)
let pp_eqn (call,to_nat,e,cl,pl) =
 "eq(" ^ pp_call call ^ "," ^
   ((if to_nat then (fun x -> "nat" ^ parens x) else fun x -> x) (pp_expr e)) ^
   "," ^ "[" ^ String.concat "," (List.map pp_call cl) ^ "]," ^
   "[" ^ String.concat "," (List.map pp_pred pl) ^ "])."

let pp_prog l = String.concat "\n" (List.map pp_eqn l)
