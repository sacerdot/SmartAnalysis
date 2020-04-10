type func = string
type var = string
type expr =
 | TInt of int
 | TVar of var
 | TPlus of expr * expr
 | TMinus of expr * expr
 | TMult of expr * expr
 | TDiv of expr * expr
 | TUMinus of expr
type pred =
 | TBool of bool
 | TGeq of expr * expr
 | TGt of expr * expr
 | TEq of expr * expr
 | TAnd of pred * pred
 | TOr of pred * pred
 | TNot of pred
type typ =
 | TGamma of expr list
 | TCall of func * expr list
 | TPlus of pred * typ * pred * typ
type functions = func * var list * typ
type types = functions list

let rec pp_expr =
 function
  | TInt n -> string_of_int n
  | TVar v -> v
  | TPlus(e1,e2) -> "(" ^ pp_expr e1 ^ " + " ^ pp_expr e2 ^ ")"
  | TMinus(e1,e2) -> "(" ^ pp_expr e1 ^ " - " ^ pp_expr e2 ^ ")"
  | TMult(e1,e2) -> "(" ^ pp_expr e1 ^ " * " ^ pp_expr e2 ^ ")"
  | TDiv(e1,e2) -> "(" ^ pp_expr e1 ^ " / " ^ pp_expr e2 ^ ")"
  | TUMinus e -> "-" ^ pp_expr e

let rec pp_pred =
 function
  | TBool b -> string_of_bool b
  | TGeq(e1,e2) -> "(" ^ pp_expr e1 ^ " >= " ^ pp_expr e2 ^ ")"
  | TGt(e1,e2) -> "(" ^ pp_expr e1 ^ " > " ^ pp_expr e2 ^ ")"
  | TEq(e1,e2) -> "(" ^ pp_expr e1 ^ " = " ^ pp_expr e2 ^ ")"
  | TAnd(e1,e2) -> "(" ^ pp_pred e1 ^ " && " ^ pp_pred e2 ^ ")"
  | TOr(e1,e2) -> "(" ^ pp_pred e1 ^ " || " ^ pp_pred e2 ^ ")"
  | TNot p -> "!" ^ pp_pred p

let mk_indent n = String.make (3 * n) ' '

let rec pp_stm ~indent s =
 mk_indent indent ^
 match s with
    TGamma l -> String.concat "," (List.map pp_expr l)
  | TCall(f,l) -> f ^ "(" ^ String.concat "," (List.map pp_expr l) ^ ")"
  | TPlus(p1,s1,p2,s2) ->
      "  [" ^ pp_pred p1 ^ "]\n" ^ pp_stm ~indent:(indent+2) s1 ^ "\n" ^
      mk_indent indent ^
      "+ [" ^ pp_pred p2 ^ "]\n" ^ pp_stm ~indent:(indent+2) s2

let pp_function (f,params,stm) =
 f ^ "(" ^ String.concat "," params ^ ") =\n" ^ (pp_stm ~indent:1) stm

let pp_types l =
 String.concat "\n"
  (List.map pp_function l)
