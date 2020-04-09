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
 | TCall of func * expr list
type pred =
 | TBool of bool
 | TGeq of expr * expr
 | TGt of expr * expr
 | TEq of expr * expr
 | TAnd of pred * pred
 | TOr of pred * pred
 | TNot of pred
type stm =
 | TExpr of expr
 | TPlus of pred * stm * pred * stm
type functions = func * var list * stm
type program = functions list

val pp_program: (var * var list * stm) list -> var
