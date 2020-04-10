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

val pp_types: (var * var list * typ) list -> var
