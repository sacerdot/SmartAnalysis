type address = string
type 'a tag =
 Unit : unit tag | Int : int tag | Bool : bool tag | Address : address tag
type _ tag_list =
    TNil : unit tag_list
  | TCons : 'a tag * 'b tag_list -> ('a * 'b) tag_list
type 'a ident = 'a tag * string
type ('a, 'b) meth = 'a tag * 'b tag_list * string
type 'a field = 'a ident
type any_field = AnyField : 'a field -> any_field
type 'a var = 'a ident
type _ expr =
    Var : 'a var -> 'a expr
  | This : address expr
  | Field : 'a field -> 'a expr
  | Plus : int expr * int expr -> int expr
  | Minus : int expr * int expr -> int expr
  | Mult : int expr * int expr -> int expr
  | Div : int expr * int expr -> int expr
  | UMinus : int expr -> int expr
  | Geq : int expr * int expr -> bool expr
  | Gt : int expr * int expr -> bool expr
  | Eq : 'a tag * 'a expr * 'a expr -> bool expr
  | And : bool expr * bool expr -> bool expr
  | Or : bool expr * bool expr -> bool expr
  | Not : bool expr -> bool expr
  | Value : 'a -> 'a expr
  | MsgSender : address expr
  | MsgValue : int expr
  | Balance : address expr -> int expr
type 'a tagged_expr = 'a tag * 'a expr
type _ var_list =
    VNil : unit var_list
  | VCons : 'a var * 'b var_list -> ('a * 'b) var_list
type _ expr_list =
    ENil : unit expr_list
  | ECons : 'a expr * 'b expr_list -> ('a * 'b) expr_list
type _ lhs =
    LField : 'a field -> 'a lhs
  | LVar : 'a var -> 'a lhs
  | LDiscard : unit lhs
type _ rhs =
    Expr : 'a expr -> 'a rhs
  | Call : address expr * ('a, 'b) meth * int expr option *
      'b expr_list -> 'a rhs
type (_, _) stm =
    Epsilon : ('d, [ `Epsilon ]) stm
  | ReturnRhs : 'a rhs -> ('a, 'b) stm
  | Return : (unit, 'b) stm
  | Assign : 'a lhs * 'a rhs * ('b, 'c) stm -> ('b, 'c) stm
  | IfThenElse : bool expr * ('b, [ `Epsilon ]) stm *
      ('b, [ `Epsilon ]) stm * ('b, 'c) stm -> ('b, 'c) stm
  | Revert : ('e, 'f) stm
type ('a, 'b) block =
    Block : 'b var_list * 'c var_list *
      ('a, [ `Return ]) stm -> ('a, 'b) block
type any_method_decl =
    AnyMethodDecl : ('a, 'b) meth * ('a, 'b) block * bool -> any_method_decl
type methods = any_method_decl list
type fields = any_field list
type a_contract =
    AContract : address * methods * (unit, unit) block option *
      fields -> a_contract
type configuration = a_contract list
type (_, _) eq = Refl : ('a, 'a) eq
val eq_tag : 'a tag -> 'b tag -> ('a, 'b) eq option
val eq_tag_list : 'a tag_list -> 'b tag_list -> ('a, 'b) eq option
val tag_of_lhs : 'a lhs -> 'a tag
val expr_list_map :
 < f: 'a. 'a tag -> 'a expr -> 'b > -> 'c tag_list -> 'c expr_list -> 'b list
val tag_list_length : 'a tag_list -> int
val var_list_length : 'a var_list -> int
val expr_list_of_var_list : 'a var_list -> 'a expr_list
val fallback : (unit,unit) meth
val any_method_decl_of_fallback : (unit,unit) block -> any_method_decl
val match_methods :
 this:address -> address expr -> ('a,'b) meth -> bool -> configuration ->
  (address * any_method_decl) list
val pp_tag : 'a tag -> string
val pp_ident : 'a tag * string -> string
val pp_var : 'a tag * string -> string
val pp_var_list : 'a var_list -> string list
val pp_address : address -> string
val pp_value : 'a tag -> 'a -> string
val pp_field : 'a tag * string -> string
val pp_expr : 'a tag -> 'a expr -> string
val pp_tagged_expr : 'a tag * 'a expr -> string
val pp_expr_list : 'a tag_list -> 'a expr_list -> string list
val pp_tag_list : 'a tag_list -> string list
val pp_meth : ?verbose:bool -> 'a tag * 'b tag_list * string -> string
val pp_lhs : 'a lhs -> string
val pp_rhs : 'a tag -> 'a rhs -> string
val pp_stm : indent:int -> ?breakline:bool -> 'a tag -> ('a, 'b) stm -> string
val pp_any_method_decl: indent:int -> any_method_decl -> address
val pp_a_contract : a_contract -> string
val pp_configuration : configuration -> string

val lookup_method : ('a, 'b) meth -> methods -> ('a, 'b) block
