open Lib

type address = int
type 'a tag =
 | Int : int tag
 | Bool : bool tag
 | Address : address tag
type _ tag_list =
 | TNil : unit tag_list
 | TCons : 'a tag * 'b tag_list -> ('a * 'b) tag_list
type 'a ident = 'a tag * string
type ('a,'b) meth = 'a tag * 'b tag_list * string
type 'a field = 'a ident
type any_field =
 | AnyField : _ field -> any_field
type 'a var = 'a ident
type _ expr =
 | Var : 'a var -> 'a expr
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
 | VNil : unit var_list
 | VCons : 'a var * 'b var_list -> ('a * 'b) var_list
type _ expr_list =
 | ENil : unit expr_list
 | ECons : 'a expr * 'b expr_list -> ('a * 'b) expr_list
type _ lhs =
 | LField : 'a field -> 'a lhs
 | LVar : 'a var -> 'a lhs
 | LDiscard : 'a tag -> 'a lhs
type _ rhs =
 | Expr : 'a expr -> 'a rhs
 | Call : address expr * ('a,'b) meth * int expr option * 'b expr_list -> 'a rhs
type (_,_) stm =
 | Epsilon : (_,[`Epsilon]) stm
 | Return : 'a expr -> ('a,[`Return]) stm
 | Assign : 'a lhs * 'a rhs * ('b,'c) stm -> ('b,'c) stm
 | IfThenElse : bool expr * ('b,_) stm * ('b,_) stm * ('b,'c) stm -> ('b,'c) stm
 | Revert : _ stm
type ('a,'b) block =
 Block : 'b var_list * _ var_list * ('a,[`Return]) stm -> ('a,'b) block
type any_method_decl =
 | AnyMethodDecl : ('a,'b) meth * ('a,'b) block * (*payable:*)bool -> any_method_decl
type methods = any_method_decl list
type fields = any_field list
type a_contract =
 AContract : address * methods * (int,unit tag_list) block option * fields -> a_contract
type configuration = a_contract list

(*
## Syntactic differences w.r.t. the paper ##
1. no void returning functions and epsilon used as void:
   we always return 0 instead
2. no transfer function:
   we just call fallback instead

## Syntactic or typing constraints that are not captured ##
1. a function can only invoke fields and variables that exist
*)

type (_,_) eq = Refl : ('a,'a) eq

let eq_tag : type a b. a tag -> b tag -> (a,b) eq option = fun t1 t2 ->
 match t1,t2 with
 | Int, Int -> Some Refl
 | Bool, Bool -> Some Refl
 | Address, Address -> Some Refl
 | _,_ -> None

let rec eq_tag_list : type a b. a tag_list -> b tag_list -> (a,b) eq option =
 fun tl1 tl2 ->
 match tl1,tl2 with
  | TNil,TNil -> Some Refl
  | TCons(t1,tl1),TCons(t2,tl2) ->
     (match eq_tag t1 t2 with
         None -> None
       | Some Refl ->
          match eq_tag_list tl1 tl2 with
             None -> None
           | Some Refl -> Some Refl)
  | _,_ -> None

(*** Utils ***)

let tag_of_lhs =
 function
    LField f -> fst f
  | LVar v -> fst v
  | LDiscard t -> t

(*** Serialization ***)
let pp_tag : type a. a tag -> string =
 function
  | Int -> "int"
  | Bool -> "bool"
  | Address -> "address"
let rec pp_tag_list : type a. a tag_list -> string list =
 function
    TNil -> []
  | TCons(x,tl) -> pp_tag x :: pp_tag_list tl
let pp_ident (t,s) = s ^ ":" ^ pp_tag t
let pp_var = pp_ident
let rec pp_var_list : type a. a var_list -> string list =
 function
    VNil -> []
  | VCons(v,tl) -> pp_var v :: pp_var_list tl
let pp_address : address -> string = string_of_int
let pp_value (type a) (tag : a tag) (v : a) =
 match tag with
    Int -> string_of_int v
  | Bool -> string_of_bool v
  | Address -> pp_address v
let pp_field = pp_ident

let rec pp_expr : type a. a tag -> a expr -> string =
 fun tag ->
 function
  | Var v -> pp_var v
  | This -> "this"
  | Field f -> pp_field f
  | Plus (e1,e2) -> "(" ^ pp_expr tag e1 ^ " + " ^ pp_expr tag e2 ^ ")"
  | Minus (e1,e2) -> "(" ^ pp_expr tag e1 ^ " - " ^ pp_expr tag e2 ^ ")"
  | Mult (c,e) -> "(" ^ pp_expr tag c ^ " * " ^ pp_expr tag e ^ ")"
  | Div (c,e) -> "(" ^ pp_expr tag c ^ " / " ^ pp_expr tag e ^ ")"
  | UMinus e -> "-" ^ pp_expr tag e
  | Geq (e1,e2) -> "(" ^ pp_expr Int e1 ^ " >= " ^ pp_expr Int e2 ^ ")"
  | Gt (e1,e2) -> "(" ^ pp_expr Int e1 ^ " > " ^ pp_expr Int e2 ^ ")"
  | Eq (tag,e1,e2) -> "(" ^ pp_expr tag e1 ^ " = " ^ pp_expr tag e2 ^ ")"
  | And (g1,g2) -> "(" ^ pp_expr tag g1 ^ " /\\\\ " ^ pp_expr tag g2 ^ ")"
  | Or (g1,g2) -> "(" ^ pp_expr tag g1 ^ " \\\\/ " ^ pp_expr tag g2 ^ ")"
  | Not g -> "~" ^ pp_expr tag g
  | Value v -> pp_value tag v
  | MsgSender -> "msg.sender"
  | MsgValue -> "msg.value"
  | Balance e -> pp_expr Address e ^ ".balance"

let rec  pp_tagged_expr e = pp_expr (fst e) (snd e)

let rec pp_expr_list : type a. a tag_list -> a expr_list -> string list = fun tg el ->
 match tg,el with
    TNil,ENil -> []
   | TCons(tag,tagl),ECons(v,tl) -> pp_expr tag v :: pp_expr_list tagl tl

let rec pp_tag_list : type a. a tag_list -> string list =
 function
    TNil -> []
  | TCons(tag,tagl) -> pp_tag tag :: pp_tag_list tagl

let pp_meth (rtag,tags,id) =
 id ^ ":(" ^ String.concat "*" (pp_tag_list tags) ^ " -> " ^ pp_tag rtag ^ ")"

let pp_lhs =
 function
  | LField f -> pp_field f ^ " := "
  | LVar v -> pp_var v ^ " := "
  | LDiscard t -> ""

let rec pp_rhs tag =
 function
  | Expr e -> pp_expr tag e
  | Call(addr,meth,value,exprl) ->
     pp_expr Address addr ^
     pp_meth meth ^
     (match value with None -> "" | Some v -> pp_expr Int v ^ ".") ^
     "(" ^ String.concat "," (pp_expr_list (snd3 meth) exprl) ^ ")"

let rec pp_stm : type b. 'a tag -> ('a,b) stm -> string = fun tag ->
 function
  | Epsilon -> ""
  | Return e -> "return " ^ pp_expr tag e
  | Assign(lhs,rhs,stm) ->
     pp_lhs lhs ^
     pp_rhs (tag_of_lhs lhs) rhs ^
     "; " ^ pp_stm tag stm
  | IfThenElse(c,stm1,stm2,stm3) ->
     "if " ^ pp_expr Bool c ^
     " { " ^ pp_stm tag stm1 ^ " } else { " ^
     pp_stm tag stm2 ^ " }; " ^
     pp_stm tag stm3
  | Revert -> "revert"

(*
type ('a,'b,'c) block = 'b var_list * 'c var_list * ('a,[`Return]) stm
type any_method_decl =
 | AnyMethodDecl : ('a,'b) meth * ('a,'b,'c) block * (*payable:*)bool -> any_method_decl
type methods = any_method_decl list
type fields = any_field list
type a_contract =
 AContract : address * methods * (int,unit tag_list,_) block option * fields -> a_contract
type configuration = a_contract list
*)

(*** Lookups ***)

(*
let lookup (type a) (f : a field) (s : store) : a =
 let rec aux : store -> a =
  function
    [] ->
     prerr_endline ("Error: assignment to undefined field " ^ pp_field f);
     assert false
  | Let(g,v)::tl ->
     match eq_tag (fst f) (fst g) with
        Some Refl when snd f = snd g -> v
      | _ -> aux tl
 in
  aux s
*)

let lookup_method (type a b) (f : (a,b) meth) (s : methods) : (a,b) block =
 let rec aux : methods -> (a,b) block =
  function
    [] ->
     prerr_endline ("Error: call to undefined method " ^ pp_meth f);
     assert false
  | AnyMethodDecl(g,v,_payable)::tl ->
     match eq_tag (fst3 f) (fst3 g), eq_tag_list (snd3 f) (snd3 g) with
      | Some Refl, Some Refl when (third3 f)=(third3 g) -> v
      | _,_ -> aux tl
 in
  aux s
