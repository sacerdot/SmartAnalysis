type address = string
type 'a tag =
 | Unit : unit tag
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
 | ReturnRhs : 'a rhs -> ('a,_) stm
 | Return : (unit,_) stm
 | Assign : 'a lhs * 'a rhs * ('b,'c) stm -> ('b,'c) stm
 | IfThenElse : bool expr * ('b,[`Epsilon]) stm * ('b,[`Epsilon]) stm * ('b,'c) stm -> ('b,'c) stm
 | Revert : _ stm
type ('a,'b) block =
 Block : 'b var_list * _ var_list * ('a,[`Return]) stm -> ('a,'b) block
type any_method_decl =
 | AnyMethodDecl : ('a,'b) meth * ('a,'b) block * (*payable:*)bool -> any_method_decl
type methods = any_method_decl list
type fields = any_field list
type a_contract =
 AContract : address * methods * (unit,unit) block option * fields -> a_contract
type configuration = a_contract list

(*
## Syntactic differences w.r.t. the paper ##
1. we differentiate Epsilon (used only in if-then-else branches) from
   Return
2. return f(); is tail recursive and works if f() returns void too
2. no transfer function:
   we just call fallback instead

## Syntactic or typing constraints that are not captured ##
1. a function can only invoke functions that exist if contract is known?
2. calling a function with bad return type?
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
let mk_indent indent = String.make (3 * indent) ' '

let pp_tag : type a. a tag -> string =
 function
  | Unit -> "?VOID?"
  | Int -> "int"
  | Bool -> "bool"
  | Address -> "address"
let rec pp_tag_list : type a. a tag_list -> string list =
 function
    TNil -> []
  | TCons(x,tl) -> pp_tag x :: pp_tag_list tl
let pp_decl (t,s) = pp_tag t ^ " " ^ s
let pp_ident (_t,s) = (*pp_tag t ^ " " ^*) s
let pp_var = pp_ident
let rec pp_var_list : type a. a var_list -> string list =
 function
    VNil -> []
  | VCons(v,tl) -> pp_decl v :: pp_var_list tl
let pp_address : address -> string = fun s -> s
let pp_value (type a) (tag : a tag) (v : a) =
 match tag with
  | Unit -> assert false (* it should not happen *)
  | Int -> string_of_int v
  | Bool -> string_of_bool v
  | Address -> pp_address v
let pp_field = pp_ident
let pp_any_field (AnyField f) = pp_decl f
let pp_fields ~indent l =
 String.concat "" (List.map (fun f -> mk_indent indent ^ pp_any_field f ^ ";\n") l)

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
  | Eq (tag,e1,e2) -> "(" ^ pp_expr tag e1 ^ " == " ^ pp_expr tag e2 ^ ")"
  | And (g1,g2) -> "(" ^ pp_expr tag g1 ^ " && " ^ pp_expr tag g2 ^ ")"
  | Or (g1,g2) -> "(" ^ pp_expr tag g1 ^ " || " ^ pp_expr tag g2 ^ ")"
  | Not g -> "!" ^ pp_expr tag g
  | Value v -> pp_value tag v
  | MsgSender -> "msg.sender"
  | MsgValue -> "msg.value"
  | Balance e -> pp_expr Address e ^ ".balance"

let pp_tagged_expr e = pp_expr (fst e) (snd e)

let rec pp_expr_list : type a. a tag_list -> a expr_list -> string list = fun tg el ->
 match tg,el with
    TNil,ENil -> []
   | TCons(tag,tagl),ECons(v,tl) -> pp_expr tag v :: pp_expr_list tagl tl

let pp_meth (_rtag,_tags,id) =
 id(* ^ ":(" ^ String.concat "*" (pp_tag_list tags) ^ " -> " ^ pp_tag rtag ^ ")"*)

let pp_lhs =
 function
  | LField f -> pp_field f ^ " = "
  | LVar v -> pp_var v ^ " = "
  | LDiscard _ -> ""

let pp_rhs tag =
 function
  | Expr e -> pp_expr tag e
  | Call(addr,meth,value,exprl) ->
     pp_expr Address addr ^
     "." ^
     pp_meth meth ^
     (match value with None -> "" | Some v -> ".value(" ^ pp_expr Int v ^ ")") ^
     "(" ^ String.concat "," (pp_expr_list (Utils.snd3 meth) exprl) ^ ")"

let rec pp_stm : type a b. indent:int -> ?breakline:bool -> a tag -> (a,b) stm -> string = fun ~indent ?(breakline=true) tag stm ->
 (match stm with Epsilon -> "" | _ -> mk_indent indent) ^
 (match stm with
  | Epsilon -> ""
  | ReturnRhs e -> "return " ^ pp_rhs tag e ^ ";"
  | Return -> "return;"
  | Assign(lhs,rhs,stm) ->
     pp_lhs lhs ^
     pp_rhs (tag_of_lhs lhs) rhs ^ ";" ^
     (match stm with Epsilon -> "" | _ -> "\n") ^
     pp_stm ~indent ~breakline:false tag stm
  | IfThenElse(c,stm1,stm2,stm3) ->
     "if " ^ pp_expr Bool c ^ " {\n" ^
     pp_stm ~indent:(indent+1) tag stm1 ^
     mk_indent indent ^ "} else {\n" ^
     pp_stm ~indent:(indent+1) tag stm2 ^
     mk_indent indent ^ "}\n" ^
     pp_stm ~indent ~breakline:false tag stm3
  | Revert -> "revert();") ^
 (match stm with Epsilon -> "" | _ when breakline -> "\n" | _ -> "")

let pp_block : type a. indent:int -> bool -> a tag -> (a, 'b) block -> address =
fun ~indent payable tag (Block (vl,lvl,stm)) ->
 "(" ^ String.concat "," (pp_var_list vl) ^ ") " ^
 (match tag with Unit -> "" | _ -> "returns (" ^ pp_tag tag ^ ") ") ^
 (if payable then "payable " else " ") ^ "{\n" ^
 String.concat "" (List.map (fun s -> mk_indent (indent+1) ^ s ^ ";\n") (pp_var_list lvl)) ^
 pp_stm ~indent:(indent+1) tag stm ^
 mk_indent indent ^ "}\n\n"

let pp_any_method_decl ~indent (AnyMethodDecl(m,b,payable)) =
 mk_indent indent ^
 "function " ^ pp_meth m ^ " " ^ pp_block ~indent payable (Utils.fst3 m) b

let pp_methods ~indent l =
 String.concat "\n" (List.map (pp_any_method_decl ~indent) l)

let pp_fallback ~indent =
 function
    None -> ""
  | Some b -> mk_indent indent ^ "function " ^ pp_block ~indent true Unit b

let pp_a_contract (AContract (addr,methods,fallback,fields)) =
 "contract " ^ addr ^ " {\n" ^
 pp_fields ~indent:1 fields ^ "\n" ^
 pp_methods ~indent:1 methods ^
 pp_fallback ~indent:1 fallback ^
 "}\n"

let pp_configuration l =
 String.concat "\n"
  (List.map pp_a_contract l)

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
     match eq_tag (Utils.fst3 f) (Utils.fst3 g), eq_tag_list (Utils.snd3 f) (Utils.snd3 g) with
      | Some Refl, Some Refl when (Utils.trd3 f)=(Utils.trd3 g) -> v
      | _,_ -> aux tl
 in
  aux s
