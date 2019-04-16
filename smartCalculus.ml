open Lib

type contract = [`Contract]
type human = [`Human]
type idle = [`Idle]
type actor = [human | contract]
type idle_or_contract = [idle | contract]
type _ address =
 | Contract : string -> contract address
 | Human : string -> human address
type any_address = AnyAddress : _ address -> any_address
type 'a tag =
 | Int : int tag
 | Bool : bool tag
 | String : string tag
 | ContractAddress : (contract address) tag
 | HumanAddress : (human address) tag
type _ tag_list =
   TNil : unit tag_list
 | TCons : 'a tag * 'b tag_list -> ('a * 'b) tag_list
type 'a ident = 'a tag * string
type ('a,'b) meth = 'a tag * 'b tag_list * string
type 'a field = 'a ident
type 'a var = 'a ident
type const = Symbolic of string | Numeric of int
type _ expr =
 | Var : 'a var -> 'a expr
 | Fail : 'a expr
 | This : (contract address) expr
 | Field : 'a field -> 'a expr
 | Plus : int expr * int expr -> int expr
 | Mult : const * int expr -> int expr
 | Minus : int expr -> int expr
 | Max : int expr * int expr -> int expr
 | Geq : int expr * int expr -> bool expr
 | Gt : int expr * int expr -> bool expr
 | Eq : 'a tag * 'a expr * 'a expr -> bool expr
 | And : bool expr * bool expr -> bool expr
 | Or : bool expr * bool expr -> bool expr
 | Not : bool expr -> bool expr
 | Value : 'a -> 'a expr
 | Symbol : string -> int expr
type 'a tagged_expr = 'a tag * 'a expr
type _ var_list =
   VNil : unit var_list
 | VCons : 'a var * 'b var_list -> ('a * 'b) var_list
type _ expr_list =
   ENil : unit expr_list
 | ECons : 'a expr * 'b expr_list -> ('a * 'b) expr_list
type _ rhs =
 | Expr : 'a expr -> 'a rhs
 | Call : (contract address) expr option * ('a,'b) meth * 'b expr_list -> 'a rhs
type stm =
 | Assign : 'a field * 'a rhs -> stm
 | IfThenElse : bool expr * stm * stm -> stm
 | Comp : stm * stm -> stm
 | Choice : stm * stm -> stm
type stack_entry =
   Stm : stm -> stack_entry
 | AssignBullet : (* FIXME: make it idle if a human ?? *)
    'b field * (contract address) expr -> stack_entry
and 'actor stack =
 | Zero : idle stack
 | Return : _ tagged_expr -> human stack
 | InitialCall : _ tagged_expr * _ address var -> contract stack
 | SComp : stack_entry * 'actor stack -> 'actor stack
type any_stack = AnyStack : _ stack -> any_stack
type ('a,'b) program = 'b var_list * stm list * (*return:*)'a expr
type assign =
 | Let : 'a field * 'a -> assign
type store = assign list
type any_method_decl =
 | AnyMethodDecl : ('a,'b) meth * ('a,'b) program -> any_method_decl
type methods = any_method_decl list
type a_contract = contract address * methods * store
type a_human = human address * methods * store * human stack
type configuration =
 { contracts : a_contract list
 ; humans : a_human list
 }

type (_,_) eq = Refl : ('a,'a) eq

let eq_tag : type a b. a tag -> b tag -> (a,b) eq option = fun t1 t2 ->
 match t1,t2 with
 | Int, Int -> Some Refl
 | Bool, Bool -> Some Refl
 | String, String -> Some Refl
 | ContractAddress, ContractAddress -> Some Refl
 | HumanAddress, HumanAddress -> Some Refl
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

(*** Serialization ***)
let pp_tag : type a. a tag -> string =
 function
  | Int -> "int"
  | Bool -> "bool"
  | String -> "string"
  | ContractAddress -> "contract_address"
  | HumanAddress -> "human_address"
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
let pp_address : type a. a address -> string =
 function Contract a -> "C("^a^")" | Human a -> "H("^a^")"
let pp_value (type a) (tag : a tag) (v : a) =
 match tag with
    Int -> string_of_int v
  | Bool -> string_of_bool v
  | String -> v
  | ContractAddress -> pp_address v
  | HumanAddress -> pp_address v
let pp_field = pp_ident
let pp_const =
 function
    Symbolic s -> s
  | Numeric n -> string_of_int n

let pp_any_address (AnyAddress a) = pp_address a

let rec pp_expr : type a. a tag -> a expr -> string =
 fun tag ->
 function
  | Var v -> pp_var v
  | Fail -> "fail"
  | This -> "this"
  | Symbol s -> s
  | Field f -> pp_field f
  | Plus (e1,e2) -> "(" ^ pp_expr tag e1 ^ " + " ^ pp_expr tag e2 ^ ")"
  | Mult (c,e) -> "(" ^ pp_const c ^ " * " ^ pp_expr tag e ^ ")"
  | Minus e -> "-" ^ pp_expr tag e
  | Max (e1,e2) -> "(max " ^ pp_expr tag e1 ^ " " ^ pp_expr tag e2 ^ ")"
  | Geq (e1,e2) -> "(" ^ pp_expr Int e1 ^ " >= " ^ pp_expr Int e2 ^ ")"
  | Gt (e1,e2) -> "(" ^ pp_expr Int e1 ^ " > " ^ pp_expr Int e2 ^ ")"
  | Eq (tag,e1,e2) -> "(" ^ pp_expr tag e1 ^ " = " ^ pp_expr tag e2 ^ ")"
  | And (g1,g2) -> "(" ^ pp_expr tag g1 ^ " /\\\\ " ^ pp_expr tag g2 ^ ")"
  | Or (g1,g2) -> "(" ^ pp_expr tag g1 ^ " \\\\/ " ^ pp_expr tag g2 ^ ")"
  | Not g -> "~" ^ pp_expr tag g
  | Value v -> pp_value tag v
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
let pp_rhs tag =
 function
  | Expr e -> pp_expr tag e
  | Call(addr,meth,exprl) ->
     (match addr with None -> "this" | Some a -> pp_expr ContractAddress a)^     pp_meth meth ^ "(" ^ String.concat "," (pp_expr_list (snd3 meth) exprl) ^ ")"

let rec pp_stm =
 function
  | Assign(f,rhs) -> pp_field f ^ " := " ^ pp_rhs (fst f) rhs
  | IfThenElse(c,stm1,stm2) -> "if " ^ pp_expr Bool c ^ " then " ^ pp_stm stm1 ^ " else " ^ pp_stm stm2
  | Comp(stm1,stm2) -> pp_stm stm1 ^ ";" ^ pp_stm stm2
  | Choice(stm1,stm2) -> pp_stm stm1 ^ "+" ^ pp_stm stm2

let pp_stack_entry =
 function
    Stm stm -> pp_stm stm
  | AssignBullet(f,e) ->
     pp_expr ContractAddress e ^ "." ^ pp_field f ^ " := * ..."

let rec pp_stack : type contract. contract stack -> string =
 function
  | Zero -> "0"
  | Return e -> "return " ^ pp_tagged_expr e
  | InitialCall(e,addr) -> "return " ^ pp_tagged_expr e ^ ";" ^ pp_var addr
  | SComp(se,s) -> pp_stack_entry se ^ ";\n" ^ pp_stack s

let pp_any_stack (AnyStack s) = pp_stack s

(*** Lookups ***)

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

let lookup_method (type a b) (f : (a,b) meth) (s : methods) : (a,b) program =
 let rec aux : methods -> (a,b) program =
  function
    [] ->
     prerr_endline ("Error: call to undefined method " ^ pp_meth f);
     assert false
  | AnyMethodDecl(g,v)::tl ->
     match eq_tag (fst3 f) (fst3 g), eq_tag_list (snd3 f) (snd3 g) with
      | Some Refl, Some Refl when (third3 f)=(third3 g) -> v
      | _,_ -> aux tl
 in
  aux s


(*** Evaluation ***)
type truth_values = F | T | M (* false, true, maybe *)
let tv_not = function F -> T | T -> F | M -> M
let tv_and v1 v2 =
 match v1,v2 with
    F,_
  | _,F -> F
  | T,T -> T
  | _,_ -> M
let tv_or v1 v2 =
 match v1,v2 with
    F,x
  | x,F -> x
  | T,_
  | _,T -> T
  | M,M -> M

let smart_and c1 c2 =
 match c1,c2 with
  | Value(true), c
  | c, Value(true) -> c
  | _,_ -> And(c1,c2)

let smart_minus =
 function
    Value (c) -> Value (-c)
  | x -> Minus x

let smart_plus e1 e2 =
 match e1,e2 with
    Value (c1), Value (c2) -> Value (c1 + c2)
  | _,_ -> Plus(e1,e2)

let smart_mult c e =
 match c,e with
    Numeric c1, Value (c2) -> Value (c1 + c2)
  | _,_ -> Mult(c,e)

let smart_max e1 e2 =
 match e1,e2 with
    Value (c1), Value (c2) -> Value (max c1 c2)
  | _,_ -> Max(e1,e2)

let geq e1 e2 =
 match e1,e2 with
    Value (c1), Value (c2) ->
     if c1 >= c2 then T else F
  | _,_ -> if e1 = e2 then T else M

let gt e1 e2 =
 match e1,e2 with
    Value (c1), Value (c2) ->
     if c1 > c2 then T else F
  | _,_ -> if e1 = e2 then F else M

let rec eval_expr : type a. a expr -> a expr =
 function
  | Var _
  | Field _
  | Value _ as x -> x
  | Symbol _ as x -> x
  | Fail -> Fail
  | This -> This
  | Plus (e1,e2) -> smart_plus (eval_expr e1) (eval_expr e2)
  | Mult (c,e) -> smart_mult c (eval_expr e)
  | Minus e -> smart_minus (eval_expr e)
  | Max (e1,e2) -> smart_max (eval_expr e1) (eval_expr e2)
  | Geq _ -> assert false
  | Gt _ -> assert false
  | Eq _ -> assert false
  | And _ -> assert false
  | Or _ -> assert false
  | Not _ -> assert false

let eq e1 e2 =
 match e1,e2 with
    Value (c1), Value (c2) ->
     if c1 = c2 then T else F
  | _,_ -> if e1 = e2 then T else M

let rec eval_cond : bool expr -> truth_values =
 function
  | Fail -> M
  | Var _ -> M
  | Field _ -> M
  | Value true -> T
  | Value false -> F
  | Geq (e1,e2) -> geq (eval_expr e1) (eval_expr e2)
  | Gt (e1,e2) -> gt (eval_expr e1) (eval_expr e2)
  | Eq (_,e1,e2) -> eq (eval_expr e1) (eval_expr e2)
  | And (g1,g2) -> tv_and (eval_cond g1) (eval_cond g2)
  | Or (g1,g2) -> tv_or (eval_cond g1) (eval_cond g2)
  | Not g -> tv_not (eval_cond g)
