(*** Smart Calculus ***)

module SmartCalculus =
struct
 type contract
 type human
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
 type 'a stack_entry =
    Stm : stm -> 'a stack_entry
  | AssignBullet : 'b field * (contract address) expr * (*backtracking:*)'a stack -> 'a stack_entry
 and 'a stack =
  | Return : 'a expr -> 'a stack
  | SComp : 'a stack_entry * 'a stack -> 'a stack
 type ('a,'b) program = 'b var_list * stm list * (*return:*)'a expr
 type assign =
  | Let : 'a field * 'a -> assign
 type store = assign list
 type any_method_decl =
  | AnyMethodDecl : ('a,'b) meth * ('a,'b) program -> any_method_decl
 type methods = any_method_decl list
 type a_contract = contract address * methods * store
 type a_human = human address * methods * store * int stack
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

 let lookup (type a) (f : a field) (s : store) : a =
  let rec aux : store -> a =
   function
     [] -> assert false
   | Let(g,v)::tl ->
      match eq_tag (fst f) (fst g) with
         Some Refl when snd f = snd g -> v
       | _ -> aux tl
  in
   aux s

 let fst3 (a,_,_) = a
 let snd3 (_,a,_) = a
 let third3 (_,_,a) = a

 let lookup_method (type a b) (f : (a,b) meth) (s : methods) : (a,b) program =
  let rec aux : methods -> (a,b) program =
   function
     [] -> assert false
   | AnyMethodDecl(g,v)::tl ->
      match eq_tag (fst3 f) (fst3 g), eq_tag_list (snd3 f) (snd3 g) with
       | Some Refl, Some Refl when (third3 f)=(third3 g) -> v
       | _,_ -> aux tl
  in
   aux s

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

let pp_tagged_expr e = pp_expr (fst e) (snd e)

let rec pp_expr_list : type a. a tag_list -> a expr_list -> string list = fun tg el ->
 match tg,el with
    TNil,ENil -> []
  | TCons(tag,tagl),ECons(v,tl) -> pp_expr tag v :: pp_expr_list tagl tl

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

end


(*** Presburger Automata ***)
module Presburger =
struct

type id = int list
type 'b label = 'b SmartCalculus.tag_list * string
let is_contract : type a. a SmartCalculus.address -> bool = function SmartCalculus.Contract _ -> true | SmartCalculus.Human _ -> false
type assignment =
 Assignment : 'a SmartCalculus.var * 'a SmartCalculus.expr -> assignment
type subst = assignment list
type cond = bool SmartCalculus.expr

type action =
 | Input : (*receiver:*)(_ SmartCalculus.address) * (*sender:*)((_ SmartCalculus.address) SmartCalculus.tagged_expr) option * 'b label * 'b SmartCalculus.var_list -> action
 | Output : (*sender:*)(_ SmartCalculus.address) * (*receiver:*)(_ SmartCalculus.address) SmartCalculus.tagged_expr * 'b label * 'b SmartCalculus.expr_list -> action
 | Tau : action

type state = id * (subst * bool(*= no actor running*))
type transition = id * id * cond * action
type automaton = SmartCalculus.any_address list * id(*=initial state*) * state list * transition list

let lookup (type a) (f : a SmartCalculus.var) (s : subst) : a SmartCalculus.expr =
 let rec aux : subst -> a SmartCalculus.expr =
  function
    [] -> raise Not_found
  | Assignment(g,v)::tl ->
     match SmartCalculus.eq_tag (fst f) (fst g) with
      | Some SmartCalculus.Refl when (snd f) = (snd g) -> v
      | _ -> aux tl
 in
  aux s

(*** Serialization ***)
let pp_id l = String.concat "*" (List.map string_of_int l)
let pp_label (tags,s) = s ^ "::" ^ String.concat "*" (SmartCalculus.pp_tag_list tags)
let pp_assignment (Assignment (v,e)) = SmartCalculus.pp_var v ^ "=" ^ SmartCalculus.pp_expr (fst v) e
let pp_subst al = String.concat " ; " (List.map pp_assignment al)
let pp_cond : bool SmartCalculus.expr -> string = function SmartCalculus.Value true -> "" | g -> SmartCalculus.pp_expr Bool g
let pp_action =
 function
  | Input (r,s,l,vl) ->
     SmartCalculus.pp_address r ^ "." ^
     pp_label l ^
     "[" ^ (match s with None -> "" | Some a -> SmartCalculus.pp_tagged_expr a ^ ".") ^ "]" ^
     "(" ^ String.concat "," (SmartCalculus.pp_var_list vl) ^ ")"
  | Output (r,aexpr,l,al) ->
     SmartCalculus.pp_address r ^ ":" ^
     SmartCalculus.pp_tagged_expr aexpr ^ "." ^ pp_label l ^
      "(" ^ String.concat "," (SmartCalculus.pp_expr_list (fst l) al) ^ ")"
  | Tau -> "tau"
let pp_state i (id,(al,zero)) =
 "\"" ^ pp_id id ^ "\" [label=\"" ^
  pp_id id ^ "[" ^ string_of_bool zero ^ "]: " ^ String.concat ", " (List.map pp_assignment al) ^
  "\"" ^
  (if i = id then " shape=\"rectangle\"" else "") ^
  "]"
let color_of_action = function Input _ -> "red" | Output _ -> "blue" | Tau -> "black"
let pp_transition (s,d,c,a) =
 "\"" ^ pp_id s ^ "\" -> \"" ^ pp_id d ^ "\" [label=\"" ^
  pp_action a ^ "\n" ^ pp_cond c ^ "\" color=\"" ^
  color_of_action a ^ "\"]"
let pp_automaton ((al, i, sl, tl) : automaton) =
 "digraph \"" ^  String.concat "*" (List.map SmartCalculus.pp_any_address al) ^ "\" {\n" ^
 String.concat "\n" (List.map (pp_state i) sl) ^ "\n" ^
 String.concat "\n" (List.map pp_transition tl) ^ "\n" ^
"}"

(*** Fresh int generator ***)
let mk_fresh =
 let n = ref 0 in
 function () -> incr n ; !n

(*** Substitution ***)
let rec make_subst : type a. a SmartCalculus.var_list -> a SmartCalculus.expr_list -> subst =
 fun vl el ->
  match vl, el with
     SmartCalculus.VNil, SmartCalculus.ENil -> []
   | SmartCalculus.VCons(x,vtl),SmartCalculus.ECons(e,etl) ->
      Assignment(x,e) :: make_subst vtl etl

let map_option f = function None -> None | Some x -> Some (f x)

let rec apply_subst_expr : type a. subst -> a SmartCalculus.expr -> a SmartCalculus.expr =
 fun subst expr -> match expr with
  | SmartCalculus.Symbol _ as e -> e
  | SmartCalculus.Fail -> Fail
  | SmartCalculus.This -> This
  | SmartCalculus.Field _ as e -> e
  | SmartCalculus.Var v as e -> (try lookup v subst with Not_found -> e)
  | SmartCalculus.Value _ as e -> e
  | SmartCalculus.Plus (e1,e2) -> Plus (apply_subst_expr subst e1,apply_subst_expr subst e2)
  | SmartCalculus.Mult (c,e2) -> Mult (c,apply_subst_expr subst e2)
  | SmartCalculus.Minus e -> Minus (apply_subst_expr subst e)
  | SmartCalculus.Max (e1,e2) -> Max (apply_subst_expr subst e1,apply_subst_expr subst e2)
  | SmartCalculus.Geq (e1,e2) -> Geq (apply_subst_expr subst e1,apply_subst_expr subst e2)
  | SmartCalculus.Gt (e1,e2) -> Gt (apply_subst_expr subst e1,apply_subst_expr subst e2)
  | SmartCalculus.Eq (tag,e1,e2) -> Eq (tag,apply_subst_expr subst e1,apply_subst_expr subst e2)
  | SmartCalculus.And (g1,g2) -> And (apply_subst_expr subst g1,apply_subst_expr subst g2)
  | SmartCalculus.Or (g1,g2) -> Or (apply_subst_expr subst g1,apply_subst_expr subst g2)
  | SmartCalculus.Not g -> Not (apply_subst_expr subst g)
let apply_subst_tagged_expr subst (t,e) = t,apply_subst_expr subst e
let apply_subst_assignment subst (Assignment (v,e)) =
 Assignment (v, apply_subst_expr subst e)
let apply_subst_subst subst al =
 List.map (apply_subst_assignment subst) al
let rec apply_subst_expr_list : type a. subst -> a SmartCalculus.expr_list -> a SmartCalculus.expr_list =
 fun subst -> function
    SmartCalculus.ENil -> SmartCalculus.ENil
  | SmartCalculus.ECons(x,tl) -> ECons(apply_subst_expr subst x,apply_subst_expr_list subst tl)
let apply_subst_action subst =
 function
  | Output (r, aexpr,l,al) ->
     Output (r, apply_subst_tagged_expr subst aexpr,l,apply_subst_expr_list subst al)
  | Input (r, aexpr, l, vl) ->
     Input (r, map_option (apply_subst_tagged_expr subst) aexpr, l, vl)
  | Tau -> Tau

 let apply_subst_rhs subst =
  function
   | SmartCalculus.Expr e -> SmartCalculus.Expr (apply_subst_expr subst e)
   | SmartCalculus.Call(addr,meth,exprl) ->
      Call(map_option (apply_subst_expr subst) addr,meth,apply_subst_expr_list subst exprl)

 let rec apply_subst_stm subst =
  function
  | SmartCalculus.Assign(f,rhs) -> SmartCalculus.Assign(f,apply_subst_rhs subst rhs)
  | SmartCalculus.IfThenElse(c,stm1,stm2) ->
     IfThenElse(apply_subst_expr subst c, apply_subst_stm subst stm1,
      apply_subst_stm subst stm2)
  | SmartCalculus.Comp(stm1,stm2) ->
     Comp(apply_subst_stm subst stm1,apply_subst_stm subst stm2)
  | SmartCalculus.Choice(stm1,stm2) ->
     Choice(apply_subst_stm subst stm1,apply_subst_stm subst stm2)

(*** Composition ***)
let rec same_but_last l1 l2 =
 match l1,l2 with
    [_],[_] -> true
  | x::xs,y::ys -> x=y && same_but_last xs ys
  | _,_ -> false

exception Skip

let (@@) (ass1,zero1) (ass2,zero2) =
 assert(zero1 || zero2) ;
 ass1 @ ass2, zero1 && zero2

let (===) (e : ('a SmartCalculus.address) SmartCalculus.tagged_expr) (a : SmartCalculus.any_address) =
 match snd e with
  | SmartCalculus.Value b -> SmartCalculus.AnyAddress b = a
  | _ -> false

let change_sub (sub : subst) : action -> subst =
 function
  | Input(_,_,_,vl) ->
     let rec aux : type a. a SmartCalculus.var_list -> assignment list =
      function
         SmartCalculus.VNil -> sub
       | SmartCalculus.VCons(x,tl) -> Assignment(x, SmartCalculus.Var x) :: aux tl in
     aux vl
  | Tau
  | Output _ -> sub

let rec add_transition id1' id2' ~sub cond assign action id ((a1,_,sl1,tl1) as au1 : automaton) ((a2,_,sl2,tl2) as au2 : automaton) sp tp =
 try
  let id' = id1' @ id2' in
  let cond = apply_subst_expr sub cond in
  let cond =
   let ground_cond =
    apply_subst_expr sub (apply_subst_expr (fst assign) cond) in
   match SmartCalculus.eval_cond ground_cond with SmartCalculus.T -> SmartCalculus.Value true | M -> cond | F -> raise Skip in
  let action = apply_subst_action sub action in
  let s12' = List.assoc id1' sl1 @@ List.assoc id2' sl2 in
  let s12' = apply_subst_subst sub (fst s12'),snd s12' in
  let id' = id' @ [mk_fresh ()] in
  let (id',_) as s',is_new =
   try
    List.find (fun (idx,sx) -> sx = s12' && same_but_last idx id') sp, false
   with Not_found -> (id',s12'),true in
  let tr = id,id',cond,action in
  let tp = if List.mem tr tp then tp else tr::tp in
  if is_new then
   let sp = s'::sp in
   move_state ~sub au1 au2 id' id1' id2' sp tp
  else
   sp,tp
 with Skip -> sp,tp

and move_state ~sub (au1 : automaton) (au2 : automaton) id id1 id2 sp tp =
 let sp,tp = move1 ~sub au1 au2 id id1 id2 sp tp in
 let sp,tp = move2 ~sub au1 au2 id id1 id2 sp tp in
 let sp,tp = interact1in_2out ~sub au1 au2 id id1 id2 sp tp in
 let sp,tp = interact2in_1out ~sub au1 au2 id id1 id2 sp tp in
 sp,tp

and move1 ~sub ((_,_,sl1,tl1) as au1 : automaton) ((a2,_,sl2,tl2) as au2 : automaton) id id1 id2 sp tp =
 let moves = List.filter (fun (s,_,_,_) -> s = id1) tl1 in
 let id1' x = x in
 let id2' _ = id2 in
 let your_ass = List.assoc id1 sl1 in
 let other_ass = List.assoc id2 sl2 in
 let the_others = a2 in
 movex your_ass other_ass the_others moves id1' id2' ~sub au1 au2 id sp tp

and move2 ~sub ((a1,_,sl1,tl1) as au1) ((_,_,sl2,tl2) as au2) id id1 id2 sp tp =
 let moves = List.filter (fun (s,_,_,_) -> s = id2) tl2 in
 let id1' _ = id1 in
 let id2' x = x in
 let your_ass = List.assoc id2 sl2 in
 let other_ass = List.assoc id1 sl1 in
 let the_others = a1 in
 movex your_ass other_ass the_others moves id1' id2' ~sub au1 au2 id sp tp

and movex your_ass other_ass the_others moves id1' id2' ~sub ((a1,_,sl1,tl1) as au1 : automaton) ((a2,_,sl2,tl2) as au2 : automaton) id sp tp =
 let assign = your_ass @@ other_ass in
 let can_fire =
  function
   | Tau | Input (_,None,_,_) -> true
   | Input (_,Some d,_,_) ->
      let d = apply_subst_tagged_expr sub (apply_subst_tagged_expr (fst your_ass) d) in
      List.for_all (fun a -> not (d === a)) the_others
   | Output(r,d,_,_) ->
      (is_contract r || snd assign) &&
      let d = apply_subst_tagged_expr sub (apply_subst_tagged_expr (fst your_ass) d) in
      List.for_all (fun a -> not (d === a)) the_others in
 List.fold_left
  (fun (sp,tp) (_,aexpr,cond,action) ->
    if can_fire action then begin
     let id1' = id1' aexpr in
     let id2' = id2' aexpr in
     let sub = change_sub sub action in
(* prerr_endline ("#1 " ^ pp_id id1' ^ " " ^ string_of_bool (snd your_ass));
prerr_endline ("#2 " ^ pp_id id2' ^ " " ^ string_of_bool (snd other_ass));
prerr_endline ("## " ^ string_of_bool (snd assign)); *)
     add_transition id1' id2' ~sub cond assign action id au1 au2 sp tp
    end else
     sp,tp
  ) (sp,tp) moves

and interact1in_2out ~sub ((a1,_,sl1,tl1) as au1 : automaton) ((a2,_,sl2,tl2) as au2 : automaton) id id1 id2 sp tp =
let ass_in = List.assoc id1 sl1 in
let ass_out = List.assoc id2 sl2 in
 let zero = snd ass_in && snd ass_out in
 let moves1 =
  List.filter (function (s,_,_,Input _) -> s = id1 | _ -> false) tl1 in
 let moves2 =
  List.filter
   (function
       (s,_,_,Output (r,d,_,_)) ->
         (is_contract r || zero) &&
         let d =
          apply_subst_tagged_expr sub (apply_subst_tagged_expr (fst (List.assoc id2 sl2)) d) in
         s = id2 && List.exists (fun a -> d === a) a1
     | _ -> false) tl2 in
 let id1' din _ = din in
 let id2' _ don = don in
 interact_in_out id1' id2' moves1 moves2 ass_in ass_out ~sub au1 au2 id sp tp

and interact2in_1out ~sub ((a1,_,sl1,tl1) as au1) ((a2,_,sl2,tl2) as au2) id id1 id2 sp tp =
 let ass_in = List.assoc id2 sl2 in
 let ass_out = List.assoc id1 sl1 in
 let zero = snd ass_in && snd ass_out in
 let moves2 =
  List.filter (function (s,_,_,Input _) -> s = id2 | _ -> false) tl2 in
 let moves1 =
  List.filter
   (function
       (s,_,_,Output (r,d,_,_)) ->
         (is_contract r || zero) &&
         let d =
          apply_subst_tagged_expr sub (apply_subst_tagged_expr (fst (List.assoc id1 sl1)) d) in
         s = id1 && List.exists (fun a -> d === a) a2
     | _ -> false) tl1 in
 let id1' _ don = don in
 let id2' din _ = din in
 interact_in_out id1' id2' moves2 moves1 ass_in ass_out ~sub au1 au2 id sp tp

and interact_in_out id1' id2' moves_in moves_out ass_in ass_out ~sub ((a1,_,sl1,tl1) as au1) ((a2,_,sl2,tl2) as au2) id sp tp =
 List.fold_left
  (fun (sp,tp) t_in ->
    List.fold_left
     (fun (sp,tp) t_out ->
       match t_in,t_out with
        | (_,din,condi,Input(receiver,sender,li,vl)), (_,don,condo,Output(addr_out,rec_out,lo,al))
          when
            apply_subst_tagged_expr sub (apply_subst_tagged_expr (fst ass_out) rec_out) === (SmartCalculus.AnyAddress receiver) &&
            (match sender with
                None -> true
              | Some aexpr ->
                 apply_subst_tagged_expr sub (apply_subst_tagged_expr (fst ass_in) aexpr)
                 === SmartCalculus.AnyAddress addr_out)
             && snd li = snd lo ->
            (match SmartCalculus.eq_tag_list (fst li) (fst lo) with
              | Some SmartCalculus.Refl ->
                 let sub = make_subst vl (apply_subst_expr_list sub al) @ sub in
                 let cond = SmartCalculus.smart_and condi condo in
                 add_transition (id1' din don) (id2' din don) ~sub cond
                  (ass_in @@ ass_out) Tau id au1 au2 sp tp
              | None -> sp,tp)
        | _ -> sp,tp
     ) (sp,tp) moves_out
  ) (sp,tp) moves_in

let compose ((a1,i1,sl1,tl1) as au1 : automaton) ((a2,i2,sl2,tl2) as au2 : automaton) =
 let id = i1 @ i2 @ [mk_fresh ()] in
 let s1 = List.assoc i1 sl1 in
 let s2 = List.assoc i2 sl2 in
 let s = id, s1 @@ s2 in
 let sp,tp = move_state ~sub:[] au1 au2 id i1 i2 [s] [] in
 a1 @ a2,id,sp,tp

end

module PresburgerOfSmartCalculus =
struct

exception Skip

let empty_stack_of = []
let same_stack stack_of id stack =
 try
  List.assoc id stack_of = stack
 with Not_found -> assert false
let bind stack_of id stack = (id,stack)::stack_of

type any_var = AnyVar : 'a SmartCalculus.var -> any_var

let rec change_in_assignment_list : type a. a SmartCalculus.field -> a SmartCalculus.expr -> Presburger.assignment list -> Presburger.assignment list =
 fun v value -> function
    [] -> assert false
  | Presburger.Assignment(v',_) as hd::tl ->
     match SmartCalculus.eq_tag (fst v) (fst v') with
      | Some SmartCalculus.Refl when snd v = snd v' -> Presburger.Assignment(v,value)::tl
      | _ ->  hd::change_in_assignment_list v value tl

let (++) (ass1,zero1) (ass2,zero2) =
 assert(zero1 || zero2) ;
 List.fold_left
  (fun ass2 (Presburger.Assignment(v,value)) ->
    change_in_assignment_list v value ass2) ass2 ass1,zero1 && zero2

(* assign is the NEW assignment after the transition
   returns ((stack_of,sp',tp'),new_state_generated) *)
let add_transition cond (assign : Presburger.subst * bool) action id stack stack_of (sp : Presburger.state list) (tp : Presburger.transition list) =
 try
  let store = List.assoc id sp in
  let cond =
   let ground_cond = Presburger.apply_subst_expr (fst store) cond in
   match SmartCalculus.eval_cond ground_cond with SmartCalculus.T -> SmartCalculus.Value true | M -> cond | F -> raise Skip in
  let id' = [Presburger.mk_fresh ()] in
  let assign = assign ++ store in
  let (id',_) as s',stack_of,is_new =
   try
    List.find (fun (idx,sx) -> sx = assign && same_stack stack_of idx stack) sp,
    stack_of, false
   with Not_found -> (id',assign),bind stack_of id' stack,true in
  let tr = id,id',cond,action in
  let tp = if List.mem tr tp then tp else tr::tp in
  if is_new then
   (stack_of,s'::sp,tp),Some id'
  else
   (stack_of,sp,tp),None
 with Skip -> (stack_of,sp,tp),None

let return_ok ty = SmartCalculus.TCons (ty, TNil), "__return_ok__"
let return_ko = SmartCalculus.TNil, "__return_ko__"

let (+:) h t = SmartCalculus.SComp(SmartCalculus.Stm h,t)
let rec (@:) l = List.fold_right (+:) l

let do_substitution : type a b. (a,b) SmartCalculus.program -> b SmartCalculus.expr_list -> SmartCalculus.stm list * a SmartCalculus.expr =
 fun (vars,stm_list,ret) exprl ->
  let subst = Presburger.make_subst vars exprl in
  List.map (Presburger.apply_subst_stm subst) stm_list,
   Presburger.apply_subst_expr subst ret

let stack_call prog exprl f stk2 =
 let stml,ret = do_substitution prog exprl in
 stml @: SmartCalculus.Assign(f,(SmartCalculus.Expr ret))+:stk2

let tail_stack_call prog exprl =
 let stml,ret = do_substitution prog exprl in
 stml @: SmartCalculus.Return ret

let is_tail_call stack f =
 match stack with
    SmartCalculus.Return (SmartCalculus.Var g) when snd f = snd g ->
     SmartCalculus.eq_tag (fst g) (fst f)
  | _ -> None

(* takes:
    address = ???
    id = id del nodo che deve eseguire stack
    stack = to be executed
    stack_of = maps the ids of the automaton state to their stack
    sp = list of states
    tp = list of transitions
   returns
    stack_of,sp,tp
*)
let rec grow_human address methods id stm_stack stack_of sp tp =
 match stm_stack with
    SmartCalculus.Return _ -> stack_of,sp,tp
  | SmartCalculus.SComp(entry,stack) ->
     let stacks,res =
      match entry with
       | SmartCalculus.Stm stm ->
          (match stm with
           | SmartCalculus.IfThenElse(c,stm1,stm2) ->
              let assign = [],true in
              let (stack_of,sp,tp),next_state1 =
               add_transition c assign Presburger.Tau id (stm1+:stack) stack_of sp tp in
              let (stack_of,sp,tp),next_state2 =
               add_transition (SmartCalculus.Not c) assign Presburger.Tau id
                (stm2+:stack) stack_of sp tp in
              [stm1+:stack, next_state1 ; stm2+:stack, next_state2],
                (stack_of,sp,tp)
           | SmartCalculus.Assign(f,SmartCalculus.Expr e) ->
              let store = List.assoc id sp in
              let e = Presburger.apply_subst_expr (fst store) e in
              let assign = ([Presburger.Assignment(f,e)],true) in
              let res,next_state =
               add_transition (SmartCalculus.Value true) assign Presburger.Tau
                id stack stack_of sp tp in
              [stack,next_state], res
           | SmartCalculus.Assign(f,SmartCalculus.Call(None,meth,exprl)) ->
              (fun (type a b c) (f: a SmartCalculus.field) (stack: c SmartCalculus.stack) (meth: (a,b) SmartCalculus.meth) exprl : ((c SmartCalculus.stack * _) list * _) ->
              (match is_tail_call stack f with
               | Some SmartCalculus.Refl ->
                  let body = SmartCalculus.lookup_method meth methods in
                  let store = List.assoc id sp in
                  let exprl = Presburger.apply_subst_expr_list (fst store) exprl in
                  [tail_stack_call body exprl, Some id], (stack_of,sp,tp)
               | None ->
                  let body = SmartCalculus.lookup_method meth methods in
                  let store = List.assoc id sp in
                  let exprl = Presburger.apply_subst_expr_list (fst store) exprl in
                  [stack_call body exprl f stack, Some id], (stack_of,sp,tp))
              ) f stack meth exprl
           | SmartCalculus.Assign(f,SmartCalculus.Call(Some receiver,meth,exprl)) ->
              let assign = [],true in
              let label = let (_,tags,name) = meth in tags,name in
              let stack =
               SmartCalculus.SComp(SmartCalculus.AssignBullet(f,receiver,stm_stack),stack) in
              let res,next_state =
               add_transition (SmartCalculus.Value true) assign
                (Presburger.Output(address,(ContractAddress,receiver),label,exprl)) id stack stack_of sp tp in
              [stack,next_state], res
           | SmartCalculus.Comp(stm1,stm2) ->
              [stm1+:(stm2+:stack), Some id], (stack_of,sp,tp)
           | SmartCalculus.Choice(stm1,stm2) ->
              let var = SmartCalculus.Int, "__choice__" ^ string_of_int (Presburger.mk_fresh ()) in
              let cond n = SmartCalculus.Eq (SmartCalculus.Int, SmartCalculus.Var var, SmartCalculus.Value n) in
              let assign = [],true in
              let (stack_of,sp,tp),next_state1 =
               add_transition (cond 0) assign Presburger.Tau id (stm1+:stack) stack_of sp tp in
              let (stack_of,sp,tp),next_state2 =
               add_transition (cond 1) assign Presburger.Tau id
                (stm2+:stack) stack_of sp tp in
              [stm1+:stack, next_state1 ; stm2+:stack, next_state2],
                (stack_of,sp,tp))
     | SmartCalculus.AssignBullet(f,receiver,backtracking_stack) ->
        let assign = [],true in
        let var = fst f, "__ra__ " ^ string_of_int (Presburger.mk_fresh ()) in
        (* ok *)
        let (stack_of,sp,tp),next_state =
         add_transition (SmartCalculus.Value true) ([Presburger.Assignment(f,SmartCalculus.Var var)],true)
          (Presburger.Input(address,Some (ContractAddress,receiver),return_ok (fst f),SmartCalculus.VCons(var,VNil))) id stack stack_of sp tp in
        (* ko *)
        let (stack_of,sp,tp),_ =
         add_transition (SmartCalculus.Value true) assign
          (Presburger.Input(address,Some (ContractAddress,receiver),return_ko,SmartCalculus.VNil)) id backtracking_stack stack_of sp tp in
        [stack,next_state],(stack_of,sp,tp)
     in
      List.fold_left
       (fun (stack_of,sp,tp as res) (stack,next_state) ->
         match next_state with
            None -> res
          | Some id -> grow_human address methods id stack stack_of sp tp
       ) res stacks

let human_to_automaton (address,methods,store,stack : SmartCalculus.a_human) : Presburger.automaton =
 let id = [Presburger.mk_fresh ()] in
 let store = List.map (function SmartCalculus.Let(x,v) -> Presburger.Assignment(x,SmartCalculus.Value v)) store in
 let sp = [id,(store,true)] in
 let _,sp,tp = grow_human address methods id stack (bind empty_stack_of id stack) sp [] in
  [SmartCalculus.AnyAddress address], id, sp, tp

end

 (*** Examples ***)
 module CalculusTest = struct
  open SmartCalculus

  let id = Int,TCons(Int,TNil),"id"
  let loop = Int,TNil,"loop"
  let loop_body =
    Comp
      (Assign((Int,"x"),Expr (Value 3))
      ,Comp (Assign((Int, "r"), Call(None,id,ECons (Var(Int,"x"), ENil))),
             Comp
               (IfThenElse(
                   Gt(Var(Int,"x"),Var(Int,"z")),
                   Assign((Int,"b"),Expr (Value 1)),
                   Assign((Int,"b"),Expr (Value 2)))
               ,Choice
                   (Comp(Assign((Int,"b"),Expr (Value 0)),Assign((Int,"res"),Call(None,loop,ENil)))
                   ,Assign((Int,"d"),Call (Some (Value(Contract "foo")),(Int,TNil,"foo"),ENil))))))

  let automaton2 =
    PresburgerOfSmartCalculus.human_to_automaton
      (Human "test"
      ,[AnyMethodDecl (id,(VCons((Int,"w"),VNil),[],Var(Int,"w")));
        AnyMethodDecl (loop,(VNil,[loop_body],Var(Int,"res")))]
      , [Let((Int,"b"),0)
        ;Let((Int,"r"),3)
        ;Let((Int,"x"),3)
        ;Let((Int,"d"),0)]
      ,SComp(Stm (Assign((Int,"res2"),Call(None,loop,ENil))),Return(Var (Int,"res2"))))



  let citizen_body =
    Comp(
    Comp(
      Comp(
        Comp(
          Assign((Int,"balance"),Expr (Symbol ("D")))
          ,Comp(
              Assign((Int,"weight"),Expr (Value 0))
            ,Assign((Int,"balance"),Call (Some (Value(Contract "incinerator")),(Int,TCons(Int,TNil),"fee"),ECons( Symbol("D"),ENil)))))
          ,Comp(
              Assign((Int,"weight"),Expr(Value 2))
             ,Choice(
                Comp(
                  Assign((Int,"balance"),Call (Some (Value(Contract "garbage_bin")),(Int,TCons(Int,TNil),"dep"),ECons( Value 1,ENil)))
                 ,Comp(
                    Assign((Int,"weight"),Expr (Value 1))
                   ,Comp(
                      Assign((Int,"balance"),Call (Some (Value(Contract "garbage_bin")),(Int,TCons(Int,TNil),"dep"),ECons( Value 1,ENil)))
                    ,Assign((Int,"weight"),Expr (Value 0)))))
            ,Comp(
                Assign((Int,"balance"),Call (Some (Value(Contract "garbage_bin")),(Int,TCons(Int,TNil),"dep"),ECons( Value 2,ENil)))
              ,Assign((Int,"weight"),Expr (Value 0))))))
    ,Assign((Int,"balance"),Call (Some (Value(Contract "banca")),(Int,TCons(Int,TNil),"save"),ECons(Var(Int,"balance"),ENil))))
  ,Assign((Int,"res"),Call(None,loop,ENil)))




  let automaton =
   PresburgerOfSmartCalculus.human_to_automaton
    (Human "citizen"
    ,[AnyMethodDecl (id,(VCons((Int,"w"),VNil),[],Var(Int,"w")));
      AnyMethodDecl (loop,(VNil,[citizen_body],Var(Int,"res")))]
    , [Let((Int,"balance"),0)
      ;Let((Int,"weight"),0)]
    ,SComp(Stm (Assign((Int,"res2"),Call(None,loop,ENil))),Return(Var (Int,"res2"))))

 end

open SmartCalculus
open Presburger

let dep = (TCons(Int,TCons(HumanAddress,TNil)),"dep")

 (*** Garbage Collection Example ***)
 module Bin = struct
  let (states : state list) =
    [ [1], ([Assignment((Int,"gp"),Value(0)) ; Assignment((Int,"gbalance"),Symbol("D"))], true)
    ; [2], ([Assignment((Int,"gp"),Value(0)) ; Assignment((Int,"gbalance"),Symbol("D")) ; Assignment((Int,"cur_q"),Var(Int,"q"))
            ; Assignment((HumanAddress,"ID"),Var(HumanAddress,"id"))],false)
    ; [3], ([Assignment((Int,"gp"),Value(1)) ; Assignment((Int,"gbalance"),Plus(Symbol("D"),Minus(Symbol("R"))))],true)
    ; [4], ([Assignment((Int,"gp"),Value(1)) ; Assignment((Int,"gbalance"),Plus(Symbol("D"),Minus(Symbol("R")))) ; Assignment((Int,"cur_q"),Var(Int,"q'"))
            ; Assignment((HumanAddress,"ID"),Var(HumanAddress,"id'"))],false)
    ; [5], ([Assignment((Int,"gp"),Value(2)) ; Assignment((Int,"gbalance"),Plus(Symbol("D"),Minus(Mult(Numeric(2),Symbol("R")))))],true)
    ; [6], ([Assignment((Int,"gp"),Value(2)) ; Assignment((Int,"gbalance"),Plus(Symbol("D"),Minus(Mult(Numeric(2),Symbol("R")))))
            ; Assignment((Int,"of"),Var(Int,"e'")); Assignment((HumanAddress,"ID"),Var(HumanAddress,"gt_id"))],true)
    ; [7], ([Assignment((Int,"gp"),Value(2)) ; Assignment((Int,"gbalance"),Plus(Symbol("D"),Minus(Mult(Numeric(2),Symbol("R")))))
            ; Assignment((Int,"of"),Var(Int,"e")); Assignment((HumanAddress,"ID"),Var(HumanAddress,"gt_id"))
            ; Assignment((Int,"of'"),Var(Int,"e'")); Assignment((HumanAddress,"ID'"),Var(HumanAddress,"gt_id'"))],true)
    ; [8], ([Assignment((Int,"gp"),Value(2)) ; Assignment((Int,"gbalance"),Plus(Symbol("D"),Minus(Mult(Numeric(2),Symbol("R")))))
            ; Assignment((Int,"of"),Var(Int,"e")); Assignment((HumanAddress,"ID"),Var(HumanAddress,"gt_id"))
            ; Assignment((Int,"of'"),Var(Int,"e'")); Assignment((HumanAddress,"ID'"),Var(HumanAddress,"gt_id'"))],true)
    ; [9], ([Assignment((Int,"gp"),Value(2)) ; Assignment((Int,"gbalance"),Plus(Symbol("D"),Minus(Mult(Numeric(2),Symbol("R")))))
            ; Assignment((Int,"of"),Var(Int,"e")); Assignment((HumanAddress,"ID"),Var(HumanAddress,"gt_id"))
            ; Assignment((Int,"of'"),Var(Int,"e'")); Assignment((HumanAddress,"ID'"),Var(HumanAddress,"gt_id'"))],true)
    ; [10], ([Assignment((Int,"gp"),Value(0)) ; Assignment((Int,"gbalance"),Plus(Symbol("D"),Minus(Mult(Numeric(2),Symbol("R")))))
            ; Assignment((Int,"of"),Var(Int,"e")); Assignment((HumanAddress,"ID"),Var(HumanAddress,"gt_id"))
            ; Assignment((Int,"of'"),Var(Int,"e'")); Assignment((HumanAddress,"ID'"),Var(HumanAddress,"gt_id'"))],false)
    ; [11], ([Assignment((Int,"gp"),Value(0))
            ; Assignment((Int,"gbalance"),Plus(Symbol("D"),Plus(Minus(Mult(Numeric(2),Symbol("R"))),Max(Var(Int,"of"), Var(Int,"of'")))))
            ; Assignment((Int,"of"),Var(Int,"e")); Assignment((HumanAddress,"ID"),Var(HumanAddress,"gt_id"))
            ; Assignment((Int,"of'"),Var(Int,"e'")); Assignment((HumanAddress,"ID'"),Var(HumanAddress,"gt_id'"))],true)
   ]

  let (transitions : transition list) =
    [ [1],[2],Value true,
      Input (Contract "garbage_bin",None, dep, VCons((Int,"q"),VCons((HumanAddress,"id"),VNil)))
    ; [2],[1],Gt(Var (Int,"cur_q"),Value (2)),
      Output (Contract "garbage_bin", (HumanAddress,Var(HumanAddress,"ID")),(TNil,"NOK"),ENil)
    ; [2],[3],Eq(Int,Var(Int, "cur_q"),Value (1)),
      Output (Contract "garbage_bin",(HumanAddress,Var (HumanAddress,"ID")),(TCons(Int ,TNil),"OK"), ECons(Symbol("R"),ENil))
    ; [2],[5],Eq(Int,Var(Int, "cur_q"),Value(2)),
      Output (Contract "garbage_bin",(HumanAddress,Var( HumanAddress,"ID")),(TCons(Int ,TNil),"OK"),ECons(Mult( Numeric 2, Symbol("R")),ENil))
    ; [3],[4],Value true,
      Input (Contract "garbage_bin",None, dep, VCons((Int,"q'"),VCons((HumanAddress,"id'"),VNil)))
    ; [4],[3],Gt(Var (Int, "cur_q"),Value (2)),
      Output (Contract "garbage_bin",(HumanAddress,Var (HumanAddress, "ID")),(TNil,"NOK"),ENil)
    ; [4],[5],Eq(Int,Var (Int, "cur_q"), Value (1)),
      Output (Contract "garbage_bin",(HumanAddress,Var(HumanAddress, "ID")),(TCons(Int ,TNil),"OK"),ECons(Symbol("R"),ENil))
    ; [5],[6],Value true,
      Input (Contract "garbage_bin",None, (TCons(Int,TCons(HumanAddress,TNil)),"bid"), VCons((Int,"e"),VCons((HumanAddress,"gt_id"),VNil)))
    ; [6],[5],Gt(Mult(Numeric 2, Var(Int, "R")), Var (Int,"of")),
      Output (Contract "garbage_bin",(HumanAddress,Var (HumanAddress, "ID")),(TCons(Int ,TNil),"lost"),ECons(Var(Int,"of"),ENil))
    ; [6],[7],Geq(Var (Int, "of"),Mult( Numeric 2, Var(Int, "R"))),
      Input (Contract "garbage_bin",None, (TCons(Int,TCons(HumanAddress,TNil)),"bid"), VCons((Int,"e'"),VCons((HumanAddress,"gt_id'"),VNil)))
    ; [7],[8],Geq(Var (Int,"of"), Var(Int, "of'")),
      Output (Contract "garbage_bin", (HumanAddress,Var (HumanAddress,"ID'")),(TCons(Int,TNil),"LOST"),ECons(Var(Int,"of'"),ENil))
    ; [7],[8],Gt(Var (Int,"of"), Var(Int, "of'")),
      Output (Contract "garbage_bin",(HumanAddress,Var (HumanAddress,"ID")), (TCons(Int ,TNil),"LOST"),ECons(Var(Int,"of"),ENil))
    ; [8],[9],Geq(Var (Int,"of"), Var(Int, "of'")),
      Output (Contract "garbage_bin",(HumanAddress,Var (HumanAddress,"ID")),(TNil,"WIN"),ENil)
    ; [8],[9],Geq(Var (Int,"of"), Var(Int, "of'")),
      Output (Contract "garbage_bin",(HumanAddress,Var (HumanAddress,"ID'")),(TNil,"WIN"),ENil)
    ; [9],[10],Value true,
      Input (Contract "garbage_bin",None, (TCons(String ,TNil),"empty"), (*[AVar "id"]*)VCons((String,"id"),VNil))
    ; [10],[9],Or(And (Geq(Var (Int,"of"), Var(Int, "of'")), Not (Eq(HumanAddress, Var(HumanAddress, "id"), Var(HumanAddress, "ID")))),
                  And (Gt(Var (Int,"of'"), Var(Int, "of")), Not (Eq(HumanAddress, Var(HumanAddress, "id"), Var(HumanAddress, "ID'"))))),Tau
    ; [10],[11],Geq(Var (Int,"of"), Var(Int, "of'")),
      Output (Contract "garbage_bin",  (ContractAddress, Var (ContractAddress, "incinerator")),(TCons(String,TCons(Int,TNil)),"notify"),
              ECons(Var(String,"ID"),ECons(Var(Int,"id"),ENil)))
    ; [10],[11],Geq(Var (Int,"of'"), Var(Int, "of")),
      Output (Contract "garbage_bin",(ContractAddress, Var (ContractAddress, "incinerator")),(TCons(String,TCons(Int,TNil)),"notify"),
              ECons(Var(String,"ID"),ECons(Var(Int,"id"),ENil)))
    ; [11],[1],Value true,
      Output (Contract "garbage_bin",(ContractAddress, Var (ContractAddress, "incinerator")),(TCons(Int ,TNil),"save"),
            ECons(Plus(Var(Int,"D"),Plus(Minus(Mult(Numeric(2),Symbol("R"))),Max(Var(Int,"of"), Var(Int,"of'")))),ENil))
   ]

  let automaton : automaton = ([AnyAddress (Contract( "garbage_bin"))],[1],states,transitions)

   let _ =
    let ch = open_out "garbage_bin.dot" in
    output_string ch (pp_automaton automaton);
    close_out ch

 end

module Citizen = struct
  let (states : state list) =
    [ [1], ([Assignment((Int,"cp"),Value(0)); Assignment((Int,"balance"),Symbol("D"))],true)
    ; [2], ([Assignment((Int,"cp"),Value(2)); Assignment((Int,"balance"),Value(0))],true)
    ; [3], ([Assignment((Int,"cp"),Value(1)); Assignment((Int,"balance"),Value(0))],true)
    ; [4], ([Assignment((Int,"cp"),Value(1)); Assignment((Int,"balance"),Value(0))],true)
    ; [5], ([Assignment((Int,"cp"),Value(1)); Assignment((Int,"balance"),Value(0))],true)
    ; [6], ([Assignment((Int,"cp"),Value(1)); Assignment((Int,"balance"),Value(0))],true)
    ; [7], ([Assignment((Int,"cp"),Value(0)); Assignment((Int,"balance"),Var(Int,"a"))],true)
    ; [8], ([Assignment((Int,"cp"),Value(1)); Assignment((Int,"balance"),Var(Int,"a"))],true)
    ; [9], ([Assignment((Int,"cp"),Value(0)); Assignment((Int,"balance"),Value(0))],true)
    ;[10], ([Assignment((Int,"cp"),Value(0)); Assignment((Int,"balance"),Value(0))],true)
    ;[11], ([Assignment((Int,"cp"),Value(0)); Assignment((Int,"balance"),Var(Int,"a"))],true)
    ;[12], ([Assignment((Int,"cp"),Value(0)); Assignment((Int,"balance"),Var(Int,"a"))],true)
    ;[13], ([Assignment((Int,"cp"),Value(0)); Assignment((Int,"balance"),Var(Int,"a"))],true)
    ;[14], ([Assignment((Int,"cp"),Value(0)); Assignment((Int,"balance"),Mult(Numeric 2,Var(Int,"a")))],true)
    ]

    let address0 = Human "citizen"
    let address = Value address0
    let gb = ContractAddress,Value (Contract "garbage_bin")
    let incinerator = ContractAddress,Value (Contract "incinerator")
    let banca = ContractAddress,Value (Contract "banca")

  let (transitions : transition list) =
    [ [1],[2],Value true,Output (address0, incinerator,(TCons(Int,TNil),"fee"),ECons(Var(Int,"D"),ENil))
    ; [2],[3],Value true,Output (address0,gb,dep,ECons( Value 2, ECons(address,ENil)))
    ; [3],[2],Value true,Input (address0,Some (gb),(TNil,"NOK"), VNil)
    ; [2],[4],Value true,Output (address0,gb,dep,ECons( Value 1, ECons(address,ENil)))
    ; [4],[2],Value true,Input (address0,Some (gb),(TNil,"NOK"), VNil)
    ; [2],[5],Value true, Tau
    ; [2],[6],Value true, Tau
    ; [3],[7], Value true,Input (address0,Some (gb),(TCons(Int,TNil),"OK"), VCons((Int,"a"),VNil))
    ; [4],[8], Value true,Input (address0,Some (gb),(TCons(Int,TNil),"OK"), VCons((Int,"a"),VNil))
    ; [8],[12], Value true, Output (address0,gb,dep,ECons(Value 1, ECons(address,ENil)))
    ; [12],[8],Value true,Input (address0,Some (gb),(TNil,"NOK"), VNil)
    ; [8],[13],Value true, Tau
    ; [12],[14],Value true,Input (address0,Some (gb),(TCons(Int,TNil),"OK"), VCons((Int,"a"),VNil))
    ; [5],[9],Value true, Output (address0,gb,dep,ECons(Value 1, ECons(address,ENil)))
    ; [9],[5],Value true,Input (address0,Some (gb),(TNil,"NOK"), VNil)
    ; [5],[10],Value true, Tau
    ; [9],[11],Value true,Input (address0,Some (gb),(TCons(Int,TNil),"OK"), VCons((Int,"a"),VNil))
    ; [7],[1], Value true,Output (address0,banca,(TCons(Int,TNil),"save"),ECons( Var(Int,"balance"),ENil))
    ; [14],[1], Value true,Output (address0,banca,(TCons(Int,TNil),"save"),ECons( Var(Int,"balance"),ENil))
    ; [13],[1], Value true,Output (address0,banca,(TCons(Int,TNil),"save"),ECons( Var(Int,"balance"),ENil))
    ; [11],[1],Value true,Output (address0,banca,(TCons(Int,TNil),"save"),ECons( Var(Int,"balance"),ENil))
    ; [10],[1], Value true,Output (address0,banca,(TCons(Int,TNil),"save"),ECons( Var(Int,"balance"),ENil))
    ; [6],[1], Value true,Output (address0,banca,(TCons(Int,TNil),"save"),ECons( Var(Int,"balance"),ENil))
    ]

  let automaton : automaton = ([AnyAddress (address0)],[1],states,transitions)

  let _ =
    let ch = open_out "citizen.dot" in
    output_string ch (pp_automaton automaton);
    close_out ch

end

module BasicCitizen = struct
  let (states : state list) =
    [ [1], ([Assignment((Int,"cp"),Value(0)); Assignment((Int,"cbalance"),Symbol("D"))],true)
    ; [2], ([Assignment((Int,"cp"),Value(2)); Assignment((Int,"cbalance"),Value(0))],true)
    ; [3], ([Assignment((Int,"cp"),Value(1)); Assignment((Int,"cbalance"),Value(0))],true)
    ; [4], ([Assignment((Int,"cp"),Value(1)); Assignment((Int,"cbalance"),Var(Int,"a"))],true)
    ; [5], ([Assignment((Int,"cp"),Value(0)); Assignment((Int,"cbalance"),Var(Int,"a"))],true)
    ; [6], ([Assignment((Int,"cp"),Value(0)); Assignment((Int,"cbalance"),Var(Int,"a"))],true)

    ]

  let address0 = Human "basiccitizen"
  let address = Value address0
  let gb = ContractAddress,Value (Contract "garbage_bin")
  let incinerator = ContractAddress,Value (Contract "incinerator")
  let banca = ContractAddress,Value (Contract "banca")

  let (transitions : transition list) =
    [ [1],[2],Value true,Output (address0, incinerator,(TCons(Int,TNil),"fee"),ECons(Var(Int,"D"),ENil))
    ; [2],[3],Value true,Output (address0,gb,dep,ECons( Value 1, ECons(address,ENil)))
    ; [3],[2],Value true,Input (address0,Some (gb),(TNil,"NOK"), VNil)
    ; [3],[4], Value true,Input (address0,Some (gb),(TCons(Int,TNil),"OK"), VCons((Int,"a"),VNil))
    ; [4],[5],Value true,Output (address0,gb,dep,ECons( Value 1, ECons(address,ENil)))
    ; [5],[4],Value true,Input (address0,Some (gb),(TNil,"NOK"), VNil)
    ; [5],[6], Value true,Input (address0,Some (gb),(TCons(Int,TNil),"OK"), VCons((Int,"a"),VNil))
    ; [6],[1], Value true,Output (address0,banca,(TCons(Int,TNil),"save"),ECons( Var(Int,"balance"),ENil))
    ]

  let automaton : automaton = ([AnyAddress (address0)],[1],states,transitions)

  let _ =
    let ch = open_out "basiccitizen.dot" in
    output_string ch (pp_automaton automaton);
    close_out ch

end
 (*
 module Truck = struct
   let (states : state list) =
     [ [1], ["p",Const (Numeric 0) ; "balance", Const (Symbolic "A")]
     ; [2], ["p",Const (Numeric 0) ; "balance", Plus (Const (Symbolic "A"), Minus (Const (Symbolic "e")))]
     ; [3], ["p",Const (Numeric 0) ; "balance", Plus (Const (Symbolic "A"), Minus (Const (Symbolic "e")))]
     ; [4], ["p",Const (Numeric 0) ; "balance", Plus (Const (Symbolic "A"), Minus (Const (Symbolic "e")))]
     ; [10], ["p",Const (Numeric 0) ; "balance", Plus (Const (Symbolic "A"), Minus (Const (Symbolic "e")))]
     ; [5], ["p",Const (Numeric 0) ;
           "balance", Plus (Const (Symbolic "A"), Plus (Minus(Var "d"), Minus (Mult (Numeric 2,Const (Symbolic "e")))))]
     ; [6], ["p",Const (Numeric 0) ;
           "balance", Plus (Const (Symbolic "A"), Plus (Minus(Var "d"), Minus (Const (Symbolic "e"))))]
     ; [7], ["p",Const (Numeric 0) ;
           "balance", Plus (Const (Symbolic "A"), Plus (Minus(Var "d"), Minus (Const (Symbolic "e"))))]
     ; [8], ["p",Const (Numeric 0) ;
           "balance", Plus (Const (Symbolic "A"), Plus (Minus(Var "d"), Minus (Const (Symbolic "e"))))]
     ; [9], ["p",Const (Symbolic "h") ;
           "balance", Plus (Const (Symbolic "A"), Plus (Minus(Var "d"), Minus (Const (Symbolic "e"))))]
     ; [11], ["p",Const (Symbolic "h") ; "balance", Plus (Const (Symbolic "A"), Minus (Const (Symbolic "e")))]
     ; [12], ["p",Mult(Numeric 2,Const (Symbolic "h")) ; "balance", Plus (Const (Symbolic "A"), Minus (Const (Symbolic "e")))]
     ; [13], ["p",Mult(Numeric 2,Const (Symbolic "h")) ; "balance", Plus (Const (Symbolic "A"), Minus (Const (Symbolic "e")))]

     ; [14], ["p",Const (Symbolic "h") ; "balance", Plus (Const (Symbolic "A"), Minus (Const (Symbolic "e")))]
     ; [15], ["p",Const (Symbolic "h") ; "balance", Plus (Const (Symbolic "A"), Minus (Mult (Numeric 2,Const (Symbolic "e"))))]
     ; [16], ["p",Const (Symbolic "h") ; "balance", Plus (Const (Symbolic "A"), Minus (Mult (Numeric 2,Const (Symbolic "e"))))]
     ; [17], ["p",Const (Symbolic "h") ; "balance", Plus (Const (Symbolic "A"), Minus (Mult (Numeric 2,Const (Symbolic "e"))))]
     ; [18], ["p",Mult(Numeric 2,Const (Symbolic "h")) ; "balance", Plus (Const (Symbolic "A"), Minus (Mult (Numeric 2,Const (Symbolic "e"))))]
     ; [19], ["p",Const (Symbolic "h") ;
            "balance", Plus (Const (Symbolic "A"), Plus (Minus(Var "d"), Minus (Mult (Numeric 2,Const (Symbolic "e")))))]
     ; [20], ["p",Const (Symbolic "h") ;
            "balance", Plus (Const (Symbolic "A"), Plus (Minus(Var "d"), Minus (Const (Symbolic "e"))))]
     ; [21], ["p",Const (Symbolic "h") ;
            "balance", Plus (Const (Symbolic "A"), Plus (Minus(Var "d"), Minus (Mult (Numeric 2,Const (Symbolic "e")))))]
     ; [23], ["p",Const (Symbolic "h") ;
            "balance", Plus (Const (Symbolic "A"), Plus (Minus(Var "d"), Minus (Mult (Numeric 2,Const (Symbolic "e")))))]
     ; [24], ["p",Mult(Numeric 2,Const (Symbolic "h")) ;
                    "balance", Plus (Const (Symbolic "A"), Plus (Minus(Var "d"), Minus (Mult (Numeric 2,Const (Symbolic "e")))))]
     ; [22], ["p",Const (Symbolic "h") ;
            "balance", Plus (Const (Symbolic "A"), Plus (Minus(Mult (Numeric 2,Const (Symbolic "d"))), Minus (Mult (Numeric 3,Const (Symbolic "e")))))]
     ; [25], ["p",Const (Symbolic "h");
            "balance", Plus (Const (Symbolic "A"), Plus (Minus(Mult (Numeric 2,Const (Symbolic "d"))), Minus (Mult (Numeric 2,Const (Symbolic "e")))))]
     ; [26], ["p",Const (Symbolic "h") ;
            "balance", Plus (Const (Symbolic "A"), Plus (Minus(Mult (Numeric 2,Const (Symbolic "d"))), Minus (Mult (Numeric 2,Const (Symbolic "e")))))]
     ; [27], ["p",Const (Symbolic "h") ;
            "balance", Plus (Const (Symbolic "A"), Plus (Minus(Mult (Numeric 2,Const (Symbolic "d"))), Minus (Mult (Numeric 2,Const (Symbolic "e")))))]
     ; [28], ["p",Mult(Numeric 2,Const (Symbolic "h")) ;
            "balance", Plus (Const (Symbolic "A"), Plus (Minus(Mult (Numeric 2,Const (Symbolic "d"))), Minus (Mult (Numeric 2,Const (Symbolic "e")))))]
     ; [37], ["p",Mult(Numeric 2,Const (Symbolic "h")) ;
            "balance", Plus (Const (Symbolic "A"), Plus (Minus(Mult (Numeric 2,Const (Symbolic "d"))), Minus (Mult (Numeric 2,Const (Symbolic "e")))))]
     ; [38], ["p",Mult(Numeric 2,Const (Symbolic "h")) ;
            "balance", Plus (Const (Symbolic "A"), Plus (Minus(Mult (Numeric 2,Const (Symbolic "d"))), Minus (Plus ( Mult (Numeric 2,Const (Symbolic "e")), Const (Symbolic "a")))))]
     ; [39], ["p",Plus (Mult(Numeric 2,Const (Symbolic "h")),Const (Symbolic("eps"))) ;
            "balance", Plus (Const (Symbolic "A"), Plus (Minus(Mult (Numeric 2,Const (Symbolic "d"))), Minus (Mult (Numeric 2,Const (Symbolic "e")))))]
     ; [40], ["p",Plus (Mult(Numeric 2,Const (Symbolic "h")),Const (Symbolic("eps"))) ;
            "balance", Plus (Const (Symbolic "A"), Plus (Minus(Mult (Numeric 2,Const (Symbolic "d"))), Minus (Mult (Numeric 2,Const (Symbolic "e")))))]
     ; [29], ["p",Mult(Numeric 2,Const (Symbolic "h")) ; "balance", Plus (Const (Symbolic "A"), Minus (Mult (Numeric 2,Const (Symbolic "e"))))]
     ; [32], ["p",Mult(Numeric 2,Const (Symbolic "h")) ; "balance", Plus (Const (Symbolic "A"), Plus(Minus (Mult (Numeric 2,Const (Symbolic "e"))),Const(Symbolic("a"))))]
     ; [30], ["p",Plus (Mult(Numeric 2,Const (Symbolic "h")),Const(Symbolic("eps"))) ; "balance", Plus (Const (Symbolic "A"), Minus (Mult (Numeric 2,Const (Symbolic "e"))))]
     ; [31], ["p",Plus (Mult(Numeric 2,Const (Symbolic "h")),Const(Symbolic("eps"))) ; "balance", Plus (Const (Symbolic "A"), Minus (Mult (Numeric 2,Const (Symbolic "e"))))]
     ; [33], ["p",Mult(Numeric 2,Const (Symbolic "h")) ;
            "balance", Plus (Const (Symbolic "A"), Plus (Minus(Var "d"), Minus (Mult (Numeric 2,Const (Symbolic "e")))))]
     ; [34], ["p",Mult(Numeric 2,Const (Symbolic "h")) ;
            "balance", Plus (Const (Symbolic "A"), Plus (Minus(Var "d"), Plus (Minus (Mult (Numeric 2,Const (Symbolic "e"))),Const(Symbolic("a")))))]
     ; [35], ["p",Plus (Mult(Numeric 2,Const (Symbolic "h")),Const(Symbolic("eps"))) ;
            "balance", Plus (Const (Symbolic "A"), Plus (Minus(Var "d"), Minus (Mult (Numeric 2,Const (Symbolic "e")))))]
     ; [36], ["p",Plus (Mult(Numeric 2,Const (Symbolic "h")),Const(Symbolic("eps"))) ;
            "balance", Plus (Const (Symbolic "A"), Plus (Minus(Var "d"), Minus (Mult (Numeric 2,Const (Symbolic "e")))))]
     ]

   let address0 = "truck"
   let address = DAddress address0

   let (transitions : transition list) =
     [ [1],[2],True,
         Output (DAddress "gb","bid",[Address address; Expr( Const (Symbolic "e"))])
     ; [2],[1], True, Input ("LOST", ["e"])
     ; [2],[3],True,Input ("WIN", [])
     ; [2],[4],True,Output (DAddress "gb","empty",[Address address])
     ; [4],[2],True,Input ("NOK", [])
     ; [3],[10],True,Output (DAddress "gb","empty",[Address address])
     ; [10],[11],True,Input ("OK", [])
     ; [11],[12],True,Tau
     ; [12],[13],True,
       Output (DAddress "incinerator","empty",[Address address; Expr( Const (Symbolic "p"))])
     ; [12],[1],True,Tau
     ; [11],[14],True,
       Output (DAddress "gb","bid",[Address address; Expr( Const (Symbolic "e"))])
     ; [14],[15],True,Output (DAddress "gb","empty",[Address address])
     ; [15],[14],True,Input ("NOK", [])
     ; [14],[16],True,Input ("WIN", [])
     ; [16],[17],True,Output (DAddress "gb","empty",[Address address])
     ; [17],[18],True,Input ("OK", [])
     ; [2],[5],True,
       Output (DAddress "gb","bid",[Address address; Expr(Plus (Const (Symbolic "e"),Const(Symbolic "d")))])
     ; [5],[6], True, Input ("LOST", ["e"])
     ; [6],[7],True,Input ("WIN", [])
     ; [7],[8],True,Output (DAddress "gb","empty",[Address address])
     ; [8],[9],True,Input ("OK", [])
     ]

   let automaton : automaton = (address0,[1],states,transitions)

   let _ =
    let ch = open_out "truck.dot" in
    output_string ch (pp_automaton automaton);
    close_out ch
 end
 *)

 let basiccitizen_bin = compose BasicCitizen.automaton Bin.automaton
 (*let basiccitizen_bin = compose BasicCitizen.automaton Bin.automaton
 let basictruck_bin = compose BasicTruck.automaton Bin.automaton
 let basiccitizen_basictruck_bin = compose BasicCitizen.automaton basictruck_bin*)
 let automata =
  [ (*"basiccitizen_bin",basiccitizen_bin
  ; "basictruck_bin",basictruck_bin
  ; "basiccitizen_basictruck_bin",basiccitizen_basictruck_bin
  ;*) "basiccitizen_bin",basiccitizen_bin
    ; "citizen",CalculusTest.automaton
  ; "test",CalculusTest.automaton2
  ]

 let _ =
  List.iter
   (fun (fn,au) ->
     let ch = open_out (fn ^ ".dot") in
     output_string ch (pp_automaton au) ;
     close_out ch ;
     ignore (Unix.system ("dot -Tpdf " ^ fn ^ ".dot -o " ^ fn ^ ".pdf"))
    ) automata
