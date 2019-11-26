open Lib

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

type bind_or_check_address =
 | Bind : (_ SmartCalculus.address) SmartCalculus.var -> bind_or_check_address
 | Check : (_ SmartCalculus.address) SmartCalculus.tagged_expr -> bind_or_check_address

type action =
 | Input : (*receiver:*)(_ SmartCalculus.address) * (*sender:*) bind_or_check_address * 'b label * 'b SmartCalculus.var_list -> action
 | Output : (*sender:*)(_ SmartCalculus.address) * (*receiver:*)(_ SmartCalculus.address) SmartCalculus.tagged_expr * 'b label * 'b SmartCalculus.expr_list -> action
 | Tau : action

type 's state = id * ('s * subst)
type transition = id * id * cond * action
type 's automaton = SmartCalculus.any_address list * id(*=initial state*) * 's state list * transition list

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
let pp_subst_bool (al,e) = String.concat " ; " (List.map pp_assignment al) ^ "  " ^ string_of_bool e

let pp_cond : bool SmartCalculus.expr -> string = function SmartCalculus.Value true -> "" | g -> SmartCalculus.pp_expr Bool g
let pp_action =
 function
  | Input (r,s,l,vl) ->
     SmartCalculus.pp_address r ^ "." ^
     pp_label l ^
     "[" ^ (match s with Bind a -> "?" ^ SmartCalculus.pp_var a | Check a -> SmartCalculus.pp_tagged_expr a ^ ".") ^ "]" ^
     "(" ^ String.concat "," (SmartCalculus.pp_var_list vl) ^ ")"
  | Output (r,aexpr,l,al) ->
     SmartCalculus.pp_address r ^ ":" ^
     SmartCalculus.pp_tagged_expr aexpr ^ "." ^ pp_label l ^
      "(" ^ String.concat "," (SmartCalculus.pp_expr_list (fst l) al) ^ ")"
  | Tau -> "tau"
let pp_state pp_stack i (id,(stack,al)) =
 "\"" ^ pp_id id ^ "\" [label=\"" ^
  pp_id id ^ String.concat ", " (List.map pp_assignment al) ^ "\n" ^ pp_stack stack ^
  "\"" ^
  (if i = id then " shape=\"rectangle\"" else "") ^
 "]"

let pp_state_list pp_stack sp = (List.map (pp_state pp_stack) sp)

let color_of_action = function Input _ -> "red" | Output _ -> "blue" | Tau -> "black"
let pp_transition (s,d,c,a) =
 "\"" ^ pp_id s ^ "\" -> \"" ^ pp_id d ^ "\" [label=\"" ^
  pp_action a ^ "\n" ^ pp_cond c ^ "\" color=\"" ^
  color_of_action a ^ "\"]"
let pp_automaton pp_stack ((al, i, sl, tl) : 's automaton) =
 "digraph \"" ^  String.concat "*" (List.map SmartCalculus.pp_any_address al) ^ "\" {\n" ^
 String.concat "\n" (List.map (pp_state pp_stack i) sl) ^ "\n" ^
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
     let aexpr =
      match aexpr with
       | Bind _ -> aexpr
       | Check x -> Check (apply_subst_tagged_expr subst x) in
     Input (r, aexpr, l, vl)
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

let (@@) (zero1,ass1) (zero2,ass2) =
 assert(zero1 || zero2) ;
 zero1 && zero2, ass1 @ ass2

let (===) (e : ('a SmartCalculus.address) SmartCalculus.tagged_expr) (a : SmartCalculus.any_address) =
 match snd e with
  | SmartCalculus.Value b -> SmartCalculus.AnyAddress b = a
  | _ -> false

let rec make_identity_subst : type b. b SmartCalculus.var_list -> subst =
 function
    SmartCalculus.VNil -> []
  | SmartCalculus.VCons(v,tl) -> Assignment(v,SmartCalculus.Var v) :: make_identity_subst tl

let change_sub (sub : subst) : action -> subst =
 function
  | Input(_,_,_,vl) -> make_identity_subst vl @ sub
  | Tau
  | Output _ -> sub

let rec add_transition id1' id2' ~sub cond assign action id ((a1,_,sl1,tl1) as au1 : bool automaton) ((a2,_,sl2,tl2) as au2 : bool automaton) (sp : _ state list) tp =
 try
  let id' = id1' @ id2' in
  let cond = apply_subst_expr sub cond in
  let cond =
   let ground_cond =
    apply_subst_expr sub (apply_subst_expr (snd assign) cond) in
   match SmartCalculus.eval_cond ground_cond with SmartCalculus.T -> SmartCalculus.Value true | M -> cond | F -> raise Skip in
  let action = apply_subst_action sub action in
  let s12' = List.assoc id1' sl1 @@ List.assoc id2' sl2 in
  let s12' = fst s12',apply_subst_subst sub (snd s12') in
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

and move_state ~sub (au1 : bool automaton) (au2 : bool automaton) id id1 id2 sp tp =
 let sp,tp = move1 ~sub au1 au2 id id1 id2 sp tp in
 let sp,tp = move2 ~sub au1 au2 id id1 id2 sp tp in
 let sp,tp = interact1in_2out ~sub au1 au2 id id1 id2 sp tp in
 let sp,tp = interact2in_1out ~sub au1 au2 id id1 id2 sp tp in
 sp,tp

and move1 ~sub ((_,_,sl1,tl1) as au1 : bool automaton) ((a2,_,sl2,tl2) as au2 : bool automaton) id id1 id2 sp tp =
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

and movex your_ass other_ass the_others moves id1' id2' ~sub ((a1,_,sl1,tl1) as au1 : bool automaton) ((a2,_,sl2,tl2) as au2 : bool automaton) id sp tp =
 let assign = your_ass @@ other_ass in
 let can_fire =
  function
   | Tau | Input (_,Bind _,_,_) -> true
   | Input (_,Check d,_,_) ->
      let d = apply_subst_tagged_expr sub (apply_subst_tagged_expr (snd your_ass) d) in
      List.for_all (fun a -> not (d === a)) the_others
   | Output(r,d,_,_) ->
      (is_contract r || fst assign) &&
      let d = apply_subst_tagged_expr sub (apply_subst_tagged_expr (snd your_ass) d) in
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

and interact1in_2out ~sub ((a1,_,sl1,tl1) as au1 : bool automaton) ((a2,_,sl2,tl2) as au2 : bool automaton) id id1 id2 sp tp =
let ass_in = List.assoc id1 sl1 in
let ass_out = List.assoc id2 sl2 in
 let zero = fst ass_in && fst ass_out in
 let moves1 =
  List.filter (function (s,_,_,Input _) -> s = id1 | _ -> false) tl1 in
 let moves2 =
  List.filter
   (function
       (s,_,_,Output (r,d,_,_)) ->
         (is_contract r || zero) &&
         let d =
          apply_subst_tagged_expr sub (apply_subst_tagged_expr (snd (List.assoc id2 sl2)) d) in
         s = id2 && List.exists (fun a -> d === a) a1
     | _ -> false) tl2 in
 let id1' din _ = din in
 let id2' _ don = don in
 interact_in_out id1' id2' moves1 moves2 ass_in ass_out ~sub au1 au2 id sp tp

and interact2in_1out ~sub ((a1,_,sl1,tl1) as au1) ((a2,_,sl2,tl2) as au2) id id1 id2 sp tp =
 let ass_in = List.assoc id2 sl2 in
 let ass_out = List.assoc id1 sl1 in
 let zero = fst ass_in && fst ass_out in
 let moves2 =
  List.filter (function (s,_,_,Input _) -> s = id2 | _ -> false) tl2 in
 let moves1 =
  List.filter
   (function
       (s,_,_,Output (r,d,_,_)) ->
         (is_contract r || zero) &&
         let d =
          apply_subst_tagged_expr sub (apply_subst_tagged_expr (snd (List.assoc id1 sl1)) d) in
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
            apply_subst_tagged_expr sub (apply_subst_tagged_expr (snd ass_out) rec_out) === (SmartCalculus.AnyAddress receiver) &&
            (match sender with
                Bind _ -> true
              | Check aexpr ->
                 apply_subst_tagged_expr sub (apply_subst_tagged_expr (snd ass_in) aexpr)
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

let compose ((a1,i1,sl1,tl1) as au1 : bool automaton) ((a2,i2,sl2,tl2) as au2 : bool automaton) =
 let id = i1 @ i2 @ [mk_fresh ()] in
 let s1 = List.assoc i1 sl1 in
 let s2 = List.assoc i2 sl2 in
 let s = id, s1 @@ s2 in
 let sp,tp = move_state ~sub:[] au1 au2 id i1 i2 [s] [] in
 a1 @ a2,id,sp,tp

end

module RemoveTau = struct
 let add_transition id2 s2 tr (sp,tp) =
  let tp = if List.mem tr tp then tp else tr::tp in
  if List.mem s2 sp then
   None,(sp,tp)
  else
   Some id2,(s2::sp,tp)

 let rec visit (sp0,tp0 as au0) id idtau condtau res =
  let adj = List.filter(function (id',_,_,_) -> id' = idtau) tp0 in
  List.fold_left (fun res (_,id2,cond,action) ->
   let cond = SmartCalculus.smart_and condtau cond in
   match action with
     Presburger.Tau ->
      visit au0 id id2 cond res
   | Presburger.Input _ | Presburger.Output _ ->
      let s2 = List.assoc id2 sp0 in
      let new_state,res = add_transition id2 (id2,s2) (id,id2,cond,action) res in
      (match new_state with
          None -> res
        | Some id ->
           visit au0 id id (SmartCalculus.Value true) res)
  ) res adj

 let remove_tau (addrs,init,sp,tp : 's Presburger.automaton) :
  's Presburger.automaton
 =
  let sinit = init, List.assoc init sp in
  let sp,tp =
   visit (sp,tp) init init (SmartCalculus.Value true) ([sinit],[]) in
  addrs,init,sp,tp

end

module PresburgerOfSmartCalculus =
struct

exception Skip

type any_var = AnyVar : 'a SmartCalculus.var -> any_var

let pp_any_stack_backtrack (s,bt) =
 SmartCalculus.pp_any_stack s ^ "\n" ^
  match bt with None -> "_" | Some id -> Presburger.pp_id id

let rec change_in_assignment_list : type a. a SmartCalculus.field -> a SmartCalculus.expr -> Presburger.assignment list -> Presburger.assignment list =
  fun v value -> function
    [] -> assert false
  | Presburger.Assignment(v',_) as hd::tl ->
     match SmartCalculus.eq_tag (fst v) (fst v') with
      | Some SmartCalculus.Refl when snd v = snd v' -> Presburger.Assignment(v,value)::tl
      | _ ->  hd::change_in_assignment_list v value tl

(* ignore assignments to "_" *)
let change_in_assignment_list f e subst =
 if snd f = "_" then subst else change_in_assignment_list f e subst

let make_store stack backtrackto ass1 (_,ass2) =
 (SmartCalculus.AnyStack stack,backtrackto),
  List.fold_left
   (fun ass2 (Presburger.Assignment(v,value)) ->
      change_in_assignment_list v value ass2) ass2 ass1

(* assign is the NEW assignment after the transition
   returns (new_states_generated,(sp',tp')) *)
let add_transition ?backtrackto cond (assign : Presburger.subst) action id stack
 ((sp : (SmartCalculus.any_stack * Presburger.id option) Presburger.state list),(tp : Presburger.transition list)) =
 try
  let store = List.assoc id sp in
  let backtrackto =
   match backtrackto with Some bt -> bt | None -> snd (fst store) in
  let action = Presburger.apply_subst_action (snd store) action in
  let cond =
   let ground_cond = Presburger.apply_subst_expr (snd store) cond in
   match SmartCalculus.eval_cond ground_cond with SmartCalculus.T -> SmartCalculus.Value true | M -> cond | F -> raise Skip in
  let id' = [Presburger.mk_fresh ()] in
  let assign = make_store stack backtrackto assign store in
  let (id',_) as s',is_new =
   try List.find (fun (idx,sx) -> sx = assign) sp,false
   with Not_found -> (id',assign),true in
  let tr = id,id',cond,action in
  let tp = if List.mem tr tp then tp else tr::tp in
  if is_new then
   [SmartCalculus.AnyStack stack,id'],(s'::sp,tp)
  else
   [],(sp,tp)
 with Skip -> [],(sp,tp)

let add_backtrack_to backtrackto cond action id
 ((sp : (SmartCalculus.any_stack * Presburger.id option) Presburger.state list),(tp : Presburger.transition list)) =
 let store = List.assoc id sp in
 assert (snd (fst store) = Some backtrackto);
 let action = Presburger.apply_subst_action (snd store) action in
 let tr = id,backtrackto,cond,action in
 let tp = if List.mem tr tp then tp else tr::tp in
 (sp,tp)

let return_ok ty = SmartCalculus.TCons (ty, TNil), "__return_ok__"
let return_ko = SmartCalculus.TNil, "__return_ko__"

let (+:) h t = SmartCalculus.SComp(SmartCalculus.Stm h,t)
let rec (@:) l = List.fold_right (+:) l

let do_substitution : type a b. (a,b) SmartCalculus.program -> b SmartCalculus.expr_list -> SmartCalculus.stm list * a SmartCalculus.expr =
 fun (vars,stm_list,ret) exprl ->
  let subst = Presburger.make_subst vars exprl in
  List.map (Presburger.apply_subst_stm subst) stm_list,
   Presburger.apply_subst_expr subst ret

let optimize_stack_call stack f prog exprl =
 let stml,ret = do_substitution prog exprl in
 let optimized_stack =
  (fun (type c) (stack : c SmartCalculus.stack) : (c SmartCalculus.stack) option ->
    match stack with
       SmartCalculus.Return (_,SmartCalculus.Var g)
        when snd f = snd g ->
        map_option (fun _ -> stml @: SmartCalculus.Return(fst f,ret))
         (SmartCalculus.eq_tag (fst g) (fst f))
     | SmartCalculus.InitialCall ((_,SmartCalculus.Var g),addr)
        when snd f = snd g ->
        map_option
         (fun _ -> stml @: SmartCalculus.InitialCall((fst f,ret),addr))
         (SmartCalculus.eq_tag (fst g) (fst f))
     | _ -> None) stack in
 match optimized_stack with
    None -> stml @: SmartCalculus.Assign(f,(SmartCalculus.Expr ret))+:stack
  | Some optimized_stack -> optimized_stack


let rec expr_list_of_var_list : type b. b SmartCalculus.var_list -> b SmartCalculus.expr_list =
 function
    SmartCalculus.VNil -> ENil
  | SmartCalculus.VCons(v,tl) -> ECons(SmartCalculus.Var v,expr_list_of_var_list tl)

let human_call caller tag prog exprl =
 let stml,ret = do_substitution prog exprl in
 stml @: SmartCalculus.InitialCall((tag,ret),caller)

let grow_idle address methods id res =
 List.fold_left
  (fun (next_states,res) (SmartCalculus.AnyMethodDecl(meth,program)) ->
    let tag = fst3 meth in
    let exprl = expr_list_of_var_list (fst3 program) in
    let caller = SmartCalculus.HumanAddress, "caller" in
    let stack = human_call caller tag program exprl in
    let label = snd3 meth,third3 meth in
    let next_state,res =
     add_transition ~backtrackto:(Some id) (SmartCalculus.Value true) []
      (Presburger.Input(address,Bind caller,label,fst3 program)) id stack res in
    next_state @ next_states, res
  ) ([],res) methods

(* takes:
    address = ???
    id = id del nodo che deve eseguire stack
    stack = to be executed
    sp = list of states
    tp = list of transitions
   returns
    sp,tp
*)
let rec grow : type actor. _ -> _ -> _ ->
 (actor SmartCalculus.stack as 'stack) -> (((SmartCalculus.any_stack * Presburger.id option) Presburger.state list * _) as 'b) -> 'b =
 fun address methods id stm_stack (sp,_tp as res) ->
 let next_states,res =
 match stm_stack with
  | SmartCalculus.Zero -> grow_idle address methods id res
  | SmartCalculus.InitialCall(ret,addr) ->
     let ((_,backtrackto),_) = List.assoc id sp in
     let next_states1,res =
      match backtrackto with
         None -> assert false
       | Some bkto ->
          [],add_backtrack_to bkto
           (SmartCalculus.Eq(fst ret,snd ret,Fail))
           (Presburger.Output(address,(fst addr,SmartCalculus.Var addr),return_ko,ENil)) id res in
     let next_states2,res =
      add_transition ~backtrackto:None
      (SmartCalculus.Not (Eq(fst ret,snd ret,Fail)))
      []
      (Presburger.Output(address,(fst addr,SmartCalculus.Var addr),return_ok (fst ret),ECons(snd ret,ENil)))
      id Zero res in
     next_states1 @ next_states2,res
  | SmartCalculus.Return _ -> [],res
  | SmartCalculus.SComp(entry,stack) ->
      match entry with
       | SmartCalculus.Stm stm ->
          (match stm with
           | SmartCalculus.IfThenElse(c,stm1,stm2) ->
              let next_state1,res =
               add_transition c [] Presburger.Tau id (stm1+:stack) res in
              let next_state2,res =
               add_transition (SmartCalculus.Not c) [] Presburger.Tau id
                (stm2+:stack) res in
              next_state1 @ next_state2,res
           | SmartCalculus.Assign(f,SmartCalculus.Expr e) ->
              let store = List.assoc id sp in
              let e = Presburger.apply_subst_expr (snd store) e in
              let assign = [Presburger.Assignment(f,e)] in
              add_transition (SmartCalculus.Value true) assign
               Presburger.Tau id stack res
           | SmartCalculus.Assign(f,SmartCalculus.Call(None,meth,exprl)) ->
              let body = SmartCalculus.lookup_method meth methods in
              let store = List.assoc id sp in
              let exprl= Presburger.apply_subst_expr_list (snd store) exprl in
              let stack = optimize_stack_call stack f body exprl in
              add_transition (SmartCalculus.Value true) []
               Presburger.Tau id stack res
           | SmartCalculus.Assign(f,SmartCalculus.Call(Some receiver,meth,exprl)) ->
              let label = let (_,tags,name) = meth in tags,name in
              let stack =
               SmartCalculus.SComp(SmartCalculus.AssignBullet(f,receiver),stack) in
              add_transition (SmartCalculus.Value true) []
               (Presburger.Output(address,(ContractAddress,receiver),label,exprl))
               id stack res
           | SmartCalculus.Comp(stm1,stm2) ->
             let stack = (stm1+:(stm2+:stack)) in
             add_transition (SmartCalculus.Value true) [] Presburger.Tau
              id stack res
           | SmartCalculus.Choice(stm1,stm2) ->
              let var = SmartCalculus.Int, "__choice__" ^ string_of_int (Presburger.mk_fresh ()) in
              let cond n = SmartCalculus.Eq (SmartCalculus.Int, SmartCalculus.Var var, SmartCalculus.Value n) in
              let next_state1,res =
               add_transition (cond 0) [] Presburger.Tau id
                (stm1+:stack) res in
              let next_state2,res =
               add_transition (cond 1) [] Presburger.Tau id
                (stm2+:stack) res in
              next_state1 @ next_state2, res)
     | SmartCalculus.AssignBullet(f,receiver) ->
        let var = fst f, "__ra__ " ^ string_of_int (Presburger.mk_fresh ()) in
        let ((_,backtrackto),_) = List.assoc id sp in
        (* ko *)
        let new_states1,res =
         match backtrackto with
            None ->
             add_transition (SmartCalculus.Value true)
               [Presburger.Assignment(f,SmartCalculus.Fail)]
               (Presburger.Input(address,Check (ContractAddress,receiver),return_ko,SmartCalculus.VNil)) id stack res
          | Some bkto ->
             [],add_backtrack_to bkto
              (SmartCalculus.Value true)
              (Presburger.Input(address,Check (ContractAddress,receiver),return_ko,SmartCalculus.VNil)) id res in
        (* ok *)
        let new_states2,res =
         add_transition
          (SmartCalculus.Not (Eq(fst var,Var var,Fail)))
          [Presburger.Assignment(f,SmartCalculus.Var var)]
          (Presburger.Input(address,Check (ContractAddress,receiver),return_ok (fst f),SmartCalculus.VCons(var,VNil))) id stack res in
        new_states1 @ new_states2,res
 in
 List.fold_left
   (fun res (SmartCalculus.AnyStack stack,id) ->
     grow address methods id stack res) res next_states

let actor_to_automaton address methods store stack : (SmartCalculus.any_stack * Presburger.id option) Presburger.automaton =
 let id = [Presburger.mk_fresh ()] in
 let store = List.map (function SmartCalculus.Let(x,v) -> Presburger.Assignment(x,SmartCalculus.Value v)) store in
 let sp = [id,((SmartCalculus.AnyStack stack,None),store)] in
 let sp,tp = grow address methods id stack (sp,[]) in
  [SmartCalculus.AnyAddress address], id, sp, tp

let human_to_automaton (address,methods,store,stack : SmartCalculus.a_human) : (SmartCalculus.any_stack * Presburger.id option) Presburger.automaton =
 actor_to_automaton address methods store stack

let contract_to_automaton (address,methods,store : SmartCalculus.a_contract) : (SmartCalculus.any_stack * Presburger.id option) Presburger.automaton =
 actor_to_automaton address methods store (SmartCalculus.Zero)

end

 (*** Examples ***)
 module CalculusTest = struct
  open SmartCalculus

  let id = Int,TCons(Int,TNil),"id"
  let throw = Int,TCons(Int,TNil),"throwAway"
  let res = Int,"res"
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
                   ,Comp(Assign((Int,"d"),Call (Some (Value(Contract "foo")),(Int,TNil,"foo"),ENil)),Assign((Int,"x"),Expr(Symbol("y"))))))))

  let test_automaton =
    PresburgerOfSmartCalculus.human_to_automaton
      (Human "test"
         ,[AnyMethodDecl (id,(VCons((Int,"w"),VNil),[],Var(Int,"w")));
          AnyMethodDecl (loop,(VNil,[loop_body],Var(Int,"res")))]
      , [Let((Int,"x"),0)
        ;Let((Int,"r"),0)
        ;Let((Int,"b"),0)
        ;Let((Int,"d"),0)]
      ,SComp(Stm (Assign(res,Call(None,loop,ENil))),Return(Int, Var res)))

  let balance = Int,"balance"
  let weight = Int,"weight"
  let _D = Symbol "D"
  let incinerator = Value (Contract "incinerator")
  let banca = Value (Contract "banca")
  let bin = Value (Contract "garbage_bin")
  let dep = Int,TCons(Int,TNil),"dep"
  let fee = Int,TCons(Int,TNil),"fee"
  let save = Int,TCons(Int,TNil),"save"
  let tmp = Int,"_"

  let v1 = Int,"v1"
  let v2 = Int,"v2"

  let simple_citizen_body =
    Comp(
        (* butto 1 kg nel rusco *)
        Choice(Assign(v1,Call (Some bin,dep,ECons( Value 1,ENil))),Assign(v1,Expr(Value 0))),
        (* butto 1 kg nel rusco *)
        Comp(Choice(Assign(v2,Call (Some bin,dep,ECons( Value 1,ENil))),
               (* butto 1 kg per strada *)
               Assign(v2,Expr(Value 0))),
      Comp(Assign(tmp,Call (Some banca,save,ECons((Plus(Var v1, Var v2)),ENil))),
           Comp(Assign(v1,Expr(Value 0)),
                Comp(Assign(v2,Expr(Value 0)),
                     Assign(tmp,Call(None,loop,ENil)))))))

  let automaton =
    PresburgerOfSmartCalculus.human_to_automaton
      (Human "simple_citizen"
      ,[AnyMethodDecl (loop,(VNil,[simple_citizen_body],Var tmp))]
      , [Let(v1,0)
        ;Let(v2,0)]
      ,SComp(Stm (Assign(tmp,Call(None,loop,ENil))),Return(Int, Var tmp)))


  let notau_automaton = RemoveTau.remove_tau automaton


  let truck = Value (Contract "truck")
  let empty = Int,TCons(Int,TNil),"empty"
  let res = Int,"res"

  let dep = Int,TCons(Int,TNil),"dep"

  let h = Int, "h"
  let a = Int, "a"
  let k = Symbol "k"

  let simple_dep_body =
    IfThenElse(Eq(Int,Var h,Value 0),
               Comp(Assign(h,Expr(Value 1)),
                    Assign(res,Expr(Plus(Var a, Minus(k))))),
               Comp(Assign(tmp,Call (Some banca,save,ECons((Plus(Var a, k)),ENil))),
                    Comp(Assign(a,Expr(Var tmp)),
                    Comp(Assign(tmp,Call (Some truck,empty,ECons(Value 0,ENil))),
                         Assign(res,Expr(k))))))

  let contract_automaton =
    PresburgerOfSmartCalculus.contract_to_automaton
      (Contract "bin"
      ,[
        AnyMethodDecl (dep,(VCons((Int,"x"),VNil),[simple_dep_body],Var(res)))
      ]
      ,[Let(h,0);
        Let(a,0);
        Let(res,0)
      ])

  let notau_bin = RemoveTau.remove_tau contract_automaton

end

open SmartCalculus
open Presburger

let dep = (TCons(Int,TCons(HumanAddress,TNil)),"dep")

 (*** Garbage Collection Example ***)
 module Bin = struct
  let (states : bool state list) =
    [ [1], (true,[Assignment((Int,"gp"),Value(0)) ; Assignment((Int,"gbalance"),Symbol("D"))])
    ; [2], (false,[Assignment((Int,"gp"),Value(0)) ; Assignment((Int,"gbalance"),Symbol("D")) ; Assignment((Int,"cur_q"),Var(Int,"q"))
            ; Assignment((HumanAddress,"ID"),Var(HumanAddress,"id"))])
    ; [3], (true,[Assignment((Int,"gp"),Value(1)) ; Assignment((Int,"gbalance"),Plus(Symbol("D"),Minus(Symbol("R"))))])
    ; [4], (false,[Assignment((Int,"gp"),Value(1)) ; Assignment((Int,"gbalance"),Plus(Symbol("D"),Minus(Symbol("R")))) ; Assignment((Int,"cur_q"),Var(Int,"q'"))
            ; Assignment((HumanAddress,"ID"),Var(HumanAddress,"id'"))])
    ; [5], (true,[Assignment((Int,"gp"),Value(2)) ; Assignment((Int,"gbalance"),Plus(Symbol("D"),Minus(Mult(Numeric(2),Symbol("R")))))])
    ; [6], (true,[Assignment((Int,"gp"),Value(2)) ; Assignment((Int,"gbalance"),Plus(Symbol("D"),Minus(Mult(Numeric(2),Symbol("R")))))
            ; Assignment((Int,"of"),Var(Int,"e'")); Assignment((HumanAddress,"ID"),Var(HumanAddress,"gt_id"))])
    ; [7], (true,[Assignment((Int,"gp"),Value(2)) ; Assignment((Int,"gbalance"),Plus(Symbol("D"),Minus(Mult(Numeric(2),Symbol("R")))))
            ; Assignment((Int,"of"),Var(Int,"e")); Assignment((HumanAddress,"ID"),Var(HumanAddress,"gt_id"))
            ; Assignment((Int,"of'"),Var(Int,"e'")); Assignment((HumanAddress,"ID'"),Var(HumanAddress,"gt_id'"))])
    ; [8], (true,[Assignment((Int,"gp"),Value(2)) ; Assignment((Int,"gbalance"),Plus(Symbol("D"),Minus(Mult(Numeric(2),Symbol("R")))))
            ; Assignment((Int,"of"),Var(Int,"e")); Assignment((HumanAddress,"ID"),Var(HumanAddress,"gt_id"))
            ; Assignment((Int,"of'"),Var(Int,"e'")); Assignment((HumanAddress,"ID'"),Var(HumanAddress,"gt_id'"))])
    ; [9], (true,[Assignment((Int,"gp"),Value(2)) ; Assignment((Int,"gbalance"),Plus(Symbol("D"),Minus(Mult(Numeric(2),Symbol("R")))))
            ; Assignment((Int,"of"),Var(Int,"e")); Assignment((HumanAddress,"ID"),Var(HumanAddress,"gt_id"))
            ; Assignment((Int,"of'"),Var(Int,"e'")); Assignment((HumanAddress,"ID'"),Var(HumanAddress,"gt_id'"))])
    ; [10], (false,[Assignment((Int,"gp"),Value(0)) ; Assignment((Int,"gbalance"),Plus(Symbol("D"),Minus(Mult(Numeric(2),Symbol("R")))))
            ; Assignment((Int,"of"),Var(Int,"e")); Assignment((HumanAddress,"ID"),Var(HumanAddress,"gt_id"))
            ; Assignment((Int,"of'"),Var(Int,"e'")); Assignment((HumanAddress,"ID'"),Var(HumanAddress,"gt_id'"))])
    ; [11], (true,[Assignment((Int,"gp"),Value(0))
            ; Assignment((Int,"gbalance"),Plus(Symbol("D"),Plus(Minus(Mult(Numeric(2),Symbol("R"))),Max(Var(Int,"of"), Var(Int,"of'")))))
            ; Assignment((Int,"of"),Var(Int,"e")); Assignment((HumanAddress,"ID"),Var(HumanAddress,"gt_id"))
            ; Assignment((Int,"of'"),Var(Int,"e'")); Assignment((HumanAddress,"ID'"),Var(HumanAddress,"gt_id'"))])
   ]

  let (transitions : transition list) =
    [ [1],[2],Value true,
      Input (Contract "garbage_bin",Bind (HumanAddress,"caller"), dep, VCons((Int,"q"),VCons((HumanAddress,"id"),VNil)))
    ; [2],[1],Gt(Var (Int,"cur_q"),Value (2)),
      Output (Contract "garbage_bin", (HumanAddress,Var(HumanAddress,"ID")),(TNil,"NOK"),ENil)
    ; [2],[3],Eq(Int,Var(Int, "cur_q"),Value (1)),
      Output (Contract "garbage_bin",(HumanAddress,Var (HumanAddress,"ID")),(TCons(Int ,TNil),"OK"), ECons(Symbol("R"),ENil))
    ; [2],[5],Eq(Int,Var(Int, "cur_q"),Value(2)),
      Output (Contract "garbage_bin",(HumanAddress,Var( HumanAddress,"ID")),(TCons(Int ,TNil),"OK"),ECons(Mult( Numeric 2, Symbol("R")),ENil))
    ; [3],[4],Value true,
      Input (Contract "garbage_bin",Bind (HumanAddress,"caller"), dep, VCons((Int,"q'"),VCons((HumanAddress,"id'"),VNil)))
    ; [4],[3],Gt(Var (Int, "cur_q"),Value (2)),
      Output (Contract "garbage_bin",(HumanAddress,Var (HumanAddress, "ID")),(TNil,"NOK"),ENil)
    ; [4],[5],Eq(Int,Var (Int, "cur_q"), Value (1)),
      Output (Contract "garbage_bin",(HumanAddress,Var(HumanAddress, "ID")),(TCons(Int ,TNil),"OK"),ECons(Symbol("R"),ENil))
    ; [5],[6],Value true,
      Input (Contract "garbage_bin",Bind (HumanAddress,"caller"), (TCons(Int,TCons(HumanAddress,TNil)),"bid"), VCons((Int,"e"),VCons((HumanAddress,"gt_id"),VNil)))
    ; [6],[5],Gt(Mult(Numeric 2, Var(Int, "R")), Var (Int,"of")),
      Output (Contract "garbage_bin",(HumanAddress,Var (HumanAddress, "ID")),(TCons(Int ,TNil),"lost"),ECons(Var(Int,"of"),ENil))
    ; [6],[7],Geq(Var (Int, "of"),Mult( Numeric 2, Var(Int, "R"))),
      Input (Contract "garbage_bin",Bind (HumanAddress,"caller"), (TCons(Int,TCons(HumanAddress,TNil)),"bid"), VCons((Int,"e'"),VCons((HumanAddress,"gt_id'"),VNil)))
    ; [7],[8],Geq(Var (Int,"of"), Var(Int, "of'")),
      Output (Contract "garbage_bin", (HumanAddress,Var (HumanAddress,"ID'")),(TCons(Int,TNil),"LOST"),ECons(Var(Int,"of'"),ENil))
    ; [7],[8],Gt(Var (Int,"of"), Var(Int, "of'")),
      Output (Contract "garbage_bin",(HumanAddress,Var (HumanAddress,"ID")), (TCons(Int ,TNil),"LOST"),ECons(Var(Int,"of"),ENil))
    ; [8],[9],Geq(Var (Int,"of"), Var(Int, "of'")),
      Output (Contract "garbage_bin",(HumanAddress,Var (HumanAddress,"ID")),(TNil,"WIN"),ENil)
    ; [8],[9],Geq(Var (Int,"of"), Var(Int, "of'")),
      Output (Contract "garbage_bin",(HumanAddress,Var (HumanAddress,"ID'")),(TNil,"WIN"),ENil)
    ; [9],[10],Value true,
      Input (Contract "garbage_bin",Bind (HumanAddress,"caller"), (TCons(String ,TNil),"empty"), (*[AVar "id"]*)VCons((String,"id"),VNil))
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

  let automaton : bool automaton = ([AnyAddress (Contract( "garbage_bin"))],[1],states,transitions)

   let _ =
    let ch = open_out "garbage_bin.dot" in
    output_string ch (pp_automaton pp_bool automaton);
    close_out ch

 end

module Citizen = struct
  let (states : bool state list) =
    [ [1], (true,[Assignment((Int,"cp"),Value(0)); Assignment((Int,"balance"),Symbol("D"))])
    ; [2], (true,[Assignment((Int,"cp"),Value(2)); Assignment((Int,"balance"),Value(0))])
    ; [3], (true,[Assignment((Int,"cp"),Value(1)); Assignment((Int,"balance"),Value(0))])
    ; [4], (true,[Assignment((Int,"cp"),Value(1)); Assignment((Int,"balance"),Value(0))])
    ; [5], (true,[Assignment((Int,"cp"),Value(1)); Assignment((Int,"balance"),Value(0))])
    ; [6], (true,[Assignment((Int,"cp"),Value(1)); Assignment((Int,"balance"),Value(0))])
    ; [7], (true,[Assignment((Int,"cp"),Value(0)); Assignment((Int,"balance"),Var(Int,"a"))])
    ; [8], (true,[Assignment((Int,"cp"),Value(1)); Assignment((Int,"balance"),Var(Int,"a"))])
    ; [9], (true,[Assignment((Int,"cp"),Value(0)); Assignment((Int,"balance"),Value(0))])
    ;[10], (true,[Assignment((Int,"cp"),Value(0)); Assignment((Int,"balance"),Value(0))])
    ;[11], (true,[Assignment((Int,"cp"),Value(0)); Assignment((Int,"balance"),Var(Int,"a"))])
    ;[12], (true,[Assignment((Int,"cp"),Value(0)); Assignment((Int,"balance"),Var(Int,"a"))])
    ;[13], (true,[Assignment((Int,"cp"),Value(0)); Assignment((Int,"balance"),Var(Int,"a"))])
    ;[14], (true,[Assignment((Int,"cp"),Value(0)); Assignment((Int,"balance"),Mult(Numeric 2,Var(Int,"a")))])
    ]

    let address0 = Human "citizen"
    let address = Value address0
    let gb = ContractAddress,Value (Contract "garbage_bin")
    let incinerator = ContractAddress,Value (Contract "incinerator")
    let banca = ContractAddress,Value (Contract "banca")

  let (transitions : transition list) =
    [ [1],[2],Value true,Output (address0, incinerator,(TCons(Int,TNil),"fee"),ECons(Var(Int,"D"),ENil))
    ; [2],[3],Value true,Output (address0,gb,dep,ECons( Value 2, ECons(address,ENil)))
    ; [3],[2],Value true,Input (address0,Check (gb),(TNil,"NOK"), VNil)
    ; [2],[4],Value true,Output (address0,gb,dep,ECons( Value 1, ECons(address,ENil)))
    ; [4],[2],Value true,Input (address0,Check (gb),(TNil,"NOK"), VNil)
    ; [2],[5],Value true, Tau
    ; [2],[6],Value true, Tau
    ; [3],[7], Value true,Input (address0,Check (gb),(TCons(Int,TNil),"OK"), VCons((Int,"a"),VNil))
    ; [4],[8], Value true,Input (address0,Check (gb),(TCons(Int,TNil),"OK"), VCons((Int,"a"),VNil))
    ; [8],[12], Value true, Output (address0,gb,dep,ECons(Value 1, ECons(address,ENil)))
    ; [12],[8],Value true,Input (address0,Check (gb),(TNil,"NOK"), VNil)
    ; [8],[13],Value true, Tau
    ; [12],[14],Value true,Input (address0,Check (gb),(TCons(Int,TNil),"OK"), VCons((Int,"a"),VNil))
    ; [5],[9],Value true, Output (address0,gb,dep,ECons(Value 1, ECons(address,ENil)))
    ; [9],[5],Value true,Input (address0,Check (gb),(TNil,"NOK"), VNil)
    ; [5],[10],Value true, Tau
    ; [9],[11],Value true,Input (address0,Check (gb),(TCons(Int,TNil),"OK"), VCons((Int,"a"),VNil))
    ; [7],[1], Value true,Output (address0,banca,(TCons(Int,TNil),"save"),ECons( Var(Int,"balance"),ENil))
    ; [14],[1], Value true,Output (address0,banca,(TCons(Int,TNil),"save"),ECons( Var(Int,"balance"),ENil))
    ; [13],[1], Value true,Output (address0,banca,(TCons(Int,TNil),"save"),ECons( Var(Int,"balance"),ENil))
    ; [11],[1],Value true,Output (address0,banca,(TCons(Int,TNil),"save"),ECons( Var(Int,"balance"),ENil))
    ; [10],[1], Value true,Output (address0,banca,(TCons(Int,TNil),"save"),ECons( Var(Int,"balance"),ENil))
    ; [6],[1], Value true,Output (address0,banca,(TCons(Int,TNil),"save"),ECons( Var(Int,"balance"),ENil))
    ]

  let automaton : bool automaton = ([AnyAddress (address0)],[1],states,transitions)

  let _ =
    let ch = open_out "citizen.dot" in
    output_string ch (pp_automaton pp_bool automaton);
    close_out ch

end

module BasicCitizen = struct
  let (states : bool state list) =
    [ [1], (true,[Assignment((Int,"cp"),Value(0)); Assignment((Int,"cbalance"),Symbol("D"))])
    ; [2], (true,[Assignment((Int,"cp"),Value(2)); Assignment((Int,"cbalance"),Value(0))])
    ; [3], (true,[Assignment((Int,"cp"),Value(1)); Assignment((Int,"cbalance"),Value(0))])
    ; [4], (true,[Assignment((Int,"cp"),Value(1)); Assignment((Int,"cbalance"),Var(Int,"a"))])
    ; [5], (true,[Assignment((Int,"cp"),Value(0)); Assignment((Int,"cbalance"),Var(Int,"a"))])
    ; [6], (true,[Assignment((Int,"cp"),Value(0)); Assignment((Int,"cbalance"),Var(Int,"a"))])

    ]

  let address0 = Human "basiccitizen"
  let address = Value address0
  let gb = ContractAddress,Value (Contract "garbage_bin")
  let incinerator = ContractAddress,Value (Contract "incinerator")
  let banca = ContractAddress,Value (Contract "banca")

  let (transitions : transition list) =
    [ [1],[2],Value true,Output (address0, incinerator,(TCons(Int,TNil),"fee"),ECons(Var(Int,"D"),ENil))
    ; [2],[3],Value true,Output (address0,gb,dep,ECons( Value 1, ECons(address,ENil)))
    ; [3],[2],Value true,Input (address0,Check (gb),(TNil,"NOK"), VNil)
    ; [3],[4], Value true,Input (address0,Check (gb),(TCons(Int,TNil),"OK"), VCons((Int,"a"),VNil))
    ; [4],[5],Value true,Output (address0,gb,dep,ECons( Value 1, ECons(address,ENil)))
    ; [5],[4],Value true,Input (address0,Check (gb),(TNil,"NOK"), VNil)
    ; [5],[6], Value true,Input (address0,Check (gb),(TCons(Int,TNil),"OK"), VCons((Int,"a"),VNil))
    ; [6],[1], Value true,Output (address0,banca,(TCons(Int,TNil),"save"),ECons( Var(Int,"balance"),ENil))
    ]

  let automaton : bool automaton = ([AnyAddress (address0)],[1],states,transitions)

  let _ =
    let ch = open_out "basiccitizen.dot" in
    output_string ch (pp_automaton pp_bool automaton);
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
      ;*) "basiccitizen_bin",pp_automaton pp_bool basiccitizen_bin
    ; "basiccitizen",pp_automaton pp_bool BasicCitizen.automaton
    ; "basicbin",pp_automaton pp_bool Bin.automaton
    ; "test",pp_automaton PresburgerOfSmartCalculus.pp_any_stack_backtrack CalculusTest.test_automaton
    ; "simple_citizen",pp_automaton PresburgerOfSmartCalculus.pp_any_stack_backtrack CalculusTest.automaton
     ; "simple_citizen_notau",pp_automaton PresburgerOfSmartCalculus.pp_any_stack_backtrack CalculusTest.notau_automaton
    ; "bin_notau",pp_automaton PresburgerOfSmartCalculus.pp_any_stack_backtrack CalculusTest.notau_bin

    ; "bin",pp_automaton PresburgerOfSmartCalculus.pp_any_stack_backtrack CalculusTest.contract_automaton
  ]

 let _ =
  List.iter
   (fun (fn,au) ->
     let ch = open_out (fn ^ ".dot") in
     output_string ch au ;
     close_out ch ;
     ignore (Unix.system ("dot -Tpdf " ^ fn ^ ".dot -o " ^ fn ^ ".pdf"))
    ) automata
