(*** Presburger Automata ***)

type id = int list
type label = string
type var = string
type address = Contract of string | Human of string
let is_contract = function Contract _ -> true | Human _ -> false
type aexpr = DVar of var | DAddress of address
type const = Symbolic of string | Numeric of int
type expr =
 | Var of var
 | Const of const
 | Plus of expr * expr
 | Mult of const * expr
 | Minus of expr
 | Max of expr * expr
type actual = Expr of expr | String of string | Address of aexpr
type typed_var = EVar of var | AVar of var

type assignment = typed_var * actual
type cond =
 | Geq of expr * expr
 | Gt of expr * expr
 | Eq of actual * actual
 | And of cond * cond
 | Or of cond * cond
 | Not of cond
 | True

let smart_and c1 c2 =
 match c1,c2 with
  | True, c
  | c, True -> c
  | _,_ -> And(c1,c2)

type action =
 | Input of (*receiver:*)address * (*sender:*)aexpr option * label * typed_var list
 | Output of (*sender:*)address * (*receiver:*)aexpr * label * actual list
 | Tau

type state = id * (assignment list * bool(*= no actor running*))
type transition = id * id * cond * action
type automaton = address list * id(*=initial state*) * state list * transition list

(*** Serialization ***)
let pp_id l = String.concat "*" (List.map string_of_int l)
let pp_label l = l
let pp_var v = v
let pp_typed_var = function EVar v | AVar v -> pp_var v
let pp_address = function Contract a -> "C("^a^")" | Human a -> "H("^a^")"
let pp_aexpr = function DVar v -> pp_var v | DAddress a -> pp_address a
let pp_const = function Symbolic s -> s | Numeric n -> string_of_int n
let rec pp_expr =
 function
  | Var v -> pp_var v
  | Const c -> pp_const c
  | Plus (e1,e2) -> "(" ^ pp_expr e1 ^ " + " ^ pp_expr e2 ^ ")"
  | Mult (c,e) -> "(" ^ pp_const c ^ " * " ^ pp_expr e ^ ")"
  | Minus e -> "-" ^ pp_expr e
  | Max (e1,e2) -> "(max " ^ pp_expr e1 ^ " " ^ pp_expr e2 ^ ")"
let pp_actual =
 function
    Expr e -> pp_expr e
  | String s -> s
  | Address d -> pp_aexpr d
let pp_assignment (v,e) = pp_typed_var v ^ "=" ^ pp_actual e
let rec pp_cond =
 function
  | Geq (e1,e2) -> "(" ^ pp_expr e1 ^ " >= " ^ pp_expr e2 ^ ")"
  | Gt (e1,e2) -> "(" ^ pp_expr e1 ^ " > " ^ pp_expr e2 ^ ")"
  | Eq (e1,e2) -> "(" ^ pp_actual e1 ^ " = " ^ pp_actual e2 ^ ")"
  | And (g1,g2) -> "(" ^ pp_cond g1 ^ " /\\\\ " ^ pp_cond g2 ^ ")"
  | Or (g1,g2) -> "(" ^ pp_cond g1 ^ " \\\\/ " ^ pp_cond g2 ^ ")"
  | Not g -> "~" ^ pp_cond g
  | True -> "T"
let pp_cond = function True -> "" | g -> pp_cond g
let pp_action =
 function
  | Input (r,s,l,vl) ->
     pp_address r ^ "." ^
     pp_label l ^
     "[" ^ (match s with None -> "" | Some a -> pp_aexpr a ^ ".") ^ "]" ^
     "(" ^ String.concat "," (List.map pp_typed_var vl) ^ ")"
  | Output (r,aexpr,l,al) ->
     pp_address r ^ ":" ^
     pp_aexpr aexpr ^ "." ^ pp_label l ^
      "(" ^ String.concat "," (List.map pp_actual al) ^ ")"
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
 "digraph \"" ^  String.concat "*" (List.map pp_address al) ^ "\" {\n" ^
 String.concat "\n" (List.map (pp_state i) sl) ^ "\n" ^
 String.concat "\n" (List.map pp_transition tl) ^ "\n" ^
"}"

(*** Approximate evaluation ***)
type truth_values = F | T | M (* false, true, maybe *)
let tv_not = function F -> T | T -> F | M -> M
let tv_and v1 v2 =
 match v1,v2 with
    F,_
  | _,F -> F
  | T,x
  | x,T -> T
  | M,M -> M
let tv_or v1 v2 =
 match v1,v2 with
    F,x
  | x,F -> x
  | T,_
  | _,T -> T
  | M,M -> M

let smart_minus =
 function
    Const (Numeric c) -> Const (Numeric (-c))
  | x -> Minus x

let smart_plus e1 e2 =
 match e1,e2 with
    Const (Numeric c1), Const (Numeric c2) -> Const (Numeric (c1 + c2))
  | _,_ -> Plus(e1,e2)

let smart_mult c e =
 match c,e with
    Numeric c1, Const (Numeric c2) -> Const (Numeric (c1 + c2))
  | _,_ -> Mult(c,e)

let smart_max e1 e2 =
 match e1,e2 with
    Const (Numeric c1), Const (Numeric c2) -> Const (Numeric (max c1 c2))
  | _,_ -> Max(e1,e2)

let geq e1 e2 =
 match e1,e2 with
    Const (Numeric c1), Const (Numeric c2) ->
     if c1 >= c2 then T else F
  | _,_ -> if e1 = e2 then T else M

let gt e1 e2 =
 match e1,e2 with
    Const (Numeric c1), Const (Numeric c2) ->
     if c1 > c2 then T else F
  | _,_ -> if e1 = e2 then F else M

let rec eval_expr =
 function
  | Var _
  | Const _ as x -> x
  | Plus (e1,e2) -> smart_plus (eval_expr e1) (eval_expr e2)
  | Mult (c,e) -> smart_mult c (eval_expr e)
  | Minus e -> smart_minus (eval_expr e)
  | Max (e1,e2) -> smart_max (eval_expr e1) (eval_expr e2)

let eq e1 e2 =
 match e1,e2 with
    String s1, String s2 -> if s1 = s2 then T else F
  | Address s1, Address s2 -> if s1 = s2 then T else M
  | Expr e1, Expr e2 ->
     (match eval_expr e1, eval_expr e2 with
        Const (Numeric c1), Const (Numeric c2) -> if c1 = c2 then T else F
      | x,y -> if x = y then T else M)
  | _,_ -> assert false (* Dynamic type error *)


let eval_actual =
 function
    Expr e -> Expr (eval_expr e)
  | String _ | Address _ as x -> x

let rec eval_cond =
 function
  | Geq (e1,e2) -> geq (eval_expr e1) (eval_expr e2)
  | Gt (e1,e2) -> gt (eval_expr e1) (eval_expr e2)
  | Eq (e1,e2) -> eq (eval_actual e1) (eval_actual e2)
  | And (g1,g2) -> tv_and (eval_cond g1) (eval_cond g2)
  | Or (g1,g2) -> tv_or (eval_cond g1) (eval_cond g2)
  | Not g -> tv_not (eval_cond g)
  | True -> T

(*** Fresh int generator ***)
let mk_fresh =
 let n = ref 0 in
 function () -> incr n ; !n

(*** Substitution ***)
let map_option f = function None -> None | Some x -> Some (f x)

let rec apply_subst_expr subst =
 function
  | Var v as e ->
     (try
       (match List.assoc (EVar v) subst with
         | Expr e -> e
         | Address _
         | String _ ->
           prerr_endline ("### " ^ v);
           assert false) (* dynamic typing error.. *)
      with Not_found -> e)
  | Const _ as e -> e
  | Plus (e1,e2) -> Plus (apply_subst_expr subst e1,apply_subst_expr subst e2)
  | Mult (c,e2) -> Mult (c,apply_subst_expr subst e2)
  | Minus e -> Minus (apply_subst_expr subst e)
  | Max (e1,e2) -> Max (apply_subst_expr subst e1,apply_subst_expr subst e2)
let apply_subst_aexpr subst =
 function
  | DAddress _ as d -> d
  | DVar v as d ->
     try
      (match List.assoc (AVar v) subst with
       | Expr _ | String _ -> assert false (* Dynamic type error... *)
       | Address d -> d)
     with Not_found -> d
let apply_subst_actual subst =
 function
  | Expr e -> Expr (apply_subst_expr subst e)
  | Address d -> Address (apply_subst_aexpr subst d)
  | String _ as a -> a
let apply_subst_assignment subst (v,e) =
 v, apply_subst_actual subst e
let apply_subst_assignment_list subst al =
 List.map (apply_subst_assignment subst) al
let rec apply_subst_cond subst =
 function
  | Geq (e1,e2) -> Geq (apply_subst_expr subst e1,apply_subst_expr subst e2)
  | Gt (e1,e2) -> Gt (apply_subst_expr subst e1,apply_subst_expr subst e2)
  | Eq (e1,e2) -> Eq (apply_subst_actual subst e1,apply_subst_actual subst e2)
  | And (g1,g2) -> And (apply_subst_cond subst g1,apply_subst_cond subst g2)
  | Or (g1,g2) -> Or (apply_subst_cond subst g1,apply_subst_cond subst g2)
  | Not g -> Not (apply_subst_cond subst g)
  | True -> True
let apply_subst_action subst =
 function
  | Output (r, aexpr,l,al) ->
     Output (r, apply_subst_aexpr subst aexpr,l,List.map (apply_subst_actual subst) al)
  | Input (r, aexpr, l, vl) ->
     Input (r, map_option (apply_subst_aexpr subst) aexpr, l, vl)
  | Tau as a -> a

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


let rec add_transition id1' id2' ~sub cond assign action id ((a1,_,sl1,tl1) as au1) ((a2,_,sl2,tl2) as au2) sp tp =
 try
  let id' = id1' @ id2' in
  let cond = apply_subst_cond sub cond in
  let cond =
   let ground_cond =
    apply_subst_cond sub (apply_subst_cond (fst assign) cond) in
   match eval_cond ground_cond with T -> True | M -> cond | F -> raise Skip in
  let action = apply_subst_action sub action in
  let s12' = List.assoc id1' sl1 @@ List.assoc id2' sl2 in
  let s12' = apply_subst_assignment_list sub (fst s12'),snd s12' in
  let id' = id' @ [mk_fresh ()] in
  let (id',_) as s',is_new =
   try
    List.find (fun (idx,sx) -> sx = s12' && same_but_last idx id') sp, false
   with Not_found -> (id',s12'),true in
  let tr = id,id',cond,action in
  let tp = tr::tp in
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

and movex your_ass other_ass the_others moves id1' id2' ~sub ((a1,_,sl1,tl1) as au1) ((a2,_,sl2,tl2) as au2) id sp tp =
 let assign = your_ass @@ other_ass in
 let can_fire =
  function
   | Tau | Input (_,None,_,_) -> true
   | Input (_,Some d,_,_) ->
      let d = apply_subst_aexpr sub (apply_subst_aexpr (fst your_ass) d) in
      List.for_all (fun a -> d <> DAddress a) the_others
   | Output(r,d,_,_) ->
      (is_contract r || snd assign) &&
      let d = apply_subst_aexpr sub (apply_subst_aexpr (fst your_ass) d) in
      List.for_all (fun a -> d <> DAddress a) the_others in
 let change_sub sub =
  function
     Tau
   | Output _ -> sub
   | Input(_,_,_,vl) ->
      List.map
       (function
           (EVar v) as x -> x, Expr (Var v)
         | (AVar v) as x -> x, Address (DVar v)) vl @ sub in
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
          apply_subst_aexpr sub (apply_subst_aexpr (fst (List.assoc id2 sl2)) d) in
         s = id2 && List.exists (fun a -> d = DAddress a) a1
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
          apply_subst_aexpr sub (apply_subst_aexpr (fst (List.assoc id1 sl1)) d) in
         s = id1 && List.exists (fun a -> d = DAddress a) a2
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
            DAddress receiver = apply_subst_aexpr sub (apply_subst_aexpr (fst ass_out) rec_out) &&
            (match sender with
                None -> true
              | Some aexpr ->
                 apply_subst_aexpr sub (apply_subst_aexpr (fst ass_in) aexpr)
                 = DAddress addr_out)
             && li=lo && List.length vl = List.length al ->
            let sub =
             List.combine vl (List.map (apply_subst_actual sub) al) @ sub in
            let cond = smart_and condi condo in
            add_transition (id1' din don) (id2' din don) ~sub cond
             (ass_in @@ ass_out) Tau id au1 au2 sp tp
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

 (*** Garbage Collection Example ***)
 module Bin = struct
  let (states : state list) =
    [ [1], ([EVar "p",Expr (Const (Numeric 0)) ; EVar "d", Expr (Const (Symbolic "D"))], true)
    ; [2], ([EVar "p",Expr(Const (Numeric 0)) ; EVar "d", Expr (Const (Symbolic "D")) ; EVar "cur_q",Expr (Var "q")
            ;AVar "ID",Address(DVar "id")],false)
    ; [3], ([EVar "p",Expr(Const (Numeric 1)) ;
             EVar "d", Expr(Plus (Var "D", Minus (Const (Symbolic "R"))))], true)
    ; [4], ([EVar "p",Expr(Const (Numeric 1))
            ; EVar "d", Expr(Plus (Var "D", Minus (Const (Symbolic "R"))))
            ; EVar "cur_q",Expr(Var "q'") ;AVar "ID",Address(DVar "id'")], false)
    ; [5], ([EVar "p",Expr(Const (Numeric 2)) ;
             EVar "d", Expr(Plus (Var "D", Minus (Mult (Numeric 2, Const (Symbolic "R")))))],true)
    ; [6], ([EVar "p",Expr(Const (Numeric 2))
        ; EVar "d", Expr(Plus (Var "D", Minus (Mult (Numeric 2, Const (Symbolic "R")))))
            ; EVar "of",Expr(Var "e") ;AVar "ID",Address(DVar "gt_id")],true)
    ; [7], ([EVar "p",Expr(Const (Numeric 2))
        ; EVar "d", Expr(Plus (Var "D", Minus (Mult (Numeric 2, Const (Symbolic "R")))))
        ; EVar "of", Expr(Var "e")  ;AVar "ID", Address(DVar "gt_id")
            ; EVar "of'",Expr(Var "e'") ;AVar "ID'",Address(DVar "gt_id'")],true)
    ; [8], ([EVar "p",Expr(Const (Numeric 2))
        ; EVar "d", Expr(Plus (Var "D", Minus (Mult (Numeric 2, Const (Symbolic "R")))))
        ; EVar "of", Expr(Var "e")  ;AVar "ID", Address(DVar "gt_id")
            ; EVar "of'",Expr(Var "e'") ;AVar "ID'",Address(DVar "gt_id'")],true)
    ; [9], ([EVar "p",Expr(Const (Numeric 2))
        ; EVar "d", Expr(Plus (Var "D", Minus (Mult (Numeric 2, Const (Symbolic "R")))))
        ; EVar "of", Expr(Var "e")  ;AVar "ID", Address(DVar "gt_id")
            ; EVar "of'",Expr(Var "e'") ;AVar "ID'",Address(DVar "gt_id'") ],true)
    ;[10], ([EVar "p",Expr(Const (Numeric 0))
        ; EVar "d",
          Expr(Plus
           (Plus (Var "d", Minus (Mult (Numeric 2, Const (Symbolic "R")))),
            Max (Var "of", Var "of'")))
        ; EVar "of", Expr(Var "e")  ;AVar "ID", Address(DVar "gt_id")
            ; EVar "of'",Expr(Var "e'") ;AVar "ID'",Address(DVar "gt_id'") ],false)
    ;[11], ([EVar "p",Expr(Const (Numeric 0))
        ; EVar "d",
          Expr(Plus
           (Plus (Var "d", Minus (Mult (Numeric 2, Const (Symbolic "R")))),
            Max (Var "of", Var "of'")))
        ; EVar "of", Expr(Var "e")  ;AVar "ID", Address(DVar "gt_id")
            ; EVar "of'",Expr(Var "e'") ;AVar "ID'",Address(DVar "gt_id'")],true)
   ]

  let (transitions : transition list) =
   [ [1],[2],True,Input (Contract "garbage_bin",None, "dep", [EVar "q";AVar "id"])
   ; [2],[1],Gt(Var "cur_q",Const(Numeric 2)),Output (Contract "garbage_bin",DVar "ID","NOK",[])
   ; [2],[3],Eq(Expr (Var "cur_q"),Expr (Const(Numeric 1))),
      Output (Contract "garbage_bin",DVar "ID","OK",[Expr(Const (Symbolic "R"))])
   ; [2],[5],Eq(Expr(Var "cur_q"),Expr(Const(Numeric 2))),
      Output (Contract "garbage_bin",DVar "ID","OK",[Expr(Mult(Numeric 2, Const (Symbolic "R")))])
   ; [3],[4],True,Input (Contract "garbage_bin",None, "dep", [EVar "q'";AVar "id'"])
   ; [4],[3],Gt(Var "cur_q",Const(Numeric 2)),Output (Contract "garbage_bin",DVar "ID","NOK",[])
   ; [4],[5],Eq(Expr(Var "cur_q"),Expr(Const(Numeric 1))),
      Output (Contract "garbage_bin",DVar "ID","OK",[Expr(Const (Symbolic "R"))])
   ; [5],[6],True,Input (Contract "garbage_bin",None, "bid", [EVar "e";AVar "gt_id"])
   ; [6],[5],Gt(Mult(Numeric 2, Const (Symbolic "R")), Var "of"),
      Output (Contract "garbage_bin",DVar "ID","lost",[Expr(Var "of")])
   ; [6],[7],Geq(Var "of",Mult(Numeric 2, Const (Symbolic "R"))),Input (Contract "garbage_bin",None, "bid", [EVar "e'";AVar "gt_id'"])
   ; [7],[8],Geq(Var "of", Var "of'"), Output (Contract "garbage_bin",DVar "ID'","LOST",[Expr(Var "of'")])
   ; [7],[8],Gt(Var "of'", Var "of"),  Output (Contract "garbage_bin",DVar "ID", "LOST",[Expr(Var "of")])
   ; [8],[9],Geq(Var "of", Var "of'"), Output (Contract "garbage_bin",DVar "ID","WIN",[])
   ; [8],[9],Geq(Var "of'", Var "of"), Output (Contract "garbage_bin",DVar "ID'","WIN",[])
   ; [9],[10],True,Input (Contract "garbage_bin",None, "empty", [AVar "id"])
   ; [10],[9],Or(And (Geq(Var "of",Var "of'"), Not (Eq(Address (DVar "id"), Address (DVar "ID")))),
             And (Gt(Var "of'",Var "of"), Not (Eq(Address (DVar "id"), Address (DVar "ID'"))))),Tau
   ; [10],[11],Geq(Var "of", Var "of'"),
     Output (Contract "garbage_bin",DAddress (Contract "incinerator"),"notify",
        [Expr(Var "ID");Expr(Const(Numeric 2))])
   ; [10],[11],Geq(Var "of'", Var "of"),
     Output (Contract "garbage_bin",DAddress (Contract "incinerator'"),"notify",
        [Expr(Var "ID'");Expr(Const(Numeric 2))])
   ; [11],[1],True,
     Output (Contract "garbage_bin",DAddress (Contract "incinerator"),"save",
        [Expr(Plus(Max(Var "of", Var "of'"),
                   Minus (Mult(Numeric 2, Const (Symbolic "R")))))])
   ]

  let automaton : automaton = ([Contract "garbage_bin"],[1],states,transitions)

   let _ =
    let ch = open_out "garbage_bin.dot" in
    output_string ch (pp_automaton automaton);
    close_out ch

 end

module Citizen = struct
  let (states : state list) =
    [ [1], ([EVar "cp",Expr(Const (Numeric 0)) ; EVar "balance", Expr(Const (Symbolic "D"))],true)
    ; [2], ([EVar "cp",Expr(Const (Numeric 2)) ; EVar "balance", Expr(Const (Numeric 0))],true)
    ; [3], ([EVar "cp",Expr(Const (Numeric 0)) ; EVar "balance", Expr(Const (Numeric 0))],true)
    ; [4], ([EVar "cp",Expr(Const (Numeric 1)) ; EVar "balance", Expr(Const (Numeric 0))],true)
    ; [5], ([EVar "cp",Expr(Const (Numeric 1)) ; EVar "balance", Expr(Const (Numeric 0))],true)
    ; [6], ([EVar "cp",Expr(Const (Numeric 1)) ;
             EVar "balance", Expr(Const (Numeric 0))],true)
    ; [7], ([EVar "cp",Expr(Const (Numeric 0))  ;
             EVar "balance", Expr(Const (Symbolic "2*a"))],true)
    ; [8], ([EVar "cp",Expr(Const (Numeric 1))  ;
             EVar "balance", Expr(Const (Symbolic "a"))],true)
    ; [9], ([EVar "cp",Expr(Const (Numeric 0))  ;
             EVar "balance", Expr(Const (Numeric 0))],true)
    ;[10], ([EVar "cp",Expr(Const (Numeric 0)) ;
             EVar "balance", Expr(Const (Numeric 0))],true)
    ;[11], ([EVar "cp",Expr(Const (Numeric 0)) ;
             EVar "balance", Expr(Const (Symbolic "a"))],true)
    ;[12], ([EVar "cp",Expr(Const (Numeric 0)) ;
             EVar "balance", Expr(Const (Symbolic "a"))],true)
    ;[13], ([EVar "cp",Expr(Const (Numeric 0)) ;
             EVar "balance", Expr(Const (Symbolic "a"))],true)
    ;[14], ([EVar "cp",Expr(Const (Numeric 0))  ;
             EVar "balance", Expr(Const (Symbolic "2*a"))],true)
    ]

    let address0 = Human "citizen"
    let address = DAddress address0
    let gb = Contract "garbage_bin"
    let incinerator = Contract "incinerator"

  let (transitions : transition list) =
    [ [1],[2],True,Output (address0, DAddress incinerator,"fee",[Expr(Const (Symbolic "D"))])
    ; [2],[3],True,
      Output (address0,DAddress gb,"dep",[Expr( Const (Numeric 2)); Address address])
    ; [3],[2],True,Input (address0,Some (DAddress gb),"NOK", [])
    ; [2],[4],True,
      Output (address0,DAddress gb,"dep",[Expr( Const (Numeric 1)); Address address])
    ; [4],[2],True,Input (address0,Some (DAddress gb),"NOK", [])
    ; [2],[5],True, Tau
    ; [2],[6],True, Tau
    ; [3],[7], True,Input (address0,Some (DAddress gb),"OK", [EVar "2*a"])
    ; [4],[8], True,Input (address0,Some (DAddress gb),"OK", [EVar "a"])
    ; [8],[12],True,
      Output (address0,DAddress gb,"dep",[Expr( Const (Numeric 1)); Address address])
    ; [12],[8],True,Input (address0,Some (DAddress gb),"NOK", [])
    ; [8],[13],True, Tau
    ; [12],[14], True,Input (address0,Some (DAddress gb),"OK", [EVar "a"])
    ; [5],[9],True,
      Output (address0,DAddress gb,"dep",[Expr( Const (Numeric 1)); Address address])
    ; [9],[5],True,Input (address0,Some (DAddress gb),"NOK", [])
    ; [5],[10],True, Tau
    ; [9],[11], True,Input (address0,Some (DAddress gb),"OK", [EVar "a"])
    ; [7],[1], True,Output (address0,DAddress (Contract "banca"),"save", [Expr (Var "balance")])
    ; [14],[1], True,Output (address0,DAddress (Contract "banca"),"save", [Expr (Var "balance")])
    ; [13],[1], True,Output (address0,DAddress (Contract "banca"),"save", [Expr (Var "balance")])
    ; [11],[1], True,Output (address0,DAddress (Contract "banca"),"save", [Expr (Var "balance")])
    ; [10],[1], True,Output (address0,DAddress (Contract "banca"),"save", [Expr (Var "balance")])
    ; [6],[1], True,Output (address0,DAddress (Contract "banca"),"save", [Expr (Var "balance")])

    ]

  let automaton : automaton = ([address0],[1],states,transitions)

  let _ =
    let ch = open_out "citizen.dot" in
    output_string ch (pp_automaton automaton);
    close_out ch

end

 module BasicCitizen = struct
   let (states : state list) =
     [ [1], ([EVar "cp",Expr(Const (Numeric 2)) ; EVar "balance", Expr(Plus (Const (Symbolic "A"), Minus (Const (Symbolic "D"))))],true)
     ; [2], ([EVar "cp",Expr(Const (Numeric 1)) ; EVar "balance", Expr(Plus (Const (Symbolic "A"), Minus (Const (Symbolic "D"))))],true)
     ; [3], ([EVar "cp",Expr(Const (Numeric 1)) ;
             EVar "balance", Expr(Plus (Const (Symbolic "A"), Plus (Var "a", Minus (Const (Symbolic "D")))))],true)
     ; [4], ([EVar "cp",Expr(Const (Numeric 0)) ;
             EVar "balance", Expr(Plus (Const (Symbolic "A"), Plus (Var "a", Minus (Const (Symbolic "D")))))],true)
     ]

   let address0 = Human "basiccitizen"
   let address = DAddress address0
   let gb = Contract "garbage_bin"

   let (transitions : transition list) =
     [ [1],[2],True,
       Output (address0,DAddress gb,"dep",[Expr( Const (Numeric 1)); Address address])
     (*; [2],[1],True,Input ("NOK", [])*)
     (*; [2],[1], True, Input ("OK", ["a"])*)
     ; [2],[3], True, Input (address0,Some (DAddress gb), "OK", [EVar "a"])
     ; [3],[4], True,
       Output(address0,DAddress gb,"dep",[Expr( Const (Numeric 1)); Address address])
     (*; [4],[3],True ,Input ("NOK", [])*)
     ; [4],[1], True, Input (address0,Some (DAddress gb), "OK", [EVar "a"])
     ]

   let automaton : automaton = ([address0],[1],states,transitions)

   let _ =
     let ch = open_out "basiccitizen.dot" in
     output_string ch (pp_automaton automaton);
     close_out ch

 end

 module BasicTruck = struct
   let (states : state list) =
     [ [1], ([EVar "tp",Expr(Const (Numeric 0)) ; EVar "truck_balance", Expr(Const (Symbolic "A"))], true)
     ; [2], ([EVar "tp",Expr(Const (Numeric 0)) ; EVar "truck_balance", Expr(Plus (Const (Symbolic "A"), Minus (Const (Symbolic "e"))))], true)

     ; [3], ([EVar "tp",Expr(Const (Numeric 0)) ; EVar "truck_balance", Expr(Plus (Const (Symbolic "A"), Minus (Const (Symbolic "e"))))], true)
     ]

   let address0 = Human "basictruck"
   let address = DAddress address0
   let gb = Contract "garbage_bin"

   let (transitions : transition list) =
     [ [1],[2],True,
       Output (address0,DAddress gb,"bid",[Expr( Const( Symbolic "e")) ;Address address])
     ; [2],[1], True, Input (address0,Some (DAddress gb), "LOST", [EVar "e"])
     ; [2],[3], True, Input (address0,Some (DAddress gb), "WIN", [])
     ; [3],[1], True,
       Output (address0,DAddress gb,"empty",[Address address])
       ]

   let automaton : automaton = ([address0],[1],states,transitions)

   let _ =
     let ch = open_out "basictruck.dot" in
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
 let basictruck_bin = compose BasicTruck.automaton Bin.automaton
 let basiccitizen_basictruck_bin = compose BasicCitizen.automaton basictruck_bin
 let automata =
  [ "basiccitizen_bin",basiccitizen_bin
  ; "basictruck_bin",basictruck_bin
  ; "basiccitizen_basictruck_bin",basiccitizen_basictruck_bin
  ]

 let _ =
  List.iter
   (fun (fn,au) ->
     let ch = open_out (fn ^ ".dot") in
     output_string ch (pp_automaton au) ;
     close_out ch ;
     ignore (Unix.system ("dot -Tpdf " ^ fn ^ ".dot -o " ^ fn ^ ".pdf"))
   ) automata
