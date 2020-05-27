open Types
open Cofloco

exception NotLinear

let (&&&) pll l =
 List.concat
  (List.map
   (fun (fcall,to_nat,cost,calls,pl1) ->
     List.map (fun pl -> fcall,to_nat,cost,calls,pl@pl1) pll
   ) l)

let rec compute_expr =
 function
  | TInt n -> Rat n
  | TVar v -> Var v
  | TPlus(e1,e2) -> Plus(compute_expr e1, compute_expr e2)
  | TMinus(e1,e2) -> Minus(compute_expr e1, compute_expr e2)
  | TMult(TInt n,e2) -> Mult(n, compute_expr e2)
  | TMult _ -> raise NotLinear
  | TDiv(e1,TInt n) -> Div(compute_expr e1, n)
  | TDiv _ -> raise NotLinear
  | TUMinus e -> UMinus(compute_expr e)

let comb op l1 l2 =
 List.concat (List.map (fun x -> List.map (fun y -> op x y) l2) l1)

let top = [[]]
let bot = []
let disj = (@)
let conj = comb (@)

let op_neg =
 function
  | Geq -> [Lt]
  | Leq -> [Gt]
  | Eq -> [Lt; Gt]
  | Lt -> [Geq]
  | Gt -> [Leq]

let atomic_neg (e1,p,e2) =
 List.map (fun op -> e1,op,e2) (op_neg p)

let rec distribute =
 function
    [] -> top
  | hd::tl -> conj hd (distribute tl)

let neg : pred list list -> pred list list = fun disjl ->
 let conjl_disj_conj' =
  List.map (
   fun conjl ->
    let disj' =
     List.map (fun x -> [x]) (List.concat (List.map atomic_neg conjl)) in
    disj'
  ) disjl in
 distribute conjl_disj_conj'

let rec compute_pred =
 function
  | TBool true -> top
  | TBool false -> bot
  | TGeq(e1,e2) ->
     let e1 = compute_expr e1 in
     let e2 = compute_expr e2 in
     [[e1, Geq, e2]]
  | TGt(e1,e2) ->
     let e1 = compute_expr e1 in
     let e2 = compute_expr e2 in
     [[e1, Gt, e2]]
  | TEq(e1,e2) ->
     let e1 = compute_expr e1 in
     let e2 = compute_expr e2 in
     [[e1, Eq, e2]]
  | TAnd(p1,p2) ->
     let p1 = compute_pred p1 in
     let p2 = compute_pred p2 in
     conj p1 p2
  | TOr(p1,p2) ->
     let p1 = compute_pred p1 in
     let p2 = compute_pred p2 in
     disj p1 p2
  | TNot p ->
     let p = compute_pred p in
     neg p

let rec compute_typ fcall =
 function
  | TGamma el ->
     let el = List.map compute_expr el in
     (* XXX here I am adding all fields together for now *)
     (*let cost = List.fold_left (fun acc x -> Plus(acc,x)) (Rat 0) el in*)
     let initial_balance = List.hd el in
     let final_balance = List.nth el (List.length el / 2) in
     let cost = Minus(final_balance,initial_balance) in
     [fcall,true,cost,[],[]]
  | TCall(f,el) ->
     let el = List.map compute_expr el in
     [fcall,false,Rat 0,[f,el],[]]
  | TChoice l ->
     List.concat
      (List.map (fun (p,typ) ->
       let pl = compute_pred p in
       let l = compute_typ fcall typ in
       pl &&& l) l)

let compute_functions (name,vars,typ) =
 compute_typ (name,vars) typ

let rec skip_nth n =
 function
    l when n = 0 -> l
  | _::tl -> skip_nth (n - 1) tl
  | [] -> assert false

let duplicate_saved_fields fieldsno =
 let rec aux acc n =
  function
     vars when n = 0 -> 
      let acc = List.rev acc in
      let locals = skip_nth fieldsno vars in
      acc @ locals, acc @ acc @ locals
   | v::vars -> aux (v::acc) (n - 1) vars
   | [] -> assert false in
 aux [] fieldsno

let main fieldsno (name,vars,_) =
 let params,args = duplicate_saved_fields fieldsno vars in 
 ("main__",params),false,Rat 0,[name,List.map (fun x -> Var x) args],[]

let compute (fieldsno,l) =
 main fieldsno (List.hd l) ::
  List.concat (List.map compute_functions l)
