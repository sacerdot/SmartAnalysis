open MicroSolidity
open Types
open Static
open Cofloco
open CostEquationsGeneration

exception GenerationFail of string

type any_meth = AnyMeth : ('a, 'b) MicroSolidity.meth -> any_meth

(*from typeInference.ml*)
let (^^) s1 s2 = s1 ^ "_" ^ s2

(*base Cofloco.var *)
(********************************************)
let msg_sender = "_msg_sender_"
let msg_value  = "_msg_value_"
let balance    = "_balance_"
let ret int = "Ret"^string_of_int int
let initial = "_initial_"

let bottom = Rat min_int
let zero is_address = if is_address then bottom else Rat 0
(********************************************)

(* MAPPING TYPE + relative functs *)
(********************************************)
type mapping  =
 { fields       : (bool(*address*)*Cofloco.var) list
 ; last_assignment : (Cofloco.var * Cofloco.expr) list
 ; this            : address
 ; meth_decl_list  : (address * (any_meth * (*payable:*)bool) list) list
 }

type eq_frame =
 { acalls : Cofloco.acall list
 ; preds  : Cofloco.pred list
 }

let rec add_pred p ~eq_frame = {eq_frame with preds = eq_frame.preds@[p]}
let rec add_preds p ~eq_frame = {eq_frame with preds = eq_frame.preds@p}
let rec add_acall a ~eq_frame = {eq_frame with acalls = eq_frame.acalls@[a]}

let rec set_assignment k v =
 function
  | [] -> Utils.error ("Variable or field " ^ k ^" not found");assert false
  | (k',_)::tl when k=k' -> (k,v)::tl
  | p::tl -> p::set_assignment k v tl
let assign k v ~mapping = {mapping with last_assignment = set_assignment k v mapping.last_assignment}

let lookup_assignment k assign =
 try List.assoc k assign
 with Not_found -> Utils.error ("Variable or field " ^ k ^" not found");assert false
let lookup ~mapping k = lookup_assignment k mapping.last_assignment
(********************************************)

(*Base translate functions *)
(********************************************)
let string_of_meth addr m =
 addr ^^ Utils.trd3 m ^^ String.concat "_" (pp_tag_list (Utils.snd3 m))
let int_of_address = fun n -> Rat (Hashtbl.hash n)
let int_of_meth = fun (type a b) (m: (a,b) meth) -> Rat (Hashtbl.hash (Utils.snd3 m, Utils.trd3 m))
let int_of_bool = function | false -> Rat 0 | true -> Rat 1
let int_of_unit = Rat 0

type any_return_meth =
 AnyReturnMeth : ('a,'b) meth * bool * 'b expr_list -> any_return_meth
let match_method : type a b. mapping:mapping -> address -> (a,b) meth -> b expr_list -> any_return_meth option
= fun ~mapping addr meth params ->
 let meths =
  try List.assoc addr mapping.meth_decl_list
  with Not_found -> assert false in
 let rec aux :
  type a b. (a,b) meth -> b expr_list -> (any_meth * bool) list -> any_return_meth
  = fun meth params meths ->
  match meths with
     [] -> raise Not_found
   | (AnyMeth meth',payable)::tl ->
      match
       eq_tag_list (Utils.snd3 meth) (Utils.snd3 meth')
      with
         Some Refl when Utils.trd3 meth = Utils.trd3 meth' ->
          AnyReturnMeth (meth',payable,params)
       | _ -> aux meth params tl in
 try
  Some (aux meth params meths)
 with
  Not_found ->
   try
    Some (aux fallback ENil meths)
   with
    Not_found -> None

let fields_of_a_contract (AContract(a,_,_,fields)) =
 List.rev_map
  (fun (AnyField f) -> eq_tag (fst f) Address <> None, a ^^ snd f) fields @ [false, a ^^ balance]

let address_of ~mapping v =
 let a = lookup ~mapping v in
 try fst (List.find (fun (c,_) -> int_of_address c = a) mapping.meth_decl_list)
 with Not_found ->
   Utils.error ("Variable or field " ^ v);
   Utils.error ("holds unrecognized address "^Cofloco.pp_expr a);
   Utils.error ("Known addresses: " ^ String.concat "," (List.map fst mapping.meth_decl_list));
   assert false

let trans_address : mapping:mapping -> int -> address MicroSolidity.expr -> address =
fun ~mapping out_f_numb expr ->
 match expr with
    Value a -> a
  | Var v -> address_of ~mapping (snd v)
  | Field v -> address_of ~mapping (mapping.this ^^ snd v^^"out"^string_of_int out_f_numb)
  | This -> mapping.this
  | MsgSender -> address_of ~mapping msg_sender
let rec trans_iexpr : mapping:mapping -> int -> int MicroSolidity.expr -> Cofloco.expr =
fun ~mapping out_f_numb expr ->
 match expr with
    Value b -> Rat b
  | Var v -> lookup ~mapping (snd v)
  | Field v -> lookup ~mapping (mapping.this ^^ snd v^^"out"^string_of_int out_f_numb)
  | Plus(e1,e2) -> Plus(trans_iexpr ~mapping out_f_numb e1, trans_iexpr ~mapping out_f_numb e2)
  | Minus(e1,e2) -> Minus(trans_iexpr ~mapping out_f_numb e1, trans_iexpr ~mapping out_f_numb e2)
  | Mult(e1,e2) ->
    let e1 = trans_iexpr ~mapping out_f_numb e1 in
    let e2 = trans_iexpr ~mapping out_f_numb e2 in
    (match e1 with
    | Rat x -> Mult(x,e2)
    | _ -> (match e2 with
          | Rat x -> Mult(x,e1)
          | _ -> assert false))
  | Div(e1,e2) ->
    let e1 = trans_iexpr ~mapping out_f_numb e1 in
    let e2 = trans_iexpr ~mapping out_f_numb e2 in
    (match e2 with
    | Rat x -> Div(e1,x)
    | _ -> assert false)
  | UMinus e -> UMinus(trans_iexpr ~mapping out_f_numb e)
  | MsgValue -> lookup ~mapping msg_value
  | Balance a -> lookup ~mapping (trans_address ~mapping out_f_numb a ^^ balance)

let rec bexpr_pred : mapping:mapping -> int -> bool MicroSolidity.expr -> Types.pred =
 fun ~mapping out_f_numb -> function
 | Value b -> TBool b
 | Var v -> 
   let res = lookup ~mapping (snd v) in
   TEq(lookup_to_typ_e res, (TInt 1))
 | Field v -> 
   let res = lookup ~mapping (mapping.this ^^ snd v^^"out"^string_of_int out_f_numb) in
   TEq(lookup_to_typ_e res, (TInt 1))
 | Geq(e1,e2) -> TGeq(iexpr_to_expr ~mapping out_f_numb e1, iexpr_to_expr ~mapping out_f_numb e2)
 | Gt(e1,e2) -> TGt(iexpr_to_expr ~mapping out_f_numb e1, iexpr_to_expr ~mapping out_f_numb e2)
 | Eq(Int,e1,e2) -> TEq(iexpr_to_expr ~mapping out_f_numb e1, iexpr_to_expr ~mapping out_f_numb e2)
 | Eq(Bool,e1,e2) ->
   let e1 = bexpr_pred ~mapping out_f_numb e1 in
   let e2 = bexpr_pred ~mapping out_f_numb e2 in
   TOr(TAnd(e1,e2),TAnd(TNot e1,TNot e2))
 | Eq(Address,a1,a2) ->
   (match int_of_address (trans_address ~mapping out_f_numb a1),int_of_address (trans_address ~mapping out_f_numb a2) with
   | Rat a1,Rat a2 -> TEq(TInt a1,TInt a2)
   | _ -> assert false
   )
 | Eq(Unit,_,_) -> TBool true
 | And(e1,e2) -> TAnd(bexpr_pred ~mapping out_f_numb e1, bexpr_pred ~mapping out_f_numb e2)
 | Or(e1,e2) -> TOr(bexpr_pred ~mapping out_f_numb e1, bexpr_pred ~mapping out_f_numb e2)
 | Not p -> TNot(bexpr_pred ~mapping out_f_numb p)
and iexpr_to_expr : mapping:mapping -> int -> int MicroSolidity.expr -> Types.expr =
fun ~mapping out_f_numb expr ->
 match expr with
 | Value i -> TInt i
 | Var v -> 
   let res = lookup ~mapping (snd v) in
   lookup_to_typ_e res
 | Field v -> 
   let res = lookup ~mapping (mapping.this ^^ snd v^^"out"^string_of_int out_f_numb) in
   lookup_to_typ_e res
 | Plus(e1,e2) -> TPlus(iexpr_to_expr ~mapping out_f_numb e1, iexpr_to_expr ~mapping out_f_numb e2)
 | Minus(e1,e2) -> TMinus(iexpr_to_expr ~mapping out_f_numb e1, iexpr_to_expr ~mapping out_f_numb e2)
 | Mult(e1,e2) -> TMult(iexpr_to_expr ~mapping out_f_numb e1, iexpr_to_expr ~mapping out_f_numb e2)
 | Div(e1,e2) -> TDiv(iexpr_to_expr ~mapping out_f_numb e1, iexpr_to_expr ~mapping out_f_numb e2)
 | UMinus e -> TUMinus(iexpr_to_expr ~mapping out_f_numb e)
 | MsgValue -> 
   let res = lookup ~mapping msg_value in
   lookup_to_typ_e res
 | Balance a -> 
   let res = lookup ~mapping (trans_address ~mapping out_f_numb a ^^ balance) in
   lookup_to_typ_e res
and lookup_to_typ_e : Cofloco.expr -> Types.expr =
 function
 | Var v -> TVar v
 | Rat i -> TInt i
 | Plus(e1,e2) -> TPlus(lookup_to_typ_e e1,lookup_to_typ_e e2)
 | Minus(e1,e2) -> TMinus(lookup_to_typ_e e1,lookup_to_typ_e e2)
 | Mult(r,e2) -> TMult(TInt r,lookup_to_typ_e e2)
 | Div (e1,r) -> TDiv(lookup_to_typ_e e1,TInt r)
 | UMinus e -> TUMinus (lookup_to_typ_e e)

let trans_expr :
 type a. mapping:mapping -> int -> a tag -> a MicroSolidity.expr -> 
  [`Single of Cofloco.expr | `Split of Types.pred]
= fun ~mapping out_f_numb tag expr ->
 match tag with
    Int -> `Single (trans_iexpr ~mapping out_f_numb expr)
  | Bool -> `Split(bexpr_pred ~mapping out_f_numb expr)
  | Address -> `Single (int_of_address (trans_address ~mapping out_f_numb expr))
  | Unit -> `Single (int_of_unit)

(*trans functs*)
(********************************************)
let trans_fst_method ~fields ~meth_decl_list this ~name ~args ~locals ~typ_of =
 let out_fields = List.map (fun (b,f) -> b,f^^"out0") fields in
 let other_params = fields @ (true,msg_sender) :: (false,msg_value) :: args in
 let last_assignment =
   List.map2 (fun (b1,i) (b2,o) -> o,Cofloco.Var i) fields out_fields @ 
   List.map (fun (b,v) -> v,Cofloco.Var v) (other_params@[false,ret 0]) @ List.map (fun (t,v) -> v,zero t) locals in
 let mapping = { fields ; last_assignment ; this ; meth_decl_list } in
 let typ = typ_of ~mapping in
 string_of_meth this name, other_params@out_fields@[false,ret 0], typ

let rec args_of_var_list : type a. a MicroSolidity.var_list -> (bool * Cofloco.var) list =
 function
 | VNil -> []
 | VCons(n,tl) -> (eq_tag Address (fst n) <> None,snd n) :: args_of_var_list tl

let args_of_block (Block(args,locals,_)) =
 args_of_var_list args, args_of_var_list locals

let trans_value ~mapping out_f_numb v =
 Option.fold ~none:(Rat 0) ~some:(trans_iexpr out_f_numb ~mapping) v

let type_of_expr_poly ~mapping out_f_numb =
 object
  method f : 'a. 'a tag -> 'a MicroSolidity.expr -> 'b
           = trans_expr ~mapping out_f_numb 
 end

let trans_call_w: mapping:mapping -> eq_frame:eq_frame -> addr:address -> meth:(_ meth) ->
  value:expr -> sender:expr -> params:(expr list) -> acall
= fun ~mapping ~eq_frame ~addr ~meth ~value ~sender ~params ->
  assert (List.length params = tag_list_length (Utils.snd3 meth));
  let name = string_of_meth addr meth in
  let f_out_numb = (List.length eq_frame.acalls) in
  
  let from = mapping.this in
  let in_from_balance = lookup ~mapping (from^^balance^^"out"^string_of_int f_out_numb) in
  let in_to_balance = lookup ~mapping (addr^^balance^^"out"^string_of_int f_out_numb) in
  let mapping = 
    if value<>Rat 0 then
      (if in_from_balance<>in_to_balance then
        {mapping with last_assignment=
          ((from^^balance^^"out"^string_of_int f_out_numb),(Minus(in_from_balance,value)))::
          ((addr^^balance^^"out"^string_of_int f_out_numb),(Plus(in_to_balance,value)))::
          mapping.last_assignment}
      else
        {mapping with last_assignment=
          ((from^^balance^^"out"^string_of_int f_out_numb),Plus((Minus(in_from_balance,value)),value))::
          mapping.last_assignment}
      )  
    else mapping in
  let input_fields = List.map (fun (b,f) -> lookup ~mapping (f^^"out"^string_of_int f_out_numb)) mapping.fields in
  let output_fields = List.map (fun (b,f) -> Cofloco.Var(f^^"out"^string_of_int ((List.length (eq_frame.acalls)+1)))) mapping.fields in
  let args =
   input_fields @
   sender :: value :: params @ output_fields @ [Cofloco.Var (ret ((List.length eq_frame.acalls)+1))] in
  name,args

let get_split_preds_and_negs: Types.pred -> Cofloco.pred list list * Cofloco.pred list list =
 fun p -> 
  let preds = CostEquationsGeneration.compute_pred p in
  preds,CostEquationsGeneration.neg preds

let is_trans_call: type a b. (a,b) MicroSolidity.meth -> bool = function
 | Unit,TCons(Int,TNil),name when (String.equal name "transfer") || (String.equal name "send") -> true
 | _ -> false

let rec trans_call_params :
 mapping:mapping -> eq_frame:eq_frame -> addr:address -> meth:(_ meth) ->
  value:expr -> sender:expr -> params:('a list) -> Cofloco.expr list -> eq_frame list
= fun ~mapping ~eq_frame ~addr ~meth ~value ~sender ~params expr_params ->
 match params with
 | (`Single e)::tl -> trans_call_params ~mapping ~eq_frame ~addr ~meth ~value ~sender ~params:tl (expr_params@[e])
 | (`Split p)::tl -> 
   let p1,p2 = get_split_preds_and_negs p in
   let aux ~eq_frame p =
     if List.length p=0 then [] else
     let eql = List.map (fun pl -> add_preds pl ~eq_frame) p in
     List.flatten (List.map (fun eq -> trans_call_params ~mapping ~eq_frame:eq ~addr ~meth ~value ~sender ~params:tl (expr_params@[(Rat 1)])) eql)
   in
   aux ~eq_frame p1 @ aux ~eq_frame p2
 | [] -> 
   let f_out_numb = (List.length eq_frame.acalls) in
   if value<>Rat 0 then
     let from = mapping.this in
     let from_balance = lookup ~mapping (from^^balance^^"out"^string_of_int f_out_numb) in
     let eq = add_acall (trans_call_w ~mapping ~eq_frame ~addr ~meth ~value:value ~sender ~params:expr_params) ~eq_frame in
     [add_preds [from_balance,Geq,value; value,Geq,Rat 0] eq]
   else 
     [add_acall (trans_call_w ~mapping ~eq_frame ~addr ~meth ~value:value ~sender ~params:expr_params) ~eq_frame]

let trans_call :
 mapping:mapping -> eq_frame:eq_frame ->
  tag:('a tag) -> addr:(address MicroSolidity.expr) -> meth:(('a,_) meth) ->
   value:(int MicroSolidity.expr option) -> sender:expr ->
    params:('b expr_list) -> eq_frame list
= fun ~mapping ~eq_frame ~tag ~addr ~meth ~value ~sender ~params ->
 let f_out_numb = (List.length eq_frame.acalls) in
 let addr = trans_address ~mapping f_out_numb addr in
 let is_trans_call = is_trans_call meth in
 match match_method ~mapping addr meth params with
    None -> []
  | Some AnyReturnMeth(meth0,payable,params0) ->
     let output_type_ok =
      eq_tag tag Unit <> None || eq_tag tag (Utils.fst3 meth0) <> None in
     let payable_ok = payable || value = None in
     if output_type_ok=false || payable_ok=false then [] 
     else
      let params = 
       if is_trans_call then
         expr_list_map (type_of_expr_poly ~mapping f_out_numb) (Utils.snd3 meth) params
       else
         expr_list_map (type_of_expr_poly ~mapping f_out_numb) (Utils.snd3 meth0) params0
      in
      let amount = 
       if is_trans_call then
        (match params with | [`Single e] -> e | _ -> assert false)
       else
        trans_value ~mapping f_out_numb value
      in
      trans_call_params ~mapping ~eq_frame ~addr ~meth:meth0 ~value:amount ~sender ~params:(if is_trans_call then [] else params) []
     
let return_single: type a b. eq_frame:eq_frame -> mapping:mapping -> Cofloco.expr -> eq_frame list =
fun ~eq_frame ~mapping e ->
   let eq = add_pred (Var(ret 0),Eq,e) ~eq_frame in
   let out_numb = List.length eq_frame.acalls in
   let out_fields = List.map (fun (b,f)->f^^"out0") mapping.fields in
   let last_out_fields = List.map (fun (b,f)->f^^"out"^string_of_int out_numb) mapping.fields in
   let out_pred = List.map2 
     (fun f_out f -> Var(f_out),Eq,Var(f)) out_fields 
     (if out_numb=0 then List.map snd mapping.fields else last_out_fields) in
   [add_preds out_pred eq]

let return_split: type a b. eq_frame:eq_frame -> mapping:mapping -> Cofloco.pred list list -> Cofloco.expr -> eq_frame list =
fun ~eq_frame ~mapping preds_l e ->
  if List.length preds_l=0 then [] else
    let eql = List.map (fun pl -> add_preds pl ~eq_frame) preds_l in
    List.flatten (List.map (fun eq -> return_single ~eq_frame:eq ~mapping e) eql)

(* if all branches are the same, compress to one *)
let compress l0 =
  let rec aux acc l =
    match acc,l with
      None,[] -> Some([])
    | Some p,[] -> Some([p])
    | None,hd::tl -> aux (Some hd) tl
    | Some hd1,hd2::tl when hd1=hd2 -> aux (Some hd1) tl
    | _ -> None in
  aux None l0

let rec trans_stm : type a b. eq_frame:eq_frame -> mapping:mapping -> a tag -> (a,b) stm -> eq_frame list =
fun ~eq_frame ~mapping tag stm ->
 match stm with
 | Revert -> []
 | Return -> return_single ~eq_frame ~mapping (Rat 0)
 | ReturnRhs(Expr e) -> 
    let out_numb = List.length eq_frame.acalls in
    let expr = trans_expr ~mapping out_numb tag e in
    (match expr with
    | `Single e -> return_single ~eq_frame ~mapping e
    | `Split p -> 
        let p1,p2 = get_split_preds_and_negs p in
        return_split ~eq_frame ~mapping p1 (int_of_bool true) @
        return_split ~eq_frame ~mapping p1 (int_of_bool false))
 | Assign(LField(t,n),(Expr e),s) ->
    let out_numb = List.length eq_frame.acalls in
    let expr = trans_expr ~mapping out_numb t e in
    (match expr with
    | `Single e ->
        trans_stm ~eq_frame ~mapping:(assign (mapping.this ^^ n^^"out"^string_of_int out_numb) e ~mapping) tag s    
    | `Split p -> 
        let p1,p2 = get_split_preds_and_negs p in
        trans_preds_assign_stm ~eq_frame ~mapping p1 (mapping.this ^^ n^^"out"^string_of_int out_numb,(int_of_bool true)) tag stm @
        trans_preds_assign_stm ~eq_frame ~mapping p2 (mapping.this ^^ n^^"out"^string_of_int out_numb,(int_of_bool false)) tag stm)
 | Assign(LVar(t,n),(Expr e),s) ->
    let out_numb = List.length eq_frame.acalls in
    let expr = trans_expr ~mapping out_numb t e in
    (match expr with
    | `Single e -> trans_stm ~eq_frame ~mapping:(assign n e ~mapping) tag s    
    | `Split p -> 
        let p1,p2 = get_split_preds_and_negs p in
        trans_preds_assign_stm ~eq_frame ~mapping p1 (n,(int_of_bool true)) tag stm @
        trans_preds_assign_stm ~eq_frame ~mapping p2 (n,(int_of_bool false)) tag stm)
 | IfThenElse(guard,stm1,stm2,Revert) ->
    let out_numb = List.length eq_frame.acalls in
    let bpred = bexpr_pred ~mapping out_numb guard in
    let p1,p2 = get_split_preds_and_negs bpred in    
    trans_preds_if_stm ~eq_frame ~mapping p1 tag stm1 @
    trans_preds_if_stm ~eq_frame ~mapping p2 tag stm2
 | ReturnRhs(Call(addr,m,opt,el)) ->
   let calls = (trans_call ~mapping ~eq_frame ~tag:tag ~addr:addr ~meth:m ~value:opt ~sender:(int_of_address mapping.this) ~params:el) in
   List.flatten (List.map (fun eq -> return_single ~eq_frame:eq ~mapping (Var(ret(List.length eq.acalls)))) calls)
 | Assign(lhs,(Call(addr,m,opt,el)),s) ->
   let t = tag_of_lhs lhs in
   let calls = (trans_call ~mapping ~eq_frame ~tag:t ~addr:addr ~meth:m ~value:opt ~sender:(int_of_address mapping.this) ~params:el) in
   let fields = List.map (fun eq -> (List.map (fun (b,f) -> f^^"out"^string_of_int(List.length eq.acalls)) mapping.fields)) calls in
   let x = List.map2 (fun eq f -> 
    List.fold_left (fun acc field -> (field,(Var field))::acc) mapping.last_assignment f
   ) (calls) (fields) in
   let new_mappings = List.map (fun new_assignment -> {mapping with last_assignment = new_assignment}) x in
   let only_addr_fields = List.filter_map (fun (b,f) -> if b then Some f else None) mapping.fields in
   
   let aux2 f = List.map (fun (c,_) -> f c) mapping.meth_decl_list in
   let rec aux ~mapping ~eq = function
   | x::tl -> 
      let out_x = x^^"out"^string_of_int(List.length eq.acalls) in
      List.flatten (aux2 (fun a -> 
       let a = int_of_address a in
       let p = (lookup ~mapping out_x),Eq,a in
       let t = aux ~mapping:(assign ~mapping out_x a) ~eq tl in
       (match compress t with
       | None -> List.map (fun eq -> add_pred p ~eq_frame:eq) t
       | Some x -> x)))
   | [] -> 
       trans_stm 
      ~eq_frame:eq 
      ~mapping:(match lhs with 
               | LDiscard -> mapping 
               | LVar(_,n) -> (assign n (Var(ret(List.length eq.acalls))) ~mapping:mapping)
               | LField(_,n) -> (assign (mapping.this ^^ n) (Var(ret(List.length eq.acalls))) ~mapping:mapping))
      tag s
   in
   List.flatten (List.map2 (fun m e -> aux ~mapping:m ~eq:e only_addr_fields) new_mappings calls)
 | _ -> assert false
and trans_preds_assign_stm: type a b. eq_frame:eq_frame -> mapping:mapping -> Cofloco.pred list list -> (Cofloco.var * Cofloco.expr) -> a tag -> (a,b) stm -> eq_frame list =
fun ~eq_frame ~mapping preds_l (k,v) tag stm ->
  if List.length preds_l = 0 then [] else
    let eql = List.map (fun pl -> add_preds pl ~eq_frame) preds_l in
    List.flatten (List.map (fun eq -> trans_stm ~eq_frame:eq ~mapping:(assign k v ~mapping) tag stm) eql)
and trans_preds_if_stm: type a b. eq_frame:eq_frame -> mapping:mapping -> Cofloco.pred list list -> a tag -> (a,b) stm -> eq_frame list =
fun ~eq_frame ~mapping preds_l tag stm ->
  if List.length preds_l = 0 then [] else
    let eql = List.map (fun pl -> add_preds pl ~eq_frame) preds_l in
    List.fold_left (fun acc eq -> acc@trans_stm ~eq_frame:eq ~mapping tag stm) [] eql

let rec stm_concat: type a b. (a,[`Epsilon]) MicroSolidity.stm -> (a,b) MicroSolidity.stm -> (a,[`Epsilon]) MicroSolidity.stm =
 fun s1 s2 -> match s1 with
 | Revert -> Revert
 | Return -> Return
 | ReturnRhs r -> ReturnRhs r
 | Assign(l,r,s) -> Assign(l,r,(stm_concat s s2))
 | Epsilon -> Static.retype_stm s2
 | IfThenElse(c,stm1,stm2,stm3) ->
    let x = stm_concat stm3 s2 in
    let stm1 = (stm_concat stm1 x) in
    let stm2 = (stm_concat stm2 x) in
    IfThenElse(c,stm1,stm2,Revert)

let rec normalize : type a b. (a,b) stm -> (a,b) stm =
 function
 | IfThenElse(c,s1,s2,s3) ->
   let x = normalize s3 in
   IfThenElse(c,(stm_concat s1 x),(stm_concat s2 x),Revert)
 | Revert -> Revert
 | Return -> Return
 | ReturnRhs r -> ReturnRhs r
 | Assign(l,r,s) -> Assign(l,r,(normalize s))
 | Epsilon -> assert false

let trans_block ~mapping tag (Block(_,_,stm)) = 
  let eq_frame = {acalls=[];preds=[]} in
  trans_stm ~mapping ~eq_frame:eq_frame tag (normalize stm)

let forall_contract ~mapping ~otherwise f =
 let l = List.map (fun (c,ms) -> f c ms) mapping.meth_decl_list in
 List.flatten (List.map (fun (pred_opt,prog) -> (match pred_opt with | Some p -> (List.map (fun e -> add_pred p ~eq_frame:e) prog)| None -> prog)) l )
 
let trans_method ~fields ~meth_decl_list this (AnyMethodDecl(name,block,_payable)) = 
 let args,locals = args_of_block block in
 let to_sum_on =
  List.filter_map (fun (b,v) -> if b then Some v else None) (fields @ args) @ [msg_sender]
 in
 let rec aux ~mapping = 
  function
  | []    -> trans_block ~mapping (Utils.fst3 name) block
  | v::tl -> 
    forall_contract ~mapping ~otherwise:[] 
     (fun a _ -> 
       let a = int_of_address a in 
       let base_pred = ((lookup ~mapping v),Cofloco.Eq,a) in
       let mapping = (assign ~mapping v a) in
       let mapping = if List.exists (fun f -> f=(true,v)) fields then (assign ~mapping (v^^"out0") a) else mapping in 
       let t = aux ~mapping:mapping tl in
       (match compress t with
       | None -> (Some base_pred),t
       | Some p -> None,p)
       (*base_pred,t*)
     )
 in
 trans_fst_method ~fields ~meth_decl_list this ~name ~args ~locals ~typ_of:(aux to_sum_on)

let get_main ~fields cfg =
 let rec aux = function
 | AContract(a,_,_,_) :: tl -> ((Cofloco.Var (a^^balance)),Geq,Rat 0) :: (aux tl)
 | [] -> [((Cofloco.Var msg_value),Geq,Rat 0)]
 in
 let rec aux2 ~fields pred = function
 | [] -> assert false
 | AContract(addr,ml,fl,_) :: tl ->
    let len = List.length ml in
    if len=0 && fl = None then aux2 ~fields pred tl else
      let fields = List.map snd fields in
      let out_fields = List.map (fun f -> f^^"out0") fields in    
      let name = (string_of_meth "main" ((),TNil,"")) in 
      if len>0 then 
          let AnyMethodDecl(m,block,_) = List.nth ml 0 in
          let args,_ = args_of_block block in
          let other_params = fields @ msg_sender :: msg_value :: (List.map (fun a -> snd a) args)  in
          let fst_meth = (string_of_meth addr m),(List.map (fun v -> Var v) (other_params@out_fields@[ret 0])) in
          [((name, other_params),true,(Minus(Var(addr^^balance^^"out0"),Var(addr^^balance))),[fst_meth],pred)]
      else if fl<>None then
          let m,block = fallback,(match fl with Some block -> block | _ -> assert false) in
          let args,_ = args_of_block block in
          let other_params = fields @ msg_sender :: msg_value :: (List.map (fun a -> snd a) args)  in
          let fst_meth = (string_of_meth addr m),(List.map (fun v -> Var v) (other_params@out_fields@[ret 0])) in
          [((name, other_params),true,(Minus(Var(addr^^balance^^"out0"),Var(addr^^balance))),[fst_meth],pred)] 
      else
          assert false
 in
 let pred = aux cfg in
 aux2 ~fields pred cfg

let trans_contract ~fields ~meth_decl_list (AContract(a,meths,fb,_)) =
 List.fold_left (fun acc meth -> trans_method ~fields ~meth_decl_list a meth :: acc) 
 []
 (match fb with 
 | None -> meths 
 | Some fb -> meths @ [any_method_decl_of_fallback fb])

let trans cfg =
  let meth_decl_list =
    List.map (function AContract(a,methods,fb,_) ->
        a, List.map (function AnyMethodDecl(m,_,payable) -> AnyMeth m,payable) 
        methods @ (match fb with None -> [] | Some _ -> [AnyMeth fallback,true])
    ) cfg 
  in
  let fields =
    List.rev (List.fold_left(fun acc contr -> fields_of_a_contract contr @ acc) [] cfg) 
  in
  let eql = List.fold_left (fun acc contr -> trans_contract ~fields ~meth_decl_list contr @ acc) [] cfg in 
  
  (get_main ~fields cfg) @
  List.rev (List.flatten 
    (List.map (fun (name,var,list) -> (List.map (fun {acalls;preds} -> 
      (name,List.map snd var)
      ,false
      ,Rat 0
      ,acalls
      ,preds) 
    list)) 
  eql))