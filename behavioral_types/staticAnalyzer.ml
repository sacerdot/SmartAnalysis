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
 { initial_fields : Cofloco.var list
 ; fields          : Cofloco.var list
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
  | [] -> assert false
  | (k',_)::tl when k=k' -> (k,v)::tl
  | p::tl -> p::set_assignment k v tl
let assign k v ~mapping = {mapping with last_assignment = set_assignment k v mapping.last_assignment}

let lookup_assignment k assign =
 try List.assoc k assign
 with Not_found -> assert false
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

let trans_address : mapping:mapping -> address MicroSolidity.expr -> address =
fun ~mapping expr ->
 match expr with
    Value a -> a
  | Var v -> address_of ~mapping (snd v)
  | Field v -> address_of ~mapping (mapping.this ^^ snd v)
  | This -> mapping.this
  | MsgSender -> address_of ~mapping msg_sender
let rec trans_iexpr : mapping:mapping -> int MicroSolidity.expr -> Cofloco.expr =
fun ~mapping expr ->
 match expr with
    Value b -> Rat b
  | Var v -> lookup ~mapping (snd v)
  | Field v -> lookup ~mapping (mapping.this ^^ snd v)
  | Plus(e1,e2) -> Plus(trans_iexpr ~mapping e1, trans_iexpr ~mapping e2)
  | Minus(e1,e2) -> Minus(trans_iexpr ~mapping e1, trans_iexpr ~mapping e2)
  | Mult(e1,e2) ->
    let e1 = trans_iexpr ~mapping e1 in
    let e2 = trans_iexpr ~mapping e2 in
    (match e1 with
    | Rat x -> Mult(x,e2)
    | _ -> (match e2 with
          | Rat x -> Mult(x,e1)
          | _ -> assert false))
  | Div(e1,e2) ->
    let e1 = trans_iexpr ~mapping e1 in
    let e2 = trans_iexpr ~mapping e2 in
    (match e2 with
    | Rat x -> Div(e1,x)
    | _ -> assert false)
  | UMinus e -> UMinus(trans_iexpr ~mapping e)
  | MsgValue -> lookup ~mapping msg_value
  | Balance a -> lookup ~mapping (trans_address ~mapping a ^^ balance)

let rec bexpr_pred : mapping:mapping -> bool MicroSolidity.expr -> Types.pred =
 fun ~mapping -> function
 | Value b -> TBool b
 | Var v -> 
   let res = lookup ~mapping (snd v) in
   TEq(lookup_to_typ_e res, (TInt 1))
 | Field v -> 
   let res = lookup ~mapping (mapping.this ^^ snd v) in
   TEq(lookup_to_typ_e res, (TInt 1))
 | Geq(e1,e2) -> TGeq(iexpr_to_expr ~mapping e1, iexpr_to_expr ~mapping e2)
 | Gt(e1,e2) -> TGt(iexpr_to_expr ~mapping e1, iexpr_to_expr ~mapping e2)
 | Eq(Int,e1,e2) -> TEq(iexpr_to_expr ~mapping e1, iexpr_to_expr ~mapping e2)
 | Eq(Bool,e1,e2) ->
   let e1 = bexpr_pred ~mapping e1 in
   let e2 = bexpr_pred ~mapping e2 in
   TOr(TAnd(e1,e2),TAnd(TNot e1,TNot e2))
 | Eq(Address,a1,a2) ->
   (match int_of_address (trans_address ~mapping a1),int_of_address (trans_address ~mapping a2) with
   | Rat a1,Rat a2 -> TEq(TInt a1,TInt a2)
   | _ -> assert false
   )
 | Eq(Unit,_,_) -> TBool true
 | And(e1,e2) -> TAnd(bexpr_pred ~mapping e1, bexpr_pred ~mapping e2)
 | Or(e1,e2) -> TOr(bexpr_pred ~mapping e1, bexpr_pred ~mapping e2)
 | Not p -> TNot(bexpr_pred ~mapping p)
and iexpr_to_expr : mapping:mapping -> int MicroSolidity.expr -> Types.expr =
fun ~mapping expr ->
 match expr with
 | Value i -> TInt i
 | Var v -> 
   let res = lookup ~mapping (snd v) in
   lookup_to_typ_e res
 | Field v -> 
   let res = lookup ~mapping (mapping.this ^^ snd v) in
   lookup_to_typ_e res
 | Plus(e1,e2) -> TPlus(iexpr_to_expr ~mapping e1, iexpr_to_expr ~mapping e2)
 | Minus(e1,e2) -> TMinus(iexpr_to_expr ~mapping e1, iexpr_to_expr ~mapping e2)
 | Mult(e1,e2) -> TMult(iexpr_to_expr ~mapping e1, iexpr_to_expr ~mapping e2)
 | Div(e1,e2) -> TDiv(iexpr_to_expr ~mapping e1, iexpr_to_expr ~mapping e2)
 | UMinus e -> TUMinus(iexpr_to_expr ~mapping e)
 | MsgValue -> 
   let res = lookup ~mapping msg_value in
   lookup_to_typ_e res
 | Balance a -> 
   let res = lookup ~mapping (trans_address ~mapping a ^^ balance) in
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
 type a. mapping:mapping -> a tag -> a MicroSolidity.expr -> 
  [`Single of Cofloco.expr | `Split of Types.pred]
= fun ~mapping tag expr ->
 match tag with
    Int -> `Single (trans_iexpr ~mapping expr)
  | Bool -> `Split(bexpr_pred ~mapping expr)
  | Address -> `Single (int_of_address (trans_address ~mapping expr))
  | Unit -> `Single (int_of_unit)

(*trans functs*)
(********************************************)
let trans_fst_method ~fields ~meth_decl_list this ~name ~args ~locals ~typ_of =
 let fields = List.map snd fields in
 let args   = List.map snd args in
 let initial_fields = List.map (fun n -> n ^ initial) fields in
 let other_params = fields @ msg_sender :: msg_value :: args @ [ret 0] in
 let last_assignment =
  List.map (fun v -> v,Cofloco.Var v) (initial_fields@other_params) @
  List.map (fun (t,v) -> v,zero t) locals in
 let mapping = { initial_fields; fields ; last_assignment ; this ; meth_decl_list } in
 let typ = typ_of ~mapping in
 string_of_meth this name, initial_fields@other_params, typ

let rec args_of_var_list : type a. a MicroSolidity.var_list -> (bool * Cofloco.var) list =
 function
 | VNil -> []
 | VCons(n,tl) -> (eq_tag Address (fst n) <> None,snd n) :: args_of_var_list tl

let args_of_block (Block(args,locals,_)) =
 args_of_var_list args, args_of_var_list locals

let trans_value ~mapping v =
 Option.fold ~none:(Rat 0) ~some:(trans_iexpr ~mapping) v

let type_of_expr_poly ~mapping =
 object
  method f : 'a. 'a tag -> 'a MicroSolidity.expr -> 'b
           = trans_expr ~mapping 
 end

let transfer :
 mapping:mapping -> eq_frame:eq_frame -> addr:address -> meth:(_ meth) ->
  value:expr -> sender:expr -> params:(expr list) -> acall
= fun ~mapping ~eq_frame ~addr ~meth ~value ~sender ~params ->
 assert (List.length params = tag_list_length (Utils.snd3 meth));
 let name = string_of_meth addr meth in
 
 let from = mapping.this in
 let from_balance = lookup ~mapping (from^^balance) in

 let to_balance = lookup ~mapping (addr^^balance) in
 let mapping = assign (from^^balance) (Minus(from_balance,value)) ~mapping in
 let mapping = assign (addr^^balance) (Plus(to_balance,value)) ~mapping:mapping in
 
 let args =
  List.map (fun f -> Var f) mapping.initial_fields @

  List.map (lookup ~mapping:mapping) mapping.fields @
  sender :: value :: params @ [Cofloco.Var (ret ((List.length eq_frame.acalls)+1))] in
  name,args

let trans_call0 :
 mapping:mapping -> eq_frame:eq_frame -> addr:address -> meth:(_ meth) ->
  value:expr -> sender:expr -> params:(expr list) -> acall
= fun ~mapping ~eq_frame ~addr ~meth ~value ~sender ~params ->
 assert (List.length params = tag_list_length (Utils.snd3 meth));
 let name = string_of_meth addr meth in
 let args =
  List.map (fun f -> Var f) mapping.initial_fields @
  List.map (lookup ~mapping) mapping.fields @
  sender :: value :: params @ [Cofloco.Var (ret ((List.length eq_frame.acalls)+1))] in
  name,args

let rec trans_call_param :
 mapping:mapping -> eq_frame:eq_frame -> addr:address -> meth:(_ meth) ->
  value:expr -> sender:expr -> params:('a list) -> Cofloco.expr list -> eq_frame list
= fun ~mapping ~eq_frame ~addr ~meth ~value ~sender ~params expr_params ->
 match params with
 | (`Single e)::tl -> trans_call_param ~mapping ~eq_frame ~addr ~meth ~value ~sender ~params:tl (expr_params@[e])
 | (`Split p)::tl -> 
   let p1 = CostEquationsGeneration.compute_pred p in
   let p2 = (CostEquationsGeneration.neg p1) in

   let eq_f1 = 
    if List.length p1 >= 1 then
     let eql_p1 = List.map (fun pl -> add_preds pl ~eq_frame) p1 in
     List.map (fun eq -> trans_call_param ~mapping ~eq_frame:eq ~addr ~meth ~value ~sender ~params:tl (expr_params@[(Rat 1)])) eql_p1
    else [] in
   let eq_f2 = 
    if List.length p2 >= 1 then
     let eql_p2 = List.map (fun pl -> add_preds pl ~eq_frame) p2 in
     List.map (fun eq -> trans_call_param ~mapping ~eq_frame:eq ~addr ~meth ~value ~sender ~params:tl (expr_params@[(Rat 0)])) eql_p2
    else [] in

    List.flatten eq_f1@ List.flatten eq_f2
 | [] -> 
   if value<>Rat 0 then
    let from = mapping.this in
    let from_balance = lookup ~mapping (from^^balance) in
    let eq = add_acall (transfer ~mapping ~eq_frame ~addr ~meth ~value:value ~sender ~params:expr_params) ~eq_frame in
    [add_preds [from_balance,Geq,value; value,Geq,Rat 0] eq]
   else [add_acall (trans_call0 ~mapping ~eq_frame ~addr ~meth ~value:value ~sender ~params:expr_params) ~eq_frame]

let trans_call :
 mapping:mapping -> eq_frame:eq_frame ->
  tag:('a tag) -> addr:(address MicroSolidity.expr) -> meth:(('a,_) meth) ->
   value:(int MicroSolidity.expr option) -> sender:expr ->
    params:('b expr_list) -> eq_frame list
= fun ~mapping ~eq_frame ~tag ~addr ~meth ~value ~sender ~params ->
 let addr = trans_address ~mapping addr in
 match match_method ~mapping addr meth params with
    None -> []
  | Some AnyReturnMeth(meth,payable,params) ->
     let output_type_ok =
      eq_tag tag Unit <> None || eq_tag tag (Utils.fst3 meth) <> None in
     let payable_ok = payable || value = None in
     if output_type_ok && payable_ok then
      let amount = trans_value ~mapping value in
      let params =
       expr_list_map (type_of_expr_poly ~mapping) (Utils.snd3 meth) params in      
      trans_call_param ~mapping ~eq_frame ~addr ~meth ~value:amount ~sender ~params:params []
     else
      []
and trans_call_transfer :
 mapping:mapping -> eq_frame:eq_frame ->
  tag:('a tag) -> addr:(address MicroSolidity.expr) -> meth:(('a,_) meth) ->
   value:(int MicroSolidity.expr option) -> sender:expr ->
    params:('b expr_list) -> eq_frame list
= fun ~mapping ~eq_frame ~tag ~addr ~meth ~value ~sender ~params ->
 let addr = trans_address ~mapping addr in
 
 let params2 =
  expr_list_map (type_of_expr_poly ~mapping) (Utils.snd3 meth) params in 
 let v = (match params2 with (`Single e)::[] -> e | _ -> Rat 0) in 
 
 match match_method ~mapping addr meth params with
    None -> []
  | Some AnyReturnMeth(((Unit,TNil,name) as meth),payable,_) ->
     let output_type_ok =
      eq_tag tag Unit <> None || eq_tag tag (Utils.fst3 meth) <> None in
     let payable_ok = payable || value = None in
     if output_type_ok && payable_ok then
      let amount = trans_value ~mapping value in
      let from = mapping.this in
      let from_balance = lookup ~mapping (from^^balance) in
      let to_balance = lookup ~mapping (addr^^balance) in
      let mapping = assign (from^^balance) (Minus(from_balance,v)) ~mapping in
      let mapping = assign (addr^^balance) (Plus(to_balance,v)) ~mapping:mapping in
      let args =
        List.map (fun f -> Var f) mapping.initial_fields @
        List.map (lookup ~mapping:mapping) mapping.fields @
        sender :: v :: [Cofloco.Var (ret ((List.length eq_frame.acalls)+1))] in
      let acall = (addr^^name^"_"),args in
      let eq = add_acall acall ~eq_frame in
      [add_preds [from_balance,Geq,v; v,Geq,Rat 0] eq]
     else
      []
  | _ -> assert false
  
let rec trans_stm : type a b. eq_frame:eq_frame -> mapping:mapping -> a tag -> (a,b) stm -> eq_frame list =
fun ~eq_frame ~mapping tag stm ->
 match stm with
 | Revert -> []
 | Return -> [add_pred (Var(ret 0),Eq,Rat 0) ~eq_frame]
 | ReturnRhs(Expr e) -> 
    let expr = trans_expr ~mapping tag e in
    (match expr with
    | `Single e -> [add_pred (Var(ret 0),Eq,e) eq_frame]
    | `Split p -> 
        let p1 = CostEquationsGeneration.compute_pred p in
        let p2 = (CostEquationsGeneration.neg p1) in

        let eq_f1 = 
         if List.length p1 >= 1 then
          let eql_p1 = List.map (fun pl -> add_preds pl ~eq_frame) p1 in
          List.map (fun eq -> add_pred (Var(ret 0),Eq,(int_of_bool true)) eq) eql_p1
         else [] in
        let eq_f2 = 
         if List.length p2 >= 1 then
          let eql_p2 = List.map (fun pl -> add_preds pl ~eq_frame) p2 in
          List.map (fun eq -> add_pred (Var(ret 0),Eq,(int_of_bool false)) eq) eql_p2
         else [] in

        eq_f1@eq_f2
    )
 | ReturnRhs(Call(addr,((Unit,TCons(Int,TNil),name) as m),opt,el)) when (String.equal name "transfer") || (String.equal name "send") ->
   let calls = (trans_call_transfer ~mapping ~eq_frame ~tag:Unit ~addr:addr ~meth:m ~value:opt ~sender:(int_of_address mapping.this) ~params:el) in
   List.map (fun eq -> add_pred (Var(ret 0),Eq,Var(ret(List.length eq.acalls))) eq) calls
 | ReturnRhs(Call(addr,m,opt,el)) ->
   let calls = (trans_call ~mapping ~eq_frame ~tag:tag ~addr:addr ~meth:m ~value:opt ~sender:(int_of_address mapping.this) ~params:el) in
   List.map (fun eq -> add_pred (Var(ret 0),Eq,Var(ret(List.length eq.acalls))) eq) calls
 | Assign(LField(t,n),(Expr e),s) ->
    let expr = trans_expr ~mapping t e in
    (match expr with
    | `Single e -> trans_stm ~eq_frame ~mapping:(assign (mapping.this ^^ n) e ~mapping) tag s    
    | `Split p -> 
        let p1 = CostEquationsGeneration.compute_pred p in
        let p2 = (CostEquationsGeneration.neg p1) in

        let eq_f1 = 
         if List.length p1 >= 1 then
          let eql_p1 = List.map (fun pl -> add_preds pl ~eq_frame) p1 in
          List.map (fun eq -> trans_stm ~eq_frame:eq ~mapping:(assign (mapping.this ^^ n) (int_of_bool true) ~mapping) tag s) eql_p1
         else [] in
        let eq_f2 = 
         if List.length p2 >= 1 then
          let eql_p2 = List.map (fun pl -> add_preds pl ~eq_frame) p2 in
          List.map (fun eq -> trans_stm ~eq_frame:eq ~mapping:(assign (mapping.this ^^ n) (int_of_bool false) ~mapping) tag s) eql_p2
         else [] in

        List.flatten (eq_f1)@
        List.flatten (eq_f2)
    )
 | Assign(LVar(t,n),(Expr e),s) ->
    let expr = trans_expr ~mapping t e in
    (match expr with
    | `Single e -> trans_stm ~eq_frame ~mapping:(assign n e ~mapping) tag s    
    | `Split p -> 
        let p1 = CostEquationsGeneration.compute_pred p in
        let p2 = (CostEquationsGeneration.neg p1) in

        let eq_f1 = 
         if List.length p1 >= 1 then
          let eql_p1 = List.map (fun pl -> add_preds pl ~eq_frame) p1 in
          List.map (fun eq -> trans_stm ~eq_frame:eq ~mapping:(assign (n) (int_of_bool true) ~mapping) tag s) eql_p1
         else [] in
        let eq_f2 = 
         if List.length p2 >= 1 then
          let eql_p2 = List.map (fun pl -> add_preds pl ~eq_frame) p2 in
          List.map (fun eq -> trans_stm ~eq_frame:eq ~mapping:(assign (n) (int_of_bool false) ~mapping) tag s) eql_p2
         else [] in

        List.flatten (eq_f1)@
        List.flatten (eq_f2)
    )

 | Assign(LDiscard,(Call(addr,((Unit,TCons(Int,TNil),name) as m),opt,el)),s) when (String.equal name "transfer") || (String.equal name "send") ->
   let calls = (trans_call_transfer ~mapping ~eq_frame ~tag:Unit ~addr:addr ~meth:m ~value:opt ~sender:(int_of_address mapping.this) ~params:el) in
   List.flatten (List.map (fun eq -> trans_stm ~eq_frame:eq ~mapping tag s) calls)
 | Assign(LDiscard,(Call(addr,m,opt,el)),s) ->
   let calls = (trans_call ~mapping ~eq_frame ~tag:Unit ~addr:addr ~meth:m ~value:opt ~sender:(int_of_address mapping.this) ~params:el) in
   List.flatten (List.map (fun eq -> trans_stm ~eq_frame:eq ~mapping tag s) calls)
 | Assign((LVar(t,n)),(Call(addr,m,opt,el)),s) ->
   let calls = (trans_call ~mapping ~eq_frame ~tag:t ~addr:addr ~meth:m ~value:opt ~sender:(int_of_address mapping.this) ~params:el) in
   List.flatten (List.map (fun eq -> trans_stm ~eq_frame:eq ~mapping:(assign n (Var(ret(List.length eq.acalls))) ~mapping) tag s) calls)
 | Assign((LField(t,n)),(Call(addr,m,opt,el)),s) ->
   let calls = (trans_call ~mapping ~eq_frame ~tag:t ~addr:addr ~meth:m ~value:opt ~sender:(int_of_address mapping.this) ~params:el) in
   List.flatten (List.map (fun eq -> trans_stm ~eq_frame:eq ~mapping:(assign (mapping.this ^^ n) (Var(ret(List.length eq.acalls))) ~mapping) tag s) calls)
 | IfThenElse(guard,stm1,stm2,Revert) ->
    let bpred = bexpr_pred ~mapping guard in
    let stm1_p = CostEquationsGeneration.compute_pred bpred in
    let stm2_p = (CostEquationsGeneration.neg stm1_p) in
    
    let eq_f1 = 
     if List.length stm1_p >= 1 then
      let eql_stm1 = List.map (fun pl -> add_preds pl ~eq_frame) stm1_p in
      List.fold_left (fun acc eq -> acc@trans_stm ~eq_frame:eq ~mapping tag stm1) [] eql_stm1
     else [] in
    let eq_f2 = 
     if List.length stm2_p >= 1 then
      let eql_stm2 = List.map (fun pl -> add_preds pl ~eq_frame) stm2_p in
      List.fold_left (fun acc eq -> acc@trans_stm ~eq_frame:eq ~mapping tag stm2) [] eql_stm2
     else [] in

    eq_f1@eq_f2
 | _ -> assert false

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
 let p = List.flatten (List.map (fun (p,prog) -> (List.map (fun e -> add_pred p ~eq_frame:e) prog)) l) in
 p
 
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
       let t = aux ~mapping:(assign ~mapping v a) tl in
       base_pred,t
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
    if List.length ml = 0 && fl = None then aux2 ~fields pred tl else
    (match (List.nth_opt ml 0),fl with
    | (Some AnyMethodDecl(m,block,_)),_ ->
      let fields = List.map snd fields in
      let args,_ = args_of_block block in
      let other_params = fields @ msg_sender :: msg_value :: (List.map (fun a -> snd a) args)  in
      let name = (string_of_meth "main" ((),TNil,"")) in
      let fst_meth = (string_of_meth addr m),(List.map (fun v -> Var v) fields)@(List.map (fun v -> Var v) other_params)@[Var (ret 0)] in
      [((name, other_params),false,(Cofloco.Rat 0),[fst_meth],pred)]
    | _,Some block -> 
      let fields = List.map snd fields in
      let args,_ = args_of_block block in
      let other_params = fields @ msg_sender :: msg_value :: (List.map (fun a -> snd a) args)  in
      let name = (string_of_meth "main" ((),TNil,"")) in
      let fst_meth = (string_of_meth addr MicroSolidity.fallback),(List.map (fun v -> Var v) fields)@(List.map (fun v -> Var v) other_params)@[Var (ret 0)] in
      [((name, other_params),false,(Cofloco.Rat 0),[fst_meth],pred)]
    | _ -> assert false) 
 in
 let pred = aux cfg in
 aux2 ~fields pred cfg

let rec all_fallback_names = function
| [] -> []
| (AContract(a,_,fb,_))::tl ->
   (match fb with 
   | None -> all_fallback_names tl
   | Some fb -> 
     let AnyMethodDecl(m,_,_) = any_method_decl_of_fallback fb in
     string_of_meth a m :: all_fallback_names tl)

let rec get_main_costEq = function
 | [] -> assert false
 | AContract(_,ml,fl,_) :: tl when List.length ml = 0 && fl = None -> get_main_costEq tl 
 | AContract(addr,_,_,_) :: tl -> Cofloco.Minus(Var(addr^^balance^initial),Var(addr^^balance))

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
  
  let main_costEq = get_main_costEq cfg in
  let fallbacks = all_fallback_names cfg in

  (get_main ~fields cfg) @
  List.rev (List.flatten 
    (List.map (fun (name,var,list) -> (List.map (fun {acalls;preds} -> 
      (name,var)
      ,false
      ,(if List.exists (fun n -> String.equal n name) fallbacks then main_costEq else (Rat 0))
      ,acalls
      ,preds) 
    list)) 
  eql))