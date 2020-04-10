open MicroSolidity
open Types

let (^^) s1 s2 = s1 ^ "_" ^ s2

let msg_sender = "_msg_sender_"
let msg_value = "_msg_value_"
let balance = "_balance_"
let saved = "_saved"
let stack = "_stack_"

let stack_address = stack ^^ string_of_int 1
(*let stack_method = stack ^^ string_of_int 2*)

let bottom = TInt min_int

let int_of_address : MicroSolidity.address -> expr =
 fun n -> TInt (Hashtbl.hash n)
let int_of_bool = function false -> TInt 0 | true -> TInt 1

let fields_of_a_contract (AContract(a,_,_,fields)) =
 List.rev_map (fun (AnyField f) -> a ^^ snd f) fields @
  [a ^^ balance]

type status =
 { saved_gamma : var list
 ; fields : var list
 ; gamma : (var * expr) list
 ; k : int
 ; this : address
 ; contracts : address list
 }

let rec assign_gamma k v =
 function
    [] -> assert false
  | (k',_)::tl when k=k' -> (k,v)::tl
  | p::tl -> p::assign_gamma k v tl

let assign k v ~status =
 {status with gamma = assign_gamma k v status.gamma}

let lookup ~status k =
 try
  List.assoc k status.gamma
 with
  Not_found -> assert false

let address_of ~status a =
 try
  List.find (fun c -> int_of_address c = a) status.contracts
 with
  Not_found -> assert false

let type_of_address : status:status -> address MicroSolidity.expr -> address =
fun ~status expr ->
 match expr with
    Value a -> a
  | Var v -> address_of ~status (lookup ~status (snd v))
  | Field v -> address_of ~status (lookup ~status (status.this ^^ snd v))
  | This -> status.this
  | MsgSender -> address_of ~status (lookup ~status msg_sender)

let rec type_of_iexpr : status:status -> int MicroSolidity.expr -> expr =
fun ~status expr ->
 match expr with
    Value b -> TInt b
  | Var v -> lookup ~status (snd v)
  | Field v -> lookup ~status (status.this ^^ snd v)
  | Plus(e1,e2) -> TPlus(type_of_iexpr ~status e1, type_of_iexpr ~status e2)
  | Minus(e1,e2) -> TMinus(type_of_iexpr ~status e1, type_of_iexpr ~status e2)
  | Mult(e1,e2) -> TMult(type_of_iexpr ~status e1, type_of_iexpr ~status e2)
  | Div(e1,e2) -> TDiv(type_of_iexpr ~status e1, type_of_iexpr ~status e2)
  | UMinus e -> TUMinus(type_of_iexpr ~status e)
  | MsgValue -> lookup ~status msg_value
  | Balance a -> lookup ~status (type_of_address ~status a ^^ balance)

let rec type_of_pred : status:status -> bool MicroSolidity.expr -> pred =
fun ~status expr ->
 match expr with
    Value b -> TBool b
  | Var v -> TEq(lookup ~status (snd v), int_of_bool true)
  | Field v -> TEq(lookup ~status (status.this ^^ snd v), int_of_bool true)
  | Geq(e1,e2) -> TGeq(type_of_iexpr ~status e1, type_of_iexpr ~status e2)
  | Gt(e1,e2) -> TGt(type_of_iexpr ~status e1, type_of_iexpr ~status e2)
  | Eq(Int,e1,e2) -> TEq(type_of_iexpr ~status e1, type_of_iexpr ~status e2)
  | Eq(Bool,e1,e2) ->
     let e1 = type_of_pred ~status e1 in
     let e2 = type_of_pred ~status e2 in
     TOr(TAnd(e1,e2),TAnd(TNot e1,TNot e2))
  | Eq(Address,a1,a2) ->
     let a1 = int_of_address (type_of_address ~status a1) in
     let a2 = int_of_address (type_of_address ~status a2) in
     TEq(a1,a2)
  | Eq(_,_,_) -> assert false
  | And(e1,e2) -> TAnd(type_of_pred ~status e1, type_of_pred ~status e2)
  | Or(e1,e2) -> TOr(type_of_pred ~status e1, type_of_pred ~status e2)
  | Not p -> TNot(type_of_pred ~status p)

let type_of_expr : type a. status:status -> a MicroSolidity.expr -> expr =
fun ~status:_ _expr ->
 (* XXX *)
 TInt 999666

let rec type_of_stm : type a b. status:status -> (a,b) stm -> typ =
fun ~status stm ->
 match stm with
  | ReturnRhs _rhs ->
      (* XXX TODO *)
      TGamma [TInt 666999]
  | Return ->
     if lookup ~status stack_address = bottom then
      TGamma (List.map (lookup ~status) status.fields)
     else
      (* XXX TODO *)
      TGamma [TInt 666999]
  | Revert -> TGamma (List.map (fun v -> TVar v) status.saved_gamma)
  | Assign(lhs,Expr e,stm) ->
     let lhs =
      match lhs with
       | LField f -> Some (status.this ^^ snd f)
       | LVar v -> Some (snd v)
       | LDiscard -> None in
     (match lhs with
         None -> type_of_stm ~status stm
       | Some lhs ->
          let e = type_of_expr ~status e in
          let status = assign ~status lhs e in
          type_of_stm ~status stm)
  | Assign(_,_rhs1,ReturnRhs _rhs2) ->
      (* XXX TODO *)
      TGamma [TInt 666999]
  | IfThenElse(guard,stm1,stm2,Revert) ->
     let guard = type_of_pred ~status guard in
     let stm1 = type_of_stm ~status stm1 in
     let stm2 = type_of_stm ~status stm2 in
     TPlus(guard,stm1,TNot guard,stm2)
  | _ -> assert false

let rec args_of_var_list : type a. a var_list -> var list =
 function
    VNil -> []
  | VCons(n,tl) -> snd n :: args_of_var_list tl

let args_of_block (Block(args,locals,_)) =
 args_of_var_list args @ args_of_var_list locals

let type_of_block ~status (Block(_,_,stm)) =
 type_of_stm ~status stm

let rec mk_stack ?(acc=[]) k =
 if k = 0 then acc
 else mk_stack ~acc:((stack ^^ string_of_int k)::acc) (k-1)

let type_of_a_method ~k ~fields ~contracts this (AnyMethodDecl(name,block,_payable)) =
 let saved_gamma = List.map (fun n -> n ^ saved) fields in
 let args = args_of_block block in
 let other_params = fields @ msg_sender :: msg_value :: args in
 let stack = mk_stack k in
 let status =
  { saved_gamma
  ; fields
  ; gamma =
     List.map (fun v -> v,TVar v) other_params @
     List.map (fun v -> v,bottom) stack
  ; k
  ; this
  ; contracts
  } in
 let typ = type_of_block ~status block in
 this ^^ Utils.trd3 name, saved_gamma @ other_params @ stack, typ

let type_of_a_contract ~k ~fields ~contracts (AContract(a,meths,fb,_)) =
 List.fold_left
  (fun acc meth -> type_of_a_method ~k ~fields ~contracts a meth :: acc) []
   (match fb with None -> meths | Some fb -> meths @ [any_method_decl_of_fallback fb])

let type_of ~max_args ~max_stack cfg =
 let contracts = List.map (function AContract(a,_,_,_) -> a) cfg in
 (* address, method, msg.sender, msg.value *)
 let continuation_args = 4 in
 let k = (continuation_args + max_args) * max_stack in
 let fields =
  List.rev (
   List.fold_left
    (fun acc contr -> fields_of_a_contract contr @ acc) [] cfg) in
 let program_rev =
  List.fold_left
   (fun acc contr -> type_of_a_contract ~k ~fields ~contracts contr @ acc) [] cfg in
 List.rev program_rev
