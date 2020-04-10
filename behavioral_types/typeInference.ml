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
let int_of_unit = TInt 0

let fields_of_a_contract (AContract(a,_,_,fields)) =
 List.rev_map
  (fun (AnyField f) -> eq_tag (fst f) Address <> None, a ^^ snd f)
  fields @
 [false, a ^^ balance]

type status =
 { saved_gamma : var list
 ; fields : var list
 ; gamma : (var * expr) list
 ; k : int
 ; frame_size : int
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

let lookup_gamma k gamma =
 try
  List.assoc k gamma
 with
  Not_found -> assert false

let lookup ~status k = lookup_gamma k status.gamma

let _push ~status l =
 assert (List.length l = status.frame_size);
 let gamma = ref status.gamma in
 for i = status.k downto status.frame_size + 1 do
  gamma :=
   assign_gamma (stack ^^ string_of_int i) (lookup_gamma (stack ^^ string_of_int (i - status.frame_size)) !gamma) !gamma
 done ;
 {status with gamma = Utils.set_prefix ~prefix:l !gamma}

let pop ~status =
 let gamma = ref status.gamma in
 for i = 1 to status.k - status.frame_size do
  gamma :=
   assign_gamma (stack ^^ string_of_int i) (lookup_gamma (stack ^^ string_of_int (i + status.frame_size)) !gamma) !gamma
 done ;
 for i = status.k - status.frame_size + 1 to status.k do
  gamma := assign_gamma (stack ^^ string_of_int i) bottom !gamma
 done ;
 List.map snd (Utils.prefix status.frame_size status.gamma),
 {status with gamma = !gamma }

let address_of ~status a =
 try
  List.find (fun c -> int_of_address c = a) status.contracts
 with
  Not_found ->
   Utils.error ("Unrecognized address: " ^ Types.pp_expr a);
   Utils.error ("Known addresses: " ^ String.concat "," status.contracts);
   assert false

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
  | Eq(Unit,_,_) -> TBool true
  | And(e1,e2) -> TAnd(type_of_pred ~status e1, type_of_pred ~status e2)
  | Or(e1,e2) -> TOr(type_of_pred ~status e1, type_of_pred ~status e2)
  | Not p -> TNot(type_of_pred ~status p)

let type_of_expr :
 type a. status:status -> a tag -> a MicroSolidity.expr ->
  [`Single of expr | `Split of pred]
= fun ~status tag expr ->
 match tag with
    Int -> `Single(type_of_iexpr ~status expr)
  | Bool -> `Split(type_of_pred ~status expr)
  | Address -> `Single(int_of_address (type_of_address ~status expr))
  | Unit -> `Single(int_of_unit)

let type_of_cont ~status =
 let _frame,_status = pop ~status in
 (* XXX *)
 TGamma [TInt 666999]

let rec type_of_stm : type a b. status:status -> a tag -> (a,b) stm -> typ =
fun ~status tag stm ->
 match stm with
  | ReturnRhs (Call _) ->
      (* XXX *)
      TGamma [TInt 666999]
  | ReturnRhs (Expr e) ->
     let e = type_of_expr ~status tag e in
     let is_empty = TEq(lookup ~status stack_address,bottom) in
     (match e with
         `Single _e ->
           let cont = type_of_cont ~status in
           TChoice(
            is_empty, TGamma (List.map (lookup ~status) status.fields),
            TNot is_empty, cont)
       | `Split p ->
           let cont1 = type_of_cont ~status in
           let cont2 = type_of_cont ~status in
           TChoice(
            is_empty, TGamma (List.map (lookup ~status) status.fields),
            TNot is_empty, TChoice(p, cont1, TNot p, cont2)))
  | Return ->
     let is_empty = TEq(lookup ~status stack_address,bottom) in
     let cont = type_of_cont ~status in
     TChoice(
      is_empty, TGamma (List.map (lookup ~status) status.fields),
      TNot is_empty, cont)
  | Revert -> TGamma (List.map (fun v -> TVar v) status.saved_gamma)
  | Assign(lhs,Expr e,stm) ->
     let lhs_tag = tag_of_lhs lhs in
     let lhs =
      match lhs with
       | LField f -> Some (status.this ^^ snd f)
       | LVar v -> Some (snd v)
       | LDiscard -> None in
     (match lhs with
         None -> type_of_stm ~status tag stm
       | Some lhs ->
          match type_of_expr ~status lhs_tag e with
             `Single e ->
               let status = assign ~status lhs e in
               type_of_stm ~status tag stm
           | `Split p ->
               let status1 = assign ~status lhs (int_of_bool true) in
               let typ1 = type_of_stm ~status:status1 tag stm in
               let status2 = assign ~status lhs (int_of_bool false) in
               let typ2 = type_of_stm ~status:status2 tag stm in
               TChoice(p,typ1,TNot p,typ2))
  | Assign(_,_rhs1,ReturnRhs _rhs2) ->
      (* XXX TODO *)
      TGamma [TInt 666999]
  | IfThenElse(guard,stm1,stm2,Revert) ->
     let guard = type_of_pred ~status guard in
     let stm1 = type_of_stm ~status tag stm1 in
     let stm2 = type_of_stm ~status tag stm2 in
     TChoice(guard,stm1,TNot guard,stm2)
  | _ -> assert false

let rec args_of_var_list : type a. a var_list -> (bool * var) list =
 function
    VNil -> []
  | VCons(n,tl) -> (eq_tag Address (fst n) <> None,snd n) :: args_of_var_list tl

let args_of_block (Block(args,locals,_)) =
 args_of_var_list args, args_of_var_list locals

let type_of_block ~status tag (Block(_,_,stm)) =
 type_of_stm ~status tag stm

let rec mk_stack ?(acc=[]) k =
 if k = 0 then acc
 else mk_stack ~acc:((stack ^^ string_of_int k)::acc) (k-1)

let forall_contract ~status f =
 let guards_and_typs = List.map f status.contracts in
 List.fold_right
  (fun (g,typ) acc -> TChoice(g,typ,TNot g,acc))
  guards_and_typs (TGamma (List.map (fun v -> TVar v) status.saved_gamma))

let type_of_a_method ~k ~frame_size ~fields ~contracts this (AnyMethodDecl(name,block,_payable)) =
 let args,locals = args_of_block block in
 let to_sum_on =
  List.filter_map (fun (b,v) -> if b then Some v else None)
   (fields @ args) @ [msg_sender] in
 let fields = List.map snd fields in
 let args = List.map snd args in
 let locals = List.map snd locals in
 let saved_gamma = List.map (fun n -> n ^ saved) fields in
 let stack = mk_stack k in
 let other_params = fields @ msg_sender :: msg_value :: args @ stack in
 let gamma =
  List.map (fun v -> v,TVar v) other_params @
  List.map (fun v -> v,bottom) locals in
 let status =
  { saved_gamma ; fields ; gamma ; k ; frame_size ; this ; contracts } in
 let rec aux ~status =
  function
     [] -> type_of_block ~status (Utils.fst3 name) block
   | v::tl ->
      forall_contract ~status
       (fun a ->
         let a = int_of_address a in
         TEq(lookup ~status v,a),aux ~status:(assign ~status v a) tl) in
 let typ = aux ~status to_sum_on in
 this ^^ Utils.trd3 name, saved_gamma @ other_params, typ

let type_of_a_contract ~k ~frame_size ~fields ~contracts (AContract(a,meths,fb,_)) =
 List.fold_left
  (fun acc meth -> type_of_a_method ~k ~frame_size ~fields ~contracts a meth :: acc) []
   (match fb with None -> meths | Some fb -> meths @ [any_method_decl_of_fallback fb])

let type_of ~max_args ~max_stack cfg =
 let contracts = List.map (function AContract(a,_,_,_) -> a) cfg in
 (* address, method, msg.sender, msg.value *)
 let continuation_args = 4 in
 let frame_size = continuation_args + max_args in
 let k = frame_size * (1 + max_stack) in
 let fields =
  List.rev (
   List.fold_left
    (fun acc contr -> fields_of_a_contract contr @ acc) [] cfg) in
 let program_rev =
  List.fold_left
   (fun acc contr -> type_of_a_contract ~k ~frame_size ~fields ~contracts contr @ acc) [] cfg in
 List.rev program_rev
