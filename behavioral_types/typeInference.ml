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


let string_of_meth addr m =
 addr ^^ Utils.trd3 m ^^ String.concat "_" (pp_tag_list (Utils.snd3 m))
let int_of_address : MicroSolidity.address -> expr =
 fun n -> TInt (Hashtbl.hash n)
let int_of_meth : ('a,'b) meth -> expr =
 fun m -> TInt (Hashtbl.hash (Utils.snd3 m, Utils.trd3 m))
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
 ; contracts : (address * Parser.any_meth list) list
 }

type frame =
 { addr : expr
 ; meth : expr
 ; value : expr
 ; sender : expr
 ; params : expr list
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

let from_frame ~status { addr ; meth ; value ; sender ; params } =
 let l = addr::meth::value::sender::params in
 l @ Utils.mk_list bottom (status.frame_size - List.length l)

let to_frame ~status l =
 assert (status.frame_size = List.length l);
 match l with
    addr::meth::value::sender::params ->
     { addr ; meth ; value ; sender ; params }
  | _ -> assert false

let push ~status frame =
 let l = from_frame ~status frame in
 let gamma = ref status.gamma in
 for i = status.k downto status.frame_size + 1 do
  gamma :=
   assign_gamma (stack ^^ string_of_int i) (lookup_gamma (stack ^^ string_of_int (i - status.frame_size)) !gamma) !gamma
 done ;
 Utils.iteri
  (fun i v -> gamma := assign_gamma (stack ^^ string_of_int i) v !gamma) l;
 {status with gamma = !gamma}

let pop ~status =
 let gamma = ref status.gamma in
 for i = 1 to status.k - status.frame_size do
  gamma :=
   assign_gamma (stack ^^ string_of_int i) (lookup_gamma (stack ^^ string_of_int (i + status.frame_size)) !gamma) !gamma
 done ;
 for i = status.k - status.frame_size + 1 to status.k do
  gamma := assign_gamma (stack ^^ string_of_int i) bottom !gamma
 done ;
 let rec read i =
  if i > status.frame_size then []
  else
   lookup_gamma (stack ^^ string_of_int i) status.gamma :: read (i+1) in
 to_frame ~status (read 1), {status with gamma = !gamma }

let address_of ~status v =
 let a = lookup ~status v in
 try
  fst (List.find (fun (c,_) -> int_of_address c = a) status.contracts)
 with
  Not_found ->
   Utils.error ("Variable or field " ^ v);
   Utils.error ("holds the unrecognized address: " ^ Types.pp_expr a);
   Utils.error ("Known addresses: " ^ String.concat "," (List.map fst status.contracts));
   assert false

let type_of_address : status:status -> address MicroSolidity.expr -> address =
fun ~status expr ->
 match expr with
    Value a -> a
  | Var v -> address_of ~status (snd v)
  | Field v -> address_of ~status (status.this ^^ snd v)
  | This -> status.this
  | MsgSender -> address_of ~status msg_sender

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

let revert ~status =
 TGamma (List.map (fun v -> TVar v) status.saved_gamma)

let distribute_split l =
 let rec aux acc =
  function
     [] -> acc
   | `Single expr :: tl ->
       let acc =
        List.map (fun (accp,accl) -> accp,List.cons expr accl) acc in
       aux acc tl
   | `Split p :: tl ->
       let acctrue =
        List.map (fun (accp,accl) ->
          TAnd(accp,p),List.cons (int_of_bool true) accl) acc in
       let accfalse =
        List.map (fun (accp,accl) ->
          TAnd(accp,TNot p),List.cons (int_of_bool false) accl) acc in
       aux (acctrue @ accfalse) tl
 in
  aux [TBool true,[]] l


let forall_boolean ~status l f =
 let ll = distribute_split l in
 let rec aux =
  function
     [] -> revert ~status
   | (p,l)::ll ->
      let typ = f l in
      TChoice(p,typ,TNot p,aux ll)
 in
  aux ll

let type_of_value ~status v =
 Option.fold ~none:(TInt 0) ~some:(type_of_iexpr ~status) v

let type_of_expr_poly ~status =
 object
  method f : 'a. 'a tag -> 'a MicroSolidity.expr -> 'b
           = type_of_expr ~status 
 end

let type_of_call0 :
 status:status -> addr:address -> meth:(_ meth) ->
  value:expr -> sender:expr -> params:(expr list) -> typ
= fun ~status ~addr ~meth ~value ~sender ~params ->
 assert (List.length params = tag_list_length (Utils.snd3 meth));
 let name = string_of_meth addr meth in
(*
 let params = prefix ??? params in XXXX
 bisogna guardare se invocare il fallback e le pippe sul payable sì o no!
 (con tanto di incremento del balance!)
*)
 let stack =
  let rec aux i =
   if i > status.k then []
   else lookup ~status (stack ^^ string_of_int i) :: aux (i+1) in
   aux 1 in
 let args =
  List.map (fun v -> TVar v) status.saved_gamma @
  List.map (lookup ~status) status.fields @
  sender :: value :: params @ stack in
 TCall(name,args)

let type_of_call :
 status:status ->
  addr:(address MicroSolidity.expr) -> meth:(_ meth) ->
   value:(int MicroSolidity.expr option) -> sender:expr ->
    params:('b expr_list) -> typ
= fun ~status ~addr ~meth ~value ~sender ~params ->
 let addr = type_of_address ~status addr in
 let value = type_of_value ~status value in
 let params =
  expr_list_map (type_of_expr_poly ~status) (Utils.snd3 meth) params in
 forall_boolean ~status params
  (fun params -> type_of_call0 ~status ~addr ~meth ~value ~sender ~params)

let forall_contract ~status f =
 let guards_and_typs = List.map (fun (c,ms) -> f c ms) status.contracts in
 List.fold_right (fun (g,typ) acc -> TChoice(g,typ,TNot g,acc))
  guards_and_typs (revert ~status)

(* we could iterate only on those that are continuation, but we have not
   tracked this information *)
let forall_methods ~status meths f =
 let guards_and_typs = List.map f meths in
 List.fold_right (fun (g,typ) acc -> TChoice(g,typ,TNot g,acc))
  guards_and_typs (revert ~status)

let type_of_cont ~status ret =
 let {addr;meth;value;sender;params},status = pop ~status in
 forall_contract ~status
  (fun addr' meths ->
    TEq(addr,int_of_address addr'),
    forall_methods ~status meths 
     (fun (Parser.AnyMeth meth') ->
       let params =
        Utils.prefix (tag_list_length (Utils.snd3 meth')) (ret::params) in
       TEq(meth,int_of_meth meth'),
       type_of_call0 ~status ~addr:addr' ~meth:meth' ~value ~sender ~params))

let rec type_of_stm : type a b. status:status -> a tag -> (a,b) stm -> typ =
fun ~status tag stm ->
 match stm with
  | ReturnRhs (Call(a1,m1,val1,args1)) ->
      let sender = int_of_address status.this in
      type_of_call ~status ~addr:a1 ~meth:m1 ~value:val1 ~sender
       ~params:args1
  | ReturnRhs (Expr e) ->
     let e = type_of_expr ~status tag e in
     let is_empty = TEq(lookup ~status stack_address,bottom) in
     (match e with
         `Single e ->
           let cont = type_of_cont ~status e in
           TChoice(
            is_empty, TGamma (List.map (lookup ~status) status.fields),
            TNot is_empty, cont)
       | `Split p ->
           let cont1 = type_of_cont ~status (int_of_bool true) in
           let cont2 = type_of_cont ~status (int_of_bool false) in
           TChoice(
            is_empty, TGamma (List.map (lookup ~status) status.fields),
            TNot is_empty, TChoice(p, cont1, TNot p, cont2)))
  | Return ->
     let is_empty = TEq(lookup ~status stack_address,bottom) in
     let cont = type_of_cont ~status int_of_unit in
     TChoice(
      is_empty, TGamma (List.map (lookup ~status) status.fields),
      TNot is_empty, cont)
  | Revert -> revert ~status
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
  | Assign(_,Call(a1,m1,val1,args1),ReturnRhs Call(a2,m2,None,args2)) ->
     let args2 =
      expr_list_map (type_of_expr_poly ~status) (Utils.snd3 m2) args2 in
     let a2 = int_of_address (type_of_address ~status a2) in
     let m2 = int_of_meth m2 in
     let sender = int_of_address status.this in
     let value = type_of_iexpr ~status MsgValue in
     forall_boolean ~status args2
      (fun args2 ->
        let f = 
         { addr = a2
         ; meth = m2
         ; value
         ; sender
         ; params = args2
         } in
        let status = push ~status f in
        type_of_call ~status ~addr:a1 ~meth:m1 ~value:val1 ~sender
         ~params:args1)
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
     [] ->
      type_of_block ~status (Utils.fst3 name) block
   | v::tl ->
      forall_contract ~status
       (fun a _ ->
         let a = int_of_address a in
         TEq(lookup ~status v,a),aux ~status:(assign ~status v a) tl) in
 let typ = aux ~status to_sum_on in
 string_of_meth this name, saved_gamma @ other_params, typ

let type_of_a_contract ~k ~frame_size ~fields ~contracts (AContract(a,meths,fb,_)) =
 List.fold_left
  (fun acc meth -> type_of_a_method ~k ~frame_size ~fields ~contracts a meth :: acc) []
   (match fb with None -> meths | Some fb -> meths @ [any_method_decl_of_fallback fb])

let type_of ~max_args ~max_stack cfg =
 let contracts =
  List.map
   (function AContract(a,methods,_,_) ->
     a,
     List.map (function AnyMethodDecl(m,_,_) -> Parser.AnyMeth m)
      methods
   ) cfg in
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
