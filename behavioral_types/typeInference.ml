open MicroSolidity
open Types

let (^^) s1 s2 = s1 ^ "_" ^ s2

let msg_sender = "_msg_sender_"
let msg_value = "_msg_value_"
let balance = "_balance_"
let saved = "_saved"
let stack = "_stack_"
let dummy = TInt 0 (* XXX eliminarne il bisogno *)

(* for the dispatcher *)
let ret = "ret"
let runtime = "runtime"
let dispatch = Int,TCons(Int,TNil),"dispatch"

let stack_address = stack ^^ string_of_int 1
(*let stack_method = stack ^^ string_of_int 2*)

let bottom = TInt min_int

(* local variables are initialized to:
   - bottom if address
   - otherwise, i.e.
     - 0 if integral
     - false if boolean *)
let zero is_address =
 if is_address then bottom else TInt 0

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
 ; contracts : (address * (Parser.any_meth * (*payable:*)bool) list) list
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
  Not_found ->
   Utils.error k;
   assert false

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
 TGamma (List.map (fun v -> TVar v) (status.saved_gamma @ status.saved_gamma))

let commit ~status =
 TGamma (List.map (fun v -> TVar v) status.saved_gamma @
  List.map (lookup ~status) status.fields)

let distribute_split l =
 let rec aux acc =
  function
     [] -> acc
   | `Single expr :: tl ->
       let acc =
        List.map (fun (accp,accl) -> accp,List.cons expr accl) acc in
       aux acc tl
   | `Split p :: tl ->
(* XXX optimize here to avoid the split when not necessary *)
       let acctrue =
        List.map (fun (accp,accl) ->
          TAnd(accp,p),List.cons (int_of_bool true) accl) acc in
       let accfalse =
        List.map (fun (accp,accl) ->
          TAnd(accp,TNot p),List.cons (int_of_bool false) accl) acc in
       aux (acctrue @ accfalse) tl
 in
  aux [TBool true,[]] l

let if_then_else p t1 t2 =
 if t1 = t2 then t1 else TChoice [p,t1 ; TNot p,t2]

let forall_boolean ~status l f =
 let ll = distribute_split l in
 (* minimal optimization, waiting for an improved distribute_split *) 
 match ll with
    [TBool true, l] -> f l
  | _ ->
    let rec aux =
     function
        [] -> revert ~status
      | (p,l)::ll ->
         let typ = f l in
         if_then_else p typ (aux ll)
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

type any_return_meth =
 AnyReturnMeth : ('a,'b) meth * bool * 'b expr_list -> any_return_meth

let match_method : type a b. status:status -> address -> (a,b) meth -> b expr_list -> any_return_meth option
= fun ~status addr meth params ->
 let meths =
  try List.assoc addr status.contracts
  with Not_found -> assert false in
 let rec aux :
  type a b. (a,b) meth -> b expr_list -> (Parser.any_meth * bool) list -> any_return_meth
  = fun meth params meths ->
  match meths with
     [] -> raise Not_found
   | (Parser.AnyMeth meth',payable)::tl ->
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

let transfer0 ~status ~from ~to_ ~amount =
 let status =
  assign ~status (from ^^ balance)
   (TMinus(lookup ~status (from ^^ balance),amount)) in
 let status =
  assign ~status (to_ ^^ balance)
   (TPlus(lookup ~status (to_ ^^ balance),amount)) in
 status

let transfer ~status to_ amount k =
 if match_method ~status to_ fallback ENil = None
 then revert ~status
 else
  let from = status.this in
  let from_balance = lookup ~status (from ^^ balance) in
  if_then_else (TAnd(TGeq(amount,TInt 0),TGeq(from_balance,amount)))
   (k ~status:(transfer0 ~status ~from ~to_ ~amount))
   (revert ~status)

let msg_transfer ~status a1 val1 args1 k =
 if val1 <> None then
  revert ~status
 else
  let amount = match args1 with ECons(e,ENil) -> e in
  let amount = type_of_iexpr ~status amount in
  let to_ = type_of_address ~status a1 in
  transfer ~status to_ amount k

let type_of_call :
 status:status ->
  tag:('a tag) -> addr:(address MicroSolidity.expr) -> meth:(('a,_) meth) ->
   value:(int MicroSolidity.expr option) -> sender:expr ->
    params:('b expr_list) -> typ
= fun ~status ~tag ~addr ~meth ~value ~sender ~params ->
 let addr = type_of_address ~status addr in
 match match_method ~status addr meth params with
    None -> revert ~status
  | Some AnyReturnMeth(meth,payable,params) ->
     let output_type_ok =
      eq_tag tag Unit <> None || eq_tag tag (Utils.fst3 meth) <> None in
     let payable_ok = payable || value = None in
     if output_type_ok && payable_ok then
      let amount = type_of_value ~status value in
      let params =
       expr_list_map (type_of_expr_poly ~status) (Utils.snd3 meth) params in
      forall_boolean ~status params
       (fun params ->
         if value = None then
          type_of_call0 ~status ~addr ~meth ~value:amount ~sender ~params
         else
          transfer ~status addr amount
           (type_of_call0 ~addr ~meth ~value:amount ~sender ~params))
     else
      revert ~status

let tchoice ~status:_ guards_and_typs =
 (* tiny improvement to legibility *)
 let tor guard g = if guard = TBool false then g else TOr(guard,g) in
 let rec aux guard =
  function
     [] -> [(*TNot guard, revert ~status*)]
   | (g,typ)::tl ->
      (g,typ)::aux (tor guard g) tl
 in
  TChoice (aux (TBool false) guards_and_typs)

(* if all branches are the same, compress to one by just puting in Or
   all the guards *)
let compress ~status l0 =
 let rec aux acc l =
  match acc,l with
     None,[] -> TChoice []
   | Some p,[] -> snd p
   | None,hd::tl -> aux (Some hd) tl
   | Some hd1,hd2::tl when snd hd1 = snd hd2 ->
      aux (Some (TOr(fst hd1,fst hd2),snd hd1)) tl
   | _ -> tchoice ~status l0 in
 aux None l0

let forall_contract ~status ~otherwise f =
 let l = List.map (fun (c,ms) -> f c ms) status.contracts in
 if otherwise = [] then compress ~status l else tchoice ~status (l@otherwise)

(* we could iterate only on those that are continuation, but we have not
   tracked this information *)
let forall_methods ~status meths f =
 tchoice ~status (List.map f meths)

let mk_type_of_cont ~status ret =
 let is_empty = TEq(lookup ~status stack_address,bottom) in
 let otherwise=[is_empty, commit ~status] in
 let {addr;meth;value;sender;params},status = pop ~status in
 forall_contract ~status ~otherwise
  (fun addr' meths ->
    TEq(addr,int_of_address addr'),
    forall_methods ~status meths 
     (fun (Parser.AnyMeth meth',_) ->
       let params =
        Utils.prefix (tag_list_length (Utils.snd3 meth')) (ret::params) in
       TEq(meth,int_of_meth meth'),
       type_of_call0 ~status ~addr:addr' ~meth:meth' ~value ~sender ~params))

(* fallback to simple case of no continuations *)
let mk_type_of_cont ~status ret =
 if status.k > 0 then mk_type_of_cont ~status ret
 else commit ~status

let type_of_cont ~status ret =
 type_of_call0 ~status ~addr:runtime ~meth:dispatch
  ~value:dummy ~sender:dummy ~params:[ret]

let rec type_of_stm : type a b. status:status -> a tag -> (a,b) stm -> typ =
fun ~status tag stm ->
 match stm with
  | ReturnRhs (Call(a1,(Unit,TCons(Int,TNil),"transfer"),val1,args1)) ->
     msg_transfer ~status a1 val1 args1 (type_of_cont int_of_unit)
  | ReturnRhs (Call(a1,m1,val1,args1)) ->
(*
Utils.error("# " ^ pp_stm ~indent:0 tag stm);
let res =
*)
      let sender = int_of_address status.this in
      type_of_call ~status ~tag ~addr:a1 ~meth:m1 ~value:val1 ~sender
       ~params:args1
(*
in Utils.error("# " ^ pp_stm ~indent:0 tag stm ^ " : " ^ pp_typ ~indent:0 res); res *)
  | ReturnRhs (Expr e) ->
     let e = type_of_expr ~status tag e in
     (match e with
         `Single e -> type_of_cont ~status e
       | `Split p ->
           let cont1 = type_of_cont ~status (int_of_bool true) in
           let cont2 = type_of_cont ~status (int_of_bool false) in
           if_then_else p cont1 cont2)
  | Return -> type_of_cont ~status int_of_unit
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
               if_then_else p typ1 typ2)
  | Assign(LDiscard,Call(a1,(Unit,TCons(Int,TNil),"transfer"),val1,args1),stm)->
    msg_transfer ~status a1 val1 args1 (type_of_stm tag stm)
  | Assign(lhs,Call(a1,m1,val1,args1),ReturnRhs Call(a2,m2,None,args2)) ->
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
        type_of_call ~status ~tag:(tag_of_lhs lhs) ~addr:a1 ~meth:m1
         ~value:val1 ~sender ~params:args1)
  | IfThenElse(guard,stm1,stm2,Revert) ->
     let guard = type_of_pred ~status guard in
     let stm1 = type_of_stm ~status tag stm1 in
     let stm2 = type_of_stm ~status tag stm2 in
     if_then_else guard stm1 stm2
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

let type_of_a_method0 ~k ~frame_size ~fields ~contracts this ~name ~args ~locals ~typ_of =
 let fields = List.map snd fields in
 let args = List.map snd args in
 let saved_gamma = List.map (fun n -> n ^ saved) fields in
 let stack = mk_stack k in
 let other_params = fields @ msg_sender :: msg_value :: args @ stack in
 let gamma =
  List.map (fun v -> v,TVar v) other_params @
  List.map (fun (t,v) -> v,zero t) locals in
 let status =
  { saved_gamma ; fields ; gamma ; k ; frame_size ; this ; contracts } in
 let typ = typ_of ~status in
 string_of_meth this name, saved_gamma @ other_params, typ

let type_of_a_method ~k ~frame_size ~fields ~contracts this (AnyMethodDecl(name,block,_payable)) =
 let args,locals = args_of_block block in
 let to_sum_on =
  List.filter_map (fun (b,v) -> if b then Some v else None)
   (fields @ args) @ [msg_sender] in
 let rec aux ~status =
  function
     [] ->
      type_of_block ~status (Utils.fst3 name) block
   | v::tl ->
      forall_contract ~status ~otherwise:[]
       (fun a _ ->
         let a = int_of_address a in
         TEq(lookup ~status v,a),aux ~status:(assign ~status v a) tl) in
 type_of_a_method0 ~k ~frame_size ~fields ~contracts this ~name ~args ~locals
  ~typ_of:(aux to_sum_on)

let type_of_a_contract ~k ~frame_size ~fields ~contracts (AContract(a,meths,fb,_)) =
 Utils.error (a ^ " encoded as " ^ pp_expr (int_of_address a));
 List.fold_left
  (fun acc meth -> type_of_a_method ~k ~frame_size ~fields ~contracts a meth :: acc) []
   (match fb with None -> meths | Some fb -> meths @ [any_method_decl_of_fallback fb])

type inferred =
 { types: Types.types ;
   fieldsno : int ;
   non_negatives : string list
 }

let type_of ~max_args ~max_stack cfg =
 let contracts =
  List.map
   (function AContract(a,methods,fb,_) ->
     a,
     List.map (function AnyMethodDecl(m,_,payable) ->
       Parser.AnyMeth m,payable) methods
      @ (match fb with None -> [] | Some _ -> [Parser.AnyMeth fallback,true])
   ) cfg in
 (* address, method, msg.sender, msg.value *)
 let continuation_args = 4 in
 let frame_size = continuation_args + max_args in
 let k = frame_size * (1 + max_stack) in
 (* fallback to simple case of no continuations *)
 let frame_size,k = if max_stack = 0 then 0,0 else frame_size,k in
 let fields =
  List.rev (
   List.fold_left
    (fun acc contr -> fields_of_a_contract contr @ acc) [] cfg) in
 let program_rev =
  List.fold_left
   (fun acc contr -> type_of_a_contract ~k ~frame_size ~fields ~contracts contr @ acc) [] cfg in
 let balances = List.map (fun (a,_) -> a ^^ balance) contracts in
 let fieldsno = List.length fields in
 let types =
  List.rev program_rev
  @ [type_of_a_method0 ~k ~frame_size ~fields ~contracts runtime
     ~name:dispatch ~args:[Int,ret] ~locals:[] ~typ_of:(mk_type_of_cont (TVar ret))] in
 { types ; fieldsno ; non_negatives = balances@[msg_value] }
