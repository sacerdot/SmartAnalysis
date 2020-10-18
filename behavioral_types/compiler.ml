open MicroSolidity
open Solidity

exception CompilationFail of string

(*ANY_Solidity_TYPE*)
type any_Solidity_tag         = AnyTag      : 'a Solidity.tag -> any_Solidity_tag
type any_Solidity_tag_list    = AnyTagList  : 'a Solidity.tag_list -> any_Solidity_tag_list
type any_Solidity_meth        = AnySolMeth  : ('a,'b) Solidity.meth -> any_Solidity_meth
type any_Solidity_var_list    = AnyVarList  : 'a Solidity.var_list -> any_Solidity_var_list
type any_Solidity_lhs         = AnyLhs      : 'a Solidity.lhs * 'a Solidity.tag -> any_Solidity_lhs
type any_Solidity_expr        = AnyExpr     : 'a Solidity.tag * 'a Solidity.expr -> any_Solidity_expr
(*ANY_USOLIDITY_TYPE*)
type any_uSolidity_meth     = AnyMeth : ('a,'b) MicroSolidity.meth -> any_uSolidity_meth
type any_microSolidity_stm  = AnyStm : 'a MicroSolidity.tag option * ('a,'b) MicroSolidity.stm -> any_microSolidity_stm
(*TRANS TYPE*)
type mapping = {contracts: string list; call: MicroSolidity.address MicroSolidity.expr;
                meths : (any_uSolidity_meth*Solidity.view) list; trans : Solidity.interface Solidity.expr;
                ref_to: Solidity.interface option}
type table = mapping list

let default_constructor = 
  Solidity.Block(Solidity.VNil,Solidity.Public,Solidity.Payable
    ,Solidity.VNil,Solidity.Assign((LField(Bool,"_initialized")),(Expr(Value(false))),Return))
let snd_or_trans: type a b. (a,b) MicroSolidity.meth -> bool =
 fun (t,tl,n) ->
  match t,tl with
  | MicroSolidity.Unit,(MicroSolidity.TCons(Int,TNil)) -> (String.equal n "send") || (String.equal n "transfer")
  | _,_ -> false
(*trans FUNCTS *)
let convert_tag: type a. bool -> a MicroSolidity.tag -> any_Solidity_tag = 
 fun force_uint_cast -> 
  function
  | MicroSolidity.Unit     -> AnyTag Solidity.Unit
  | MicroSolidity.Int      -> if force_uint_cast then AnyTag Solidity.UInt else AnyTag Solidity.Int
  | MicroSolidity.Bool     -> AnyTag Solidity.Bool
  | MicroSolidity.Address  -> AnyTag Solidity.Address
let rec convert_tag_list: type a. bool -> a MicroSolidity.tag_list -> any_Solidity_tag_list = 
 fun force_uint_cast -> 
  function
  | TNil -> AnyTagList TNil
  | TCons(h,t) -> 
    let (AnyTag tag)   = convert_tag force_uint_cast h in
    let (AnyTagList x) = convert_tag_list force_uint_cast t in
    AnyTagList(Solidity.TCons(tag, x))
let rec convert_var_list: type a. a MicroSolidity.var_list -> any_Solidity_var_list = 
 function
 | VNil -> AnyVarList VNil
 | VCons((t,n),tl) ->
   let (AnyTag tag)    = convert_tag false t in
   let (AnyVarList x)  = convert_var_list tl in
   AnyVarList(Solidity.VCons(((tag,n)), x))
let convert_meth: type a b. (a,b) MicroSolidity.meth -> any_Solidity_meth = 
 fun (t,tl,name) -> 
   let (AnyTag tag)         = convert_tag false t in
   let force_uint_cast      = snd_or_trans(t,tl,name) in
   let (AnyTagList tagList) = convert_tag_list force_uint_cast tl in
   AnySolMeth(tag,tagList,name)

(**FUN TABLE*)
let rec find_match_in_table:
 type a b. table -> string -> MicroSolidity.address MicroSolidity.expr -> (a,b) MicroSolidity.meth option -> bool =
  fun tbl c cl m -> 
   List.exists (fun {contracts;call;meths;trans;ref_to} -> 
      (List.exists (fun s -> String.equal s c) contracts) && call=cl && 
      (match m with | None -> true | Some m -> (List.exists (fun (x,_) -> x=(AnyMeth(m))) meths))
    ) tbl
let add_in_table : 
 table -> string -> MicroSolidity.address MicroSolidity.expr -> (any_uSolidity_meth*Solidity.view) list -> (Solidity.interface option * Solidity.interface Solidity.expr) -> table =
  fun tbl addr call ml_vis (i,i_expr) -> {contracts=[addr]; call=call; meths=ml_vis; trans=i_expr; ref_to=i}::tbl
let add_method_to_entry_table: mapping -> any_uSolidity_meth*Solidity.view -> mapping = 
 fun e m_vis -> {contracts=e.contracts; call=e.call; meths=e.meths@[m_vis]; trans=e.trans; ref_to=e.ref_to}

let rec get_trans_or_none: 
 type a b. table -> string -> MicroSolidity.address MicroSolidity.expr -> (a,b) MicroSolidity.meth option -> mapping option =
  fun tbl c cl m ->
   List.find_opt 
    (fun {contracts;call;meths;trans;ref_to} -> 
      (List.exists (fun s -> String.equal s c) contracts) && call=cl && 
      (match m with | None -> true | Some m -> (List.exists (fun (x,_) -> x=(AnyMeth(m))) meths))
    ) tbl

let get_new_interface : 
 table -> MicroSolidity.address MicroSolidity.expr -> (Solidity.interface option * Solidity.interface Solidity.expr) =
  fun tbl ->
   let new_name = "Interf"^string_of_int(List.length tbl) in
   function 
   | MsgSender -> (Some(IID(new_name)),AddressToInterface(IID(new_name),MsgSender))
   | This      -> assert false(*(None,This)*) (*((Some(IID(new_name)),AddressToInterface((IID(new_name)),(InterfaceToAddress(This)))))*)
   | Value x   -> (Some(IID(new_name)),Field(Interface,String.uncapitalize_ascii x))
   | Var(Address,x)   -> (Some(IID(new_name)),AddressToInterface(IID(new_name),Var(Address,String.uncapitalize_ascii x)))
   | Field(Address,x) -> (Some(IID(new_name)),AddressToInterface(IID(new_name),Var(Address,String.uncapitalize_ascii x)))

let rec get_mapping: table -> string -> MicroSolidity.address MicroSolidity.expr -> table = 
 fun tbl addr c ->
  List.filter (fun {contracts;call;meths;trans;ref_to} -> 
   (List.exists (fun s -> String.equal s addr) contracts) && call=c) tbl

let rec update_table_expr: 
 type a. table -> string -> a MicroSolidity.tag -> a MicroSolidity.expr -> table =
  fun tbl addr tag -> 
   function
   | Plus(a,b) -> update_table_expr (update_table_expr tbl addr Int a) addr Int b
   | Minus(a,b) -> update_table_expr (update_table_expr tbl addr Int a) addr Int b
   | Mult(a,b) -> update_table_expr (update_table_expr tbl addr Int a) addr Int b
   | Div(a,b) -> update_table_expr (update_table_expr tbl addr Int a) addr Int b
   | UMinus(a) -> update_table_expr tbl addr Int a
   | Geq(a,b) -> update_table_expr (update_table_expr tbl addr Int a) addr Int b
   | Gt(a,b) -> update_table_expr (update_table_expr tbl addr Int a) addr Int b
   | Eq(t,a,b) -> update_table_expr (update_table_expr tbl addr t a) addr t b
   | And(a,b) -> update_table_expr (update_table_expr tbl addr Bool a) addr Bool b
   | Or(a,b) -> update_table_expr (update_table_expr tbl addr Bool a) addr Bool b
   | Not(a) -> update_table_expr tbl addr Bool a
   | Value x -> (match tag with 
     | Address -> 
       let entry_opt = List.find_opt (fun {contracts;call;meths;trans;ref_to} -> call=(Value x)) tbl in
       (match entry_opt with
       | Some e -> (*add addr to contracts *)
         if List.exists (fun s -> String.equal s addr) e.contracts then tbl(*nothing to do*)
         else {contracts=addr::e.contracts;call=e.call;meths=e.meths;trans=e.trans;ref_to=e.ref_to}
               ::(List.filter (fun {contracts;call;meths;trans;ref_to} -> call<>e.call) tbl)
       | None ->  (*crate interface and add to table*)
         let (i_typ,trans_e) = get_new_interface tbl (Value x) in (*create interface*)
         let new_entry = {contracts=[addr];call=(Value x);meths=[];trans=trans_e;ref_to=i_typ} in
         new_entry::tbl(*add interf*))
     | _ -> tbl)
   | Balance x -> update_table_expr tbl addr (Address) x
   | _ -> tbl
let rec update_table_expr_list:
 type a. table -> string -> a MicroSolidity.tag_list -> a MicroSolidity.expr_list -> table =
  fun tbl addr tl el -> match tl,el with
  | TNil,ENil -> tbl
  | TCons(t,tl1),ECons(e,tl2) -> 
     let tbl0 = update_table_expr tbl addr t e in
     update_table_expr_list tbl0 addr tl1 tl2

let update_table_rhs:
 type a. table -> string -> a MicroSolidity.tag -> a MicroSolidity.rhs -> table =
  fun tbl addr tag -> 
   function
   | Expr e -> update_table_expr tbl addr tag e
   | Call(Value x,((t,tl,n) as m),opt,el) -> 
      let tbl0 = (match opt with | None -> tbl | Some e -> update_table_expr tbl addr Int e) in
      let tbl1 = update_table_expr_list tbl0 addr tl el in
      let view = (match opt with | Some _ -> Solidity.Payable | None -> Solidity.NoView) in
      if snd_or_trans m then (*send or transfer function are special function. they must not be added to inferface. *)
       let entry_opt = List.find_opt (fun {contracts;call;meths;trans;ref_to} -> call=(Value x)) tbl1 in
       (match entry_opt with
       | Some e -> (*add addr to contracts *)
         if List.exists (fun s -> String.equal s addr) e.contracts then tbl1(*nothing to do*)
         else {contracts=addr::e.contracts;call=e.call;meths=e.meths;trans=e.trans;ref_to=e.ref_to}
               ::(List.filter (fun {contracts;call;meths;trans;ref_to} -> call<>e.call) tbl1)
       | None ->  (*crate interface and add to table*)
         let (i_typ,trans_e) = get_new_interface tbl (Value x) in (*create interface*)
         let new_entry = {contracts=[addr];call=(Value x);meths=[];trans=trans_e;ref_to=i_typ} in
         new_entry::tbl1(*add interf*))
      else
       let entry_opt = List.find_opt (fun {contracts;call;meths;trans;ref_to} -> call=(Value x)) tbl1 in
       (match entry_opt with
       | Some e -> (*an entry match*)
          if List.exists (fun (x,_) -> x=AnyMeth(m)) e.meths then
            if List.exists (fun s -> String.equal s addr) e.contracts then tbl1(*nothing to do*)
            else {contracts=addr::e.contracts;call=e.call;meths=e.meths;trans=e.trans;ref_to=e.ref_to}
              ::(List.filter (fun {contracts;call;meths;trans;ref_to} -> call<>e.call) tbl1)(*add contract to *)
          else if List.exists (fun s -> String.equal s addr) e.contracts then
            {contracts=e.contracts;call=e.call;meths=((AnyMeth m),view)::e.meths;trans=e.trans;ref_to=e.ref_to}
            ::(List.filter (fun {contracts;call;meths;trans;ref_to} -> call<>e.call) tbl1)(*add method only*)
          else 
            {contracts=addr::e.contracts;call=e.call;meths=((AnyMeth m),view)::e.meths;trans=e.trans;ref_to=e.ref_to} (*add method and contract to *)
            ::(List.filter (fun {contracts;call;meths;trans;ref_to} -> call<>e.call) tbl1)
       | None ->  (*create interface and add to table*)
          let (i_typ,trans_e) = get_new_interface tbl1 (Value x) in (*create interface*)
          {contracts=[addr];call=(Value x);meths=[((AnyMeth m),view)];trans=trans_e;ref_to=i_typ}::tbl1)
   | Call(x,((t,tl,n) as m),opt,el) -> 
      let tbl0 = (match opt with | None -> tbl | Some e -> update_table_expr tbl addr Int e) in
      let tbl1 = update_table_expr_list tbl0 addr tl el in
      let view = (match opt with | Some _ -> Solidity.Payable | None -> Solidity.NoView) in
      if snd_or_trans m || x=This then tbl1
      else if find_match_in_table tbl1 addr x (Some m) then 
       tbl1 (*related interface has already been added, nothing to do. *)
      else 
       let interf_opt = get_mapping tbl1 addr x in
       let len_of_res = List.length interf_opt in
       if len_of_res>1 then assert false (*some bad happens.*)
       else if len_of_res=0 then (* create new interface and add method to interf *)
        let (i_typ,trans_e) = get_new_interface tbl1 x in (*create interface*)
        let new_entry = {contracts=[addr];call=x;meths=[(AnyMeth m),view];trans=trans_e;ref_to=i_typ} in
        new_entry::tbl1(*add interf*) 
       else (* add method to an existing interface *)
        let e = add_method_to_entry_table (List.nth interf_opt 0) ((AnyMeth m,view)) in
        e
        ::(List.filter (fun {contracts;call;meths;trans;ref_to} -> contracts<>e.contracts||call<>e.call||trans<>e.trans||ref_to<>e.ref_to) tbl1)
        
let rec update_table_stm: type a b. table -> string -> a MicroSolidity.tag -> (a,b) MicroSolidity.stm -> table =
 fun tbl addr tag -> 
  function
  | ReturnRhs rhs -> update_table_rhs tbl addr tag rhs
  | Assign(l,rhs,s) -> 
      let tag_lhs = MicroSolidity.tag_of_lhs l in
      let tbl0     = update_table_rhs tbl addr tag_lhs rhs in
      update_table_stm tbl0 addr tag s 
  | IfThenElse(cond,so,ss,st) ->
     let tbl0 = update_table_rhs tbl addr Bool (Expr cond) in  
     let tbl1 = update_table_stm tbl0 addr tag so in
     let tbl2 = update_table_stm tbl1 addr tag ss in
     update_table_stm tbl2 addr tag st 
  | _ -> tbl (*Epsilon, Return, Revert don't alter table*)
let rec update_table: table -> string -> MicroSolidity.methods -> table = 
 fun tbl addr ml -> 
  let rec aux tbl = function
  | (AnyMethodDecl((oty,_,_),Block(_,_,stm),_))::tl -> 
     let tbl0 = update_table_stm tbl addr oty stm in
     aux tbl0 tl
  | [] -> tbl
  in
  aux tbl ml
(****************)
(** NEXT FUNCTION ARE RELATED TO INTERFACE DEFINITION **)
(*Create a list of vars given a list of tags. Use this to dynamically create a method declaration*)
let rec create_var_list: type b. int -> b MicroSolidity.tag_list -> any_Solidity_var_list = 
 fun i -> 
   let rec create_name: int -> string = (*{a,b,....,aa,ab,....}*) 
    fun i -> if i<0 then "" else (create_name ((i/26)-1))^(String.make 1 (Char.chr(97+i mod 26)))
   in
   function
   | TNil -> AnyVarList Solidity.VNil
   | TCons(tag,tail) ->
     let (AnyTag new_tag) = convert_tag false tag in
     let (AnyVarList vl)  = create_var_list (i+1) tail in
     AnyVarList (Solidity.VCons(((new_tag,(create_name i))), vl))
let rec unify_type_tag_var :
 type a b. a Solidity.tag_list -> b Solidity.var_list -> a Solidity.var_list = 
  fun tl vl -> 
    match tl,vl with
    | Solidity.TNil, Solidity.VNil -> Solidity.VNil
    | Solidity.TCons(t,tl),Solidity.VCons(v,vl) ->
      let y = unify_type_tag_var tl vl in 
      (match t,v with
      | Int,((Int,name))              -> VCons(((Int,name)),y)
      | UInt,((UInt,name))            -> (VCons(((UInt,name)),y))
      | Byte,((Byte,name))            -> (VCons(((Byte,name)),y))
      | Bool,((Bool,name))            -> (VCons(((Bool,name)),y))
      | Address,((Address,name))      -> (VCons(((Address,name)),y))
      | Interface,((Interface,name))  -> (VCons(((Interface,name)),y))
      | _,_ -> raise (CompilationFail ("Fail in unify_type_tag_var: t and v have different types")))
    | _,_ -> raise (CompilationFail("Fail in unify_type_tag_var: tl and vl doesn't match"))
let rec add_methods_to_interface: 
 Solidity.functions -> (any_uSolidity_meth*Solidity.view) list -> Solidity.functions = 
  fun fl -> 
   function
   | (AnyMeth((tag,tl,name) as m),view)::tail ->
      let (AnySolMeth (t,tl2,n))  = convert_meth m in
      let (AnyVarList vl)         = create_var_list 0 tl in
      let vl2                     = unify_type_tag_var tl2 vl in 
      add_methods_to_interface (fl@[(Solidity.AnyFunct((t,tl2,n),vl2,Solidity.External,view))]) tail
   | [] -> fl
let process_a_mapping: mapping -> an_interface = 
 fun t -> 
   let get_iid = function | Some x -> x | None -> raise (CompilationFail ("Fail in get_iid")) in
   Solidity.AInterface((get_iid t.ref_to),(add_methods_to_interface [] t.meths))
let rec create_interface_decl: table -> an_interface list = 
 fun tbl -> List.fold_left (fun acc e -> (process_a_mapping e) :: acc) [] tbl
(**********)
let value_of_int (v:int) = Value v
let value_of_bool (v:bool) = Value v

let rec convert_expr:
 type a b. table -> string -> interface option -> a Solidity.tag -> b MicroSolidity.tag -> b MicroSolidity.expr -> a Solidity.expr =
  fun tbl cName interf_opt oty uSol_tag -> function
  | Field(t,n) -> 
    let trans_tag = convert_tag false t in
    (match trans_tag,oty with
    | AnyTag Int,Int -> Field(Int,n)
    | AnyTag Int,UInt -> IntToUInt(Field(Int,n))
    | AnyTag Bool,Bool -> Field(Bool,n)
    | AnyTag Address,Address -> Field(Address,n)
    | AnyTag Address,Interface -> (match interf_opt with
       | Some interf -> AddressToInterface(interf,Field(Address,n))
       | None -> (match get_trans_or_none tbl cName (Field(Address,n)) None with
                 | Some {contracts;call;meths;trans;ref_to} -> trans
                 | None -> assert false))
    | _,_ -> assert false)
  | Var(t,n) -> 
    let trans_tag = convert_tag false t in
    (match trans_tag,oty with
    | AnyTag Int,Int -> Var(Int,n)
    | AnyTag Int,UInt -> IntToUInt(Var(Int,n))
    | AnyTag Bool,Bool -> Var(Bool,n)
    | AnyTag Address,Address -> Var(Address,n)
    | AnyTag Address,Interface -> (match interf_opt with
       | Some interf -> AddressToInterface(interf,Var(Address,n))
       | None -> (match get_trans_or_none tbl cName (Var(Address,n)) None with
                 | Some {contracts;call;meths;trans;ref_to} -> trans
                 | None -> assert false))
    | _,_ -> assert false)
  | This -> (match oty with Interface -> This | Address -> InterfaceToAddress(This) | _ -> assert false)
  | Value v as e ->
   let AnyExpr(t,a) = convert_expr_value tbl cName interf_opt uSol_tag e in
   (match t,oty with
   | Int,Int              -> a
   | Int,UInt             -> IntToUInt a
   | Interface,Interface  -> a
   | Interface,Address    -> InterfaceToAddress a
   | Bool,Bool            -> a
   | _                    -> assert false)
  | Plus(a,b) -> 
     let trans = Plus((convert_expr tbl cName interf_opt Int Int a),(convert_expr tbl cName interf_opt Int Int b)) in
     (match oty with Int -> trans | UInt -> IntToUInt(trans) | _ -> assert false)
  | Minus(a,b) ->
     let trans = Minus((convert_expr tbl cName interf_opt Int Int a),(convert_expr tbl cName interf_opt Int Int b)) in
     (match oty with Int -> trans | UInt -> IntToUInt(trans) | _ -> assert false)
  | Mult(a,b) ->     
     let trans = Mult((convert_expr tbl cName interf_opt Int Int a),(convert_expr tbl cName interf_opt Int Int b)) in
     (match oty with Int -> trans | UInt -> IntToUInt(trans) | _ -> assert false)
  | Div(a,b) ->     
     let trans = Div((convert_expr tbl cName interf_opt Int Int a),(convert_expr tbl cName interf_opt Int Int b)) in
     (match oty with Int -> trans | UInt -> IntToUInt(trans) | _ -> assert false)
  | UMinus a ->     
     let trans = UMinus(convert_expr tbl cName interf_opt Int Int a) in
     (match oty with Int -> trans | UInt -> IntToUInt(trans) | _ -> assert false)
  | Geq(a,b) -> 
     let trans = Geq((convert_expr tbl cName interf_opt Int Int a),(convert_expr tbl cName interf_opt Int Int b)) in
     (match oty with Bool -> trans | _ -> assert false)
  | Gt(a,b) -> 
     let trans = Gt((convert_expr tbl cName interf_opt Int Int a),(convert_expr tbl cName interf_opt Int Int b)) in
     (match oty with Bool -> trans | _ -> assert false)
  | Eq(t,a,b) ->
     let AnyTag tag = convert_tag false t in 
     let trans = Eq(tag,(convert_expr tbl cName interf_opt tag t a),(convert_expr tbl cName interf_opt tag t b)) in
     (match oty with Bool -> trans | _ -> assert false)
  | And(a,b) ->
     let trans = And((convert_expr tbl cName interf_opt Bool Bool a),(convert_expr tbl cName interf_opt Bool Bool b)) in
     (match oty with Bool -> trans | _ -> assert false)
  | Or(a,b) ->
     let trans = Or((convert_expr tbl cName interf_opt Bool Bool a),(convert_expr tbl cName interf_opt Bool Bool b)) in
     (match oty with Bool -> trans | _ -> assert false)
  | Not a ->     
     let trans = Not(convert_expr tbl cName interf_opt Bool Bool a) in
     (match oty with Bool -> trans | _ -> assert false)
  | MsgSender -> (match oty with 
    | Address -> MsgSender
    | Interface -> (match interf_opt with
       | Some interf -> AddressToInterface(interf,MsgSender)
       | None -> (match get_trans_or_none tbl cName MsgSender None with
                 | Some {contracts;call;meths;trans;ref_to} -> trans
                 | None -> assert false))
    | _ -> assert false)
  | MsgValue -> (match oty with Int -> UIntToInt(MsgValue) | UInt -> MsgValue | _ -> assert false)
  | Balance addr ->
     let trans = convert_expr tbl cName interf_opt Address Address addr in
     (match oty with Int -> UIntToInt(Balance(trans)) | UInt -> Balance(trans) | _ -> assert false)
and convert_expr_value: 
 type a b. table -> string -> interface option -> a MicroSolidity.tag -> a MicroSolidity.expr -> any_Solidity_expr = 
  fun tbl cName interf_opt tag e -> match tag,e with
  | Int,Value y -> AnyExpr(Int,value_of_int y)
  | Bool,Value y -> AnyExpr(Bool,value_of_bool y)
  | Address,Value y -> 
     (match get_trans_or_none tbl cName (Value y) None with
      | Some {contracts;call;meths;trans;ref_to} ->
        AnyExpr(Interface,(match interf_opt,ref_to with
        | Some _,None -> assert false
        | Some interf1,Some interf2 -> if interf1=interf2 then trans else AddressToInterface(interf1,InterfaceToAddress(trans))
        | None,_ -> trans))
      | None -> raise (CompilationFail("Fail in convert_expr_value. Not found in table: CONTRACT="^cName^". EXPR="^(MicroSolidity.pp_expr Address (Value y)))))
  | _ -> assert false

let rec convert_expr_list: 
 type a b. table -> string -> b Solidity.tag_list -> a MicroSolidity.tag_list -> a MicroSolidity.expr_list -> b Solidity.expr_list = 
  fun tbl contractName sol_tl uSol_tl el ->
   match sol_tl,uSol_tl,el with
   | TNil,TNil,ENil -> ENil
   | TCons(sol_tag,tl1),TCons(usol_tag,tl2),ECons(expr,tl3) -> 
      ECons((convert_expr tbl contractName None sol_tag usol_tag expr),(convert_expr_list tbl contractName tl1 tl2 tl3))
   | _,_,_ -> assert false

let convert_rhs:
 type a b. table -> string -> interface option -> a Solidity.tag -> b MicroSolidity.tag -> b MicroSolidity.rhs -> a Solidity.rhs =
 fun tbl cName interf_opt oty uSol_tag -> function
 | MicroSolidity.Expr e -> Solidity.Expr(convert_expr tbl cName interf_opt oty uSol_tag e)
 | MicroSolidity.Call(addr,((Unit,TCons(Int,TNil),"transfer") as m),opt,el) ->
    let trans_addr = convert_expr tbl cName None Address Address addr in
    let trans_opt = (match opt with None -> None | Some e -> Some (convert_expr tbl cName None UInt Int e)) in
    let AnySolMeth(t,tl,name) = convert_meth m in
    let trans_el = convert_expr_list tbl cName tl (TCons(Int,TNil)) el in
    (match eq_tag t oty with 
    | Some Refl -> Call(OnAddressCall(trans_addr),(oty,tl,name),trans_opt,trans_el)
    | _ -> assert false)
 | MicroSolidity.Call(addr,((Unit,TCons(Int,TNil),"send") as m),opt,el) -> 
    let trans_addr = convert_expr tbl cName None Address Address addr in
    let trans_opt = (match opt with None -> None | Some e -> Some (convert_expr tbl cName None UInt Int e)) in
    let AnySolMeth(t,tl,name) = convert_meth m in
    let trans_el = convert_expr_list tbl cName tl (TCons(Int,TNil)) el in
    (match eq_tag t oty with 
    | Some Refl -> Call(OnAddressCall(trans_addr),(oty,tl,name),trans_opt,trans_el)
    | _ -> assert false)
 | MicroSolidity.Call(addr,m,opt,el) -> 
    let trans_addr = convert_expr tbl cName None Interface Address addr in
    let trans_opt = (match opt with None -> None | Some e -> Some (convert_expr tbl cName None UInt Int e)) in
    let AnySolMeth(t,tl,name) = convert_meth m in
    let trans_el = convert_expr_list tbl cName tl (Utils.snd3 m) el in
    (match eq_tag t oty with 
    | Some Refl -> Call(trans_addr,(oty,tl,name),trans_opt,trans_el)
    | _ -> assert false)
let convert_lhs:
 type a. table -> string -> a MicroSolidity.lhs -> (Solidity.interface option * any_Solidity_lhs) =
  fun tbl cName -> function
  | LField(t,n) ->
     (match convert_tag false t with 
     | AnyTag Address -> None,AnyLhs(LVar(Address,n),Address)
     | AnyTag Bool -> None,AnyLhs(LField(Bool,n),Bool)
     | AnyTag Int -> None,AnyLhs(LField(Int,n),Int)
     | _ -> assert false
     )
  | LVar(t,n) ->
     (match convert_tag false t with 
     | AnyTag Bool -> None,AnyLhs(LVar(Bool,n),Bool)
     | AnyTag Int -> None,AnyLhs(LVar(Int,n),Int)
     | AnyTag Address -> None,AnyLhs(LVar(Address,n),Address)
     | _ -> assert false
     )
  | LDiscard -> None,AnyLhs(LDiscard,Unit)

let rec convert_stm:
 type a b. table -> string -> a Solidity.tag -> any_microSolidity_stm -> (a,[`Return]) Solidity.stm = 
  fun tbl cName oty -> function
 | AnyStm(_,Epsilon) -> assert false
 | AnyStm(_,Revert) -> Revert
 | AnyStm(Some Unit, Return) -> (match oty with | Unit -> Return | _ -> assert false)
 | AnyStm(Some t, ReturnRhs r) -> ReturnRhs(convert_rhs tbl cName None oty t r)
 | AnyStm(Some t, Assign(usol_lhs,rhs,s1)) -> 
    let (interf_opt,AnyLhs(lhs,lhs_t)) = convert_lhs tbl cName usol_lhs in
    let rhs = convert_rhs tbl cName interf_opt lhs_t (MicroSolidity.tag_of_lhs usol_lhs) rhs in
    let s = convert_stm tbl cName oty (AnyStm((Some t),s1)) in
    Assign(lhs,rhs,s)
 | AnyStm(Some t,MicroSolidity.IfThenElse(guard,s1,s2,s3)) ->
    let guard = convert_expr tbl cName None Bool Bool guard in
    let trans_s1 = convert_eps_stm tbl cName oty (AnyStm(Some t,s1)) in
    let trans_s2 = convert_eps_stm tbl cName oty (AnyStm(Some t,s2)) in
    let trans_s3 = convert_stm tbl cName oty (AnyStm(Some t,s3)) in
    IfThenElse(guard,trans_s1,trans_s2,trans_s3)
 | _ -> assert false
and convert_eps_stm:
 type a. table -> string -> a Solidity.tag -> any_microSolidity_stm -> (a,[`Epsilon]) Solidity.stm = 
  fun tbl cName oty -> function
  | AnyStm(_,Epsilon) -> Epsilon
  | AnyStm(_,Revert) -> Revert
  | AnyStm(Some Unit, Return) -> (match oty with | Unit -> Return | _ -> assert false)
  | AnyStm(Some t, ReturnRhs r) -> ReturnRhs(convert_rhs tbl cName None oty t r)
  | AnyStm(Some t, Assign(usol_lhs,rhs,s1)) -> 
     let (interf_opt,AnyLhs(lhs,lhs_t)) = convert_lhs tbl cName usol_lhs in
     let rhs = convert_rhs tbl cName interf_opt lhs_t (MicroSolidity.tag_of_lhs usol_lhs) rhs in
     let s = convert_eps_stm tbl cName oty (AnyStm((Some t),s1)) in
     Assign(lhs,rhs,s)
  | AnyStm(Some t,MicroSolidity.IfThenElse(guard,s1,s2,s3)) ->
    let guard = convert_expr tbl cName None Bool Bool guard in
    let trans_s1 = convert_eps_stm tbl cName oty (AnyStm(Some t,s1)) in
    let trans_s2 = convert_eps_stm tbl cName oty (AnyStm(Some t,s2)) in
    let trans_s3 = convert_eps_stm tbl cName oty (AnyStm(Some t,s3)) in
    IfThenElse(guard,trans_s1,trans_s2,trans_s3)
  | _ -> assert false

let trans_meth_iml contractName tbl (AnyMethodDecl(m,Block(vl1,vl2,stm),payable)) =
   let AnySolMeth(tag,tagList,name) = convert_meth m in
   let AnyVarList x = convert_var_list vl1 in
   let AnyVarList y = convert_var_list vl2 in
   let vl = unify_type_tag_var tagList x in
   let stm = convert_stm tbl contractName tag (AnyStm((Some(Utils.fst3 m)),stm)) in
   AnyMethDecl((tag,tagList,name),Block(vl,Public,(if payable then Payable else NoView),y,stm))
let convert_meths_iml contractName ml tbl = List.map (trans_meth_iml contractName tbl) ml

let rec convert_fields fl = 
 List.map (fun (MicroSolidity.AnyField(t,n)) -> let AnyTag tag = convert_tag false t in AnyField((tag,n),None)) fl
(**)
let rec create_interface_fields tbl =
 List.map (fun {contracts;call;meths;trans;ref_to} -> (match trans with Field(t,n) -> AnyField((t,n),ref_to) | _ -> assert false)) tbl
(***********)
(*Fallback Function*)
let convert_fallback: 
 string -> table -> (unit,unit) MicroSolidity.block option -> (unit,unit) Solidity.block option = 
  fun contractName tbl ->
   function
   | None -> None
   | Some Block(VNil,vl,stm) -> 
     let AnyVarList v = convert_var_list vl in
     let stm = convert_stm tbl contractName Unit (AnyStm((Some Unit),stm)) in
     Some (Block(VNil,External,Payable,v,stm))
(***********)
(*_INIT Function*)
let rec get_init_stm: type a. Solidity.fields -> (a,[`Epsilon]) Solidity.stm = 
 function
  | [] -> Assign(LField(Bool,"_initialized"),Expr(Value(true)),Epsilon)
  | AnyField((Interface,name),Some(x))::t -> 
     Assign((LField(Interface,name)),(Expr(AddressToInterface(x,Var((Address,"_"^name))))),(get_init_stm t))
  | _::t -> get_init_stm t
let rec interf_flds_2_var_list: type a. Solidity.fields -> any_Solidity_var_list = 
 function
 | [] -> AnyVarList VNil
 | AnyField((Interface,name),_)::t ->
    let AnyVarList(x) = interf_flds_2_var_list t in
    AnyVarList(VCons(((Address,"_"^name)),x))
 | _::t -> interf_flds_2_var_list t
let rec interf_flds_2_tag_list: Solidity.fields -> any_Solidity_tag_list = 
 function
 | [] -> AnyTagList TNil
 | h::t ->
   let AnyTagList(x) = interf_flds_2_tag_list t in
   AnyTagList (TCons(Address,x))
let create_init_fun: Solidity.fields -> Solidity.any_method_decl = 
 fun fl ->
  let AnyTagList tl = interf_flds_2_tag_list fl in
  let AnyVarList vl = interf_flds_2_var_list fl in
  let vl2 = unify_type_tag_var tl vl in
  let stm = IfThenElse((Not(Field(Bool,"_initialized"))),(get_init_stm fl),(Epsilon),(Return)) in
  AnyMethDecl((Unit,tl,"_init_"),Block(vl2,Public,NoView,VNil,stm))
(***********)
let trans_a_contract: 
 table -> MicroSolidity.a_contract -> (table * Solidity.a_contract) =
  fun tbl (MicroSolidity.AContract (addr,m,fallback,f)) ->
    (*Create/update trans mapping for all methods*)
    let tbl1  = update_table tbl addr m in
    
    let tbl_this_only = List.filter (fun {contracts;call;meths;trans;ref_to} -> 
                                      List.exists (fun s -> String.equal s addr) contracts) tbl1 in

    let tbl_only_f = List.filter (fun {contracts;call;meths;trans;ref_to} -> (match trans with Field(Interface,_) -> true | _ -> false)) tbl_this_only in
    let all_interf_flds = create_interface_fields (List.rev tbl_only_f) in
    let fields_to_init = create_interface_fields (List.rev(List.filter (fun {contracts;call;meths;trans;ref_to} -> match call with Value _ -> true | _ -> false) tbl_only_f)) in
    let init    = create_init_fun fields_to_init in
    
    let meths   = convert_meths_iml addr m tbl_this_only in
    let fields  = convert_fields f in
    let flback  = convert_fallback addr tbl_this_only fallback in

    tbl1,(Solidity.AContract(addr,(Some(default_constructor)),init::meths,flback, (AnyField((Bool,"_initialized"),None))::fields@all_interf_flds))
let rec trans_configuration: 
 table -> Solidity.configuration -> MicroSolidity.configuration -> Solidity.configuration =
  fun tbl (il,cl) -> function
  | [] -> (create_interface_decl (List.filter (fun x -> (match x.ref_to with Some y -> true | None -> false)) tbl)),List.rev cl
  | c::tl -> 
    let (tbl2,trans_c) = trans_a_contract tbl c in
    trans_configuration tbl2 ([],trans_c::cl) tl 