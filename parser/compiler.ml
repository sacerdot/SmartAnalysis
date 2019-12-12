open Grammar
open SmartCalculus
open ParserCombinator

let nl = "\n"
let symb_array = "symbol"
let balance = "balance"
let msg_value = "value"
let initialize = "initialize"
let sol_filename = "demo/out.sol"

type 'a typename = 
 | Int : int typename 
 | String : string typename
 | Bool : bool typename
 | Interf : interface_id typename
 | Address : addr typename
and addr = AddrInt of interface_id
and interface_id = InterfaceId of string
and storage = Storage | Memory | Calldata  
and 'a var = 'a typename * string 
and 'a expression =
 | Var : 'a var -> 'a expression 
 | Value : 'a -> 'a expression
 | MsgValue : int expression
 | Balance : int expression
 | This : interface_id expression
 | CastInterf : interface_id * addr expression -> interface_id expression
 | Addr : interface_id expression -> addr expression
 | Plus : int expression * int expression -> int expression
 | Minus : int expression * int expression -> int expression
 | Mult : int expression * int expression -> int expression
 | Symbol : string -> int expression
 | Geq : int expression * int expression -> bool expression
 | Gt : int expression * int expression -> bool expression
 | Eq : 'a typename * 'a expression * 'a expression -> bool expression
 | And : bool expression * bool expression -> bool expression
 | Or : bool expression * bool expression -> bool expression
 | Not : bool expression -> bool expression
 | CondExpr : bool expression * 'a expression * 'a expression -> 'a expression
 | Call : interface_id expression * ('a, 'b) funct * 'a expression_list
 * (int expression) option-> 'b expression
and _ expression_list =
   ExprNil : unit expression_list
 | ExprCons : ('a typename * 'a expression) * 'b expression_list -> ('a * 'b) expression_list
and _ param_list = PNil: unit param_list | PCons: ('a var * storage option) * 'b param_list -> ('a * 'b) param_list  
and view = View | Pure | Payable
and visibility = External | Public | Internal | Private
and ('a, 'b) funct = string * 'a param_list * ('b typename * storage option)
option * view list * visibility list
and meth = Funct : (('a, 'b) funct) -> meth
and interface = Interface : (interface_id * meth list) ->  interface
and declaration = Declaration : 'a var * ('a expression option) -> declaration
and statement = 
 | Empty
 | IfElse : bool expression * statement * statement -> statement
 | Assignment : 'a var * 'a expression -> statement
 | Sequence : statement * statement -> statement
(*name,param_list,visibility,view,outtype,stm,return*) 
type any_funct=  Function: ('a, 'b) funct * statement * ('b expression option)-> any_funct
type field = Field : ('a var * ('a option) * bool) -> field
type symbol = Symbol : string -> symbol
type table = (field list *  interface list * symbol list)
type contract_ast = Contract of string * (declaration list) * (any_funct list) *
int
type ('a,'b) trans = table -> 'a -> 'b *table 
type ast = contract_ast list
type ('a, 'b) mapping = Mapping of 'a expression * 'b expression 
exception CompilationFail

(*AnyType*)
type any_typename = Typename : 'a typename -> any_typename
type any_expression = Expr : 'a typename * 'a expression -> any_expression
type any_expression_list = ExprList : 'a expression_list -> any_expression_list
type any_param_list = Parameters: 'a param_list -> any_param_list

(*Utils*)
let ident x = x
let fst (f,_,_) = f
let scd (_,s,_) = s
let thd (_,_,t) = t

let eq_type : type a b. a typename -> b typename -> (a,b) eq option = fun t1 t2 ->
 match t1,t2 with
  | Int, Int -> Some Refl
  | Bool, Bool -> Some Refl
  | String, String -> Some Refl
  | Interf, Interf -> Some Refl
  | Address, Address -> Some Refl
  | _,_ -> None

let is_same_type: type a b. a typename -> b typename -> bool = fun t1 t2 ->
 match eq_type t1 t2 with
  | Some Refl -> true
  | None -> false

let rec is_same_params: type a b. a param_list -> b param_list -> bool = fun p1 p2 -> 
 match p1,p2 with
  | PNil,PNil -> true
  | PCons(((t1,name1),_),tail1),PCons(((t2,name2),_),tail2) ->
          (is_same_type t1 t2) && (is_same_params tail1 tail2)
  | _,_ -> false

let rec match_exprlist_with_params: type a b. a param_list -> b expression_list ->
(a,b) eq option = fun pl el ->
  match (pl,el) with
   | PNil,ExprNil -> Some Refl
   | PCons(((t1,_),_),ptail),ExprCons((t2,_),etail) -> 
    (match eq_type t1 t2 with 
    | Some Refl ->
     (match match_exprlist_with_params ptail etail with
     | Some Refl -> Some Refl
     | None -> None)
    | None -> None)
   | _,_ -> None

let rec is_matching_meths =
 fun meth1 meth2 -> match (meth1,meth2) with
 |Funct(name1,params1,opt1,view1,vis1),Funct(name2,params2,opt2,view2,vis2) -> 
     name1=name2 && is_same_params params1 params2 && view1 = view2 && 
    (match opt1,opt2 with
    | Some (out1,stg1), Some (out2,stg2) -> is_same_type out1 out2 && stg1=stg2 
    | None,None -> true
    | _,_ -> false)

let pp_opt f = 
 function
 | Some o -> (f o) 
 | None -> ""

let comp : type a b c. (a -> b) -> (b -> c) -> a -> c = fun f g x -> g (f x)

let apply_to_first = fun f (fst,scd,thd) -> (f fst),scd,thd

let apply_to_second = fun f (fst,scd,thd) -> fst,(f scd),thd

let apply_to_third = fun f (fst,scd,thd) -> fst,scd,(f thd)

(*Symbol*)
let rec is_symbol_in_table = 
 fun (_,_,tbl) s -> 
 let rec aux stbl = match stbl with
  | [] -> false
  | Symbol(name)::_  when name = s -> true
  | _::tl -> aux tl
 in aux tbl

let rec add_symbol =
 fun tbl s -> 
  if (is_symbol_in_table tbl s) then tbl 
  else apply_to_third (fun sl -> [Symbol s]@sl) tbl

let rec get_symbols tbl =
  let rec aux =
   function
    | [] -> []
    | Symbol s :: tl -> [s]@aux tl 
  in aux (thd tbl)

(*Type Table*)
let rec get_field_list = fun (tbl,_,_) -> tbl

let rec get_interface_list = fun (_,tbl,_) -> tbl

let rec is_var_in_table tbl (t,name) =
 let rec aux ftbl =
  match ftbl with
   | [] -> false 
   | Field ((tfield, namefield),_,_) ::_ when namefield=name -> 
           is_same_type t tfield
   | _::tl -> aux tl
 in aux (fst tbl)

let get_fresh_interface : interface list -> interface = 
 fun il -> Interface (InterfaceId ("Interf" ^ string_of_int (List.length il)), []) 

let add_interface i = apply_to_second (List.append [i])

let add_field_in_table =
 fun (t,name) value islocal tbl ->
  if (is_var_in_table tbl (t,name)) then tbl
  else apply_to_first 
   (fun fl -> 
       if List.exists (fun (Field((_,nfield),_,_)) -> name = nfield) fl then 
        raise CompilationFail 
       else [Field((t,name),value,islocal)]@fl) tbl 

let add_funct_to_interface i meth = match i with
 Interface(InterfaceId(name), functs) ->
     if List.exists (fun f -> is_matching_meths f meth) functs then
         Interface(InterfaceId(name),functs)
     else
         Interface(InterfaceId(name),[meth]@functs)

let get_field t n =
   List.find_opt (fun (Field ((typ,name),_,_)) -> (is_same_type typ t) && name=n) 

let get_interface n =
   List.find (fun (Interface ((InterfaceId name),meths)) -> name=n) 

let get_contr_interface conname tbl =
 match get_field Interf conname (fst tbl) with
  | Some Field((Interf,_),Some (InterfaceId int_name),_) -> 
    Some (get_interface int_name (scd tbl))
  | _ -> None

let get_addr_interface conname tbl =
 match get_field Address conname (get_field_list tbl) with
  | Some Field ((Address,_),Some (AddrInt (InterfaceId int_name)),_) -> 
    Some (get_interface int_name (get_interface_list tbl))
  | _ -> None

let get_interface_id = function Interface(id,_) -> id

let add_contract_to_table name tbl =
  let i = get_fresh_interface (scd tbl) in
  add_interface i ((add_field_in_table (Interf,name) (Some(get_interface_id i)) false) tbl)

let add_address_to_table name tbl islocal =
  let i = get_fresh_interface (scd tbl) in
  add_interface i ((add_field_in_table (Address,name)
  (Some(AddrInt(get_interface_id i))) islocal) tbl)

let add_funct_to_contr_interf conname f tbl =
 apply_to_second
 (List.map (fun i ->
   match get_contr_interface conname tbl with 
    Some c_int -> if (i = c_int) then add_funct_to_interface c_int f else i
   | None -> i)) tbl

let add_funct_to_addr_interf conname f tbl =
 apply_to_second
 (List.map (fun i ->
   match get_addr_interface conname tbl with 
    Some c_int -> if (i = c_int) then add_funct_to_interface c_int f else i
   | None -> i)) tbl

let remove_local_var = apply_to_first (List.filter (fun (Field(_,_,islocal)) -> not islocal))

let rec pp_typename : type a. a typename -> string =
 function 
  | Int -> "int"
  | Bool -> "bool"
  | String -> "string"
  | Interf -> "interface"
  | Address -> "address"

let rec pp_table_fields =
 function 
  | (Field ((t,name),_,_))::tl -> "field: "^ pp_typename t ^ " " ^ name ^ nl ^ pp_table_fields tl
  | [] -> ""

let rec pp_table_function =
 function 
  | (Funct (name,_,_,_,_))::tl -> "function: " ^ name ^ " " ^ nl ^ pp_table_function tl
  | [] -> ""

let pp_interface_short =
  fun (Interface ((InterfaceId name),flist)) ->  "interface: " ^ name  ^ nl ^ pp_table_function flist ^ nl 

let rec pp_table_interface =
 function 
  | inter::tl -> pp_interface_short inter ^ pp_table_interface tl
  | [] -> ""

let rec pp_table_symbol  = 
 function
  | (Symbol name)::tl -> "symbol: " ^ name ^ nl ^ pp_table_symbol tl
  | [] -> ""

let pp_table = fun (f, i, s) ->
  pp_table_fields f ^ nl ^ pp_table_interface i  ^ nl ^ pp_table_symbol s

(*translating*)
let get_typename  : type a b. a typename -> b tag -> any_typename = 
 fun typ tag -> 
  match tag with
  | Int -> Typename Int
  | Bool -> Typename Bool
  | String -> Typename String
  | ContractAddress -> Typename typ
  | _ -> raise CompilationFail

let trans_unary =
  fun op trans tbl e -> (fun (expr, ntbl) -> (op expr),ntbl) (trans tbl e)

let trans_double = 
  fun op trans tbl e1 e2 -> 
   (fun (op_unary, ntbl) -> trans_unary op_unary trans ntbl e2) (trans_unary op trans tbl e1)

let check_type : type a. a typename -> any_expression -> a expression = 
    fun t (Expr(typename, e)) -> 
     match eq_type t typename with
      Some Refl -> e 
     | None -> raise CompilationFail

let apply_to_trans : ('a, 'b) trans -> ('b -> 'c) -> ('a, 'c) trans =
    fun trans f tbl s -> 
        let (ast,ntbl) = trans tbl s in (f ast),ntbl

let comp_trans : ('a, 'b) trans -> ('b, 'c) trans -> ('a, 'c) trans =
    fun trans1 trans2 tbl s ->
        let (ast, ntbl) = trans1 tbl s in trans2 ntbl ast

let trans_opt trans tbl = 
 function
  | None -> None,tbl
  | Some s -> apply_to_trans trans (fun x -> Some x) tbl s

let rec const_expression =
 function
  | Numeric n -> SmartCalculus.Value n
  | _ -> raise CompilationFail

let rec base_expression : type a b. a tag ->  (a expr, any_expression) trans   = 
 fun t tbl expr -> 
  let get_new_int name = Expr(Interf,(Var(Interf,name))),(match get_contr_interface name tbl with
     | Some i -> tbl
     | None ->  add_contract_to_table name tbl) in
  let get_new_add name = 
    match get_addr_interface name tbl with
     | Some i -> Expr(Address,(Var(Address,name))),tbl
     | None -> get_new_int name
  in
  (match t,expr with
   | Int,Var(Int,v) when v = msg_value -> Expr(Int,MsgValue),tbl
   | Int,Var(Int,v) when v = balance-> Expr(Int,Balance),tbl
   | ContractAddress,Field(ContractAddress,name) -> get_new_int name
   | ContractAddress,Var(ContractAddress,name) -> get_new_add name
   | _,(Var(tag,e)) | _,(Field(tag,e))-> (match get_typename Address tag with Typename t -> 
     Expr(t,Var(t,e)),(add_field_in_table (t,e) None false tbl))
   | String, Value s -> Expr(String,(Value s)),tbl
   | Int, Value n -> Expr(Int,(Value n)),tbl
   | Bool, Value b -> Expr(Bool,(Value b)),tbl
   | _,_ -> raise CompilationFail)

and int_expression :(int expr, int expression) trans =
 fun tbl -> 
  function 
   | Plus ((Minus e1),(e2)) -> trans_double (fun e1 e2 -> Minus(e1,e2)) int_expression tbl e2 e1
   | Plus ((e1),(Minus e2)) -> trans_double (fun e1 e2 -> Minus(e1,e2)) int_expression tbl e1 e2
   | Plus (e1, e2) ->  trans_double (fun e1 e2 -> Plus(e1,e2)) int_expression tbl e1 e2
   | Mult (c, e) -> trans_double (fun e1 e2 -> Mult(e1,e2)) int_expression tbl (const_expression c) e
   | Minus (Value v) -> (Value ((-1) * v)),tbl
   | Minus e -> 
     trans_double (fun e1 e2 -> Mult(e1,e2)) int_expression tbl (const_expression (Numeric (-1))) e
   | Max (e1,e2) -> let bexpr,ntbl = bool_expression tbl (Gt(e1,e2)) in
     trans_double (fun v1 v2 -> CondExpr(bexpr,v1,v2)) int_expression tbl e1 e2
   | Symbol s -> (Symbol s),(add_symbol tbl s)
   | e -> apply_to_trans (base_expression Int) (check_type Int) tbl e

and bool_expression :  (bool SmartCalculus.expr, bool expression) trans =
 fun tbl ->
  function
   | Geq (e1, e2) -> 
     trans_double (fun e1 e2 -> Geq(e1,e2)) int_expression tbl e1 e2
   | Gt (e1, e2) -> 
     trans_double (fun e1 e2 -> Gt(e1,e2)) int_expression tbl e1 e2
   | Eq (tag, e1, e2) -> 
    (match get_typename Address tag with Typename t ->
        trans_double 
        (fun anye1 anye2 -> 
          match anye1,anye2 with 
          | Expr(t1,e1),Expr(t2,e2) -> 
            match eq_type t1 t2 with 
             |Some Refl -> Eq(t1,e1,e2) 
             | _ -> raise CompilationFail)
        (trans_expression tag) tbl e1 e2)
   | And (e1, e2) -> trans_double (fun e1 e2 -> And(e1,e2)) bool_expression tbl e1 e2
   | Or (e1, e2) -> trans_double (fun e1 e2 -> Or(e1,e2)) bool_expression tbl e1 e2
   | Not e -> trans_unary (fun e -> Not(e)) bool_expression tbl e
   | e -> apply_to_trans (base_expression Bool) (check_type Bool) tbl e

and contract_expression  = fun tbl -> 
 function
  | SmartCalculus.This -> Expr(Interf,This),tbl
  | e -> (base_expression ContractAddress) tbl e

and trans_expression: type a. a tag -> table -> a expr -> any_expression * table = 
 function
  | Int -> apply_to_trans int_expression (fun e -> Expr(Int,e))  
  | Bool -> apply_to_trans bool_expression (fun e -> Expr(Bool,e))
  | ContractAddress -> contract_expression 
  | t -> base_expression t 

let trans_decl : (assign, declaration) trans = fun tbl -> 
 function           
 Let ((tag,name),v) -> match get_typename Interf tag with Typename t -> 
 (fun (value,ntbl) -> 
   let v = match value with 
    | Value v -> Some v 
    | _ -> None in
  (Declaration ((t,name),Some value), add_field_in_table (t,name) v false ntbl))
 (match t with
  | Interf -> 
    let Interface(int_id,meths) = get_fresh_interface (scd tbl) in
    (Value(int_id)),(add_interface (Interface(int_id,meths)) tbl)
  | _ -> 
   (fun (anye,ntbl) -> (check_type t anye),ntbl)(trans_expression tag tbl (Value v)))

let rec trans_expression_list : type a. a tag_list -> (a expr_list, any_expression_list) trans=
 fun tlist tbl elist ->
  match tlist,elist with 
   | TNil,ENil -> (ExprList ExprNil),tbl
   | TCons(t,ttail),ECons(e,etail) -> 
    let (Expr(typename,expr),ntbl1) = trans_expression t tbl e in
    let (ExprList elist,ntbl2) = trans_expression_list ttail ntbl1 etail in
    (match typename with 
    | Interf -> ExprList (ExprCons ((Address, (Addr expr)),elist))
    | _ -> ExprList (ExprCons ((typename,expr), elist))),ntbl2

let get_storage: type a. a typename -> storage option =
 function
  | String -> Some Memory
  | _ ->  None

let rec get_param_list : type a. a var_list -> any_param_list  = 
 function       
  | VNil -> Parameters PNil
  | VCons((tagvar,var),vartail) ->
   (match (get_typename Address tagvar),(get_param_list vartail) with 
   | Typename t,Parameters (plist) ->
   Parameters (PCons(((t,var), (get_storage t)),plist)))

let get_contract_name =
 function 
  | Var(Interf,name) -> Some name
  | This -> Some "this"
  |  _ -> None 

let rec get_unnamed_varlist : type a. a tag_list -> a var_list =
 function
  | TNil -> VNil
  | TCons (tag, tl) -> VCons((tag,""), get_unnamed_varlist tl)

let get_unnamed_param_list l = get_param_list (get_unnamed_varlist l)

let rec set_calldata_params =
 function
  | Parameters (PCons ((var,Some s),ptl)) ->
    (match set_calldata_params (Parameters ptl) with
    | Parameters p -> Parameters (PCons((var,Some Calldata),p)))
  | pl -> pl

let trans_meth : type a b. (a, b) SmartCalculus.meth -> visibility list-> meth =
 fun (tagret, taglist, name) vis ->
  match get_typename Address tagret with Typename t ->
  let outtype = t,(get_storage t) in 
  let adjust_par = 
   if List.exists (fun v -> v = External) vis then set_calldata_params 
   else ident in 
  match adjust_par (get_unnamed_param_list taglist) with Parameters params -> 
  Funct(name,params,(Some outtype),[Payable],vis)

let rec trans_rhs : 'a tag  -> ('a rhs, any_expression) trans =
 fun tag tbl  -> 
  let rec aux value tbl = 
   function 
   | SmartCalculus.Expr e -> trans_expression tag tbl e 
   | Call (opt, (funtag, tags, name), elist) -> 
    let (con,ntbl1) = 
     (apply_to_trans (trans_opt contract_expression) 
     (function 
      | None -> This 
      | Some Expr(_,Var(Address,name)) -> 
       (match get_addr_interface name tbl with
       | Some interf -> CastInterf (get_interface_id interf,Var(Address,name))
       | None -> Var(Interf,name))
      | Some Expr(Interf,s) -> s
      | _ -> raise Fail)) tbl opt in
    let (ExprList(expr),ntbl2) = trans_expression_list tags ntbl1 elist in
    (let Funct m = trans_meth (funtag,tags,name) [External]in 
    match m with 
     | (n,par,Some(t,stg),view,vis) ->
      (match match_exprlist_with_params par expr with
      Some Refl -> (Expr(t,Call(con,m,expr,value)),
       ((match con with 
        | Var(Interf,conname) -> add_funct_to_contr_interf conname (Funct m) 
        | CastInterf(_,Var(Address,conname)) -> add_funct_to_addr_interf conname (Funct m) 
        | _ -> ident) ntbl2))
      | None -> raise CompilationFail)
     | _ -> raise CompilationFail)
   | CallWithValue (opt, (funtag, tags, name), elist, vexpr) ->
    let v,ntbl = trans_expression Int tbl vexpr in
    aux (Some (check_type Int v)) ntbl (Call(opt,(funtag,tags,name),elist))
   in aux None tbl 

let rec trans_stm : (stm, statement) trans = fun tbl -> 
 function 
  | Assign((tag, name),rhs) ->  
   (match get_typename Interf tag with Typename t ->
       let aux tbl =
        let (Expr(typ,expr), ntbl) = 
         trans_rhs tag tbl rhs in
         Assignment ((t,name),
        (match t,typ with
         | Interf,Interf -> 
           (CastInterf (get_interface_id 
            (match get_contr_interface name ntbl with
              Some i -> i 
            | None -> raise CompilationFail),(Addr expr)))
         | Interf,Address -> 
           (CastInterf (get_interface_id 
            (match get_contr_interface name ntbl with
              Some i -> i 
            | None -> raise CompilationFail),expr))
         | Address,Interf -> Addr expr
         | _,_ -> 
           match eq_type t typ with Some Refl -> expr| None -> raise
          CompilationFail)),ntbl in
   if (is_var_in_table tbl (t,name)) then aux tbl
   else 
       (fun (_,ntbl) -> aux ntbl)
       (trans_decl tbl (Let((tag,name), get_null_value tag)))
   ) 
  | IfThenElse(expression,stm1,stm2) -> 
          let (expr,ntbl) = bool_expression tbl expression in
          trans_double (fun stm1 stm2 -> IfElse (expr, stm1, stm2))
          trans_stm  ntbl stm1 stm2
  | Comp (stm1,stm2) -> trans_double (fun stm1 stm2 -> Sequence(stm1,stm2))
  trans_stm tbl stm1 stm2
  | _ -> raise CompilationFail

let rec trans_stmlist : (stm list, statement) trans = 
 fun tbl stml ->
  match stml with
  | h::[] -> trans_stm tbl h
  | h::tl ->
   let (stm,ntbl) = trans_stm  tbl h in 
   trans_unary (fun v -> Sequence(stm,v)) 
   trans_stmlist ntbl tl
  | [] -> Empty,tbl

let rec add_params_in_tbl : type a. meth -> a param_list -> table -> table =
 fun m par_list tbl -> match par_list with 
  | PNil -> tbl
  | PCons(((t,name),_),tail) -> 
    if (is_same_type t Address) then
     let ntbl = add_address_to_table name tbl true in
     add_params_in_tbl m tail ntbl
    else 
     (comp (add_params_in_tbl m tail) (add_field_in_table
     (t,name) None true)) tbl

let trans_funct: (any_method_decl, any_funct) trans = 
 fun tbl meth ->
  match meth with 
  AnyMethodDecl((tagret, taglist, name),(param_list, stmlist, retexpr)) -> 
   let m = trans_meth (tagret, taglist, name) [Public] in
   match m with Funct (meth_name,p,outtype,payable,public) ->
   let (Parameters params) = (get_param_list param_list) in
   let tbl_params = add_params_in_tbl m params tbl in
   let (stm,ntbl1) = trans_stmlist tbl_params stmlist in
   let (Expr(typeret,return),ntbl2) = trans_expression tagret ntbl1 retexpr in
   match eq_type typeret ((fun x -> match x with Some (t,_) -> t | _ -> raise CompilationFail) outtype) with
   Some Refl -> 
    (Function ((name,params,outtype,payable,public),stm,Some return)),(remove_local_var ntbl2)
   | None -> raise CompilationFail

let rec assign_symbol : string list -> int -> statement =
 fun l n -> match l with
  | [] -> Empty
  | h::tl -> Sequence((Assignment((Int, symb_array ^ "['" ^ h ^ "']"), Value(n)),
  assign_symbol tl (n + 1)))

let rec trans_list : type a b. (a,b) trans -> a list ->
 table -> b list -> b list * table =
 fun f l1 tbl l2 ->
  match l1 with 
  | [] -> l2,tbl
  | h::tl -> 
   let (nel,ntbl) = f tbl h in 
   trans_list f tl ntbl (l2@[nel])

let rec add_actorlist_to_table tbl = 
 function
  | [] -> tbl
  | ((SmartCalculus.Contract name),_,_) :: tl ->
   add_actorlist_to_table (add_contract_to_table name tbl) tl

let rec add_decl_list tbl : a_contract list -> declaration list * table =
 function
  | [] -> [],tbl
  | (SmartCalculus.Contract(name),_,_) :: tl -> 
    let (decl1,ntbl1) = trans_decl tbl
    (Let((ContractAddress,name),(get_null_value ContractAddress))) in
    let (decl2,ntbl2) = add_decl_list ntbl1 tl in
    ([decl1]@decl2),ntbl2

let uniq_cons x xs = 
 match x with Declaration ((_,name1),_) -> 
 if List.exists (fun (Declaration((_,name2),_)) -> name1=name2) xs then xs else x :: xs

let remove_duplicates xs = List.fold_right uniq_cons xs []

let extract_balance dl = 
 let rec aux (bl:int) acc = 
  function 
  | [] -> bl,acc
  | Declaration ((Int,var),(Some (Value v))) :: tl when var = balance ->
    aux v acc tl
  | h::tl -> aux bl ([h]@acc) tl
  in aux 0 [] dl

let rec get_decl_list =
 function 
  | [] -> []
  | Field((t,name),value,_)::tl ->
    match value with 
    | Some v -> [Declaration((t,name), Some(Value v))]@(get_decl_list tl)
    | None -> [Declaration((t,name), None)]@(get_decl_list tl)

let rec get_contr_param_list =
 function
  | [] -> Parameters PNil
  | (SmartCalculus.Contract name,_,_)::tl -> 
    let (Parameters ptail) = get_contr_param_list tl in
    Parameters (PCons(((Address,"_" ^ name),None),ptail)) 

let get_other_contrlist_assign tbl cl =
  let rec aux = 
   function
    | [] -> Assignment((Bool,initialize),(Value true))
    | (SmartCalculus.Contract name,_,_)::tl -> 
      let interface = match (get_contr_interface name tbl) with Some i -> i | None
      -> raise CompilationFail in
      Sequence (Assignment
      ((Interf,name),(CastInterf((get_interface_id interface),Var(Address,"_" ^
      name)))),aux tl)
  in IfElse (Not(Var(Bool,initialize)),(aux cl),Empty)

let get_init_funct : table -> a_contract list -> any_funct = fun tbl cl ->
  match (get_contr_param_list cl) with 
  Parameters pms -> 
   Function(("init",pms,None,[],[Public]),(get_other_contrlist_assign tbl cl),None)

let decl_initialize = Declaration((Bool,initialize),Some (Value false))

let trans_contract : a_contract list -> (a_contract, contract_ast) trans =
 fun others tbl (add, meths, fields) -> match add with
  | Contract name -> 
   let (decl_others, ntbl0) = add_decl_list tbl others in
   let (decl_expl, ntbl1) = trans_list trans_decl fields ntbl0 [] in 
   let (flist, ntbl2) = trans_list trans_funct meths ntbl1 [] in 
   let (bal,decls) = extract_balance (remove_duplicates ([decl_initialize]@(get_decl_list (fst
   ntbl2))@(decl_others@decl_expl))) in
   let constructor = 
    Function (("constructor",PNil,None,[Payable],[Public]),(assign_symbol 
    (get_symbols ntbl2) 0),None) in
   (Contract(name, decls, [constructor]@[get_init_funct ntbl2 others]@flist, bal)), ntbl2

let rec trans_contract_list tbl l = 
 function 
  | [] -> [],tbl
  | h::tl -> 
   let (contr, (fl,il,sl)) = 
    trans_contract (List.filter (fun c -> c<>h) l)  tbl h in
   let (contr_list, ntbl2) = trans_contract_list ([],il,[]) l tl in
   ([contr]@contr_list, ntbl2)
        
let rec trans_configuration =
 function
  {contracts = cl; _} -> 
    (trans_contract_list ([],[],[]) cl cl)

let pp_value : type a. a typename -> a -> string =
 fun t v ->
 match t,v with 
 | String,s -> "'" ^ s ^ "'"
 | Int,n -> string_of_int n
 | Bool,b -> string_of_bool b
 | Interf,(InterfaceId name) -> name 
 | Address,AddrInt(InterfaceId name) -> name 

let pp_cast_type t s = pp_typename t ^ "(" ^ s ^ ")"
let cast_interf =
    function Interface(InterfaceId name,_) -> "(" ^ name ^ ")" 
let rec pp_expression : type a. table -> a typename ->
 a expression -> string =
 fun  tbl t expr->
  let pp_expr_info tag e = (pp_expression tbl tag e) in
  match t,expr with 
  | Int,Balance ->  pp_cast_type Int ((pp_expr_info Interf This) ^
      ".balance" )
          | Int,MsgValue -> pp_cast_type Int "msg.value"
      | Interf,CastInterf ((InterfaceId name),expr) -> name ^ "(" ^ pp_expr_info Address expr ^ ")"
  | t,Var(_, name) -> name
  | Interf,This -> "this"
  | Address,Addr (expr) -> "address(" ^ pp_expr_info Interf expr ^ ")"
  | t,Value (v) -> pp_value t v
  | Int,(Plus(e1,e2)) -> "(" ^ pp_expr_info Int e1 ^ " + " ^ pp_expr_info Int e2 ^ ")"
  | Int,(Minus(e1,e2)) -> "(" ^ pp_expr_info Int e1 ^ " - " ^ pp_expr_info Int e2 ^ ")"
  | _,(Mult(e1,e2))  -> "(" ^ pp_expr_info Int e1 ^ " * " ^ pp_expr_info Int e2 ^ ")"
  | t,(CondExpr(b,e1,e2)) -> "(" ^ pp_expr_info Bool b ^ " ? " ^ pp_expr_info
  t e1 ^ " : " ^ pp_expr_info t e2 ^ ")"
  | _,(Geq(e1,e2)) -> "(" ^ pp_expr_info Int e1 ^ " >= " ^ pp_expr_info Int e2 ^ ")"
  | _,(Gt(e1,e2)) -> "(" ^ pp_expr_info Int e1 ^ " > " ^ pp_expr_info Int e2 ^ ")"
  | _,(Eq(t,e1,e2)) -> "(" ^ pp_expr_info t e1 ^ " == " ^ pp_expr_info t e2 ^ ")"
  | _,(And(e1,e2)) -> "(" ^ pp_expr_info Bool e1 ^ " && " ^ pp_expr_info Bool e2 ^ ")"
  | _,(Or(e1,e2)) -> "(" ^ pp_expr_info Bool e1 ^ " || " ^ pp_expr_info Bool e2 ^ ")"
  | _,(Not e) -> "(!" ^ pp_expr_info Bool e ^ ")" 
  | _,(Call(c,(s,_,_,_,_),exprl,value)) ->  
              pp_expr_info Interf c ^ "."  ^ s ^ pp_opt (fun e -> ".value(uint(" ^ pp_expr_info Int e ^ "))")
  value ^ "(" ^ (String.concat ", " (string_list_of_expression tbl exprl)) ^ ")" 
  | _,(Symbol s) -> symb_array ^ "['" ^ s ^ "']"
 and string_list_of_expression : type a. table  -> a expression_list -> string list =
 fun tbl el -> match el with
  | ExprNil -> []
  | ExprCons ((t,e), tl) -> [(pp_expression tbl t e)]@(string_list_of_expression tbl tl) 
      
let pp_declaration tbl = function
 Declaration ((t,name),e) -> 
  let equals = pp_opt (fun expr -> " = " ^ pp_expression tbl t expr) e in
  (match t,e with
  | Interf,(Some (Value (InterfaceId id))) -> id ^ " " ^ name
  | _,_ -> pp_typename t ^ " " ^ name ^ equals) ^ ";"


let rec pp_statement  = 
 fun tbl stm -> 
  let pp_stm_info = pp_statement tbl in
  match stm with
  | IfElse (b, stm1, stm2) -> "if " ^ pp_expression tbl Bool b ^ "{"  ^ nl ^
  (pp_stm_info stm1) ^ nl ^ "}" ^(match stm2 with Empty -> "" | _ -> nl ^ "else {" 
  ^ nl ^ pp_stm_info stm2 ^ nl ^ "}")
  | Assignment ((t,name), e) -> pp_expression tbl t (Var(t,name)) ^ " = " ^ pp_expression tbl t e ^ ";"
  | Sequence (stm1, stm2) -> pp_stm_info stm1 ^ nl ^ pp_stm_info stm2
  | _ -> ""

let pp_storage =
 function
  | Storage -> "storage "
  | Memory -> "memory "
  | Calldata -> "calldata "

let rec string_list_of_params : type a. a param_list -> string list=
 function
  | PNil -> []
  | PCons(((t, name), opt),tl) -> [pp_typename t ^ " " ^ (pp_opt pp_storage opt) ^ name]@(string_list_of_params tl)

let rec pp_params : type a. a param_list -> string =
 fun l -> "(" ^ (String.concat ", " (string_list_of_params l)) ^ ")"

let pp_view =
 function
  | View -> "view "
  | Pure -> "pure "
  | Payable -> "payable "
     
let pp_visibility =
 function 
  | External -> "external "
  | Public -> "public "
  | Internal -> "internal "
  | Private -> "private "

let declare_symbols =
 "mapping (" ^ pp_typename String ^ " => " ^ pp_typename Int ^ ") " ^ symb_array ^ ";"

let rec pp_meth =
 function 
 Funct (name, params,out, view, vis) ->
  (if (name = "constructor") then name else "function " ^ name) ^ pp_params params 
  ^ " " ^ (String.concat " " (List.map pp_view view)) ^ (String.concat " " (List.map pp_visibility vis)) ^  
  (match out with 
  | Some (outtype,storage) -> 
    "returns (" ^ pp_typename outtype ^ " " ^ (pp_opt pp_storage storage) ^ ")"
  | None -> "") 
let rec pp_funct =
 fun tbl f -> 
 match f with 
  Function (m , stm, return) ->
   let meth = (Funct m) in 
   pp_meth  meth ^ "{" ^ nl ^ pp_statement tbl stm ^ nl ^
   (match return,m with Some r,(_,_,Some(outtype,_),_,_) ->
   "return " ^ pp_expression tbl outtype r ^ ";" ^ nl | _ -> "")  ^ "}" 

let rec pp_contract =
 fun tbl c -> match c with
 Contract (name, fields, meths,_) ->  "contract " ^ name ^ " {" ^ nl ^ (declare_symbols ^ nl) ^
 (String.concat nl (List.map (pp_declaration tbl)fields)) ^ nl ^
  (String.concat nl (List.map (pp_funct tbl) meths)) ^ nl ^ "}"

let pp_interface : interface -> string = 
 function 
  | Interface ((InterfaceId name),funct_list) -> 
   "interface " ^ name ^ "{" ^ nl ^ String.concat nl
   (List.map (fun m -> pp_meth m ^ ";") funct_list) ^ nl ^ "}"

let rec pp_ast : ast * table -> string =
 fun (cl,(fl,il,ml)) -> 
  "pragma solidity 0.4.25;" ^ nl ^ 
  String.concat nl  (List.map pp_interface  (List.rev il)) ^ nl ^
  String.concat nl (List.map (pp_contract (fl,il,ml)) cl)
;;

let sol_ast = trans_configuration (Grammar.conf);;
let outstr = (pp_ast sol_ast);;
print_string outstr;;
let out_channel = open_out sol_filename;;
Printf.fprintf out_channel "%s" outstr;
