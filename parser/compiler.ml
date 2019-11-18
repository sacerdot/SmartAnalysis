open Grammar
open SmartCalculus
open ParserCombinator

let nl = "\n"
let symb_array = "symbol"
let this_str = "this"

type 'a typename = 
    | Int : int typename 
    | String : string typename
    | Bool : bool typename
    | ContractAddress : (contract address) typename
type storage = Storage | Memory | Calldata  
type 'a var = 'a typename * string 
type 'a expression =
    | Var : 'a var -> 'a expression 
    | Value : 'a -> 'a expression
    | MsgValue : int expression
    | Balance : int expression
    | This : (contract address) expression
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
    | Call : (contract address) expression * string * 'a expression_list
    * (int expression) option-> 'b expression
and _ expression_list =
      ExprNil : unit expression_list
    | ExprCons : ('a typename * 'a expression) * 'b expression_list -> ('a * 'b) expression_list
and _ param_list = PNil: unit param_list | PCons: ('a var * storage option) * 'b param_list -> ('a * 'b) param_list  
type view = View | Pure | Payable
type visibility = External | Public | Internal | Private
and ('a, 'b) funct = string * 'a param_list * ('b typename * storage option) *
view list * visibility list
type declaration = Declaration : 'a var * ('a expression option) -> declaration
type statement = 
    | Empty
    | IfElse : bool expression * statement * statement -> statement
    | Assignment : 'a var * 'a expression -> statement
    | Sequence : statement * statement -> statement
(*name,param_list,visibility,view,outtype,stm,return*) 
type any_funct=  Function: ('a, 'b) funct * statement * 'b expression -> any_funct
type meth = Funct : (('a, 'b) funct) -> meth
type interface = Interface : (string * meth list * bool)
->  interface
type field = Field : ('a var * bool) -> field
type contr_info = Contr : (string * string option * meth option * interface) ->
    contr_info
type symbol = Symbol : string -> symbol
type table = (field list *  contr_info list * meth list * symbol list)
type contract_ast = Contract of string *  statement option * (declaration list) * (any_funct list) 
type ('a,'b) pars = table -> 'a -> 'b *table 
type ast = contract_ast list
type ('a, 'b) mapping = Mapping of 'a expression * 'b expression 
exception CompilationFail

(*Utils*)
let eq_type : type a b. a typename -> b typename -> (a,b) eq option = fun t1 t2 ->
 match t1,t2 with
 | Int, Int -> Some Refl
 | Bool, Bool -> Some Refl
 | String, String -> Some Refl
 | ContractAddress, ContractAddress -> Some Refl
 | _,_ -> None

let is_same_type: type a b. a typename -> b typename -> bool =
    fun t1 t2 ->
        (match eq_type t1 t2 with
            | Some Refl -> true
            | None -> false)

let rec is_same_params: type a b. a param_list -> b param_list -> bool =
    fun p1 p2 -> 
        match p1,p2 with
            | PNil,PNil -> true
            | PCons(((t1,name1),_),tail1),PCons(((t2,name2),_),tail2) ->
                    (is_same_type t1 t2) && (is_same_params
                    tail1 tail2)
            | _,_ -> false

let rec is_matching_meths =
    fun meth1 meth2 -> match (meth1,meth2) with
    |(Some(Funct(name1,params1,(out1,stg1),view1,vis1))),(Some(Funct(name2,params2,(out2,stg2),view2,vis2))) -> 
        name1=name2 && is_same_params params1 params2 &&
        is_same_type out1 out2 && stg1=stg2 && view1 = view2 && vis1=vis2
    | None,None -> true
    | _,_ -> false


let pp_opt =
    fun f opt ->
        match opt with
        | Some o -> (f o) 
        | None -> ""


let comp_funct : type a b c. (a -> b) -> (b -> c) -> a -> c =
    fun f g x -> g (f x)

let rec is_var_in_params : type a b. a param_list -> b var -> bool =
    fun params (vartype,varname) -> 
        match params with
        | PNil -> false
        | PCons(((partype,parname),_),tail) when parname=varname -> 
                is_same_type partype vartype
        | PCons(_,tail) -> is_var_in_params tail (vartype,varname)


let apply_to_first =
    fun f (fst,scd,thd,fth) -> (f fst),scd,thd,fth

let apply_to_second =
    fun f (fst,scd,thd,fth) -> fst,(f scd),thd,fth

let apply_to_third =
    fun f (fst,scd,thd,fth) -> fst,scd,(f thd),fth

let apply_to_fourth =
    fun f (fst,scd,thd,fth) -> fst,scd,thd,(f fth)


(*Symbol*)
let rec is_symbol_in_table = 
    fun (_,_,_,tbl) s -> 
    let rec aux stbl = match stbl with
        | [] -> false
        | Symbol(name)::_  when name = s -> true
        | _::tl -> aux tl
    in aux tbl


let rec add_symbol =
    fun tbl s -> 
        if (is_symbol_in_table tbl s) then tbl 
        else apply_to_fourth (fun sl -> [Symbol s]@sl) tbl

let rec get_symbols =
    fun (_,_,_,tbl) -> 
        let rec aux stbl = match stbl with
            | [] -> []
            | Symbol s :: tl -> [s]@aux tl 
        in aux tbl

(*Type Table*)

let rec is_var_in_table =
    fun (tbl,_,_,_) (t,name) ->
        let rec aux ftbl =
           match ftbl with
            | [] -> false 
            | Field ((tfield, namefield),_) ::_ when namefield=name -> 
                    is_same_type t tfield
            | _::tl -> aux tl
        in aux tbl

let rec is_fun_in_table =
    fun (_,_,tbl,_) (name, params, (outtype,stor)) ->
        let rec aux ftbl =
           match ftbl with
            | [] -> false
            | Funct (name_fun, params_fun, (outtype_fun,_), _, _) ::_ when name_fun=name -> 
                (is_same_params params_fun params) && (is_same_type outtype outtype_fun)
            | _::tl -> aux tl
        in aux tbl


let apply_to_contr : string  -> meth option -> (contr_info ->
    contr_info) -> contr_info list -> contr_info list= 
    fun name funct f tbl ->
            List.map 
            (fun (Contr (s,p,m,i)) -> 
                if s = name && (p = None) && (is_matching_meths m funct) then 
                    f (Contr(s,p,m,i))
                else (Contr(s,p,m,i))) tbl

let change_interface_name =
    fun contr funct new_name ->
        apply_to_second
        (apply_to_contr contr funct 
        (fun (Contr (s,p,m,(Interface(n,f,i)))) -> 
            if n="" then Contr (s,p,m,(Interface(new_name,f,i)))
            else raise CompilationFail))

let add_field_in_table =
    fun var islocal tbl -> match tbl with 
    fl,il,funl,sl -> ([Field(var,islocal)]@fl),il,funl,sl

let add_interface_in_table =
    fun interface_name contr_name f implemented ->
        apply_to_second (fun itbl -> 
            [Contr (contr_name, None, f,
            (Interface(interface_name,[],implemented)))]@itbl)
       
let add_funct_to_contract_meths : meth -> string -> meth option -> contr_info list -> contr_info list = 
    fun meth contr_name funct_par tbl ->
        apply_to_contr contr_name funct_par
        (fun (Contr(n,p,f,i)) ->
            match i with Interface(interface_name, fl, impl) ->
                if (List.exists (fun f -> is_matching_meths (Some f) (Some meth)) fl) then 
                    Contr(n,p,f,i)
                else 
                    Contr(n,p,f,(Interface(interface_name,([meth]@fl),impl)))
        ) tbl

let add_function_in_table : meth -> string -> table -> table =
    fun f contr_name tbl-> 
        apply_to_second (add_funct_to_contract_meths f contr_name None) 
        (apply_to_third (fun funl ->[f]@funl) tbl)

let name_interface =
        let rec aux n i_list = match i_list with
        | [] -> []
        | (Contr(name, par, funct, (Interface("",fl,false))))::tl -> 
                [Contr(name, par, funct, (Interface(("Interface" ^ (string_of_int
                n)),fl,false)))]@(aux (n+1) tl)
        | h::tl -> [h]@(aux n tl)
        in aux 0

let remove_local_var =
    apply_to_first (List.filter (fun f -> match f with
            | Field (_,true) -> false 
            | _ -> true))

let delete_empty_interface =
        (List.filter 
        (fun (Interface(name,f,i)) -> f <> [] || name <> ""))

let rec get_interface_list =
    function
        | [] -> []
        | (Contr(_,_,_,i))::tl -> [i]@(get_interface_list tl)
let rec get_interface =
    fun name par meth contrl -> match contrl with
        | [] -> None
        | (Contr(n,p,f,i)):: tl when n = name && p=par && is_matching_meths meth f -> Some i
        | h::tl -> get_interface name par meth tl


let rec set_parent_name_contract =
    fun name contr_list -> match contr_list with
        | [] -> []
        | (Contr(n,None,f,(Interface(iname,imeth,false))))::tl -> 
                [Contr(n,(Some
                name),f,(Interface(iname,imeth,false)))]@(set_parent_name_contract
                name tl)
        | (Contr("this",None,None,i))::tl ->
                [Contr("",None,None,i)]@(set_parent_name_contract name tl)
        | h::tl -> [h]@tl

let sort_interface_list =
    List.stable_sort 
    (fun i1 i2 -> match i1,i2 with
        | Interface(n1,_,_),Interface(n2,_,_) -> String.compare n1 n2) 
   
let rec pp_table_fields =
    function 
        | (Field ((_,name),_))::tl -> "field: " ^ name ^ nl ^ pp_table_fields tl
        | [] -> ""

let rec pp_table_function =
    function 
        | (Funct (name,_,_,_,_))::tl -> "function: " ^ name ^ nl ^ pp_table_function tl
        | [] -> ""

let pp_interface_short =
    function (Interface (t,flist,i)) ->  "interface: " ^ t  ^ nl ^ pp_table_function flist ^ nl 

let pp_interface_name =
    function (Interface (t,flist,i)) ->  t
let rec pp_table_contract =
    function 
        | (Contr (name, parent, funct, inter))::tl ->
                name ^ pp_opt (fun x -> " parent:" ^ x) parent ^ " -> " ^ pp_interface_short inter ^ pp_table_contract tl
        | [] -> ""

let rec pp_table_symbol  = 
    function
        | (Symbol name)::tl -> "symbol: " ^ name ^ nl ^ pp_table_symbol tl
        | [] -> ""

let pp_table = 
    fun (f, i, func, s) ->
        pp_table_fields f ^ nl ^ pp_table_contract i ^ nl ^ pp_table_function
        func ^ nl ^ pp_table_symbol s

(*Parsing*)
let pars_unary =
    fun op pars tbl e ->
        let (expr, ntbl) = pars tbl e in
        (op expr),ntbl

let pars_double = 
    fun op pars tbl e1 e2 ->
        let (op_unary, ntbl) = (pars_unary op pars tbl e1)  in 
        pars_unary op_unary pars ntbl e2

let pars_typename : type a. a tag -> a typename  = 
    function
        | SmartCalculus.Int -> Int
        | SmartCalculus.String -> String
        | SmartCalculus.Bool -> Bool
        | SmartCalculus.ContractAddress -> ContractAddress
        | _ -> raise CompilationFail

let rec const_expression =
    function
        | Numeric n -> SmartCalculus.Value n
        | _ -> raise CompilationFail
        (*
        | Symbolic s -> Leaf ("'" ^ s ^ "'") *)(*Come fare???*)

let rec base_expression : type a. (a expr, a expression) pars   = 
    fun tbl expr -> (
        match expr with
        | Var(Int,"value") -> MsgValue
        | Var(Int,"balance") -> Balance
        | Var(tag,e) ->  
                if (is_var_in_table tbl ((pars_typename tag),e)) then Var((pars_typename tag),e)
                else raise CompilationFail
        | Field(tag,e) -> 
                if (is_var_in_table tbl ((pars_typename tag),e)) then Var((pars_typename tag),e)
                else raise CompilationFail
        | Value v -> Value v
        | _ -> raise CompilationFail),tbl

and int_expression :(int expr, int expression) pars =
    fun tbl expr -> (match expr with
        | Plus ((Minus e1),(e2)) -> pars_double (fun e1 e2 -> Minus(e1,e2)) int_expression tbl e2 e1
        | Plus ((e1),(Minus e2)) -> pars_double (fun e1 e2 -> Minus(e1,e2)) int_expression tbl e1 e2
        | Plus (e1, e2) ->  pars_double (fun e1 e2 -> Plus(e1,e2))
        int_expression tbl e1 e2
        | Mult (c, e) -> pars_double (fun e1 e2 -> Mult(e1,e2)) int_expression
        tbl (const_expression c) e
        | Minus (Value v) -> (Value ((-1) * v)),tbl
        | Minus e -> pars_double (fun e1 e2 -> Mult(e1,e2)) int_expression
        tbl (const_expression (Numeric (-1))) e
        | Max (e1,e2) -> let bexpr,ntbl = bool_expression tbl (Gt(e1,e2)) in
            pars_double (fun v1 v2 -> CondExpr(bexpr,v1,v2)) int_expression tbl e1 e2
        | Symbol s -> (Symbol s),(add_symbol tbl s)
        | e -> base_expression tbl e)
and bool_expression :  (bool SmartCalculus.expr, bool expression) pars =
    fun tbl expr  -> match expr with
        | Geq (e1, e2) -> pars_double (fun e1 e2 -> Geq(e1,e2)) int_expression
        tbl e1 e2
        | Gt (e1, e2) -> pars_double (fun e1 e2 -> Gt(e1,e2)) int_expression
        tbl e1 e2
        | Eq (t, e1, e2) -> pars_double (fun e1 e2 -> Eq((pars_typename
        t),e1,e2)) (pars_expression (pars_typename t)) tbl e1 e2 
        | And (e1, e2) -> pars_double (fun e1 e2 -> And(e1,e2)) bool_expression
        tbl e1 e2
        | Or (e1, e2) -> pars_double (fun e1 e2 -> Or(e1,e2)) bool_expression
        tbl e1 e2
        | Not e -> pars_unary (fun e -> Not(e)) bool_expression tbl e
        | e -> base_expression tbl e 
and contract_expression :  ((contract address) expr, (contract address)
expression) pars = 
    fun tbl expr -> match expr with
        | SmartCalculus.This -> This,tbl
        | e -> base_expression tbl e
and pars_expression: type a. a typename -> table -> a expr -> a expression
* table =
    fun t tbl -> match t with
        | Int -> int_expression tbl
        | String -> base_expression tbl 
        | Bool -> bool_expression tbl
        | ContractAddress -> contract_expression tbl

let pars_decl : (assign, declaration) pars =
    fun tbl ass  -> match ass with
            Let ((t,name),v) -> 
                let (value,ntbl) = (pars_expression (pars_typename t) tbl (Value v)) in
                let new_table = 
                    match (pars_typename t),v with
                    | ContractAddress,(Contract s) -> add_field_in_table
                    (ContractAddress, name) false (add_interface_in_table s name
                    None false ntbl)
                    | _,_ -> add_field_in_table ((pars_typename t), name) false ntbl in
                (Declaration(((pars_typename t),name),(Some value))),new_table

let rec pars_expression_list : type a. table -> a tag_list -> a expr_list -> a expression_list * table=
    fun tbl tlist elist ->
        match tlist,elist with 
        | (TCons(t,ttail)),(ECons(e,etail)) -> 
                let (expr,ntbl) = (pars_expression (pars_typename t) tbl e) in
                (ExprCons (((pars_typename t),expr),
                ((fun (x,_) -> x)(pars_expression_list ntbl ttail
                etail)))),ntbl
        | TNil,ENil -> ExprNil,tbl

let get_storage: type a. a typename -> storage option =
        function
        | String -> Some Memory
        | _ ->  None
let rec get_param_list : type a. a var_list -> a param_list = 
    fun varlist ->
        match varlist with
        | VCons((tagvar,var),vartail) ->
            let t = pars_typename tagvar
            in PCons(((t,var), (get_storage t)),(get_param_list vartail))
        | VNil -> PNil

let pars_contract_ref =
    fun tbl opt -> match opt with
        | None -> This,tbl
        | Some c -> pars_expression ContractAddress tbl c

let get_contract_name : (contract address) expression -> string option =
    function 
        | Var(ContractAddress,name) -> Some name
        | This -> Some "this"
        |  _ -> None 

let rec get_type_list : type a. a tag_list -> a param_list =
    function
        TNil -> PNil
        | TCons (tag, tl) -> 
                PCons((((pars_typename tag), ""),(get_storage
        (pars_typename tag))), get_type_list tl)

let pars_meth : type a b. (a, b) SmartCalculus.meth -> meth =
    fun (tagret, taglist, name) ->
        let t = (pars_typename tagret) in 
        let outtype = t,(get_storage t) in 
        let params = (get_type_list taglist) in
        Funct(name,params,outtype,[Payable],[Public])

let rec pars_rhs : 'a typename -> meth -> ('a rhs, 'a expression) pars =
    fun t m tbl rhs ->
        let add_interf_opt =
            fun funct contr tbl -> 
                apply_to_second 
                (fun itbl -> match contr with
                | None -> itbl
                | Some name ->
                add_funct_to_contract_meths funct name (Some m) itbl) tbl in
        match rhs with  
            | Expr e -> pars_expression t tbl e 
            | Call (opt, (funtag, tags, name), elist) -> 
                let (expr,ntbl1) = pars_expression_list tbl tags elist in
                let (con,ntbl2) = pars_contract_ref ntbl1 opt in
                Call(con,name,expr,None),
                (match pars_meth (funtag,tags,name) with 
                 f ->(add_interf_opt f (get_contract_name con) ntbl2)) 
            | CallWithValue (opt, (funtag, tags, name), elist, vexpr) ->
                let value,ntbl1 = pars_expression Int tbl vexpr in
                match pars_rhs t m ntbl1 (Call(opt,(funtag,tags,name),elist)) with
                | (Call(con,name,expr,None)),ntbl2 -> Call(con, name, expr, (Some
                value)),ntbl2
                | _ -> raise CompilationFail

let rec pars_stm : meth -> (stm, statement) pars = 
    fun m tbl s -> match s with
        | Assign((tag, name),rhs) -> 
                if (is_var_in_table tbl ((pars_typename tag),name)) then
                    let (expr, ntbl) = pars_rhs (pars_typename tag) m tbl rhs in
                        match (pars_typename tag),expr with
                        | ContractAddress,(Value (Contract int_name)) ->
                                Empty,(change_interface_name name (Some m) int_name
                            ntbl)
                        | _ -> 
                            Assignment (((pars_typename tag),name),expr),ntbl
                else  raise CompilationFail
        | IfThenElse(expression,stm1,stm2) -> 
                let (expr,ntbl) = bool_expression tbl expression in
                pars_double (fun stm1 stm2 -> IfElse (expr, stm1, stm2))
                (pars_stm m) ntbl stm1 stm2
        | Comp (stm1,stm2) -> pars_double (fun stm1 stm2 -> Sequence(stm1,stm2))
        (pars_stm m) tbl stm1 stm2
        | _ -> raise CompilationFail


let rec pars_stmlist : meth -> (stm list, statement) pars = 
    fun m tbl stml ->
        match stml with
        | h::[] -> (pars_stm m) tbl h
        | h::tl ->
                let (stm,ntbl) = (pars_stm m) tbl h in 
                pars_unary (fun v -> Sequence(stm,v)) 
                (pars_stmlist m) ntbl tl
        | [] -> Empty,tbl
let rec add_params_in_tbl : type a. meth -> a param_list -> table -> table =
    fun m par_list -> match par_list with 
        | PNil -> (fun x -> x)
        | PCons(((t,name),_),tail) -> 
                if (is_same_type t ContractAddress) then
                    comp_funct (add_params_in_tbl m tail) 
                    (comp_funct (add_field_in_table (t,name) true)
                    (add_interface_in_table "" name (Some m) false))
                else 
                    comp_funct (add_params_in_tbl m tail) (add_field_in_table (t,name) true)

let pars_funct: (any_method_decl, any_funct) pars = 
    fun tbl meth ->
        match meth with 
        AnyMethodDecl((tagret, taglist, name),(param_list, stmlist, retexpr)) -> 
            let m = pars_meth (tagret, taglist, name) in
            match m with Funct (meth_name,p,outtype,payable,public) ->
            let params = (get_param_list param_list) in
            let tbl_with_fun = add_params_in_tbl m params (add_function_in_table
            m this_str tbl) in
            let (stm,ntbl1) = pars_stmlist m tbl_with_fun stmlist in
            let (return,ntbl2) = (pars_expression (pars_typename tagret) ntbl1 retexpr) in
            match eq_type (pars_typename tagret) ((fun (x,_) -> x) outtype) with
            Some Refl -> (Function 
            ((name,params,outtype,payable,public),stm,
            return)),(remove_local_var ntbl2)
            | None -> raise CompilationFail

let rec assign_symbol : string list -> int -> statement =
    fun l n -> match l with
        | [] -> Empty
        | h::tl -> Sequence((Assignment((Int, "symbol[" ^ h ^ "]"), Value(n)),
        assign_symbol tl (n + 1)))


let rec pars_list : type a b. (a,b) pars -> a list ->
    table -> b list -> b list * table =
    fun f l1 tbl l2 ->
        match l1 with 
        | [] -> l2,tbl
        | h::tl -> 
                let (nel,ntbl) = f tbl h in 
                pars_list f tl ntbl (l2@[nel])

let pars_contract : (a_contract, contract_ast) pars =
    fun tbl (add, meths, fields) -> match add with
        | Contract name -> 
                let (decls, ntbl1) = pars_list pars_decl fields (add_interface_in_table
                name this_str None true tbl) [] in 
                let (flist, ntbl2) = pars_list pars_funct meths ntbl1 [] in 
                let constructor = 
                    match assign_symbol (get_symbols ntbl2) 0 with 
                    Empty -> None | s -> Some s in  
                (Contract(name, constructor, decls, flist),
                (apply_to_second (set_parent_name_contract name) ntbl2))

let rec pars_contract_list = 
    fun tbl l -> match l with 
        | [] -> print_endline (pp_table tbl);[],tbl
        | h::tl -> 
                let (contr, (fl,il,funl,sl)) = pars_contract tbl h in
                let (contr_list, ntbl2) = pars_contract_list ([],il,[],[]) tl in
                ([contr]@contr_list, ntbl2)
        
let rec pars_configuration =
    function
       {contracts = cl; _} -> 
            (pars_contract_list ([],[],[],[]) cl)

(*From ast to string*)
let rec pp_typename : type a. a typename -> string =
    function 
        | Int -> "int"
        | Bool -> "bool"
        | String -> "string"
        | ContractAddress -> "address"

let pp_value : type a. a typename -> a -> string =
    fun t v ->
        match t,v with 
        | String,s -> "'" ^ s ^ "'"
        | Int,n -> string_of_int n
        | Bool,b -> string_of_bool b
        | ContractAddress,(Contract s) -> "new " ^ s ^ "()"

let rec pp_expression : type a. string option -> meth option -> contr_info list -> a typename ->
    a expression -> string =
    fun  p m tbl t expr->
        let pp_expr_info tag e = 
            (pp_expression p m tbl tag e) in
        match t,expr with 
        | Int,Balance -> "(int)(address(this).balance)"
        | Int,MsgValue -> "(int)(msg.value)"
        | t,Var(_, name) -> name
        | ContractAddress,This -> "address(this)"
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
        | _,(Call(c,s,exprl,value)) ->  
                "(" ^ pp_contract_ref 
        c p m tbl ^ ")."  ^ s ^ pp_opt (fun e -> ".value((uint)(" ^ pp_expr_info Int e ^ "))")
        value ^ "(" ^ (String.concat ", " (string_list_of_expression
        p m tbl exprl)) ^ ")" 
        | _,(Symbol s) -> symb_array ^ "[" ^ "'" ^ s ^ "'" ^ "]"
 and string_list_of_expression : type a. string option -> meth option ->
     contr_info list  -> a expression_list -> string list =
    fun p m tbl el -> match el with
        | ExprNil -> []
        | ExprCons ((t,e), tl) -> [(pp_expression p m tbl t e)]@(string_list_of_expression p m tbl tl) 
and pp_contract_ref =
    fun contr p f ctbl -> match contr with
        | Var(_, name) -> "(" ^ pp_opt pp_interface_name (get_interface name p
        f ctbl) ^ ")" ^ name
        | Value v -> "new " ^ pp_value ContractAddress v ^ "()"
        | This -> "this"
        | _ -> pp_expression p f ctbl ContractAddress contr 
      
(*type declaration = Declaration : 'a var * ('a expression option) ->  declaration*)
let pp_declaration =
    fun p tbl decl -> match decl with
        Declaration ((t,name),e) -> 
            let equals = pp_opt (fun expr -> " = " ^ pp_expression p None tbl t expr) e in
            pp_typename t ^ " " ^ name ^
            (match t,e with
            | ContractAddress,(Some n) -> " "
            | _,_ -> equals) ^ ";"


let rec pp_statement  = 
    fun p m tbl stm -> 
        let pp_stm_info = pp_statement p m tbl in
        match stm with
        | IfElse (b, stm1, stm2) -> "if (" ^ pp_expression p m tbl Bool b ^ "){"  ^ nl ^
        (pp_stm_info stm1) ^ nl ^ "}" ^ nl ^ "else {" ^ nl ^ pp_stm_info stm2
        ^ nl ^ "}"
        | Assignment ((t,name), e) -> pp_expression p m tbl t (Var(t,name)) ^ " = " ^ pp_expression p m tbl t e ^ ";"
        | Sequence (stm1, stm2) -> pp_stm_info stm1 ^ nl ^ pp_stm_info stm2
        | Empty -> ""

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
    function l -> "(" ^ (String.concat ", " (string_list_of_params l)) ^ ")"

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

let declare_simbols =
    "mapping (" ^ pp_typename String ^ " => " ^ pp_typename Int ^ ") " ^ symb_array
    ^ ";"
let rec pp_meth =
    function 
        Funct (name, params,(outtype,storage), view, vis) ->
            "function " ^ name ^ pp_params params ^ " " ^ 
            (String.concat " " (List.map pp_view view)) ^ 
            (String.concat " " (List.map pp_visibility vis)) ^ 
            "returns (" ^ pp_typename outtype ^ " " ^ (pp_opt pp_storage storage) ^
            ")"

let rec pp_funct =
    fun p tbl f -> 
        match f with 
        Function ((name, params,(outtype,storage), view, vis) , stm, return) ->
            let meth = (Funct (name, params,(outtype,storage), view, vis)) in
            pp_meth  meth ^
            "{" ^ nl ^ pp_statement p (Some meth) tbl stm ^ nl ^
            "return " ^ pp_expression p (Some meth) tbl outtype return ^ ";" ^ nl ^ "}" 

let pp_constructor  =
    fun p tbl s ->
        "constructor() public{" ^ nl ^ pp_statement p None tbl s ^ "}"

let rec pp_contract =
    fun tbl c -> match c with
    Contract (name, constructor, fields, meths) ->  "contract " ^ name ^ " {" ^ nl ^
    (match constructor with None -> "" | _ -> declare_simbols ^ nl) ^
    (String.concat nl (List.map (pp_declaration (Some name) tbl)fields)) ^ nl ^
    pp_opt (pp_constructor (Some name) tbl) constructor ^ nl ^ (String.concat nl (List.map
    (pp_funct (Some name) tbl) meths)) ^ nl ^ "}"

let rec pp_actor =
    fun tbl act -> match act with
        | ActCon c -> pp_contract tbl ((fun (x,_) -> x) (pars_contract ([],[],[],[]) c))
        | ActHum h -> raise CompilationFail

let pp_interface : interface -> string = 
    function 
        | Interface (name,funct_list,false) -> 
                "interface " ^ name ^ "{" ^ nl ^ String.concat (";" ^ nl) (List.map pp_meth
            funct_list) ^ nl ^ "}"
        | _ -> ""

let rec divide_by_func =
    fun i_list -> match i_list with
        | Interface(name,f,i)::[] -> [[Interface(name,f,i)]]
        | (Interface(name,f,i))::tl -> 
                [List.filter (fun (Interface(n,funct,impl)) -> n = name)
                i_list]@(divide_by_func(List.filter (fun (Interface(n,funct,impl)) -> n <> name)
                tl))
        | [] -> raise CompilationFail

module MethSet = Set.Make(struct let compare = compare type t = meth end ) 
let union_without_dupl =
    fun l1 l2 -> MethSet.elements (MethSet.union (MethSet.of_list l1)
    (MethSet.of_list l2))
let rec funct_union_interface =
    fun inlist f -> match inlist with
        | [] -> None
        | Interface (n,meths,i)::[] ->  Some (Interface(n,(union_without_dupl meths f),i))
        | Interface (n,meths,_)::tl -> funct_union_interface tl
        (union_without_dupl meths f)

let rec unify_funct =
    fun int_list -> 
        List.map (fun il -> 
        match funct_union_interface il [] with 
            Some i -> i 
            | None -> Interface("",[],false)) 
        (divide_by_func int_list)

let rec pp_ast : ast * table -> string =
    fun (cl,(_,il,_,_)) -> 
        let int_list = name_interface il
        in
        "pragma solidity 0.5.11;" ^ nl ^ 
        String.concat nl  (List.map pp_interface  (unify_funct
        (get_interface_list (int_list)))) ^ nl ^
        String.concat nl (List.map (pp_contract int_list) cl)
;;
let outstr = (pp_ast (pars_configuration (Grammar.conf)));;
print_string outstr;;
let out_channel = open_out "out.sol";;
Printf.fprintf out_channel "%s" outstr;
