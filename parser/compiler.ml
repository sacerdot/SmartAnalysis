open Grammar
open SmartCalculus
open ParserCombinator

let nl = "\n"
let symb_array = "symbol"

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
    | Call : (contract address) expression option * string * 'a expression_list
    * (int expression) option-> 'b expression
and _ expression_list =
      ExprNil : unit expression_list
    | ExprCons : ('a typename * 'a expression) * 'b expression_list -> ('a * 'b) expression_list
and _ parameters = PNil: unit parameters | PCons: ('a var * storage option) * 'b parameters -> ('a * 'b) parameters  
and ('a, 'b) funct = string * 'a parameters * ('b typename * storage option)
type declaration = Declaration : 'a var * ('a expression option) -> declaration
type statement = 
    | Empty
    | IfElse : bool expression * statement * statement -> statement
    | Assignment : 'a var * 'a expression -> statement
    | Sequence : statement * statement -> statement
type view = View | Pure | Payable
type visibility = External | Public | Internal | Private
(*name,parameters,visibility,view,outtype,stm,return*) 
type any_funct=  Function: ('a, 'b) funct * view list * visibility 
    list * statement * 'b expression -> any_funct
type any_type_item = 
    | Field: 'a var * bool-> any_type_item
    | Contract: (string * string) -> any_type_item
    | Funct: ('a, 'b) funct -> any_type_item
    | Symbol: string -> any_type_item
type type_table = any_type_item list
type contract_ast = Contract of string *  statement option * (declaration list) * (any_funct list) 
type ('a,'b) pars = type_table -> 'a -> 'b * type_table
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

let rec is_same_params: type a b. a parameters -> b parameters -> bool =
    fun p1 p2 -> 
        match p1,p2 with
            | PNil,PNil -> true
            | PCons(((t1,name1),_),tail1),PCons(((t2,name2),_),tail2) ->
                    (is_same_type t1 t2) && (name1 == name2) && (is_same_params
                    tail1 tail2)
            | _,_ -> false

let comp_funct : type a b c. (a -> b) -> (b -> c) -> a -> c =
    fun f g x -> g (f x)

let rec is_var_in_params : type a b. a parameters -> b var -> bool =
    fun params (vartype,varname) -> 
        match params with
        | PNil -> false
        | PCons(((partype,parname),_),tail) when parname=varname -> 
                is_same_type partype vartype
        | PCons(_,tail) -> is_var_in_params tail (vartype,varname)


(*Symbol*)
  
let rec is_symbol_in_table = 
    fun tbl s -> match tbl with
    | [] -> false
    | Symbol(name)::_  when name = s -> true
    | _::tl -> is_symbol_in_table tl s


let rec add_symbol : type_table -> string -> type_table =
    fun tbl s -> 
        if (is_symbol_in_table tbl s) then tbl 
        else 
            [Symbol s]@tbl

let rec get_symbols =
    function 
        | [] -> []
        | (Symbol s) :: tl -> [s]@get_symbols tl
        | h::tl -> get_symbols tl
(*Type Table*)
let rec is_var_in_table : type a. type_table -> a var -> bool =
    fun tbl (t,name) -> 
        match tbl with
        | [] -> false
        | Field ((tfield, namefield),_) ::_ when namefield=name -> 
                is_same_type t tfield
        | Contract(tcon, namecon) ::_ when namecon=name ->
                is_same_type t ContractAddress
        | _::tl -> is_var_in_table tl (t,name)

let rec is_fun_in_table : type a b. type_table -> (a, b) funct -> bool =
    fun tbl (name, params, (outtype,stor)) ->
        match tbl with
        | [] -> false
        | Funct (name_fun, params_fun, (outtype_fun,_)) ::_ when name_fun=name -> 
                (is_same_params params_fun params) && (is_same_type outtype outtype_fun)
        | _::tl -> is_fun_in_table tl (name, params, (outtype,stor))

let add_field_in_table : type a . a var -> bool -> type_table -> type_table =
    fun var islocal tbl -> match tbl with l -> (l@[Field(var,islocal)])

let add_contract_in_table : string*string -> type_table -> type_table =
    fun con tbl -> match tbl with l -> (l@[Contract(con)])
    
let add_function_in_table : type a b. (a,b) funct -> type_table ->  type_table =
    fun f tbl-> match tbl with l -> (l@[Funct(f)])

let rec remove_local_var =
    function 
        | [] -> []
        | Field (_,true)::tl -> remove_local_var tl
        | h::tl -> [h]@(remove_local_var tl)
(*Parsing*)
let pars_unary =
    fun op pars tbl e ->
        let (expr, ntbl) = pars tbl e in
        (op expr),ntbl
let pars_double = 
    fun op pars tbl e1 e2 ->
        let (op_unary, ntbl) = (pars_unary op pars tbl e1)  in 
        pars_unary op_unary pars ntbl e2
        (*
let rec repeat_pars =
    fun op pars tbl el -> match el with
    | [] -> raise CompilationFail
    | [h] -> let (expr, ntbl) = pars tbl h in
            (op expr),ntbl
    | h::tl -> 
            let (new_op, new_tbl) = (repeat_pars op pars tbl [h]) in
            repeat_pars new_op pars new_tbl tl 
            *)
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
and pars_expression: type a. a typename -> type_table -> a expr -> a expression
* type_table =
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
                    | ContractAddress,(Contract s) -> 
                            add_contract_in_table (s,name) ntbl
                    | _,_ -> add_field_in_table ((pars_typename t), name) false ntbl in
                (Declaration(((pars_typename t),name),(Some value))),new_table

let rec pars_expression_list : type  a. type_table -> a tag_list -> a expr_list
-> a expression_list * type_table =
    fun tbl tlist elist ->
        match tlist,elist with 
        | (TCons(t,ttail)),(ECons(e,etail)) -> 
                let (expr,ntbl) = (pars_expression (pars_typename t) tbl e) in
                (ExprCons (((pars_typename t),expr),
                ((fun (x,_) -> x)(pars_expression_list ntbl ttail
                etail)))),ntbl
        | TNil,ENil -> ExprNil,tbl

let pars_rhs :'a typename -> ('a rhs, 'a expression) pars =
    fun t tbl rhs ->
        let con opt with_value= match opt,with_value with 
            None,false -> None 
            | None,true -> Some This
            | Some c,_ -> (Some ((fun (expr,t) -> expr )(pars_expression
            ContractAddress tbl c))) in
        match rhs with  
        | Expr e -> pars_expression t tbl e 
        | Call (opt, (funtag, tags, name), elist) -> 
            let (expr,ntbl) = (pars_expression_list tbl tags elist) in
            Call(con opt false,name,expr,None),ntbl
        | CallWithValue (opt, (funtag, tags, name), elist, vexpr) ->
            let (expr,ntbl1) = (pars_expression_list tbl tags elist) in
            let (value,ntbl2) = (pars_expression Int ntbl1 vexpr) in
            Call(con opt true, name, expr, (Some value)),ntbl2

let get_storage: type a. a typename -> storage option =
        function
        | String -> Some Memory
        | _ ->  None
let rec get_parameters : type a. a var_list -> a parameters = 
    fun varlist ->
        match varlist with
        | VCons((tagvar,var),vartail) ->
            let t = pars_typename tagvar
            in PCons(((t,var), (get_storage t)),(get_parameters vartail))
        | VNil -> PNil

let rec pars_stm : (stm, statement) pars = 
    fun tbl s -> match s with
        | Assign((tag, name),rhs) -> 
                if (is_var_in_table tbl ((pars_typename tag),name)) then
                    pars_unary (fun e ->  Assignment (((pars_typename
                    tag),name),e)) (pars_rhs (pars_typename
                    tag)) tbl rhs
                else  raise CompilationFail
        | IfThenElse(expression,stm1,stm2) -> 
                let (expr,ntbl) = bool_expression tbl expression in
                pars_double (fun stm1 stm2 -> IfElse (expr, stm1, stm2))
                pars_stm ntbl stm1 stm2
        | Comp (stm1,stm2) -> pars_double (fun stm1 stm2 -> Sequence(stm1,stm2))
        pars_stm tbl stm1 stm2
        | _ -> raise CompilationFail

let rec pars_stmlist : (stm list, statement) pars = 
    fun tbl stml   ->
        match stml with
        | h::[] -> pars_stm tbl h
        | h::tl ->
                let (stm,ntbl) = pars_stm tbl h in 
                pars_unary (fun v -> Sequence(stm,v)) 
                pars_stmlist ntbl tl
        | [] -> Empty,tbl

let rec pp_type_table : type_table -> string =
    function 
        | (Field ((_,name),_))::tl -> "field: " ^ name ^ nl ^ pp_type_table tl
        | (Contract (t,name))::tl -> "contract: " ^ t ^ " " ^ name ^ nl ^
        pp_type_table tl
        | (Funct (name,_,_))::tl -> "function: " ^ name ^ nl ^ pp_type_table tl
        | (Symbol name)::tl -> "symbol: " ^ symb_array ^ "['" ^ name ^ "'] "
        | [] -> ""

let rec add_params_in_tbl : type a. a parameters -> type_table -> type_table =
    function 
        | PNil -> (fun x -> x)
        | PCons(((t,name),_),tail) -> comp_funct (add_params_in_tbl tail)
        (add_field_in_table (t,name) true)

let pars_funct: (any_method_decl, any_funct) pars = 
    fun tbl meth ->
        match meth with 
        AnyMethodDecl((tagret, taglist, name),(parameters, stmlist, retexpr)) -> 
            let t = (pars_typename tagret) in 
            let outtype = t,(get_storage t) in 
            let params = (get_parameters parameters) in
            let tbl_with_fun = add_params_in_tbl params (add_function_in_table
            (name,params,outtype) tbl) in
            let (stm,ntbl1) = pars_stmlist tbl_with_fun stmlist in
            let (return,ntbl2) = (pars_expression t ntbl1 retexpr) in
            (Function 
            ((name,
            params,
            outtype),
            [Payable],
            [Public],
            stm,
            return)),(ntbl2)

let rec assign_symbol : string list -> int -> statement =
    fun l n -> match l with
        | [] -> Empty
        | h::tl -> Sequence((Assignment((Int, "symbol[" ^ h ^ "]"), Value(n)),
        assign_symbol tl (n + 1)))

(*
let rec add_param =
    fun (t,name) params -> match params  with AnyParams p -> AnyParams(PCons(((t,
    name),None),p))
let rec set_contract_params : type_table -> any_parameters -> any_parameters =
    fun tbl params -> match tbl with
    | [] -> params
    | Contract(t,name)::tl -> set_contract_params tl  (add_param
    (ContractAddress,name) params)
    | _::tl -> set_contract_params  tl params
let set_address_funct =
    fun tbl ->
        let parameters = match (set_contract_params tbl (AnyParams PNil)) with
        AnyParams p -> p in 
        Function ("setAddresses", parameters , [], [Public], TNil, Empty, ExprNil)
*)
let rec pars_list : type a b. (a,b) pars -> a list ->
    type_table -> b list -> b list * type_table =
    fun f l1 tbl l2 ->
        match l1 with 
        | [] -> l2,tbl
        | h::tl -> 
                let (nel,ntbl) = f tbl h in 
                pars_list f tl ntbl (l2@[nel])
let pars_contract : a_contract -> contract_ast =
    function (add, meths, fields) ->
        match add with
        | Contract name -> 
                let (decls, tbl) = pars_list pars_decl fields [] [] in 
                print_endline (pp_type_table tbl);
                let (flist, newtbl) = pars_list pars_funct meths tbl [] in 
                let constructor = 
                    match assign_symbol (get_symbols newtbl) 0 with 
                    Empty -> None | s -> Some s in  
                Contract(name, constructor, decls, flist)

let rec pars_contract_list : a_contract list -> ast = 
    function 
        | [] -> []
        | h::tl -> [pars_contract h]@(pars_contract_list tl)
        
let rec pars_configuration : configuration -> ast =
    function
        {contracts = cl; _} -> pars_contract_list cl

(*From ast to string*)
let pp_opt =
    fun f opt ->
        match opt with
        | Some o -> (f o) 
        | None -> ""

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
    
let rec pp_expression : type a . a typename -> a expression -> string =
    fun t expr ->
        match t,expr with 
        | Int,Balance -> "(int)(address(this).balance)"
        | Int,MsgValue -> "(int)(msg.value)"
        | t,Var(_, name) -> name
        | ContractAddress,This -> "this"
        | t,Value (v) -> pp_value t v
        | Int,(Plus(e1,e2)) -> "(" ^ pp_expression Int e1 ^ " + " ^ pp_expression Int e2 ^ ")"
        | Int,(Minus(e1,e2)) -> "(" ^ pp_expression Int e1 ^ " - " ^ pp_expression Int e2 ^ ")"
        | _,(Mult(e1,e2))  -> "(" ^ pp_expression Int e1 ^ " * " ^ pp_expression Int e2 ^ ")"
        | t,(CondExpr(b,e1,e2)) -> "(" ^ pp_expression Bool b ^ " ? " ^ pp_expression
        t e1 ^ " : " ^ pp_expression t e2 ^ ")"
        | _,(Geq(e1,e2)) -> "(" ^ pp_expression Int e1 ^ " >= " ^ pp_expression Int e2 ^ ")"
        | _,(Gt(e1,e2)) -> "(" ^ pp_expression Int e1 ^ " > " ^ pp_expression Int e2 ^ ")"
        | _,(Eq(t,e1,e2)) -> "(" ^ pp_expression t e1 ^ " == " ^ pp_expression t e2 ^ ")"
        | _,(And(e1,e2)) -> "(" ^ pp_expression Bool e1 ^ " && " ^ pp_expression Bool e2 ^ ")"
        | _,(Or(e1,e2)) -> "(" ^ pp_expression Bool e1 ^ " || " ^ pp_expression Bool e2 ^ ")"
        | _,(Not e) -> "(!" ^ pp_expression Bool e ^ ")" 
        | _,(Call(c,s,exprl,value)) -> pp_opt (fun e -> "(" ^ pp_expression ContractAddress
        e ^ ").") c ^ s ^ pp_opt (fun e -> ".value((uint)(" ^ pp_expression Int e ^ "))")
        value ^ "(" ^ (String.concat ", " (string_list_of_expression
        exprl)) ^ ")" 
        | _,(Symbol s) -> symb_array ^ "[" ^ "'" ^ s ^ "'" ^ "]"

 and string_list_of_expression : type a. a expression_list -> string list =
    function
        | ExprCons ((t,e), tl) -> [(pp_expression t e)]@(string_list_of_expression tl) 
        | ExprNil -> []
       
(*type declaration = Declaration : 'a var * ('a expression option) ->  declaration*)
let pp_declaration : declaration -> string =
    function 
        Declaration ((t,name),e) -> 
            let equals = pp_opt (fun expr -> " = " ^ pp_expression t expr) e in
            match t,e with
            | ContractAddress,(Some (Value (SmartCalculus.Contract s))) -> s ^ " " ^ name ^ ";"
            | _,_ -> (pp_typename t) ^ " " ^ name ^ equals ^ ";"


let rec pp_statement : statement -> string  = 
    function
        | IfElse (b, stm1, stm2) -> "if (" ^ pp_expression Bool b ^ "){"  ^ nl ^
        (pp_statement stm1) ^ nl ^ "}" ^ nl ^ "else {" ^ nl ^ pp_statement stm2
        ^ nl ^ "}"
        | Assignment ((t,name), e) -> pp_expression t (Var(t,name)) ^ " = " ^ pp_expression t e ^ ";"
        | Sequence (stm1, stm2) -> pp_statement stm1 ^  nl ^ pp_statement stm2
        | Empty -> ""

let pp_storage =
    function
        | Storage -> "storage "
        | Memory -> "memory "
        | Calldata -> "calldata "

let rec string_list_of_params : type a. a parameters -> string list=
    function
        | PNil -> []
        | PCons(((t, name), opt),tl) -> [pp_typename t ^ " " ^ (pp_opt pp_storage opt) ^ name]@(string_list_of_params tl)


let rec pp_params : type a. a parameters -> string =
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
let rec pp_funct : any_funct -> string =
    function 
        Function ((name, params,(outtype,storage)), view, vis,  stm, return) ->
            "function " ^ 
            name ^ 
            pp_params params ^ " " ^ 
            (String.concat " " (List.map pp_view view)) ^ 
            (String.concat " " (List.map pp_visibility vis)) ^ 
            "returns (" ^ pp_typename outtype ^ " " ^ (pp_opt pp_storage storage) ^
            "){" ^ nl ^ pp_statement stm ^ nl ^
            "return " ^ pp_expression outtype return ^ ";" ^ nl ^ "}" 

let pp_constructor : statement -> string =
    fun s ->
    "constructor() public{" ^ nl ^ pp_statement s ^ "}"
let rec pp_contract : contract_ast -> string =
    function 
    Contract (name, constructor, fields, meths) ->  "contract " ^ name ^ " {" ^ nl ^
    (match constructor with None -> "" | _ -> declare_simbols ^ nl) ^
    (String.concat nl (List.map pp_declaration fields)) ^ nl ^ pp_opt pp_constructor constructor ^ nl ^ (String.concat nl (List.map
    pp_funct meths)) ^ nl ^ "}"

let rec pp_actor : any_actor -> string =
    function
        | ActCon c -> pp_contract (pars_contract c)
        | ActHum h -> raise CompilationFail

let rec pp_ast : ast -> string =
    function cl -> "pragma solidity 0.5.11;" ^ nl ^ String.concat nl (List.map pp_contract cl)
;;
let outstr = (pp_ast (pars_configuration (Grammar.conf)));;
print_string outstr;;
let out_channel = open_out "out.sol";;
Printf.fprintf out_channel "%s" outstr;
