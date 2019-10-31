open Grammar
open SmartCalculus
open ParserCombinator

let nl = "\n"
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
    | This : (contract address) expression
    | Plus : int expression * int expression -> int expression
    | Minus : int expression * int expression -> int expression
    | Mult : int expression * int expression -> int expression
    | Geq : int expression * int expression -> bool expression
    | Gt : int expression * int expression -> bool expression
    | Eq : 'a typename * 'a expression * 'a expression -> bool expression
    | And : bool expression * bool expression -> bool expression
    | Or : bool expression * bool expression -> bool expression
    | Not : bool expression -> bool expression
    | CondExpr : bool expression * 'a expression * 'a expression -> 'a expression
    | Call : string * 'a expression_list -> 'b expression
and _ expression_list =
   ExprNil : unit expression_list
 | ExprCons : ('a typename * 'a expression) * 'b expression_list -> ('a * 'b) expression_list
type _ type_list = TNil: unit type_list | TCons: ('a typename * storage option) * 'b type_list-> ('a * 'b) type_list  
type _ parameters = PNil: unit parameters | PCons: ('a var * storage option) * 'b parameters -> ('a * 'b) parameters  
type declaration = Declaration : 'a var * ('a expression option) -> declaration
type statement = 
    | Empty
    | IfElse : bool expression * statement * statement -> statement
    | Assignment : 'a var * 'a expression -> statement
    | Sequence : statement * statement -> statement
type view = View | Pure | Payable
type visibility = External | Public | Internal | Private
(*name,parameters,visibility,view,outtype,stm,return*) 
type any_funct =  Function: string * 'a parameters * view list * visibility 
    list * 'b type_list * statement * 'b expression_list -> any_funct
type contract_ast = Contract of string * (declaration list) * (any_funct list) 
type ast = contract_ast list
exception CompilationFail

let get_typename : type a. a tag -> a typename  = 
    function
        | SmartCalculus.Int -> Int
        | SmartCalculus.String -> String
        | SmartCalculus.Bool -> Bool
        | SmartCalculus.ContractAddress -> ContractAddress
        | _ -> raise CompilationFail

let rec const_expression =
    function
        | Numeric n -> Value n
        | _ -> raise Fail
        (*
        | Symbolic s -> Leaf ("'" ^ s ^ "'") *)(*Come fare???*)

let rec base_expression : type a. a expr -> a expression = 
    function
        | Var(tag,e) -> Var((get_typename tag),e)
        | Field(tag,e) -> Var((get_typename tag),e)
        | Value v -> Value v
        | _ -> raise Fail
and int_expression : int SmartCalculus.expr -> int expression =
    function
        | Plus ((Minus e1),(e2)) -> Minus ((int_expression e2),(int_expression e1))
        | Plus ((e1),(Minus e2)) -> Minus ((int_expression e1),(int_expression e2))
        | Plus (e1, e2) -> Plus ((int_expression e1),(int_expression e2))
        | Mult (c, e) -> Mult ((const_expression c),(int_expression e))
        | Minus (Value v) -> Value ((-1) * v)
        | Minus e ->  Mult ((const_expression (Numeric (-1))),(int_expression e))
        | Max (e1,e2) -> CondExpr((bool_expression (Gt(e1,e2))), (int_expression e1), (int_expression e2))
        (*| Symbol s -> Leaf ("'" ^ s ^ "'") (*Boh*) *)
        | e -> base_expression e
and bool_expression : bool SmartCalculus.expr -> bool expression =
    function
        | Geq (e1, e2) -> Geq ((int_expression e1),(int_expression e2))
        | Gt (e1, e2) -> Gt ((int_expression e1),(int_expression e2))
        | Eq (t, e1, e2) -> Eq ((get_typename t),(pars_expression (get_typename
        t) e1),(pars_expression (get_typename t) e2))
        | And (e1, e2) -> And ((bool_expression e1),(bool_expression e2))
        | Or (e1, e2) -> Or ((bool_expression e1),(bool_expression e2))
        | Not e -> Not (bool_expression e)
        | e -> base_expression e
and contract_expression : (contract address) expr -> (contract address) expression = 
    function 
        | SmartCalculus.This -> This
        | e -> base_expression e
and pars_expression: type a. a typename -> a expr -> a expression =
    function
        | Int -> int_expression
        | String -> base_expression
        | Bool -> bool_expression
        | ContractAddress -> contract_expression

let pars_decl  =
    function Let ((t,name),v) -> Declaration(((get_typename t),name),
     (Some (pars_expression (get_typename t) (Value v))))

let rec map_expression_list : type  b. b tag_list -> b expr_list -> b expression_list =
    fun tlist elist ->
        match tlist,elist with 
        | (TCons(t,ttail)),(ECons(e,etail)) -> (ExprCons (((get_typename t),(pars_expression (get_typename t) e)),(map_expression_list ttail etail)))
        | TNil,ENil -> ExprNil

let pars_rhs : 'a typename -> 'a rhs -> 'a expression =
    fun t rhs ->
        match rhs with  
        | Expr e -> pars_expression t e 
        | Call (opt, (funtag, tags, name), elist) -> Call (name,(map_expression_list tags elist))

let get_storage: type a. a typename -> storage option =
        function
        | String -> Some Memory
        | _ ->  None
let rec get_parameters : type a. a var_list -> a parameters = 
    fun varlist ->
        match varlist with
        | VCons((tagvar,var),vartail) ->
            let t = get_typename tagvar
            in PCons(((t,var), (get_storage t)),(get_parameters vartail))
        | VNil -> PNil

let rec pars_stm : stm -> statement = 
    function 
        | Assign((tag, name),rhs) -> Assignment (((get_typename
        tag),name),pars_rhs (get_typename tag) rhs)
        | IfThenElse(expression,stm1,stm2) -> IfElse ((bool_expression expression),(pars_stm
        stm1),(pars_stm stm2))
        | Comp (stm1,stm2) -> Sequence((pars_stm stm1),(pars_stm stm2))
        | _ -> raise CompilationFail

let rec pars_stmlist : stm list ->  statement  = 
    fun stml ->
        match stml with
        | h::[] -> pars_stm h
        | h::tl -> Sequence((pars_stm h),(pars_stmlist tl))
        | [] -> Empty

let pars_funct = 
    function AnyMethodDecl((tagret, taglist, name),(parameters, stmlist, retexpr))
    -> let t = (get_typename tagret) in 
    Function 
        (name,
        (get_parameters parameters),
        [],
        [Public],
        TCons((t,(get_storage t)),TNil),
        (pars_stmlist stmlist ),
        ExprCons((t,(pars_expression t retexpr)),ExprNil))

let pars_contract : a_contract -> contract_ast =
    function (add, meths, fields) ->
        match add with
        | Contract name -> Contract(name, (List.map pars_decl
    fields), (List.map pars_funct meths))

let rec pars_contract_list : a_contract list -> ast = 
    function 
        | [] -> []
        | h::tl -> [(pars_contract h)]@(pars_contract_list tl)
        
let rec pars_configuration : configuration -> ast =
    function
        {contracts = cl; _} -> pars_contract_list cl

(*From ast to string*)
let pp_opt =
    fun f opt ->
        match opt with
        | Some o -> (f o) 
        | None -> ""

let pp_typename : type a. a typename -> string =
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
        | _,Var(_, name) -> name
        | _,This -> "this"
        | t,Value (v) -> pp_value t v
        | _,(Plus(e1,e2)) -> "(" ^ pp_expression Int e1 ^ " + " ^ pp_expression Int e2 ^ ")"
        | _,(Minus(e1,e2)) -> "(" ^ pp_expression Int e1 ^ " - " ^ pp_expression Int e2 ^ ")"
        | _,(Mult(e1,e2))  -> "(" ^ pp_expression Int e1 ^ " * " ^ pp_expression Int e2 ^ ")"
        | t,(CondExpr(b,e1,e2)) -> "(" ^ pp_expression Bool b ^ " ? " ^ pp_expression
        t e1 ^ " : " ^ pp_expression t e2 ^ ")"
        | _,(Geq(e1,e2)) -> "(" ^ pp_expression Int e1 ^ " >= " ^ pp_expression Int e2 ^ ")"
        | _,(Gt(e1,e2)) -> "(" ^ pp_expression Int e1 ^ " > " ^ pp_expression Int e2 ^ ")"
        | _,(Eq(t,e1,e2)) -> "(" ^ pp_expression t e1 ^ " == " ^ pp_expression t e2 ^ ")"
        | _,(And(e1,e2)) -> "(" ^ pp_expression Bool e1 ^ " && " ^ pp_expression Bool e2 ^ ")"
        | _,(Or(e1,e2)) -> "(" ^ pp_expression Bool e1 ^ " || " ^ pp_expression Bool e2 ^ ")"
        | _,(Not e) -> "(!" ^ pp_expression Bool e ^ ")" 
        | _,(Call(s,exprl)) -> s ^ "(" ^ (String.concat ", " (string_list_of_expression exprl)) ^ ")"
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
        | Assignment ((t,name), e) -> name ^ " = " ^ pp_expression t e ^ ";"
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

let rec string_list_of_type : type a. a type_list -> string list=
    function
        | TNil -> []
        | TCons((h,_),tl) -> [pp_typename h]@(string_list_of_type tl)


let rec pp_funct : any_funct -> string =
    function 
        Function (name, params, view, vis, outtype, stm, return) ->
            "function " ^ 
            name ^ 
            pp_params params ^ " " ^ 
            (String.concat " " (List.map pp_view view)) ^ 
            (String.concat " " (List.map pp_visibility vis)) ^ 
            "returns (" ^ (String.concat " " (string_list_of_type outtype)) ^
            "){" ^ nl ^ pp_statement stm ^ nl ^
            "return " ^ (String.concat " " (string_list_of_expression return)) ^ ";" ^ nl ^ "}" 

let rec pp_contract : contract_ast -> string =
    function 
    Contract (name, fields, meths) ->  "contract " ^ name ^ " {" ^ nl ^ (String.concat
    nl (List.map pp_declaration fields)) ^ nl ^ (String.concat nl (List.map
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
