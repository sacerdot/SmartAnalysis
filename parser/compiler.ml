open Grammar
open SmartCalculus
open ParserCombinator

let nl = "\n"
type expression =
    | Leaf of string
    | BinOp of string * expression * expression
    | UnOp of string * expression
    | TerOp of (string*string) * expression * expression * expression
    | Call of string * (expression list)
type parameters = (string * string) list
type declaration = Declaration of string * string * expression
type statement = 
    | IfElse of expression * statement * statement 
    | Assignment of string * expression 
    | Sequence of statement * statement
    | StmList of statement list

(*name,parameters,visibility,view,outtype,stm,return*) 
type funct =  Function of string * parameters * string * string option * string * statement *
    expression
type ast =
    | Empty
    | Contract of string * (declaration list) * (funct list) 

exception CompilationFail

let get_varname : 'a ident -> string = function (_, name) -> name
   
let rec const_expr =
    function
        | Numeric n -> Leaf (string_of_int n)
        | Symbolic s -> Leaf ("'" ^ s ^ "'") (*Come fare???*)


let rec string_cast: any_expr -> string =
    fun (AnyExpr(t,e)) ->
        match e with
        |  Value v -> 
            (match t with 
            | Bool -> string_of_bool v
            | Int -> string_of_int v
            | String -> "'" ^ v ^ "'"
            | ContractAddress -> (match v with Contract s -> s)
            | HumanAddress -> (match v with Human s -> s))
        | _ -> raise CompilationFail

let string_of_anytag : any_tag -> string = 
    fun (AnyTag t) ->
        match t with
        | Int -> "int"
        | Bool -> "bool"
        | String -> "string"
        | _ -> "address" (*????*)
 
let rec pars_expr = 
    fun (AnyExpr(t,e)) ->
        match t,e with
         | _,(Var v) -> Leaf (get_varname v)
         | _,Fail -> Leaf "fail"
         | _,(Field f) -> Leaf (get_varname f)
         | _,(Value v) -> Leaf (string_cast (AnyExpr(t,e)))
         | Int,_ -> int_expr e 
         | Bool,_ -> bool_expr e
         | ContractAddress,This -> Leaf "this"
and int_expr : int expr -> expression =
    function
        | Plus (e1, e2) -> BinOp ("+",(int_expr e1),(int_expr e2))
        | Mult (c, e) -> BinOp ("+",(const_expr c),(int_expr e))
        | Minus e -> UnOp ("-", (int_expr e))
        | Max (e1,e2) -> TerOp(("?", ":"), (BinOp(">",(int_expr e1),(int_expr e2))), (int_expr e1), (int_expr e2))
        | Symbol s -> Leaf ("'" ^ s ^ "'") (*Boh*)
        | e -> pars_expr (AnyExpr(Int,e))
and bool_expr : bool expr -> expression =
    function
        | Geq (e1, e2) -> BinOp (">=",(int_expr e1),(int_expr e2))
        | Gt (e1, e2) -> BinOp (">",(int_expr e1),(int_expr e2))
        | Eq (t, e1, e2) -> BinOp ("==", (pars_expr (AnyExpr(t, e1))),(pars_expr
        (AnyExpr(t, e2))))
        | And (e1, e2) -> BinOp ("&&",(bool_expr e1),(bool_expr e2))
        | Or (e1, e2) -> BinOp ("||",(bool_expr e1),(bool_expr e2))
        | Not e -> UnOp ("!", (bool_expr e))
        | e -> pars_expr (AnyExpr(Bool,e))

let pars_decl  =
    function Let ((t,name),v) -> Declaration((string_of_anytag (AnyTag t)),name,
    pars_expr (AnyExpr(t,(Value v))))

let rec map_expr_list : type c. (any_expr -> 'a) -> c tag_list -> c expr_list-> 'a list =
    fun f tlist elist ->
        match tlist,elist with 
        | (TCons(t,ttail)),(ECons(e,etail)) -> (map_expr_list
        f ttail etail)@[f (AnyExpr(t,e))]
        | TNil,ENil -> []
let pars_rhs : any_rhs -> expression =
    fun (AnyRhs (tag,rhs)) ->
        match rhs with
        | Expr e -> pars_expr (AnyExpr(tag,e))
        | Call (opt, (funtag, tags, name), (elist)) -> Call (name,(map_expr_list pars_expr tags elist))


let rec get_parameters : type a. any_tag_list -> a var_list -> parameters = 
    fun tagl parlist ->
        match (tagl,parlist) with
        | (AnyTagList(TCons(taghead,tagtail))),(VCons((tagvar,var),vartail)) -> 
            (match eq_tag taghead tagvar with
            | Some _ -> 
                (get_parameters (AnyTagList tagtail)
                vartail)@[(string_of_anytag(AnyTag taghead)),var]
            | None -> raise CompilationFail)
        | _,_ -> []
 
let rec pars_stm : stm -> statement = 
    function 
        | Assign((tag, name),rhs) -> Assignment ((get_varname (tag,name)),(pars_rhs(AnyRhs(tag,rhs))))
        | IfThenElse(expr,stm1,stm2) -> IfElse ((bool_expr expr),(pars_stm
        stm1),(pars_stm stm2))
        | Comp (stm1,stm2) -> Sequence((pars_stm stm1),(pars_stm stm2))
        | _ -> raise CompilationFail

let rec pars_stmlist  = 
    fun stms stml ->
        match stml with 
        | (StmList l) -> (
            match stms with  
            | [] -> StmList l
            | h::tl -> pars_stmlist tl (StmList (l@[(pars_stm h)])))
        | _ -> raise CompilationFail

let pars_funct = 
    function AnyMethodDecl((tagret, taglist, name),(parameters, stmlist, retexpr))
    -> Function 
        (name,
        (get_parameters (AnyTagList taglist) parameters),
        "public",
        None,
        (string_of_anytag (AnyTag tagret)),
        (pars_stmlist stmlist (StmList [])),
        (pars_expr (AnyExpr(tagret,retexpr))))

let pars_contract : a_contract -> ast =
    function (add, meths, fields) ->
        match add with
        | Contract name -> Contract(name, (List.map pars_decl
    fields), (List.map pars_funct meths))

(*From ast to string*)
let rec pp_expression : expression -> string =
    function 
        | Leaf s -> s
        | BinOp (s,e1,e2) -> "(" ^ (pp_expression e1) ^ " " ^ s ^ " " ^ (pp_expression e2) ^ ")"
        | UnOp (s,e) ->  "(" ^ s  ^ (pp_expression e) ^ ")"
        | TerOp((s1,s2),e1,e2,e3) -> "(" ^ (pp_expression e1) ^ " " ^ s1 ^ " " ^
        (pp_expression e2) ^ " " ^ s2 ^ " " ^ (pp_expression e3) ^ ")"
        | Call (s, l) ->  s ^ "(" ^(String.concat ", " (List.map pp_expression l)) ^ ")"

let pp_declaration : declaration -> string =
    function Declaration (t,name,e) -> t ^ " " ^ name ^ " = " ^ (pp_expression
    e) ^ ";"


let rec pp_statement : statement -> string  = 
    function
        | IfElse (be, stm1, stm2) -> "if (" ^ pp_expression be ^ "){"  ^ nl ^
        (pp_statement stm1) ^ nl ^ "}" ^ nl ^ "else {" ^ nl ^ pp_statement stm2
        ^ nl ^ "}"
        | Assignment (s, e) -> s ^ " = " ^ pp_expression e ^ ";"
        | Sequence (stm1, stm2) -> pp_statement stm1 ^  nl ^ pp_statement stm2
        | StmList (stml) -> String.concat nl (List.map pp_statement stml)

let rec pp_params : parameters -> string =
    function l -> "(" ^ (String.concat ", " (List.map (fun (s1,s2) -> s1 ^ " " ^
    s2) l)) ^ ")"

let rec inmem_params : parameters -> parameters =
    function
        ("string",n)::tl -> [("string memory",n)]@(inmem_params tl)
        | h::tl -> [h]@(inmem_params tl)
        | [] -> []
let pp_opt = function Some s -> s ^ " " | None -> ""

let rec pp_funct : funct -> string =
    function 
        Function (name, params, vis, view, outtype, stm, return) ->
        "function " ^ name ^ pp_params (inmem_params params) ^ " " ^ vis ^ " " ^
        (pp_opt view) ^ "returns (" ^ outtype ^ ")" ^ "{" ^ nl ^ pp_statement stm ^ nl ^ "return " ^
        pp_expression return ^ ";" ^ nl ^ "}" 

let rec pp_contract : ast -> string =
    function 
    | Empty -> ""
    | Contract (name, fields, meths) -> "pragma solidity 0.5.11;" ^ nl ^ "contract " ^ name ^ " {" ^ nl ^ (String.concat
    nl (List.map pp_declaration fields)) ^ nl ^ (String.concat nl (List.map
    pp_funct meths)) ^ nl ^ "}"

let rec pp_actor : any_actor -> string =
    fun a ->
        match a with
        | ActCon c -> pp_contract (pars_contract c)
        | ActHum h -> raise CompilationFail
;;
print_string (pp_actor Grammar.actor);;
let out_channel = open_out "out.sol";;
Printf.fprintf out_channel "%s" (pp_actor Grammar.actor);
