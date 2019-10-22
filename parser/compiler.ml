open Grammar
open SmartCalculus
open ParserCombinator

type expression =
    | Leaf of string
    | BinOp of string * expression * expression
    | UnaryOp of string * expression
    | Call of string * (expression list)
type parameters = (string * string) list
type declaration = Declaration of string * string * expression
type statement = 
    | IfElse of expression * statement * statement 
    | Assignment of string * expression 
    | Sequence of statement * statement
    | StmList of statement list
type funct =  Function of string * parameters * string * string * string * statement *
    expression
    (*name,parameters,visibility,view,outtype,stm,return*) 

type ast =
    | Empty
    | Contract of string * (declaration list) * (funct list) 
exception CompilationFail

let get_varname : 'a ident -> string = function (_, name) -> name
   
let rec const_expr =
    function
        | Numeric n -> Leaf (string_of_int n)
        | Symbolic s -> Leaf s (*Come fare???*)


let rec string_cast: any_expr -> string =
    fun (AnyExpr(t,e)) ->
        match e with
        |  Value v -> 
            (match t with 
            | Bool -> string_of_bool v
            | Int -> string_of_int v
            | String -> v
            | ContractAddress -> (match v with Contract s -> s)
            | HumanAddress -> (match v with Human s -> s))
        | _ -> raise CompilationFail

let string_of_anytag : any_tag -> string = 
    fun (AnyTag t) ->
        match t with
        | Int -> "int"
        | Bool -> "boolean"
        | String -> "string"
        | _ -> "address" (*????*)
 
let rec comp_expr = 
    fun (AnyExpr(t,e)) ->
        match t,e with
         | _,(Var v) -> Leaf (get_varname v)
         | _,Fail -> Leaf "fail"
         | _,(Field f) -> Leaf (get_varname f)
         | _,(Value v) -> Leaf (string_cast (AnyExpr(t,e)))
         | Int,_ -> int_expr e 
         | Bool,_ -> bool_expr e
         | ContractAddress,This -> Leaf "this"
         | _,_ -> raise CompilationFail
and int_expr : int expr -> expression =
    function
        | Plus (e1, e2) -> BinOp ("+",(int_expr e1),(int_expr e2))
        | Mult (c, e) -> BinOp ("+",(const_expr c),(int_expr e))
        | Minus e -> UnaryOp ("-", (int_expr e))
        | Max (e1,e2) -> BinOp ("+",(int_expr e1),(int_expr e2)) (*Capire
        come chiamare max*)
        | Symbol s -> Leaf s (*Boh*)
        | e -> comp_expr (AnyExpr(Int,e))
and bool_expr : bool expr -> expression =
    function
        | Geq (e1, e2) -> BinOp (">=",(int_expr e1),(int_expr e2))
        | Gt (e1, e2) -> BinOp (">",(int_expr e1),(int_expr e2))
        | Eq (t, e1, e2) -> BinOp ("==", (comp_expr (AnyExpr(t, e1))),(comp_expr
        (AnyExpr(t, e2))))
        | And (e1, e2) -> BinOp ("&&",(bool_expr e1),(bool_expr e2))
        | Or (e1, e2) -> BinOp ("||",(bool_expr e1),(bool_expr e2))
        | Not e -> UnaryOp ("!", (bool_expr e))
        | e -> comp_expr (AnyExpr(Bool,e))

let comp_decl  =
    function Let ((t,name),v) -> Declaration((string_of_anytag (AnyTag t)),name,
    comp_expr (AnyExpr(t,(Value v))))

let rec map_expr_list : type c. (any_expr -> 'a) -> c tag_list -> c expr_list-> 'a list =
    fun f tlist elist ->
        match tlist,elist with 
        | (TCons(t,ttail)),(ECons(e,etail)) -> (f (AnyExpr(t,e)))::(map_expr_list
        f ttail etail)
        | _,_-> raise CompilationFail
(*TODO: Verify function type*)
let comp_rhs : any_rhs -> expression =
    fun (AnyRhs (tag,rhs)) ->
        match rhs with
        | Expr e -> comp_expr (AnyExpr(tag,e))
        | Call (opt, (funtag, tags, name), (elist)) -> Call (name,(map_expr_list comp_expr tags elist))


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
 
let rec comp_stm : stm -> statement = 
    function 
        | Assign((tag, name),rhs) -> Assignment ((get_varname (tag,name)),(comp_rhs(AnyRhs(tag,rhs))))
        | IfThenElse(expr,stm1,stm2) -> IfElse ((bool_expr expr),(comp_stm
        stm1),(comp_stm stm2))
        | Comp (stm1,stm2) -> Sequence((comp_stm stm1),(comp_stm stm2))
        | _ -> raise CompilationFail

let rec comp_stmlist  = 
    fun stms stml ->
        match stml with 
        | (StmList l) -> (
            match stms with  
            | [] -> StmList l
            | h::tl -> comp_stmlist tl (StmList (l@[(comp_stm h)])))
        | _ -> raise CompilationFail

let comp_funct = 
    function AnyMethodDecl((tagret, taglist, name),(parameters, stmlist, retexpr))
    -> Function 
        (name,
        (get_parameters (AnyTagList taglist) parameters),
        "",
        "",
        (string_of_anytag (AnyTag tagret)),
        (comp_stmlist stmlist (StmList [])),
        (comp_expr (AnyExpr(tagret,retexpr))))

let comp_contract : a_contract -> ast =
    function (add, meths, fields) ->
        match add with
        | Contract name -> Contract(name, (List.map comp_decl
    fields), (List.map comp_funct meths))
        | _ -> raise CompilationFail

(*Serialization*)
let rec pp_expression : expression -> string =
    function 
        | Leaf s -> s
        | BinOp (s,e1,e2) -> "(" ^ (pp_expression e1) ^ ")" ^ s ^ "(" ^ (pp_expression e2) ^ ")"
        | UnaryOp (s,e) -> s ^ "(" ^ (pp_expression e) ^ ")"
        | Call (s, l) -> s ^ "(" ^ (String.concat ", " (List.map pp_expression l)) ^ ")"

let pp_declaration : declaration -> string =
    function Declaration (t,name,e) -> t ^ " " ^ name ^ " = " ^ (pp_expression e) ^ ";"

let rec pp_statement : statement -> string  = 
    function
        | IfElse (be, stm1, stm2) -> "if (" ^ pp_expression be ^ "){ " ^
        (pp_statement stm1) ^ " } else { " ^ pp_statement stm2 ^ " }"
        | Assignment (s, e) -> s ^ " = " ^ pp_expression e
        | Sequence (stm1, stm2) -> pp_statement stm1 ^ "; " ^ pp_statement stm2
        | StmList (stml) -> "{" ^ (String.concat "} {" (List.map pp_statement stml)) ^ "}"

let rec pp_params : parameters -> string =
    function l -> "(" ^ (String.concat ", " (List.map (fun (s1,s2) -> s1 ^ " " ^
    s2) l)) ^ ")"

let rec pp_funct : funct -> string =
    function Function (name, params, vis, view, outtype, stm, return) ->
        "function " ^ name ^ pp_params params ^ " " ^ vis ^ " " ^ view ^ "
        returns (" ^ outtype ^ ")" ^ "{" ^ pp_statement stm ^ "return " ^
        pp_expression return ^ ";}" 

