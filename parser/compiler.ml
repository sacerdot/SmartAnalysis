open Grammar
open SmartCalculus
open ParserCombinator

type ast =
    | Empty
    | Declaration of string * string * expression
    | Function of string * parameters * string * string * ast * ast
    (*name,parameters,visibility,view,outputs,stm*) 
and expression =
    | Leaf of string
    | BinOp of string * expression * expression
    | UnaryOp of string * expression
and parameters = (string * string) list

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
    
let comp_funct : any_method_decl -> ast = 
    function AnyMethodDecl((tagret, taglist, name),(parameters, stmlist, retexpr))
    -> Function 
        (name,
        (get_parameters (AnyTagList taglist) parameters),
        "",
        "",
        Empty,
        Empty)

let comp_decl :  assign -> ast =
    function Let ((t,name),v) -> Declaration((string_of_anytag (AnyTag t)),name,
    comp_expr (AnyExpr(t,(Value v))))
        
    (*
let rec inorder_visit : ('a -> unit) -> 'a tree -> unit  = 
    fun f t -> 
        match t with 
        | Node (s,(h::tl))-> (f s; inorder_visit f h; List.iter (inorder_visit f) tl)
        | Node (s,_) -> f s
        | Empty -> ()

let expr1 = (AnyExpr(Int,Minus(Value(8))));;
inorder_visit print_string (comp_expr expr1)
*)
