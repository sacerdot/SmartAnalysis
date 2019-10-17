open SmartCalculus

open ParserCombinator
open Genlex

(*Expression *)
let plus e1 e2 = 
    match e1,e2 with
    | AnyExpr(Int,v1),AnyExpr(Int,v2) -> AnyExpr(Int,Plus(v1,v2))
    | _ -> raise Fail
  
let minus e = match e with AnyExpr(Int,e) -> AnyExpr(Int,Minus(e)) | _ -> raise Fail

let subtract e1 e2 = plus e1 (minus e2)

let mult c e = 
    match c,e with 
    | AnyExpr(Int,Value v),AnyExpr(Int,expr) -> AnyExpr(Int,Mult(Numeric(v),expr)) 
    | AnyExpr(Int,(Symbol v)),AnyExpr(Int,expr) -> AnyExpr(Int,Mult(Symbolic(v),expr)) 
    | _-> raise Fail

let max e1 e2 =
   match e1,e2 with
    | AnyExpr(Int,v1),AnyExpr(Int,v2) -> AnyExpr(Int,Max(v1,v2))
    | _ -> raise Fail
  

let gt e1 e2 =
    match e1,e2 with
    | AnyExpr(Int,v1),AnyExpr(Int,v2) -> AnyExpr(Bool,Gt(v1,v2))
    | _ -> raise Fail

let ge e1 e2 =
    match e1,e2 with
    | AnyExpr(Int,v1),AnyExpr(Int,v2) -> AnyExpr(Bool,Geq(v1,v2))
    | _ -> raise Fail

let eq e1 e2 = 
    match e1,e2 with
    | AnyExpr(t1,v1),AnyExpr(t2,v2) ->
            (match eq_tag t1 t2 with
            | Some Refl -> AnyExpr(Bool,Eq(t1,v1,v2))
            | _ -> raise Fail)

let lt e1 e2 = gt e2 e1

let le e1 e2 = ge e2 e1

let andb e1 e2 =
    match e1,e2 with
    | AnyExpr(Bool,v1),AnyExpr(Bool,v2) -> AnyExpr(Bool,And(v1,v2))
    | _ -> raise Fail


let orb e1 e2 =
    match e1,e2 with
    | AnyExpr(Bool,v1),AnyExpr(Bool,v2) -> AnyExpr(Bool,Or(v1,v2))
    | _ -> raise Fail


let notb e = 
    match e with
    | AnyExpr(Bool, v) -> AnyExpr(Bool, Not(v))
    | _ -> raise Fail

let scd_notb _ e = notb e

let neq e1 e2 = notb (eq e1 e2)


let varname s t = match s with | (Ident x) :: tl -> tl,x,t | _ -> raise Fail

let symbol_pars s t = 
    match s with
    | (Ident var)::tl -> tl,AnyExpr(Int,Symbol(var)),t
    | _ -> raise Fail

let var_pars s t = 
    match s,t with
    | (Ident var)::tl,(tbl,_) -> tl,getopt (get_field tbl var),t
    | _ -> raise Fail

let value_pars s t = (junk s),(value (List.hd s)),t

let fail_pars perm =
    const (Kwd "fail") (fun _ -> if perm then AnyExpr(Int,Fail) else raise Fail)
(*variable | value | fail*)
let base s (tbl,act) =
    choice_list[
        comb_parser var_pars (fun (AnyField(tag,name)) -> AnyExpr(tag,Var(tag,name)));
        value_pars;
        fail_pars act;
    ] s (tbl,act)
(* Int Expression
 * atomic_int_expr :=
    base Int | "-" atomic_int_expr | varname | "(" int_expr ")" | "max" int_expr
    int_expr | string
 * int_expr := atomic_int_expr ?cont_int_expr
 * cont_int_expr ::= eoexpr | "+" int_expr | "*" int_expr | "-" int_expr |
 *)
let rec atomic_int_expr s = 
 choice_list [
   comb_parser base (fun expr -> AnyExpr(Int,(check_type Int expr)));
   concat (kwd "-") atomic_int_expr (fun _ -> minus) ;
   concat (concat (kwd "(") int_expr scd) (kwd ")") fst ;
   concat (concat (kwd "max") int_expr scd) int_expr max;
   symbol_pars;
 ] s
and int_expr s =
 concat atomic_int_expr (option cont_int_expr) (fun x f -> match f with Some funct
 -> funct x | _ -> x) s
and binop s =
 choice_list [
  const (Kwd "+") (fun _ -> plus) ;
  const (Kwd "*") (fun _ -> mult) ;
  const (Kwd "-") (fun _ -> subtract)
 ] s
and cont_int_expr s = concat binop int_expr (fun f x -> f x) s

 (* Bool Expression
 * atomic_bool_expr :=
    bool | int_expr ">" int_expr  | int_expr ">=" int_expr  | int_expr "<"
    int_expr | int_expr "<=" int_expr | expr "==" expr | varname | "(" bool_expr
    ")" | "!" bool_expr
 * bool_expr := atomic_int_expr ?cont_int_expr
 * cont_bool_expr ::=  "&&" bool_expr | "||" bool_expr 
 *)
let rec atomic_bool_expr s =
    choice_list[
        comb_parser base (fun expr -> AnyExpr(Bool,(check_type Bool expr)));
        concat (concat (kwd "(") bool_expr scd) (kwd ")") fst ;
        concat (kwd "!") atomic_bool_expr (fun _ -> notb) ;
        concat int_expr (concat cmpop int_expr (fun f x -> f x)) (fun x f -> f x);
 ] s
 and cmpop s =  
    choice_list [
      const (Kwd ">") (fun _ -> gt) ;
      const (Kwd ">=") (fun _ -> ge) ;
      const (Kwd "==") (fun _ -> eq); 
      const (Kwd "!=") (fun _ -> neq);
      const (Kwd "<") (fun _ -> lt);
      const (Kwd "<=") (fun _ -> le) ;
    ] s
and bool_expr s =
 concat atomic_bool_expr (option cont_bool_expr) (fun x f -> match f with Some y ->
     y x | _ -> x) s
and bin_bool_op s =
 choice_list [
  const (Kwd "&&") (fun _ -> andb) ;
  const (Kwd "||") (fun _ -> orb) ;
 ] s
and cont_bool_expr s = concat bin_bool_op bool_expr (fun f x -> f x) s

let expr_pars s = choice_list[int_expr; bool_expr; base] s

let type_pars =
    let tag_pars str tag = const (Kwd str) (fun _ -> AnyTag tag) in
    choice_list[
        tag_pars "int" Int;
        tag_pars "string" String;
        tag_pars "bool" Bool;
        tag_pars "Contract" ContractAddress;
        tag_pars "Human" HumanAddress;
]

let field_pars = concat type_pars varname (fun (AnyTag t) v -> AnyField (t,v))

let field_add_pars s t = 
    let (ns,field,(tbl,act)) = field_pars s t in 
    ns,field,((add_field_to_table tbl field false),act)

let store_pars =
    let assign = fun f exp -> 
        match f with 
            | AnyField(t1,name) -> match check_type t1 exp with Value v -> Let((t1,name),v) 
            | _ -> raise Fail in
    kleenestar (concat field_add_pars (concat (kwd "=") value_pars
    scd) assign) [] addel

let concat_list : type b. b tag_list -> (b expr_list -> 'c) -> 'c parser =
    fun tl f ->
        let rec aux: type b. b tag_list -> b expr_list parser =
            fun  tl s t->
            match tl with
            | TNil -> (s,ENil,t)
            | TCons(x,tail) ->
                    match expr_pars s t with
                    | ns,expr,nt -> 
                        comb_parser (aux tail) (fun el -> ECons((check_type x
                        expr),el)) ns nt
        in comb_parser (aux tl) f


let parse_method_call : string -> any_rhs parser =
 fun m s (tbl,act) ->
  let rec aux = function
     [] -> raise Fail
   | (Fun (tag,tags,name))::_ when name = m ->
       concat_list tags 
       (fun el -> AnyRhs(tag,Call(None,(tag,tags,name),el)))
   | _::tl -> aux tl
  in
       (aux tbl) s (tbl,act)

let call_pars s t = 
    let (ns,str,nt) = varname s t in 
    parse_method_call str ns nt

(* parameter_pars = (unit | comb)
 * comb_parameters = type ?( * comb)
 * meth_pars = name: parameter_pars -> type
 * *)
let rec parameter_pars s = 
    choice (const (Kwd "unit") (fun _ -> AnyTagList(TNil))) comb_parameters s
and comb_parameters s =
    concat type_pars (option (concat (kwd "*") comb_parameters
    scd)) (fun (AnyTag t)  tlist -> 
        match tlist with
        | Some (AnyTagList ls) -> AnyTagList (TCons(t,ls))
        | None ->  AnyTagList (TCons(t,TNil))) s 
let meth_pars s t = 
    let (ns, (AnyMeth ast), (tbl,act)) = 
        concat (concat varname (kwd ":") fst) 
        (concat (concat parameter_pars (kwd "->") fst) type_pars (fun e1 e2 -> e1,e2)) 
        (fun name ((AnyTagList tlist),(AnyTag t))-> AnyMeth(t,tlist,name)) s t 
    in (ns,(AnyMeth ast),((add_fun_to_table tbl ast),act))

(*
 * atomic_stm = assign | if bool_expr then stm else stm | { stm } 
 * stm_pars =  atomic_stm ?stm | atomic_stm + stm    
 *)
let check_rhs_type: type b. b tag -> any_rhs -> b rhs =
    fun tag rhs ->
        match rhs with
        | AnyRhs(t,Call(x,y,z)) -> (match eq_tag t tag with Some Refl ->
                Call(x,y,z) | None -> raise Fail)
        | AnyRhs(t,Expr(expr)) -> Expr(check_type tag (AnyExpr(t,expr)))

let rec atomic_stm s =
    choice_list[
        (*assign*)
        concat 
        (concat var_pars (kwd "=") fst)
        (choice call_pars (comb_parser expr_pars (fun (AnyExpr(et,expr)) -> AnyRhs(et,Expr(expr)))))
        (fun (AnyField(et,varname)) any_rhs -> 
            Assign((et,varname),(check_rhs_type et any_rhs)));
        (*if then else*)
        concat 
        (concat (concat (concat (kwd "if") bool_expr scd) (kwd "then") fst ) 
        stm_pars (fun bexpr stm -> bexpr,stm))
        (concat (kwd "else") stm_pars scd) 
        (fun (bexpr,stm1) stm2 -> IfThenElse((check_type Bool bexpr),stm1,stm2));

        concat (kwd "{") (concat stm_pars (kwd "}") fst) scd;
    ] s
and stm_pars s =
    concat atomic_stm (option double_stm) (fun x funct -> match funct with Some
    f -> f x | _ -> x ) s
and double_stm s (tbl,act) =
    choice
        (comb_parser stm_pars (fun stm2 -> (fun stm1 -> Comp(stm1,stm2))))
        (concat (kwd "+") stm_pars (fun _ stm2 -> (fun stm1 -> if act then
            Choice(stm1,stm2) else raise Fail)))
    s (tbl,act)
let stm_list_pars s = kleenestar stm_pars [] addel s

let stack_entry_pars =
    (comb_parser stm_pars (fun stm -> Stm stm))

let rec hum_stack_pars s =
    concat (option stack_entry_pars) (concat (kwd "return") expr_pars (fun _ (AnyExpr(t,e)) -> Return(t,e)))
    (fun entry ret -> match entry with None -> ret | Some st -> SComp(st,ret)) s
(*
 * local_var = varname*
 * program = fun local_var -> stm_list return expr
 *)
let rec local_var_pars: type b. b tag_list -> b var_list parser =
    fun tl s t ->
        match tl with
        | TNil -> s,VNil,t
        | TCons (x,tail) -> 
                match varname s t with
                | ns,var,(tbl,act) -> comb_parser (local_var_pars tail) (fun
                tl -> VCons((x,var),tl)) ns ((add_field_to_table tbl
                (AnyField(x,var)) true),act)

let program_pars: type a b. (a,b) meth -> (a,b) program parser =
    fun m s t ->
        match m with
        | (rettag, taglist, _) -> 
                let (ns, prg, (tbl,act)) =
                concat (concat (concat (kwd "fun") (local_var_pars taglist)
                scd) (kwd "->") fst) (concat stm_list_pars (concat
                (kwd "return") (choice expr_pars (fail_pars true)) scd) (fun stml expr -> stml,expr))
                (fun vl (stml,expr) -> vl,stml,(check_type rettag expr)) s t
                in ns,prg,((remove_local_var tbl ),act)

let any_meth_pars s t =
    let (ns, (AnyMeth meth), nt) = (concat meth_pars (kwd "=") fst) s t in 
    comb_parser (program_pars meth) (fun prg -> AnyMethodDecl(meth, prg)) ns
    (nt)

let methods_pars s = kleenestar any_meth_pars [] addel s

let hum_or_con = function
    | AnyTag ContractAddress -> false 
    | AnyTag HumanAddress -> true
    | _ -> raise Fail

(*
 * Contract | Human varname store
 * *)
let actor_pars s t =
    let (ns, atag, (tbl,cond)) = type_pars s t in
    let is_hum = hum_or_con atag in
    concat (concat varname store_pars (fun actname assls -> actname,assls))
    (concat methods_pars (option hum_stack_pars)
    (fun meths se -> meths,se)) (fun (actname,assls) (meths,se) ->
        match is_hum,se with
        | false,None -> ActCon((Contract actname),meths,assls)
        | true,(Some stack) ->  ActHum((Human actname),meths,assls,stack)
        | _,_ -> raise Fail) ns (tbl, is_hum)
       
(*testing*)
let in_channel = open_in "input"
let file = Stream.of_channel(in_channel)
let lexer = make_lexer["+"; "-"; "*"; "max"; "("; ")"; ">"; ">="; "=="; "<";
"<="; "!="; "&&"; "||"; "!"; "true"; "false"; "int"; "string"; "bool"; 
"="; ","; "fail"; "if"; "then"; "else"; "{"; "fun";
"}";"choice";"return";"Human";"Contract";":";"unit";"->"]
let tokens = remove_minspace (of_token(lexer file));;
(*print_token_list tokens;;*)
(*let empty_t = (Fun(Int,(TCons(Int,TCons(Int,TCons(String,TNil)))),"prova"));
Field(Int,"ciao","main")];;*)
let (s, ast, (tbl,act)) = actor_pars tokens ([],false);;
