open SmartCalculus

open ParserCombinator
open Genlex

(*Expression *)
let plus e1 e2 = 
 match e1,e2 with
 | AnyExpr(Int,v1),AnyExpr(Int,v2) -> AnyExpr(Int,Plus(v1,v2))
 | _ -> raise Fail
  
let minus e = match e with AnyExpr(Int,e) -> AnyExpr(Int,Minus(e)) | _ -> raise Fail

let subtract e2 e1 = plus e1 (minus e2)

let mult e c = 
 match c,e with 
 | AnyExpr(Int,Value v),AnyExpr(Int,expr) -> AnyExpr(Int,Mult(Numeric(v),expr)) 
 | AnyExpr(Int,(Symbol v)),AnyExpr(Int,expr) -> AnyExpr(Int,Mult(Symbolic(v),expr)) 
 | _-> raise Fail

let max e1 e2 =
   match e1,e2 with
    | AnyExpr(Int,v1),AnyExpr(Int,v2) -> AnyExpr(Int,Max(v1,v2))
    | _ -> raise Fail
  

let gt e2 e1 =
    match e1,e2 with
    | AnyExpr(Int,v1),AnyExpr(Int,v2) -> AnyExpr(Bool,Gt(v1,v2))
    | _ -> raise Fail

let ge e2 e1 =
    match e1,e2 with
    | AnyExpr(Int,v1),AnyExpr(Int,v2) -> AnyExpr(Bool,Geq(v1,v2))
    | _ -> raise Fail

let eq e2 e1 = 
    match e1,e2 with
    | AnyExpr(t1,v1),AnyExpr(t2,v2) ->
            (match eq_tag t1 t2 with
            | Some Refl -> AnyExpr(Bool,Eq(t1,v1,v2))
            | _ -> raise Fail)

let lt e1 e2 = gt e2 e1

let le e1 e2 = ge e2 e1

let andb e2 e1 =
    match e1,e2 with
    | AnyExpr(Bool,v1),AnyExpr(Bool,v2) -> AnyExpr(Bool,And(v1,v2))
    | _ -> raise Fail


let orb e2 e1 =
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
 | (String s)::tl -> tl,AnyExpr(Int,Symbol(s)),t
 | _ -> raise Fail

let var_pars: type a. a tag -> (a expr) parser = fun tag s t ->
    match tag,s,t with
    | Int,(Kwd "value")::tl,_ -> tl,(Var(Int,"value")),t
    | Int,(Kwd "balance")::tl,_ -> tl,(Field(Int,"balance")),t
    | _,(Ident var)::tl,(tbl,act) -> 
            (match get_field tbl var with
            | Some (AnyField(tagfield,name),islocal) ->
                    (match (eq_tag tagfield tag),islocal with
                    | (Some Refl),false -> tl,(Field(tagfield,name)),t
                    | (Some Refl),true -> tl,(Var(tagfield,name)),t
                    | None,_ -> raise Fail)
            | None -> tl,Var(tag,var),t)
     | _ -> raise Fail

let value_pars tag s t = (junk s),(value tag (List.hd s)),t

let fail_pars : type a . a tag -> bool -> (a expr) parser = fun tag perm ->
    const (Kwd "fail") (fun _ -> if perm then SmartCalculus.Fail else raise Fail)

let this_pars =
    const (Kwd "this") (fun _ -> SmartCalculus.This)

(*variable | value | fail*)
let base tag s (tbl,act) =
    choice_list[
        var_pars tag;
        value_pars tag ;
        fail_pars tag act;
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
   comb_parser (base Int) (fun expr -> AnyExpr(Int,expr));
   concat (kwd "-") atomic_int_expr (fun _ -> minus) ;
   concat (concat (kwd "(") int_expr scd) (kwd ")") fst ;
   concat (concat (kwd "max") int_expr scd) int_expr max;
   concat (kwd "symbol") symbol_pars scd;
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
        comb_parser (base Bool) (fun expr -> AnyExpr(Bool,expr));
        concat (concat (kwd "(") bool_expr scd) (kwd ")") fst ;
        concat (kwd "!") atomic_bool_expr (fun _ -> notb) ;
        concat int_expr (concat cmpop int_expr (fun f x -> f x)) (fun x f -> f x);
        concat int_expr (concat eqop int_expr (fun f x -> f x)) (fun x f -> f x);
 ] s
 and cmpop s =  
    choice_list [
      const (Kwd ">") (fun _ -> gt) ;
      const (Kwd ">=") (fun _ -> ge) ;
      const (Kwd "<") (fun _ -> lt);
      const (Kwd "<=") (fun _ -> le) ;
    ] s
and eqop s =
    choice_list [
      const (Kwd "==") (fun _ -> eq); 
      const (Kwd "!=") (fun _ -> neq);
    ] s
and bool_expr s =
 concat atomic_bool_expr (option cont_bool_expr) (fun x f -> match f with Some y ->
     y x | _ -> x) s
and bin_bool_op s =
 choice_list [
  const (Kwd "&&") (fun _ -> andb) ;
  const (Kwd "||") (fun _ -> orb) ;
  eqop;
 ] s
and cont_bool_expr s = concat bin_bool_op bool_expr (fun f x -> f x) s

and contract_expr s = comb_parser (choice (base ContractAddress) this_pars) (fun
    expr -> AnyExpr(ContractAddress, expr)) s
and string_expr s = 
    comb_parser (base String) (fun expr -> AnyExpr(String,expr)) s
and human_expr s = 
    comb_parser (base HumanAddress) (fun expr -> AnyExpr(HumanAddress,expr)) s

and expr_pars s = choice_list[int_expr; bool_expr; contract_expr; string_expr;
human_expr] s

let get_null_value : type a. a tag -> a =
function
    | Int ->  0
    | String ->  ""
    | Bool ->  false
    | ContractAddress -> Contract ""
    | HumanAddress -> Human ""

let type_pars =
    let tag_pars str tag = const (Kwd str) (fun _ -> AnyTag tag) in
    choice_list[
        tag_pars "int" Int;
        tag_pars "string" String;
        tag_pars "bool" Bool;
        tag_pars "Contract" ContractAddress;
        tag_pars "Human" HumanAddress;
]

let pars_this = concat (kwd "this") (kwd ".") (fun _ _ -> This)

let field_pars s t = 
    let (ns,field,(tbl,act)) =
        concat type_pars varname (fun (AnyTag t) v -> AnyField (t,v)) s t in 
    ns,field,((add_field_to_table tbl field false),act)

let decl_pars s t = 
    let (ns,(AnyField(tag,name)),nt) = field_pars s t in
    comb_parser (option (concat (kwd "=") (value_pars tag) scd)) 
    (fun opt_exp -> match opt_exp with 
            | Some (Value v) -> Let ((tag,name),v)
            | None -> Let ((tag,name),(get_null_value tag))
            | _ -> raise Fail) ns nt 


let store_pars =
        kleenestar decl_pars [] addel

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


let parse_any_expr_list =
    kleenestar expr_pars [] (fun el expr -> el@[expr]) 

let get_rhs_from_expr_list = 
    fun m c typ el -> 
        let rec aux el rhs =
            match el with
            | [] -> rhs
            | AnyExpr (t,expr) :: tl -> 
                    (match rhs with 
                    | Call(c,(tag,tags,name),elist) -> 
                        aux tl
                        (Call(c,(tag,TCons(t,tags),name),ECons(expr,elist)))
                    | _ -> raise Fail)
        in aux (List.rev el) (Call(c,(typ,TNil,m),ENil))

let  parse_method_call : string  -> any_rhs parser =
 fun m s (tbl,act) ->
  let rec aux = function
     [] -> raise Fail
   | (Fun (tag,tags,name))::_ when name = m ->
       concat_list tags
       (fun el -> AnyRhs(tag,Call(None,(tag,tags,name),el)))
      | _::tl -> aux tl
  in
       (aux tbl) s (tbl,act)

let opt_expr : type a .a tag -> any_expr -> a expr option = fun t -> 
 function
  | AnyExpr(texp,e) -> 
    match eq_tag texp t with 
     | Some Refl -> Some e
     | None -> None 

let pars_mesg_value s t= try comb_parser (concat (concat (concat (kwd ".") (kwd "(") scd)
    (concat (kwd "value") int_expr scd) scd) (kwd ")") fst) (opt_expr Int) s t
    with Fail -> (s,None,t)


let call_with_contr tag s t =
    let (ns1, (contr,funname), nt1) = 
        concat (comb_parser (concat contract_expr (kwd ".") fst)
        (opt_expr ContractAddress)) (varname) (fun x1 x2 -> x1,x2) s t in
    let (ns2,value,nt2) = pars_mesg_value ns1 nt1 in
    comb_parser parse_any_expr_list ((fun el -> (fun rhs -> match rhs,value with
    Call(c,meth,el),Some v -> CallWithValue (c,meth,el,v) | _,_ -> rhs) (get_rhs_from_expr_list funname
    contr tag el))) ns2 nt2


let call_pars s t = 
    (*let (ns1, contr, nt1) = try comb_parser (concat expr_pars (kwd ".") fst)
    (opt_expr ContractAddress) s t with Fail -> s,None,t in*)
    let (ns1,str,nt1) = varname s t in 
    let (ns2,value,nt2) = pars_mesg_value ns1 nt1 in
    comb_parser (parse_method_call str)
    (function 
        | AnyRhs(tag,Call(c,meth,el)) ->
                (match value with 
                | Some v -> 
                    AnyRhs(tag,CallWithValue(c,meth,el,v))
                | None -> AnyRhs(tag,Call(c,meth,el)))
        | _ -> raise Fail) ns2 nt2

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
        | AnyRhs(t,CallWithValue(x,y,z,v)) -> (match eq_tag t tag with Some Refl ->
                CallWithValue(x,y,z,v) | None -> raise Fail)
        | AnyRhs(t,Expr(expr)) -> Expr(check_type tag (AnyExpr(t,expr)))

let assign_pars : stm parser = fun s tbl ->
    let (ns0,this_opt,ntbl0) = option (concat this_pars (kwd ".") fst) s tbl in
    let (ns1,varname, (ntbl1,act)) = concat varname (kwd "=") fst ns0 ntbl0 in
    let rhs_pars = choice 
     (comb_parser expr_pars (fun (AnyExpr(et,expr)) -> AnyRhs(et,Expr(expr))))
     call_pars in
    (match get_field ntbl1 varname with
     | Some (AnyField (tag,_),_) -> 
         choice 
         (comb_parser (call_with_contr tag) (fun rhs -> Assign((tag,varname),rhs))) 
         (comb_parser rhs_pars
         (fun any_rhs -> match any_rhs with AnyRhs(ft,_) ->
             Assign((tag,varname),(check_rhs_type tag any_rhs)))) ns1
             (ntbl1,act)
     | None ->
         let (ns2,any_rhs, (ntbl2,act)) = rhs_pars ns1 (ntbl1,act) in
         let islocal = match this_opt with Some _ -> false | _ -> true in
         match any_rhs with AnyRhs(et,_) ->
         ns2,(Assign((et,varname),(check_rhs_type et any_rhs))),
         ((add_field_to_table ntbl2 (AnyField(et,varname)) islocal),act)
    )


let rec atomic_stm s =
    choice_list[
        (*assign*)
        assign_pars;
        comb_parser decl_pars (fun (Let (f,v)) -> Assign(f,Expr(Value v)));
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
 * local_var = varname *
 * program = fun local_var -> stm_list return expr
 *)
let rec local_var_pars: type b. b tag_list -> b var_list parser =
    fun tl s (t,a) ->
        match tl with
        | TNil -> s,VNil,(t,a)
        | TCons (x,tail) -> 
                match varname s (t,a) with
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
                (kwd "return") expr_pars scd) (fun stml expr -> stml,expr))
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


let parse_init_balance =
    concat 
    (concat (kwd "(") (value_pars Int)
        (fun _ expr -> match expr with
        Value v -> Let((Int,"balance"),v) | _ -> raise Fail)) 
    (kwd ")") fst

let couple el1 el2 = el1,el2

(*
 * Contract (value_pars)| Human varname store
 *)
let actor_pars s t =
    let (ns, atag, (nt,cond)) = type_pars s ([],false)  in
    let is_hum = hum_or_con atag in
    concat (concat (concat (concat varname (option parse_init_balance) couple) 
    (kwd "{") fst) store_pars 
    (fun (actname,bal) assls -> 
        match bal with 
        Some b -> (actname,([b]@assls)) 
    | _ -> (actname,assls))) 
    (concat methods_pars (concat (option hum_stack_pars)(kwd "}") fst) couple) 
    (fun (actname,assls) (meths,se) ->
        match is_hum,se with
        | false,None -> ActCon((Contract actname),meths,assls)
        | true,(Some stack) ->  ActHum((Human actname),meths,assls,stack)
    | _,_ -> raise Fail) 
    ns 
    (nt, is_hum)

let add_act : configuration -> any_actor -> configuration =
    fun conf act ->
        match act,conf with
            | ActCon c, {contracts = cl; humans = hl} -> {contracts = cl@[c]; humans = hl}
            | ActHum h, {contracts = cl; humans = hl} -> {contracts = cl; humans
            = hl@[h]}

let configuration_pars =  
    kleenestar actor_pars {contracts = []; humans = []} add_act
(*testing*)
let in_channel = open_in "input"
let file = Stream.of_channel(in_channel)
let lexer = make_lexer["+"; "-"; "*"; "max"; "("; ")"; ">"; ">="; "=="; "<";
"<="; "!="; "&&"; "||"; "!"; "true"; "false"; "int"; "string"; "bool"; 
"="; ","; "fail"; "if"; "then"; "else"; "{"; "fun";
"}"; "choice"; "return"; "Human"; "Contract"; ":"; "unit"; "->"; "this"; ".";
"value"; "balance"; "symbol"]
let tokens = remove_minspace (of_token(lexer file));;
(*print_token_list tokens;;*)
(*let empty_t = (Fun(Int,(TCons(Int,TCons(Int,TCons(String,TNil)))),"prova"));
Field(Int,"ciao","main")];;*)
let (s, conf, (tbl,act)) = configuration_pars tokens ([],false);;
print_token_list s;;
print_table tbl;;
