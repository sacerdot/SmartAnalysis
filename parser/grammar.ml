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

let couple el1 el2 = el1,el2

let symbol_pars s t = 
 match s with
 | (String s)::tl -> tl,AnyExpr(Int,Symbol(s)),t
 | _ -> raise Fail

let var_pars: type a. a tag -> (a expr) parser = fun tag s t ->
const (List.hd s) (fun _ -> 
 let aux : (a expr) =
 (match tag,s,t with
 | Int,(Kwd "value")::tl,_ -> Var(Int,"value")
 | Int,(Kwd "balance")::tl,_ -> Var(Int,"balance")
 | _,(Ident var)::tl,(tbl,act) -> 
  (match get_field tbl var with
  | Some (AnyField(tagfield,name),islocal) ->
   (match (eq_tag tagfield tag),islocal with
   | (Some Refl),false -> SmartCalculus.Field(tagfield,name)
   | (Some Refl),true -> Var(tagfield,name)
   | None,_ -> raise Fail)
  | None -> 
    (match tag with 
    | ContractAddress -> Var(tag,var)
    | HumanAddress -> Var(tag,var)
    | _ -> raise Fail))
   | _ -> raise Fail) in aux) s t

let value_pars tag s t = (junk s),(value tag (List.hd s)),t

let fail_pars : type a . a tag -> bool -> (a expr) parser = fun tag perm ->
 const (Kwd "fail") (fun _ -> if perm then SmartCalculus.Fail else raise Fail)

let this_pars = const (Kwd "this") (fun _ -> SmartCalculus.This)

let brackets_pars pars = concat (concat (kwd "(") pars scd) (kwd ")") fst

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
 * cont_int_expr ::=  "+" int_expr | "*" int_expr | "-" int_expr 
 *)
let rec atomic_int_expr s = 
 choice_list [
   comb_parser (base Int) (fun expr -> AnyExpr(Int,expr));
   concat (kwd "-") atomic_int_expr (fun _ -> minus) ;
   brackets_pars int_expr;
   comb_parser (concat (kwd "max") (brackets_pars (concat (concat int_expr (kwd ",") fst)
   int_expr couple)) scd) (fun (e1,e2) -> max e1 e2)  ;
   concat (kwd "symbol") (brackets_pars symbol_pars) scd;
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
  concat (choice_list[int_expr; string_expr; contract_expr; human_expr]) (concat eqop expr_pars (fun f x -> f x)) (fun x f -> f x);
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
and cont_bool_expr s = concat (choice bin_bool_op eqop) bool_expr (fun f x -> f x) s

and contract_expr s = 
 let rec aux s =
  choice_list [
   base ContractAddress; 
   this_pars;
   brackets_pars aux;
   concat (kwd "contr_addr") (brackets_pars (value_pars String)) 
   (fun _ -> function Value s -> Value (Contract s) | _ -> raise Fail)] s
 in 
 comb_parser aux (fun expr -> AnyExpr(ContractAddress, expr)) s

and string_expr s = 
 let rec aux s = choice (base String) (brackets_pars aux) s in
 comb_parser aux (fun expr -> AnyExpr(String,expr)) s

and human_expr s = 
 let rec aux s =
  choice_list [
   base HumanAddress;
   brackets_pars aux;
   concat (kwd "hum_addr") (brackets_pars(value_pars String)) 
   (fun _ -> function Value s -> Value (Human s) | _ -> raise Fail)
  ] s 
 in comb_parser aux (fun expr -> AnyExpr(HumanAddress,expr)) s

and expr_pars s = choice_list[concat (concat (kwd "(") expr_pars scd) (kwd ")")
fst; int_expr; bool_expr; contract_expr; string_expr; human_expr] s

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

let field_pars islocal s t = 
 let (ns,field,(tbl,act)) =
  concat type_pars varname (fun (AnyTag t) v -> AnyField (t,v)) s t in 
 ns,field,((add_field_to_table tbl field islocal),act)

let decl_pars islocal s t = 
 let (ns,(AnyField(tag,name)),nt) = field_pars islocal s t in
 comb_parser (option (concat (kwd "=") (value_pars tag) scd)) 
 (fun opt_exp -> match opt_exp with 
  | Some (Value v) -> Let ((tag,name),v)
  | None -> Let ((tag,name),(get_null_value tag))
  | _ -> raise Fail) ns nt 

let store_pars = kleenestar (decl_pars false) [] addel

let parse_any_expr_list = 
 comb_parser 
 (brackets_pars (option (concat expr_pars 
 (kleenestar (concat (kwd ",") expr_pars scd) [] addel) 
 (fun expr el -> [expr]@el))))(function Some s -> s | None -> [])

let rec check_expr_list_type: type a. a tag_list -> any_expr list -> a expr_list 
= fun tl el ->
 match tl,el with
  | TNil,[] -> ENil
  | TCons(t,ttail),(h::etail) -> 
    ECons((check_type t h),(check_expr_list_type ttail etail))
  | _,_ -> raise Fail

let concat_list : type b. b tag_list -> (b expr_list -> 'c) -> 'c parser =
 fun tl f ->
   comb_parser (comb_parser parse_any_expr_list (check_expr_list_type tl)) f

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

let parse_method_call : string -> any_rhs parser =
 fun m s (tbl,act) ->
  let rec aux = function
     [] -> raise Fail
   | (Fun (tag,tags,name))::_ when name = m ->
       concat_list tags
       (fun el -> AnyRhs(tag,Call(None,(tag,tags,name),el)))
      | _::tl -> aux tl
  in (aux tbl) s (tbl,act)

let opt_expr : type a .a tag -> any_expr -> a expr option = fun t -> 
 function
  | AnyExpr(texp,e) -> 
    match eq_tag texp t with 
     | Some Refl -> Some e
     | None -> None 

let check_rhs_type: type a. a tag -> any_rhs -> a rhs =
 fun tag rhs ->
  match rhs with
  | AnyRhs(t,r) -> 
    (match eq_tag t tag with Some Refl -> r | None -> raise Fail)

let pars_mesg_value s t= try comb_parser (concat (kwd ".") 
    (concat (kwd "value") (brackets_pars int_expr) scd) scd) (opt_expr Int) s t
    with Fail -> (s,None,t)

let funname s (tbl,act) = 
 comb_parser varname (fun var -> match get_fun tbl var with Some _ ->
  var | None -> raise Fail) s (tbl,act)

let call_pars s t = 
 let (ns1,str,nt1) = funname s t in 
 let (ns2,value,nt2) = pars_mesg_value ns1 nt1 in
 comb_parser (parse_method_call str)
 (function 
  | AnyRhs(tag,Call(c,meth,el)) ->
   (match value with 
   | Some v -> AnyRhs(tag,CallWithValue(c,meth,el,v))
   | None -> AnyRhs(tag,Call(c,meth,el)))
  | _ -> raise Fail) ns2 nt2


let call_with_contr tag s t =
 let (ns0, contr, nt0) = comb_parser (concat contract_expr (kwd ".") fst)
  (opt_expr ContractAddress) s t in
 match contr with
 | Some This -> comb_parser call_pars (check_rhs_type tag) ns0 nt0 
 | _ -> 
 let (ns1, funname, nt1) = varname ns0 nt0 in
 let (ns2,value,nt2) = pars_mesg_value ns1 nt1 in
 comb_parser parse_any_expr_list ((fun el -> (fun rhs -> match rhs,value with
 Call(c,meth,el),Some v -> CallWithValue (c,meth,el,v) | _,_ -> rhs) (get_rhs_from_expr_list funname
 contr tag el))) ns2 nt2

(*
 * atomic_stm = assign | if bool_expr then stm else stm | { stm } 
 * stm_pars =  atomic_stm ?stm | atomic_stm + stm    
 *)
let rec atomic_rhs this_opt varname s = 
 let aux = fun this_opt varname s (tbl,act) ->
 let expr_call_pars = choice call_pars 
  (comb_parser expr_pars (fun (AnyExpr(et,expr)) -> AnyRhs(et,Expr(expr))))
 in
 (match get_field tbl varname with
  | Some (AnyField (tag,_),_) -> 
   choice 
   (comb_parser (call_with_contr tag) (fun rhs -> Assign((tag,varname),rhs))) 
   (comb_parser expr_call_pars
   (fun any_rhs -> match any_rhs with AnyRhs(ft,_) ->
       Assign((tag,varname),(check_rhs_type tag any_rhs)))) s
       (tbl,act)
  | None ->
   let (ns1,any_rhs, (ntbl1,act)) = expr_call_pars s (tbl,act) in
   let islocal = match this_opt with Some _ -> false | _ -> true in
   match any_rhs with AnyRhs(et,_) ->
   ns1,(Assign((et,varname),(check_rhs_type et any_rhs))),
   ((add_field_to_table ntbl1 (AnyField(et,varname)) islocal),act)) in
 choice (concat (concat (kwd "(")
(rhs_pars this_opt varname) scd) (kwd ")") fst) (aux this_opt varname) s

and rhs_pars this_opt varname s = atomic_rhs this_opt varname s

let assign_pars s tbl =
 let (ns0,this_opt,ntbl0) = option (concat this_pars (kwd ".") fst) s tbl in
 let (ns1,varname, (ntbl1,act)) = concat varname (kwd "=") fst ns0 ntbl0 in
 rhs_pars this_opt varname ns1 (ntbl1,act)
    
let rec atomic_stm s =
 choice_list[
  (*assign*)
  assign_pars;
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

let stack_entry_pars = comb_parser stm_pars (fun stm -> Stm stm)

let rec hum_stack_pars s =
 concat (option stack_entry_pars) (concat (kwd "return") expr_pars (fun _ (AnyExpr(t,e)) -> Return(t,e)))
 (fun entry ret -> match entry with None -> ret | Some st -> SComp(st,ret)) s

 (* parameter_pars = (void | comb)
 * comb_parameters = type ?( * comb)
 * meth_pars = name: parameter_pars -> type
 * *)
let rec add_local_var tbl =
  function 
   | AnyVarList (VNil) -> tbl
   | AnyVarList (VCons(h,tl)) -> 
    add_local_var (add_field_to_table tbl (AnyField h) true) (AnyVarList tl)
  
let rec get_varlist = 
 function
  | [] -> AnyVarList VNil
  | AnyExpr(_,Var(t,name))::tl -> 
   let AnyVarList l = get_varlist tl in AnyVarList(VCons((t,name),l))
  | _ -> raise Fail

let rec get_taglist : type a. a var_list -> a tag_list =
 function
  | VNil -> TNil
  | VCons((t,_),tl) -> TCons (t,(get_taglist tl))

let rec varlist_append l1 l2 =
 match l1 with
 | AnyVarList(VNil) -> l2
 | AnyVarList(VCons(hd,tl)) -> 
   let AnyVarList l = varlist_append (AnyVarList tl) l2 in
   AnyVarList(VCons(hd,l))
 
let rec parameter_pars s t = 
 let pars_varlist_singleton = concat type_pars varname 
 (fun (AnyTag t) s -> (AnyVarList(VCons((t,s),VNil)))) in
 let (ns,vl,(nt,act)) = 
  comb_parser (brackets_pars (option (concat pars_varlist_singleton
  (kleenestar (concat (kwd ",") pars_varlist_singleton scd) 
  (AnyVarList(VNil)) varlist_append) varlist_append))) 
  (function | Some s -> s | None -> AnyVarList(VNil)) s t in
 ns,vl,((add_local_var nt vl),act)
 
let any_meth_pars s t =
 let (ns1,(name,((AnyVarList vl),(AnyTag t1))),(nt1,act)) =
  concat (concat (kwd "function") varname scd) 
  (concat parameter_pars (concat (kwd ":") type_pars scd) couple) couple s t in
 let (ns2,(stml,e),(nt2,act)) = 
  concat (concat (kwd "{")
  (concat (concat (kleenestar (comb_parser (decl_pars true)
  (fun (Let (f,v)) -> Assign(f,Expr(Value v)))) [] addel)
  stm_list_pars List.append) (concat (kwd "return") expr_pars scd) 
  couple) scd) (kwd "}") fst ns1 ((add_fun_to_table nt1 (AnyMeth(t1,get_taglist vl,name))),act) in
  ns2,(AnyMethodDecl((t1,(get_taglist vl),name),(vl,stml,(check_type t1
  e)))),((remove_local_var nt2),act)

let methods_pars s = kleenestar any_meth_pars [] addel s

let hum_or_con = 
 function
 | AnyTag ContractAddress -> false 
 | AnyTag HumanAddress -> true
 | _ -> raise Fail

let parse_init_balance =
 concat (concat (kwd "(") (value_pars Int)
  (fun _ expr -> 
    match expr with
    Value v -> Let((Int,"balance"),v) 
    | _ -> raise Fail)) (kwd ")") fst

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
 ns  (nt, is_hum)

let add_act : configuration -> any_actor -> configuration =
 fun conf act ->
  match act,conf with
   | ActCon c, {contracts = cl; humans = hl} -> {contracts = cl@[c]; humans = hl}
   | ActHum h, {contracts = cl; humans = hl} -> {contracts = cl; humans = hl@[h]}

let configuration_pars = kleenestar actor_pars {contracts = []; humans = []} add_act

let lexer = make_lexer["+"; "-"; "*"; "max"; "("; ")"; ">"; ">="; "=="; "<";
"<="; "!="; "&&"; "||"; "!"; "true"; "false"; "int"; "string"; "bool"; 
"="; ","; "fail"; "if"; "then"; "else"; "{"; "function";
"}"; "return"; "Human"; "Contract"; ":"; "this"; ".";
"value"; "balance"; "symbol"; "contr_addr"; "hum_addr"]
let get_tokens file = remove_minspace (of_token(lexer file));;

let in_channel = open_in "input"
let file = Stream.of_channel(in_channel)
let (s, conf, (tbl,act)) = configuration_pars (get_tokens file) ([],false);;
print_token_list s;;
print_table tbl;;

let pars_human file =
 comb_parser actor_pars (function ActHum hum -> hum | _ -> raise Fail) 
 (get_tokens file) ([],false)

let pars_contract file =
 comb_parser actor_pars (function ActCon con -> con | _ -> raise Fail) 
 (get_tokens file) ([],false)


