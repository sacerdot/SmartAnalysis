open MicroSolidity
open ParserCombinator
open Genlex

(*Expression *)
let plus e1 e2 = 
 match e1,e2 with
 | AnyExpr(Int,v1),AnyExpr(Int,v2) -> AnyExpr(Int,Plus(v1,v2))
 | _ -> raise Fail
  
let uminus e =
 match e with
  | AnyExpr(Int,e) -> AnyExpr(Int,UMinus(e)) | _ -> raise Fail

let minus e1 e2 = 
 match e1,e2 with
 | AnyExpr(Int,v1),AnyExpr(Int,v2) -> AnyExpr(Int,Minus(v1,v2))
 | _ -> raise Fail

let mult e1 e2 = 
 match e1,e2 with
 | AnyExpr(Int,v1),AnyExpr(Int,v2) -> AnyExpr(Int,Mult(v1,v2))
 | _ -> raise Fail

let div e1 e2 = 
 match e1,e2 with
 | AnyExpr(Int,v1),AnyExpr(Int,v2) -> AnyExpr(Int,Div(v1,v2))
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

let var_pars: type a. a tag -> (a expr) parser = fun tag s t ->
const (List.hd s) (fun _ -> 
 let aux : a expr =
 (match tag,s,t with
 | Int,(Kwd "msg")::(Kwd ".")::(Kwd "value")::tl,_ -> MsgValue
 (*| Int,(Kwd "balance")::tl,_ -> Var(Int,"balance")*)
 | _,(Ident var)::tl,tbl -> 
  (match get_field tbl var with
    | Some (AnyField(tagfield,name),islocal) ->
       (match (eq_tag tagfield tag),islocal with
         | Some Refl,false -> MicroSolidity.Field(tagfield,name)
         | Some Refl,true -> Var(tagfield,name)
         | None,_ -> raise Fail)
    | None -> 
(*XXX qua dovrei parsare i nomi dei contratti in indirizzi!
    (match tag with 
    | Address -> Value var
    | _ -> raise Fail)) *) raise Fail)
 | _ -> raise Fail) in aux) s t

let value_pars tag s = const (List.hd s) (value tag) s

let this_pars = const (Kwd "this") (fun _ -> MicroSolidity.This)

let brackets_pars pars = concat (concat (kwd "(") pars scd) (kwd ")") fst

(*Variable | value *)
let base tag s tbl =
    choice_list[
        var_pars tag;
        value_pars tag ;
    ] s tbl

(* Int Expression
 * atomic_int_expr :=
    base Int | - atomic_int_expr | varname | ( int_expr ) | string
 * int_expr := atomic_int_expr ?cont_int_expr
 * cont_int_expr ::=  + int_expr | * int_expr | / int_expr | - int_expr 
 *)
let rec atomic_int_expr s = 
 choice_list [
   comb_parser (base Int) (fun expr -> AnyExpr(Int,expr));
   concat (kwd "-") atomic_int_expr (fun _ -> uminus) ;
   brackets_pars int_expr
 ] s
and int_expr s =
 concat atomic_int_expr (option cont_int_expr) (fun x f -> match f with Some funct
 -> funct x | _ -> x) s
and binop s =
 choice_list [
  const (Kwd "+") (fun _ -> plus) ;
  const (Kwd "*") (fun _ -> mult) ;
  const (Kwd "/") (fun _ -> div) ;
  const (Kwd "-") (fun _ -> minus)
 ] s
and cont_int_expr s = concat binop int_expr (fun f x -> f x) s

 (* Bool Expression
 * atomic_bool_expr :=
    bool | int_expr > int_expr  | int_expr >= int_expr  | int_expr <
    int_expr | int_expr <= int_expr | expr == expr | varname | ( bool_expr
    ) | ! bool_expr
 * bool_expr := atomic_int_expr ?cont_int_expr
 * cont_bool_expr ::=  && bool_expr | || bool_expr 
 *)
let rec atomic_bool_expr s =
 choice_list[
  comb_parser (base Bool) (fun expr -> AnyExpr(Bool,expr));
  concat (concat (kwd "(") bool_expr scd) (kwd ")") fst ;
  concat (kwd "!") atomic_bool_expr (fun _ -> notb) ;
  concat int_expr (concat cmpop int_expr (fun f x -> f x)) (fun x f -> f x);
  concat (choice_list[int_expr; contract_expr]) (concat eqop expr_pars (fun f x -> f x)) (fun x f -> f x);
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

(*
 * contr_expr ::= this | Var
 *)
and contract_expr s = 
 let rec aux s =
  choice_list [
   base Address; 
   this_pars;
   brackets_pars aux;
   ] s
 in 
 comb_parser aux (fun expr -> AnyExpr(Address, expr)) s

and expr_pars s =
 choice_list [
  concat (concat (kwd "(") expr_pars scd) (kwd ")") fst;
  int_expr;
  bool_expr;
  contract_expr
 ] s

(*
let get_null_value : type a. a tag -> a =
function
 | Int ->  0
 | Bool ->  false
 | ContractAddress -> Contract ""
 | HumanAddress -> Human ""
*)
(*
* t ::= int | bool
*)
let type_pars =
 let tag_pars str tag = const (Kwd str) (fun _ -> AnyTag tag) in
 choice_list[
  tag_pars "int" Int;
  tag_pars "bool" Bool;
]

let field_pars islocal s t = 
 let (ns,field,tbl) =
  concat type_pars varname (fun (AnyTag t) v -> AnyField (t,v)) s t in 
 ns,field,add_field_to_table tbl field islocal

 (*
  * decl ::= t
  *)
let decl_pars islocal s t = field_pars islocal s t

(*
 * store ::= decl*
 *)
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
    ECons(check_type t h,check_expr_list_type ttail etail)
  | _,_ -> raise Fail

let concat_list : type b. b tag_list -> (b expr_list -> 'c) -> 'c parser =
 fun tl f ->
   comb_parser (comb_parser parse_any_expr_list (check_expr_list_type tl)) f

let get_rhs_from_expr_list = 
 fun m c typ value el -> 
  let rec aux el rhs =
   match el with
   | [] -> rhs
   | AnyExpr (t,expr) :: tl -> 
    (match rhs with 
    | Call(c,(tag,tags,name),value,elist) -> 
        aux tl
        (Call(c,(tag,TCons(t,tags),name),value,ECons(expr,elist)))
    | _ -> raise Fail)
  in aux (List.rev el) (Call(c,(typ,TNil,m),value,ENil))

(*
let parse_method_call : string -> any_rhs parser =
 fun m s tbl ->
  let rec aux = function
     [] -> raise Fail
   | (Fun (tag,tags,name))::_ when name = m ->
       concat_list tags
       (fun el -> AnyRhs(tag,Call(None,(tag,tags,name),el)))
      | _::tl -> aux tl
  in aux tbl s tbl
*)

let opt_expr : type a. a tag -> any_expr -> a expr option = fun t -> 
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

let funname s tbl = 
 comb_parser varname (fun var -> match get_fun tbl var with Some _ ->
  var | None -> raise Fail) s tbl

(*
(*
* call_contr ::= contr_expr.varname (.value)? (( (e (, e)* ? )
*)
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
*)

(*
(*
 * call_contr ::= contr_expr.varname (.value)? (( (e (, e)* ? )
 *)
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
*)

(*
let rec rhs_toassign_pars this_opt varname s = 
 let aux = fun this_opt varname s tbl ->
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
       tbl
  | None ->
   let (ns1,any_rhs,ntbl1) = expr_call_pars s tbl in
   let islocal = match this_opt with Some _ -> false | _ -> true in
   match any_rhs with AnyRhs(et,_) ->
   ns1,(Assign((et,varname),(check_rhs_type et any_rhs))),
   add_field_to_table ntbl1 (AnyField(et,varname)) islocal) in
 choice (concat (concat (kwd "(")
(rhs_toassign_pars this_opt varname) scd) (kwd ")") fst) (aux this_opt varname) s
*)

(*
(*assign ::= Var = rhs*)
let assign_pars s tbl =
 let (ns0,this_opt,ntbl0) = option (concat this_pars (kwd ".") fst) s tbl in
 let (ns1,varname, ntbl1) = concat varname (kwd "=") fst ns0 ntbl0 in
 rhs_toassign_pars this_opt varname ns1 ntbl1
*)

type 'a rettag = RTEpsilon : [`Epsilon] rettag | RTReturn : [`Return] rettag

let revert_pars : 'b rettag -> ('a,'b) stm parser = fun tag -> const (Kwd "revert") (fun _ -> MicroSolidity.Revert)

let epsilon_pars : type b. b rettag -> ('a,b) stm parser =
 function
    RTEpsilon -> fun s t -> s,MicroSolidity.Epsilon,t 
  | RTReturn -> raise Fail

let if_then_else bexpr stm1 stm2 stm3 =
 IfThenElse(check_type Bool bexpr,stm1,stm2,stm3)
    
(*
 * stm ::= revert | return expr | assign | if bool_expr then stm else stm ; stm | { stm } | epsilon
 *)
let rec stm_pars : type b. b rettag -> ('a,b) stm parser = fun tag s ->
 choice_list[
  (* revert *)
  revert_pars tag ;

(*XXX
  (* return *)
  return_pars ;
*)

(*XXX
  (*assign*)
  assign_pars;
*)
  (*if then else*)
  comb_parser (concat (concat (concat (concat (concat (concat (concat
   (kwd "if")
   bool_expr scd)
   (kwd "then") fst)
   (stm_pars RTEpsilon) couple)
   (kwd "else") fst)
   (stm_pars RTEpsilon) couple)
   (kwd ";") fst)
   (stm_pars tag) couple)
   (fun (((bexpr,stm1),stm2),stm3) ->
     if_then_else bexpr stm1 stm2 stm3);

  (* {stm} *)
  concat (kwd "{") (concat (stm_pars tag) (kwd "}") fst) scd;

  (* epsilon *)
  epsilon_pars tag
 ] s

let rec add_local_var tbl =
  function 
   | AnyVarList VNil -> tbl
   | AnyVarList (VCons(h,tl)) -> 
    add_local_var (add_field_to_table tbl (AnyField h) true) (AnyVarList tl)
  
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

(*
* parameters ::= t Var (, t Var)* ?
*)
let rec parameter_pars s t = 
 let pars_varlist_singleton =
  concat type_pars varname 
   (fun (AnyTag t) s -> (AnyVarList(VCons((t,s),VNil)))) in
 let (ns,vl,nt) = 
  comb_parser (option (concat pars_varlist_singleton
  (kleenestar (concat (kwd ",") pars_varlist_singleton scd) 
  (AnyVarList(VNil)) varlist_append) varlist_append))
  (function Some s -> s | None -> AnyVarList(VNil)) s t in
 ns,vl,add_local_var nt vl

(*
 * meth ::= function Var parameters : t { paramters stm }
 *)
let any_meth_pars s t =
 let (ns1,(name,((AnyVarList vl),(AnyTag t1))),nt1) =
  concat (concat
   (kwd "function")
   varname scd)
   (concat parameter_pars (concat (kwd ":") type_pars scd) couple) couple
   s t in
 let (ns2,((payable,AnyVarList lvl),stm),nt2) = 
  concat (concat (concat (concat
   (comb_parser (option (kwd "payable")) (function None -> false | Some () -> true))
   (kwd "{") fst)
   parameter_pars couple)
   (stm_pars RTReturn) couple)
   (kwd "}") fst
   ns1 (add_fun_to_table nt1 (AnyMeth(t1,get_taglist vl,name))) in
 ns2,
  AnyMethodDecl((t1,get_taglist vl,name),Block(vl,lvl,stm),payable),
  remove_local_vars nt2

let methods_pars s = kleenestar any_meth_pars [] addel s

(*
 * act ::= contract varname { field* meth* }
 *)
let actor_pars : a_contract parser =
 comb_parser (concat (concat (concat (concat (concat
  (kwd "contract")
  varname scd)
  (kwd "{") fst)
  store_pars couple)
  methods_pars couple)
  (kwd "}") fst)
 (fun ((name,fields),methods) -> AContract(assert false (*name*),methods,assert false,fields))

let configuration_pars : configuration parser = kleenestar actor_pars [] addel

let lexer = make_lexer["+"; "-"; "*"; "/"; "("; ")"; ">"; ">="; "=="; "<";
"<="; "!="; "&&"; "||"; "!"; "true"; "false"; "int"; "bool"; 
"="; ","; "fail"; "if"; "then"; "else"; "{"; "function";
"}"; "return"; ":"; "this"; "."; "value"; "balance"; "msg"; "sender" ]

let get_tokens file = remove_minspace (of_token(lexer file));;

let test filename =
 let in_channel = open_in filename in
 let file = Stream.of_channel(in_channel) in
 let (s, conf, tbl) = configuration_pars (get_tokens file) [] in
 print_token_list s;
 print_table tbl;
 pp_configuration conf

let _ = test "demo/transf-example"
