open MicroSolidity
open ParserCombinator
open Genlex

(* weakly typed expressions *)

type any_expr = AnyExpr : 'a MicroSolidity.tag * 'a MicroSolidity.expr -> any_expr
type any_tag = AnyTag : 'a MicroSolidity.tag -> any_tag
type any_meth = AnyMeth : ('a,'b) MicroSolidity.meth -> any_meth
type any_var_list = AnyVarList : 'a MicroSolidity.var_list -> any_var_list
type any_rhs = AnyRhs: 'a MicroSolidity.tag * 'a MicroSolidity.rhs -> any_rhs

let check_type : type a. a MicroSolidity.tag -> any_expr -> a MicroSolidity.expr =
 fun tag (AnyExpr(t, e)) ->
   match MicroSolidity.eq_tag tag t with 
   | Some Refl -> e
   | _ -> raise (Fail (`Typing (MicroSolidity.pp_expr t e ^ " should have type " ^ MicroSolidity.pp_tag tag)))


let pp_any_expr (AnyExpr (t,e)) = pp_expr t e

(* symbol table *)

type any_field_or_fun = 
    | Field: _ MicroSolidity.field * bool -> any_field_or_fun
    | Fun:  _ MicroSolidity.meth -> any_field_or_fun
type vartable = any_field_or_fun list

let print_table l =
 String.concat ""
  (List.map
    (function
      | Field (f,_) -> MicroSolidity.pp_field f
      | Fun (meth) -> MicroSolidity.pp_meth meth) l)

let rec get_field : vartable -> string -> (MicroSolidity.any_field  * bool) option =
 fun tbl varname -> 
  match tbl with
  | [] -> None
  | Field ((tag, name), islocal )::_ when varname=name ->  Some (AnyField(tag,
  name),islocal)
  | _::tl -> get_field tl varname

let add_field_to_table : vartable -> MicroSolidity.any_field -> bool -> vartable =
 fun tbl (AnyField(t,fieldname)) is_local -> 
  match get_field tbl fieldname with
  | None -> List.append ([Field((t,fieldname),is_local)]) tbl 
  | Some(AnyField(tag,_),_) -> 
   (match MicroSolidity.eq_tag tag t with
   | Some Refl -> tbl
   | None -> raise (Fail (`Typing (MicroSolidity.pp_tag tag ^ " vs " ^ MicroSolidity.pp_tag t))))

let rec get_fun : vartable -> string -> any_meth option =
 fun tbl funname -> 
  match tbl with
  | [] -> None
  | Fun (rettag, tagl, name)::_ when funname=name -> Some (AnyMeth(rettag, tagl,
  name))
  | _::tl -> get_fun tl funname

let add_fun_to_table : vartable -> any_meth -> vartable =
 fun tbl (AnyMeth(t,l,funname)) -> 
  match get_fun tbl funname with
  | None -> List.append ([Fun(t,l,funname)]) tbl
  | _ -> raise (Fail (`Typing (funname ^ "(..) not found")))

let remove_local_vars: vartable -> vartable =
 fun tbl  -> List.filter (function
  | Field(_, true) -> false
  | _ -> true) tbl

(*Expression *)

let plus e1 e2 = 
 match e1,e2 with
 | AnyExpr(Int,v1),AnyExpr(Int,v2) -> AnyExpr(Int,Plus(v1,v2))
 | _ -> raise (Fail (`Typing (pp_any_expr e1 ^ " + " ^ pp_any_expr e2)))
  
let uminus e =
 match e with
  | AnyExpr(Int,e) -> AnyExpr(Int,UMinus(e))
  | _ -> raise (Fail (`Typing ("-" ^ pp_any_expr e)))

let minus e1 e2 = 
 match e1,e2 with
 | AnyExpr(Int,v1),AnyExpr(Int,v2) -> AnyExpr(Int,Minus(v1,v2))
 | _ -> raise (Fail (`Typing (pp_any_expr e1 ^ " - " ^ pp_any_expr e2)))

let mult e1 e2 = 
 match e1,e2 with
 | AnyExpr(Int,v1),AnyExpr(Int,v2) -> AnyExpr(Int,Mult(v1,v2))
 | _ -> raise (Fail (`Typing (pp_any_expr e1 ^ " * " ^ pp_any_expr e2)))

let div e1 e2 = 
 match e1,e2 with
 | AnyExpr(Int,v1),AnyExpr(Int,v2) -> AnyExpr(Int,Div(v1,v2))
 | _ -> raise (Fail (`Typing (pp_any_expr e1 ^ " / " ^ pp_any_expr e2)))

let gt e2 e1 =
 match e1,e2 with
 | AnyExpr(Int,v1),AnyExpr(Int,v2) -> AnyExpr(Bool,Gt(v1,v2))
 | _ -> raise (Fail (`Typing (pp_any_expr e1 ^ " > " ^ pp_any_expr e2)))

let ge e2 e1 =
 match e1,e2 with
 | AnyExpr(Int,v1),AnyExpr(Int,v2) -> AnyExpr(Bool,Geq(v1,v2))
 | _ -> raise (Fail (`Typing (pp_any_expr e1 ^ " >= " ^ pp_any_expr e2)))

let eq e2 e1 = 
 match e1,e2 with
 | AnyExpr(t1,v1),AnyExpr(t2,v2) ->
  (match eq_tag t1 t2 with
  | Some Refl -> AnyExpr(Bool,Eq(t1,v1,v2))
  | _ -> raise (Fail (`Typing (pp_any_expr e1 ^ " == " ^ pp_any_expr e2))))

let lt e1 e2 = gt e2 e1

let le e1 e2 = ge e2 e1

let andb e2 e1 =
 match e1,e2 with
 | AnyExpr(Bool,v1),AnyExpr(Bool,v2) -> AnyExpr(Bool,And(v1,v2))
 | _ -> raise (Fail (`Typing (pp_any_expr e1 ^ " && " ^ pp_any_expr e2)))


let orb e2 e1 =
 match e1,e2 with
 | AnyExpr(Bool,v1),AnyExpr(Bool,v2) -> AnyExpr(Bool,Or(v1,v2))
 | _ -> raise (Fail (`Typing (pp_any_expr e1 ^ " || " ^ pp_any_expr e2)))


let notb e = 
 match e with
 | AnyExpr(Bool, v) -> AnyExpr(Bool, Not(v))
 | _ -> raise (Fail (`Typing ("!" ^ pp_any_expr e)))

let scd_notb _ e = notb e

let neq e1 e2 = notb (eq e1 e2)

let varname s t =
 match s with
  | (Ident x) :: tl -> tl,x,t
  | _ -> raise (Fail (`Syntax s))

let couple el1 el2 = el1,el2

let var_pars: type a. a tag -> (a expr,'t) parser = fun tag s t ->
const (List.hd s) (fun _ -> 
 let aux : a expr =
 (match tag,s,t with
 | _,(Ident var)::_,tbl -> 
  (match get_field tbl var with
    | Some (AnyField(tagfield,name),islocal) ->
       (match eq_tag tagfield tag,islocal with
         | Some Refl,false -> MicroSolidity.Field(tagfield,name)
         | Some Refl,true -> Var(tagfield,name)
         | None,_ -> raise (Fail (`Typing (pp_tag tagfield ^ " vs " ^ pp_tag tag))))
    | None -> 
(*XXX qua dovrei parsare i nomi dei contratti in indirizzi!
    (match tag with 
    | Address -> Value var
    | _ -> raise Fail)) *) raise (Fail (`Typing (var ^ " not found"))))
 | _ -> raise (Fail (`Syntax s))) in aux) s t

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
  concat (concat
   type_pars
   varname (fun (AnyTag t) v -> AnyField (t,v)))
   (kwd ";") fst s t in 
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
  | TNil,_ -> raise (Fail (`Typing "too many args"))
  | _,[] -> raise (Fail (`Typing "not enough args"))

let concat_list : type b. b tag_list -> (b expr_list -> 'c) -> ('c,'t) parser =
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
    | _ -> raise (Fail (`Typing "not a function call")))
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
    (match eq_tag t tag with
        Some Refl -> r
      | None -> raise (Fail (`Typing (pp_tag t ^ " vs " ^ pp_tag tag))))

let pars_mesg_value s t= try comb_parser (concat (kwd ".") 
    (concat (kwd "value") (brackets_pars int_expr) scd) scd) (opt_expr Int) s t
    with Fail _ -> (s,None,t)

let funname s tbl = 
 comb_parser varname
  (fun var ->
    match get_fun tbl var with
       Some _ -> var
     | None -> raise (Fail (`Typing (var ^ "(..) not found ")))) s tbl

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

let revert_pars : 'a tag -> 'b rettag -> (('a,'b) stm,'t) parser = fun _ _ s t ->
 const (Kwd "revert") (fun _ -> MicroSolidity.Revert) s t

let epsilon_pars : type b. 'a tag -> b rettag -> (('a,b) stm,'t) parser =
 fun _ rettag s t ->
  match rettag with
    RTEpsilon -> s,MicroSolidity.Epsilon,t 
  | RTReturn -> raise (Fail (`Typing "epsilon not allowed here"))

let return_pars : 'a tag -> 'b rettag -> (('a,'b) stm,'t) parser = fun tag _ ->
 concat
  (kwd "return")
  expr_pars
  (fun () expr -> MicroSolidity.Return (check_type tag expr))
    
(*
 * stm ::= revert | return expr | assign | if bool_expr then stm else stm ; stm | { stm } | epsilon
 *)
let rec stm_pars : type b. 'a tag -> b rettag -> (('a,b) stm,'t) parser = fun tag rettag s t ->
 choice_list[
  (* revert *)
  revert_pars tag rettag ;

  (* return *)
  return_pars tag rettag ;

(*XXX
  (*assign*)
  assign_pars;
*)
  (*if then else*)
  comb_parser (concat (concat (concat (concat (concat (concat (concat
   (kwd "if")
   bool_expr scd)
   (kwd "then") fst)
   (stm_pars tag RTEpsilon) couple)
   (kwd "else") fst)
   (stm_pars tag RTEpsilon) couple)
   (kwd ";") fst)
   (stm_pars tag rettag) couple)
   (fun (((bexpr,stm1),stm2),stm3) ->
     IfThenElse(check_type Bool bexpr,stm1,stm2,stm3));

  (* {stm} *)
  concat (kwd "{") (concat (stm_pars tag rettag) (kwd "}") fst) scd;

  (* epsilon *)
  epsilon_pars tag rettag
 ] s t

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
let parameter_pars s t = 
 let pars_varlist_singleton =
  concat type_pars varname 
   (fun (AnyTag t) s -> (AnyVarList(VCons((t,s),VNil)))) in
 let (ns,vl,nt) = 
  comb_parser (option (concat pars_varlist_singleton
  (kleenestar (concat (kwd ",") pars_varlist_singleton scd) 
  (AnyVarList(VNil)) varlist_append) varlist_append))
  (function Some s -> s | None -> AnyVarList(VNil)) s t in
 ns,vl,add_local_var nt vl

(* [payable] { paramterms stm } *)
let block_pars tag vl s t =
 let (ns2,((payable,AnyVarList lvl),stm),nt2) = 
  concat (concat (concat (concat
   (comb_parser (option (kwd "payable")) (function None -> false | Some () -> true))
   (kwd "{") fst)
   parameter_pars couple)
   (stm_pars tag RTReturn) couple)
   (kwd "}") fst
   s t in
 ns2, (Block(vl,lvl,stm),payable), remove_local_vars nt2

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
 let (ns2,(block,payable),nt2) = 
  block_pars t1 vl ns1 (add_fun_to_table nt1 (AnyMeth(t1,get_taglist vl,name))) in
 ns2,
  AnyMethodDecl((t1,get_taglist vl,name),block,payable),
  remove_local_vars nt2

let methods_pars s = kleenestar any_meth_pars [] addel s

let fallback_pars =
 comb_parser (concat (concat (concat
  (kwd "function")
  (kwd "(") fst)
  (kwd ")") fst)
  (block_pars Int VNil) scd)
  (function
      block,true -> block
    | _,false -> raise (Fail (`Typing "the fallback method must be payable")))

(*
 * act ::= contract varname { field* meth* }
 *)
let actor_pars : (a_contract,'t) parser =
 comb_parser (concat (concat (concat (concat (concat (concat
  (kwd "contract")
  varname scd)
  (kwd "{") fst)
  store_pars couple)
  methods_pars couple)
  (option fallback_pars) couple)
  (kwd "}") fst)
 (fun (((name,fields),methods),fallback) -> AContract(name,methods,fallback,fields))

let configuration_pars : (configuration,'t) parser =
 kleenestar_eof actor_pars [] addel

let lexer = make_lexer["+"; "-"; "*"; "/"; "("; ")"; ">"; ">="; "=="; "<";
"<="; "!="; "&&"; "||"; "!"; "true"; "false"; "int"; "bool"; 
"="; ","; ";"; "fail"; "if"; "then"; "else"; "{"; "function";
"}"; "return"; ":"; "this"; "."; "value"; "balance"; "msg"; "sender" ; "contract" ; "payable" ]

let get_tokens file = remove_minspace (of_token(lexer file));;

let test_stream stream =
 try
  let (_s, conf,_tbl) = configuration_pars (get_tokens stream) [] in
(*
  "######## TOKENS #######\n" ^
  print_token_list s ^
  "######## TABLE #######\n" ^
  print_table tbl ^
  "######## PROGRAM #######" ^
*)
  pp_configuration conf
 with
  | Fail (`Syntax l) ->
     "######## SYNTAX ERROR #######\n" ^
     print_token_list l ^
     "error"
  | Fail (`Typing msg) ->
     "######## TYPING ERROR #######\n" ^
     msg ^
     "error"

let test_file filename =
 let in_channel = open_in filename in
 let stream = Stream.of_channel in_channel in
 test_stream stream

let test_string s =
 let stream = Stream.of_string s in
 test_stream stream
