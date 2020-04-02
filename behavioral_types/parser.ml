open MicroSolidity
open ParserCombinators
open Genlex

(** weakly typed expressions **)

type any_ident = AnyIdent : 'a MicroSolidity.ident -> any_ident
type any_expr = AnyExpr : 'a MicroSolidity.tag * 'a MicroSolidity.expr -> any_expr
type any_expr_list = AnyExprList : 'a MicroSolidity.tag_list * 'a MicroSolidity.expr_list -> any_expr_list
type any_tag = AnyTag : 'a MicroSolidity.tag -> any_tag
type any_meth = AnyMeth : ('a,'b) MicroSolidity.meth -> any_meth
type any_var_list = AnyVarList : 'a MicroSolidity.var_list -> any_var_list

let pp_any_expr (AnyExpr (t,e)) = pp_expr t e

let check_type : type a. a MicroSolidity.tag -> any_expr -> a MicroSolidity.expr =
 fun tag (AnyExpr(t, e)) ->
   match MicroSolidity.eq_tag tag t with 
   | Some Refl -> e
   | _ -> raise (Reject (MicroSolidity.pp_expr t e ^ " should have type " ^ MicroSolidity.pp_tag tag))

(** symbol table **)

type any_field_or_fun = 
    | Contract: address -> any_field_or_fun
    | VarOrField: _ MicroSolidity.ident * bool -> any_field_or_fun
    | Fun:  _ MicroSolidity.meth -> any_field_or_fun
type vartable = any_field_or_fun list

let print_table l =
 String.concat ""
  (List.map
    (function
      | Contract a -> MicroSolidity.pp_address a
      | VarOrField (f,_) -> MicroSolidity.pp_field f
      | Fun (meth) -> MicroSolidity.pp_meth meth) l)

let rec get_field : vartable -> string -> (any_ident  * bool) option =
 fun tbl varname -> 
  match tbl with
  | [] -> None
  | VarOrField ((tag, name), islocal )::_ when varname=name ->  Some (AnyIdent(tag,name),islocal)
  | _::tl -> get_field tl varname

let add_field_to_table : vartable -> any_ident -> bool -> vartable =
 fun tbl (AnyIdent(t,fieldname)) is_local -> 
  match get_field tbl fieldname with
  | None -> VarOrField((t,fieldname),is_local)::tbl 
  | Some(AnyIdent _,is_local2) when not is_local2 && is_local -> 
     VarOrField((t,fieldname),is_local)::tbl
  | _ -> raise (Reject (fieldname ^ " declared twice"))

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
  | None -> Fun(t,l,funname)::tbl
  | Some (AnyMeth(_,l',_)) ->
     match eq_tag_list l l' with
        None -> Fun(t,l,funname)::tbl
      | Some Refl -> raise (Reject (funname ^ " redeclared"))

let rec get_contract : vartable -> string -> address option =
 fun tbl name -> 
  match tbl with
  | [] -> None
  | Contract name'::_ when name = name' -> Some name
  | _::tl -> get_contract tl name

let add_contract_to_table : vartable -> address -> vartable =
 fun tbl name -> 
  match get_contract tbl name with
  | None -> Contract name::tbl
  | Some _ -> raise (Reject ("contract " ^ name ^ " redeclared"))

let remove_local_vars: vartable -> vartable =
 fun tbl  -> List.filter (function
  | VarOrField(_, true) -> false
  | _ -> true) tbl

(*Expression *)

let balance e =
 match e with
  | AnyExpr(Address,a) -> AnyExpr(Int,Balance a)
  | _ -> raise (Reject (pp_any_expr e ^ ".balance"))

let plus e1 e2 = 
 match e1,e2 with
 | AnyExpr(Int,v1),AnyExpr(Int,v2) -> AnyExpr(Int,Plus(v1,v2))
 | _ -> raise (Reject (pp_any_expr e1 ^ " + " ^ pp_any_expr e2))
  
let uminus e =
 match e with
  | AnyExpr(Int,e) -> AnyExpr(Int,UMinus(e))
  | _ -> raise (Reject ("-" ^ pp_any_expr e))

let minus e1 e2 = 
 match e1,e2 with
 | AnyExpr(Int,v1),AnyExpr(Int,v2) -> AnyExpr(Int,Minus(v1,v2))
 | _ -> raise (Reject (pp_any_expr e1 ^ " - " ^ pp_any_expr e2))

let mult e1 e2 = 
 match e1,e2 with
 | AnyExpr(Int,v1),AnyExpr(Int,v2) -> AnyExpr(Int,Mult(v1,v2))
 | _ -> raise (Reject (pp_any_expr e1 ^ " * " ^ pp_any_expr e2))

let div e1 e2 = 
 match e1,e2 with
 | AnyExpr(Int,v1),AnyExpr(Int,v2) -> AnyExpr(Int,Div(v1,v2))
 | _ -> raise (Reject (pp_any_expr e1 ^ " / " ^ pp_any_expr e2))

let gt e1 e2 =
 match e1,e2 with
 | AnyExpr(Int,v1),AnyExpr(Int,v2) -> AnyExpr(Bool,Gt(v1,v2))
 | _ -> raise (Reject (pp_any_expr e1 ^ " > " ^ pp_any_expr e2))

let ge e1 e2 =
 match e1,e2 with
 | AnyExpr(Int,v1),AnyExpr(Int,v2) -> AnyExpr(Bool,Geq(v1,v2))
 | _ -> raise (Reject (pp_any_expr e1 ^ " >= " ^ pp_any_expr e2))

let eq e1 e2 = 
 match e1,e2 with
 | AnyExpr(t1,v1),AnyExpr(t2,v2) ->
  (match eq_tag t1 t2 with
  | Some Refl -> AnyExpr(Bool,Eq(t1,v1,v2))
  | _ -> raise (Reject (pp_any_expr e1 ^ " == " ^ pp_any_expr e2)))

let lt e1 e2 = gt e2 e1

let le e1 e2 = ge e2 e1

let andb e1 e2 =
 match e1,e2 with
 | AnyExpr(Bool,v1),AnyExpr(Bool,v2) -> AnyExpr(Bool,And(v1,v2))
 | _ -> raise (Reject (pp_any_expr e1 ^ " && " ^ pp_any_expr e2))


let orb e1 e2 =
 match e1,e2 with
 | AnyExpr(Bool,v1),AnyExpr(Bool,v2) -> AnyExpr(Bool,Or(v1,v2))
 | _ -> raise (Reject (pp_any_expr e1 ^ " || " ^ pp_any_expr e2))


let notb e = 
 match e with
 | AnyExpr(Bool, v) -> AnyExpr(Bool, Not(v))
 | _ -> raise (Reject ("!" ^ pp_any_expr e))

let neq e1 e2 = notb (eq e1 e2)

let varname s t =
 match s with
  | (Ident x) :: tl -> tl,x,("ok",tl),t
  | _ -> raise (Fail ("expected ident",s))

let couple el1 el2 = el1,el2

let var_pars: type a. a tag -> (a expr,'t) parser = fun tag s t ->
 let x =
  try
   List.hd s
  with Failure _ -> raise (Fail ("var expected, eof found",s)) in
const x (fun _ -> 
 let aux : a expr =
 match tag,s,t with
 | _,(Ident var)::_,tbl -> 
  (match get_field tbl var with
    | Some (AnyIdent(tagfield,name),islocal) ->
       (match eq_tag tagfield tag,islocal with
         | Some Refl,false -> MicroSolidity.Field(tagfield,name)
         | Some Refl,true -> Var(tagfield,name)
         | None,_ -> raise (Reject (pp_tag tagfield ^ " vs " ^ pp_tag tag)))
    | None -> raise (Reject (var ^ " not previously declared")))
 | _ -> raise (Reject ("ident expected")) in aux) s t

let value : type a. a MicroSolidity.tag -> vartable -> Genlex.token -> a MicroSolidity.expr = fun tag tbl tok ->
 match tag,tok with
 | Int,Int x -> Value x
 | Bool,Kwd "true" -> Value true
 | Bool,Kwd "false" -> Value false
 | Address,Ident x ->
    (match get_contract tbl x with
        None -> raise (Reject ("value of type " ^ pp_tag tag ^ " expected"))
      | Some a -> Value a)
 | _ -> raise (Reject ("value of type " ^ pp_tag tag ^ " expected"))

let value_pars tag s tbl =
 let t =
  try
   List.hd s
  with Failure _ -> raise (Fail ("value expected, eof found",s)) in
 const t (value tag tbl) s tbl

let this_pars = const (Kwd "this") (fun _ -> MicroSolidity.This)

let brackets_pars pars = concat (concat (kwd "(") pars csnd) (kwd ")") cfst

let msg_sender_pars =
 comb_parser
  (concat (concat (kwd "msg") (kwd ".") csnd) (kwd "sender") csnd)
  (fun () -> MsgSender)

let msg_value_pars =
 comb_parser
  (concat (concat (kwd "msg") (kwd ".") csnd) (kwd "value") csnd)
  (fun () -> AnyExpr(Int,MsgValue))

(*Variable | value *)
let base tag s tbl =
    choice_list[
        var_pars tag;
        value_pars tag;
    ] s tbl

(* Int Expression
 * atomic_int_expr :=
    base Int | msg.value | address.balance | - atomic_int_expr | varname | ( int_expr ) | string
 * mul_int_expr := atomic_int_expr  (( * | / ) atomic_int_expr)*
 * int_expr := mul_int_expr  (( + | - ) mul_int_expr)*
 *)
let rec atomic_int_expr s = 
 choice_list [
   msg_value_pars;
   balance_pars;
   comb_parser (base Int) (fun expr -> AnyExpr(Int,expr));
   concat (kwd "-") atomic_int_expr (fun _ -> uminus) ;
   brackets_pars int_expr
 ] s
and mul_int_expr s = nelist atomic_int_expr mul_binop s
and int_expr s = nelist mul_int_expr add_binop s
and add_binop s =
 choice_list [
  const (Kwd "+") (fun _ -> plus) ;
  const (Kwd "-") (fun _ -> minus)
 ] s
and mul_binop s =
 choice_list [
  const (Kwd "*") (fun _ -> mult) ;
  const (Kwd "/") (fun _ -> div) ;
 ] s

 (* Bool Expression
 * atomic_bool_expr :=
    bool | int_expr > int_expr  | int_expr >= int_expr  | int_expr <
    int_expr | int_expr <= int_expr | expr == expr | varname | ( bool_expr
    ) | ! bool_expr
 * bool_expr := atomic_int_expr ?cont_int_expr
 * cont_bool_expr ::=  && bool_expr | || bool_expr 
 *)
and atomic_bool_expr s =
 choice_list[
  comb_parser (base Bool) (fun expr -> AnyExpr(Bool,expr));
  concat (concat (kwd "(") bool_expr csnd) (kwd ")") cfst ;
  concat (kwd "!") atomic_bool_expr (fun _ -> notb) ;
  concat int_expr (concat cmpop int_expr (fun f y x -> f x y)) (fun x f -> f x);
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
and eq_bool_expr s = nelist (choice_list [atomic_bool_expr ; int_expr ; contract_expr]) eqop s
and and_bool_expr s = nelist eq_bool_expr and_binop s
and bool_expr s = nelist and_bool_expr or_binop s
and and_binop s =
 choice_list [
  const (Kwd "&&") (fun _ -> andb) ;
 ] s
and or_binop s =
 choice_list [
  const (Kwd "||") (fun _ -> orb) ;
 ] s

(* ... ::= contract.balance *)
and balance_pars s =
 concat (concat contract_expr (kwd ".") cfst) (kwd "balance")
  (fun a _ -> balance a) s
(*
 * contr_expr ::= this | Var
 *)
and contract_expr s = 
 let rec aux s =
  choice_list [
   msg_sender_pars;
   base Address; 
   this_pars;
   brackets_pars aux;
   ] s
 in 
 comb_parser aux (fun expr -> AnyExpr(Address, expr)) s

and expr_pars s =
 choice_list [
  concat (concat (kwd "(") expr_pars csnd) (kwd ")") cfst;
  int_expr;
  bool_expr;
  contract_expr
 ] s

(*
* t ::= int | bool
*)
let type_pars =
 let tag_pars str tag = const (Kwd str) (fun _ -> AnyTag tag) in
 choice_list[
  tag_pars "int" Int;
  tag_pars "bool" Bool;
  tag_pars "address" Address;
]

let field_pars islocal s t = 
 let ns,field,error,tbl =
  concat (concat
   type_pars
   varname (fun (AnyTag t) v -> AnyIdent (t,v)))
   (kwd ";") cfst s t in 
 let x =
  try
   add_field_to_table tbl field islocal
  with
   Reject msg -> raise (Fail (best error (msg,s)))
 in
  ns,field,error,x

(*
 * fields ::= decl*
 *)
let fields_pars =
 comb_parser (kleenestar (field_pars false) [] addel)
  (List.map (fun (AnyIdent (tag,id)) -> AnyField (tag,id)))

let rec expr_list_of_any_expr_list : any_expr list -> any_expr_list =
 function
    [] -> AnyExprList(TNil,ENil)
  | AnyExpr(t,e)::tl ->
     let AnyExprList(ts,es) = expr_list_of_any_expr_list tl in
      AnyExprList(TCons(t,ts),ECons(e,es))

let parse_any_expr_list = 
 comb_parser 
 (brackets_pars
   (option2 [] (concat
     expr_pars 
     (kleenestar (concat (kwd ",") expr_pars csnd) [] addel) List.cons)))
  expr_list_of_any_expr_list

let opt_expr : type a. a tag -> any_expr -> a expr option = fun t -> 
 function
  | AnyExpr(texp,e) -> 
    match eq_tag texp t with 
     | Some Refl -> Some e
     | None -> None 

let ident_pars s t =
 match s with
    Ident i::tl -> tl,i,("ok",tl),t
  | _ -> raise (Fail ("ident expected",s))

let dot_value_pars s t=
  comb_parser (
   option (concat (concat
    (kwd ".") 
    (kwd "value") csnd)
    (brackets_pars int_expr) csnd))
   (fun x -> Option.bind x (opt_expr Int)) s t

(*
 * call_contr ::= contr_expr.varname (.value)? (( (e (, e)* ? )
 *)
let call_pars tag =
 comb_parser (concat (concat (concat
  (option2 (AnyExpr(Address,This)) (concat contract_expr (kwd ".") cfst))
  ident_pars couple)
  dot_value_pars couple)
  parse_any_expr_list couple)
 (fun (((addr,name),value),params) ->
   let addr = check_type Address addr in
   let AnyExprList(tags,exprs) = params in
   let name = tag,tags,name in
   Call(addr,name,value,exprs))

let rhs_pars : 'a tag -> ('a rhs,'t) parser = fun tag ->
 choice_list [
  comb_parser expr_pars
   (fun expr -> MicroSolidity.Expr (check_type tag expr)) ;
  call_pars tag
 ]

type 'a rettag = RTEpsilon : [`Epsilon] rettag | RTReturn : [`Return] rettag

let revert_pars : 'a tag -> 'b rettag -> (('a,'b) stm,'t) parser = fun _ _ s t ->
 concat (concat (concat
  (kwd "revert")
  (kwd "(") csnd)
  (kwd ")") csnd)
  (kwd ";") (fun _ _ -> MicroSolidity.Revert) s t

let epsilon_pars : type a b. a tag -> b rettag -> ((a,b) stm,'t) parser =
 fun tag rettag s t ->
  match rettag,tag with
    RTEpsilon,_ -> s,MicroSolidity.Epsilon,("ok",s),t 
  | RTReturn,Unit -> s,MicroSolidity.Return,("ok",s),t
  | RTReturn,_ -> raise (Fail ("implicit return not allowed here",s))

let return_pars : type a. a tag -> 'b rettag -> ((a,'b) stm,'t) parser = fun tag _ ->
 concat (concat
  (kwd "return")
  (option (rhs_pars tag)) csnd)
  (kwd ";")
    (fun rhs () ->
      match rhs,tag with
       | Some rhs,_ -> MicroSolidity.ReturnRhs rhs
       | None,Unit -> MicroSolidity.Return
       | None,_ -> raise (Reject ("return without value of type " ^ pp_tag tag)))
    
(*
 * stm ::= revert | return expr | assign | if bool_expr then stm else stm ; stm | { stm } | epsilon
 *)
let rec stm_pars : type a b. a tag -> b rettag -> ((a,b) stm,'t) parser = fun tag rettag s t ->
 choice_list[
  (* revert *)
  revert_pars tag rettag ;

  (* return *)
  return_pars tag rettag ;

  (*assign*)
  assign_pars tag rettag;

  (*if then else*)
  comb_parser (concat (concat (concat (concat
   (kwd "if")
   bool_expr csnd)
   (stm_pars tag RTEpsilon) couple)
   (option (concat (kwd "else") (stm_pars tag RTEpsilon) csnd)) couple)
   (stm_pars tag rettag) couple)
   (fun (((bexpr,stm1),stm2),stm3) ->
     let stm2 = Option.value stm2 ~default:Epsilon in 
     IfThenElse(check_type Bool bexpr,stm1,stm2,stm3));

  (* {stm} *)
  concat (kwd "{") (concat (stm_pars tag rettag) (kwd "}") cfst) csnd;

  (* epsilon *)
  epsilon_pars tag rettag
 ] s t

(*assign ::= [var|field =] rhs*)
and assign_pars : type a b. a tag -> b rettag -> ((a,b) stm,'t) parser =
 fun tag rettag s t ->
  let s1,var,error1,t1 = option (concat varname (kwd "=") cfst) s t in
  let aux : type c. c tag -> c lhs -> ((a,b) stm,'t) parser = fun lhstag lhs s1 t1 ->
   let s2,(rhs,cont),error2,t2 =
    concat (concat (rhs_pars lhstag) (kwd ";") cfst) (stm_pars tag rettag) couple s1 t1 in
   s2,Assign(lhs,rhs,cont),best (best error1 error2) ("ok",s2),t2 in
  match Option.map (get_field t1) var with
     None -> aux Unit LDiscard s1 t1
   | Some None -> raise (Fail (best ("Unknown field/var",s)error1))
   | Some (Some (AnyIdent(lhstag,id),true)) ->
      aux lhstag (LVar(lhstag,id)) s1 t1
   | Some (Some (AnyIdent(lhstag,id),false)) ->
      aux lhstag (LField(lhstag,id)) s1 t1

let rec add_local_var tbl =
  function 
   | AnyVarList VNil -> tbl
   | AnyVarList (VCons(h,tl)) -> 
    add_local_var (add_field_to_table tbl (AnyIdent h) true) (AnyVarList tl)
  
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

let pars_varlist_singleton =
 concat type_pars varname 
  (fun (AnyTag t) s -> (AnyVarList(VCons((t,s),VNil))))

(*
* parameters ::= t Var (, t Var)* ?
*)
let parameter_pars s t = 
 let ns,vl,error,nt = 
  brackets_pars (option2 (AnyVarList VNil) (concat pars_varlist_singleton
  (kleenestar (concat (kwd ",") pars_varlist_singleton csnd) 
  (AnyVarList(VNil)) varlist_append) varlist_append))
  s t in
 let x =
  try
   add_local_var nt vl
  with Reject msg -> raise (Fail (best error (msg,ns))) in
 ns,vl,error,x

(*
* vars ::= t Var; (t Var;)* ?
*)
let vars_pars s t = 
 let ns,vl,error,nt = 
  kleenestar (concat pars_varlist_singleton (kwd ";") cfst) (AnyVarList(VNil))
   varlist_append s t in
 let x =
  try
   add_local_var nt vl
  with Reject msg -> raise (Fail (best error (msg,ns))) in
 ns,vl,error,x

(* [payable] { paramterms stm } *)
let block_pars ?(check_payable=false) tag vl s t =
 let ns2,((payable,AnyVarList lvl),stm),error2,nt2 = 
  concat (concat (concat (concat
   (comb_parser (option (kwd "payable")) (function None -> if check_payable then raise (Reject "must be payable") ; false | Some () -> true))
   (kwd "{") cfst)
   vars_pars couple)
   (stm_pars tag RTReturn) couple)
   (kwd "}") cfst
   s t in
 ns2, (Block(vl,lvl,stm),payable), error2, remove_local_vars nt2

(*
 * meth ::= function Var parameters : t { paramters stm }
 *)
let any_meth_pars s t =
 let ns1,((name,AnyVarList vl),(AnyTag t1)),error1,nt1 =
  concat (concat (concat
   (kwd "function")
   varname csnd)
   parameter_pars couple)
   (option2 (AnyTag Unit) ((concat (kwd "returns") (brackets_pars type_pars)) csnd)) couple
   s t in
 let nt1 =
  try
   add_fun_to_table nt1 (AnyMeth(t1,get_taglist vl,name))
  with Reject msg -> raise (Fail (best (msg,s) error1)) in
 let ns2,(block,payable),error2,nt2 = block_pars t1 vl ns1 nt1 in
 ns2,
  AnyMethodDecl((t1,get_taglist vl,name),block,payable),
  best error1 error2,
  remove_local_vars nt2

let methods_pars s = kleenestar any_meth_pars [] addel s

let fallback_pars =
 comb_parser (concat (concat (concat
  (kwd "function")
  (kwd "(") cfst)
  (kwd ")") cfst)
  (block_pars ~check_payable:true Unit VNil) csnd)
  (function
      block,true -> block
    | _,false -> assert false)

(*
 * act ::= contract varname { field* meth* }
 *)
let actor_pars : (a_contract,'t) parser =
 comb_parser (concat (concat (concat (concat (concat (concat
  (kwd "contract")
  varname csnd)
  (kwd "{") cfst)
  fields_pars couple)
  methods_pars couple)
  (option fallback_pars) couple)
  (kwd "}") cfst)
 (fun (((name,fields),methods),fallback) -> AContract(name,methods,fallback,fields))

let configuration_pars : (configuration,'t) parser =
 concat (kleenestar actor_pars [] addel) eof cfst

let lexer = make_lexer["+"; "-"; "*"; "/"; "("; ")"; ">"; ">="; "=="; "<";
"<="; "!="; "&&"; "||"; "!"; "true"; "false"; "int"; "bool"; "address";
"="; ","; ";"; "fail"; "if"; "else"; "revert"; "{"; "function";
"}"; "return"; "returns"; "this"; "."; "value"; "balance"; "msg"; "sender" ; "contract" ; "payable" ]

let initialize_table_with_contracts tokens =
 let rec skip_to_end_of_contract n =
  function
     Kwd "{" :: tl -> skip_to_end_of_contract (n+1) tl
   | Kwd "}" :: tl ->
      if n = 0 then tl else skip_to_end_of_contract (n-1) tl
   | [] -> raise (Fail ("} expected, but eof found",[]))
   | _ :: tl -> skip_to_end_of_contract n tl in
 let rec aux acc =
  function
     [] -> acc
   | (Kwd "contract" :: Ident id :: Kwd "{" :: tl) as l ->
      let acc =
       try add_contract_to_table acc id
       with Reject msg -> raise (Fail (msg,l)) in
      aux acc (skip_to_end_of_contract 0 tl)
   | l -> raise (Fail ("contract declaration expected",l))
 in
  List.rev (aux [] tokens)

let test_stream f stream =
 try
  let tokens = get_tokens lexer stream in
  let tbl = initialize_table_with_contracts tokens in
  let _s, conf, _error, _tbl = configuration_pars tokens tbl in
(*
  "######## TOKENS #######\n" ^
  print_token_list s ^
  "######## TABLE #######\n" ^
  print_table tbl ^
  "######## PROGRAM #######" ^
*)
  f conf
 with
  | Fail (msg,l) ->
     "######## SYNTAX ERROR #######\n" ^
     "<< " ^ msg ^ " >>\n" ^
     print_token_list l
  | exn ->
     "######## UNHANLDED EXCEPTION #######\n" ^
     Printexc.to_string exn

let test_file f filename =
 let in_channel = open_in filename in
 let stream = Stream.of_channel in_channel in
 test_stream f stream

let test_string f s =
 let stream = Stream.of_string s in
 test_stream f stream

(* to avoid warnings for unused functions *)
let _ = print_table
