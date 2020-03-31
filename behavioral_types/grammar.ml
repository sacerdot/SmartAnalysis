open MicroSolidity
open ParserCombinator
open Genlex

(** weakly typed expressions **)

type any_ident = AnyIdent : 'a MicroSolidity.ident -> any_ident
type any_expr = AnyExpr : 'a MicroSolidity.tag * 'a MicroSolidity.expr -> any_expr
type any_expr_list = AnyExprList : 'a MicroSolidity.tag_list * 'a MicroSolidity.expr_list -> any_expr_list
type any_tag = AnyTag : 'a MicroSolidity.tag -> any_tag
type any_meth = AnyMeth : ('a,'b) MicroSolidity.meth -> any_meth
type any_var_list = AnyVarList : 'a MicroSolidity.var_list -> any_var_list
(*
type any_rhs = AnyRhs: 'a MicroSolidity.tag * 'a MicroSolidity.rhs -> any_rhs
*)

let pp_any_expr (AnyExpr (t,e)) = pp_expr t e

let check_type : type a. a MicroSolidity.tag -> any_expr -> a MicroSolidity.expr =
 fun tag (AnyExpr(t, e)) ->
   match MicroSolidity.eq_tag tag t with 
   | Some Refl -> e
   | _ -> raise (Reject (MicroSolidity.pp_expr t e ^ " should have type " ^ MicroSolidity.pp_tag tag))

(** symbol table **)

type any_field_or_fun = 
    | VarOrField: _ MicroSolidity.ident * bool -> any_field_or_fun
    | Fun:  _ MicroSolidity.meth -> any_field_or_fun
type vartable = any_field_or_fun list

let print_table l =
 String.concat ""
  (List.map
    (function
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
  | None -> List.append ([VarOrField((t,fieldname),is_local)]) tbl 
  | Some(AnyIdent(tag,_),_) -> 
   (match MicroSolidity.eq_tag tag t with
   | Some Refl -> tbl
   | None -> raise (Reject (MicroSolidity.pp_tag tag ^ " vs " ^ MicroSolidity.pp_tag t)))

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
  | _ -> raise (Reject (funname ^ "(..) not found"))

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

let gt e2 e1 =
 match e1,e2 with
 | AnyExpr(Int,v1),AnyExpr(Int,v2) -> AnyExpr(Bool,Gt(v1,v2))
 | _ -> raise (Reject (pp_any_expr e1 ^ " > " ^ pp_any_expr e2))

let ge e2 e1 =
 match e1,e2 with
 | AnyExpr(Int,v1),AnyExpr(Int,v2) -> AnyExpr(Bool,Geq(v1,v2))
 | _ -> raise (Reject (pp_any_expr e1 ^ " >= " ^ pp_any_expr e2))

let eq e2 e1 = 
 match e1,e2 with
 | AnyExpr(t1,v1),AnyExpr(t2,v2) ->
  (match eq_tag t1 t2 with
  | Some Refl -> AnyExpr(Bool,Eq(t1,v1,v2))
  | _ -> raise (Reject (pp_any_expr e1 ^ " == " ^ pp_any_expr e2)))

let lt e1 e2 = gt e2 e1

let le e1 e2 = ge e2 e1

let andb e2 e1 =
 match e1,e2 with
 | AnyExpr(Bool,v1),AnyExpr(Bool,v2) -> AnyExpr(Bool,And(v1,v2))
 | _ -> raise (Reject (pp_any_expr e1 ^ " && " ^ pp_any_expr e2))


let orb e2 e1 =
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
    | None -> 
(*XXX qua dovrei parsare i nomi dei contratti in indirizzi!
    (match tag with 
    | Address -> Value var
    | _ -> raise Fail)) *) raise (Reject (var ^ " not found")))
 | _ -> raise (Reject ("ident expected")) in aux) s t

let value : type a. a MicroSolidity.tag -> Genlex.token -> a MicroSolidity.expr = fun tag tok ->
 match tag,tok with
 | Int,Int x -> Value x
 | Bool,Kwd "true" -> Value true
 | Bool,Kwd "false" -> Value false
 | _ -> raise (Reject ("value expected"))

let value_pars tag s =
 let t =
  try
   List.hd s
  with Failure _ -> raise (Fail ("value expected, eof found",s)) in
 const t (value tag) s

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
 * int_expr := atomic_int_expr ?cont_int_expr
 * cont_int_expr ::=  + int_expr | * int_expr | / int_expr | - int_expr 
 *)
let rec atomic_int_expr s = 
 choice_list [
   msg_value_pars;
   balance_pars;
   comb_parser (base Int) (fun expr -> AnyExpr(Int,expr));
   concat (kwd "-") atomic_int_expr (fun _ -> uminus) ;
   brackets_pars int_expr
 ] s
and int_expr s =
 concat atomic_int_expr (option cont_int_expr) (fun x f -> match f with Some funct -> funct x | _ -> x) s
and binop s =
 choice_list [
  const (Kwd "+") (fun _ -> plus) ;
  const (Kwd "*") (fun _ -> mult) ;
  const (Kwd "/") (fun _ -> div) ;
  const (Kwd "-") (fun _ -> minus)
 ] s
and cont_int_expr s = concat binop int_expr (fun f x y -> f y x) s

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
 concat atomic_bool_expr (option cont_bool_expr) (fun x f -> match f with Some y -> y x | _ -> x) s
and bin_bool_op s =
 choice_list [
  const (Kwd "&&") (fun _ -> andb) ;
  const (Kwd "||") (fun _ -> orb) ;
  eqop;
 ] s
and cont_bool_expr s = concat (choice bin_bool_op eqop) bool_expr (fun f x -> f x) s
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

(*
let rec check_expr_list_type: type a. a tag_list -> any_expr list -> a expr_list 
= fun tl el ->
 match tl,el with
  | TNil,[] -> ENil
  | TCons(t,ttail),(h::etail) -> 
    ECons(check_type t h,check_expr_list_type ttail etail)
  | TNil,_ -> raise (Reject "too many args")
  | _,[] -> raise (Reject "not enough args")
*)

(*
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
    | _ -> raise (Reject ("not a function call")))
  in aux (List.rev el) (Call(c,(typ,TNil,m),value,ENil))
*)

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

(*
let check_rhs_type: type a. a tag -> any_rhs -> a rhs =
 fun tag rhs ->
  match rhs with
  | AnyRhs(t,r) -> 
    (match eq_tag t tag with
        Some Refl -> r
      | None -> raise (Reject (pp_tag t ^ " vs " ^ pp_tag tag)))
*)

(*
let pars_mesg_value s t=
  comb_parser (
   option (concat (concat
    (kwd ".") 
    (kwd "value") csnd)
    (brackets_pars int_expr) csnd))
   (fun x -> Option.bind x (opt_expr Int)) s t
*)

(*
let funname s tbl = 
 comb_parser varname
  (fun var ->
    match get_fun tbl var with
       Some _ -> var
     | None -> raise (Reject (var ^ "(..) not found "))) s tbl
*)

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
 let (ns0, contr, nt0) = comb_parser (concat contract_expr (kwd ".") cfst)
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
(rhs_toassign_pars this_opt varname) csnd) (kwd ")") cfst) (aux this_opt varname) s
*)

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

(*
(*assign ::= Var = rhs*)
let assign_pars s tbl =
 let (ns0,this_opt,ntbl0) = option (concat this_pars (kwd ".") cfst) s tbl in
 let (ns1,varname, ntbl1) = concat varname (kwd "=") cfst ns0 ntbl0 in
 rhs_toassign_pars this_opt varname ns1 ntbl1
*)

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

let rhs_pars : 'a tag -> ('a rhs,'t) parser = fun tag ->
 choice_list [
  comb_parser expr_pars
   (fun expr -> MicroSolidity.Expr (check_type tag expr)) ;
  call_pars tag
 ]

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
  kleenestar (concat (kwd ",") pars_varlist_singleton csnd) 
  (AnyVarList(VNil)) varlist_append s t in
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
 let ns2,(block,payable),error2,nt2 = 
  block_pars t1 vl ns1 (add_fun_to_table nt1 (AnyMeth(t1,get_taglist vl,name))) in
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
"<="; "!="; "&&"; "||"; "!"; "true"; "false"; "int"; "bool"; 
"="; ","; ";"; "fail"; "if"; "else"; "revert"; "{"; "function";
"}"; "return"; "returns"; "this"; "."; "value"; "balance"; "msg"; "sender" ; "contract" ; "payable" ]

let test_stream stream =
 try
  let _s, conf, _error, _tbl = configuration_pars (get_tokens lexer stream) [] in
(*
  "######## TOKENS #######\n" ^
  print_token_list s ^
  "######## TABLE #######\n" ^
  print_table tbl ^
  "######## PROGRAM #######" ^
*)
  pp_configuration conf
 with
  | Fail (msg,l) ->
     "######## SYNTAX ERROR #######\n" ^
     "<< " ^ msg ^ " >>\n" ^
     print_token_list l
  | exn ->
     "######## UNHANLDED EXCEPTION #######\n" ^
     Printexc.to_string exn

let test_file filename =
 let in_channel = open_in filename in
 let stream = Stream.of_channel in_channel in
 test_stream stream

let test_string s =
 let stream = Stream.of_string s in
 test_stream stream

(* to avoid warnings for unused functions *)
let _ = print_table
