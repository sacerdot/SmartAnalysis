open String
open Char
open Genlex
open SmartCalculus

(*Types*)
type 'a t = 'a list
type any_expr = AnyExpr : 'a tag * 'a expr -> any_expr
type any_tag = AnyTag : 'a tag -> any_tag
type any_field = AnyField: 'a SmartCalculus.field -> any_field
type any_meth = AnyMeth : ('a,'b) SmartCalculus.meth -> any_meth
type any_tag_list = AnyTagList : 'a SmartCalculus.tag_list -> any_tag_list
type any_expr_list = AnyExprList : 'a SmartCalculus.expr_list -> any_expr_list
type any_field_or_fun = 
    | Field: 'a tag * string * bool -> any_field_or_fun
    | Fun:  ('a, 'b) SmartCalculus.meth -> any_field_or_fun
type vartable = any_field_or_fun list
type any_rhs = AnyRhs: 'a tag * 'a rhs -> any_rhs
type any_actor = 
    | ActHum: a_human -> any_actor
    | ActCon: a_contract -> any_actor
type 'ast parser = token t -> (vartable * bool) -> token t * 'ast * (vartable * bool)
exception Fail

(*Utils*)

let fst = (fun x _ -> x)
let scd = (fun _ x -> x)

let addel = (fun l el -> l@[el]) 
let identity = (fun x -> x)

(*print*)
let rec print_token_list l =
    match l with
    | (Kwd x)::l -> print_string "Kwd "; print_string x; print_endline ""; print_token_list l
    | (Ident x)::l -> print_string "Ident "; print_string x; print_endline ""; print_token_list l
    | (Int n)::l -> print_string "int "; print_int n; print_endline ""; print_token_list l
    | (Char c)::l -> print_string "char "; print_char c; print_endline ""; print_token_list l
    | (String s)::l -> print_string "string "; print_string s; print_endline ""; print_token_list l
    | _ -> ()

let rec print_table=
    function
    | [] -> print_endline "";
    | Field (t,f,_)::tl -> print_endline (pp_field (t,f)); print_table tl
    | Fun (meth)::tl -> print_endline(pp_meth meth); print_table tl


(*Cast*)
let check_type : type a. a tag -> any_expr -> a expr =
    fun tag expr ->
        match expr,tag with
        | AnyExpr(_,Fail),_ -> Fail
        | AnyExpr(_,Var(t,var)),t2 -> Var(t2,var)
        | AnyExpr(t, e),_ -> 
                match eq_tag tag t with 
                | Some Refl -> e
                | _ -> raise Fail 

let value : type a. a tag -> token -> a expr = fun tag tok ->
    match tag,tok with
    | String,Genlex.String x -> Value x
    | ContractAddress,Kwd "this" -> This
    | Int,Int x -> Value x
    | Bool,Kwd "true" -> Value true
    | Bool,Kwd "false" -> Value false
    | _ -> raise Fail
   
let rec remove_minspace =
    function
    | [] -> []
    | (Genlex.Int x)::tl -> 
            if (x < 0) then [(Kwd "-")]@[(Genlex.Int (-x))]@(remove_minspace tl) else
                [(Genlex.Int x)]@(remove_minspace tl)
    | hd::tl -> [hd]@(remove_minspace tl)

let getopt: 'a option -> 'a =
    function
    | Some x -> x
    | _ -> raise Fail

let comb_parser: 'a parser -> ('a -> 'b) -> 'b parser =
    fun pars f s tbl ->
        let (ns,nast,nt) = pars s tbl in ns,(f nast),nt

let junk =
 function
    [] -> []
  | _::tl -> tl

let of_token streamt =
    let rec aux acc s = 
        try
            aux ((Stream.next s) :: acc) s
        with
            Stream.Failure -> acc
    in List.rev (aux [] streamt)

(*table*)
let rec get_field : vartable -> string -> (any_field  * bool) option =
    fun tbl varname -> 
        match tbl with
        | [] -> None
        | Field (tag, name, islocal )::_ when varname=name ->  Some (AnyField(tag,
        name),islocal)
        | _::tl -> get_field tl varname

let add_field_to_table : vartable -> any_field -> bool -> vartable =
    fun tbl (AnyField(t,fieldname)) is_local -> 
        match get_field tbl fieldname with
        | None -> List.append ([Field(t,fieldname,is_local)]) tbl 
        | Some(AnyField(tag,name),_) -> 
                (match eq_tag tag t with
                | Some Refl -> tbl
                | None -> raise Fail)

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
        | _ -> raise Fail

 let remove_local_var: vartable -> vartable =
     fun tbl  -> List.filter (fun x -> 
         match x with
         | Field(_, _ , true) -> false
         | _ -> true
        ) tbl
   
(*parser*)
let const : token -> (token -> 'ast) -> 'ast parser =
 fun t1 f t2 tbl ->
  if (List.length t2 > 0) && (t1 = (List.hd t2)) then
   (junk t2), f t1, tbl
  else
   raise Fail

let choice : 'ast parser -> 'ast parser -> 'ast parser
= fun p1 p2 s tbl -> 
 try p1 s tbl with Fail -> p2 s tbl

let concat : 'ast1 parser -> 'ast2 parser -> ('ast1 -> 'ast2 -> 'ast3) -> 'ast3 parser
 = fun p1 p2 f s tbl ->
  let rest1,ast1,tbl1 = p1 s tbl in
  let rest2,ast2,tbl2 = p2 rest1 tbl1 in
  rest2,f ast1 ast2,tbl2

let kleenestar : 'ast2 parser -> 'ast1 -> ('ast1 -> 'ast2 -> 'ast1) -> 'ast1 parser = 
 fun p empty_ast f s t ->
  let rec aux p1 s1 acc tbl=
  try
   let (rest1, ast1, ntbl) = p1 s1 tbl in
   aux p1 rest1 (f acc ast1) ntbl
  with Fail -> (s1, acc, tbl)
  in aux p s empty_ast t

let option : 'ast parser -> 'ast option parser =
 fun p s tbl -> try 
  let next,res,ntbl = p s tbl in next,Some res,ntbl
 with Fail -> s,None,tbl

let rec choice_list: 'ast parser list -> 'ast parser
= fun l->
 match l with
  | [] -> raise Fail
  | hd :: [] -> hd
  | hd :: tl -> choice hd (choice_list tl)

let kwd str = const (Kwd str) ignore
