(*Types*)
type 'a t = 'a list
type any_expr = AnyExpr : 'a MicroSolidity.tag * 'a MicroSolidity.expr -> any_expr
(*
type any_tag = AnyTag : 'a tag -> any_tag
*)
type any_meth = AnyMeth : ('a,'b) MicroSolidity.meth -> any_meth
(*
type any_tag_list = AnyTagList : 'a SmartCalculus.tag_list -> any_tag_list
type any_var_list = AnyVarList : 'a SmartCalculus.var_list -> any_var_list
*)
type any_field_or_fun = 
    | Field: _ MicroSolidity.field * bool -> any_field_or_fun
    | Fun:  _ MicroSolidity.meth -> any_field_or_fun
type vartable = any_field_or_fun list
(*
type any_rhs = AnyRhs: 'a tag * 'a rhs -> any_rhs
type any_actor = 
    | ActHum: a_human -> any_actor
    | ActCon: a_contract -> any_actor
*)
type 'ast parser = Genlex.token t -> vartable * bool -> Genlex.token t * 'ast * (vartable * bool)
exception Fail

(*Utils*)

let fst = (fun x _ -> x)
let scd = (fun _ x -> x)

let addel = (fun l el -> l@[el]) 
let identity = (fun x -> x)

(*print*)
let print_token_list =
 List.iter
  (fun t ->
    (match t with
      | (Genlex.Kwd x) -> print_string "Kwd "; print_string x
      | (Ident x) -> print_string "Ident "; print_string x
      | (Int n) -> print_string "int "; print_int n
      | (Char c) -> print_string "char "; print_char c
      | (String s) -> print_string "string "; print_string s
      | (Float f) -> print_string "float "; print_float f
    ); print_endline "")

let print_table =
 List.iter
  (function
    | Field (f,_) -> print_endline (MicroSolidity.pp_field f)
    | Fun (meth) -> print_endline(MicroSolidity.pp_meth meth))


(*Cast*)
let check_type : type a. a MicroSolidity.tag -> any_expr -> a MicroSolidity.expr =
 fun tag (AnyExpr(t, e)) ->
   match MicroSolidity.eq_tag tag t with 
   | Some Refl -> e
   | _ -> raise Fail 

let value : type a. a MicroSolidity.tag -> Genlex.token -> a MicroSolidity.expr = fun tag tok ->
 match tag,tok with
 | Address,Kwd "this" -> This
 | Int,Int x -> Value x
 | Bool,Kwd "true" -> Value true
 | Bool,Kwd "false" -> Value false
 | _ -> raise Fail
   
let rec remove_minspace =
 function
 | [] -> []
 | (Genlex.Int x)::tl when x < 0 -> 
     [(Genlex.Kwd "-")]@[(Genlex.Int (-x))]@(remove_minspace tl)
 | hd::tl -> [hd]@(remove_minspace tl)

let comb_parser: 'a parser -> ('a -> 'b) -> 'b parser =
 fun pars f s tbl -> let ns,nast,nt = pars s tbl in ns,(f nast),nt

let junk =
 function
  [] -> []
 | _::tl -> tl

let of_token streamt =
 let rec aux acc s = 
  try aux ((Stream.next s) :: acc) s
  with Stream.Failure -> acc
 in List.rev (aux [] streamt)

(*table*)
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
  | Some(AnyField(tag,name),_) -> 
   (match MicroSolidity.eq_tag tag t with
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

let remove_local_vars: vartable -> vartable =
 fun tbl  -> List.filter (function
  | Field(_, true) -> false
  | _ -> true) tbl
   
(*parser*)
let const : Genlex.token -> (Genlex.token -> 'ast) -> 'ast parser =
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
