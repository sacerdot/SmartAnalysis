(*Types*)
type 'a t = 'a list
type any_expr = AnyExpr : 'a MicroSolidity.tag * 'a MicroSolidity.expr -> any_expr
type any_tag = AnyTag : 'a MicroSolidity.tag -> any_tag
type any_meth = AnyMeth : ('a,'b) MicroSolidity.meth -> any_meth
type any_var_list = AnyVarList : 'a MicroSolidity.var_list -> any_var_list
type any_field_or_fun = 
    | Field: _ MicroSolidity.field * bool -> any_field_or_fun
    | Fun:  _ MicroSolidity.meth -> any_field_or_fun
type vartable = any_field_or_fun list
type any_rhs = AnyRhs: 'a MicroSolidity.tag * 'a MicroSolidity.rhs -> any_rhs
type 'ast parser = Genlex.token t -> vartable -> Genlex.token t * 'ast * vartable
exception Fail of [`Syntax of Genlex.token t | `Typing of string ]

(*Utils*)

let fst = (fun x _ -> x)
let scd = (fun _ x -> x)

let addel = (fun l el -> l@[el]) 
let identity = (fun x -> x)

(*print*)
let print_token_list l =
 String.concat ""
  (List.map
   (fun t ->
     (match t with
       | (Genlex.Kwd x) -> "Kwd " ^ x
       | (Ident x) -> "Ident " ^ x
       | (Int n) -> "int " ^ string_of_int n
       | (Char c) -> "char " ^ String.make 1 c
       | (String s) -> "string " ^ s
       | (Float f) -> "float " ^ string_of_float f
     ) ^ "\n") l)

let print_table l =
 String.concat ""
  (List.map
    (function
      | Field (f,_) -> MicroSolidity.pp_field f
      | Fun (meth) -> MicroSolidity.pp_meth meth) l)

(*Cast*)
let check_type : type a. a MicroSolidity.tag -> any_expr -> a MicroSolidity.expr =
 fun tag (AnyExpr(t, e)) ->
   match MicroSolidity.eq_tag tag t with 
   | Some Refl -> e
   | _ -> raise (Fail (`Typing (MicroSolidity.pp_expr t e ^ " should have type " ^ MicroSolidity.pp_tag tag)))

let value : type a. a MicroSolidity.tag -> Genlex.token -> a MicroSolidity.expr = fun tag tok ->
 match tag,tok with
 | Int,Int x -> Value x
 | Bool,Kwd "true" -> Value true
 | Bool,Kwd "false" -> Value false
 | _ -> raise (Fail (`Syntax [tok]))
   
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
   
(*parser*)
let const : Genlex.token -> (Genlex.token -> 'ast) -> 'ast parser =
 fun t1 f t2 tbl ->
  if (List.length t2 > 0) && (t1 = (List.hd t2)) then
   (junk t2), f t1, tbl
  else
   raise (Fail (`Syntax t2))

let choice : 'ast parser -> 'ast parser -> 'ast parser
= fun p1 p2 s tbl -> 
 try p1 s tbl with Fail _ -> p2 s tbl

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
  with Fail _ -> (s1, acc, tbl)
  in aux p s empty_ast t

let kleenestar_eof : 'ast2 parser -> 'ast1 -> ('ast1 -> 'ast2 -> 'ast1) -> 'ast1 parser = 
 fun p empty_ast f s t ->
  let rec aux p1 s1 acc tbl=
   if s1 = [] then s1,acc,tbl
   else
    let (rest1, ast1, ntbl) = p1 s1 tbl in
    aux p1 rest1 (f acc ast1) ntbl
  in aux p s empty_ast t

let option : 'ast parser -> 'ast option parser =
 fun p s tbl -> try 
  let next,res,ntbl = p s tbl in next,Some res,ntbl
 with Fail _ -> s,None,tbl

let rec choice_list: 'ast parser list -> 'ast parser
= fun l ->
 match l with
  | [] -> assert false
  | hd :: [] -> hd
  | hd :: tl -> choice hd (choice_list tl)

let kwd str = const (Kwd str) ignore

let eof : unit parser =
 fun l t ->
  match l with
   | [] -> l,(),t
   | _ -> raise (Fail (`Syntax l))
