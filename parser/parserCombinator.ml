(*
stm ::= type varname | varname "=" rhs | "if " bexpr "then" stm "else" stm | 
        stm "+" stm | def_funct | type varname "()"| "{" stm "}" | "/*" stringc "*/"
        *)

open String
open Char
open Genlex
open SmartCalculus

(*Types*)
type 'a t = 'a list
type any_expr = AnyExpr : 'a tag * 'a expr -> any_expr
type any_tag = AnyTag : 'a tag -> any_tag
type any_field = AnyField: 'a SmartCalculus.field -> any_field
type any_field_or_fun = 
    | Field: any_field * string -> any_field_or_fun
    | Fun:  any_tag * (any_tag list) * string -> any_field_or_fun
type vartable = any_field_or_fun list
type any_rhs = AnyRhs: 'a tag * 'a rhs -> any_rhs
type any_actor = 
    | ActHum: a_human -> any_actor
    | ActCon: a_contract -> any_actor
exception Fail

type any_meth = AnyMeth : ('a,'b) SmartCalculus.meth -> any_meth

check_type : type a. a tag -> any_expr -> a expr

concat_list : type b. b tag_list -> (b expr_list -> 'c) -> 'c parser

let parse_method_call : string -> any_expr parser =
 fun m ->
  let rec aux
     [] -> assert false
   | (AnyMeth (tag,tags,name))::_ when name = m ->
       concat_list tags (fun el -> ... Call(...,el,))
   | _::tl -> aux tl
  in
   aux tbl

let rec npeek n stream =
 match n,stream with
    0,_ -> []
  | _,[] -> []
  | _,hd::tl -> hd::npeek (n-1) tl

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

let rec nnext : int -> 'a t -> 'a t =
    fun n stream ->
     if n = 0 then stream else nnext (n-1) (junk stream)

let print_list = String.concat " "

(*table*)
let get_vartag : vartable -> string -> any_tag option =
    fun tbl s -> 
        match (List.find_opt (fun x -> match x with Field ((AnyField (_,var)),_)
        -> var = s | _ -> false) tbl) with
        | Some Field((AnyField (tag,_)),_) -> Some(AnyTag tag)
        | _ -> None

 let add_field_to_table : vartable -> 'a tag -> string -> string -> vartable =
    fun tbl t fieldname funname -> 
        match get_vartag tbl fieldname with
        | None -> List.append tbl ([Field(AnyField(t,fieldname), funname)])
        | _ -> raise Fail

let get_funtag : vartable -> string -> (any_tag*(any_tag list)) option =
    fun tbl s -> 
        match (List.find_opt (fun x -> match x with Fun (_,_,name) -> name = s |
        _ -> false) tbl) with
        | Some Fun(itag, outtags,_) -> Some (itag,outtags)
        | _ -> None

 let add_fun_to_table : vartable -> 'a tag -> any_tag list -> string -> vartable =
    fun tbl t l funname -> 
        match get_funtag tbl funname with
        | None -> List.append tbl ([Fun(AnyTag t,l,funname)])
        | _ -> raise Fail

 let remove_local_var: vartable -> string -> vartable =
     fun tbl funname -> List.filter (fun x -> 
         match x with
         | Field(_, name) -> (name != funname)
         | _ -> true
        ) tbl
   
(*parser*)
type 'ast parser = token t -> vartable -> token t * 'ast * vartable

let val_token : (token -> 'ast) -> 'ast parser =
    fun f t2 tbl ->
        match t2 with
        | (Int x) :: l -> l, f (Int x), tbl
        | (String x) :: l -> l, f (String x), tbl
        | (Char x) :: l -> l, f (Char x), tbl
        | (Kwd "true") :: l -> l, f (Kwd "true") , tbl
        | (Kwd "false") :: l -> l, f (Kwd "false") , tbl
        | _ -> raise Fail

let const : token -> (token -> 'ast) -> 'ast parser =
    fun t1 f t2 tbl ->
        if (List.length t2 > 0) && (t1 = (List.hd t2)) then
            (nnext 1 t2), f t1, tbl
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
