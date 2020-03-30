(*Types*)
type 'a t = 'a list
type ('ast,'a) parser = Genlex.token t -> 'a -> Genlex.token t * 'ast * 'a
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

(*Cast*)

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

let comb_parser pars f s tbl =
 let ns,nast,nt = pars s tbl in ns,(f nast),nt

let junk =
 function
  [] -> []
 | _::tl -> tl

let of_token streamt =
 let rec aux acc s = 
  try aux ((Stream.next s) :: acc) s
  with Stream.Failure -> acc
 in List.rev (aux [] streamt)

(*parser*)
let const =
 fun t1 f t2 tbl ->
  if (List.length t2 > 0) && (t1 = (List.hd t2)) then
   (junk t2), f t1, tbl
  else
   raise (Fail (`Syntax t2))

let choice p1 p2 s tbl =
 try p1 s tbl with Fail _ -> p2 s tbl

let concat p1 p2 f s tbl =
 let rest1,ast1,tbl1 = p1 s tbl in
 let rest2,ast2,tbl2 = p2 rest1 tbl1 in
 rest2,f ast1 ast2,tbl2

let kleenestar p empty_ast f s t =
 let rec aux p1 s1 acc tbl=
  try
   let (rest1, ast1, ntbl) = p1 s1 tbl in
   aux p1 rest1 (f acc ast1) ntbl
  with Fail _ -> (s1, acc, tbl) in
 aux p s empty_ast t

let kleenestar_eof p empty_ast f s t =
 let rec aux p1 s1 acc tbl=
  if s1 = [] then s1,acc,tbl
  else
   let (rest1, ast1, ntbl) = p1 s1 tbl in
   aux p1 rest1 (f acc ast1) ntbl
 in aux p s empty_ast t

let option p s tbl =
 try 
  let next,res,ntbl = p s tbl in next,Some res,ntbl
 with Fail _ -> s,None,tbl

let rec choice_list =
 function
  | [] -> assert false
  | hd :: [] -> hd
  | hd :: tl -> choice hd (choice_list tl)

let kwd str = const (Kwd str) ignore

let eof l t =
  match l with
   | [] -> l,(),t
   | _ -> raise (Fail (`Syntax l))
