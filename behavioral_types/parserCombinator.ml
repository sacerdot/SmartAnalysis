(** Types **)
type 'a t = 'a list
type error = string * Genlex.token t
type ('ast,'a) parser =
  Genlex.token t -> 'a -> Genlex.token t * 'ast * error * 'a
exception Fail of error
exception Reject of string

(** Utils **)

let best err1 err2 =
 if fst err1 = "ok" then err2
 else if fst err2 = "ok" then err1
 else if List.length (snd err1) < List.length (snd err2) then err1
 else if List.length (snd err1) = List.length (snd err2) then
  (fst err1 ^ "\n| " ^ fst err2, snd err1)
 else err2
  
let cfst = (fun x _ -> x)
let csnd = (fun _ x -> x)

let addel = (fun l el -> l@[el]) 
let identity = (fun x -> x)

(** Streams **)

let rec remove_minspace =
 function
 | [] -> []
 | (Genlex.Int x)::tl when x < 0 -> 
     [(Genlex.Kwd "-")]@[(Genlex.Int (-x))]@(remove_minspace tl)
 | hd::tl -> [hd]@(remove_minspace tl)

let of_token streamt =
 let rec aux acc s = 
  try aux ((Stream.next s) :: acc) s
  with Stream.Failure -> acc
 in List.rev (aux [] streamt)

let get_tokens lexer file = remove_minspace (of_token(lexer file));;

let string_of_token =
 function
  | (Genlex.Kwd x) -> "Kwd " ^ x
  | (Ident x) -> "Ident " ^ x
  | (Int n) -> "int " ^ string_of_int n
  | (Char c) -> "char " ^ String.make 1 c
  | (String s) -> "string " ^ s
  | (Float f) -> "float " ^ string_of_float f

let print_token_list l =
 String.concat "" (List.map (fun t -> string_of_token t ^ "\n") l)

(** Parser combinators **)

let comb_parser pars f s tbl =
 let ns,nast,error,nt = pars s tbl in
 let x =
  try
   f nast
  with Reject msg -> raise (Fail (best error (msg, s)))
 in
  ns,x,error,nt

let eof s t =
  match s with
   | [] -> s,(),("ok",s),t
   | _ -> raise (Fail ("eof expected", s))

let const kwd f s tbl =
 match s with
  | t::tl when kwd = t ->
     let x =
      try
        f t
      with Reject msg -> raise (Fail (msg, s))
     in
      tl, x, ("ok",tl), tbl
  | _ -> raise (Fail (string_of_token kwd ^ " expected", s))

let kwd str = const (Kwd str) ignore

let option p s tbl =
 try 
  let next,res,error,ntbl = p s tbl in next,Some res,error,ntbl
 with Fail error -> s,None,error,tbl

let choice p1 p2 s tbl =
 try p1 s tbl with Fail error1 ->
 try p2 s tbl with Fail error2 ->
  raise (Fail (best error1 error2))

let rec choice_list =
 function
  | [] -> assert false
  | hd :: [] -> hd
  | hd :: tl -> choice hd (choice_list tl)

let concat p1 p2 f s tbl =
 let rest1,ast1,error1,tbl1 = p1 s tbl in
 try
  let rest2,ast2,error2,tbl2 = p2 rest1 tbl1 in
  let x =
   try
    f ast1 ast2
   with Reject msg -> raise (Fail (best (best error1 error2) (msg,s)))
  in
   rest2,x,best error1 error2,tbl2
 with Fail error2 -> raise (Fail (best error1 error2))

let kleenestar p empty_ast f s t =
 let rec aux s1 acc error tbl=
  try
   let rest1, ast1, error1, ntbl = p s1 tbl in
   let x =
    try
     f acc ast1
    with Reject msg -> raise (Fail (best error1 (msg,s1))) in
   aux rest1 x (best error1 error) ntbl
  with Fail error1 -> s1, acc, best error1 error, tbl in
 aux s empty_ast ("kleenestar",s) t
