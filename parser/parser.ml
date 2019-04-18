(*
stm ::= type varname | varname "=" rhs | "if " bexpr "then" stm "else" stm | 
        stm "+" stm | def_funct | type varname "()"| "{" stm "}" | "/*" stringc "*/"
        *)

open String

open Stream

exception Fail

(*Stream of char*)
let rec nnext : int -> char t -> char t =
    fun n stream ->
        match n with
        | 0 -> stream
        | x -> try junk stream; nnext (n - 1) stream with Stream.Failure -> stream

(*
let stream_tee stream =
    let next self other i =
      try
        if Queue.is_empty self then
          let value = Stream.next stream in
          Queue.add value other;
          Some value
        else
          Some (Queue.take self)
      with Stream.Failure -> None in
    let q1 = Queue.create () in
    let q2 = Queue.create () in
    (from (next q1 q2), from (next q2 q1))
;;
*)

let length_stream_char: char t -> int =
    fun stream ->
        let rec aux n =
            if npeek n stream = npeek (n+1) stream then n
            else aux (n+1)
        in (aux 0)

let isin: char t -> char t -> int * bool =
    fun s1 s2 -> 
        let length = length_stream_char s1 in 
        if (npeek length s1) =  (npeek length s2) then length, true
        else 0, false

let rec print_list = function 
    [] -> ()
    | e::l -> print_char e; print_list l

let print_stream_char = fun stream ->
    print_list (npeek (length_stream_char stream) stream)

(*ast*)
type ast = Leaf of char t | Node of char t * ast * ast

let singleton: char t-> ast =
    fun s -> Leaf s

let empty_leaf: ast = Leaf (of_string "")

let is_empty_leaf: ast -> bool = function
    | Leaf l -> if (peek l = None) then true else false
    | Node (_, _, _) -> false

let rec print_ast: ast -> unit = 
    fun a -> 
        match a with
        | Leaf l -> if (peek l <> None) then
            print_endline("Leaf"); print_stream_char l; print_endline("");
        | Node (s, left, right) ->  print_endline("Node"); print_stream_char s;
        print_endline(""); print_ast left; print_ast right;

let rec ast_runion: ast -> ast -> ast =
    fun a1 a2 ->
        match a1 with
        | Leaf l -> if (peek l = None) then a2 else Node(l, empty_leaf, a2)
        | Node (s, left, right) -> Node(s, left, (ast_runion right a2))

(*parser*)

type parser = char t -> char t * ast

let const : char t -> (char t -> ast) -> parser =
    fun s1 f s2 -> 
        let (offset, cond) = isin s1 s2 in
        if cond then
            (nnext offset s2), f s1
        else
            raise Fail

let choice : parser -> parser -> parser
= fun p1 p2 s -> 
        try p1 s with Fail -> p2 s

let concat : parser -> parser -> (ast -> ast -> ast) -> parser
    = fun p1 p2 f s ->
        let rest1,ast1 = p1 s in
        let rest2,ast2 = p2 rest1 in
        rest2,f ast1 ast2

let kleenestar : parser -> (ast -> ast -> ast) -> parser = 
    fun p f s ->
        let rec aux p1 s1 acc =
        try
            let (rest1, ast1) = p1 s1 in
            aux p1 rest1 (f acc ast1)
        with Fail -> (s1, acc)
        in aux p s empty_leaf

(* Grammar example
 * f::= "x"f | g* 
 * g::= "a" | "b" 
 * *)
let rec g : parser =
    fun s -> choice (const (of_string "a") singleton) (const (of_string "b")
    singleton) s

let rec f : parser =  
    fun s -> choice (concat(const (of_string "x") singleton) f (ast_runion))
    (kleenestar g ast_runion) s

(*testing*)
let in_channel = open_in "input"
let file = Stream.of_channel(in_channel)
let (s, l) = f file;;
print_stream_char s;;
print_ast l;;

(*
type ::= "int" | "string" | "bool" | "Contract" | "Human"

value ::= intc | stringc | boolc 

rhs ::= call_funct | iexpr | bexpr

iexpr ::= intc | iexpr "+" iexpr |  "*" iexpr | "-" iexpr | "max" iexpr iexpr | 
          iexpr ">=" iexpr | iexpr ">" iexpr | iexpr "==" iexpr | "(" iexpr ")"
          | varname
*
          bexpr ::= boolc | bexpr "&&" bexpr | bexpr "||" bexpr | "!" bexpr |
          "(" bexpr ")" | varname

          def_funct ::= type varname "(" def_par ")" stm "return" rhs | 
type varname "()" stm "return" rhs  

def_par ::= def_par "," def_par | def_par | 
type varname
par ::= par "," par | par | varname

callfunct ::= varname "()" | varname "(" par ")"

varname ::= 

    boolc = 0 | 1

    intc = [0-9]*

    stringc = 
        *)

