(** Types **)
type 'a t = 'a list
type error = string * Genlex.token t
type ('ast,'a) parser =
  Genlex.token t -> 'a -> Genlex.token t * 'ast * error * 'a
exception Fail of error
exception Reject of string

(** Utils **)

val best : error -> error -> error
val cfst : 'a -> 'b -> 'a
val csnd : 'a -> 'b -> 'b
val addel : 'a list -> 'a -> 'a list
val identity : 'a -> 'a

(** Streams **)

val string_of_token : Genlex.token -> string
val print_token_list : Genlex.token list -> string
val get_tokens : ('a -> Genlex.token Stream.t) -> 'a -> Genlex.token t

(** Parser combinators **)

val comb_parser : ('a,'t) parser -> ('a -> 'b) -> ('b,'t) parser

val eof : (unit,'t) parser
val const : Genlex.token -> (Genlex.token -> 'ast) -> ('ast,'t) parser
val kwd : string -> (unit,'t) parser

val option : ('ast,'t) parser -> ('ast option, 't) parser
val option2 : 'ast -> ('ast,'t) parser -> ('ast, 't) parser
val choice : ('ast,'t) parser -> ('ast,'t) parser -> ('ast,'t) parser
val choice_list : ('ast,'t) parser list -> ('ast,'t) parser
val concat :
  ('ast1,'t) parser -> ('ast2,'t) parser -> ('ast1 -> 'ast2 -> 'ast3) ->
   ('ast3,'t) parser
val kleenestar :
  ('ast2,'t) parser -> 'ast1 -> ('ast1 -> 'ast2 -> 'ast1) -> ('ast1,'t) parser
(* (nelist p sep) parses p (sep p)* (left-associative) *)
val nelist :
  ('a,'t) parser -> ('a -> 'a -> 'a,'t) parser -> ('a,'t) parser
