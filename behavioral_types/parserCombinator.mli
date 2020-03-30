type 'a t = 'a list
type ('ast,'a) parser = Genlex.token t -> 'a -> Genlex.token t * 'ast * 'a
exception Fail of [`Syntax of Genlex.token t | `Typing of string ]
val fst : 'a -> 'b -> 'a
val scd : 'a -> 'b -> 'b
val addel : 'a list -> 'a -> 'a list
val identity : 'a -> 'a
val print_token_list : Genlex.token list -> string
val value : 'a MicroSolidity.tag -> Genlex.token -> 'a MicroSolidity.expr
val remove_minspace : Genlex.token list -> Genlex.token list
val comb_parser : ('a,'t) parser -> ('a -> 'b) -> ('b,'t) parser
val junk : 'a list -> 'a list
val of_token : 'a Stream.t -> 'a list
val const : Genlex.token -> (Genlex.token -> 'ast) -> ('ast,'t) parser
val choice : ('ast,'t) parser -> ('ast,'t) parser -> ('ast,'t) parser
val concat :
  ('ast1,'t) parser -> ('ast2,'t) parser -> ('ast1 -> 'ast2 -> 'ast3) -> ('ast3,'t) parser
val kleenestar :
  ('ast2,'t) parser -> 'ast1 -> ('ast1 -> 'ast2 -> 'ast1) -> ('ast1,'t) parser
val kleenestar_eof :
  ('ast2,'t) parser -> 'ast1 -> ('ast1 -> 'ast2 -> 'ast1) -> ('ast1,'t) parser
val option : ('ast,'t) parser -> ('ast option, 't) parser
val choice_list : ('ast,'t) parser list -> ('ast,'t) parser
val kwd : string -> (unit,'t) parser
val eof : (unit,'t) parser
