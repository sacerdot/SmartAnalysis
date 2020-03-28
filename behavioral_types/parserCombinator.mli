type 'a t = 'a list
type any_expr =
    AnyExpr : 'a MicroSolidity.tag * 'a MicroSolidity.expr -> any_expr
type any_tag = AnyTag : 'a MicroSolidity.tag -> any_tag
type any_meth = AnyMeth : ('a, 'b) MicroSolidity.meth -> any_meth
type any_var_list = AnyVarList : 'a MicroSolidity.var_list -> any_var_list
type any_field_or_fun =
    Field : 'a MicroSolidity.field * bool -> any_field_or_fun
  | Fun : ('b, 'c) MicroSolidity.meth -> any_field_or_fun
type vartable = any_field_or_fun list
type any_rhs = AnyRhs: 'a MicroSolidity.tag * 'a MicroSolidity.rhs -> any_rhs
type 'ast parser =
    Genlex.token t ->
    vartable -> Genlex.token t * 'ast * vartable
exception Fail of [`Syntax of Genlex.token t | `Typing of string ]
val fst : 'a -> 'b -> 'a
val scd : 'a -> 'b -> 'b
val addel : 'a list -> 'a -> 'a list
val identity : 'a -> 'a
val print_token_list : Genlex.token list -> string
val print_table : any_field_or_fun list -> string
val check_type : 'a MicroSolidity.tag -> any_expr -> 'a MicroSolidity.expr
val value : 'a MicroSolidity.tag -> Genlex.token -> 'a MicroSolidity.expr
val remove_minspace : Genlex.token list -> Genlex.token list
val comb_parser : 'a parser -> ('a -> 'b) -> 'b parser
val junk : 'a list -> 'a list
val of_token : 'a Stream.t -> 'a list
val get_field : vartable -> string -> (MicroSolidity.any_field * bool) option
val add_field_to_table :
  vartable -> MicroSolidity.any_field -> bool -> vartable
val get_fun : vartable -> string -> any_meth option
val add_fun_to_table : vartable -> any_meth -> vartable
val remove_local_vars : vartable -> vartable
val const : Genlex.token -> (Genlex.token -> 'ast) -> 'ast parser
val choice : 'ast parser -> 'ast parser -> 'ast parser
val concat :
  'ast1 parser -> 'ast2 parser -> ('ast1 -> 'ast2 -> 'ast3) -> 'ast3 parser
val kleenestar :
  'ast2 parser -> 'ast1 -> ('ast1 -> 'ast2 -> 'ast1) -> 'ast1 parser
val kleenestar_eof :
  'ast2 parser -> 'ast1 -> ('ast1 -> 'ast2 -> 'ast1) -> 'ast1 parser
val option : 'ast parser -> 'ast option parser
val choice_list : 'ast parser list -> 'ast parser
val kwd : string -> unit parser
val eof : unit parser
