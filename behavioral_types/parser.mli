type any_meth = AnyMeth : ('a,'b) MicroSolidity.meth -> any_meth
type any_var_list = AnyVarList : 'a MicroSolidity.var_list -> any_var_list
type tagged_var_list = TaggedVarList : 'a MicroSolidity.tag_list * 'a MicroSolidity.var_list -> tagged_var_list

val varlist_append : any_var_list -> any_var_list -> any_var_list
val tagged_var_list_of_any_var_list : any_var_list -> tagged_var_list

val test_file : (MicroSolidity.configuration -> string) -> string -> string
val test_string : (MicroSolidity.configuration -> string) -> string -> string

type any_field_or_fun = 
    | Contract: MicroSolidity.address -> any_field_or_fun
    | VarOrField: _ MicroSolidity.ident * bool -> any_field_or_fun
    | Fun:  _ MicroSolidity.meth -> any_field_or_fun
type vartable = any_field_or_fun list

val lexer : char Stream.t -> Genlex.token Stream.t
val initialize_table_with_contracts : Genlex.token ParserCombinators.t -> any_field_or_fun list
val configuration_pars :  (MicroSolidity.configuration, vartable) ParserCombinators.parser