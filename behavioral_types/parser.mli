type any_var_list = AnyVarList : 'a MicroSolidity.var_list -> any_var_list
type tagged_var_list = TaggedVarList : 'a MicroSolidity.tag_list * 'a MicroSolidity.var_list -> tagged_var_list

val varlist_append : any_var_list -> any_var_list -> any_var_list
val tagged_var_list_of_any_var_list : any_var_list -> tagged_var_list

val test_file : (MicroSolidity.configuration -> string) -> string -> string
val test_string : (MicroSolidity.configuration -> string) -> string -> string
