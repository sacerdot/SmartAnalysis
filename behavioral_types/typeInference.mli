type inferred =
 { types: Types.types ;
   fieldsno : int ;
   balances : string list
 }

val type_of :
 max_args:int -> max_stack:int -> MicroSolidity.configuration ->
  inferred
