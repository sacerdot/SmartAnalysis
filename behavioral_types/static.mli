(** normalization **)
val normalize: MicroSolidity.configuration -> MicroSolidity.configuration

(** computation of max stack bounds **)
type stack_bounds
val with_bounds:
 (stack_bounds -> string) -> MicroSolidity.configuration -> string
val pp_bounds: stack_bounds -> string

(** computation of max args and max stack depth **)
val with_maxargs_and_stack_bound:
 (bounds:stack_bounds -> max_args:int -> max_stack:int -> string) ->
   MicroSolidity.configuration -> string
