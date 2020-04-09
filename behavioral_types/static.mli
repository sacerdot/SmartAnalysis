val normalize: MicroSolidity.configuration -> MicroSolidity.configuration

type bounds
val get_bounds: MicroSolidity.configuration -> bounds
val pp_bounds: bounds -> string

type cycle
val pp_cycle : cycle -> string
val maxargs_and_stack_bound:
 MicroSolidity.configuration -> [> `Bounds of int * int | `Unbounded of cycle ]
