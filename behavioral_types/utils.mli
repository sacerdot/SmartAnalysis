val set_error : (string -> unit) -> unit
val error : string -> unit

val fst3 : 'a * 'b * 'c -> 'a
val snd3 : 'a * 'b * 'c -> 'b
val trd3 : 'a * 'b * 'c -> 'c

val prefix : int -> 'a list -> 'a list
val iteri : (int -> 'a -> unit) -> 'a list -> unit

val mk_list : 'a -> int -> 'a list
