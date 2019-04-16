let fst3 (a,_,_) = a
let snd3 (_,a,_) = a
let third3 (_,_,a) = a

let map_option f = function None -> None | Some x -> Some (f x)

let pp_unit () = ""
let pp_bool = string_of_bool
