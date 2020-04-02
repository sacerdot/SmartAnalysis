let set_error,error =
 let f = ref prerr_endline in
 (fun g -> f := g),(fun s -> !f s)

let fst3 (a,_,_) = a
let snd3 (_,a,_) = a
let trd3 (_,_,a) = a
