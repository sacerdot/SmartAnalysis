let set_error,error =
 let f = ref prerr_endline in
 (fun g -> f := g),(fun s -> !f s)
