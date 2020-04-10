let set_error,error =
 let f = ref prerr_endline in
 (fun g -> f := g),(fun s -> !f s)

let fst3 (a,_,_) = a
let snd3 (_,a,_) = a
let trd3 (_,_,a) = a

let rec prefix n =
 function
    _ when n = 0 -> []
  | [] -> assert false
  | hd::tl -> hd::prefix (n-1) tl

let rec set_prefix ~prefix l =
 match prefix,l with
    [],_ -> l
  | _::_,[] -> assert false
  | v::ptl,(k,_)::tl -> (k,v)::set_prefix ~prefix:ptl tl

let rec mk_list c =
 function
    0 -> []
  | n -> c::mk_list c (n-1)
