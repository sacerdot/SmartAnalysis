let fst3 (a,_,_) = a
let snd3 (_,a,_) = a
let third3 (_,_,a) = a

let map_option f = function None -> None | Some x -> Some (f x)

let rec map_skip f =
 function
    [] -> []
  | x::xs ->
     match f x with
        None -> map_skip f xs
      | Some y -> y :: map_skip f xs

let classify f =
 let rec aux ~p ~np =
  function
     [] -> p,np
   | hd::tl ->
      let p,np =
       match f hd with
          `True x  -> x::p,np
        | `False x -> p,x::np in
      aux ~p ~np tl
 in
  aux ~p:[] ~np:[]

let pp_unit () = ""
let pp_bool = string_of_bool
