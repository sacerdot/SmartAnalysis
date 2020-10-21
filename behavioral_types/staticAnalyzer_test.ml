open StaticAnalyzer
open Parser

let files = (List.filter (fun x -> (match((String.equal x "transf-example") || (String.equal x "out") || (String.equal x "papero6X.sol")) with | true -> false | false -> true)) (Array.to_list (Sys.readdir "demo")));;

type res = Problem | Ok

let make_dir: string -> res = fun dir -> 
  try 
   let _ = Unix.mkdir dir 0o755 in
   Ok
  with 
  | exn -> Problem

let tangle = 
 fun name outstr ->
   let l = (String.length name)-4 in
   let c_name = String.sub name 0 l in
   let base_dir = "demo/out/"^c_name^"/" in
   let _ = make_dir base_dir in
   let cofloco_o = open_out ("demo/out/"^c_name^"/"^c_name^".cfg") in
   Printf.fprintf cofloco_o "%s" outstr;
   close_out cofloco_o;
;;

let rec process = 
 fun x -> 
  match x with
  | [] -> "All done."
  | name::t ->
    try(
     let in_channel  = open_in ("demo/"^name) in
     let stream      = Stream.of_channel in_channel in
    
     let tokens      = ParserCombinators.get_tokens Parser.lexer stream in
     let tbl         = Parser.initialize_table_with_contracts tokens in
     let _s, conf, _error, _tbl = Parser.configuration_pars tokens tbl in
    
     let res = StaticAnalyzer.trans conf in
     let str = Cofloco.pp_prog res in

     tangle name str;
     "[Processed "^name^"] -- "^(process t);
    ) with | exn -> ("Fail with= "^name^" -- "^Printexc.to_string exn)
;;
process files