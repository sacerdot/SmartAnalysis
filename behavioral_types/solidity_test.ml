open Solidity
open MicroSolidity
open Compiler
open Parser
open PythonDeploy
open PyTest

let files = (List.filter (fun x -> (match((String.equal x "transf-example") || (String.equal x "out")) with | true -> false | false -> true)) (Array.to_list (Sys.readdir "demo")));;

type res = Problem | Ok

let make_dir: string -> res = fun dir -> 
  try 
   let _ = Unix.mkdir dir 0o755 in
   Ok
  with 
  | exn -> Problem

let tangle = 
 fun name outstr py py_test ->
   let l = (String.length name)-4 in
   let c_name = String.sub name 0 l in
   let base_dir = "demo/out/"^c_name^"/" in
   let _ = make_dir base_dir in
   let oc = open_out ("demo/out/"^c_name^"/"^name) in
   let oc2 = open_out ("demo/out/"^c_name^"/"^c_name^".py") in
   let oc3 = open_out("demo/out/"^c_name^"/"^c_name^"_test.py") in
   Printf.fprintf oc "%s" outstr;
   Printf.fprintf oc2 "%s" py;
   Printf.fprintf oc3 "%s" py_test;
   close_out oc;
   close_out oc2;
   close_out oc3;
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
    
     let il,cl   = Compiler.trans_configuration [] ([],[]) conf in
     
     let py = PythonDeploy.get_python cl name in
     let py_test = PyTest.get_python cl in

     let outstr  = Solidity.pp_configuration "0.6.0" "0.8.0" (il,cl) in
     tangle name outstr py py_test;
     "[Processed "^name^"] -- "^(process t);
    ) with | exn -> ("Fail with= "^name^" -- "^Printexc.to_string exn)
;;
process files