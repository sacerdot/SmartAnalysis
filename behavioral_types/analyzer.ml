open Js_of_ocaml

let document = Dom_html.window##.document

let _ =
 Utils.set_error (fun msg ->
  let errors = Js.Opt.get (document##getElementById (Js.string "errors")) (fun () -> assert false) in
  Dom.appendChild errors (document##createTextNode (Js.string msg));
  Dom.appendChild errors (document##createElement (Js.string "br"));
 )

let transform f () =
 (*let _ = Js.Unsafe.fun_call (Js.Unsafe.variable "alert") [|s|] in*)
 let doc_in = Js.Unsafe.variable "window.doc_in" in
 let x = Js.Unsafe.meth_call doc_in "getValue" [| |] in
 (*let x = (Js.coerce_opt (document##getElementById (Js.string "in")) Dom_html.CoerceTo.textarea (fun _ -> assert false))##.value in*)
 let input = Js.to_string x in
 let output = f input in
 let y = Js.string output in
 (*let main = Js.Opt.get (document##getElementById (Js.string "out")) (fun () -> assert false) in
 main##.innerHTML := y*)
 let doc_out = Js.Unsafe.variable "window.doc_out" in
 let _ = Js.Unsafe.meth_call doc_out "setValue" [| Js.Unsafe.inject y |] in
 ()

let parse = transform (Parser.test_string MicroSolidity.pp_configuration)
let normalize =
 transform (Parser.test_string
  (fun c -> MicroSolidity.pp_configuration (Static.normalize c)))
let get_bounds =
 transform (Parser.test_string
  (fun c -> Static.pp_bounds (Static.get_bounds (Static.normalize c))))

let copy_output_to_input () =
 let doc_in = Js.Unsafe.variable "window.doc_out" in
 let x = Js.Unsafe.meth_call doc_in "getValue" [| |] in
 let doc_out = Js.Unsafe.variable "window.doc_in" in
 let _ = Js.Unsafe.meth_call doc_out "setValue" [| Js.Unsafe.inject x |] in
 ()

let _ = Js.export "ms_parse" (Js.wrap_callback parse)
let _ = Js.export "ms_normalize" (Js.wrap_callback normalize)
let _ = Js.export "ms_get_bounds" (Js.wrap_callback get_bounds)
let _ = Js.export "ms_copy_output_to_input" (Js.wrap_callback copy_output_to_input)

(*
let onload _ =
 let res = document##createDocumentFragment in
(*
 let s = ref "" in
 Strong_cbv.parse "x (y. (z.z) (z.z))" (fun t -> s := Strong_cbv.string_of_t t);
 Dom.appendChild res (document##createTextNode (Js.string !s));
 let main = Js.Opt.get (document##getElementById (Js.string "main")) (fun () -> assert false) in
 Dom.appendChild main res;
*) ignore res;
 Js._false

let _ = Dom_html.window##.onload := Dom_html.handler onload
*)
