open Js_of_ocaml

let document = Dom_html.window##.document

let _ =
 Utils.set_error (fun msg ->
  let errors = Js.Opt.get (document##getElementById (Js.string "errors")) (fun () -> assert false) in
  Dom.appendChild errors (document##createTextNode (Js.string msg));
  Dom.appendChild errors (document##createElement (Js.string "br"));
 )

let eval () =
 (*let _ = Js.Unsafe.fun_call (Js.Unsafe.variable "alert") [|s|] in*)
 let doc_in = Js.Unsafe.variable "window.doc_in" in
 let x = Js.Unsafe.meth_call doc_in "getValue" [| |] in
 (*let x = (Js.coerce_opt (document##getElementById (Js.string "in")) Dom_html.CoerceTo.textarea (fun _ -> assert false))##.value in*)
 let input = Js.to_string x in
 let output = Grammar.test_string input in
 let y = Js.string output in
 (*let main = Js.Opt.get (document##getElementById (Js.string "out")) (fun () -> assert false) in
 main##.innerHTML := y*)
 let doc_out = Js.Unsafe.variable "window.doc_out" in
 let _ = Js.Unsafe.meth_call doc_out "setValue" [| Js.Unsafe.inject y |] in
 ()

let _ = Js.export "eval" (Js.wrap_callback eval)

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
