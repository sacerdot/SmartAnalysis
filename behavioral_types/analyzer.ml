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

let parse =
 transform (Parser.test_string MicroSolidity.pp_configuration)

let normalize =
 transform (Parser.test_string
  (fun c -> MicroSolidity.pp_configuration (Static.normalize c)))

let get_bounds =
 transform (Parser.test_string
  (fun c ->
    let c = Static.normalize c in
    Static.with_maxargs_and_stack_bound
     (fun ~bounds ~max_args:m ~max_stack:n ->
       Static.pp_bounds bounds ^
       "\n\n" ^
       "Maximum number of locals: " ^ string_of_int m ^ "\n" ^
       "Maximum stack length: " ^ string_of_int n) c))

let type_of =
 transform (Parser.test_string
  (fun c ->
    let c = Static.normalize c in
    Static.with_maxargs_and_stack_bound
     (fun ~bounds:_ ~max_args ~max_stack ->
       Types.pp_types (TypeInference.type_of ~max_args ~max_stack c).types) c))

let cost b =
 transform (Parser.test_string
  (fun c ->
    let c = Static.normalize c in
    Static.with_maxargs_and_stack_bound
     (fun ~bounds:_ ~max_args ~max_stack ->
       Cofloco.pp_prog
        (CostEquationsGeneration.compute ~gain:(Js.to_bool b)
         (TypeInference.type_of ~max_args ~max_stack c))) c)) ()

let copy_output_to_input () =
 let doc_in = Js.Unsafe.variable "window.doc_out" in
 let x = Js.Unsafe.meth_call doc_in "getValue" [| |] in
 let doc_out = Js.Unsafe.variable "window.doc_in" in
 let _ = Js.Unsafe.meth_call doc_out "setValue" [| Js.Unsafe.inject x |] in
 ()

let _ = Js.export "ms_parse" (Js.wrap_callback parse)
let _ = Js.export "ms_normalize" (Js.wrap_callback normalize)
let _ = Js.export "ms_get_bounds" (Js.wrap_callback get_bounds)
let _ = Js.export "ms_type_of" (Js.wrap_callback type_of)
let _ = Js.export "ms_cost" (Js.wrap_callback cost)
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
