(** Decorate each file with a little bit of boilerplate, then print it *)

open Utils
open PPrint

let boilerplate =
{|/* This file auto-generated by KreMLin */
#include <inttypes.h>
#include <string.h>
#include <stdio.h>
|}

let write_one (name, program) =
  let f = name ^ ".c" in
  with_open_out f (fun oc ->
    let doc =
      string boilerplate ^^ hardline ^^
      separate_map (hardline ^^ hardline) PrintC.p_decl_or_function program
    in
    PPrint.ToChannel.pretty 0.95 100 oc doc
  )

let write files =
  List.iter write_one files
