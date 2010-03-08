open Mytools

let rec split_at_dots s pos =
  try
    let dot = String.index_from s pos '.' in
    String.sub s pos (dot - pos) :: split_at_dots s (dot + 1)
  with Not_found ->
    [String.sub s pos (String.length s - pos)]

let name_of_mlpath s =
   List.hd (List.rev (split_at_dots s 0))


(*#########################################################################*)
(* Detection of primitive and exception-raising functions *)

let primitive_special = -1

let inlined_primitives_table = 
  ["Pervasives.+", (2, "Coq.ZArith.BinInt.Zplus");
   "Pervasives.-", (2, "Coq.ZArith.BinInt.Zminus");
   "Pervasives.*", (2, "Coq.ZArith.BinInt.Zmult");
   "Pervasives.~-", (1, "Coq.ZArith.BinInt.Zopp"); 
   "Pervasives.&&", (2, "LibBool.and");
   "Pervasives.||", (2, "LibBool.or");
   "Pervasives./", (primitive_special, "Coq.ZArith.Zdiv.Zdiv");
   "Pervasives.mod", (primitive_special, "Coq.ZArith.Zdiv.Zmod");
   "Pervasives.=", (2, "(fun _y _z => istrue (_y = _z))");
   "Pervasives.<>", (2, "(fun _y _z => istrue (_y <> _z))");
   "Pervasives.<", (2, "(fun _y _z => istrue (_y < _z))");
   "Pervasives.<=", (2, "(fun _y _z => istrue (_y <= _z))");
   "Pervasives.>", (2, "(fun _y _z => istrue (_y > _z))");
   "Pervasives.>=", (2, "(fun _y _z => istrue (_y >= _z))");
   "Pervasives.@", (2, "LibList.append");
   "List.rev", (1, "LibList.rev"); 
   "List.append", (2, "LibList.append"); 
   "Stream.++", (2, "LibList.append"); 
   "Stream.reverse", (1, "LibList.rev");
   "Lazy.force", (1, ""); (* @LibLogic.id _*)
   "Okasaki.!$", (1, "") ]
   (* todo: add asr, etc.. *)

let all_primitives_table = (*todo:complete*)
  [ "Pervasives.=", "ml_eqb";
    "Pervasives.<>", "ml_neq";
    "Pervasives.+", "ml_plus";
    "Pervasives.-", "ml_minus";
    "Pervasives.~-", "ml_opp";
    "Pervasives.*", "ml_mul";
    "Pervasives./", "ml_div";
    "Pervasives.mod", "ml_mod";
    "Pervasives.<=", "ml_leq";
    "Pervasives.<", "ml_lt";
    "Pervasives.>", "ml_gt";
    "Pervasives.>=", "ml_geq";
    "Pervasives.&&", "ml_and";
    "Pervasives.||", "ml_or";
    "Pervasives.@", "ml_append";
    "Pervasives.raise", "ml_raise";
    "Pervasives.asr", "ml_asr";
    "List.hd", "ml_list_hd";
    "List.tl", "ml_list_tl";
    "List.rev", "ml_rev";
    "List.append", "ml_append";
    "Stream.append", "ml_append";
    "Stream.take", "mk_take";  
    "Stream.drop", "ml_drop";  ]

let builtin_constructors_table = (* todo: indiquer pervasives *)
  [ "[]", "nil";
    "::", "cons";
    "()", "tt";
    "true", "true";
    "false", "false";
    "Nil", "nil";
    "Cons", "cons";
    "Stream.Nil", "nil";
    "Stream.Cons", "cons";
    ]

let inlined_primitives_names =
   List.map (fun (x,(n,y)) -> name_of_mlpath x, n) inlined_primitives_table

let is_inlined_primitive_name p arity =
   match list_assoc_option (name_of_mlpath p) inlined_primitives_names with
   | None -> false
   | Some n -> (arity = n)

let find_inlined_primitive p arity =
   match list_assoc_option p inlined_primitives_table with
   | None -> None
   | Some (n,x) -> if n = arity then Some x else None

let find_primitive p =
   list_assoc_option p all_primitives_table

let find_builtin_constructor p =
   list_assoc_option p builtin_constructors_table

let skip_cf_for = function
  | "!$" -> true
  | _ -> false

