(*
  common datatypes bwtween cpsword and word semantics
*)
open preamble;

val _ = new_theory"wordcommon";

val _ = Datatype `
  word_loc = Word ('a word) | Loc num num `;


val _ = export_theory();
