(* etq.sml - "Evaluate Tactic Quoted" for goaltree mode

   etq takes a tactic as a string, compiles it at runtime using smlExecute,
   and applies it via goaltree's `et` which records both the string and
   the compiled tactic. This lets p() show the exact proof script.

   Usage:
     gt `A /\ B ==> B /\ A`;
     etq "DISCH_TAC";
     etq "CONJ_TAC";
     etq "ASM_REWRITE_TAC []";
     p();  (* Shows: DISCH_TAC \\ CONJ_TAC >- (...) >- (...) *)

   Eliminates duplication: etq "tac" instead of et ("tac", tac)
*)

val _ = app load ["aiLib", "smlTimeout", "smlLexer", "smlExecute"];

fun etq s = proofManagerLib.et (s, smlExecute.tactic_of_sml 30.0 s)
  handle HOL_ERR _ =>
    raise HOL_ERR {origin_structure = "etq",
                   origin_function = "etq",
                   message = "Cannot compile tactic: " ^ s};
