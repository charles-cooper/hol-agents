(* etq.sml - "Evaluate Tactic Quoted" for goaltree mode

   Mirrors HOL's etqLib but with output optimizations:
   - Returns unit (not proof) to avoid REPL auto-printing the proof tree
   - Prints only goal count + first goal (not all goals)

   Usage:
     gt `A /\ B ==> B /\ A`;
     etq "DISCH_TAC";
     etq "CONJ_TAC";
     etq "ASM_REWRITE_TAC []";
     p();  (* Shows: DISCH_TAC \\ CONJ_TAC >- (...) >- (...) *)
*)

val _ = load "smlExecute";

fun print_goal g =
  HOLPP.prettyPrint (print, !Globals.linewidth) (goalStack.pp_goal g);

fun print_goals [] = print "Goal proved.\n"
  | print_goals [g] = print_goal g
  | print_goals (g::gs) =
      (print (Int.toString (1 + length gs) ^ " subgoals:\n\n"); print_goal g);

fun etq_tmo timeout s =
  let
    val _ = proofManagerLib.et (s, smlExecute.tactic_of_sml timeout s)
    val goals = proofManagerLib.top_goals ()
  in
    print_goals goals
  end
  handle e => raise mk_HOL_ERR "etq" "etq" (Feedback.exn_to_string e);

val etq = etq_tmo 30.0;
