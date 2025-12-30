(* cheat_finder.sml - Extract tactics before cheat using TacticParse

   Usage:
     extract_before_cheat "strip_tac \\\\ simp[] >- cheat"
     => "strip_tac \\\\ simp[]"
*)

(* dropWhile is not in HOL's List structure *)
fun dropWhile _ [] = []
  | dropWhile p (x::xs) = if p x then dropWhile p xs else x::xs;

fun extract_before_cheat source =
  let
    val tree = TacticParse.parseTacticBlock source

    (* Extract text at span (s, e) *)
    fun text_at (s, e) =
      if s >= 0 andalso e <= String.size source andalso s < e then
        String.substring (source, s, e - s)
      else ""

    (* Check if this span contains "cheat" *)
    fun is_cheat span = text_at span = "cheat"

    (* Find start position of first "cheat" in AST; returns NONE if not found *)
    fun find_cheat_pos (TacticParse.Opaque (_, span)) =
          if is_cheat span then SOME (#1 span) else NONE
      | find_cheat_pos (TacticParse.LOpaque (_, span)) =
          if is_cheat span then SOME (#1 span) else NONE
      | find_cheat_pos (TacticParse.OOpaque (_, span)) =
          if is_cheat span then SOME (#1 span) else NONE
      | find_cheat_pos (TacticParse.Then []) = NONE
      | find_cheat_pos (TacticParse.Then items) =
          let fun loop [] = NONE
                | loop (x::xs) = case find_cheat_pos x of SOME p => SOME p | NONE => loop xs
          in loop items end
      | find_cheat_pos (TacticParse.ThenLT (base, arms)) =
          (case find_cheat_pos base of
             SOME pos => SOME pos
           | NONE => let fun loop [] = NONE
                           | loop (x::xs) = case find_cheat_pos x of SOME p => SOME p | NONE => loop xs
                     in loop arms end)
      | find_cheat_pos (TacticParse.LThen (base, arms)) =
          (case find_cheat_pos base of
             SOME pos => SOME pos
           | NONE => let fun loop [] = NONE
                           | loop (x::xs) = case find_cheat_pos x of SOME p => SOME p | NONE => loop xs
                     in loop arms end)
      | find_cheat_pos (TacticParse.First items) =
          let fun loop [] = NONE
                | loop (x::xs) = case find_cheat_pos x of SOME p => SOME p | NONE => loop xs
          in loop items end
      | find_cheat_pos (TacticParse.LFirst items) =
          let fun loop [] = NONE
                | loop (x::xs) = case find_cheat_pos x of SOME p => SOME p | NONE => loop xs
          in loop items end
      | find_cheat_pos (TacticParse.Group (_, _, inner)) = find_cheat_pos inner
      | find_cheat_pos (TacticParse.Try inner) = find_cheat_pos inner
      | find_cheat_pos (TacticParse.LTry inner) = find_cheat_pos inner
      | find_cheat_pos (TacticParse.Repeat inner) = find_cheat_pos inner
      | find_cheat_pos (TacticParse.LRepeat inner) = find_cheat_pos inner
      | find_cheat_pos (TacticParse.LAllGoals inner) = find_cheat_pos inner
      | find_cheat_pos (TacticParse.LHeadGoal inner) = find_cheat_pos inner
      | find_cheat_pos (TacticParse.LLastGoal inner) = find_cheat_pos inner
      | find_cheat_pos (TacticParse.LThenLT items) =
          let fun loop [] = NONE
                | loop (x::xs) = case find_cheat_pos x of SOME p => SOME p | NONE => loop xs
          in loop items end
      | find_cheat_pos (TacticParse.LThen1 inner) = find_cheat_pos inner
      | find_cheat_pos (TacticParse.LTacsToLT inner) = find_cheat_pos inner
      | find_cheat_pos (TacticParse.LNullOk inner) = find_cheat_pos inner
      | find_cheat_pos (TacticParse.LNthGoal (inner, _)) = find_cheat_pos inner
      | find_cheat_pos (TacticParse.LFirstLT inner) = find_cheat_pos inner
      | find_cheat_pos (TacticParse.LSplit (_, a, b)) =
          (case find_cheat_pos a of SOME p => SOME p | NONE => find_cheat_pos b)
      | find_cheat_pos (TacticParse.LSelectThen (a, b)) =
          (case find_cheat_pos a of SOME p => SOME p | NONE => find_cheat_pos b)
      | find_cheat_pos (TacticParse.List (_, items)) =
          let fun loop [] = NONE
                | loop (x::xs) = case find_cheat_pos x of SOME p => SOME p | NONE => loop xs
          in loop items end
      | find_cheat_pos (TacticParse.MapEvery (_, items)) =
          let fun loop [] = NONE
                | loop (x::xs) = case find_cheat_pos x of SOME p => SOME p | NONE => loop xs
          in loop items end
      | find_cheat_pos (TacticParse.MapFirst (_, items)) =
          let fun loop [] = NONE
                | loop (x::xs) = case find_cheat_pos x of SOME p => SOME p | NONE => loop xs
          in loop items end
      | find_cheat_pos (TacticParse.RepairGroup (_, _, inner, _)) = find_cheat_pos inner
      (* Remaining cases have no inner tac_expr to search *)
      | find_cheat_pos (TacticParse.Subgoal _) = NONE
      | find_cheat_pos (TacticParse.Rename _) = NONE
      | find_cheat_pos (TacticParse.LSelectGoal _) = NONE
      | find_cheat_pos (TacticParse.LSelectGoals _) = NONE
      | find_cheat_pos TacticParse.LReverse = NONE
      | find_cheat_pos (TacticParse.RepairEmpty _) = NONE

    (* Trim trailing whitespace *)
    fun trim_right s =
      String.implode (List.rev (dropWhile Char.isSpace (List.rev (String.explode s))))

    (* Check and strip trailing separator *)
    fun ends_with str suffix =
      let val slen = String.size str val plen = String.size suffix in
        slen >= plen andalso String.substring (str, slen - plen, plen) = suffix
      end

    fun strip_trailing_sep str =
      if ends_with str "\\\\" then String.substring (str, 0, String.size str - 2)
      else if ends_with str ">>" then String.substring (str, 0, String.size str - 2)
      else if ends_with str ">-" then String.substring (str, 0, String.size str - 2)
      else str

    (* Repeatedly trim whitespace and separators *)
    fun clean s =
      let
        val s1 = trim_right s
        val s2 = strip_trailing_sep s1
        val s3 = trim_right s2
      in
        if s3 = s then s else clean s3
      end

    (* Check if AST contains RepairGroup (unbalanced delimiters) or RepairEmpty *)
    fun has_repair (TacticParse.RepairGroup _) = true
      | has_repair (TacticParse.RepairEmpty _) = true
      | has_repair (TacticParse.Then items) = List.exists has_repair items
      | has_repair (TacticParse.ThenLT (base, arms)) =
          has_repair base orelse List.exists has_repair arms
      | has_repair (TacticParse.LThen (base, arms)) =
          has_repair base orelse List.exists has_repair arms
      | has_repair (TacticParse.First items) = List.exists has_repair items
      | has_repair (TacticParse.LFirst items) = List.exists has_repair items
      | has_repair (TacticParse.Group (_, _, inner)) = has_repair inner
      | has_repair (TacticParse.Try inner) = has_repair inner
      | has_repair (TacticParse.LTry inner) = has_repair inner
      | has_repair (TacticParse.Repeat inner) = has_repair inner
      | has_repair (TacticParse.LRepeat inner) = has_repair inner
      | has_repair (TacticParse.LAllGoals inner) = has_repair inner
      | has_repair (TacticParse.LHeadGoal inner) = has_repair inner
      | has_repair (TacticParse.LLastGoal inner) = has_repair inner
      | has_repair (TacticParse.LThenLT items) = List.exists has_repair items
      | has_repair (TacticParse.LThen1 inner) = has_repair inner
      | has_repair (TacticParse.LTacsToLT inner) = has_repair inner
      | has_repair (TacticParse.LNullOk inner) = has_repair inner
      | has_repair (TacticParse.LNthGoal (inner, _)) = has_repair inner
      | has_repair (TacticParse.LFirstLT inner) = has_repair inner
      | has_repair (TacticParse.LSplit (_, a, b)) =
          has_repair a orelse has_repair b
      | has_repair (TacticParse.LSelectThen (a, b)) =
          has_repair a orelse has_repair b
      | has_repair (TacticParse.List (_, items)) = List.exists has_repair items
      | has_repair (TacticParse.MapEvery (_, items)) = List.exists has_repair items
      | has_repair (TacticParse.MapFirst (_, items)) = List.exists has_repair items
      | has_repair _ = false

  in
    case find_cheat_pos tree of
      NONE => ""  (* No cheat found *)
    | SOME pos =>
        if pos = 0 then ""
        else
          let val prefix = clean (String.substring (source, 0, pos))
              val prefix_tree = TacticParse.parseTacticBlock prefix
          in
            (* Reject unbalanced syntax - prefix must parse without repair nodes *)
            if has_repair prefix_tree then "" else prefix
          end
  end
  handle _ => "";
