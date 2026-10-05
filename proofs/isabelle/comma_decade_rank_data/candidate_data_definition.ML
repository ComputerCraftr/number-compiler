structure Comma_Decade_Candidate_Data =
struct
  structure Node_Key = Table(
    type key = int * int list
    val ord = prod_ord int_ord (list_ord int_ord))

  fun candidate_code max_code c =
    let val n = Char.ord c - Char.ord #"A"
    in
      if 0 <= n andalso n <= max_code then n
      else error "Malformed untrusted decade candidate row"
    end

  fun validate_row max_code row =
    let
      val _ = if max_code >= 0 then () else error "Negative candidate alphabet bound"
      val chars = String.explode row
      val _ = if length chars = 91 then ()
        else error "Malformed untrusted decade candidate row"
      val codes = map (candidate_code max_code) chars
    in codes end

  fun validate_rows {max_code, rows} =
    let
      val _ = if max_code >= 0 then () else error "Negative candidate alphabet bound"
      val _ = if length rows = 924 then ()
        else error "Incomplete untrusted decade candidate rows"
    in map (validate_row max_code) rows end

  fun define lthy {binding, max_code, rows, description} =
    let
      val started = Time.now ()
      val _ = if max_code >= 0 then () else error "Negative candidate alphabet bound"
      val numerals = Vector.tabulate (max_code + 1, fn n =>
        (HOLogic.mk_number @{typ nat} n, n))
      val nodes = Unsynchronized.ref (Node_Key.empty: (term * int) Node_Key.table)
      val next = Unsynchronized.ref (max_code + 1)
      val hits = Unsynchronized.ref 0
      fun checkpoint stage =
        if getenv "COMMA_PROFILE_LOG" = "" then () else
          Comma_Proof_Profile.report
            ("Comma candidate definition " ^ binding ^ " stage=" ^ stage ^
            " elapsed_ms=" ^ Comma_Proof_Profile.elapsed_ms started ^
            " interned=" ^ Int.toString (!next - max_code - 1) ^
            " shared=" ^ Int.toString (!hits))

      val _ = checkpoint "validation-start"
      val parsed = validate_rows {max_code = max_code, rows = rows}
      val _ = checkpoint "validated"

      fun node level children =
        let
          val _ = if null children then error "Empty ragged candidate node" else ()
          val key = (level, map #2 children)
        in
          case Node_Key.lookup (!nodes) key of
            SOME result => (hits := !hits + 1; result)
          | NONE =>
              let
                val terms = map #1 children
                val result = (HOLogic.mk_list (fastype_of (hd terms)) terms, !next)
                val _ = next := !next + 1
                val _ = nodes := Node_Key.update (key, result) (!nodes)
              in result end
        end

      fun row_tree row =
        node 2 (map (node 1 o map (fn n => Vector.sub (numerals, n)))
          (chop_groups 16 row))

      val _ = checkpoint "construction-start"
      val phase_rows = map row_tree parsed
      val _ = checkpoint "row-trees"
      val phase_groups = map (node 3) (chop_groups 16 phase_rows)
      val _ = checkpoint "phase-groups"
      val phase_quarters = map (node 4) (chop_groups 16 phase_groups)
      val _ = checkpoint "phase-quarters"
      val (body, _) = node 5 phase_quarters
      val _ = checkpoint "root-built"
      val _ = checkpoint "local-define-start"
      val result = Local_Theory.define
        ((Binding.name binding, NoSyn),
          ((Binding.name (binding ^ "_def"), []), body)) lthy
      val _ = checkpoint "local-define-finished"
      val _ = warning (description ^ ": nodes=" ^ Int.toString (!next - max_code - 1) ^
        " shared=" ^ Int.toString (!hits) ^ " milliseconds=" ^
        LargeInt.toString (Time.toMilliseconds (Time.- (Time.now (), started))))
    in #2 result end
end

(* Reject malformed dimensions and alphabet values before term construction. *)
val _ =
  let
    fun rejected message f =
      (case Exn.capture f () of
        Exn.Exn (ERROR actual) => actual = message
      | _ => false)
    val short_row = String.implode (replicate 90 #"A")
    val valid_row = String.implode (replicate 91 #"A")
    val negative_code = String.implode (replicate 90 #"A" @ [#"?"])
    val excessive_code = String.implode (replicate 90 #"A" @ [#"J"])
    val malformed = "Malformed untrusted decade candidate row"
    val incomplete = "Incomplete untrusted decade candidate rows"
    val short_rejected = rejected malformed (fn () =>
      Comma_Decade_Candidate_Data.validate_row 26 short_row)
    val negative_code_rejected = rejected malformed (fn () =>
      Comma_Decade_Candidate_Data.validate_row 8 negative_code)
    val excessive_code_rejected = rejected malformed (fn () =>
      Comma_Decade_Candidate_Data.validate_row 8 excessive_code)
    val too_few_rejected = rejected incomplete (fn () =>
      Comma_Decade_Candidate_Data.validate_rows
        {max_code = 26, rows = replicate 923 ""})
    val too_many_rejected = rejected incomplete (fn () =>
      Comma_Decade_Candidate_Data.validate_rows
        {max_code = 26, rows = replicate 925 ""})
    val negative_bound_rejected = rejected "Negative candidate alphabet bound" (fn () =>
      Comma_Decade_Candidate_Data.validate_row ~1 valid_row)
  in
    if short_rejected andalso negative_code_rejected andalso
        excessive_code_rejected andalso too_few_rejected andalso too_many_rejected andalso
        negative_bound_rejected then ()
    else error "Malformed candidate rows were not rejected"
  end
