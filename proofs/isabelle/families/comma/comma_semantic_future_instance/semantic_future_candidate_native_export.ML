(* Serialize exact candidate definitions after Comma_Semantic_Release's audit. *)

structure Comma_Semantic_Future_Candidate_Native_Export =
struct

  val source_count = 16 * 924
  val max_classes = source_count
  val max_payload_bytes = 2 * 1024 * 1024
  val max_rank_digits = 128
  val natT = @{typ nat}

  fun checked_closed receiving_thy label theorem =
    if Thm.nprems_of theorem = 0 andalso null (Thm.hyps_of theorem) andalso
        null (Thm.tpairs_of theorem) andalso
        not (Term.is_open (Thm.prop_of theorem)) andalso
        null (Term.add_frees (Thm.prop_of theorem) []) andalso
        null (Term.add_vars (Thm.prop_of theorem) []) andalso
        Context.subthy (Thm.theory_of_thm theorem, receiving_thy) then theorem
    else error (label ^ " is not a closed theorem admitted in the receiving theory")

  fun definition_rhs receiving_thy expected_constant expected_type label theorem =
    let
      val checked = checked_closed receiving_thy label theorem
      val (lhs, rhs) =
        (case try Logic.dest_equals (Thm.prop_of checked) of
          SOME pair => pair
        | NONE => HOLogic.dest_eq (HOLogic.dest_Trueprop (Thm.prop_of checked)))
      val _ = if lhs aconv expected_constant then ()
        else error (label ^ " proves a different constant definition")
      val _ = if fastype_of rhs = expected_type then ()
        else error (label ^ " has a different constant type")
    in rhs end

  fun natural term =
    (case try HOLogic.dest_number term of
      SOME (typ, value) =>
        if typ = natT andalso value >= 0 then value
        else error "Native candidate export found a non-natural numeral"
    | NONE => error "Native candidate export found a nonliteral natural")

  fun bounded_natural maximum label term =
    let
      val value = natural term
      val _ = if value <= IntInf.fromInt maximum then ()
        else error (label ^ " exceeds the native candidate export bound")
    in IntInf.toInt value end

  fun constructor_name term =
    (case strip_comb term of
      (Const (name, _), args) => (name, args)
    | _ => error "Native candidate export found a malformed constructor")

  fun option_natural maximum label term =
    let
      val (name, args) = constructor_name term
    in
      if name = @{const_name None} andalso null args then "null"
      else if name = @{const_name Some} then
        (case args of
          [value] => Int.toString (bounded_natural maximum label value)
        | _ => error (label ^ " option has the wrong arity"))
      else error (label ^ " is not an option numeral")
    end

  fun control_json term =
    let
      val (name, args) = constructor_name term
    in
      if name = @{const_name Comma_Future_Landmine} andalso null args then
        "[\"landmine\",null]"
      else if name = @{const_name Comma_Future_Fork} then
        (case args of
          [target] =>
            let
              val value = bounded_natural 9 "Fork coefficient" target
              val _ = if 2 <= value then ()
                else error "Fork coefficient is below the source boundary range"
            in "[\"fork\"," ^ Int.toString value ^ "]" end
        | _ => error "Fork control has the wrong arity")
      else error "Native candidate export found an unknown control"
    end

  fun join separator values =
    (case values of
      [] => ""
    | first :: rest => first ^ String.concat
        (map (fn value => separator ^ value) rest))

  fun json_array values = "[" ^ join "," values ^ "]"

  fun varint value =
    if value < 128 then [value]
    else (value mod 128 + 128) :: varint (value div 128)

  fun encode_class_ids ids =
    let
      val bytes = String.implode
        (map Char.chr (List.concat (map varint ids)))
    in Bytes.content (Base64.encode (Bytes.string bytes)) end

  fun render_candidate ids controls children ranks =
    let
      val class_count = length controls
      val _ = if length ids = source_count then ()
        else error "Native candidate source map has the wrong universe size"
      val _ = if 0 < class_count andalso class_count <= max_classes then ()
        else error "Native candidate class count exceeds the supported bound"
      val _ = if length children = class_count andalso length ranks = class_count then ()
        else error "Native candidate class table lengths differ"
      val class_ids = map (bounded_natural (class_count - 1) "Class ID") ids
      val seen = fold (fn id => Inttab.update (id, ())) class_ids Inttab.empty
      val _ = if length (Inttab.keys seen) = class_count andalso
          List.all (Inttab.defined seen) (0 upto (class_count - 1)) then ()
        else error "Native candidate source map omits a class ID"
      val control_values = map control_json controls
      val child_values = map (fn row =>
        let
          val (left, right) = HOLogic.dest_prod row
        in json_array
          [option_natural (class_count - 1) "Left child" left,
           option_natural (class_count - 1) "Right child" right]
        end) children
      val rank_values = map (fn rank =>
        let
          val (name, args) = constructor_name rank
        in
          if name = @{const_name None} andalso null args then "null"
          else if name = @{const_name Some} then
            (case args of
              [value] =>
                let
                  val decimal = IntInf.toString (natural value)
                  val _ = if String.size decimal <= max_rank_digits then ()
                    else error "Native candidate rank exceeds the export digit bound"
                in decimal end
            | _ => error "Candidate rank option has the wrong arity")
          else error "Native candidate rank is not an option numeral"
        end) ranks
      val payload =
        "{\"authority\":\"untrusted-source-derived-candidate\"," ^
        "\"class_of_state_varint_base64\":\"" ^
          encode_class_ids class_ids ^ "\"," ^
        "\"class_rank_candidate\":" ^ json_array rank_values ^ "," ^
        "\"controls\":" ^ json_array control_values ^ "," ^
        "\"format\":\"comma-semantic-future-candidate-v2\"," ^
        "\"ordered_children\":" ^ json_array child_values ^ "," ^
        "\"state_universe\":\"kind=N,Z; a=2..9; residue=0..923; nested-order\"}\n"
      val _ = if String.size payload <= max_payload_bytes then ()
        else error "Native candidate JSON exceeds the bounded payload size"
    in payload end

  fun publish thy =
    let
      val _ = checked_closed thy "Global semantic release theorem"
        @{thm comma_semantic_producer_global_release_contract}
      val _ = checked_closed thy "Checked source-bound candidate provider theorem"
        @{thm comma_semantic_future_candidate_provider_check_checked}
      val _ = checked_closed thy "Checked concrete future rank theorem"
        @{thm comma_semantic_concrete_future_rank_check}
      val _ = checked_closed thy "Candidate class-table theorem"
        @{thm comma_semantic_future_candidate_class_table_checked}
      val ids = definition_rhs
        thy
        @{term comma_semantic_future_candidate_class_ids}
        @{typ "nat list"} "Candidate source-ID definition"
        @{thm comma_semantic_future_candidate_class_ids_def}
      val controls = definition_rhs
        thy
        @{term comma_semantic_future_candidate_controls}
        @{typ "comma_future_control list"} "Candidate controls definition"
        @{thm comma_semantic_future_candidate_controls_def}
      val children = definition_rhs
        thy
        @{term comma_semantic_future_candidate_children}
        @{typ "(nat option \<times> nat option) list"}
        "Candidate ordered-child definition"
        @{thm comma_semantic_future_candidate_children_def}
      val ranks = definition_rhs
        thy
        @{term comma_semantic_future_candidate_ranks}
        @{typ "nat option list"} "Candidate rank definition"
        @{thm comma_semantic_future_candidate_ranks_def}
      val payload = render_candidate
        (HOLogic.dest_list ids) (HOLogic.dest_list controls)
        (HOLogic.dest_list children) (HOLogic.dest_list ranks)
    in
      Export.export thy (Path.explode_binding0
        "comma-semantic-future-candidate-v2.json") [XML.Text payload]
    end

end;

val _ = Comma_Semantic_Future_Candidate_Native_Export.publish @{theory};
