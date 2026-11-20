(* Export the exact checked M204 definitions, without enumerating occurrences. *)
structure Comma_Semantic_Future_Candidate_Native_Export =
struct
  val natT = @{typ nat}
  val nodeT = @{typ "nat comma_crt_mdd_node"}
  val nodesT = HOLogic.listT nodeT
  val chunksT = HOLogic.listT nodesT
  val rowsT = @{typ "comma_future_m204_row list"}
  val max_bytes = 2 * 1024 * 1024

  fun closed thy label theorem =
    if Thm.nprems_of theorem = 0 andalso null (Thm.hyps_of theorem) andalso
        null (Thm.tpairs_of theorem) andalso not (Term.is_open (Thm.prop_of theorem)) andalso
        null (Term.add_frees (Thm.prop_of theorem) []) andalso
        null (Term.add_vars (Thm.prop_of theorem) []) andalso
        Context.subthy (Thm.theory_of_thm theorem,thy)
    then theorem else error (label ^ " is not a closed theorem in the receiving theory")

  fun rhs thy constant typ label theorem =
    let
      val checked = closed thy label theorem
      val (left,right) =
        (case try Logic.dest_equals (Thm.prop_of checked) of
          SOME pair => pair
        | NONE => HOLogic.dest_eq (HOLogic.dest_Trueprop (Thm.prop_of checked)))
      val _ = if left aconv constant andalso fastype_of right = typ then ()
        else error (label ^ " does not define the expected constant")
    in right end

  fun natural term =
    (case try HOLogic.dest_number term of
      SOME (typ,value) => if typ = natT andalso value >= 0 then value
        else error "M204 export encountered a non-natural number"
    | NONE => error "M204 export encountered a nonliteral number")
  fun bounded bound label term =
    let val value = natural term
    in if value < IntInf.fromInt bound then IntInf.toInt value
      else error (label ^ " is outside its bound") end
  fun array parts = "[" ^ space_implode "," parts ^ "]"
  fun constructor term =
    (case strip_comb term of (Const (name,_),args) => (name,args)
    | _ => error "M204 export encountered a nonliteral constructor")
  fun option term =
    (case constructor term of
      (name,[]) => if name = @{const_name None} then NONE
        else error "M204 export encountered a malformed option"
    | (name,[x]) => if name = @{const_name Some} then SOME x
        else error "M204 export encountered a malformed option"
    | _ => error "M204 export encountered a malformed option")
  fun optional_nat bound label term =
    (case option term of NONE => "null"
    | SOME value => Int.toString (bounded bound label value))

  (* The table definition is a balanced append tree over chunk selections.
     Inspect its syntax against the checked definitions instead of replaying
     a separate lookup proof for every row. *)
  fun selected_chunks chunks term =
    (case strip_comb term of
      (Const (name,_),[left,right]) =>
        if name = @{const_name append} then
          selected_chunks chunks left @ selected_chunks chunks right
        else if name = @{const_name nth} andalso left aconv chunks then
          [bounded 65536 "MDD chunk index" right]
        else error "M204 table contains an unexpected selection"
    | _ => error "M204 table contains an unexpected expression")

  fun node_json node =
    (case constructor node of
      (name,[value]) =>
        if name = @{const_name Comma_CRT_MDD_Leaf} then
          array [IntInf.toString (natural value)]
        else error "M204 export found an unknown leaf"
    | (name,[axis,children]) =>
        if name = @{const_name Comma_CRT_MDD_Branch} then
          array [Int.toString (bounded 4 "MDD axis" axis),
            array (map (Int.toString o bounded 65536 "MDD child")
              (HOLogic.dest_list children))]
        else error "M204 export found an unknown branch"
    | _ => error "M204 export found a malformed node")

  fun row_json class_count row =
    let
      val (control,rest) = HOLogic.dest_prod row
      val (children,rank) = HOLogic.dest_prod rest
      val children = HOLogic.dest_list children
      val (control_json,children_json) =
        (case option control of
          NONE => if null children then ("[\"landmine\",null]","[null,null]")
            else error "M204 Landmine has children"
        | SOME digit =>
            let val d = bounded 10 "Fork digit" digit
                val _ = if 2 <= d andalso length children = 2 then ()
                  else error "M204 Fork has malformed ordered children"
            in ("[\"fork\"," ^ Int.toString d ^ "]",
              array (map (Int.toString o bounded class_count "Child class") children)) end)
      val rank_json = (case option rank of NONE => "null"
        | SOME value => let val text = IntInf.toString (natural value)
          in if size text <= 128 then text else error "M204 rank is oversized" end)
    in (control_json,children_json,rank_json) end

  fun publish thy =
    let
      val ctxt = Proof_Context.init_global thy
      val release = closed thy "Global release" @{thm comma_semantic_producer_global_release_contract}
      val rank = closed thy "M204 rank" @{thm comma_future_m204_compact_rank_native}
      val _ = Comma_Proof_Dependency_Audit.require_native_clean ctxt "M204 export" [release,rank]
      val class_map = @{term comma_future_m204_compact_class_map}
      val rows_constant = @{term comma_future_m204_class_rows}
      val morphism = closed thy "M204 compact physical morphism"
        @{thm comma_future_m204_compact_morphism_native}
      val weight = @{term comma_frontier_m204_weight}
      val expected_morphism = HOLogic.mk_Trueprop (Envir.beta_norm
        (@{term "\<lambda>D::nat \<Rightarrow> nat \<Rightarrow> nat.
          \<lambda>rows::comma_future_m204_row list.
          \<lambda>class_of::comma_boundary_state \<Rightarrow> nat.
          \<forall>q J delta. comma_boundary_valid q \<longrightarrow>
            comma_future_m204_source_output D q = Some (J,delta) \<longrightarrow>
            comma_future_m204_graph_control rows (class_of q) = Suc J \<and>
            comma_future_m204_graph_child rows (class_of q) 0 =
              (if J=8 then 0 else Suc (class_of
                (Comma_N,J+2,(snd (snd q)+delta) mod 924))) \<and>
            comma_future_m204_graph_child rows (class_of q) 1 =
              (if J=8 then 0 else Suc (class_of
                (Comma_Z,J+2,(snd (snd q)+delta) mod 924)))"} $
          weight $ rows_constant $ class_map))
      val _ = Comma_CRT_MDD_Proof_Utils.exact_prop ctxt
        "M204 compact physical morphism export authority" expected_morphism morphism
      val _ = Comma_Proof_Dependency_Audit.require_native_clean ctxt
        "M204 export compact physical morphism" [morphism]
      val expected_rank = HOLogic.mk_Trueprop (Envir.beta_norm
        (@{term "\<lambda>rows::comma_future_m204_row list.
          \<lambda>class_of::comma_boundary_state \<Rightarrow> nat.
          comma_semantic_rank_check comma_boundary_valid
            (comma_future_m204_rank rows \<circ> class_of)
            (comma_semantic_boundary_children comma_semantic_decade_summary)
            (comma_semantic_boundary_control_step comma_semantic_decade_summary)"} $
          rows_constant $ class_map))
      val _ = Comma_CRT_MDD_Proof_Utils.exact_prop ctxt
        "M204 rank export authority" expected_rank rank
      val table = @{term comma_future_m204_compact_nodes}
      val chunks = @{term comma_future_m204_compact_nodes_chunks}
      val map_rhs = rhs thy class_map (fastype_of class_map) "Class map" @{thm comma_future_m204_compact_class_map_def}
      val roots_term = (case strip_comb map_rhs of
        (head,[actual_table,roots]) =>
          if head aconv @{term comma_future_m204_mdd_class} andalso actual_table aconv table
          then roots else error "M204 class map is not bound to the exported table"
        | _ => error "M204 class map definition has an unexpected shape")
      val table_rhs = rhs thy table nodesT "MDD table" @{thm comma_future_m204_compact_nodes_def}
      val chunks_rhs = rhs thy chunks chunksT "MDD chunks" @{thm comma_future_m204_compact_nodes_chunks_def}
      val literal_chunks = map HOLogic.dest_list (HOLogic.dest_list chunks_rhs)
      val order = selected_chunks chunks table_rhs
      val _ = if order = (0 upto (length literal_chunks - 1)) then ()
        else error "M204 table changes the checked chunk ordering"
      val nodes = List.concat literal_chunks
      val _ = if 0 < length nodes andalso length nodes <= 65536 then ()
        else error "M204 node count exceeds the supported bound"
      val roots = map (Int.toString o bounded (length nodes) "MDD root")
        (HOLogic.dest_list roots_term)
      val _ = if length roots = 16 then () else error "M204 needs sixteen source roots"
      val rows_term = rhs thy rows_constant rowsT
        "M204 class rows" @{thm comma_future_m204_class_rows_def}
      val row_chunks = @{term comma_future_m204_class_rows_chunks}
      val row_chunks_rhs = rhs thy row_chunks (HOLogic.listT rowsT)
        "M204 class row chunks" @{thm comma_future_m204_class_rows_chunks_def}
      val literal_row_chunks = map HOLogic.dest_list (HOLogic.dest_list row_chunks_rhs)
      val row_order = selected_chunks row_chunks rows_term
      val _ = if row_order = (0 upto (length literal_row_chunks - 1)) then ()
        else error "M204 class rows change the checked chunk ordering"
      val rows = List.concat literal_row_chunks
      val count = length rows
      val _ = if 0 < count andalso count <= 14784 then ()
        else error "M204 class count exceeds the supported bound"
      val rendered = map (row_json count) rows
      val payload =
        "{\"authority\":\"untrusted-source-derived-candidate\"," ^
        "\"class_rank_candidate\":" ^ array (map #3 rendered) ^ "," ^
        "\"controls\":" ^ array (map #1 rendered) ^ "," ^
        "\"format\":\"comma-semantic-future-candidate-v3\"," ^
        "\"ordered_children\":" ^ array (map #2 rendered) ^ "," ^
        "\"source_nodes\":" ^ array (map node_json nodes) ^ "," ^
        "\"source_radices\":[3,4,7,11]," ^
        "\"source_roots\":" ^ array roots ^ "," ^
        "\"state_universe\":\"kind=N,Z; a=2..9; residue=0..923; nested-order\"}\n"
      val _ = if size payload <= max_bytes then () else error "M204 export exceeds the byte bound"
    in Export.export thy (Path.explode_binding0 "comma-semantic-future-candidate-v3.json")
      [XML.Text payload] end
end;

val _ = Comma_Semantic_Future_Candidate_Native_Export.publish @{theory};
