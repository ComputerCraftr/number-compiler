(* Proof-producing conversion and run-local profiling for canonical template
   partition certificates and their shared cofactor states. *)
structure Comma_Semantic_B1_Partition_Conversion =
struct
  fun shape depth term =
    let
      fun label current =
        (case Term.head_of current of
          Const (name, _) => Long_Name.base_name name
        | Free (_, _) => "Free"
        | Var (_, _) => "Var"
        | Bound _ => "Bound"
        | Abs _ => "Abs")
      val head = label term
      val (_, arguments) = strip_comb term
    in
      if depth = 0 orelse null arguments then head
      else head ^ "(" ^ String.concatWith ","
        (map (shape (depth - 1)) (take 4 arguments)) ^
        (if length arguments > 4 then ",..." else "") ^ ")"
    end
  fun profile_message make_message =
    if Comma_Proof_Profile.enabled () then
      Comma_Proof_Profile.report (make_message ()) else ()
  fun profile_stage name phase elapsed = profile_message (fn () =>
    "B1 partition stage=" ^ name ^ " phase=" ^ phase ^
    (case elapsed of NONE => "" | SOME ms => " elapsed_ms=" ^ LargeInt.toString ms))
  fun make_template_partition_profile () =
    let
      val active = Unsynchronized.ref 0
      val certificate_conversions = Unsynchronized.ref 0
      val certificate_memo_hits = Unsynchronized.ref 0
      val cofactor_state_conversions = Unsynchronized.ref 0
      val cofactor_state_memo_hits = Unsynchronized.ref 0
      val cofactor_state_normalizations = Unsynchronized.ref 0
      val cofactor_state_normalization_rewrites = Unsynchronized.ref 0
      val cofactor_state_normalization_ms = Unsynchronized.ref (0: LargeInt.int)
      val cofactor_root_rewrite_calls = Unsynchronized.ref 0
      val cofactor_root_rewrite_ms = Unsynchronized.ref (0: LargeInt.int)
      val cofactor_recursive_rewrite_calls = Unsynchronized.ref 0
      val cofactor_recursive_rewrite_ms = Unsynchronized.ref (0: LargeInt.int)
      val template_geometry_stage_times = Unsynchronized.ref
        (Symtab.empty: (int * LargeInt.int) Symtab.table)
      val cofactor_state_shape_checks = Unsynchronized.ref 0
      val cofactor_state_shape_cache_hits = Unsynchronized.ref 0
      val cofactor_state_cache_probes = Unsynchronized.ref 0
      val cofactor_state_cache_probe_ms = Unsynchronized.ref (0: LargeInt.int)
      val cid_state_conversions = Unsynchronized.ref 0
      val cid_state_memo_hits = Unsynchronized.ref 0
      val cid_vector_transitions = Unsynchronized.ref 0
      val cid_vector_transition_hits = Unsynchronized.ref 0
      fun is_certificate request =
        (case Term.head_of request of
          Const (name, _) =>
            name = @{const_name comma_semantic_b1_crt_columns_partition_certified}
        | _ => false)
      fun is_template_geometry request =
        (case Term.head_of request of
          Const (name, _) =>
            name = @{const_name comma_semantic_b1_crt_template_geometry_certified}
        | _ => false)
      fun is_profile_scope request =
        is_certificate request orelse is_template_geometry request
      fun is_cofactor_state request =
        (case Term.head_of request of
          Const (name, _) =>
            name = @{const_name comma_semantic_b1_crt_partition_cofactor_checked}
        | _ => false)
      fun stats () =
        "template_partition_certificate_conversions=" ^
          Int.toString (!certificate_conversions) ^
        " template_partition_certificate_memo_hits=" ^
          Int.toString (!certificate_memo_hits) ^
        " template_partition_cofactor_state_conversions=" ^
          Int.toString (!cofactor_state_conversions) ^
        " template_partition_cofactor_state_memo_hits=" ^
          Int.toString (!cofactor_state_memo_hits) ^
        " template_partition_cofactor_state_normalizations=" ^
          Int.toString (!cofactor_state_normalizations) ^
        " template_partition_cofactor_state_normalization_rewrites=" ^
          Int.toString (!cofactor_state_normalization_rewrites) ^
        " template_partition_cofactor_state_normalization_ms=" ^
          LargeInt.toString (!cofactor_state_normalization_ms) ^
        " template_partition_cofactor_root_rewrite_calls=" ^
          Int.toString (!cofactor_root_rewrite_calls) ^
        " template_partition_cofactor_root_rewrite_inclusive_ms=" ^
          LargeInt.toString (!cofactor_root_rewrite_ms) ^
        " template_partition_cofactor_recursive_rewrite_calls=" ^
          Int.toString (!cofactor_recursive_rewrite_calls) ^
        " template_partition_cofactor_recursive_rewrite_inclusive_ms=" ^
          LargeInt.toString (!cofactor_recursive_rewrite_ms) ^
        " template_partition_cofactor_state_shape_checks=" ^
          Int.toString (!cofactor_state_shape_checks) ^
        " template_partition_cofactor_state_shape_cache_hits=" ^
          Int.toString (!cofactor_state_shape_cache_hits) ^
        " template_partition_cofactor_state_cache_probes=" ^
          Int.toString (!cofactor_state_cache_probes) ^
        " template_partition_cofactor_state_cache_probe_ms=" ^
          LargeInt.toString (!cofactor_state_cache_probe_ms) ^
        " template_partition_cid_state_conversions=" ^
          Int.toString (!cid_state_conversions) ^
        " template_partition_cid_state_memo_hits=" ^
          Int.toString (!cid_state_memo_hits) ^
        " template_partition_cid_vector_transitions=" ^
          Int.toString (!cid_vector_transitions) ^
        " template_partition_cid_vector_transition_memo_hits=" ^
          Int.toString (!cid_vector_transition_hits) ^
        " template_geometry_premise_times=" ^
          String.concatWith ","
            (map (fn (name, (calls, elapsed)) =>
              name ^ ":" ^ Int.toString calls ^ ":" ^ LargeInt.toString elapsed)
              (Symtab.dest (!template_geometry_stage_times)))
      fun capture_conversion request work =
        if is_profile_scope request then
          let
            val prior_depth = !active
            val _ = active := prior_depth + 1
            val result = Exn.capture work ()
            val entered_depth = !active
            val _ = active := prior_depth
            val _ = if entered_depth = prior_depth + 1 then ()
              else error "B1 partition conversion depth changed unexpectedly"
          in result end
        else Exn.capture work ()
      fun note_memo_hit request =
        if is_certificate request then
          certificate_memo_hits := !certificate_memo_hits + 1
        else if !active > 0 andalso is_cofactor_state request then
          cofactor_state_memo_hits := !cofactor_state_memo_hits + 1
        else ()
      fun note_result request result =
        (case result of
          SOME _ =>
            if is_certificate request then
              certificate_conversions := !certificate_conversions + 1
            else if !active > 0 andalso is_cofactor_state request then
              cofactor_state_conversions := !cofactor_state_conversions + 1
            else ()
        | NONE => ())
      fun report_partial request rhs counters =
        if (is_certificate request orelse is_cofactor_state request) andalso
            Comma_Proof_Profile.enabled () then
          Comma_Proof_Profile.report
            ("B1 partition checker partial head=" ^
             (case Term.head_of request of
               Const (name, _) => name
             | _ => "<non-constant>") ^
             " request_shape=" ^ shape 7 request ^
             " rhs_shape=" ^ shape 9 rhs ^
             " counters=" ^ counters ())
        else ()
    in
      {is_certificate = is_certificate, is_cofactor_state = is_cofactor_state,
       inside = fn () => !active > 0,
       capture_conversion = capture_conversion,
       cofactor_state_counts = fn () =>
         (!cofactor_state_conversions, !cofactor_state_memo_hits),
       certificate_counts = fn () =>
         (!certificate_conversions, !certificate_memo_hits),
       note_cofactor_state_normalization = fn (elapsed, rewritten) =>
         if !active > 0 then
           (cofactor_state_normalizations := !cofactor_state_normalizations + 1;
            if rewritten then cofactor_state_normalization_rewrites :=
              !cofactor_state_normalization_rewrites + 1 else ();
            cofactor_state_normalization_ms :=
              !cofactor_state_normalization_ms + elapsed)
         else (),
       cofactor_state_normalization_counts = fn () =>
         (!cofactor_state_normalizations,
          !cofactor_state_normalization_rewrites,
          !cofactor_state_normalization_ms),
       note_cofactor_state_rewrite = fn (root, elapsed) =>
         if !active > 0 then
           if root then
             (cofactor_root_rewrite_calls := !cofactor_root_rewrite_calls + 1;
              cofactor_root_rewrite_ms := !cofactor_root_rewrite_ms + elapsed)
           else
             (cofactor_recursive_rewrite_calls :=
                !cofactor_recursive_rewrite_calls + 1;
              cofactor_recursive_rewrite_ms :=
                !cofactor_recursive_rewrite_ms + elapsed)
         else (),
       cofactor_state_rewrite_counts = fn () =>
         (!cofactor_root_rewrite_calls, !cofactor_root_rewrite_ms,
          !cofactor_recursive_rewrite_calls, !cofactor_recursive_rewrite_ms),
       note_cofactor_state_shape_check = fn () =>
         if !active > 0 then cofactor_state_shape_checks :=
           !cofactor_state_shape_checks + 1 else (),
       note_cofactor_state_shape_cache_hit = fn () =>
         if !active > 0 then cofactor_state_shape_cache_hits :=
           !cofactor_state_shape_cache_hits + 1 else (),
       cofactor_state_shape_counts = fn () =>
         (!cofactor_state_shape_checks, !cofactor_state_shape_cache_hits),
       note_cofactor_state_cache_probe = fn elapsed =>
         if !active > 0 then
           (cofactor_state_cache_probes := !cofactor_state_cache_probes + 1;
            cofactor_state_cache_probe_ms := !cofactor_state_cache_probe_ms + elapsed)
         else (),
       cofactor_state_cache_probe_counts = fn () =>
        (!cofactor_state_cache_probes, !cofactor_state_cache_probe_ms),
       note_cid_state = fn hit => if !active > 0 then
         if hit then cid_state_memo_hits := !cid_state_memo_hits + 1
         else cid_state_conversions := !cid_state_conversions + 1 else (),
       note_cid_vector_transition = fn hit => if !active > 0 then
         if hit then cid_vector_transition_hits := !cid_vector_transition_hits + 1
         else cid_vector_transitions := !cid_vector_transitions + 1 else (),
       note_template_geometry_stage = fn (name, elapsed) =>
         let
           val (calls, total) = the_default (0, 0: LargeInt.int)
             (Symtab.lookup (!template_geometry_stage_times) name)
         in template_geometry_stage_times := Symtab.update
           (name, (calls + 1, total + elapsed)) (!template_geometry_stage_times)
         end,
       reset_cofactor_run_counts = fn () =>
         (cofactor_state_conversions := 0;
          cofactor_state_memo_hits := 0;
          cofactor_state_normalizations := 0;
          cofactor_state_normalization_rewrites := 0;
          cofactor_state_normalization_ms := 0;
          cofactor_root_rewrite_calls := 0;
          cofactor_root_rewrite_ms := 0;
          cofactor_recursive_rewrite_calls := 0;
          cofactor_recursive_rewrite_ms := 0;
          cofactor_state_shape_checks := 0;
          cofactor_state_shape_cache_hits := 0;
          cofactor_state_cache_probes := 0;
          cofactor_state_cache_probe_ms := 0;
          cid_state_conversions := 0;
          cid_state_memo_hits := 0;
          cid_vector_transitions := 0;
          cid_vector_transition_hits := 0;
          template_geometry_stage_times := Symtab.empty),
       note_memo_hit = note_memo_hit,
       note_result = note_result,
       report_partial = report_partial,
       stats = stats}
    end
  fun rewrite_template_partition_certificate context cterm =
    let
      val recursive_rules = @{thms comma_semantic_b1_crt_partition_cofactor_checked.simps}
      val certificate_context =
        (context delsimps recursive_rules) addsimps
          @{thms comma_semantic_b1_crt_columns_partition_certified_def}
    in Simplifier.rewrite certificate_context cterm end
  fun rewrite_partition_cofactor_checked context note_state_rewrite cterm =
    let
      val request = Thm.term_of cterm
      val levels =
        (case strip_comb request of
          (Const (name, _), [levels, _]) =>
            if name = @{const_name comma_semantic_b1_crt_partition_cofactor_checked}
            then levels else error "B1 partition rewrite received another request head"
        | _ => error "B1 partition rewrite received a malformed checker request")
      val root_rule =
        (case try HOLogic.dest_list levels of
          SOME [] => @{thm comma_semantic_b1_crt_partition_cofactor_checked.simps(1)}
        | SOME (_ :: _) => @{thm comma_semantic_b1_crt_partition_cofactor_checked.simps(2)}
        | _ => error "B1 partition checker levels are not a canonical list")
      val root = Conv.rewr_conv (root_rule RS @{thm eq_reflection}) cterm
      val recursive_rules = @{thms comma_semantic_b1_crt_partition_cofactor_checked.simps}
      val step_context = (context delsimps recursive_rules) addsimps
        @{thms comma_semantic_b1_crt_partition_drop_false.simps
          comma_semantic_b1_crt_partition_has_node_at.simps}
      val rewrite_started = Time.now ()
      val rest = Simplifier.rewrite step_context (Thm.rhs_of root)
      val rewrite_elapsed = Time.toMilliseconds
        (Time.- (Time.now (), rewrite_started))
      val _ = note_state_rewrite
        (length (the (try HOLogic.dest_list levels)) = 4, rewrite_elapsed)
    in Thm.transitive root rest end

  (* Prove the public checker from literal CID vectors.  Every recursive edge
     is rewritten by the column converter's exact, cached one-CID equation;
     child checker equations are memoized by the ordered vector, including
     duplicates.  No residual MDD vector is normalized or reified. *)
  fun make_template_state_prover ctxt
      {column_value: int -> term, step: int -> thm,
       cofactor_transition: int * int * int -> {target_cid: int, theorem: thm},
       node_count: int}
      {note_cid_state: bool -> unit, note_cid_vector_transition: bool -> unit} =
    let
      val natT = @{typ nat}
      val columnT = @{typ comma_crt_column}
      val column_listT = HOLogic.listT columnT
      val boolT = @{typ bool}
      val checker_name = @{const_name comma_semantic_b1_crt_partition_cofactor_checked}
      val checker_const = Const (checker_name,
        HOLogic.listT natT --> column_listT --> boolT)
      val drop_false = Const (@{const_name comma_semantic_b1_crt_partition_drop_false},
        column_listT --> column_listT)
      val drop_false_ct = Thm.cterm_of ctxt drop_false
      val cons_ct = Thm.cterm_of ctxt
        (Const (@{const_name Cons}, columnT --> column_listT --> column_listT))
      val has_node = Const (@{const_name comma_semantic_b1_crt_partition_has_node_at},
        natT --> column_listT --> boolT)
      val false_column = @{term "Comma_CRT_Bool False"}
      val true_column = @{term "Comma_CRT_Bool True"}
      val true_list = HOLogic.mk_list columnT [true_column]
      val checker_rules = @{thms comma_semantic_b1_crt_partition_cofactor_checked.simps}
      val base_context =
        (Comma_Entry_Arithmetic.natural_context ctxt
          delsimps (checker_rules @ @{thms list.map
            comma_semantic_b1_crt_partition_drop_false.simps
            comma_semantic_b1_crt_partition_has_node_at.simps
            list.size list.inject list.distinct})) addsimps
        (@{thms list_all_Nil_iff list_all_Cons_iff Let_def
          comma_crt_period_def upt_rec_numeral
          nth_Cons'})
      val zero_step = step 0
      val nonfalse_facts = Unsynchronized.ref (Inttab.empty: thm Inttab.table)
      val residual_head_facts = Unsynchronized.ref (Inttab.empty: thm Inttab.table)
      val residual_head_builds = Unsynchronized.ref 0
      val residual_head_hits = Unsynchronized.ref 0
      val residual_facts = Unsynchronized.ref (Symtab.empty: thm Symtab.table)
      val residual_fallback_scans = Unsynchronized.ref 0
      val residual_transition_derivations = Unsynchronized.ref 0
      val node_facts = Unsynchronized.ref (Symtab.empty: thm Symtab.table)
      val terminal_facts = Unsynchronized.ref (Symtab.empty: thm Symtab.table)
      val state_facts = Unsynchronized.ref (Symtab.empty: thm Symtab.table)
      val state_fact_count = Unsynchronized.ref 0
      val state_requests = Unsynchronized.ref 0
      val vector_transition_facts =
        Unsynchronized.ref (Symtab.empty: (int list * thm) Symtab.table)
      val vector_transition_fact_count = Unsynchronized.ref 0
      val vector_edge_calls = Unsynchronized.ref 0
      val vector_work_times = Array.array (10, Time.zeroTime)
      fun time_work_stage index work =
        if not (Comma_Proof_Profile.enabled ()) then work ()
        else let val start = Time.now () val result = work ()
          val elapsed = Time.- (Time.now (), start)
        in Array.update (vector_work_times, index, Time.+ (Array.sub (vector_work_times, index), elapsed)); result end
      fun vector_work_summary () =
        let val metric = fn (i, name) => " " ^ name ^ "=" ^
          LargeInt.toString (Time.toMilliseconds (Array.sub (vector_work_times, i)))
        in " edge_calls=" ^ Int.toString (!vector_edge_calls) ^ String.concat
          (map metric [(0, "edges_ms"), (1, "map_ms"), (2, "nonfalse_proof_ms"),
            (3, "vector_reduce_ms"), (4, "residual_fallback_ms"), (5, "terminal_ms"),
            (6, "node_ms"), (7, "root_ms"), (8, "residual_transition_ms")]) ^
          metric (9, "column_step_lookup_ms") ^
          " residual_fallbacks=" ^ Int.toString (!residual_fallback_scans) ^
          " residual_from_transitions=" ^ Int.toString (!residual_transition_derivations) ^
          " residual_head_rule_builds=" ^ Int.toString (!residual_head_builds) ^
          " residual_head_rule_hits=" ^ Int.toString (!residual_head_hits)
        end
      fun profile_event message = profile_message (fn () => "B1 partition " ^ message)
      fun level_summary levels =
        (case levels of [] => "terminal" | level :: _ => Int.toString level)
      fun profile_state phase ordinal levels ids =
        if ordinal mod 32 = 0 then profile_message (fn () =>
          "B1 partition state_progress phase=" ^ phase ^ " requests=" ^ Int.toString ordinal ^
          " new=" ^ Int.toString (!state_fact_count) ^ " vectors=" ^
          Int.toString (!vector_transition_fact_count) ^ " level=" ^ level_summary levels ^
          " levels=" ^ Int.toString (length levels) ^ " ids=" ^ Int.toString (length ids)) else ()
      fun number n = HOLogic.mk_number natT n
      fun literal_columns ids = HOLogic.mk_list columnT (map column_value ids)
      fun key levels ids =
        String.concatWith "," (map Int.toString levels) ^ "|" ^
        String.concatWith "," (map Int.toString ids)
      fun clean theorem = Thm.nprems_of theorem = 0 andalso
        null (Thm.hyps_of theorem) andalso null (Thm.tpairs_of theorem)
      fun checked_equation label lhs rhs theorem =
        if Thm.term_of (Thm.lhs_of theorem) aconv lhs andalso
            Thm.term_of (Thm.rhs_of theorem) aconv rhs andalso clean theorem
        then theorem else error
          ("B1 CID partition " ^ label ^ " changed its exact equation; lhs=" ^
           shape 6 (Thm.term_of (Thm.lhs_of theorem)) ^ " rhs=" ^
           shape 10 (Thm.term_of (Thm.rhs_of theorem)) ^ " expected_rhs=" ^
           shape 6 rhs)
      fun rewrite_equation label context lhs rhs =
        let
          val theorem = Simplifier.rewrite context (Thm.cterm_of ctxt lhs)
        in checked_equation label lhs rhs theorem end
      fun nonfalse cid =
        (case Inttab.lookup (!nonfalse_facts) cid of
          SOME theorem => theorem
        | NONE =>
            if cid <= 0 orelse cid >= node_count then
              error "B1 CID partition non-false check received a foreign CID"
            else
              let
                val value = column_value cid
                val value_step = time_work_stage 9 (fn () => step cid)
                val fact = time_work_stage 2 (fn () =>
                  Comma_Semantic_B1_CRT_Operation_Conversion.prove_nonfalse_from_step
                    ctxt value false_column true_column value_step)
              val _ = nonfalse_facts := Inttab.update (cid, fact) (!nonfalse_facts)
              in fact end)
      fun false_residual_head_rule () =
        let
          val generic = @{thm comma_semantic_b1_crt_partition_drop_false_false_head}
            RS @{thm eq_reflection}
          val (_, source_ct) = Thm.dest_comb (Thm.lhs_of generic)
          val (_, tail_ct) = Thm.dest_comb source_ct
          val cons_head = Thm.combination (Thm.reflexive cons_ct) zero_step
          val cons_list = Thm.combination cons_head (Thm.reflexive tail_ct)
          val lifted = Thm.combination (Thm.reflexive drop_false_ct) cons_list
          val theorem = Thm.transitive lifted generic
          val _ = if Thm.term_of (Thm.lhs_of zero_step) aconv (column_value 0) andalso
              Thm.term_of (Thm.rhs_of zero_step) aconv false_column andalso clean theorem
            then () else error "B1 false-head equation did not resolve canonical CID 0"
        in theorem end
      fun residual_head_rule cid =
        (case Inttab.lookup (!residual_head_facts) cid of
          SOME theorem => (residual_head_hits := !residual_head_hits + 1; theorem)
        | NONE =>
            let
              val theorem = if cid = 0 then false_residual_head_rule ()
                else
                  (Drule.infer_instantiate ctxt
                    [(("column", 0), Thm.cterm_of ctxt (column_value cid))]
                    @{thm comma_semantic_b1_crt_partition_drop_false_nonfalse_head}
                   OF [nonfalse cid]) RS @{thm eq_reflection}
              val _ = if clean theorem then () else error
                ("B1 CID partition cons equation is not closed for cid=" ^ Int.toString cid)
              val _ = residual_head_builds := !residual_head_builds + 1
              val _ = residual_head_facts := Inttab.update (cid, theorem) (!residual_head_facts)
            in theorem end)
      fun residual_equation ids =
        let
          val residual_ids = filter (fn cid => cid <> 0) ids
          val state_key = String.concatWith "," (map Int.toString ids)
          val lhs = drop_false $ literal_columns ids
          val rhs = literal_columns residual_ids
        in
          (case Symtab.lookup (!residual_facts) state_key of
            SOME theorem => (theorem, residual_ids)
          | NONE =>
              let
                val _ = residual_fallback_scans := !residual_fallback_scans + 1
                val theorem = time_work_stage 4 (fn () =>
                  let
                    fun build source_ct remaining =
                      case remaining of
                        [] => Conv.rewr_conv
                          (@{thm comma_semantic_b1_crt_partition_drop_false.simps(1)} RS
                            @{thm eq_reflection}) (Thm.apply drop_false_ct source_ct)
                      | cid :: tail_ids =>
                          let
                            val (cons_head_ct, tail_source_ct) = Thm.dest_comb source_ct
                            val (cons_constant_ct, head_ct) = Thm.dest_comb cons_head_ct
                            val _ = (case Thm.term_of cons_constant_ct of
                              Const (name, _) => if name = @{const_name Cons} then ()
                                else error "B1 false-removal source is not a literal list"
                            | _ => error "B1 false-removal source is not a literal list")
                            val head_fact = Conv.rewr_conv (residual_head_rule cid)
                              (Thm.apply drop_false_ct source_ct)
                            val tail_fact = build tail_source_ct tail_ids
                            val tail_rule = if cid = 0 then tail_fact
                              else Thm.combination
                                (Thm.reflexive (Thm.apply cons_ct head_ct)) tail_fact
                          in Thm.transitive head_fact tail_rule end
                    val theorem = build (Thm.cterm_of ctxt (literal_columns ids)) ids
                  in checked_equation "false removal" lhs rhs theorem end)
                val _ = residual_facts := Symtab.update (state_key, theorem)
                  (!residual_facts)
              in (theorem, residual_ids) end)
        end
      fun boolean_rhs label theorem =
        (case Thm.term_of (Thm.rhs_of theorem) of
          Const (name, _) =>
            if name = @{const_name True} then true
            else if name = @{const_name False} then false
            else error ("B1 CID partition " ^ label ^ " is not Boolean")
        | _ => error ("B1 CID partition " ^ label ^ " is not Boolean"))
      fun has_node_equation level ids =
        let
          val state_key = Int.toString level ^ "|" ^
            String.concatWith "," (map Int.toString ids)
        in
          (case Symtab.lookup (!node_facts) state_key of
            SOME theorem => theorem
          | NONE =>
              let
            val lhs = has_node $ number level $ literal_columns ids
                val (root_rule, head_rules, tail) =
                  (case ids of
                    [] => (@{thm comma_semantic_b1_crt_partition_has_node_at.simps(1)}, [], NONE)
                  | cid :: tail =>
                      (@{thm comma_semantic_b1_crt_partition_has_node_at.simps(2)},
                       [step cid] @ @{thms comma_crt_column.case}, SOME tail))
                val unfolded = Conv.rewr_conv (root_rule RS @{thm eq_reflection})
                  (Thm.cterm_of ctxt lhs)
                val head_reduced = time_work_stage 6 (fn () => Simplifier.rewrite
                  (base_context addsimps head_rules)
                  (Thm.rhs_of unfolded))
                val head_rhs = Thm.term_of (Thm.rhs_of head_reduced)
                val theorem =
                  (case (tail, head_rhs) of
                    (SOME tail_ids, rhs) =>
                      if rhs aconv @{term True} then Thm.transitive unfolded head_reduced
                      else
                        let
                          val tail_lhs = has_node $ number level $ literal_columns tail_ids
                          val _ = if rhs aconv tail_lhs then () else error
                            ("B1 CID partition node head did not reduce to True or its tail; rhs=" ^
                             shape 6 rhs)
                          val tail_theorem = has_node_equation level tail_ids
                        in Thm.transitive (Thm.transitive unfolded head_reduced) tail_theorem end
                  | (NONE, rhs) =>
                      if rhs aconv @{term True} orelse rhs aconv @{term False} then
                        Thm.transitive unfolded head_reduced
                      else error "B1 empty node-level test did not reduce")
                val rhs = Thm.term_of (Thm.rhs_of theorem)
                val _ = if (rhs aconv @{term True} orelse rhs aconv @{term False}) andalso
                    Thm.term_of (Thm.lhs_of theorem) aconv lhs andalso clean theorem
                  then () else error
                      ("B1 CID partition node-level check did not reduce: " ^
                       shape 5 rhs)
                val _ = node_facts := Symtab.update (state_key, theorem)
                  (!node_facts)
              in theorem end)
        end
      fun terminal_equation ids =
        let
          val state_key = String.concatWith "," (map Int.toString ids)
          val lhs = HOLogic.mk_eq (literal_columns ids, true_list)
        in
          (case Symtab.lookup (!terminal_facts) state_key of
            SOME theorem => theorem
          | NONE =>
              let
                val rules = @{thms list.inject list.distinct list.size
                  comma_crt_column.inject comma_crt_column.distinct} @
                  (case ids of [cid] => [step cid] | _ => [])
                val theorem = time_work_stage 5 (fn () =>
                  Simplifier.rewrite (base_context addsimps rules) (Thm.cterm_of ctxt lhs))
                val rhs = Thm.term_of (Thm.rhs_of theorem)
                val _ = if (rhs aconv @{term True} orelse rhs aconv @{term False}) andalso
                    clean theorem then () else error
                      "B1 CID partition terminal test did not reduce"
                val _ = terminal_facts := Symtab.update (state_key, theorem)
                  (!terminal_facts)
              in theorem end)
        end
      val period_values = Unsynchronized.ref (Inttab.empty: int Inttab.table)
      fun period level =
        if level < 0 orelse level >= 4 then
          error "B1 CID partition requested a period outside the CRT schedule"
        else case Inttab.lookup (!period_values) level of
          SOME radix => radix
        | NONE =>
            let
              val request = Const (@{const_name comma_crt_period}, natT --> natT) $
                number level
              val theorem = Simplifier.rewrite base_context (Thm.cterm_of ctxt request)
              val radix =
                (case try HOLogic.dest_number (Thm.term_of (Thm.rhs_of theorem)) of
                  SOME (typ, value) => if typ = natT andalso value > 0 andalso value <= 11
                    then value else error "B1 CID partition has an inadmissible CRT radix"
                | NONE => error "B1 CID partition CRT radix did not reduce to a numeral")
              val _ = period_values := Inttab.update (level, radix) (!period_values)
            in radix end
      val cofactor = Const (@{const_name comma_crt_cofactor_or_false},
        natT --> natT --> columnT --> columnT)
      fun vector_key level digit ids = Int.toString level ^ ":" ^
        Int.toString digit ^ "|" ^ String.concatWith "," (map Int.toString ids)
      fun vector_transition level digit ids =
        let
          val _ = if level >= 0 andalso level < 4 then () else error
            "B1 CID partition vector has an invalid CRT level"
          val radix = period level
          val _ = if digit >= 0 andalso digit < radix then () else error
            "B1 CID partition vector digit is outside its radix"
          val _ = if forall (fn cid => cid >= 0 andalso cid < node_count) ids then ()
            else error "B1 CID partition vector contains a foreign CID"
          val cache_key = vector_key level digit ids
        in
          (case Symtab.lookup (!vector_transition_facts) cache_key of
            SOME (target_ids, theorem) =>
              (note_cid_vector_transition true; (target_ids, theorem))
          | NONE =>
              let
                val _ = note_cid_vector_transition false
                val edges = time_work_stage 0 (fn () => map (fn cid =>
                  let
                    val {target_cid, theorem} = cofactor_transition (level, digit, cid)
                    val _ = if target_cid >= 0 andalso target_cid < node_count then ()
                      else error "B1 CID partition transition produced a foreign CID"
                  in (target_cid, theorem) end) ids)
                val _ = if Comma_Proof_Profile.enabled () then
                  vector_edge_calls := !vector_edge_calls + length ids else ()
                val target_ids = map #1 (filter (fn (cid, _) => cid <> 0) edges)
                val source_values = map column_value ids
                val cofactor_function = cofactor $ number level $ number digit
                val map_function = Const (@{const_name map},
                  (columnT --> columnT) --> column_listT --> column_listT) $
                  cofactor_function
                val map_lhs = map_function $ literal_columns ids
                val expanded_values = map (fn value =>
                  cofactor_function $ value) source_values
                val expanded = HOLogic.mk_list columnT expanded_values
                val map_equation = time_work_stage 1 (fn () => Simplifier.rewrite
                  (base_context addsimps @{thms list.map})
                  (Thm.cterm_of ctxt map_lhs))
                val _ = checked_equation "ordered vector map" map_lhs expanded map_equation
                val lhs = drop_false $ expanded
                val rhs = literal_columns target_ids
                val edge_rules = map (fn (target, theorem) =>
                  if target = 0 then Thm.transitive theorem zero_step else theorem) edges
                val false_rules = map nonfalse (distinct (op =) target_ids)
                val reduced = time_work_stage 3 (fn () =>
                  rewrite_equation "ordered vector transition"
                  (base_context addsimps
                    (@{thms comma_semantic_b1_crt_partition_drop_false.simps} @
                     edge_rules @ false_rules)) lhs rhs)
                val map_under_drop = Thm.combination
                  (Thm.reflexive (Thm.cterm_of ctxt drop_false)) map_equation
                val theorem = Thm.transitive map_under_drop reduced
                val theorem = checked_equation "ordered vector transition" 
                  (drop_false $ map_lhs) rhs theorem
                val residual_key = String.concatWith "," (map Int.toString target_ids)
                val residual_lhs = drop_false $ rhs
                val _ = (case Symtab.lookup (!residual_facts) residual_key of
                  SOME old => ignore (checked_equation "cached vector residual"
                    residual_lhs rhs old)
                | NONE =>
                    let
                      val residual = time_work_stage 8 (fn () =>
                        let
                          val idempotent = Conv.rewr_conv
                            (@{thm comma_semantic_b1_crt_partition_drop_false_idempotent} RS
                              @{thm eq_reflection})
                            (Thm.apply drop_false_ct (Thm.lhs_of theorem))
                          val lifted = Thm.combination
                            (Thm.reflexive drop_false_ct)
                            (Thm.symmetric theorem)
                          val candidate = Thm.transitive
                            (Thm.transitive lifted idempotent) theorem
                        in checked_equation "vector residual" residual_lhs rhs candidate end)
                      val _ = residual_facts := Symtab.update
                        (residual_key, residual) (!residual_facts)
                      val _ = residual_transition_derivations :=
                        !residual_transition_derivations + 1
                    in () end)
                val _ = vector_transition_facts := Symtab.update
                  (cache_key, (target_ids, theorem)) (!vector_transition_facts)
                val _ = vector_transition_fact_count := !vector_transition_fact_count + 1
              in (target_ids, theorem) end)
        end
      fun prove_state levels ids =
        let
          val _ = state_requests := !state_requests + 1
          val ordinal = !state_requests
          val allowed_suffixes = [[], [3], [2, 3], [1, 2, 3], [0, 1, 2, 3]]
          val _ = if member (op =) allowed_suffixes levels then ()
            else error "B1 CID partition state has a noncanonical CRT suffix"
          val _ = if forall (fn cid => cid >= 0 andalso cid < node_count) ids
            then () else error "B1 CID partition state contains a foreign CID"
          val state_key = key levels ids
        in
          (case Symtab.lookup (!state_facts) state_key of
            SOME theorem =>
              (note_cid_state true; profile_state "hit" ordinal levels ids; theorem)
          | NONE =>
              let
                val _ = note_cid_state false
                val _ = profile_state "new" ordinal levels ids
                val request = checker_const $
                  HOLogic.mk_list natT (map number levels) $ literal_columns ids
                val (residual, residual_ids) = residual_equation ids
                val terminal = terminal_equation residual_ids
                val terminal_value = boolean_rhs "terminal test" terminal
                val tail_levels = (case levels of [] => [] | _ :: rest => rest)
                val node = if null levels orelse terminal_value then NONE
                  else SOME (has_node_equation (hd levels) residual_ids)
                val active_node = Option.map
                  (boolean_rhs "node test") node
                val child_equations =
                  (case (levels, active_node) of
                    (_ :: _, SOME true) =>
                      let
                        val level = hd levels
                        val radix = period level
                        fun child digit =
                          let
                            val (child_ids, vector_fact) =
                              vector_transition level digit residual_ids
                            val child_fact = prove_state tail_levels child_ids
                          in [vector_fact, child_fact] end
                        val all_rules = maps child (0 upto (radix - 1))
                      in all_rules end
                  | (_ :: _, SOME false) =>
                      let val tail_fact = prove_state tail_levels residual_ids
                      in [tail_fact] end
                  | _ => [])
                val node_rule = (case node of SOME theorem => [theorem] | NONE => [])
                val rules = @{thms list_all_Nil_iff list_all_Cons_iff Let_def
                  comma_crt_period_def upt_0 upt_Suc upt_rec upt_rec_numeral} @
                  [residual, terminal] @ node_rule @ child_equations
                val root_rule = if null levels
                  then @{thm comma_semantic_b1_crt_partition_cofactor_checked.simps(1)}
                  else @{thm comma_semantic_b1_crt_partition_cofactor_checked.simps(2)}
                val unfolded = Conv.rewr_conv (root_rule RS @{thm eq_reflection})
                  (Thm.cterm_of ctxt request)
                val rewrite_started = Time.now ()
                val reduced = time_work_stage 7 (fn () =>
                  Simplifier.rewrite (base_context addsimps rules) (Thm.rhs_of unfolded))
                val rewrite_elapsed = Time.toMilliseconds
                  (Time.- (Time.now (), rewrite_started))
                val _ = if rewrite_elapsed >= 100 then
                  profile_event ("slow_state_rewrite level=" ^ level_summary levels ^
                    " levels=" ^ Int.toString (length levels) ^
                    " ids=" ^ Int.toString (length ids) ^
                    " elapsed_ms=" ^ LargeInt.toString rewrite_elapsed)
                  else ()
                val theorem = Thm.transitive unfolded reduced
                val expected_rhs = @{term True}
                val checked = checked_equation "state" request expected_rhs theorem
                val _ = state_facts := Symtab.update (state_key, checked)
                  (!state_facts)
                val _ = state_fact_count := !state_fact_count + 1
              in checked end)
        end
    in
      {prove_state = prove_state, number = number,
       literal_columns = literal_columns, prove_transition = vector_transition,
       prove_residual = residual_equation,
       vector_work_summary = vector_work_summary, check_equation = checked_equation,
       residual_head_counts = fn () => (!residual_head_builds, !residual_head_hits),
       residual_work_counts = fn () =>
         (!residual_fallback_scans, !residual_transition_derivations),
       state_counts = fn () => (!state_fact_count,
         !vector_transition_fact_count, Symtab.size (!residual_facts),
         Inttab.size (!nonfalse_facts))}
    end
  fun make_template_partition_checker ctxt
      {column_value, step, cofactor_transition, node_count}
      {note_cid_state, note_cid_vector_transition} =
    let
      val natT = @{typ nat}
      val columnT = @{typ comma_crt_column}
      val rowT = HOLogic.listT columnT
      val boolT = @{typ bool}
      val thy = Proof_Context.theory_of ctxt
      val column_values = make_template_state_prover ctxt
        {column_value = column_value, step = step,
         cofactor_transition = cofactor_transition, node_count = node_count}
        {note_cid_state = note_cid_state,
         note_cid_vector_transition = note_cid_vector_transition}
      val prove_state = #prove_state column_values
      val number = #number column_values
      val check_equation = #check_equation column_values
      val table_name = Sign.intern_const thy "comma_semantic_b1_crt_columns"
      val count_name = Sign.intern_const thy "comma_semantic_b1_crt_column_count"
      val table = Const (table_name, rowT)
      val count = Const (count_name, natT)
      val table_definition = Local_Defs.meta_rewrite_rule ctxt
        (Proof_Context.get_thm ctxt "comma_semantic_b1_crt_columns_def")
      val count_definition = Local_Defs.meta_rewrite_rule ctxt
        (Proof_Context.get_thm ctxt "comma_semantic_b1_crt_column_count_def")
      val table_body = Thm.term_of (Thm.rhs_of table_definition)
      val count_value = Thm.term_of (Thm.rhs_of count_definition)
      val (dag, count_arg) = (case strip_comb table_body of
          (Const (name, _), [dag, count_arg]) =>
            if name = @{const_name comma_semantic_b1_crt_columns_for}
            then (dag, count_arg)
            else error "B1 template table is not a checked DAG projection"
        | _ => error "B1 template table definition is malformed")
      val declared_count_matches =
        (case try HOLogic.dest_number count_value of
          SOME (typ, value) => typ = natT andalso value = node_count
        | NONE => false)
      val _ = if Thm.term_of (Thm.lhs_of table_definition) aconv table andalso
          Thm.term_of (Thm.lhs_of count_definition) aconv count andalso
          count_arg aconv count andalso
          fastype_of dag = @{typ comma_semantic_b1_crt_column_dag} andalso
          declared_count_matches andalso
          fastype_of (column_value 0) = columnT
        then () else error "B1 template table extent or DAG does not match the checked catalogue"
      val (column_at_head, column_at_args) = strip_comb (column_value 0)
      val _ = (case (column_at_head, column_at_args) of
          (Const (name, _), [column_dag, zero]) =>
            if name = @{const_name comma_semantic_b1_crt_column_at} andalso
                column_dag aconv dag andalso
                (case try HOLogic.dest_number zero of
                  SOME (typ, value) => typ = natT andalso value = 0
                | NONE => false)
            then () else error "B1 column-value callback changed the fixed DAG"
        | _ => error "B1 column-value callback returned another term")
      fun dest_nat_list label term =
        (case try HOLogic.dest_list term of
          SOME values => map (fn value =>
            (case try HOLogic.dest_number value of
              SOME (typ, number) => if typ = natT andalso number >= 0 then number
                else error ("B1 partition " ^ label ^ " has an invalid natural")
            | NONE => error ("B1 partition " ^ label ^ " is not a numeral"))) values
        | NONE => error ("B1 partition " ^ label ^
            " is not a literal list; rhs=" ^ shape 8 term))
      fun prove_checker {context, checker_ct, ids_row, row, resolved_fact} =
        let
          val _ = profile_stage "row_projection" "start" NONE
          val row_started = Time.now ()
          val checker_request = Thm.term_of checker_ct
          val (checker_head, checker_arguments) = strip_comb checker_request
          val (levels_term, row_term) =
            (case (checker_head, checker_arguments) of
              (Const (name, _), [levels, columns]) =>
                if name = @{const_name comma_semantic_b1_crt_partition_cofactor_checked} andalso
                    columns aconv row
                then (levels, columns)
                else error "B1 template partition checker request changed its exact row"
            | _ => error "B1 template partition checker request is malformed")
          val ids_equation = Simplifier.rewrite context (Thm.cterm_of ctxt ids_row)
          val _ = check_equation "selected IDs" ids_row
            (Thm.term_of (Thm.rhs_of ids_equation)) ids_equation
          val ids = dest_nat_list "selected column IDs"
            (Thm.term_of (Thm.rhs_of ids_equation))
          val _ = if Thm.term_of (Thm.rhs_of ids_equation) aconv
                  HOLogic.mk_list natT (map (HOLogic.mk_number natT) ids) andalso
              Thm.term_of (Thm.lhs_of ids_equation) aconv ids_row andalso
              Thm.nprems_of ids_equation = 0 andalso
              null (Thm.hyps_of ids_equation) andalso null (Thm.tpairs_of ids_equation) andalso
              forall (fn cid => cid < node_count) ids then ()
            else error "B1 selected template row has a foreign column ID"
          val selected_ids = HOLogic.mk_list natT (map (HOLogic.mk_number natT) ids)
          val column_at = Const (@{const_name comma_semantic_b1_crt_column_at},
            @{typ "comma_semantic_b1_crt_column_dag"} --> natT --> columnT) $ dag
          val map_column_at = Const (@{const_name map},
            (natT --> columnT) --> HOLogic.listT natT --> rowT) $ column_at
          val selected_map = map_column_at $ selected_ids
          val selected_columns = HOLogic.mk_list columnT (map column_value ids)
          val selected_equation = Simplifier.rewrite
            (put_simpset HOL_basic_ss ctxt addsimps @{thms list.map})
            (Thm.cterm_of ctxt selected_map)
          val _ = check_equation "catalogue row projection" selected_map
            selected_columns selected_equation
          val table_object = table_definition RS @{thm meta_eq_to_obj_eq}
          val resolved_columns =
            @{thm comma_semantic_b1_crt_column_ids_resolve_columns_for}
              OF [table_object, resolved_fact]
          val resolved_columns_meta = resolved_columns RS @{thm eq_reflection}
          val ids_under_map = Thm.combination
            (Thm.reflexive (Thm.cterm_of ctxt map_column_at)) ids_equation
          val row_equation = Thm.transitive
            (Thm.transitive resolved_columns_meta ids_under_map)
            selected_equation
          val _ = check_equation "resolved row" row_term selected_columns row_equation
          val row_elapsed = Time.toMilliseconds (Time.- (Time.now (), row_started))
          val _ = profile_stage "row_projection" "done" (SOME row_elapsed)
          val _ = profile_stage "levels" "start" NONE
          val levels_started = Time.now ()
          val levels_base_context = Comma_Entry_Arithmetic.natural_context ctxt addsimps
            @{thms upt_rec_numeral}
          val levels_context = the_default levels_base_context
            (Comma_Semantic_B1_CRT_Operation_Conversion.small_closed_upt_context
              levels_base_context levels_term)
              addsimps @{thms upt_0 upt_Suc upt_rec upt_rec_numeral}
          val levels_equation = Simplifier.rewrite levels_context
            (Thm.cterm_of ctxt levels_term)
          val levels = dest_nat_list "checker levels"
            (Thm.term_of (Thm.rhs_of levels_equation))
          val literal_levels = HOLogic.mk_list natT (map number levels)
          val _ = check_equation "checker levels" levels_term literal_levels levels_equation
          val _ = if levels = [0, 1, 2, 3] then ()
            else error "B1 template partition checker has another CRT level schedule"
          val levels_elapsed = Time.toMilliseconds (Time.- (Time.now (), levels_started))
          val _ = profile_stage "levels" "done" (SOME levels_elapsed)
          val checker_const = Const
            (@{const_name comma_semantic_b1_crt_partition_cofactor_checked},
              HOLogic.listT natT --> rowT --> boolT)
          val head_ct = Thm.cterm_of ctxt checker_const
          val prefix_equation = Thm.combination
            (Thm.reflexive head_ct) levels_equation
          val request_equation = Thm.combination prefix_equation row_equation
          val _ = profile_message (fn () => "B1 partition stage=state phase=start levels=" ^
            Int.toString (length levels) ^ " ids=" ^ Int.toString (length ids))
          val state_started = Time.now ()
          val state_equation = prove_state levels ids
          val state_elapsed = Time.toMilliseconds (Time.- (Time.now (), state_started))
          val _ = profile_message (fn () =>
            let val (states, vectors, _, _) = #state_counts column_values ()
            in "B1 partition stage=state phase=done elapsed_ms=" ^
              LargeInt.toString state_elapsed ^ " states=" ^ Int.toString states ^
              " vectors=" ^ Int.toString vectors ^
              (#vector_work_summary column_values) () end)
          val equation = Thm.transitive request_equation state_equation
          val _ = check_equation "template checker" checker_request @{term True} equation
        in equation end
    in {prove_checker = prove_checker, prove_transition = #prove_transition column_values,
        state_counts = #state_counts column_values} end
  fun make_template_partition_session ctxt
      {column_value, step, cofactor_transition, node_count} =
    let
      val profile = make_template_partition_profile ()
      val checker = make_template_partition_checker ctxt
        {column_value = column_value, step = step,
         cofactor_transition = cofactor_transition, node_count = node_count}
        {note_cid_state = #note_cid_state profile,
         note_cid_vector_transition = #note_cid_vector_transition profile}
    in {profile = profile, prove_checker = #prove_checker checker} end
  fun make_partition_cofactor_canonicalizer context
      {note_shape_check, note_shape_cache_hit} =
    let
      val normal_columns = Unsynchronized.ref
        (Termtab.empty: bool Termtab.table)
      val closed = Comma_Selected_List_Conversion.closed
      fun natural_literal term =
        (case try HOLogic.dest_number term of
          SOME (typ, number) => typ = @{typ nat} andalso number >= 0
        | NONE => false)
      fun canonical_entry entry =
        (case Termtab.lookup (!normal_columns) entry of
          SOME result => (note_shape_cache_hit (); result)
        | NONE =>
            let
              val _ = note_shape_check ()
              val result =
                (case strip_comb entry of
                  (Const (name, _), [payload]) =>
                    name = @{const_name Comma_CRT_Bool} andalso
                      (payload aconv @{term True} orelse payload aconv @{term False})
                | (Const (name, _), [first, second]) =>
                    if name = @{const_name Comma_CRT_Node} then
                      natural_literal first andalso
                        (case try HOLogic.dest_list second of
                          SOME row => List.all canonical_entry row
                        | NONE => false)
                    else if name = @{const_name comma_semantic_b1_crt_column_at}
                    then closed first andalso natural_literal second
                    else false
                | _ => false)
              val _ = normal_columns := Termtab.update (entry, result)
                (!normal_columns)
            in result end)
      fun is_canonical_levels term =
        (case try HOLogic.dest_list term of
          SOME levels => List.all natural_literal levels
        | NONE => false)
      fun is_canonical_columns term =
        (case try HOLogic.dest_list term of
          SOME columns => List.all canonical_entry columns
        | NONE => false)
      fun canonicalize cterm =
        let val request = Thm.term_of cterm
        in
          (case strip_comb request of
            (Const (name, _), [levels, columns]) =>
              if name <> @{const_name comma_semantic_b1_crt_partition_cofactor_checked}
              then Thm.reflexive cterm
              else if is_canonical_levels levels andalso is_canonical_columns columns
              then Thm.reflexive cterm
              else
                let
                  (* Congruence simprocs see this root before descending. Normalize
                     raw recipes once, then key the exact ordered residual vector.
                     The constructor cache validates each MDD subterm at most once;
                     literal False remains valid input and is never discarded here. *)
                  val state_context = context addsimps
                    @{thms comma_semantic_b1_crt_partition_drop_false.simps}
                  val levels_context =
                    if is_canonical_levels levels then state_context
                    else the_default state_context
                      (Comma_Semantic_B1_CRT_Operation_Conversion.small_closed_upt_context
                        state_context levels)
                  val (head_levels_ct, columns_ct) = Thm.dest_comb cterm
                  val (head_ct, levels_ct) = Thm.dest_comb head_levels_ct
                  val levels_eq =
                    if is_canonical_levels levels then Thm.reflexive levels_ct
                    else Simplifier.rewrite levels_context levels_ct
                  val columns_eq =
                    if is_canonical_columns columns then Thm.reflexive columns_ct
                    else Simplifier.rewrite state_context columns_ct
                  val head_eq = Thm.reflexive head_ct
                  val prefix_eq = Thm.combination head_eq levels_eq
                  val normalized = Thm.combination prefix_eq columns_eq
                  val normalized_levels = Thm.term_of (Thm.rhs_of levels_eq)
                  val normalized_columns = Thm.term_of (Thm.rhs_of columns_eq)
                  (* Literal levels and canonical columns establish that this
                     constant-headed request is closed without a second traversal. *)
                  val _ = if Thm.term_of (Thm.lhs_of normalized) aconv request
                      andalso is_canonical_levels normalized_levels andalso
                        is_canonical_columns normalized_columns
                    then () else error
                      ("B1 partition cofactor state did not canonicalize to closed ordered lists" ^
                       " levels=" ^ shape 3 normalized_levels ^
                       " columns=" ^ shape 3 normalized_columns ^
                       " levels_literal=" ^ Bool.toString
                         (is_canonical_levels normalized_levels) ^
                       " columns_literal=" ^ Bool.toString
                         (is_canonical_columns normalized_columns))
                in normalized end
            | _ => error "B1 partition cofactor state has a malformed request")
        end
    in canonicalize end
end
