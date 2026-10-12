(* Proof-producing labelled zipper for the concrete B1 column catalogue. *)
structure Comma_Semantic_B1_Labelled_Zip =
struct
  val cache_limit = 8192
  structure State_Key = Table(type key = int * int list
    val ord = prod_ord int_ord (list_ord int_ord))

  fun argument_at index conversion cterm =
    if index = 0 then Conv.arg_conv conversion cterm
    else Conv.fun_conv (argument_at (index - 1) conversion) cterm

  fun make ctxt
      {column_value: int -> term,
       step: int -> thm,
       cofactor_transition: int * int * int -> {target_cid: int, theorem: thm},
       cofactor_node_level: int -> int option,
       try_evaluate: Proof.context -> cterm -> thm option,
       node_count: int,
       note_cid_state: bool -> unit,
       note_cid_vector_transition: bool -> unit} =
    let
      val natT = @{typ nat}
      val columnT = @{typ comma_crt_column}
      val column_listT = HOLogic.listT columnT
      val nat_listT = HOLogic.listT natT
      val boolT = @{typ bool}
      val witness_name =
        @{const_name comma_semantic_b1_crt_partition_witness}
      val witness_const = Const (witness_name,
        natT --> column_listT --> boolT)
      val checker_const = Const
        (@{const_name comma_semantic_b1_crt_partition_cofactor_checked},
          nat_listT --> column_listT --> boolT)
      val cofactor_const = Const (@{const_name comma_crt_cofactor_or_false},
        natT --> natT --> columnT --> columnT)
      val base_context = Comma_Entry_Arithmetic.natural_context ctxt
      val indexed_labels = Comma_Semantic_B1_Indexed_Labels.make ctxt
        {column_value = column_value, step = step, node_count = node_count,
         cache_limit = cache_limit}
      val compress_indexed_labels = #compress indexed_labels
      val indexed_label_proof_counts = #proof_counts indexed_labels
      val indexed_label_occurrence_counts = #occurrence_counts indexed_labels
      val indexed_label_cache_hits = #cache_hits indexed_labels
      val indexed_label_stats = #stats indexed_labels
      val node_presence_prover =
        Comma_Semantic_B1_Partition_Support.make_node_presence_prover ctxt
          {column_value = column_value, step = step, base_context = base_context}
      val node_presence_equation = #prove node_presence_prover
      val node_presence_counts = #counts node_presence_prover
      val node_presence_stats = #stats node_presence_prover
      val terminal_list_rules =
        @{thms list.map list.size nth_Cons' upt_rec upt_rec_numeral if_weak_cong}
      val dag =
        (case strip_comb (column_value 0) of
          (Const (name, _), [owner, index]) =>
            if name = @{const_name comma_semantic_b1_crt_column_at} andalso
                (case try HOLogic.dest_number index of
                  SOME (typ, 0) => typ = natT
                | _ => false)
            then owner
            else error "B1 labelled zipper received a noncanonical column root"
        | _ => error "B1 labelled zipper received a malformed column root")
      val state_cache = Unsynchronized.ref (State_Key.empty:
        (int list * thm) State_Key.table)
      val state_order_cache = Unsynchronized.ref (State_Key.empty:
        thm State_Key.table)
      val state_builds = Unsynchronized.ref 0
      val state_hits = Unsynchronized.ref 0
      val state_refusals = Unsynchronized.ref 0
      val state_owner_reorder_hits = Unsynchronized.ref 0
      val state_order_cache_hits = Unsynchronized.ref 0
      val state_order_cache_refusals = Unsynchronized.ref 0
      val state_sort_elapsed = Unsynchronized.ref Time.zeroTime
      val state_sort_calls = Unsynchronized.ref 0
      val vector_builds = Unsynchronized.ref 0
      val transition_edges = Unsynchronized.ref 0
      val node_metadata_reads = Unsynchronized.ref 0
      val admission_requests = Unsynchronized.ref 0
      val admission_header_uses = Unsynchronized.ref 0
      val state_column_occurrences = Unsynchronized.ref 0
      val vector_column_occurrences = Unsynchronized.ref 0
      val distinct_vector_cids = Unsynchronized.ref 0
      val maximum_state_width = Unsynchronized.ref 0
      val state_key_input_width = Unsynchronized.ref 0
      val warm_owner_fixture_runs = Unsynchronized.ref 0
      val warm_owner_fixture_checked = Unsynchronized.ref false
      (* A root replay is intentionally order-preserving now.  Keep the first
         actual non-root transport witness so the warm fixture still checks
         that the exact occurrence permutation certificate is reused for a
         child state, including owner-cache hits. *)
      val child_permutation_fixture =
        Unsynchronized.ref (NONE:
          (int * int list * int list * thm) option)
      val child_permutation_fixture_checked = Unsynchronized.ref false
      val child_permutation_fixture_runs = Unsynchronized.ref 0
      val terminal_ms = Unsynchronized.ref (0: LargeInt.int)
      val node_presence_ms = Unsynchronized.ref (0: LargeInt.int)
      val admission_ms = Unsynchronized.ref (0: LargeInt.int)
      val vector_ms = Unsynchronized.ref (0: LargeInt.int)
      val childfold_ms = Unsynchronized.ref (0: LargeInt.int)
      val compression_ms = Unsynchronized.ref (0: LargeInt.int)
      val lift_ms = Unsynchronized.ref (0: LargeInt.int)
      val lift_applications = Unsynchronized.ref 0

      fun number n = HOLogic.mk_number natT n
      fun canonical_key_ids level ids =
        let
          val result = if level = 0 then ids
            else
              let
                val started = Time.now ()
                val sorted = sort int_ord ids
                val duration = Time.- (Time.now (), started)
                val _ = state_sort_elapsed := Time.+ (!state_sort_elapsed, duration)
                val _ = state_sort_calls := !state_sort_calls + 1
              in sorted end
        in result end
      val successor_equations = Vector.tabulate (4, fn n =>
        Simplifier.rewrite base_context
          (Thm.cterm_of ctxt (HOLogic.mk_Suc (number n))))
      fun literal_columns ids = HOLogic.mk_list columnT (map column_value ids)
      val permutation_cache = Comma_Semantic_B1_Permutation_Cache.make ctxt
        {dag = dag, number = number, literal_columns = literal_columns,
         witness_const = witness_const, cache_limit = cache_limit}
      val raw_transport_witness = #transport permutation_cache
      val permutation_cache_stats = #stats permutation_cache
      val permutation_certificate_builds = #certificate_builds permutation_cache
      val permutation_transport_count = #transports permutation_cache
      fun measured elapsed work =
        let
          val started = Time.now ()
          val result = Exn.capture work ()
          val duration = Time.toMilliseconds (Time.- (Time.now (), started))
          val _ = elapsed := LargeInt.+ (!elapsed, duration)
        in Exn.release result end
      fun list_all_term predicate items =
        Const (@{const_name list_all}, fastype_of predicate -->
          fastype_of items --> boolT) $ predicate $ items
      fun closed theorem = Thm.nprems_of theorem = 0 andalso
        null (Thm.hyps_of theorem) andalso null (Thm.tpairs_of theorem)
      fun check_theorem label proposition theorem =
        if Thm.prop_of theorem aconv proposition andalso closed theorem
        then theorem
        else error ("B1 labelled zipper " ^ label ^
          " theorem changed authority or is not kernel-closed")
      fun transport_state_witness level source_ids target_ids theorem =
        let
          val transported = raw_transport_witness level source_ids target_ids theorem
          val _ = if level > 0 andalso source_ids <> target_ids then
            (case !child_permutation_fixture of
              NONE =>
                let
                  val source_proposition = HOLogic.mk_Trueprop
                    (witness_const $ number level $
                      literal_columns source_ids)
                  val _ = check_theorem
                    "captured child permutation source" source_proposition theorem
                in child_permutation_fixture :=
                  SOME (level, source_ids, target_ids, theorem) end
            | SOME _ => ())
          else ()
        in transported end
      fun check_equation label lhs rhs theorem =
        if Thm.term_of (Thm.lhs_of theorem) aconv lhs andalso
            Thm.term_of (Thm.rhs_of theorem) aconv rhs andalso closed theorem
        then theorem
        else error ("B1 labelled zipper " ^ label ^ " equation changed: " ^
          Syntax.string_of_term ctxt (Thm.term_of (Thm.rhs_of theorem)) ^
          " expected " ^ Syntax.string_of_term ctxt rhs)
      fun proposition_equality equation = Thm.combination
        (Thm.reflexive (Thm.cterm_of ctxt @{term Trueprop})) equation
      fun step_rules ids = map step (distinct (op =) ids)
      fun proposition_from_true_equation theorem =
        let
          val equation = Thm.combination
            (Thm.reflexive (Thm.cterm_of ctxt @{term Trueprop})) theorem
        in Thm.equal_elim (Thm.symmetric equation) @{thm TrueI} end
      val list_all_cons = @{thm list_all_Cons_iff} RS @{thm eq_reflection}
      val list_all_nil = @{thm list_all_Nil_iff} RS @{thm eq_reflection}
      fun fold_list_all label predicate elementT element_of elements fact_for =
        let
          val elements_with_terms = map (fn element => (element, element_of element)) elements
          val items = HOLogic.mk_list elementT (map #2 elements_with_terms)
          val request = list_all_term predicate items
          val request_ct = Thm.cterm_of ctxt request
          val (list_all_function_ct, source_ct) = Thm.dest_comb request_ct
          fun fold [] source =
                (case Thm.term_of source of
                  Const (name, _) => if name = @{const_name Nil} then
                    let
                      val equation = Conv.rewr_conv list_all_nil
                        (Thm.apply list_all_function_ct source)
                    in proposition_from_true_equation equation end
                    else error "B1 list-all fold ended before its literal list"
                | _ => error "B1 list-all fold ended before its literal list")
            | fold ((element, element_term) :: rest) source =
                let
                  val (cons_head_ct, tail_ct) = Thm.dest_comb source
                  val (cons_ct, head_ct) = Thm.dest_comb cons_head_ct
                  val _ = (case Thm.term_of cons_ct of
                    Const (name, _) => if name = @{const_name Cons} then ()
                      else error "B1 list-all fold encountered a non-cons source"
                  | _ => error "B1 list-all fold encountered a malformed source")
                  val _ = if Thm.term_of head_ct aconv element_term then ()
                    else error "B1 list-all fold changed element order"
                  val tail_fact = fold rest tail_ct
                  val head_fact = fact_for element
                  val head_proposition = HOLogic.mk_Trueprop
                    (predicate $ element_term)
                  val head_fact = check_theorem (label ^ " atom")
                    head_proposition head_fact
                  val equation = Conv.rewr_conv list_all_cons
                    (Thm.apply list_all_function_ct source)
                  val conjunction = @{thm conjI} OF [head_fact, tail_fact]
                  val theorem = Thm.equal_elim
                    (Thm.symmetric (proposition_equality equation)) conjunction
                in theorem end
          val theorem = fold elements_with_terms source_ct
          val expected = HOLogic.mk_Trueprop request
          val _ = check_theorem label expected theorem
        in (items, theorem) end
      fun negated_proposition_from_false predicate theorem =
        let
          val negated = Thm.combination
            (Thm.reflexive (Thm.cterm_of ctxt @{term Not})) theorem
          val normalized = Thm.transitive negated (Simplifier.rewrite base_context
            (Thm.rhs_of negated))
          val equation = Thm.combination
            (Thm.reflexive (Thm.cterm_of ctxt @{term Trueprop})) normalized
          val proposition = HOLogic.mk_Trueprop (HOLogic.mk_not predicate)
          val checked = Thm.equal_elim (Thm.symmetric equation) @{thm TrueI}
        in check_theorem "negative structural proposition" proposition checked end
      fun admission_fact lower cid =
        let
          val _ = if cid >= 0 andalso cid < node_count then ()
            else error "B1 labelled zipper admission requested a foreign CID"
          val column = column_value cid
          val predicate = Const (@{const_name comma_crt_admitted},
            natT --> columnT --> boolT) $ number lower $ column
          val proposition = HOLogic.mk_Trueprop predicate
          val _ = admission_requests := !admission_requests + 1
        in
          if lower = 0 then
            let
              val theorem = Drule.infer_instantiate ctxt
                [(("dag", 0), Thm.cterm_of ctxt dag),
                 (("cid", 0), Thm.cterm_of ctxt (number cid))]
                @{thm comma_semantic_b1_crt_column_at_admitted}
            in check_theorem "source-column admission" proposition theorem end
          else
            let
              val request = Thm.cterm_of ctxt predicate
              val equation =
                (case try_evaluate ctxt request of
                  SOME theorem => theorem
                | NONE => error "B1 column owner could not certify an admitted header")
              val _ = check_equation "column-owner admission header"
                predicate @{term True} equation
              val theorem = proposition_from_true_equation equation
              val _ = admission_header_uses := !admission_header_uses + 1
            in check_theorem "column-owner admission" proposition theorem end
        end
      fun admitted_vector_impl level ids =
        let
          val predicate = Const (@{const_name comma_crt_admitted},
            natT --> columnT --> boolT) $ number level
          val unique_ids = distinct (op =) ids
          val facts = map (admission_fact level) unique_ids
          val fact_table = fold (fn (cid, theorem) =>
            Inttab.update (cid, theorem)) (ListPair.zip (unique_ids, facts)) Inttab.empty
          val (columns, theorem) = fold_list_all "ordered vector admission"
            predicate columnT column_value ids (fn cid =>
              (case Inttab.lookup fact_table cid of
                SOME fact => fact
              | NONE => error "B1 admission fold lost an atom theorem"))
          val proposition = HOLogic.mk_Trueprop (list_all_term predicate columns)
        in check_theorem "ordered vector admission" proposition theorem end
      fun admitted_vector level ids = measured admission_ms (fn () =>
        admitted_vector_impl level ids)
      val vector_cache_helper = Comma_Semantic_B1_Vector_Suffix_Cache.make ctxt
        {columnT = columnT, column_listT = column_listT,
         cofactor_const = cofactor_const, number = number,
         column_value = column_value, dag = dag, node_count = node_count,
         cofactor_transition = cofactor_transition, cache_limit = cache_limit,
         check_equation = check_equation,
         note_transition_edge = fn () =>
           transition_edges := !transition_edges + 1}
      val prove_vector_map = #prove vector_cache_helper
      val check_vector_alias_fixture = #check_alias_fixture vector_cache_helper
      val vector_cache_stats = #stats vector_cache_helper
      fun node_presence_impl level ids =
        let
          val metadata = map (fn cid => (cid, cofactor_node_level cid))
            (distinct (op =) ids)
          val _ = node_metadata_reads := !node_metadata_reads + length metadata
          val _ = List.app (fn (_, maybe_level) =>
            case maybe_level of SOME old_level =>
              if old_level < level then error
                "B1 labelled zipper encountered a node before its CRT level"
              else ()
            | NONE => ()) metadata
          val expected = List.exists (fn (_, maybe_level) => maybe_level = SOME level)
            metadata
          val columns = literal_columns ids
          val request = Const
            (@{const_name comma_semantic_b1_crt_partition_has_node_at},
              natT --> column_listT --> boolT) $ number level $ columns
          val theorem = node_presence_equation level ids
          val rhs = Thm.term_of (Thm.rhs_of theorem)
          val actual = if rhs aconv @{term True} then true
            else if rhs aconv @{term False} then false
            else error "B1 labelled zipper node test did not normalize"
          val _ = if actual = expected then ()
            else error "B1 labelled zipper node metadata disagrees with its theorem"
          val _ = check_equation "node-presence" request
            (if expected then @{term True} else @{term False}) theorem
          val fact = if expected then proposition_from_true_equation theorem
            else negated_proposition_from_false request theorem
        in (fact, expected) end
      fun node_presence level ids = measured node_presence_ms (fn () =>
        node_presence_impl level ids)
      fun evaluate_radix level =
        let
          val request = @{term comma_crt_period} $ number level
          val equation = Simplifier.rewrite
            (base_context addsimps @{thms comma_crt_period_def nth_Cons'})
            (Thm.cterm_of ctxt request)
        in
          (case try HOLogic.dest_number (Thm.term_of (Thm.rhs_of equation)) of
            SOME (typ, value) =>
              if typ = natT andalso value > 0 andalso value <= 11 then (value, equation)
              else error "B1 labelled zipper CRT radix is invalid"
          | NONE => error "B1 labelled zipper CRT radix is symbolic")
        end
      val radix_facts = Vector.tabulate (4, evaluate_radix)
      fun radix level =
        if level >= 0 andalso level < 4 then #1 (Vector.sub (radix_facts, level))
        else error "B1 labelled zipper requested a radix outside the fixed schedule"
      val level_bounds = Vector.tabulate (4, fn level =>
        Goal.prove ctxt [] [] (HOLogic.mk_Trueprop
          (HOLogic.mk_binrel @{const_name less} (number level, number 4)))
          (fn {context, ...} => simp_tac base_context 1))
      val child_ranges = Vector.tabulate (4, fn level =>
        Simplifier.rewrite (base_context addsimps
          @{thms comma_crt_period_def upt_0 upt_Suc upt_rec upt_rec_numeral nth_Cons'})
          (Thm.cterm_of ctxt (Const (@{const_name upt},
            natT --> natT --> nat_listT) $ number 0 $
              (@{term comma_crt_period} $ number level))))
      fun one_hot ids =
        let
          val _ = if forall (fn cid => cid = 0 orelse cid = 1) ids then ()
            else error "B1 labelled zipper reached a non-Boolean terminal CID"
          val selected = map_index (fn (index, cid) => if cid = 1 then SOME index else NONE) ids
            |> map_filter I
          val _ = if length selected = 1 then () else error
            "B1 labelled zipper terminal row is not exactly one-hot"
        in hd selected end
      fun build level raw_ids =
        let
          val _ = if level >= 0 andalso level <= 4 then ()
            else error "B1 labelled zipper level is outside the fixed CRT schedule"
          val _ = if raw_ids <> [] andalso forall
              (fn cid => cid >= 0 andalso cid < node_count) raw_ids then ()
            else error "B1 labelled zipper raw state is empty or contains a foreign CID"
          val (_, compact_ids, compact_columns, embedded) =
            measured compression_ms (fn () => compress_indexed_labels raw_ids)
          val raw_columns = literal_columns raw_ids
          val compact_theorem = build_compact level compact_ids
          val compact_proposition = HOLogic.mk_Trueprop
            (witness_const $ number level $ compact_columns)
          val compact_theorem = check_theorem "compact state witness"
            compact_proposition compact_theorem
          val _ = lift_applications := !lift_applications + 1
          val theorem = measured lift_ms (fn () =>
            let
              val lifted = @{thm comma_semantic_b1_crt_partition_witness_lift}
                OF [compact_theorem, embedded]
              val raw_proposition = HOLogic.mk_Trueprop
                (witness_const $ number level $ raw_columns)
            in check_theorem "lifted raw state witness"
              raw_proposition lifted end)
        in theorem end
      and build_compact level ids =
        let
          val _ = if level >= 0 andalso level <= 4 then ()
            else error "B1 labelled zipper level is outside the fixed CRT schedule"
          val _ = if forall (fn cid => cid >= 0 andalso cid < node_count) ids then ()
            else error "B1 labelled zipper state contains a foreign CID"
          val _ = if forall (fn cid => cid <> 0) ids then ()
            else error "B1 compact state retained the false CID"
          val key_ids = canonical_key_ids level ids
          val state_key = (level, key_ids)
          val requested_key = (level, ids)
          val _ = state_key_input_width := !state_key_input_width + length ids
          fun cache_requested_order source_ids theorem =
            if ids = source_ids then theorem
            else if State_Key.size (!state_order_cache) < cache_limit then
              (state_order_cache := State_Key.update (requested_key, theorem)
                (!state_order_cache); theorem)
            else (state_order_cache_refusals :=
                !state_order_cache_refusals + 1; theorem)
          fun record_hit () =
            (state_hits := !state_hits + 1; note_cid_state true)
          fun requested_cache () =
            (case State_Key.lookup (!state_order_cache) requested_key of
              SOME theorem =>
                let
                  val _ = record_hit ()
                  val _ = state_order_cache_hits :=
                    !state_order_cache_hits + 1
                  val expected = HOLogic.mk_Trueprop
                    (witness_const $ number level $ literal_columns ids)
                in SOME (check_theorem "cached requested-order state witness"
                  expected theorem) end
            | NONE => NONE)
          fun owner_cache () =
            (case State_Key.lookup (!state_cache) state_key of
              SOME (source_ids, source_theorem) =>
                let
                  val _ = record_hit ()
                  val _ = if ids = source_ids then () else
                    state_owner_reorder_hits :=
                      !state_owner_reorder_hits + 1
                  val source_proposition = HOLogic.mk_Trueprop
                    (witness_const $ number level $ literal_columns source_ids)
                  val _ = check_theorem "cached owner-order state witness"
                    source_proposition source_theorem
                  val theorem = if ids = source_ids then source_theorem
                    else transport_state_witness level source_ids ids source_theorem
                in SOME (cache_requested_order source_ids theorem) end
            | NONE => NONE)
        in
          (case requested_cache () of
            SOME result => result
          | NONE =>
              (case owner_cache () of
                SOME result => result
              | NONE =>
              let
                val _ = Comma_Proof_Profile.report
                  ("B1 zipper stage=build-start level=" ^ string_of_int level ^
                   " width=" ^ string_of_int (length ids))
                val columns = literal_columns ids
                val _ = state_builds := !state_builds + 1
                val _ = note_cid_state false
                val _ = state_column_occurrences :=
                  !state_column_occurrences + length ids
                val _ = maximum_state_width := Int.max
                  (!maximum_state_width, length ids)
                val derived =
                  if level = 4 orelse forall
                      (fn cid => cid = 0 orelse cid = 1) ids then
                    measured terminal_ms (fn () => let
                      val index = one_hot ids
                      val actual_one_hot = literal_columns ids
                      val bool_column = Const
                        (@{const_name Comma_CRT_Bool}, boolT --> columnT)
                      val label_test = Abs ("i", natT,
                        bool_column $ (Const (@{const_name HOL.eq},
                          natT --> natT --> boolT) $ Bound 0 $ number index))
                      val column_length = Const (@{const_name size},
                        column_listT --> natT) $ actual_one_hot
                      val domain = Const (@{const_name upt}, natT --> natT --> nat_listT) $
                        number 0 $ column_length
                      val code_rhs = Const (@{const_name map},
                        (natT --> columnT) --> nat_listT --> column_listT) $
                        label_test $ domain
                      val code_request = HOLogic.mk_eq (actual_one_hot, code_rhs)
                      val code_equation = check_equation "terminal one-hot code"
                        code_request @{term True} (Simplifier.rewrite
                        (base_context addsimps (step_rules ids @
                          terminal_list_rules @ @{thms comma_crt_column.case}))
                        (Thm.cterm_of ctxt code_request))
                      val code_fact = proposition_from_true_equation code_equation
                      val index_bound = HOLogic.mk_binrel @{const_name less}
                        (number index, column_length)
                      val index_prop = HOLogic.mk_Trueprop
                        index_bound
                      val index_fact = Goal.prove ctxt [] [] index_prop
                        (fn {context, ...} => simp_tac
                          (base_context addsimps terminal_list_rules) 1)
                      val intro = Goal.prove ctxt [] []
                        (HOLogic.mk_Trueprop
                          (witness_const $ number level $ columns))
                        (fn {context, ...} =>
                          (resolve_tac context
                            [@{thm comma_semantic_b1_crt_partition_witness_terminal}]
                            THEN_ALL_NEW (fn i => resolve_tac context [index_fact] i ORELSE
                              resolve_tac context [code_fact] i)) 1)
                    in intro end)
                  else
                    let
                      val (node_fact, node_expected) =
                        node_presence level ids
                    in
                      if node_expected then
                        let
                          val input_admitted = admitted_vector level ids
                          val period = radix level
                          val branches = map (fn digit =>
                            let
                              val inputs = ids
                              val (targets, vector_fact) = measured vector_ms
                                (fn () => let
                                  val vector_function = cofactor_const $
                                    number level $ number digit
                                  val vector_request =
                                    Const (@{const_name map},
                                      (columnT --> columnT) --> column_listT --> column_listT) $
                                    vector_function $ columns
                                  val unique_inputs = distinct (op =) inputs
                                  val _ = vector_column_occurrences :=
                                    !vector_column_occurrences + length inputs
                                  val _ = distinct_vector_cids :=
                                    !distinct_vector_cids + length unique_inputs
                                  val (targets, theorem) = prove_vector_map
                                    level digit inputs NONE
                                  val theorem = check_equation "vector cofactor"
                                    vector_request (literal_columns targets) theorem
                                  val _ = vector_builds := !vector_builds + 1
                                  val _ = note_cid_vector_transition false
                                in (targets, theorem) end)
                              val child_fact = build (level + 1) targets
                            in (targets, vector_fact, child_fact) end)
                            (0 upto (period - 1))
                          val child_predicate = Abs ("digit", natT,
                            witness_const $ HOLogic.mk_Suc (number level) $
                              (Const (@{const_name map},
                                (columnT --> columnT) --> column_listT --> column_listT) $
                                (cofactor_const $ number level $ Bound 0) $ columns))
                          val child_range = Const (@{const_name upt},
                            natT --> natT --> nat_listT) $ number 0 $
                              (@{term comma_crt_period} $ number level)
                          val child_list_prop = list_all_term child_predicate child_range
                          val child_range_equation = Vector.sub (child_ranges, level)
                          val child_digits = 0 upto (period - 1)
                          fun child_branch_fact digit vector_fact child_fact =
                            let
                              val request = child_predicate $ number digit
                              val beta = Thm.beta_conversion false (Thm.cterm_of ctxt request)
                              val after_vector = argument_at 0
                                (Conv.rewr_conv vector_fact) (Thm.rhs_of beta)
                              val after_level = argument_at 1
                                (Conv.rewr_conv (Vector.sub (successor_equations, level)))
                                (Thm.rhs_of after_vector)
                              val equation = Thm.transitive beta
                                (Thm.transitive after_vector after_level)
                              val expected = HOLogic.dest_Trueprop (Thm.prop_of child_fact)
                              val _ = check_equation "child witness instance"
                                request expected equation
                              val theorem = Thm.equal_elim
                                (Thm.symmetric (proposition_equality equation)) child_fact
                            in check_theorem "child witness instance"
                              (HOLogic.mk_Trueprop request) theorem end
                          val child_list_fact = measured childfold_ms (fn () =>
                            let
                              val branch_facts = Vector.fromList (map_index
                                (fn (digit, (_, vector_fact, child_fact)) =>
                                  child_branch_fact digit vector_fact child_fact) branches)
                              val (explicit_range, explicit_fact) = fold_list_all
                                "finite child existence list" child_predicate natT number
                                child_digits (fn digit => Vector.sub (branch_facts, digit))
                              val _ = if Thm.term_of (Thm.rhs_of child_range_equation)
                                  aconv explicit_range then () else error
                                "B1 child existence range changed its radix"
                              val range_equation = Conv.arg_conv
                                (Conv.rewr_conv child_range_equation)
                                (Thm.cterm_of ctxt child_list_prop)
                              val theorem = Thm.equal_elim
                                (Thm.symmetric (proposition_equality range_equation)) explicit_fact
                            in check_theorem "finite child existence witnesses"
                              (HOLogic.mk_Trueprop child_list_prop) theorem end)
                          val level_fact = Vector.sub (level_bounds, level)
                          val node_theorem =
                            @{thm comma_semantic_b1_crt_partition_witness_node} OF
                              [level_fact, input_admitted, node_fact, child_list_fact]
                        in node_theorem end
                      else
                        let
                          val input_admitted = admitted_vector level ids
                          val child_fact = build (level + 1) ids
                          val level_fact = Vector.sub (level_bounds, level)
                          val skip_rule =
                            @{thm comma_semantic_b1_crt_partition_witness_skip} OF
                              [level_fact, input_admitted, node_fact]
                          val child_request = witness_const $
                            HOLogic.mk_Suc (number level) $ columns
                          val child_equation = argument_at 1
                            (Conv.rewr_conv (Vector.sub (successor_equations, level)))
                            (Thm.cterm_of ctxt child_request)
                          val _ = check_equation "successor witness level"
                            child_request
                            (witness_const $ number (level + 1) $ columns)
                            child_equation
                          val child_proposition = Thm.combination
                            (Thm.reflexive (Thm.cterm_of ctxt @{term Trueprop}))
                            child_equation
                          val child_at_successor = Thm.equal_elim
                            (Thm.symmetric child_proposition) child_fact
                          val theorem = skip_rule OF [child_at_successor]
                        in theorem end
                    end
                val _ = Comma_Proof_Profile.report
                  ("B1 zipper stage=build-done level=" ^ string_of_int level)
                val proposition = HOLogic.mk_Trueprop
                  (witness_const $ number level $ columns)
                val theorem = check_theorem "new witness" proposition
                  derived
                val _ = if State_Key.size (!state_cache) < cache_limit then
                  state_cache := State_Key.update
                    (state_key, (ids, theorem)) (!state_cache)
                  else state_refusals := !state_refusals + 1
              in cache_requested_order ids theorem end))
        end
      fun warm_child_permutation_fixture () =
        if !child_permutation_fixture_checked then ()
        else
          (case !child_permutation_fixture of
            NONE => ()
          | SOME (child_level, child_source_ids, child_target_ids, child_theorem) =>
              let
                val certificate_builds_before = permutation_certificate_builds ()
                val transports_before = permutation_transport_count ()
                val child_warm_theorem = transport_state_witness
                  child_level child_source_ids child_target_ids child_theorem
                val child_expected = HOLogic.mk_Trueprop
                  (witness_const $ number child_level $
                    literal_columns child_target_ids)
                val _ = check_theorem "warm child permutation replay"
                  child_expected child_warm_theorem
                val _ = if permutation_certificate_builds () =
                    certificate_builds_before then ()
                  else error
                    "B1 warm child replay rebuilt its permutation certificate"
                val _ = if permutation_transport_count () =
                    transports_before + 1 then ()
                  else error
                    "B1 warm child replay missed its permutation transport"
                val _ = child_permutation_fixture_runs :=
                  !child_permutation_fixture_runs + 1
                val _ = child_permutation_fixture_checked := true
              in () end)
      fun warm_owner_fixture raw_ids root_theorem =
        let
          val compact_ids = filter (fn cid => cid <> 0) raw_ids
          val _ = if !warm_owner_fixture_checked then ()
            else
              (case State_Key.lookup (!state_cache) (0, compact_ids) of
                NONE => ()
              | SOME (owner_ids, stored_theorem) =>
                  let
                    val _ = if owner_ids = compact_ids then () else error
                      "B1 root owner cache changed its first-request order"
                    val is_nonterminal = exists (fn cid => cid > 1) compact_ids
                    fun cold_snapshot () =
                      (!state_builds, !state_refusals, !vector_builds,
                       !transition_edges, !admission_requests,
                       !admission_header_uses, !node_metadata_reads,
                       !state_column_occurrences, !vector_column_occurrences,
                       !distinct_vector_cids, !terminal_ms, !node_presence_ms,
                       !admission_ms, !vector_ms, !childfold_ms,
                       indexed_label_proof_counts (), node_presence_counts (),
                       permutation_certificate_builds (),
                       permutation_transport_count ())
                    val raw_proposition = HOLogic.mk_Trueprop
                      (witness_const $ number 0 $ literal_columns raw_ids)
                    val _ = check_theorem "warm raw-owner input witness"
                      raw_proposition root_theorem
                    val cached_proposition = HOLogic.mk_Trueprop
                      (witness_const $ number 0 $
                        literal_columns compact_ids)
                    val _ = check_theorem "warm compact-owner cached state"
                      cached_proposition stored_theorem
                    val _ = if is_nonterminal then
                      let
                        val cold_before = cold_snapshot ()
                        val hits_before = !state_hits
                        val order_hits_before = !state_order_cache_hits
                        val embeddings_before = indexed_label_cache_hits ()
                        val proof_counts_before = indexed_label_proof_counts ()
                        val (raw_occurrences_before, zero_occurrences_before) =
                          indexed_label_occurrence_counts ()
                        val key_width_before = !state_key_input_width
                        val lifts_before = !lift_applications
                        val warm_theorem =
                          build 0 raw_ids
                        val cold_after = cold_snapshot ()
                        val _ = if Thm.prop_of warm_theorem aconv
                              Thm.prop_of root_theorem andalso closed warm_theorem
                          then () else error
                            "B1 warm-owner fixture changed its raw cached theorem"
                        val _ = check_theorem "warm raw-owner fixture replay"
                          raw_proposition warm_theorem
                        val _ = if cold_after = cold_before then ()
                          else error "B1 warm raw-owner fixture performed cold owner/compression work"
                        val _ = if !state_hits = hits_before + 1 then ()
                          else error "B1 warm raw-owner fixture did not hit compact owner state"
                        val _ = if !state_order_cache_hits = order_hits_before then ()
                          else error
                            "B1 root warm-owner fixture unexpectedly used an order transport"
                        val _ = if indexed_label_cache_hits () = embeddings_before + 1 andalso
                            indexed_label_proof_counts () = proof_counts_before then ()
                          else error "B1 warm raw-owner fixture missed its embedding cache"
                        val _ = if !state_key_input_width =
                            key_width_before + length compact_ids then ()
                          else error "B1 warm-owner fixture did not measure its compact replay"
                        val (raw_occurrences_after, zero_occurrences_after) =
                          indexed_label_occurrence_counts ()
                        val _ = if raw_occurrences_after =
                            raw_occurrences_before + length raw_ids andalso
                            zero_occurrences_after = zero_occurrences_before +
                              length raw_ids - length compact_ids then ()
                          else error "B1 warm raw-owner fixture lost raw occurrence accounting"
                        val _ = if !lift_applications = lifts_before + 1 then ()
                          else error "B1 warm raw-owner fixture did not count its selector lift"
                        val _ = warm_owner_fixture_runs :=
                          !warm_owner_fixture_runs + 1
                        val _ = warm_owner_fixture_checked := true
                      in () end
                      else ()
                  in () end)
          val _ = warm_child_permutation_fixture ()
        in
          ()
        end
      fun prove_root_checker ids =
        let
          val _ = if ids <> [] andalso forall (fn cid => cid >= 0 andalso
              cid < node_count) ids then ()
            else error "B1 labelled zipper root row is empty or has a foreign CID"
          val witness = build 0 ids
          val _ = warm_owner_fixture ids witness
          val checker_true =
            (@{thm comma_semantic_b1_crt_partition_witness_checker_true}
              OF [witness]) RS @{thm eq_reflection}
          val levels = HOLogic.mk_list natT (map number [0, 1, 2, 3])
          val request = checker_const $ levels $ literal_columns ids
          val normalized_checker = argument_at 1
            (Simplifier.rewrite (base_context addsimps
              @{thms upt_0 upt_Suc upt_rec upt_rec_numeral}))
            (Thm.lhs_of checker_true)
          val theorem = Thm.transitive (Thm.symmetric normalized_checker) checker_true
          val _ = check_equation "public partition checker" request @{term True} theorem
        in theorem end
      val row_projection =
        Comma_Semantic_B1_Partition_Conversion.make_template_partition_checker_with_state
          ctxt {column_value = column_value, node_count = node_count}
          {prove_state = prove_root_checker,
           state_counts = fn () =>
             (!state_builds, !vector_builds, 0, 0),
           state_work_summary = fn () => ""}
      val prove_checker = #prove_checker row_projection
      fun check_terminal_fixtures () =
        let
          val selectorT = @{typ "nat option comma_crt_mdd"}
          val optionT = @{typ "nat option"}
          val mdd_leaf = Const (@{const_name Comma_CRT_MDD_Leaf}, optionT --> selectorT)
          val some = Const (@{const_name Some}, natT --> optionT)
          val concrete_witness = Const
            (@{const_name comma_semantic_b1_crt_labelled_zip_witness},
              natT --> column_listT --> selectorT --> boolT)
          fun reject_unless_interrupted failure =
            if Exn.is_interrupt failure then Exn.reraise failure else ()
          fun rejected label candidate =
            (case Exn.capture (fn () => terminal_candidate candidate) () of
              Exn.Exn failure => reject_unless_interrupted failure
            | Exn.Res _ => error ("B1 labelled zipper accepted " ^ label))
          and terminal_candidate (entries, index) =
            let
              val columns = HOLogic.mk_list columnT entries
              val selector = mdd_leaf $ (some $ number index)
              val proposition = HOLogic.mk_Trueprop
                (concrete_witness $ number 4 $ columns $ selector)
              val theorem = Goal.prove ctxt [] [] proposition
                (fn {context, ...} =>
                  (resolve_tac context
                    [@{thm comma_semantic_b1_crt_labelled_zip_terminal_from_columns}]
                  THEN_ALL_NEW (fn i => simp_tac
                    (base_context addsimps terminal_list_rules) i)) 1)
            in check_theorem "terminal fixture" proposition theorem end
          val _ = ignore (terminal_candidate
            ([ @{term "Comma_CRT_Bool True"},
               @{term "Comma_CRT_Bool False"} ], 0))
          val _ = rejected "duplicate-true terminal"
            ([ @{term "Comma_CRT_Bool True"},
               @{term "Comma_CRT_Bool True"} ], 0)
          val _ = rejected "all-false terminal"
            ([ @{term "Comma_CRT_Bool False"},
               @{term "Comma_CRT_Bool False"} ], 0)
          val _ = rejected "swapped terminal label"
            ([ @{term "Comma_CRT_Bool False"},
               @{term "Comma_CRT_Bool True"} ], 0)
          val eval_column = Const (@{const_name comma_crt_eval},
            natT --> columnT --> boolT)
          val label_fiber = Const
            (@{const_name comma_semantic_b1_crt_label_fiber},
              natT --> selectorT --> columnT)
          val wrong_odd_selector = @{term
            "Comma_CRT_MDD_Node 0
              [Comma_CRT_MDD_Leaf (Some (0::nat)),
               Comma_CRT_MDD_Leaf (Some (0::nat)),
               Comma_CRT_MDD_Leaf (Some (1::nat)),
               Comma_CRT_MDD_Leaf (Some (1::nat))]"}
          val alternating_first_column = @{term
            "Comma_CRT_Node 0
              [Comma_CRT_Bool True, Comma_CRT_Bool False,
               Comma_CRT_Bool True, Comma_CRT_Bool False]"}
          val odd_phase_mismatch = HOLogic.mk_Trueprop (HOLogic.mk_not
            (HOLogic.mk_eq
              (eval_column $ number 1 $ (label_fiber $ number 0 $ wrong_odd_selector),
               eval_column $ number 1 $ alternating_first_column)))
          val _ = Goal.prove ctxt [] [] odd_phase_mismatch
            (fn {context, ...} => simp_tac
              (context addsimps
                @{thms comma_semantic_b1_crt_label_fiber.simps
                  comma_crt_eval.simps comma_crt_node_def
                  comma_crt_period_def}) 1)
          val _ = (case Exn.capture (fn () => prove_checker
              {context = ctxt,
               checker_ct = Thm.cterm_of ctxt
                 (checker_const $ HOLogic.mk_list natT (map number [0, 1, 2, 3]) $
                   literal_columns [node_count]),
               ids_row = HOLogic.mk_list natT [number node_count],
               row = literal_columns [node_count],
               resolved_fact = @{thm TrueI}}) () of
              Exn.Exn failure => reject_unless_interrupted failure
            | Exn.Res _ => error "B1 labelled zipper accepted a foreign/stale catalog CID")
        in () end
      fun check_complete_fixtures () =
        let
          val _ = if !warm_owner_fixture_runs > 0 andalso
              !child_permutation_fixture_checked andalso
              !child_permutation_fixture_runs > 0 then ()
            else error "B1 completed publication did not exercise both warm owner fixtures"
          val _ = check_vector_alias_fixture ()
        in () end
      fun stats () =
        " labelled_zip_states=" ^ Int.toString (!state_builds) ^
        " labelled_zip_state_hits=" ^ Int.toString (!state_hits) ^
        " labelled_zip_state_refusals=" ^ Int.toString (!state_refusals) ^
        " labelled_zip_vectors=" ^ Int.toString (!vector_builds) ^
        vector_cache_stats () ^
        " labelled_zip_warm_owner_fixture_runs=" ^
          Int.toString (!warm_owner_fixture_runs) ^
        " labelled_zip_child_permutation_fixture_runs=" ^
          Int.toString (!child_permutation_fixture_runs) ^
        " labelled_zip_transition_edges=" ^ Int.toString (!transition_edges) ^
        " labelled_zip_node_metadata_reads=" ^ Int.toString (!node_metadata_reads) ^
        node_presence_stats () ^
        " labelled_zip_admission_requests=" ^ Int.toString (!admission_requests) ^
        " labelled_zip_admission_header_uses=" ^ Int.toString (!admission_header_uses) ^
        " labelled_zip_terminal_ms=" ^ LargeInt.toString (!terminal_ms) ^
        " labelled_zip_node_presence_ms=" ^ LargeInt.toString (!node_presence_ms) ^
        " labelled_zip_admission_ms=" ^ LargeInt.toString (!admission_ms) ^
        " labelled_zip_vector_ms=" ^ LargeInt.toString (!vector_ms) ^
        " labelled_zip_childfold_ms=" ^ LargeInt.toString (!childfold_ms) ^
        " labelled_zip_compression_ms=" ^ LargeInt.toString (!compression_ms) ^
        " labelled_zip_lift_ms=" ^ LargeInt.toString (!lift_ms) ^
        " labelled_zip_lift_applications=" ^ Int.toString (!lift_applications) ^
        " labelled_zip_state_order_cache_hits=" ^
          Int.toString (!state_order_cache_hits) ^
        " labelled_zip_state_order_cache_refusals=" ^
          Int.toString (!state_order_cache_refusals) ^
        " labelled_zip_state_owner_reorder_hits=" ^
          Int.toString (!state_owner_reorder_hits) ^
        permutation_cache_stats () ^
        " labelled_zip_state_sort_seconds=" ^
          Real.toString (Time.toReal (!state_sort_elapsed)) ^
        " labelled_zip_state_sort_calls=" ^ Int.toString (!state_sort_calls) ^
        indexed_label_stats () ^
        " labelled_zip_state_column_occurrences=" ^
          Int.toString (!state_column_occurrences) ^
        " labelled_zip_vector_column_occurrences=" ^
          Int.toString (!vector_column_occurrences) ^
        " labelled_zip_distinct_vector_cids=" ^
          Int.toString (!distinct_vector_cids) ^
        " labelled_zip_max_state_width=" ^ Int.toString (!maximum_state_width) ^
        " labelled_zip_state_key_input_width=" ^
          Int.toString (!state_key_input_width)
    in
      {prove_checker = prove_checker, stats = stats,
       check_terminal_fixtures = check_terminal_fixtures,
       check_complete_fixtures = check_complete_fixtures}
    end
end
