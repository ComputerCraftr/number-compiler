(* Proof a selected template's exact resolved-row and cardinality obligation.
   The fixed catalogue and projection context are supplied by the occurrence
   owner; this owner caches one closed theorem per checked template CID. *)
structure Comma_Semantic_B1_Template_Mass_Check =
struct
  fun make ctxt {context, mass_row, node_count} =
    let
      val natT = @{typ nat}
      val columnT = @{typ comma_crt_column}
      val certificates = Unsynchronized.ref (Inttab.empty: thm Inttab.table)
      val requests = Unsynchronized.ref 0
      val hits = Unsynchronized.ref 0
      val misses = Unsynchronized.ref 0
      val elapsed = Unsynchronized.ref (0: LargeInt.int)
      val row_selection_ms = Unsynchronized.ref (0: LargeInt.int)
      val mass_requests_ms = Unsynchronized.ref (0: LargeInt.int)
      val row_proof_ms = Unsynchronized.ref (0: LargeInt.int)
      val row_bound_ms = Unsynchronized.ref (0: LargeInt.int)
      val row_map_ms = Unsynchronized.ref (0: LargeInt.int)
      val row_resolution_ms = Unsynchronized.ref (0: LargeInt.int)
      val cid_transport_ms = Unsynchronized.ref (0: LargeInt.int)
      (* These tables are a finite census of rows which have actually
         reached the checked cold proof.  Keys are closed nat lists, so
         repeated occurrences remain visible in the vector and in the
         sorted multiset key.  They are deliberately local to this owner;
         no catalogue-wide scan is performed. *)
      val ordered_mass_vectors = Unsynchronized.ref
        (Termtab.empty: unit Termtab.table)
      val mass_histograms = Unsynchronized.ref
        (Termtab.empty: unit Termtab.table)
      val row_cid_multisets = Unsynchronized.ref
        (Termtab.empty: unit Termtab.table)
      val exact_row_theorems = Unsynchronized.ref 0
      val cid_transport_calls = Unsynchronized.ref 0
      val cid_transport_nonidentity = Unsynchronized.ref 0
      val histogram_arithmetic_cache = Unsynchronized.ref
        (Termtab.empty: thm Termtab.table)
      val ordered_arithmetic_cache = Unsynchronized.ref
        (Termtab.empty: thm Termtab.table)
      val histogram_arithmetic_builds = Unsynchronized.ref 0
      val histogram_arithmetic_hits = Unsynchronized.ref 0
      val ordered_arithmetic_builds = Unsynchronized.ref 0
      val ordered_arithmetic_hits = Unsynchronized.ref 0
      val arithmetic_transport_builds = Unsynchronized.ref 0
      val arithmetic_ms = Unsynchronized.ref (0: LargeInt.int)
      fun number value = HOLogic.mk_number natT value
      fun list_key values = HOLogic.mk_list natT (map number values)
      fun note table values =
        let val key = list_key values
        in if Termtab.defined (!table) key then ()
           else table := Termtab.update (key, ()) (!table)
        end
      fun timed timer work =
        let
          val started = Time.now ()
          val result = Exn.capture work ()
          val _ = timer := !timer +
            Time.toMilliseconds (Time.- (Time.now (), started))
        in Exn.release result end
      fun row_total_ms () =
        !row_proof_ms + !row_bound_ms + !row_map_ms + !row_resolution_ms
      fun normalize term = Comma_Selected_List_Conversion.validate_equation term
        (Simplifier.rewrite context (Thm.cterm_of ctxt term))
      fun bounded_term term =
        "nodes_cap=" ^ Int.toString
          (Comma_Semantic_B1_Construction_Check.capped_nodes 64 term) ^
        " shape=" ^ Comma_Semantic_B1_Partition_Support.shape 6 term
      fun numeral label term =
        (case try HOLogic.dest_number term of
          SOME (typ, value) =>
            if typ = natT andalso value >= 0 then value
            else error ("B1 template mass " ^ label ^
              " is not a natural numeral; residual=" ^ bounded_term term)
        | NONE => error ("B1 template mass " ^ label ^
            " did not select to a numeral; residual=" ^ bounded_term term))
      fun check_fact theorem proposition =
        if Thm.prop_of theorem aconv HOLogic.mk_Trueprop proposition andalso
            Thm.nprems_of theorem = 0 andalso null (Thm.hyps_of theorem) andalso
            null (Thm.tpairs_of theorem)
        then theorem else error "B1 template mass theorem failed exact closed audit"
      val dagT = @{typ comma_semantic_b1_crt_column_dag}
      val nat_listT = HOLogic.listT natT
      val multisetT = Type (@{type_name multiset}, [natT])
      val expected_dag = @{term comma_semantic_b1_crt_column_node_dag}
      val column_at_const = Const (@{const_name comma_semantic_b1_crt_column_at},
        dagT --> natT --> columnT)
      val mass_const = Const (@{const_name comma_semantic_b1_crt_column_mass},
        columnT --> natT)
      val column_at_function = column_at_const $ expected_dag
      val column_listT = HOLogic.listT columnT
      val map_column_at_const = Const (@{const_name map},
        (natT --> columnT) --> nat_listT --> column_listT)
      val map_column_at = map_column_at_const $ column_at_function
      val map_column_at_ct = Thm.cterm_of ctxt map_column_at
      val column_cons_ct = Thm.cterm_of ctxt
        (Const (@{const_name Cons}, columnT --> column_listT --> column_listT))
      val map_nil = @{thm list.map(1)} RS @{thm eq_reflection}
      val map_cons = @{thm list.map(2)} RS @{thm eq_reflection}
      val sum_list_const = Const (@{const_name sum_list}, nat_listT --> natT)
      val mset_const = Const (@{const_name mset}, nat_listT --> multisetT)
      val map_const = Const (@{const_name map},
        (columnT --> natT) --> HOLogic.listT columnT --> nat_listT)
      val map_mass = map_const $ mass_const
      fun checked_mass_row ids {equation, values} =
        let
          val expected_left = map_mass $ HOLogic.mk_list columnT
            (map (fn cid => column_at_const $ expected_dag $ number cid) ids)
          val expected_right = list_key values
          val _ = if length ids = length values andalso
              forall (fn value => value >= 0) values andalso
              Thm.nprems_of equation = 0 andalso null (Thm.hyps_of equation)
              andalso null (Thm.tpairs_of equation) andalso
              Thm.term_of (Thm.lhs_of equation) aconv expected_left andalso
              Thm.term_of (Thm.rhs_of equation) aconv expected_right then ()
            else error "B1 template mass callback changed ordered column authority"
        in (equation, values) end
      fun sum_list_term values = sum_list_const $ list_key values
      fun mset_term values = mset_const $ list_key values
      fun sum_equation values rhs = HOLogic.mk_Trueprop
        (HOLogic.mk_eq (sum_list_term values, number rhs))
      fun mset_equation source target = HOLogic.mk_Trueprop
        (HOLogic.mk_eq (mset_term source, mset_term target))
      val (certify_arithmetic, arithmetic_certification_stats) =
        Comma_Entry_Arithmetic.make_certifier ctxt
      val arithmetic_context = Comma_Entry_Arithmetic.natural_context ctxt
        addsimps @{thms sum_list.Cons sum_list.Nil list.map}
      fun checked_cid term =
        let
          fun reject normalized = error
            ("B1 template mass CID did not select to a numeral; raw=" ^
             bounded_term term ^ "; normalized=" ^ bounded_term normalized)
        in
          (case try HOLogic.dest_number term of
            SOME (typ, value) =>
              if typ = natT andalso value >= 0 then
                (Thm.reflexive (Thm.cterm_of ctxt term), value)
              else reject term
          | NONE =>
              let
                val selected = normalize term
                val arithmetic = Simplifier.rewrite arithmetic_context
                  (Thm.rhs_of selected)
                val equation = Thm.transitive selected arithmetic
                val normalized = Thm.term_of (Thm.rhs_of equation)
              in
                (case try HOLogic.dest_number normalized of
                  SOME (typ, value) =>
                    if typ = natT andalso value >= 0 then (equation, value)
                    else reject normalized
                | NONE => reject normalized)
              end)
        end
      val _ =
        let
          val (_, zero) = checked_cid (number 0)
          val (_, one) = checked_cid (number 1)
        in
          if zero = 0 andalso one = 1 then ()
          else error "B1 template mass literal CID conversion regression"
        end
      fun check_closed_arithmetic label proposition theorem =
        if Thm.prop_of theorem aconv proposition andalso
            Thm.nprems_of theorem = 0 andalso null (Thm.hyps_of theorem) andalso
            null (Thm.tpairs_of theorem)
        then theorem else error ("B1 template arithmetic " ^ label ^
          " theorem failed exact closed audit")
      fun close_true_arithmetic label proposition normalized =
        let
          val _ = if Thm.term_of (Thm.rhs_of normalized) aconv @{prop True}
            then () else error ("B1 template arithmetic " ^ label ^
              " did not reduce to True")
          val theorem = check_closed_arithmetic label proposition
            (Thm.equal_elim (Thm.symmetric normalized) @{thm TrueI})
        in certify_arithmetic theorem end
      fun histogram_fact values =
        let
          val key = list_key values
        in
          (case Termtab.lookup (!histogram_arithmetic_cache) key of
            SOME theorem =>
              (histogram_arithmetic_hits := !histogram_arithmetic_hits + 1;
               check_closed_arithmetic "cached histogram" (sum_equation values 924)
                 theorem)
          | NONE =>
              let
                val proposition = sum_equation values 924
                val normalized = timed arithmetic_ms (fn () =>
                  Simplifier.rewrite arithmetic_context
                    (Thm.cterm_of ctxt proposition))
                val theorem = close_true_arithmetic "histogram" proposition normalized
                val _ = histogram_arithmetic_builds :=
                  !histogram_arithmetic_builds + 1
                val _ = if Termtab.size (!histogram_arithmetic_cache) < 8192
                  then histogram_arithmetic_cache :=
                    Termtab.update (key, theorem) (!histogram_arithmetic_cache)
                  else ()
              in theorem end)
        end
      fun ordered_fact values =
        let
          val key = list_key values
        in
          (case Termtab.lookup (!ordered_arithmetic_cache) key of
            SOME theorem =>
              (ordered_arithmetic_hits := !ordered_arithmetic_hits + 1;
               check_closed_arithmetic "cached ordered vector" (sum_equation values 924)
                 theorem)
          | NONE =>
              let
                val histogram = sort int_ord values
                val histogram_theorem = histogram_fact histogram
                val theorem =
                  if values = histogram then histogram_theorem
                  else
                    let
                      val mset_proposition = mset_equation values histogram
                      val mset_fact = timed arithmetic_ms (fn () =>
                        Goal.prove ctxt [] [] mset_proposition
                          (fn {context, ...} =>
                            simp_tac (put_simpset HOL_basic_ss context addsimps
                              @{thms mset.simps add_mset_commute}) 1))
                      val _ = check_closed_arithmetic "ordered multiset"
                        mset_proposition mset_fact
                      val sum_proposition = HOLogic.mk_Trueprop
                        (HOLogic.mk_eq (sum_list_term values,
                          sum_list_term histogram))
                      val transported = timed arithmetic_ms (fn () =>
                        @{thm comma_semantic_b1_crt_sum_list_mset} OF [mset_fact])
                      val _ = check_closed_arithmetic "ordered transport"
                        sum_proposition transported
                      val _ = arithmetic_transport_builds :=
                        !arithmetic_transport_builds + 1
                    in
                      check_closed_arithmetic "ordered vector"
                        (sum_equation values 924)
                        (@{thm trans} OF [transported, histogram_theorem])
                    end
                val _ = ordered_arithmetic_builds :=
                  !ordered_arithmetic_builds + 1
                val _ = if Termtab.size (!ordered_arithmetic_cache) < 8192
                  then ordered_arithmetic_cache :=
                    Termtab.update (key, theorem) (!ordered_arithmetic_cache)
                  else ()
              in theorem end)
        end
      fun extent table =
        let
          val size = Const (@{const_name size}, fastype_of table --> natT) $ table
          val equation = normalize size
        in numeral "catalogue extent" (Thm.term_of (Thm.rhs_of equation)) end
      val template_extent = extent @{term comma_semantic_b1_crt_templates}
      val ids_extent = extent @{term comma_semantic_b1_crt_template_column_ids}
      (* Bind the generic row-resolution theorem to the exact closed column
         table published by this owner.  The numeral check ties its named
         extent to the mass owner's independently checked node count. *)
      val columns_definition = Proof_Context.get_thm ctxt
        "comma_semantic_b1_crt_columns_def"
      val column_count_definition = Proof_Context.get_thm ctxt
        "comma_semantic_b1_crt_column_count_def"
      val columns_term = @{term comma_semantic_b1_crt_columns}
      val column_count_term = @{term comma_semantic_b1_crt_column_count}
      val columns_for_const = Const (@{const_name comma_semantic_b1_crt_columns_for},
        dagT --> natT --> column_listT)
      fun clean_equation theorem = Thm.nprems_of theorem = 0 andalso
        null (Thm.hyps_of theorem) andalso null (Thm.tpairs_of theorem)
      val _ = if clean_equation columns_definition andalso
          Thm.term_of (Thm.lhs_of columns_definition) aconv columns_term
        then () else error "B1 template mass columns definition changed authority"
      val _ = if clean_equation column_count_definition andalso
          Thm.term_of (Thm.lhs_of column_count_definition) aconv column_count_term
        then () else error "B1 template mass column-count definition changed authority"
      val column_count_value = numeral "column count"
        (Thm.term_of (Thm.rhs_of column_count_definition))
      val _ = if column_count_value = node_count then ()
        else error "B1 template mass column extent disagrees with the DAG owner"
      val columns_rhs = Thm.term_of (Thm.rhs_of columns_definition)
      val _ = (case strip_comb columns_rhs of
        (Const (name, _), [dag, extent]) =>
          if name = @{const_name comma_semantic_b1_crt_columns_for} andalso
              dag aconv expected_dag andalso extent aconv column_count_term then ()
          else error "B1 template mass columns definition changed its DAG or extent"
      | _ => error "B1 template mass columns definition has an unexpected shape")
      val columns_table_fact = check_fact
        (columns_definition RS @{thm meta_eq_to_obj_eq})
        (HOLogic.mk_eq (columns_term,
          columns_for_const $ expected_dag $ column_count_term))
      val column_bounds_context = Comma_Entry_Arithmetic.natural_context ctxt
        addsimps (column_count_definition ::
          @{thms list_all_Cons_iff list_all_Nil_iff})
      val list_all_nat_const = Const (@{const_name list_all},
        (natT --> @{typ bool}) --> nat_listT --> @{typ bool})
      val column_bound_predicate = Abs ("cid", natT,
        Const (@{const_name less}, natT --> natT --> @{typ bool}) $
          Bound 0 $ column_count_term)
      (* These rewrite rules are fixed for the lifetime of this checker.  Keep
         the row-specific mass facts out of the shared context so every row
         still receives its exact, occurrence-preserving arithmetic evidence. *)
      val template_mass_proof_context = context delsimps
        @{thms sum_list.Cons sum_list.Nil}
      fun component_fact label proposition facts =
        let
          val normalized = timed row_proof_ms (fn () =>
            Simplifier.rewrite (template_mass_proof_context addsimps facts)
              (Thm.cterm_of ctxt (HOLogic.mk_Trueprop proposition)))
          val _ = if Thm.term_of (Thm.rhs_of normalized) aconv @{prop True}
            then () else error ("B1 selected template " ^ label ^
              " did not reduce to True")
        in check_fact
          (Thm.equal_elim (Thm.symmetric normalized) @{thm TrueI}) proposition end
      fun prove_column_id_bounds ids =
        let
          val ids_list = HOLogic.mk_list natT (map number ids)
          val proposition = list_all_nat_const $ column_bound_predicate $ ids_list
          val normalized = timed row_bound_ms (fn () =>
            Simplifier.rewrite column_bounds_context
              (Thm.cterm_of ctxt (HOLogic.mk_Trueprop proposition)))
          val _ = if Thm.term_of (Thm.rhs_of normalized) aconv @{prop True}
            then () else error "B1 template mass row contains an out-of-range column ID"
        in check_fact
          (Thm.equal_elim (Thm.symmetric normalized) @{thm TrueI}) proposition end
      fun map_column_at_equation ids =
        let
          val source = HOLogic.mk_list natT (map number ids)
          val expected = HOLogic.mk_list columnT
            (map (fn id => column_at_function $ number id) ids)
          fun map_spine current remaining =
            (case Thm.term_of current of
              Const (name, _) =>
                if name = @{const_name Nil} andalso null remaining then
                  Conv.rewr_conv map_nil (Thm.apply map_column_at_ct current)
                else error "B1 template mass map found a malformed row spine"
            | _ =>
                (case remaining of
                  [] => error "B1 template mass map ran out of row IDs"
                | id :: tail_ids =>
                    let
                      val (cons_head, tail) = Thm.dest_comb current
                      val (cons_ct, head_ct) = Thm.dest_comb cons_head
                      val _ = (case Thm.term_of cons_ct of
                        Const (name, _) => if name = @{const_name Cons} then ()
                          else error "B1 template mass map found a non-cons row spine"
                      | _ => error "B1 template mass map found a malformed row spine")
                      val _ = if Thm.term_of head_ct aconv number id then ()
                        else error "B1 template mass map changed the selected ID order"
                      val head = column_at_function $ number id
                      val tail_equation = map_spine tail tail_ids
                      val map_equation = Conv.rewr_conv map_cons
                        (Thm.apply map_column_at_ct current)
                      val cons_head_equation = Thm.combination
                        (Thm.reflexive column_cons_ct)
                        (Thm.reflexive (Thm.cterm_of ctxt head))
                      val cons_target_equation = Thm.combination
                        cons_head_equation tail_equation
                    in Thm.transitive map_equation cons_target_equation end))
          val equation = map_spine (Thm.cterm_of ctxt source) ids
          val _ = if Thm.term_of (Thm.lhs_of equation) aconv (map_column_at $ source)
              andalso Thm.term_of (Thm.rhs_of equation) aconv expected andalso
              clean_equation equation
            then () else error "B1 template mass structural map changed row order"
        in equation end
      fun prove request =
        let
          val started = Time.now ()
          val _ = requests := !requests + 1
          val (head, arguments) = strip_comb request
          val (columns_arg, templates_arg, ids_arg, cid_term) =
            (case (head, arguments) of
              (Const (name, _), [columns_arg, templates_arg, ids_arg, cid_term]) =>
                if name = @{const_name comma_semantic_b1_crt_template_mass_certified}
                    andalso columns_arg aconv
                      @{term comma_semantic_b1_crt_columns}
                    andalso templates_arg aconv
                      @{term comma_semantic_b1_crt_templates}
                    andalso ids_arg aconv
                      @{term comma_semantic_b1_crt_template_column_ids}
                then (columns_arg, templates_arg, ids_arg, cid_term)
                else error "B1 template mass request has a foreign catalogue"
            | _ => error "B1 template mass request is malformed")
          val (cid_eq, cid) = timed cid_transport_ms (fn () => checked_cid cid_term)
          val _ = if cid < template_extent andalso cid < ids_extent
            then () else error "B1 template mass CID is outside its checked catalogues"
          val canonical_request = list_comb (head,
            [columns_arg, templates_arg, ids_arg, number cid])
          val root_fact =
            (case Inttab.lookup (!certificates) cid of
              SOME theorem =>
                (hits := !hits + 1; check_fact theorem canonical_request)
            | NONE =>
                let
                  val ids_type = fastype_of ids_arg
                  val ids_row_type = HOLogic.listT natT
                  val nth = Const (@{const_name nth}, ids_type --> natT --> ids_row_type)
                  val ids_term = nth $ ids_arg $ number cid
                  val (ids_equation, ids_values) = timed row_selection_ms (fn () =>
                    let
                      val ids_equation = normalize ids_term
                      val ids_values =
                        (case try HOLogic.dest_list
                            (Thm.term_of (Thm.rhs_of ids_equation)) of
                          SOME values => map (fn value =>
                            let val id = numeral "row ID" value
                            in if id < node_count then id
                              else error "B1 template row contains a foreign column ID" end)
                            values
                        | NONE => error
                            "B1 template mass request did not select a literal ID row")
                    in
                      (ids_equation, ids_values)
                    end)
                  (* The shared column owner proves the ordered map once.
                     Its exact equation preserves duplicates and catalogue authority. *)
                  val (mass_equation, mass_values) = timed mass_requests_ms (fn () =>
                    checked_mass_row ids_values (mass_row ids_values))
                  (* Build or reuse the numeric row-sum certificate separately
                     from row resolution.  The histogram cache is keyed by a
                     sorted occurrence list; ordered rows receive a checked
                     mset transport theorem before being composed with the
                     cached histogram sum. *)
                  val row_arithmetic = ordered_fact mass_values
                  val templates_type = fastype_of templates_arg
                  val template_row_type = HOLogic.listT columnT
                  val nth_templates = Const (@{const_name nth},
                    templates_type --> natT --> template_row_type)
                  val template_row_term = nth_templates $ templates_arg $ number cid
                  (* Select the exact published row once.  Both the resolution
                     and mass components consume this same closed equation;
                     neither component reopens the lazy template projection. *)
                  val template_row_equation = timed row_selection_ms (fn () =>
                    let
                      val equation = normalize template_row_term
                      val row = Thm.term_of (Thm.rhs_of equation)
                      val _ = (case try HOLogic.dest_list row of
                        SOME _ => ()
                      | NONE => error
                          "B1 template mass request did not select a literal template row")
                    in equation end)
                  val length_templates = Const (@{const_name size},
                    templates_type --> natT) $ templates_arg
                  val length_ids = Const (@{const_name size},
                    fastype_of ids_arg --> natT) $ ids_arg
                  val template_bound = component_fact "template bound"
                    (HOLogic.mk_binrel @{const_name less} (number cid, length_templates)) []
                  val ids_bound = component_fact "row bound"
                    (HOLogic.mk_binrel @{const_name less} (number cid, length_ids)) []
                  val resolved_prop =
                    (@{term comma_semantic_b1_crt_column_ids_resolve} $
                      columns_arg $ (nth $ ids_arg $ number cid) $ template_row_term)
                  val literal_id_bounds = prove_column_id_bounds ids_values
                  val selected_id_bounds_raw = Thm.combination
                    (Thm.reflexive (Thm.cterm_of ctxt
                      (list_all_nat_const $ column_bound_predicate))) ids_equation
                  val selected_id_bounds = Thm.combination
                    (Thm.reflexive (Thm.cterm_of ctxt @{term Trueprop}))
                    selected_id_bounds_raw
                  val id_bounds = check_fact
                    (Thm.equal_elim (Thm.symmetric selected_id_bounds) literal_id_bounds)
                    (list_all_nat_const $ column_bound_predicate $ ids_term)
                  val mapped_row = timed row_map_ms (fn () =>
                    let
                      val selected_map = Thm.combination
                        (Thm.reflexive map_column_at_ct) ids_equation
                      val literal_map = map_column_at_equation ids_values
                      val selected_literal_map = Thm.transitive selected_map literal_map
                      val _ = if Thm.term_of (Thm.rhs_of selected_literal_map) aconv
                          Thm.term_of (Thm.rhs_of template_row_equation)
                        then () else error
                          "B1 template row does not match its selected ordered ID row"
                      val equation = Thm.transitive selected_literal_map
                        (Thm.symmetric template_row_equation)
                      val expected_lhs = map_column_at $ ids_term
                      val _ = if Thm.term_of (Thm.lhs_of equation) aconv expected_lhs
                          andalso Thm.term_of (Thm.rhs_of equation) aconv template_row_term
                          andalso clean_equation equation
                        then () else error
                          "B1 template row map changed its exact selected request"
                    in equation end)
                  val resolved = timed row_resolution_ms (fn () =>
                    check_fact
                      (@{thm comma_semantic_b1_crt_column_ids_resolve_columns_for_from_map}
                        OF [columns_table_fact, id_bounds,
                          mapped_row RS @{thm meta_eq_to_obj_eq}])
                      resolved_prop)
                  val row_mass_prop = HOLogic.mk_eq
                    (sum_list_const $ (map_mass $ template_row_term), number 924)
                  val row_mass = timed row_proof_ms (fn () =>
                    let
                      val row_map = Thm.combination
                        (Thm.reflexive (Thm.cterm_of ctxt map_mass)) template_row_equation
                      val mapped = Thm.transitive row_map mass_equation
                      val summed = Thm.combination
                        (Thm.reflexive (Thm.cterm_of ctxt sum_list_const)) mapped
                      val exact_sum = Thm.transitive summed
                        (row_arithmetic RS @{thm eq_reflection})
                    in check_fact (exact_sum RS @{thm meta_eq_to_obj_eq})
                      row_mass_prop end)
                  val theorem = check_fact
                    (@{thm comma_semantic_b1_crt_template_mass_certified_intro}
                      OF [template_bound, ids_bound, resolved, row_mass])
                    canonical_request
                  (* Census only successful exact rows.  The ordered vector
                     is the proof input; the sorted key records multiplicity
                     sharing candidates without changing the proof order. *)
                  val _ = note ordered_mass_vectors mass_values
                  val _ = note mass_histograms (sort int_ord mass_values)
                  val _ = note row_cid_multisets (sort int_ord ids_values)
                  val _ = exact_row_theorems := !exact_row_theorems + 1
                  val _ = misses := !misses + 1
                  val _ = if !misses mod 8 = 0 then
                    Comma_Proof_Profile.report
                      ("B1 shared template masses completed=" ^ Int.toString (!misses) ^
                        " mass_ms=" ^ LargeInt.toString (!mass_requests_ms) ^
                        " row_ms=" ^ LargeInt.toString (row_total_ms ()) ^
                        " row_bound_ms=" ^ LargeInt.toString (!row_bound_ms) ^
                        " row_map_ms=" ^ LargeInt.toString (!row_map_ms) ^
                        " row_resolution_ms=" ^ LargeInt.toString (!row_resolution_ms) ^
                        " numeric_schemas=" ^ Int.toString (!histogram_arithmetic_builds))
                    else ()
                  val _ = if Inttab.size (!certificates) < 8192
                    then certificates := Inttab.update (cid, theorem) (!certificates)
                    else ()
                in theorem end)
          (* Transport only the requested CID. A whole-proposition rewrite can
             unfold the catalogue arguments and change the admitted owner. *)
          val request_normalized = timed cid_transport_ms (fn () =>
            Conv.arg_conv (Conv.arg_conv (K cid_eq))
              (Thm.cterm_of ctxt (HOLogic.mk_Trueprop request)))
          val _ = cid_transport_calls := !cid_transport_calls + 1
          val _ = if cid_term aconv number cid then ()
            else cid_transport_nonidentity := !cid_transport_nonidentity + 1
          val _ = if Thm.term_of (Thm.rhs_of request_normalized) aconv
              HOLogic.mk_Trueprop canonical_request
            then () else error "B1 template mass CID normalization changed another argument"
          val theorem = check_fact
            (Thm.equal_elim (Thm.symmetric request_normalized) root_fact) request
          val _ = elapsed := !elapsed +
            Time.toMilliseconds (Time.- (Time.now (), started))
        in theorem end
      fun stats () =
        "template_mass_requests=" ^ Int.toString (!requests) ^
        " template_mass_hits=" ^ Int.toString (!hits) ^
        " template_mass_misses=" ^ Int.toString (!misses) ^
        " template_mass_roots=" ^ Int.toString (Inttab.size (!certificates)) ^
        " template_mass_proof_ms=" ^ LargeInt.toString (!elapsed) ^
        " template_mass_row_selection_ms=" ^ LargeInt.toString (!row_selection_ms) ^
        " template_mass_mass_requests_ms=" ^ LargeInt.toString (!mass_requests_ms) ^
        " template_mass_row_proof_ms=" ^ LargeInt.toString (row_total_ms ()) ^
        " template_mass_row_bound_ms=" ^ LargeInt.toString (!row_bound_ms) ^
        " template_mass_row_map_ms=" ^ LargeInt.toString (!row_map_ms) ^
        " template_mass_row_resolution_ms=" ^ LargeInt.toString (!row_resolution_ms) ^
        " template_mass_cid_transport_ms=" ^ LargeInt.toString (!cid_transport_ms) ^
        " template_mass_distinct_ordered_mass_vectors=" ^
          Int.toString (Termtab.size (!ordered_mass_vectors)) ^
        " template_mass_distinct_mass_histograms=" ^
          Int.toString (Termtab.size (!mass_histograms)) ^
        " template_mass_distinct_row_cid_multisets=" ^
          Int.toString (Termtab.size (!row_cid_multisets)) ^
        " template_mass_exact_row_theorems=" ^
          Int.toString (!exact_row_theorems) ^
        " template_mass_cid_transport_calls=" ^
          Int.toString (!cid_transport_calls) ^
        " template_mass_cid_transport_nonidentity=" ^
          Int.toString (!cid_transport_nonidentity) ^
        " template_mass_histogram_arithmetic_builds=" ^
          Int.toString (!histogram_arithmetic_builds) ^
        " template_mass_histogram_arithmetic_hits=" ^
          Int.toString (!histogram_arithmetic_hits) ^
        " template_mass_ordered_arithmetic_builds=" ^
          Int.toString (!ordered_arithmetic_builds) ^
        " template_mass_ordered_arithmetic_hits=" ^
          Int.toString (!ordered_arithmetic_hits) ^
        " template_mass_arithmetic_transport_builds=" ^
          Int.toString (!arithmetic_transport_builds) ^
        " template_mass_arithmetic_ms=" ^
          LargeInt.toString (!arithmetic_ms) ^
        " template_mass_arithmetic_certifier_calls=" ^
          Int.toString (#calls (arithmetic_certification_stats ())) ^
        " template_mass_arithmetic_certifier_nodes=" ^
          Int.toString (#nodes (arithmetic_certification_stats ()))
    in {prove = prove, stats = stats} end
end
