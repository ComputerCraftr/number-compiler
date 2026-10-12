(*
   One-shot mass certificate for a dependency-closed column-DAG fragment.

   This file stays separate from semantic_b1_column_mass.ML.  The legacy
   per-CID step path remains available while the concrete publisher adopts an
   authenticated annotation producer.  The producer publishes two clean,
   oracle-free theorems:

     comma_semantic_b1_crt_column_mass_annotation_tree_valid
       dag node_count mass_tree

     (\<forall>cid level mass.
        mass_tree_lookup mass_tree cid = Some (level,mass) \<longrightarrow>
        admitted 0 (column_at dag cid) \<and>
        column_mass (column_at dag cid) = mass)

   The first theorem is the executable checker: exact source-DAG lookup,
   child closure, key ordering/balance, level/radix checks, admission, and the recurrence.  The
   second theorem is its strong-induction result.  A mass request only
   specializes that universal theorem, so it never calls column_step.

   The mass tree is an AVL-balanced sparse dependency closure, not a
   50,213-entry vector.  Original child lists remain authoritative and
   repeated child positions remain repeated in the recurrence.

   Generic owner contract:

     datatype comma_semantic_b1_crt_mass_tree =
       Comma_B1_CRT_Mass_Tree_Empty |
       Comma_B1_CRT_Mass_Tree_Node nat nat nat
         comma_semantic_b1_crt_mass_tree comma_semantic_b1_crt_mass_tree

     comma_semantic_b1_crt_mass_tree_lookup ::
       comma_semantic_b1_crt_mass_tree \<Rightarrow> nat \<Rightarrow>
         (nat \<times> nat) option
*)
structure Comma_Semantic_B1_Column_Mass_Invariant =
struct
  type mass_entry = {value: int, theorem: thm}
  type annotation_row = Comma_Semantic_B1_Mass_Candidate.annotation_row
  type node_row = Comma_Semantic_B1_Mass_Candidate.node_row

  (* The ordered map proof is shared by both mass owners.  Its input list is
     the exact source order and its child theorems are positional; therefore
     duplicate columns are retained and no semantic-ID set conversion is
     involved.  Keeping this spine here avoids subtly different map proofs in
     the invariant and legacy paths. *)
  fun ordered_mass_map_equation ctxt map_function source expected child_theorems =
    let
      val natT = @{typ nat}
      val nat_listT = HOLogic.listT natT
      val map_function_ct = Thm.cterm_of ctxt map_function
      val nat_cons_ct = Thm.cterm_of ctxt
        (Const (@{const_name Cons}, natT --> nat_listT --> nat_listT))
      val map_nil = @{thm list.map(1)} RS @{thm eq_reflection}
      val map_cons = @{thm list.map(2)} RS @{thm eq_reflection}
      val map_request = Thm.apply map_function_ct (Thm.cterm_of ctxt source)
      fun map_spine current remaining =
        (case Thm.term_of current of
          Const (name, _) =>
            if name = @{const_name Nil} andalso null remaining then
              Conv.rewr_conv map_nil (Thm.apply map_function_ct current)
            else error "B1 mass map encountered a malformed list spine"
        | _ =>
            (case remaining of
              [] => error "B1 mass map ran out of child theorems"
            | child_theorem :: tail_theorems =>
                let
                  val (cons_head, tail) = Thm.dest_comb current
                  val (cons_ct, _) = Thm.dest_comb cons_head
                  val _ = (case Thm.term_of cons_ct of
                    Const (name, _) => if name = @{const_name Cons} then ()
                      else error "B1 mass map found a non-cons list spine"
                  | _ => error "B1 mass map found a malformed list spine")
                  val child_equation = child_theorem RS @{thm eq_reflection}
                  val tail_equation = map_spine tail tail_theorems
                  val map_equation = Conv.rewr_conv map_cons
                    (Thm.apply map_function_ct current)
                  val cons_head_equation = Thm.combination
                    (Thm.reflexive nat_cons_ct) child_equation
                  val target_cons_equation = Thm.combination
                    cons_head_equation tail_equation
                in Thm.transitive map_equation target_cons_equation end))
      val equation = map_spine (Thm.cterm_of ctxt source) child_theorems
      val lhs = Thm.term_of (Thm.lhs_of equation)
      val rhs = Thm.term_of (Thm.rhs_of equation)
      val _ = if lhs aconv Thm.term_of map_request andalso rhs aconv expected andalso
          Thm.nprems_of equation = 0 andalso null (Thm.hyps_of equation) andalso
          null (Thm.tpairs_of equation) andalso not (Term.is_open lhs) andalso
          not (Term.is_open rhs) then () else
        error "B1 mass map changed its ordered multiplicity"
    in equation end

  val make_annotation = Comma_Semantic_B1_Mass_Candidate.make_annotation
  val dependency_table = Comma_Semantic_B1_Mass_Candidate.dependency_table
  val make_annotation_and_cids =
    Comma_Semantic_B1_Mass_Candidate.make_annotation_and_cids
  val make_annotation_from_nodes =
    Comma_Semantic_B1_Mass_Candidate.make_annotation_from_nodes

  type source_binding = {
      base: int, extent: int, constant: term, definition: thm, interval: thm}

  (* One global validity proof over the sparse tree.  A source binding is a
     checked block definition paired with one universal DAG-to-block interval
     theorem.  Keeping only demanded bindings here avoids constructing one
     point lookup theorem per annotation row while retaining exact source
     authority and the original ordered child payloads. *)
  fun make_validity_prover ctxt node_count source_bindings root_data =
    let
      val prover_started = Time.now ()
      val natT = @{typ nat}
      val treeT = @{typ comma_semantic_b1_crt_mass_tree}
      val dagT = @{typ comma_semantic_b1_crt_column_dag}
      val blockT = @{typ comma_semantic_b1_crt_column_block}
      val lookupT = @{typ "(nat \<times> nat list) option"}
      val boolT = @{typ bool}
      val dag = @{term comma_semantic_b1_crt_column_node_dag}
      val dag_lookup = Const
        (@{const_name comma_semantic_b1_crt_column_dag_lookup},
          dagT --> natT --> lookupT)
      val block_lookup = Const
        (@{const_name comma_semantic_b1_crt_column_block_lookup},
          blockT --> natT --> lookupT)
      val valid = Const
        (@{const_name comma_semantic_b1_crt_column_mass_annotation_tree_valid},
          dagT --> natT --> treeT --> boolT)
      val thy = Proof_Context.theory_of ctxt
      val source_validation_started = Time.now ()
      fun closed term = not (Term.is_open term) andalso
        null (Term.add_frees term []) andalso null (Term.add_vars term [])
      fun source_rules ({base, extent, constant, definition, interval}: source_binding) =
        let
          val definition_left = Thm.term_of (Thm.lhs_of definition)
          val definition_right = Thm.term_of (Thm.rhs_of definition)
          val expected_definition = Logic.mk_equals (constant, definition_right)
          val cid = Bound 0
          val lower = HOLogic.mk_number natT base
          val upper = HOLogic.mk_number natT (base + extent)
          val interval_body = HOLogic.mk_imp
            (HOLogic.mk_conj
              (HOLogic.mk_binrel @{const_name less_eq} (lower, cid),
               Const (@{const_name less}, natT --> natT --> boolT) $ cid $ upper),
             HOLogic.mk_eq (dag_lookup $ dag $ cid,
               block_lookup $ constant $ cid))
          val expected_interval = HOLogic.mk_Trueprop
            (HOLogic.mk_all ("cid", natT, interval_body))
          val source_constant = (case constant of Const _ => true | _ => false)
          fun clean_in_context theorem =
            Thm.nprems_of theorem = 0 andalso null (Thm.hyps_of theorem) andalso
            null (Thm.tpairs_of theorem) andalso
            Context.subthy (Thm.theory_of_thm theorem, thy) andalso
            closed (Thm.prop_of theorem)
          val _ = if base >= 2 andalso extent > 0 andalso extent <= 512 then ()
            else error "B1 source binding has an invalid block interval"
          val _ = if source_constant andalso fastype_of constant = blockT andalso
              Thm.prop_of definition aconv expected_definition andalso
              definition_left aconv constant andalso fastype_of definition_right = blockT andalso
              clean_in_context definition then ()
            else error "B1 source binding has an unauthenticated block definition"
          val _ = if Thm.prop_of interval aconv expected_interval andalso
              clean_in_context interval then ()
            else error "B1 source binding has an unauthenticated interval theorem"
        in (definition, interval) end
      val source_pairs = map source_rules source_bindings
      val source_theorems = maps (fn (definition, interval) => [definition, interval])
        source_pairs
      val _ = if null (Thm_Deps.all_oracles source_theorems) then ()
        else error "B1 source binding bundle depends on an oracle"
      val _ = Comma_Proof_Profile.report
        ("B1 mass invariant validated-source-bindings-complete count=" ^
         Int.toString (length source_bindings) ^ " elapsed_ms=" ^
         Comma_Proof_Profile.elapsed_ms source_validation_started)
      val arithmetic_context = Comma_Entry_Arithmetic.natural_context ctxt
      val _ = Comma_Proof_Profile.report
        ("B1 mass invariant validity-prover-ready source-bindings=" ^
         Int.toString (length source_bindings) ^ " setup_ms=" ^
         Comma_Proof_Profile.elapsed_ms prover_started)
    in
      fn annotation =>
        let
          val started = Time.now ()
          val treeT = @{typ comma_semantic_b1_crt_mass_tree}
          val (published_tree, root_equation) =
            (case root_data of
              NONE =>
                let val tree_ct = Thm.cterm_of ctxt annotation
                in (annotation, Thm.reflexive tree_ct) end
            | SOME (authority, equation) => (authority, equation))
          val ordered = Const
            (@{const_name comma_semantic_b1_crt_mass_tree_ordered},
              natT --> natT --> treeT --> boolT)
          val rows = Const
            (@{const_name comma_semantic_b1_crt_mass_tree_rows_valid},
              dagT --> treeT --> treeT --> boolT)
          val _ = Comma_Proof_Profile.report
            ("B1 mass invariant validity-ordered-start elapsed_ms=" ^
             Comma_Proof_Profile.elapsed_ms started)
          val ordered_body_fact = Comma_Semantic_B1_Mass_Layout.make
            ctxt arithmetic_context node_count annotation
          val ordered_fun = Thm.combination
            (Thm.reflexive (Thm.cterm_of ctxt ordered))
            (Thm.reflexive (Thm.cterm_of ctxt (HOLogic.mk_number natT 2)))
          val ordered_prefix = Thm.combination ordered_fun
            (Thm.reflexive (Thm.cterm_of ctxt (HOLogic.mk_number natT node_count)))
          val ordered_transport = Thm.combination ordered_prefix root_equation
          val ordered_proposition = Thm.combination
            (Thm.reflexive (Thm.cterm_of ctxt @{term Trueprop})) ordered_transport
          val ordered_fact = Thm.equal_elim
            (Thm.symmetric ordered_proposition) ordered_body_fact
          val _ = Comma_Proof_Profile.report
            ("B1 mass invariant validity-ordered-complete elapsed_ms=" ^
             Comma_Proof_Profile.elapsed_ms started)
          val source_rows = Comma_Semantic_B1_Mass_Rows.source_row_provider
            ctxt arithmetic_context dag node_count source_bindings
          val rows_result = Comma_Semantic_B1_Mass_Rows.make
            {ctxt = ctxt, arithmetic_context = arithmetic_context, dag = dag,
             tree = annotation, tree_cterm = Thm.cterm_of ctxt annotation,
             published_tree = published_tree, root_equation = root_equation,
             ordered_fact = ordered_body_fact,
             node_count = node_count, source_row = #lookup source_rows}
          val rows_fact = #theorem rows_result
          val _ = if Thm.prop_of rows_fact aconv
              HOLogic.mk_Trueprop (rows $ dag $ published_tree $ published_tree) then () else
            error "B1 structural mass rows changed the exact tree-validity request"
          val _ = Comma_Proof_Profile.report
            ("B1 mass invariant validity-rows-complete elapsed_ms=" ^
             Comma_Proof_Profile.elapsed_ms started ^
             ((#counters source_rows) ()))
          val conjunction_fact = @{thm conjI} OF [ordered_fact, rows_fact]
          val target = valid $ dag $
            HOLogic.mk_number natT node_count $ published_tree
          val unfold = @{thm comma_semantic_b1_crt_column_mass_annotation_tree_valid_def}
            RS @{thm eq_reflection}
          val proposition_unfold = Thm.combination
            (Thm.reflexive (Thm.cterm_of ctxt @{term Trueprop}))
            (Conv.rewr_conv unfold (Thm.cterm_of ctxt target))
          val result = Thm.equal_elim
            (Thm.symmetric proposition_unfold) conjunction_fact
          val _ = if Thm.prop_of result aconv HOLogic.mk_Trueprop target then () else
            error "B1 mass invariant validity changed its exact tree authority"
          val _ = Comma_Proof_Profile.report
            ("B1 mass invariant validity-complete elapsed_ms=" ^
             Comma_Proof_Profile.elapsed_ms started)
        in (result, #lookup_fact rows_result) end
    end

  (* Exercise the source-binding trust boundary with real checked bindings.
     These failures happen before any catalogue-wide validity proof is run. *)
  fun check_source_binding_authority ctxt node_count source_bindings =
    let
      fun require condition message = if condition then () else error message
      fun expect_error expected label operation =
        (case Exn.capture operation () of
          Exn.Exn (ERROR message) =>
            if message = expected then ()
            else error (label ^ " failed for the wrong reason: " ^ message)
        | Exn.Exn exn => Exn.reraise exn
        | Exn.Res _ => error (label ^ " was unexpectedly accepted"))
      fun one_binding cids label =
        (case source_bindings cids of
          [binding] => binding
        | _ => error ("B1 source-binding fixture expected one " ^ label))
      val first = one_binding [2] "first block"
      val {base, extent, constant, definition, interval} = first
      val _ = require (base = 2 andalso extent > 1)
        "B1 source-binding fixture did not select the first block"
      val _ = make_validity_prover ctxt node_count [first] NONE
      val changed_base =
        {base = base + 1, extent = extent, constant = constant,
         definition = definition, interval = interval}: source_binding
      val _ = expect_error "B1 source binding has an unauthenticated interval theorem"
        "changed source-binding base" (fn () =>
          make_validity_prover ctxt node_count [changed_base] NONE)
      val changed_extent =
        {base = base, extent = extent - 1, constant = constant,
         definition = definition, interval = interval}: source_binding
      val _ = expect_error "B1 source binding has an unauthenticated interval theorem"
        "changed source-binding extent" (fn () =>
          make_validity_prover ctxt node_count [changed_extent] NONE)
      val second = one_binding [base + extent] "following block"
      val {definition = second_definition, interval = second_interval, ...} = second
      val changed_definition =
        {base = base, extent = extent, constant = constant,
         definition = second_definition, interval = interval}: source_binding
      val _ = expect_error "B1 source binding has an unauthenticated block definition"
        "foreign source block definition" (fn () =>
          make_validity_prover ctxt node_count [changed_definition] NONE)
      val changed_interval =
        {base = base, extent = extent, constant = constant,
         definition = definition, interval = second_interval}: source_binding
      val _ = expect_error "B1 source binding has an unauthenticated interval theorem"
        "foreign source block interval" (fn () =>
          make_validity_prover ctxt node_count [changed_interval] NONE)
    in () end

  fun make_soundness_prover ctxt certificate =
    Proof_Context.get_thm ctxt
      "comma_semantic_b1_crt_column_mass_annotation_tree_sound" OF [certificate]

  type mass_annotation_alias =
    Comma_Semantic_B1_Occurrence_Publication.mass_annotation

  val validate_mass_annotation_alias =
    Comma_Semantic_B1_Mass_Alias.validate

  type input = {
      certificate: thm,
      invariant: thm,
      annotation_body: term option,
      annotation_definition: thm option,
      node_count: int,
      column_value: int -> term,
      known_column: term -> bool,
      cache_limit: int
    }

  (* Only the checked producer below may supply a lookup provider.  Keeping
     this helper private excludes arbitrary theorem callbacks without rescanning
     an already checked proof DAG for oracles on every mass request. *)
  local
  fun make_with_lookup_provider ctxt cached_lookup
      ({certificate, invariant, annotation_body, annotation_definition,
        node_count, column_value, known_column, cache_limit}: input) =
    let
      val natT = @{typ nat}
      val columnT = @{typ comma_crt_column}
      val dagT = @{typ comma_semantic_b1_crt_column_dag}
      val annotationT = @{typ comma_semantic_b1_crt_mass_tree}
      val pairT = @{typ "nat \<times> nat"}
      val option_pairT = @{typ "(nat \<times> nat) option"}
      val boolT = @{typ bool}
      val thy = Proof_Context.theory_of ctxt
      val _ = if node_count >= 2 then () else
        error "B1 invariant mass certificate requires two terminal CIDs"
      val _ = if cache_limit >= 1 andalso cache_limit <= 8192 then () else
        error "B1 invariant mass certificate capacity must lie in 1..8192"

      val dag = Const
        (@{const_name comma_semantic_b1_crt_column_node_dag}, dagT)
      val column_at = Const
        (@{const_name comma_semantic_b1_crt_column_at},
          dagT --> natT --> columnT)
      val mass_const = Const
        (@{const_name comma_semantic_b1_crt_column_mass},
          columnT --> natT)
      val annotation_valid = Const
        (@{const_name comma_semantic_b1_crt_column_mass_annotation_tree_valid},
          dagT --> natT --> annotationT --> boolT)
      val annotation_lookup = Const
        (@{const_name comma_semantic_b1_crt_mass_tree_lookup},
          annotationT --> natT --> option_pairT)
      val number = HOLogic.mk_number natT
      val closed = fn t => not (Term.is_open t) andalso
        null (Term.add_frees t []) andalso null (Term.add_vars t [])
      val clean = fn th => Thm.nprems_of th = 0 andalso
        null (Thm.hyps_of th) andalso null (Thm.tpairs_of th) andalso
        Context.subthy (Thm.theory_of_thm th, thy)
      val oracle_free = fn th => null (Thm_Deps.all_oracles [th])

      fun dest_nat t =
        (case try HOLogic.dest_number t of
          SOME (typ, n) => if typ = natT andalso n >= 0 then n
            else error "B1 invariant mass certificate contains a non-natural numeral"
        | NONE => error "B1 invariant mass certificate requires closed natural numerals")

      fun prop th =
        (case try HOLogic.dest_Trueprop (Thm.prop_of th) of
          SOME p => p
        | NONE => error "B1 invariant mass certificate is not an object proposition")

      fun insert_row table (row as {cid, ...}: annotation_row) =
        if is_some (Inttab.lookup table cid) then
          error "B1 invariant annotation repeats a CID"
        else Inttab.update (cid, row) table

      fun tree_rows node table =
        (case strip_comb node of
          (Const (name, _), []) =>
            if name = @{const_name Comma_B1_CRT_Mass_Tree_Empty}
            then table
            else error "B1 invariant mass tree has an unknown leaf"
        | (Const (name, _), [key_term, level_term, mass_term, left, right]) =>
            if name = @{const_name Comma_B1_CRT_Mass_Tree_Node}
            then
              let
                val key = dest_nat key_term
                val level = dest_nat level_term
                val value = dest_nat mass_term
                val _ = if fastype_of node = annotationT andalso closed node then () else
                  error "B1 invariant mass tree is open or ill-typed"
                val left_table = tree_rows left table
                val right_table = tree_rows right left_table
              in insert_row right_table {cid = key, level = level, value = value} end
            else error "B1 invariant mass tree has an unknown constructor"
        | _ => error "B1 invariant mass tree has malformed shape")

      fun annotation_rows annotation =
        let
          val table = tree_rows annotation Inttab.empty
          val rows = map snd (Inttab.dest table)
        in
          if forall (fn {cid, ...} => cid >= 2 andalso cid < node_count) rows then
            (table, rows)
          else error "B1 invariant annotation has a foreign CID"
        end

      fun check_certificate () =
        let
          val p = prop certificate
          val (name, args) = (case strip_comb p of
            (Const (name, _), args) => (name, args)
          | _ => error "B1 invariant validity theorem has malformed proposition")
          val _ = if name = @{const_name comma_semantic_b1_crt_column_mass_annotation_tree_valid}
            then () else error "B1 invariant validity theorem has a foreign predicate"
          val _ = if length args = 3 then () else
            error "B1 invariant validity theorem has the wrong arity"
          val [dag_term, count_term, annotation_term] = args
          val _ = if dag_term aconv dag then () else
            error "B1 invariant validity theorem changed DAG authority"
          val _ = if dest_nat count_term = node_count then () else
            error "B1 invariant validity theorem changed node extent"
          val _ = if fastype_of annotation_term = annotationT andalso
              closed annotation_term then () else
            error "B1 invariant validity theorem has an open mass tree"
          val body =
            (case annotation_body of
              NONE => annotation_term
            | SOME candidate =>
                let
                  val _ = if fastype_of candidate = annotationT andalso
                      closed candidate then () else
                    error "B1 invariant annotation body is open or ill-typed"
                in candidate end)
          val (rows_by_cid, rows) = annotation_rows body
          val expected = annotation_valid $ dag $ number node_count $ annotation_term
          val _ = if p aconv expected then () else
            error "B1 invariant validity theorem changed its exact annotation request"
          val _ = if clean certificate andalso oracle_free certificate then () else
            error "B1 invariant validity theorem is not a clean oracle-free theorem"
        in (annotation_term, rows_by_cid, rows) end

      fun expected_invariant annotation_term =
        let
          val cid = Bound 2
          val level = Bound 1
          val value = Bound 0
          val some = Const (@{const_name Some}, pairT --> option_pairT)
          val pair = Const (@{const_name Pair}, natT --> natT --> pairT)
          val result = some $ (pair $ level $ value)
          val request = annotation_lookup $ annotation_term $ cid
          val antecedent = HOLogic.mk_eq (request, result)
          val lhs = mass_const $ (column_at $ dag $ cid)
          val admitted_const = Const (@{const_name comma_crt_admitted},
            natT --> columnT --> boolT)
          val admitted = admitted_const $ number 0 $ (column_at $ dag $ cid)
          val conclusion = HOLogic.mk_conj (admitted, HOLogic.mk_eq (lhs, value))
          val body = HOLogic.mk_imp (antecedent, conclusion)
          val all_value = HOLogic.mk_all ("mass", natT, body)
          val all_level = HOLogic.mk_all ("level", natT, all_value)
        in HOLogic.mk_all ("cid", natT, all_level) end

      fun check_invariant annotation_term =
        let
          val p = prop invariant
          val expected = expected_invariant annotation_term
          val _ = if p aconv expected then () else
            error "B1 invariant soundness theorem changed its exact universal contract"
          val _ = if clean invariant andalso oracle_free invariant then () else
            error "B1 invariant soundness theorem is not a clean oracle-free theorem"
        in () end

      val (annotation_term, rows_by_cid, rows) = check_certificate ()
      val _ = check_invariant annotation_term
      (* Certify the shared search-tree operand once.  Per-CID lookup proofs
         descend using certified child cterms rather than recertifying the
         full candidate tree. *)
      val annotation_ct = Thm.cterm_of ctxt annotation_term
      val annotation_body_ct = Option.map (Thm.cterm_of ctxt) annotation_body
      val annotation_lookup_ct = Thm.cterm_of ctxt annotation_lookup
      val lookup_arithmetic_context = Comma_Entry_Arithmetic.natural_context ctxt

      val facts = Synchronized.var "semantic_b1_mass_invariant_facts"
        (Inttab.empty: mass_entry Inttab.table)
      val gate = Synchronized.var "semantic_b1_mass_invariant_gate" ()
      val lookups = Synchronized.var "semantic_b1_mass_invariant_lookups" 0
      val hits = Synchronized.var "semantic_b1_mass_invariant_hits" 0
      val misses = Synchronized.var "semantic_b1_mass_invariant_misses" 0
      val races = Synchronized.var "semantic_b1_mass_invariant_races" 0
      val refusals = Synchronized.var "semantic_b1_mass_invariant_refusals" 0
      val specialized = Synchronized.var "semantic_b1_mass_invariant_specialized" 0
      val lookup_fact_reuses = Synchronized.var "semantic_b1_mass_invariant_lookup_fact_reuses" 0

      fun add counter n = Synchronized.change counter (fn old => old + n)
      fun read counter = Synchronized.value counter

      fun checked_column cid =
        let
          val _ = if cid >= 0 andalso cid < node_count then () else
            error "B1 invariant mass request has a foreign CID"
          val term = column_value cid
          val _ = if fastype_of term = columnT andalso closed term then () else
            error "B1 invariant mass callback returned an open or ill-typed column"
          val expected = column_at $ dag $ number cid
          val _ = if term aconv expected andalso known_column term then () else
            error "B1 invariant mass callback returned a foreign DAG column"
        in term end

      fun mk_mass_eq cid value = HOLogic.mk_Trueprop
        (HOLogic.mk_eq (mass_const $ (column_at $ dag $ number cid), number value))

      fun specialize cid level value =
        let
          val request = mk_mass_eq cid value
          val lookup = annotation_lookup $ annotation_term $ number cid
          val pair = Const (@{const_name Pair}, natT --> natT --> pairT)
          val expected_lookup = Const (@{const_name Some}, pairT --> option_pairT) $
            (pair $ number level $ number value)
          val (lookup_equation, reused_cached_lookup) =
            (case cached_lookup of
              SOME lookup_fact => (lookup_fact cid, true)
            | NONE => ((case annotation_definition of
              NONE => Comma_Semantic_B1_Mass_Rows.lookup_equation
                ctxt lookup_arithmetic_context annotation_term annotation_ct
                  annotation_lookup_ct cid
            | SOME definition =>
                let
                  val body_ct = (case annotation_body_ct of
                    SOME candidate => candidate
                  | NONE => error "B1 invariant alias is missing its body")
                  val body = Thm.term_of body_ct
                  val body_equation = Comma_Semantic_B1_Mass_Rows.lookup_equation
                    ctxt lookup_arithmetic_context body body_ct annotation_lookup_ct cid
                  val alias_request = annotation_lookup $ annotation_term $ number cid
                  val body_request = annotation_lookup $ body $ number cid
                  val alias_to_body = Conv.fun_conv
                    (Conv.arg_conv (Conv.rewr_conv definition))
                    (Thm.cterm_of ctxt alias_request)
                  val _ = if Thm.term_of (Thm.lhs_of alias_to_body) aconv alias_request andalso
                      Thm.term_of (Thm.rhs_of alias_to_body) aconv body_request then () else
                    error "B1 invariant alias lookup did not expose its exact body"
                in Thm.transitive alias_to_body body_equation end), false))
          val lookup_fact = lookup_equation RS @{thm meta_eq_to_obj_eq}
          val expected_lookup_fact = HOLogic.mk_Trueprop
            (HOLogic.mk_eq (lookup, expected_lookup))
          val _ = if Thm.prop_of lookup_fact aconv expected_lookup_fact then () else
            error "B1 invariant path lookup changed its exact annotation result"
          val _ = if clean lookup_fact then () else
            error "B1 invariant path lookup is not a closed theorem in this context"
          val _ = if reused_cached_lookup then add lookup_fact_reuses 1 else ()
          val spec_cid = Drule.infer_instantiate ctxt
            [( ("x", 0), Thm.cterm_of ctxt (number cid))] @{thm spec}
          val by_cid = spec_cid OF [invariant]
          val spec_level = Drule.infer_instantiate ctxt
            [( ("x", 0), Thm.cterm_of ctxt (number level))] @{thm spec}
          val by_level = spec_level OF [by_cid]
          val spec_value = Drule.infer_instantiate ctxt
            [( ("x", 0), Thm.cterm_of ctxt (number value))] @{thm spec}
          val implication = spec_value OF [by_level]
          val full_theorem = @{thm mp} OF [implication, lookup_fact]
          val theorem = full_theorem RS @{thm conjunct2}
          val _ = if Thm.prop_of theorem aconv request andalso clean theorem then () else
            error "B1 invariant specialization changed its exact mass request"
        in {value = value, theorem = theorem}: mass_entry end

      fun mass cid =
        let
          val _ = checked_column cid
          val _ = add lookups 1
        in
          case Inttab.lookup (Synchronized.value facts) cid of
            SOME entry => (add hits 1; entry)
          | NONE =>
              let
                val _ = add misses 1
                val {level, value, ...} = (case Inttab.lookup rows_by_cid cid of
                  SOME row => row
                | NONE => error
                    "B1 invariant mass certificate does not cover requested CID")
                val result = Synchronized.change_result gate (fn () =>
                  let
                    val table = Synchronized.value facts
                  in
                    case Inttab.lookup table cid of
                      SOME existing => (add races 1; (existing, ()))
                    | NONE =>
                        let
                          val made = specialize cid level value
                          val _ = add specialized 1
                          val _ = if Inttab.size table < cache_limit then () else
                            add refusals 1
                          val _ = if Inttab.size table < cache_limit then
                            Synchronized.change facts (Inttab.update (cid, made))
                            else ()
                        in (made, ()) end
                  end)
              in result end
        end

      val terminal_facts = Synchronized.var "semantic_b1_mass_invariant_terminals"
        (Inttab.empty: mass_entry Inttab.table)
      val terminal_gate = Synchronized.var "semantic_b1_mass_invariant_terminal_gate" ()
      fun terminal cid =
        let
          val _ = checked_column cid
          val value = if cid = 0 then 0 else if cid = 1 then 924 else
            error "B1 invariant terminal helper received a nonterminal CID"
        in
          case Inttab.lookup (Synchronized.value terminal_facts) cid of
            SOME entry => entry
          | NONE => Synchronized.change_result terminal_gate (fn () =>
              case Inttab.lookup (Synchronized.value terminal_facts) cid of
                SOME entry => (entry, ())
              | NONE =>
                  let
                    val request = mk_mass_eq cid value
                    val terminal_context = put_simpset HOL_basic_ss ctxt addsimps
                      @{thms comma_semantic_b1_crt_column_at_false
                        comma_semantic_b1_crt_column_at_true
                        comma_semantic_b1_crt_column_mass.simps if_True if_False}
                    val theorem = Goal.prove ctxt [] [] request
                      (fn _ => simp_tac terminal_context 1)
                    val _ = if Thm.prop_of theorem aconv request andalso
                        clean theorem andalso oracle_free theorem then ()
                      else error
                        "B1 invariant terminal mass theorem changed its exact request"
                    val entry = {value = value, theorem = theorem}: mass_entry
                    val _ = Synchronized.change terminal_facts
                      (Inttab.update (cid, entry))
                  in (entry, ()) end)
        end

      fun mass_entry cid = if cid < 2 then terminal cid else mass cid

      (* Exact ordered row transport.  This is intentionally a small map-spine
         proof over the requested CIDs; it uses only the already-specialized
         invariant facts and never opens the source DAG or invokes column_step. *)
      val row_cache = Synchronized.var "semantic_b1_mass_invariant_rows"
        (Termtab.empty: ({equation: thm, values: int list}) Termtab.table)
      val row_gate = Synchronized.var "semantic_b1_mass_invariant_row_gate" ()
      val row_hits = Synchronized.var "semantic_b1_mass_invariant_row_hits" 0
      val row_misses = Synchronized.var "semantic_b1_mass_invariant_row_misses" 0
      val row_refusals = Synchronized.var "semantic_b1_mass_invariant_row_refusals" 0
      val map_mass = Const (@{const_name map},
        (columnT --> natT) --> HOLogic.listT columnT --> HOLogic.listT natT) $ mass_const
      fun mass_row ids =
        let
          val ids_term = HOLogic.mk_list natT (map number ids)
          val key = ids_term
          val _ = if forall (fn cid => cid >= 0 andalso cid < node_count) ids
            then () else error "B1 invariant mass row contains a foreign CID"
        in
          case Termtab.lookup (Synchronized.value row_cache) key of
            SOME result => (add row_hits 1; result)
          | NONE =>
              Synchronized.change_result row_gate (fn () =>
                case Termtab.lookup (Synchronized.value row_cache) key of
                  SOME result => (add row_hits 1; (result, ()))
                | NONE =>
                  let
                    val _ = add row_misses 1
                val entries = map mass_entry ids
                val columns = map (fn cid => column_at $ dag $ number cid) ids
                val source = HOLogic.mk_list columnT columns
                val expected = HOLogic.mk_list natT (map (number o #value) entries)
                val equation = ordered_mass_map_equation ctxt map_mass source expected
                  (map #theorem entries)
                val _ = if clean equation then () else
                  error "B1 invariant mass row changed ordered authority"
                    val result = {equation = equation, values = map #value entries}
                    val _ = if Termtab.size (Synchronized.value row_cache) < cache_limit then
                        Synchronized.change row_cache (Termtab.update (key, result))
                      else Synchronized.change row_refusals (fn old => old + 1)
                  in (result, ()) end)
        end

      fun stats () =
        "column_mass_invariant_lookups=" ^ Int.toString (read lookups) ^
        " column_mass_invariant_hits=" ^ Int.toString (read hits) ^
        " column_mass_invariant_misses=" ^ Int.toString (read misses) ^
        " column_mass_invariant_specialized=" ^ Int.toString (read specialized) ^
        " column_mass_invariant_cached_lookup_reuses=" ^
          Int.toString (read lookup_fact_reuses) ^
        " column_mass_invariant_races=" ^ Int.toString (read races) ^
        " column_mass_invariant_refusals=" ^ Int.toString (read refusals) ^
        " column_mass_invariant_rows=" ^ Int.toString (length rows) ^
        " column_mass_invariant_row_cache=" ^
          Int.toString (Termtab.size (Synchronized.value row_cache)) ^
        " column_mass_invariant_row_hits=" ^ Int.toString (read row_hits) ^
        " column_mass_invariant_row_misses=" ^ Int.toString (read row_misses) ^
        " column_mass_invariant_row_refusals=" ^
          Int.toString (Synchronized.value row_refusals)
    in
      {mass = (fn cid => #theorem (mass_entry cid)),
       mass_value = (fn cid => #value (mass_entry cid)),
       certificate = certificate,
       invariant = invariant,
       annotation = annotation_term,
       mass_row = mass_row,
       stats = stats}
    end

  in
  (* Preserve the direct certificate API used by small callers and fixtures.
     The production constructor supplies the immutable lookup provider built
     by the same rows proof that established the certificate. *)
  fun make ctxt input = make_with_lookup_provider ctxt NONE input

  type checked_producer_input = {
      node_count: int,
      period: int -> int,
      roots: int list,
      get_node: int -> node_row option,
      source_bindings: int list -> source_binding list,
      column_value: int -> term,
      known_column: term -> bool,
      cache_limit: int,
      annotation_alias: mass_annotation_alias option
    }

  (* Concrete producer boundary used by the occurrence publisher.  It creates
     the sparse candidate, obtains authenticated universal source bindings for
     its exact closure, then proves validity and soundness before returning the
     mass owner. *)
  fun make_from_nodes ctxt
      ({node_count, period, roots, get_node, source_bindings, column_value,
        known_column, cache_limit, annotation_alias}: checked_producer_input) =
    let
      val started = Time.now ()
      val (annotation, annotation_body, alias_definition, cids, alias_roots) =
        (case annotation_alias of
          NONE =>
            let
              val (candidate, candidate_cids) =
                make_annotation_and_cids node_count period roots get_node
            in (candidate, candidate, NONE, candidate_cids, roots) end
        | SOME alias =>
            let
              val (constant, body, definition, alias_cids, alias_roots) =
                validate_mass_annotation_alias ctxt node_count alias
            in (constant, body, SOME definition, alias_cids, alias_roots) end)
      val _ = if alias_roots = roots then () else
        error "B1 mass annotation alias demanded roots changed at the consumer boundary"
      val _ = (case annotation_alias of
        NONE => ()
      | SOME alias => Comma_Semantic_B1_Mass_Alias.check_fixtures
          ctxt node_count alias)
      val _ = Comma_Proof_Profile.report
        ("B1 mass invariant candidate closure=" ^ Int.toString (length cids) ^
         " elapsed_ms=" ^ Comma_Proof_Profile.elapsed_ms started)
      val bindings = source_bindings cids
      val _ = Comma_Proof_Profile.report
        ("B1 mass invariant source-bindings=" ^ Int.toString (length bindings) ^
         " elapsed_ms=" ^ Comma_Proof_Profile.elapsed_ms started)
      val validity_tree_authority = Option.map
        (fn definition => (annotation, definition)) alias_definition
      val prove_valid = make_validity_prover ctxt node_count bindings
        validity_tree_authority
      val (certificate, cached_lookup) = prove_valid annotation_body
      val _ = Comma_Proof_Profile.report
        ("B1 mass invariant validity-complete elapsed_ms=" ^
         Comma_Proof_Profile.elapsed_ms started)
      val invariant = make_soundness_prover ctxt certificate
      val _ = Comma_Proof_Profile.report
        ("B1 mass invariant soundness-complete elapsed_ms=" ^
         Comma_Proof_Profile.elapsed_ms started)
      val owner = make_with_lookup_provider ctxt (SOME cached_lookup)
        {certificate = certificate, invariant = invariant,
         annotation_body = SOME annotation_body,
         annotation_definition = alias_definition,
         node_count = node_count, column_value = column_value,
         known_column = known_column, cache_limit = cache_limit}
      val _ = (case (annotation_alias, cids) of
        (SOME _, cid :: _) => ((#mass owner) cid; ())
      | _ => ())
    in owner
    end
  end
end
