(* Proof-producing cardinality cache for the closed B1 column catalogue.
   The occurrence publisher supplies the catalogue authority and shared
   admission checker; each cached fact remains local to that proof context. *)
structure Comma_Semantic_B1_Column_Mass =
struct
  (* One-shot annotated-DAG owner.  The legacy step cache below remains
     available for its existing fixtures, while the live publisher uses this
     checked sparse invariant endpoint. *)
  fun make_invariant ctxt input =
    Comma_Semantic_B1_Column_Mass_Invariant.make ctxt input
  val make_annotation = Comma_Semantic_B1_Column_Mass_Invariant.make_annotation
  val make_annotation_from_nodes =
    Comma_Semantic_B1_Column_Mass_Invariant.make_annotation_from_nodes
  val make_from_nodes =
    Comma_Semantic_B1_Column_Mass_Invariant.make_from_nodes

  datatype shape =
      Bool_Shape of bool
    | Node_Shape of {level: int, children: int list}

  type mass_entry = {value: int, theorem: thm}
  type schema_entry = {value: int, theorem: thm, owner: term}

  fun make ctxt
      {column_value, step, known_column, node_count, prove_admitted,
       cache_limit} =
    let
      val natT = @{typ nat}
      val columnT = @{typ comma_crt_column}
      val boolT = @{typ bool}
      val dagT = @{typ comma_semantic_b1_crt_column_dag}
      val setT = HOLogic.mk_setT natT
      val thy = Proof_Context.theory_of ctxt
      val _ = if node_count >= 2 then () else
        error "B1 mass cache requires at least the two terminal CIDs"
      val _ = if cache_limit >= 1 andalso cache_limit <= 8192 then () else
        error "B1 mass cache capacity must lie in 1..8192"

      val mass_const = Const (@{const_name comma_semantic_b1_crt_column_mass},
        columnT --> natT)
      val admitted_const = Const (@{const_name comma_crt_admitted},
        natT --> columnT --> boolT)
      val set_const = Const (@{const_name comma_crt_set}, columnT --> setT)
      val card_const = Const (@{const_name card}, setT --> natT)
      val column_at_name = @{const_name comma_semantic_b1_crt_column_at}
      val bool_name = @{const_name Comma_CRT_Bool}
      val node_name = @{const_name Comma_CRT_Node}
      val expected_dag = Const
        (@{const_name comma_semantic_b1_crt_column_node_dag}, dagT)
      val column_at_const = Const (@{const_name comma_semantic_b1_crt_column_at},
        dagT --> natT --> columnT)

      val periods = Vector.fromList [4, 3, 7, 11]
      val max_depth = 5

      fun number n = HOLogic.mk_number natT n
      fun closed term = not (Term.is_open term) andalso
        null (Term.add_frees term []) andalso null (Term.add_vars term [])
      fun clean theorem = Thm.nprems_of theorem = 0 andalso
        null (Thm.hyps_of theorem) andalso null (Thm.tpairs_of theorem)
      fun theorem_in_context theorem =
        Context.subthy (Thm.theory_of_thm theorem, thy)
      fun require_depth depth =
        if depth <= max_depth then () else
          error "B1 mass cache encountered a DAG deeper than four CRT levels"
      fun require_cid cid =
        if cid >= 0 andalso cid < node_count then () else
          error "B1 mass cache received a foreign CID"
      fun dest_nat term =
        (case try HOLogic.dest_number term of
          SOME (typ, value) =>
            if typ = natT andalso value >= 0 then value
            else error "B1 mass cache encountered a non-natural numeral"
        | NONE => error "B1 mass cache requires a closed natural numeral")

      fun expected_column cid = column_at_const $ expected_dag $ number cid

      fun checked_column cid =
        let
          val _ = require_cid cid
          val term = column_value cid
          val _ = if fastype_of term = columnT andalso closed term then () else
            error "B1 mass cache column callback returned a non-closed column"
          val _ = if term aconv expected_column cid then () else
            error "B1 mass cache column callback returned a foreign DAG column"
          val _ = if known_column term then () else
            error "B1 mass cache column callback returned a foreign column"
        in term end

      fun child_id parent term =
        (case strip_comb term of
          (Const (name, _), [dag, cid_term]) =>
            if name = column_at_name andalso fastype_of term = columnT andalso
                fastype_of dag = @{typ comma_semantic_b1_crt_column_dag}
            then
              let
                val cid = dest_nat cid_term
                val expected = checked_column cid
                val _ = if term aconv expected then () else
                  error "B1 mass cache child column changed its authority"
                val _ = if cid < parent then () else
                  error "B1 mass cache child CID is not a strict DAG predecessor"
              in cid end
            else error "B1 mass cache node contains a foreign child column"
        | _ => error "B1 mass cache node contains a malformed child column")

      fun parse_shape cid body =
        (case strip_comb body of
          (Const (name, _), [value]) =>
            if name = bool_name andalso fastype_of body = columnT andalso
                fastype_of value = boolT
            then
              if value aconv @{term True} then Bool_Shape true
              else if value aconv @{term False} then Bool_Shape false
              else error "B1 mass cache Boolean body is not literal"
            else error "B1 mass cache column body is not a Boolean column"
        | (Const (name, _), [level_term, children_term]) =>
            if name = node_name andalso fastype_of body = columnT then
              let
                val level = dest_nat level_term
                val _ = if level < Vector.length periods then () else
                  error "B1 mass cache node has an invalid CRT level"
                val children =
                  (HOLogic.dest_list children_term handle TERM _ =>
                    error "B1 mass cache node has a malformed child list")
                val _ = if length children = Vector.sub (periods, level) then () else
                  error "B1 mass cache node has an invalid radix width"
                val child_ids = map (child_id cid) children
              in Node_Shape {level = level, children = child_ids} end
            else error "B1 mass cache column body is not a CRT node"
        | _ => error "B1 mass cache column body has an unknown constructor")

      val mass_facts = Synchronized.var "semantic_b1_mass_facts"
        (Termtab.empty: mass_entry Termtab.table)
      val step_gate = Synchronized.var "semantic_b1_mass_step_gate" ()
      val certify_gate = Synchronized.var "semantic_b1_mass_certify_gate" ()
      val (certify, certification_stats) =
        Comma_Entry_Arithmetic.make_certifier ctxt

      val lookups = Synchronized.var "semantic_b1_mass_lookups" 0
      val hits = Synchronized.var "semantic_b1_mass_hits" 0
      val misses = Synchronized.var "semantic_b1_mass_misses" 0
      val step_opens = Synchronized.var "semantic_b1_mass_step_opens" 0
      val races = Synchronized.var "semantic_b1_mass_races" 0
      val refusals = Synchronized.var "semantic_b1_mass_refusals" 0
      val malformed = Synchronized.var "semantic_b1_mass_malformed" 0
      val mass_proofs = Synchronized.var "semantic_b1_mass_proofs" 0
      val admission_calls = Synchronized.var "semantic_b1_mass_admission_calls" 0
      val card_proofs = Synchronized.var "semantic_b1_mass_card_proofs" 0
      val schema_lookups = Synchronized.var "semantic_b1_mass_schema_lookups" 0
      val schema_hits = Synchronized.var "semantic_b1_mass_schema_hits" 0
      val schema_misses = Synchronized.var "semantic_b1_mass_schema_misses" 0
      val schema_distinct_owner_hits =
        Synchronized.var "semantic_b1_mass_schema_distinct_owner_hits" 0
      val schema_same_owner_hits =
        Synchronized.var "semantic_b1_mass_schema_same_owner_hits" 0
      val schema_proofs = Synchronized.var "semantic_b1_mass_schema_proofs" 0
      val schema_refusals = Synchronized.var "semantic_b1_mass_schema_refusals" 0
      val schema_fixture_runs = Synchronized.var "semantic_b1_mass_schema_fixture_runs" 0
      val schema_fixture_cross_owner_hits =
        Synchronized.var "semantic_b1_mass_schema_fixture_cross_owner_hits" 0
      val step_ms = Synchronized.var "semantic_b1_mass_step_ms" (0: LargeInt.int)
      val mass_ms = Synchronized.var "semantic_b1_mass_mass_ms" (0: LargeInt.int)
      val admission_ms =
        Synchronized.var "semantic_b1_mass_admission_ms" (0: LargeInt.int)
      val card_ms = Synchronized.var "semantic_b1_mass_card_ms" (0: LargeInt.int)
      val schema_ms = Synchronized.var "semantic_b1_mass_schema_ms" (0: LargeInt.int)

      fun add counter amount = Synchronized.change counter (fn value => value + amount)
      fun read counter = Synchronized.value counter
      fun timed timer work =
        let
          val started = Time.now ()
          val result = Exn.capture work ()
          val elapsed = Time.toMilliseconds (Time.- (Time.now (), started))
          val _ = add timer elapsed
        in Exn.release result end

      fun certify_theorem theorem =
        Synchronized.change_result certify_gate (fn () =>
          let val checked = certify theorem in (checked, ()) end)

      fun reject message = (add malformed 1; error message)

      fun check_equation label request theorem =
        let
          val left = Thm.term_of (Thm.lhs_of theorem)
          val right = Thm.term_of (Thm.rhs_of theorem)
          val _ = if left aconv request then () else
            reject ("B1 mass cache " ^ label ^ " changed its request")
          val _ = if fastype_of left = fastype_of right andalso
              fastype_of left = columnT andalso closed left andalso closed right andalso
              clean theorem andalso theorem_in_context theorem then () else
            reject ("B1 mass cache " ^ label ^
              " is not a closed column equation")
        in theorem end

      fun step_data cid =
        let
          val request = checked_column cid
          val _ = add step_opens 1
          val (theorem, shape) =
            Synchronized.change_result step_gate (fn () =>
              let
                val theorem = timed step_ms (fn () => step cid)
                val theorem = check_equation "column step" request theorem
                val body = Thm.term_of (Thm.rhs_of theorem)
                val shape = parse_shape cid body
              in ((theorem, shape), ()) end)
        in (theorem, shape) end

      fun cache_lookup cache request =
        let
          val _ = add lookups 1
        in
          (case Termtab.lookup (Synchronized.value cache) request of
            SOME entry => (add hits 1; SOME entry)
          | NONE => (add misses 1; NONE))
        end

      fun publish cache request entry =
        Synchronized.change_result cache (fn table =>
          (case Termtab.lookup table request of
            SOME existing => (add races 1; (existing, table))
          | NONE =>
              if Termtab.size table < cache_limit then
                (entry, Termtab.update (request, entry) table)
              else (add refusals 1; (entry, table))))

      fun shape_period level = Vector.sub (periods, level)
      fun mass_request cid = mass_const $ checked_column cid
      fun admission_request lower cid =
        admitted_const $ number lower $ checked_column cid
      fun card_request cid = card_const $ (set_const $ checked_column cid)

      fun check_mass theorem request value =
        let
          val expected = HOLogic.mk_Trueprop
            (HOLogic.mk_eq (request, number value))
          val _ = if Thm.prop_of theorem aconv expected andalso clean theorem andalso
              theorem_in_context theorem then () else
            reject "B1 mass theorem has a mismatched exact numeral"
        in theorem end

      fun check_admission theorem request =
        let
          val expected = HOLogic.mk_Trueprop request
          val _ = if Thm.prop_of theorem aconv expected andalso clean theorem andalso
              theorem_in_context theorem then () else
            reject "B1 admission theorem has a mismatched exact request"
        in theorem end

      fun check_card theorem request value =
        let
          val expected = HOLogic.mk_Trueprop
            (HOLogic.mk_eq (request, number value))
          val _ = if Thm.prop_of theorem aconv expected andalso clean theorem andalso
              theorem_in_context theorem then () else
            reject "B1 cardinality theorem has a mismatched exact numeral"
        in theorem end

      val mass_context = Comma_Entry_Arithmetic.natural_context ctxt addsimps
        @{thms comma_semantic_b1_crt_column_mass.simps comma_crt_period_def
          list.map list.size nth_Cons' sum_list.Cons sum_list.Nil}
      val mass_schema_context = Comma_Entry_Arithmetic.natural_context ctxt addsimps
        @{thms comma_crt_period_def nth_Cons' sum_list.Cons sum_list.Nil}
      val mass_function = Thm.reflexive (Thm.cterm_of ctxt mass_const)
      val map_const = Const (@{const_name map}, (columnT --> natT) -->
        HOLogic.listT columnT --> HOLogic.listT natT)
      val map_function = map_const $ mass_const
      val sum_list_const = Const (@{const_name sum_list}, HOLogic.listT natT --> natT)
      val divide_const = Const (@{const_name divide}, natT --> natT --> natT)
      val period_const = Const (@{const_name comma_crt_period}, natT --> natT)
      val schema_cache = Synchronized.var "semantic_b1_mass_schema_facts"
        (Termtab.empty: schema_entry Termtab.table)
      val schema_gate = Synchronized.var "semantic_b1_mass_schema_gate" ()
      val schema_fixture_done = Unsynchronized.ref false

      fun checked_mass_map child_columns child_entries =
        let
          val _ = if length child_columns = length child_entries then () else
            reject "B1 mass map has a mismatched child extent"
          val _ = ListPair.appEq (fn (column, entry) =>
            (check_mass (#theorem entry) (mass_const $ column) (#value entry); ()))
            (child_columns, child_entries)
          val source = HOLogic.mk_list columnT child_columns
          val expected = HOLogic.mk_list natT (map (number o #value) child_entries)
          val equation =
            Comma_Semantic_B1_Column_Mass_Invariant.ordered_mass_map_equation
              ctxt map_function source expected (map #theorem child_entries)
          val lhs = Thm.term_of (Thm.lhs_of equation)
          val rhs = Thm.term_of (Thm.rhs_of equation)
          val _ = if clean equation andalso closed lhs andalso closed rhs then () else
            reject "B1 child mass map changed its ordered multiplicity"
        in equation end

      fun schema_key level values =
        HOLogic.mk_prod (number level, HOLogic.mk_list natT (map number values))

      fun schema_request level values value =
        HOLogic.mk_eq
          (divide_const $ (sum_list_const $ HOLogic.mk_list natT (map number values)) $
              (period_const $ number level), number value)

      fun check_schema theorem request =
        let val expected = HOLogic.mk_Trueprop request in
          if Thm.prop_of theorem aconv expected andalso clean theorem andalso
              theorem_in_context theorem andalso closed expected then theorem
          else reject "B1 arithmetic mass schema changed its exact numeral vector"
        end

      fun numeric_schema level values value owner =
        let
          val _ = if level >= 0 andalso level < Vector.length periods andalso
              length values = shape_period level andalso forall (fn n => n >= 0) values andalso
              fold (fn n => fn total => n + total) values 0 div
                shape_period level = value then () else
            reject "B1 arithmetic mass schema has an invalid level/vector"
          val key = schema_key level values
          val request = schema_request level values value
          val _ = add schema_lookups 1
        in
          Synchronized.change_result schema_gate (fn () =>
            let val table = Synchronized.value schema_cache in
              (case Termtab.lookup table key of
                SOME entry =>
                  let
                    val _ = if #value entry = value then () else
                      reject "B1 arithmetic schema reused another quotient"
                    val _ = check_schema (#theorem entry) request
                    val _ = add schema_hits 1
                    val _ = if #owner entry aconv owner then
                        add schema_same_owner_hits 1
                      else add schema_distinct_owner_hits 1
                  in (entry, ()) end
              | NONE =>
                  let
                    val _ = add schema_misses 1
                    val goal = HOLogic.mk_Trueprop request
                    val theorem = timed schema_ms (fn () =>
                      Goal.prove ctxt [] [] goal
                        (fn _ => simp_tac mass_schema_context 1))
                    val theorem = check_schema theorem request
                    val _ = add schema_proofs 1
                    val entry = {value = value, theorem = theorem, owner = owner}: schema_entry
                    val _ = if Termtab.size table < cache_limit then
                        Synchronized.change schema_cache
                          (Termtab.update (key, entry))
                      else add schema_refusals 1
                  in (entry, ()) end)
            end)
        end

      fun prove_mass depth cid =
        let
          val _ = require_depth depth
          val request = mass_request cid
        in
          (case cache_lookup mass_facts request of
            SOME entry => entry
          | NONE =>
              let
                val (step_theorem, shape) = step_data cid
                val (value, child_entries) =
                  (case shape of
                    Bool_Shape truth => ((if truth then 924 else 0), [])
                  | Node_Shape {level, children} =>
                      let
                        val child_entries = map (prove_mass (depth + 1)) children
                        val total = fold (fn entry => fn sum =>
                          #value entry + sum) child_entries 0
                        val value = total div shape_period level
                      in (value, child_entries) end)
                (* Charge only this node's local kernel proof and its exact
                   closed-term audit.  Recursive child work is timed by each
                   child entry and must not be counted again at every parent. *)
                val theorem = timed mass_ms (fn () =>
                  let
                    val theorem =
                      (case shape of
                        Bool_Shape _ =>
                          let
                            val mass_application = Thm.combination mass_function step_theorem
                            val body_equation = Simplifier.rewrite mass_context
                              (Thm.rhs_of mass_application)
                            val meta_equation = Thm.transitive mass_application body_equation
                          in meta_equation RS @{thm meta_eq_to_obj_eq} end
                      | Node_Shape {level, children} =>
                          let
                            val child_columns = map checked_column children
                            val map_equation = checked_mass_map child_columns child_entries
                            val step_object = step_theorem RS @{thm meta_eq_to_obj_eq}
                            val map_object = map_equation RS @{thm meta_eq_to_obj_eq}
                            val mass_step = @{thm comma_semantic_b1_crt_column_mass_step}
                              OF [step_object, map_object]
                            val expected_mass_step = HOLogic.mk_Trueprop
                              (HOLogic.mk_eq (request,
                                  divide_const $ (sum_list_const $ HOLogic.mk_list natT
                                    (map number (map #value child_entries))) $
                                    (period_const $ number level)))
                            val _ = if Thm.prop_of mass_step aconv expected_mass_step then () else
                              reject "B1 generic mass step changed its exact parent request"
                            val schema = numeric_schema level
                              (map #value child_entries) value request
                          in @{thm trans} OF [mass_step, #theorem schema] end)
                    val theorem = check_mass theorem request value
                    val theorem = certify_theorem theorem
                    val _ = add mass_proofs 1
                    val _ = if read mass_proofs mod 512 = 0 then
                      Comma_Proof_Profile.report
                        ("B1 column mass checkpoint proofs=" ^ Int.toString (read mass_proofs) ^
                          " hits=" ^ Int.toString (read hits) ^
                          " retained=" ^ Int.toString
                            (Termtab.size (Synchronized.value mass_facts)) ^
                          " refusals=" ^ Int.toString (read refusals) ^
                          " step_ms=" ^ LargeInt.toString (read step_ms) ^
                          " local_mass_ms=" ^ LargeInt.toString (read mass_ms) ^
                          " schema_ms=" ^ LargeInt.toString (read schema_ms))
                      else ()
                  in theorem end)
                val entry = {value = value, theorem = theorem}: mass_entry
                val published = publish mass_facts request entry
              in published end)
        end

      (* Admission is owned by Column_Conversion.  This cache deliberately
         consumes that checked producer instead of replaying its recursive
         header construction here. *)
      fun admission_fact lower cid =
        let
          val request = admission_request lower cid
          val _ = add admission_calls 1
          val theorem = timed admission_ms (fn () => prove_admitted (lower, cid))
          val theorem = check_admission theorem request
        in certify_theorem theorem end

      fun prove_card cid =
        let
          val request = card_request cid
          val entry = timed card_ms (fn () =>
            let
              val mass = prove_mass 0 cid
              val admission = admission_fact 0 cid
              val card_mass =
                @{thm comma_semantic_b1_crt_column_card_mass} OF [admission]
              val value = #value mass
              (* Both inputs are HOL equalities under Trueprop.  Thm.transitive
                 composes Pure.meta equality, so use the object-level HOL
                 transitivity rule for the cardinality bridge. *)
              val theorem = @{thm trans} OF [card_mass, #theorem mass]
              val theorem = check_card theorem request value
              val theorem = certify_theorem theorem
              val _ = add card_proofs 1
            in {value = value, theorem = theorem}: mass_entry end)
        in entry end

      (* Produce one exact ordered mass map for a published row.  The input
         list is intentionally traversed as supplied: repeated CIDs remain
         repeated map entries, while prove_mass reuses the closed per-CID
         cache.  checked_mass_map then audits every position against the
         expected DAG authority. *)
      fun mass_row ids =
        let
          val entries = map (prove_mass 0) ids
          val columns = map expected_column ids
          val equation = checked_mass_map columns entries
          val values = map #value entries
        in {equation = equation, values = values} end

      fun rejected work =
        (case Exn.capture work () of
          Exn.Res _ => false
        | Exn.Exn failure =>
            if Exn.is_interrupt failure then Exn.reraise failure else true)

      (* These fixtures exercise the authority boundary and the only cache
         retained here.  They are explicit opt-in checks for the integration
         owner; construction of this cache never runs them implicitly. *)
      fun check_fixtures () =
        let
          val first = prove_mass 0 0
          val mass_after_first = read mass_proofs
          val steps_after_first = read step_opens
          val second = prove_mass 0 0
          val _ = if #value first = #value second andalso
              Thm.prop_of (#theorem first) aconv Thm.prop_of (#theorem second) andalso
              read mass_proofs = mass_after_first andalso
              read step_opens = steps_after_first
            then () else error "B1 mass warm fixture recomputed a cached root"
          val valid_card = prove_card 0
          val expected_card = HOLogic.mk_Trueprop
            (HOLogic.mk_eq (card_request 0, number 0))
          val _ = if #value valid_card = 0 andalso
              Thm.prop_of (#theorem valid_card) aconv expected_card
            then () else error "B1 mass cardinality fixture returned an invalid result"
          val foreign_dag = Const
            (@{const_name Comma_B1_CRT_Column_DAG_Empty}, dagT)
          val foreign_at = Const (@{const_name comma_semantic_b1_crt_column_at},
            dagT --> natT --> columnT)
          fun foreign_column cid = foreign_at $ foreign_dag $ number cid
          val foreign_cache = make ctxt
            {column_value = foreign_column, step = step,
             known_column = known_column, node_count = node_count,
             prove_admitted = prove_admitted, cache_limit = cache_limit}
          val _ = if rejected (fn () => (#mass foreign_cache) 0) then ()
            else error "B1 mass foreign-DAG fixture was accepted"
          val malformed_step_cache = make ctxt
            {column_value = column_value, step = (fn _ => @{thm TrueI}),
             known_column = known_column, node_count = node_count,
             prove_admitted = prove_admitted, cache_limit = cache_limit}
          val _ = if rejected (fn () => (#mass malformed_step_cache) 0) then ()
            else error "B1 mass malformed-step fixture was accepted"
          val malformed_admission_cache = make ctxt
            {column_value = column_value, step = step,
             known_column = known_column, node_count = node_count,
             prove_admitted = (fn _ => @{thm TrueI}),
             cache_limit = cache_limit}
          val _ = if rejected (fn () => (#admission malformed_admission_cache) 0) then ()
            else error "B1 mass malformed-admission fixture was accepted"

          (* Two exact DAG rows share the same child-mass vector but have
             different ordered child columns.  Each parent theorem must
             still consume its own step equation and child map equation;
             only the final numeral arithmetic is shared. *)
          val _ = if !schema_fixture_done then () else
            let
              val _ = if Termtab.size (Synchronized.value schema_cache) = 0 then ()
                else error "B1 arithmetic fixture ran after production schema use"
              val blockT = @{typ comma_semantic_b1_crt_column_block}
              val dagT = @{typ comma_semantic_b1_crt_column_dag}
              val block_empty = @{term Comma_B1_CRT_Column_Block_Empty}
              val block_node = Const
                (@{const_name Comma_B1_CRT_Column_Block_Node},
                 natT --> natT --> HOLogic.listT natT --> blockT --> blockT --> blockT)
              fun block key level children left right =
                block_node $ number key $ number level $
                  HOLogic.mk_list natT (map number children) $ left $ right
              val left = block 2 2 (replicate 7 1) block_empty block_empty
              val right = block 4 1 [2, 1, 1] block_empty block_empty
              val root = block 3 1 [1, 1, 1] left right
              val dag_block = Const
                (@{const_name Comma_B1_CRT_Column_DAG_Block},
                 natT --> natT --> blockT --> dagT)
              val fixture_dag = dag_block $ number 2 $ number 3 $ root
              val fixture_column_at = Const
                (@{const_name comma_semantic_b1_crt_column_at},
                 dagT --> natT --> columnT)
              fun fixture_column cid = fixture_column_at $ fixture_dag $ number cid
              fun fixture_node level children =
                Const (@{const_name Comma_CRT_Node}, natT --> HOLogic.listT columnT --> columnT) $
                  number level $ HOLogic.mk_list columnT children
              val true_column = @{term "Comma_CRT_Bool True"}
              val false_column = @{term "Comma_CRT_Bool False"}
              val wide_true = fixture_node 2 (replicate 7 true_column)
              val parent_a = fixture_node 1 (replicate 3 true_column)
              val parent_b = fixture_node 1 [wide_true, true_column, true_column]
              val fixture_step_context = Comma_Entry_Arithmetic.natural_context ctxt addsimps
                @{thms comma_semantic_b1_crt_column_at.simps
                  comma_semantic_b1_crt_column_dag_lookup.simps
                  comma_semantic_b1_crt_column_block_lookup.simps
                  comma_semantic_b1_crt_guarded_node_def
                  comma_crt_admitted.simps list_all_Nil_iff list_all_Cons_iff
                  list.map list.size nth_Cons' option.case comma_crt_period_def}
              fun fixture_step cid expected =
                let
                  val request = fixture_column cid
                  val theorem = Simplifier.rewrite fixture_step_context
                    (Thm.cterm_of ctxt request)
                  val _ = check_equation "arithmetic fixture step" request theorem
                  val actual = Thm.term_of (Thm.rhs_of theorem)
                  val _ = if actual aconv expected then () else
                    error ("B1 arithmetic fixture simplified to another node shape: actual=" ^
                      Syntax.string_of_term ctxt actual ^ ", expected=" ^
                      Syntax.string_of_term ctxt expected)
                in theorem end
              fun fixture_mass column value =
                let
                  val request = mass_const $ column
                  val theorem = Goal.prove ctxt [] []
                    (HOLogic.mk_Trueprop (HOLogic.mk_eq (request, number value)))
                    (fn _ => simp_tac mass_context 1)
                in {value = value, theorem = check_mass theorem request value}: mass_entry end
              val true_entry = fixture_mass true_column 924
              val false_entry = fixture_mass false_column 0
              val wide_entry = fixture_mass wide_true 924
              val duplicate_map = checked_mass_map
                [true_column, true_column, false_column, true_column]
                [true_entry, true_entry, false_entry, true_entry]
              val duplicate_expected = HOLogic.mk_list natT
                (map number [924, 924, 0, 924])
              val _ = if Thm.term_of (Thm.rhs_of duplicate_map) aconv duplicate_expected then ()
                else error "B1 arithmetic fixture lost repeated child multiplicity"

              fun fixture_parent cid expected children entries =
                let
                  val step_theorem = fixture_step cid expected
                  val map_theorem = checked_mass_map children entries
                  val step_object = step_theorem RS @{thm meta_eq_to_obj_eq}
                  val map_object = map_theorem RS @{thm meta_eq_to_obj_eq}
                  val step = @{thm comma_semantic_b1_crt_column_mass_step}
                    OF [step_object, map_object]
                  val values = map #value entries
                  val expected_step = HOLogic.mk_Trueprop
                    (HOLogic.mk_eq (mass_const $ fixture_column cid,
                      divide_const $ (sum_list_const $ HOLogic.mk_list natT
                        (map number values)) $ (period_const $ number 1)))
                  val _ = if Thm.prop_of step aconv expected_step then () else
                    error "B1 arithmetic fixture changed exact step or child requests"
                  val value = fold (fn n => fn total => n + total) values 0 div 3
                  val schema = numeric_schema 1 values value (fixture_column cid)
                  val result = @{thm trans} OF [step, #theorem schema]
                  val result = check_mass result (mass_const $ fixture_column cid) value
                in result end

              val schema_misses_before = read schema_misses
              val schema_hits_before = read schema_hits
              val cross_owner_before = read schema_distinct_owner_hits
              val result_a = fixture_parent 3 parent_a
                [true_column, true_column, true_column]
                [true_entry, true_entry, true_entry]
              val result_b = fixture_parent 4 parent_b
                [wide_true, true_column, true_column]
                [wide_entry, true_entry, true_entry]
              val _ = if not (Thm.prop_of result_a aconv Thm.prop_of result_b) then () else
                error "B1 arithmetic schema fixture conflated exact parent requests"
              val _ = if read schema_misses = schema_misses_before + 1 andalso
                  read schema_hits = schema_hits_before + 1 andalso
                  read schema_distinct_owner_hits = cross_owner_before + 1 then () else
                error "B1 arithmetic schema fixture did not record one distinct-owner reuse"
              val wrong_step_rejected = rejected (fn () =>
                let
                  val step_a = fixture_step 3 parent_a
                  val map_b = (checked_mass_map
                    [wide_true, true_column, true_column] [wide_entry, true_entry, true_entry]
                    RS @{thm meta_eq_to_obj_eq})
                  val step_object = step_a RS @{thm meta_eq_to_obj_eq}
                  val _ = @{thm comma_semantic_b1_crt_column_mass_step}
                    OF [step_object, map_b]
                in () end)
              val wrong_child_mass_rejected = rejected (fn () =>
                ignore (checked_mass_map [true_column] [false_entry]))
              val _ = if wrong_step_rejected andalso wrong_child_mass_rejected then () else
                error "B1 arithmetic schema fixture accepted foreign step or child mass"
              val _ = Synchronized.change schema_cache (K Termtab.empty)
              val _ = Synchronized.change schema_lookups (K 0)
              val _ = Synchronized.change schema_hits (K 0)
              val _ = Synchronized.change schema_misses (K 0)
              val _ = Synchronized.change schema_distinct_owner_hits (K 0)
              val _ = Synchronized.change schema_same_owner_hits (K 0)
              val _ = Synchronized.change schema_proofs (K 0)
              val _ = Synchronized.change schema_refusals (K 0)
              val _ = Synchronized.change schema_ms (K 0)
              val _ = Synchronized.change schema_fixture_cross_owner_hits (K 1)
              val _ = Synchronized.change schema_fixture_runs (K 1)
              val _ = schema_fixture_done := true
            in () end
        in () end

      fun stats () =
        "column_mass_lookups=" ^ Int.toString (read lookups) ^
        " column_mass_hits=" ^ Int.toString (read hits) ^
        " column_mass_misses=" ^ Int.toString (read misses) ^
        " column_mass_step_opens=" ^ Int.toString (read step_opens) ^
        " column_mass_races=" ^ Int.toString (read races) ^
        " column_mass_refusals=" ^ Int.toString (read refusals) ^
        " column_mass_malformed=" ^ Int.toString (read malformed) ^
        " column_mass_mass_proofs=" ^ Int.toString (read mass_proofs) ^
        " column_mass_admission_calls=" ^ Int.toString (read admission_calls) ^
        " column_mass_card_proofs=" ^ Int.toString (read card_proofs) ^
        " column_mass_arithmetic_schema_lookups=" ^ Int.toString (read schema_lookups) ^
        " column_mass_arithmetic_schema_hits=" ^ Int.toString (read schema_hits) ^
        " column_mass_arithmetic_schema_misses=" ^ Int.toString (read schema_misses) ^
        " column_mass_arithmetic_schema_distinct_owner_hits=" ^
          Int.toString (read schema_distinct_owner_hits) ^
        " column_mass_arithmetic_schema_same_owner_hits=" ^
          Int.toString (read schema_same_owner_hits) ^
        " column_mass_arithmetic_schema_proofs=" ^ Int.toString (read schema_proofs) ^
        " column_mass_arithmetic_schema_refusals=" ^ Int.toString (read schema_refusals) ^
        " column_mass_arithmetic_schema_ms=" ^ LargeInt.toString (read schema_ms) ^
        " column_mass_arithmetic_schema_fixture_runs=" ^
          Int.toString (read schema_fixture_runs) ^
        " column_mass_arithmetic_schema_fixture_distinct_owner_hits=" ^
          Int.toString (read schema_fixture_cross_owner_hits) ^
        " column_mass_step_ms=" ^ LargeInt.toString (read step_ms) ^
        " column_mass_mass_ms=" ^ LargeInt.toString (read mass_ms) ^
        " column_mass_admission_ms=" ^ LargeInt.toString (read admission_ms) ^
        " column_mass_card_ms=" ^ LargeInt.toString (read card_ms) ^
        " column_mass_retained_mass=" ^
          Int.toString (Termtab.size (Synchronized.value mass_facts)) ^
        " column_mass_certifier_calls=" ^
          Int.toString (#calls (certification_stats ())) ^
        " column_mass_certifier_nodes=" ^
          Int.toString (#nodes (certification_stats ()))
    in
      {mass = (fn cid => #theorem (prove_mass 0 cid)),
       mass_value = (fn cid => #value (prove_mass 0 cid)),
       mass_row = mass_row,
       admission = (fn cid => admission_fact 0 cid),
       prove = (fn cid => #theorem (prove_card cid)),
       cardinality = (fn cid => #value (prove_card cid)),
       check_fixtures = check_fixtures,
       stats = stats}
    end
end
