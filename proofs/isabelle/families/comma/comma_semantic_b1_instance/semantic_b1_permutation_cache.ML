(* Exact numeric multiset certificates and bounded occurrence-order transport
   for canonical B1 zipper states. *)
structure Comma_Semantic_B1_Permutation_Cache =
struct
  structure State_Key = Table(type key = int list * int list
    val ord = prod_ord (list_ord int_ord) (list_ord int_ord))

  fun make ctxt {dag, number, literal_columns, witness_const, cache_limit} =
    let
      val natT = @{typ nat}
      val columnT = @{typ comma_crt_column}
      val nat_listT = HOLogic.listT natT
      val column_listT = HOLogic.listT columnT
      val map_column = Const (@{const_name map}, (natT --> columnT) -->
        nat_listT --> column_listT)
      val map_context = put_simpset HOL_basic_ss ctxt addsimps @{thms list.map}
      val column_map = Const (@{const_name comma_semantic_b1_crt_column_at},
        @{typ comma_semantic_b1_crt_column_dag} --> natT --> columnT) $ dag
      val (certify_certificate, _) = Comma_Entry_Arithmetic.make_certifier ctxt
      val certificate_cache = Unsynchronized.ref
        (State_Key.empty: thm State_Key.table)
      val certificate_builds = Unsynchronized.ref 0
      val certificate_hits = Unsynchronized.ref 0
      val certificate_refusals = Unsynchronized.ref 0
      val transports = Unsynchronized.ref 0
      val certificate_ms = Unsynchronized.ref (0: LargeInt.int)
      val transport_ms = Unsynchronized.ref (0: LargeInt.int)

      fun closed theorem = Thm.nprems_of theorem = 0 andalso
        null (Thm.hyps_of theorem) andalso null (Thm.tpairs_of theorem)
      fun check_theorem label proposition theorem =
        if Thm.prop_of theorem aconv proposition andalso closed theorem then theorem
        else error ("B1 multiset cache " ^ label ^
          " theorem changed authority or is not kernel-closed")
      fun measured elapsed work =
        let
          val started = Time.now ()
          val result = Exn.capture work ()
          val duration = Time.toMilliseconds (Time.- (Time.now (), started))
          val _ = elapsed := LargeInt.+ (!elapsed, duration)
        in Exn.release result end
      fun number_list values = HOLogic.mk_list natT (map number values)
      fun mset_equation elementT listT left right =
        let
          val setT = Type (@{type_name multiset}, [elementT])
          val operation = Const (@{const_name mset}, listT --> setT)
        in HOLogic.mk_Trueprop (HOLogic.mk_eq (operation $ left, operation $ right)) end

      fun build_certificate source_ids target_ids =
        let
          val width = length source_ids
          val _ = Comma_Proof_Profile.report
            ("B1 permutation stage=mset-certificate phase=start width=" ^
              Int.toString width)
          val source_numbers = number_list source_ids
          val target_numbers = number_list target_ids
          val numeric_proposition = mset_equation natT nat_listT
            source_numbers target_numbers
          val numeric_fact = Goal.prove ctxt [] [] numeric_proposition
            (fn {context, ...} =>
              simp_tac (put_simpset HOL_basic_ss context addsimps
                @{thms mset.simps add_mset_commute}) 1)
          val _ = check_theorem "numeric occurrence multiset" numeric_proposition numeric_fact
          val _ = certify_certificate numeric_fact
          val numeric_columns =
            (map_column $ column_map) $ source_numbers
          val requested_columns =
            (map_column $ column_map) $ target_numbers
          val column_proposition = mset_equation columnT column_listT
            (literal_columns source_ids) (literal_columns target_ids)
          val mapped_proposition = mset_equation columnT column_listT
            numeric_columns requested_columns
          val mapped_fact = Goal.prove ctxt [] [] mapped_proposition
            (fn {context, ...} =>
              simp_tac (put_simpset HOL_basic_ss context addsimps @{thms mset_map}) 1 THEN
              resolve_tac context [@{thm arg_cong}] 1 THEN
              resolve_tac context [numeric_fact] 1)
          val mapped_equation = Simplifier.rewrite map_context
            (Thm.cterm_of ctxt (Thm.prop_of mapped_fact))
          val _ = if Thm.term_of (Thm.lhs_of mapped_equation) aconv
                Thm.prop_of mapped_fact andalso
              Thm.term_of (Thm.rhs_of mapped_equation) aconv column_proposition andalso
              closed mapped_equation
            then () else error
              "B1 numeric multiset map changed its exact column occurrence lists"
          val column_fact = Thm.equal_elim mapped_equation mapped_fact
          val checked = check_theorem "exact mapped occurrence multiset"
            column_proposition column_fact
          val _ = certify_certificate checked
          val _ = Comma_Proof_Profile.report
            ("B1 permutation stage=mset-certificate phase=done width=" ^
              Int.toString width)
        in checked end

      fun certificate source_ids target_ids =
        let
          val _ = if sort int_ord source_ids = sort int_ord target_ids then ()
            else error "B1 requested state changed occurrence multiplicity"
          val key = (source_ids, target_ids)
          val expected = mset_equation columnT column_listT
            (literal_columns source_ids) (literal_columns target_ids)
        in
          (case State_Key.lookup (!certificate_cache) key of
            SOME theorem =>
              (certificate_hits := !certificate_hits + 1;
               check_theorem "cached exact occurrence multiset" expected theorem)
          | NONE =>
              let
                val theorem = measured certificate_ms (fn () =>
                  build_certificate source_ids target_ids)
                val _ = certificate_builds := !certificate_builds + 1
                val _ = if State_Key.size (!certificate_cache) < cache_limit then
                  certificate_cache := State_Key.update
                    (key, theorem) (!certificate_cache)
                else certificate_refusals := !certificate_refusals + 1
              in check_theorem "new exact occurrence multiset" expected theorem end)
        end

      fun check_numeric_fixtures () =
        let
          val source_ids = [2, 1, 2, 0]
          val target_ids = [0, 2, 2, 1]
          val positive = certificate source_ids target_ids
          val _ = if !certificate_builds = 1 andalso !certificate_hits = 0
            then () else error "B1 multiset fixture did not build one certificate"
          val repeated = certificate source_ids target_ids
          val _ = if !certificate_builds = 1 andalso !certificate_hits = 1 andalso
              Thm.prop_of positive aconv Thm.prop_of repeated
            then () else error "B1 multiset fixture did not reuse its exact certificate"
          val alternate_source = certificate [1, 2, 0, 2] target_ids
          val _ = if !certificate_builds = 2 andalso !certificate_hits = 1 andalso
              not (Thm.prop_of positive aconv Thm.prop_of alternate_source)
            then () else error "B1 multiset fixture conflated source-order cache keys"
          val wrong_multiplicity_rejected =
            ((certificate source_ids [0, 2, 1, 1]; false)
              handle ERROR message =>
                if message = "B1 requested state changed occurrence multiplicity" then true
                else error ("B1 multiset fixture failed for an unrelated reason: " ^ message))
          val _ = if wrong_multiplicity_rejected andalso
              !certificate_builds = 2 andalso !certificate_hits = 1
            then () else error "B1 multiset fixture accepted changed occurrence multiplicity"
        in () end

      fun transport level source_ids target_ids theorem =
        if source_ids = target_ids then
          let
            val expected = HOLogic.mk_Trueprop
              (witness_const $ number level $ literal_columns target_ids)
          in check_theorem "identity compact state witness" expected theorem end
        else measured transport_ms (fn () =>
          let
            val multiset_fact = certificate source_ids target_ids
            val transported =
              @{thm comma_semantic_b1_crt_partition_witness_mset}
                OF [multiset_fact, theorem]
            val expected = HOLogic.mk_Trueprop
              (witness_const $ number level $ literal_columns target_ids)
            val checked = check_theorem "multiset-rebased compact state witness"
              expected transported
            val _ = transports := !transports + 1
          in checked end)

      fun stats () =
        " labelled_zip_state_permutation_transports=" ^ Int.toString (!transports) ^
        " labelled_zip_state_permutation_certificate_builds=" ^
          Int.toString (!certificate_builds) ^
        " labelled_zip_state_permutation_certificate_hits=" ^
          Int.toString (!certificate_hits) ^
        " labelled_zip_state_permutation_certificate_refusals=" ^
          Int.toString (!certificate_refusals) ^
        " labelled_zip_state_permutation_cert_ms=" ^
          LargeInt.toString (!certificate_ms) ^
        " labelled_zip_state_permutation_transport_ms=" ^
          LargeInt.toString (!transport_ms)
    in
      {transport = transport, stats = stats,
       check_numeric_fixtures = check_numeric_fixtures,
       certificate_builds = fn () => !certificate_builds,
       certificate_hits = fn () => !certificate_hits,
       transports = fn () => !transports}
    end

  fun check_fixtures ctxt =
    let
      val natT = @{typ nat}
      val columnT = @{typ comma_crt_column}
      val column_listT = HOLogic.listT columnT
      val boolT = @{typ bool}
      fun number n = HOLogic.mk_number natT n
      val dag = Const (@{const_name Comma_B1_CRT_Column_DAG_Empty},
        @{typ comma_semantic_b1_crt_column_dag})
      val column_at = Const (@{const_name comma_semantic_b1_crt_column_at},
        @{typ comma_semantic_b1_crt_column_dag} --> natT --> columnT)
      fun literal_columns ids = HOLogic.mk_list columnT
        (map (fn cid => column_at $ dag $ number cid) ids)
      val witness_const = Const
        (@{const_name comma_semantic_b1_crt_partition_witness},
          natT --> column_listT --> boolT)
      val cache = make ctxt
        {dag = dag, number = number, literal_columns = literal_columns,
         witness_const = witness_const, cache_limit = 4}
      val _ = #check_numeric_fixtures cache ()
      val fixture_ids = [2, 1, 2, 0]
      val exact_witness = HOLogic.mk_Trueprop
        (witness_const $ number 0 $ literal_columns fixture_ids)
      val open_witness = Thm.assume (Thm.cterm_of ctxt exact_witness)
      val open_rejected =
        ((#transport cache) 0 fixture_ids fixture_ids open_witness; false)
          handle ERROR _ => true
      val _ = if open_rejected then ()
        else error "B1 identity fixture accepted a theorem with an open assumption"

      val level_witness = Abs ("level", natT,
        Abs ("columns", column_listT,
          Const (@{const_name HOL.eq}, natT --> natT --> boolT) $ Bound 1 $ number 0))
      val level_cache = make ctxt
        {dag = dag, number = number, literal_columns = literal_columns,
         witness_const = level_witness, cache_limit = 4}
      val level_zero_proposition = HOLogic.mk_Trueprop
        (level_witness $ number 0 $ literal_columns fixture_ids)
      val level_zero_fact = Goal.prove ctxt [] [] level_zero_proposition
        (fn {context, ...} => simp_tac (put_simpset HOL_basic_ss context) 1)
      val wrong_level_rejected =
        ((#transport level_cache) 1 fixture_ids fixture_ids level_zero_fact; false)
          handle ERROR _ => true
      val true_i_rejected =
        ((#transport level_cache) 0 fixture_ids fixture_ids @{thm TrueI}; false)
          handle ERROR _ => true
      val _ = if wrong_level_rejected andalso true_i_rejected then ()
        else error "B1 identity fixture accepted a wrong-level or TrueI theorem"

      fun reversed_columns ids = literal_columns (rev ids)
      val malformed_cache = make ctxt
        {dag = dag, number = number, literal_columns = reversed_columns,
         witness_const = witness_const, cache_limit = 4}
      val malformed_rejected =
        ((#check_numeric_fixtures malformed_cache (); false)
          handle ERROR message =>
            if message = "B1 numeric multiset map changed its exact column occurrence lists"
            then true else error
              ("B1 malformed-column fixture failed for an unrelated reason: " ^ message))
      val _ = if malformed_rejected then ()
        else error "B1 multiset fixture accepted a malformed literal-column callback"
    in () end
end
