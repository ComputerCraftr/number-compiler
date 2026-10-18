(* Context-owned, one-node evaluation of a closed global column DAG.  The
   published tree contains only levels and child CIDs.  Each proof step uses
   the generic well-founded interpreter once, keeping child CIDs opaque. *)
structure Comma_Semantic_B1_Column_Conversion =
struct
  open Comma_Semantic_B1_Column_Catalog
  fun closed term = not (Term.is_open term) andalso
    null (Term.add_frees term []) andalso null (Term.add_vars term [])
  fun time_profile timer work =
    if not (Comma_Proof_Profile.enabled ()) then work ()
    else let val started = Time.now () val result = work ()
      val _ = timer := Time.+ (!timer, Time.- (Time.now (), started))
    in result end
  val argument_at = Comma_Semantic_B1_Column_Lookup_Cache.argument_at

  fun make_template_projection ctxt selected_context definition =
    Comma_Semantic_B1_Template_Projection.make
      {ctxt = ctxt, selected_context = selected_context, definition = definition,
       natT = natT, columnT = columnT, dagT = dagT, closed = closed,
       dest_nat = dest_nat, argument_at = argument_at}

  fun make ctxt definitions =
    let
      val thy = Proof_Context.theory_of ctxt
      (* All derived facts in this owner share one immutable proof-serial
         audit.  Each theorem root is still checked on publication; common
         dependencies from column steps and cofactor edges are walked once. *)
      val (certify_derived_fact, derived_certification_stats) =
        Comma_Entry_Arithmetic.make_certifier ctxt
      fun certify_derived_theorem label theorem =
        let
          val left = Thm.term_of (Thm.lhs_of theorem)
          val right = Thm.term_of (Thm.rhs_of theorem)
          val closed_contract = Thm.nprems_of theorem = 0 andalso
            null (Thm.hyps_of theorem) andalso null (Thm.tpairs_of theorem) andalso
            closed left andalso closed right
        in
          if closed_contract then
            (certify_derived_fact theorem
              handle ERROR message => error (label ^ " certification failed: " ^ message))
          else error (label ^ " is not a closed standalone theorem")
        end
      val expected_name = Sign.intern_const thy
        "comma_semantic_b1_crt_column_node_dag"
      val expected_dag_constant = Const (expected_name, dagT)
      val blockT = @{typ comma_semantic_b1_crt_column_block}
      fun clean_equation equation left right =
        Thm.nprems_of equation = 0 andalso null (Thm.hyps_of equation) andalso
        null (Thm.tpairs_of equation) andalso
        null (Thm_Deps.all_oracles [equation]) andalso
        closed left andalso closed right
      fun equation_data theorem =
        let
          val equation = Local_Defs.meta_rewrite_rule ctxt theorem
          val left = Thm.term_of (Thm.lhs_of equation)
          val right = Thm.term_of (Thm.rhs_of equation)
          val name = (case left of
              Const (name, _) => name
            | _ => error "B1 column block authority has a nonconstant left side")
        in (equation, left, right, name) end
      val raw_definitions = map equation_data definitions
      val dag_definitions = filter (fn (_, _, _, name) => name = expected_name)
        raw_definitions
      val block_definitions = filter (fn (_, _, _, name) =>
        is_some (parse_block_index name)) raw_definitions
      val _ = if length dag_definitions = 1 andalso
          length block_definitions + 1 = length raw_definitions then ()
        else error "B1 column block authority has missing or foreign definitions"
      val (equation, left, dag_body, _) = hd dag_definitions
      val _ = if fastype_of left = dagT andalso fastype_of dag_body = dagT andalso
          clean_equation equation left dag_body
        then () else error "B1 column DAG definition has invalid authority"
      fun parse_block_definition (block_equation, block_left, block_body, name) =
        let
          val index = (case parse_block_index name of
              SOME index => index
            | NONE => error "B1 column block has an invalid name")
          val base = 2 + index * block_size
          val _ = if canonical_block_name thy index name andalso
              fastype_of block_left = blockT andalso
              fastype_of block_body = blockT andalso
              clean_equation block_equation block_left block_body
            then () else error "B1 column block definition has invalid authority"
          val nodes = parse_block_tree base block_body
          val extent = length nodes
          val _ = if extent > 0 andalso extent <= block_size then ()
            else error "B1 column block exceeds its bound or is empty"
        in {index = index, base = base, extent = extent, nodes = nodes,
            constant = block_left, theorem = block_equation}: block end
      val blocks = map parse_block_definition block_definitions
      val block_count = length blocks
      val ordered_blocks = sort
        (fn (left: block, right: block) => int_ord (#index left, #index right)) blocks
      val expected_block_indices = 0 upto (block_count - 1)
      val _ = if map #index ordered_blocks = expected_block_indices then ()
        else error "B1 column block definitions are duplicated or incomplete"
      val _ = if forall (fn ({index, nodes, ...}: block) =>
          if index + 1 < block_count then length nodes = block_size
          else not (null nodes) andalso length nodes <= block_size) ordered_blocks
        then () else error "B1 column block partition is not canonical"
      val block_index = fold (fn (block: block) => fn table =>
        Inttab.update (#index block, block) table) ordered_blocks Inttab.empty
      val _ = if Inttab.size block_index = block_count then ()
        else error "B1 column block definitions repeat an index"
      val directory_indices = parse_directory block_index dag_body
      val _ = if directory_indices = expected_block_indices then ()
        else error "B1 column DAG directory does not cover its blocks"
      val nodes = maps #nodes ordered_blocks
      val (node_index, structure_index) = validate_nodes nodes
      val count = length nodes + 2
      val columns_constant = Const
        (Sign.intern_const thy "comma_semantic_b1_crt_columns",
         HOLogic.listT columnT)
      val blocks_vector = Vector.fromList ordered_blocks
      fun block_for_cid cid =
        if cid < 2 orelse cid >= count then
          error "B1 column lookup requested a foreign CID"
        else Vector.sub (blocks_vector, (cid - 2) div block_size)
      val column_at_name = @{const_name comma_semantic_b1_crt_column_at}
      val column_at_const = Const (@{const_name comma_semantic_b1_crt_column_at},
        dagT --> natT --> columnT)
      fun column_value cid = column_at_const $ expected_dag_constant $
        HOLogic.mk_number natT cid
      fun dest_column_cid term =
        (case strip_comb term of
          (Const (name, _), [dag, cid_term]) =>
            if name = column_at_name andalso dag aconv expected_dag_constant andalso
                fastype_of term = columnT then
              (case try dest_nat cid_term of
                SOME cid => if cid < count then SOME cid else NONE
              | NONE => NONE)
            else NONE
        | _ => NONE)
      fun known_column term = is_some (dest_column_cid term)
      fun node cid =
        (case Inttab.lookup node_index cid of
          SOME entry => entry
        | NONE => error "B1 column DAG lookup requested a foreign CID")
      fun body_cid term =
        (case strip_comb term of
          (Const (name, _), [level_term, children_term]) =>
            if name <> @{const_name Comma_CRT_Node} then NONE
            else
              (case (try dest_nat level_term, try HOLogic.dest_list children_term) of
                (SOME level, SOME child_terms) =>
                  let
                    val child_ids = map dest_column_cid child_terms
                  in
                    if forall is_some child_ids then
                      Symtab.lookup structure_index
                        (structure_key level (map the child_ids))
                    else NONE
                  end
              | _ => NONE)
        | _ => NONE)
      fun shallow_body cid =
        if cid = 0 then @{term "Comma_CRT_Bool False"}
        else if cid = 1 then @{term "Comma_CRT_Bool True"}
        else
          let
            val {level, children, ...} = node cid
            val child_terms = map column_value children
          in
            Const (@{const_name Comma_CRT_Node},
              natT --> HOLogic.listT columnT --> columnT) $
              HOLogic.mk_number natT level $
              HOLogic.mk_list columnT child_terms
          end
      val step_facts = Unsynchronized.ref (Termtab.empty: thm Termtab.table)
      val lookup_facts = Unsynchronized.ref (Termtab.empty: thm Termtab.table)
      val lookup_hits = Unsynchronized.ref 0
      val lookup_misses = Unsynchronized.ref 0
      val step_hits = Unsynchronized.ref 0
      val step_misses = Unsynchronized.ref 0
      val child_admission_facts = Unsynchronized.ref
        (Termtab.empty: thm Termtab.table)
      val child_admission_hits = Unsynchronized.ref 0
      val child_admission_misses = Unsynchronized.ref 0
      val child_admission_refusals = Unsynchronized.ref 0
      val lookup_value_ms = Unsynchronized.ref Time.zeroTime
      val step_rewrite_ms = Unsynchronized.ref Time.zeroTime
      val step_admission_ms = Unsynchronized.ref Time.zeroTime
      val column_at_unfold_ms = Unsynchronized.ref Time.zeroTime
      val column_at_rule = Local_Defs.meta_rewrite_rule ctxt
        @{thm comma_semantic_b1_crt_column_at.simps}
      val lookupT = @{typ "(nat \<times> nat list) option"}
      val lookup_const = Const (@{const_name comma_semantic_b1_crt_column_dag_lookup},
        dagT --> natT --> lookupT)
      val numeral_context = Comma_Entry_Arithmetic.natural_context ctxt
      val prove_admitted_header =
        Comma_Semantic_B1_CRT_Operation_Conversion.make_column_at_admitted_header ctxt
      val lookup_visits = Unsynchronized.ref 0
      val directory_lookup_cache =
        Comma_Semantic_B1_Column_Lookup_Cache.make_directory
          ctxt numeral_context 8192 expected_dag_constant equation
      val interval_lookup_cache = Comma_Semantic_B1_Column_Lookup_Cache.make
        ctxt numeral_context 8192

      fun lookup_value_uncounted cid =
        let
          val request = lookup_const $ expected_dag_constant $
            HOLogic.mk_number natT cid
        in
          (case Termtab.lookup (!lookup_facts) request of
            SOME theorem => (lookup_hits := !lookup_hits + 1; theorem)
          | NONE =>
              let
                val _ = lookup_misses := !lookup_misses + 1
                val request_ct = Thm.cterm_of ctxt request
                val selected_block = block_for_cid cid
                val directory_step =
                  #lookup directory_lookup_cache
                    (#constant selected_block) (#theorem selected_block)
                    (#base selected_block) (#extent selected_block) cid request_ct
                val lookup_step = #lookup interval_lookup_cache lookup_visits
                  (#constant selected_block) (#theorem selected_block)
                  (#base selected_block) (#extent selected_block) cid
                  (Thm.rhs_of directory_step)
                val theorem = Thm.transitive directory_step lookup_step
                val {level, children, ...} = node cid
                val expected_value = Const (@{const_name Some},
                    @{typ "nat \<times> nat list"} --> lookupT) $
                  HOLogic.mk_prod (HOLogic.mk_number natT level,
                    HOLogic.mk_list natT (map (HOLogic.mk_number natT) children))
                val _ = if Thm.term_of (Thm.lhs_of theorem) aconv request andalso
                    Thm.term_of (Thm.rhs_of theorem) aconv expected_value
                  then () else error
                    "B1 selected column block returned another node payload"
                val _ = if Thm.nprems_of theorem = 0 andalso
                    null (Thm.hyps_of theorem) andalso null (Thm.tpairs_of theorem)
                  then () else error "B1 controlled block lookup is not a clean theorem"
                val _ = lookup_facts := Termtab.update (request, theorem)
                  (!lookup_facts)
              in theorem end)
        end
      fun lookup_value cid = time_profile lookup_value_ms (fn () => lookup_value_uncounted cid)

      val admitted_const = Const (@{const_name comma_crt_admitted}, natT --> columnT --> HOLogic.boolT)
      fun check_child_admission_fact request theorem =
        let
          val expected = HOLogic.mk_Trueprop request
        in
          if Thm.prop_of theorem aconv expected andalso
              Thm.nprems_of theorem = 0 andalso null (Thm.hyps_of theorem) andalso
              null (Thm.tpairs_of theorem) andalso closed expected
          then theorem
          else error "B1 child-admission theorem changed its exact request"
        end

      (* Prove the exact child fact needed by a raw row, with lookup/header
         authority for internal CIDs and closed equations for terminal CIDs. *)
      fun child_admission_fact lower child =
        let
          val request = admitted_const $ HOLogic.mk_number natT lower $ column_value child
        in
          (case Termtab.lookup (!child_admission_facts) request of
            SOME theorem =>
              (child_admission_hits := !child_admission_hits + 1;
               check_child_admission_fact request theorem)
          | NONE =>
              let
                val _ = child_admission_misses := !child_admission_misses + 1
                val theorem =
                  if child < 2 then
                    Goal.prove ctxt [] [] (HOLogic.mk_Trueprop request)
                      (fn {context, ...} =>
                        simp_tac (put_simpset HOL_basic_ss context addsimps
                          (@{thms comma_crt_admitted.simps
                            comma_semantic_b1_crt_column_at_false
                            comma_semantic_b1_crt_column_at_true})) 1)
                  else
                    let
                      val {level, children, ...} = node child
                      val lookup = lookup_value child
                      val children_term = HOLogic.mk_list natT
                        (map (HOLogic.mk_number natT) children)
                      val admitted_equation = prove_admitted_header
                            {request = request,
                             dag = expected_dag_constant,
                             cid = HOLogic.mk_number natT child,
                             lower = HOLogic.mk_number natT lower,
                             level = HOLogic.mk_number natT level,
                             children = children_term, lookup = lookup}
                      val proposition_equation = Thm.combination
                        (Thm.reflexive (Thm.cterm_of ctxt @{term Trueprop}))
                        admitted_equation
                    in
                      Thm.equal_elim (Thm.symmetric proposition_equation)
                        @{thm TrueI}
                    end
                val theorem = check_child_admission_fact request theorem
                (* Route every newly generated admission through the shared
                   proof-serial oracle audit before the fact enters either
                   admission cache.  This preserves transitive oracle
                   rejection while reusing already checked proof dependencies. *)
                val theorem = certify_derived_fact theorem
                val theorem = check_child_admission_fact request theorem
                val _ = if Termtab.size (!child_admission_facts) < 8192 then
                    child_admission_facts := Termtab.update
                      (request, theorem) (!child_admission_facts)
                  else child_admission_refusals :=
                    !child_admission_refusals + 1
              in theorem end)
        end

      val raw_node_admission_context = numeral_context addsimps
        @{thms comma_crt_admitted.simps list_all_Nil_iff list_all_Cons_iff
          list.size nth_Cons' comma_crt_period_def}
      val targeted_step_base_context = numeral_context addsimps
        @{thms list_all_Nil_iff list_all_Cons_iff list.map list.size nth_Cons'
          option.case comma_crt_period_def comma_semantic_b1_crt_guarded_node_def}

      fun raw_node_admission_fact cid =
        let
          val {level, children, ...} = node cid
          val child_facts = map (child_admission_fact (level + 1)) children
          val request = admitted_const $ HOLogic.mk_number natT 0 $ shallow_body cid
          val context = raw_node_admission_context addsimps child_facts
          val equation = Simplifier.rewrite context (Thm.cterm_of ctxt request)
          val _ = if Thm.term_of (Thm.lhs_of equation) aconv request andalso
              Thm.term_of (Thm.rhs_of equation) aconv @{term True} then ()
            else error "B1 raw-node admission did not reduce to True"
          val theorem = Thm.equal_elim (Thm.symmetric (Thm.combination
            (Thm.reflexive (Thm.cterm_of ctxt @{term Trueprop})) equation)) @{thm TrueI}
        in check_child_admission_fact request theorem end
      fun targeted_step_context root_lookup raw_admission =
        targeted_step_base_context addsimps [root_lookup, raw_admission]
      fun column_step cid =
        let val request = column_value cid in
          (case Termtab.lookup (!step_facts) request of
            SOME theorem => (step_hits := !step_hits + 1; theorem)
          | NONE =>
              let
                val _ = step_misses := !step_misses + 1
                val request_ct = Thm.cterm_of ctxt request
                val unfolded = time_profile column_at_unfold_ms
                  (fn () =>
                    if cid = 0 then Conv.rewr_conv
                      (@{thm comma_semantic_b1_crt_column_at_false} RS @{thm eq_reflection}) request_ct
                    else if cid = 1 then Conv.rewr_conv
                      (@{thm comma_semantic_b1_crt_column_at_true} RS @{thm eq_reflection}) request_ct
                    else Conv.rewr_conv column_at_rule request_ct)
                val root_lookup = if cid < 2 then NONE else
                  SOME (time_profile lookup_value_ms (fn () =>
                    lookup_value_uncounted cid))
                val raw_admission = if cid < 2 then NONE else
                  SOME (time_profile step_admission_ms (fn () =>
                    raw_node_admission_fact cid))
                val reduced = time_profile step_rewrite_ms (fn () =>
                  (case (root_lookup, raw_admission) of
                    (SOME lookup, SOME admission) =>
                      Simplifier.rewrite
                        (targeted_step_context lookup admission)
                        (Thm.rhs_of unfolded)
                  | (NONE, NONE) => Thm.reflexive (Thm.rhs_of unfolded)
                  | _ => error "B1 targeted column-step context is incomplete"))
                val theorem = Thm.transitive unfolded reduced
                val lhs = Thm.term_of (Thm.lhs_of theorem)
                val rhs = Thm.term_of (Thm.rhs_of theorem)
                val expected = shallow_body cid
                val _ = if lhs aconv request andalso rhs aconv expected andalso
                    fastype_of lhs = columnT andalso fastype_of rhs = columnT andalso
                    closed lhs andalso closed rhs then () else
                  error ("B1 one-node column unfolding failed; expected=" ^
                    Syntax.string_of_term ctxt expected ^ "; actual=" ^ Syntax.string_of_term ctxt rhs)
                val _ = certify_derived_theorem "B1 one-node column unfolding" theorem
                val _ = step_facts := Termtab.update (request, theorem) (!step_facts)
              in theorem end)
        end
      val cofactor_or_false_const = Const
        (@{const_name comma_crt_cofactor_or_false},
         natT --> natT --> columnT --> columnT)
      val cofactor_transition_facts =
        Unsynchronized.ref (Termtab.empty: (int * thm) Termtab.table)
      val cofactor_transition_lookups = Unsynchronized.ref 0
      val cofactor_transition_hits = Unsynchronized.ref 0
      val cofactor_transition_misses = Unsynchronized.ref 0
      val cofactor_transition_proofs = Unsynchronized.ref 0
      val cofactor_transition_context = numeral_context addsimps
        (@{thms comma_crt_cofactor.simps comma_crt_cofactor_or_false_def
          option.case list.map list.size nth_Cons'})
      fun cofactor_target level digit cid =
        if cid < 2 then cid
        else
          let val {level = node_level, children, ...} = node cid in
            if node_level < level then 0
            else if level < node_level then cid
            else
              (case try List.nth (children, digit) of
                SOME child => child
              | NONE => error "B1 cofactor digit is outside its node row")
          end
      fun check_cofactor_transition_contract theorem request target_cid =
        let
          val left = Thm.term_of (Thm.lhs_of theorem)
          val right = Thm.term_of (Thm.rhs_of theorem)
          val target = column_value target_cid
        in
          if left aconv request andalso right aconv target andalso
              fastype_of left = columnT andalso fastype_of right = columnT andalso
              Thm.nprems_of theorem = 0 andalso null (Thm.hyps_of theorem) andalso
              null (Thm.tpairs_of theorem) andalso
              closed left andalso closed right
          then theorem
          else error "B1 cofactor transition theorem has a mismatched contract"
        end
      fun check_fresh_cofactor_transition theorem request target_cid =
        let val checked =
          check_cofactor_transition_contract theorem request target_cid
        in
          certify_derived_theorem "B1 fresh cofactor transition" checked
        end
      fun build_cofactor_transition level cid target_cid request =
        let
          val request_ct = Thm.cterm_of ctxt request
          val target = column_value target_cid
          val theorem = if cid >= 2 andalso level < #level (node cid) then
              let
                val admission = child_admission_fact (level + 1) cid
                val rule = Drule.infer_instantiate ctxt
                  [(("level", 0), Thm.cterm_of ctxt (HOLogic.mk_number natT level))]
                  @{thm comma_crt_cofactor_skip_from_admission}
                val skip = Simplifier.full_simplify numeral_context rule OF [admission]
              in Simplifier.rewrite
                (put_simpset HOL_basic_ss ctxt addsimps
                  (@{thms comma_crt_cofactor_or_false_def option.case} @ [skip]))
                request_ct end
            else
              let
                val unfolded = Conv.arg_conv
                  (Conv.rewr_conv (column_step cid)) request_ct
                val reduced = Simplifier.rewrite cofactor_transition_context
                  (Thm.rhs_of unfolded)
                val rhs = Thm.term_of (Thm.rhs_of reduced)
                val target_wrap = if rhs aconv target
                  then Thm.reflexive (Thm.rhs_of reduced)
                  else Conv.rewr_conv (Thm.symmetric (column_step target_cid))
                    (Thm.rhs_of reduced)
              in Thm.transitive unfolded (Thm.transitive reduced target_wrap) end
          val checked = check_fresh_cofactor_transition theorem request target_cid
          val _ = cofactor_transition_proofs :=
            !cofactor_transition_proofs + 1
        in checked end
      fun cofactor_transition (level, digit, cid) =
        let
          val _ = cofactor_transition_lookups :=
            !cofactor_transition_lookups + 1
          val _ = if level >= 0 andalso level < Vector.length periods then ()
            else error "B1 cofactor transition has an invalid CRT level"
          val radix = Vector.sub (periods, level)
          val _ = if digit >= 0 andalso digit < radix then ()
            else error "B1 cofactor transition has a digit outside its radix"
          val _ = if cid >= 0 andalso cid < count then ()
            else error "B1 cofactor transition requested a foreign CID"
          val target_cid = cofactor_target level digit cid
          val _ = if target_cid >= 0 andalso target_cid < count then ()
            else error "B1 cofactor transition produced a foreign CID"
          val request = cofactor_or_false_const $
            HOLogic.mk_number natT level $
            HOLogic.mk_number natT digit $ column_value cid
        in
          (case Termtab.lookup (!cofactor_transition_facts) request of
            SOME (cached_target, theorem) =>
              let
                val _ = cofactor_transition_hits :=
                  !cofactor_transition_hits + 1
                val _ = if cached_target = target_cid then ()
                  else error "B1 cached cofactor transition changed its target CID"
              in
                {target_cid = cached_target,
                 theorem = check_cofactor_transition_contract
                   theorem request cached_target}
              end
          | NONE =>
              let
                val _ = cofactor_transition_misses :=
                  !cofactor_transition_misses + 1
                val theorem = build_cofactor_transition level cid
                  target_cid request
                val _ = cofactor_transition_facts :=
                  Termtab.update (request, (target_cid, theorem))
                    (!cofactor_transition_facts)
              in {target_cid = target_cid, theorem = theorem} end)
        end
      fun cofactor_transition_counts () =
        {lookups = !cofactor_transition_lookups,
         hits = !cofactor_transition_hits,
         misses = !cofactor_transition_misses,
         proofs = !cofactor_transition_proofs}
      fun cofactor_node_level cid =
        if cid < 0 orelse cid >= count then
          error "B1 cofactor metadata requested a foreign CID"
        else if cid < 2 then NONE
        else SOME (#level (node cid))
      val active = Unsynchronized.ref (Termtab.empty: unit Termtab.table)
      val facts = Unsynchronized.ref (Termtab.empty: thm Termtab.table)
      val admission_facts = Unsynchronized.ref (Termtab.empty: thm Termtab.table)
      val admitted_name = @{const_name comma_crt_admitted}
      fun admitted_column_shape request =
        (case strip_comb request of
          (Const (name, _), [lower, column]) =>
            if name = admitted_name then
              (case dest_column_cid column of
                SOME cid => SOME (lower, cid)
              | _ => NONE)
            else NONE
        | _ => NONE)
      fun admitted_column_request request =
        (case admitted_column_shape request of
          SOME (lower, cid) => Option.map (fn bound => (bound, cid))
            (try dest_nat lower)
        | NONE => NONE)
      fun admitted_column_cid request =
        (case admitted_column_request request of
          SOME (0, cid) => SOME cid
        | _ => NONE)
      val opened = Unsynchronized.ref 0
      val reify_visits = Unsynchronized.ref 0
      val reify_facts = Synchronized.var
        "semantic_b1_column_reify_facts" (Termtab.empty: thm Termtab.table)
      val reify_cache_hits = Synchronized.var "semantic_b1_column_reify_hits" 0
      val reify_cache_misses = Synchronized.var "semantic_b1_column_reify_misses" 0
      val reify_body_hits = Synchronized.var "semantic_b1_column_reify_body_hits" 0
      val reify_cache_races = Synchronized.var "semantic_b1_column_reify_races" 0
      val reify_cache_refusals = Synchronized.var
        "semantic_b1_column_reify_refusals" 0
      fun check_reify_fact request theorem =
        let
          val left = Thm.term_of (Thm.lhs_of theorem)
          val right = Thm.term_of (Thm.rhs_of theorem)
        in
          if left aconv request andalso fastype_of left = fastype_of right andalso
              Thm.nprems_of theorem = 0 andalso null (Thm.hyps_of theorem) andalso
              null (Thm.tpairs_of theorem)
          then theorem
          else error "B1 cached column reification has a mismatched theorem"
        end
      fun remember_reify_fact request theorem =
        let
          (* Validate before publication; immutable hits inherit the invariant. *)
          val checked = check_reify_fact request theorem
          val (chosen, race) =
            if not (closed (Thm.term_of (Thm.rhs_of checked))) then (NONE, false)
            else Synchronized.change_result reify_facts (fn cache =>
              (case Termtab.lookup cache request of
                SOME existing => ((SOME existing, true), cache)
              | NONE => if Termtab.size cache < 8192 then
                  ((SOME checked, false), Termtab.update (request, checked) cache)
                else ((NONE, false), cache)))
          val _ = if is_none chosen then
              Synchronized.change reify_cache_refusals (fn count => count + 1) else if race then
              Synchronized.change reify_cache_races (fn count => count + 1) else ()
        in (case chosen of SOME admitted => admitted | NONE => checked) end
      val hits = Unsynchronized.ref 0
      val publications = Unsynchronized.ref 0
      val fact_capacity_refusals = Unsynchronized.ref 0
      val equation_checker =
        Comma_Semantic_B1_CRT_Operation_Conversion.make_equation_checker_with_columns
          ctxt known_column
      fun check_and_publish request theorem =
        let
          val result = #check equation_checker request theorem
          val checked = #equation result
          val complete = #complete (#status result)
          val _ = if complete then
              ((case admitted_column_cid request of
                 SOME _ => admission_facts :=
                   Termtab.update (request, checked) (!admission_facts)
               | NONE => ());
               if Termtab.size (!facts) < 8192 then
                 (facts := Termtab.update (request, checked) (!facts);
                  publications := !publications + 1)
               else fact_capacity_refusals := !fact_capacity_refusals + 1)
            else ()
        in if complete then SOME checked else NONE end
      fun admission_header_equation request =
        (case admitted_column_shape request of
          SOME (raw_lower, cid) =>
            let
              val lower_equation = Simplifier.rewrite numeral_context
                (Thm.cterm_of ctxt raw_lower)
            in
              (case try dest_nat (Thm.term_of (Thm.rhs_of lower_equation)) of
                NONE => NONE
              | SOME lower =>
                  if lower = 0 orelse cid < 2 then NONE
                  else
                    let val {level, children, ...} = node cid in
                      if lower > level then NONE
                      else
                        let
                          val normalized = argument_at 1
                            (Conv.rewr_conv lower_equation)
                            (Thm.cterm_of ctxt request)
                          val normalized_request =
                            Thm.term_of (Thm.rhs_of normalized)
                          val lookup = lookup_value cid
                          val children_term = HOLogic.mk_list natT
                            (map (HOLogic.mk_number natT) children)
                          val expected = Const (@{const_name Some},
                            @{typ "nat \<times> nat list"} --> lookupT) $
                            HOLogic.mk_prod (HOLogic.mk_number natT level, children_term)
                          val _ = if Thm.term_of (Thm.rhs_of lookup) aconv expected then ()
                            else error "B1 admission header disagrees with the validated column row"
                          val header = prove_admitted_header
                            {request = normalized_request, dag = expected_dag_constant,
                             cid = HOLogic.mk_number natT cid,
                             lower = HOLogic.mk_number natT lower,
                             level = HOLogic.mk_number natT level,
                             children = children_term,
                             lookup = lookup}
                          val theorem = Thm.transitive normalized header
                          val _ = if Thm.term_of (Thm.lhs_of theorem) aconv request andalso
                              Thm.term_of (Thm.rhs_of theorem) aconv @{term True} andalso
                              Thm.nprems_of theorem = 0 andalso null (Thm.hyps_of theorem) andalso
                              null (Thm.tpairs_of theorem) then () else
                            error "B1 normalized admission header changed its exact request"
                        in SOME theorem end
                    end)
            end
        | NONE => NONE)
      fun unfold_column ct =
        (case dest_column_cid (Thm.term_of ct) of
          NONE => Thm.reflexive ct
        | SOME cid =>
            (opened := !opened + 1; Conv.rewr_conv (column_step cid) ct))
      fun reify ct =
        let
          val term = Thm.term_of ct
        in
          (* Exact references already are the canonical named form.  Returning
             reflexivity here avoids a reify-cache lookup (and theorem checks)
             for every owned child encountered while rebuilding a row. *)
          if known_column term then Thm.reflexive ct
          else
            let
              val _ = reify_visits := !reify_visits + 1
            in
              (case if closed term then
                  Termtab.lookup (Synchronized.value reify_facts) term else NONE of
                SOME theorem =>
                  (Synchronized.change reify_cache_hits (fn count => count + 1); theorem)
              | NONE =>
                let
                  val _ = Synchronized.change reify_cache_misses (fn count => count + 1)
                  val direct =
                    (case body_cid term of
                      SOME cid =>
                        let val body = shallow_body cid in
                          if closed term andalso body aconv term
                          then SOME (Conv.rewr_conv (Thm.symmetric (column_step cid)) ct)
                          else NONE
                        end
                    | NONE => NONE)
                  val theorem =
                    (case direct of
                      SOME theorem => (Synchronized.change reify_body_hits
                        (fn count => count + 1); theorem)
                    | NONE =>
                        let
                          val children =
                            (case strip_comb term of
                              (Const (name, _), [_, _]) =>
                                if name = @{const_name Comma_CRT_Node}
                                then argument_at 0 reify_child_list ct
                                else Conv.combination_conv reify reify ct
                            | _ => (case term of
                                _ $ _ => Conv.combination_conv reify reify ct
                              | _ => Thm.reflexive ct))
                          val result = Thm.rhs_of children
                          val theorem =
                            (case body_cid (Thm.term_of result) of
                              NONE => children
                            | SOME cid => Thm.transitive children
                                (Conv.rewr_conv (Thm.symmetric (column_step cid)) result))
                        in theorem end)
                in
                  if closed term then remember_reify_fact term theorem
                  else check_reify_fact term theorem
                end)
            end
        end
      and reify_child ct =
        let val term = Thm.term_of ct in
          if term aconv @{term "Comma_CRT_Bool False"} then
            Conv.rewr_conv (Thm.symmetric (column_step 0)) ct
          else if term aconv @{term "Comma_CRT_Bool True"} then
            Conv.rewr_conv (Thm.symmetric (column_step 1)) ct
          else if known_column term then Thm.reflexive ct
          else reify ct
        end
      and reify_child_list ct =
        (case strip_comb (Thm.term_of ct) of
          (Const (name, _), [_, _]) =>
            if name = @{const_name Cons}
            then Conv.combination_conv (Conv.arg_conv reify_child) reify_child_list ct
            else Thm.reflexive ct
        | _ => Thm.reflexive ct)
      fun operands ct =
        (case Thm.term_of ct of
          _ $ _ => Conv.combination_conv operands unfold_column ct
        | _ => Thm.reflexive ct)

      fun evaluate context ct =
        let val request = Thm.term_of ct in
          (case Termtab.lookup (!facts) request of
            SOME theorem => (hits := !hits + 1; SOME theorem)
          | NONE =>
            (case Termtab.lookup (!admission_facts) request of
              SOME theorem => (hits := !hits + 1; SOME theorem)
            | NONE =>
              if not (closed request) orelse Termtab.defined (!active) request
              then NONE
              else
                (case admission_header_equation request of
                  SOME theorem => check_and_publish request theorem
                | NONE =>
                    let val expanded = operands ct in
                      if Thm.term_of (Thm.rhs_of expanded) aconv request then NONE
                      else
                        let
                          val _ = active := Termtab.update (request, ()) (!active)
                          val attempt = Exn.capture (fn () =>
                            let
                              val evaluated = Simplifier.rewrite context
                                (Thm.rhs_of expanded)
                              val named = reify (Thm.rhs_of evaluated)
                              val theorem = Thm.transitive expanded
                                (Thm.transitive evaluated named)
                            in check_and_publish request theorem end) ()
                          val _ = active := Termtab.delete request (!active)
                        in Exn.release attempt end
                    end)))
        end

      val patterns =
        [@{term "case_comma_crt_column bool_case node_case
            (column::comma_crt_column)"},
         @{term "comma_crt_admitted lower column"},
         @{term "comma_crt_supported column"},
         @{term "comma_crt_cofactor level digit column"},
         @{term "comma_crt_shift shift column"},
         @{term "comma_crt_negate column"},
         @{term "comma_crt_apply operation left right"},
         @{term "comma_crt_apply_from depth operation left right"},
         @{term "comma_crt_apply_shifted operation shift left right"},
         @{term "comma_crt_apply_shifted_from depth shift operation left right"},
         @{term "comma_crt_apply_shortcut operation left right"},
         @{term "comma_crt_shifted_apply_shortcut operation shift left right"},
         @{term "(left::comma_crt_column) = right"}]
      val apply_heads =
        [@{const_name comma_crt_apply}, @{const_name comma_crt_apply_from},
         @{const_name comma_crt_apply_shifted},
         @{const_name comma_crt_apply_shifted_from},
         @{const_name comma_crt_apply_shortcut},
         @{const_name comma_crt_shifted_apply_shortcut}]
      fun is_apply_pattern pattern =
        member (op =) apply_heads
          (case Term.head_of pattern of Const (name, _) => name | _ => "")
      val operation_patterns = filter_out is_apply_pattern patterns
      fun make_column_procedure name kind selected_patterns =
        Simplifier.make_simproc ctxt
          {name = name, kind = kind,
           lhss = map Comma_Selected_List_Conversion.schematize selected_patterns,
           proc = fn _ => evaluate, identifier = []}
      val procedure = Simplifier.make_simproc ctxt
        {name = "comma_semantic_b1_named_columns",
         kind = Simplifier.Congproc false,
         lhss = map Comma_Selected_List_Conversion.schematize patterns,
         proc = fn _ => evaluate, identifier = []}
      val post_procedure = Simplifier.make_simproc ctxt
        {name = "comma_semantic_b1_named_columns_after_operands",
         kind = Simplifier.Simproc,
         lhss = map Comma_Selected_List_Conversion.schematize patterns,
         proc = fn _ => evaluate, identifier = []}
      (* The production occurrence context gives recursive apply terms to the
         proof-producing DAG owner.  Keep the ordinary column procedures for
         other consumers, and expose versions that cannot preempt that owner. *)
      val operation_procedure = make_column_procedure
        "comma_semantic_b1_named_operation_columns"
        (Simplifier.Congproc false) operation_patterns
      val operation_post_procedure = make_column_procedure
        "comma_semantic_b1_named_operation_columns_after_operands"
        Simplifier.Simproc operation_patterns
      fun prove_columns_admitted_conversion target_ct =
        let
          val target = Thm.term_of target_ct
          val (predicate_requested, columns_requested) =
            (case strip_comb target of
              (Const (name, _), [predicate, columns]) =>
                if name = @{const_name list_all} then (predicate, columns)
                else error "B1 all-column admission target is not list_all"
            | _ => error "B1 all-column admission target has the wrong shape")
          val (admitted_lower, columns_name) =
            (case strip_comb predicate_requested of
              (Const (name, _), [lower]) =>
                if name = admitted_name then
                  (dest_nat lower,
                   (case columns_requested of
                     Const (column_name, _) => column_name
                   | _ => error "B1 admission target uses a nonconstant column table"))
                else error "B1 admission target uses another column predicate"
            | _ => error "B1 admission target predicate is malformed")
          val _ = if admitted_lower = 0 andalso
              columns_name = Sign.intern_const thy "comma_semantic_b1_crt_columns" andalso
              fastype_of target = HOLogic.boolT andalso closed target then ()
            else error "B1 admission target is not the published zero-level column list"
          fun checked_definition expected_name expected_type theorem message =
            let
              val equation = Local_Defs.meta_rewrite_rule ctxt theorem
              val left = Thm.term_of (Thm.lhs_of equation)
              val right = Thm.term_of (Thm.rhs_of equation)
              val name = (case left of Const (name, _) => name | _ => "")
              val _ = if name = expected_name andalso
                  fastype_of left = expected_type andalso
                  clean_equation equation left right
                then () else error message
            in (equation, right) end
          val (count_definition, count_value) = checked_definition
            (Sign.intern_const thy "comma_semantic_b1_crt_column_count") natT
            (Proof_Context.get_thm ctxt "comma_semantic_b1_crt_column_count_def")
            "B1 published column count definition has invalid authority"
          val (columns_definition, columns_body) = checked_definition
            (Sign.intern_const thy "comma_semantic_b1_crt_columns")
            (HOLogic.listT columnT)
            (Proof_Context.get_thm ctxt "comma_semantic_b1_crt_columns_def")
            "B1 published column-list definition has invalid authority"
          val declared_count = dest_nat count_value
          val _ = if declared_count = count then ()
            else error "B1 published column count disagrees with the validated DAG extent"
          val count_term = HOLogic.mk_number natT declared_count
          val columns_for_type = dagT --> natT --> HOLogic.listT columnT
          val columns_for = Const
            (@{const_name comma_semantic_b1_crt_columns_for}, columns_for_type)
          val count_constant = Const
            (Sign.intern_const thy "comma_semantic_b1_crt_column_count", natT)
          val expected_columns_body =
            columns_for $ expected_dag_constant $ count_constant
          val _ = if columns_body aconv expected_columns_body then ()
            else error "B1 published column list is not the DAG/count projection"
          val all_columns_rule = Drule.infer_instantiate ctxt
            [(("dag", 0), Thm.cterm_of ctxt expected_dag_constant),
             (("extent", 0), Thm.cterm_of ctxt count_term)]
            @{thm comma_semantic_b1_crt_columns_for_admitted}
          val expected_expansion =
            @{term "list_all :: (comma_crt_column => bool) => comma_crt_column list => bool"} $
              (@{term "comma_crt_admitted (0::nat)"}) $
              (columns_for $ expected_dag_constant $ count_term)
          val expand_context = put_simpset HOL_basic_ss ctxt
            addsimps [columns_definition, count_definition]
          val target_expansion = Simplifier.rewrite expand_context target_ct
          val _ = if Thm.term_of (Thm.rhs_of target_expansion) aconv expected_expansion
            then () else error "B1 column list definitions do not match the DAG extent"
          val proposition_expansion = Thm.combination
            (Thm.reflexive (Thm.cterm_of ctxt @{term Trueprop})) target_expansion
          val theorem = Thm.equal_elim
            (Thm.symmetric proposition_expansion) all_columns_rule
          val _ = if Thm.prop_of theorem aconv HOLogic.mk_Trueprop target andalso
              Thm.nprems_of theorem = 0 andalso null (Thm.hyps_of theorem) andalso
              null (Thm.tpairs_of theorem) andalso
              null (Thm_Deps.all_oracles [theorem]) then ()
            else error "B1 all-column admission certificate is not a clean target theorem"
        in theorem end
      val columns_table_name = Sign.intern_const thy "comma_semantic_b1_crt_columns"
      val columns_table_type = Sign.the_const_type thy columns_table_name
      val _ = if columns_table_type = HOLogic.listT columnT then ()
        else error "B1 published column table has an unexpected type"
      val columns_table = Const (columns_table_name, columns_table_type)
      val admitted_predicate = @{term "comma_crt_admitted (0::nat)"}
      val list_all = Const (@{const_name list_all},
        fastype_of admitted_predicate --> HOLogic.listT columnT --> @{typ bool})
      val all_columns_admitted_request =
        list_all $ admitted_predicate $ columns_table
      val all_columns_admitted_target =
        Thm.cterm_of ctxt all_columns_admitted_request
      val all_columns_admitted_fact = Unsynchronized.ref (NONE: thm option)
      val all_columns_admission_captures = Unsynchronized.ref 0
      val all_columns_admission_reuses = Unsynchronized.ref 0
      fun check_all_columns_admitted theorem =
        if Thm.prop_of theorem aconv HOLogic.mk_Trueprop all_columns_admitted_request andalso
            Thm.nprems_of theorem = 0 andalso null (Thm.hyps_of theorem) andalso
            null (Thm.tpairs_of theorem)
        then theorem
        else error "B1 cached whole-column admission fact changed authority"
      fun prove_columns_admitted target_ct =
        if Thm.term_of target_ct aconv all_columns_admitted_request then
          (case !all_columns_admitted_fact of
            SOME theorem =>
              (all_columns_admission_reuses := !all_columns_admission_reuses + 1;
               check_all_columns_admitted theorem)
          | NONE =>
              let
                val theorem = check_all_columns_admitted
                  (prove_columns_admitted_conversion all_columns_admitted_target)
                val _ = all_columns_admitted_fact := SOME theorem
                val _ = all_columns_admission_captures :=
                  !all_columns_admission_captures + 1
              in theorem end)
        else prove_columns_admitted_conversion target_ct
      fun prove_all_columns_admitted () =
        prove_columns_admitted all_columns_admitted_target
      val free_table_request = list_all $ admitted_predicate $
        Free ("untrusted_columns", HOLogic.listT columnT)
      val captures_before_free_table = !all_columns_admission_captures
      val reuses_before_free_table = !all_columns_admission_reuses
      val free_table_attempt = Exn.capture (fn () =>
        prove_columns_admitted (Thm.cterm_of ctxt free_table_request)) ()
      val _ = (case free_table_attempt of
        Exn.Exn (ERROR message) =>
          if message = "B1 admission target uses a nonconstant column table" then ()
          else error ("B1 free-table fixture raised another error: " ^ message)
      | Exn.Exn exn => Exn.reraise exn
      | Exn.Res _ => error "B1 all-column admission accepted a free table request")
      val _ = if !all_columns_admission_captures = captures_before_free_table andalso
          !all_columns_admission_reuses = reuses_before_free_table then ()
        else error "B1 free-table rejection changed the canonical admission cache"
      fun counters () =
        let
          val {calls, failed_calls, nodes, milliseconds} = derived_certification_stats ()
          val cofactor_counts = cofactor_transition_counts ()
        in
        " column_derived_certifier_calls=" ^ Int.toString calls ^
        " column_derived_certifier_failed=" ^ Int.toString failed_calls ^
        " column_derived_certifier_nodes=" ^ Int.toString nodes ^
        " column_derived_certifier_ms=" ^ LargeInt.toString milliseconds ^
        " column_nodes=" ^ Int.toString count ^
        " column_lookup_node_visits=" ^ Int.toString (!lookup_visits) ^
        " column_lookup_value_hits=" ^ Int.toString (!lookup_hits) ^
        " column_lookup_value_misses=" ^ Int.toString (!lookup_misses) ^
        " column_step_hits=" ^ Int.toString (!step_hits) ^
        " column_step_misses=" ^ Int.toString (!step_misses) ^
        " column_child_admission_hits=" ^
          Int.toString (!child_admission_hits) ^
        " column_child_admission_misses=" ^
          Int.toString (!child_admission_misses) ^
        " column_child_admission_refusals=" ^
          Int.toString (!child_admission_refusals) ^
        " column_lookup_value_ms=" ^ LargeInt.toString
          (Time.toMilliseconds (!lookup_value_ms)) ^
        (#counters directory_lookup_cache) () ^
        (#counters interval_lookup_cache) () ^
        " column_step_rewrite_ms=" ^ LargeInt.toString
          (Time.toMilliseconds (!step_rewrite_ms)) ^
        " column_step_admission_ms=" ^ LargeInt.toString
          (Time.toMilliseconds (!step_admission_ms)) ^
        " column_at_unfold_ms=" ^ LargeInt.toString
          (Time.toMilliseconds (!column_at_unfold_ms)) ^
        " column_head_opens=" ^ Int.toString (!opened) ^
        " column_reify_visits=" ^ Int.toString (!reify_visits) ^
        " column_reify_cache_hits=" ^ Int.toString
          (Synchronized.value reify_cache_hits) ^
        " column_reify_cache_misses=" ^ Int.toString
          (Synchronized.value reify_cache_misses) ^
        " column_reify_body_hits=" ^ Int.toString
          (Synchronized.value reify_body_hits) ^
        " column_reify_cache_races=" ^ Int.toString
          (Synchronized.value reify_cache_races) ^
        " column_reify_cache_retained=" ^ Int.toString
          (Termtab.size (Synchronized.value reify_facts)) ^
        " column_reify_cache_refusals=" ^ Int.toString
          (Synchronized.value reify_cache_refusals) ^
        " column_fact_hits=" ^ Int.toString (!hits) ^
        " column_fact_publications=" ^ Int.toString (!publications) ^
        " column_fact_capacity_refusals=" ^ Int.toString (!fact_capacity_refusals) ^
        " column_table_admission_captures=" ^
          Int.toString (!all_columns_admission_captures) ^
        " column_table_admission_reuses=" ^
          Int.toString (!all_columns_admission_reuses) ^
        " column_cofactor_transition_lookups=" ^
          Int.toString (#lookups cofactor_counts) ^
        " column_cofactor_transition_hits=" ^
          Int.toString (#hits cofactor_counts) ^
        " column_cofactor_transition_misses=" ^
          Int.toString (#misses cofactor_counts) ^
        " column_cofactor_transition_proofs=" ^
          Int.toString (#proofs cofactor_counts)
        end
    in
      {known_column = known_column, column_id = dest_column_cid,
       column_value = column_value,
       node_count = count, step = column_step, procedure = procedure,
       post_procedure = post_procedure,
       operation_procedure = operation_procedure,
       operation_post_procedure = operation_post_procedure,
       resolve_column = (fn term => Option.map column_step (dest_column_cid term)),
       reify = reify, reify_cache_hits = fn () => Synchronized.value reify_cache_hits,
       counters = counters, head_opens = fn () => !opened,
       cofactor_transition = cofactor_transition,
       cofactor_transition_counts = cofactor_transition_counts,
       cofactor_node_level = cofactor_node_level,
       source_bindings = fn cids => Comma_Semantic_B1_Column_Catalog.source_bindings_for (#interval directory_lookup_cache) ordered_blocks count cids,
       mass_node_row = Comma_Semantic_B1_Column_Catalog.mass_node_row count node,
       step_misses = fn () => !step_misses,
       prove_admitted = fn (lower, cid) => child_admission_fact lower cid,
       prove_columns_admitted = prove_columns_admitted,
       prove_all_columns_admitted = prove_all_columns_admitted,
       try_evaluate = evaluate}
    end
end
