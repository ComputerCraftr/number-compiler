(* Kernel transport for the locally compiled Boolean core guards.  The
   arena's shared IDs are never treated as evidence: each imported root gets
   a root-map derivation over the frozen Store table. *)
signature COMMA_FRONTIER24_MDD_IMPORT_CERTIFICATES =
sig
  type guard_import =
    {source_nodes: term, source_root: int,
     source_seeds: Comma_CRT_MDD_Arena.seed_node list,
     arena_roots: Comma_CRT_MDD_Arena.boolean_root list, arena_nodes: int list}
  val root_map_certificate:
    Comma_CRT_MDD_Certificate_Store.store -> Comma_CRT_MDD_Arena.arena ->
    guard_import -> thm
end

structure Comma_Frontier24_MDD_Import_Certificates =
struct
  structure Arena = Comma_CRT_MDD_Arena
  structure Store = Comma_CRT_MDD_Certificate_Store
  structure Utils = Comma_CRT_MDD_Proof_Utils

  type guard_import =
    {source_nodes: term, source_root: int,
     source_seeds: Arena.seed_node list, arena_roots: Arena.boolean_root list,
     arena_nodes: int list}

  val natT = @{typ nat}
  val boolT = @{typ bool}
  val source_nodeT = @{typ "bool comma_crt_mdd_node"}
  val target_nodeT = @{typ "nat comma_crt_mdd_node"}
  val source_nodesT = HOLogic.listT source_nodeT
  val nat_listT = HOLogic.listT natT
  val target_nodesT = HOLogic.listT target_nodeT

  fun nat n = HOLogic.mk_number natT n
  fun mk_if typ condition yes no =
    Const (@{const_name If}, boolT --> typ --> typ --> typ) $
      condition $ yes $ no

  fun list_nth listT elemT xs index =
    Const (@{const_name nth}, listT --> natT --> elemT) $ xs $ index

  fun source_node_term (Arena.Seed_Leaf 0) =
        Const (@{const_name Comma_CRT_MDD_Leaf}, boolT --> source_nodeT) $ @{term False}
    | source_node_term (Arena.Seed_Leaf 1) =
        Const (@{const_name Comma_CRT_MDD_Leaf}, boolT --> source_nodeT) $ @{term True}
    | source_node_term (Arena.Seed_Leaf _) = error "Boolean source leaf is not 0 or 1"
    | source_node_term (Arena.Seed_Branch (axis, children)) =
        Const (@{const_name Comma_CRT_MDD_Branch},
          natT --> nat_listT --> source_nodeT) $ nat axis $
          HOLogic.mk_list natT (map nat children)

  fun target_node_term (Arena.Leaf_Value label) =
        Const (@{const_name Comma_CRT_MDD_Leaf}, natT --> target_nodeT) $ nat label
    | target_node_term (Arena.Branch_At (axis, children)) =
        Const (@{const_name Comma_CRT_MDD_Branch},
          natT --> nat_listT --> target_nodeT) $ nat axis $
          HOLogic.mk_list natT (map nat children)

  fun root_map_term radices source_nodes target_nodes encode source target =
    let
      val ty = nat_listT --> source_nodesT --> target_nodesT -->
        (boolT --> natT) --> natT --> natT --> boolT
      val relation = Const (@{const_name comma_crt_mdd_root_map_certificate}, ty)
    in relation $ radices $ source_nodes $ target_nodes $ encode $ source $ target end

  val exact_prop = Utils.exact_prop

  fun prove ctxt proposition facts extra_simps =
    Goal.prove ctxt [] [] proposition
      (fn {context, ...} => Simplifier.asm_full_simp_tac
        (Comma_Entry_Arithmetic.natural_context context
          |> Simplifier.add_simps extra_simps
          |> Simplifier.add_simps facts) 1)

  fun prove_by_rule ctxt proposition rule facts extra_simps =
    Goal.prove ctxt [] [] proposition
      (fn {context,...} =>
        let
          val ss = Comma_Entry_Arithmetic.natural_context context
            |> Simplifier.add_simps extra_simps
            |> Simplifier.add_simps facts
          fun fact_tac fact i =
            (resolve_tac context [Thm.forall_elim_vars 0 fact]
              THEN_ALL_NEW assume_tac context) i
        in resolve_tac context [rule] 1 THEN
          ALLGOALS (fn i => FIRST
            (map (fn fact => fact_tac fact i) facts @
              [assume_tac context i, Simplifier.asm_full_simp_tac ss i])) end)

  fun instantiate ctxt theorem bindings = Drule.infer_instantiate ctxt
    (map (fn (name,term) => ((name,0),Thm.cterm_of ctxt term)) bindings) theorem

  fun certify_root_map ctxt store arena
      (import: guard_import) =
    let
      val source_nodes = #source_nodes import
      val target_nodes = Store.table store
      val radices = Store.radices store
      val seeds = #source_seeds import
      val mapped_roots = #arena_roots import
      val mapped_ids = #arena_nodes import
      val count = length seeds
      val _ = if count > 0 andalso length mapped_roots = count andalso
          length mapped_ids = count then ()
        else error "Core guard root map has inconsistent local/arena lengths"
      val encode = Abs ("guard", boolT,
        mk_if natT (Bound 0) (nat 1) (nat 0))
      val cache = Unsynchronized.ref (Inttab.empty: thm Inttab.table)
      val source_context = Store.context store
      val lookup_simp = @{thms nth_Cons' nth_Cons_0 list.simps list.size}

      fun source_binding index =
        let
          val request = list_nth source_nodesT source_nodeT source_nodes (nat index)
          val expected = Logic.mk_equals
            (request, source_node_term (List.nth (seeds,index)))
          val theorem = prove source_context expected [] lookup_simp
        in exact_prop source_context "Local core-guard node lookup" expected theorem end

      fun target_binding source_index target_index =
        let
          val mapped_root = List.nth (mapped_roots,source_index)
          val root_index = Arena.boolean_index arena mapped_root
          val _ = if root_index = target_index then ()
            else error "Core-guard shared index disagrees with its mapped root"
          val theorem = Store.lookup store target_index
          val expected = Logic.mk_equals
            (list_nth target_nodesT target_nodeT target_nodes (nat target_index),
              target_node_term (Arena.boolean_view arena mapped_root))
        in exact_prop source_context "Frozen core-guard node lookup" expected theorem end

      fun bound_source index =
        let
          val proposition = HOLogic.mk_Trueprop
            (HOLogic.mk_binrel @{const_name less}
              (nat index, Const (@{const_name size}, source_nodesT --> natT) $ source_nodes))
          val theorem = prove source_context proposition [] lookup_simp
        in exact_prop source_context "Local core-guard node bound" proposition theorem end

      fun relation source target = HOLogic.mk_Trueprop
        (root_map_term radices source_nodes target_nodes encode (nat source) (nat target))

      fun prove_child_list source_children target_at axis radix child_theorems =
        let
          val slotT = natT
          val slot = Free ("slot",slotT)
          val source_nth = list_nth nat_listT natT source_children slot
          val target_nth = target_at slot
          val body = root_map_term radices source_nodes target_nodes encode
            source_nth target_nth
          val predicate = Term.lambda slot body
          val _ = if length child_theorems = radix then ()
            else error "Core-guard child proofs do not match the branch radix"
          val successor_cache =
            Comma_Selected_List_Conversion.make_successor_cache source_context radix
          val reduction_context =
            Comma_Entry_Arithmetic.natural_context source_context
            |> Simplifier.add_simps
              (@{thms list.simps list.size nth_Cons_0 nth_Cons_Suc nth_Cons'})
          fun prove_item index =
            let
              val application = predicate $ nat index
              val beta = Thm.beta_conversion false
                (Thm.cterm_of source_context application)
              val normalized_term = Thm.term_of (Thm.rhs_of beta)
              val normalized_expected = HOLogic.mk_Trueprop normalized_term
              val normalized = Utils.prove_exact source_context
                "Concrete core-guard child relation" normalized_expected
                (fn context => Method.insert_tac context
                    [List.nth (child_theorems,index)] 1 THEN
                  Simplifier.asm_full_simp_tac reduction_context 1)
            in Utils.predicate_application source_context
              "Core-guard child predicate application" predicate (nat index)
              normalized end
          val all = Comma_Selected_List_Conversion.prove_indexed_list_all
            {ctxt=source_context, predicate=predicate, bound=radix,
             prove_item=prove_item,
             zero_fact = @{thm comma_indexed_all_zero},
             step_fact = @{thm comma_indexed_all_Suc},
             successor_equation= #equation successor_cache}
          val slot_free = Free ("slot",slotT)
          val point = root_map_term radices source_nodes target_nodes encode
            (list_nth nat_listT natT source_children slot_free)
            (target_at slot_free)
          val radix_at = list_nth nat_listT natT radices (nat axis)
          val bound = HOLogic.mk_binrel @{const_name less} (slot_free,radix_at)
          val universal = Logic.all slot_free
            (Logic.mk_implies (HOLogic.mk_Trueprop bound, HOLogic.mk_Trueprop point))
          val selected = @{thm comma_crt_mdd_indexed_allD} OF [all]
          val theorem = Utils.prove_exact source_context
            "Finite core-guard child relation" universal
            (fn context => resolve_tac context [selected] 1 THEN
              Simplifier.asm_full_simp_tac
                (Comma_Entry_Arithmetic.natural_context context
                  |> Simplifier.add_simps lookup_simp) 1)
        in theorem end

      fun cert source =
        (case Inttab.lookup (!cache) source of
          SOME theorem => theorem
        | NONE =>
            let
              val target = List.nth (mapped_ids,source)
              val source_bound_thm = bound_source source
              val target_bound_thm = Store.bound store target
              val source_node_thm = source_binding source
              val target_node_thm = target_binding source target
              val proposition = relation source target
              val theorem = (case (List.nth (seeds,source),
                  Arena.boolean_view arena (List.nth (mapped_roots,source))) of
                (Arena.Seed_Leaf label, Arena.Leaf_Value output) =>
                  let
                    val expected_output = if label=0 then 0 else if label=1 then 1
                      else error "Local Boolean source leaf is malformed"
                    val _ = if output=expected_output then ()
                      else error "Frozen arena changed a Boolean guard leaf"
                    val payload = if label=0 then @{term False} else @{term True}
                    val rule = instantiate source_context
                      @{thm comma_crt_mdd_root_map_certificate.map_leaf}
                      [("radices",radices),("source_nodes",source_nodes),
                       ("target_nodes",target_nodes),("encode",encode),
                       ("source",nat source),("target",nat target),
                       ("payload",payload)]
                    val facts = [source_bound_thm,target_bound_thm,
                      source_node_thm,target_node_thm]
                  in prove_by_rule source_context proposition
                    rule facts [] end
              | (Arena.Seed_Branch (axis,source_children), target_view) =>
                  let
                    val target = List.nth (mapped_ids,source)
                    val mapped_children = map (fn child =>
                      List.nth (mapped_ids,child)) source_children
                    val source_children_term =
                      HOLogic.mk_list natT (map nat source_children)
                    val child_theorems = map cert source_children
                    val radix = List.nth (Arena.radices arena,axis)
                    val target_children = (case target_view of
                      Arena.Branch_At (target_axis,children) =>
                        if target_axis=axis andalso children=mapped_children then
                          SOME children
                        else NONE
                    | Arena.Leaf_Value _ => NONE)
                    fun child_relation target_at =
                      prove_child_list source_children_term target_at axis radix
                        child_theorems
                  in case target_children of
                    SOME children =>
                      let
                        val target_children_term = HOLogic.mk_list natT (map nat children)
                        val universal = child_relation
                          (fn slot => list_nth nat_listT natT target_children_term slot)
                        val rule = instantiate source_context
                          @{thm comma_crt_mdd_root_map_certificate.map_branch}
                          [("radices",radices),("source_nodes",source_nodes),
                           ("target_nodes",target_nodes),("encode",encode),
                           ("source",nat source),("target",nat target),
                           ("axis",nat axis),
                           ("source_children",source_children_term),
                           ("target_children",target_children_term)]
                        val facts = [source_bound_thm,target_bound_thm,
                          source_node_thm,target_node_thm,universal]
                      in prove_by_rule source_context proposition
                        rule facts lookup_simp end
                  | NONE =>
                      let
                        val _ = if List.all (fn mapped_child => mapped_child=target)
                            mapped_children then ()
                          else error "Frozen guard branch is neither an exact branch nor a reduced alias"
                        val universal = child_relation (fn _ => nat target)
                        val rule = instantiate source_context
                          @{thm comma_crt_mdd_root_map_certificate.map_reduced_alias}
                          [("radices",radices),("source_nodes",source_nodes),
                           ("target_nodes",target_nodes),("encode",encode),
                           ("source",nat source),("target",nat target),
                           ("axis",nat axis),
                           ("source_children",source_children_term)]
                        val facts = [source_bound_thm,target_bound_thm,
                          source_node_thm,universal]
                      in prove_by_rule source_context proposition
                        rule facts lookup_simp end
                  end
                | _ => error "Core guard local/frozen node kinds disagree")
              val theorem = Utils.exact_prop source_context
                "Core guard root-map certificate" proposition theorem
              val _ = cache := Inttab.update (source,theorem) (!cache)
            in theorem end)
      val root = #source_root import
    in cert root end

  fun root_map_certificate store arena import =
    certify_root_map (Store.context store) store arena import

end
