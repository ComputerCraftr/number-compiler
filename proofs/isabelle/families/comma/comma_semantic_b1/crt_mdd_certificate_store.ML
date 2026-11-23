(* One immutable semantic table and one wellformedness proof per frozen arena.
   A single nested chunk constant backs its balanced root; bounded indexed
   conversion avoids per-chunk definitions and full-table flattening. *)
signature COMMA_CRT_MDD_CERTIFICATE_STORE =
sig
  type store
  datatype node = Leaf of int | Branch of int * int list
  val make: string -> Comma_CRT_MDD_Arena.arena -> local_theory -> store * local_theory
  val context: store -> Proof.context
  val table: store -> term
  val radices: store -> term
  val wellformed: store -> thm
  val node_count: store -> int
  val node: store -> int -> node
  val node_term: node -> term
  val lookup: store -> int -> thm
  val phase_leaf: store -> int -> thm
  val bound: store -> int -> thm
  val branch_width: store -> int -> thm
  val action_index: store -> Comma_CRT_MDD_Arena.action_root -> int
  val payload_cap: store -> int -> Comma_CRT_MDD_Arena.action_root -> thm
  val boolean_index: store -> Comma_CRT_MDD_Arena.boolean_root -> int
  val bind_witness: store -> Comma_CRT_MDD_Arena.bind_key -> Comma_CRT_MDD_Arena.bind_witness
  val priority_witness: store -> Comma_CRT_MDD_Arena.priority_key ->
    Comma_CRT_MDD_Arena.priority_witness
  val priority_normalize: store -> Comma_CRT_MDD_Arena.priority_key ->
    Comma_CRT_MDD_Arena.priority_key
  val priority_normalize_trace: store -> Comma_CRT_MDD_Arena.priority_key ->
    Comma_CRT_MDD_Arena.priority_normalization
  val statistics: store -> string
end

structure Comma_CRT_MDD_Certificate_Store :> COMMA_CRT_MDD_CERTIFICATE_STORE =
struct
  structure Arena = Comma_CRT_MDD_Arena
  structure Proof_Utils = Comma_CRT_MDD_Proof_Utils
  datatype node = Leaf of int | Branch of int * int list
  val natT = @{typ nat}
  val natOptionT = Type (@{type_name option}, [natT])
  val nodeT = @{typ "nat comma_crt_mdd_node"}
  val nodesT = HOLogic.listT nodeT
  fun nat n = HOLogic.mk_number natT n
  fun nth nodes index = Const (@{const_name nth}, nodesT --> natT --> nodeT) $
    nodes $ nat index
  fun length_term nodes = Const (@{const_name size}, nodesT --> natT) $ nodes
  val closed = Proof_Utils.closed
  val natural = Proof_Utils.dest_nat "MDD node" natT

  fun parse_node term =
    (case Term.strip_comb term of
      (Const (name,_),[payload]) =>
        if name = @{const_name Comma_CRT_MDD_Leaf} then Leaf (natural payload)
        else error "MDD node has an unknown leaf constructor"
    | (Const (name,_),[axis,children]) =>
        if name = @{const_name Comma_CRT_MDD_Branch} then
          Branch (natural axis,map natural (HOLogic.dest_list children))
        else error "MDD node has an unknown branch constructor"
    | _ => error "MDD node is not a literal constructor")

  fun node_term (Leaf payload) =
        Const (@{const_name Comma_CRT_MDD_Leaf},natT --> nodeT) $ nat payload
    | node_term (Branch (axis,children)) =
        Const (@{const_name Comma_CRT_MDD_Branch},
          natT --> @{typ "nat list"} --> nodeT) $ nat axis $
          HOLogic.mk_list natT (map nat children)

  datatype store = Store of
    {arena: Arena.arena, ctxt: Proof.context, table: term, radices: term,
     count: int, nodes: node Vector.vector,
     wellformed: thm, lookup: int -> thm, bound: int -> thm,
     branch_width: int -> thm,
     phase_leaf_cache: thm Inttab.table Unsynchronized.ref,
     statistics: unit -> string}

  fun context (Store data) = #ctxt data
  fun table (Store data) = #table data
  fun radices (Store data) = #radices data
  fun wellformed (Store data) = #wellformed data
  fun node_count (Store data) = #count data
  fun statistics (Store data) = #statistics data ()
  fun check_index (Store data) index =
    if 0 <= index andalso index < #count data then index
    else error "MDD root is outside its frozen certificate table"
  fun lookup (store as Store data) index = #lookup data (check_index store index)
  fun node (store as Store data) index =
    Vector.sub (#nodes data,check_index store index)
  fun bound (store as Store data) index = #bound data (check_index store index)
  fun branch_width (store as Store data) index =
    #branch_width data (check_index store index)
  fun phase_leaf (store as Store data) index =
    let
      val index = check_index store index
      val payload = (case Vector.sub (#nodes data,index) of
        Leaf value => value
      | Branch _ => error "MDD phase-leaf request names a branch")
    in
      (case Inttab.lookup (!(#phase_leaf_cache data)) index of
        SOME theorem => theorem
      | NONE =>
          let
            val ctxt = #ctxt data
            val phase = Free ("mdd_phase_leaf_phase",natT)
            val root = nat index
            val eval = Const (@{const_name comma_crt_mdd_eval_phase},
              @{typ "nat list"} --> nodesT --> natT --> natT --> natOptionT) $
              #radices data $ #table data $ phase $ root
            val some = Const (@{const_name Some},natT --> natOptionT) $ nat payload
            val body = HOLogic.mk_Trueprop (HOLogic.mk_eq (eval,some))
            val expected = Logic.all phase body
            val expected_lookup = Logic.mk_equals
              (nth (#table data) index,node_term (Leaf payload))
            val leaf_lookup = Proof_Utils.exact_prop ctxt
              "Frozen MDD phase-leaf row" expected_lookup (#lookup data index)
            val theorem = @{thm comma_crt_mdd_eval_phase_leaf} OF
              [#wellformed data,#bound data index,
               leaf_lookup RS @{thm meta_eq_to_obj_eq}]
            val pointwise = Drule.infer_instantiate ctxt
              [(("phase",0),Thm.cterm_of ctxt phase)] theorem
            val generalized = Thm.forall_intr (Thm.cterm_of ctxt phase) pointwise
            val theorem = Proof_Utils.exact_prop ctxt
              "Frozen MDD phase leaf evaluation" expected generalized
            val _ = #phase_leaf_cache data :=
              Inttab.update (index,theorem) (!(#phase_leaf_cache data))
          in theorem end)
    end
  fun action_index (store as Store data) root =
    check_index store (Arena.action_index (#arena data) root)
  (* The cache belongs to one frozen Store and one cap. The action handle is
     independently authenticated before any numeric node ID is consulted. *)
  fun payload_cap store maximum =
    let
      val _ = if maximum >= 0 then () else error "MDD payload cap must be nonnegative"
      val ctxt = context store
      val limit = nat maximum
      val scalar = Comma_Entry_Arithmetic.natural_context ctxt
      val booleans = scalar |> Simplifier.add_simps @{thms ball_simps set_simps list.simps}
      val predicate = @{term comma_crt_mdd_payload_cap} $ table store
      fun cap child = predicate $ child $ limit
      fun prove description simps goal = Proof_Utils.prove_exact ctxt description
        (HOLogic.mk_Trueprop goal) (fn _ => simp_tac simps 1)
      val cache = Unsynchronized.ref Inttab.empty
      fun visit index =
        let val goal = HOLogic.mk_Trueprop (cap (nat index))
        in
          (case Inttab.lookup (!cache) index of
            SOME theorem => theorem
          | NONE =>
              let
                val within = bound store index
                val equation = lookup store index RS @{thm meta_eq_to_obj_eq}
                val theorem =
                  (case node store index of
                    Leaf payload =>
                      let
                        val _ = if payload <= maximum then ()
                          else error "Reachable MDD payload exceeds its cap"
                        val local_bound = prove "MDD leaf payload cap" scalar
                          (HOLogic.mk_binrel @{const_name less_eq} (nat payload,limit))
                      in @{thm comma_crt_mdd_payload_cap_leaf} OF [within,equation,local_bound] end
                  | Branch (_,children) =>
                      let
                        val order = @{thm comma_crt_mdd_payload_branch_child_order} OF
                          [wellformed store,within,equation]
                        val facts = map visit (distinct (op =) children)
                        val child = Free ("payload_cap_child",natT)
                        val set = @{term "set :: nat list => nat set"} $
                          HOLogic.mk_list natT (map nat children)
                        val coverage = prove "MDD branch payload cap" (Simplifier.add_simps facts booleans)
                          (@{term "Ball :: nat set => (nat => bool) => bool"} $ set $
                            Term.lambda child (cap child))
                      in @{thm comma_crt_mdd_payload_cap_branch} OF
                        [within,equation,order,coverage] end)
                val checked = Proof_Utils.exact_prop ctxt "Frozen MDD payload cap" goal theorem
                val _ = cache := Inttab.update (index,checked) (!cache)
              in checked end)
        end
    in fn root => visit (action_index store root) end

  fun boolean_index (store as Store data) root =
    check_index store (Arena.boolean_index (#arena data) root)
  fun bind_witness (store as Store data) key =
    let
      fun check_key (source,fallback,mapping) =
        List.app (fn id => ignore (check_index store id))
          (source :: fallback :: map #2 mapping)
      val _ = check_key key
      val witness = Arena.bind_witness (#arena data) key
      val _ = check_key (#key witness)
      val _ = check_index store (#result witness)
      val _ = (case #step witness of
        Arena.Bind_Leaf _ => ()
      | Arena.Bind_Branch (_,children) => List.app check_key children
      | Arena.Bind_Selected_Leaf_Branch (_,rows) =>
          List.app (fn (source,_,target,result) =>
            List.app (fn id => ignore (check_index store id)) [source,target,result]) rows)
    in witness end

  fun priority_normalize_trace (store as Store data) key =
    let
      fun check_key (pairs,fallback) =
        List.app (fn id => ignore (check_index store id))
          (fallback :: maps (fn (guard,action) => [guard,action]) pairs)
      val _ = check_key key
      val normalized = Arena.priority_normalize_trace (#arena data) key
      val _ = check_key (#key normalized)
    in normalized end

  fun priority_normalize store key = #key (priority_normalize_trace store key)

  fun priority_witness (store as Store data) key =
    let
      fun check_key (pairs,fallback) =
        List.app (fn id => ignore (check_index store id))
          (fallback :: maps (fn (guard,action) => [guard,action]) pairs)
      val canonical = priority_normalize store key
      val witness = Arena.priority_witness (#arena data) key
      val _ = if #key witness=canonical then () else error "Priority witness key differs"
      val _ = ignore (check_index store (#result witness))
      val _ = (case #step witness of
          Arena.Priority_Fallback => ()
        | Arena.Priority_Skip child => check_key child
        | Arena.Priority_Take => ()
        | Arena.Priority_Leaf _ => ()
        | Arena.Priority_Branch (_,children) => List.app check_key children)
    in witness end

  val exact_closed = Comma_CRT_Balanced_Table.exact_closed
  val specialize_object_all = Comma_CRT_Balanced_Table.specialize_object_all
  val list_size = Comma_CRT_Balanced_Table.list_size

  fun make name arena lthy =
    let
      val leaf_capacity = 128
      fun checkpoint stage = Comma_Proof_Profile.report
        ("MDD Store " ^ name ^ " stage=" ^ stage)
      val count = Arena.node_count arena
      val _ = if count > 0 andalso count <= 65536 then () else
        error "MDD certificate table exceeds the indexed publication bound"
      val _ = checkpoint ("table-term-start count=" ^ Int.toString count)
      val nodes = Arena.table_term arena
      val _ = if fastype_of nodes = nodesT andalso closed nodes then () else
        error "MDD certificate needs a closed natural-payload table"
      val original_rows = HOLogic.dest_list nodes
      val _ = if length original_rows = count then () else
        error "MDD arena node count disagrees with its frozen row vector"
      val node_views = Vector.fromList (map parse_node original_rows)
      val radix_term = HOLogic.mk_list natT (map nat (Arena.radices arena))
      val (published,lthy') = Comma_CRT_Balanced_Table.make name nodeT original_rows lthy
      val table = #table published
      val root_size = #size published
      val lookup = #lookup published
      val selected_elapsed = #selected_elapsed published
      val segment_elapsed = #segment_elapsed published
      val bound_elapsed = #bound_elapsed published
      val offset_elapsed = #offset_elapsed published
      val ctxt = Local_Theory.target_of lthy'
      val definition_context = Comma_Entry_Arithmetic.natural_context ctxt
        |> Simplifier.add_simps [root_size]
      val ordered_elapsed = Unsynchronized.ref Time.zeroTime
      fun elapsed_ms elapsed = LargeInt.toString (Time.toMilliseconds (!elapsed))
      fun timed elapsed action =
        let val started = Time.now ()
            val result = action ()
            val _ = elapsed := Time.+ (!elapsed,Time.- (Time.now (),started))
        in result end
      val axis_cache = Unsynchronized.ref (Inttab.empty: thm Inttab.table)
      val axis_context = put_simpset HOL_basic_ss ctxt
        |> Simplifier.add_simps @{thms comma_crt_mdd_node_axis.simps}
      fun axis_value (Leaf _) = Const (@{const_name None},natOptionT)
        | axis_value (Branch (axis,_)) =
            Const (@{const_name Some},natT --> natOptionT) $ nat axis
      fun axis_lookup index =
        (case Inttab.lookup (!axis_cache) index of
          SOME theorem => theorem
        | NONE =>
            let
              val node_lookup = lookup index
              val axis_const = Const (@{const_name comma_crt_mdd_node_axis},
                nodeT --> natOptionT)
              val request = axis_const $ nth table index
              val applied = Thm.combination
                (Thm.reflexive (Thm.cterm_of ctxt axis_const)) node_lookup
              val reduced = Simplifier.rewrite axis_context (Thm.rhs_of applied)
              val theorem = Thm.transitive applied reduced
              val expected = Logic.mk_equals
                (request,axis_value (Vector.sub (node_views,index)))
              val theorem = exact_closed expected theorem
              val _ = axis_cache := Inttab.update (index,theorem) (!axis_cache)
            in theorem end)

      val node_context = definition_context |> Simplifier.add_simps
        @{thms list.simps list.size list_all_Cons_iff list_all_Nil_iff
          option.simps nth_Cons_0 nth_Cons_Suc nth_Cons'}
      val predicate = Const (@{const_name comma_crt_mdd_node_ordered},
        @{typ "nat list"} --> nodesT --> natT --> @{typ bool}) $ radix_term $ table
      fun checked_true label context proposition =
        let
          val expected = HOLogic.mk_Trueprop proposition
          val conversion = Simplifier.rewrite context
            (Thm.cterm_of ctxt proposition)
          val reduced = Thm.term_of (Thm.rhs_of conversion)
          val _ = if reduced aconv @{term True} then ()
            else error (label ^ " did not reduce to True")
          val theorem = conversion RS @{thm meta_eq_to_obj_eq} RS @{thm eqTrueE}
        in exact_closed expected theorem end
      fun less left right = HOLogic.mk_binrel @{const_name less} (left,right)
      fun unique_ids ids =
        let
          fun add id (seen, kept) =
            if Inttab.defined seen id then (seen, kept)
            else (Inttab.update (id, ()) seen, id::kept)
          val (_, reversed) = fold add ids (Inttab.empty, [])
        in rev reversed end
      (* Closed generic branch facts are owned by this frozen store.  The
         universally quantified width theorem is reusable for every concrete
         child list of the same arity, without weakening the child guard. *)
      val branch_shapes = Unsynchronized.ref (Symtab.empty:
        (thm * thm * thm) Symtab.table)
      val branch_shape_hits = Unsynchronized.ref 0
      val branch_shape_misses = Unsynchronized.ref 0
      fun branch_shape axis arity =
        let val key = Int.toString axis ^ ":" ^ Int.toString arity in
          case Symtab.lookup (!branch_shapes) key of
            SOME facts => (branch_shape_hits := !branch_shape_hits + 1; facts)
          | NONE =>
              let
                val _ = branch_shape_misses := !branch_shape_misses + 1
                val axis_term = nat axis
                val radix_at = Const (@{const_name nth},
                  @{typ "nat list"} --> natT --> natT) $ radix_term $ axis_term
                val axis_bound = checked_true "MDD reusable axis bound" node_context
                  (less axis_term (list_size radix_term))
                val positive = checked_true "MDD reusable positive radix" node_context
                  (less (nat 0) radix_at)
                val names = map (fn n => "mdd_branch_child_" ^ Int.toString n)
                  (0 upto (arity-1))
                val variables = map (fn name => Free (name,natT)) names
                val generic_width = HOLogic.mk_eq
                  (list_size (HOLogic.mk_list natT variables),radix_at)
                val quantified = fold_rev (fn name => fn body =>
                  HOLogic.mk_all (name,natT,body)) names generic_width
                val expected = HOLogic.mk_Trueprop quantified
                val width = Proof_Utils.prove_exact ctxt
                  "MDD reusable branch width" expected (fn proof_ctxt =>
                    REPEAT_DETERM (resolve_tac proof_ctxt [@{thm allI}] 1)
                    THEN Simplifier.asm_full_simp_tac node_context 1)
                val facts = (axis_bound,positive,width)
                val _ = branch_shapes := Symtab.update (key,facts)
                  (!branch_shapes)
              in facts end
        end
      fun specialize_branch_width children theorem =
        fold (fn child => fn current =>
          specialize_object_all ctxt (nat child) current) children theorem

      fun prove_item index =
        let
          val _ = if index mod 256 = 0 then checkpoint
            ("node-start index=" ^ Int.toString index ^
             " selected_ms=" ^ elapsed_ms selected_elapsed ^
             " segment_ms=" ^ elapsed_ms segment_elapsed ^
             " bound_ms=" ^ elapsed_ms bound_elapsed ^
             " offset_ms=" ^ elapsed_ms offset_elapsed ^
             " ordered_ms=" ^ elapsed_ms ordered_elapsed) else ()
          val expected = HOLogic.mk_Trueprop (predicate $ nat index)
          val node_lookup = lookup index
          val node_view = Vector.sub (node_views,index)
          val children = (case node_view of Leaf _ => [] | Branch (_,ids) => ids)
          val child_facts = map axis_lookup (unique_ids children)
          val theorem = timed ordered_elapsed (fn () =>
            let
              val node_binding = node_lookup RS @{thm meta_eq_to_obj_eq}
            in case node_view of
              Leaf _ =>
                let
                  val root_bound = checked_true "MDD ordered-row root bound"
                    node_context (less (nat index) (length_term table))
                in
                (Drule.infer_instantiate ctxt
                  [(("radices",0),Thm.cterm_of ctxt radix_term)]
                  @{thm comma_crt_mdd_node_ordered_leaf_intro}) OF
                  [root_bound,node_binding]
                end
            | Branch (axis,children) =>
                let
                  val children_term = HOLogic.mk_list natT (map nat children)
                  val (axis_bound',positive',generic_width) =
                    branch_shape axis (length children)
                  val width' = specialize_branch_width children generic_width
                  val child = Free ("mdd_ordered_child",natT)
                  val child_node = Const (@{const_name nth},nodesT --> natT --> nodeT) $
                    table $ child
                  val child_axis = Const (@{const_name comma_crt_mdd_node_axis},
                    nodeT --> natOptionT) $ child_node
                  val child_axis_guard = Const (@{const_name case_option},
                    @{typ "bool => (nat => bool) => nat option => bool"}) $
                      @{term True} $
                      Term.lambda (Free ("mdd_ordered_child_axis",natT))
                        (less (nat axis) (Free ("mdd_ordered_child_axis",natT))) $
                      child_axis
                  val child_property = Term.lambda child
                    (HOLogic.mk_conj (less child (nat index),child_axis_guard))
                  val child_list_all = Const (@{const_name list_all},
                    fastype_of child_property --> @{typ "nat list"} --> @{typ bool}) $
                      child_property $ children_term
                  val root_bound = checked_true "MDD ordered-row root bound"
                    node_context (less (nat index) (length_term table))
                  val child_context = node_context |> Simplifier.add_simps child_facts
                  val child_order = checked_true "MDD ordered-row child guards"
                    child_context child_list_all
                in
                  @{thm comma_crt_mdd_node_ordered_branch_intro} OF
                    [root_bound,node_binding,axis_bound',positive',width',child_order]
                end
            end)
          val _ = if index mod 256 = 255 then checkpoint
            ("node-complete index=" ^ Int.toString index ^
             " selected_ms=" ^ elapsed_ms selected_elapsed ^
             " segment_ms=" ^ elapsed_ms segment_elapsed ^
             " bound_ms=" ^ elapsed_ms bound_elapsed ^
             " offset_ms=" ^ elapsed_ms offset_elapsed ^
             " ordered_ms=" ^ elapsed_ms ordered_elapsed) else ()
        in exact_closed expected theorem end
      val successors = Comma_Selected_List_Conversion.make_successor_cache ctxt count
      val _ = checkpoint "indexed-wellformedness-start"
      val all_nodes = Comma_Selected_List_Conversion.prove_indexed_list_all
        {ctxt=ctxt, predicate=predicate, bound=count, prove_item=prove_item,
         zero_fact= @{thm comma_indexed_all_zero},
         step_fact= @{thm comma_indexed_all_Suc}, successor_equation= #equation successors}
      val _ = checkpoint "indexed-wellformedness-complete"
      val wf_rule = Drule.infer_instantiate ctxt
        [( ("radices",0), Thm.cterm_of ctxt radix_term),
         ( ("nodes",0), Thm.cterm_of ctxt table)]
        @{thm comma_frontier24_table_wellformed_iff_list_all}
      val length_context = Comma_Entry_Arithmetic.natural_context ctxt
        |> Simplifier.add_simps [root_size]
      val normalized_rule = Simplifier.full_simplify length_context wf_rule
      val wellformed = @{thm iffD2} OF [normalized_rule, all_nodes]
      val expected_wf = HOLogic.mk_Trueprop
        (Const (@{const_name comma_crt_mdd_table_wellformed},
          @{typ "nat list"} --> nodesT --> @{typ bool}) $ radix_term $ table)
      val wellformed = exact_closed expected_wf wellformed
      val _ = checkpoint "native-audit-start"
      val _ = Comma_Proof_Dependency_Audit.require_native_clean ctxt
        "One frozen MDD arena wellformedness certificate" [wellformed]
      val _ = checkpoint "native-audit-complete"
      val bounds = Unsynchronized.ref (Inttab.empty: thm Inttab.table)
      fun bound index =
        (case Inttab.lookup (!bounds) index of
          SOME theorem => theorem
        | NONE =>
            let
              val expected = HOLogic.mk_Trueprop
                (HOLogic.mk_binrel @{const_name less} (nat index, length_term table))
              val theorem = exact_closed expected
                (Goal.prove ctxt [] [] expected (fn _ =>
                  Simplifier.asm_full_simp_tac length_context 1))
              val _ = bounds := Inttab.update (index,theorem) (!bounds)
            in theorem end)
      fun branch_width index =
        (case Vector.sub (node_views,index) of
          Leaf _ => error "MDD branch-width request names a leaf"
        | Branch (axis,children) =>
            let
              val (_,_,generic) = branch_shape axis (length children)
              val expected = HOLogic.mk_Trueprop (HOLogic.mk_eq
                (list_size (HOLogic.mk_list natT (map nat children)),
                 Const (@{const_name nth}, @{typ "nat list"} --> natT --> natT) $
                   radix_term $ nat axis))
            in exact_closed expected (specialize_branch_width children generic) end)
      val phase_leaf_cache = Unsynchronized.ref (Inttab.empty: thm Inttab.table)
      val store = Store {arena=arena, ctxt=ctxt, table=table,
        radices=radix_term, count=count, nodes=node_views, wellformed=wellformed,
        lookup=lookup, bound=bound, branch_width=branch_width,
        phase_leaf_cache=phase_leaf_cache,
        statistics=fn () => #statistics published () ^
          " ordered_item_ms=" ^ elapsed_ms ordered_elapsed ^
          " branch_shape_hits=" ^ Int.toString (!branch_shape_hits) ^
          " branch_shape_misses=" ^ Int.toString (!branch_shape_misses) ^
          " node_axis_equations=" ^ Int.toString (Inttab.size (!axis_cache)) ^
          " phase_leaf_certificates=" ^
            Int.toString (Inttab.size (!phase_leaf_cache))}
    in (store,lthy') end
end
