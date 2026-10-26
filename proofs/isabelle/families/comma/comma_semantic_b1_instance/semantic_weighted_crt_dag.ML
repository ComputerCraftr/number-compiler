(* Ephemeral hash-consed weighted CRT decision DAG and its checked normalization
   proof constructor. Arena addresses and proof-cache entries are publication-local. *)
signature COMMA_SEMANTIC_WEIGHTED_CRT_DAG =
sig
  datatype graph_edge = Goto of int | Live of int | Stop of int | Invalid
  type graph_node = {period: int, actions: graph_edge Vector.vector}
  type progress = string -> string -> unit
  type diagram
  type arena
  type composer
  type composition =
    {span: int, slot: int, left: diagram, rights: diagram Vector.vector,
     raw: diagram, normalized: diagram}
  type node_build =
    {raw: diagram, normalized: diagram, normalization_equation: thm}
  type terminal_summary =
    {all_stopped: bool, max_height: int, terminal_paths: int}
  type source_action =
    {cid: int, diagram: diagram, action: term, compiler_equation: thm,
     normalization_equation: thm}
  type serializer
  type normalization_proof_cache
  type publication =
    {arena: arena, root_cids: int list, node_actions: (int * diagram) list,
     node_builds: (int * node_build) list,
     base: diagram Vector.vector, normalized_base: diagram Vector.vector,
     powers: (int * diagram Vector.vector) list,
     final: diagram Vector.vector,
     normalizations: (diagram * diagram) list,
     compositions: composition list,
     normalization_serializer: serializer,
     normalization_cache: normalization_proof_cache,
     stats: unit -> string}
  type checked_publication =
    {publication: publication,
     compiler_cids: int list,
     node_action_terms: (int * term) list,
     compiler_local_actions: (int * term) list,
     compiler_equations: thm list,
     composition_equations: thm list,
     normalization_equations: thm list,
     root_normalization_equations: thm list,
     source_actions: source_action list,
     power_equation: thm,
     terminal_bound: thm,
     bounded_stops: thm,
     base_actions_term: term,
     final_actions_term: term,
     source_nf_actions_term: term,
     source_nf_apply_refinement: thm,
     source_nf_bounded_stops: thm}
  val compile: Proof.context -> progress -> graph_node Inttab.table ->
    int list -> int list -> publication
  val compile_checked: progress -> Proof.context -> publication ->
    graph_node Inttab.table -> term -> int list -> thm list -> checked_publication
  val make_serializer: arena -> serializer
  val make_normalization_proof_cache: Proof.context -> arena -> normalization_proof_cache
  val with_composer: arena -> int -> diagram Vector.vector ->
    (composer -> 'a) -> 'a
  val apply_with: composer -> diagram -> diagram * diagram
  val apply: arena -> int -> diagram -> diagram Vector.vector -> diagram * diagram
  val certify_normalization: Proof.context -> arena -> serializer ->
    normalization_proof_cache -> diagram ->
    {normalized: diagram, equation: thm, certified_nodes: int}
  val compiler_expression_reflexive: Proof.context -> serializer -> diagram ->
    term -> thm list -> thm
  val all_stopped_bounded: arena -> int -> diagram -> bool
  val summarize_terminals: arena -> diagram Vector.vector -> terminal_summary
end

structure Comma_Semantic_Weighted_CRT_DAG:>
  COMMA_SEMANTIC_WEIGHTED_CRT_DAG =
struct
  val natT = @{typ nat}
  fun nat n = HOLogic.mk_number natT n
  fun closed term = not (Term.is_open term) andalso
    null (Term.add_frees term []) andalso null (Term.add_vars term [])
  fun standalone theorem = Thm.nprems_of theorem = 0 andalso
    null (Thm.hyps_of theorem) andalso null (Thm.tpairs_of theorem) andalso
    closed (Thm.prop_of theorem)
  datatype control = Continue_C of int | Stop_C of int | Invalid_C
  datatype graph_edge = Goto of int | Live of int | Stop of int | Invalid
  type graph_node = {period: int, actions: graph_edge Vector.vector}
  type progress = string -> string -> unit
  structure Data = Comma_Semantic_Weighted_CRT_Data
  type diagram = Data.diagram
  type arena =
    {data: Data.arena,
     raw_branch_calls: int Unsynchronized.ref,
     shift_calls: int Unsynchronized.ref,
     apply_calls: int Unsynchronized.ref}
  type composer = (arena * diagram Vector.vector) option Unsynchronized.ref
  type composition =
    {span: int, slot: int, left: diagram, rights: diagram Vector.vector,
     raw: diagram, normalized: diagram}
  type node_build =
    {raw: diagram, normalized: diagram, normalization_equation: thm}
  type terminal_summary =
    {all_stopped: bool, max_height: int, terminal_paths: int}
  type source_action =
    {cid: int, diagram: diagram, action: term, compiler_equation: thm,
     normalization_equation: thm}
  type serializer = Data.serializer
  type normalization_proof_cache = Data.normalization_proof_cache
  type publication =
    {arena: arena, root_cids: int list, node_actions: (int * diagram) list,
     node_builds: (int * node_build) list,
     base: diagram Vector.vector, normalized_base: diagram Vector.vector,
     powers: (int * diagram Vector.vector) list,
     final: diagram Vector.vector,
     normalizations: (diagram * diagram) list,
     compositions: composition list,
     normalization_serializer: serializer,
     normalization_cache: normalization_proof_cache,
     stats: unit -> string}
  type checked_publication =
    {publication: publication,
     compiler_cids: int list,
     node_action_terms: (int * term) list,
     compiler_local_actions: (int * term) list,
     compiler_equations: thm list,
     composition_equations: thm list,
     normalization_equations: thm list,
     root_normalization_equations: thm list,
     source_actions: source_action list,
     power_equation: thm,
     terminal_bound: thm,
     bounded_stops: thm,
     base_actions_term: term,
     final_actions_term: term,
     source_nf_actions_term: term,
     source_nf_apply_refinement: thm,
     source_nf_bounded_stops: thm}

  val radices = [4, 3, 7, 11]
  val clock_weights = [693, 616, 792, 672]
  val controlT = @{typ comma_semantic_b1_crt_control}
  val dagT = @{typ comma_semantic_b1_crt_dag}
  val edgeT = HOLogic.mk_prodT (natT, dagT)

  fun control_key control =
    (case control of
      Continue_C root => "b1-control:continue:" ^ Int.toString root
    | Stop_C terminal => "b1-control:stop:" ^ Int.toString terminal
    | Invalid_C => "b1-control:invalid")

  fun control_term control =
    (case control of
      Continue_C root =>
        Const (@{const_name Comma_Semantic_B1_CRT_Continue}, natT --> controlT) $ nat root
    | Stop_C terminal =>
        Const (@{const_name Comma_Semantic_B1_CRT_Stop}, natT --> controlT) $ nat terminal
    | Invalid_C => Const (@{const_name Comma_Semantic_B1_CRT_Invalid}, controlT))

  fun parse_control_term term =
    (case strip_comb term of
      (Const (name, _), [value]) =>
        let val number = HOLogic.dest_number value
        in if #1 number <> natT orelse #2 number < 0 then
            error "Weighted CRT payload contains a non-natural control index"
          else if name = @{const_name Comma_Semantic_B1_CRT_Continue} then
            Continue_C (IntInf.toInt (#2 number))
          else if name = @{const_name Comma_Semantic_B1_CRT_Stop} then
            Stop_C (IntInf.toInt (#2 number))
          else error "Weighted CRT payload contains an unknown indexed control"
        end
    | (Const (name, _), []) =>
        if name = @{const_name Comma_Semantic_B1_CRT_Invalid} then Invalid_C
        else error "Weighted CRT payload contains an unknown nullary control"
    | _ => error "Weighted CRT payload is not a control constructor")

  fun payload control: Data.payload =
    {key=control_key control, value=control_term control}

  fun payload_control ({key, value}: Data.payload) =
    let val control = parse_control_term value
    in if key = control_key control then control
      else error "Weighted CRT payload key does not match its typed value" end

  fun make_arena capacity: arena =
    {data=Data.make_arena capacity,
     raw_branch_calls=Unsynchronized.ref 0,
     shift_calls=Unsynchronized.ref 0,
     apply_calls=Unsynchronized.ref 0}

  fun check_diagram (arena: arena) diagram =
    Data.check_diagram (#data arena) diagram

  fun offset diagram = Data.offset diagram

  fun reserve_scratch arena lease =
    Data.reserve_external (#data arena) lease

  fun reserve_scratch_entries arena lease count =
    if count < 0 then error "Weighted CRT scratch reservation is negative"
    else if count = 0 then ()
    else (reserve_scratch arena lease;
      reserve_scratch_entries arena lease (count - 1))

  fun with_scratch arena work =
    Data.with_reservation (#data arena) work

  fun retain_scratch arena lease count =
    Data.retain_external (#data arena) lease count

  fun leaf (arena: arena) control : diagram =
    let
      val _ = (case control of
        Continue_C root => if 0 <= root andalso root < 46 then ()
          else error "Weighted CRT Continue root is outside 0..45"
      | Stop_C terminal => if 0 <= terminal andalso terminal < 9 then ()
          else error "Weighted CRT Stop terminal is outside 0..8"
      | Invalid_C => ())
    in Data.leaf (#data arena) (payload control) end

  (* Preserve the compiler's source expression exactly.  This constructor is
     intentionally not a quotient: every child root weight remains on its
     incoming edge, including equal rows and common offsets.  The checked
     normalizer below is the only place that may recenter or collapse these
     rows, and it produces a theorem relating this raw tree to that result. *)
  fun raw_branch (arena: arena) axis children : diagram =
    let
      val _ = List.app (check_diagram arena) children
      val _ = #raw_branch_calls arena := ! (#raw_branch_calls arena) + 1
    in Data.raw_branch_diagrams (#data arena) axis children end

  (* Canonicalize an arbitrary selector/bind tree into ascending CRT axis
     order by cofactoring the coordinate throughout the complete subgraph,
     then rebuilding one exact row per residue. *)
  fun normalize arena (action: diagram) : diagram =
    (check_diagram arena action; Data.normalize (#data arena) action)

  fun validate_nonterminal_zero arena (action: diagram) =
    let
      val _ = check_diagram arena action
      fun check_leaf item total () =
        (case payload_control item of
          Continue_C _ => if total = 0 then ()
            else error "Weighted CRT action carries height on Continue"
        | Invalid_C => if total = 0 then ()
            else error "Weighted CRT action carries height on Invalid"
        | Stop_C terminal => if 0 <= terminal andalso terminal < 9 andalso
              total >= 0 then ()
            else error "Weighted CRT Stop control or height is outside its domain"
        )
      val _ = Data.fold_leaves (#data arena) check_leaf () action
    in () end

  fun shift_validated arena delta (action: diagram) : diagram =
    let
      val _ = check_diagram arena action
      val _ = if delta >= 0 then ()
        else error "Weighted CRT phase shift is negative"
      val _ = #shift_calls arena := ! (#shift_calls arena) + 1
    in Data.shift (#data arena) delta action end

  fun shift arena delta (action: diagram) : diagram =
    (validate_nonterminal_zero arena action; shift_validated arena delta action)

  fun add_stop_validated arena amount (action: diagram) : diagram =
    let
      val _ = check_diagram arena action
      val _ = if amount >= 0 then ()
        else error "Weighted CRT Stop addition is negative"
      val data = #data arena
      fun transform item _ =
        let
          val control = payload_control item
          val base = Data.leaf data (payload control)
        in case control of
          Stop_C _ => Data.with_offset data amount base
        | _ => base end
    in Data.bind data transform action end

  fun add_stop arena amount (action: diagram) : diagram =
    (validate_nonterminal_zero arena action;
      add_stop_validated arena amount action)

  fun with_composer arena span rights use =
    with_scratch arena (fn lease =>
      let
        val _ = if span >= 0 then ()
          else error "Weighted CRT application span is negative"
        val _ = if Vector.length rights = 46 then ()
          else error "Weighted CRT composition requires the checked 46-root vector"
        val _ = Vector.app (check_diagram arena) rights
        val _ = Vector.app (validate_nonterminal_zero arena) rights
        (* Account for the retained view before materializing its mapped form. *)
        val _ = reserve_scratch_entries arena lease (Vector.length rights)
        val prepared = Vector.map (fn right =>
          add_stop_validated arena span (shift_validated arena span right)) rights
        val state: composer = Unsynchronized.ref (SOME (arena, prepared))
        (* Invalidate escaped handles before the reservation scope is closed;
           on exceptions the scoped lease also releases every prepared entry. *)
        val outcome = Exn.capture (fn () => use state) ()
        val _ = state := NONE
      in Exn.release outcome end)

  fun apply_with_using normalize_action (composer: composer) left =
    (case !composer of
      NONE => error "Weighted CRT composer escaped its prepared-action scope"
    | SOME (arena, prepared) => let
      val _ = check_diagram arena left
      val _ = validate_nonterminal_zero arena left
      val _ = #apply_calls arena := ! (#apply_calls arena) + 1
      val data = #data arena
      fun continue child =
        if 0 <= child andalso child < Vector.length prepared then
          Vector.sub (prepared, child)
        else error "Weighted CRT Continue control is outside the root vector"
      fun bind_leaf item _ =
        (case payload_control item of
          Continue_C child => continue child
        | Stop_C terminal => Data.leaf data (payload (Stop_C terminal))
        | Invalid_C => Data.leaf data (payload Invalid_C))
      val raw_result = Data.bind data bind_leaf left
      val _ = validate_nonterminal_zero arena raw_result
      val normalized = normalize_action raw_result
      val _ = validate_nonterminal_zero arena normalized
    in (raw_result, normalized) end)

  fun apply_with (composer: composer) left =
    (case !composer of
      NONE => error "Weighted CRT composer escaped its prepared-action scope"
    | SOME (arena, _) => apply_with_using (normalize arena) composer left)

  fun apply arena span left rights =
    with_composer arena span rights (fn composer => apply_with composer left)

  fun compile ctxt report (graph: graph_node Inttab.table) roots source_cids =
    let
      val arena = make_arena 8192
      val normalization_serializer =
        Data.make_serializer (#data arena) controlT
      val normalization_cache =
        Data.make_normalization_proof_cache ctxt (#data arena) controlT
      fun certify_action action : node_build =
        let
          val certified = Data.certify_normalization ctxt (#data arena) controlT
            normalization_serializer normalization_cache action
          val normalized = #normalized certified
          val _ = validate_nonterminal_zero arena normalized
        in {raw=action, normalized=normalized,
          normalization_equation= #equation certified} end
      fun normalize_certified action = #normalized (certify_action action)
      val certify_node = certify_action
      val _ = if length roots = 46 andalso
          List.all (fn root => root >= 0 andalso
            Inttab.defined graph root) roots then ()
        else error "Weighted CRT compiler requires the checked 46-root domain"
      val _ = if length source_cids = 16 andalso
          List.all (fn cid => cid >= 0 andalso Inttab.defined graph cid) source_cids then ()
        else error "Weighted CRT compiler requires the authenticated 16-source domain"
      val compiled = Unsynchronized.ref (Inttab.empty: node_build Inttab.table)
      val node_build_attempts = Unsynchronized.ref 0
      val selector_branches = Unsynchronized.ref 0
      val secondary_report_failures = Unsynchronized.ref 0
      val normalization_rows = Unsynchronized.ref ([]: (diagram * diagram) list)
      fun stats () =
        let val shared = Data.stats (#data arena)
        in "weighted_crt_nodes=" ^ Int.toString (#nodes shared) ^
        " weighted_crt_node_builds=" ^ Int.toString (!node_build_attempts) ^
        " weighted_crt_completed_graph_cids=" ^ Int.toString (Inttab.size (!compiled)) ^
        " weighted_crt_selector_branches=" ^ Int.toString (!selector_branches) ^
        " weighted_crt_branch_calls=" ^ Int.toString (#branch_calls shared) ^
        " weighted_crt_raw_branch_calls=" ^
          Int.toString (! (#raw_branch_calls arena)) ^
        " weighted_crt_shift_calls=" ^ Int.toString (! (#shift_calls arena)) ^
        " weighted_crt_apply_calls=" ^ Int.toString (! (#apply_calls arena)) ^
        " weighted_crt_normalization_node_visits=" ^
          Int.toString (#normalization_node_visits shared) ^
        " weighted_crt_serialization_node_visits=" ^
          Int.toString (#serialization_node_visits shared) ^
        " weighted_crt_intern_hits=" ^ Int.toString (#intern_hits shared) ^
        " weighted_crt_active_scratch=" ^ Int.toString (#scratch_entries shared) ^
        " weighted_crt_peak_entries=" ^ Int.toString (#peak_entries shared) ^
        " weighted_crt_retained_nodes=" ^ Int.toString (#nodes shared) ^
        " weighted_crt_retained_proofs=" ^ Int.toString (#proof_entries shared) ^
        " weighted_crt_secondary_report_failures=" ^
          Int.toString (!secondary_report_failures) end
      fun report_on_failure stage work =
        (case Exn.capture work () of
          Exn.Res result => result
        | Exn.Exn failure =>
            let
              val report_status = Exn.capture
                (fn () => report (stage ^ " failed") (stats ())) ()
              val _ = (case report_status of
                  Exn.Res () => ()
                | Exn.Exn _ => secondary_report_failures :=
                    !secondary_report_failures + 1)
            in Exn.reraise failure end)
      fun edge_diagram parent action =
        (case action of
          Goto child => if 0 <= child andalso child < parent then
              #normalized (build_node child)
            else error "Weighted CRT compiler rejected a non-decreasing Goto edge"
        | Live root => leaf arena (Continue_C root)
        | Stop terminal => leaf arena (Stop_C terminal)
        | Invalid => leaf arena Invalid_C)
      and build_selector parent axes period accumulated actions =
        (case axes of
          [] => edge_diagram parent
            (Vector.sub (actions, accumulated mod period))
        | axis :: rest =>
            if List.nth (clock_weights, axis) mod period = 0 then
              build_selector parent rest period accumulated actions
            else
              let
                val _ = selector_branches := !selector_branches + 1
                val radix = List.nth (radices, axis)
                val weight = List.nth (clock_weights, axis)
                val children = map (fn slot =>
                  build_selector parent rest period (accumulated + weight * slot) actions)
                  (0 upto (radix - 1))
              in raw_branch arena axis children end)
      and build_node cid =
        (case Inttab.lookup (!compiled) cid of
          SOME result => result
        | NONE =>
            let
              val _ = node_build_attempts := !node_build_attempts + 1
              val current = (case Inttab.lookup graph cid of
                SOME node => node
              | NONE => error "Weighted CRT graph compiler has a missing child CID")
              val _ = if #period current > 0 andalso #period current <= 924 andalso
                  924 mod #period current = 0 andalso
                  Vector.length (#actions current) = #period current then ()
                else error "Weighted CRT graph node has an invalid period or row length"
              val raw = build_selector cid [0, 1, 2, 3] (#period current) 0
                (#actions current)
              val _ = validate_nonterminal_zero arena raw
              val result = certify_node raw
              val _ = compiled := Inttab.update (cid, result) (!compiled)
              val completed = Inttab.size (!compiled)
              val _ = if completed mod 16 = 0 then
                  report ("postorder graph-node completion completed=" ^
                    Int.toString completed) (stats ())
                else ()
            in result end)
      val base_raw = report_on_failure "raw graph selector/bind DAG"
        (fn () => Vector.fromList (map (fn cid => #normalized (build_node cid)) roots))
      val _ = report "raw graph selector/bind DAG" (stats ())
      val base_roots = base_raw
      val _ = report_on_failure "authenticated initial-source graph seeds"
        (fn () => List.app (fn cid => ignore (build_node cid)) source_cids)
      val _ = report "authenticated initial-source graph seeds" (stats ())
      val _ = report "postorder graph-node normalization" (stats ())
      val powers = Unsynchronized.ref
        ([]: (int * diagram Vector.vector) list)
      val compositions = Unsynchronized.ref ([]: composition list)
      fun pow2 k = if k = 0 then 1 else 2 * pow2 (k - 1)
      fun square k current =
        if k = 5 then current
        else
          let
            val span = pow2 k
            val steps = report_on_failure
              ("B" ^ Int.toString (span * 2) ^ " data square")
              (fn () => with_composer arena span current (fn composer =>
                Vector.tabulate (length roots, fn root =>
                  let
                    val left = Vector.sub (current, root)
                    val (raw, normalized) = apply_with_using
                      normalize_certified composer left
                    val _ = normalization_rows := (raw, normalized) :: !normalization_rows
                    val _ = compositions :=
                      {span=span, slot=root, left=left, rights=current, raw=raw,
                       normalized=normalized} :: !compositions
                  in (raw, normalized) end)))
            val next = Vector.map #2 steps
            val _ = powers := (span, next) :: !powers
            val _ = report ("B" ^ Int.toString (span * 2) ^ " data square") (stats ())
          in square (k + 1) next end
      val final_roots = square 0 base_roots
      val _ = Vector.app (validate_nonterminal_zero arena) final_roots
    in {arena=arena, root_cids=roots,
      node_actions=map (fn (cid, build) => (cid,#normalized build))
        (Inttab.dest (!compiled)),
      node_builds=Inttab.dest (!compiled),
      base=base_raw, normalized_base=base_roots, powers=rev (!powers),
      final=final_roots, normalizations=rev (!normalization_rows),
      compositions=rev (!compositions),
      normalization_serializer=normalization_serializer,
      normalization_cache=normalization_cache, stats=stats}: publication end

  (* Serialize only the final reachable DAG, memoizing each arena node so
     repeated subdiagrams remain shared by the Isabelle term representation.
     Temporary arena addresses are deliberately erased here. *)
  fun make_serializer arena = Data.make_serializer (#data arena) controlT

  fun make_normalization_proof_cache ctxt arena =
    Data.make_normalization_proof_cache ctxt (#data arena) controlT

  fun certify_normalization ctxt arena serializer cache initial =
    Data.certify_normalization ctxt (#data arena) controlT serializer cache initial

  fun equivalent_diagrams arena left right =
    Data.same_action (#data arena) left right

  fun summarize_terminals arena actions : terminal_summary =
    let
      fun summarize_action action (all_stopped, max_height, terminal_paths) =
        let
          val _ = check_diagram arena action
          fun observe item total (all, maximum, count) =
            (case payload_control item of
              Stop_C terminal =>
                (all andalso 0 <= terminal andalso terminal < 9,
                 Int.max (maximum, total), count + 1)
            | _ => (false, maximum, count + 1))
        in Data.fold_leaves (#data arena) observe
          (all_stopped, max_height, terminal_paths) action end
      val (all_stopped, max_height, terminal_paths) =
        Vector.foldl (fn (action, state) => summarize_action action state)
          (true, 0, 0) actions
    in {all_stopped=all_stopped, max_height=max_height,
      terminal_paths=terminal_paths} end

  (* Establish that a raw ML compiler product is the actual HOL compiler
     expression after the caller's checked source equations are simplified.
     This is deliberately a closed syntactic transport: if the serialized
     source action does not match the defining selector/bind expression, it
     fails instead of treating a numerically similar MDD as authority. *)
  fun compiler_expression_reflexive ctxt
      (serializer: serializer) (raw: diagram) expected simp_rules =
    let
      val actual = Data.action serializer raw
      val reduced = Simplifier.rewrite (ctxt addsimps simp_rules)
        (Thm.cterm_of ctxt expected)
      val _ = if standalone reduced andalso
          Thm.term_of (Thm.rhs_of reduced) aconv actual then ()
        else error "Raw weighted CRT action does not match its checked HOL compiler expression"
    in Thm.transitive (Thm.reflexive (Thm.cterm_of ctxt actual))
      (Thm.symmetric reduced) end

  fun compile_checked report ctxt (publication: publication) graph nodes_term source_cids compiler_rules =
    let
      val arena = #arena publication
    in with_scratch arena (fn lease =>
     let
      val serializer = #normalization_serializer publication
      val cache = #normalization_cache publication
      (* Both caches are publication-local. The shared lease commits their
         retained accounting only on successful completion; exceptions drop
         the local references and roll back the lease's pending reservations. *)
      val expression_cache = Unsynchronized.ref (Termtab.empty:
        (diagram * thm) Termtab.table)
      val expression_entries = Unsynchronized.ref 0
      val secondary_proof_report_failures = Unsynchronized.ref 0
      fun proof_stats () =
        let val shared = Data.stats (#data arena)
        in
        #stats publication () ^
        " weighted_crt_normalization_certificates=" ^
          Int.toString (#proof_entries shared) ^
        " weighted_crt_serialization_node_visits=" ^
          Int.toString (#serialization_node_visits shared) ^
        " weighted_crt_expression_certificates=" ^
          Int.toString (!expression_entries) ^
        " weighted_crt_secondary_proof_report_failures=" ^
          Int.toString (!secondary_proof_report_failures) end
      fun report_proof stage = report stage (proof_stats ())
      fun preserve_failure_stage stage work =
        (case Exn.capture work () of
          Exn.Res result => result
        | Exn.Exn failure =>
            let
              val report_status = Exn.capture
                (fn () => report_proof
                  (stage ^ " failed; last counters retained")) ()
              val _ = (case report_status of
                  Exn.Res () => ()
                | Exn.Exn _ => secondary_proof_report_failures :=
                    !secondary_proof_report_failures + 1)
            in Exn.reraise failure end)
      fun checked_expression raw expected rules =
        (case Termtab.lookup (!expression_cache) expected of
          SOME (certified_raw, theorem) =>
            let
              val _ = if Data.same_action (#data arena) raw certified_raw then ()
                else error "Weighted CRT proof cache key omits its result action"
            in theorem end
        | NONE =>
            let
              val _ = reserve_scratch arena lease
              val theorem = compiler_expression_reflexive ctxt serializer raw
                expected rules
              val _ = expression_entries := !expression_entries + 1
              val _ = expression_cache := Termtab.update
                (expected, (raw, theorem)) (!expression_cache)
            in theorem end)
      val actionT = fastype_of (Data.action serializer
        (Vector.sub (#base publication, 0)))
      val serialized_right_vectors = Unsynchronized.ref
        ([]: (diagram Vector.vector * term Vector.vector * term) list)
      fun same_vector left right =
        Vector.length left = Vector.length right andalso
        ListPair.allEq (fn (first, second) =>
          Data.same_action (#data arena) first second)
          (Vector.foldr op:: [] left, Vector.foldr op:: [] right)
      fun serialized_rights rights =
        (case List.find (fn (known, _, _) => same_vector known rights)
            (!serialized_right_vectors) of
          SOME (_, terms, list_term) => (terms, list_term)
        | NONE =>
            let
              val _ = if Vector.length rights = 46 then ()
                else error "Weighted CRT proof received a noncanonical right-action vector"
              (* The serialized vector is retained once for this power level.
                 Charge its 46 action terms to the same bounded publication
                 lease used for compiler and composition certificates. *)
              val _ = reserve_scratch_entries arena lease (Vector.length rights)
              val terms = Vector.map (Data.action serializer) rights
              val list_term = HOLogic.mk_list actionT (Vector.foldr op:: [] terms)
              val _ = serialized_right_vectors :=
                (rights, terms, list_term) :: !serialized_right_vectors
            in (terms, list_term) end)
      fun check_normalization (raw, expected) =
        let
          val certified = certify_normalization ctxt arena serializer cache raw
          val _ = if equivalent_diagrams arena (#normalized certified) expected then ()
            else error "Checked CRT normalizer disagrees with its compiled candidate"
        in #equation certified end
      val compiler_const = @{term comma_semantic_b1_crt_compile_node_from_children}
      val compiler_cids = map #1 (#node_builds publication)
      val normalized_by_cid = Inttab.make (#node_actions publication)
      val node_action_terms = map (fn (cid, value) =>
        (cid, Data.action serializer value)) (#node_actions publication)
      fun action_of_cid cid =
        (case Inttab.lookup normalized_by_cid cid of
          SOME value => Data.action serializer value
        | NONE => error "Postorder child action was not normalized before its parent")
      val compiler_local_actions =
        Comma_Semantic_Weighted_CRT_Local_Node_Compiler.local_actions
          compiler_const nodes_term nat natT
          @{term comma_semantic_b1_crt_invalid_action}
          (fn table => fn cid => Inttab.lookup table cid)
          (fn node => Vector.foldr (fn (edge, rest) =>
            (case edge of Goto child => child :: rest | _ => rest)) []
            (#actions node))
          action_of_cid graph compiler_cids
      val compiler_equations = preserve_failure_stage
        "postorder local graph-node compiler expression certification" (fn () =>
          Comma_Semantic_Weighted_CRT_Local_Node_Compiler.certify_local_actions
            compiler_rules checked_expression #1
            (fn (_,build: node_build) => #raw build) (#node_builds publication)
            compiler_local_actions)
      val _ = if length source_cids = 16 andalso
          List.all (fn cid => Inttab.defined graph cid) source_cids then ()
        else error "Weighted CRT source action requests do not match the authenticated 16-source domain"
      val _ = if length compiler_cids = length compiler_equations then ()
        else error "Weighted compiler CID/equation vectors have different lengths"
      val compiler_by_cid = fold (fn (cid, theorem) => fn table =>
        if Inttab.defined table cid then
          error "Weighted compiler emitted duplicate canonical CID equations"
        else Inttab.update (cid, theorem) table)
        (ListPair.zip (compiler_cids, compiler_equations)) Inttab.empty
      val builds_by_cid = Inttab.make (#node_builds publication)
      fun certify_source cid : source_action =
        let
          val build = (case Inttab.lookup builds_by_cid cid of
              SOME value => value
            | NONE => error "Authenticated source CID has no postorder compilation record")
          val compiler_equation = (case Inttab.lookup compiler_by_cid cid of
              SOME theorem => theorem
            | NONE => error "Authenticated source CID has no checked compiler theorem")
          val normalized = #normalized build
          val normalization_equation = #normalization_equation build
          val _ = validate_nonterminal_zero arena normalized
        in {cid=cid, action=Data.action serializer normalized,
          diagram=normalized,
          compiler_equation=compiler_equation,
          normalization_equation=normalization_equation}: source_action end
      val source_actions = preserve_failure_stage
        "authenticated source action normalization" (fn () => map certify_source source_cids)
      val _ = report_proof
        ("canonical graph-node compiler expressions certified nodes=" ^
          Int.toString (length compiler_cids) ^ " root references=" ^
          Int.toString (length source_cids))
      val compose_const = @{term comma_semantic_b1_crt_compose}
      val compose_rules = @{thms comma_semantic_b1_crt_compose_def
        comma_semantic_b1_crt_add_stop_def comma_semantic_b1_crt_leaf_def
        comma_semantic_b1_crt_invalid_action_def comma_weighted_crt_bind.simps
        comma_weighted_crt_shift.simps fst_conv snd_conv list.map
        nth_Cons_0 nth_Cons_Suc nth_Cons'}
      fun check_composition ({span, slot, left, rights, raw, ...}: composition) =
        let
          val (right_terms, right_list) = serialized_rights rights
          val _ = if slot >= 0 andalso slot < Vector.length rights andalso
              Data.same_action (#data arena) left (Vector.sub (rights, slot)) then ()
            else error "Weighted CRT composition slot does not identify its issued left action"
          val expected = compose_const $ nat span $ Vector.sub (right_terms, slot) $
            right_list
        in checked_expression raw expected compose_rules end
      (* Compose each admitted source graph action with the completed B32
         action.  The added span is one complete-decade action unit; it is
         not a physical recurrence tick or a C1 mod-50 clock advance. *)
      val source_nf_steps = preserve_failure_stage
        "authenticated source-to-B32 action composition" (fn () =>
          with_composer arena 1 (#final publication) (fn composer =>
            Vector.tabulate (length source_actions, fn index =>
              let
                val source = List.nth (source_actions, index)
                val (raw, normalized) = apply_with composer (#diagram source)
              in {span=1, slot=index, left= #diagram source,
                rights= #final publication, raw=raw,
                normalized=normalized}: composition end)))
      val source_nf_compositions = Vector.foldr op:: [] source_nf_steps
      val source_nf_composition_equations = map check_composition
        source_nf_compositions
      val source_nf_normalization_equations = map (fn step =>
        check_normalization (#raw step, #normalized step)) source_nf_compositions
      fun two_power exponent =
        if exponent = 0 then 1 else 2 * two_power (exponent - 1)
      fun certify_grouped label check values =
        let
          fun loop index [] accumulated = rev accumulated
            | loop index (value :: rest) accumulated =
                let
                  val theorem = preserve_failure_stage
                    (label ^ " root=" ^ Int.toString index)
                    (fn () => check value)
                  val next = theorem :: accumulated
                  val group = index div 46
                  val level = if label = "chronological composition" then group + 1
                    else group
                  val level_name = if level = 0 then "B1"
                    else "B" ^ Int.toString (two_power level)
                  val _ = if (index + 1) mod 46 = 0 then
                      report_proof (label ^ " " ^ level_name ^ " roots=" ^
                        Int.toString (index + 1))
                    else ()
                in loop (index + 1) rest next end
        in loop 0 values [] end
      val composition_equations = certify_grouped
        "chronological composition" check_composition
        (#compositions publication)
      val composition_normalization_equations = certify_grouped
        "raw-to-normalized all-phase proof" check_normalization
        (#normalizations publication)
      val node_normalization_equations = map
        (fn (_, build: node_build) => #normalization_equation build)
        (#node_builds publication)
      val normalization_equations =
        node_normalization_equations @ composition_normalization_equations
      val root_normalization_equations = map (fn cid =>
        (case Inttab.lookup builds_by_cid cid of
          SOME build => #normalization_equation build
        | NONE => error "A requested root CID has no postorder normalization proof"))
        (#root_cids publication)
      val apply_const = Const (@{const_name comma_weighted_crt_apply},
        actionT --> natT -->
          Type (@{type_name option},
            [HOLogic.mk_prodT (controlT, natT)]))
      val nth_action = Const (@{const_name nth},
        HOLogic.listT actionT --> natT --> actionT)
      val crt_power = Const (@{const_name comma_semantic_b1_crt_power},
        natT --> HOLogic.listT actionT --> HOLogic.listT actionT)
      val action_list = fn values =>
        if Vector.length values = 46 then #2 (serialized_rights values)
        else HOLogic.mk_list actionT
          (Vector.foldr (fn (value, rest) =>
            Data.action serializer value :: rest) [] values)
      val base_list = action_list (#normalized_base publication)
      val final_list = action_list (#final publication)
      val source_actions_list = HOLogic.mk_list actionT
        (map #action source_actions)
      val source_nf_actions = Vector.map #normalized source_nf_steps
      val source_nf_actions_list = action_list source_nf_actions
      val phase = Free ("phase", natT)
      val root = Free ("root", natT)
      fun list_all_term element_type predicate values =
        Const (@{const_name list_all},
          (element_type --> HOLogic.boolT) --> HOLogic.listT element_type -->
            HOLogic.boolT) $ predicate $ values
      val source_slot = Free ("source_slot", natT)
      val source_nf_at_slot = nth_action $ source_nf_actions_list $ source_slot
      val source_at_slot = nth_action $ source_actions_list $ source_slot
      val source_then_b32 = compose_const $ nat 1 $ source_at_slot $ final_list
      val source_nf_row = HOLogic.mk_eq
        (apply_const $ source_nf_at_slot $ phase,
         apply_const $ source_then_b32 $ phase)
      fun certify_source_nf_row index =
        let
          val slot = nat index
          val source_term = nth_action $ source_actions_list $ slot
          val action_term = nth_action $ source_nf_actions_list $ slot
          val composed = compose_const $ nat 1 $ source_term $ final_list
          val proposition = HOLogic.mk_Trueprop
            (HOLogic.mk_all ("phase", natT,
              HOLogic.mk_eq (apply_const $ action_term $ phase,
                apply_const $ composed $ phase)))
          val facts = [List.nth (source_nf_composition_equations, index),
            Comma_Semantic_Weighted_CRT_Data_Transport.object_symmetric ctxt
              (List.nth (source_nf_normalization_equations, index))]
          val theorem = Goal.prove ctxt [] [] proposition
            (fn {context, ...} =>
              asm_full_simp_tac (context addsimps facts) 1)
        in
          if standalone theorem andalso Thm.prop_of theorem aconv proposition then theorem
          else error "Source-to-B32 weighted action row is not a closed exact refinement"
        end
      val source_nf_row_equations = preserve_failure_stage
        "source-to-B32 all-phase action rows" (fn () =>
          map certify_source_nf_row (0 upto (length source_actions - 1)))
      val source_nf_rows_prop = HOLogic.mk_Trueprop
        (list_all_term natT
          (Term.lambda source_slot
            (HOLogic.mk_all ("phase", natT,
              HOLogic.mk_imp
                (HOLogic.mk_binrel @{const_name less}
                  (source_slot, nat (length source_actions)), source_nf_row))))
          @{term "[0..<16] :: nat list"})
      val _ = reserve_scratch arena lease
      val source_nf_apply_refinement = preserve_failure_stage
        "source-to-B32 vector refinement" (fn () =>
          Goal.prove ctxt [] [] source_nf_rows_prop
            (fn {context, ...} =>
              asm_full_simp_tac (context addsimps
                (source_nf_row_equations @ @{thms list_all_iff set_upt
                  atLeastLessThan_iff nth_Cons_0 nth_Cons_Suc nth_Cons'})) 1))
      val _ = if standalone source_nf_apply_refinement andalso
          Thm.prop_of source_nf_apply_refinement aconv source_nf_rows_prop then ()
        else error "Source-to-B32 action-vector refinement is not closed"
      val source_nf_summary = summarize_terminals arena source_nf_actions
      val _ = if #all_stopped source_nf_summary andalso
          #max_height source_nf_summary <= 27 then ()
        else error "Source-to-B32 action has a nonterminal or height above 27"
      val source_nf_action = Free ("source_nf_action", actionT)
      val source_nf_terminal_bound_const = Const
        (@{const_name comma_semantic_b1_crt_terminal_bound},
          natT --> actionT --> HOLogic.boolT)
      val source_nf_bound_predicate = Term.lambda source_nf_action
        (source_nf_terminal_bound_const $ nat 27 $ source_nf_action)
      val source_nf_bound_request = HOLogic.mk_Trueprop
        (list_all_term actionT source_nf_bound_predicate source_nf_actions_list)
      val _ = reserve_scratch arena lease
      val source_nf_terminal_bound_theorem = preserve_failure_stage
        "source-to-B32 structural terminal bound" (fn () =>
          Goal.prove ctxt [] [] source_nf_bound_request
            (fn {context, ...} =>
              asm_full_simp_tac (context addsimps
                @{thms comma_semantic_b1_crt_terminal_bound.simps
                  list_all_iff}) 1))
      val source_nf_phase = Free ("source_nf_phase", natT)
      val source_nf_terminal = Free ("source_nf_terminal", natT)
      val source_nf_height = Free ("source_nf_height", natT)
      val source_nf_stop = Const (@{const_name Comma_Semantic_B1_CRT_Stop},
        natT --> controlT) $ source_nf_terminal
      val source_nf_stop_pair = HOLogic.mk_prod
        (source_nf_stop, source_nf_height)
      val source_nf_stop_some = Const (@{const_name Some},
        HOLogic.mk_prodT (controlT, natT) -->
          Type (@{type_name option}, [HOLogic.mk_prodT (controlT, natT)])) $
        source_nf_stop_pair
      val source_nf_stop_observation = HOLogic.mk_all ("source_nf_phase", natT,
        HOLogic.mk_exists ("source_nf_terminal", natT,
          HOLogic.mk_exists ("source_nf_height", natT,
            HOLogic.mk_conj
              (HOLogic.mk_eq
                (apply_const $ source_nf_action $ source_nf_phase,
                  source_nf_stop_some),
               HOLogic.mk_conj
                 (HOLogic.mk_binrel @{const_name less}
                   (source_nf_terminal, nat 9),
                  HOLogic.mk_binrel @{const_name less_eq}
                    (source_nf_height, nat 27))))))
      val source_nf_stopped_request = HOLogic.mk_Trueprop
        (list_all_term actionT
          (Term.lambda source_nf_action source_nf_stop_observation)
          source_nf_actions_list)
      val _ = reserve_scratch arena lease
      val source_nf_bounded_stops = preserve_failure_stage
        "source-to-B32 all-phase Stop transport" (fn () =>
          Goal.prove ctxt [] [] source_nf_stopped_request
            (fn {context, ...} =>
              Method.insert_tac context [source_nf_terminal_bound_theorem] 1 THEN
              blast_tac (context addIs
                [@{thm comma_semantic_b1_crt_terminal_bound_sound}]
                addDs @{thms list_all_iff}) 1))
      val _ = if standalone source_nf_bounded_stops andalso
          Thm.prop_of source_nf_bounded_stops aconv source_nf_stopped_request then ()
        else error "Source-to-B32 all-phase Stop transport is not closed"
      val power_request =
        HOLogic.mk_Trueprop (list_all_term natT
          (Term.lambda root (HOLogic.mk_all ("phase", natT,
            HOLogic.mk_eq
              (apply_const $ (nth_action $ final_list $ root) $ phase,
               apply_const $
                 (nth_action $ (crt_power $ nat 5 $ base_list) $ root) $
                 phase))))
          @{term "[0..<46] :: nat list"})
      val power_facts = map Thm.symmetric composition_equations @
        normalization_equations @ @{thms comma_semantic_b1_crt_power.simps
          comma_weighted_crt_apply_def comma_weighted_crt_eval_branch
          list_all_iff set_upt atLeastLessThan_iff nth_Cons_0 nth_Cons_Suc
          nth_Cons' list.map}
      val _ = reserve_scratch arena lease
      val power_equation = preserve_failure_stage "five-square proof" (fn () =>
        Goal.prove ctxt [] [] power_request
        (fn {context, ...} =>
          asm_full_simp_tac (context addsimps power_facts) 1))
      val _ = if standalone power_equation andalso
          Thm.prop_of power_equation aconv power_request then ()
        else error "Weighted CRT five-square theorem is not closed"
      val terminal_pred = Const (@{const_name comma_semantic_b1_crt_terminal_bound},
        natT --> actionT --> HOLogic.boolT) $ nat 26
      val terminal_request =
        HOLogic.mk_Trueprop (list_all_term natT
          (Term.lambda root
            (terminal_pred $ (nth_action $ final_list $ root)))
          @{term "[0..<46] :: nat list"})
      val _ = reserve_scratch arena lease
      val summary = summarize_terminals arena (#final publication)
      val _ = if #all_stopped summary andalso #max_height summary <= 26 then ()
        else error "Weighted CRT final action contains Live, Invalid, or height above 26"
      val _ = report_proof ("canonical terminal summary paths=" ^
        Int.toString (#terminal_paths summary))
      val terminal_equation = preserve_failure_stage "terminal-bound proof" (fn () =>
        Goal.prove ctxt [] [] terminal_request
        (fn {context, ...} =>
          asm_full_simp_tac (context addsimps
            (@{thms comma_semantic_b1_crt_terminal_bound.simps
              list_all_iff set_upt atLeastLessThan_iff nth_Cons_0
              nth_Cons_Suc nth_Cons'})) 1))
      val _ = if standalone terminal_equation andalso
          Thm.prop_of terminal_equation aconv terminal_request then ()
        else error "Weighted CRT terminal-height bound is not closed"
      val J = Free ("J", natT)
      val H = Free ("H", natT)
      val weighted_resultT = HOLogic.mk_prodT (controlT, natT)
      val weighted_optionT = Type (@{type_name option}, [weighted_resultT])
      val stop_control = Const (@{const_name Comma_Semantic_B1_CRT_Stop},
        natT --> controlT) $ J
      val stop_pair = HOLogic.mk_prod (stop_control, H)
      val stop_some = Const (@{const_name Some}, weighted_resultT --> weighted_optionT) $
        stop_pair
      val stop_facts = HOLogic.mk_conj
        (HOLogic.mk_eq
          (apply_const $ (nth_action $ final_list $ root) $ phase, stop_some),
         HOLogic.mk_conj
          (HOLogic.mk_binrel @{const_name less} (J, nat 9),
           HOLogic.mk_binrel @{const_name less_eq} (H, nat 26)))
      val bounded_stops_prop = HOLogic.mk_Trueprop
        (HOLogic.mk_all ("root", natT,
          HOLogic.mk_imp
            (HOLogic.mk_binrel @{const_name less} (root, nat 46),
             HOLogic.mk_all ("phase", natT,
               HOLogic.mk_exists ("J", natT,
                 HOLogic.mk_exists ("H", natT,
                   stop_facts))))))
      val _ = reserve_scratch arena lease
      val bounded_stops = preserve_failure_stage "all-phase Stop theorem" (fn () =>
        Goal.prove ctxt [] [] bounded_stops_prop
        (fn {context, ...} =>
          asm_full_simp_tac (context addsimps
            (terminal_equation :: @{thms
              comma_semantic_b1_crt_terminal_bound_sound list_all_iff
              set_upt atLeastLessThan_iff nth_Cons_0 nth_Cons_Suc
              nth_Cons' comma_weighted_crt_apply_def})) 1))
      val _ = if standalone bounded_stops andalso
          Thm.prop_of bounded_stops aconv bounded_stops_prop then ()
        else error "Weighted CRT all-phase Stop bound did not close"
      val _ = Thm.consolidate
        (compiler_equations @ composition_equations @ normalization_equations @
          source_nf_composition_equations @ source_nf_normalization_equations @
          source_nf_row_equations @
          [source_nf_apply_refinement, source_nf_terminal_bound_theorem,
            source_nf_bounded_stops, power_equation, terminal_equation,
            bounded_stops])
      val _ = retain_scratch arena lease (!expression_entries)
      val _ = if #scratch_entries (Data.stats (#data arena)) = 0 then ()
        else error "Weighted CRT proof publication retained scratch memo entries"
      val _ = report_proof "B32 action, Stop controls, and 26-height bound certified"
    in {publication=publication, compiler_cids=compiler_cids,
      node_action_terms=node_action_terms,
      compiler_local_actions=compiler_local_actions,
      compiler_equations=compiler_equations,
      composition_equations=composition_equations,
      normalization_equations=normalization_equations,
      root_normalization_equations=root_normalization_equations,
      source_actions=source_actions,
      power_equation=power_equation, terminal_bound=terminal_equation,
      bounded_stops=bounded_stops,
      base_actions_term=base_list, final_actions_term=final_list,
      source_nf_actions_term=source_nf_actions_list,
      source_nf_apply_refinement=source_nf_apply_refinement,
      source_nf_bounded_stops=source_nf_bounded_stops}:
      checked_publication end)
    end

  fun all_stopped_bounded arena max_height action =
    let
      val summary = summarize_terminals arena (Vector.fromList [action])
    in #all_stopped summary andalso #max_height summary <= max_height end
end
