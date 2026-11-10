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
  val make_arena: int -> arena
  type publication =
    {arena: arena, source_cids: int list,
     node_actions: (int * diagram) list,
     node_builds: (int * node_build) list,
     source_actions: diagram Vector.vector,
     normalization_serializer: serializer,
     normalization_cache: normalization_proof_cache,
     stats: unit -> string}
  type checked_publication =
    {publication: publication,
     compiler_cids: int list,
     node_action_terms: (int * term) list,
     compiler_local_actions: (int * term) list,
     compiler_equations: thm list,
     normalization_equations: thm list,
     root_normalization_equations: thm list,
     source_actions: source_action list}
  val compile_sources: Proof.context -> progress -> graph_node Inttab.table ->
    int list -> publication
  val compile_sources_checked: progress -> Proof.context -> publication ->
    graph_node Inttab.table -> term -> int list -> thm list -> checked_publication
  val make_serializer: arena -> serializer
  val serialize_action: serializer -> diagram -> term
  val import_action_term: arena -> term -> diagram
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
    {arena: arena, source_cids: int list,
     node_actions: (int * diagram) list,
     node_builds: (int * node_build) list,
     source_actions: diagram Vector.vector,
     normalization_serializer: serializer,
     normalization_cache: normalization_proof_cache,
     stats: unit -> string}
  type checked_publication =
    {publication: publication,
     compiler_cids: int list,
     node_action_terms: (int * term) list,
     compiler_local_actions: (int * term) list,
     compiler_equations: thm list,
     normalization_equations: thm list,
     root_normalization_equations: thm list,
     source_actions: source_action list}

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

  (* Import a closed HOL weighted action into this publication-local arena.
     The parser accepts only the exact weighted-DAG constructors, validates
     every radix/row through Data.raw_branch, and canonicalizes control leaves
     through the typed control decoder.  It creates no proof authority: the
     caller must retain the theorem that authenticates the imported term. *)
  fun import_action_term (arena: arena) action_term =
    let
      val actionT = HOLogic.mk_prodT (natT, dagT)
      val _ = if fastype_of action_term = actionT andalso closed action_term then ()
        else error "Weighted CRT import requires a closed action term of the checked type"
      fun numeral term =
        (case try HOLogic.dest_number term of
          SOME (typ, value) =>
            if typ = natT andalso value >= 0 then IntInf.toInt value
            else error "Weighted CRT import contains a non-natural numeral"
        | NONE => error "Weighted CRT import contains a non-numeral field")
      val tree_memo = Unsynchronized.ref (Termtab.empty: diagram Termtab.table)
      fun import_tree term =
        (case Termtab.lookup (!tree_memo) term of
          SOME diagram => diagram
        | NONE =>
            let
              val diagram =
                (case strip_comb term of
                  (Const (name, _), [value]) =>
                    if name = @{const_name Comma_Weighted_CRT_Leaf} then
                      Data.leaf (#data arena) (payload_control value)
                    else error "Weighted CRT import contains an unknown unary DAG node"
                | (Const (name, _), [axis_term, rows_term]) =>
                    if name = @{const_name Comma_Weighted_CRT_Branch} then
                      let
                        val axis = numeral axis_term
                        val rows = HOLogic.dest_list rows_term
                        val children = map (fn row =>
                          let
                            val (weight, child) = HOLogic.dest_prod row
                          in (numeral weight, import_tree child) end) rows
                      in Data.raw_branch (#data arena) axis children end
                    else error "Weighted CRT import contains an unknown binary DAG node"
                | _ => error "Weighted CRT import contains a malformed DAG node")
              val _ = tree_memo := Termtab.update (term, diagram) (!tree_memo)
            in diagram end)
      val (offset_term, tree_term) = HOLogic.dest_prod action_term
      val diagram = Data.with_offset (#data arena) (numeral offset_term)
        (import_tree tree_term)
      val _ = check_diagram arena diagram
    in diagram end

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

  fun compile_sources ctxt report (graph: graph_node Inttab.table) source_cids =
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
      val _ = if length source_cids = 16 andalso
          List.all (fn cid => cid >= 0 andalso Inttab.defined graph cid) source_cids then ()
        else error "Weighted CRT source compiler requires the authenticated 16-source domain"
      val compiled = Unsynchronized.ref (Inttab.empty: node_build Inttab.table)
      val node_build_attempts = Unsynchronized.ref 0
      val selector_branches = Unsynchronized.ref 0
      val secondary_report_failures = Unsynchronized.ref 0
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
              val result = certify_action raw
              val _ = compiled := Inttab.update (cid, result) (!compiled)
              val completed = Inttab.size (!compiled)
              val _ = if completed mod 16 = 0 then
                  report ("postorder source-node completion completed=" ^
                    Int.toString completed) (stats ())
                else ()
            in result end)
      val source_roots = report_on_failure "raw authenticated source selector DAG"
        (fn () => Vector.fromList (map (fn cid => #normalized (build_node cid)) source_cids))
      val _ = report "raw authenticated source selector DAG" (stats ())
      val _ = report "postorder source-node normalization" (stats ())
    in {arena=arena, source_cids=source_cids,
      node_actions=map (fn (cid, build) => (cid, #normalized build))
        (Inttab.dest (!compiled)),
      node_builds=Inttab.dest (!compiled),
      source_actions=source_roots,
      normalization_serializer=normalization_serializer,
      normalization_cache=normalization_cache, stats=stats}: publication end

  (* Serialize only the final reachable DAG, memoizing each arena node so
     repeated subdiagrams remain shared by the Isabelle term representation.
     Temporary arena addresses are deliberately erased here. *)
  fun make_serializer arena = Data.make_serializer (#data arena) controlT

  fun serialize_action (serializer: serializer) (diagram: diagram) =
    Data.action serializer diagram

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
      val reduced = Simplifier.rewrite (Simplifier.add_simps (simp_rules) (ctxt))
        (Thm.cterm_of ctxt expected)
      val _ = if standalone reduced andalso
          Thm.term_of (Thm.rhs_of reduced) aconv actual then ()
        else error "Raw weighted CRT action does not match its checked HOL compiler expression"
    in Thm.transitive (Thm.reflexive (Thm.cterm_of ctxt actual))
      (Thm.symmetric reduced) end

  fun compile_sources_checked report ctxt (publication: publication)
      graph nodes_term source_cids compiler_rules =
    let
      val arena = #arena publication
      val _ = if source_cids = #source_cids publication andalso
          length source_cids = 16 then ()
        else error "Checked source compiler received a foreign source vector"
      val serializer = #normalization_serializer publication
      val compiler_const = @{term comma_semantic_b1_crt_compile_node_from_children}
      val compiler_cids = map #1 (#node_builds publication)
      val normalized_by_cid = Inttab.make (#node_actions publication)
      val node_action_terms = map (fn (cid, value) =>
        (cid, Data.action serializer value)) (#node_actions publication)
      fun action_of_cid cid =
        (case Inttab.lookup normalized_by_cid cid of
          SOME value => Data.action serializer value
        | NONE => error "Postorder child action was not normalized before its parent")
      val invalid_action = @{term comma_semantic_b1_crt_invalid_action}
      val compiler_local_actions =
        Comma_Semantic_Weighted_CRT_Local_Node_Compiler.local_actions
          compiler_const nodes_term nat natT invalid_action
          (fn table => fn cid => Inttab.lookup table cid)
          (fn node => Vector.foldr (fn (edge, rest) =>
            (case edge of Goto child => child :: rest | _ => rest)) []
            (#actions node))
          action_of_cid graph compiler_cids
      val expression_cache = Unsynchronized.ref (Termtab.empty: (diagram * thm) Termtab.table)
      fun checked_expression raw expected rules =
        (case Termtab.lookup (!expression_cache) expected of
          SOME (certified_raw, theorem) =>
            let
              val _ = if Data.same_action (#data arena) raw certified_raw then ()
                else error "Source compiler proof cache key omits its result action"
            in theorem end
        | NONE =>
            let
              val theorem = compiler_expression_reflexive ctxt serializer raw expected rules
              val _ = expression_cache := Termtab.update
                (expected, (raw, theorem)) (!expression_cache)
            in theorem end)
      val compiler_equations =
        Comma_Semantic_Weighted_CRT_Local_Node_Compiler.certify_local_actions
          compiler_rules checked_expression #1
          (fn (_, build: node_build) => #raw build) (#node_builds publication)
          compiler_local_actions
      val _ = if length compiler_cids = length compiler_equations andalso
          length source_cids = 16 andalso
          List.all (fn cid => Inttab.defined graph cid) source_cids then ()
        else error "Source compiler theorem vectors do not cover the authenticated input"
      val compiler_by_cid = fold (fn (cid, theorem) => fn table =>
        if Inttab.defined table cid then
          error "Source compiler emitted duplicate canonical CID equations"
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
          val _ = validate_nonterminal_zero arena normalized
        in {cid=cid, action=Data.action serializer normalized,
          diagram=normalized, compiler_equation=compiler_equation,
          normalization_equation= #normalization_equation build}: source_action end
      val source_actions = map certify_source source_cids
      val normalization_equations = map
        (fn (_, build: node_build) => #normalization_equation build)
        (#node_builds publication)
      val root_normalization_equations = map (fn cid =>
        (case Inttab.lookup builds_by_cid cid of
          SOME build => #normalization_equation build
        | NONE => error "An authenticated source CID has no normalization proof"))
        source_cids
      val proof_bundle = compiler_equations @ normalization_equations @
        root_normalization_equations @ map #compiler_equation source_actions @
        map #normalization_equation source_actions
      val _ = Thm.consolidate proof_bundle
      val _ = report ("authenticated source compiler equations=" ^
        Int.toString (length compiler_equations) ^ " source actions=" ^
        Int.toString (length source_actions) ^ " " ^ #stats publication ())
    in {publication=publication, compiler_cids=compiler_cids,
      node_action_terms=node_action_terms,
      compiler_local_actions=compiler_local_actions,
      compiler_equations=compiler_equations,
      normalization_equations=normalization_equations,
      root_normalization_equations=root_normalization_equations,
      source_actions=source_actions}: checked_publication end

  fun all_stopped_bounded arena max_height action =
    let
      val summary = summarize_terminals arena (Vector.fromList [action])
    in #all_stopped summary andalso #max_height summary <= max_height end
end
