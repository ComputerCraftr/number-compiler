structure Comma_Semantic_Weighted_CRT_Data :>
  COMMA_SEMANTIC_WEIGHTED_CRT_DATA =
struct
  type payload = {key: string, value: term}
  datatype shape = Leaf of payload | Branch of int * (int * int) list
  datatype node_descriptor = Node_Descriptor of
    {shape: shape, nf_lower: int option}
  type owner_token = unit Unsynchronized.ref
  type diagram = {owner: owner_token, offset: int, node: int}
  type reservation =
    {owner: owner_token, active_scratch: int Unsynchronized.ref,
     pending_proofs: int Unsynchronized.ref, alive: bool Unsynchronized.ref}
  type arena =
    {owner: owner_token,
     nodes: node_descriptor Inttab.table Unsynchronized.ref,
     payload_keys: int Symtab.table Unsynchronized.ref,
     next: int Unsynchronized.ref,
     proof_entries: int Unsynchronized.ref,
     scratch_entries: int Unsynchronized.ref,
     peak_entries: int Unsynchronized.ref,
     capacity: int,
     intern_hits: int Unsynchronized.ref,
     branch_calls: int Unsynchronized.ref,
     normalization_node_visits: int Unsynchronized.ref,
     serialization_node_visits: int Unsynchronized.ref}
  type serializer =
    {owner: owner_token, payloadT: typ, tree: diagram -> term, action: diagram -> term}
  type normalization_entry =
    {source_node: int, result: diagram, theorem: thm,
     source_tree: term, target_tree: term}
  type selector_proof_entry = {result: diagram, theorem: thm,
    source_tree: term, target_tree: term, proposition: term}
  type proof_profile = Comma_Semantic_Weighted_CRT_Data_Transport.proof_profile
  type normalization_proof_cache =
    {owner: owner_token, payloadT: typ, theory: theory,
     native_certify: thm -> thm,
     proof_profile: proof_profile,
     bottom_up_entries: normalization_entry Inttab.table Unsynchronized.ref,
     selector_entries: selector_proof_entry Symtab.table Unsynchronized.ref,
     size: int Unsynchronized.ref}
  type stats = {nodes: int, proof_entries: int, scratch_entries: int,
    peak_entries: int,
    normalization_node_visits: int, serialization_node_visits: int,
    branch_calls: int, intern_hits: int}

  val natT = @{typ nat}
  val radices = [4, 3, 7, 11]
  val clock_weights = [693, 616, 792, 672]

  fun nat n = HOLogic.mk_number natT n

  fun closed term = not (Term.is_open term) andalso
    null (Term.add_frees term []) andalso null (Term.add_vars term [])

  fun standalone theorem = Thm.nprems_of theorem = 0 andalso
    null (Thm.hyps_of theorem) andalso null (Thm.tpairs_of theorem) andalso
    closed (Thm.prop_of theorem)

  fun make_arena capacity: arena =
    if capacity <= 0 then error "Weighted CRT data arena capacity must be positive"
    else
      {owner=Unsynchronized.ref (),
       nodes=Unsynchronized.ref Inttab.empty,
       payload_keys=Unsynchronized.ref Symtab.empty,
       next=Unsynchronized.ref 0,
       proof_entries=Unsynchronized.ref 0,
       scratch_entries=Unsynchronized.ref 0,
       peak_entries=Unsynchronized.ref 0,
       capacity=capacity,
       intern_hits=Unsynchronized.ref 0,
       branch_calls=Unsynchronized.ref 0,
       normalization_node_visits=Unsynchronized.ref 0,
       serialization_node_visits=Unsynchronized.ref 0}

  fun used (arena: arena) = ! (#next arena) + ! (#proof_entries arena) +
    ! (#scratch_entries arena)

  fun reserve (arena: arena) =
    let
      val current = used arena
      val _ = if current < #capacity arena then ()
        else error "Weighted CRT shared data arena exceeded its node/proof envelope"
      val next = current + 1
      val _ = #peak_entries arena := Int.max (! (#peak_entries arena), next)
    in () end

  fun reserve_scratch (arena: arena) allocated =
    let
      val current = used arena
      val _ = if current < #capacity arena then ()
        else error "Weighted CRT scratch exceeded the shared data arena envelope"
      val _ = allocated := !allocated + 1
      val _ = #scratch_entries arena := ! (#scratch_entries arena) + 1
      val _ = #peak_entries arena := Int.max (! (#peak_entries arena), current + 1)
    in () end

  fun release_scratch (arena: arena) allocated count =
    if count < 0 orelse count > !allocated orelse
        count > ! (#scratch_entries arena) then
      error "Weighted CRT attempted to release unowned scratch entries"
    else
      (allocated := !allocated - count;
       #scratch_entries arena := ! (#scratch_entries arena) - count)

  fun with_scratch (arena: arena) work =
    let
      val allocated = Unsynchronized.ref 0
      val outcome = Exn.capture (fn () => work allocated) ()
      val _ = #scratch_entries arena := ! (#scratch_entries arena) - !allocated
    in Exn.release outcome end

  fun check_reservation (arena: arena) (reservation: reservation) =
    if #owner reservation = #owner arena andalso ! (#alive reservation) then ()
    else error "Weighted CRT reservation is foreign or outside its scope"

  fun reserve_external (arena: arena) (reservation: reservation) =
    (check_reservation arena reservation;
     reserve_scratch arena (#active_scratch reservation))

  fun retain_external (arena: arena) (reservation: reservation) count =
    let
      val _ = check_reservation arena reservation
      val _ = if 0 <= count andalso count <= ! (#active_scratch reservation) then ()
        else error "Weighted CRT external proof retention is inconsistent"
      val _ = #active_scratch reservation := ! (#active_scratch reservation) - count
      val _ = #scratch_entries arena := ! (#scratch_entries arena) - count
      val _ = #pending_proofs reservation := ! (#pending_proofs reservation) + count
      val _ = #proof_entries arena := ! (#proof_entries arena) + count
      val _ = if used arena <= #capacity arena then ()
        else error "Weighted CRT external proofs exceeded the shared arena envelope"
      val _ = #peak_entries arena := Int.max (! (#peak_entries arena), used arena)
    in () end

  (* A reservation scope may publish retained cache state only when the
     callback returns successfully.  On failure, active scratch and pending
     proof charges roll back; callers must keep partial cache tables local to
     the callback and discard them before propagating the exception. *)
  fun with_reservation (arena: arena) work =
    let
      val reservation: reservation =
        {owner= #owner arena, active_scratch=Unsynchronized.ref 0,
         pending_proofs=Unsynchronized.ref 0, alive=Unsynchronized.ref true}
      val outcome = Exn.capture (fn () => work reservation) ()
      val active = ! (#active_scratch reservation)
      val pending = ! (#pending_proofs reservation)
      val _ = #alive reservation := false
      val _ = #active_scratch reservation := 0
      val _ = #pending_proofs reservation := 0
      val _ = #scratch_entries arena := ! (#scratch_entries arena) - active
      val _ = (case outcome of
        Exn.Res _ => ()
      | Exn.Exn _ => #proof_entries arena := ! (#proof_entries arena) - pending)
    in
      (case outcome of
        Exn.Res result => result
      | Exn.Exn failure => Exn.reraise failure)
    end

  fun with_proof_entry (arena: arena) work =
    with_reservation arena (fn reservation =>
      let
        val _ = reserve_external arena reservation
        val result = work ()
        val _ = retain_external arena reservation 1
      in result end)

  fun make_diagram (arena: arena) weight node: diagram =
    if weight < 0 then error "Weighted CRT data diagram has a negative offset"
    else {owner= #owner arena, offset=weight, node=node}

  fun check_diagram (arena: arena) ({owner, ...}: diagram) =
    if owner = #owner arena then ()
    else error "Weighted CRT data diagram belongs to another arena generation"

  fun payload_key ({key, value}: payload) =
    if String.size key = 0 then error "Weighted CRT data payload has an empty key"
    else if not (closed value) then
      error "Weighted CRT data payload term is open"
    else key

  fun shape_key shape =
    (case shape of
      Leaf {key, ...} => "L:" ^ key
    | Branch (axis, children) =>
        "B:" ^ Int.toString axis ^ ":" ^
          space_implode "," (map (fn (weight, child) =>
            Int.toString weight ^ "/" ^ Int.toString child) children))

  (* This conservative certificate is intrinsic to the immutable node.  A
     branch is already in normal form from its axis onward only when every
     child has a strictly greater certified lower axis, the edge vector is
     exact, the least edge weight is zero, and the branch cannot collapse. *)
  fun nf_lower (arena: arena) shape =
    (case shape of
      Leaf _ => SOME 4
    | Branch (axis,edges) =>
        if axis < 0 orelse axis >= length radices then NONE
        else
          let
            val radix = List.nth (radices,axis)
            val exact_extent = length edges = radix
            val nonnegative = List.all (fn (weight,_) => weight >= 0) edges
            val zero_minimum = List.exists (fn (weight,_) => weight = 0) edges
            val noncollapsing =
              (case edges of
                [] => false
              | first :: rest => not (forall (fn edge => edge = first) rest))
            fun child_lower child =
              (case Inttab.lookup (! (#nodes arena)) child of
                SOME (Node_Descriptor {nf_lower=SOME lower,...}) => lower
              | _ => ~1)
            val children_above =
              List.all (fn (_,child) => child_lower child > axis) edges
          in
            if exact_extent andalso nonnegative andalso zero_minimum andalso
                noncollapsing andalso children_above then SOME axis
            else NONE
          end)

  fun nf_lower_of (arena: arena) node =
    (case Inttab.lookup (! (#nodes arena)) node of
      SOME (Node_Descriptor {nf_lower,...}) => nf_lower
    | NONE => error "Weighted CRT data descriptor has a foreign node address")

  fun intern (arena: arena) shape =
    let val key = shape_key shape
    in
      (case Symtab.lookup (! (#payload_keys arena)) key of
        SOME id =>
          (case shape of
            Leaf payload =>
              (case Inttab.lookup (! (#nodes arena)) id of
                SOME (Node_Descriptor {shape=Leaf existing,...}) =>
                  if #value payload aconv #value existing then
                    (#intern_hits arena := ! (#intern_hits arena) + 1; id)
                  else error "Weighted CRT payload key aliases distinct typed values"
              | _ => error "Weighted CRT intern table has a leaf/branch key collision")
          | Branch _ => (#intern_hits arena := ! (#intern_hits arena) + 1; id))
      | NONE =>
          let
            val _ = reserve arena
            val id = ! (#next arena)
            val _ = #next arena := id + 1
            val descriptor = Node_Descriptor {shape=shape,nf_lower=nf_lower arena shape}
            val _ = #nodes arena := Inttab.update (id, descriptor) (! (#nodes arena))
            val _ = #payload_keys arena := Symtab.update (key, id)
              (! (#payload_keys arena))
          in id end)
    end

  fun shape_of (arena: arena) id =
    (case Inttab.lookup (! (#nodes arena)) id of
      SOME (Node_Descriptor {shape,...}) => shape
    | NONE => error "Weighted CRT data diagram contains a foreign node address")

  fun leaf (arena: arena) (payload: payload) =
    let
      val _ = payload_key payload
      val node = intern arena (Leaf payload)
    in make_diagram arena 0 node end

  fun check_axis axis =
    if 0 <= axis andalso axis < 4 then List.nth (radices, axis)
    else error "Weighted CRT data branch axis is outside 0..3"

  fun raw_branch (arena: arena) axis children =
    let
      val radix = check_axis axis
      val _ = List.app (check_diagram arena) (map #2 children)
      val _ = if List.all (fn (_, child) => #offset child = 0) children then ()
        else error "Raw weighted CRT branch requires offsets on explicit edges"
      val _ = if length children = radix then ()
        else error "Weighted CRT data branch has the wrong CRT radix"
      val _ = if List.all (fn (weight, _) => weight >= 0) children then ()
        else error "Weighted CRT data branch has a negative edge weight"
      val edges = map (fn (weight, child) => (weight, #node child)) children
      val node = intern arena (Branch (axis, edges))
    in make_diagram arena 0 node end

  fun raw_branch_diagrams (arena: arena) axis children =
    let
      val _ = List.app (check_diagram arena) children
    in raw_branch arena axis (map (fn child =>
      (#offset child, make_diagram arena 0 (#node child))) children) end

  fun branch (arena: arena) axis children =
    let
      val radix = check_axis axis
      val _ = List.app (check_diagram arena) children
      val _ = #branch_calls arena := ! (#branch_calls arena) + 1
      val _ = if length children = radix then ()
        else error "Weighted CRT data branch has the wrong CRT radix"
      val common = (case map #offset children of
          [] => error "Weighted CRT data branch has no children"
        | first :: rest => fold (fn n => fn minimum => Int.min (n, minimum)) rest first)
      val edges = map (fn child => (#offset child - common, #node child)) children
      val reduced = (case edges of
          [] => false
        | first :: rest => forall (fn edge => edge = first) rest)
    in
      if reduced then
        let val (weight, node) = hd edges
        in make_diagram arena (common + weight) node end
      else make_diagram arena common (intern arena (Branch (axis, edges)))
    end

  fun with_offset arena amount (action: diagram) =
    let
      val _ = check_diagram arena action
      val _ = if amount >= 0 then ()
        else error "Weighted CRT data offset adjustment is negative"
    in make_diagram arena (#offset action + amount) (#node action) end

  fun offset (action: diagram) = #offset action

  fun same_action arena left right =
    let
      val _ = check_diagram arena left
      val _ = check_diagram arena right
    in #offset left = #offset right andalso #node left = #node right end


  fun first_port (arena: arena) axis slot (action: diagram) =
    let
      val radix = check_axis axis
      val _ = check_diagram arena action
      val _ = if 0 <= slot andalso slot < radix then ()
        else error "Weighted CRT selector first-port slot is outside its radix"
      val lower = (case nf_lower_of arena (#node action) of
          SOME value => value
        | NONE => error "Weighted CRT selector received a noncanonical child")
    in
      if lower > axis then action
      else if lower < axis then
        error "Weighted CRT selector first-port axis precedes its split axis"
      else
        (case shape_of arena (#node action) of
          Branch (child_axis,edges) =>
            if child_axis = axis andalso length edges = radix then
              let val (weight,child) = List.nth (edges,slot)
              in make_diagram arena (#offset action + weight) child end
            else error "Weighted CRT selector metadata disagrees with child branch"
        | Leaf _ => error "Weighted CRT leaf has an impossible minimum axis")
    end

  fun erase_weights arena (action: diagram) =
    let
      val _ = check_diagram arena action
    in with_scratch arena (fn scratch =>
      let
        val memo = Unsynchronized.ref (Inttab.empty: diagram Inttab.table)
        fun visit id =
          (case Inttab.lookup (!memo) id of
            SOME result => result
          | NONE =>
              let
                val _ = reserve_scratch arena scratch
                val result =
                  (case shape_of arena id of
                    Leaf _ => make_diagram arena 0 id
                  | Branch (axis, children) =>
                      raw_branch arena axis
                        (map (fn (_, child) => (0, visit child)) children))
                val _ = reserve_scratch arena scratch
                val _ = memo := Inttab.update (id, result) (!memo)
              in result end)
        val projected = visit (#node action)
      in make_diagram arena 0 (#node projected) end)
    end

  fun shift_tree (arena: arena) delta initial_node =
    with_scratch arena (fn scratch =>
      let
        val memo = Unsynchronized.ref (Inttab.empty: diagram Inttab.table)
        fun visit id =
          (case Inttab.lookup (!memo) id of
            SOME result => result
          | NONE =>
              let
                val result =
                  (case shape_of arena id of
                    Leaf _ => make_diagram arena 0 id
                  | Branch (axis, children) =>
                      let
                        val radix = List.nth (radices, axis)
                        val selected = map (fn residue =>
                          let
                            val prior = (residue + delta) mod radix
                            val (weight, child) = List.nth (children, prior)
                            val shifted = visit child
                          in with_offset arena weight shifted end)
                          (0 upto (radix - 1))
                      in raw_branch_diagrams arena axis selected end)
                val _ = reserve_scratch arena scratch
                val _ = memo := Inttab.update (id, result) (!memo)
              in result end)
      in visit initial_node end)

  fun shift (arena: arena) delta (action: diagram) =
    let
      val _ = check_diagram arena action
      val _ = if delta >= 0 then ()
        else error "Weighted CRT phase shift is negative"
      val shifted = shift_tree arena delta (#node action)
    in make_diagram arena (#offset action + #offset shifted) (#node shifted) end

  (* Callback height includes the diagram root offset and all traversed edge
     weights.  The callback returns only additional output weight; source
     weights are retained by the rebuilt branches exactly once. *)
  fun bind (arena: arena) transform (action: diagram) =
    with_scratch arena (fn scratch =>
      let
        val _ = check_diagram arena action
        val memo = Unsynchronized.ref
          (Inttab.empty: diagram Inttab.table Inttab.table)
        fun visit accumulated id =
          (case Inttab.lookup
              (the_default Inttab.empty (Inttab.lookup (!memo) accumulated)) id of
            SOME result => result
          | NONE =>
              let
                val result =
                  (case shape_of arena id of
                    Leaf payload =>
                      let val mapped = transform payload (#offset action + accumulated)
                          val _ = check_diagram arena mapped
                      in mapped end
                  | Branch (axis, children) =>
                      raw_branch_diagrams arena axis (map (fn (weight, child) =>
                        with_offset arena weight (visit (accumulated + weight) child))
                        children))
                val row = the_default Inttab.empty
                  (Inttab.lookup (!memo) accumulated)
                val _ = reserve_scratch arena scratch
                val _ = memo := Inttab.update
                  (accumulated, Inttab.update (id, result) row) (!memo)
              in result end)
        val mapped = visit 0 (#node action)
      in make_diagram arena (#offset action + #offset mapped) (#node mapped) end)

  fun map_leaves (arena: arena) transform action =
    bind arena (fn payload => fn _ => leaf arena (transform payload)) action

  fun fold_leaves (arena: arena) step initial (action: diagram) =
    with_scratch arena (fn scratch =>
      let
        val _ = check_diagram arena action
        val visited = Unsynchronized.ref (Inttab.empty: unit Inttab.table Inttab.table)
        fun seen accumulated id =
          (case Inttab.lookup (the_default Inttab.empty
              (Inttab.lookup (!visited) accumulated)) id of
            SOME _ => true
          | NONE =>
              let
                val row = the_default Inttab.empty
                  (Inttab.lookup (!visited) accumulated)
                val _ = reserve_scratch arena scratch
                val _ = visited := Inttab.update
                  (accumulated, Inttab.update (id, ()) row) (!visited)
              in false end)
        fun walk accumulated id value =
          if seen accumulated id then value
          else
            (case shape_of arena id of
              Leaf payload => step payload (#offset action + accumulated) value
            | Branch (_, children) => fold (fn (weight, child) =>
                fn result => walk (accumulated + weight) child result) children value)
      in walk 0 (#node action) initial end)

  fun compile_selector (arena: arena) period values =
    let
      val _ = if period > 0 andalso 924 mod period = 0 andalso
          length values = period then ()
        else error "Weighted CRT selector period or row length is unsupported"
      fun build axes accumulated =
        (case axes of
          [] => leaf arena (List.nth (values, accumulated mod period))
        | axis :: rest =>
            let val weight = List.nth (clock_weights, axis)
            in
              if weight mod period = 0 then build rest accumulated
              else raw_branch arena axis (map (fn slot =>
                (0, build rest (accumulated + weight * slot)))
                (0 upto (List.nth (radices, axis) - 1)))
            end)
    in build [0,1,2,3] 0 end

  fun make_serializer (arena: arena) payloadT: serializer =
    let
      val dagT = Type (@{type_name comma_semantic_weighted_crt_dag}, [payloadT])
      val edgeT = HOLogic.mk_prodT (natT, dagT)
      fun tree (action: diagram) = with_scratch arena (fn scratch =>
        let
          val _ = check_diagram arena action
          val memo = Unsynchronized.ref (Inttab.empty: term Inttab.table)
          fun tree_node id =
            (case Inttab.lookup (!memo) id of
              SOME result => result
            | NONE =>
                let
                  val _ = reserve_scratch arena scratch
                  val _ = #serialization_node_visits arena :=
                    ! (#serialization_node_visits arena) + 1
                  val result =
                    (case shape_of arena id of
                      Leaf {value, ...} =>
                        if fastype_of value = payloadT then
                          Const (@{const_name Comma_Weighted_CRT_Leaf},
                            payloadT --> dagT) $ value
                        else error "Weighted CRT serializer payload type mismatch"
                    | Branch (axis, children) =>
                        let
                          val rows = map (fn (weight, child) =>
                            HOLogic.mk_prod (nat weight, tree_node child)) children
                        in Const (@{const_name Comma_Weighted_CRT_Branch},
                          natT --> HOLogic.listT edgeT --> dagT) $
                          nat axis $ HOLogic.mk_list edgeT rows end)
                  val _ = memo := Inttab.update (id, result) (!memo)
                in result end)
        in tree_node (#node action) end)
      fun action (diagram: diagram) =
        HOLogic.mk_prod (nat (#offset diagram), tree diagram)
    in {owner= #owner arena, payloadT=payloadT,
      tree=tree, action=action}: serializer end

  fun check_serializer (arena: arena) payloadT (serializer: serializer) =
    if #owner serializer = #owner arena andalso #payloadT serializer = payloadT then ()
    else error "Weighted CRT serializer belongs to another arena or payload type"

  fun tree (serializer: serializer) diagram = (#tree serializer) diagram

  fun action (serializer: serializer) diagram = (#action serializer) diagram

  fun make_normalization_proof_cache ctxt (arena: arena) payloadT =
    let
      val (native_certify, _) = Comma_Entry_Arithmetic.make_certifier ctxt
      val proof_profile =
        Comma_Semantic_Weighted_CRT_Data_Transport.make_profile
          "weighted_crt_normalization"
          ["data_wellformed", "data_cofactor", "branch_rows",
           "branch_normalize", "selector_admissibility", "selector_port",
           "selector_first_port_root", "selector_spine", "selector_family",
           "selector_diagonal",
           "selector_common", "closed_validation"]
    in {owner= #owner arena, payloadT=payloadT,
     theory=Proof_Context.theory_of ctxt,
     native_certify=native_certify,
     proof_profile=proof_profile,
     bottom_up_entries=Unsynchronized.ref Inttab.empty,
     selector_entries=Unsynchronized.ref Symtab.empty,
     size=Unsynchronized.ref 0}: normalization_proof_cache end

  fun cached_theorem_in_context ctxt cache label theorem =
    let val theorem_theory = Thm.theory_of_thm theorem
    in if Context.subthy (#theory cache, theorem_theory) andalso
        Context.subthy (theorem_theory, Proof_Context.theory_of ctxt) then ()
      else error (label ^ " is outside the cache theory lineage") end

  fun validated_cached_entry ctxt (arena: arena) payloadT
      (cache: normalization_proof_cache) node =
    (case Inttab.lookup (! (#bottom_up_entries cache)) node of
      NONE => NONE
    | SOME (entry: normalization_entry) =>
        let
          val _ = if #source_node entry = node then ()
            else error "Cached descendant normalization source key changed"
          val _ = check_diagram arena (#result entry)
          val _ = if #payloadT cache = payloadT andalso
              Context.subthy (#theory cache,Proof_Context.theory_of ctxt) then ()
            else error "Cached normalization entry has another publication authority"
          val _ = cached_theorem_in_context ctxt cache
            "Cached descendant normalization theorem" (#theorem entry)
        in SOME entry end)

  fun endpoint_trees ctxt arena payloadT cache node =
    Option.map (fn (entry: normalization_entry) =>
      (#source_tree entry,#target_tree entry))
      (validated_cached_entry ctxt arena payloadT cache node)

  fun native_closed ctxt cache theorem = standalone theorem andalso
    Context.subthy (#theory cache, Thm.theory_of_thm theorem) andalso
    Context.subthy (Thm.theory_of_thm theorem, Proof_Context.theory_of ctxt)

  fun check_publication ctxt _ _ profile cache label proposition theorem =
    Comma_Semantic_Weighted_CRT_Data_Transport.with_profile profile
      "closed_validation" (fn () =>
        if native_closed ctxt cache theorem andalso Thm.prop_of theorem aconv proposition
        then ignore ((#native_certify cache) theorem)
        else error (label ^ " was not a closed native theorem"))
  val cached_theorem_context = cached_theorem_in_context

  structure Certificate_Backend =
  struct
    type arena = arena
    type diagram = diagram
    type serializer = serializer
    type proof_cache = normalization_proof_cache
    type owner_token = owner_token
    type entry = normalization_entry
    type proof_profile = Comma_Semantic_Weighted_CRT_Data_Transport.proof_profile
    type node_view = {leaf: term option, branch: (int * (int * int) list) option}
    type stats = {nodes: int, proof_entries: int, scratch_entries: int,
      normalization_node_visits: int, serialization_node_visits: int}

    val natT = natT
    val radices = radices
    val nat = nat
    val profile_stats = Comma_Semantic_Weighted_CRT_Data_Transport.profile_stats
    val report = Comma_Proof_Profile.report
    val check_diagram = check_diagram
    fun owner_token (arena: arena) = #owner arena
    val make_diagram = make_diagram
    val with_offset = with_offset
    fun node (diagram: diagram) = #node diagram
    fun offset (diagram: diagram) = #offset diagram
    val same_action = same_action
    val nf_lower_of = nf_lower_of
    fun node_view (arena: arena) node =
      (case shape_of arena node of
        Leaf {value,...} => {leaf=SOME value,branch=NONE}
      | Branch (axis,rows) => {leaf=NONE,branch=SOME (axis,rows)})
    val first_port = first_port
    val raw_branch_diagrams = raw_branch_diagrams
    val branch = branch
    val with_proof_entry = with_proof_entry
    val with_scratch = with_scratch
    val reserve_scratch = reserve_scratch
    val release_scratch = release_scratch
    fun serialization_visit arena =
      #serialization_node_visits arena := ! (#serialization_node_visits arena) + 1
    fun normalization_visit arena =
      #normalization_node_visits arena := ! (#normalization_node_visits arena) + 1
    fun stats (arena: arena) =
      {nodes= ! (#next arena), proof_entries= ! (#proof_entries arena),
       scratch_entries= ! (#scratch_entries arena),
       normalization_node_visits= ! (#normalization_node_visits arena),
       serialization_node_visits= ! (#serialization_node_visits arena)}: stats
    fun validate_request ctxt (arena: arena) (payloadT: typ)
        (serializer: serializer) (cache: normalization_proof_cache)
        (initial: diagram) =
      let
        val _ = check_diagram arena initial
        val _ = check_serializer arena payloadT serializer
        val _ = if #owner cache = #owner arena andalso #payloadT cache = payloadT then ()
          else error "Weighted CRT normalization proof cache belongs to another arena or payload type"
        val _ = if Context.subthy (#theory cache,Proof_Context.theory_of ctxt) then ()
          else error "Weighted CRT normalization proof cache used outside its theory lineage"
      in () end
    fun native_certify (cache: normalization_proof_cache) = #native_certify cache
    fun profile (cache: normalization_proof_cache) = #proof_profile cache
    fun lookup_entry ctxt (arena: arena) (payloadT: typ)
        (cache: normalization_proof_cache) node =
      validated_cached_entry ctxt arena payloadT cache node
    fun cached_endpoint_trees ctxt (arena: arena) (payloadT: typ)
        (cache: normalization_proof_cache) node =
      endpoint_trees ctxt arena payloadT cache node
    fun lookup_selector ctxt (arena: arena) (payloadT: typ)
        (cache: normalization_proof_cache) key result =
      (case Symtab.lookup (! (#selector_entries cache)) key of
        NONE => NONE
      | SOME (entry: selector_proof_entry) =>
          let
            val _ = check_diagram arena (#result entry)
            val _ = if same_action arena (#result entry) result then ()
              else error "Cached weighted CRT selector result changed"
            val dagT = Type (@{type_name comma_semantic_weighted_crt_dag},[payloadT])
            val _ = if fastype_of (#source_tree entry) = dagT andalso
                fastype_of (#target_tree entry) = dagT then ()
              else error "Cached weighted CRT selector endpoint has the wrong type"
            val _ = cached_theorem_in_context ctxt cache
              "Cached weighted CRT selector theorem" (#theorem entry)
          in SOME (#theorem entry) end)
    val cached_theorem_in_context = cached_theorem_context
    fun publish_entry ctxt (arena: arena) (payloadT: typ) profile
        (cache: normalization_proof_cache)
        node delta result_node theorem proposition source_tree target_tree =
      let
        val _ = check_publication ctxt arena payloadT profile cache
          "Weighted CRT bottom-up normalization theorem" proposition theorem
        val dagT = Type (@{type_name comma_semantic_weighted_crt_dag},[payloadT])
        val _ = if fastype_of source_tree = dagT andalso fastype_of target_tree = dagT then ()
          else error "Weighted CRT normalization endpoint has the wrong type"
        val result = make_diagram arena delta result_node
        val _ = #bottom_up_entries cache := Inttab.update
          (node,{source_node=node,result=result,theorem=theorem,
            source_tree=source_tree,target_tree=target_tree})
          (! (#bottom_up_entries cache))
        val _ = #size cache := ! (#size cache) + 1
      in () end
    fun publish_selector ctxt (arena: arena) (payloadT: typ)
        (cache: normalization_proof_cache)
        key result source_tree target_tree proposition theorem =
      let
        val _ = check_diagram arena result
        val dagT = Type (@{type_name comma_semantic_weighted_crt_dag},[payloadT])
        val _ = if fastype_of source_tree = dagT andalso fastype_of target_tree = dagT then ()
          else error "Weighted CRT selector endpoint has the wrong type"
        val actionT = HOLogic.mk_prodT (natT,dagT)
        val resultT = HOLogic.mk_prodT (payloadT,natT)
        val apply_const = Const (@{const_name comma_weighted_crt_apply},
          actionT --> natT --> Type (@{type_name option},[resultT]))
        val root_offset = Free ("root_offset",natT)
        val phase = Free ("phase",natT)
        val source_action = HOLogic.mk_prod (root_offset,source_tree)
        val target_action = HOLogic.mk_prod
          (HOLogic.mk_binop @{const_name plus}
            (root_offset,nat (#offset result)),target_tree)
        val expected = HOLogic.mk_Trueprop (HOLogic.mk_all
          ("root_offset",natT,HOLogic.mk_all ("phase",natT,
            HOLogic.mk_eq (apply_const $ source_action $ phase,
              apply_const $ target_action $ phase))))
        val _ = if expected aconv proposition then ()
          else error "Weighted CRT selector proposition does not match its exact endpoints"
        val _ = check_publication ctxt arena payloadT (#proof_profile cache)
          cache "New weighted CRT selector theorem" expected theorem
        val _ = cached_theorem_in_context ctxt cache "New weighted CRT selector theorem" theorem
        val _ = #selector_entries cache := Symtab.update
          (key,{result=result,theorem=theorem,source_tree=source_tree,
            target_tree=target_tree,proposition=proposition})
          (! (#selector_entries cache))
      in () end
    fun cache_size (cache: normalization_proof_cache) = ! (#size cache)
  end

  structure Certificate_Builder =
    Comma_Semantic_Weighted_CRT_Certificate_BuilderFn (Certificate_Backend)

  type normalization_plan = Certificate_Builder.normalization_plan
  type selector_plan = Certificate_Builder.selector_plan
  datatype selector_piece = datatype Certificate_Builder.selector_piece
  type selector_view = {axis: int, split_axis: int, input_rows: diagram list,
    result: diagram, pieces: selector_piece list}

  fun with_normalization_plan arena action consume =
    Certificate_Builder.with_normalization_plan arena action consume
  val plan_source = Certificate_Builder.plan_source
  val plan_completed = Certificate_Builder.plan_completed
  val plan_result = Certificate_Builder.plan_result
  val plan_selector = Certificate_Builder.plan_selector
  val selector_common = Certificate_Builder.selector_common
  val plan_children = Certificate_Builder.plan_children
  fun with_selector_view arena selector consume =
    Certificate_Builder.with_selector_view arena selector (fn view =>
      consume {axis = #axis view, split_axis = #split_axis view,
        input_rows = #input_rows view, result = #result view,
        pieces = #pieces view})
  fun normalize arena action = Certificate_Builder.normalize arena action

  fun certify_normalization ctxt arena payloadT serializer cache initial =
    let val {normalized,equation,certified_nodes} =
      Certificate_Builder.certify ctxt arena payloadT serializer cache initial
    in {normalized=normalized,equation=equation,certified_nodes=certified_nodes} end

  fun stats (arena: arena) =
    {nodes= ! (#next arena), proof_entries= ! (#proof_entries arena),
     scratch_entries= ! (#scratch_entries arena),
     peak_entries= ! (#peak_entries arena),
     normalization_node_visits= ! (#normalization_node_visits arena),
     serialization_node_visits= ! (#serialization_node_visits arena),
     branch_calls= ! (#branch_calls arena),
     intern_hits= ! (#intern_hits arena)}: stats
end
