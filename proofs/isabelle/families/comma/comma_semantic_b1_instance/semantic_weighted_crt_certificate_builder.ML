(* Private weighted CRT normalization orchestration; DATA owns interning, proofs, and the ledger. *)

signature COMMA_SEMANTIC_WEIGHTED_CRT_CERTIFICATE_BACKEND =
sig
  type arena
  type diagram
  type serializer
  type proof_cache
  eqtype owner_token
  type entry = {source_node: int, result: diagram, theorem: thm,
    source_tree: term, target_tree: term}
  type proof_profile = Comma_Semantic_Weighted_CRT_Data_Transport.proof_profile
  type node_view = {leaf: term option,
    branch: (int * (int * int) list) option}
  type stats = {nodes: int, proof_entries: int, scratch_entries: int,
    normalization_node_visits: int, serialization_node_visits: int}
  val natT: typ
  val radices: int list
  val nat: int -> term
  val validate_request: Proof.context -> arena -> typ -> serializer ->
    proof_cache -> diagram -> unit
  val native_certify: proof_cache -> thm -> thm
  val profile: proof_cache -> proof_profile
  val profile_stats: proof_profile -> string
  val report: string -> unit
  val check_diagram: arena -> diagram -> unit
  val owner_token: arena -> owner_token
  val make_diagram: arena -> int -> int -> diagram
  val with_offset: arena -> int -> diagram -> diagram
  val node: diagram -> int
  val offset: diagram -> int
  val same_action: arena -> diagram -> diagram -> bool
  val node_view: arena -> int -> node_view
  val nf_lower_of: arena -> int -> int option
  val first_port: arena -> int -> int -> diagram -> diagram
  val raw_branch_diagrams: arena -> int -> diagram list -> diagram
  val branch: arena -> int -> diagram list -> diagram
  val with_proof_entry: arena -> (unit -> 'a) -> 'a
  val with_scratch: arena -> (int Unsynchronized.ref -> 'a) -> 'a
  val reserve_scratch: arena -> int Unsynchronized.ref -> unit
  val release_scratch: arena -> int Unsynchronized.ref -> int -> unit
  val serialization_visit: arena -> unit
  val normalization_visit: arena -> unit
  val stats: arena -> stats
  val lookup_entry: Proof.context -> arena -> typ -> proof_cache -> int -> entry option
  val cached_endpoint_trees: Proof.context -> arena -> typ -> proof_cache ->
    int -> (term * term) option
  val lookup_selector: Proof.context -> arena -> typ -> proof_cache -> string ->
    diagram -> thm option
  val cached_theorem_in_context: Proof.context -> proof_cache -> string -> thm -> unit
  val publish_entry: Proof.context -> arena -> typ -> proof_profile -> proof_cache ->
    int -> int -> int -> thm -> term -> term -> term -> unit
  val publish_selector: Proof.context -> arena -> typ -> proof_cache ->
    string -> diagram -> term -> term -> term -> thm -> unit
  val cache_size: proof_cache -> int
end

functor Comma_Semantic_Weighted_CRT_Certificate_BuilderFn
    (B: COMMA_SEMANTIC_WEIGHTED_CRT_CERTIFICATE_BACKEND) =
struct
  type arena = B.arena
  type diagram = B.diagram
  type owner_token = B.owner_token
  type serializer = B.serializer
  type proof_cache = B.proof_cache

  datatype normalization_plan = Normalization_Plan of
    {scope: normalization_plan_scope, id: int, source_offset: int}
  and selector_plan = Selector_Plan of
    {scope: normalization_plan_scope, key: string, common: int,
     result: B.diagram}
  and selector_piece =
      Same_Axis_Port of {slot: int, selected: B.diagram}
    | Lower_Axis_Port of {slot: int, restricted_rows: B.diagram list,
        child: selector_plan, child_common: int, child_result: B.diagram}
  and normalization_plan_scope = Normalization_Plan_Scope of
    {owner: B.owner_token, active: bool Unsynchronized.ref,
     entries: normalization_plan_data Inttab.table Unsynchronized.ref,
     selectors: selector_plan_data Symtab.table Unsynchronized.ref}
  and normalization_plan_data = Normalization_Plan_Data of
    {completed: B.diagram, result: B.diagram, children: (int * int) list,
     selector_key: string option, selector_common: int}
  and selector_plan_data = Selector_Plan_Data of
    {axis: int, split_axis: int, input_rows: B.diagram list,
     result: B.diagram, pieces: selector_piece list, scratch_cost: int,
     compact: bool}
  type selector_view = {key: string, common: int, axis: int,
    split_axis: int, input_rows: B.diagram list, result: B.diagram,
    pieces: selector_piece list}
  type result = {normalized: B.diagram, equation: thm, certified_nodes: int}
  datatype node_shape = Leaf of term | Branch of int * (int * int) list

  fun check_axis axis = if 0 <= axis andalso axis < length B.radices then
    List.nth (B.radices,axis) else error "Weighted CRT selector axis is outside 0..3"

  fun node_shape arena node =
    (case B.node_view arena node of
      {leaf=SOME value,branch=NONE} => Leaf value
    | {leaf=NONE,branch=SOME shape} => Branch shape
    | _ => error "Weighted CRT node view returned an ambiguous descriptor")

  fun selector_key axis rows =
    "S:" ^ Int.toString axis ^ ":" ^
      space_implode ";" (map (fn row =>
        Int.toString (B.offset row) ^ "/" ^ Int.toString (B.node row)) rows)

  fun select_completed (arena: arena) scratch after_selector seed_ports
      (scope as Normalization_Plan_Scope {owner,active,selectors,...}) axis rows =
    let
      val radix = check_axis axis
      val _ = if owner = B.owner_token arena andalso !active then ()
        else error "Weighted CRT selector construction is outside its plan scope"
      val _ = if length rows = radix then ()
        else error "Weighted CRT selector input has the wrong parent radix"
      val _ = List.app (B.check_diagram arena) rows
      val offsets = map B.offset rows
      val common = (case offsets of
          [] => error "Weighted CRT selector has no rows"
        | first :: rest => fold (fn weight => fn minimum => Int.min (weight,minimum))
            rest first)
      val relative_rows = map (fn row =>
        B.make_diagram arena (B.offset row - common) (B.node row)) rows
      fun select_rows inputs =
        let
          val local_offsets = map B.offset inputs
          val local_common = (case local_offsets of
              [] => error "Weighted CRT selector has no rows"
            | first :: rest => fold
                (fn weight => fn minimum => Int.min (weight,minimum)) rest first)
          val relative = map (fn row =>
            B.make_diagram arena (B.offset row - local_common) (B.node row)) inputs
          val key = selector_key axis relative
        in
          (case Symtab.lookup (!selectors) key of
            SOME (Selector_Plan_Data cached) =>
              let
                val _ = if #axis cached = axis andalso
                    (#compact cached orelse
                     map (fn row => (B.offset row,B.node row)) (#input_rows cached) =
                       map (fn row => (B.offset row,B.node row)) relative) then ()
                  else error "Weighted CRT selector memo key aliases another input"
                val local_result = #result cached
              in
                (B.make_diagram arena (local_common + B.offset local_result)
                  (B.node local_result),key,local_common)
              end
          | NONE =>
              let
                (* Charge this plan and its ordered input view before recursion. *)
                val _ = B.reserve_scratch arena scratch
                val _ = fold (fn _ => fn () => B.reserve_scratch arena scratch)
                  relative ()
                val child_lowers = map (fn row =>
                  (case B.nf_lower_of arena (B.node row) of
                    SOME lower => lower
                  | NONE => error
                      "Weighted CRT selector input child has no canonical-axis certificate"))
                  relative
                val split_axis = fold
                  (fn lower => fn current => Int.min (lower,current))
                  child_lowers axis
                val piece_count = if split_axis = axis then radix
                  else List.nth (B.radices,split_axis)
                val _ = fold (fn _ => fn () => B.reserve_scratch arena scratch)
                  (0 upto (piece_count - 1)) ()
                val (result,pieces) =
                  if split_axis = axis then
                    let
                      val slots = 0 upto (radix - 1)
                      val selected = map2
                        (fn slot => fn row => B.first_port arena axis slot row)
                        slots relative
                      fun seed_same_axis slot sources selected_rows =
                        (case (sources,selected_rows) of
                          ([],[]) => ()
                        | (source :: rest,selected_row :: selected_rest) =>
                            (seed_ports axis slot [source] [selected_row];
                             seed_same_axis (slot + 1) rest selected_rest)
                        | _ => error "Weighted CRT same-axis seed changed its row extent")
                      val _ = seed_same_axis 0 relative selected
                      val pieces = map2
                        (fn slot => fn selected_row =>
                          Same_Axis_Port {slot=slot,selected=selected_row})
                        slots selected
                    in (B.branch arena axis selected,pieces) end
                  else
                    let
                      val split_radix = List.nth (B.radices,split_axis)
                      val slots = 0 upto (split_radix - 1)
                      val steps = map (fn slot =>
                        let
                          val restricted = map
                            (fn row => B.first_port arena split_axis slot row) relative
                          val _ = seed_ports split_axis slot relative restricted
                          val (child_result,child_key,child_common) =
                            select_rows restricted
                          val child_relative_result = B.make_diagram arena
                            (B.offset child_result - child_common) (B.node child_result)
                          val child_plan = Selector_Plan
                            {scope=scope,key=child_key,common=child_common,
                             result=child_relative_result}
                        in (child_result,Lower_Axis_Port
                          {slot=slot,restricted_rows=restricted,
                           child=child_plan,child_common=child_common,
                           child_result=child_result}) end) slots
                      val pieces = map #2 steps
                      val branch_rows = map #1 steps
                    in (B.branch arena split_axis branch_rows,pieces) end
                val scratch_cost = 1 + length relative + piece_count
                val plan_data = Selector_Plan_Data
                  {axis=axis,split_axis=split_axis,input_rows=relative,
                   result=result,pieces=pieces,
                   scratch_cost=scratch_cost,
                   compact=false}
                val _ = selectors := Symtab.update (key,plan_data) (!selectors)
                val plan = Selector_Plan
                  {scope=scope,key=key,common=local_common,result=result}
                (* Publish postorder; retain only a charged local result memo. *)
                val reclaim = after_selector plan
                val _ = if reclaim then
                  let
                    val retained_scratch = 1
                    val _ = if scratch_cost >= retained_scratch then ()
                      else error "Weighted CRT selector scratch charge is inconsistent"
                    val _ = B.release_scratch arena scratch
                      (scratch_cost - retained_scratch)
                    val memo = Selector_Plan_Data
                      {axis=axis,split_axis=axis,input_rows=[],result=result,pieces=[],
                       scratch_cost=retained_scratch,compact=true}
                    val _ = selectors := Symtab.update (key,memo) (!selectors)
                  in () end
                  else ()
              in
                (B.make_diagram arena (local_common + B.offset result)
                  (B.node result),key,local_common)
              end)
        end
      val (result,key,relative_common) = select_rows relative_rows
      val lifted_result = B.make_diagram arena
        (common + B.offset result) (B.node result)
    in (lifted_result,key,common + relative_common) end

  fun plan_entry (arena: arena)
      (Normalization_Plan {scope=Normalization_Plan_Scope
        {owner,active,entries,...},id,source_offset}) =
    let
      val _ = if owner = B.owner_token arena andalso !active then ()
        else error "Weighted CRT normalization plan is foreign or outside its scope"
      val data = (case Inttab.lookup (!entries) id of
          SOME (Normalization_Plan_Data fields) => fields
        | NONE => error "Weighted CRT normalization plan entry is unavailable")
      val _ = B.check_diagram arena (#completed data)
      val _ = B.check_diagram arena (#result data)
    in (entries, id, source_offset, data) end

  fun plan_source arena plan =
    let val (_,id,source_offset,_) = plan_entry arena plan
    in B.make_diagram arena source_offset id end

  fun plan_completed arena plan =
    let
      val (_,_,source_offset,data) = plan_entry arena plan
      val completed = #completed data
    in B.make_diagram arena (source_offset + B.offset completed) (B.node completed) end

  fun plan_result arena plan =
    let
      val (_,_,source_offset,data) = plan_entry arena plan
      val result = #result data
    in B.make_diagram arena (source_offset + B.offset result) (B.node result) end

  fun plan_children arena plan =
    let
      val (entries,_,_,data) = plan_entry arena plan
      fun child_row (weight,child_id) =
        let
          val _ = if weight >= 0 then ()
            else error "Weighted CRT normalization plan contains a negative row weight"
          val child_data = (case Inttab.lookup (!entries) child_id of
              SOME (Normalization_Plan_Data fields) => fields
            | NONE => error "Weighted CRT normalization plan omitted a child")
          val child_result = #result child_data
          val child_plan = Normalization_Plan
            {scope=(case plan of Normalization_Plan {scope,...} => scope),
             id=child_id,source_offset=0}
          val source_row = B.make_diagram arena weight child_id
          val completed_row = B.make_diagram arena
            (weight + B.offset child_result) (B.node child_result)
          val _ = B.check_diagram arena source_row
          val _ = B.check_diagram arena completed_row
        in (source_row,child_plan,completed_row) end
    in map child_row (#children data) end

  fun plan_selector arena plan =
    let
      val (_,_,_,data) = plan_entry arena plan
      val key = (case #selector_key data of
          SOME key => key
        | NONE => error "Weighted CRT leaf has no conditional selector plan")
      val selector = (case plan of
          Normalization_Plan {scope,...} =>
            Selector_Plan {scope=scope,key=key,
              common= #selector_common data,
              result=B.make_diagram arena (B.offset (#result data) - #selector_common data)
                (B.node (#result data))})
    in selector end

  fun selector_entry (arena: arena)
      (Selector_Plan {scope=Normalization_Plan_Scope
        {owner,active,selectors,...},key,common,result=handle_result}) =
    let
      val _ = if owner = B.owner_token arena andalso !active then ()
        else error "Weighted CRT selector plan is foreign or outside its scope"
      val data = (case Symtab.lookup (!selectors) key of
          SOME (Selector_Plan_Data fields) => fields
        | NONE => error "Weighted CRT selector plan entry is unavailable")
      val _ = if common >= 0 then ()
        else error "Weighted CRT selector common weight is negative"
      val _ = if #compact data then
          error "Weighted CRT compact selector memo has no proof plan view"
        else ()
      val _ = if selector_key (#axis data) (#input_rows data) = key then ()
        else error "Weighted CRT selector key does not match its ordered inputs"
      val _ = List.app (B.check_diagram arena) (#input_rows data)
      val _ = B.check_diagram arena (#result data)
      (* Plan results are relative; `common` is applied by the occurrence. *)
      val _ = if B.same_action arena handle_result (#result data) then ()
        else error "Weighted CRT selector result handle changed"
      val _ = List.app (fn piece =>
        (case piece of
          Same_Axis_Port {selected,...} => B.check_diagram arena selected
        | Lower_Axis_Port
            {restricted_rows,child,child_common=recorded_common,
             child_result,...} =>
            (List.app (B.check_diagram arena) restricted_rows;
             B.check_diagram arena child_result;
             let
               val Selector_Plan {scope=Normalization_Plan_Scope
                 {owner=child_owner,active=child_active,selectors=child_selectors,...},
                 key=child_key,common=handle_common,result=handle_result} = child
               val _ = if child_owner = B.owner_token arena andalso !child_active andalso
                   child_selectors = selectors andalso handle_common >= 0 andalso
                   recorded_common = handle_common then ()
                 else error "Weighted CRT nested selector handle has another scope"
               val _ = B.check_diagram arena handle_result
               val _ = if B.offset child_result >= handle_common andalso
                   B.same_action arena handle_result
                     (B.make_diagram arena
                       (B.offset child_result - handle_common) (B.node child_result)) then ()
                 else error "Weighted CRT nested selector result changed its common offset"
               val restricted_common = (case map B.offset restricted_rows of
                   [] => error "Weighted CRT nested selector has no restricted rows"
                 | first :: rest => fold
                     (fn weight => fn minimum => Int.min (weight,minimum)) rest first)
               val _ = if restricted_common = handle_common andalso
                   selector_key (#axis data)
                     (map (fn row => B.make_diagram arena
                       (B.offset row - restricted_common) (B.node row)) restricted_rows) = child_key then ()
                 else error "Weighted CRT nested selector key changed its restricted rows"
             in () end))) (#pieces data)
    in (selectors,key,common,data) end

  fun selector_common arena plan =
    let val (_,_,common,_) = selector_entry arena plan
    in common end

  fun with_selector_view arena plan consume =
    let
      val (_,key,common,data) = selector_entry arena plan
      val view: selector_view =
        {key=key,common=common,
         axis= #axis data, split_axis= #split_axis data,
         input_rows= #input_rows data, result= #result data,
         pieces= #pieces data}
    in consume view end

  fun with_normalization_plan_using (arena: arena) (action: diagram)
      cached_result after_node after_cleanup after_selector seed_ports consume =
    let
      val _ = B.check_diagram arena action
    in B.with_scratch arena (fn scratch =>
      let
        val scope = Normalization_Plan_Scope
          {owner= B.owner_token arena,active=Unsynchronized.ref true,
           entries=Unsynchronized.ref Inttab.empty,
           selectors=Unsynchronized.ref Symtab.empty}
        val entries = (case scope of Normalization_Plan_Scope fields => #entries fields)
        val selectors = (case scope of Normalization_Plan_Scope fields => #selectors fields)
        val active = (case scope of Normalization_Plan_Scope fields => #active fields)
        fun visit id =
          (case Inttab.lookup (!entries) id of
            SOME _ => id
          | NONE =>
              let
                val _ = B.reserve_scratch arena scratch
                val edge_slots = Unsynchronized.ref 0
                val _ = B.normalization_visit arena
                val known_result = cached_result id
                val (completed,children,result,selector_key,selector_common) =
                  (case known_result of
                    SOME result =>
                      let val _ = B.check_diagram arena result
                      in (B.make_diagram arena 0 id,[],result,NONE,0) end
                  | NONE =>
                      if Option.isSome (B.nf_lower_of arena id) then
                        let
                          val identity = B.make_diagram arena 0 id
                        in (identity,[],identity,NONE,0) end
                      else
                        let
                          val (completed,children,selector) =
                            (case node_shape arena id of
                              Leaf _ => (B.make_diagram arena 0 id, [], NONE)
                            | Branch (axis,edges) =>
                                let
                                  val _ = fold
                                    (fn _ => fn () => B.reserve_scratch arena scratch)
                                    edges ()
                                  val _ = edge_slots := length edges
                                  val children = map (fn (weight,child) =>
                                    (weight,visit child)) edges
                                  val completed_rows = map (fn (weight,child_id) =>
                                    let
                                      val child_data = (case Inttab.lookup (!entries) child_id of
                                          SOME (Normalization_Plan_Data fields) => fields
                                        | NONE => error
                                            "Weighted CRT normalization child was not completed")
                                      val child_result = #result child_data
                                      (* Revalidate/reseed after child cleanup and before
                                         building the parent selector. *)
                                      val _ = (case cached_result child_id of
                                          NONE => ()
                                        | SOME certified_result =>
                                            if B.same_action arena certified_result child_result then ()
                                            else error
                                              "Weighted CRT cached child changed after normalization")
                                    in B.make_diagram arena
                                      (weight + B.offset child_result) (B.node child_result) end)
                                    children
                                  val completed_tree =
                                    B.raw_branch_diagrams arena axis completed_rows
                                  val (result,key,common) = select_completed arena scratch
                                    after_selector seed_ports scope axis completed_rows
                                in (completed_tree,children,SOME (key,common,result)) end)
                          val (result,selector_key,selector_common) =
                            (case selector of
                              NONE => (completed,NONE,0)
                            | SOME (key,common,result) =>
                                (result,SOME key,common))
                        in (completed,children,result,selector_key,selector_common) end)
                val _ = entries := Inttab.update (id,
                  Normalization_Plan_Data
                    {completed=completed,result=result,children=children,
                     selector_key=selector_key,selector_common=selector_common}) (!entries)
                val plan = Normalization_Plan
                  {scope=scope,id=id,source_offset=0}
                val prune = after_node plan
                val _ = if prune then
                  let
                    val selector_slots = fold
                      (fn (_,Selector_Plan_Data data) => fn total =>
                        total + #scratch_cost data)
                      (Symtab.dest (!selectors)) 0
                    val _ = B.release_scratch arena scratch
                      (!edge_slots + selector_slots)
                    val _ = selectors := Symtab.empty
                    val _ = entries := Inttab.update (id,
                      Normalization_Plan_Data
                        {completed=completed,result=result,children=[],
                         selector_key=NONE,selector_common=0}) (!entries)
                  in () end
                  else ()
                val _ = if prune then after_cleanup plan else ()
              in id end)
        val outcome = Exn.capture (fn () =>
          let
            val root_id = visit (B.node action)
            val plan = Normalization_Plan
              {scope=scope,id=root_id,source_offset= B.offset action}
          in consume plan end) ()
        val _ = active := false
        val _ = entries := Inttab.empty
        val _ = selectors := Symtab.empty
      in Exn.release outcome end)
    end

  fun with_normalization_plan (arena: arena) (action: diagram) consume =
    with_normalization_plan_using arena action (fn _ => NONE) (fn _ => false)
      (fn _ => ()) (fn _ => false) (fn _ => fn _ => fn _ => fn _ => ()) consume

  fun normalize (arena: arena) (action: diagram) =
    let
      val _ = B.check_diagram arena action
    in
      (case B.nf_lower_of arena (B.node action) of
        SOME _ => action
        | NONE => with_normalization_plan arena action
          (fn plan => plan_result arena plan))
    end

  (* Validate authority before cache lookup; restore the root offset only
     when applying the cached theorem to its receiving occurrence. *)
  fun certify ctxt arena payloadT serializer cache initial: result =
    let
      val _ = B.validate_request ctxt arena payloadT serializer cache initial
      val native_certify = B.native_certify cache
      val proof_profile = B.profile cache
      val dagT = Type (@{type_name comma_semantic_weighted_crt_dag}, [payloadT])
      val actionT = HOLogic.mk_prodT (B.natT, dagT)
      val resultT = HOLogic.mk_prodT (payloadT, B.natT)
      val optionT = Type (@{type_name option}, [resultT])
      val apply_const = Const (@{const_name comma_weighted_crt_apply},
        actionT --> B.natT --> optionT)
      val leaf_const = Const (@{const_name Comma_Weighted_CRT_Leaf}, payloadT --> dagT)
      val edgeT = HOLogic.mk_prodT (B.natT, dagT)
      val edgeListT = HOLogic.listT edgeT
      val branch_const = Const (@{const_name Comma_Weighted_CRT_Branch},
        B.natT --> edgeListT --> dagT)
      val serialized_nodes = Unsynchronized.ref (Inttab.empty: term Inttab.table)
      val serialization_scratch = Unsynchronized.ref 0
      val initial_stats = B.stats arena
      val normalization_started = Time.now ()
      val initial_visits = #normalization_node_visits initial_stats
      val last_progress = Unsynchronized.ref initial_visits

      fun report_progress stage completed =
        if Comma_Proof_Profile.enabled () then
          let
            val stats = B.stats arena
            val elapsed = LargeInt.toString (Time.toMilliseconds
              (Time.- (Time.now (), normalization_started)))
          in B.report
            ("weighted_crt_normalization stage=" ^ stage ^
             " completed_nodes=" ^ Int.toString completed ^
             " normalization_visits=" ^ Int.toString (#normalization_node_visits stats) ^
             " serialization_visits=" ^ Int.toString (#serialization_node_visits stats) ^
             " nodes=" ^ Int.toString (#nodes stats) ^
             " proofs=" ^ Int.toString (#proof_entries stats) ^
             " scratch=" ^ Int.toString (#scratch_entries stats) ^
             " proof_cache_stage_totals=" ^ B.profile_stats proof_profile ^
             " request_elapsed_ms=" ^ elapsed)
          end
        else ()

      fun note_completed_node _ =
        let val stats = B.stats arena
            val visits = #normalization_node_visits stats
        in if visits - !last_progress >= 32 then
          (last_progress := visits;
           report_progress "progress" (visits - initial_visits))
          else () end

      val _ = report_progress "root-start" 0
      fun validated_cached_entry node = B.lookup_entry ctxt arena payloadT cache node
      fun cached_endpoint_trees node =
        B.cached_endpoint_trees ctxt arena payloadT cache node

      fun tree_node node =
        (case Inttab.lookup (!serialized_nodes) node of
          SOME result => result
        | NONE =>
            (case cached_endpoint_trees node of
              SOME (source_tree,_) =>
                let
                  (* Reuse the authenticated endpoint; retain a local sibling reference. *)
                  val _ = B.reserve_scratch arena serialization_scratch
                  val _ = serialized_nodes := Inttab.update
                    (node,source_tree) (!serialized_nodes)
                in source_tree end
            | NONE =>
                let
                  val shape = node_shape arena node
                  val _ = B.reserve_scratch arena serialization_scratch
                  val _ = B.serialization_visit arena
                  val result =
                    (case shape of
                      Leaf value =>
                        if fastype_of value = payloadT then leaf_const $ value
                        else error "Weighted CRT serializer payload type mismatch"
                    | Branch (axis,edges) =>
                        let
                          val rows = map (fn (weight,child) =>
                            HOLogic.mk_prod (B.nat weight, tree_node child)) edges
                        in branch_const $ B.nat axis $ HOLogic.mk_list edgeT rows end)
                  val _ = serialized_nodes := Inttab.update
                    (node,result) (!serialized_nodes)
                in result end))

      fun remember_tree node tree =
        if fastype_of tree = dagT then
          (case Inttab.lookup (!serialized_nodes) node of
            SOME existing => if existing aconv tree then ()
              else error "Weighted CRT cached tree key aliases another endpoint"
          | NONE =>
              (B.reserve_scratch arena serialization_scratch;
               serialized_nodes := Inttab.update (node,tree) (!serialized_nodes)))
        else error "Weighted CRT cached tree term has the wrong type"

      fun validated_cached_result node =
        (case validated_cached_entry node of
          NONE => NONE
        | SOME entry =>
            (remember_tree node (#source_tree entry);
             remember_tree (B.node (#result entry)) (#target_tree entry);
             SOME (#result entry)))

      fun seed_first_port_tree axis slot source selected =
        let
          val _ = B.check_diagram arena source
          val _ = B.check_diagram arena selected
          val source_tree = tree_node (B.node source)
          val selected_tree =
            (case node_shape arena (B.node source) of
              Branch (branch_axis,edges) =>
                if branch_axis = axis then
                  let
                    val _ = if length edges = List.nth (B.radices,axis) andalso
                        0 <= slot andalso slot < length edges then ()
                      else error "Weighted CRT first-port term selector has a wrong extent"
                    val (_,child) = List.nth (edges,slot)
                    val _ = if child = B.node selected then ()
                      else error "Weighted CRT first-port term selected another child"
                    val serialized_rows =
                      (case source_tree of
                        Const (name,_) $ serialized_axis $ rows =>
                          if name = @{const_name Comma_Weighted_CRT_Branch} andalso
                              serialized_axis aconv B.nat branch_axis then
                            HOLogic.dest_list rows
                          else error "Weighted CRT cached source branch changed its axis"
                      | _ => error "Weighted CRT cached source term is not a branch")
                    val (_,child_tree) = HOLogic.dest_prod (List.nth (serialized_rows,slot))
                  in child_tree end
                else if B.node source = B.node selected then source_tree
                else error "Weighted CRT unchanged first port changed its node"
            | Leaf _ =>
                if B.node source = B.node selected then source_tree
                else error "Weighted CRT leaf first port changed its node")
          val _ = remember_tree (B.node selected) selected_tree
        in () end

      fun seed_first_port_vector axis slot sources selected =
        let val _ = if length sources = length selected then ()
            else error "Weighted CRT first-port vector changed its row order"
        in List.app (fn (source,selected_row) =>
          seed_first_port_tree axis slot source selected_row)
          (ListPair.zip (sources,selected)) end

      fun action_term diagram =
        HOLogic.mk_prod (B.nat (B.offset diagram), tree_node (B.node diagram))
      fun same_vector left right = length left = length right andalso
        forall (fn (x,y) => B.same_action arena x y) (ListPair.zip (left,right))

      fun selector_proposition axis input_terms result_action =
        let
          val source_tree = branch_const $ B.nat axis $
            HOLogic.mk_list actionT input_terms
          val (result_offset,result_tree) = HOLogic.dest_prod result_action
          val root_offset = Free ("root_offset",B.natT)
          val phase = Free ("phase",B.natT)
          val source = HOLogic.mk_prod (root_offset,source_tree)
          val target = HOLogic.mk_prod
            (HOLogic.mk_binop @{const_name plus} (root_offset,result_offset),result_tree)
          val proposition = HOLogic.mk_Trueprop (HOLogic.mk_all
            ("root_offset",B.natT,HOLogic.mk_all ("phase",B.natT,
              HOLogic.mk_eq (apply_const $ source $ phase,apply_const $ target $ phase))))
        in (source_tree,result_tree,proposition) end

      fun selector_certificate selector =
        let
          val Selector_Plan {key,common,result,...} = selector
          val _ = B.check_diagram arena result
        in
          (case B.lookup_selector ctxt arena payloadT cache key result of
            SOME theorem => theorem
          | NONE =>
              let
                val {key=view_key,common=view_common,axis,split_axis,input_rows,
                  result=view_result,pieces} = with_selector_view arena selector (fn view => view)
                val _ = if key = view_key andalso common = view_common andalso
                    B.same_action arena result view_result then ()
                  else error "Weighted CRT selector handle disagrees with its live plan"
                fun certify_piece piece =
                  (case piece of
                    Same_Axis_Port {slot,selected} =>
                      (seed_first_port_tree split_axis slot
                        (List.nth (input_rows,slot)) selected;
                       Comma_Semantic_Weighted_CRT_Selector_Transport.Same_Axis_Port
                         {slot=slot,selected=action_term selected})
                  | Lower_Axis_Port
                      {slot,restricted_rows,child,child_common,child_result} =>
                      let
                        val _ = seed_first_port_vector split_axis slot input_rows restricted_rows
                        val child_equation = selector_certificate child
                        val Selector_Plan {key=child_key,common=handle_common,
                          result=handle_result,...} = child
                        val restricted_common = (case map B.offset restricted_rows of
                            [] => error "Weighted CRT lower-axis selector has no rows"
                          | first :: rest => fold
                              (fn weight => fn minimum => Int.min (weight,minimum))
                              rest first)
                        val _ = if restricted_common = child_common andalso
                            child_common = handle_common then ()
                          else error "Weighted CRT lower-axis selector common changed"
                        val child_relative_rows = map
                          (fn row => B.make_diagram arena
                            (B.offset row - child_common) (B.node row)) restricted_rows
                        val _ = if selector_key axis child_relative_rows = child_key then ()
                          else error "Weighted CRT lower-axis selector key changed its restricted rows"
                        val child_relative_result = B.make_diagram arena
                          (B.offset child_result - child_common) (B.node child_result)
                        val _ = if B.same_action arena handle_result child_relative_result then ()
                          else error "Weighted CRT lower-axis selector result handle changed"
                        val lifted_rows = map
                          (fn row => B.with_offset arena child_common row) child_relative_rows
                        val _ = if same_vector lifted_rows restricted_rows then ()
                          else error "Weighted CRT lower-axis selector changed first-port rows"
                        val lifted_result = B.with_offset arena child_common child_relative_result
                        val _ = if B.same_action arena lifted_result child_result then ()
                          else error "Weighted CRT lower-axis selector changed its child result"
                      in Comma_Semantic_Weighted_CRT_Selector_Transport.Lower_Axis_Port
                        {slot=slot,restricted_rows=map action_term child_relative_rows,
                         child_common=child_common,child_result=action_term child_relative_result,
                         child_equation=child_equation} end)
                val typed_pieces = map certify_piece pieces
                val input_terms = map action_term input_rows
                val result_action = action_term result
                val (source_tree,target_tree,proposition) =
                  selector_proposition axis input_terms result_action
                val theorem = B.with_proof_entry arena (fn () =>
                  let
                    val theorem =
                      Comma_Semantic_Weighted_CRT_Selector_Transport.certify_completed_select
                        native_certify proof_profile ctxt payloadT axis split_axis
                        input_terms typed_pieces result_action
                    val _ = B.cached_theorem_in_context ctxt cache
                      "New weighted CRT selector theorem" theorem
                    val _ = B.publish_selector ctxt arena payloadT cache key result
                      source_tree target_tree proposition theorem
                  in theorem end)
              in theorem end)
        end

      fun reflexive_proposition tree root_offset phase =
        let val action = HOLogic.mk_prod (root_offset,tree)
        in HOLogic.mk_Trueprop (HOLogic.mk_all ("root_offset",B.natT,
          HOLogic.mk_all ("phase",B.natT,
            HOLogic.mk_eq (apply_const $ action $ phase,apply_const $ action $ phase)))) end

      fun certify_plan (plan: normalization_plan) =
        let
          val source = plan_source arena plan
          val completed = plan_completed arena plan
          val result = plan_result arena plan
          val node = B.node source
          val delta = B.offset result - B.offset source
          fun publish theorem proposition source_tree target_tree =
            (B.publish_entry ctxt arena payloadT proof_profile cache node delta
              (B.node result) theorem proposition source_tree target_tree;
             theorem)
        in
          if delta < 0 then error "Weighted CRT bottom-up normalization decreased its root weight"
          else
            (case validated_cached_entry node of
              SOME entry =>
                let
                  val expected_result = B.make_diagram arena delta (B.node result)
                  val _ = if B.same_action arena (#result entry) expected_result then ()
                    else error "Cached bottom-up result disagrees with its scoped plan"
                in #theorem entry end
            | NONE =>
                if B.same_action arena source result then
                  let
                    val _ = if delta = 0 then ()
                      else error "Weighted CRT identity normalization has a nonzero delta"
                    val tree = tree_node node
                    val root_offset = Free ("root_offset",B.natT)
                    val phase = Free ("phase",B.natT)
                    val action = HOLogic.mk_prod (root_offset,tree)
                    val proposition = reflexive_proposition tree root_offset phase
                    val theorem = B.with_proof_entry arena (fn () =>
                      let
                        val theorem =
                          Comma_Semantic_Weighted_CRT_Data_Transport.pointwise_reflexive
                            native_certify proof_profile ctxt apply_const root_offset phase action
                      in publish theorem proposition tree tree end)
                  in theorem end
                else
                  let
                    val root_offset = Free ("root_offset",B.natT)
                    val phase = Free ("phase",B.natT)
                    val theorem = B.with_proof_entry arena (fn () =>
                      let
                        val (theorem,proposition,source_tree,result_tree) =
                          B.with_scratch arena (fn scratch =>
                        let
                          val rows = plan_children arena plan
                          val _ = List.app (fn _ => B.reserve_scratch arena scratch)
                            (0 upto (3 * length rows + 1))
                          fun certify_child (raw_row,child_plan,completed_row) =
                            (case node_shape arena (B.node raw_row) of
                              Leaf _ =>
                                let
                                  val _ = B.reserve_scratch arena scratch
                                  val source_tree = tree_node (B.node raw_row)
                                  val completed_tree = tree_node (B.node completed_row)
                                  val _ = if source_tree aconv completed_tree then ()
                                    else error "Weighted CRT leaf changed during normalization"
                                  val action = HOLogic.mk_prod (root_offset,source_tree)
                                in Comma_Semantic_Weighted_CRT_Data_Transport.pointwise_reflexive
                                  native_certify proof_profile ctxt apply_const
                                  root_offset phase action end
                            | Branch _ =>
                                let
                                  val equation = certify_plan child_plan
                                  val cached_entry =
                                    (case validated_cached_entry (B.node raw_row) of
                                      SOME entry => entry
                                    | NONE => error
                                        "Weighted CRT child theorem was not published")
                                  val cached = #result cached_entry
                                  val expected_child = plan_result arena child_plan
                                  val _ = if B.same_action arena cached expected_child then ()
                                    else error "Weighted CRT child theorem changed its completed action"
                                  val _ = remember_tree (B.node raw_row)
                                    (#source_tree cached_entry)
                                  val _ = remember_tree (B.node completed_row)
                                    (#target_tree cached_entry)
                                in equation end)
                          val child_equations = map certify_child rows
                          val selector_proof =
                            (case node_shape arena (B.node completed) of
                              Leaf _ => NONE
                            | Branch _ =>
                                let val selector = plan_selector arena plan
                                in SOME (selector,selector_certificate selector) end)
                          val source_tree = tree_node node
                          val completed_tree = tree_node (B.node completed)
                          val result_tree = tree_node (B.node result)
                          val proposition = HOLogic.mk_Trueprop (HOLogic.mk_all
                            ("root_offset",B.natT,HOLogic.mk_all ("phase",B.natT,
                              HOLogic.mk_eq
                                (apply_const $ HOLogic.mk_prod (root_offset,source_tree) $ phase,
                                 apply_const $ HOLogic.mk_prod
                                   (HOLogic.mk_binop @{const_name plus}
                                     (root_offset,B.nat delta),result_tree) $ phase))))
                          val unchanged = B.same_action arena source completed
                          val (raw_rows,completed_rows) =
                            (map (fn (raw_row,_,_) => action_term raw_row) rows,
                             map (fn (_,_,completed_row) => action_term completed_row) rows)
                          val canonical_equation =
                            (case node_shape arena (B.node completed) of
                              Leaf _ =>
                                let
                                  val action = HOLogic.mk_prod (root_offset,completed_tree)
                                in Comma_Semantic_Weighted_CRT_Data_Transport.pointwise_reflexive
                                  native_certify proof_profile ctxt apply_const
                                  root_offset phase action end
                            | Branch _ =>
                                let
                                  val (selector,selector_theorem) =
                                    (case selector_proof of
                                      SOME result => result
                                    | NONE => error
                                        "Weighted CRT completed branch omitted its selector proof")
                                  val Selector_Plan {common,key,result=relative_result,...} = selector
                                  val selector_axis = (case node_shape arena (B.node completed) of
                                      Branch (branch_axis,_) => branch_axis
                                    | Leaf _ => error
                                        "Weighted CRT completed selector source is not a branch")
                                  val completed_rows = map #3 rows
                                  val completed_offsets = map B.offset completed_rows
                                  val completed_common = (case completed_offsets of
                                      [] => error "Weighted CRT completed selector has no rows"
                                    | first :: rest => fold
                                        (fn weight => fn minimum => Int.min (weight,minimum))
                                        rest first)
                                  val relative_rows_data = map
                                    (fn row => B.make_diagram arena
                                      (B.offset row - completed_common) (B.node row))
                                    completed_rows
                                  val _ = if completed_common = common andalso
                                      selector_key selector_axis relative_rows_data = key then ()
                                    else error "Weighted CRT selector source changed after publication"
                                  val relative_rows = map action_term relative_rows_data
                                  val relative_result_action = action_term relative_result
                                  val lifted_rows = map
                                    (fn row => action_term (B.with_offset arena common row))
                                    relative_rows_data
                                  val expected_completed_tree = branch_const $
                                    B.nat selector_axis $
                                    HOLogic.mk_list actionT lifted_rows
                                  val _ = if completed_tree aconv expected_completed_tree then ()
                                    else error
                                      "Weighted CRT selector input differs from its completed parent"
                                  val expected_result_weight = common +
                                    B.offset relative_result
                                  val _ = if expected_result_weight = delta andalso
                                      B.node relative_result = B.node result then ()
                                    else error
                                      "Weighted CRT selector result differs from its normalization plan"
                                in Comma_Semantic_Weighted_CRT_Selector_Transport.lift_selector_common
                                  native_certify proof_profile ctxt payloadT
                                  selector_axis common relative_rows
                                  relative_result_action selector_theorem end)
                          val composed = if unchanged then
                            let
                              val action = HOLogic.mk_prod (root_offset,source_tree)
                              val reflexive =
                                Comma_Semantic_Weighted_CRT_Data_Transport.pointwise_reflexive
                                  native_certify proof_profile ctxt apply_const
                                  root_offset phase action
                              val result_action = HOLogic.mk_prod
                                (HOLogic.mk_binop @{const_name plus}
                                  (root_offset,B.nat delta),result_tree)
                            in Comma_Semantic_Weighted_CRT_Data_Transport.compose_pointwise_profile
                              native_certify proof_profile ctxt
                              "Weighted CRT bottom-up normalization theorem"
                              apply_const root_offset phase action result_action
                              [reflexive,canonical_equation] end
                          else
                            let
                              val axis = (case node_shape arena node of
                                  Branch (branch_axis,_) => branch_axis
                                | Leaf _ => error
                                    "Weighted CRT leaf changed during child completion")
                            in Comma_Semantic_Weighted_CRT_Branch_Transport.certify_bottom_up_normalization
                              native_certify proof_profile ctxt payloadT axis
                              source_tree completed_tree (B.nat delta) result_tree
                              raw_rows completed_rows child_equations canonical_equation end
                        in (composed,proposition,source_tree,result_tree) end)
                      in publish theorem proposition source_tree result_tree end)
                  in theorem end)
        end

      fun cached_normalization initial =
        (case validated_cached_entry (B.node initial) of
          NONE => NONE
        | SOME entry =>
            let
              val normalized = B.make_diagram arena
                (B.offset initial + B.offset (#result entry))
                (B.node (#result entry))
            in SOME {normalized=normalized,equation= #theorem entry,
              certified_nodes=B.cache_size cache} end)

      fun certify_selector_on_build selector =
        (ignore (selector_certificate selector); true)

      fun canonical_normalization initial =
        (case B.nf_lower_of arena (B.node initial) of
          NONE => NONE
        | SOME _ =>
            let
              val node = B.node initial
              val tree = tree_node node
              val root_offset = Free ("root_offset",B.natT)
              val phase = Free ("phase",B.natT)
              val action = HOLogic.mk_prod (root_offset,tree)
              val proposition = reflexive_proposition tree root_offset phase
              val theorem = B.with_proof_entry arena (fn () =>
                let
                  val theorem =
                    Comma_Semantic_Weighted_CRT_Data_Transport.pointwise_reflexive
                      native_certify proof_profile ctxt apply_const root_offset phase action
                  val _ = B.cached_theorem_in_context ctxt cache
                    "New canonical normalization theorem" theorem
                  val _ = B.publish_entry ctxt arena payloadT proof_profile cache
                    node 0 node theorem proposition tree tree
                in theorem end)
            in SOME {normalized=initial,equation=theorem,
              certified_nodes=B.cache_size cache} end)

      val outcome = Exn.capture (fn () =>
        (case cached_normalization initial of
          SOME result => result
        | NONE =>
            (case canonical_normalization initial of
              SOME result => result
            | NONE => with_normalization_plan_using arena initial validated_cached_result
                (fn plan =>
                  let
                    val _ = certify_plan plan
                    val _ = B.release_scratch arena serialization_scratch
                      (!serialization_scratch)
                    val _ = serialized_nodes := Inttab.empty
                  in true end)
                note_completed_node
                certify_selector_on_build
                seed_first_port_vector
                (fn plan =>
                  let
                    val _ = if B.same_action arena (plan_source arena plan) initial then ()
                      else error "Weighted CRT scoped normalization plan changed its source action"
                    val theorem = certify_plan plan
                    val normalized = plan_result arena plan
                  in {normalized=normalized,equation=theorem,
                    certified_nodes=B.cache_size cache} end)))) ()
      val _ = B.release_scratch arena serialization_scratch (!serialization_scratch)
    in Exn.release outcome end
end
