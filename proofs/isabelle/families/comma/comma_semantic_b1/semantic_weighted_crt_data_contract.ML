(* Shared payload-polymorphic weighted CRT data arena. Typed leaf terms own
   mathematical identity. Keys are checked intern labels: equal typed values
   share a node, while reusing a key for another value is rejected. Each extra
   label is charged, and a view returns the first label of its canonical node.
   This owner retains the hash-cons table, normalizer, and proof cache. *)

signature COMMA_SEMANTIC_WEIGHTED_CRT_DATA =
sig
  type payload = {key: string, value: term}
  type diagram
  eqtype identity
  type arena
  type normalization_plan
  type selector_plan
  type reservation
  type serializer
  type normalization_proof_cache
  type term_cache_result = {term: term, theorem: thm}
  type term_cache_statistics = {hits: int, misses: int}
  type term_cache =
    {reduce: term -> term_cache_result,
     statistics: unit -> term_cache_statistics}
  type term_cache_totals =
    {hits: int Unsynchronized.ref, misses: int Unsynchronized.ref}
  type stats = {nodes: int, payload_aliases: int, proof_entries: int, scratch_entries: int,
    peak_entries: int, used_entries: int,
    normalization_node_visits: int, serialization_node_visits: int,
    branch_calls: int, intern_hits: int}
  datatype selector_piece =
      Same_Axis_Port of {slot: int, selected: diagram}
    | Lower_Axis_Port of
        {slot: int, restricted_rows: diagram list,
         child: selector_plan, child_common: int, child_result: diagram}
  type selector_view =
    {axis: int, split_axis: int, input_rows: diagram list,
     result: diagram, pieces: selector_piece list}
  datatype node_view =
      View_Leaf of {offset: int, payload: payload}
    | View_Branch of
        {offset: int, axis: int, children: (int * diagram) list}

  val make_arena: int -> arena
  val axis_radix: int -> int
  val axis_weight: int -> int
  val check_diagram: arena -> diagram -> unit
  val identity: arena -> diagram -> identity
  val identity_ord: identity * identity -> order
  val view: arena -> diagram -> node_view
  val view_stats: arena -> {node_visits: int, edge_visits: int}
  val with_reservation: arena -> (reservation -> 'a) -> 'a
  val check_reservation: arena -> reservation -> unit
  val reserve_external: arena -> reservation -> unit
  val retain_external: arena -> reservation -> int -> unit
  val make_term_cache: Proof.context -> arena -> reservation ->
    (reservation -> term -> term_cache_result) -> term_cache_totals -> term_cache
  val leaf: arena -> payload -> diagram
  val raw_branch: arena -> int -> (int * diagram) list -> diagram
  val raw_branch_diagrams: arena -> int -> diagram list -> diagram
  val branch: arena -> int -> diagram list -> diagram
  val normalized_branch: arena -> int -> diagram list -> diagram
  val with_normalized_branch: arena -> int -> diagram list ->
    (diagram * selector_plan -> 'a) -> 'a
  val with_offset: arena -> int -> diagram -> diagram
  val tree_part: arena -> diagram -> diagram
  val reduce_offset: arena -> int -> diagram -> diagram
  val offset: diagram -> int
  val same_action: arena -> diagram -> diagram -> bool
  val with_normalization_plan: arena -> diagram ->
    (normalization_plan -> 'a) -> 'a
  val plan_source: arena -> normalization_plan -> diagram
  val plan_completed: arena -> normalization_plan -> diagram
  val plan_result: arena -> normalization_plan -> diagram
  val plan_selector: arena -> normalization_plan -> selector_plan
  val selector_common: arena -> selector_plan -> int
  val with_selector_view: arena -> selector_plan -> (selector_view -> 'a) -> 'a
  val plan_children: arena -> normalization_plan ->
    (diagram * normalization_plan * diagram) list
  val normalize: arena -> diagram -> diagram
  (* Complete coordinate restriction after earlier axes have been selected.
     Foreign handles and unresolved earlier axes are rejected before lookup. *)
  val first_port: arena -> int -> int -> diagram -> diagram
  val erase_weights: arena -> diagram -> diagram
  val shift: arena -> int -> diagram -> diagram
  val bind: arena -> (payload -> int -> diagram) -> diagram -> diagram
  val map_leaves: arena -> (payload -> payload) -> diagram -> diagram
  val fold_leaves: arena -> (payload -> int -> 'a -> 'a) -> 'a -> diagram -> 'a
  val compile_selector: arena -> int -> payload list -> diagram
  val make_serializer: arena -> typ -> serializer
  val tree: serializer -> diagram -> term
  val action: serializer -> diagram -> term
  val make_normalization_proof_cache: Proof.context -> arena -> typ ->
    normalization_proof_cache
  val certify_normalization: Proof.context -> arena -> typ -> serializer ->
    normalization_proof_cache -> diagram ->
    {normalized: diagram, equation: thm, certified_nodes: int}
  val stats: arena -> stats
end

