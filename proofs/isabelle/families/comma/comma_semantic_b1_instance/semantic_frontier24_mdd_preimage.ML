(* Source-root 24-round proposal for the shared CRT MDD arena.
   Returned roots and node terms are untrusted proposal data until the
   final-table kernel certificates authenticate them. *)
signature COMMA_FRONTIER24_MDD_PROPOSAL =
sig
  type arena = Comma_CRT_MDD_Arena.arena
  type round = {shifted: Comma_CRT_MDD_Arena.boolean_root list,
    roots: Comma_CRT_MDD_Arena.boolean_root list}
  type history = {initial: Comma_CRT_MDD_Arena.boolean_root list, rounds: round list}
  val new_arena: unit -> arena
  val make_initial_roots: arena -> Comma_CRT_MDD_Arena.boolean_root list
  val build_24_rounds: arena -> Comma_CRT_MDD_Arena.action_root list ->
    Comma_CRT_MDD_Arena.boolean_root list -> history
  val final_roots: history -> Comma_CRT_MDD_Arena.boolean_root list
end

structure Comma_Frontier24_MDD_Proposal: COMMA_FRONTIER24_MDD_PROPOSAL =
struct
  structure Arena = Comma_CRT_MDD_Arena

  type arena = Arena.arena
  type round = {shifted: Arena.boolean_root list, roots: Arena.boolean_root list}
  type history = {initial: Arena.boolean_root list, rounds: round list}

  fun make_initial_roots arena =
    let
      val true_root = Arena.boolean_true arena
      val false_root = Arena.boolean_false arena
      val exceptional = Inttab.make [(33,299), (10,66), (12,298), (32,67), (1,68)]
      val radices = Arena.radices arena
      val _ = if radices = [3,4,11,7] then ()
        else error "Frontier24 initial points require the declared CRT axes"
      fun point_complement phase =
        let
          val coordinates = map (fn radix => phase mod radix) radices
          fun build [] current = current
            | build ((axis, radix) :: rest) current =
                let
                  val selected = List.nth (coordinates, axis)
                  val children = map (fn slot =>
                    if slot = selected then current else true_root)
                    (0 upto (radix - 1))
                in build rest (Arena.boolean_branch arena axis children) end
        in build (rev (map_index I radices)) false_root end
      fun class_root cid =
        (case Inttab.lookup exceptional cid of
          NONE => true_root
        | SOME excluded_phase => point_complement excluded_phase)
    in map class_root (0 upto 45) end

  fun build_24_rounds arena actions roots =
    let
      val _ = if length actions = 46 andalso length roots = 46 then ()
        else error "Frontier24 recurrence requires 46 action and state roots"
      val fallback = Arena.boolean_false arena
      fun one_round previous =
        let
          val next_phase_roots = map (fn root => Arena.shift_boolean arena root 1) previous
          val target_mapping = map_index (fn (target, root) => (target, root)) next_phase_roots
          val next = map (fn action =>
            Arena.bind_action_to_boolean arena action fallback target_mapping) actions
        in {shifted=next_phase_roots,roots=next}: round end
      fun append_round _ (previous,history) =
        let val next = one_round previous
        in (#roots next,next::history) end
      val (_,reversed) = fold append_round (0 upto 23) (roots,[])
    in {initial=roots,rounds=rev reversed}: history end

  fun final_roots ({initial,rounds}: history) =
    fold (fn ({roots,...}: round) => K roots) rounds initial

  fun new_arena () = Arena.create [3, 4, 11, 7]
end
