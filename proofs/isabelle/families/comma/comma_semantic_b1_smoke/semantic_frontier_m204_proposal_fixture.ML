(* Bounded operational regression only: the resulting proposal is not a
   theorem until operation replay and source authority are kernel checked. *)
structure Comma_Frontier_M204_Proposal_Fixture =
struct
  structure Arena = Comma_CRT_MDD_Arena
  structure Proposal = Comma_Frontier_M204_Bellman_Proposal

  fun run () =
    let
      val d_arena = Arena.create [3,4,7,11]
      val step_arena = Arena.create [3,4,7,11]
      val zero = Arena.action_none d_arena
      val nine = Arena.action_some d_arena 8
      (* Continue 1 followed by Fork 2; physical phase remains external. *)
      val d_roots = nine :: replicate 45 zero
      val continue = Arena.action_some step_arena 1
      val fork2 = Arena.action_some step_arena 46
      val steps = continue :: replicate 45 fork2
      val proposal = Proposal.build d_arena d_roots step_arena steps
      val _ = if length (#roots proposal)=46 andalso
          List.all (fn root => case Arena.boolean_view (#arena proposal) root of
              Arena.Leaf_Value 1 => true | _ => false) (#roots proposal)
        then () else error "M204 proposal did not reduce correct Bellman roots to True"
      val fork3 = Arena.action_some step_arena 47
      val wrong = continue :: fork3 :: replicate 44 fork2
      val failure = Exn.capture (fn () => Proposal.build d_arena d_roots step_arena wrong) ()
      val _ = (case failure of Exn.Exn _ => ()
        | Exn.Res _ => error "M204 proposal accepted a wrong terminal label")
      val invalid = Arena.action_none step_arena
      val failure = Exn.capture (fn () =>
        Proposal.build d_arena d_roots step_arena (invalid :: replicate 45 fork2)) ()
      val _ = (case failure of Exn.Exn _ => ()
        | Exn.Res _ => error "M204 proposal accepted an invalid step")
    in () end
end
