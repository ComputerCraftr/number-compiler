(* Selector alignment and authority substitution checks. *)
val _ =
    let
      val ctxt = @{context}
      val p = @{term "Comma_Near_Boundary_Program 2"}
      val q = @{term "Comma_Near_Boundary_Program 3"}
      val first = #operator_action Comma_Frontier24_Parametric_Runtime.computation p
      val second = #operator_action Comma_Frontier24_Parametric_Runtime.computation q
      val _ = if first aconv second then error "Alignment fixture actions coincide" else ()
      val actions = HOLogic.mk_list @{typ comma_source_continuation_action} [first,second]
      fun bundle programs selectors tokens = Term.subst_free
        [(@{term "fixture_programs::comma_semantic_port_program list"},programs),
         (@{term "fixture_selectors::comma_frontier24_selector_recipe list"},selectors),
         (@{term "fixture_tokens::comma_source_continuation_action list"},tokens)]
        @{term "\<lparr>cf24_programs=fixture_programs, cf24_selectors=fixture_selectors,
          cf24_action_tokens=fixture_tokens, cf24_guard_entries=[], cf24_closures=[],
          cf24_class_program_refs=[], cf24_class_roots=[], cf24_radices=[],
          cf24_nodes=[], cf24_zero_root=0\<rparr>"}
      val programs = HOLogic.mk_list @{typ comma_semantic_port_program} [p,q]
      val selectors = @{term "[Comma_Frontier24_Near_Selector 0,
        Comma_Frontier24_Near_Selector 1]"}
      val good = bundle programs selectors actions
      val {programs=ps,selectors=ss,...} =
        Comma_Frontier24_Selector_Alignment.rows ctxt good (Comma_Frontier24_Literal_Projections.make ctxt good)
      fun reference (program,selector) = Goal.prove ctxt [] []
        (HOLogic.mk_Trueprop (@{term comma_frontier24_selector_recipe_matches} $
          program $ selector $ actions))
        (fn {context,...} => Code_Simp.dynamic_tac context 1)
      val facts = map reference (ps ~~ ss)
      val checked = Comma_Frontier24_Selector_Alignment.certify ctxt good (Comma_Frontier24_Literal_Projections.make ctxt good) facts
      fun reject label run = (case Exn.capture run () of
          Exn.Exn (ERROR _) => ()
        | Exn.Exn exn => Exn.reraise exn
        | Exn.Res _ => error ("Selector alignment accepted " ^ label))
      val _ = reject "missing proof" (fn () =>
        Comma_Frontier24_Selector_Alignment.certify ctxt good (Comma_Frontier24_Literal_Projections.make ctxt good) (take 1 facts))
      val _ = reject "extra proof" (fn () =>
        Comma_Frontier24_Selector_Alignment.certify ctxt good (Comma_Frontier24_Literal_Projections.make ctxt good) (facts @ facts))
      val _ = reject "reordered proofs" (fn () =>
        Comma_Frontier24_Selector_Alignment.certify ctxt good (Comma_Frontier24_Literal_Projections.make ctxt good) (rev facts))
      val _ = reject "unproved hypothesis" (fn () =>
        Comma_Frontier24_Selector_Alignment.certify ctxt good
          (Comma_Frontier24_Literal_Projections.make ctxt good) [Thm.assume (Thm.cprop_of (hd facts)), List.last facts])
      val wrong_actions = HOLogic.mk_list @{typ comma_source_continuation_action}
        [second,first]
      val _ = reject "changed action owner" (fn () =>
        Comma_Frontier24_Selector_Alignment.certify ctxt
          (bundle programs selectors wrong_actions)
          (Comma_Frontier24_Literal_Projections.make ctxt (bundle programs selectors wrong_actions)) facts)
      val _ = reject "unequal list extents" (fn () =>
        Comma_Frontier24_Selector_Alignment.certify ctxt
          (bundle programs @{term "[Comma_Frontier24_Near_Selector 0]"} actions)
          (Comma_Frontier24_Literal_Projections.make ctxt (bundle programs @{term "[Comma_Frontier24_Near_Selector 0]"} actions)) facts)
      val empty_bundle = bundle @{term "[]::comma_semantic_port_program list"}
          @{term "[]::comma_frontier24_selector_recipe list"} actions
      val empty = Comma_Frontier24_Selector_Alignment.certify ctxt empty_bundle
        (Comma_Frontier24_Literal_Projections.make ctxt empty_bundle) []
    in Comma_Proof_Dependency_Audit.require_native_clean ctxt
      "Selector alignment and rejected authority substitutions" (checked::empty::facts) end

