(* Terminal binding requests must retain the complete label and shift. *)
structure Comma_Direct_Terminal_Fixture =
struct
  fun run ctxt =
    let
      val owner = Comma_Direct_Terminal_Proofs.make ctxt
      val request = (@{term "Comma_Continuation_Fork 2 0"},
        @{term "Comma_Direct_Fork 2 0"})
      val first = #certify owner request
      val repeated = #certify owner request
      val _ = if Thm.prop_of first aconv Thm.prop_of repeated then ()
        else error "Repeated terminal request changed its proposition"
      val landmine = #certify owner
        (@{term "Comma_Continuation_Landmine 1"},@{term "Comma_Direct_Landmine 1"})
      fun reject label request =
        (case Exn.capture (#certify owner) request of
          Exn.Exn (ERROR _) => ()
        | Exn.Exn exn => Exn.reraise exn
        | Exn.Res _ => error ("Direct terminal owner accepted " ^ label))
      val _ = reject "changed fork label"
        (#1 request,@{term "Comma_Direct_Fork 3 0"})
      val _ = reject "lost terminal shift"
        (#1 request,@{term "Comma_Direct_Fork 2 1"})
      val _ = reject "unproved recursive child"
        (@{term "Comma_Continuation_Goto (Comma_Entry 2 0 0) 0"},
         @{term Comma_Direct_Invalid})
      val _ = reject "open expression"
        (#1 request,Free ("unproved_expression",@{typ comma_direct_action_expression}))
    in Comma_Proof_Dependency_Audit.require_native_clean ctxt
      "Direct terminal label, shift and recursive-authority boundaries"
      [first,repeated,landmine] end
end
