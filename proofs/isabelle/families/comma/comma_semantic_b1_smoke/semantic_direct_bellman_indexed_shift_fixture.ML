(* Real Continue proposal and replay use one mapped shift over a selected D root. *)
structure Comma_Direct_Bellman_Indexed_Shift_Fixture =
struct
  structure Arena = Comma_CRT_MDD_Arena
  structure Store = Comma_CRT_MDD_Certificate_Store
  structure Operation = Comma_CRT_MDD_Operation_Replay
  structure Proposal = Comma_Direct_Bellman_Terminal_Proposal
  structure Terminal = Comma_Direct_Bellman_Terminal_Proofs
  structure Utils = Comma_CRT_MDD_Proof_Utils
  val natT = @{typ nat}
  fun nat n = HOLogic.mk_number natT n
  fun run lthy =
    let
      val arena = Arena.create [3,4,7,11]
      val zero = Arena.action_none arena
      val one = Arena.action_some arena 0
      val source = Arena.action_branch arena 0 [zero,one,zero]
      val roots = map (fn i => if i=7 then source else zero) (0 upto 45)
      val proposal = Proposal.make arena roots
      val expression_body = @{term "Comma_Direct_Continue 7 1"}
      val output = (case #terminal proposal arena expression_body 0 of
          SOME value => value | NONE => error "Continue proposal missing")
      val continuations = #continuations proposal ()
      val constant_map = Arena.make_action_shift_map arena (fn _ => 4)
      val constant_output = Arena.shift_map_action constant_map source 1
      val _ = (case Arena.action_view arena constant_output of Arena.Leaf_Value 4 => ()
        | _ => error "Noninjective mapped shift did not reduce to a leaf")
      val other_map = Arena.make_action_shift_map arena (fn x => x+10)
      val other_output = Arena.shift_map_action other_map source 1
      val two = Arena.action_some arena 1
      val three = Arena.action_some arena 2
      val lower_a = Arena.action_branch arena 1 [zero,one,zero,one]
      val lower_b = Arena.action_branch arena 1 [two,three,two,three]
      val alias_source = Arena.action_branch arena 0 [lower_a,lower_b,lower_a]
      val parity_map = Arena.make_action_shift_map arena (fn x => x mod 2)
      val alias_output = Arena.shift_map_action parity_map alias_source 1
      val _ = (case Arena.action_view arena alias_output of Arena.Branch_At (axis,_) =>
          if axis=1 then () else error "Mapped alias retained wrong axis"
        | _ => error "Mapped alias failed to retain the later branch")
      fun rejects label f = (case Exn.capture f () of Exn.Exn _ => ()
        | Exn.Res _ => error ("Indexed mapped shift accepted " ^ label))
      val foreign_arena = Arena.create [3,4,7,11]
      val foreign_root = Arena.action_none foreign_arena
      val _ = rejects "foreign Arena root" (fn () =>
        Arena.shift_map_action constant_map foreign_root 1)
      val (store,lthy1) = Store.make "bellman_indexed_shift_fixture_nodes" arena lthy
      val source_id = Store.action_index store source
      val output_id = Store.action_index store output
      val zero_id = Store.action_index store zero
      val literal = HOLogic.mk_list natT (map (nat o Store.action_index store) roots)
      val ((local_roots,(_,local_roots_def)),lthy2) = Local_Theory.define
        ((Binding.name "bellman_indexed_shift_fixture_roots",NoSyn),
         ((Binding.name "bellman_indexed_shift_fixture_roots_def",[]),literal)) lthy1
      val morphism2 = Local_Theory.target_morphism lthy2
      val roots_term = Morphism.term morphism2 local_roots
      val roots_def = Morphism.thm morphism2 local_roots_def
      val rhs = @{term comma_frontier_m204_mdd_value} $
        Store.radices store $ Store.table store $ roots_term
      val ((local_D,(_,local_D_def)),lthy3) = Local_Theory.define
        ((Binding.name "bellman_indexed_shift_fixture_D",NoSyn),
         ((Binding.name "bellman_indexed_shift_fixture_D_def",[]),rhs)) lthy2
      val morphism3 = Local_Theory.target_morphism lthy3
      val D = Morphism.term morphism3 local_D
      val D_def = Morphism.thm morphism3 local_D_def
      val ((local_expr,(_,local_expr_def)),lthy4) = Local_Theory.define
        ((Binding.name "bellman_indexed_shift_fixture_expr",NoSyn),
         ((Binding.name "bellman_indexed_shift_fixture_expr_def",[]),expression_body)) lthy3
      val morphism4 = Local_Theory.target_morphism lthy4
      val expression = Morphism.term morphism4 local_expr
      val expression_def = Morphism.thm morphism4 local_expr_def
      val ctxt = Local_Theory.target_of lthy4
      val store_ctxt = Store.context store
      fun definition term = Utils.exact_prop ctxt "Fixture expression definition"
        (Logic.mk_equals (term,expression_body)) expression_def
      val owner = Terminal.make ctxt store arena roots roots_term roots_def D D_def
        definition continuations
      val theorem = #terminal owner expression 0 output_id
      val encode = @{term "\<lambda>x::nat. x+9"}
      fun leaf x y = Utils.prove_exact store_ctxt "Fixture mapped shift leaf"
        (HOLogic.mk_Trueprop (HOLogic.mk_eq (Envir.beta_norm (encode $ nat x),nat y)))
        (fn _ => simp_tac (Comma_Entry_Arithmetic.natural_context store_ctxt) 1)
      val replay = Operation.make_mapped store encode leaf
      val cert = Operation.certify_mapped_shift replay 1 source_id output_id
      val transported = Terminal.indexed_shift ctxt store roots_term roots_def
        7 source_id output_id cert
      val constant_encode = @{term "\<lambda>x::nat. (4::nat)"}
      fun constant_leaf x y = Utils.prove_exact store_ctxt "Fixture constant-map leaf"
        (HOLogic.mk_Trueprop (HOLogic.mk_eq
          (Envir.beta_norm (constant_encode $ nat x),nat y)))
        (fn _ => simp_tac (Comma_Entry_Arithmetic.natural_context store_ctxt) 1)
      val constant_replay = Operation.make_mapped store constant_encode constant_leaf
      val constant_cert = Operation.certify_mapped_shift constant_replay 1 source_id
        (Store.action_index store constant_output)
      val other_encode = @{term "\<lambda>x::nat. x+10"}
      fun other_leaf x y = Utils.prove_exact store_ctxt "Fixture alternate-map leaf"
        (HOLogic.mk_Trueprop (HOLogic.mk_eq
          (Envir.beta_norm (other_encode $ nat x),nat y)))
        (fn _ => simp_tac (Comma_Entry_Arithmetic.natural_context store_ctxt) 1)
      val other_replay = Operation.make_mapped store other_encode other_leaf
      val other_cert = Operation.certify_mapped_shift other_replay 1 source_id
        (Store.action_index store other_output)
      val parity_encode = @{term "\<lambda>x::nat. x mod 2"}
      fun parity_leaf x y = Utils.prove_exact store_ctxt "Fixture parity-map leaf"
        (HOLogic.mk_Trueprop (HOLogic.mk_eq
          (Envir.beta_norm (parity_encode $ nat x),nat y)))
        (fn _ => simp_tac (Comma_Entry_Arithmetic.natural_context store_ctxt) 1)
      val parity_replay = Operation.make_mapped store parity_encode parity_leaf
      val alias_cert = Operation.certify_mapped_shift parity_replay 1
        (Store.action_index store alias_source) (Store.action_index store alias_output)
      val _ = if Store.action_index store output <> Store.action_index store other_output
        then () else error "Distinct shift encoders reused one output"
      val bad_replay = Operation.make_mapped store encode (fn _ => fn _ => @{thm refl})
      val _ = rejects "wrong leaf encoding equation" (fn () =>
        Operation.certify_mapped_shift bad_replay 1 source_id output_id)
      val _ = rejects "wrong selected root" (fn () =>
        Terminal.indexed_shift ctxt store roots_term roots_def 0 source_id output_id cert)
      val _ = rejects "wrong mapped output" (fn () =>
        Terminal.indexed_shift ctxt store roots_term roots_def 7 source_id zero_id cert)
      val _ = rejects "wrong Continue root" (fn () => #terminal owner expression 0 zero_id)
      val _ = Comma_Proof_Dependency_Audit.require_native_clean ctxt
        "Indexed Continue mapped shift"
        [cert,transported,theorem,constant_cert,other_cert,alias_cert]
    in lthy4 end
end
