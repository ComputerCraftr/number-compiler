(* Direct projected Bellman producer over the candidate's single Store.
   All constructor, operation, source and equality claims are kernel checked. *)
structure Comma_Direct_Bellman_Issuer =
struct
  structure Arena = Comma_CRT_MDD_Arena
  structure Store = Comma_CRT_MDD_Certificate_Store
  structure Expression = Comma_Direct_Action_Proposal
  structure MDD = Comma_Direct_MDD_Proposal
  structure Evaluation = Comma_Direct_MDD_Evaluation
  structure Terminal_Proposal = Comma_Direct_Bellman_Terminal_Proposal
  structure Terminal_Proofs = Comma_Direct_Bellman_Terminal_Proofs
  structure Bind = Comma_CRT_MDD_Bind_Replay
  structure Runtime = Comma_Frontier24_Parametric_Runtime
  structure Utils = Comma_CRT_MDD_Proof_Utils
  structure Program = Comma_Direct_Program_Bindings (
    val fixed_entry_port_conversion_plan = Comma_Direct_Entry_Arithmetic.fixed_entry_port_conversion_plan
    val core_parameter_conversion_plan = Comma_Direct_Entry_Arithmetic.core_parameter_conversion_plan)
  type expressions = {classes:(int * term * term) list, sources:(term * term * term) list,
    expressions:term list, program_bindings:(term * term) list, action_bindings:(term * term) list,
    body:term -> term, definition:term -> thm, expression_hits:int, program_requests:int}
  type projected = {arena:Arena.arena,classes:MDD.application list,sources:MDD.application list,
    guards:MDD.guard list,applications:int,hits:int}
  type terminals = {terminal:Arena.arena -> term -> int -> Arena.action_root option,
    fallback:Arena.action_root,continuations:unit -> Terminal_Proposal.continued list,
    statistics:unit -> string}
  type prepared = {expressions:expressions,projected:projected,terminals:terminals,
    labels:int list}
  type publication = {arena:Arena.arena,store:Store.store,roots:Arena.action_root list,
    roots_term:term,roots_definition:thm,D:term,D_definition:thm,prepared:prepared}
  val natT = @{typ nat}
  fun nat n = HOLogic.mk_number natT n
  fun tp term = HOLogic.mk_Trueprop term
  fun prepare {arena,roots} lthy =
    let
      val _ = Comma_Proof_Profile.report "Direct Bellman expression preparation start"
      val (expressions,lthy') = Expression.build_with_sources Runtime.computation [] lthy
      val _ = Comma_Proof_Profile.report "Direct Bellman expression preparation complete"
      val terminals = Terminal_Proposal.make arena roots
      val classes = #classes expressions
      val _ = Comma_Proof_Profile.report "Direct Bellman projected MDD start"
      val proposed = MDD.build_with Runtime.computation (#body expressions) arena
        (#terminal terminals) (#fallback terminals)
        (map (fn (_,_,expression) => expression) classes) []
      val _ = Comma_Proof_Profile.report "Direct Bellman projected MDD complete"
      val outputs = map MDD.root (#classes proposed)
      (* Both sides use the same reduced arena.  Equal authenticated roots
         already denote the very same evaluation term; rebuilding an equality
         decision diagram would prove reflexivity one node at a time. *)
      val _ = List.app (fn (expected,actual) =>
        if Arena.action_index arena expected = Arena.action_index arena actual
        then () else error "Direct projected Bellman root differs from D")
        (roots ~~ outputs)
      val labels = sort int_ord (fold (fn root => union (op =) (Arena.action_support arena root)) roots [])
      val _ = if List.all (fn n => 0<=n andalso n<=242) labels then ()
        else error "Direct Bellman candidate exceeds its admitted range"
      val _ = Comma_Proof_Profile.report
        ("Direct projected proposal expressions=" ^ Int.toString (length (#expressions expressions)) ^
         " applications=" ^ Int.toString (#applications proposed) ^
         " nodes=" ^ Int.toString (Arena.node_count arena) ^ " " ^ #statistics terminals ())
    in ({expressions=expressions,projected=proposed,terminals=terminals,
      labels=labels},lthy') end

  fun certify ({arena,store,roots,roots_term,roots_definition,D,D_definition,prepared}:publication) lthy =
    let
      val ctxt = Local_Theory.target_of lthy
      fun checkpoint stage = Comma_Proof_Profile.report ("Direct Bellman certify stage=" ^ stage)
      val _ = checkpoint "initializers-start"
      val expressions = #expressions prepared
      val proposal = #projected prepared
      val terminals = #terminals prepared
      val terminal_proofs = Terminal_Proofs.make ctxt store arena roots roots_term
        roots_definition D D_definition (#definition expressions) (#continuations terminals ())
      val project = fn phase => @{term comma_direct_bellman_mask_projection} $ D $ phase
      val evaluator = Evaluation.make_with ctxt store arena (#guards proposal)
        (#body expressions) (#definition expressions) project
        (#terminal terminal_proofs) (#fallback terminal_proofs)
      val programs = Program.make ctxt Runtime.computation (#program_bindings expressions)
        (#action_bindings expressions) (#body expressions) (#definition expressions)
      val phase = Free ("direct_bellman_phase",natT)
      val phase_ct = Thm.cterm_of ctxt phase
      val wf = Store.wellformed store
      val cover = Bind.make store
      val labels = #labels prepared
      val label_term = HOLogic.mk_list natT (map nat labels)
      val label_prop = @{term "\<lambda>xs::nat list. list_all (\<lambda>x. x\<le>242) xs"} $ label_term
      val _ = checkpoint "payload-labels-start"
      val label_fact = Utils.prove_exact ctxt "Direct Bellman payload labels" (tp (Envir.beta_norm label_prop))
        (fn _ => simp_tac (Comma_Entry_Arithmetic.natural_context ctxt
          |> Simplifier.add_simps @{thms list_all_Cons_iff list_all_Nil_iff}) 1)
      val _ = checkpoint "payload-labels-complete"
      val small = Comma_Entry_Arithmetic.natural_context ctxt
        |> Simplifier.add_simp roots_definition
        |> Simplifier.add_simps @{thms list.simps list.size nth_Cons_0 nth_Cons_Suc nth_Cons_numeral nth_Cons'}
      fun row (index,((cid,program,expression),application)) =
        let
          fun row_checkpoint stage = if cid=0 then checkpoint ("class-0-" ^ stage) else ()
          val _ = row_checkpoint "start"
          val _ = if index=cid then () else error "Direct Bellman class ordering changed"
          val left = Store.action_index store (List.nth (roots,cid))
          val right = Store.action_index store (MDD.root application)
          val _ = if left=right then ()
            else error "Checked Bellman projection does not use the candidate root"
          val _ = row_checkpoint "bounds-start"
          val cid_bound = Utils.prove_exact ctxt "Direct Bellman class bound"
            (tp (HOLogic.mk_binrel @{const_name less} (nat cid,
              Const (@{const_name size},@{typ "nat list => nat"}) $ roots_term)))
            (fn _ => simp_tac small 1)
          val selected_root = Const (@{const_name nth},@{typ "nat list => nat => nat"}) $ roots_term $ nat cid
          val selected_equation = Simplifier.rewrite small (Thm.cterm_of ctxt selected_root)
          val _ = Utils.exact_prop ctxt "Direct Bellman selected root"
            (Logic.mk_equals (selected_root,nat left)) selected_equation
          val root_bound = Utils.prove_exact ctxt "Direct Bellman root bound"
            (tp (HOLogic.mk_binrel @{const_name less}
              (Const (@{const_name nth},@{typ "nat list => nat => nat"}) $ roots_term $ nat cid,
               Const (@{const_name size},@{typ "nat comma_crt_mdd_node list => nat"}) $ Store.table store)))
            (fn context => Method.insert_tac context [Store.bound store left] 1 THEN auto_tac small)
          val _ = row_checkpoint "bounds-complete"
          val d_rule = Drule.infer_instantiate ctxt
            [( ("phase",0),phase_ct),( ("cid",0),Thm.cterm_of ctxt (nat cid)),
             ( ("roots",0),Thm.cterm_of ctxt roots_term)] @{thm comma_frontier_m204_mdd_value_exact}
          val d_eval = d_rule OF [wf,cid_bound,root_bound]
          val d_eval = Simplifier.rewrite_rule (put_simpset HOL_basic_ss ctxt)
            [selected_equation,Thm.symmetric D_definition] d_eval
          val _ = row_checkpoint "d-evaluation-complete"
          val _ = row_checkpoint "program-action-start"
          val program_action = #program_action programs program
            |> Thm.forall_elim phase_ct |> Thm.forall_elim (Thm.cterm_of ctxt (nat 0))
          val _ = row_checkpoint "program-action-complete"
          val _ = if cid = 0 then Comma_Proof_Profile.report
            ("Direct Bellman first program " ^ #statistics programs ()) else ()
          val _ = row_checkpoint "projected-evaluation-start"
          val projected_eval = Thm.forall_elim phase_ct (#certify evaluator application)
          val _ = row_checkpoint "projected-evaluation-complete"
          val projected_eval = Simplifier.rewrite_rule (put_simpset HOL_basic_ss ctxt)
            [program_action RS @{thm eq_reflection}] projected_eval
          val value = D $ phase $ nat cid
          val fold = @{term comma_semantic_phase_program_fold} $
            @{term comma_phase_program_full_action_output} $ phase $ program $ nat 0
          val rhs = @{term comma_direct_bellman_mask_projection} $ D $ phase $ fold
          val projected_goal = tp (HOLogic.mk_eq (value,rhs))
          val point = Goal.prove ctxt [] [] projected_goal (fn {context,...} =>
            Method.insert_tac context [d_eval,projected_eval] 1 THEN
            auto_tac (Comma_Entry_Arithmetic.natural_context context
              |> Simplifier.add_simps @{thms option.simps}))
          val projected = Thm.forall_intr phase_ct point
          val _ = row_checkpoint "payload-cover-start"
          val payload = Bind.certify_cover cover left labels
          val _ = row_checkpoint "payload-cover-complete"
          val bounded_point = @{thm comma_frontier_m204_checked_payload_bound} OF
            [wf,Store.bound store left,payload,label_fact,d_eval]
          val bounded = Thm.forall_intr phase_ct bounded_point
          val _ = if (cid+1) mod 4=0 orelse cid=45 then
            Comma_Proof_Profile.report ("Direct Bellman class rows=" ^ Int.toString (cid+1) ^
              " " ^ #statistics evaluator () ^ " " ^ #statistics programs () ^ " " ^
              #statistics terminal_proofs ()) else ()
        in {cid=cid,program=program,projected=projected,bounded=bounded} end
      val bindings = map_index row (#classes expressions ~~ #classes proposal)
      val bellman = Comma_Direct_Bellman_Publication.publish ctxt D bindings
      val _ = Comma_Proof_Dependency_Audit.require_native_clean ctxt "Direct projected Bellman" [bellman]
      val (_,lthy') = Local_Theory.note
        ((Binding.name "comma_m204_direct_concrete_bellman_native",[]),[bellman]) lthy
    in lthy' end
end
