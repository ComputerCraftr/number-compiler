(* Issue only the 16 exact physical source roots needed by the Future join.
   This is downstream of B1 and does not issue or reprove the Bellman weight. *)
structure Comma_Future_M204_Direct_Physical_Issuer =
struct
  structure Arena = Comma_CRT_MDD_Arena
  structure Store = Comma_CRT_MDD_Certificate_Store
  structure Runtime = Comma_Frontier24_Parametric_Runtime
  structure Expression = Comma_Direct_Action_Proposal
  structure MDD = Comma_Direct_MDD_Proposal
  structure Evaluation = Comma_Direct_MDD_Evaluation
  structure Physical = Comma_Future_M204_Direct_Source_Bindings
  structure Program = Comma_Direct_Program_Bindings (
    val fixed_entry_port_conversion_plan = Comma_Direct_Entry_Arithmetic.fixed_entry_port_conversion_plan
    val core_parameter_conversion_plan = Comma_Direct_Entry_Arithmetic.core_parameter_conversion_plan)
  fun run lthy =
    let
      val (expressions,lthy1) = Expression.build_selected "comma_future_source_expression"
        Runtime.computation [] (Runtime.physical_initial_sources ()) lthy
      val sources = #sources expressions
      val proposal = MDD.build Runtime.computation (#body expressions) []
        (map (fn (_,_,expression) => expression) sources)
      val arena = #arena proposal
      val _ = Comma_Proof_Profile.report
        ("Future physical source MDD candidate nodes=" ^ Int.toString (Arena.node_count arena))
      val (store,lthy2) = Store.make "comma_future_direct_source_nodes" arena lthy1
      val ctxt = Store.context store
      val evaluator = Evaluation.make store arena (#guards proposal)
        (#body expressions) (#definition expressions)
      val programs = Program.make ctxt Runtime.computation (#program_bindings expressions)
        (#action_bindings expressions) (#body expressions) (#definition expressions)
      fun binding ((source,program,expression),application) =
        {source=source,program=program,expression=expression,
         root=HOLogic.mk_number @{typ nat} (Store.action_index store (MDD.root application)),
         evaluation= #certify evaluator application,program_action= #program_action programs program}
      val bindings = map binding (sources ~~ #sources proposal)
      val facts = Physical.certify ctxt (Store.radices store) (Store.table store) bindings
      val roots = map MDD.root (#sources proposal)
      val _ = Comma_Proof_Profile.report
        ("Future physical source " ^ #statistics evaluator () ^ " " ^ #statistics programs ())
    in ({store=store,arena=arena,roots=roots,exact=facts},lthy2) end
end
