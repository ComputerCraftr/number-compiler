theory Comma_Continue_Frontier24_Source_Bridge
  imports Comma_Semantic_B1.Comma_CRT_MDD_Certificates
    Comma_Semantic_B1.Comma_CRT_MDD_Transport
    Comma_Semantic_B1.Comma_CRT_MDD_Frontier_DAG
    Comma_Semantic_B1.Comma_Continue_Core_Fold
    Comma_Semantic_B1.Comma_Continue_Frontier_Certificate
    Comma_Semantic_B1.Comma_Continue_Frontier24_Core_Guard
    Comma_Semantic_B1.Comma_Parametric_Continue_Closure_Soundness
    Comma_Semantic_B1.Comma_Program_Continue_Guard_Exact
begin

text \<open>
The parametric producer constructs a candidate bundle only. The publisher
checks its source-bound guards and actions against the frozen MDD store; the
class-root theorem then transports one closed universal action vector to the
generic 24-step preimage consumer. No occurrence-indexed source compiler or
per-class semantic proof loop participates in this path.
\<close>

ML_file "semantic_frontier24_mdd_preimage.ML"
ML_file "semantic_frontier24_parametric_compiler.ML"
ML_file "semantic_frontier24_parametric_runtime.ML"
ML_file "semantic_frontier24_mdd_import_certificates.ML"
ML_file "semantic_frontier24_selected_table_plan.ML"
ML_file "semantic_frontier24_bundle_publisher.ML"
ML_file "semantic_frontier24_initial_proofs.ML"
ML_file "semantic_frontier24_dag_proofs.ML"

ML \<open>
structure Comma_Frontier24_Source_Bridge =
struct
  structure Arena = Comma_CRT_MDD_Arena
  structure Store = Comma_CRT_MDD_Certificate_Store
  structure Proposal = Comma_Frontier24_MDD_Proposal
  structure Runtime = Comma_Frontier24_Parametric_Runtime
  structure Publisher = Comma_Frontier24_Bundle_Publisher
  structure Operation = Comma_CRT_MDD_Operation_Replay
  structure Bind = Comma_CRT_MDD_Bind_Replay
  structure Initial = Comma_Frontier24_Initial_Proofs
  structure DAG = Comma_Frontier24_DAG_Proofs
  structure Utils = Comma_CRT_MDD_Proof_Utils

  val natT = @{typ nat}
  val bundleT = @{typ comma_frontier24_parametric_bundle}
  val rootsT = HOLogic.listT natT

  fun nat n = HOLogic.mk_number natT n
  fun tp p = HOLogic.mk_Trueprop p
  fun mk_less x y = HOLogic.mk_binrel @{const_name less} (x,y)

  fun checked_projection ctxt label projection expected =
    let
      val conv = Simplifier.rewrite
        (put_simpset HOL_basic_ss ctxt
          |> Simplifier.add_simps
            @{thms comma_frontier24_parametric_bundle.select_convs})
        (Thm.cterm_of ctxt projection)
      val actual = Thm.term_of (Thm.rhs_of conv)
      val _ = if actual aconv expected then ()
        else error (label ^ " differs from the frozen compiler result")
      val _ = Utils.exact_prop ctxt label (Logic.mk_equals (projection,expected)) conv
    in conv end

  fun universal_action_certificate ctxt store bundle bundle_theorem roots =
    let
      val root_indices = map (Store.action_index store) roots
      val _ = if length root_indices=46 then () else
        error "Parametric compiler returned an incomplete 46-class root vector"
      val root_vector = HOLogic.mk_list natT (map nat root_indices)
      val radices_projection = Const (@{const_name cf24_radices},
        bundleT --> rootsT) $ bundle
      val nodes_projection = Const (@{const_name cf24_nodes},
        bundleT --> HOLogic.listT @{typ "nat comma_crt_mdd_node"}) $ bundle
      val roots_projection = Const (@{const_name cf24_class_roots},
        bundleT --> rootsT) $ bundle
      val radices_equation = checked_projection ctxt "Parametric bundle radices"
        radices_projection (Store.radices store)
      val nodes_equation = checked_projection ctxt "Parametric bundle frozen node table"
        nodes_projection (Store.table store)
      val roots_equation = checked_projection ctxt "Parametric bundle class roots"
        roots_projection root_vector
      val phase = Free ("frontier_action_phase",natT)
      val cid = Free ("frontier_action_cid",natT)
      val phase_bound_prop = tp (mk_less phase (nat 924))
      val cid_bound_prop = tp (mk_less cid (nat 46))
      val phase_ct = Thm.cterm_of ctxt phase
      val cid_ct = Thm.cterm_of ctxt cid
      val phase_bound_ct = Thm.cterm_of ctxt phase_bound_prop
      val cid_bound_ct = Thm.cterm_of ctxt cid_bound_prop
      val phase_fact = Thm.assume phase_bound_ct
      val cid_fact = Thm.assume cid_bound_ct
      val class_rule = Drule.infer_instantiate ctxt
        [(("bundle",0),Thm.cterm_of ctxt bundle),
         (("phase",0),phase_ct),(("cid",0),cid_ct)]
        @{thm comma_frontier24_class_roots_exact}
      val point = class_rule OF [bundle_theorem,phase_fact,cid_fact]
      val point = Simplifier.rewrite_rule (put_simpset HOL_basic_ss ctxt)
        [radices_equation,nodes_equation,roots_equation] point
      val point = Thm.implies_intr cid_bound_ct point
      val all_cid = Thm.forall_intr cid_ct point
      val point = Thm.implies_intr phase_bound_ct all_cid
      val universal = Thm.forall_intr phase_ct point
    in DAG.action_certificate_from_exact ctxt store roots universal end

  fun run lthy =
    let
      val ctxt = Local_Theory.target_of lthy
      fun timed label operation =
        let
          val started = Time.now ()
          val _ = Comma_Proof_Profile.report ("Frontier24 stage=" ^ label ^ " start")
          val result = Exn.capture operation ()
          val elapsed = Time.toString (Time.- (Time.now (),started))
          val status = (case result of Exn.Res _ => "complete" | Exn.Exn _ => "failed")
          val message = "Frontier24 stage=" ^ label ^ " " ^ status ^ " elapsed=" ^ elapsed
          val _ = Comma_Proof_Profile.report message
          val _ = writeln message
        in Exn.release result end
      val compiled = timed "parametric source compilation"
        (fn () => Runtime.compile_data ctxt)
      val arena = Runtime.Compiler.arena compiled
      val action_roots = Runtime.Compiler.class_roots compiled
      val initial_roots = Proposal.make_initial_roots arena
      val history = timed ("24-round preimage construction; proposal_nodes=" ^
        Int.toString (Arena.node_count arena))
        (fn () => Proposal.build_24_rounds arena action_roots initial_roots)
      val _ = writeln ("Frontier24 proposal nodes after preimage: " ^
        Int.toString (Arena.node_count arena))
      val (store,lthy1) = timed "final Store freeze"
        (fn () => Store.make "comma_frontier24_parametric_nodes" arena lthy)
      val shift_replay = Operation.make store
      val bind_replay = Bind.make store
      val (named_actions,lthy2) = timed "named selector action table"
        (fn () => Runtime.define_action_table lthy1 compiled)
      val publisher_ctxt = Local_Theory.target_of lthy2
      val candidate = Runtime.candidate publisher_ctxt (Store.table store) compiled
        named_actions
      val published = timed "source-bound bundle certification"
        (fn () => Publisher.certify publisher_ctxt store arena
          shift_replay bind_replay candidate)
      val bundle_theorem = #theorem published
      val bundle = #bundle candidate
      val certified_prop = HOLogic.mk_Trueprop
        (@{term comma_frontier24_bundle_semantic_certified} $ bundle)
      val bundle_theorem = Utils.exact_prop publisher_ctxt
        "Frontier24 bundle certificate" certified_prop bundle_theorem
      val action_certificate = universal_action_certificate publisher_ctxt store bundle
        bundle_theorem action_roots
      val initial_ids = map (Store.boolean_index store) initial_roots
      val initial_certificates = timed "initial row certificates"
        (fn () => Initial.certify_initial publisher_ctxt store arena initial_ids)
      val frontier = timed "checked preimage vectors and generic induction"
        (fn () => DAG.make publisher_ctxt store arena history action_certificate
          initial_certificates shift_replay bind_replay)
      val expected_image = @{prop "comma_continue24_direct_image_certificate"}
      val image_certificate = #image_certificate frontier
      val _ = if Thm.prop_of image_certificate aconv expected_image andalso
          Thm.nprems_of image_certificate=0 andalso null (Thm.hyps_of image_certificate)
        then () else error "Frontier24 publisher returned an invalid image certificate"
      val (_,lthy3) = Local_Theory.note
        ((Binding.name "comma_semantic_phase_continue24_image_certificate_native",[]),
          [image_certificate]) lthy2
      val _ = writeln ("Frontier24 parametric source publisher: " ^
        Runtime.statistics candidate ^ "; " ^ Store.statistics store ^ "; " ^
        Operation.statistics shift_replay ^ "; " ^ Bind.statistics bind_replay ^ "; " ^
        #statistics published ^ "; " ^ #statistics frontier)
    in lthy3 end
end
\<close>

local_setup \<open>Comma_Frontier24_Source_Bridge.run\<close>

ML \<open>
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Frontier24 parametric Continue source closure refinement"
    @{thms comma_semantic_phase_continue24_image_certificate_native}
\<close>

end
