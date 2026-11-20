theory Comma_Semantic_Future_Instance
  imports Comma_Semantic_B1_Instance.Comma_Semantic_Summary_Instance
    Comma_Semantic_Future.Comma_Future_M204_Class_Rank_Lift
    Comma_Semantic_Future.Comma_Future_M204_Class_Decoder
    Comma_Semantic_Future.Comma_Future_M204_Select_Step
    Comma_Semantic_Future.Comma_Future_M204_Select_Chain
    Comma_Semantic_Future.Comma_Future_M204_Periodic
    Comma_Semantic_Future.Comma_Future_M204_Direct_Source
begin

text \<open>The source-to-class morphism is checked at sixteen symbolic-phase
roots. The M204 trace weight and the ordered global class graph have separate
contracts. Source occurrences select authenticated roots; they are not proof
identities. No per-phase provider-cell certificate or predecessor graph is
constructed here.\<close>

ML_file "semantic_future_m204_candidate_data.ML"
ML_file "semantic_future_m204_graph_data.ML"
ML_file "semantic_future_m204_class_rank.ML"
ML_file "semantic_future_zip_producer.ML"
ML_file "semantic_future_zip_certificates.ML"
ML_file "semantic_future_m204_join_proposal.ML"
ML_file "semantic_future_m204_graph_proposal.ML"
ML_file "semantic_future_m204_join_replay.ML"
ML_file "semantic_future_m204_graph_replay.ML"
ML_file "semantic_future_m204_graph_pointwise.ML"
ML_file "semantic_future_m204_weight_evals.ML"
ML_file "semantic_future_m204_shifted_weights.ML"
ML_file "semantic_future_m204_shifted_classes.ML"
ML_file "semantic_future_m204_select_steps.ML"
ML_file "semantic_future_m204_select_folds.ML"
ML_file "semantic_future_m204_source_transport.ML"
ML_file "semantic_future_m204_child_transport.ML"
ML_file "semantic_future_m204_source_pointwise.ML"
ML_file "semantic_future_m204_child_pointwise.ML"
ML_file "semantic_future_m204_graph_family_pointwise.ML"
ML_file "semantic_future_m204_source20.ML"
ML_file "semantic_future_m204_final_publication.ML"
ML_file "semantic_future_m204_compact_class_transport.ML"
ML_file "semantic_future_m204_compact_rank_publication.ML"
ML_file "semantic_future_m204_direct_source_bindings.ML"
ML_file "semantic_future_m204_direct_physical_issuer.ML"
ML_file "semantic_future_m204_component_loader.ML"
ML_file "semantic_future_m204_entry_open.ML"

local_setup \<open>fn lthy =>
  let
    val (prepared,lthy1) = Comma_Future_M204_Component_Loader.prepare
      @{term comma_frontier_m204_weight} lthy
    val final = #final prepared
    val compact = #compact prepared
    val classes = #class_publication prepared
    val rank_rhs = Envir.beta_norm
      (@{term "\<lambda>rows::comma_future_m204_row list.
        \<lambda>class_of::comma_boundary_state \<Rightarrow> nat.
        comma_future_m204_rank rows \<circ> class_of"} $
        #rows classes $ #class_map compact)
    val ((rank,rank_definition),lthy2) = Comma_Future_M204_Entry_Open.define
      "comma_semantic_concrete_future_rank" rank_rhs lthy1
    val ctxt = Local_Theory.target_of lthy2
    fun rename theorem = Simplifier.rewrite_rule (put_simpset HOL_basic_ss ctxt)
      [Thm.symmetric rank_definition] theorem
    fun point kind theorem =
      let
        val (_,rhs) = HOLogic.dest_eq (HOLogic.dest_Trueprop (Thm.prop_of theorem))
        val q = HOLogic.mk_prod (kind,HOLogic.mk_prod (@{term "2::nat"},@{term "10::nat"}))
        val same_goal = HOLogic.mk_Trueprop
          (HOLogic.mk_eq (#class_map final $ q,#class_map compact $ q))
        val same = Goal.prove ctxt [] [] same_goal (fn {context,...} =>
          resolve_tac context [#equality compact] 1 THEN
          simp_tac (Comma_Entry_Arithmetic.natural_context context |>
            Simplifier.add_simps @{thms comma_boundary_valid_def prod.case}) 1)
        val compact_to_work = @{thm sym} OF [same]
        val target = HOLogic.mk_Trueprop (HOLogic.mk_eq (rank $ q,rhs))
      in Goal.prove ctxt [] [] target (fn _ =>
        simp_tac (put_simpset HOL_basic_ss ctxt
          |> Simplifier.add_simps
            [rank_definition,@{thm comp_apply},compact_to_work,theorem]) 1) end
    fun note name theorem theory = snd (Local_Theory.note
      ((Binding.name name,[]),[theorem]) theory)
    val lthy3 = lthy2
      |> note "comma_semantic_concrete_future_rank_check" (rename (#rank compact))
      |> note "comma_semantic_concrete_source20_unranked" (point @{term Comma_N} (#north final))
      |> note "comma_semantic_concrete_source20_z_ranked_value" (point @{term Comma_Z} (#south final))
  in Comma_Future_M204_Entry_Open.publish (#weight prepared)
    (#compact_store prepared) (#compact_roots prepared) (#definition compact)
    (#procedure (#selector classes)) (#count_theorem classes)
    rank rank_definition lthy3 end\<close>

lemma comma_semantic_concrete_source20_z_ranked_exact:
  "comma_semantic_concrete_future_rank (Comma_Z,2,10) =
    Some (the (comma_semantic_concrete_future_rank (Comma_Z,2,10)))"
  by (simp only: comma_semantic_concrete_source20_z_ranked_value option.sel)

lemma comma_semantic_concrete_source20_z_ranked:
  "\<exists>rank. comma_semantic_concrete_future_rank (Comma_Z,2,10) = Some rank"
  using comma_semantic_concrete_source20_z_ranked_exact by blast

ML \<open>
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "M204 source morphism, ordered class rank and decimal-root gate"
    @{thms comma_frontier_m204_bellman_native comma_future_m204_rank_native
      comma_future_m204_compact_rank_native
      comma_future_m204_compact_morphism_native
      comma_semantic_concrete_future_rank_check comma_semantic_concrete_source20_unranked
      comma_semantic_concrete_source20_z_ranked_exact comma_semantic_p5_entry_future_open_checked}
\<close>

end
