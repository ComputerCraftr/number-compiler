theory Comma_Continue_Image_Bridge
  imports Comma_Symbolic_Class_Step Comma_Core_Value_Guards
begin

lemma comma_entry_guard_selects_action:
  assumes phase: "phase<924"
    and guard: "comma_crt_eval phase (comma_core_value_guard core value)"
    and digit: "d=residue mod 10"
    and core: "comma_phase_core_modulus core =
      comma_core_modulus (comma_finite_period_fast f d)"
  shows "comma_phase_program_operator_nf
      (Comma_Entry_Core_Program f d residue core) phase =
    (let key=comma_decisive_entry_clock_key_from_core_residue f residue
         (comma_phase_core_modulus core) value
     in case comma_entry_port_refined_locator f (fst key) (snd key) of
       Some (active,residual,h) \<Rightarrow>
         comma_semantic_b1_near_control_port_action f 0 h
     | None \<Rightarrow> Comma_Continuation_Invalid)"
  using comma_phase_program_operator_nf_entry_core_value[OF digit core, of phase]
    guard phase
  by (simp add: comma_core_value_guard_eval)

definition comma_phase_class_continue_option_step ::
    "(nat \<Rightarrow> 'c \<Rightarrow> 'c comma_phase_class_action) \<Rightarrow>
     (nat \<times> 'c) option \<Rightarrow> (nat \<times> 'c) option"
where
  "comma_phase_class_continue_option_step step state =
    Option.bind state (\<lambda>(phase,cid).
      case step phase cid of
        Comma_Phase_Class_Continue next_phase next_cid \<Rightarrow>
          Some (next_phase,next_cid)
      | _ \<Rightarrow> None)"

definition comma_phase_class_continue_power ::
    "(nat \<Rightarrow> 'c \<Rightarrow> 'c comma_phase_class_action) \<Rightarrow>
     nat \<Rightarrow> (nat \<times> 'c) \<Rightarrow> (nat \<times> 'c) option"
where
  "comma_phase_class_continue_power step n state =
    (comma_phase_class_continue_option_step step ^^ n) (Some state)"

lemma comma_phase_class_continue_option_step_none [simp]:
  "comma_phase_class_continue_option_step step None = None"
  by (simp add: comma_phase_class_continue_option_step_def)

lemma comma_phase_class_continue_power_0 [simp]:
  "comma_phase_class_continue_power step 0 state = Some state"
  by (simp add: comma_phase_class_continue_power_def)

lemma comma_phase_class_continue_power_option:
  "(comma_phase_class_continue_option_step step ^^ n) initial =
    Option.bind initial (comma_phase_class_continue_power step n)"
proof (cases initial)
  case None
  have "(comma_phase_class_continue_option_step step ^^ n) None = None"
    by (induction n) simp_all
  then show ?thesis using None by simp
next
  case (Some state)
  then show ?thesis by (simp add: comma_phase_class_continue_power_def)
qed

lemma comma_phase_class_continue_power_Suc:
  "comma_phase_class_continue_power step (Suc n) state =
    Option.bind (comma_phase_class_continue_option_step step (Some state))
      (comma_phase_class_continue_power step n)"
proof -
  have "comma_phase_class_continue_power step (Suc n) state =
      (comma_phase_class_continue_option_step step ^^ n)
        (comma_phase_class_continue_option_step step (Some state))"
    by (simp only: comma_phase_class_continue_power_def
        funpow_Suc_right comp_apply)
  also have "... =
      Option.bind (comma_phase_class_continue_option_step step (Some state))
        (comma_phase_class_continue_power step n)"
    by (rule comma_phase_class_continue_power_option)
  finally show ?thesis .
qed

lemma comma_phase_class_continue_power_add:
  "comma_phase_class_continue_power step (m+n) state =
    Option.bind (comma_phase_class_continue_power step m state)
      (comma_phase_class_continue_power step n)"
proof -
  have "comma_phase_class_continue_power step (m+n) state =
      (comma_phase_class_continue_option_step step ^^ n)
        (comma_phase_class_continue_power step m state)"
    by (simp only: comma_phase_class_continue_power_def
        add.commute[of m n] funpow_add comp_apply)
  also have "... = Option.bind
      (comma_phase_class_continue_power step m state)
      (comma_phase_class_continue_power step n)"
    by (rule comma_phase_class_continue_power_option)
  finally show ?thesis .
qed

lemma comma_phase_class_survives_iff_continue_power:
  "comma_phase_class_survives step n phase cid =
    (comma_phase_class_continue_power step n (phase,cid) \<noteq> None)"
proof (induction n arbitrary: phase cid)
  case 0
  then show ?case by (simp add: comma_phase_class_survives.simps)
next
  case (Suc n)
  then show ?case
    by (cases "step phase cid")
      (auto simp: comma_phase_class_survives.simps
        comma_phase_class_continue_power_Suc
        comma_phase_class_continue_option_step_def)
qed

definition comma_continue24_endpoint_list :: "(nat \<times> nat) list" where
  "comma_continue24_endpoint_list =
    [(299,33),(66,10),(298,12),(67,32),(68,1)]"

definition comma_continue24_endpoints :: "(nat \<times> nat) set" where
  "comma_continue24_endpoints = set comma_continue24_endpoint_list"

lemma comma_continue24_endpoint_list_set:
  "set comma_continue24_endpoint_list = comma_continue24_endpoints"
  by (simp add: comma_continue24_endpoints_def)

lemma comma_continue24_endpoint_phase_bound:
  assumes "(phase,target)\<in>comma_continue24_endpoints"
  shows "phase<924"
  using assms
  by (auto simp: comma_continue24_endpoints_def
      comma_continue24_endpoint_list_def)

text \<open>
These five exact steps are bounded terminal checks. They do not establish
that every 24-step image lies in this set; that universal producer obligation
remains an explicit premise of the downstream theorem.
\<close>

ML_file "semantic_program_arithmetic.ML"

lemma comma_continue24_endpoint_steps:
  "comma_semantic_phase_program_class_step 299 33 = Comma_Phase_Class_Fork 9 0"
  "comma_semantic_phase_program_class_step 298 12 = Comma_Phase_Class_Continue 299 33"
  "comma_semantic_phase_program_class_step 68 1 = Comma_Phase_Class_Fork 5 0"
  "comma_semantic_phase_program_class_step 67 32 = Comma_Phase_Class_Continue 68 1"
  "comma_semantic_phase_program_class_step 66 10 = Comma_Phase_Class_Continue 67 32"
  by (tactic \<open>
    let
      val ctxt = @{context}
      val _ = Comma_Proof_Profile.report "Continue tails stage=setup-start"
      val arithmetic = Comma_Entry_Arithmetic.signed_context ctxt
      val expose = arithmetic |> Simplifier.add_simps @{thms
        comma_semantic_phase_program_class_step_def
        comma_semantic_phase_program_for_class_def
        comma_offset_representatives_def nth_Cons'
        comma_entry_control_program_def comma_finite_period_fast_def
        comma_core_lift_parameters comma_phase_core_of_modulus_def option.case}
      val endpoint = Comma_Semantic_Program_Arithmetic.make ctxt
      val step_context = #context endpoint
      val _ = Comma_Proof_Profile.report "Continue tails stage=arithmetic-ready"
      fun lhs cv = Conv.arg_conv (Conv.fun_conv (Conv.arg_conv cv))
      val unfold_round = lhs (Conv.arg_conv (Conv.arg_conv
        (Conv.rewr_conv (mk_meta_eq @{thm comma_semantic_phase_program_round_unfold}))))
      fun selected_step ct =
        let
          val _ = Comma_Proof_Profile.report
            ("Continue tails stage=step-start term=" ^ Syntax.string_of_term ctxt (Thm.term_of ct))
          val equation = Simplifier.rewrite step_context ct
          val _ = Comma_Proof_Profile.report
            ("Continue tails stage=step-done result=" ^
              Syntax.string_of_term ctxt (Thm.term_of (Thm.rhs_of equation)))
        in equation end
      val evaluate_step = lhs
        (Conv.arg_conv (Conv.arg_conv (Conv.arg_conv selected_step)))
      val finish = ctxt |> Simplifier.add_proc (#simproc endpoint)
      val _ = Comma_Proof_Profile.report "Continue tails stage=finish-ready"
      val layer = ALLGOALS
        (CONVERSION (Conv.try_conv (unfold_round then_conv evaluate_step))
          THEN' simp_tac finish)
      fun traced label tactic state =
        (Comma_Proof_Profile.report ("Continue tails stage=" ^ label ^ "-start");
         Seq.map (fn result =>
           (Comma_Proof_Profile.report ("Continue tails stage=" ^ label ^ "-done");
            result)) (tactic state))
    in traced "expose" (ALLGOALS (simp_tac expose)) THEN
      REPEAT_DETERM (CHANGED_PROP (traced "layer" layer)) end
  \<close>)

lemma comma_continue24_endpoint_tails:
  assumes "terminal\<in>comma_continue24_endpoints"
  shows "comma_phase_class_continue_power
    comma_semantic_phase_program_class_step 3 terminal=None"
  using assms
  by (auto simp only: comma_continue24_endpoint_list_def
      comma_continue24_endpoints_def set_simps;
      simp only: numeral_3_eq_3 comma_phase_class_continue_power_Suc
        comma_phase_class_continue_power_0
        comma_phase_class_continue_option_step_def Option.bind.simps
        prod.case comma_phase_class_action.case comma_continue24_endpoint_steps)

lemma comma_no_27_from_continue24_image:
  assumes image24:
      "\<And>phase cid terminal. phase<924 \<Longrightarrow> cid<46 \<Longrightarrow>
        comma_phase_class_continue_power
          comma_semantic_phase_program_class_step 24 (phase,cid) =
          Some terminal \<Longrightarrow> terminal\<in>comma_continue24_endpoints"
    and valid: "comma_semantic_phase_class_valid phase cid"
  shows "\<not> comma_phase_class_survives
    comma_semantic_phase_program_class_step 27 phase cid"
proof -
  have phase: "phase<924" and class_bound: "cid<46"
    using valid by (auto simp: comma_semantic_phase_class_valid_def)
  have split:
      "comma_phase_class_continue_power
          comma_semantic_phase_program_class_step 27 (phase,cid) =
       Option.bind
         (comma_phase_class_continue_power
           comma_semantic_phase_program_class_step 24 (phase,cid))
         (comma_phase_class_continue_power
           comma_semantic_phase_program_class_step 3)"
    using comma_phase_class_continue_power_add[where m=24 and n=3,
      of comma_semantic_phase_program_class_step "(phase,cid)"] by simp
  have none:
      "comma_phase_class_continue_power
          comma_semantic_phase_program_class_step 27 (phase,cid) = None"
    using image24[OF phase class_bound] comma_continue24_endpoint_tails split
    by (cases "comma_phase_class_continue_power
        comma_semantic_phase_program_class_step 24 (phase,cid)") auto
  show ?thesis
    using comma_phase_class_survives_iff_continue_power[of
      comma_semantic_phase_program_class_step 27 phase cid] none by simp
qed

theorem comma_B32_if_continue24_image:
  assumes image24:
      "\<And>phase cid terminal. phase<924 \<Longrightarrow> cid<46 \<Longrightarrow>
        comma_phase_class_continue_power
          comma_semantic_phase_program_class_step 24 (phase,cid) =
          Some terminal \<Longrightarrow> terminal\<in>comma_continue24_endpoints"
    and admitted: "comma_decade_admitted source"
  shows "\<exists>h tau. h\<le>26 \<and>
    comma_decade_block_power 5 source=Comma_Block_Stop h tau \<and>
    comma_residual_block 32 (h,tau)=Comma_Residual_Stop h tau \<and>
    comma_decade_exact_summary source h tau"
  by (rule comma_semantic_phase_program_class_step_B32_if_no_27
      [OF comma_no_27_from_continue24_image[OF image24] admitted])

ML \<open>
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Continue composition and conditional five-endpoint image bridge"
    @{thms comma_entry_guard_selects_action
      comma_phase_class_continue_power_add
      comma_phase_class_survives_iff_continue_power
      comma_continue24_endpoint_steps comma_continue24_endpoint_tails
      comma_B32_if_continue24_image};
\<close>

end
