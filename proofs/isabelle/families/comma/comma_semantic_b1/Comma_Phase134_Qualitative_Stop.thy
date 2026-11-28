theory Comma_Phase134_Qualitative_Stop
  imports Comma_Qualitative_Stop Comma_Phase_134_Continue_Barrier
begin

text \<open>Composition of the checked single-phase barrier and the generic
well-founded physical Stop consumer. The only Continue relation is the one
owned by the imported generic theory. This does not establish the B32 cap.\<close>

lemma comma_program_continue_power_phase:
  assumes valid: "comma_semantic_phase_class_valid phase cid"
    and path: "comma_phase_class_continue_power
      comma_semantic_phase_program_class_step n (phase,cid) = Some (q,j)"
  shows "q = (phase+n) mod 924 \<and> comma_semantic_phase_class_valid q j"
  using valid path
proof (induction n arbitrary: phase cid)
  case 0
  then show ?case by (auto simp: comma_semantic_phase_class_valid_def)
next
  case (Suc n)
  obtain p c where step:
      "comma_semantic_phase_program_class_step phase cid =
        Comma_Phase_Class_Continue p c"
    and tail: "comma_phase_class_continue_power
      comma_semantic_phase_program_class_step n (p,c) = Some (q,j)"
    using Suc.prems(2)
    by (cases "comma_semantic_phase_program_class_step phase cid")
      (auto simp: comma_phase_class_continue_power_Suc
        comma_phase_class_continue_option_step_def split: option.splits prod.splits)
  have p: "p=(phase+1) mod 924"
    and child: "comma_semantic_phase_class_valid p c"
    using comma_semantic_phase_program_class_step_continue_closed[OF Suc.prems(1) step]
    by blast+
  have ih: "q=(p+n) mod 924" "comma_semantic_phase_class_valid q j"
    using Suc.IH[OF child tail] by blast+
  show ?case using ih p by (simp_all add: mod_add_left_eq add.assoc)
qed

lemma comma_program_single_phase_barrier:
  assumes barrier_phase: "b < 924"
    and barrier: "\<And>c. c < 46 \<Longrightarrow>
      comma_phase_class_continue_power comma_semantic_phase_program_class_step
        k (b,c) = None"
    and valid: "comma_semantic_phase_class_valid phase cid"
  shows "comma_phase_class_continue_power comma_semantic_phase_program_class_step
    ((if phase \<le> b then b-phase else 924+b-phase)+k) (phase,cid) = None"
proof -
  let ?n = "if phase \<le> b then b-phase else 924+b-phase"
  have phase_bound: "phase < 924"
    using valid by (simp add: comma_semantic_phase_class_valid_def)
  have sum: "phase + ?n = (if phase \<le> b then b else 924+b)"
    using barrier_phase phase_bound by presburger
  have reach: "(phase + ?n) mod 924 = b"
    using sum barrier_phase by (simp add: mod_add_left_eq)
  show ?thesis
  proof (cases "comma_phase_class_continue_power
      comma_semantic_phase_program_class_step ?n (phase,cid)")
    case None
    then show ?thesis by (simp add: comma_phase_class_continue_power_add)
  next
    case (Some state)
    obtain q j where state: "state=(q,j)" by (cases state) auto
    have result: "comma_phase_class_continue_power
        comma_semantic_phase_program_class_step ?n (phase,cid) = Some (q,j)"
      using Some state by simp
    have q: "q=b" and bound: "j<46"
      using comma_program_continue_power_phase[OF valid result] reach
      by (auto simp: comma_semantic_phase_class_valid_def)
    show ?thesis using Some state q barrier[OF bound]
      by (simp add: comma_phase_class_continue_power_add)
  qed
qed


text \<open>Qualitative well-foundedness uses the checked phase-134 barrier
and an infinite-chain contradiction. It does not establish a height-26 bound.\<close>

lemma comma_continue_phase_134_absent:
  assumes valid: "comma_semantic_phase_class_valid phase cid"
  shows "comma_phase_class_continue_power comma_semantic_phase_program_class_step
    930 (phase,cid) = None"
proof -
  let ?d = "if phase \<le> 134 then 134-phase else 924+134-phase"
  have phase: "phase < 924"
    using valid by (simp add: comma_semantic_phase_class_valid_def)
  have distance: "?d + 7 \<le> 930" using phase by presburger
  have barrier: "\<And>c. c<46 \<Longrightarrow> comma_phase_class_continue_power
      comma_semantic_phase_program_class_step 7 (134,c) = None"
    using comma_continue_phase_134_checked by blast
  have none: "comma_phase_class_continue_power comma_semantic_phase_program_class_step
      (?d+7) (phase,cid) = None"
    by (rule comma_program_single_phase_barrier[OF _ barrier valid]) simp
  have split: "(930::nat) = (?d+7) + (930-(?d+7))" using distance by simp
  have composed: "comma_phase_class_continue_power comma_semantic_phase_program_class_step
      ((?d+7) + (930-(?d+7))) (phase,cid) = None"
    using comma_phase_class_continue_power_add
      [of comma_semantic_phase_program_class_step "?d+7" "930-(?d+7)" "(phase,cid)"]
      none by (simp only: Option.bind.simps)
  show ?thesis using composed split by metis
qed

theorem comma_continue_phase_134_qualitative_wf:
  "wf comma_program_continue_relation_qualitative"
  unfolding wf_iff_ex_minimal
proof (intro allI impI)
  fix B :: "(nat \<times> nat) set"
  assume nonempty: "B \<noteq> {}"
  show "\<exists>z\<in>B. \<forall>y. (y,z) \<in> comma_program_continue_relation_qualitative \<longrightarrow> y \<notin> B"
  proof (rule ccontr)
    assume failure: "\<not> (\<exists>z\<in>B. \<forall>y. (y,z) \<in> comma_program_continue_relation_qualitative \<longrightarrow> y \<notin> B)"
    have predecessor: "\<And>s. s \<in> B \<Longrightarrow>
      \<exists>t\<in>B. (t,s) \<in> comma_program_continue_relation_qualitative"
      using failure by blast
    have path: "\<And>s. s \<in> B \<Longrightarrow> \<exists>t\<in>B.
      comma_phase_class_continue_power comma_semantic_phase_program_class_step n s = Some t" for n
    proof (induction n)
      case 0
      then show ?case by simp
    next
      case (Suc n)
      fix s assume s: "s \<in> B"
      obtain t where t: "t \<in> B" "(t,s) \<in> comma_program_continue_relation_qualitative"
        using predecessor[OF s] by blast
      obtain q j where t_pair: "t=(q,j)" by (cases t) auto
      obtain phase cid where s_pair: "s=(phase,cid)" by (cases s) auto
      have edge: "comma_semantic_phase_program_class_step phase cid =
          Comma_Phase_Class_Continue q j"
        using t(2) by (simp add: comma_program_continue_relation_qualitative_def
          t_pair s_pair)
      obtain u where u: "u \<in> B" "comma_phase_class_continue_power
          comma_semantic_phase_program_class_step n t = Some u"
        using Suc.IH[OF t(1)] by blast
      have "comma_phase_class_continue_power comma_semantic_phase_program_class_step
          (Suc n) s = Some u"
        using edge u(2) by (simp add: s_pair t_pair
          comma_phase_class_continue_power_Suc comma_phase_class_continue_option_step_def)
      then show "\<exists>u\<in>B. comma_phase_class_continue_power
        comma_semantic_phase_program_class_step (Suc n) s = Some u"
        using u(1) by blast
    qed
    obtain s where s: "s \<in> B" using nonempty by blast
    obtain t where edge: "(t,s) \<in> comma_program_continue_relation_qualitative"
      using predecessor[OF s] by blast
    obtain phase cid where s_pair: "s=(phase,cid)" by (cases s) auto
    have valid: "comma_semantic_phase_class_valid phase cid"
      using edge by (auto simp: comma_program_continue_relation_qualitative_def s_pair)
    obtain u where "comma_phase_class_continue_power comma_semantic_phase_program_class_step
      930 s = Some u" using path[OF s, of 930] by blast
    then show False using comma_continue_phase_134_absent[OF valid] s_pair by simp
  qed
qed


theorem comma_phase134_wf_physical_typed_stop:
  fixes phase offset :: nat
  assumes source: "comma_decade_admitted (Comma_Decade phase offset)"
  shows "\<exists>h terminal. comma_decade_exact_summary (Comma_Decade phase offset) h terminal"
  by (rule comma_qualitative_wf_source_typed_stop
      [OF comma_continue_phase_134_qualitative_wf source])

text \<open>The legacy B32 application is separately guarded: the existing
comma_semantic_b1_action_stop_from_exact_summary theorem requires height \<le> 26.
Neither the qualitative wf result nor the typed existential above supplies it.\<close>

ML \<open>
  val _ = Comma_Proof_Dependency_Audit.require_paths @{context}
    "Phase-134 qualitative typed Stop composition"
    ["comma_continue_qualitative_source_typed_stop", "comma_single_source_summary_if_not_survives_draft",
     "comma_frontier_m204_bellman_native", "comma_program_absent_power_draft",
     "comma_program_single_phase_continue_wf_draft"]
    @{thms comma_continue_phase_134_qualitative_wf comma_phase134_wf_physical_typed_stop};
\<close>

end
