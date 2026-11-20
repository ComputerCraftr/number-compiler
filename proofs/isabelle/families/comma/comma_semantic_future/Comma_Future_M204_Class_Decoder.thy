theory Comma_Future_M204_Class_Decoder
  imports Comma_Future_M204_Class_Bridge
begin

text \<open>The sixteen roots are source-bound applications of the compact
class map.  Their numerical indices are not themselves authority.\<close>

definition comma_future_m204_family_slot :: "comma_boundary_state \<Rightarrow> nat" where
  "comma_future_m204_family_slot q =
    (case q of (kind,a,r) \<Rightarrow>
      (case kind of Comma_N \<Rightarrow> a-2 | Comma_Z \<Rightarrow> 8+(a-2)))"

definition comma_future_m204_mdd_class ::
    "nat comma_crt_mdd_node list \<Rightarrow> nat list \<Rightarrow> comma_boundary_state \<Rightarrow> nat" where
  "comma_future_m204_mdd_class nodes roots q =
    the (comma_crt_mdd_eval_phase [3,4,7,11] nodes (snd (snd q))
      (roots ! comma_future_m204_family_slot q))"

lemma comma_future_m204_family_slot_bound:
  assumes "comma_boundary_valid q"
  shows "comma_future_m204_family_slot q < 16"
proof -
  obtain kind a phase where q: "q = (kind,a,phase)" by (cases q) auto
  have bounds: "2 \<le> a" "a \<le> 9"
    using assms q by (auto simp: comma_boundary_valid_def)
  have small: "a-2 < 8" using bounds by arith
  show ?thesis
  proof (cases kind)
    case Comma_N
    have "comma_future_m204_family_slot q = a-2"
      using q Comma_N by (simp add: comma_future_m204_family_slot_def)
    with small show ?thesis by arith
  next
    case Comma_Z
    have "comma_future_m204_family_slot q = 8+(a-2)"
      using q Comma_Z by (simp add: comma_future_m204_family_slot_def)
    with small show ?thesis by arith
  qed
qed

lemma comma_future_m204_mdd_class_exact:
  assumes valid: "comma_boundary_valid q"
    and wf: "comma_crt_mdd_table_wellformed [3,4,7,11] nodes"
    and count: "length roots = 16"
    and bounds: "list_all (\<lambda>root. root < length nodes) roots"
  shows "comma_crt_mdd_eval_phase [3,4,7,11] nodes (snd (snd q))
      (roots ! comma_future_m204_family_slot q) =
    Some (comma_future_m204_mdd_class nodes roots q)"
proof -
  have slot: "comma_future_m204_family_slot q < length roots"
    using comma_future_m204_family_slot_bound[OF valid] count by simp
  have root: "roots ! comma_future_m204_family_slot q < length nodes"
    using bounds nth_mem[OF slot] by (auto simp: list_all_iff)
  obtain id where eval_fact: "comma_crt_mdd_eval_phase [3,4,7,11] nodes (snd (snd q))
      (roots ! comma_future_m204_family_slot q) = Some id"
    using comma_crt_mdd_eval_phase_total[OF wf root] by blast
  show ?thesis using eval_fact by (simp add: comma_future_m204_mdd_class_def)
qed

lemma comma_future_m204_mdd_class_periodic:
  assumes wf: "comma_crt_mdd_table_wellformed [3,4,7,11] nodes"
  shows "comma_future_m204_mdd_class nodes roots (kind,a,phase mod 924) =
    comma_future_m204_mdd_class nodes roots (kind,a,phase)"
proof -
  have divides: "[3,4,7,11] ! axis dvd (924::nat)"
    if "axis < length ([3,4,7,11]::nat list)" for axis
    using nth_mem[OF that] by auto
  show ?thesis by (cases kind)
    (simp_all only: comma_future_m204_mdd_class_def comma_future_m204_family_slot_def
      prod.case comma_boundary_kind.case fst_conv snd_conv
      comma_crt_mdd_eval_phase_periodic[OF wf divides])
qed

lemma comma_future_m204_mdd_class_transport:
  assumes valid: "comma_boundary_valid q"
    and roots: "\<And>i phase. i < 16 \<Longrightarrow>
      comma_crt_mdd_eval_phase [3,4,7,11] source phase (source_roots ! i) =
      comma_crt_mdd_eval_phase [3,4,7,11] target phase (target_roots ! i)"
  shows "comma_future_m204_mdd_class source source_roots q =
    comma_future_m204_mdd_class target target_roots q"
  unfolding comma_future_m204_mdd_class_def
  using roots[OF comma_future_m204_family_slot_bound[OF valid], of "snd (snd q)"]
  by simp

ML \<open>
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Future M204 source-class decoder"
    @{thms comma_future_m204_family_slot_bound comma_future_m204_mdd_class_exact
      comma_future_m204_mdd_class_periodic comma_future_m204_mdd_class_transport};
\<close>

end
