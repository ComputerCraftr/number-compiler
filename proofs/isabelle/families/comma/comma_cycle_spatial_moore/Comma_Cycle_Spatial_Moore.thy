theory Comma_Cycle_Spatial_Moore
  imports Comma_Recursive_Pair_Language.Comma_Temporal_Action
    "HOL-Number_Theory.Modular_Inverse"
begin

ML_file "../comma_entry_arithmetic/Proof_Dependency_Audit.ML"

text \<open>
The zero-inclusive port quotient is the orbit position under subtraction by
the sector, together with a distinct off-orbit value.  The orbit position is
computed by cancelling gcd(f,10) and multiplying by the modular inverse of
the reduced sector.  It is a finite Moore observation; the exact displacement
and elapsed weight remain occurrence data.
\<close>

type_synonym comma_q19_id = "nat \<times> nat option"

definition comma_q19_id_of :: "nat \<Rightarrow> nat \<Rightarrow> comma_q19_id" where
  "comma_q19_id_of f d =
    (let g = gcd f 10;
     L = 10 div g
     in if d mod g = 0 then
          (L, Some (((d div g) *
            nat (modular_inverse (int L) (int (f div g))) mod L)))
        else (L, None))"

definition comma_q19_observation :: "comma_q19_id \<Rightarrow> bool \<times> nat" where
  "comma_q19_observation q = (case q of
    (L, None) \<Rightarrow> (False, L)
  | (L, Some j) \<Rightarrow> (j = 1, L))"

definition comma_q19_transition :: "comma_q19_id \<Rightarrow> comma_q19_id" where
  "comma_q19_transition q = (case q of
    (L, None) \<Rightarrow> (L, None)
  | (L, Some j) \<Rightarrow>
      (L, Some (if j \<le> 1 then L - 1 else j - 1)))"

definition comma_q19_classes :: "comma_q19_id set" where
  "comma_q19_classes = set
    [(10,Some 0),(10,Some 1),(10,Some 2),(10,Some 3),(10,Some 4),
     (10,Some 5),(10,Some 6),(10,Some 7),(10,Some 8),(10,Some 9),
     (5,Some 0),(5,Some 1),(5,Some 2),(5,Some 3),(5,Some 4),(5,None),
     (2,Some 0),(2,Some 1),(2,None)]"

definition comma_q19_port_image :: "comma_q19_id list" where
  "comma_q19_port_image = concat
    (map (\<lambda>f. map (comma_q19_id_of f) [0..<10]) [1..<10])"

definition comma_q19_local_law :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "comma_q19_local_law f d \<longleftrightarrow>
    comma_q19_id_of f d \<in> comma_q19_classes \<and>
    comma_q19_observation (comma_q19_id_of f d) =
      (comma_port_previous f d = 0, comma_cycle_length f) \<and>
    comma_q19_transition (comma_q19_id_of f d) =
      comma_q19_id_of f (comma_port_next f d)"

lemma comma_q19_classes_card:
  "card comma_q19_classes = 19"
  by (simp add: comma_q19_classes_def)

text \<open>The finite domain check validates the inverse-based formula against
the existing exact port output and transition.  It checks all 90 legal
zero-inclusive ports; the formula above, rather than these evaluations, is
the quotient definition.\<close>

lemma comma_q19_laws_checked:
  "list_all (\<lambda>f. list_all (comma_q19_local_law f) [0..<10]) [1..<10]"
  unfolding comma_q19_local_law_def comma_q19_id_of_def
    comma_q19_observation_def comma_q19_transition_def
    comma_q19_classes_def comma_port_previous_def comma_port_next_def
    comma_cycle_length_def
  by code_simp

lemma comma_q19_local_law:
  assumes "1 \<le> f" "f \<le> 9" "d < 10"
  shows "comma_q19_local_law f d"
proof -
  have f_member: "f \<in> set [1..<10]" using assms by simp
  have d_member: "d \<in> set [0..<10]" using assms by simp
  show ?thesis
    using comma_q19_laws_checked f_member d_member
    by (auto simp: list_all_iff)
qed

theorem comma_q19_projection_exact:
  assumes "1 \<le> f" "f \<le> 9" "d < 10"
  shows "comma_q19_observation (comma_q19_id_of f d) =
    (comma_port_previous f d = 0, comma_cycle_length f)"
  using comma_q19_local_law[OF assms]
  by (auto simp: comma_q19_local_law_def)

theorem comma_q19_step_closed:
  assumes "1 \<le> f" "f \<le> 9" "d < 10"
  shows "comma_q19_transition (comma_q19_id_of f d) =
    comma_q19_id_of f (comma_port_next f d)"
  using comma_q19_local_law[OF assms]
  by (auto simp: comma_q19_local_law_def)

theorem comma_q19_zero_observable:
  assumes "1 \<le> f" "f \<le> 9" "d < 10"
  shows "fst (comma_q19_observation (comma_q19_id_of f d)) =
    (comma_port_previous f d = 0)"
  using comma_q19_projection_exact[OF assms] by simp

theorem comma_q19_period_observable:
  assumes "1 \<le> f" "f \<le> 9" "d < 10"
  shows "snd (comma_q19_observation (comma_q19_id_of f d)) =
    comma_cycle_length f"
  using comma_q19_projection_exact[OF assms] by simp

lemma comma_q19_port_image_exact:
  "set comma_q19_port_image = comma_q19_classes"
  unfolding comma_q19_port_image_def comma_q19_classes_def
    comma_q19_id_of_def
  by code_simp

corollary comma_q19_exactly_nineteen_reachable_classes:
  "card (set comma_q19_port_image) = 19"
  using comma_q19_port_image_exact comma_q19_classes_card by simp

lemma comma_q19_iterate_suc:
  "comma_port_temporal_iterate f (Suc n) d =
    comma_port_next f (comma_port_temporal_iterate f n d)"
  by (simp add: comma_port_temporal_iterate_def comma_port_action_power_def
      comma_port_action_def)

lemma comma_q19_iterate_admitted:
  assumes sector: "1 \<le> f" "f \<le> 9" and digit: "d \<le> 9"
  shows "comma_port_temporal_iterate f n d \<le> 9"
proof (induction n)
  case 0
  show ?case using digit by (simp add: comma_port_temporal_iterate_def
      comma_port_action_power_def)
next
  case (Suc n)
  have port_bounds: "1 \<le> comma_port_next f (comma_port_temporal_iterate f n d)"
      "comma_port_next f (comma_port_temporal_iterate f n d) \<le> 9"
    using comma_port_next_admitted[OF sector Suc.IH] by auto
  show ?case by (simp only: comma_q19_iterate_suc; use port_bounds in auto)
qed

theorem comma_q19_temporal_power_refines:
  assumes sector: "1 \<le> f" "f \<le> 9" and digit: "d \<le> 9"
  shows "comma_q19_id_of f (comma_port_temporal_iterate f n d) =
    (comma_q19_transition ^^ n) (comma_q19_id_of f d)"
proof (induction n)
  case 0
  then show ?case by (simp add: comma_port_temporal_iterate_def
      comma_port_action_power_def)
next
  case (Suc n)
  have current: "comma_port_temporal_iterate f n d \<le> 9"
    by (rule comma_q19_iterate_admitted[OF sector digit])
  have current_lt: "comma_port_temporal_iterate f n d < 10"
    using current by arith
  have step: "comma_q19_transition
      (comma_q19_id_of f (comma_port_temporal_iterate f n d)) =
      comma_q19_id_of f (comma_port_next f (comma_port_temporal_iterate f n d))"
    by (rule comma_q19_step_closed[OF sector current_lt])
  show ?case
    by (simp only: comma_q19_iterate_suc step[symmetric] Suc.IH
        funpow.simps comp_apply)
qed

theorem comma_q19_occurrence_weight_separate:
  "comma_q19_id_of 1 0 = comma_q19_id_of 3 0 \<and>
    comma_finite_period 1 0 \<noteq> comma_finite_period 3 0"
  unfolding comma_q19_id_of_def comma_finite_period_def comma_cycle_length_def
  by code_simp

ML \<open>
  val checked = @{thms comma_q19_projection_exact comma_q19_step_closed
    comma_q19_zero_observable comma_q19_period_observable
    comma_q19_exactly_nineteen_reachable_classes
    comma_q19_temporal_power_refines comma_q19_occurrence_weight_separate};
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Q19 arithmetic classifier" checked;
  val _ = Comma_Proof_Dependency_Audit.require_expected_paths @{context}
    "Q19 powered source projection" ["comma_q19_step_closed"]
    @{thms comma_q19_temporal_power_refines};
\<close>
end
