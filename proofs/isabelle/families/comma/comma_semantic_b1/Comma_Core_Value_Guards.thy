theory Comma_Core_Value_Guards
  imports Comma_CRT_Columns Comma_Semantic_Phase_Action_Program
begin

definition comma_core_guard_clock ::
    "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> comma_cyclotomic_clock" where
  "comma_core_guard_clock r4 r3 r7 r11 =
    \<lparr>comma_clock_mod4=r4, comma_clock_mod3=r3,
      comma_clock_mod7=r7, comma_clock_mod11=r11\<rparr>"

definition comma_core_value_guard_leaf ::
    "comma_phase_core_id \<Rightarrow> nat \<Rightarrow> comma_cyclotomic_clock \<Rightarrow> comma_crt_column" where
  "comma_core_value_guard_leaf core wanted C =
    Comma_CRT_Bool
      (comma_cyclotomic_clock_core_value C (comma_phase_core_modulus core) = wanted)"

text \<open>One active clock axis. The node level chooses the existing C4/C3/C7/C11
coordinate; its branch values come from the shared core evaluator.\<close>
definition comma_core_value_guard_one_axis ::
    "nat \<Rightarrow> (nat \<Rightarrow> comma_cyclotomic_clock) \<Rightarrow> comma_phase_core_id \<Rightarrow> nat \<Rightarrow>
      comma_crt_column" where
  "comma_core_value_guard_one_axis level clock_at core wanted =
    Comma_CRT_Node level
      (map (\<lambda>digit. comma_core_value_guard_leaf core wanted (clock_at digit))
        [0..<comma_crt_period level])"

text \<open>The C4 character is the first axis for every two-character core. A
single shared constructor takes the second CRT level and the corresponding
clock-coordinate constructor, so no per-core branch table is stored.\<close>
definition comma_core_value_guard_two_axes ::
    "nat \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> comma_cyclotomic_clock) \<Rightarrow>
      comma_phase_core_id \<Rightarrow> nat \<Rightarrow> comma_crt_column" where
  "comma_core_value_guard_two_axes second_level clock_at core wanted =
    Comma_CRT_Node 0
      (map (\<lambda>r4. Comma_CRT_Node second_level
        (map (\<lambda>second.
          comma_core_value_guard_leaf core wanted (clock_at r4 second))
          [0..<comma_crt_period second_level]))
        [0..<comma_crt_period 0])"

lemma comma_core_value_guard_one_axis_admitted:
  assumes level: "level<4"
  shows "comma_crt_admitted 0
    (comma_core_value_guard_one_axis level clock_at core wanted)"
  using level
  by (simp add: comma_core_value_guard_one_axis_def
      comma_core_value_guard_leaf_def comma_crt_admitted.simps
      comma_crt_period_def list_all_iff)

lemma comma_core_value_guard_two_axes_admitted:
  assumes second_level: "0<second_level" "second_level<4"
  shows "comma_crt_admitted 0
    (comma_core_value_guard_two_axes second_level clock_at core wanted)"
  using second_level
  by (simp add: comma_core_value_guard_two_axes_def
      comma_core_value_guard_leaf_def comma_crt_admitted.simps
      comma_crt_period_def list_all_iff)

lemma comma_core_value_guard_one_axis_eval:
  assumes level: "level<4"
  shows "comma_crt_eval phase
      (comma_core_value_guard_one_axis level clock_at core wanted) =
    comma_crt_eval phase
      (comma_core_value_guard_leaf core wanted
        (clock_at (phase mod comma_crt_period level)))"
  using level comma_crt_period_positive[OF level]
  by (simp add: comma_core_value_guard_one_axis_def
      comma_crt_eval_node_selected nth_map)

lemma comma_core_value_guard_two_axes_eval:
  assumes second_level: "0<second_level" "second_level<4"
  shows "comma_crt_eval phase
      (comma_core_value_guard_two_axes second_level clock_at core wanted) =
    comma_crt_eval phase
      (comma_core_value_guard_leaf core wanted
        (clock_at (phase mod comma_crt_period 0)
          (phase mod comma_crt_period second_level)))"
  using second_level comma_crt_period_positive[OF second_level(2)]
    comma_crt_period_positive[of 0]
  by (simp add: comma_core_value_guard_two_axes_def
      comma_crt_eval_node_selected nth_map)

fun comma_core_value_guard ::
    "comma_phase_core_id \<Rightarrow> nat \<Rightarrow> comma_crt_column" where
  "comma_core_value_guard Comma_Core_1 wanted = Comma_CRT_Bool (wanted=0)"
| "comma_core_value_guard Comma_Core_3 wanted = Comma_CRT_Bool (wanted=1)"
| "comma_core_value_guard Comma_Core_7 wanted =
    comma_core_value_guard_two_axes 1
      (\<lambda>r4 r3. comma_core_guard_clock r4 r3 0 0) Comma_Core_7 wanted"
| "comma_core_value_guard Comma_Core_11 wanted =
    comma_core_value_guard_one_axis 0
      (\<lambda>r4. comma_core_guard_clock r4 0 0 0) Comma_Core_11 wanted"
| "comma_core_value_guard Comma_Core_13 wanted =
    comma_core_value_guard_two_axes 1
      (\<lambda>r4 r3. comma_core_guard_clock r4 r3 0 0) Comma_Core_13 wanted"
| "comma_core_value_guard Comma_Core_21 wanted =
    comma_core_value_guard_two_axes 1
      (\<lambda>r4 r3. comma_core_guard_clock r4 r3 0 0) Comma_Core_21 wanted"
| "comma_core_value_guard Comma_Core_23 wanted =
    comma_core_value_guard_two_axes 3
      (\<lambda>r4 r11. comma_core_guard_clock r4 0 0 r11) Comma_Core_23 wanted"
| "comma_core_value_guard Comma_Core_27 wanted =
    comma_core_value_guard_one_axis 1
      (\<lambda>r3. comma_core_guard_clock 0 r3 0 0) Comma_Core_27 wanted"
| "comma_core_value_guard Comma_Core_29 wanted =
    comma_core_value_guard_two_axes 2
      (\<lambda>r4 r7. comma_core_guard_clock r4 0 r7 0) Comma_Core_29 wanted"

lemma comma_core_value_guard_admitted:
  "comma_crt_admitted 0 (comma_core_value_guard core wanted)"
  by (cases core)
    (simp_all add: comma_core_value_guard_one_axis_admitted
      comma_core_value_guard_two_axes_admitted)

lemma comma_core_value_guard_eval:
  "comma_crt_eval phase (comma_core_value_guard core wanted) =
    (comma_cyclotomic_clock_core_value
      (comma_cyclotomic_clock_of phase) (comma_phase_core_modulus core) = wanted)"
proof -
  have one: "comma_recursive_core_residue 1 t=0" for t
    by (simp add: comma_recursive_core_residue_def)
  have three: "comma_recursive_core_residue 3 t=1" for t
    by (simp add: comma_recursive_core_residue_def)
  show ?thesis
  proof (cases core)
    case Comma_Core_1
    then show ?thesis
      by (simp only: comma_core_value_guard.simps comma_phase_core_modulus.simps
          comma_cyclotomic_clock_core_value_def one comma_crt_eval.simps eq_commute HOL.simp_thms)
  next
    case Comma_Core_3
    then show ?thesis
      by (simp only: comma_core_value_guard.simps comma_phase_core_modulus.simps
          comma_cyclotomic_clock_core_value_def three comma_crt_eval.simps eq_commute HOL.simp_thms)
  qed (simp_all add: comma_core_value_guard_one_axis_eval
      comma_core_value_guard_two_axes_eval comma_core_value_guard_leaf_def
      comma_core_guard_clock_def comma_cyclotomic_clock_core_value_def
      comma_cyclotomic_clock_of_def comma_cyclotomic_phase_def
      comma_core_period_def comma_phase_core_modulus.simps comma_crt_period_def)
qed

lemma comma_core_value_guard_unique:
  assumes "comma_crt_eval phase (comma_core_value_guard core left)"
    and "comma_crt_eval phase (comma_core_value_guard core right)"
  shows "left=right"
  using assms by (auto simp only: comma_core_value_guard_eval)

lemma comma_core_value_guard_cover:
  "\<exists>value<comma_phase_core_modulus core.
    comma_crt_eval phase (comma_core_value_guard core value)"
  using comma_phase_core_clock_value_bound[of
    "comma_cyclotomic_clock_of phase" core]
  by (auto simp only: comma_core_value_guard_eval)

text \<open>The selected branches use only C4 for period 2, C3 for period 3,
C4×C3 for period 6, C4×C11 for period 22, and C4×C7 for period 28. Period-1
cores are constants. Inactive clock characters are set to zero and are not
read by the matching `comma_cyclotomic_phase` formula. Consequently the
signed CRT subtractions for 6/22/28 stay owned by that existing projection.
Each column is keyed only by `(core,wanted)`; no program, environment, phase
row, 924-bit mask, or output-action table enters its definition.\<close>

ML \<open>
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Shared cyclotomic core value guards"
    @{thms comma_core_value_guard_admitted comma_core_value_guard_eval
      comma_core_value_guard_unique comma_core_value_guard_cover};
\<close>

end
