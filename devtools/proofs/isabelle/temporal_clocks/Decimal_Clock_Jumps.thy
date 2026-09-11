theory Decimal_Clock_Jumps
  imports Temporal_Clock_Jumps
begin

text \<open>Decimal primary transport: each no-growth event multiplies by 2,
each growth event by y. Birth offsets remain demanded inputs. The spatial
z clock must not be confused with the state-dependent temporal growth clock.\<close>

definition decimal_kernel :: "'a::comm_ring_1 \<Rightarrow> bool \<Rightarrow> 'a" where
  "decimal_kernel y growth = (if growth then y else 2)"

lemma decimal_kernel_product:
  "prod_list (map (decimal_kernel y) gs) =
    (2::'a::comm_ring_1) ^ count_list gs False * y ^ count_list gs True"
  by (induction gs) (auto simp: decimal_kernel_def algebra_simps)

lemma bool_counts_length:
  "count_list gs False + count_list gs True = length gs"
  by (induction gs) auto

lemma nilpotent_after_five:
  fixes a :: "'a::comm_ring_1"
  assumes "a^5 = 0" "5 \<le> n"
  shows "a^n = 0"
proof -
  obtain k where "n = 5+k" using assms(2) by (metis le_iff_add)
  then show ?thesis by (simp add: power_add assms(1))
qed

theorem decimal_nine_event_source_death:
  fixes y :: "'a::comm_ring_1"
  assumes two: "(2::'a)^5 = 0" and nilpotent: "y^5 = 0"
      and horizon: "9 \<le> length gs"
  shows "prod_list (map (decimal_kernel y) gs) = 0"
proof -
  have counts: "5 \<le> count_list gs False \<or> 5 \<le> count_list gs True"
    using bool_counts_length[of gs] horizon by arith
  show ?thesis using counts
    by (auto simp: decimal_kernel_product
      dest: nilpotent_after_five[OF two] nilpotent_after_five[OF nilpotent])
qed

lemma clock_period_reduction:
  fixes z :: "'a::monoid_mult"
  assumes period: "z^128 = 1"
  shows "z^width = z^(width mod 128)"
proof -
  have split: "width = 128 * (width div 128) + width mod 128" by arith
  have "z^width = z^(128 * (width div 128) + width mod 128)"
    using split by simp
  also have "... = (z^128)^(width div 128) * z^(width mod 128)"
    by (simp only: power_add power_mult)
  finally show ?thesis by (simp add: period)
qed

text \<open>For a fixed admitted forcing action, binary powering is a true
jump of that affine recurrence. This does not assert that reverse/add has the
same forcing action at every generation.\<close>

theorem decimal_fixed_action_skip:
  fixes y birth :: "'a::comm_ring_1"
  shows "apply_effect (dyadic_effect k (decimal_kernel y growth, birth)) source =
    ((\<lambda>x. decimal_kernel y growth * x + birth) ^^ (2^k)) source"
proof -
  have action: "apply_effect (decimal_kernel y growth, birth) =
      (\<lambda>x. decimal_kernel y growth * x + birth)"
    by (rule ext) (simp add: apply_effect_def)
  show ?thesis using dyadic_effect_jump[of k "(decimal_kernel y growth, birth)" source]
    by (simp only: action)
qed

text \<open>Fixed points and rebasing are identities of the affine action.  The
root is an action coordinate; it is not an additional occurrence payload.\<close>

lemma decimal_no_growth_fixed_point:
  "decimal_kernel y False * (-birth) + birth = (-birth)"
  by (simp add: decimal_kernel_def algebra_simps)

lemma decimal_growth_fixed_point:
  assumes "y = 1 + z" and "z * q = 1"
  shows "decimal_kernel y True * (-q * birth) + birth = (-q * birth)"
  using assms by (simp add: decimal_kernel_def algebra_simps)

lemma decimal_affine_fixed_point:
  "apply_effect (A, B) r = r \<longleftrightarrow> A * r + B = r"
  by (simp add: apply_effect_def)

lemma decimal_temporal_rebase:
  fixes A B r x r' :: "'a::comm_ring_1"
  assumes "A * r + B = r"
  shows "apply_effect (A, B) x - r' =
    A * (x - r) + (r - r')"
  using assms by (simp add: apply_effect_def algebra_simps)

lemma decimal_phase_rebase_transport:
  fixes zi A W delta :: "'a::comm_ring_1"
  shows "zi^(L+g) * (A*W+delta) =
    (zi^g*A) * (zi^L*W) + zi^(L+g)*delta"
  by (simp add: power_add algebra_simps)

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms decimal_kernel_product decimal_nine_event_source_death
      clock_period_reduction decimal_fixed_action_skip
      decimal_no_growth_fixed_point decimal_growth_fixed_point
      decimal_affine_fixed_point decimal_temporal_rebase
      decimal_phase_rebase_transport})
    then () else error "Decimal clock proof depends on an oracle";
\<close>
end
