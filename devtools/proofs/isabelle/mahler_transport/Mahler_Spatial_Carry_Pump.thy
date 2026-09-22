theory Mahler_Spatial_Carry_Pump
  imports Mahler_Source_Cylinder_Transport
begin

text \<open>
  Spatial pumping of one repeated radix block. A fixed outgoing carry is
  checked on the complete block, including its emitted numeral. This does
  not identify source occurrences or power successive Mahler time steps.
\<close>

fun spatial_repeat_value :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "spatial_repeat_value b u 0 = 0"
| "spatial_repeat_value b u (Suc n) = u + b * spatial_repeat_value b u n"

definition spatial_block_carry :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "spatial_block_carry b multiplier u c = (multiplier*u+c) div b"

definition spatial_block_output :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "spatial_block_output b multiplier u c = (multiplier*u+c) mod b"

lemma spatial_block_conservation:
  "multiplier*u+c = spatial_block_output b multiplier u c +
    b * spatial_block_carry b multiplier u c"
  by (simp add: spatial_block_output_def spatial_block_carry_def
      mult.commute mod_div_mult_eq)

text \<open>
  The radix block is a spatial view of the centered production arithmetic.
  Carry moves from the low block u into the high part v. Division by two
  transports the emitted low block and its boundary; no new source recurrence
  is defined. At radix 64 choose b=32. A finite F5 observer may be applied to
  this exact output, but equality of that observer is not successor authority.
\<close>

theorem mahler_spatial_low_block_transport:
  "mahler_D_step (u + 2*b*v) =
    spatial_block_output (2*b) 3 u 1 div 2 +
    b * (3*v + spatial_block_carry (2*b) 3 u 1)"
proof -
  have numerator: "3*(u + 2*b*v)+1 =
      spatial_block_output (2*b) 3 u 1 +
      2 * (b * (3*v + spatial_block_carry (2*b) 3 u 1))"
    using spatial_block_conservation[of 3 u 1 "2*b"]
    by (simp add: algebra_simps)
  show ?thesis
    unfolding mahler_D_step_def
    by (simp only: numerator)
qed

corollary antihydra_centered_spatial_low_block_transport:
  "antihydra_h_step (u + 2*b*v + 1) =
    spatial_block_output (2*b) 3 u 1 div 2 +
    b * (3*v + spatial_block_carry (2*b) 3 u 1) + 1"
  by (simp only: centered_return_commutes mahler_spatial_low_block_transport)

lemma spatial_repeat_value_bound:
  assumes radix: "0 < b" and digit: "u < b"
  shows "spatial_repeat_value b u n < b^n"
proof (induction n)
  case 0 then show ?case by simp
next
  case (Suc n)
  have "u + b * spatial_repeat_value b u n < b * Suc (spatial_repeat_value b u n)"
    using digit by (simp add: mult_Suc add.commute)
  also have "\<dots> \<le> b * b^n"
    using Suc.IH by (intro mult_left_mono; arith)
  finally show ?case by (simp add: power_Suc)
qed

theorem spatial_fixed_carry_repeat_conservation:
  assumes fixed: "multiplier*u+c = e+b*c"
  shows "multiplier * spatial_repeat_value b u n + c =
    spatial_repeat_value b e n + b^n*c"
proof (induction n)
  case 0 then show ?case by simp
next
  case (Suc n)
  have "multiplier * (u + b * spatial_repeat_value b u n) + c =
      (multiplier*u+c) + b * (multiplier * spatial_repeat_value b u n)"
    by (simp add: algebra_simps)
  also have "\<dots> = e + b * (multiplier * spatial_repeat_value b u n + c)"
    using fixed by (simp add: algebra_simps)
  also have "\<dots> = e + b * (spatial_repeat_value b e n + b^n*c)"
    by (simp only: Suc.IH)
  finally show ?case by (simp add: power_Suc algebra_simps)
qed

theorem spatial_fixed_carry_repeat_complete:
  assumes radix: "0 < b"
    and stable: "spatial_block_carry b multiplier u c = c"
  defines "e \<equiv> spatial_block_output b multiplier u c"
  shows "(multiplier * spatial_repeat_value b u n + c) mod b^n =
      spatial_repeat_value b e n"
    and "(multiplier * spatial_repeat_value b u n + c) div b^n = c"
proof -
  have eq: "multiplier*u+c = e+b*c"
    using spatial_block_conservation[of multiplier u c b] stable
    by (simp add: e_def)
  have all: "multiplier * spatial_repeat_value b u n + c =
      spatial_repeat_value b e n + b^n*c"
    by (rule spatial_fixed_carry_repeat_conservation[OF eq])
  have small: "e < b"
    using radix by (simp add: e_def spatial_block_output_def)
  have bound: "spatial_repeat_value b e n < b^n"
    by (rule spatial_repeat_value_bound[OF radix small])
  show "(multiplier * spatial_repeat_value b u n + c) mod b^n =
      spatial_repeat_value b e n"
    using bound by (simp add: all)
  show "(multiplier * spatial_repeat_value b u n + c) div b^n = c"
    using bound radix by (simp add: all)
qed

lemma spatial_block_carry_monotone:
  assumes "c \<le> d"
  shows "spatial_block_carry b multiplier u c \<le>
    spatial_block_carry b multiplier u d"
  unfolding spatial_block_carry_def
  by (rule div_le_mono) (use assms in arith)

text \<open>
  Spatial sharing of a safe-block consumer after interval translation.
  The source occurrence and its prefix-failure tree are retained separately.
  Equal normalized safe kernels do not imply equal first failure outside the
  admitted interval, or authorize successor substitution.
\<close>

theorem translated_safe_interval:
  fixes chart_left chart_right t :: real
  shows "strict_interval chart_left chart_right t \<longleftrightarrow>
    strict_interval 0 (chart_right-chart_left) (t-chart_left)"
  by (simp add: strict_interval_def)

theorem translated_safe_output:
  fixes chart_left t coefficient intercept :: real
  shows "coefficient*t+intercept =
    coefficient*(t-chart_left)+(coefficient*chart_left+intercept)"
  by (simp add: algebra_simps)

lemma strict_interval_intersection_nonempty:
  fixes lo hi event_lo event_hi :: real
  assumes "lo < hi" "event_lo < event_hi"
  shows "(\<exists>x. strict_interval lo hi x \<and>
      strict_interval event_lo event_hi x) \<longleftrightarrow>
    lo < event_hi \<and> event_lo < hi"
  using assms
  by (auto simp: strict_interval_def max_def intro!: exI[of _ "max lo event_lo"])

theorem event_exponent_interval_admission:
  fixes lo hi event_scale :: real
  assumes nonempty: "lo < hi" and positive: "0 < event_scale"
  shows "(\<exists>w. strict_interval lo hi w \<and>
      2 \<le> event_scale*w \<and> event_scale*w < 3) \<longleftrightarrow>
    lo < 3/event_scale \<and> 2/event_scale < hi"
proof -
  have ordered: "2/event_scale < 3/event_scale"
    using positive by (intro divide_strict_right_mono; linarith)
  have guard: "(2 \<le> event_scale*w \<and> event_scale*w < 3) =
      strict_interval (2/event_scale) (3/event_scale) w" for w
    using positive
    by (auto simp: strict_interval_def divide_le_eq less_divide_eq mult.commute)
  show ?thesis
    unfolding guard
    by (rule strict_interval_intersection_nonempty[OF nonempty ordered])
qed

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms spatial_block_conservation spatial_repeat_value_bound
      mahler_spatial_low_block_transport
      antihydra_centered_spatial_low_block_transport
      spatial_fixed_carry_repeat_conservation spatial_fixed_carry_repeat_complete
      spatial_block_carry_monotone translated_safe_interval
      translated_safe_output strict_interval_intersection_nonempty
      event_exponent_interval_admission})
    then () else error "Spatial carry pump depends on an oracle";
\<close>

end
