theory Homogeneous_Growth_Scale
  imports Main "HOL.Rat" "HOL.Transcendental"
begin

text \<open>Exact homogeneous growth is stored as the prime-exponent pair
\<open>(H,D)\<close>, denoting \<open>3^H / 2^D\<close>.  The record is the executable
normal form used by growth consumers: composition adds coordinates and
powering multiplies them.  Radix readout uses the exact logarithmic slope and
integer floor; point and interval queries are differences of these endpoint
orders, so block summaries telescope without replaying their symbols.\<close>

record homogeneous_growth_scale =
  growths :: nat
  halvings :: nat

definition homogeneous_growth_identity :: homogeneous_growth_scale where
  "homogeneous_growth_identity = \<lparr>growths=0, halvings=0\<rparr>"

definition homogeneous_growth_then ::
    "homogeneous_growth_scale \<Rightarrow> homogeneous_growth_scale \<Rightarrow>
      homogeneous_growth_scale" where
  "homogeneous_growth_then A B =
    \<lparr>growths = growths A + growths B,
     halvings = halvings A + halvings B\<rparr>"

definition homogeneous_growth_power ::
    "homogeneous_growth_scale \<Rightarrow> nat \<Rightarrow> homogeneous_growth_scale" where
  "homogeneous_growth_power A n =
    \<lparr>growths = n * growths A, halvings = n * halvings A\<rparr>"

definition homogeneous_growth_ratio :: "homogeneous_growth_scale \<Rightarrow> rat" where
  "homogeneous_growth_ratio A =
    (3::rat)^growths A / (2::rat)^halvings A"

lemma homogeneous_growth_then_identity [simp]:
  "homogeneous_growth_then homogeneous_growth_identity A = A"
  "homogeneous_growth_then A homogeneous_growth_identity = A"
proof -
  show "homogeneous_growth_then homogeneous_growth_identity A = A"
    by (cases A; simp add: homogeneous_growth_then_def
        homogeneous_growth_identity_def)
  show "homogeneous_growth_then A homogeneous_growth_identity = A"
    by (cases A; simp add: homogeneous_growth_then_def
        homogeneous_growth_identity_def)
qed

lemma homogeneous_growth_then_assoc:
  "homogeneous_growth_then (homogeneous_growth_then A B) C =
    homogeneous_growth_then A (homogeneous_growth_then B C)"
  by (cases A; cases B; cases C; simp add: homogeneous_growth_then_def
      algebra_simps)

theorem homogeneous_growth_ratio_then:
  "homogeneous_growth_ratio (homogeneous_growth_then A B) =
    homogeneous_growth_ratio A * homogeneous_growth_ratio B"
  by (cases A; cases B; simp add: homogeneous_growth_ratio_def
      homogeneous_growth_then_def power_add field_simps)

theorem homogeneous_growth_ratio_power:
  "homogeneous_growth_ratio (homogeneous_growth_power A n) =
    homogeneous_growth_ratio A ^ n"
  by (cases A; simp add: homogeneous_growth_ratio_def
      homogeneous_growth_power_def power_mult field_simps)

lemma homogeneous_growth_power_then:
  "homogeneous_growth_power A (m+n) =
    homogeneous_growth_then (homogeneous_growth_power A m)
      (homogeneous_growth_power A n)"
  by (cases A; simp add: homogeneous_growth_power_def
      homogeneous_growth_then_def algebra_simps)

definition homogeneous_growth_radix_slope ::
    "homogeneous_growth_scale \<Rightarrow> nat \<Rightarrow> real" where
  "homogeneous_growth_radix_slope A b =
    (of_nat (growths A) * ln 3 - of_nat (halvings A) * ln 2) /
      ln (of_nat b)"

definition homogeneous_growth_radix_order ::
    "homogeneous_growth_scale \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int" where
  "homogeneous_growth_radix_order A b q =
    floor (of_int q * homogeneous_growth_radix_slope A b)"

definition homogeneous_growth_point ::
    "homogeneous_growth_scale \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int" where
  "homogeneous_growth_point A b q =
    homogeneous_growth_radix_order A b (q+1) -
      homogeneous_growth_radix_order A b q"

definition homogeneous_growth_block ::
    "homogeneous_growth_scale \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> int" where
  "homogeneous_growth_block A b q n =
    homogeneous_growth_radix_order A b (q + int n) -
      homogeneous_growth_radix_order A b q"

fun homogeneous_growth_points_sum ::
    "homogeneous_growth_scale \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> int" where
  "homogeneous_growth_points_sum A b q 0 = 0"
| "homogeneous_growth_points_sum A b q (Suc n) =
    homogeneous_growth_points_sum A b q n +
      homogeneous_growth_point A b (q + int n)"

theorem homogeneous_growth_block_is_point_sum:
  "homogeneous_growth_points_sum A b q n = homogeneous_growth_block A b q n"
proof (induction n)
  case 0
  then show ?case by (simp add: homogeneous_growth_block_def)
next
  case (Suc n)
  then show ?case
    by (simp add: homogeneous_growth_block_def homogeneous_growth_point_def
        homogeneous_growth_radix_order_def algebra_simps)
qed

theorem homogeneous_growth_block_chronological:
  "homogeneous_growth_block A b q (m+n) =
    homogeneous_growth_block A b q m +
      homogeneous_growth_block A b (q + int m) n"
  by (simp add: homogeneous_growth_block_def algebra_simps)

lemma homogeneous_growth_radix_slope_then:
  "homogeneous_growth_radix_slope (homogeneous_growth_then A B) b =
    homogeneous_growth_radix_slope A b +
      homogeneous_growth_radix_slope B b"
  by (cases A; cases B; simp add: homogeneous_growth_radix_slope_def
      homogeneous_growth_then_def algebra_simps add_divide_distrib
      diff_divide_distrib)

lemma homogeneous_growth_radix_slope_power:
  "homogeneous_growth_radix_slope (homogeneous_growth_power A n) b =
    of_nat n * homogeneous_growth_radix_slope A b"
  by (cases A; simp add: homogeneous_growth_radix_slope_def
      homogeneous_growth_power_def algebra_simps)

lemma homogeneous_growth_floor_certificate:
  assumes lower: "of_int k \<le> x" and upper: "x < of_int k + 1"
  shows "floor x = k"
  by (rule floor_unique[OF lower upper])

lemma homogeneous_growth_floor_enclosure_certificate:
  assumes bracket_lower: "of_int k \<le> lo"
      and bracket_upper: "hi < of_int k + 1"
      and enclosure: "lo \<le> x" "x \<le> hi"
  shows "floor x = k"
proof (rule homogeneous_growth_floor_certificate)
  show "of_int k \<le> x" using assms by linarith
  show "x < of_int k + 1" using assms by linarith
qed

definition mahler_temporal_growth_unit :: homogeneous_growth_scale where
  "mahler_temporal_growth_unit = \<lparr>growths=1, halvings=1\<rparr>"

lemma mahler_temporal_growth_unit_exact:
  "homogeneous_growth_ratio mahler_temporal_growth_unit = (3/2::rat)"
  by (simp add: homogeneous_growth_ratio_def
      mahler_temporal_growth_unit_def)

lemma mahler_temporal_extent_exact:
  "homogeneous_growth_ratio
      (homogeneous_growth_power mahler_temporal_growth_unit n) =
    (3/2::rat)^n"
  by (simp add: homogeneous_growth_ratio_power
      mahler_temporal_growth_unit_exact)

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms homogeneous_growth_then_identity homogeneous_growth_then_assoc
      homogeneous_growth_ratio_then homogeneous_growth_ratio_power
      homogeneous_growth_power_then
      homogeneous_growth_block_is_point_sum
      homogeneous_growth_block_chronological
      homogeneous_growth_radix_slope_then
      homogeneous_growth_radix_slope_power
      homogeneous_growth_floor_certificate
      homogeneous_growth_floor_enclosure_certificate
      mahler_temporal_growth_unit_exact mahler_temporal_extent_exact})
    then () else error "Homogeneous growth scale depends on an oracle";
\<close>

end
