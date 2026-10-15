theory Fermat_Mersenne_Source_Bound_Refinement
  imports Main
begin

text \<open>
The source guard below is the no-wrap domain for a raw inner successor,
before cyclic or negacyclic reduction by a candidate modulus.  It proves
exactness only inside that domain.  It says nothing about the wrapped
terminal forcing needed for an arbitrary Fermat or Mersenne primality result.
\<close>

datatype special_source_family = Fermat_Source | Mersenne_Source

definition fermat_inner_source :: "nat \<Rightarrow> nat" where
  "fermat_inner_source t = 3^(2^t)"

fun mersenne_inner_trace :: "nat \<Rightarrow> nat" where
  "mersenne_inner_trace 0 = 4"
| "mersenne_inner_trace (Suc t) = mersenne_inner_trace t^2 - 2"

definition source_successor :: "special_source_family \<Rightarrow> nat \<Rightarrow> nat" where
  "source_successor family t =
    (case family of
       Fermat_Source \<Rightarrow> fermat_inner_source (Suc t)
     | Mersenne_Source \<Rightarrow> mersenne_inner_trace (Suc t))"

fun candidate_modulus :: "special_source_family \<Rightarrow> nat \<Rightarrow> nat" where
  "candidate_modulus Fermat_Source n = 2^(2^n) + 1"
| "candidate_modulus Mersenne_Source p = 2^p - 1"

definition source_no_wrap_guard ::
  "special_source_family \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "source_no_wrap_guard family parameter level =
    (case family of
       Fermat_Source \<Rightarrow> 3 \<le> parameter \<and> level + 2 \<le> parameter
     | Mersenne_Source \<Rightarrow> 7 \<le> parameter \<and>
         2^(level+2) \<le> parameter)"

text \<open>The Fermat inequality is the exact bound
  @{term "3^(2^t) < 2^(2^(Suc t))"}.\<close>

lemma fermat_inner_square_step:
  "fermat_inner_source (Suc t) = fermat_inner_source t^2"
proof -
  have exponent: "(2::nat)^(Suc t) = (2::nat)^t + (2::nat)^t"
    by (simp add: power_Suc algebra_simps)
  show ?thesis
    unfolding fermat_inner_source_def
    by (simp only: exponent power_add power2_eq_square)
qed

lemma four_power_is_dyadic_bound:
  "(4::nat)^(2^t) = (2::nat)^(2^(Suc t))"
  by (simp add: power_mult power_Suc algebra_simps)

lemma fermat_inner_source_bound:
  "fermat_inner_source t < 2^(2^(Suc t))"
proof -
  have growth: "(3::nat)^(2^t) < (4::nat)^(2^t)"
    by (rule power_strict_mono) simp_all
  have "fermat_inner_source t < 4^(2^t)"
    using growth by (simp add: fermat_inner_source_def)
  also have "... = 2^(2^(Suc t))"
    by (rule four_power_is_dyadic_bound)
  finally show ?thesis .
qed

lemma mersenne_inner_trace_lower:
  "4 \<le> mersenne_inner_trace t"
proof (induction t)
  case 0
  then show ?case by simp
next
  case (Suc t)
  have square_lower:
    "4*4 \<le> mersenne_inner_trace t * mersenne_inner_trace t"
    by (rule mult_mono) (use Suc.IH in auto)
  show ?case
    using square_lower by (simp add: power2_eq_square; arith)
qed

lemma dyadic_bound_square:
  "((2::nat)^(2^(Suc t)))^2 = (2::nat)^(2^(Suc(Suc t)))"
proof -
  have exponent:
    "(2::nat)^(Suc(Suc t)) = (2::nat)^(Suc t) + (2::nat)^(Suc t)"
    by (simp add: power_Suc algebra_simps)
  have "((2::nat)^(2^(Suc t)))^2 =
      (2::nat)^(2^(Suc t) * 2)"
    by (simp only: power_mult)
  also have "... = (2::nat)^(2^(Suc t) + 2^(Suc t))"
    by (simp add: algebra_simps)
  also have "... = (2::nat)^(2^(Suc(Suc t)))"
    by (simp only: exponent[symmetric])
  finally show ?thesis .
qed

lemma mersenne_inner_trace_bound:
  "mersenne_inner_trace t \<le> 2^(2^(Suc t))"
proof (induction t)
  case 0
  then show ?case by simp
next
  case (Suc t)
  let ?x = "mersenne_inner_trace t"
  let ?b = "(2::nat)^(2^(Suc t))"
  have x_bound: "?x \<le> ?b" using Suc.IH .
  have step_bound: "mersenne_inner_trace (Suc t) \<le> ?b^2"
  proof (cases "?x < ?b")
    case True
    have square: "?x^2 < ?b^2"
      by (rule power_strict_mono) (use True in auto)
    show ?thesis
      using square by (simp add: mersenne_inner_trace.simps; arith)
  next
    case False
    have equal: "?x = ?b" using x_bound False by simp
    show ?thesis
      using equal by (simp add: mersenne_inner_trace.simps; arith)
  qed
  have bound_square: "?b^2 = 2^(2^(Suc(Suc t)))"
    by (rule dyadic_bound_square)
  show ?case
    using step_bound bound_square by simp
qed

lemma mersenne_inner_successor_gap:
  "mersenne_inner_trace (Suc t) < 2^(2^(Suc(Suc t))) - 1"
proof -
  let ?x = "mersenne_inner_trace t"
  let ?b = "(2::nat)^(2^(Suc t))"
  have x_bound: "?x \<le> ?b" by (rule mersenne_inner_trace_bound)
  have x_lower: "4 \<le> ?x" by (rule mersenne_inner_trace_lower)
  have square_lower: "4 \<le> ?x^2"
  proof -
    have product_lower: "4*4 \<le> ?x * ?x"
      by (rule mult_mono) (use x_lower in auto)
    show ?thesis using product_lower by (simp add: power2_eq_square; arith)
  qed
  have step_bound: "mersenne_inner_trace (Suc t) < ?b^2 - 1"
  proof (cases "?x < ?b")
    case True
    have square: "?x^2 < ?b^2"
      by (rule power_strict_mono) (use True in auto)
    show ?thesis
      using square square_lower
      by (simp add: mersenne_inner_trace.simps; arith)
  next
    case False
    have equal: "?x = ?b" using x_bound False by simp
    show ?thesis
      using equal square_lower
      by (simp add: mersenne_inner_trace.simps; arith)
  qed
  have bound_square: "?b^2 = 2^(2^(Suc(Suc t)))"
    by (rule dyadic_bound_square)
  show ?thesis using step_bound bound_square by simp
qed

text \<open>The three-valued carry of multiplying a low radix residue by three
is the Euclidean quotient, while the carry of adding the source to its
double is only its Boolean difference from the doubling quotient. The
source-matrix consumer keeps these values in separate fields.
\<close>

theorem low_radix_tripling_carry_split:
  fixes r m :: nat
  assumes modulus_positive: "0 < m" and source_remainder: "r < m"
  shows "3*r = (3*r div m)*m + 3*r mod m"
    and "3*r div m < 3"
    and "2*r div m < 2"
proof -
  show "3*r = (3*r div m)*m + 3*r mod m"
    by (simp add: div_mult_mod_eq mult.commute)
  have triple_bound: "3*r < m*3"
    using source_remainder by arith
  show "3*r div m < 3"
    using modulus_positive triple_bound
    by (simp add: div_less_iff_less_mult)
  have double_bound: "2*r < m*2"
    using source_remainder by arith
  show "2*r div m < 2"
    using modulus_positive double_bound
    by (simp add: div_less_iff_less_mult)
qed

theorem guarded_source_successor_below_candidate:
  assumes guard: "source_no_wrap_guard family parameter level"
  shows "source_successor family level < candidate_modulus family parameter"
proof (cases family)
  case Fermat_Source
  have lower_width: "3 \<le> parameter"
    and level_bound: "level + 2 \<le> parameter"
    using guard Fermat_Source by (simp_all add: source_no_wrap_guard_def)
  have exponent_bound: "(2::nat)^(level+2) \<le> (2::nat)^parameter"
    by (rule power_increasing[OF level_bound]) simp
  have outer_bound:
    "(2::nat)^(2^(level+2)) \<le> (2::nat)^(2^parameter)"
    by (rule power_increasing[OF exponent_bound]) simp
  have source_bound:
    "source_successor family level < (2::nat)^(2^(level+2))"
  proof -
    have bound:
      "fermat_inner_source (Suc level) <
        (2::nat)^(2^(Suc(Suc level)))"
      by (rule fermat_inner_source_bound)
    have source_eq:
      "source_successor family level = fermat_inner_source (Suc level)"
      using Fermat_Source by (simp add: source_successor_def)
    have bound_eq:
      "(2::nat)^(2^(Suc(Suc level))) = (2::nat)^(2^(level+2))"
      by simp
    have "source_successor family level =
        fermat_inner_source (Suc level)"
      by (rule source_eq)
    also have "... < (2::nat)^(2^(Suc(Suc level)))"
      by (rule bound)
    also have "... = (2::nat)^(2^(level+2))"
      by (rule bound_eq)
    finally show ?thesis .
  qed
  have candidate_growth:
    "2^(2^parameter) < candidate_modulus family parameter"
    using Fermat_Source by simp
  have source_outer:
    "source_successor family level < 2^(2^parameter)"
    by (rule less_le_trans[OF source_bound outer_bound])
  show ?thesis
    by (rule less_trans[OF source_outer candidate_growth])
next
  case Mersenne_Source
  have lower_width: "7 \<le> parameter"
    and exponent_bound: "(2::nat)^(level+2) \<le> parameter"
    using guard Mersenne_Source by (simp_all add: source_no_wrap_guard_def)
  have outer_bound: "(2::nat)^(2^(level+2)) \<le> (2::nat)^parameter"
    by (rule power_increasing[OF exponent_bound]) simp
  have trace_gap:
    "mersenne_inner_trace (Suc level) <
      (2::nat)^(2^(Suc(Suc level))) - 1"
    by (rule mersenne_inner_successor_gap[of level])
  have source_eq:
    "source_successor family level = mersenne_inner_trace (Suc level)"
    using Mersenne_Source
    by (simp only: source_successor_def special_source_family.case Mersenne_Source)
  have gap_bound_eq:
    "(2::nat)^(2^(Suc(Suc level))) - 1 =
      (2::nat)^(2^(level+2)) - 1"
    by simp
  have source_gap:
    "source_successor family level <
      (2::nat)^(2^(level+2)) - 1"
  proof -
    have "source_successor family level = mersenne_inner_trace (Suc level)"
      by (rule source_eq)
    also have "... < (2::nat)^(2^(Suc(Suc level))) - 1"
      by (rule trace_gap)
    also have "... = (2::nat)^(2^(level+2)) - 1"
      by (rule gap_bound_eq)
    finally show ?thesis .
  qed
  have candidate_bound:
    "2^(2^(level+2)) - 1 \<le> candidate_modulus family parameter"
    using Mersenne_Source outer_bound
    by (simp only: candidate_modulus.simps Mersenne_Source; arith)
  show ?thesis
    using source_gap candidate_bound by (rule less_le_trans)
qed

definition candidate_successor_residue ::
  "special_source_family \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "candidate_successor_residue family parameter level =
    source_successor family level mod candidate_modulus family parameter"

theorem guarded_candidate_successor_is_unwrapped:
  assumes "source_no_wrap_guard family parameter level"
  shows "candidate_successor_residue family parameter level =
    source_successor family level"
  unfolding candidate_successor_residue_def
  by (rule mod_less[OF guarded_source_successor_below_candidate[OF assms]])

text \<open>These executable checks evaluate only small source/candidate examples.
The guard and refinement theorems quantify over all natural parameters.\<close>

value "source_no_wrap_guard Fermat_Source 12 4"
value "source_no_wrap_guard Mersenne_Source 11 1"
value "candidate_successor_residue Fermat_Source 3 0"
value "candidate_successor_residue Mersenne_Source 11 1"

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms fermat_inner_square_step four_power_is_dyadic_bound
      fermat_inner_source_bound mersenne_inner_trace_lower dyadic_bound_square
      mersenne_inner_trace_bound mersenne_inner_successor_gap
      low_radix_tripling_carry_split
      guarded_source_successor_below_candidate
      guarded_candidate_successor_is_unwrapped}) then ()
    else error "Fermat/Mersenne source-bound refinement depends on an oracle";
\<close>

end
