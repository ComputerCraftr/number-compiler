theory Cylinder_Radial_Hypergeometric_Elimination
  imports Main
begin

text \<open>
  A zero-extended shifted binomial packet admits an exact first-order
  elimination operator.  The identity includes packet birth and death; it is
  not merely an interior ratio calculation.  This theory proves the algebraic
  sparse-elimination step.  It does not prove a sign-isolation algorithm, a
  bit-cost bound for exact point probes, source admission, or temporal closure.
\<close>

definition radial_zero_binomial :: "nat \<Rightarrow> int \<Rightarrow> int" where
  "radial_zero_binomial r j =
    (if 0 \<le> j then int (r choose nat j) else 0)"

definition radial_shifted_binomial :: "nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int" where
  "radial_shifted_binomial r s k = radial_zero_binomial r (k-s)"

definition radial_pivot_operator ::
    "nat \<Rightarrow> int \<Rightarrow> (int \<Rightarrow> int) \<Rightarrow> int \<Rightarrow> int" where
  "radial_pivot_operator r a f k =
    (k + 1 - a) * f (k+1) - (int r - k + a) * f k"

lemma radial_binomial_balance:
  assumes "n < r"
  shows "int (Suc n) * int (r choose Suc n) =
    int (r-n) * int (r choose n)"
proof -
  have left: "Suc n * (r choose Suc n) = r * ((r-1) choose n)"
    using times_binomial_minus1_eq[of "Suc n" r] by simp
  have right: "(r-n) * (r choose n) = r * ((r-1) choose n)"
    using binomial_absorb_comp[of r n] .
  have balance_nat:
    "Suc n * (r choose Suc n) = (r-n) * (r choose n)"
    using left right by simp
  have balance_int:
    "int (Suc n * (r choose Suc n)) = int ((r-n) * (r choose n))"
    using balance_nat by simp
  show ?thesis
    using balance_int by (simp only: of_nat_mult)
qed

theorem radial_pivot_shifted_binomial:
  "radial_pivot_operator r a (radial_shifted_binomial r s) k =
    (s-a) * radial_shifted_binomial (Suc r) (s-1) k"
proof (cases "k < s-1")
  case True
  then show ?thesis
    by (simp add: radial_pivot_operator_def radial_shifted_binomial_def
        radial_zero_binomial_def)
next
  case False
  note not_before = False
  show ?thesis
  proof (cases "k = s-1")
    case True
    then show ?thesis
      by (simp add: radial_pivot_operator_def radial_shifted_binomial_def
          radial_zero_binomial_def)
  next
    case False
    note not_birth = False
    have start: "s \<le> k" using not_before not_birth by linarith
    let ?n = "nat (k-s)"
    have k: "k = s + int ?n" using start by simp
    show ?thesis
    proof (cases "?n < r")
      case True
      note inside = True
      have balance: "int (Suc ?n) * int (r choose Suc ?n) =
          int (r-?n) * int (r choose ?n)"
        using radial_binomial_balance[OF inside] .
      have pascal: "int (Suc r choose Suc ?n) =
          int (r choose ?n) + int (r choose Suc ?n)"
        by simp
      have r_bound: "?n \<le> r" using inside by simp
      have nat_difference: "int (r-?n) = int r - int ?n"
        using r_bound by simp
      have difference_nonnegative: "0 \<le> k-s" using start by simp
      have next_difference: "k + 1 - s = (k-s) + 1" by linarith
      have next_index: "nat (k + 1 - s) = Suc ?n"
        unfolding next_difference
        using difference_nonnegative by simp
      have transformed_difference: "k - (s-1) = (k-s) + 1" by linarith
      have transformed_index: "nat (k - (s-1)) = Suc ?n"
        unfolding transformed_difference
        using difference_nonnegative by simp
      have at_k: "radial_shifted_binomial r s k = int (r choose ?n)"
        unfolding radial_shifted_binomial_def radial_zero_binomial_def
        using k start by simp
      have at_next:
        "radial_shifted_binomial r s (k+1) = int (r choose Suc ?n)"
        unfolding radial_shifted_binomial_def radial_zero_binomial_def
        using start next_index by simp
      have transformed:
        "radial_shifted_binomial (Suc r) (s-1) k =
          int (Suc r choose Suc ?n)"
        unfolding radial_shifted_binomial_def radial_zero_binomial_def
        using start transformed_index by simp
      have decomposition:
        "(k + 1 - a) * int (r choose Suc ?n) -
            (int r - k + a) * int (r choose ?n) =
          (int (Suc ?n) * int (r choose Suc ?n) -
             int (r-?n) * int (r choose ?n)) +
          (s-a) * (int (r choose Suc ?n) + int (r choose ?n))"
        using k start nat_difference by (simp add: algebra_simps)
      show ?thesis
        unfolding radial_pivot_operator_def
        using at_k at_next transformed decomposition balance pascal
        by (simp add: algebra_simps)
    next
      case False
      note not_inside = False
      show ?thesis
      proof (cases "?n = r")
        case True
        note death = True
        have successor_integer: "1 + int r = int (Suc r)" by simp
        have successor_nat: "nat (1 + int r) = Suc r"
          by (simp only: successor_integer nat_int)
        show ?thesis
          unfolding radial_pivot_operator_def radial_shifted_binomial_def
            radial_zero_binomial_def
          using k start death successor_nat
          by (simp add: binomial_eq_0 algebra_simps)
      next
        case False
        note not_death = False
        have past: "r < ?n" using not_inside not_death by linarith
        then show ?thesis
          unfolding radial_pivot_operator_def radial_shifted_binomial_def
            radial_zero_binomial_def
          using k start by (simp add: binomial_eq_0)
      qed
    qed
  qed
qed

lemma radial_pivot_operator_add:
  "radial_pivot_operator r a (\<lambda>k. f k + g k) k =
    radial_pivot_operator r a f k + radial_pivot_operator r a g k"
  by (simp add: radial_pivot_operator_def algebra_simps)

lemma radial_pivot_operator_scale:
  "radial_pivot_operator r a (\<lambda>k. c * f k) k =
    c * radial_pivot_operator r a f k"
  by (simp add: radial_pivot_operator_def algebra_simps)

lemma radial_pivot_operator_abs_bound:
  assumes support_left: "a \<le> k"
      and support_right: "k < int r + a"
      and at_k: "abs (f k) \<le> B"
      and at_next: "abs (f (k+1)) \<le> B"
  shows "abs (radial_pivot_operator r a f k) \<le> (int r + 1) * B"
proof -
  let ?left = "k + 1 - a"
  let ?right = "int r - k + a"
  have left_nonnegative: "0 \<le> ?left" using support_left by linarith
  have right_nonnegative: "0 \<le> ?right" using support_right by linarith
  have coefficient_sum: "?left + ?right = int r + 1" by simp
  have left_bound: "abs (?left * f (k+1)) \<le> ?left * B"
  proof -
    have "abs (?left * f (k+1)) = ?left * abs (f (k+1))"
      using left_nonnegative by (simp add: abs_mult)
    also have "... \<le> ?left * B"
      using at_next left_nonnegative by (rule mult_left_mono)
    finally show ?thesis .
  qed
  have right_bound: "abs (?right * f k) \<le> ?right * B"
  proof -
    have "abs (?right * f k) = ?right * abs (f k)"
      using right_nonnegative by (simp add: abs_mult)
    also have "... \<le> ?right * B"
      using at_k right_nonnegative by (rule mult_left_mono)
    finally show ?thesis .
  qed
  have triangle:
    "abs (?left * f (k+1) - ?right * f k) \<le>
      abs (?left * f (k+1)) + abs (?right * f k)"
    by (rule abs_triangle_ineq4)
  have weighted_sum:
    "?left * B + ?right * B = (int r + 1) * B"
    using coefficient_sum by (simp add: algebra_simps)
  show ?thesis
    unfolding radial_pivot_operator_def
    using triangle left_bound right_bound weighted_sum by linarith
qed

definition radial_common_growth_sum ::
    "nat \<Rightarrow> (int * int) list \<Rightarrow> int \<Rightarrow> int" where
  "radial_common_growth_sum r terms k =
    sum_list (map (\<lambda>(s,c). c * radial_shifted_binomial r s k) terms)"

definition radial_eliminate_pivot_terms ::
    "int \<Rightarrow> (int * int) list \<Rightarrow> (int * int) list" where
  "radial_eliminate_pivot_terms a terms =
    map (\<lambda>(s,c). (s-1, c * (s-a))) terms"

theorem radial_pivot_common_growth_sum:
  "radial_pivot_operator r a (radial_common_growth_sum r terms) k =
    radial_common_growth_sum (Suc r) (radial_eliminate_pivot_terms a terms) k"
proof (induction terms)
  case Nil
  then show ?case
    by (simp add: radial_pivot_operator_def radial_common_growth_sum_def
        radial_eliminate_pivot_terms_def)
next
  case (Cons item terms)
  obtain s c where item_eq: "item = (s,c)" by (cases item)
  show ?case
    using Cons.IH
    by (simp add: item_eq radial_common_growth_sum_def
        radial_eliminate_pivot_terms_def radial_pivot_operator_add
        radial_pivot_operator_scale radial_pivot_shifted_binomial algebra_simps)
qed

corollary radial_pivot_term_eliminated:
  "radial_eliminate_pivot_terms a ((a,c)#terms) =
    (a-1,0) # radial_eliminate_pivot_terms a terms"
  by (simp add: radial_eliminate_pivot_terms_def)

text \<open>
  For distinct shifts, deleting the displayed zero entry decreases the sparse
  term count by one.  After pivots a<^sub>1,...,a<^sub>j, an uneliminated original
  term at shift s has shift s-j, growth r+j, and coefficient
  c * product (s-a<^sub>i).  Turning this algebra into a fast sign-run extractor
  still requires support-cell bookkeeping and charged exact point probes.
  Monotonicity of f / h only applies where the chosen pivot h is positive;
  birth and death cells cannot be crossed by that ratio argument.
\<close>

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
      @{thms radial_pivot_shifted_binomial radial_pivot_common_growth_sum
        radial_pivot_term_eliminated})
    then () else error "Radial hypergeometric elimination depends on an oracle";
\<close>

end
