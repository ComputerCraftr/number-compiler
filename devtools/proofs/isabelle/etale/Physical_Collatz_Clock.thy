theory Physical_Collatz_Clock
  imports Skew_Cylinder_Observers
begin

text \<open>The clock in this theory is bound to the physical Collatz source.
Its branch at every tick is recomputed from the current natural number; there
is no caller-supplied parity itinerary and no carry projection in the state.\<close>

definition physical_next :: "nat \<Rightarrow> nat" where
  "physical_next x = (if even x then x div 2 else 3*x+1)"

fun physical_odd_count :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "physical_odd_count 0 x = 0"
| "physical_odd_count (Suc n) x =
    (if even x then physical_odd_count n (physical_next x)
     else Suc (physical_odd_count n (physical_next x)))"

definition physical_atom :: "nat \<Rightarrow> int skew_transfer" where
  "physical_atom x =
    (if even x then \<lparr>upper=1, offset=0, lower=2\<rparr>
     else \<lparr>upper=3, offset=1, lower=1\<rparr>)"

fun physical_matrix :: "nat \<Rightarrow> nat \<Rightarrow> int skew_transfer" where
  "physical_matrix 0 x = skew_identity"
| "physical_matrix (Suc n) x =
    skew_then (physical_atom x) (physical_matrix n (physical_next x))"

lemma physical_odd_count_bounded:
  "physical_odd_count n x \<le> n"
  by (induction n arbitrary: x) (auto intro: le_SucI)

lemma physical_even_tick_exact:
  assumes "even x"
  shows "int x = (2::int) * int (x div 2)"
proof -
  obtain k where x: "x = 2*k" using assms by (elim evenE)
  show ?thesis by (simp add: x)
qed

lemma physical_atom_transport:
  "upper (physical_atom x) * int x + offset (physical_atom x) =
    lower (physical_atom x) * int (physical_next x)"
proof (cases "even x")
  case True
  then show ?thesis
    using physical_even_tick_exact[of x]
    by (simp add: physical_atom_def physical_next_def)
next
  case False
  then show ?thesis by (simp add: physical_atom_def physical_next_def)
qed

theorem physical_matrix_transport:
  "upper (physical_matrix n x) * int x + offset (physical_matrix n x) =
    lower (physical_matrix n x) * int ((physical_next ^^ n) x)"
proof (induction n arbitrary: x)
  case 0
  then show ?case by (simp add: skew_identity_def)
next
  case (Suc n)
  have first:
    "upper (physical_atom x) * int x + offset (physical_atom x) =
      lower (physical_atom x) * int (physical_next x)"
    by (rule physical_atom_transport)
  have second:
    "upper (physical_matrix n (physical_next x)) * int (physical_next x) +
       offset (physical_matrix n (physical_next x)) =
     lower (physical_matrix n (physical_next x)) *
       int ((physical_next ^^ n) (physical_next x))"
    by (rule Suc.IH)
  have composed:
    "upper (skew_then (physical_atom x)
       (physical_matrix n (physical_next x))) * int x +
       offset (skew_then (physical_atom x)
         (physical_matrix n (physical_next x))) =
     lower (skew_then (physical_atom x)
       (physical_matrix n (physical_next x))) *
       int ((physical_next ^^ n) (physical_next x))"
    using skew_transport_composes[OF first second] .
  show ?case
    using composed by (simp add: funpow_swap1)
qed

lemma physical_matrix_upper:
  "upper (physical_matrix n x) = (3::int)^(physical_odd_count n x)"
proof (induction n arbitrary: x)
  case 0
  then show ?case by (simp add: skew_identity_def)
next
  case (Suc n)
  then show ?case
    by (cases "even x")
      (simp_all add: physical_atom_def skew_then_def power_Suc)
qed

lemma physical_matrix_lower:
  "lower (physical_matrix n x) = (2::int)^(n - physical_odd_count n x)"
proof (induction n arbitrary: x)
  case 0
  then show ?case by (simp add: skew_identity_def)
next
  case (Suc n)
  have bound: "physical_odd_count n (physical_next x) \<le> n"
    by (rule physical_odd_count_bounded)
  show ?case
  proof (cases "even x")
    case True
    have exponent:
      "Suc n - physical_odd_count n (physical_next x) =
        Suc (n - physical_odd_count n (physical_next x))"
      using bound by arith
    show ?thesis
      using Suc.IH[of "physical_next x"] True exponent
      by (simp add: physical_atom_def skew_then_def power_Suc algebra_simps)
  next
    case False
    show ?thesis
      using Suc.IH[of "physical_next x"] False
      by (simp add: physical_atom_def skew_then_def)
  qed
qed

lemmas physical_matrix_diagonals = physical_matrix_upper physical_matrix_lower

theorem physical_odd_count_append:
  "physical_odd_count (m+n) x =
    physical_odd_count m x +
      physical_odd_count n ((physical_next ^^ m) x)"
proof (induction m arbitrary: x)
  case 0
  then show ?case by simp
next
  case (Suc m)
  then show ?case
    by (cases "even x") (simp_all add: funpow_swap1)
qed

theorem physical_matrix_append:
  "physical_matrix (m+n) x =
    skew_then (physical_matrix m x)
      (physical_matrix n ((physical_next ^^ m) x))"
proof (induction m arbitrary: x)
  case 0
  then show ?case by simp
next
  case (Suc m)
  then show ?case
    by (simp add: funpow_swap1 skew_associative)
qed

corollary physical_odd_count_double:
  "physical_odd_count (2*n) x =
    physical_odd_count n x +
      physical_odd_count n ((physical_next ^^ n) x)"
proof -
  have twice: "2*n = n+n" by arith
  show ?thesis unfolding twice by (rule physical_odd_count_append)
qed

corollary physical_matrix_double:
  "physical_matrix (2*n) x =
    skew_then (physical_matrix n x)
      (physical_matrix n ((physical_next ^^ n) x))"
proof -
  have twice: "2*n = n+n" by arith
  show ?thesis unfolding twice by (rule physical_matrix_append)
qed

definition physical_slope :: "nat \<Rightarrow> nat \<Rightarrow> rat" where
  "physical_slope n x =
    of_int (upper (physical_matrix n x)) /
      of_int (lower (physical_matrix n x))"

lemma physical_slope_S_arithmetic:
  "physical_slope n x =
    (3::rat)^(physical_odd_count n x) /
      2^(n - physical_odd_count n x)"
  by (simp add: physical_slope_def physical_matrix_diagonals)

theorem physical_slope_append:
  "physical_slope (m+n) x =
    physical_slope m x *
      physical_slope n ((physical_next ^^ m) x)"
  by (simp add: physical_slope_def physical_matrix_append skew_then_def
      physical_matrix_diagonals field_simps)

corollary physical_slope_double:
  "physical_slope (2*n) x =
    physical_slope n x * physical_slope n ((physical_next ^^ n) x)"
proof -
  have twice: "2*n = n+n" by arith
  show ?thesis unfolding twice by (rule physical_slope_append)
qed

text \<open>These results specify the exact source-bound weighted semantics.
They do not assert that a particular runtime cache discovers or stores this
matrix, nor do they establish a complexity bound for doing so.\<close>

ML \<open>
 val _ = if null (Thm_Deps.all_oracles @{thms
   physical_odd_count_bounded physical_even_tick_exact physical_atom_transport
   physical_matrix_transport physical_matrix_upper physical_matrix_lower
   physical_odd_count_append physical_matrix_append
   physical_odd_count_double physical_matrix_double
   physical_slope_S_arithmetic physical_slope_append physical_slope_double})
   then () else error "Physical Collatz clock oracle dependency";
\<close>

end
