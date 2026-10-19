theory Mersenne_Matrix_Source_Refinement
  imports Power_Clock_Jumps "HOL-Decision_Procs.Commutative_Ring"
begin

text \<open>The Mersenne trace observer is rooted at the exact selected source
\<open>2*(2^p-1)\<close> modulo a radix power. It then observes the trace-squaring
recurrence. These facts describe the source and the one-step Cayley--Hamilton
identity; they do not authorize primality conclusions or assume that a
candidate group-order exponent is valid.\<close>

definition mersenne_trace_source_residue :: "nat \<Rightarrow> nat \<Rightarrow> nat"
    where
  "mersenne_trace_source_residue modulus exponent =
    (2 * (2^exponent - 1)) mod modulus"

lemma mersenne_trace_source_residue_power_form:
  "mersenne_trace_source_residue modulus exponent =
    ((2::nat)^(exponent + 1) - 2) mod modulus"
proof -
  have positive: "1 \<le> (2::nat)^exponent" by simp
  have power: "(2::nat)^(exponent + 1) = 2 * 2^exponent"
    by (simp add: power_Suc mult.commute)
  have representative:
    "2 * (2^exponent - 1) = (2::nat)^(exponent + 1) - 2"
    using positive power by presburger
  show ?thesis
    unfolding mersenne_trace_source_residue_def
    by (simp only: representative)
qed

type_synonym 'a mersenne_matrix2 = "('a \<times> 'a) \<times> ('a \<times> 'a)"

definition mersenne_matrix2_multiply ::
    "'a::comm_ring_1 mersenne_matrix2 \<Rightarrow> 'a mersenne_matrix2 \<Rightarrow>
      'a mersenne_matrix2" where
  "mersenne_matrix2_multiply A B =
    case_prod (\<lambda>r1 r2.
      case_prod (\<lambda>s1 s2.
        ((fst r1 * fst s1 + snd r1 * fst s2,
          fst r1 * snd s1 + snd r1 * snd s2),
         (fst r2 * fst s1 + snd r2 * fst s2,
          fst r2 * snd s1 + snd r2 * snd s2))) B) A"

definition mersenne_matrix2_one :: "'a::comm_ring_1 mersenne_matrix2" where
  "mersenne_matrix2_one = ((1,0),(0,1))"

definition mersenne_matrix2_determinant ::
    "'a::comm_ring_1 mersenne_matrix2 \<Rightarrow> 'a" where
  "mersenne_matrix2_determinant A =
    case_prod (\<lambda>r1 r2. fst r1 * snd r2 - snd r1 * fst r2) A"

definition mersenne_matrix2_trace :: "'a mersenne_matrix2 \<Rightarrow> 'a::plus" where
  "mersenne_matrix2_trace A =
    case_prod (\<lambda>r1 r2. fst r1 + snd r2) A"

definition mersenne_companion_matrix ::
    "'a::comm_ring_1 \<Rightarrow> 'a mersenne_matrix2" where
  "mersenne_companion_matrix trace = ((trace,-1),(1,0))"

lemma mersenne_matrix2_multiply_assoc:
  "mersenne_matrix2_multiply
      (mersenne_matrix2_multiply A B) C =
    mersenne_matrix2_multiply A (mersenne_matrix2_multiply B C)"
proof -
  obtain arow1 arow2 where A_outer: "A = (arow1,arow2)"
    by (cases A) auto
  obtain a11 a12 where A_first: "arow1 = (a11,a12)"
    by (cases arow1) auto
  obtain a21 a22 where A_second: "arow2 = (a21,a22)"
    by (cases arow2) auto
  have A: "A = ((a11,a12),(a21,a22))"
    using A_outer A_first A_second by simp
  obtain brow1 brow2 where B_outer: "B = (brow1,brow2)"
    by (cases B) auto
  obtain b11 b12 where B_first: "brow1 = (b11,b12)"
    by (cases brow1) auto
  obtain b21 b22 where B_second: "brow2 = (b21,b22)"
    by (cases brow2) auto
  have B: "B = ((b11,b12),(b21,b22))"
    using B_outer B_first B_second by simp
  obtain crow1 crow2 where C_outer: "C = (crow1,crow2)"
    by (cases C) auto
  obtain c11 c12 where C_first: "crow1 = (c11,c12)"
    by (cases crow1) auto
  obtain c21 c22 where C_second: "crow2 = (c21,c22)"
    by (cases crow2) auto
  have C: "C = ((c11,c12),(c21,c22))"
    using C_outer C_first C_second by simp
  show ?thesis
    unfolding A B C
    by (simp add: mersenne_matrix2_multiply_def algebra_simps)
qed

lemma mersenne_matrix2_multiply_one_left:
  "mersenne_matrix2_multiply mersenne_matrix2_one A = A"
  by (cases A; simp add: mersenne_matrix2_one_def
      mersenne_matrix2_multiply_def)

lemma mersenne_matrix2_multiply_one_right:
  "mersenne_matrix2_multiply A mersenne_matrix2_one = A"
  by (cases A; simp add: mersenne_matrix2_one_def
      mersenne_matrix2_multiply_def)

lemma mersenne_matrix2_determinant_square:
  fixes A :: "'a::comm_ring_1 mersenne_matrix2"
  shows "mersenne_matrix2_determinant
      (mersenne_matrix2_multiply A A) =
    (mersenne_matrix2_determinant A)^2"
proof -
  obtain first second where outer: "A = (first,second)"
    by (cases A) auto
  obtain a b where first: "first = (a,b)"
    by (cases first) auto
  obtain c d where second: "second = (c,d)"
    by (cases second) auto
  have representation: "A = ((a,b),(c,d))"
    using outer first second by simp
  show ?thesis
    unfolding representation
    by (simp add: mersenne_matrix2_determinant_def
        mersenne_matrix2_multiply_def algebra_simps power2_eq_square)
qed

lemma mersenne_matrix2_trace_square_general:
  fixes A :: "'a::comm_ring_1 mersenne_matrix2"
  shows "mersenne_matrix2_trace (mersenne_matrix2_multiply A A) =
    (mersenne_matrix2_trace A)^2 -
      2 * mersenne_matrix2_determinant A"
proof -
  obtain row1 row2 where rows: "A = (row1, row2)"
    by (cases A) auto
  obtain a b where first_row: "row1 = (a, b)"
    by (cases row1) auto
  obtain c d where second_row: "row2 = (c, d)"
    by (cases row2) auto
  have representation: "A = ((a, b), (c, d))"
    using rows first_row second_row by simp
  show ?thesis
    unfolding representation
    by (simp add: mersenne_matrix2_trace_def
        mersenne_matrix2_determinant_def
        mersenne_matrix2_multiply_def algebra_simps power2_eq_square)
qed

fun mersenne_matrix2_square_iterate ::
    "'a::comm_ring_1 mersenne_matrix2 \<Rightarrow> nat \<Rightarrow> 'a mersenne_matrix2" where
  "mersenne_matrix2_square_iterate A 0 = A"
| "mersenne_matrix2_square_iterate A (Suc n) =
    mersenne_matrix2_multiply
      (mersenne_matrix2_square_iterate A n)
      (mersenne_matrix2_square_iterate A n)"

fun mersenne_matrix2_power ::
    "'a::comm_ring_1 mersenne_matrix2 \<Rightarrow> nat \<Rightarrow> 'a mersenne_matrix2" where
  "mersenne_matrix2_power A 0 = mersenne_matrix2_one"
| "mersenne_matrix2_power A (Suc n) =
    mersenne_matrix2_multiply (mersenne_matrix2_power A n) A"

lemma mersenne_matrix2_power_add:
  "mersenne_matrix2_power A (m+n) =
    mersenne_matrix2_multiply
      (mersenne_matrix2_power A m) (mersenne_matrix2_power A n)"
proof (induction n)
  case 0
  then show ?case
    by (simp add: mersenne_matrix2_multiply_one_right)
next
  case (Suc n)
  then show ?case
    by (simp add: mersenne_matrix2_multiply_assoc)
qed

lemma mersenne_matrix2_square_iterate_is_dyadic_power:
  "mersenne_matrix2_square_iterate A n =
    mersenne_matrix2_power A (2^n)"
proof (induction n)
  case 0
  then show ?case
    by (simp add: mersenne_matrix2_power.simps
        mersenne_matrix2_multiply_one_left)
next
  case (Suc n)
  have exponent: "(2::nat)^(Suc n) = 2^n + 2^n"
    by (simp add: power_Suc; ring)
  have powered:
    "mersenne_matrix2_power A (2^(Suc n)) =
      mersenne_matrix2_multiply
        (mersenne_matrix2_power A (2^n))
        (mersenne_matrix2_power A (2^n))"
  proof -
    have "mersenne_matrix2_power A (2^(Suc n)) =
        mersenne_matrix2_power A (2^n + 2^n)"
      by (simp only: exponent)
    also have "... = mersenne_matrix2_multiply
        (mersenne_matrix2_power A (2^n))
        (mersenne_matrix2_power A (2^n))"
      by (rule mersenne_matrix2_power_add)
    finally show ?thesis .
  qed
  have "mersenne_matrix2_square_iterate A (Suc n) =
      mersenne_matrix2_multiply
        (mersenne_matrix2_square_iterate A n)
        (mersenne_matrix2_square_iterate A n)"
    by simp
  also have "... = mersenne_matrix2_multiply
      (mersenne_matrix2_power A (2^n))
      (mersenne_matrix2_power A (2^n))"
    by (simp only: Suc.IH)
  also have "... = mersenne_matrix2_power A (2^(Suc n))"
    by (rule powered[symmetric])
  finally show ?case .
qed

lemma mersenne_matrix2_determinant_square_iterate:
  "mersenne_matrix2_determinant
      (mersenne_matrix2_square_iterate A n) =
    (mersenne_matrix2_determinant A)^(2^n)"
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have exponent: "(2::nat)^(Suc n) = 2^n * 2"
    by (simp add: power_Suc)
  have determinant_step:
    "mersenne_matrix2_determinant
        (mersenne_matrix2_square_iterate A (Suc n)) =
      (mersenne_matrix2_determinant
        (mersenne_matrix2_square_iterate A n))^2"
    by (simp add: mersenne_matrix2_square_iterate.simps
        mersenne_matrix2_determinant_square)
  have squared:
    "(mersenne_matrix2_determinant A ^ (2^n))^2 =
      mersenne_matrix2_determinant A ^ (2^n * 2)"
    by (simp add: power_mult)
  show ?case
  proof -
    have "mersenne_matrix2_determinant
        (mersenne_matrix2_square_iterate A (Suc n)) =
        (mersenne_matrix2_determinant A ^ (2^n))^2"
      using determinant_step Suc.IH by simp
    also have "... = mersenne_matrix2_determinant A ^ (2^n * 2)"
      by (rule squared)
    also have "... = mersenne_matrix2_determinant A ^ (2^(Suc n))"
      by (simp only: exponent)
    finally show ?thesis .
  qed
qed

theorem mersenne_matrix2_determinant_one_trace_squaring:
  fixes A :: "'a::comm_ring_1 mersenne_matrix2"
  assumes determinant_one: "mersenne_matrix2_determinant A = 1"
  shows "mersenne_matrix2_trace
      (mersenne_matrix2_square_iterate A n) =
    (lucas_trace_step ^^ n) (mersenne_matrix2_trace A)"
  using determinant_one
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have current_determinant:
    "mersenne_matrix2_determinant
      (mersenne_matrix2_square_iterate A n) = 1"
    using determinant_one mersenne_matrix2_determinant_square_iterate[of A n]
    by simp
  have current_trace:
    "mersenne_matrix2_trace
        (mersenne_matrix2_square_iterate A (Suc n)) =
      lucas_trace_step (mersenne_matrix2_trace
        (mersenne_matrix2_square_iterate A n))"
    using mersenne_matrix2_trace_square_general[of
        "mersenne_matrix2_square_iterate A n"] current_determinant
    by (simp add: mersenne_matrix2_square_iterate.simps
        lucas_trace_step_def power2_eq_square)
  show ?case
    using current_trace Suc.IH[OF determinant_one]
    by (simp only: funpow.simps(2) comp_apply)
qed

corollary mersenne_companion_trace_dyadic_power:
  "mersenne_matrix2_trace
      (mersenne_matrix2_power (mersenne_companion_matrix trace) (2^n)) =
    (lucas_trace_step ^^ n) trace"
proof -
  have determinant:
    "mersenne_matrix2_determinant (mersenne_companion_matrix trace) = 1"
    by (simp add: mersenne_matrix2_determinant_def
        mersenne_companion_matrix_def)
  have trace:
    "mersenne_matrix2_trace
        (mersenne_matrix2_square_iterate
          (mersenne_companion_matrix trace) n) =
      (lucas_trace_step ^^ n) trace"
    using mersenne_matrix2_determinant_one_trace_squaring[OF determinant,
        of n]
    by (simp add: mersenne_matrix2_trace_def
        mersenne_companion_matrix_def)
  have representation:
    "mersenne_matrix2_power (mersenne_companion_matrix trace) (2^n) =
      mersenne_matrix2_square_iterate (mersenne_companion_matrix trace) n"
    using mersenne_matrix2_square_iterate_is_dyadic_power[of
        "mersenne_companion_matrix trace" n]
    by simp
  show ?thesis using trace representation by simp
qed

text \<open>For \<open>A(x) = ((x,-1),(1,0))\<close>, direct matrix multiplication gives
\<open>Tr(A(x)^2) = x^2-2\<close>. This is the finite trace step consumed by the
runtime matrix-square operator. The determinant-one condition is built into
the companion form; this identity is independent of any asserted period.\<close>

lemma mersenne_companion_trace_square:
  fixes trace :: "'a::comm_ring_1"
  shows "mersenne_matrix2_trace
      (mersenne_matrix2_multiply (mersenne_companion_matrix trace)
        (mersenne_companion_matrix trace)) = trace^2 - 2"
proof -
  have determinant:
    "mersenne_matrix2_determinant (mersenne_companion_matrix trace) = 1"
    by (simp add: mersenne_matrix2_determinant_def
        mersenne_companion_matrix_def)
  have general:
    "mersenne_matrix2_trace
        (mersenne_matrix2_multiply (mersenne_companion_matrix trace)
          (mersenne_companion_matrix trace)) =
      (mersenne_matrix2_trace (mersenne_companion_matrix trace))^2 -
        2 * mersenne_matrix2_determinant
          (mersenne_companion_matrix trace)"
    by (rule mersenne_matrix2_trace_square_general)
  show ?thesis using general determinant by (simp add:
      mersenne_matrix2_trace_def mersenne_companion_matrix_def)
qed

text \<open>The optimized runtime may reduce a large exponent only after its
exact matrix owner checks \<open>A^period = I\<close> for the actual source matrix. The
following specialization records the only reduction rule licensed by that
check. It does not derive the period from the size of SL2 and therefore
cannot turn a group-cardinality estimate into an unproved period.\<close>

theorem checked_mersenne_matrix_period_reduction:
  fixes matrix :: "'a::monoid_mult"
  assumes period_positive: "period > 0"
      and period_checked: "matrix ^ period = 1"
  shows "matrix ^ exponent = matrix ^ (exponent mod period)"
  by (rule power_reduce_at_known_period[OF period_positive period_checked])

corollary checked_mersenne_dyadic_matrix_power_reduction:
  fixes matrix :: "'a::monoid_mult"
  assumes period_positive: "period > 0"
      and period_checked: "matrix ^ period = 1"
  shows "matrix ^ (2^steps) =
    matrix ^ ((2^steps) mod period)"
  by (rule checked_mersenne_matrix_period_reduction
      [OF period_positive period_checked])

ML \<open>
  val checked = @{thms mersenne_trace_source_residue_power_form
    mersenne_matrix2_determinant_square_iterate
    mersenne_companion_trace_square
    mersenne_matrix2_determinant_one_trace_squaring
    mersenne_companion_trace_dyadic_power
    checked_mersenne_matrix_period_reduction
    checked_mersenne_dyadic_matrix_power_reduction};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Mersenne matrix source refinement depends on an oracle";
  val _ = if Thm_Deps.has_skip_proof checked
    then error "Skipped Mersenne matrix source refinement proof" else ();
\<close>

end
