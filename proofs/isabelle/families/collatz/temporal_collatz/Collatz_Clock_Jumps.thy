theory Collatz_Clock_Jumps
  imports "Shared_S_Arithmetic.Hensel_Cylinders" "HOL.Rat" "Shared_S_Arithmetic.S_Arithmetic_Skew"
begin

text \<open>Exact composition laws for a caller-supplied accelerated Collatz
valuation itinerary.  The valuation sum is an input to these laws: none of the
results discovers the next valuation or asserts logarithmic first-use cost.\<close>

record collatz_clock_block =
  odd_count :: nat
  valuation_sum :: nat
  affine_offset :: int

definition collatz_block_apply ::
    "collatz_clock_block \<Rightarrow> int \<Rightarrow> int \<Rightarrow> bool" where
  "collatz_block_apply B x y \<longleftrightarrow>
    (3::int)^(odd_count B)*x + affine_offset B =
      (2::int)^(valuation_sum B)*y"

definition collatz_block_compose ::
    "collatz_clock_block \<Rightarrow> collatz_clock_block \<Rightarrow>
      collatz_clock_block" where
  "collatz_block_compose first second = \<lparr>
    odd_count = odd_count first + odd_count second,
    valuation_sum = valuation_sum first + valuation_sum second,
    affine_offset = (3::int)^(odd_count second)*affine_offset first +
      (2::int)^(valuation_sum first)*affine_offset second \<rparr>"

definition collatz_valuation_atom :: "nat \<Rightarrow> collatz_clock_block" where
  "collatz_valuation_atom k = \<lparr>
    odd_count = 1, valuation_sum = k, affine_offset = 1 \<rparr>"

definition collatz_block_identity :: collatz_clock_block where
  "collatz_block_identity = \<lparr>
    odd_count = 0, valuation_sum = 0, affine_offset = 0 \<rparr>"

definition collatz_clock_projection ::
    "collatz_clock_block \<Rightarrow> int skew_transfer" where
  "collatz_clock_projection B = \<lparr>upper = (3::int)^odd_count B,
    offset = affine_offset B, lower = (2::int)^valuation_sum B\<rparr>"

lemma collatz_clock_projection_identity:
  "collatz_clock_projection collatz_block_identity = shared_skew_identity"
  by (simp add: collatz_clock_projection_def
      collatz_block_identity_def shared_skew_identity_def)

lemma collatz_clock_projection_compose:
  "collatz_clock_projection (collatz_block_compose first second) =
    shared_skew_then (collatz_clock_projection first) (collatz_clock_projection second)"
  by (cases first; cases second)
    (simp add: collatz_clock_projection_def collatz_block_compose_def
      shared_skew_then_def power_add algebra_simps)

lemma collatz_valuation_atom_exact:
  "collatz_block_apply (collatz_valuation_atom k) x y \<longleftrightarrow>
    3*x+1 = (2::int)^k*y"
  by (simp add: collatz_block_apply_def collatz_valuation_atom_def)

theorem collatz_block_compose:
  assumes "collatz_block_apply first x y"
      and "collatz_block_apply second y z"
  shows "collatz_block_apply (collatz_block_compose first second) x z"
proof -
  have first: "(3::int)^(odd_count first)*x + affine_offset first =
      (2::int)^(valuation_sum first)*y"
    using assms(1) by (simp add: collatz_block_apply_def)
  have second: "(3::int)^(odd_count second)*y + affine_offset second =
      (2::int)^(valuation_sum second)*z"
    using assms(2) by (simp add: collatz_block_apply_def)
  have "(3::int)^(odd_count first + odd_count second)*x +
      ((3::int)^(odd_count second)*affine_offset first +
       (2::int)^(valuation_sum first)*affine_offset second) =
      (3::int)^(odd_count second)*
        ((3::int)^(odd_count first)*x + affine_offset first) +
      (2::int)^(valuation_sum first)*affine_offset second"
    by (simp add: power_add algebra_simps)
  also have "... = (2::int)^(valuation_sum first)*
      ((3::int)^(odd_count second)*y + affine_offset second)"
    using first by (simp add: algebra_simps)
  also have "... = (2::int)^(valuation_sum first + valuation_sum second)*z"
    using second by (simp add: power_add algebra_simps)
  finally show ?thesis
    by (simp add: collatz_block_apply_def collatz_block_compose_def)
qed

lemma collatz_block_compose_identity [simp]:
  "collatz_block_compose collatz_block_identity B = B"
  "collatz_block_compose B collatz_block_identity = B"
  by (auto simp: collatz_block_compose_def collatz_block_identity_def)

lemma collatz_block_compose_associative:
  "collatz_block_compose (collatz_block_compose A B) C =
    collatz_block_compose A (collatz_block_compose B C)"
  by (cases A; cases B; cases C)
    (simp add: collatz_block_compose_def power_add algebra_simps)

corollary collatz_known_two_block_itinerary:
  assumes "3*x+1 = (2::int)^k*y"
      and "collatz_block_apply tail y z"
  shows "collatz_block_apply
    (collatz_block_compose (collatz_valuation_atom k) tail) x z"
  using assms collatz_block_compose collatz_valuation_atom_exact by blast

definition collatz_physical_ticks :: "collatz_clock_block \<Rightarrow> nat" where
  "collatz_physical_ticks B = odd_count B + valuation_sum B"

lemma collatz_frame_compose:
  "collatz_physical_ticks (collatz_block_compose first second) =
    collatz_physical_ticks first + collatz_physical_ticks second"
  by (simp add: collatz_physical_ticks_def collatz_block_compose_def)

definition inverse_three_coordinate :: "nat \<Rightarrow> int \<Rightarrow> rat" where
  "inverse_three_coordinate n x = of_int x / (3::rat)^n"

theorem inverse_three_clock_conjugacy:
  assumes step: "3*x+1 = (2::int)^k*y"
  shows "inverse_three_coordinate (Suc n) y =
    (inverse_three_coordinate n x + 1/(3::rat)^(Suc n)) / (2::rat)^k"
proof -
  have rational_step:
      "(of_int (3*x+1)::rat) = of_int ((2::int)^k*y)"
    using step by simp
  show ?thesis
    unfolding inverse_three_coordinate_def
    using rational_step by (simp add: field_simps power_Suc algebra_simps)
qed

text \<open>Publishing a completed affine output may rebase it onto a new spatial
suffix.  This equality removes representation history; it does not identify
distinct exact suffix occurrences.\<close>

theorem affine_occurrence_rebase:
  fixes A A0 b M :: int
  assumes "A0 \<noteq> 0" "A0 dvd A"
  shows "A*M+b = A0*((A div A0)*M + b div A0) + b mod A0"
proof -
  obtain scale where A: "A = A0*scale" using assms(2) by (auto simp: dvd_def)
  have quotient: "A div A0 = scale" using A assms(1) by simp
  have split: "b = A0*(b div A0) + b mod A0"
    using div_mult_mod_eq[of b A0] by (simp add: algebra_simps)
  show ?thesis using A quotient split by (simp add: algebra_simps)
qed

corollary affine_occurrence_rebase_canonical:
  fixes A A0 b M :: int
  assumes "0 < A0" "A0 dvd A"
  obtains M' r where
      "A*M+b = A0*M'+r" "0 \<le> r" "r < A0"
proof
  show "A*M+b = A0*((A div A0)*M + b div A0) + b mod A0"
    using affine_occurrence_rebase assms by simp
  show "0 \<le> b mod A0" using assms(1) by simp
  show "b mod A0 < A0" using assms(1) by simp
qed

text \<open>An authenticated normalized 0/1 word has a joint affine action for
its endpoint and the sum of its successor values.  This is the exact algebra
used by the finite `DyadicTerminalFieldAction` carrier: the word is supplied
and authenticated by its caller; these definitions do not discover parity or
establish a future Moore quotient.\<close>

record collatz_joint_dyadic_action =
  joint_dyadic_steps :: nat
  joint_dyadic_gain :: nat
  joint_dyadic_offset :: nat
  joint_dyadic_sum_gain :: nat
  joint_dyadic_sum_offset :: nat

definition collatz_joint_dyadic_identity :: collatz_joint_dyadic_action where
  "collatz_joint_dyadic_identity = \<lparr>
    joint_dyadic_steps = 0, joint_dyadic_gain = 1, joint_dyadic_offset = 0,
    joint_dyadic_sum_gain = 0, joint_dyadic_sum_offset = 0 \<rparr>"

definition collatz_joint_dyadic_atom :: "bool \<Rightarrow> collatz_joint_dyadic_action" where
  "collatz_joint_dyadic_atom odd_step =
    (if odd_step then
      \<lparr>joint_dyadic_steps = 1, joint_dyadic_gain = 3,
        joint_dyadic_offset = 1, joint_dyadic_sum_gain = 3,
        joint_dyadic_sum_offset = 1\<rparr>
     else
      \<lparr>joint_dyadic_steps = 1, joint_dyadic_gain = 1,
        joint_dyadic_offset = 0, joint_dyadic_sum_gain = 1,
        joint_dyadic_sum_offset = 0\<rparr>)"

definition collatz_joint_dyadic_then ::
    "collatz_joint_dyadic_action \<Rightarrow> collatz_joint_dyadic_action \<Rightarrow>
      collatz_joint_dyadic_action" where
  "collatz_joint_dyadic_then first second = \<lparr>
    joint_dyadic_steps = joint_dyadic_steps first + joint_dyadic_steps second,
    joint_dyadic_gain = joint_dyadic_gain second * joint_dyadic_gain first,
    joint_dyadic_offset = joint_dyadic_gain second * joint_dyadic_offset first +
      2^(joint_dyadic_steps first) * joint_dyadic_offset second,
    joint_dyadic_sum_gain =
      2^(joint_dyadic_steps second) * joint_dyadic_sum_gain first +
      joint_dyadic_sum_gain second * joint_dyadic_gain first,
    joint_dyadic_sum_offset =
      2^(joint_dyadic_steps second) * joint_dyadic_sum_offset first +
      joint_dyadic_sum_gain second * joint_dyadic_offset first +
      2^(joint_dyadic_steps first) * joint_dyadic_sum_offset second \<rparr>"

definition collatz_joint_dyadic_endpoint ::
    "collatz_joint_dyadic_action \<Rightarrow> rat \<Rightarrow> rat" where
  "collatz_joint_dyadic_endpoint A x =
    (of_nat (joint_dyadic_gain A) * x + of_nat (joint_dyadic_offset A)) /
      (2::rat)^joint_dyadic_steps A"

definition collatz_joint_dyadic_sum ::
    "collatz_joint_dyadic_action \<Rightarrow> rat \<Rightarrow> rat" where
  "collatz_joint_dyadic_sum A x =
    (of_nat (joint_dyadic_sum_gain A) * x +
      of_nat (joint_dyadic_sum_offset A)) /
      (2::rat)^joint_dyadic_steps A"

lemma collatz_joint_dyadic_left_identity [simp]:
  "collatz_joint_dyadic_then collatz_joint_dyadic_identity A = A"
  by (cases A)
    (simp add: collatz_joint_dyadic_then_def collatz_joint_dyadic_identity_def)

lemma collatz_joint_dyadic_right_identity [simp]:
  "collatz_joint_dyadic_then A collatz_joint_dyadic_identity = A"
  by (cases A)
    (simp add: collatz_joint_dyadic_then_def collatz_joint_dyadic_identity_def)

lemma collatz_joint_dyadic_then_associative:
  "collatz_joint_dyadic_then (collatz_joint_dyadic_then A B) C =
    collatz_joint_dyadic_then A (collatz_joint_dyadic_then B C)"
  by (cases A; cases B; cases C)
    (simp add: collatz_joint_dyadic_then_def power_add algebra_simps)

lemma collatz_joint_dyadic_endpoint_then:
  "collatz_joint_dyadic_endpoint (collatz_joint_dyadic_then A B) x =
    collatz_joint_dyadic_endpoint B (collatz_joint_dyadic_endpoint A x)"
  by (cases A; cases B)
    (simp add: collatz_joint_dyadic_endpoint_def collatz_joint_dyadic_then_def
      power_add field_simps algebra_simps)

lemma collatz_joint_dyadic_sum_then:
  "collatz_joint_dyadic_sum (collatz_joint_dyadic_then A B) x =
    collatz_joint_dyadic_sum A x +
      collatz_joint_dyadic_sum B (collatz_joint_dyadic_endpoint A x)"
  by (cases A; cases B)
    (simp add: collatz_joint_dyadic_endpoint_def collatz_joint_dyadic_sum_def
      collatz_joint_dyadic_then_def power_add field_simps algebra_simps)

definition collatz_normalized_bit_step :: "bool \<Rightarrow> rat \<Rightarrow> rat" where
  "collatz_normalized_bit_step odd_step x =
    (if odd_step then (3*x+1)/2 else x/2)"

fun collatz_joint_dyadic_word :: "bool list \<Rightarrow> collatz_joint_dyadic_action" where
  "collatz_joint_dyadic_word [] = collatz_joint_dyadic_identity"
| "collatz_joint_dyadic_word (odd_step # bits) =
    collatz_joint_dyadic_then (collatz_joint_dyadic_atom odd_step)
      (collatz_joint_dyadic_word bits)"

fun collatz_normalized_word_endpoint :: "bool list \<Rightarrow> rat \<Rightarrow> rat" where
  "collatz_normalized_word_endpoint [] x = x"
| "collatz_normalized_word_endpoint (odd_step # bits) x =
    collatz_normalized_word_endpoint bits
      (collatz_normalized_bit_step odd_step x)"

fun collatz_normalized_word_successor_sum :: "bool list \<Rightarrow> rat \<Rightarrow> rat" where
  "collatz_normalized_word_successor_sum [] x = 0"
| "collatz_normalized_word_successor_sum (odd_step # bits) x =
    collatz_normalized_bit_step odd_step x +
      collatz_normalized_word_successor_sum bits
        (collatz_normalized_bit_step odd_step x)"

lemma collatz_joint_dyadic_word_append:
  "collatz_joint_dyadic_word (first @ second) =
    collatz_joint_dyadic_then (collatz_joint_dyadic_word first)
      (collatz_joint_dyadic_word second)"
  by (induction first)
    (simp_all add: collatz_joint_dyadic_then_associative)

theorem collatz_joint_dyadic_word_endpoint_exact:
  "collatz_joint_dyadic_endpoint (collatz_joint_dyadic_word bits) x =
    collatz_normalized_word_endpoint bits x"
proof (induction bits arbitrary: x)
  case Nil
  then show ?case
    by (simp add: collatz_joint_dyadic_endpoint_def
        collatz_joint_dyadic_identity_def)
next
  case (Cons odd_step bits)
  have atom_endpoint:
    "collatz_joint_dyadic_endpoint (collatz_joint_dyadic_atom odd_step) x =
      collatz_normalized_bit_step odd_step x"
    by (cases odd_step)
      (simp_all add: collatz_joint_dyadic_endpoint_def
        collatz_joint_dyadic_atom_def collatz_normalized_bit_step_def)
  have tail:
    "collatz_joint_dyadic_endpoint (collatz_joint_dyadic_word bits)
        (collatz_normalized_bit_step odd_step x) =
      collatz_normalized_word_endpoint bits
        (collatz_normalized_bit_step odd_step x)"
    by (rule Cons.IH)
  show ?case
    using atom_endpoint tail
    by (simp only: collatz_joint_dyadic_word.simps
        collatz_joint_dyadic_endpoint_then collatz_normalized_word_endpoint.simps)
qed

theorem collatz_joint_dyadic_word_sum_exact:
  "collatz_joint_dyadic_sum (collatz_joint_dyadic_word bits) x =
    collatz_normalized_word_successor_sum bits x"
proof (induction bits arbitrary: x)
  case Nil
  then show ?case
    by (simp add: collatz_joint_dyadic_sum_def
        collatz_joint_dyadic_identity_def)
next
  case (Cons odd_step bits)
  have atom_endpoint:
    "collatz_joint_dyadic_endpoint (collatz_joint_dyadic_atom odd_step) x =
      collatz_normalized_bit_step odd_step x"
    by (cases odd_step)
      (simp_all add: collatz_joint_dyadic_endpoint_def
        collatz_joint_dyadic_atom_def collatz_normalized_bit_step_def)
  have atom_sum:
    "collatz_joint_dyadic_sum (collatz_joint_dyadic_atom odd_step) x =
      collatz_normalized_bit_step odd_step x"
    by (cases odd_step)
      (simp_all add: collatz_joint_dyadic_sum_def
        collatz_joint_dyadic_atom_def collatz_normalized_bit_step_def)
  have tail:
    "collatz_joint_dyadic_sum (collatz_joint_dyadic_word bits)
        (collatz_normalized_bit_step odd_step x) =
      collatz_normalized_word_successor_sum bits
        (collatz_normalized_bit_step odd_step x)"
    by (rule Cons.IH)
  show ?case
    using atom_endpoint atom_sum tail
    by (simp only: collatz_joint_dyadic_word.simps
        collatz_joint_dyadic_sum_then collatz_normalized_word_successor_sum.simps)
qed

text \<open>A radix-64 root digit is a dying forcing query.  A matching digit
removes six live precision bits; a mismatching digit has empty intersection
with the live cylinder.  The digit is supplied by the spatial occurrence.\<close>

theorem hensel_matched_prefix_skip:
  "prefix + (2::int)^h*x \<in>
      cylinder (q+h) (prefix + (2::int)^h*r) \<longleftrightarrow>
    x \<in> cylinder q r"
proof
  assume member: "prefix + (2::int)^h*x \<in>
      cylinder (q+h) (prefix + (2::int)^h*r)"
  then obtain k where equation:
    "prefix + (2::int)^h*x = prefix + (2::int)^h*r +
      (2::int)^(q+h)*k"
    by (auto simp: cylinder_def)
  have "(2::int)^h*x = (2::int)^h*(r+(2::int)^q*k)"
    using equation by (simp add: power_add algebra_simps)
  then have "x = r+(2::int)^q*k" by simp
  then show "x \<in> cylinder q r" by (auto simp: cylinder_def)
next
  assume "x \<in> cylinder q r"
  then obtain k where equation: "x = r+(2::int)^q*k"
    by (auto simp: cylinder_def)
  have "prefix + (2::int)^h*x = prefix + (2::int)^h*r +
      (2::int)^(q+h)*k"
    using equation by (simp add: power_add algebra_simps)
  then show "prefix + (2::int)^h*x \<in>
      cylinder (q+h) (prefix + (2::int)^h*r)"
    by (auto simp: cylinder_def)
qed

corollary hensel_radix64_k_digit_prefix_skip:
  "prefix + (64::int)^k*x \<in>
      cylinder (q+6*k) (prefix + (64::int)^k*r) \<longleftrightarrow>
    x \<in> cylinder q r"
  using hensel_matched_prefix_skip[of prefix "6*k" x q r]
  by (simp add: power_mult)

definition hensel_consume64 ::
    "nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> (nat \<times> int) option" where
  "hensel_consume64 q r d =
    (if 6 \<le> q \<and> d = r mod 64 then Some (q-6, r div 64) else None)"

theorem hensel_match_skip_six:
  assumes "hensel_consume64 q r d = Some successor"
  shows "d+64*x \<in> cylinder q r \<longleftrightarrow>
    x \<in> cylinder (fst successor) (snd successor)"
proof -
  have q: "6 \<le> q" and d: "d = r mod 64"
      and next_state: "successor = (q-6, r div 64)"
    using assms by (auto simp: hensel_consume64_def split: if_splits)
  show ?thesis
    using radix64_matching_digit_consumes_six[OF q d, of x]
    by (simp add: next_state)
qed

corollary hensel_two_matching_digits_skip_twelve:
  assumes first: "hensel_consume64 q r d = Some middle"
      and second: "hensel_consume64 (fst middle) (snd middle) e = Some successor"
  shows "d+64*(e+64*x) \<in> cylinder q r \<longleftrightarrow>
    x \<in> cylinder (fst successor) (snd successor)"
proof -
  have "d+64*(e+64*x) \<in> cylinder q r \<longleftrightarrow>
      e+64*x \<in> cylinder (fst middle) (snd middle)"
    using hensel_match_skip_six[OF first, of "e+64*x"] .
  also have "... \<longleftrightarrow> x \<in> cylinder (fst successor) (snd successor)"
    using hensel_match_skip_six[OF second, of x] .
  finally show ?thesis .
qed

text \<open>The mismatch theorem requires a canonical radix-64 digit.  This bounded
premise is explicit rather than silently treating an arbitrary integer
representative as a digit.\<close>

theorem hensel_canonical_mismatch_kills_forcing:
  assumes "6 \<le> q" "0 \<le> d" "d < 64" "d \<noteq> r mod 64"
  shows "cylinder q r \<inter> cylinder 6 d = {}"
proof -
  have "d \<notin> cylinder 6 r"
  proof
    assume "d \<in> cylinder 6 r"
    then obtain k where equation: "d = r + (2::int)^6*k"
      by (auto simp: cylinder_def)
    have "d = d mod 64" using assms(2,3) by simp
    also have "... = r mod 64" using equation by simp
    finally show False using assms(4) by contradiction
  qed
  then show ?thesis using radix64_mismatch_is_empty assms(1) by blast
qed

theorem radix64_mismatch_tangent:
  fixes d r u z :: int
  assumes depth: "e \<le> 6" and discrepancy: "d-r = (2::int)^e*u"
  shows "(d-r+64*z) div (2::int)^e = u + (2::int)^(6-e)*z"
proof -
  have six: "(2::int)^6 = (2::int)^e * (2::int)^(6-e)"
  proof -
    have "(2::int)^e * 2^(6-e) = 2^(e+(6-e))"
      by (simp only: power_add)
    also have "... = (2::int)^6" using depth by simp
    finally show ?thesis by (rule sym)
  qed
  have "d-r+64*z = (2::int)^e*(u+(2::int)^(6-e)*z)"
    using discrepancy six by (simp add: algebra_simps)
  then show ?thesis by simp
qed

definition radix64_occupancy :: "int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> bool" where
  "radix64_occupancy d r j \<longleftrightarrow> d \<in> cylinder j r"

definition radix64_curvature :: "int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> bool" where
  "radix64_curvature d r j \<longleftrightarrow>
    radix64_occupancy d r j \<and> \<not> radix64_occupancy d r (Suc j)"

lemma radix64_occupancy_downward:
  assumes "i \<le> j" "radix64_occupancy d r j"
  shows "radix64_occupancy d r i"
proof -
  obtain n where j: "j = i+n" using assms(1) by (metis le_iff_add)
  obtain k where d: "d = r+(2::int)^j*k"
    using assms(2) by (auto simp: radix64_occupancy_def cylinder_def)
  have "d = r+(2::int)^i*((2::int)^n*k)"
    using d by (simp add: j power_add algebra_simps)
  then show ?thesis by (auto simp: radix64_occupancy_def cylinder_def)
qed

theorem radix64_curvature_is_one_hot:
  assumes "radix64_curvature d r e" "radix64_curvature d r j"
  shows "j=e"
proof (rule ccontr)
  assume "j \<noteq> e"
  consider (less) "j < e" | (greater) "e < j" using \<open>j \<noteq> e\<close> by arith
  then show False
  proof cases
    case less
    have "Suc j \<le> e" using less by arith
    then have "radix64_occupancy d r (Suc j)"
      using assms(1) radix64_occupancy_downward
      by (auto simp: radix64_curvature_def)
    then show False using assms(2) by (simp add: radix64_curvature_def)
  next
    case greater
    have "Suc e \<le> j" using greater by arith
    then have "radix64_occupancy d r (Suc e)"
      using assms(2) radix64_occupancy_downward
      by (auto simp: radix64_curvature_def)
    then show False using assms(1) by (simp add: radix64_curvature_def)
  qed
qed

theorem radix64_match_has_zero_curvature:
  assumes match: "radix64_occupancy d r 6" and "j < 6"
  shows "\<not> radix64_curvature d r j"
proof -
  have "Suc j \<le> 6" using assms(2) by arith
  then have "radix64_occupancy d r (Suc j)"
    using match radix64_occupancy_downward by blast
  then show ?thesis by (simp add: radix64_curvature_def)
qed

theorem normalized_cylinder_jet_compose:
  fixes W a1 V a2 Z :: rat
  assumes first: "W+a1 = (2::rat)^k1*V"
      and second: "V+a2 = (2::rat)^k2*Z"
  shows "W+(a1+(2::rat)^k1*a2) = (2::rat)^(k1+k2)*Z"
proof -
  have "W+(a1+(2::rat)^k1*a2) = (2::rat)^k1*(V+a2)"
    using first by (simp add: algebra_simps)
  also have "... = (2::rat)^k1*((2::rat)^k2*Z)" using second by simp
  also have "... = (2::rat)^(k1+k2)*Z"
    by (simp add: power_add algebra_simps)
  finally show ?thesis .
qed

theorem normalized_target_rebase_linear:
  fixes W a V h :: rat
  assumes base: "W+a = (2::rat)^k*V"
  shows "(W+(2::rat)^k*h+a)/(2::rat)^k = V+h"
proof -
  have "W+(2::rat)^k*h+a = (2::rat)^k*(V+h)"
    using base by (simp add: algebra_simps)
  then show ?thesis by simp
qed

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms collatz_clock_projection_identity collatz_clock_projection_compose collatz_valuation_atom_exact collatz_block_compose
      collatz_block_compose_identity collatz_block_compose_associative
      collatz_known_two_block_itinerary collatz_frame_compose
      inverse_three_clock_conjugacy
      affine_occurrence_rebase affine_occurrence_rebase_canonical
      hensel_matched_prefix_skip hensel_radix64_k_digit_prefix_skip
      hensel_match_skip_six hensel_two_matching_digits_skip_twelve
      hensel_canonical_mismatch_kills_forcing
      radix64_mismatch_tangent radix64_occupancy_downward
      radix64_curvature_is_one_hot radix64_match_has_zero_curvature
      normalized_cylinder_jet_compose normalized_target_rebase_linear
      collatz_joint_dyadic_left_identity collatz_joint_dyadic_right_identity
      collatz_joint_dyadic_then_associative
      collatz_joint_dyadic_word_append
      collatz_joint_dyadic_endpoint_then collatz_joint_dyadic_sum_then
      collatz_joint_dyadic_word_endpoint_exact collatz_joint_dyadic_word_sum_exact}) then ()
    else error "Collatz clock-jump proof depends on an oracle";
\<close>

end
