theory Dyadic_Parity_Inverse_Arithmetic
  imports "Source_Cache_Integration.Collatz_Parity_Shift_Germ"
    "Antihydra.Antihydra_Family_Iteration"
begin

text \<open>Executable arithmetic model of the shared odd-gain inverse_result loop.
The word is in chronological, least-significant-bit-first order.  The two
branch gains and offsets are parameters: Collatz, Antihydra arithmetic and
the centered Mahler source instantiate different laws.  Inverse constants
must satisfy the checked modular-inverse_scale equations at the demanded width.\<close>

fun dyadic_forward_coefficients ::
    "(bool \<Rightarrow> int) \<Rightarrow> (bool \<Rightarrow> int) \<Rightarrow>
      nat \<Rightarrow> (int \<times> int) \<Rightarrow> bool list \<Rightarrow> int \<times> int" where
  "dyadic_forward_coefficients gain branch_offset position coefficients [] =
      coefficients"
| "dyadic_forward_coefficients gain branch_offset position (scale,forward_offset)
      (branch # rest) =
    dyadic_forward_coefficients gain branch_offset (Suc position)
      (gain branch * scale,
       gain branch * forward_offset + (2::int)^position * branch_offset branch) rest"

fun dyadic_inverse_loop ::
    "int \<Rightarrow> (bool \<Rightarrow> int) \<Rightarrow> (bool \<Rightarrow> int) \<Rightarrow>
      nat \<Rightarrow> (int \<times> int) \<Rightarrow> bool list \<Rightarrow> int \<times> int" where
  "dyadic_inverse_loop modulus inverse_gain branch_offset position state [] = state"
| "dyadic_inverse_loop modulus inverse_gain branch_offset position (inverse_scale,inverse_residue)
      (branch # rest) =
    (let next_unit = (inverse_scale * inverse_gain branch) mod modulus;
         next_residue =
           (inverse_residue - (2::int)^position * branch_offset branch * next_unit)
             mod modulus
     in dyadic_inverse_loop modulus inverse_gain branch_offset (Suc position)
          (next_unit,next_residue) rest)"

lemma dyadic_inverse_one_step_unit:
  assumes "(modulus::int) > 1"
    "(gain * inverse_gain) mod modulus = 1"
    "(scale * inverse_scale) mod modulus = 1"
  shows "(gain * scale * ((inverse_scale * inverse_gain) mod modulus))
      mod modulus = 1"
proof -
  have "(gain * scale * ((inverse_scale * inverse_gain) mod modulus))
      mod modulus = (gain * scale * (inverse_scale * inverse_gain)) mod modulus"
    by (rule mod_mult_right_eq)
  also have "... = ((gain * inverse_gain) * (scale * inverse_scale)) mod modulus"
    by (simp only: mult_ac)
  also have "... = 1"
  proof -
    have "((gain * inverse_gain) mod modulus *
        ((scale * inverse_scale) mod modulus)) mod modulus = 1"
      using assms by simp
    then show ?thesis by (simp only: mod_mult_eq)
  qed
  finally show ?thesis .
qed

lemma dyadic_inverse_one_step_residue:
  assumes "modulus > 1"
    "(gain * scale * next_unit) mod modulus = 1"
    "(scale * inverse_residue + forward_offset) mod modulus = 0"
  shows "(gain * scale *
      ((inverse_residue - (2::int)^position * branch_offset * next_unit) mod modulus)
      + gain * forward_offset + (2::int)^position * branch_offset) mod modulus = 0"
proof -
  let ?delta = "(2::int)^position * branch_offset * next_unit"
  let ?t = "(2::int)^position * branch_offset"
  let ?a = "gain * scale * ((inverse_residue - ?delta) mod modulus)"
  let ?a' = "gain * scale * (inverse_residue - ?delta)"
  have inner: "?a mod modulus = ?a' mod modulus"
    by (rule mod_mult_right_eq)
  have added: "(?a + gain * forward_offset + ?t) mod modulus =
      (?a' + gain * forward_offset + ?t) mod modulus"
  proof -
    have "(?a + gain * forward_offset) mod modulus =
        (?a' + gain * forward_offset) mod modulus"
      by (rule mod_add_cong[OF inner refl])
    then show ?thesis by (rule mod_add_cong[OF _ refl])
  qed
  have polynomial: "?a' + gain * forward_offset + ?t =
      gain * (scale * inverse_residue + forward_offset) +
      ?t * (1 - gain * scale * next_unit)"
    by (simp add: algebra_simps)
  have "(?a + gain * forward_offset + ?t) mod modulus =
    (gain * (scale * inverse_residue + forward_offset) +
      ?t * (1 - gain * scale * next_unit)) mod modulus"
    using added polynomial by simp
  also have "... = 0"
  proof -
    have base_zero: "(gain * (scale * inverse_residue + forward_offset))
        mod modulus = 0"
    proof -
      have "(gain * ((scale * inverse_residue + forward_offset) mod modulus))
          mod modulus = 0"
        using assms(3) by simp
      then show ?thesis by (simp only: mod_mult_right_eq)
    qed
    have unit_zero: "(1 - gain * scale * next_unit)
        mod modulus = 0"
    proof -
      have "((1 mod modulus) -
          ((gain * scale * next_unit) mod modulus)) mod modulus = 0"
        using assms(1,2) by simp
      then show ?thesis by (simp only: mod_diff_eq)
    qed
    have tail_zero: "(?t * (1 - gain * scale * next_unit))
        mod modulus = 0"
    proof -
      have "(?t * ((1 - gain * scale * next_unit) mod modulus))
          mod modulus = 0"
        using unit_zero by simp
      then show ?thesis by (simp only: mod_mult_right_eq)
    qed
    have "((gain * (scale * inverse_residue + forward_offset)) mod modulus +
        (?t * (1 - gain * scale * next_unit)) mod modulus)
        mod modulus = 0"
      using base_zero tail_zero by simp
    then show ?thesis by (simp only: mod_add_eq)
  qed
  finally show ?thesis .
qed

theorem dyadic_inverse_loop_invariant:
  assumes "modulus > 1"
    "\<And>branch. (gain branch * inverse_gain branch) mod modulus = 1"
    "(scale * inverse_scale) mod modulus = 1"
    "(scale * inverse_residue + forward_offset) mod modulus = 0"
  shows "(fst (dyadic_forward_coefficients gain branch_offset position
        (scale,forward_offset) bits) *
      fst (dyadic_inverse_loop modulus inverse_gain branch_offset position
        (inverse_scale,inverse_residue) bits)) mod modulus = 1 \<and>
    (fst (dyadic_forward_coefficients gain branch_offset position
        (scale,forward_offset) bits) *
      snd (dyadic_inverse_loop modulus inverse_gain branch_offset position
        (inverse_scale,inverse_residue) bits) +
      snd (dyadic_forward_coefficients gain branch_offset position
        (scale,forward_offset) bits)) mod modulus = 0"
  using assms(3,4)
proof (induction bits arbitrary: position scale forward_offset inverse_scale inverse_residue)
  case Nil
  then show ?case by simp
next
  case (Cons branch rest)
  let ?next_unit = "(inverse_scale * inverse_gain branch) mod modulus"
  let ?next_residue =
    "(inverse_residue - (2::int)^position * branch_offset branch * ?next_unit) mod modulus"
  let ?next_scale = "gain branch * scale"
  let ?next_constant =
    "gain branch * forward_offset + (2::int)^position * branch_offset branch"
  have inverse_scale: "(?next_scale * ?next_unit) mod modulus = 1"
    using dyadic_inverse_one_step_unit[OF assms(1)
      assms(2)[of branch] Cons.prems(1)] by simp
  have inverse_residue: "(?next_scale * ?next_residue + ?next_constant)
      mod modulus = 0"
    using dyadic_inverse_one_step_residue
      [where position=position and branch_offset="branch_offset branch",
        OF assms(1) inverse_scale Cons.prems(2)]
    by (simp add: algebra_simps)
  note tail = Cons.IH
    [where position="Suc position" and scale="?next_scale"
      and forward_offset="?next_constant" and inverse_scale="?next_unit"
      and inverse_residue="?next_residue", OF inverse_scale inverse_residue]
  show ?case using tail
    by (simp add: Let_def)
qed

lemma dyadic_inverse_loop_residue_bounded:
  assumes "modulus > 0" "0 \<le> inverse_residue" "inverse_residue < modulus"
  shows "0 \<le> snd (dyadic_inverse_loop modulus inverse_gain branch_offset
      position (inverse_scale,inverse_residue) bits) \<and>
    snd (dyadic_inverse_loop modulus inverse_gain branch_offset
      position (inverse_scale,inverse_residue) bits) < modulus"
  using assms(2,3)
proof (induction bits arbitrary: position inverse_scale inverse_residue)
  case Nil
  then show ?case by simp
next
  case (Cons branch rest)
  let ?next_unit = "(inverse_scale * inverse_gain branch) mod modulus"
  let ?next_residue =
    "(inverse_residue - (2::int)^position * branch_offset branch * ?next_unit) mod modulus"
  have bounds: "0 \<le> ?next_residue" "?next_residue < modulus"
    using assms(1) by simp_all
  show ?case using Cons.IH
    [where position="Suc position" and inverse_scale="?next_unit"
      and inverse_residue="?next_residue", OF bounds]
    by (simp add: Let_def)
qed

lemma dyadic_inverse_modular_cancel:
  assumes "(modulus::int) > 1"
    "(scale * inverse_scale) mod modulus = 1"
    "(scale * source + forward_offset) mod modulus = 0"
    "(scale * inverse_residue + forward_offset) mod modulus = 0"
  shows "source mod modulus = inverse_residue mod modulus"
proof -
  have same_scaled: "(scale * source) mod modulus =
      (scale * inverse_residue) mod modulus"
  proof -
    have equal_sums: "(scale * source + forward_offset) mod modulus =
        (scale * inverse_residue + forward_offset) mod modulus"
      using assms(3,4) by simp
    have "((scale * source + forward_offset) - forward_offset) mod modulus =
        ((scale * inverse_residue + forward_offset) - forward_offset) mod modulus"
      by (rule mod_diff_cong[OF equal_sums refl])
    then show ?thesis by simp
  qed
  have inverse_scale: "(inverse_scale * scale) mod modulus = 1"
    using assms(2) by (simp add: mult.commute)
  have "source mod modulus =
      (inverse_scale * scale * source) mod modulus"
    using mod_mult_left_eq[of "inverse_scale * scale" modulus source] inverse_scale
    by simp
  also have "... = (inverse_scale * scale * inverse_residue) mod modulus"
  proof -
    have "(inverse_scale * (scale * source)) mod modulus =
        (inverse_scale * (scale * inverse_residue)) mod modulus"
      by (rule mod_mult_cong[OF refl same_scaled])
    then show ?thesis by (simp add: mult.assoc)
  qed
  also have "... = inverse_residue mod modulus"
    using mod_mult_left_eq[of "inverse_scale * scale" modulus inverse_residue] inverse_scale
    by simp
  finally show ?thesis .
qed

text \<open>The following is the direct loop-refinement interface.  A
source-bound forward equation is needed separately for a physical or Mahler
cursor; supplying arbitrary bits without that equation does not authorize an
endpoint value.\<close>

theorem dyadic_inverse_loop_source_residue:
  assumes "modulus > 1"
    "\<And>branch. (gain branch * inverse_gain branch) mod modulus = 1"
    "forward_result = dyadic_forward_coefficients gain branch_offset 0 (1,0) bits"
    "inverse_result = dyadic_inverse_loop modulus inverse_gain branch_offset 0 (1,0) bits"
    "(fst forward_result * source + snd forward_result) mod modulus = 0"
  shows "snd inverse_result = source mod modulus"
proof -
  have initial_unit: "((1::int) * 1) mod modulus = 1"
    using assms(1) by simp
  have initial_residue: "((1::int) * 0 + 0) mod modulus = 0"
    by simp
  have inv: "(fst forward_result * fst inverse_result) mod modulus = 1"
    "(fst forward_result * snd inverse_result + snd forward_result) mod modulus = 0"
    using dyadic_inverse_loop_invariant
      [where modulus=modulus and gain=gain and inverse_gain=inverse_gain
        and branch_offset=branch_offset and position=0 and scale=1 and forward_offset=0
        and inverse_scale=1 and inverse_residue=0 and bits=bits,
        OF assms(1,2) initial_unit initial_residue]
      assms(3,4) by (simp_all add: assms(3,4))
  have residue_bound: "snd inverse_result mod modulus = snd inverse_result"
    using dyadic_inverse_loop_residue_bounded
      [where modulus=modulus and inverse_residue=0 and
        inverse_gain=inverse_gain and branch_offset=branch_offset and
        position=0 and inverse_scale=1 and bits=bits]
      assms(1,4) by auto
  show ?thesis
    using dyadic_inverse_modular_cancel[OF assms(1) inv(1)
      assms(5) inv(2)] residue_bound by simp
qed

text \<open>A generated parity word is admitted only through its actual
source orbit.  The following trace invariant ties the executable forward
coefficient fold to that orbit, rather than assuming a supplied word is
source reachable.\<close>

lemma dyadic_forward_coefficients_trace:
  fixes orbit_value :: "nat \<Rightarrow> int"
  assumes initial: "(2::int)^position * orbit_value 0 =
      scale * source + forward_offset"
    and transition: "\<And>i. i < length bits \<Longrightarrow>
      2 * orbit_value (Suc i) =
      gain (bits ! i) * orbit_value i + branch_offset (bits ! i)"
  shows "(2::int)^(position + length bits) * orbit_value (length bits) =
      fst (dyadic_forward_coefficients gain branch_offset position
        (scale,forward_offset) bits) * source +
      snd (dyadic_forward_coefficients gain branch_offset position
        (scale,forward_offset) bits)"
  using initial transition
proof (induction bits arbitrary: orbit_value position scale forward_offset)
  case Nil
  then show ?case by simp
next
  case (Cons branch rest)
  have first: "2 * orbit_value 1 =
      gain branch * orbit_value 0 + branch_offset branch"
    using Cons.prems(2)[of 0] by simp
  have next_initial: "(2::int)^Suc position * orbit_value 1 =
      (gain branch * scale) * source +
      (gain branch * forward_offset +
        (2::int)^position * branch_offset branch)"
  proof -
    have "(2::int)^Suc position * orbit_value 1 =
        (2::int)^position * (2 * orbit_value 1)"
      by (simp add: power_Suc algebra_simps)
    also have "... = (2::int)^position *
        (gain branch * orbit_value 0 + branch_offset branch)"
      using first by simp
    also have "... = gain branch * (scale * source + forward_offset) +
        (2::int)^position * branch_offset branch"
      using Cons.prems(1) by (simp add: algebra_simps)
    also have "... = (gain branch * scale) * source +
        (gain branch * forward_offset +
          (2::int)^position * branch_offset branch)"
      by (simp add: algebra_simps)
    finally show ?thesis .
  qed
  have tail_transition: "\<And>i. i < length rest \<Longrightarrow>
      2 * (\<lambda>j. orbit_value (Suc j)) (Suc i) =
      gain (rest ! i) * (\<lambda>j. orbit_value (Suc j)) i +
      branch_offset (rest ! i)"
    using Cons.prems(2) by simp
  have tail: "(2::int)^(Suc position + length rest) *
      orbit_value (Suc (length rest)) =
      fst (dyadic_forward_coefficients gain branch_offset (Suc position)
        (gain branch * scale,
         gain branch * forward_offset +
           (2::int)^position * branch_offset branch) rest) * source +
      snd (dyadic_forward_coefficients gain branch_offset (Suc position)
        (gain branch * scale,
         gain branch * forward_offset +
           (2::int)^position * branch_offset branch) rest)"
  proof (rule Cons.IH[where orbit_value="\<lambda>i. orbit_value (Suc i)"
      and position="Suc position" and scale="gain branch * scale" and
      forward_offset="gain branch * forward_offset +
        (2::int)^position * branch_offset branch"])
    show "(2::int)^Suc position *
        (\<lambda>i. orbit_value (Suc i)) 0 =
        (gain branch * scale) * source +
        (gain branch * forward_offset +
          (2::int)^position * branch_offset branch)"
      using next_initial by simp
    show "\<And>i. i < length rest \<Longrightarrow>
        2 * (\<lambda>j. orbit_value (Suc j)) (Suc i) =
        gain (rest ! i) * (\<lambda>j. orbit_value (Suc j)) i +
        branch_offset (rest ! i)"
      using tail_transition .
  qed
  show ?case using tail by simp
qed

lemma dyadic_source_word_nth_actual:
  assumes "i < n"
  shows "dyadic_source_word step label source n ! i =
      label (dyadic_source_orbit step source i)"
  using assms
proof (induction i arbitrary: source n)
  case 0
  then obtain m where n: "n = Suc m" by (cases n) auto
  then show ?case by simp
next
  case (Suc i)
  then obtain m where n: "n = Suc m" by (cases n) auto
  have smaller: "i < m" using Suc.prems n by simp
  note tail = Suc.IH[where source="step source" and n=m, OF smaller]
  show ?case using tail by (simp add: n)
qed

lemma dyadic_source_orbit_step_at_end:
  "dyadic_source_orbit step source (Suc i) =
    step (dyadic_source_orbit step source i)"
  using dyadic_source_orbit_add[of step source i 1] by simp

theorem dyadic_generated_word_forward_equation:
  fixes gain branch_offset :: "bool \<Rightarrow> int"
  assumes local: "\<And>x. 2 * int (step x) =
      gain (label x) * int x + branch_offset (label x)"
  shows "(2::int)^n * int (dyadic_source_orbit step source n) =
      fst (dyadic_forward_coefficients gain branch_offset 0 (1,0)
        (dyadic_source_word step label source n)) * int source +
      snd (dyadic_forward_coefficients gain branch_offset 0 (1,0)
        (dyadic_source_word step label source n))"
proof -
  let ?bits = "dyadic_source_word step label source n"
  have initial: "(2::int)^0 *
      int (dyadic_source_orbit step source 0) = 1 * int source + 0"
    by simp
  have transition: "\<And>i. i < length ?bits \<Longrightarrow>
      2 * int (dyadic_source_orbit step source (Suc i)) =
      gain (?bits ! i) * int (dyadic_source_orbit step source i) +
      branch_offset (?bits ! i)"
  proof -
    fix i assume bound: "i < length ?bits"
    have within: "i < n" using bound by simp
    have tag: "?bits ! i = label (dyadic_source_orbit step source i)"
      by (rule dyadic_source_word_nth_actual[OF within])
    have local_step: "2 * int (step (dyadic_source_orbit step source i)) =
        gain (label (dyadic_source_orbit step source i)) *
          int (dyadic_source_orbit step source i) +
        branch_offset (label (dyadic_source_orbit step source i))"
      by (rule local)
    show "2 * int (dyadic_source_orbit step source (Suc i)) =
        gain (?bits ! i) * int (dyadic_source_orbit step source i) +
        branch_offset (?bits ! i)"
      by (simp only: dyadic_source_orbit_step_at_end tag local_step)
  qed
  show ?thesis
    using dyadic_forward_coefficients_trace
      [where orbit_value="\<lambda>i. int (dyadic_source_orbit step source i)"
        and position=0 and scale=1 and forward_offset=0 and
        source="int source" and gain=gain and branch_offset=branch_offset
        and bits="?bits", OF initial transition]
    by simp
qed

lemma collatz_normalized_signed_step:
  "2 * int (collatz_normalized_step x) =
    (if odd x then (3::int) else 1) * int x +
    (if odd x then 1 else 0)"
proof (cases "even x")
  case True
  then have "2 * collatz_normalized_step x = x"
    using normalized_step_even[of x] by simp
  with True show ?thesis by simp
next
  case False
  then have "2 * collatz_normalized_step x = 3*x+1"
    using normalized_step_odd[of x] by simp
  with False show ?thesis by simp
qed

corollary collatz_generated_q_forward_equation:
  "(2::int)^n * int (dyadic_source_orbit collatz_normalized_step
      source n) =
    fst (dyadic_forward_coefficients
      (\<lambda>b. if b then 3 else 1) (\<lambda>b. if b then 1 else 0)
      0 (1,0) (collatz_qprefix n source)) * int source +
    snd (dyadic_forward_coefficients
      (\<lambda>b. if b then 3 else 1) (\<lambda>b. if b then 1 else 0)
      0 (1,0) (collatz_qprefix n source))"
  using dyadic_generated_word_forward_equation
    [where step=collatz_normalized_step and label=odd and
      gain="\<lambda>b. if b then 3 else 1" and
      branch_offset="\<lambda>b. if b then 1 else 0" and
      source=source and n=n, OF collatz_normalized_signed_step]
  by (simp add: collatz_qprefix_def)

text \<open>The production D8 table computes these forward coefficients from
the low eight source bits. The source-lift theorem supplies every higher
fiber; enumeration of a few lifted endpoints is only a differential check.
This theorem does not refine Python table ownership or give a bound on the
number of D8 applications needed by an arbitrary source.\<close>

definition collatz_d8_coefficients :: "nat \<Rightarrow> int \<times> int" where
  "collatz_d8_coefficients residue = dyadic_forward_coefficients
    (\<lambda>b. if b then 3 else 1) (\<lambda>b. if b then 1 else 0)
    0 (1,0) (collatz_qprefix 8 residue)"

corollary collatz_d8_all_source_fibers:
  "256 * int (dyadic_source_orbit collatz_normalized_step source 8) =
    fst (collatz_d8_coefficients (source mod 256)) * int source +
    snd (collatz_d8_coefficients (source mod 256))"
proof -
  have low: "collatz_qprefix 8 (source mod 256) = collatz_qprefix 8 source"
    using collatz_qprefix_low[of 8 source] by simp
  show ?thesis
    using collatz_generated_q_forward_equation[of 8 source]
    by (simp add: collatz_d8_coefficients_def low)
qed

lemma antihydra_signed_step_by_parity:
  "2 * int (antihydra_family_step x) =
    (3::int) * int x + (if odd x then -1 else 0)"
proof -
  have parity: "int (x mod 2) = (if odd x then 1 else 0)"
    by (cases "odd x")
      (simp_all add: odd_iff_mod_2_eq_one even_iff_mod_2_eq_zero)
  show ?thesis
    using antihydra_family_step_skew_equation[of x] parity by simp
qed

lemma antihydra_bool_word_generated:
  "dyadic_source_word antihydra_family_step odd source n =
    map odd (antihydra_family_bits source n)"
  by (induction n arbitrary: source) simp_all

lemma antihydra_orbit_is_dyadic_source_orbit:
  "antihydra_family_orbit source n =
    dyadic_source_orbit antihydra_family_step source n"
  by (induction n arbitrary: source) simp_all

corollary antihydra_generated_word_forward_equation:
  "(2::int)^n * int (antihydra_family_orbit source n) =
    fst (dyadic_forward_coefficients
      (\<lambda>_. 3) (\<lambda>b. if b then -1 else 0) 0 (1,0)
      (map odd (antihydra_family_bits source n))) * int source +
    snd (dyadic_forward_coefficients
      (\<lambda>_. 3) (\<lambda>b. if b then -1 else 0) 0 (1,0)
      (map odd (antihydra_family_bits source n)))"
  using dyadic_generated_word_forward_equation
    [where step=antihydra_family_step and label=odd and
      gain="\<lambda>_. 3" and branch_offset="\<lambda>b. if b then -1 else 0"
      and source=source and n=n, OF antihydra_signed_step_by_parity]
  by (simp add: antihydra_bool_word_generated
      antihydra_orbit_is_dyadic_source_orbit)

text \<open>The executable inverse returns the low source residue for an
actual generated word.  The modular inverse units are explicit parameters:
the runtime's unit validation must discharge them.  This theorem does not
construct the word, a physical-time selector, or an exterior blank guard.\<close>

theorem dyadic_generated_word_inverse_residue:
  fixes gain branch_offset inverse_gain :: "bool \<Rightarrow> int"
  assumes positive: "0 < n"
    and local: "\<And>x. 2 * int (step x) =
      gain (label x) * int x + branch_offset (label x)"
    and units: "\<And>b. (gain b * inverse_gain b) mod (2::int)^n = 1"
  shows "snd (dyadic_inverse_loop ((2::int)^n) inverse_gain
      branch_offset 0 (1,0)
      (dyadic_source_word step label source n)) =
    int source mod (2::int)^n"
proof -
  let ?m = "(2::int)^n"
  let ?bits = "dyadic_source_word step label source n"
  let ?forward = "dyadic_forward_coefficients gain branch_offset
    0 (1,0) ?bits"
  let ?inverse = "dyadic_inverse_loop ?m inverse_gain branch_offset
    0 (1,0) ?bits"
  have m_gt_one: "1 < ?m"
  proof -
    obtain k where n: "n = Suc k"
      using positive by (cases n) auto
    have power_pos: "0 < (2::int)^k" by simp
    show ?thesis using power_pos by (simp add: n power_Suc; linarith)
  qed
  have source_equation: "?m * int (dyadic_source_orbit step source n) =
      fst ?forward * int source + snd ?forward"
    by (rule dyadic_generated_word_forward_equation[OF local])
  have zero: "(fst ?forward * int source + snd ?forward) mod ?m = 0"
    by (simp only: source_equation[symmetric] mod_mult_self1_is_0)
  show ?thesis
    using dyadic_inverse_loop_source_residue
      [where modulus="?m" and gain=gain and inverse_gain=inverse_gain
        and branch_offset=branch_offset and bits="?bits" and
        forward_result="?forward" and inverse_result="?inverse" and
        source="int source", OF m_gt_one units refl refl zero]
    by simp
qed

corollary collatz_generated_inverse_residue:
  assumes "0 < n"
    "\<And>b. ((if b then (3::int) else 1) * inverse_gain b)
      mod 2^n = 1"
  shows "snd (dyadic_inverse_loop ((2::int)^n) inverse_gain
      (\<lambda>b. if b then 1 else 0) 0 (1,0)
      (collatz_qprefix n source)) = int source mod (2::int)^n"
  using dyadic_generated_word_inverse_residue
    [where step=collatz_normalized_step and label=odd and
      gain="\<lambda>b. if b then 3 else 1" and
      branch_offset="\<lambda>b. if b then 1 else 0" and
      inverse_gain=inverse_gain and source=source and n=n,
      OF assms(1) collatz_normalized_signed_step assms(2)]
  by (simp add: collatz_qprefix_def)

corollary antihydra_generated_inverse_residue:
  assumes "0 < n" "\<And>b. ((3::int) * inverse_gain b) mod 2^n = 1"
  shows "snd (dyadic_inverse_loop ((2::int)^n) inverse_gain
      (\<lambda>b. if b then -1 else 0) 0 (1,0)
      (map odd (antihydra_family_bits source n))) =
    int source mod (2::int)^n"
  using dyadic_generated_word_inverse_residue
    [where step=antihydra_family_step and label=odd and
      gain="\<lambda>_. 3" and branch_offset="\<lambda>b. if b then -1 else 0"
      and inverse_gain=inverse_gain and source=source and n=n,
      OF assms(1) antihydra_signed_step_by_parity assms(2)]
  by (simp add: antihydra_bool_word_generated)

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms dyadic_inverse_one_step_unit
      dyadic_inverse_one_step_residue dyadic_inverse_loop_invariant
      dyadic_inverse_loop_residue_bounded
      dyadic_inverse_modular_cancel dyadic_inverse_loop_source_residue
      dyadic_forward_coefficients_trace dyadic_source_word_nth_actual
      dyadic_source_orbit_step_at_end
      dyadic_generated_word_forward_equation
      collatz_normalized_signed_step collatz_generated_q_forward_equation
      collatz_d8_all_source_fibers
      antihydra_signed_step_by_parity antihydra_bool_word_generated
      antihydra_orbit_is_dyadic_source_orbit
      antihydra_generated_word_forward_equation
      dyadic_generated_word_inverse_residue
      collatz_generated_inverse_residue antihydra_generated_inverse_residue})
    then () else error "Dyadic inverse-loop proof depends on an oracle";
\<close>

end
