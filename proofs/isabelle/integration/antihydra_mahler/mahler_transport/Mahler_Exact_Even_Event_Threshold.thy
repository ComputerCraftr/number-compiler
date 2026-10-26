theory Mahler_Exact_Even_Event_Threshold
  imports Mahler_Source_Event_Safety
    Mahler_Safety_Cylinders.Mahler_Cyclotomic_Boundary
begin

text \<open>The cold scheduler may use a logarithm to propose an even-run
failure position.  The accepted event is the exact integer comparison below.
This theory proves the comparison against the source-selected fractional
guard; it gives no authority to the floating-point proposal itself.\<close>

definition mahler_even_event_impossible :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "mahler_even_event_impossible numerator denominator ticks \<longleftrightarrow>
    2 * numerator * 3^ticks \<ge> denominator * 2^ticks"

lemma mahler_even_event_impossible_mono:
  "ticks \<le> later \<Longrightarrow>
    mahler_even_event_impossible numerator denominator ticks \<Longrightarrow>
    mahler_even_event_impossible numerator denominator later"
proof (induction later arbitrary: ticks)
  case 0
  then show ?case by simp
next
  case (Suc later)
  have bound: "ticks \<le> Suc later" using Suc.prems(1) .
  have bad: "mahler_even_event_impossible numerator denominator ticks"
    using Suc.prems(2) .
  show ?case
  proof (cases "ticks \<le> later")
    case True
    have prior: "mahler_even_event_impossible numerator denominator later"
      by (rule Suc.IH[OF True bad])
    have compare:
      "denominator * 2^later \<le> 2 * numerator * 3^later"
      using prior by (simp add: mahler_even_event_impossible_def)
    have twice:
      "2 * (denominator * 2^later) \<le>
        2 * (2 * numerator * 3^later)"
      using compare by arith
    have triple:
      "2 * (2 * numerator * 3^later) \<le>
        3 * (2 * numerator * 3^later)"
      by (simp; arith)
    have scaled:
      "2 * numerator * 3^(Suc later) \<ge>
        denominator * 2^(Suc later)"
      using order_trans[OF twice triple]
      by (simp only: power_Suc; simp add: algebra_simps)
    show ?thesis using scaled
      by (simp add: mahler_even_event_impossible_def)
  next
    case False
      then have "ticks = Suc later" using bound by arith
      then show ?thesis using bad by simp
    qed
qed

lemma mahler_word_carry_append:
  "mahler_word_carry (left @ right) =
    3^(length right) * mahler_word_carry left +
    2^(length left) * mahler_word_carry right"
proof (induction left arbitrary: right)
  case Nil
  then show ?case by simp
next
  case (Cons bit left)
  show ?case
    using Cons.IH[of right]
    by (simp add: power_add algebra_simps)
qed

lemma mahler_source_word_append:
  "mahler_source_word source (left + right) =
    mahler_source_word source left @
      mahler_source_word (mahler_orbit source left) right"
proof (induction right arbitrary: source)
  case 0
  then show ?case by simp
next
  case (Suc right)
  have orbit:
    "mahler_orbit source (left + right) =
      mahler_orbit (mahler_orbit source left) right"
    by (rule mahler_orbit_add)
  show ?case
    using Suc.IH[of source] orbit
    by (simp only: mahler_source_word.simps; simp add: append_assoc)
qed

theorem mahler_source_carry_append:
  "mahler_word_carry (mahler_source_word source (left + right)) =
    3^right * mahler_word_carry (mahler_source_word source left) +
    2^left * mahler_word_carry
      (mahler_source_word (mahler_orbit source left) right)"
  using mahler_word_carry_append[of
    "mahler_source_word source left"
    "mahler_source_word (mahler_orbit source left) right"]
    mahler_source_word_append[of source left right]
  by simp

text \<open>This equality connects the centered source innovation used by the
cold arithmetic scheduler to the existing Antihydra block action.  The H
family stores the complementary parity bit and its offset J; translating
H=D+1 yields the centered innovation by the exact constant
3^n-2^n+J.  No large endpoint multiplication needs to be repeated to obtain
that innovation.\<close>

theorem mahler_centered_carry_from_antihydra_block:
  "mahler_word_carry (mahler_source_word D n) =
    sk_J (antihydra_arithmetic_block (D+1) n) +
      (3::int)^n - (2::int)^n"
proof -
  let ?block = "antihydra_arithmetic_block (D+1) n"
  have family_application:
    "sk_D ?block * int (antihydra_family_orbit (D+1) n) =
      sk_A ?block * int (D+1) + sk_J ?block"
    using antihydra_arithmetic_block_skew_application[of "D+1" n]
    by (simp add: skew_numerator_def)
  have centered_orbit:
    "int (antihydra_family_orbit (D+1) n) = int (mahler_orbit D n) + 1"
    using antihydra_family_centered_orbit[of D n] by simp
  have family_centered:
    "(2::int)^n * int (mahler_orbit D n) + (2::int)^n =
      (3::int)^n * int D + (3::int)^n + sk_J ?block"
    using family_application centered_orbit
    by (simp add: antihydra_arithmetic_block_def algebra_simps)
  have source_carry:
    "(2::int)^n * int (mahler_orbit D n) =
      (3::int)^n * int D + mahler_word_carry (mahler_source_word D n)"
    by (rule mahler_source_carry_bridge)
  show ?thesis using family_centered source_carry by linarith
qed

corollary antihydra_block_offset_from_centered_carry:
  "sk_J (antihydra_arithmetic_block (D+1) n) =
    mahler_word_carry (mahler_source_word D n) +
      (2::int)^n - (3::int)^n"
  using mahler_centered_carry_from_antihydra_block[of D n] by linarith

theorem mahler_source_word_high_fiber:
  assumes horizon: "ticks \<le> width"
  shows "mahler_source_word (source + 2^width * lift) ticks =
    mahler_source_word source ticks"
  using horizon
proof (induction ticks arbitrary: source width lift)
  case 0
  then show ?case by simp
next
  case (Suc ticks)
  have prefix_bound: "ticks \<le> width" using Suc.prems by arith
  have prefix:
    "mahler_source_word (source + 2^width * lift) ticks =
      mahler_source_word source ticks"
    by (rule Suc.IH[OF prefix_bound])
  have endpoint:
    "mahler_orbit (source + 2^width * lift) ticks =
      mahler_orbit source ticks + lift * 2^(width-ticks) * 3^ticks"
    using moving_source_cylinder[OF prefix_bound, of source lift]
    by (simp add: mult.commute)
  have width_ahead: "ticks < width" using Suc.prems by arith
  have positive_exponent: "0 < width-ticks" using width_ahead by arith
  obtain q where exponent: "width-ticks = Suc q"
    using positive_exponent by (cases "width-ticks") auto
  have even_translation:
    "even (lift * 2^(width-ticks) * 3^ticks)"
    using exponent by simp
  have parity:
    "odd (mahler_orbit (source + 2^width * lift) ticks) =
      odd (mahler_orbit source ticks)"
    using endpoint even_translation by simp
  show ?case
    using prefix parity by (simp only: mahler_source_word.simps; simp)
qed

corollary mahler_source_carry_high_fiber:
  assumes "ticks \<le> width"
  shows "mahler_word_carry
      (mahler_source_word (source + 2^width * lift) ticks) =
    mahler_word_carry (mahler_source_word source ticks)"
  using mahler_source_word_high_fiber[OF assms] by simp

lemma mahler_even_event_fraction_exact:
  assumes denominator: "0 < denominator"
      and inlet: "2 * numerator < denominator"
  shows "(of_nat numerator / of_nat denominator) * (3/2)^ticks < (1/2::real)
    \<longleftrightarrow> \<not> mahler_even_event_impossible numerator denominator ticks"
proof -
  have den_pos: "(0::real) < of_nat denominator"
    using denominator by simp
  have quotient:
    "((of_nat numerator::real) / of_nat denominator) * (3/2)^ticks =
      (of_nat (numerator * 3^ticks)::real) / of_nat (denominator * 2^ticks)"
  proof -
    have power: "(3/2::real)^ticks =
        (of_nat (3^ticks)::real) / of_nat (2^ticks)"
      by (simp add: power_divide)
    show ?thesis using den_pos power
      by (simp only: power divide_inverse of_nat_mult inverse_mult_distrib;
          simp add: algebra_simps)
  qed
  have scaled_den_pos: "(0::real) < of_nat (denominator * 2^ticks)"
    using denominator by simp
  have comparison:
    "(of_nat (numerator * 3^ticks)::real) /
        of_nat (denominator * 2^ticks) < (1/2::real)
      \<longleftrightarrow> (2::real) * of_nat (numerator * 3^ticks) <
        (of_nat (denominator * 2^ticks)::real)"
    using scaled_den_pos by (simp add: pos_divide_less_eq; linarith)
  have comparison_nat:
    "(of_nat (numerator * 3^ticks)::real) /
        of_nat (denominator * 2^ticks) < (1/2::real)
      \<longleftrightarrow> 2 * (numerator * 3^ticks) < denominator * 2^ticks"
  proof -
    have cast: "(2::real) * of_nat (numerator * 3^ticks) =
        (of_nat (2 * (numerator * 3^ticks))::real)"
      by simp
    show ?thesis using comparison by (simp only: cast of_nat_less_iff)
  qed
  show ?thesis
    using quotient comparison_nat
    by (simp add: mahler_even_event_impossible_def mult.assoc not_le)
qed

lemma mahler_even_run_guard_exact:
  assumes inlet: "0 \<le> t" "t < 1/2"
  shows "cylinder_guard (2^ticks * source) ticks t \<longleftrightarrow>
    (3/2)^ticks * t < 1/2"
proof
  assume admitted: "cylinder_guard (2^ticks * source) ticks t"
  have end_bound:
    "fractional_endpoint (2^ticks * source) ticks t < 1/2"
    by (rule guard_endpoint_bounds(2)[OF admitted])
  have endpoint: "fractional_endpoint (2^ticks * source) ticks t = (3/2)^ticks*t"
    using even_run_fraction[of ticks ticks source t] by (simp add: mult.commute)
  show "(3/2)^ticks * t < 1/2" using end_bound endpoint by simp
next
  assume terminal: "(3/2)^ticks * t < 1/2"
  have bounds: "0 \<le> fractional_endpoint (2^ticks * source) j t \<and>
      fractional_endpoint (2^ticks * source) j t < 1/2"
    if j_bound: "j \<le> ticks" for j
  proof -
    have powered: "(3/2::real)^j \<le> (3/2)^ticks"
      by (rule power_increasing[OF j_bound]) simp
    have nonnegative: "0 \<le> (3/2::real)^j * t"
      using inlet(1) by (simp add: mult_nonneg_nonneg)
    have scaled: "(3/2::real)^j*t \<le> (3/2)^ticks*t"
      by (rule mult_right_mono[OF powered inlet(1)])
    have upper: "(3/2::real)^j*t < 1/2"
      using scaled terminal by linarith
    have endpoint: "fractional_endpoint (2^ticks * source) j t = (3/2)^j*t"
      by (rule even_run_fraction[OF j_bound])
    show ?thesis using nonnegative upper endpoint by simp
  qed
  have all_bounds:
    "\<forall>j\<le>ticks. 0 \<le> fractional_endpoint (2^ticks * source) j t \<and>
      fractional_endpoint (2^ticks * source) j t < 1/2"
    using bounds by blast
  show "cylinder_guard (2^ticks * source) ticks t"
    using all_bounds inlet
    by (simp only: guard_iff_endpoint_bounds; blast)
qed

theorem mahler_even_event_guard_exact:
  assumes denominator: "0 < denominator"
      and inlet: "2 * numerator < denominator"
  shows "cylinder_guard (2^ticks * source) ticks
      (of_nat numerator / of_nat denominator) \<longleftrightarrow>
    \<not> mahler_even_event_impossible numerator denominator ticks"
proof -
  have den_pos: "(0::real) < of_nat denominator"
    using denominator by simp
  have t_nonnegative:
    "0 \<le> (of_nat numerator / of_nat denominator::real)"
    by (simp add: denominator)
  have t_upper:
    "(of_nat numerator / of_nat denominator::real) < 1/2"
  proof -
    have scaled_inlet:
      "(2::real) * of_nat numerator < of_nat denominator"
    proof -
      have cast_inlet:
        "(of_nat (2 * numerator)::real) < (of_nat denominator::real)"
        using inlet by (simp only: of_nat_less_iff)
      show ?thesis using cast_inlet by simp
    qed
    show ?thesis using scaled_inlet den_pos
      by (simp add: field_simps; linarith)
  qed
  have guard:
    "cylinder_guard (2^ticks * source) ticks
        (of_nat numerator / of_nat denominator) \<longleftrightarrow>
      (3/2::real)^ticks * (of_nat numerator / of_nat denominator) < (1/2::real)"
    by (rule mahler_even_run_guard_exact[OF t_nonnegative t_upper])
  have exact:
    "(3/2)^ticks * (of_nat numerator / of_nat denominator) < (1/2::real) \<longleftrightarrow>
      \<not> mahler_even_event_impossible numerator denominator ticks"
    using mahler_even_event_fraction_exact[OF denominator inlet, of ticks]
    by (simp add: mult.commute)
  show ?thesis using guard exact by simp
qed

text \<open>The exponential predicate is monotone in the run length.  Therefore a
binary search may choose any candidate position, then correct it using this
exact predicate; equality belongs to the failing side because the fractional
guard is half-open.\<close>

ML \<open>
  val checked = @{thms mahler_even_event_impossible_mono
    mahler_even_run_guard_exact
    mahler_even_event_fraction_exact mahler_even_event_guard_exact
    mahler_word_carry_append mahler_source_word_append
    mahler_source_carry_append mahler_centered_carry_from_antihydra_block
    antihydra_block_offset_from_centered_carry
    mahler_source_word_high_fiber mahler_source_carry_high_fiber};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Exact Mahler event threshold depends on an oracle";
  val _ = if Thm_Deps.has_skip_proof checked
    then error "Skipped exact Mahler event threshold proof" else ();
\<close>

end
