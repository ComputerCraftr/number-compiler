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
  Two centered Mahler steps expose a radix-four source fiber. The multiplier
  nine is a spatial carry action on that fiber, not a supplied temporal event
  itinerary. Its nine incoming carries are closed on radix-four digits.
  Sentinel digit one forgets the incoming carry after two spatial positions;
  this statement alone is not a future safety or temporal-closure theorem.
  A Collatz accelerated return must authenticate its own carry separately;
  these ports belong to the centered Mahler recurrence defined in this session.
\<close>

lemma radix_four_nine_carry_closed:
  assumes digit: "u < 4" and carry: "c < 9"
  shows "spatial_block_output 4 9 u c < 4"
    and "spatial_block_carry 4 9 u c < 9"
proof -
  have digits: "u = 0 \<or> u = 1 \<or> u = 2 \<or> u = 3"
    using digit by arith
  have carries: "c = 0 \<or> c = 1 \<or> c = 2 \<or> c = 3 \<or>
    c = 4 \<or> c = 5 \<or> c = 6 \<or> c = 7 \<or> c = 8"
    using carry by arith
  show "spatial_block_output 4 9 u c < 4"
    and "spatial_block_carry 4 9 u c < 9"
    using digits carries
    by (auto simp: spatial_block_output_def spatial_block_carry_def)
qed

text \<open>
  The derivative of the rational source root with intercept 3*c+1 uses the
  same multiplication carry. The denominator-four branch is admitted only
  when its radix-four emitted digit is one; a separate unauthenticated port
  cannot supply that condition. The next finite port is the multiplier-nine
  carry, not the rational-root intercept 3*carry+1.
\<close>

theorem radix_four_root_derivative_carry:
  assumes branch: "(9*x+c) mod 4 = 1"
  shows "(27*x+3*c+1) div 4 =
    3*spatial_block_carry 4 9 x c+1"
proof -
  have block: "9*x+c = 1+4*spatial_block_carry 4 9 x c"
    using spatial_block_conservation[of 9 x c 4] branch
    by (simp add: spatial_block_output_def)
  have numerator: "27*x+3*c+1 =
      4*(3*spatial_block_carry 4 9 x c+1)"
    using block by arith
  show ?thesis by (simp only: numerator; simp)
qed

corollary radix_four_root_derivative_finite_port:
  assumes branch: "(9*x+c) mod 4 = 1"
    and digit: "x < 4" and carry: "c < 9"
  shows "(27*x+3*c+1) div 4 =
      3*spatial_block_carry 4 9 x c+1"
    and "spatial_block_carry 4 9 x c < 9"
  using radix_four_root_derivative_carry[OF branch]
    radix_four_nine_carry_closed(2)[OF digit carry]
  by auto

lemma radix_four_one_two_reset:
  assumes "c < 9"
  shows "spatial_block_carry 4 9 1 (spatial_block_carry 4 9 1 c) =
    (if c < 3 then 2 else 3)"
proof -
  have "c = 0 \<or> c = 1 \<or> c = 2 \<or> c = 3 \<or>
    c = 4 \<or> c = 5 \<or> c = 6 \<or> c = 7 \<or> c = 8"
    using assms by arith
  then show ?thesis by (auto simp: spatial_block_carry_def)
qed

lemma radix_four_one_reset_fixed:
  "spatial_block_carry 4 9 1 (if c < 3 then 2 else 3) =
    (if c < 3 then 2 else 3)"
  "spatial_block_output 4 9 1 (if c < 3 then 2 else 3) =
    (if c < 3 then 3 else 0)"
  by (auto simp: spatial_block_carry_def spatial_block_output_def)

lemma radix_four_one_two_conservation:
  fixes c c1 e0 e1 carry_tail :: nat
  assumes carry: "c < 9"
  defines "c1 \<equiv> spatial_block_carry 4 9 1 c"
    and "e0 \<equiv> spatial_block_output 4 9 1 c"
    and "e1 \<equiv> spatial_block_output 4 9 1 c1"
    and "carry_tail \<equiv> if c < 3 then 2 else 3"
  shows "9 * 5 + c = e0 + 4*e1 + 16*carry_tail"
proof -
  have first: "9+c = e0+4*c1"
    using spatial_block_conservation[of 9 1 c 4]
    by (simp add: e0_def c1_def)
  have second: "9+c1 = e1+4*carry_tail"
    using spatial_block_conservation[of 9 1 c1 4]
      radix_four_one_two_reset[OF carry]
    by (simp add: e1_def c1_def carry_tail_def)
  show ?thesis using first second by arith
qed

theorem radix_four_one_run_conservation:
  fixes c c1 e0 e1 carry_tail e n :: nat
  assumes carry: "c < 9"
  defines "c1 \<equiv> spatial_block_carry 4 9 1 c"
    and "e0 \<equiv> spatial_block_output 4 9 1 c"
    and "e1 \<equiv> spatial_block_output 4 9 1 c1"
    and "carry_tail \<equiv> if c < 3 then 2 else 3"
    and "e \<equiv> if c < 3 then 3 else 0"
  shows "9 * spatial_repeat_value 4 1 (n+2) + c =
    e0 + 4*e1 + 16*spatial_repeat_value 4 e n + 4^(n+2)*carry_tail"
proof -
  have prefix: "9*5+c = e0+4*e1+16*carry_tail"
    using radix_four_one_two_conservation[OF carry]
    by (simp add: c1_def e0_def e1_def carry_tail_def)
  have fixed: "9*1+carry_tail = e+4*carry_tail"
    by (auto simp: carry_tail_def e_def)
  have tail: "9*spatial_repeat_value 4 1 n+carry_tail =
      spatial_repeat_value 4 e n+4^n*carry_tail"
    by (rule spatial_fixed_carry_repeat_conservation[OF fixed])
  have split: "spatial_repeat_value 4 1 (n+2) =
      5+16*spatial_repeat_value 4 1 n"
    by (simp add: numeral_2_eq_2 algebra_simps)
  show ?thesis
    using prefix tail
    by (simp add: split power_add algebra_simps; arith)
qed

theorem mahler_radix_four_reentry:
  "mahler_orbit (r+4*M) 2 = 9*M+mahler_orbit r 2"
  using moving_source_cylinder[of 2 2 r M]
  by (simp add: mult.commute)

lemma mahler_radix_four_two_steps:
  "mahler_orbit D 2 = mahler_D_step (mahler_D_step D)"
  by (simp add: numeral_2_eq_2)

lemma mahler_radix_four_direct_witness:
  "mahler_orbit 1 2 = 3"
  "mahler_orbit 2 2 = 5"
  by (simp_all add: mahler_radix_four_two_steps mahler_D_step_def)

lemma mahler_radix_four_reentry_ports:
  assumes "r < 4"
  shows "mahler_orbit r 2 =
    (if r = 0 then 0 else if r = 1 then 3 else if r = 2 then 5 else 8)"
    and "mahler_orbit r 2 \<in> {0,3,5,8}"
proof -
  have "r = 0 \<or> r = 1 \<or> r = 2 \<or> r = 3"
    using assms by arith
  then show "mahler_orbit r 2 =
      (if r = 0 then 0 else if r = 1 then 3 else if r = 2 then 5 else 8)"
    and "mahler_orbit r 2 \<in> {0,3,5,8}"
    by (auto simp: mahler_radix_four_two_steps mahler_D_step_def)
qed


text \<open>
  Executable nine-port first-hole classification. A complete left summary is
  consumed before the right source is demanded. A hole records a position in
  the original source, the emitted digit and the carry just after that digit.
  The source cursor itself is not the transformed high residual. Recursive
  source nodes carry authenticated cached extents. Classification never checks
  validity by rescanning the source: publication maintains that invariant.
  The right branch and the left extent are demanded only after a Clear result.
\<close>

datatype radix_four_summary =
    RadixFourClear nat
  | RadixFourHole nat nat nat

fun radix_four_summary_join ::
  "nat \<Rightarrow> radix_four_summary \<Rightarrow> (nat \<Rightarrow> radix_four_summary)
    \<Rightarrow> radix_four_summary" where
  "radix_four_summary_join n (RadixFourHole h e c) right = RadixFourHole h e c"
| "radix_four_summary_join n (RadixFourClear c) right =
    (case right c of RadixFourClear d \<Rightarrow> RadixFourClear d
      | RadixFourHole h e d \<Rightarrow> RadixFourHole (n+h) e d)"

fun radix_four_classifier :: "nat list \<Rightarrow> nat \<Rightarrow> radix_four_summary" where
  "radix_four_classifier [] c = RadixFourClear c"
| "radix_four_classifier (x#xs) c =
    (let e = spatial_block_output 4 9 x c;
         d = spatial_block_carry 4 9 x c
     in if e = 1 then radix_four_summary_join 1 (RadixFourClear d)
          (radix_four_classifier xs)
        else RadixFourHole 0 e d)"

lemma radix_four_summary_join_associative:
  "radix_four_summary_join (m+n)
      (radix_four_summary_join m left middle) right =
    radix_four_summary_join m left
      (\<lambda>c. radix_four_summary_join n (middle c) right)"
  by (cases left; auto split: radix_four_summary.splits)

lemma radix_four_classifier_identity:
  "radix_four_classifier [] c = RadixFourClear c"
  "radix_four_summary_join 0 (RadixFourClear c) right = right c"
  by (simp_all split: radix_four_summary.splits)

theorem radix_four_classifier_append:
  "radix_four_classifier (xs@ys) c =
    radix_four_summary_join (length xs) (radix_four_classifier xs c)
      (radix_four_classifier ys)"
proof (induction xs arbitrary: c)
  case Nil then show ?case by (simp split: radix_four_summary.splits)
next
  case (Cons x xs)
  then show ?case
    by (auto simp: Let_def split: radix_four_summary.splits)
qed

datatype radix_four_source =
    RadixFourEmpty
  | RadixFourDigit nat
  | RadixFourConcat nat radix_four_source radix_four_source

fun radix_four_source_word :: "radix_four_source \<Rightarrow> nat list" where
  "radix_four_source_word RadixFourEmpty = []"
| "radix_four_source_word (RadixFourDigit x) = [x]"
| "radix_four_source_word (RadixFourConcat n left right) =
    radix_four_source_word left @ radix_four_source_word right"

fun radix_four_source_length :: "radix_four_source \<Rightarrow> nat" where
  "radix_four_source_length RadixFourEmpty = 0"
| "radix_four_source_length (RadixFourDigit x) = 1"
| "radix_four_source_length (RadixFourConcat n left right) = n"

fun radix_four_source_valid :: "radix_four_source \<Rightarrow> bool" where
  "radix_four_source_valid RadixFourEmpty = True"
| "radix_four_source_valid (RadixFourDigit x) = (x < 4)"
| "radix_four_source_valid (RadixFourConcat n left right) =
    (radix_four_source_valid left \<and> radix_four_source_valid right \<and>
      n = radix_four_source_length left + radix_four_source_length right)"

fun radix_four_source_classifier ::
  "radix_four_source \<Rightarrow> nat \<Rightarrow> radix_four_summary" where
  "radix_four_source_classifier RadixFourEmpty c = RadixFourClear c"
| "radix_four_source_classifier (RadixFourDigit x) c = radix_four_classifier [x] c"
| "radix_four_source_classifier (RadixFourConcat n left right) c =
    (case radix_four_source_classifier left c of
      RadixFourHole h e d \<Rightarrow> RadixFourHole h e d
    | RadixFourClear d \<Rightarrow> radix_four_summary_join (radix_four_source_length left)
        (RadixFourClear d) (radix_four_source_classifier right))"

lemma radix_four_source_length_refinement:
  assumes "radix_four_source_valid source"
  shows "radix_four_source_length source = length (radix_four_source_word source)"
  using assms by (induction source) simp_all

theorem radix_four_source_classifier_refinement:
  assumes "radix_four_source_valid source"
  shows "radix_four_source_classifier source c =
    radix_four_classifier (radix_four_source_word source) c"
  using assms
proof (induction source arbitrary: c)
  case RadixFourEmpty then show ?case by simp
next
  case (RadixFourDigit x) then show ?case by simp
next
  case (RadixFourConcat n left right)
  have valid_left: "radix_four_source_valid left"
    and valid_right: "radix_four_source_valid right"
    using RadixFourConcat.prems by simp_all
  have right: "radix_four_source_classifier right =
      radix_four_classifier (radix_four_source_word right)"
    by (rule ext; rule RadixFourConcat.IH(2)[OF valid_right])
  show ?case
    by (simp add: RadixFourConcat.IH(1)[OF valid_left] right radix_four_classifier_append
        radix_four_source_length_refinement[OF valid_left]
        split: radix_four_summary.splits)
qed

corollary radix_four_source_classifier_early_exit:
  assumes "radix_four_source_classifier left c = RadixFourHole h e d"
  shows "radix_four_source_classifier (RadixFourConcat n left right) c =
    RadixFourHole h e d"
  by (simp add: assms)

fun radix_four_word_value :: "nat list \<Rightarrow> nat" where
  "radix_four_word_value [] = 0"
| "radix_four_word_value (x#xs) = x+4*radix_four_word_value xs"

lemma radix_four_classifier_clear_conservation:
  assumes "radix_four_classifier xs c = RadixFourClear d"
  shows "9*radix_four_word_value xs+c =
    spatial_repeat_value 4 1 (length xs)+4^(length xs)*d"
  using assms
proof (induction xs arbitrary: c d)
  case Nil then show ?case by simp
next
  case (Cons x xs)
  let ?e = "spatial_block_output 4 9 x c"
  let ?c = "spatial_block_carry 4 9 x c"
  have emitted: "?e = 1" and tail: "radix_four_classifier xs ?c = RadixFourClear d"
    using Cons.prems by (auto simp: Let_def split: radix_four_summary.splits if_splits)
  have head: "9*x+c = 1+4*?c"
    using spatial_block_conservation[of 9 x c 4] emitted by simp
  have rest: "9*radix_four_word_value xs+?c =
    spatial_repeat_value 4 1 (length xs)+4^(length xs)*d"
    by (rule Cons.IH[OF tail])
  show ?case using head rest by (simp add: power_Suc algebra_simps; arith)
qed

theorem radix_four_classifier_cursor_conservation:
  assumes "radix_four_classifier xs c = RadixFourHole h e d"
  shows "9*radix_four_word_value xs+c =
    spatial_repeat_value 4 1 h+4^h*e+
      4^(Suc h)*(9*radix_four_word_value (drop (Suc h) xs)+d)"
  using assms
proof (induction xs arbitrary: c h e d)
  case Nil then show ?case by simp
next
  case (Cons x xs)
  let ?out = "spatial_block_output 4 9 x c"
  let ?carry = "spatial_block_carry 4 9 x c"
  have head: "9*x+c = ?out+4*?carry"
    by (rule spatial_block_conservation)
  show ?case
  proof (cases "?out = 1")
    case False
    then have position: "h=0" and emission: "e=?out" and carry: "d=?carry"
      using Cons.prems by (auto simp: Let_def)
    show ?thesis using head
      by (simp add: position emission carry algebra_simps)
  next
    case True
    obtain j where tail: "radix_four_classifier xs ?carry = RadixFourHole j e d"
      and position: "h = Suc j"
      using Cons.prems True
      by (cases "radix_four_classifier xs ?carry") (auto simp: Let_def)
    have rest: "9*radix_four_word_value xs+?carry =
        spatial_repeat_value 4 1 j+4^j*e+
          4^(Suc j)*(9*radix_four_word_value (drop (Suc j) xs)+d)"
      by (rule Cons.IH[OF tail])
    show ?thesis using head rest True
      by (simp add: position power_Suc algebra_simps; arith)
  qed
qed

lemma radix_four_classifier_hole_position:
  assumes "radix_four_classifier xs c = RadixFourHole h e d"
  shows "h < length xs" "e \<noteq> 1"
proof -
  have combined: "h < length xs \<and> e \<noteq> 1"
    using assms
  proof (induction xs arbitrary: c h e d)
    case Nil then show ?case by simp
  next
    case (Cons x xs)
    let ?out = "spatial_block_output 4 9 x c"
    let ?carry = "spatial_block_carry 4 9 x c"
    show ?case
    proof (cases "?out = 1")
      case False
      then have position: "h=0" and emission: "e=?out"
        using Cons.prems by (auto simp: Let_def)
      show ?thesis using False position emission by simp
    next
      case True
      obtain j where tail: "radix_four_classifier xs ?carry = RadixFourHole j e d"
        and position: "h = Suc j"
        using Cons.prems True
        by (cases "radix_four_classifier xs ?carry") (auto simp: Let_def)
      have bounds: "j < length xs \<and> e \<noteq> 1"
        by (rule Cons.IH[OF tail])
      show ?thesis using bounds by (simp add: position)
    qed
  qed
  show "h < length xs" "e \<noteq> 1" using combined by auto
qed

lemma radix_four_classifier_finite_port:
  assumes "c < 9" "\<forall>x\<in>set xs. x < 4"
  shows "(case radix_four_classifier xs c of
    RadixFourClear d \<Rightarrow> d < 9 | RadixFourHole h e d \<Rightarrow> e < 4 \<and> d < 9)"
  using assms
proof (induction xs arbitrary: c)
  case Nil then show ?case by simp
next
  case (Cons x xs)
  have digit: "x < 4" and carry: "c < 9" and tail: "\<forall>x\<in>set xs. x < 4"
    using Cons.prems by auto
  have emission: "spatial_block_output 4 9 x c < 4"
    and next_carry: "spatial_block_carry 4 9 x c < 9"
    using radix_four_nine_carry_closed[OF digit carry] by auto
  have rest: "(case radix_four_classifier xs (spatial_block_carry 4 9 x c) of
    RadixFourClear d \<Rightarrow> d < 9 | RadixFourHole h e d \<Rightarrow> e < 4 \<and> d < 9)"
    by (rule Cons.IH[OF next_carry tail])
  show ?case using emission next_carry rest
    by (auto simp: Let_def split: radix_four_summary.splits)
qed

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
      spatial_block_carry_monotone radix_four_nine_carry_closed
      radix_four_root_derivative_carry radix_four_root_derivative_finite_port
      radix_four_one_two_reset radix_four_one_reset_fixed
      radix_four_one_two_conservation radix_four_one_run_conservation
      mahler_radix_four_reentry mahler_radix_four_two_steps
      mahler_radix_four_direct_witness
      mahler_radix_four_reentry_ports
      radix_four_summary_join_associative radix_four_classifier_identity
      radix_four_classifier_append radix_four_source_length_refinement
      radix_four_source_classifier_refinement radix_four_source_classifier_early_exit
      radix_four_classifier_clear_conservation radix_four_classifier_cursor_conservation
      radix_four_classifier_hole_position radix_four_classifier_finite_port
      translated_safe_interval
      translated_safe_output strict_interval_intersection_nonempty
      event_exponent_interval_admission})
    then () else error "Spatial carry pump depends on an oracle";
\<close>

end
