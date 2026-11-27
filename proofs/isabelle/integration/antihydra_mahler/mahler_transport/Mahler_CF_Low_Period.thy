theory Mahler_CF_Low_Period
  imports Mahler_Continued_Fraction_Refinement "HOL.Groebner_Basis"
    "Shared_Carry_Dynamics.Dyadic_Unit_Carry_Frontier"
begin

text \<open>The decimal low suffix is derived from the same raw power of five.
The settled phase belongs only to this bounded suffix and does not identify
the changing-width upper word.\<close>

lemma mahler_cf_low_dyadic_phase:
  fixes columns exponent :: nat
  assumes "0 < columns"
  shows "(5::nat)^exponent mod 2^columns =
    5^(exponent mod dyadic_unit_phase_period 5 columns) mod 2^columns"
proof -
  let ?period = "dyadic_unit_phase_period 5 columns"
  let ?modulus = "(2::nat)^columns"
  have period_positive: "0 < ?period"
    by (simp add: dyadic_unit_phase_period_def)
  have modulus_gt_one: "1 < ?modulus"
    by (rule one_less_power) (use assms in simp_all)
  have returned: "(5::nat)^?period mod ?modulus = 1"
    by (rule dyadic_five_unit_phase_period_returns[OF assms])
  have repeated: "(5::nat)^(?period * (exponent div ?period)) mod ?modulus = 1"
  proof -
    have "((5::nat)^?period)^(exponent div ?period) mod ?modulus =
        (((5::nat)^?period mod ?modulus)^(exponent div ?period)) mod ?modulus"
      by (rule power_mod[symmetric])
    also have "... = 1"
      using assms by (simp only: returned power_one) simp
    finally show ?thesis by (simp only: power_mult)
  qed
  have decomposition:
    "exponent = exponent mod ?period + ?period * (exponent div ?period)"
    using div_mult_mod_eq[of exponent ?period] by (simp add: mult.commute)
  have "(5::nat)^exponent mod ?modulus =
      (5^(exponent mod ?period) * 5^(?period * (exponent div ?period))) mod ?modulus"
    by (subst (1) decomposition) (simp only: power_add)
  also have "... = 5^(exponent mod ?period) mod ?modulus"
  proof -
    have "((5::nat)^(exponent mod ?period) *
        5^(?period * (exponent div ?period))) mod ?modulus =
      ((5^(exponent mod ?period) mod ?modulus) *
        (5^(?period * (exponent div ?period)) mod ?modulus)) mod ?modulus"
      by (rule mod_mult_eq[symmetric])
    also have "... = 5^(exponent mod ?period) mod ?modulus"
      using modulus_gt_one by (simp add: repeated)
    finally show ?thesis .
  qed
  finally show ?thesis .
qed

theorem mahler_cf_settled_low_suffix:
  fixes exponent columns :: nat
  assumes columns: "0 < columns" and settled: "columns \<le> exponent"
  shows "(5::nat)^exponent mod 10^columns =
    5^columns *
      (5^((exponent-columns) mod dyadic_unit_phase_period 5 columns) mod 2^columns)"
proof -
  have decomposition: "exponent = columns + (exponent-columns)"
    using settled by simp
  have decimal: "(10::nat)^columns = 5^columns * 2^columns"
    by (simp add: power_mult_distrib[symmetric] mult.commute)
  have "(5::nat)^exponent mod 10^columns =
      5^columns * (5^(exponent-columns) mod 2^columns)"
    by (subst (1) decomposition)
       (simp only: power_add decimal mod_mult_mult1)
  also have "... =
      5^columns * (5^((exponent-columns) mod
        dyadic_unit_phase_period 5 columns) mod 2^columns)"
    by (rule arg_cong[where f="(\<lambda>x. 5^columns * x)"])
       (rule mahler_cf_low_dyadic_phase[OF columns])
  finally show ?thesis .
qed

theorem mahler_cf_low_suffix_ordered_consumer:
  fixes exponent columns :: nat
  assumes "0 < columns" "columns \<le> exponent"
  shows "mahler_cf_word (mahler_cf_decimal_digits columns (5^exponent mod 10^columns)) =
    mahler_cf_word (mahler_cf_decimal_digits columns
      (5^columns * (5^((exponent-columns) mod
        dyadic_unit_phase_period 5 columns) mod 2^columns)))"
  using mahler_cf_settled_low_suffix[OF assms] by simp


lemma mahler_cf_settled_low_return:
  fixes columns offset :: nat
  assumes columns: "0 < columns"
  shows "(5::nat)^(columns+offset+dyadic_unit_phase_period 5 columns) mod 10^columns =
    5^(columns+offset) mod 10^columns"
proof -
  let ?period = "dyadic_unit_phase_period 5 columns"
  have left: "(5::nat)^(columns+offset+?period) mod 10^columns =
    5^columns * (5^((offset+?period) mod ?period) mod 2^columns)"
    using mahler_cf_settled_low_suffix[OF columns, of "columns+offset+?period"]
    by simp
  have right: "(5::nat)^(columns+offset) mod 10^columns =
    5^columns * (5^(offset mod ?period) mod 2^columns)"
    using mahler_cf_settled_low_suffix[OF columns, of "columns+offset"]
    by simp
  show ?thesis using left right by simp
qed

theorem mahler_cf_low_suffix_ordered_period:
  fixes columns offset rows :: nat
  assumes columns: "0 < columns"
    and fits: "dyadic_unit_phase_period 5 columns \<le> rows"
  defines "period \<equiv> dyadic_unit_phase_period 5 columns"
  shows "mahler_cf_word (concat (map (\<lambda>i.
      mahler_cf_decimal_digits columns (5^(columns+offset+i) mod 10^columns))
        [0..<rows])) =
    ordered_matrix2_multiply
      (ordered_matrix2_power (mahler_cf_word (concat (map (\<lambda>i.
        mahler_cf_decimal_digits columns (5^(columns+offset+i) mod 10^columns))
        [0..<period]))) (rows div period))
      (mahler_cf_word (concat (take (rows mod period) (map (\<lambda>i.
        mahler_cf_decimal_digits columns (5^(columns+offset+i) mod 10^columns))
        [0..<period]))))"
proof -
  let ?row = "\<lambda>i. mahler_cf_decimal_digits columns
    (5^(columns+offset+i) mod 10^columns)"
  have positive: "0 < period"
    by (simp add: period_def dyadic_unit_phase_period_def)
  have periodic: "?row (i+period) = ?row i" if "i+period < rows" for i
    using mahler_cf_settled_low_return[OF columns, of "offset+i"]
    by (simp add: period_def add.assoc)
  have sequence:
    "map ?row [0..<rows] =
      concat (replicate (rows div period) (map ?row [0..<period])) @
      take (rows mod period) (map ?row [0..<period])"
    by (rule mahler_cf_periodic_list[OF positive]) (use fits periodic in \<open>auto simp: period_def\<close>)
  show ?thesis using sequence
    by (simp only: mahler_cf_concat_repeated_rows concat_append
        mahler_cf_word_append mahler_cf_word_repeat)
qed

ML \<open>
  val checked = @{thms mahler_cf_low_dyadic_phase
    mahler_cf_settled_low_suffix mahler_cf_low_suffix_ordered_consumer
    mahler_cf_settled_low_return mahler_cf_low_suffix_ordered_period};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Mahler low-column phase depends on an oracle";
  val _ = if Thm_Deps.has_skip_proof checked
    then error "Skipped Mahler low-column phase proof" else ();
\<close>

text \<open>For an even radix, the full ordered row observations distinguish
every canonical lift at the admitted extent. The low bit comes from the
first row, and the remaining observations belong to the shifted lift.\<close>

lemma mahler_cf_lift_separation:
  fixes x y base :: nat
  assumes even_base: "2 dvd base"
    and obs: "\<And>i. i \<le> n \<Longrightarrow> (x div 2^i) mod base = (y div 2^i) mod base"
  shows "x mod (base * 2^n) = y mod (base * 2^n)"
  using obs
proof (induction n arbitrary: x y)
  case 0
  then show ?case using "0.prems"[of 0] by simp
next
  case (Suc n)
  have first: "x mod base = y mod base" using Suc.prems[of 0] by simp
  have bit: "x mod 2 = y mod 2"
    using arg_cong[OF first, where f="\<lambda>v. v mod 2"]
    by (simp add: mod_mod_cancel[OF even_base])
  have tail: "(x div 2) mod (base * 2^n) = (y div 2) mod (base * 2^n)"
  proof (rule Suc.IH)
    fix i assume "i \<le> n"
    then have "(x div 2^(Suc i)) mod base = (y div 2^(Suc i)) mod base"
      by (intro Suc.prems) simp
    then show "((x div 2) div 2^i) mod base = ((y div 2) div 2^i) mod base"
      by (simp add: div_mult2_eq)
  qed
  have eq: "x mod (2 * (base * 2^n)) = y mod (2 * (base * 2^n))"
    unfolding mod_mult2_eq[of x 2] mod_mult2_eq[of y 2] using bit tail by simp
  then show ?case by (simp add: mult_ac)
qed

theorem mahler_cf_ordered_row_moore_id:
  fixes x y base :: nat
  assumes "2 dvd base"
  shows "(x mod (base * 2^n) = y mod (base * 2^n)) =
    (\<forall>i\<le>n. (x div 2^i) mod base = (y div 2^i) mod base)"
proof
  assume eq: "x mod (base * 2^n) = y mod (base * 2^n)"
  show "\<forall>i\<le>n. (x div 2^i) mod base = (y div 2^i) mod base"
  proof (intro allI impI)
    fix i assume le: "i \<le> n"
    have proj: "\<And>v. ((v mod (base * 2^n)) div 2^i) mod base = (v div 2^i) mod base"
      using mahler_cf_left_child_row[where left="Suc n" and time=i and base=base]
        le by simp
    show "(x div 2^i) mod base = (y div 2^i) mod base"
      by (metis proj eq)
  qed
next
  assume "\<forall>i\<le>n. (x div 2^i) mod base = (y div 2^i) mod base"
  then show "x mod (base * 2^n) = y mod (base * 2^n)"
    by (intro mahler_cf_lift_separation[OF assms]) simp
qed

definition mahler_cf_low_phase_actions :: "nat \<Rightarrow> nat ordered_matrix2 list" where
  "mahler_cf_low_phase_actions w = map
     (\<lambda>p. mahler_cf_word (mahler_cf_decimal_digits w (5^w * (5^p mod 2^w))))
     [0..<dyadic_unit_phase_period 5 w]"

lemma mahler_cf_low_phase_table_checked:
  "mahler_cf_low_phase_actions 1 = [Ordered_Matrix2 6 1 1 0]"
  "mahler_cf_low_phase_actions 2 = [Ordered_Matrix2 19 3 6 1]"
  "mahler_cf_low_phase_actions 3 = [Ordered_Matrix2 44 7 19 3, Ordered_Matrix2 139 22 19 3]"
  "mahler_cf_low_phase_actions 4 = [Ordered_Matrix2 158 25 139 22, Ordered_Matrix2 195 31 44 7, Ordered_Matrix2 853 135 139 22, Ordered_Matrix2 415 66 44 7]"
  by (simp_all add: mahler_cf_low_phase_actions_def dyadic_unit_phase_period_def
      mahler_cf_decimal_digits_def mahler_cf_word_def mahler_cf_digit_def
      ordered_matrix2_identity_def upt_rec)

lemma mahler_cf_low_phase_selection:
  assumes width: "0 < w" and source: "w \<le> n"
  shows "mahler_cf_word (mahler_cf_decimal_digits w (5^n mod 10^w)) =
    mahler_cf_low_phase_actions w ! ((n-w) mod dyadic_unit_phase_period 5 w)"
proof -
  have positive: "0 < dyadic_unit_phase_period 5 w" by (simp add: dyadic_unit_phase_period_def)
  show ?thesis using mahler_cf_low_suffix_ordered_consumer[OF width source]
    by (simp add: mahler_cf_low_phase_actions_def positive)
qed

theorem mahler_cf_small_suffix_moore_id:
  assumes width: "w \<in> {1,2,3,4}" and sources: "w \<le> n" "w \<le> m"
  shows "(mahler_cf_word (mahler_cf_decimal_digits w (5^n mod 10^w)) =
          mahler_cf_word (mahler_cf_decimal_digits w (5^m mod 10^w))) =
    ((n-w) mod dyadic_unit_phase_period 5 w = (m-w) mod dyadic_unit_phase_period 5 w)"
proof -
  have pos: "0 < w" using width by auto
  have sep: "distinct (mahler_cf_low_phase_actions w)" using width
    by (auto simp: mahler_cf_low_phase_table_checked
        mahler_cf_low_phase_table_checked(1)[unfolded One_nat_def])
  have len: "length (mahler_cf_low_phase_actions w) = dyadic_unit_phase_period 5 w"
    by (simp add: mahler_cf_low_phase_actions_def)
  have positive: "0 < dyadic_unit_phase_period 5 w" by (simp add: dyadic_unit_phase_period_def)
  show ?thesis unfolding mahler_cf_low_phase_selection[OF pos sources(1)]
      mahler_cf_low_phase_selection[OF pos sources(2)]
    by (rule nth_eq_iff_index_eq[OF sep]) (simp_all add: len positive)
qed

lemma cf_half_phase_unit:
  "\<exists>h::nat. 5^(2^s) = 1 + 2^(s+2)*(2*h+1)"
proof (induction s)
  case 0
  show ?case by (rule exI[of _ 0]) simp
next
  case (Suc s)
  obtain h::nat where h: "5^(2^s) = 1 + 2^(s+2)*(2*h+1)" using Suc.IH by blast
  have double: "(2::nat)^Suc s = 2^s + 2^s" by simp
  have extended: "(2::nat)^(Suc s+2) = 2*2^(s+2)" by simp
  have square: "(5::nat)^(2^Suc s) = (1+2^(s+2)*(2*h+1))^2"
    by (simp only: double power_add h power2_eq_square)
  have scale: "(2::nat)^(s+2) = 4*2^s" by (simp add: power_add)
  show ?case
  proof (rule exI[of _ "h + 2^s*(2*h+1)^2"])
    show "(5::nat)^(2^Suc s) = 1 + 2^(Suc s+2)*(2*(h+2^s*(2*h+1)^2)+1)"
      unfolding square extended scale by (simp add: power2_eq_square algebra_simps; arith)
  qed
qed

lemma cf_context_half_observer_delta:
  fixes u v w z t a b c d :: int
  shows "(u*((t+5)*a+c) + v*((t+5)*b+d) + w*a + z*b) -
         (u*(t*a+c) + v*(t*b+d) + w*a + z*b) = 5*(a*u+b*v)"
  by algebra

lemma cf_four_column_lattice:
  fixes u v q :: int
  shows "(q dvd 44*u+7*v \<and> q dvd 139*u+22*v) =
         (q dvd 7*u+v \<and> q dvd 5*u)"
proof -
  have a: "7*u+v = (139*u+22*v) - 3*(44*u+7*v)" by algebra
  have b: "5*u = 7*(7*u+v) - (44*u+7*v)" by algebra
  have c: "44*u+7*v = 7*(7*u+v)-5*u" by algebra
  have d: "139*u+22*v = 3*(44*u+7*v)+(7*u+v)" by algebra
  show ?thesis
  proof
    assume H: "q dvd 44*u+7*v \<and> q dvd 139*u+22*v"
    have first: "q dvd 7*u+v" by (subst a; rule dvd_diff; (assumption | rule dvd_mult | rule H[THEN conjunct1] | rule H[THEN conjunct2])+)
    have second: "q dvd 5*u" by (subst b; rule dvd_diff; (rule H[THEN conjunct1] | rule dvd_mult | rule first)+)
    show "q dvd 7*u+v \<and> q dvd 5*u" using first second by simp
  next
    assume H: "q dvd 7*u+v \<and> q dvd 5*u"
    have first: "q dvd 44*u+7*v" by (subst c; rule dvd_diff; (rule H[THEN conjunct1] | rule H[THEN conjunct2] | rule dvd_mult)+)
    have second: "q dvd 139*u+22*v" by (subst d; rule dvd_add; (rule H[THEN conjunct1] | rule dvd_mult | rule first)+)
    show "q dvd 44*u+7*v \<and> q dvd 139*u+22*v" using first second by simp
  qed
qed


lemma mahler_cf_low_source_half_shift_three:
  assumes "3 \<le> n"
  shows "mahler_cf_word (mahler_cf_decimal_digits 3 (5^n mod 10^3)) =
      (if even (n-3) then Ordered_Matrix2 44 7 19 3 else Ordered_Matrix2 139 22 19 3)"
  using mahler_cf_low_phase_selection[of 3 n] assms
  by (cases "even (n-3)"; simp add: mahler_cf_low_phase_table_checked dyadic_unit_phase_period_def mod_2_eq_odd)

lemma cf_source_half_physical:
  fixes s j :: nat
  obtains h :: nat where "5^(s+3+j+2^s) = 5^(s+3+j) + 5*10^(s+2)*(2*h+1)"
proof -
  obtain a::nat where phase: "5^(2^s) = 1+2^(s+2)*(2*a+1)"
    using cf_half_phase_unit[of s] by blast
  have odd: "odd ((5::nat)^j*(2*a+1))" by simp
  then obtain h where h: "(5::nat)^j*(2*a+1)=2*h+1" by (elim oddE) auto
  have base: "(5::nat)^(s+3+j) = 5 * 5^(s+2) * 5^j"
    by (simp add: power_add)
  have ten: "(10::nat)^(s+2) = 5^(s+2)*2^(s+2)"
    using power_mult_distrib[of "5::nat" 2 "s+2"] by simp
  have split: "(5::nat)^(s+3+j+2^s) = 5^(s+3+j) * (1+2^(s+2)*(2*a+1))"
    by (simp only: power_add[of "5::nat" "s+3+j" "2^s"] phase)
  show thesis
    by (rule that[of h]; unfold split base ten h[symmetric]; simp add: algebra_simps)
qed

text \<open>The coefficients below are fixed weights after pulling the fixed
left and right contexts back through the ordered product. The physical decimal
letter d is represented by the positive continued-fraction coefficient d+1.
Divisibility is stated directly at the observer modulus, avoiding a hidden
coprimality assumption when 5 divides it.\<close>

fun cf_observe :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat ordered_matrix2 \<Rightarrow> int" where
  "cf_observe u v w z (Ordered_Matrix2 a b c d) =
    u * int a + v * int b + w * int c + z * int d"


fun cf_observe_int :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int ordered_matrix2 \<Rightarrow> int" where
  "cf_observe_int u v w z (Ordered_Matrix2 a b c d) = u*a+v*b+w*c+z*d"

fun cf_context_weights :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow>
    int ordered_matrix2 \<Rightarrow> int ordered_matrix2 \<Rightarrow> int ordered_matrix2" where
  "cf_context_weights u v w z (Ordered_Matrix2 l00 l01 l10 l11)
      (Ordered_Matrix2 r00 r01 r10 r11) =
    Ordered_Matrix2
      ((u*l00+w*l10)*r00+(v*l00+z*l10)*r01)
      ((u*l00+w*l10)*r10+(v*l00+z*l10)*r11)
      ((u*l01+w*l11)*r00+(v*l01+z*l11)*r01)
      ((u*l01+w*l11)*r10+(v*l01+z*l11)*r11)"

lemma cf_fixed_context_pullback:
  "cf_observe_int u v w z (ordered_matrix2_multiply
      (ordered_matrix2_multiply left action) right) =
    (case cf_context_weights u v w z left right of Ordered_Matrix2 u' v' w' z' \<Rightarrow>
      cf_observe_int u' v' w' z' action)"
  by (cases left; cases right; cases action) (simp add: algebra_simps)

definition cf_half_eq :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat ordered_matrix2 \<Rightarrow> nat ordered_matrix2 \<Rightarrow> bool" where
  "cf_half_eq m u v w z x y \<longleftrightarrow> m dvd cf_observe u v w z y - cf_observe u v w z x"

lemma cf_half_three_exact:
  "cf_half_eq m u v w z (Ordered_Matrix2 44 7 19 3)
    (Ordered_Matrix2 139 22 19 3) = (m dvd 5*(19*u+3*v))"
  by (simp add: cf_half_eq_def algebra_simps)

lemma cf_half_four_exact:
  "(cf_half_eq m u v w z (Ordered_Matrix2 158 25 139 22) (Ordered_Matrix2 853 135 139 22) \<and>
     cf_half_eq m u v w z (Ordered_Matrix2 195 31 44 7) (Ordered_Matrix2 415 66 44 7)) =
    (m dvd 5*(7*u+v) \<and> m dvd 25*u)"
proof -
  have eq: "(m dvd 5*(44*u+7*v) \<and> m dvd 5*(139*u+22*v)) =
      (m dvd 5*(7*u+v) \<and> m dvd 25*u)"
    using cf_four_column_lattice[of m "5*u" "5*v"] by (simp add: algebra_simps)
  show ?thesis using eq by (auto simp: cf_half_eq_def algebra_simps)
qed

lemma cf_half_common_lower_sufficient:
  fixes m u v w z a b c d t t' :: int
  assumes sign: "t' - t = 5 \<or> t' - t = -5"
    and u: "m dvd 5*u" and v: "m dvd 5*v"
  shows "m dvd (u*(t'*a+c) + v*(t'*b+d) + w*a+z*b) -
      (u*(t*a+c) + v*(t*b+d) + w*a+z*b)"
proof -
  have dvd: "m dvd 5*(a*u+b*v)" using u v
    by (simp add: algebra_simps dvd_add dvd_mult)
  have difference: "(u*(t'*a+c)+v*(t'*b+d)+w*a+z*b) -
      (u*(t*a+c)+v*(t*b+d)+w*a+z*b) = (t'-t)*(a*u+b*v)"
    by algebra
  show ?thesis unfolding difference using sign dvd by auto
qed



lemma cf_half_common_ordered_word:
  fixes m u v w z :: int and d d' :: nat
  assumes sign: "int d' - int d = 5 \<or> int d' - int d = -5"
    and u: "m dvd 5*u" and v: "m dvd 5*v"
  shows "cf_half_eq m u v w z (mahler_cf_word (d # tail)) (mahler_cf_word (d' # tail))"
proof -
  obtain a b c e where lower: "mahler_cf_word tail = Ordered_Matrix2 a b c e"
    by (cases "mahler_cf_word tail") auto
  have t: "(int d' + 1) - (int d + 1) = 5 \<or> (int d' + 1) - (int d + 1) = -5"
    using sign by arith
  have observed: "m dvd (u*((int d'+1)*int a + int c) +
      v*((int d'+1)*int b + int e) + w*int a + z*int b) -
      (u*((int d+1)*int a + int c) + v*((int d+1)*int b + int e) + w*int a + z*int b)"
    by (rule cf_half_common_lower_sufficient[OF t u v])
  have factor: "mahler_cf_word (q # tail) =
      ordered_matrix2_multiply (mahler_cf_digit q) (mahler_cf_word tail)" for q
    using mahler_cf_word_append[of "[q]" tail]
    by (simp add: mahler_cf_word_def; cases "mahler_cf_digit q"; simp add: ordered_matrix2_identity_def)
  show ?thesis using observed lower
    by (simp add: cf_half_eq_def factor mahler_cf_digit_def algebra_simps)
qed

lemma cf_half_cut_arithmetic:
  fixes x y p h :: nat
  assumes positive: "0 < p" and shift: "y = x + 5*p*(2*h+1)"
  shows "y mod p = x mod p"
    and "(y div p) mod 10 = ((x div p) + 5) mod 10"
proof -
  have split: "y = x + p*(10*h+5)" using shift by algebra
  show "y mod p = x mod p" by (simp add: split)
  have rearrange: "10*h+5+x div p = (x div p+5)+h*10" by algebra
  show "(y div p) mod 10 = ((x div p) + 5) mod 10"
    using positive by (simp add: split rearrange)
qed


lemma cf_half_digit_sign:
  fixes d d' :: nat
  assumes digit: "d < 10" and successor: "d' = (d+5) mod 10"
  shows "int d' - int d = 5 \<or> int d' - int d = -5"
proof (cases "d < 5")
  case True
  then have "d+5 < 10" by arith
  then show ?thesis using successor by (simp add: mod_less)
next
  case False
  then have lower: "10 \<le> d+5" by arith
  have upper: "d+5 < 20" using digit by arith
  have mod: "(d+5) mod 10 = d-5"
    using lower upper by (simp add: mod_if; arith)
  show ?thesis using False successor mod by arith
qed

lemma cf_source_half_fixed_cut:
  fixes s j :: nat
  obtains h where
    "(5::nat)^(s+3+j+2^s) mod 10^(s+2) = 5^(s+3+j) mod 10^(s+2)"
    "((5::nat)^(s+3+j+2^s) div 10^(s+2)) mod 10 =
       ((5^(s+3+j) div 10^(s+2)) + 5) mod 10"
    "(5::nat)^(s+3+j+2^s) = 5^(s+3+j) + 5*10^(s+2)*(2*h+1)"
proof -
  obtain h where shift: "(5::nat)^(s+3+j+2^s) = 5^(s+3+j) + 5*10^(s+2)*(2*h+1)"
    using cf_source_half_physical[of s j] by blast
  have low: "(5::nat)^(s+3+j+2^s) mod 10^(s+2) = 5^(s+3+j) mod 10^(s+2)"
    and high: "((5::nat)^(s+3+j+2^s) div 10^(s+2)) mod 10 =
       ((5^(s+3+j) div 10^(s+2)) + 5) mod 10"
    using cf_half_cut_arithmetic[OF _ shift] by simp_all
  show thesis by (rule that[OF low high shift])
qed

lemma cf_decimal_digits_split:
  "mahler_cf_decimal_digits (Suc w) x =
    ((x div 10^w) mod 10) # mahler_cf_decimal_digits w x"
proof -
  have tail: "map (\<lambda>i. x div 10^(w-Suc i) mod 10) [0..<w] =
      map (\<lambda>i. x div 10^(w-1-i) mod 10) [0..<w]"
    by (rule map_cong[OF refl]) simp
  show ?thesis unfolding mahler_cf_decimal_digits_def
    using tail by (simp only: map_upt_Suc diff_Suc_1) simp
qed

lemma cf_decimal_digits_lower_congruent:
  assumes "x mod 10^w = y mod 10^w"
  shows "mahler_cf_decimal_digits w x = mahler_cf_decimal_digits w y"
proof (rule nth_equalityI)
  show "length (mahler_cf_decimal_digits w x) = length (mahler_cf_decimal_digits w y)"
    by (simp add: mahler_cf_decimal_digits_def)
  fix i assume i: "i < length (mahler_cf_decimal_digits w x)"
  let ?e = "w-1-i"
  have i': "i<w" using i by (simp add: mahler_cf_decimal_digits_def)
  have exp: "Suc ?e \<le> w" using i' by arith
  have divides: "(10::nat)^Suc ?e dvd 10^w" by (rule le_imp_power_dvd[OF exp])
  have same: "x mod 10^Suc ?e = y mod 10^Suc ?e"
    using arg_cong[where f="\<lambda>n. n mod 10^Suc ?e", OF assms] mod_mod_cancel[OF divides] by simp
  have digit: "(n div 10^?e) mod 10 = (n mod 10^Suc ?e) div 10^?e" for n :: nat
    using arg_cong[where f="\<lambda>v. v div 10^?e", OF mod_mult2_eq[of n "10^?e" 10]]
    by (simp add: power_Suc mult.commute)
  have deq: "(x div 10^?e) mod 10 = (y div 10^?e) mod 10"
    using same by (simp only: digit)
  show "mahler_cf_decimal_digits w x ! i = mahler_cf_decimal_digits w y ! i"
    using i' deq by (simp only: mahler_cf_decimal_digits_def nth_map nth_upt) simp
qed

lemma cf_decimal_digit_cut:
  fixes n w :: nat
  shows "(n div 10^w) mod 10 = (n mod 10^(Suc w)) div 10^w"
  using arg_cong[where f="\<lambda>v. v div 10^w", OF mod_mult2_eq[of n "10^w" 10]]
  by (simp add: power_Suc mult.commute)

theorem cf_source_half_observer_sufficient:
  fixes m u v a b :: int and s j :: nat
  assumes U: "m dvd 5*u" and V: "m dvd 5*v"
  defines "width \<equiv> s+3" and "n \<equiv> s+3+j"
  shows "cf_half_eq m u v a b
    (mahler_cf_word (mahler_cf_decimal_digits width (5^n mod 10^width)))
    (mahler_cf_word (mahler_cf_decimal_digits width (5^(n+2^s) mod 10^width)))"
proof -
  let ?w = "s+2"
  let ?x = "(5::nat)^n"
  let ?y = "(5::nat)^(n+2^s)"
  let ?X = "?x mod 10^width"
  let ?Y = "?y mod 10^width"
  have ws: "width = Suc ?w" by (simp add: width_def)
  obtain h where
    low_raw: "(5::nat)^(s+3+j+2^s) mod 10^(s+2) = 5^(s+3+j) mod 10^(s+2)"
    and high_raw: "((5::nat)^(s+3+j+2^s) div 10^(s+2)) mod 10 =
       ((5^(s+3+j) div 10^(s+2))+5) mod 10"
    and shift_raw: "(5::nat)^(s+3+j+2^s) = 5^(s+3+j)+5*10^(s+2)*(2*h+1)"
    by (rule cf_source_half_fixed_cut)
  have low: "?y mod 10^?w = ?x mod 10^?w"
    using low_raw by (simp only: n_def)
  have high: "(?y div 10^?w) mod 10 = ((?x div 10^?w)+5) mod 10"
    using high_raw by (simp only: n_def)
  have divides: "(10::nat)^?w dvd 10^width" by (simp add: ws)
  have same: "?X mod 10^?w = ?Y mod 10^?w"
    using low mod_mod_cancel[OF divides, of ?x] mod_mod_cancel[OF divides, of ?y] by simp
  have lower: "mahler_cf_decimal_digits ?w ?X = mahler_cf_decimal_digits ?w ?Y"
    by (rule cf_decimal_digits_lower_congruent[OF same])
  have dx: "(?X div 10^?w) mod 10 = (?x div 10^?w) mod 10"
    using cf_decimal_digit_cut[of ?x ?w] by (simp add: ws mod_less_divisor)
  have dy: "(?Y div 10^?w) mod 10 = (?y div 10^?w) mod 10"
    using cf_decimal_digit_cut[of ?y ?w] by (simp add: ws mod_less_divisor)
  have relation: "(?Y div 10^?w) mod 10 = (((?X div 10^?w) mod 10)+5) mod 10"
    using high by (simp only: dx dy mod_add_left_eq mod_mod_trivial)
  have bounded: "(?X div 10^?w) mod 10 < 10" by simp
  have sign: "int ((?Y div 10^?w) mod 10) - int ((?X div 10^?w) mod 10) = 5 \<or>
      int ((?Y div 10^?w) mod 10) - int ((?X div 10^?w) mod 10) = -5"
    by (rule cf_half_digit_sign[OF bounded relation])
  have lower': "mahler_cf_decimal_digits ?w (?x mod 10^(Suc ?w)) =
      mahler_cf_decimal_digits ?w (?y mod 10^(Suc ?w))"
    using lower by (simp only: ws)
  show ?thesis using cf_half_common_ordered_word[OF sign U V, of a b "mahler_cf_decimal_digits ?w ?X"]
    by (simp only: ws cf_decimal_digits_split lower'[symmetric])
qed

lemma cf_half_eq_symmetric:
  "cf_half_eq m u v w z x y = cf_half_eq m u v w z y x"
  by (simp add: cf_half_eq_def dvd_diff_commute)

definition cf_source_action where
  "cf_source_action w n =
    mahler_cf_word (mahler_cf_decimal_digits w (5^n mod 10^w))"

theorem cf_source_three_half_exact:
  assumes n: "3 \<le> n"
  shows "cf_half_eq m u v w z (cf_source_action 3 n) (cf_source_action 3 (n+1)) =
    (m dvd 5*(19*u+3*v))"
proof -
  have p: "n+1-3 = (n-3)+1" using n by arith
  have n': "3 \<le> n+1" using n by simp
  show ?thesis
  proof (cases "even (n-3)")
    case True
    have next_odd: "\<not> even (n+1-3)" using p True by simp
    have a: "cf_source_action 3 n = Ordered_Matrix2 44 7 19 3"
      using mahler_cf_low_source_half_shift_three[OF n] True
      by (simp only: cf_source_action_def if_True)
    have b: "cf_source_action 3 (n+1) = Ordered_Matrix2 139 22 19 3"
      using mahler_cf_low_source_half_shift_three[OF n'] next_odd
      by (simp only: cf_source_action_def if_False)
    show ?thesis by (simp only: a b cf_half_three_exact)
  next
    case False
    have next_even: "even (n+1-3)" using p False by simp
    have a: "cf_source_action 3 n = Ordered_Matrix2 139 22 19 3"
      using mahler_cf_low_source_half_shift_three[OF n] False
      by (simp only: cf_source_action_def if_False)
    have b: "cf_source_action 3 (n+1) = Ordered_Matrix2 44 7 19 3"
      using mahler_cf_low_source_half_shift_three[OF n'] next_even
      by (simp only: cf_source_action_def if_True)
    show ?thesis by (subst cf_half_eq_symmetric) (simp only: a b cf_half_three_exact)
  qed
qed


lemma cf_25_singleton_actions:
  "mahler_cf_digit 2 = Ordered_Matrix2 3 1 1 0"
  "mahler_cf_digit 5 = Ordered_Matrix2 6 1 1 0"
  "mahler_cf_word [2,5] = Ordered_Matrix2 19 3 6 1"
  by (simp_all add: mahler_cf_digit_def mahler_cf_word_def ordered_matrix2_identity_def)

lemma cf_source_four_phase:
  assumes "4 \<le> n"
  shows "cf_source_action 4 n = mahler_cf_low_phase_actions 4 ! ((n-4) mod 4)"
  using mahler_cf_low_phase_selection[of 4 n] assms
  by (simp add: cf_source_action_def dyadic_unit_phase_period_def)

lemma cf_half_four_table_all:
  "(\<forall>r<4. cf_half_eq m u v w z (mahler_cf_low_phase_actions 4 ! r)
        (mahler_cf_low_phase_actions 4 ! ((r+2) mod 4))) =
    (m dvd 5*(7*u+v) \<and> m dvd 25*u)"
proof
  assume H: "\<forall>r<4. cf_half_eq m u v w z (mahler_cf_low_phase_actions 4 ! r)
        (mahler_cf_low_phase_actions 4 ! ((r+2) mod 4))"
  have a: "cf_half_eq m u v w z (Ordered_Matrix2 158 25 139 22) (Ordered_Matrix2 853 135 139 22)"
    using H[rule_format, of 0] by (simp add: mahler_cf_low_phase_table_checked)
  have b: "cf_half_eq m u v w z (Ordered_Matrix2 195 31 44 7) (Ordered_Matrix2 415 66 44 7)"
    using H[rule_format, of 1] by (simp add: mahler_cf_low_phase_table_checked)
  show "m dvd 5*(7*u+v) \<and> m dvd 25*u" using cf_half_four_exact a b by blast
next
  assume H: "m dvd 5*(7*u+v) \<and> m dvd 25*u"
  have pair: "cf_half_eq m u v w z (Ordered_Matrix2 158 25 139 22) (Ordered_Matrix2 853 135 139 22) \<and>
    cf_half_eq m u v w z (Ordered_Matrix2 195 31 44 7) (Ordered_Matrix2 415 66 44 7)"
    using cf_half_four_exact H by blast
  show "\<forall>r<4. cf_half_eq m u v w z (mahler_cf_low_phase_actions 4 ! r)
        (mahler_cf_low_phase_actions 4 ! ((r+2) mod 4))"
  proof (intro allI impI)
    fix r :: nat assume "r<4"
    then have "r=0 \<or> r=1 \<or> r=2 \<or> r=3" by arith
    then show "cf_half_eq m u v w z (mahler_cf_low_phase_actions 4 ! r)
        (mahler_cf_low_phase_actions 4 ! ((r+2) mod 4))"
      using pair cf_half_eq_symmetric[of m u v w z]
      by (auto simp: mahler_cf_low_phase_table_checked)
  qed
qed

theorem cf_source_four_half_exact:
  "(\<forall>n\<ge>4. cf_half_eq m u v w z (cf_source_action 4 n) (cf_source_action 4 (n+2))) =
    (m dvd 5*(7*u+v) \<and> m dvd 25*u)"
proof
  assume H: "\<forall>n\<ge>4. cf_half_eq m u v w z (cf_source_action 4 n) (cf_source_action 4 (n+2))"
  have a: "cf_half_eq m u v w z (Ordered_Matrix2 158 25 139 22) (Ordered_Matrix2 853 135 139 22)"
    using H[rule_format, of 4] cf_source_four_phase[of 4] cf_source_four_phase[of 6]
    by (simp add: mahler_cf_low_phase_table_checked)
  have b: "cf_half_eq m u v w z (Ordered_Matrix2 195 31 44 7) (Ordered_Matrix2 415 66 44 7)"
    using H[rule_format, of 5] cf_source_four_phase[of 5] cf_source_four_phase[of 7]
    by (simp add: mahler_cf_low_phase_table_checked)
  show "m dvd 5*(7*u+v) \<and> m dvd 25*u" using cf_half_four_exact a b by blast
next
  assume H: "m dvd 5*(7*u+v) \<and> m dvd 25*u"
  have table: "\<forall>r<4. cf_half_eq m u v w z (mahler_cf_low_phase_actions 4 ! r)
        (mahler_cf_low_phase_actions 4 ! ((r+2) mod 4))"
    using cf_half_four_table_all H by blast
  show "\<forall>n\<ge>4. cf_half_eq m u v w z (cf_source_action 4 n) (cf_source_action 4 (n+2))"
  proof (intro allI impI)
    fix n :: nat assume n: "4\<le>n"
    have p: "n+2-4 = n-4+2" using n by arith
    have idx: "((n+2-4) mod 4) = (((n-4) mod 4)+2) mod 4"
      by (simp only: p mod_add_left_eq)
    show "cf_half_eq m u v w z (cf_source_action 4 n) (cf_source_action 4 (n+2))"
      using table[rule_format, of "(n-4) mod 4"] cf_source_four_phase[OF n]
        cf_source_four_phase[of "n+2"] n by (simp only: idx; simp)
  qed
qed


ML \<open>
  val checked = @{thms cf_half_phase_unit cf_context_half_observer_delta cf_four_column_lattice mahler_cf_low_source_half_shift_three mahler_cf_lift_separation mahler_cf_ordered_row_moore_id
    mahler_cf_low_phase_table_checked mahler_cf_low_phase_selection mahler_cf_small_suffix_moore_id
    cf_fixed_context_pullback cf_half_three_exact cf_half_four_exact cf_source_half_fixed_cut
    cf_half_common_ordered_word cf_source_half_observer_sufficient cf_source_three_half_exact
    cf_25_singleton_actions cf_source_four_half_exact};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Mahler ordered row Moore proof depends on an oracle";
  val _ = if Thm_Deps.has_skip_proof checked
    then error "Skipped Mahler ordered row Moore proof" else ();
\<close>

end
