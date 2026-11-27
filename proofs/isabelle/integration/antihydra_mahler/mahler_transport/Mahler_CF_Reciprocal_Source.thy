theory Mahler_CF_Reciprocal_Source
  imports Mahler_CF_Ordered_Row_Blocks
begin

text \<open>The reciprocal source keeps one authenticated power of five. The
selected later row is obtained by splitting that source at its binary cut.
No claim about an unselected row or decimal width is needed for this identity.\<close>

lemma mahler_cf_width_clock_step:
  fixes v lower threshold :: nat
  assumes "0 < lower" "threshold = 10 * lower"
    "lower \<le> v" "v < threshold"
  shows "(if 5 * v < threshold then
      lower \<le> 5 * v \<and> 5 * v < threshold
    else threshold \<le> 5 * v \<and> 5 * v < 10 * threshold)"
  using assms by (auto; arith)

definition mahler_cf_reciprocal_row :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "mahler_cf_reciprocal_row q t =
    (q div 2^t) * 10^t + (q mod 2^t) * 5^t"

theorem mahler_cf_reciprocal_row_exact:
  "mahler_cf_reciprocal_row q t = 5^t * q"
proof -
  have split: "q div 2^t * 2^t + q mod 2^t = q"
    by (rule div_mult_mod_eq)
  have ten: "(10::nat)^t = 2^t * 5^t"
    by (induction t) (simp_all add: algebra_simps)
  have scaled: "(q div 2^t * 2^t + q mod 2^t) * 5^t = q * 5^t"
    by (simp only: split)
  show ?thesis
    unfolding mahler_cf_reciprocal_row_def ten
    using scaled by (simp only: algebra_simps)
qed

text \<open>The leading place of every selected physical row in a window of
at most five is determined by the inlet alone. Equality at a threshold
belongs to the wider row, including a cut exactly at its final digit.\<close>

lemma mahler_cf_inlet_width_window:
  fixes q place :: nat
  assumes "0 < place" "place \<le> q" "q < 10 * place"
  shows "(let p = (if 2 * place \<le> q then 10 * place else 1 * place);
      v = mahler_cf_reciprocal_row q 1 in p \<le> v \<and> v < 10 * p)"
    and "(let p = (if 4 * place \<le> q then 100 * place else 10 * place);
      v = mahler_cf_reciprocal_row q 2 in p \<le> v \<and> v < 10 * p)"
    and "(let p = (if 8 * place \<le> q then 1000 * place else 100 * place);
      v = mahler_cf_reciprocal_row q 3 in p \<le> v \<and> v < 10 * p)"
    and "(let p = (if 8 * place \<le> 5 * q then 1000 * place else 100 * place);
      v = mahler_cf_reciprocal_row q 4 in p \<le> v \<and> v < 10 * p)"
  by (use assms in \<open>auto simp: Let_def mahler_cf_reciprocal_row_exact
      split: if_splits; linarith\<close>)+

theorem mahler_cf_reciprocal_physical_source:
  "mahler_cf_reciprocal_row (5^n) t = 5^(n+t)"
  using mahler_cf_reciprocal_row_exact[of "5^n" t]
  by (simp add: power_add mult.commute)

theorem mahler_cf_reciprocal_lower_fits:
  "((q::nat) mod 2^t) * 5^t < 10^t"
proof -
  have bound: "q mod 2^t < 2^t" by simp
  have ten: "(10::nat)^t = 2^t * 5^t"
    by (induction t) (simp_all add: algebra_simps)
  show ?thesis using bound unfolding ten by simp
qed

definition mahler_cf_reciprocal_selected_digits ::
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "mahler_cf_reciprocal_selected_digits q t width start count =
    (mahler_cf_reciprocal_row q t div 10^(width - start - count)) mod 10^count"

theorem mahler_cf_reciprocal_selected_physical_source:
  "mahler_cf_reciprocal_selected_digits (5^n) t width start count =
    ((5^(n+t)) div 10^(width - start - count)) mod 10^count"
  by (simp only: mahler_cf_reciprocal_selected_digits_def
      mahler_cf_reciprocal_physical_source)

lemma mahler_cf_reciprocal_first_selected_digits:
  "mahler_cf_reciprocal_selected_digits q 0 width start count =
    q div 10^(width - start - count) mod 10^count"
  by (simp add: mahler_cf_reciprocal_selected_digits_def mahler_cf_reciprocal_row_exact)

theorem mahler_cf_reciprocal_upper_cut:
  "mahler_cf_reciprocal_row q t div 10^(t+k) mod base =
     (q div 2^t div 10^k) mod base"
  "mahler_cf_reciprocal_row q (t+k) div 10^t mod base =
     ((q * 5^k) div 2^t) mod base"
proof -
  have ten: "(10::nat)^t = 5^t * 2^t"
    by (simp flip: power_mult_distrib)
  have denominator: "(10::nat)^(t+k) = 5^t * (2^t * 10^k)"
    by (simp only: power_add ten mult.assoc)
  show "mahler_cf_reciprocal_row q t div 10^(t+k) mod base =
      (q div 2^t div 10^k) mod base"
    by (simp add: mahler_cf_reciprocal_row_exact denominator div_mult2_eq[symmetric])
  have numerator: "mahler_cf_reciprocal_row q (t+k) = 5^t * (q * 5^k)"
    by (simp add: mahler_cf_reciprocal_row_exact power_add ac_simps)
  show "mahler_cf_reciprocal_row q (t+k) div 10^t mod base =
      ((q * 5^k) div 2^t) mod base"
    by (simp add: numerator ten)
qed

lemma mahler_cf_pow5_settled_two_columns:
  "((5::nat) ^ (n + 2)) mod 100 = 25"
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have "(5::nat) ^ (Suc n + 2) mod 100 =
      (5 * ((5::nat) ^ (n + 2) mod 100)) mod 100"
    by (simp add: power_Suc mod_mult_right_eq)
  also have "... = 25" using Suc.IH by simp
  finally show ?case .
qed

theorem mahler_cf_reciprocal_settled_two_columns:
  "mahler_cf_reciprocal_row (5^(n+2)) t mod 100 = 25"
proof -
  have exponent: "n + 2 + t = (n + t) + 2" by simp
  have row: "mahler_cf_reciprocal_row (5^(n+2)) t = 5^((n+t)+2)"
    by (simp only: mahler_cf_reciprocal_physical_source exponent)
  show ?thesis by (simp only: row mahler_cf_pow5_settled_two_columns)
qed

lemma mahler_cf_settled_upper_step:
  fixes x :: nat
  assumes "x mod 100 = 25"
  shows "(5*x) div 100 = 5*(x div 100)+1"
proof -
  have source: "x div 100 * 100 + 25 = x"
    using div_mult_mod_eq[of x 100] assms by simp
  have split: "5 * x = (5 * (x div 100) + 1) * 100 + 25"
  proof -
    have "5 * x = 5 * (x div 100 * 100 + 25)"
      by (rule arg_cong[OF source[symmetric], where f="\<lambda>q. 5*q"])
    also have "... = (5 * (x div 100) + 1) * 100 + 25"
      by (simp add: algebra_simps)
    finally show ?thesis .
  qed
  show ?thesis by (simp only: split; simp)
qed

theorem mahler_cf_settled_upper_physical_run:
  "((\<lambda>u::nat. 5*u+1) ^^ ticks) (5^(n+2) div 100) =
    mahler_cf_reciprocal_row (5^(n+2)) ticks div 100"
proof (induction ticks)
  case 0
  then show ?case by (simp add: mahler_cf_reciprocal_row_exact)
next
  case (Suc t)
  let ?x = "mahler_cf_reciprocal_row (5^(n+2)) t"
  have next_row: "mahler_cf_reciprocal_row (5^(n+2)) (Suc t) = 5 * ?x"
    by (simp add: mahler_cf_reciprocal_row_exact power_Suc ac_simps)
  show ?case
    using mahler_cf_settled_upper_step[OF mahler_cf_reciprocal_settled_two_columns[of n t]]
    by (simp only: funpow.simps comp_apply Suc.IH next_row)
qed

theorem mahler_cf_reciprocal_suffix_25_action:
  "mahler_cf_word (mahler_cf_decimal_digits 2
      (mahler_cf_reciprocal_row (5^(n+2)) t mod 100)) =
    Ordered_Matrix2 19 3 6 1"
  apply (subst mahler_cf_reciprocal_settled_two_columns)
  by (simp add: mahler_cf_decimal_digits_def mahler_cf_word_def mahler_cf_digit_def
      ordered_matrix2_identity_def upt_rec)

corollary mahler_cf_reciprocal_suffix_25_after_prefix:
  "mahler_cf_word (prefix @ mahler_cf_decimal_digits 2
      (mahler_cf_reciprocal_row (5^(n+2)) t mod 100)) =
    ordered_matrix2_multiply (mahler_cf_word prefix) (Ordered_Matrix2 19 3 6 1)"
  by (simp only: mahler_cf_word_append mahler_cf_reciprocal_suffix_25_action)

text \<open>The issuer checks the significant interval for every selected
row before publishing an ordered action. The row-major product keeps the
complete intervening digits of each physical row.\<close>

theorem mahler_cf_reciprocal_row_major_consumer:
  fixes n rows :: nat and widths :: "nat \<Rightarrow> nat"
  assumes significant: "\<And>t. t < rows \<Longrightarrow>
    10^(widths t - 1) \<le> (5::nat)^(n+t) \<and> (5::nat)^(n+t) < 10^(widths t)"
  shows "mahler_cf_word (concat (map (\<lambda>t.
      mahler_cf_decimal_digits (widths t) (mahler_cf_reciprocal_row (5^n) t))
      [0..<rows])) =
    mahler_cf_word (concat (map (\<lambda>t.
      mahler_cf_decimal_digits (widths t) (5^(n+t))) [0..<rows]))"
    "\<And>t. t < rows \<Longrightarrow>
      10^(widths t - 1) \<le> mahler_cf_reciprocal_row (5^n) t \<and>
      mahler_cf_reciprocal_row (5^n) t < 10^(widths t)"
  using significant by (simp_all only: mahler_cf_reciprocal_physical_source)

text \<open>The selected block can begin and end inside physical rows. The
issuer authenticates the significant width of every row in that block.\<close>

theorem mahler_cf_reciprocal_clipped_first_physical_prefix:
  fixes n rows start count index :: nat and widths :: "nat \<Rightarrow> nat"
    and low high :: real and prefix :: "nat list"
  defines "emitted \<equiv> take count (drop start (concat (map (\<lambda>t.
    mahler_cf_decimal_digits (widths t) (mahler_cf_reciprocal_row (5^n) t)) [0..<rows])))"
  assumes significant: "\<And>t. t < rows \<Longrightarrow>
      10^(widths t - 1) \<le> (5::nat)^(n+t) \<and> (5::nat)^(n+t) < 10^(widths t)"
    and old: "\<not> mahler_cf_guard_contains_prefix low high prefix"
    and before: "\<And>j. j < index \<Longrightarrow>
      \<not> mahler_cf_guard_contains_prefix low high (prefix @ take j emitted)"
    and found: "mahler_cf_guard_contains_prefix low high (prefix @ take index emitted)"
    and inside: "index \<le> length emitted"
  shows "mahler_cf_guard_contains_prefix low high
      (take (length prefix + index) (prefix @ take count (drop start (concat (map (\<lambda>t.
        mahler_cf_decimal_digits (widths t) (5^(n+t))) [0..<rows])))))"
    "\<And>j. j < length prefix + index \<Longrightarrow>
      \<not> mahler_cf_guard_contains_prefix low high
        (take j (prefix @ take count (drop start (concat (map (\<lambda>t.
          mahler_cf_decimal_digits (widths t) (5^(n+t))) [0..<rows])))))"
    "\<And>t. t < rows \<Longrightarrow>
      10^(widths t - 1) \<le> mahler_cf_reciprocal_row (5^n) t \<and>
      mahler_cf_reciprocal_row (5^n) t < 10^(widths t)"
proof -
  have selected: "emitted = take count (drop start (concat (map (\<lambda>t.
      mahler_cf_decimal_digits (widths t) (5^(n+t))) [0..<rows])))"
    by (simp only: emitted_def mahler_cf_reciprocal_physical_source)
  have hit: "mahler_cf_guard_contains_prefix low high
      (take (length prefix + index) (prefix @ emitted))"
    by (rule mahler_cf_block_prefix_global_earliest(1)[where index=index])
       (fact old before found inside)+
  show "mahler_cf_guard_contains_prefix low high
      (take (length prefix + index) (prefix @ take count (drop start (concat (map (\<lambda>t.
        mahler_cf_decimal_digits (widths t) (5^(n+t))) [0..<rows])))))"
    using hit
    by (simp only: selected)
  show "\<And>j. j < length prefix + index \<Longrightarrow>
      \<not> mahler_cf_guard_contains_prefix low high
        (take j (prefix @ take count (drop start (concat (map (\<lambda>t.
          mahler_cf_decimal_digits (widths t) (5^(n+t))) [0..<rows])))))"
  proof -
    fix j assume j: "j < length prefix + index"
    have missed: "\<not> mahler_cf_guard_contains_prefix low high
        (take j (prefix @ emitted))"
      by (rule mahler_cf_block_prefix_global_earliest(2)[where index=index])
         (fact old before found inside j)+
    show "\<not> mahler_cf_guard_contains_prefix low high
        (take j (prefix @ take count (drop start (concat (map (\<lambda>t.
          mahler_cf_decimal_digits (widths t) (5^(n+t))) [0..<rows])))))"
      using missed
      by (simp only: selected; simp)
  qed
  show "\<And>t. t < rows \<Longrightarrow>
      10^(widths t - 1) \<le> mahler_cf_reciprocal_row (5^n) t \<and>
      mahler_cf_reciprocal_row (5^n) t < 10^(widths t)"
    using significant by (simp only: mahler_cf_reciprocal_physical_source)
qed

ML \<open>
  val checked = @{thms mahler_cf_reciprocal_upper_cut mahler_cf_inlet_width_window
    mahler_cf_reciprocal_first_selected_digits mahler_cf_width_clock_step mahler_cf_reciprocal_row_exact
    mahler_cf_reciprocal_physical_source mahler_cf_reciprocal_lower_fits
    mahler_cf_pow5_settled_two_columns mahler_cf_reciprocal_settled_two_columns
    mahler_cf_settled_upper_physical_run mahler_cf_settled_upper_step
    mahler_cf_reciprocal_suffix_25_action mahler_cf_reciprocal_suffix_25_after_prefix
    mahler_cf_reciprocal_selected_physical_source
    mahler_cf_reciprocal_row_major_consumer mahler_cf_reciprocal_clipped_first_physical_prefix};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Mahler reciprocal source depends on an oracle";
  val _ = if Thm_Deps.has_skip_proof checked
    then error "Skipped Mahler reciprocal source proof" else ();
\<close>

end
