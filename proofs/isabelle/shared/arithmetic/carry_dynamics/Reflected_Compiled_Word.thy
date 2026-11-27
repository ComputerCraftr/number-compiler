theory Reflected_Compiled_Word
  imports Reflected_Dyadic_Writer
begin

text \<open>The compiler evaluates each emitted cell, including both boundary
halos.  Its result has an even extent; the unused high digits are zeros.\<close>

definition reflected_compiled_digit ::
    "nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat" where
  "reflected_compiled_digit multiplier order source i =
    (let padding = 2 ^ order + 1;
         pair = overlap_recursive order (reflected_pair_action multiplier)
           (\<lambda>j. reflected_pair_at
             (reflected_shift (2 * padding) (reflected_padded_source source))
             (i div 2 + padding - j)) 0
     in if even i then fst pair else snd pair)"

definition reflected_compiled_word :: "nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat list" where
  "reflected_compiled_word multiplier order source =
    map (reflected_compiled_digit multiplier order source)
      [0..<2 * ((length source + 1) div 2 + 2 ^ order)]"

lemma reflected_compiled_digit_exact:
  assumes "multiplier = 2 \<or> multiplier = 5"
    "reflected_decimal source"
  shows "reflected_compiled_digit multiplier order source i =
    reflected_padded_source (reflected_padded_H_iter multiplier (2 ^ order) source) i"
proof -
  note action = reflected_padded_dyadic_all_cells[OF assms, of order "i div 2"]
  have decompose: "2 * (i div 2) + i mod 2 = i"
    using div_mult_mod_eq[of i 2] by arith
  have bit: "i mod 2 = 0 \<or> i mod 2 = 1" by arith
  show ?thesis using action decompose bit
    by (auto simp: reflected_compiled_digit_def Let_def even_iff_mod_2_eq_zero)
qed

theorem reflected_compiled_word_exact:
  assumes multiplier: "multiplier = 2 \<or> multiplier = 5"
    and digits: "reflected_decimal source"
  shows "reflected_compiled_word multiplier order source =
    reflected_padded_H_iter multiplier (2 ^ order) source @
      replicate (2 * ((length source + 1) div 2) - length source) 0"
proof (rule nth_equalityI)
  show "length (reflected_compiled_word multiplier order source) =
    length (reflected_padded_H_iter multiplier (2 ^ order) source @
      replicate (2 * ((length source + 1) div 2) - length source) 0)"
    by (simp add: reflected_compiled_word_def reflected_padded_H_iter_length; arith)
  fix i
  assume bound: "i < length (reflected_compiled_word multiplier order source)"
  have total: "i < length (reflected_padded_H_iter multiplier (2 ^ order) source) +
      (2 * ((length source + 1) div 2) - length source)"
    using bound by (simp add: reflected_compiled_word_def reflected_padded_H_iter_length; arith)
  have pad_bound: "i \<ge> length (reflected_padded_H_iter multiplier (2 ^ order) source) \<Longrightarrow>
      i - length (reflected_padded_H_iter multiplier (2 ^ order) source) <
        2 * ((length source + 1) div 2) - length source"
    using total by arith
  show "reflected_compiled_word multiplier order source ! i =
      (reflected_padded_H_iter multiplier (2 ^ order) source @
        replicate (2 * ((length source + 1) div 2) - length source) 0) ! i"
    using bound pad_bound by (simp add: reflected_compiled_word_def
        reflected_compiled_digit_exact[OF multiplier digits] reflected_padded_source_def nth_append)
qed

theorem reflected_compiled_relative_interior:
  fixes a b shift :: int
  assumes m: "m = 2 \<or> m = 5" and digits: "reflected_decimal source"
    and base: "0 \<le> a" and shift: "0 \<le> shift" "shift \<le> 2"
    and returns: "\<And>j. a + 2 \<le> j \<Longrightarrow> j < b \<Longrightarrow>
      reflected_relative_two (reflected_source_two_gate m)
        (\<lambda>k. reflected_padded_source source (nat k)) j =
      reflected_padded_source source (nat (j - shift))"
    and bounds: "a + 2 * int (2 ^ order) \<le> int i" "int i < b"
  shows "reflected_compiled_digit m order source i =
    reflected_padded_source source (nat (int i - int (2 ^ order) * shift))"
  using reflected_compiled_digit_exact[OF m digits, of order i]
    reflected_padded_relative_H_interior[OF m digits base shift returns bounds]
  by simp

lemma reflected_pad_H:
  assumes "m = 2 \<or> m = 5" "reflected_pad_equiv x y"
  shows "reflected_pad_equiv (reflected_padded_H m x) (reflected_padded_H m y)"
  unfolding reflected_padded_H_def
  by (rule reflected_pad_E[OF assms(1) reflected_pad_multiply[OF assms]])

lemma reflected_pad_H_iter:
  assumes "m = 2 \<or> m = 5" "reflected_pad_equiv x y"
  shows "reflected_pad_equiv (reflected_padded_H_iter m steps x)
      (reflected_padded_H_iter m steps y)"
  using assms(2) by (induction steps) (simp_all add: reflected_pad_H[OF assms(1)])

lemma reflected_pad_high_zeros:
  assumes "reflected_decimal x"
  shows "reflected_pad_equiv (x @ replicate n 0) x"
  using assms
proof (induction n)
  case 0
  then show ?case by (simp add: reflected_pad_equiv.same)
next
  case (Suc n)
  have valid: "reflected_decimal (x @ replicate n 0)"
    using Suc.prems by (auto simp: list_all_iff)
  have "reflected_pad_equiv ((x @ replicate n 0) @ [0]) (x @ replicate n 0)"
    by (rule reflected_pad_equiv.high[OF valid])
  then have composed: "reflected_pad_equiv ((x @ replicate n 0) @ [0]) x"
    by (rule reflected_pad_equiv.compose[OF _ Suc.IH[OF Suc.prems]])
  show ?case using composed by (simp add: replicate_append_same)
qed

lemma reflected_compiled_word_padding:
  assumes "m = 2 \<or> m = 5" "reflected_decimal source"
  shows "reflected_pad_equiv (reflected_compiled_word m order source)
    (reflected_padded_H_iter m (2 ^ order) source)"
  unfolding reflected_compiled_word_exact[OF assms]
  by (rule reflected_pad_high_zeros[OF reflected_padded_H_iter_decimal[OF assms]])

fun reflected_compiled_levels :: "nat \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list" where
  "reflected_compiled_levels m [] source = source"
| "reflected_compiled_levels m (level # rest) source =
    reflected_compiled_levels m rest
      (reflected_trim_high (reflected_trim_low (reflected_compiled_word m level source)))"

lemma reflected_pad_equiv_decimal:
  "reflected_pad_equiv x y \<Longrightarrow> reflected_decimal x \<and> reflected_decimal y"
  by (induction rule: reflected_pad_equiv.induct) (auto simp: list_all_iff)

theorem reflected_compiled_levels_padding:
  assumes m: "m = 2 \<or> m = 5" and digits: "reflected_decimal source"
  shows "reflected_pad_equiv (reflected_compiled_levels m levels source)
    (reflected_dyadic_H m levels source)"
  using digits
proof (induction levels arbitrary: source)
  case Nil
  then show ?case by (simp add: reflected_pad_equiv.same)
next
  case (Cons level rest)
  let ?raw = "reflected_compiled_word m level source"
  let ?trim = "reflected_trim_high (reflected_trim_low ?raw)"
  have eq: "reflected_pad_equiv ?raw (reflected_padded_H_iter m (2 ^ level) source)"
    by (rule reflected_compiled_word_padding[OF m Cons.prems])
  have raw: "reflected_decimal ?raw" using reflected_pad_equiv_decimal[OF eq] by simp
  have low: "reflected_decimal (reflected_trim_low ?raw)"
    using raw unfolding reflected_trim_low_def list_all_iff by (auto dest: set_dropWhileD)
  have trim: "reflected_pad_equiv ?trim ?raw"
    by (rule reflected_pad_equiv.compose[OF reflected_pad_trim_high[OF low]
          reflected_pad_trim_low[OF raw]])
  have valid: "reflected_decimal ?trim" using reflected_pad_equiv_decimal[OF trim] by simp
  have next_padding: "reflected_pad_equiv ?trim (reflected_padded_H_iter m (2 ^ level) source)"
    by (rule reflected_pad_equiv.compose[OF trim eq])
  have transported: "reflected_pad_equiv (reflected_dyadic_H m rest ?trim)
      (reflected_dyadic_H m rest (reflected_padded_H_iter m (2 ^ level) source))"
    unfolding reflected_dyadic_H_exact
    by (rule reflected_pad_H_iter[OF m next_padding])
  show ?case using reflected_pad_equiv.compose[OF Cons.IH[OF valid] transported] by simp
qed

theorem reflected_compiled_levels_emit:
  assumes "m = 2 \<or> m = 5" "reflected_decimal source"
  shows "reflected_emit m (reflected_compiled_levels m levels source) =
    reflected_emit m (reflected_dyadic_H m levels source)"
  by (rule reflected_emit_respects_padding[OF assms(1)
        reflected_compiled_levels_padding[OF assms]])

theorem reflected_compiled_odd_value:
  assumes m: "m = 2 \<or> m = 5" and digits: "reflected_decimal seed"
    and canonical: "reflected_trim_high seed = seed"
  shows "decimal_lsd_value (reflected_emit m (reflected_compiled_levels m levels (rev seed))) =
    ((\<lambda>x. m * decimal_reverse x) ^^ (2 * reflected_dyadic_spans levels + 1))
      (decimal_lsd_value seed)"
  using reflected_compiled_levels_emit[OF m, of "rev seed" levels]
    reflected_dyadic_odd_value[OF m digits canonical, of levels] digits
  by (simp add: list_all_iff)

theorem reflected_compiled_even_value:
  assumes m: "m = 2 \<or> m = 5" and digits: "reflected_decimal seed"
    and canonical: "reflected_trim_high seed = seed"
  shows "decimal_lsd_value
      (reflected_emit m (reflected_compiled_levels m levels (reflected_padded_E m seed))) =
    ((\<lambda>x. m * decimal_reverse x) ^^ (2 * reflected_dyadic_spans levels + 2))
      (decimal_lsd_value seed)"
  using reflected_compiled_levels_emit[OF m reflected_padded_E_decimal[OF m digits], of levels]
    reflected_dyadic_even_value[OF m digits canonical, of levels]
  by simp

ML \<open>
  val checked = @{thms reflected_compiled_relative_interior reflected_compiled_word_exact reflected_compiled_levels_padding
    reflected_compiled_levels_emit reflected_compiled_odd_value reflected_compiled_even_value};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Reflected compiled word proof depends on an oracle";
  val _ = if Thm_Deps.has_skip_proof checked
    then error "Skipped reflected compiled word proof" else ();
\<close>

end
