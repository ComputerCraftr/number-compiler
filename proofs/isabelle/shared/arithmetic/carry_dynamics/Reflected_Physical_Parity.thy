theory Reflected_Physical_Parity
  imports Reflected_Padded_Orbit Decimal_Word_Reversal
begin

text \<open>Inner H tiles may have zero padding at either boundary. The final
multiplication preserves its physical low digit, including a genuine zero.\<close>

abbreviation reflected_decimal where
  "reflected_decimal xs \<equiv> list_all (\<lambda>d. d < (10::nat)) xs"

inductive reflected_pad_equiv :: "nat list \<Rightarrow> nat list \<Rightarrow> bool" where
  same: "reflected_decimal x \<Longrightarrow> reflected_pad_equiv x x"
| low: "reflected_decimal x \<Longrightarrow> reflected_pad_equiv (0#x) x"
| high: "reflected_decimal x \<Longrightarrow> reflected_pad_equiv (x@[0]) x"
| compose: "reflected_pad_equiv x y \<Longrightarrow> reflected_pad_equiv y z \<Longrightarrow>
    reflected_pad_equiv x z"
| symmetric: "reflected_pad_equiv x y \<Longrightarrow> reflected_pad_equiv y x"

lemma reflected_pad_reverse:
  "reflected_pad_equiv x y \<Longrightarrow> reflected_pad_equiv (rev x) (rev y)"
  by (induction rule: reflected_pad_equiv.induct)
     (auto simp: list_all_iff intro!: reflected_pad_equiv.same reflected_pad_equiv.high
       reflected_pad_equiv.low intro: reflected_pad_equiv.compose reflected_pad_equiv.symmetric)

lemma reflected_pad_trim_low:
  "reflected_decimal x \<Longrightarrow> reflected_pad_equiv (reflected_trim_low x) x"
proof (induction x)
  case Nil
  then show ?case by (simp add: reflected_trim_low_def reflected_pad_equiv.same)
next
  case (Cons d ds)
  show ?case
  proof (cases "d=0")
    case True
    have rest: "reflected_decimal ds" using Cons.prems by simp
    have link: "reflected_pad_equiv ds (0#ds)"
      by (rule reflected_pad_equiv.symmetric[OF reflected_pad_equiv.low[OF rest]])
    show ?thesis using reflected_pad_equiv.compose[OF Cons.IH[OF rest] link] True
      by (simp add: reflected_trim_low_def)
  next
    case False
    then show ?thesis using Cons.prems by (simp add: reflected_trim_low_def reflected_pad_equiv.same)
  qed
qed

lemma reflected_pad_trim_high:
  assumes "reflected_decimal x"
  shows "reflected_pad_equiv (reflected_trim_high x) x"
proof -
  have "reflected_decimal (rev x)" using assms by (simp add: list_all_iff)
  from reflected_pad_reverse[OF reflected_pad_trim_low[OF this]] show ?thesis
    by (simp add: reflected_trim_low_def reflected_trim_high_def)
qed

lemma reflected_valid_append_zero:
  assumes m: "m=2 \<or> m=5" and valid: "reflected_decimal x"
  shows "reflected_padded_multiply m (x@[0]) = reflected_padded_multiply m x @ [0]"
proof -
  have inlet: "0<m" using m by arith
  have "snd (decimal_block_run m x 0)<m"
    by (rule reflected_digit_pass_carry_bound[OF m valid inlet])
  with m have "snd (decimal_block_run m x 0)<10" by arith
  then show ?thesis by (rule reflected_padded_multiply_append_zero)
qed

lemma reflected_pad_multiply:
  assumes m: "m=2 \<or> m=5" and eq: "reflected_pad_equiv x y"
  shows "reflected_pad_equiv (reflected_padded_multiply m x) (reflected_padded_multiply m y)"
  using eq
  by (induction rule: reflected_pad_equiv.induct)
     (auto simp: reflected_padded_multiply_zero_low_digit reflected_valid_append_zero[OF m]
       intro: reflected_padded_multiply_decimal[OF m] reflected_pad_equiv.intros)

lemma reflected_pad_E:
  assumes "m=2 \<or> m=5" "reflected_pad_equiv x y"
  shows "reflected_pad_equiv (reflected_padded_E m x) (reflected_padded_E m y)"
  unfolding reflected_padded_E_def
  by (rule reflected_pad_reverse[OF reflected_pad_multiply[OF assms(1) reflected_pad_reverse[OF assms(2)]]])

definition reflected_emit :: "nat \<Rightarrow> nat list \<Rightarrow> nat list" where
  "reflected_emit m x =
     reflected_trim_high (reflected_padded_multiply m (reflected_trim_low x))"

lemma reflected_emit_high:
  assumes m: "m=2 \<or> m=5"
  shows "reflected_decimal x \<Longrightarrow> reflected_emit m (x@[0]) = reflected_emit m x"
proof (induction x)
  case Nil
  then show ?case by (simp add: reflected_emit_def reflected_trim_low_def)
next
  case (Cons d ds)
  show ?case
  proof (cases "d=0")
    case True
    then show ?thesis using Cons.IH Cons.prems
      by (simp add: reflected_emit_def reflected_trim_low_def)
  next
    case False
    have eq: "reflected_padded_multiply m ((d#ds)@[0]) =
        reflected_padded_multiply m (d#ds)@[0]"
      by (rule reflected_valid_append_zero[OF m Cons.prems])
    show ?thesis using False eq
      by (simp add: reflected_emit_def reflected_trim_low_def reflected_trim_high_def)
  qed
qed

lemma reflected_emit_respects_padding:
  assumes m: "m=2 \<or> m=5" and eq: "reflected_pad_equiv x y"
  shows "reflected_emit m x = reflected_emit m y"
  using eq
proof (induction rule: reflected_pad_equiv.induct)
  case (low x)
  then show ?case by (simp add: reflected_emit_def reflected_trim_low_def)
next
  case (high x)
  then show ?case by (rule reflected_emit_high[OF m])
qed auto

lemma reflected_two_ticks_from_emission:
  assumes m: "m=2 \<or> m=5" and valid: "reflected_decimal x"
  shows "reflected_physical_word m (reflected_physical_word m (reflected_emit m x)) =
      reflected_emit m (reflected_padded_H m x)"
proof -
  have trimmed: "reflected_decimal (reflected_trim_low x)"
    using valid unfolding reflected_trim_low_def list_all_iff
    by (meson set_dropWhileD)
  have eq: "reflected_pad_equiv (reflected_emit m x) (reflected_padded_multiply m x)"
    unfolding reflected_emit_def
    by (rule reflected_pad_equiv.compose[OF reflected_pad_trim_high[OF
        reflected_padded_multiply_decimal[OF m trimmed]]
        reflected_pad_multiply[OF m reflected_pad_trim_low[OF valid]]])
  have transported: "reflected_emit m (reflected_padded_E m (reflected_emit m x)) =
      reflected_emit m (reflected_padded_E m (reflected_padded_multiply m x))"
    by (rule reflected_emit_respects_padding[OF m reflected_pad_E[OF m eq]])
  show ?thesis using transported
    by (simp only: reflected_physical_two_step_padded reflected_padded_H_def
        reflected_emit_def reflected_trim_low_def)
qed

theorem reflected_emitted_orbit:
  assumes m: "m=2 \<or> m=5" and valid: "reflected_decimal x"
  shows "(reflected_physical_word m ^^ (2*k)) (reflected_emit m x) =
      reflected_emit m (reflected_padded_H_iter m k x)"
proof (induction k)
  case 0
  then show ?case by simp
next
  case (Suc k)
  have valid_k: "reflected_decimal (reflected_padded_H_iter m k x)"
    by (rule reflected_padded_H_iter_decimal[OF m valid])
  have count: "2*Suc k = Suc (Suc (2*k))" by simp
  show ?case by (simp only: count funpow.simps comp_apply Suc.IH
    reflected_two_ticks_from_emission[OF m valid_k] reflected_padded_H_iter.simps)
qed

theorem reflected_odd_endpoint:
  assumes m: "m=2 \<or> m=5" and digits: "reflected_decimal seed"
    and canonical: "reflected_trim_high seed = seed"
  shows "(reflected_physical_word m ^^ (2*k+1)) seed =
    reflected_emit m (reflected_padded_H_iter m k (rev seed))"
proof -
  have inlet: "reflected_trim_low (rev seed) = rev seed"
    using arg_cong[where f=rev, OF canonical]
    by (simp add: reflected_trim_low_def reflected_trim_high_def)
  have first: "reflected_physical_word m seed = reflected_emit m (rev seed)"
    by (simp only: reflected_physical_word_def reflected_emit_def inlet)
  have valid: "reflected_decimal (rev seed)" using digits by (simp add: list_all_iff)
  have once: "(reflected_physical_word m ^^ 1) seed = reflected_physical_word m seed"
    by simp
  show ?thesis using reflected_emitted_orbit[OF m valid, of k]
    by (simp only: funpow_add comp_apply once first)
qed

theorem reflected_even_endpoint:
  assumes m: "m=2 \<or> m=5" and digits: "reflected_decimal seed"
  shows "(reflected_physical_word m ^^ (2*k+2)) seed =
    reflected_emit m (reflected_padded_H_iter m k (reflected_padded_E m seed))"
proof -
  have first: "(reflected_physical_word m ^^ 2) seed =
      reflected_emit m (reflected_padded_E m seed)"
    by (simp add: numeral_eq_Suc reflected_physical_two_step_padded reflected_emit_def reflected_trim_low_def)
  have valid: "reflected_decimal (reflected_padded_E m seed)"
    by (rule reflected_padded_E_decimal[OF m digits])
  show ?thesis using reflected_emitted_orbit[OF m valid, of k]
    by (simp only: funpow_add comp_apply first)
qed

lemma reflected_physical_word_one_step:
  assumes "reflected_decimal source" "source \<noteq> []" "last source > 0"
  shows "decimal_lsd_value (reflected_physical_word m source) =
    m * decimal_reverse (decimal_lsd_value source)"
  using decimal_reverse_lsd_value[OF assms] reflected_physical_word_value[of m source]
  by (simp only: reflected_msf_value_def)

lemma reflected_physical_clock_value:
  assumes m: "m=2 \<or> m=5" and digits: "reflected_decimal source"
    and canonical: "reflected_trim_high source = source"
  shows "decimal_lsd_value ((reflected_physical_word m ^^ ticks) source) =
    ((\<lambda>x. m * decimal_reverse x) ^^ ticks) (decimal_lsd_value source)"
  using digits canonical
proof (induction ticks arbitrary: source)
  case 0
  then show ?case by simp
next
  case (Suc k)
  let ?next = "reflected_physical_word m source"
  have rev_valid: "reflected_decimal (rev source)"
    using Suc.prems(1) by (simp add: list_all_iff)
  have valid: "reflected_decimal ?next"
    using reflected_padded_multiply_decimal[OF m rev_valid]
    unfolding reflected_physical_word_def reflected_trim_high_def list_all_iff
    by (auto dest: set_dropWhileD)
  have canonical: "reflected_trim_high ?next = ?next"
    by (simp add: reflected_trim_high_def reflected_physical_word_def)
  have step: "decimal_lsd_value ?next = m * decimal_reverse (decimal_lsd_value source)"
  proof (cases "source=[]")
    case True
    then show ?thesis by (simp add: reflected_physical_word_zero)
  next
    case False
    have trim: "dropWhile ((=) 0) (rev source) = rev source"
      using arg_cong[where f=rev, OF Suc.prems(2)] by (simp add: reflected_trim_high_def)
    have high: "last source > 0"
      using trim False by (simp add: dropWhile_eq_self_iff hd_rev)
    show ?thesis by (rule reflected_physical_word_one_step[OF Suc.prems(1) False high])
  qed
  show ?case using Suc.IH[OF valid canonical]
    by (simp only: funpow_Suc_right comp_apply step)
qed

ML \<open>
  val checked = @{thms reflected_odd_endpoint reflected_even_endpoint reflected_physical_clock_value};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Reflected parity endpoint depends on an oracle";
\<close>

end
