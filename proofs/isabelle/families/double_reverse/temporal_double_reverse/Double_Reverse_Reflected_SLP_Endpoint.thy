theory Double_Reverse_Reflected_SLP_Endpoint
  imports Double_Reverse_Reflected_SLP_Blocks Double_Reverse_Reflected_SLP_Normalization
    Double_Reverse_Reflected_SLP_Emission Double_Reverse_Reflected_Writer
begin

text \<open>The word equations describe interval observation of the staged
publisher. Each power uses a normalized previous word, and the final
observation uses that same normalization. Reification into a representative
SLP states the extensional contract of the block-grammar publisher.\<close>

abbreviation reflected_slp_lsd_digits where
  "reflected_slp_lsd_digits source \<equiv> reflected_lsd_digits_of_cells (double_reverse_source_slp_word source)"

fun reflected_slp_stages ::
    "nat \<Rightarrow> nat list \<Rightarrow> double_reverse_source_slp \<Rightarrow> double_reverse_source_slp" where
  "reflected_slp_stages m [] source = reflected_slp_normalize source"
| "reflected_slp_stages m (order # rest) source = reflected_slp_stages m rest
    (reflected_writer_word (reflected_slp_stage_word m order (reflected_slp_normalize source)))"

lemma reflected_lsd_digits_of_cells_valid_inverse:
  assumes "reflected_decimal (reflected_lsd_digits_of_cells cells)"
  shows "list_all (\<lambda>c. c < 100) cells"
  using assms by (induction cells) (simp_all add: div_less_iff_less_mult)

fun reflected_slp_pair_digits :: "nat list \<Rightarrow> nat list" where
  "reflected_slp_pair_digits [] = []"
| "reflected_slp_pair_digits [low] = [low]"
| "reflected_slp_pair_digits (low # high # rest) =
    (low + 10 * high) # reflected_slp_pair_digits rest"

lemma reflected_slp_pair_digits_decoded:
  assumes "reflected_decimal digits"
  shows "\<exists>padding. reflected_lsd_digits_of_cells (reflected_slp_pair_digits digits) =
    digits @ replicate padding 0"
  using assms
proof (induction digits rule: reflected_slp_pair_digits.induct)
  case 1
  show ?case by (rule exI[of _ 0]) simp
next
  case (2 low)
  have digit: "low < 10" using "2.prems" by simp
  show ?case using digit by (intro exI[of _ 1]) simp
next
  case (3 low high rest)
  have low: "low < 10" and rest: "reflected_decimal rest" using "3.prems" by simp_all
  obtain padding where decoded:
    "reflected_lsd_digits_of_cells (reflected_slp_pair_digits rest) = rest @ replicate padding 0"
    using "3.IH"[OF rest] by blast
  have l: "(low + 10 * high) mod 10 = low" using low by simp
  have h: "(low + 10 * high) div 10 = high" using low by simp
  show ?case by (rule exI[of _ padding]) (simp only: reflected_slp_pair_digits.simps
    reflected_lsd_digits_of_cells.simps l h decoded append_Cons)
qed

definition reflected_slp_digit_inlet :: "nat list \<Rightarrow> double_reverse_source_slp" where
  "reflected_slp_digit_inlet digits = reflected_writer_word (reflected_slp_pair_digits digits)"

lemma reflected_slp_digit_inlet_exact:
  assumes "reflected_decimal digits"
  shows "reflected_pad_equiv (reflected_slp_lsd_digits (reflected_slp_digit_inlet digits)) digits"
proof -
  obtain padding where decoded:
    "reflected_lsd_digits_of_cells (reflected_slp_pair_digits digits) = digits @ replicate padding 0"
    using reflected_slp_pair_digits_decoded[OF assms] by blast
  show ?thesis
    unfolding reflected_slp_digit_inlet_def reflected_writer_word_exact decoded
    by (rule reflected_pad_high_zeros[OF assms])
qed

lemma reflected_slp_digit_inlet_valid:
  assumes "reflected_decimal digits"
  shows "list_all (\<lambda>c. c < 100) (double_reverse_source_slp_word (reflected_slp_digit_inlet digits))"
  by (rule reflected_lsd_digits_of_cells_valid_inverse)
     (rule conjunct1[OF reflected_pad_equiv_decimal[OF reflected_slp_digit_inlet_exact[OF assms]]])

lemma reflected_slp_reverse_inlet_valid:
  "reflected_decimal digits \<Longrightarrow> reflected_decimal (rev digits)"
  by (simp add: list_all_iff)

theorem reflected_slp_stages_normalized:
  assumes m: "m = 2 \<or> m = 5"
    and input: "list_all (\<lambda>c. c < 100) (double_reverse_source_slp_word source)"
  shows "reflected_pad_equiv (reflected_slp_lsd_digits (reflected_slp_stages m levels source))
      (reflected_dyadic_H m levels (reflected_slp_lsd_digits source)) \<and>
    (reflected_trim_low (reflected_slp_lsd_digits (reflected_slp_stages m levels source)) =
      reflected_slp_lsd_digits (reflected_slp_stages m levels source) \<or>
      decimal_lsd_value (reflected_slp_lsd_digits (reflected_slp_stages m levels source)) = 0)"
  using input
proof (induction levels arbitrary: source)
  case Nil
  show ?case
    unfolding reflected_slp_stages.simps reflected_dyadic_H.simps
    by (rule conjI[OF reflected_slp_normalize_padding[OF Nil.prems]
      reflected_slp_normalize_emit_inlet[OF Nil.prems]])
next
  case (Cons order rest)
  let ?digits = "reflected_slp_lsd_digits source"
  let ?normalized = "reflected_slp_normalize source"
  let ?flat = "reflected_slp_lsd_digits ?normalized"
  let ?raw = "reflected_writer_word (reflected_slp_stage_word m order ?normalized)"
  have initial: "reflected_pad_equiv ?flat ?digits"
    by (rule reflected_slp_normalize_padding[OF Cons.prems])
  have normalized_decimal: "reflected_decimal ?flat"
    using reflected_pad_equiv_decimal[OF initial] by simp
  have compiled: "reflected_slp_lsd_digits ?raw = reflected_compiled_word m order ?flat"
    using reflected_slp_stage_word_compiled[OF m normalized_decimal, of order]
    by (simp only: reflected_writer_word_exact)
  have raw_pad: "reflected_pad_equiv (reflected_slp_lsd_digits ?raw)
      (reflected_padded_H_iter m (2^order) ?flat)"
    unfolding compiled by (rule reflected_compiled_word_padding[OF m normalized_decimal])
  have raw_valid: "list_all (\<lambda>c. c < 100) (double_reverse_source_slp_word ?raw)"
    using reflected_pad_equiv_decimal[OF raw_pad]
    by (blast intro: reflected_lsd_digits_of_cells_valid_inverse)
  have input_transport: "reflected_pad_equiv (reflected_padded_H_iter m (2^order) ?flat)
      (reflected_padded_H_iter m (2^order) ?digits)"
    by (rule reflected_pad_H_iter[OF m initial])
  have tail_transport: "reflected_pad_equiv (reflected_dyadic_H m rest (reflected_slp_lsd_digits ?raw))
      (reflected_dyadic_H m rest (reflected_padded_H_iter m (2^order) ?digits))"
    unfolding reflected_dyadic_H_exact
    by (rule reflected_pad_H_iter[OF m reflected_pad_equiv.compose[OF raw_pad input_transport]])
  note tail = Cons.IH[OF raw_valid]
  note eq = reflected_pad_equiv.compose[OF conjunct1[OF tail] tail_transport]
  show ?case
    unfolding reflected_slp_stages.simps reflected_dyadic_H.simps
    by (rule conjI[OF eq conjunct2[OF tail]])
qed

definition reflected_slp_untrimmed_digits ::
  "nat \<Rightarrow> nat list \<Rightarrow> double_reverse_source_slp \<Rightarrow> nat list" where
  "reflected_slp_untrimmed_digits m levels source =
    double_reverse_source_slp_word (reflected_slp_cell_digits
      (reflected_slp_scale_cells m (reflected_slp_stages m levels source)))"

definition reflected_slp_primary_digits ::
  "nat \<Rightarrow> nat list \<Rightarrow> double_reverse_source_slp \<Rightarrow> nat list" where
  "reflected_slp_primary_digits m levels source =
    reflected_msd_drop_one_zero (reflected_slp_untrimmed_digits m levels source)"

theorem reflected_slp_primary_value:
  assumes m: "m = 2 \<or> m = 5"
    and input: "list_all (\<lambda>c. c < 100) (double_reverse_source_slp_word source)"
    and inlet: "reflected_pad_equiv (reflected_slp_lsd_digits source) digits"
  shows "decimal_lsd_value (rev (reflected_slp_primary_digits m levels source)) =
    decimal_lsd_value (reflected_emit m (reflected_dyadic_H m levels digits))"
proof -
  let ?final = "reflected_slp_stages m levels source"
  let ?flat = "reflected_slp_lsd_digits ?final"
  note stages = reflected_slp_stages_normalized[OF m input, of levels]
  have result: "reflected_pad_equiv ?flat
      (reflected_dyadic_H m levels (reflected_slp_lsd_digits source))"
    by (rule conjunct1[OF stages])
  have normalized: "reflected_trim_low ?flat = ?flat \<or> decimal_lsd_value ?flat = 0"
    by (rule conjunct2[OF stages])
  have valid: "list_all (\<lambda>c. c < 100) (double_reverse_source_slp_word ?final)"
    by (rule reflected_lsd_digits_of_cells_valid_inverse)
       (rule conjunct1[OF reflected_pad_equiv_decimal[OF result]])
  have emit:
    "decimal_lsd_value (rev (reflected_slp_primary_digits m levels source)) =
      decimal_lsd_value (reflected_emit m ?flat)"
    unfolding reflected_slp_primary_digits_def reflected_slp_untrimmed_digits_def
    by (rule reflected_slp_emission_reflected_emit_value[OF m valid normalized])
  have transport: "reflected_pad_equiv (reflected_dyadic_H m levels (reflected_slp_lsd_digits source))
      (reflected_dyadic_H m levels digits)"
    unfolding reflected_dyadic_H_exact by (rule reflected_pad_H_iter[OF m inlet])
  show ?thesis using emit
    by (simp only: reflected_emit_respects_padding[OF m reflected_pad_equiv.compose[OF result transport]])
qed

corollary reflected_slp_odd_endpoint_value:
  assumes m: "m = 2 \<or> m = 5"
    and input: "list_all (\<lambda>c. c < 100) (double_reverse_source_slp_word source)"
    and seed: "reflected_decimal seed" "reflected_trim_high seed = seed"
    and inlet: "reflected_pad_equiv (reflected_slp_lsd_digits source) (rev seed)"
  shows "decimal_lsd_value (rev (reflected_slp_primary_digits m levels source)) =
    ((\<lambda>x. m * decimal_reverse x) ^^ (2 * reflected_dyadic_spans levels + 1)) (decimal_lsd_value seed)"
  using reflected_slp_primary_value[OF m input inlet, of levels]
    reflected_dyadic_odd_value[OF m seed, of levels] by simp

corollary reflected_slp_five_even_endpoint_value:
  assumes input: "list_all (\<lambda>c. c < 100) (double_reverse_source_slp_word source)"
    and seed: "reflected_decimal seed" "reflected_trim_high seed = seed"
    and inlet: "reflected_pad_equiv (reflected_slp_lsd_digits source) (reflected_padded_E 5 seed)"
  shows "decimal_lsd_value (rev (reflected_slp_primary_digits 5 levels source)) =
    ((\<lambda>x. 5 * decimal_reverse x) ^^ (2 * reflected_dyadic_spans levels + 2)) (decimal_lsd_value seed)"
proof -
  have five: "(5::nat)=2 \<or> 5=5" by simp
  show ?thesis using reflected_slp_primary_value[OF five input inlet, of levels]
    reflected_dyadic_even_value[OF five seed, of levels] by simp
qed

corollary reflected_slp_two_even_endpoint_value:
  assumes input: "list_all (\<lambda>c. c < 100) (double_reverse_source_slp_word source)"
    and seed: "reflected_decimal seed" "reflected_trim_high seed = seed"
    and inlet: "reflected_pad_equiv (reflected_slp_lsd_digits source) (rev seed)"
  shows "decimal_lsd_value (reflected_even_final_columns
      (dropWhile ((=) 0) (reflected_slp_untrimmed_digits 2 levels source))) =
    ((\<lambda>x. 2 * decimal_reverse x) ^^ (2 * reflected_dyadic_spans levels + 2)) (decimal_lsd_value seed)"
proof -
  let ?final = "reflected_slp_stages 2 levels source"
  let ?msd = "reflected_slp_untrimmed_digits 2 levels source"
  have two: "(2::nat)=2 \<or> 2=5" by simp
  have normalized: "reflected_pad_equiv (reflected_slp_lsd_digits ?final)
      (reflected_dyadic_H 2 levels (reflected_slp_lsd_digits source))"
    by (rule conjunct1[OF reflected_slp_stages_normalized[OF two input, of levels]])
  have valid: "list_all (\<lambda>c. c < 100) (double_reverse_source_slp_word ?final)"
    by (rule reflected_lsd_digits_of_cells_valid_inverse)
       (rule conjunct1[OF reflected_pad_equiv_decimal[OF normalized]])
  have decimal: "reflected_decimal ?msd"
    unfolding reflected_slp_untrimmed_digits_def
    by (rule reflected_slp_scaled_decimal_valid[OF two valid])
  have odd: "decimal_lsd_value (rev ?msd) =
      ((\<lambda>x. 2 * decimal_reverse x) ^^ (2 * reflected_dyadic_spans levels + 1)) (decimal_lsd_value seed)"
    using reflected_slp_odd_endpoint_value[OF two input seed inlet, of levels]
    by (simp only: reflected_slp_primary_digits_def reflected_msd_drop_one_zero_value)
  have clock: "2 * reflected_dyadic_spans levels + 2 = Suc (2 * reflected_dyadic_spans levels + 1)"
    by simp
  have recurrence:
    "((\<lambda>x. 2 * decimal_reverse x) ^^ (2 * reflected_dyadic_spans levels + 2)) (decimal_lsd_value seed) =
      2 * decimal_reverse (((\<lambda>x. 2 * decimal_reverse x) ^^ (2 * reflected_dyadic_spans levels + 1))
        (decimal_lsd_value seed))"
    by (simp only: clock funpow.simps(2) o_apply)
  show ?thesis
    by (simp only: reflected_even_final_arbitrary_msd[OF decimal] odd recurrence)
qed

corollary reflected_slp_odd_from_seed:
  assumes m: "m = 2 \<or> m = 5"
    and seed: "reflected_decimal seed" "reflected_trim_high seed = seed"
  shows "decimal_lsd_value (rev (reflected_slp_primary_digits m levels
      (reflected_slp_digit_inlet (rev seed)))) =
    ((\<lambda>x. m * decimal_reverse x) ^^ (2 * reflected_dyadic_spans levels + 1)) (decimal_lsd_value seed)"
proof -
  have digits: "reflected_decimal (rev seed)" by (rule reflected_slp_reverse_inlet_valid[OF seed(1)])
  show ?thesis
    by (rule reflected_slp_odd_endpoint_value[OF m reflected_slp_digit_inlet_valid[OF digits]
          seed reflected_slp_digit_inlet_exact[OF digits]])
qed

corollary reflected_slp_five_even_from_seed:
  assumes seed: "reflected_decimal seed" "reflected_trim_high seed = seed"
  shows "decimal_lsd_value (rev (reflected_slp_primary_digits 5 levels
      (reflected_slp_digit_inlet (reflected_padded_E 5 seed)))) =
    ((\<lambda>x. 5 * decimal_reverse x) ^^ (2 * reflected_dyadic_spans levels + 2)) (decimal_lsd_value seed)"
proof -
  have five: "(5::nat)=2 \<or> 5=5" by simp
  have digits: "reflected_decimal (reflected_padded_E 5 seed)"
    by (rule reflected_padded_E_decimal[OF five seed(1)])
  show ?thesis
    by (rule reflected_slp_five_even_endpoint_value[OF reflected_slp_digit_inlet_valid[OF digits]
          seed reflected_slp_digit_inlet_exact[OF digits]])
qed

corollary reflected_slp_two_even_from_seed:
  assumes seed: "reflected_decimal seed" "reflected_trim_high seed = seed"
  shows "decimal_lsd_value (reflected_even_final_columns
      (dropWhile ((=) 0) (reflected_slp_untrimmed_digits 2 levels
         (reflected_slp_digit_inlet (rev seed))))) =
    ((\<lambda>x. 2 * decimal_reverse x) ^^ (2 * reflected_dyadic_spans levels + 2)) (decimal_lsd_value seed)"
proof -
  have digits: "reflected_decimal (rev seed)" by (rule reflected_slp_reverse_inlet_valid[OF seed(1)])
  show ?thesis
    by (rule reflected_slp_two_even_endpoint_value[OF reflected_slp_digit_inlet_valid[OF digits]
          seed reflected_slp_digit_inlet_exact[OF digits]])
qed

ML \<open>
  val checked = @{thms reflected_slp_stages_normalized reflected_slp_odd_endpoint_value
    reflected_slp_five_even_endpoint_value reflected_slp_two_even_endpoint_value
    reflected_slp_odd_from_seed reflected_slp_five_even_from_seed reflected_slp_two_even_from_seed};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Reflected SLP endpoint depends on an oracle";
  val _ = if Thm_Deps.has_skip_proof checked
    then error "Skipped reflected SLP endpoint proof" else ();
\<close>

end
