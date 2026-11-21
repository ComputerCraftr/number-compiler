theory Double_Reverse_Reflected_Writer
  imports Double_Reverse_Source_Window_Refinement Double_Reverse_Reflected_Physical
    Shared_Carry_Dynamics.Reflected_Compiled_Word
begin

text \<open>The published grammar is MSD-first. The doubled even endpoint
reads the odd word from its other end before applying the one-step pass.\<close>

fun reflected_writer_word :: "nat list \<Rightarrow> double_reverse_source_slp" where
  "reflected_writer_word [] = Double_Reverse_Source_Empty"
| "reflected_writer_word (digit # rest) =
    Double_Reverse_Source_Concat (Double_Reverse_Source_Term digit)
      (reflected_writer_word rest)"

lemma reflected_writer_word_exact:
  "double_reverse_source_slp_word (reflected_writer_word word) = word"
  by (induction word) simp_all

definition reflected_odd_writer :: "nat list \<Rightarrow> double_reverse_source_slp" where
  "reflected_odd_writer lsd_digits = reflected_writer_word (rev lsd_digits)"

lemma reflected_odd_writer_exact:
  "double_reverse_source_slp_word (reflected_odd_writer lsd_digits) = rev lsd_digits"
  by (simp add: reflected_odd_writer_def reflected_writer_word_exact)

definition reflected_dyadic_odd_writer ::
    "nat \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> double_reverse_source_slp" where
  "reflected_dyadic_odd_writer multiplier levels seed =
    reflected_odd_writer (reflected_emit multiplier
      (reflected_compiled_levels multiplier levels (rev seed)))"

theorem double_reverse_dyadic_writer_value:
  assumes "reflected_decimal seed" "reflected_trim_high seed = seed"
  shows "double_reverse_msf_value
      (double_reverse_source_slp_word (reflected_dyadic_odd_writer 2 levels seed)) =
    ((\<lambda>x. 2 * decimal_reverse x) ^^ (2 * reflected_dyadic_spans levels + 1))
      (decimal_lsd_value seed)"
  using reflected_compiled_odd_value[of 2 seed levels] assms
  by (simp add: reflected_dyadic_odd_writer_def reflected_odd_writer_exact
      double_reverse_msf_value_def double_reverse_lsf_value_shared)

definition double_reverse_even_writer :: "nat list \<Rightarrow> double_reverse_source_slp" where
  "double_reverse_even_writer msd_source =
    reflected_writer_word (rev (reflected_physical_word 2 (rev msd_source)))"

lemma double_reverse_even_writer_exact:
  "double_reverse_source_slp_word (double_reverse_even_writer msd_source) =
    rev (reflected_physical_word 2 (rev msd_source))"
  by (simp add: double_reverse_even_writer_def reflected_writer_word_exact)

theorem double_reverse_even_writer_physical_value:
  assumes "list_all (\<lambda>digit. digit < 10) msd_source"
    "msd_source \<noteq> []" "hd msd_source > 0"
  shows "double_reverse_msf_value
      (double_reverse_source_slp_word (double_reverse_even_writer msd_source)) =
    double_reverse_T (double_reverse_msf_value msd_source)"
proof -
  have decimal: "list_all (\<lambda>digit. digit < 10) (rev msd_source)"
    using assms by simp
  have nonempty: "rev msd_source \<noteq> []" using assms by simp
  have high: "last (rev msd_source) > 0" using assms by (simp add: last_rev)
  show ?thesis
    using double_reverse_physical_word_one_step[OF decimal nonempty high]
    by (simp add: double_reverse_even_writer_exact double_reverse_msf_value_def
        double_reverse_lsf_value_shared)
qed

definition double_reverse_dyadic_even_writer ::
    "nat list \<Rightarrow> nat list \<Rightarrow> double_reverse_source_slp" where
  "double_reverse_dyadic_even_writer levels seed =
    double_reverse_even_writer
      (double_reverse_source_slp_word (reflected_dyadic_odd_writer 2 levels seed))"

theorem double_reverse_dyadic_even_writer_value:
  assumes digits: "reflected_decimal seed" and canonical: "reflected_trim_high seed = seed"
  shows "double_reverse_msf_value
      (double_reverse_source_slp_word (double_reverse_dyadic_even_writer levels seed)) =
    ((\<lambda>x. 2 * decimal_reverse x) ^^ (2 * reflected_dyadic_spans levels + 2))
      (decimal_lsd_value seed)"
proof -
  have valid: "reflected_decimal (rev seed)" using digits by (simp add: list_all_iff)
  have odd:
    "rev (double_reverse_source_slp_word (reflected_dyadic_odd_writer 2 levels seed)) =
      (reflected_physical_word 2 ^^ (2 * reflected_dyadic_spans levels + 1)) seed"
    using reflected_compiled_levels_emit[of 2 "rev seed" levels]
      reflected_dyadic_odd_source[of 2 seed levels] digits canonical valid
    by (simp add: reflected_dyadic_odd_writer_def reflected_odd_writer_exact)
  have step:
    "reflected_physical_word 2
      ((reflected_physical_word 2 ^^ (2 * reflected_dyadic_spans levels + 1)) seed) =
      (reflected_physical_word 2 ^^ (2 * reflected_dyadic_spans levels + 2)) seed"
    by (simp add: funpow_Suc_right)
  show ?thesis
    using reflected_physical_clock_value[of 2 seed "2 * reflected_dyadic_spans levels + 2"]
      digits canonical
    by (simp add: double_reverse_dyadic_even_writer_def double_reverse_even_writer_exact
        double_reverse_msf_value_def double_reverse_lsf_value_shared odd step)
qed

definition reflected_cone_pairs ::
    "nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) list" where
  "reflected_cone_pairs multiplier order source count =
    (let padding = 2 ^ order + 1 in
      map (\<lambda>cell. overlap_recursive order (reflected_pair_action multiplier)
        (\<lambda>j. reflected_pair_at
          (reflected_shift (2 * padding) (reflected_padded_source source))
          (cell + padding - j)) 0) [0..<count])"

theorem reflected_cone_pairs_source_exact:
  assumes "multiplier = 2 \<or> multiplier = 5"
    "list_all (\<lambda>digit. digit < 10) source"
  shows "reflected_cone_pairs multiplier order source count =
    map (\<lambda>cell.
      (reflected_padded_source (reflected_padded_H_iter multiplier (2 ^ order) source)
         (2 * cell),
       reflected_padded_source (reflected_padded_H_iter multiplier (2 ^ order) source)
         (2 * cell + 1))) [0..<count]"
  unfolding reflected_cone_pairs_def Let_def
proof (rule map_cong[OF refl])
  fix cell
  assume "cell \<in> set [0..<count]"
  show "overlap_recursive order (reflected_pair_action multiplier)
      (\<lambda>j. reflected_pair_at
        (reflected_shift (2 * (2 ^ order + 1)) (reflected_padded_source source))
        (cell + (2 ^ order + 1) - j)) 0 =
    (reflected_padded_source (reflected_padded_H_iter multiplier (2 ^ order) source)
       (2 * cell),
     reflected_padded_source (reflected_padded_H_iter multiplier (2 ^ order) source)
       (2 * cell + 1))"
    by (rule reflected_padded_dyadic_all_cells[OF assms])
qed

definition reflected_cone_writer ::
    "nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> double_reverse_source_slp" where
  "reflected_cone_writer multiplier order source count =
    reflected_odd_writer
      (concat (map (\<lambda>pair. [fst pair, snd pair])
        (reflected_cone_pairs multiplier order source count)))"

theorem reflected_cone_writer_source_word:
  assumes "multiplier = 2 \<or> multiplier = 5"
    "list_all (\<lambda>digit. digit < 10) source"
  shows "double_reverse_source_slp_word (reflected_cone_writer multiplier order source count) =
    rev (concat (map (\<lambda>cell.
      [reflected_padded_source (reflected_padded_H_iter multiplier (2 ^ order) source)
         (2 * cell),
       reflected_padded_source (reflected_padded_H_iter multiplier (2 ^ order) source)
         (2 * cell + 1)]) [0..<count]))"
proof -
  have pairs: "reflected_cone_pairs multiplier order source count =
      map (\<lambda>cell.
        (reflected_padded_source (reflected_padded_H_iter multiplier (2 ^ order) source)
           (2 * cell),
         reflected_padded_source (reflected_padded_H_iter multiplier (2 ^ order) source)
           (2 * cell + 1))) [0..<count]"
    by (rule reflected_cone_pairs_source_exact[OF assms])
  show ?thesis using pairs
    by (simp add: reflected_cone_writer_def reflected_odd_writer_exact o_def)
qed

ML \<open>
  val checked = @{thms reflected_writer_word_exact reflected_odd_writer_exact
    double_reverse_even_writer_physical_value reflected_cone_pairs_source_exact
    reflected_cone_writer_source_word};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Reflected writer proof depends on an oracle";
  val _ = if Thm_Deps.has_skip_proof checked
    then error "Skipped reflected writer proof" else ();
\<close>

end
