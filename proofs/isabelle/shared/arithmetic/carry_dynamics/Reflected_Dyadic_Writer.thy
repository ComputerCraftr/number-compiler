theory Reflected_Dyadic_Writer
  imports Reflected_Padded_Halo Reflected_Physical_Parity
begin

text \<open>Each exponent denotes an actual adjacent H span. The list is
chronological and may include repeated levels; no future period is assumed.\<close>

lemma reflected_H_iter_add:
  "reflected_padded_H_iter multiplier (a + b) source =
    reflected_padded_H_iter multiplier b (reflected_padded_H_iter multiplier a source)"
  by (induction b) simp_all

fun reflected_dyadic_spans :: "nat list \<Rightarrow> nat" where
  "reflected_dyadic_spans [] = 0"
| "reflected_dyadic_spans (level # rest) = 2 ^ level + reflected_dyadic_spans rest"

fun reflected_dyadic_H :: "nat \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list" where
  "reflected_dyadic_H multiplier [] source = source"
| "reflected_dyadic_H multiplier (level # rest) source =
    reflected_dyadic_H multiplier rest
      (reflected_padded_H_iter multiplier (2 ^ level) source)"

theorem reflected_dyadic_H_exact:
  "reflected_dyadic_H multiplier levels source =
    reflected_padded_H_iter multiplier (reflected_dyadic_spans levels) source"
  by (induction levels arbitrary: source)
     (simp_all add: reflected_H_iter_add)

theorem reflected_dyadic_odd_source:
  assumes multiplier: "multiplier = 2 \<or> multiplier = 5"
    and digits: "reflected_decimal seed"
    and canonical: "reflected_trim_high seed = seed"
  shows "(reflected_physical_word multiplier ^^
      (2 * reflected_dyadic_spans levels + 1)) seed =
    reflected_emit multiplier (reflected_dyadic_H multiplier levels (rev seed))"
  using reflected_odd_endpoint[OF multiplier digits canonical,
      of "reflected_dyadic_spans levels"]
  by (simp only: reflected_dyadic_H_exact)

theorem reflected_dyadic_even_source:
  assumes multiplier: "multiplier = 2 \<or> multiplier = 5"
    and digits: "reflected_decimal seed"
  shows "(reflected_physical_word multiplier ^^
      (2 * reflected_dyadic_spans levels + 2)) seed =
    reflected_emit multiplier
      (reflected_dyadic_H multiplier levels (reflected_padded_E multiplier seed))"
  using reflected_even_endpoint[OF multiplier digits, of "reflected_dyadic_spans levels"]
  by (simp only: reflected_dyadic_H_exact)

theorem reflected_dyadic_odd_value:
  assumes multiplier: "multiplier = 2 \<or> multiplier = 5"
    and digits: "reflected_decimal seed"
    and canonical: "reflected_trim_high seed = seed"
  shows "decimal_lsd_value
      (reflected_emit multiplier (reflected_dyadic_H multiplier levels (rev seed))) =
    ((\<lambda>x. multiplier * decimal_reverse x) ^^
      (2 * reflected_dyadic_spans levels + 1)) (decimal_lsd_value seed)"
  using reflected_physical_clock_value[OF multiplier digits canonical,
      of "2 * reflected_dyadic_spans levels + 1"]
    reflected_dyadic_odd_source[OF multiplier digits canonical, of levels]
  by simp

theorem reflected_dyadic_even_value:
  assumes multiplier: "multiplier = 2 \<or> multiplier = 5"
    and digits: "reflected_decimal seed"
    and canonical: "reflected_trim_high seed = seed"
  shows "decimal_lsd_value
      (reflected_emit multiplier
        (reflected_dyadic_H multiplier levels (reflected_padded_E multiplier seed))) =
    ((\<lambda>x. multiplier * decimal_reverse x) ^^
      (2 * reflected_dyadic_spans levels + 2)) (decimal_lsd_value seed)"
  using reflected_physical_clock_value[OF multiplier digits canonical,
      of "2 * reflected_dyadic_spans levels + 2"]
    reflected_dyadic_even_source[OF multiplier digits, of levels]
  by simp

lemma reflected_padded_H_length:
  "length (reflected_padded_H multiplier source) = length source + 2"
  by (simp add: reflected_padded_H_def reflected_padded_E_def
      reflected_padded_multiply_length)

lemma reflected_padded_H_iter_length:
  "length (reflected_padded_H_iter multiplier steps source) = length source + 2 * steps"
  by (induction steps) (simp_all add: reflected_padded_H_length algebra_simps)

theorem reflected_dyadic_H_extent:
  "length (reflected_dyadic_H multiplier levels source) =
    length source + 2 * reflected_dyadic_spans levels"
  by (simp only: reflected_dyadic_H_exact reflected_padded_H_iter_length)

ML \<open>
  val checked = @{thms reflected_H_iter_add reflected_dyadic_H_exact
    reflected_dyadic_odd_source reflected_dyadic_even_source
    reflected_dyadic_H_extent reflected_dyadic_odd_value reflected_dyadic_even_value};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Reflected dyadic writer proof depends on an oracle";
  val _ = if Thm_Deps.has_skip_proof checked
    then error "Skipped reflected dyadic writer proof" else ();
\<close>

end
