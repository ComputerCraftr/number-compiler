theory Reflected_Padded_Physical_Trim
  imports Reflected_Padded_Digit_Word
begin

text \<open>Words are least-significant digit first. Removing high zeroes
preserves the represented value and produces the physical word after a
single reversed multiplication.\<close>

definition reflected_trim_high :: "nat list \<Rightarrow> nat list" where
  "reflected_trim_high word = rev (dropWhile ((=) 0) (rev word))"

lemma reflected_trim_high_value:
  "decimal_lsd_value (reflected_trim_high word) =
    decimal_lsd_value word"
proof (induction word rule: rev_induct)
  case Nil
  then show ?case by (simp add: reflected_trim_high_def)
next
  case (snoc digit rest)
  show ?case
  proof (cases "digit = 0")
    case True
    then show ?thesis using snoc.IH
      by (simp add: reflected_trim_high_def decimal_lsd_value_append)
  next
    case False
    then show ?thesis by (simp add: reflected_trim_high_def)
  qed
qed

definition reflected_physical_word :: "nat \<Rightarrow> nat list \<Rightarrow> nat list" where
  "reflected_physical_word multiplier source =
    reflected_trim_high (reflected_padded_multiply multiplier (rev source))"

lemma reflected_physical_word_zero:
  "reflected_physical_word multiplier [] = []"
  by (simp add: reflected_physical_word_def reflected_trim_high_def
      reflected_padded_multiply_def Let_def)

lemma reflected_reverse_trim_high:
  "rev (reflected_trim_high source) = dropWhile ((=) 0) (rev source)"
  by (simp add: reflected_trim_high_def)

theorem reflected_physical_two_step_padded:
  "reflected_physical_word multiplier
      (reflected_physical_word multiplier source) =
    reflected_trim_high
      (reflected_padded_multiply multiplier
        (dropWhile ((=) 0) (reflected_padded_E multiplier source)))"
  by (simp only: reflected_physical_word_def reflected_padded_E_def
      reflected_reverse_trim_high)

theorem reflected_physical_word_value:
  "decimal_lsd_value (reflected_physical_word multiplier source) =
    multiplier * reflected_msf_value source"
  by (simp only: reflected_physical_word_def reflected_trim_high_value
      reflected_padded_multiply_value reflected_msf_value_def)

ML \<open>
  val checked = @{thms reflected_trim_high_value reflected_physical_word_zero
    reflected_reverse_trim_high
    reflected_physical_two_step_padded reflected_physical_word_value};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Reflected physical word proof depends on an oracle";
  val _ = if Thm_Deps.has_skip_proof checked
    then error "Skipped reflected physical word proof" else ();
\<close>

end
