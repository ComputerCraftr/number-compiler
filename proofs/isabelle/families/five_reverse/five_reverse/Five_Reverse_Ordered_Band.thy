theory Five_Reverse_Ordered_Band
  imports Five_Reverse_Window_Consumer
    "Shared_Carry_Dynamics.Ordered_Matrix_Program_Algebra"
begin

text \<open>The physical source publishes low decimal digits in increasing
least-significant-first order. Its row action uses those digits in physical
order, followed by chronological multiplication of the row actions.\<close>

definition five_reverse_band_digits :: "nat \<Rightarrow> nat \<Rightarrow> nat list" where
  "five_reverse_band_digits value width =
    map (\<lambda>i. (value div 10^i) mod 10) [0..<width]"

definition five_reverse_band_letter :: "nat \<Rightarrow> nat ordered_matrix2" where
  "five_reverse_band_letter digit = Ordered_Matrix2 (Suc digit) 1 1 0"

definition five_reverse_band_rows ::
    "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat ordered_matrix2 list list" where
  "five_reverse_band_rows seed generation steps width =
    map (\<lambda>tick. map five_reverse_band_letter
      (five_reverse_band_digits (five_reverse_orbit (Suc (generation+tick)) seed) width))
      [0..<steps]"

definition five_reverse_compiled_band ::
    "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat ordered_matrix2" where
  "five_reverse_compiled_band seed generation steps width =
    foldl (\<lambda>action row. ordered_matrix2_multiply (ordered_matrix2_word row) action)
      ordered_matrix2_identity (five_reverse_band_rows seed generation steps width)"

lemma five_reverse_ordered_rows_fold:
  "foldl (\<lambda>action row. ordered_matrix2_multiply (ordered_matrix2_word row) action)
      ordered_matrix2_identity rows = ordered_matrix2_word (concat rows)"
proof (induction rows rule: rev_induct)
  case Nil
  then show ?case by simp
next
  case (snoc row rows)
  then show ?case by (simp add: ordered_matrix2_word_append)
qed

theorem five_reverse_band_physical_order:
  "five_reverse_compiled_band seed generation steps width =
    ordered_matrix2_word
      (concat (map (\<lambda>tick. map five_reverse_band_letter
        (five_reverse_band_digits (five_reverse_orbit (Suc (generation+tick)) seed) width))
          [0..<steps]))"
  by (simp only: five_reverse_compiled_band_def five_reverse_band_rows_def
      five_reverse_ordered_rows_fold)

lemma five_reverse_right_product_reverse:
  "ordered_matrix2_word word =
    foldl ordered_matrix2_multiply ordered_matrix2_identity (rev word)"
proof (induction word)
  case Nil
  then show ?case by simp
next
  case (Cons a word)
  then show ?case by (simp add: ordered_matrix2_multiply_associative)
qed

theorem five_reverse_shared_continuant_rows:
  "five_reverse_compiled_band seed generation steps width =
    foldl (\<lambda>action row. ordered_matrix2_multiply
        (foldl ordered_matrix2_multiply ordered_matrix2_identity (rev row)) action)
      ordered_matrix2_identity (five_reverse_band_rows seed generation steps width)"
  by (simp only: five_reverse_compiled_band_def five_reverse_right_product_reverse)


theorem five_reverse_shared_modular_band:
  "ordered_matrix2_mod m (five_reverse_compiled_band seed generation steps width) =
    ordered_matrix2_word_mod m
      (concat (map (\<lambda>tick. map five_reverse_band_letter
        (five_reverse_band_digits (five_reverse_orbit (Suc (generation+tick)) seed) width))
          [0..<steps]))"
  by (simp only: five_reverse_band_physical_order ordered_matrix2_word_mod_exact)

ML \<open>
  val checked = @{thms five_reverse_band_physical_order
    five_reverse_shared_continuant_rows five_reverse_shared_modular_band};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Five-reverse ordered band depends on an oracle";
  val _ = if Thm_Deps.has_skip_proof checked then
    error "Five-reverse ordered band has a skipped proof" else ();
\<close>

end
