theory Double_Reverse_Reflected_SLP_Seams
  imports Double_Reverse_Source_Slice_Refinement
    Shared_Carry_Dynamics.Reflected_Compiled_Word
begin

fun reflected_lsd_cell_value :: "nat list \<Rightarrow> nat" where
  "reflected_lsd_cell_value [] = 0"
| "reflected_lsd_cell_value (cell # rest) =
    cell + 100 * reflected_lsd_cell_value rest"

fun reflected_lsd_digits_of_cells :: "nat list \<Rightarrow> nat list" where
  "reflected_lsd_digits_of_cells [] = []"
| "reflected_lsd_digits_of_cells (cell # rest) =
    (cell mod 10) # (cell div 10) # reflected_lsd_digits_of_cells rest"

lemma reflected_lsd_digits_of_cells_append:
  "reflected_lsd_digits_of_cells (xs @ ys) =
    reflected_lsd_digits_of_cells xs @ reflected_lsd_digits_of_cells ys"
  by (induction xs) simp_all

lemma reflected_lsd_digits_of_cells_valid:
  assumes "list_all (\<lambda>cell. cell < 100) xs"
  shows "reflected_decimal (reflected_lsd_digits_of_cells xs)"
  using assms by (induction xs) auto

text \<open>These equations give the exact list semantics of the one-sided
adjacent-cell transducer at concatenation and repetition seams. The source
SLP stays a compressed syntax tree. These laws concern a finite source word
and do not supply physical source admission.\<close>

fun double_reverse_adjacent :: "(nat \<Rightarrow> nat \<Rightarrow> nat) \<Rightarrow> nat list \<Rightarrow> nat list" where
  "double_reverse_adjacent f [] = []"
| "double_reverse_adjacent f [a] = []"
| "double_reverse_adjacent f (a # b # rest) = f a b # double_reverse_adjacent f (b # rest)"

lemma double_reverse_adjacent_append:
  assumes "xs \<noteq> []" "ys \<noteq> []"
  shows "double_reverse_adjacent f (xs @ ys) =
    double_reverse_adjacent f xs @ [f (last xs) (hd ys)] @ double_reverse_adjacent f ys"
  using assms
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  show ?case
  proof (cases xs)
    case Nil
    then show ?thesis using Cons.prems by (cases ys) auto
  next
    case (Cons b rest)
    then show ?thesis using Cons.IH Cons.prems by simp
  qed
qed

lemma double_reverse_source_repeat_empty[simp]:
  "double_reverse_source_repeat_word [] count = []"
  by (induction count) simp_all

lemma double_reverse_adjacent_repeat:
  assumes nonempty: "word \<noteq> []"
  shows "double_reverse_adjacent f (double_reverse_source_repeat_word word (Suc count)) =
    double_reverse_adjacent f word @
      double_reverse_source_repeat_word
        ([f (last word) (hd word)] @ double_reverse_adjacent f word) count"
proof (induction count)
  case 0
  then show ?case by simp
next
  case (Suc count)
  have tail: "double_reverse_source_repeat_word word (Suc count) \<noteq> []"
    using nonempty by simp
  have head: "hd (double_reverse_source_repeat_word word (Suc count)) = hd word"
    using nonempty by (cases word) auto
  show ?case
    using double_reverse_adjacent_append[OF nonempty tail, of f] Suc.IH head
    by (simp add: append.assoc)
qed

fun double_reverse_adjacent_slp ::
  "(nat \<Rightarrow> nat \<Rightarrow> nat) \<Rightarrow> double_reverse_source_slp \<Rightarrow> double_reverse_source_slp" where
  "double_reverse_adjacent_slp f Double_Reverse_Source_Empty = Double_Reverse_Source_Empty"
| "double_reverse_adjacent_slp f (Double_Reverse_Source_Term d) = Double_Reverse_Source_Empty"
| "double_reverse_adjacent_slp f (Double_Reverse_Source_Concat left right) =
    (if double_reverse_source_slp_word left = [] then double_reverse_adjacent_slp f right
     else if double_reverse_source_slp_word right = [] then double_reverse_adjacent_slp f left
     else Double_Reverse_Source_Concat (double_reverse_adjacent_slp f left)
       (Double_Reverse_Source_Concat
         (Double_Reverse_Source_Term (f (last (double_reverse_source_slp_word left))
           (hd (double_reverse_source_slp_word right)))) (double_reverse_adjacent_slp f right)))"
| "double_reverse_adjacent_slp f (Double_Reverse_Source_Repeat child count) =
    (if count = 0 \<or> double_reverse_source_slp_word child = [] then Double_Reverse_Source_Empty
     else Double_Reverse_Source_Concat (double_reverse_adjacent_slp f child)
       (Double_Reverse_Source_Repeat
         (Double_Reverse_Source_Concat
           (Double_Reverse_Source_Term (f (last (double_reverse_source_slp_word child))
             (hd (double_reverse_source_slp_word child)))) (double_reverse_adjacent_slp f child))
         (count - 1)))"

theorem double_reverse_adjacent_slp_exact:
  "double_reverse_source_slp_word (double_reverse_adjacent_slp f source) =
    double_reverse_adjacent f (double_reverse_source_slp_word source)"
proof (induction source)
  case Double_Reverse_Source_Empty
  then show ?case by simp
next
  case (Double_Reverse_Source_Term x)
  then show ?case by simp
next
  case (Double_Reverse_Source_Concat left right)
  then show ?case
    using double_reverse_adjacent_append[of "double_reverse_source_slp_word left"
      "double_reverse_source_slp_word right" f]
    by (cases "double_reverse_source_slp_word left = []";
        cases "double_reverse_source_slp_word right = []") auto
next
  case (Double_Reverse_Source_Repeat child count)
  then show ?case
  proof (cases count)
    case 0
    then show ?thesis by simp
  next
    case (Suc n)
    show ?thesis
    proof (cases "double_reverse_source_slp_word child = []")
      case True
      then show ?thesis using Suc by simp
    next
      case False
      then show ?thesis using Suc Double_Reverse_Source_Repeat.IH
        double_reverse_adjacent_repeat[OF False, of f n] by simp
    qed
  qed
qed

corollary double_reverse_slp_shift_cells_exact:
  "double_reverse_source_slp_word
      (double_reverse_adjacent_slp (\<lambda>a b. a div 10 + 10 * (b mod 10)) source) =
    double_reverse_adjacent (\<lambda>a b. a div 10 + 10 * (b mod 10))
      (double_reverse_source_slp_word source)"
  by (rule double_reverse_adjacent_slp_exact)


theorem reflected_compiled_slp_interval_exact:
  assumes multiplier: "m = 2 \<or> m = 5"
    and interval: "start_index \<le> end_index"
    and bound: "end_index \<le> double_reverse_source_slp_length source"
    and digits: "reflected_decimal (double_reverse_source_slp_word source)"
  defines "slice \<equiv> take (end_index - start_index)
    (drop start_index (double_reverse_source_slp_word source))"
  shows "reflected_compiled_word m order
      (double_reverse_source_slp_word
        (double_reverse_source_slp_part source start_index end_index)) =
    reflected_padded_H_iter m (2 ^ order) slice @
      replicate (2 * ((length slice + 1) div 2) - length slice) 0"
proof -
  have exact: "double_reverse_source_slp_word
    (double_reverse_source_slp_part source start_index end_index) = slice"
    using double_reverse_source_slp_part_exact[OF interval bound]
    by (simp only: slice_def)
  have subset: "set slice \<subseteq> set (double_reverse_source_slp_word source)"
    unfolding slice_def by (rule subset_trans[OF set_take_subset set_drop_subset])
  have slice_digits: "reflected_decimal slice"
    using digits subset by (auto simp only: list_all_iff dest: subsetD)
  show ?thesis using reflected_compiled_word_exact[OF multiplier slice_digits, of order]
    by (simp only: exact)
qed

lemma reflected_repeat_snoc:
  "double_reverse_source_repeat_word word count @ word =
    word @ double_reverse_source_repeat_word word count"
  by (induction count) (simp_all add: append.assoc)

lemma reflected_reverse_repeat:
  "rev (double_reverse_source_repeat_word word count) =
    double_reverse_source_repeat_word (rev word) count"
  by (induction count) (simp_all add: reflected_repeat_snoc)

lemma reflected_map_repeat:
  "concat (map f (double_reverse_source_repeat_word word count)) =
    double_reverse_source_repeat_word (concat (map f word)) count"
  by (induction count) simp_all

fun reflected_slp_cell_digits :: "double_reverse_source_slp \<Rightarrow> double_reverse_source_slp" where
  "reflected_slp_cell_digits Double_Reverse_Source_Empty = Double_Reverse_Source_Empty"
| "reflected_slp_cell_digits (Double_Reverse_Source_Term cell) =
    Double_Reverse_Source_Concat (Double_Reverse_Source_Term (cell div 10))
      (Double_Reverse_Source_Term (cell mod 10))"
| "reflected_slp_cell_digits (Double_Reverse_Source_Concat left right) =
    Double_Reverse_Source_Concat (reflected_slp_cell_digits right) (reflected_slp_cell_digits left)"
| "reflected_slp_cell_digits (Double_Reverse_Source_Repeat child count) =
    Double_Reverse_Source_Repeat (reflected_slp_cell_digits child) count"

theorem reflected_slp_cell_digits_exact:
  "double_reverse_source_slp_word (reflected_slp_cell_digits source) =
    concat (map (\<lambda>cell. [cell div 10, cell mod 10])
      (rev (double_reverse_source_slp_word source)))"
  by (induction source)
    (simp_all add: map_append concat_append reflected_reverse_repeat reflected_map_repeat)

lemma reflected_decimal_cell_carry:
  fixes cell multiplier :: nat
  assumes "multiplier = 2 \<or> multiplier = 5"
  shows "(multiplier * cell) div 100 = cell div (100 div multiplier)"
proof -
  have two: "(2 * cell) div 100 = cell div 50"
    using div_mult_mult1[of "2::nat" cell 50] by simp
  have five: "(5 * cell) div 100 = cell div 20"
    using div_mult_mult1[of "5::nat" cell 20] by simp
  show ?thesis using assms two five by auto
qed

lemma reflected_decimal_cell_emission:
  fixes cell carry multiplier :: nat
  assumes m: "multiplier = 2 \<or> multiplier = 5" and carry: "carry < multiplier"
  shows "(multiplier * cell + carry) mod 100 = (multiplier * cell) mod 100 + carry"
proof -
  have two: "(2 * cell) mod 100 = 2 * (cell mod 50)"
    using mod_mult_mult1[of "2::nat" cell 50] by simp
  have five: "(5 * cell) mod 100 = 5 * (cell mod 20)"
    using mod_mult_mult1[of "5::nat" cell 20] by simp
  have bounds: "cell mod 50 < 50" "cell mod 20 < 20" by simp_all
  have width: "(multiplier * cell) mod 100 + carry < 100"
    using m carry two five bounds by (elim disjE; simp_all; arith)
  have reduced: "((multiplier * cell) mod 100 + carry) mod 100 =
      (multiplier * cell + carry) mod 100"
    by (rule mod_add_left_eq)
  have unwrapped: "((multiplier * cell) mod 100 + carry) mod 100 =
      (multiplier * cell) mod 100 + carry"
    by (rule mod_less[OF width])
  show ?thesis using reduced unwrapped by simp
qed

lemma reflected_decimal_cell_carry_independent:
  fixes cell carry multiplier :: nat
  assumes m: "multiplier = 2 \<or> multiplier = 5" and carry: "carry < multiplier"
  shows "(multiplier * cell + carry) div 100 = cell div (100 div multiplier)"
proof -
  have carry100: "carry < 100" using m carry by auto
  have rem: "(multiplier * cell + carry) mod 100 < 100" by simp
  have width: "(multiplier * cell) mod 100 + carry < 100"
    using reflected_decimal_cell_emission[OF m carry, of cell] rem by simp
  have "(multiplier * cell + carry) div 100 = (multiplier * cell) div 100"
    using div_add1_eq[of "multiplier * cell" carry "100::nat"] width carry100
    by simp
  also have "\<dots> = cell div (100 div multiplier)"
    by (rule reflected_decimal_cell_carry[OF m])
  finally show ?thesis .
qed

fun reflected_decimal_cells_run :: "nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat list" where
  "reflected_decimal_cells_run m carry [] = (if carry = 0 then [] else [carry])"
| "reflected_decimal_cells_run m carry (cell # rest) =
    ((m * cell + carry) mod 100) #
      reflected_decimal_cells_run m ((m * cell + carry) div 100) rest"

lemma reflected_decimal_cells_run_adjacent:
  assumes m: "multiplier = 2 \<or> multiplier = 5"
    and valid: "list_all (\<lambda>cell. cell < 100) (cell # rest)"
    and inlet: "inlet < multiplier"
  defines "next \<equiv> \<lambda>previous current.
    multiplier * current mod 100 + previous div (100 div multiplier)"
  shows "reflected_decimal_cells_run multiplier inlet (cell # rest) =
    (multiplier * cell mod 100 + inlet) #
      (double_reverse_adjacent next (cell # rest) @
       (if last (cell # rest) div (100 div multiplier) = 0 then []
        else [last (cell # rest) div (100 div multiplier)]))"
  using valid inlet
proof (induction rest arbitrary: cell inlet)
  case Nil
  then show ?case using reflected_decimal_cell_emission[OF m, of inlet cell]
      reflected_decimal_cell_carry_independent[OF m, of inlet cell]
    by simp
next
  case (Cons current tail)
  have cell: "cell < 100" and tail: "list_all (\<lambda>cell. cell < 100) (current # tail)"
    using Cons.prems by simp_all
  have bound: "cell div (100 div multiplier) < multiplier"
    using m cell by (elim disjE; simp_all add: div_less_iff_less_mult)
  have emission: "(multiplier * cell + inlet) mod 100 = multiplier * cell mod 100 + inlet"
    by (rule reflected_decimal_cell_emission[OF m Cons.prems(2)])
  have carry: "(multiplier * cell + inlet) div 100 = cell div (100 div multiplier)"
    by (rule reflected_decimal_cell_carry_independent[OF m Cons.prems(2)])
  show ?case using Cons.IH[OF tail bound] emission carry
    by (simp add: next_def)
qed

ML \<open>
  val checked = @{thms reflected_compiled_slp_interval_exact reflected_slp_cell_digits_exact};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Reflected SLP seam depends on an oracle";
  val _ = if Thm_Deps.has_skip_proof checked then error "Skipped reflected SLP seam" else ();
\<close>

end
