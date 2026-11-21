theory Reflected_Padded_Halo
  imports Reflected_E_Word
begin

text \<open>Low padding translates the coordinate origin without changing
the finite causal rule. The extra cells supply the complete lower halo even
for the physical output cell at index zero.\<close>

definition reflected_shift :: "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat" where
  "reflected_shift offset source i = (if i < offset then 0 else source (i - offset))"

lemma reflected_previous_shift:
  "reflected_previous (reflected_shift offset source) i =
    reflected_shift offset (reflected_previous source) i"
proof (cases "i = 0")
  case True
  then show ?thesis by (simp add: reflected_previous_def reflected_shift_def)
next
  case False
  note nonzero = False
  show ?thesis
  proof (cases "i < offset")
    case True
    have "i - 1 < offset" using True by arith
    with True False show ?thesis
      by (simp add: reflected_previous_def reflected_shift_def)
  next
    case False
    note not_below = False
    show ?thesis
    proof (cases "i = offset")
      case True
      with nonzero not_below show ?thesis
        by (simp add: reflected_previous_def reflected_shift_def)
    next
      case False
      have previous: "offset \<le> i - 1" using not_below False by arith
      have positive: "i \<noteq> 0" using not_below False by arith
      have difference: "i - 1 - offset = i - offset - 1" by arith
      show ?thesis using not_below False positive previous difference
        by (simp add: reflected_previous_def reflected_shift_def)
    qed
  qed
qed

lemma reflected_M_shift:
  "reflected_M_digit multiplier (reflected_shift offset source) =
    reflected_shift offset (reflected_M_digit multiplier source)"
  by (rule ext)
     (simp add: reflected_M_digit_def reflected_previous_shift reflected_shift_def
        split: if_splits)

lemma reflected_E_shift:
  "reflected_E_digit multiplier (reflected_shift offset source) =
    reflected_shift offset (reflected_E_digit multiplier source)"
  by (rule ext)
     (simp add: reflected_E_digit_def reflected_previous_shift reflected_shift_def
        split: if_splits)

lemma reflected_H_shift:
  "reflected_H_digit multiplier (reflected_shift offset source) =
    reflected_shift offset (reflected_H_digit multiplier source)"
  by (simp only: reflected_H_digit_def reflected_M_shift reflected_E_shift)

lemma reflected_H_iter_shift:
  "reflected_H_digit_iter multiplier steps (reflected_shift offset source) =
    reflected_shift offset (reflected_H_digit_iter multiplier steps source)"
  by (induction steps) (simp_all only: reflected_H_digit_iter.simps reflected_H_shift)

theorem reflected_padded_dyadic_all_cells:
  fixes order :: nat
  assumes multiplier: "multiplier = 2 \<or> multiplier = 5"
    and digits: "list_all (\<lambda>digit. digit < 10) source"
  defines "padding \<equiv> 2 ^ order + 1"
  shows "overlap_recursive order (reflected_pair_action multiplier)
      (\<lambda>j. reflected_pair_at
        (reflected_shift (2 * padding) (reflected_padded_source source))
        (cell + padding - j)) 0 =
    (reflected_padded_source (reflected_padded_H_iter multiplier (2 ^ order) source)
       (2 * cell),
     reflected_padded_source (reflected_padded_H_iter multiplier (2 ^ order) source)
       (2 * cell + 1))"
proof -
  have halo: "0 + 2 ^ order < cell + padding"
    unfolding padding_def by arith
  have window:
    "overlap_recursive order (reflected_pair_action multiplier)
        (\<lambda>j. reflected_pair_at
          (reflected_shift (2 * padding) (reflected_padded_source source))
          (cell + padding - j)) 0 =
      (reflected_H_digit_iter multiplier (2 ^ order)
          (reflected_shift (2 * padding) (reflected_padded_source source))
          (2 * (cell + padding)),
       reflected_H_digit_iter multiplier (2 ^ order)
          (reflected_shift (2 * padding) (reflected_padded_source source))
          (2 * (cell + padding) + 1))"
    using reflected_H_dyadic_physical_window[OF halo] by simp
  show ?thesis using window reflected_padded_H_iter_source_digit[OF multiplier digits]
    by (simp add: reflected_H_iter_shift reflected_shift_def algebra_simps)
qed

end
