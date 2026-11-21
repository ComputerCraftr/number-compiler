theory Double_Reverse_Reflected_SLP_Normalization
  imports Double_Reverse_Reflected_SLP_Seams Double_Reverse_Source_Slice_Refinement
begin

text \<open>Zero-edge accounting is a fold over the compressed source grammar;
the expanded word appears only in its specification. Cell order is least
significant first. The nonempty shift keeps the final nonzero high digit.\<close>

definition reflected_cell_zero_edges :: "nat list \<Rightarrow> nat \<times> nat \<times> nat" where
  "reflected_cell_zero_edges word =
    (length word, length (takeWhile ((=) 0) word),
      length (takeWhile ((=) 0) (rev word)))"

fun reflected_cell_zero_join :: "nat \<times> nat \<times> nat \<Rightarrow> nat \<times> nat \<times> nat \<Rightarrow> nat \<times> nat \<times> nat" where
  "reflected_cell_zero_join (l, lp, ls) (r, rp, rs) =
    (l + r, (if lp = l then lp + rp else lp),
      (if rs = r then r + ls else rs))"

fun reflected_cell_zero_repeat :: "nat \<times> nat \<times> nat \<Rightarrow> nat \<Rightarrow> nat \<times> nat \<times> nat" where
  "reflected_cell_zero_repeat (l, lp, ls) count =
    (if count = 0 then (0, 0, 0)
     else if lp = l then (count*l, count*l, count*l)
     else (count*l, lp, ls))"

lemma reflected_cell_takewhile_full:
  "(length (takeWhile P word) = length word) \<longleftrightarrow> (\<forall>x \<in> set word. P x)"
proof
  assume size: "length (takeWhile P word) = length word"
  have "takeWhile P word = word" using takeWhile_eq_take[of P word] size by simp
  then show "\<forall>x \<in> set word. P x" by simp
next
  assume "\<forall>x \<in> set word. P x"
  then show "length (takeWhile P word) = length word"
    by (induction word) auto
qed

lemma reflected_cell_zero_edges_append:
  "reflected_cell_zero_edges (xs @ ys) =
    reflected_cell_zero_join (reflected_cell_zero_edges xs) (reflected_cell_zero_edges ys)"
  unfolding reflected_cell_zero_edges_def
  by (simp only: rev_append length_append length_rev takeWhile_append
      reflected_cell_takewhile_full[symmetric] reflected_cell_zero_join.simps;
      split if_splits; simp_all)

lemma reflected_cell_zero_join_repeat:
  assumes lp: "lp \<le> l" and ls: "ls \<le> l" and all: "(lp = l) = (ls = l)"
  shows "reflected_cell_zero_join (l, lp, ls) (reflected_cell_zero_repeat (l, lp, ls) n) =
    reflected_cell_zero_repeat (l, lp, ls) (Suc n)"
  using assms by (cases n; cases "lp = l"; cases "ls = l")
    (auto simp: algebra_simps)

lemma reflected_cell_zero_edges_repeat:
  "reflected_cell_zero_edges (double_reverse_source_repeat_word word count) =
    reflected_cell_zero_repeat (reflected_cell_zero_edges word) count"
proof -
  obtain l lp ls where summary: "reflected_cell_zero_edges word = (l, lp, ls)"
    by (cases "reflected_cell_zero_edges word") auto
  have lp: "lp \<le> l" and ls: "ls \<le> l"
    using length_takeWhile_le[of "((=) 0)" word]
      length_takeWhile_le[of "((=) 0)" "rev word"] summary
    by (simp_all add: reflected_cell_zero_edges_def)
  have all: "(lp = l) = (ls = l)"
  proof -
    have "(length (takeWhile ((=) 0) word) = length word) =
        (length (takeWhile ((=) 0) (rev word)) = length (rev word))"
      using reflected_cell_takewhile_full[of "((=) 0)" word]
        reflected_cell_takewhile_full[of "((=) 0)" "rev word"] by simp
    then show ?thesis using summary by (simp add: reflected_cell_zero_edges_def)
  qed
  show ?thesis
  proof (induction count)
    case 0
    then show ?case by (simp add: reflected_cell_zero_edges_def)
  next
    case (Suc count)
    have "reflected_cell_zero_edges
        (double_reverse_source_repeat_word word (Suc count)) =
        reflected_cell_zero_join (reflected_cell_zero_edges word)
          (reflected_cell_zero_edges (double_reverse_source_repeat_word word count))"
      by (simp only: double_reverse_source_repeat_word.simps reflected_cell_zero_edges_append)
    also have "... = reflected_cell_zero_join (l, lp, ls)
        (reflected_cell_zero_repeat (l, lp, ls) count)"
      using Suc.IH summary by simp
    also have "... = reflected_cell_zero_repeat (l, lp, ls) (Suc count)"
      by (rule reflected_cell_zero_join_repeat[OF lp ls all])
    finally show ?case using summary by simp
  qed
qed

fun reflected_slp_zero_edges :: "double_reverse_source_slp \<Rightarrow> nat \<times> nat \<times> nat" where
  "reflected_slp_zero_edges Double_Reverse_Source_Empty = (0, 0, 0)"
| "reflected_slp_zero_edges (Double_Reverse_Source_Term cell) =
    (1, (if cell = 0 then 1 else 0), (if cell = 0 then 1 else 0))"
| "reflected_slp_zero_edges (Double_Reverse_Source_Concat left right) =
    reflected_cell_zero_join (reflected_slp_zero_edges left) (reflected_slp_zero_edges right)"
| "reflected_slp_zero_edges (Double_Reverse_Source_Repeat child count) =
    reflected_cell_zero_repeat (reflected_slp_zero_edges child) count"

theorem reflected_slp_zero_edges_exact:
  "reflected_slp_zero_edges source =
    reflected_cell_zero_edges (double_reverse_source_slp_word source)"
proof (induction source)
  case Double_Reverse_Source_Empty
  then show ?case by (simp add: reflected_cell_zero_edges_def)
next
  case (Double_Reverse_Source_Term cell)
  then show ?case by (simp add: reflected_cell_zero_edges_def)
next
  case (Double_Reverse_Source_Concat left right)
  then show ?case
    by (simp only: reflected_slp_zero_edges.simps double_reverse_source_slp_word.simps
        reflected_cell_zero_edges_append)
next
  case (Double_Reverse_Source_Repeat child count)
  then show ?case
    by (simp only: reflected_slp_zero_edges.simps double_reverse_source_slp_word.simps
        reflected_cell_zero_edges_repeat)
qed

lemma reflected_cell_nonzero_zero_edges_disjoint:
  assumes "length (takeWhile ((=) 0) word) < length word"
  shows "length (takeWhile ((=) 0) word) +
    length (takeWhile ((=) 0) (rev word)) \<le> length word"
  using assms
proof (induction word)
  case Nil
  then show ?case by simp
next
  case (Cons a word)
  show ?case
  proof (cases "a = 0")
    case True
    have zero_prefix: "takeWhile ((=) 0) (a # word) =
        0 # takeWhile ((=) 0) word"
      by (subst True) (simp only: takeWhile.simps simp_thms(6) if_True)
    have smaller: "Suc (length (takeWhile ((=) 0) word)) < Suc (length word)"
      using Cons.prems by (simp only: zero_prefix list.size)
    have proper: "length (takeWhile ((=) 0) word) < length word"
      by (rule Suc_less_SucD[OF smaller])
    have notall: "\<not> (\<forall>x \<in> set (rev word). x = 0)"
      using reflected_cell_takewhile_full[of "((=) 0)" word] proper by auto
    obtain x where member: "x \<in> set (rev word)" and failure: "\<not> ((=) 0) x"
      using notall by auto
    have trailing: "takeWhile ((=) 0) (rev word @ [0]) =
        takeWhile ((=) 0) (rev word)"
      by (rule takeWhile_append1[where P="((=) 0)", OF member failure])
    have suffix: "takeWhile ((=) 0) (rev (a # word)) =
        takeWhile ((=) 0) (rev word)"
      by (subst True) (simp only: rev.simps trailing)
    show ?thesis using Cons.IH[OF proper]
      by (simp only: zero_prefix list.size suffix; arith)
  next
    case False
    have neq: "0 \<noteq> a" using False by auto
    have no_prefix: "takeWhile ((=) 0) (a # word) = []"
      by (simp only: takeWhile.simps neq if_False)
    note bound = length_takeWhile_le[of "((=) 0)" "rev (a # word)"]
    show ?thesis using bound
      by (simp only: no_prefix list.size length_rev add_0_left)
  qed
qed

lemma reflected_slp_zero_edges_bounds:
  assumes edges: "reflected_slp_zero_edges source = (width, prefix, suffix)"
  shows "width - suffix \<le> double_reverse_source_slp_length source"
    "prefix \<noteq> width \<Longrightarrow> prefix \<le> width - suffix"
proof -
  let ?word = "double_reverse_source_slp_word source"
  have summary: "reflected_cell_zero_edges ?word = (width, prefix, suffix)"
    using edges reflected_slp_zero_edges_exact by simp
  have eqs: "width = length ?word"
    "prefix = length (takeWhile ((=) 0) ?word)"
    "suffix = length (takeWhile ((=) 0) (rev ?word))"
    using summary by (simp_all add: reflected_cell_zero_edges_def)
  show "width - suffix \<le> double_reverse_source_slp_length source"
    using eqs by (simp add: double_reverse_source_slp_word_length)
  assume "prefix \<noteq> width"
  then have proper: "length (takeWhile ((=) 0) ?word) < length ?word"
    using eqs length_takeWhile_le[of "((=) 0)" ?word] by arith
  show "prefix \<le> width - suffix"
    using reflected_cell_nonzero_zero_edges_disjoint[OF proper] eqs by arith
qed

definition reflected_cell_decimal_shift :: "nat list \<Rightarrow> nat list" where
  "reflected_cell_decimal_shift cells =
    (if cells = [] then [] else
      double_reverse_adjacent (\<lambda>a b. a div 10 + 10 * (b mod 10)) cells @
      (if last cells < 10 then [] else [last cells div 10]))"

lemma reflected_cell_decimal_shift_cons:
  "reflected_cell_decimal_shift (a # b # rest) =
    (a div 10 + 10 * (b mod 10)) # reflected_cell_decimal_shift (b # rest)"
  by (cases rest) (simp_all add: reflected_cell_decimal_shift_def)

lemma reflected_shift_low_digit:
  fixes q r :: nat
  assumes "q < 10"
  shows "(q + 10 * r) mod 10 = q"
proof -
  have "(q + 10 * r) mod 10 = q mod 10"
    by (rule mod_mult_self2)
  also have "... = q" by (rule mod_less[OF assms])
  finally show ?thesis .
qed

lemma reflected_cell_decimal_shift_digits:
  assumes "list_all (\<lambda>cell. cell < 100) cells" "cells \<noteq> []"
  shows "reflected_lsd_digits_of_cells (reflected_cell_decimal_shift cells) @
      (if last cells < 10 then [0] else []) =
    tl (reflected_lsd_digits_of_cells cells) @
      (if last cells < 10 then [] else [0])"
  using assms
proof (induction cells)
  case Nil
  then show ?case by simp
next
  case (Cons a cells)
  note IH = Cons.IH
  note valid = Cons.prems
  have a: "a < 100" using valid by simp
  have digit: "a div 10 < 10" using a by simp
  show ?case
  proof (cases cells)
    case Nil
    then show ?thesis using digit
      by (auto simp: reflected_cell_decimal_shift_def)
  next
    case (Cons b rest)
    have tail: "list_all (\<lambda>cell. cell < 100) (b # rest)"
      using valid Cons by simp
    have low: "(a div 10 + 10 * (b mod 10)) mod 10 = a div 10"
      by (rule reflected_shift_low_digit[OF digit])
    have high: "(a div 10 + 10 * (b mod 10)) div 10 = b mod 10"
      using digit by simp
    have recursive:
      "reflected_lsd_digits_of_cells (reflected_cell_decimal_shift (b # rest)) @
          (if last (b # rest) < 10 then [0] else []) =
        tl (reflected_lsd_digits_of_cells (b # rest)) @
          (if last (b # rest) < 10 then [] else [0])"
      using IH tail Cons by simp
    show ?thesis using recursive Cons low high
      by (simp add: reflected_cell_decimal_shift_cons)
  qed
qed

definition reflected_slp_decimal_shift :: "double_reverse_source_slp \<Rightarrow> double_reverse_source_slp" where
  "reflected_slp_decimal_shift source =
    (if double_reverse_source_slp_word source = [] then Double_Reverse_Source_Empty
     else Double_Reverse_Source_Concat
       (double_reverse_adjacent_slp (\<lambda>a b. a div 10 + 10 * (b mod 10)) source)
       (if last (double_reverse_source_slp_word source) < 10 then Double_Reverse_Source_Empty
        else Double_Reverse_Source_Term (last (double_reverse_source_slp_word source) div 10)))"

theorem reflected_slp_decimal_shift_exact:
  "double_reverse_source_slp_word (reflected_slp_decimal_shift source) =
    reflected_cell_decimal_shift (double_reverse_source_slp_word source)"
  by (simp add: reflected_slp_decimal_shift_def reflected_cell_decimal_shift_def
      double_reverse_adjacent_slp_exact)

definition reflected_slp_normalize :: "double_reverse_source_slp \<Rightarrow> double_reverse_source_slp" where
  "reflected_slp_normalize source =
    (case reflected_slp_zero_edges source of (width, prefix, suffix) \<Rightarrow>
      if prefix = width then Double_Reverse_Source_Term 0
      else let cut = double_reverse_source_slp_part source prefix (width - suffix)
        in if hd (double_reverse_source_slp_word cut) mod 10 \<noteq> 0 then cut
           else reflected_slp_decimal_shift cut)"

theorem reflected_slp_normalize_exact:
  assumes edges: "reflected_slp_zero_edges source = (width, prefix, suffix)"
  defines "trimmed \<equiv> take (width - suffix - prefix)
      (drop prefix (double_reverse_source_slp_word source))"
  shows "double_reverse_source_slp_word (reflected_slp_normalize source) =
    (if prefix = width then [0]
     else if hd trimmed mod 10 \<noteq> 0 then trimmed
     else reflected_cell_decimal_shift trimmed)"
proof (cases "prefix = width")
  case True
  then show ?thesis using edges by (simp add: reflected_slp_normalize_def)
next
  case False
  note bounds = reflected_slp_zero_edges_bounds[OF edges]
  note exact = double_reverse_source_slp_part_exact[OF bounds(2)[OF False] bounds(1)]
  show ?thesis using edges False exact
    by (simp add: reflected_slp_normalize_def Let_def trimmed_def
        reflected_slp_decimal_shift_exact)
qed

lemma reflected_lsd_digits_of_zero_cells:
  "reflected_lsd_digits_of_cells (replicate n 0) = replicate (2*n) 0"
  by (induction n) (simp_all add: replicate_add)

lemma reflected_pad_low_zeros:
  assumes valid: "reflected_decimal x"
  shows "reflected_pad_equiv (replicate n 0 @ x) x"
proof (induction n)
  case 0
  then show ?case by (simp add: reflected_pad_equiv.same valid)
next
  case (Suc n)
  have zeros: "reflected_decimal (replicate n 0)"
    by (induction n) simp_all
  have digits: "reflected_decimal (replicate n 0 @ x)"
    using zeros valid by (simp only: list_all_append)
  have first: "reflected_pad_equiv (0 # (replicate n 0 @ x)) (replicate n 0 @ x)"
    by (rule reflected_pad_equiv.low[OF digits])
  show ?case using reflected_pad_equiv.compose[OF first Suc.IH] by simp
qed

(* Remaining proof obligations to connect to normalize output:
   1. For nonzero cells, source = replicate prefix 0 @ trimmed @ replicate suffix 0,
      with the two counts from reflected_slp_zero_edges_exact. Derive from
      takeWhile_dropWhile_id twice (second on the reversed remainder).
   2. Use append + replicate zero + reflected_pad_equiv.low/high to transport
      digit expansion across that decomposition; show trimmed cell validity.
   3. If hd trimmed mod 10 = 0, use reflected_cell_decimal_shift_digits. Its
      low-digit zero, and whichever optional high zero appears, yield the
      desired equivalence via low/high/symmetric/compose. Handle all-zero
      separately with Term 0 equivalent to [] and append-zero rules.
   4. Replace the spec word via reflected_slp_normalize_exact and the existing
      source SLP shift exactness. *)

lemma reflected_pad_two_low_zeros:
  assumes valid: "reflected_decimal xs"
  shows "reflected_pad_equiv (0 # 0 # xs) xs"
proof -
  have first: "reflected_pad_equiv (0 # 0 # xs) (0 # xs)"
    by (rule reflected_pad_equiv.low) (use valid in simp)
  show ?thesis using first reflected_pad_equiv.low[OF valid]
    by (rule reflected_pad_equiv.compose)
qed

lemma reflected_pad_two_high_zeros:
  assumes valid: "reflected_decimal xs"
  shows "reflected_pad_equiv (xs @ [0,0]) xs"
proof -
  have first: "reflected_pad_equiv ((xs @ [0]) @ [0]) (xs @ [0])"
    by (rule reflected_pad_equiv.high) (use valid in simp)
  have "reflected_pad_equiv ((xs @ [0]) @ [0]) xs"
    using first reflected_pad_equiv.high[OF valid]
    by (rule reflected_pad_equiv.compose)
  then show ?thesis by simp
qed

lemma reflected_expand_trim_low_equiv:
  assumes valid: "list_all (\<lambda>cell. cell < 100) cells"
  shows "reflected_pad_equiv
    (reflected_lsd_digits_of_cells (dropWhile ((=) 0) cells))
    (reflected_lsd_digits_of_cells cells)"
  using valid
proof (induction cells)
  case Nil
  then show ?case by (simp add: reflected_pad_equiv.same)
next
  case (Cons cell rest)
  show ?case
  proof (cases "cell = 0")
    case True
    have rest: "list_all (\<lambda>cell. cell < 100) rest" using Cons.prems by simp
    have digits: "reflected_decimal (reflected_lsd_digits_of_cells rest)"
      by (rule reflected_lsd_digits_of_cells_valid[OF rest])
    have link: "reflected_pad_equiv (reflected_lsd_digits_of_cells rest)
        (0 # 0 # reflected_lsd_digits_of_cells rest)"
      by (rule reflected_pad_equiv.symmetric[OF reflected_pad_two_low_zeros[OF digits]])
    show ?thesis using reflected_pad_equiv.compose[OF Cons.IH[OF rest] link] True by simp
  next
    case False
    have digits: "reflected_decimal (reflected_lsd_digits_of_cells (cell # rest))"
      by (rule reflected_lsd_digits_of_cells_valid[OF Cons.prems])
    show ?thesis using False reflected_pad_equiv.same[OF digits] by simp
  qed
qed

lemma reflected_expand_trim_high_equiv:
  assumes valid: "list_all (\<lambda>cell. cell < 100) cells"
  shows "reflected_pad_equiv
    (reflected_lsd_digits_of_cells (reflected_trim_high cells))
    (reflected_lsd_digits_of_cells cells)"
  using valid
proof (induction cells rule: rev_induct)
  case Nil
  then show ?case by (simp add: reflected_trim_high_def reflected_pad_equiv.same)
next
  case (snoc cell rest)
  show ?case
  proof (cases "cell = 0")
    case True
    have rest: "list_all (\<lambda>cell. cell < 100) rest" using snoc.prems by simp
    have digits: "reflected_decimal (reflected_lsd_digits_of_cells rest)"
      by (rule reflected_lsd_digits_of_cells_valid[OF rest])
    have link: "reflected_pad_equiv (reflected_lsd_digits_of_cells rest)
        (reflected_lsd_digits_of_cells rest @ [0,0])"
      by (rule reflected_pad_equiv.symmetric[OF reflected_pad_two_high_zeros[OF digits]])
    show ?thesis using reflected_pad_equiv.compose[OF snoc.IH[OF rest] link] True
      by (simp add: reflected_trim_high_def reflected_lsd_digits_of_cells_append)
  next
    case False
    have digits: "reflected_decimal (reflected_lsd_digits_of_cells (rest @ [cell]))"
      by (rule reflected_lsd_digits_of_cells_valid[OF snoc.prems])
    show ?thesis using False digits
      by (simp add: reflected_trim_high_def reflected_pad_equiv.same)
  qed
qed

lemma reflected_expand_drop_zero_equiv:
  assumes valid: "list_all (\<lambda>cell. cell < 100) cells"
    and zeros: "list_all ((=) 0) (take n cells)"
  shows "reflected_pad_equiv (reflected_lsd_digits_of_cells (drop n cells))
    (reflected_lsd_digits_of_cells cells)"
proof -
  let ?prefix = "take n cells"
  let ?tail = "drop n cells"
  have tail_valid: "list_all (\<lambda>cell. cell < 100) ?tail"
    using valid set_drop_subset[of n cells] by (auto simp: list_all_iff)
  have tail_digits: "reflected_decimal (reflected_lsd_digits_of_cells ?tail)"
    by (rule reflected_lsd_digits_of_cells_valid[OF tail_valid])
  have prefix: "?prefix = replicate (length ?prefix) 0"
    using replicate_length_same[of ?prefix 0] zeros by (auto simp: list_all_iff)
  have equiv: "reflected_pad_equiv
      (replicate (2 * length ?prefix) 0 @ reflected_lsd_digits_of_cells ?tail)
      (reflected_lsd_digits_of_cells ?tail)"
    by (rule reflected_pad_low_zeros[OF tail_digits])
  have split: "reflected_lsd_digits_of_cells cells =
      reflected_lsd_digits_of_cells ?prefix @ reflected_lsd_digits_of_cells ?tail"
    using arg_cong[OF append_take_drop_id[of n cells], of reflected_lsd_digits_of_cells]
    by (simp only: reflected_lsd_digits_of_cells_append)
  have prefix_digits: "reflected_lsd_digits_of_cells ?prefix =
      replicate (2 * length ?prefix) 0"
    by (subst prefix) (rule reflected_lsd_digits_of_zero_cells)
  have expanded: "reflected_lsd_digits_of_cells cells =
      replicate (2 * length ?prefix) 0 @ reflected_lsd_digits_of_cells ?tail"
    using split by (simp only: prefix_digits)
  show ?thesis using reflected_pad_equiv.symmetric[OF equiv] expanded by simp
qed

lemma reflected_cell_trim_high_take:
  "reflected_trim_high cells =
    take (length cells - length (takeWhile ((=) 0) (rev cells))) cells"
  by (simp add: reflected_trim_high_def dropWhile_eq_drop rev_drop)

lemma reflected_shift_padding_equiv:
  assumes valid: "list_all (\<lambda>cell. cell < 100) cells"
    and nonempty: "cells \<noteq> []" and low: "hd cells mod 10 = 0"
  shows "reflected_pad_equiv
    (reflected_lsd_digits_of_cells (reflected_cell_decimal_shift cells))
    (reflected_lsd_digits_of_cells cells)"
proof -
  let ?original = "reflected_lsd_digits_of_cells cells"
  let ?tail = "tl ?original"
  let ?shift = "reflected_lsd_digits_of_cells (reflected_cell_decimal_shift cells)"
  have digits: "reflected_decimal ?original"
    by (rule reflected_lsd_digits_of_cells_valid[OF valid])
  have tail_valid: "reflected_decimal ?tail" using digits by (cases ?original) auto
  have decompose: "?original = 0 # ?tail" using nonempty low by (cases cells) auto
  have tail_to_original: "reflected_pad_equiv ?tail ?original"
    using reflected_pad_equiv.symmetric[OF reflected_pad_equiv.low[OF tail_valid]]
      decompose by simp
  note equation = reflected_cell_decimal_shift_digits[OF valid nonempty]
  have shift_to_tail: "reflected_pad_equiv ?shift ?tail"
  proof (cases "last cells < 10")
    case True
    have eq: "?shift @ [0] = ?tail" using equation True by simp
    have appended: "reflected_decimal (?shift @ [0])"
      using tail_valid by (simp only: eq)
    have shift_valid: "reflected_decimal ?shift"
      using appended by (simp only: list_all_append)
    have append_pad: "reflected_pad_equiv (?shift @ [0]) ?shift"
      by (rule reflected_pad_equiv.high[OF shift_valid])
    show ?thesis using reflected_pad_equiv.symmetric[OF append_pad]
      by (simp only: eq)
  next
    case False
    have eq: "?shift = ?tail @ [0]" using equation False by simp
    show ?thesis using reflected_pad_equiv.high[OF tail_valid] eq by simp
  qed
  show ?thesis by (rule reflected_pad_equiv.compose[OF shift_to_tail tail_to_original])
qed

lemma reflected_cell_zero_prefix_list:
  "list_all ((=) 0) (takeWhile ((=) 0) cells)"
  by (induction cells) auto

theorem reflected_slp_normalize_padding:
  assumes valid: "list_all (\<lambda>cell. cell < 100) (double_reverse_source_slp_word source)"
  shows "reflected_pad_equiv
    (reflected_lsd_digits_of_cells (double_reverse_source_slp_word
      (reflected_slp_normalize source)))
    (reflected_lsd_digits_of_cells (double_reverse_source_slp_word source))"
proof -
  let ?word = "double_reverse_source_slp_word source"
  obtain width prefix suffix where edges:
    "reflected_slp_zero_edges source = (width, prefix, suffix)"
    by (cases "reflected_slp_zero_edges source") auto
  have summary: "reflected_cell_zero_edges ?word = (width, prefix, suffix)"
    using edges reflected_slp_zero_edges_exact by simp
  have eqs: "width = length ?word"
    "prefix = length (takeWhile ((=) 0) ?word)"
    "suffix = length (takeWhile ((=) 0) (rev ?word))"
    using summary by (simp_all add: reflected_cell_zero_edges_def)
  let ?trim = "take (width - suffix - prefix) (drop prefix ?word)"
  have normalized: "double_reverse_source_slp_word (reflected_slp_normalize source) =
    (if prefix = width then [0]
     else if hd ?trim mod 10 \<noteq> 0 then ?trim
     else reflected_cell_decimal_shift ?trim)"
    by (rule reflected_slp_normalize_exact[OF edges])
  show ?thesis
  proof (cases "prefix = width")
    case True
    have all_zero: "list_all ((=) 0) ?word"
      using True eqs reflected_cell_takewhile_full[of "((=) 0)" ?word]
      by (simp add: list_all_iff)
    have whole: "take width ?word = ?word" using eqs(1) by simp
    have zeros: "list_all ((=) 0) (take width ?word)"
      using all_zero by (simp only: whole)
    have dropped: "reflected_pad_equiv
        (reflected_lsd_digits_of_cells (drop width ?word))
        (reflected_lsd_digits_of_cells ?word)"
      by (rule reflected_expand_drop_zero_equiv[OF valid zeros])
    have empty: "reflected_pad_equiv [] (reflected_lsd_digits_of_cells ?word)"
      using dropped eqs by simp
    have zero: "reflected_pad_equiv [0,0] []"
      by (rule reflected_pad_two_low_zeros) simp
    show ?thesis using reflected_pad_equiv.compose[OF zero empty] normalized True by simp
  next
    case False
    let ?high = "reflected_trim_high ?word"
    have cut: "prefix \<le> width - suffix"
      using reflected_slp_zero_edges_bounds[OF edges] False by blast
    have high_take: "?high = take (width - suffix) ?word"
      using reflected_cell_trim_high_take[of ?word] eqs by simp
    have high_valid: "list_all (\<lambda>cell. cell < 100) ?high"
      using valid high_take set_take_subset[of "width - suffix" ?word]
      by (auto simp: list_all_iff)
    have prefix_high: "take prefix ?high = take prefix ?word"
      by (simp only: high_take take_take min.absorb1[OF cut])
    have prefix_word: "take prefix ?word = takeWhile ((=) 0) ?word"
      by (subst eqs(2)) (rule takeWhile_eq_take[symmetric])
    have prefix_take: "take prefix ?high = takeWhile ((=) 0) ?word"
      by (rule trans[OF prefix_high prefix_word])
    have prefix_zero: "list_all ((=) 0) (take prefix ?high)"
      using prefix_take reflected_cell_zero_prefix_list by simp
    have trimmed: "drop prefix ?high = ?trim"
      by (simp add: high_take drop_take)
    have trim_to_high: "reflected_pad_equiv (reflected_lsd_digits_of_cells ?trim)
        (reflected_lsd_digits_of_cells ?high)"
      using reflected_expand_drop_zero_equiv[OF high_valid prefix_zero] trimmed by simp
    have high_to_word: "reflected_pad_equiv (reflected_lsd_digits_of_cells ?high)
        (reflected_lsd_digits_of_cells ?word)"
      by (rule reflected_expand_trim_high_equiv[OF valid])
    have trim_to_word: "reflected_pad_equiv (reflected_lsd_digits_of_cells ?trim)
        (reflected_lsd_digits_of_cells ?word)"
      by (rule reflected_pad_equiv.compose[OF trim_to_high high_to_word])
    have trim_valid: "list_all (\<lambda>cell. cell < 100) ?trim"
      using valid set_take_subset[of "width - suffix - prefix" "drop prefix ?word"]
        set_drop_subset[of prefix ?word] by (auto simp: list_all_iff)
    show ?thesis
    proof (cases "hd ?trim mod 10 = 0")
      case False
      then show ?thesis using normalized `prefix \<noteq> width` trim_to_word by simp
    next
      case True
      have shift: "reflected_pad_equiv
          (reflected_lsd_digits_of_cells (reflected_cell_decimal_shift ?trim))
          (reflected_lsd_digits_of_cells ?trim)"
      proof (cases "?trim = []")
        case True
        have empty: "reflected_pad_equiv [] []"
          by (rule reflected_pad_equiv.same) simp
        show ?thesis using empty
          by (simp only: True reflected_cell_decimal_shift_def simp_thms(6)
              if_True reflected_lsd_digits_of_cells.simps)
      next
        case False
        show ?thesis by (rule reflected_shift_padding_equiv[OF trim_valid False True])
      qed
      show ?thesis using reflected_pad_equiv.compose[OF shift trim_to_word]
        normalized `prefix \<noteq> width` True by simp
    qed
  qed
qed

(* A nonzero source has a nonzero cell after the zero-edge slice. If that
   cell is divisible by 10, its quotient is in 1..9, so the adjacent-cell
   right shift has nonzero low decimal digit. The all-zero source normalizes
   to [0,0], whose value is zero. *)

lemma reflected_cell_nonzero_zero_edges_strict:
  assumes "length (takeWhile ((=) 0) word) < length word"
  shows "length (takeWhile ((=) 0) word) +
    length (takeWhile ((=) 0) (rev word)) < length word"
  using assms
proof (induction word)
  case Nil
  then show ?case by simp
next
  case (Cons a word)
  show ?case
  proof (cases "a = 0")
    case True
    have zero_prefix: "takeWhile ((=) 0) (a # word) =
        0 # takeWhile ((=) 0) word"
      by (subst True) (simp only: takeWhile.simps simp_thms(6) if_True)
    have smaller: "Suc (length (takeWhile ((=) 0) word)) < Suc (length word)"
      using Cons.prems by (simp only: zero_prefix list.size)
    have proper: "length (takeWhile ((=) 0) word) < length word"
      by (rule Suc_less_SucD[OF smaller])
    have notall: "\<not> (\<forall>x \<in> set (rev word). x = 0)"
      using reflected_cell_takewhile_full[of "((=) 0)" word] proper by auto
    obtain x where member: "x \<in> set (rev word)" and failure: "\<not> ((=) 0) x"
      using notall by auto
    have trailing: "takeWhile ((=) 0) (rev word @ [0]) =
        takeWhile ((=) 0) (rev word)"
      by (rule takeWhile_append1[where P="((=) 0)", OF member failure])
    have suffix: "takeWhile ((=) 0) (rev (a # word)) =
        takeWhile ((=) 0) (rev word)"
      by (subst True) (simp only: rev.simps trailing)
    show ?thesis using Cons.IH[OF proper]
      by (simp only: zero_prefix list.size suffix; arith)
  next
    case False
    have neq: "0 \<noteq> a" using False by auto
    have no_prefix: "takeWhile ((=) 0) (a # word) = []"
      by (simp only: takeWhile.simps neq if_False)
    have trailing: "takeWhile ((=) 0) (rev word @ [a]) =
        takeWhile ((=) 0) (rev word)"
      by (rule takeWhile_tail) (use neq in simp)
    note bound = length_takeWhile_le[of "((=) 0)" "rev word"]
    show ?thesis using bound
      by (simp only: no_prefix list.size rev.simps trailing length_rev; arith)
  qed
qed

lemma reflected_normalize_trimmed_nonzero_head:
  assumes edges: "reflected_slp_zero_edges source = (width, prefix, suffix)"
    and nonzero: "prefix \<noteq> width"
  defines "trimmed \<equiv> take (width - suffix - prefix)
    (drop prefix (double_reverse_source_slp_word source))"
  shows "trimmed \<noteq> []" "hd trimmed \<noteq> 0"
proof -
  let ?word = "double_reverse_source_slp_word source"
  have summary: "reflected_cell_zero_edges ?word = (width, prefix, suffix)"
    using edges reflected_slp_zero_edges_exact by simp
  have eqs: "width = length ?word" "prefix = length (takeWhile ((=) 0) ?word)"
    "suffix = length (takeWhile ((=) 0) (rev ?word))"
    using summary by (simp_all add: reflected_cell_zero_edges_def)
  have proper: "length (takeWhile ((=) 0) ?word) < length ?word"
    using nonzero eqs length_takeWhile_le[of "((=) 0)" ?word] by arith
  have strict: "prefix + suffix < width"
    using reflected_cell_nonzero_zero_edges_strict[OF proper] eqs by simp
  show nonempty: "trimmed \<noteq> []"
    using proper strict eqs by (simp add: trimmed_def)
  have nth: "?word ! prefix \<noteq> 0"
    using nth_length_takeWhile[OF proper] eqs by simp
  show "hd trimmed \<noteq> 0"
    using nth proper strict eqs by (simp add: trimmed_def hd_drop_conv_nth)
qed

lemma reflected_shift_has_nonzero_low_digit:
  assumes valid: "list_all (\<lambda>cell. cell < 100) cells"
    and nonempty: "cells \<noteq> []" and head: "hd cells \<noteq> 0"
    and low: "hd cells mod 10 = 0"
  shows "reflected_lsd_digits_of_cells (reflected_cell_decimal_shift cells) \<noteq> []"
    "hd (reflected_lsd_digits_of_cells (reflected_cell_decimal_shift cells)) \<noteq> 0"
proof -
  obtain a rest where cells: "cells = a # rest" using nonempty by (cases cells) auto
  have a: "a < 100" "a \<noteq> 0" "a mod 10 = 0" using valid head low cells by simp_all
  have ten_le: "10 \<le> a" using a by (cases "a < 10") (auto simp: mod_less)
  have q: "0 < a div 10" "a div 10 < 10" using a ten_le by simp_all
  show "reflected_lsd_digits_of_cells (reflected_cell_decimal_shift cells) \<noteq> []"
    using ten_le cells by (cases rest) (simp_all add: reflected_cell_decimal_shift_def
      reflected_cell_decimal_shift_cons)
  show "hd (reflected_lsd_digits_of_cells (reflected_cell_decimal_shift cells)) \<noteq> 0"
  proof (cases rest)
    case Nil
    then show ?thesis using cells q ten_le
      by (simp add: reflected_cell_decimal_shift_def)
  next
    case (Cons b tail)
    have low_digit: "(a div 10 + 10 * (b mod 10)) mod 10 = a div 10"
      by (rule reflected_shift_low_digit[OF q(2)])
    then show ?thesis using cells Cons q
      by (simp add: reflected_cell_decimal_shift_cons)
  qed
qed

theorem reflected_slp_normalize_emit_inlet:
  assumes valid: "list_all (\<lambda>cell. cell < 100) (double_reverse_source_slp_word source)"
  defines "digits \<equiv> reflected_lsd_digits_of_cells
      (double_reverse_source_slp_word (reflected_slp_normalize source))"
  shows "reflected_trim_low digits = digits \<or> decimal_lsd_value digits = 0"
proof -
  let ?word = "double_reverse_source_slp_word source"
  obtain width prefix suffix where edges:
    "reflected_slp_zero_edges source = (width, prefix, suffix)"
    by (cases "reflected_slp_zero_edges source") auto
  let ?trim = "take (width - suffix - prefix) (drop prefix ?word)"
  have normalized: "double_reverse_source_slp_word (reflected_slp_normalize source) =
    (if prefix = width then [0]
     else if hd ?trim mod 10 \<noteq> 0 then ?trim
     else reflected_cell_decimal_shift ?trim)"
    by (rule reflected_slp_normalize_exact[OF edges])
  show ?thesis
  proof (cases "prefix = width")
    case True
    then show ?thesis using normalized by (simp add: digits_def)
  next
    case False
    note source_nonzero = False
    have head: "?trim \<noteq> []" "hd ?trim \<noteq> 0"
      using reflected_normalize_trimmed_nonzero_head[OF edges False] by auto
    have trim_valid: "list_all (\<lambda>cell. cell < 100) ?trim"
      using valid set_take_subset[of "width - suffix - prefix" "drop prefix ?word"]
        set_drop_subset[of prefix ?word] by (auto simp: list_all_iff)
    have low_nonzero:
      "reflected_lsd_digits_of_cells
        (double_reverse_source_slp_word (reflected_slp_normalize source)) \<noteq> [] \<and>
      hd (reflected_lsd_digits_of_cells
        (double_reverse_source_slp_word (reflected_slp_normalize source))) \<noteq> 0"
    proof (cases "hd ?trim mod 10 = 0")
      case True
      show ?thesis
        using reflected_shift_has_nonzero_low_digit[OF trim_valid head True] normalized source_nonzero True
        by auto
    next
      case False
      have selected: "double_reverse_source_slp_word (reflected_slp_normalize source) = ?trim"
        using normalized source_nonzero False by simp
      obtain a rest where cells: "?trim = a # rest" using head(1) by (cases ?trim) auto
      have nonzero: "a mod 10 \<noteq> 0"
        using False by (simp only: cells list.sel; simp)
      show ?thesis using nonzero
        by (simp only: selected cells reflected_lsd_digits_of_cells.simps list.simps; simp)
    qed
    then show ?thesis by (cases digits) (auto simp: digits_def reflected_trim_low_def)
  qed
qed

ML \<open>
  val checked = @{thms reflected_slp_zero_edges_exact reflected_slp_zero_edges_bounds
    reflected_slp_decimal_shift_exact
    reflected_cell_decimal_shift_digits
    reflected_slp_normalize_exact reflected_slp_normalize_padding
    reflected_slp_normalize_emit_inlet};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Reflected SLP normalization depends on an oracle";
  val _ = if Thm_Deps.has_skip_proof checked
    then error "Skipped reflected SLP normalization proof" else ();
\<close>

end
