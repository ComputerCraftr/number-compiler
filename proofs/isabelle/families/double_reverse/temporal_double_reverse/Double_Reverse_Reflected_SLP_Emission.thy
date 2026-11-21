theory Double_Reverse_Reflected_SLP_Emission
  imports Double_Reverse_Reflected_SLP_Seams
begin

text \<open>Scale the LSD-first base-100 source using the previous cell's
carry, retain the final carry when it is nonzero, then publish cells in
MSD-first decimal order. This does not yet establish stage admission or trim.\<close>

definition reflected_slp_scale_cells ::
  "nat \<Rightarrow> double_reverse_source_slp \<Rightarrow> double_reverse_source_slp" where
  "reflected_slp_scale_cells m source =
    (let cells = double_reverse_source_slp_word source in
     if cells = [] then Double_Reverse_Source_Empty
     else Double_Reverse_Source_Concat
       (Double_Reverse_Source_Term (m * hd cells mod 100))
       (Double_Reverse_Source_Concat
         (double_reverse_adjacent_slp
           (\<lambda>previous current. m * current mod 100 + previous div (100 div m)) source)
         (if last cells div (100 div m) = 0 then Double_Reverse_Source_Empty
          else Double_Reverse_Source_Term (last cells div (100 div m)))))"

theorem reflected_slp_scale_cells_exact:
  assumes m: "multiplier = 2 \<or> multiplier = 5"
    and valid: "list_all (\<lambda>cell. cell < 100) (double_reverse_source_slp_word source)"
  shows "double_reverse_source_slp_word (reflected_slp_scale_cells multiplier source) =
    reflected_decimal_cells_run multiplier 0 (double_reverse_source_slp_word source)"
proof (cases "double_reverse_source_slp_word source")
  case Nil
  then show ?thesis by (simp add: reflected_slp_scale_cells_def)
next
  case (Cons cell rest)
  have inlet: "0 < multiplier" using m by auto
  have run: "reflected_decimal_cells_run multiplier 0 (cell # rest) =
    (multiplier * cell mod 100 + 0) #
      (double_reverse_adjacent
        (\<lambda>previous current. multiplier * current mod 100 +
          previous div (100 div multiplier)) (cell # rest) @
       (if last (cell # rest) div (100 div multiplier) = 0 then []
        else [last (cell # rest) div (100 div multiplier)]))"
    by (rule reflected_decimal_cells_run_adjacent[OF m _ inlet]) (use valid Cons in simp)
  show ?thesis using run Cons
    by (simp add: reflected_slp_scale_cells_def double_reverse_adjacent_slp_exact)
qed

theorem reflected_slp_scaled_decimal_exact:
  assumes "multiplier = 2 \<or> multiplier = 5"
    "list_all (\<lambda>cell. cell < 100) (double_reverse_source_slp_word source)"
  shows "double_reverse_source_slp_word
      (reflected_slp_cell_digits (reflected_slp_scale_cells multiplier source)) =
    concat (map (\<lambda>cell. [cell div 10, cell mod 10])
      (rev (reflected_decimal_cells_run multiplier 0 (double_reverse_source_slp_word source))))"
  by (simp only: reflected_slp_cell_digits_exact reflected_slp_scale_cells_exact[OF assms])

theorem reflected_decimal_cells_run_value:
  assumes m: "multiplier = 2 \<or> multiplier = 5"
    and cells: "list_all (\<lambda>cell. cell < 100) source"
    and inlet: "carry < multiplier"
  shows "reflected_lsd_cell_value (reflected_decimal_cells_run multiplier carry source) =
    multiplier * reflected_lsd_cell_value source + carry"
  using cells inlet
proof (induction source arbitrary: carry)
  case Nil
  then show ?case using m by (cases "carry = 0") simp_all
next
  case (Cons cell rest)
  have cell: "cell < 100" and rest: "list_all (\<lambda>cell. cell < 100) rest"
    using Cons.prems by simp_all
  have outgoing: "(multiplier * cell + carry) div 100 < multiplier"
    using m cell Cons.prems(2)
    by (elim disjE; simp_all add: div_less_iff_less_mult; arith)
  have rec: "reflected_lsd_cell_value
      (reflected_decimal_cells_run multiplier ((multiplier * cell + carry) div 100) rest) =
    multiplier * reflected_lsd_cell_value rest + ((multiplier * cell + carry) div 100)"
    by (rule Cons.IH[OF rest outgoing])
  have split: "((multiplier * cell + carry) div 100) * 100 +
      (multiplier * cell + carry) mod 100 = multiplier * cell + carry"
    by (rule div_mult_mod_eq)
  show ?case using rec split by (simp add: algebra_simps)
qed

lemma reflected_lsd_digits_cells_value:
  "decimal_lsd_value (reflected_lsd_digits_of_cells cells) = reflected_lsd_cell_value cells"
proof (induction cells)
  case Nil
  then show ?case by simp
next
  case (Cons cell rest)
  have split: "cell div 10 * 10 + cell mod 10 = cell" by (rule div_mult_mod_eq)
  show ?case using Cons.IH split by (simp add: algebra_simps)
qed

lemma reflected_cell_digits_reverse:
  "rev (concat (map (\<lambda>cell. [cell div 10, cell mod 10]) (rev cells))) =
    reflected_lsd_digits_of_cells cells"
  by (induction cells) (simp_all add: reflected_lsd_digits_of_cells_append)

theorem reflected_slp_scaled_decimal_value:
  assumes m: "multiplier = 2 \<or> multiplier = 5"
    and valid: "list_all (\<lambda>cell. cell < 100) (double_reverse_source_slp_word source)"
  shows "decimal_lsd_value (rev (double_reverse_source_slp_word
      (reflected_slp_cell_digits (reflected_slp_scale_cells multiplier source)))) =
    multiplier * reflected_lsd_cell_value (double_reverse_source_slp_word source)"
proof -
  have inlet: "0 < multiplier" using m by auto
  show ?thesis
    using reflected_slp_scaled_decimal_exact[OF m valid]
      reflected_decimal_cells_run_value[OF m valid inlet]
    by (simp add: reflected_cell_digits_reverse reflected_lsd_digits_cells_value)
qed

definition reflected_msd_drop_one_zero :: "nat list \<Rightarrow> nat list" where
  "reflected_msd_drop_one_zero digits =
    (case digits of [] \<Rightarrow> [] | d # rest \<Rightarrow> if d = 0 then rest else digits)"

lemma reflected_msd_drop_one_zero_value:
  "decimal_lsd_value (rev (reflected_msd_drop_one_zero digits)) =
    decimal_lsd_value (rev digits)"
  by (cases digits) (simp_all add: reflected_msd_drop_one_zero_def decimal_lsd_value_append)

corollary reflected_slp_scaled_trimmed_decimal_value:
  assumes m: "multiplier = 2 \<or> multiplier = 5"
    and valid: "list_all (\<lambda>cell. cell < 100) (double_reverse_source_slp_word source)"
  shows "decimal_lsd_value (rev (reflected_msd_drop_one_zero
      (double_reverse_source_slp_word
        (reflected_slp_cell_digits (reflected_slp_scale_cells multiplier source))))) =
    multiplier * reflected_lsd_cell_value (double_reverse_source_slp_word source)"
  by (simp only: reflected_msd_drop_one_zero_value reflected_slp_scaled_decimal_value[OF m valid])

lemma reflected_decimal_columns_length:
  "length (fst (decimal_multiplier_columns multiplier inlet digits)) = length digits"
proof (induction digits arbitrary: inlet)
  case Nil
  then show ?case by simp
next
  case (Cons digit digits)
  obtain tail carry where eq:
    "decimal_multiplier_columns multiplier ((multiplier * digit + inlet) div 10) digits = (tail, carry)"
    by (cases "decimal_multiplier_columns multiplier ((multiplier * digit + inlet) div 10) digits") auto
  show ?case using Cons.IH[of "(multiplier * digit + inlet) div 10"] eq
    by (simp add: Let_def)
qed

definition reflected_even_final_columns :: "nat list \<Rightarrow> nat list" where
  "reflected_even_final_columns msd_digits =
    (let columns = decimal_multiplier_columns 2 0 (reflected_trim_high msd_digits)
     in fst columns @ (if snd columns = 0 then [] else [snd columns]))"

theorem reflected_even_final_columns_value:
  "decimal_lsd_value (reflected_even_final_columns msd_digits) =
    2 * decimal_lsd_value msd_digits"
proof -
  let ?digits = "reflected_trim_high msd_digits"
  let ?columns = "decimal_multiplier_columns 2 0 ?digits"
  have exact: "2 * decimal_lsd_value ?digits =
    decimal_lsd_value (fst ?columns) + 10 ^ length ?digits * snd ?columns"
    using decimal_multiplier_columns_exact[of 2 ?digits 0] by simp
  show ?thesis using exact
    by (simp add: reflected_even_final_columns_def Let_def decimal_lsd_value_append
        reflected_decimal_columns_length reflected_trim_high_value split: if_splits)
qed

corollary reflected_even_final_reverse_value:
  assumes digits: "list_all (\<lambda>digit. digit < 10) msd_digits"
    and nonempty: "msd_digits \<noteq> []" and high: "hd msd_digits > 0"
  shows "decimal_lsd_value (reflected_even_final_columns msd_digits) =
    2 * decimal_reverse (decimal_lsd_value (rev msd_digits))"
proof -
  have rev_digits: "list_all (\<lambda>digit. digit < 10) (rev msd_digits)"
    using digits by (simp add: list_all_iff)
  have rev_nonempty: "rev msd_digits \<noteq> []" using nonempty by simp
  have rev_high: "last (rev msd_digits) > 0"
    using nonempty high by (cases msd_digits) simp_all
  have reverse: "decimal_reverse (decimal_lsd_value (rev msd_digits)) =
      decimal_lsd_value msd_digits"
    using decimal_reverse_lsd_value[OF rev_digits rev_nonempty rev_high] by simp
  show ?thesis by (simp only: reflected_even_final_columns_value reverse)
qed

lemma reflected_trim_low_zero_value:
  assumes "decimal_lsd_value digits = 0"
  shows "decimal_lsd_value (reflected_trim_low digits) = 0"
  using assms unfolding reflected_trim_low_def by (induction digits) auto

theorem reflected_slp_emission_reflected_emit_value:
  assumes m: "multiplier = 2 \<or> multiplier = 5"
    and valid: "list_all (\<lambda>cell. cell < 100) (double_reverse_source_slp_word source)"
    and normal: "reflected_trim_low (reflected_lsd_digits_of_cells
       (double_reverse_source_slp_word source)) =
        reflected_lsd_digits_of_cells (double_reverse_source_slp_word source) \<or>
      decimal_lsd_value (reflected_lsd_digits_of_cells
        (double_reverse_source_slp_word source)) = 0"
  shows "decimal_lsd_value (rev (reflected_msd_drop_one_zero
      (double_reverse_source_slp_word
        (reflected_slp_cell_digits (reflected_slp_scale_cells multiplier source))))) =
    decimal_lsd_value (reflected_emit multiplier
      (reflected_lsd_digits_of_cells (double_reverse_source_slp_word source)))"
proof -
  let ?digits = "reflected_lsd_digits_of_cells (double_reverse_source_slp_word source)"
  have low: "decimal_lsd_value (reflected_trim_low ?digits) = decimal_lsd_value ?digits"
  proof (cases "reflected_trim_low ?digits = ?digits")
    case True
    then show ?thesis by simp
  next
    case False
    have zero: "decimal_lsd_value ?digits = 0" using normal False by blast
    have "decimal_lsd_value (reflected_trim_low ?digits) = 0"
      by (rule reflected_trim_low_zero_value[OF zero])
    then show ?thesis using zero by simp
  qed
  show ?thesis using reflected_slp_scaled_trimmed_decimal_value[OF m valid] low
    by (simp add: reflected_emit_def reflected_trim_high_value reflected_padded_multiply_value
        reflected_lsd_digits_cells_value)
qed

lemma reflected_positive_cell_msd:
  fixes cell :: nat
  assumes positive: "0 < cell" and bound: "cell < 100"
  shows "hd (reflected_msd_drop_one_zero ([cell div 10, cell mod 10] @ tail)) > 0"
proof (cases "cell < 10")
  case True
  then have q: "cell div 10 = 0" and r: "cell mod 10 = cell" by simp_all
  show ?thesis using positive q r by (simp add: reflected_msd_drop_one_zero_def)
next
  case False
  then have q: "cell div 10 > 0" by (simp add: div_greater_zero_iff)
  show ?thesis using q by (simp add: reflected_msd_drop_one_zero_def)
qed

lemma reflected_decimal_cells_run_high_positive:
  assumes m: "multiplier = 2 \<or> multiplier = 5"
    and valid: "list_all (\<lambda>cell. cell < 100) source"
    and nonempty: "source \<noteq> []" and high: "last source > 0"
    and inlet: "carry < multiplier"
  shows "last (reflected_decimal_cells_run multiplier carry source) > 0"
  using valid nonempty high inlet
proof (induction source arbitrary: carry)
  case Nil
  then show ?case by simp
next
  case (Cons cell rest)
  have cell: "cell < 100" and rest: "list_all (\<lambda>cell. cell < 100) rest"
    using Cons.prems by simp_all
  have outgoing: "(multiplier * cell + carry) div 100 < multiplier"
    using m cell Cons.prems(4)
    by (elim disjE; simp_all add: div_less_iff_less_mult; arith)
  note induction_hypothesis = Cons.IH
  note prems_saved = Cons.prems
  show ?case
  proof (cases rest)
    case Nil
    have positive: "0 < multiplier * cell + carry"
      using m prems_saved(3) Nil by (elim disjE; simp_all; arith)
    show ?thesis
    proof (cases "(multiplier * cell + carry) div 100 = 0")
      case True
      then have small: "multiplier * cell + carry < 100"
        by (simp add: div_eq_0_iff)
      show ?thesis using Nil True positive small by simp
    next
      case False
      then show ?thesis using Nil by simp
    qed
  next
    case (Cons first_cell tail)
    have tail_high: "last rest > 0" using prems_saved(3) Cons by simp
    have recursive: "last (reflected_decimal_cells_run multiplier
        ((multiplier * cell + carry) div 100) rest) > 0"
      by (rule induction_hypothesis[OF rest]) (use Cons tail_high outgoing in auto)
    show ?thesis using recursive Cons by simp
  qed
qed

lemma reflected_decimal_cells_run_bounded:
  assumes m: "multiplier = 2 \<or> multiplier = 5"
    and valid: "list_all (\<lambda>cell. cell < 100) source"
    and inlet: "carry < multiplier"
  shows "list_all (\<lambda>cell. cell < 100)
    (reflected_decimal_cells_run multiplier carry source)"
  using valid inlet
proof (induction source arbitrary: carry)
  case Nil
  then show ?case using m by (cases "carry = 0") auto
next
  case (Cons cell rest)
  have cell: "cell < 100" and rest: "list_all (\<lambda>cell. cell < 100) rest"
    using Cons.prems by simp_all
  have outgoing: "(multiplier * cell + carry) div 100 < multiplier"
    using m cell Cons.prems(2)
    by (elim disjE; simp_all add: div_less_iff_less_mult; arith)
  show ?case using Cons.IH[OF rest outgoing] by simp
qed

lemma reflected_decimal_cells_run_high_bounded:
  assumes m: "multiplier = 2 \<or> multiplier = 5"
    and valid: "list_all (\<lambda>cell. cell < 100) source"
    and nonempty: "source \<noteq> []" and inlet: "carry < multiplier"
  shows "last (reflected_decimal_cells_run multiplier carry source) < 100"
proof -
  have bound: "list_all (\<lambda>cell. cell < 100)
      (reflected_decimal_cells_run multiplier carry source)"
    by (rule reflected_decimal_cells_run_bounded[OF m valid inlet])
  have nonempty_output: "reflected_decimal_cells_run multiplier carry source \<noteq> []"
    using nonempty by (cases source) simp_all
  show ?thesis using bound nonempty_output by (auto simp: list_all_iff)
qed

theorem reflected_slp_scaled_decimal_valid:
  assumes m: "multiplier = 2 \<or> multiplier = 5"
    and valid: "list_all (\<lambda>cell. cell < 100) (double_reverse_source_slp_word source)"
  shows "reflected_decimal (double_reverse_source_slp_word
      (reflected_slp_cell_digits (reflected_slp_scale_cells multiplier source)))"
proof -
  have inlet: "0 < multiplier" using m by auto
  have cells: "list_all (\<lambda>cell. cell < 100)
      (reflected_decimal_cells_run multiplier 0 (double_reverse_source_slp_word source))"
    by (rule reflected_decimal_cells_run_bounded[OF m valid inlet])
  have digits: "reflected_decimal (reflected_lsd_digits_of_cells
      (reflected_decimal_cells_run multiplier 0 (double_reverse_source_slp_word source)))"
    by (rule reflected_lsd_digits_of_cells_valid[OF cells])
  have reverse: "rev (double_reverse_source_slp_word
      (reflected_slp_cell_digits (reflected_slp_scale_cells multiplier source))) =
      reflected_lsd_digits_of_cells
        (reflected_decimal_cells_run multiplier 0 (double_reverse_source_slp_word source))"
    by (simp only: reflected_slp_scaled_decimal_exact[OF m valid] reflected_cell_digits_reverse)
  have "reflected_decimal (rev (double_reverse_source_slp_word
      (reflected_slp_cell_digits (reflected_slp_scale_cells multiplier source))))"
    using digits reverse by simp
  then show ?thesis by (simp add: list_all_iff)
qed

lemma reflected_positive_cell_msd_nonempty:
  fixes cell :: nat
  assumes "0 < cell" "cell < 100"
  shows "reflected_msd_drop_one_zero ([cell div 10, cell mod 10] @ tail) \<noteq> []"
  by (simp add: reflected_msd_drop_one_zero_def)

theorem reflected_slp_scaled_decimal_canonical:
  assumes m: "multiplier = 2 \<or> multiplier = 5"
    and valid: "list_all (\<lambda>cell. cell < 100) (double_reverse_source_slp_word source)"
    and nonempty: "double_reverse_source_slp_word source \<noteq> []"
    and high: "last (double_reverse_source_slp_word source) > 0"
  defines "result \<equiv> reflected_msd_drop_one_zero
      (double_reverse_source_slp_word
        (reflected_slp_cell_digits (reflected_slp_scale_cells multiplier source)))"
  shows "result \<noteq> [] \<and> hd result > 0"
proof -
  let ?cells = "reflected_decimal_cells_run multiplier 0 (double_reverse_source_slp_word source)"
  have inlet: "0 < multiplier" using m by auto
  have cells_nonempty: "?cells \<noteq> []" using nonempty by (cases "double_reverse_source_slp_word source") simp_all
  have positive: "last ?cells > 0"
    by (rule reflected_decimal_cells_run_high_positive[OF m valid nonempty high inlet])
  have bound: "last ?cells < 100"
    by (rule reflected_decimal_cells_run_high_bounded[OF m valid nonempty inlet])
  obtain cell tail where reversed: "rev ?cells = cell # tail"
    using cells_nonempty by (cases "rev ?cells") auto
  have head_reverse: "hd (rev ?cells) = last ?cells" by (rule hd_rev)
  have cell: "cell = last ?cells" using reversed head_reverse by simp
  have emitted: "result = reflected_msd_drop_one_zero
      ([cell div 10, cell mod 10] @ concat (map (\<lambda>c. [c div 10, c mod 10]) tail))"
    unfolding result_def reflected_slp_scaled_decimal_exact[OF m valid] reversed by simp
  show ?thesis using reflected_positive_cell_msd[of cell "concat (map (\<lambda>c. [c div 10, c mod 10]) tail)"]
      reflected_positive_cell_msd_nonempty[of cell "concat (map (\<lambda>c. [c div 10, c mod 10]) tail)"]
      positive bound cell emitted by simp
qed

(* General even endpoint from an MSD word, including leading or trailing zeros. *)
lemma reflected_decimal_reverse_any_msd:
  assumes decimal: "reflected_decimal msd"
  shows "decimal_reverse (decimal_lsd_value (rev msd)) =
    decimal_lsd_value (dropWhile ((=) 0) msd)"
proof -
  let ?trim = "dropWhile ((=) 0) msd"
  let ?canon = "rev ?trim"
  have canon: "reflected_trim_high (rev msd) = ?canon"
    by (simp add: reflected_trim_high_def)
  have valid: "reflected_decimal ?canon"
    using decimal by (auto simp: list_all_iff dest: set_dropWhileD)
  have canonical_value: "decimal_lsd_value ?canon = decimal_lsd_value (rev msd)"
    using reflected_trim_high_value[of "rev msd"] canon by simp
  show ?thesis
  proof (cases "?trim = []")
    case True
    have zero: "decimal_lsd_value (rev msd) = 0"
      using canonical_value by (simp only: True rev.simps(1) decimal_lsd_value.simps(1))
    have reverse_zero: "decimal_reverse 0 = 0" by simp
    show ?thesis by (simp only: True zero reverse_zero decimal_lsd_value.simps(1))
  next
    case False
    have first: "hd ?trim \<noteq> 0" using hd_dropWhile[OF False] by simp
    have nonempty: "?canon \<noteq> []" using False by simp
    have high: "last ?canon > 0" using first False by (cases ?trim) simp_all
    have "decimal_reverse (decimal_lsd_value ?canon) = decimal_lsd_value (rev ?canon)"
      by (rule decimal_reverse_lsd_value[OF valid nonempty high])
    then show ?thesis using canonical_value by (simp only: rev_rev_ident)
  qed
qed

corollary reflected_even_final_arbitrary_msd:
  assumes "reflected_decimal msd"
  shows "decimal_lsd_value (reflected_even_final_columns (dropWhile ((=) 0) msd)) =
    2 * decimal_reverse (decimal_lsd_value (rev msd))"
  using reflected_even_final_columns_value[of "dropWhile ((=) 0) msd"]
    reflected_decimal_reverse_any_msd[OF assms] by simp

ML \<open>
  val checked = @{thms reflected_slp_scale_cells_exact reflected_slp_scaled_decimal_exact
    reflected_decimal_cells_run_value reflected_slp_scaled_decimal_value
    reflected_slp_scaled_trimmed_decimal_value reflected_even_final_reverse_value};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Reflected SLP emission depends on an oracle";
  val _ = if Thm_Deps.has_skip_proof checked then error "Skipped reflected SLP emission" else ();
\<close>

end
