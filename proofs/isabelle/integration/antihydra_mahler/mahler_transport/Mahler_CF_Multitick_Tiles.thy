theory Mahler_CF_Multitick_Tiles
  imports Mahler_CF_Pow5_Source Mahler_Continued_Fraction_Refinement
    "Shared_Carry_Dynamics.Overlap_Quarter"
    "Shared_Carry_Dynamics.Reflected_Padded_Physical_Trim"
begin

text \<open>The decimal multiplication input is LSD first. For its MSD-first
tile presentation, each cell reads the current digit and its lower neighbor.
The explicit low and high zero halos are source data for every selected
physical position, including the leading carry digit.\<close>

definition mahler_cf_mul5_cell :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "mahler_cf_mul5_cell current low = (5 * current + low div 2) mod 10"

fun mahler_cf_local_columns :: "nat \<Rightarrow> nat list \<Rightarrow> nat list" where
  "mahler_cf_local_columns previous [] = []"
| "mahler_cf_local_columns previous (digit # rest) =
    mahler_cf_mul5_cell digit previous # mahler_cf_local_columns digit rest"

lemma mahler_cf_local_columns_exact:
  assumes decimal: "list_all (\<lambda>digit. digit < 10) digits" and prev: "previous < 10"
  shows "decimal_block_run 5 digits (previous div 2) =
    (mahler_cf_local_columns previous digits,
      (if digits = [] then previous div 2 else last digits div 2))"
  using decimal prev
proof (induction digits arbitrary: previous)
  case Nil
  then show ?case by simp
next
  case (Cons digit rest)
  have digit: "digit < 10" and rest: "list_all (\<lambda>d. d < 10) rest"
    using Cons.prems by auto
  have carry: "(5 * digit + previous div 2) div 10 = digit div 2"
    by (rule mahler_cf_digit_carry[OF digit]) (use Cons.prems in auto)
  have tail: "decimal_block_run 5 rest (digit div 2) =
      (mahler_cf_local_columns digit rest,
       (if rest = [] then digit div 2 else last rest div 2))"
    by (rule Cons.IH[OF rest digit])
  show ?case using carry tail
    by (simp add: mahler_cf_mul5_cell_def Let_def split: if_splits)
qed

definition mahler_cf_full_step :: "nat list \<Rightarrow> nat list" where
  "mahler_cf_full_step digits = mahler_cf_local_columns 0 digits @
    [(if digits = [] then 0 else last digits div 2) mod 10]"

theorem mahler_cf_full_step_exact:
  assumes "list_all (\<lambda>digit. digit < 10) digits"
  shows "reflected_trim_high (mahler_cf_full_step digits) =
    reflected_trim_high (mahler_cf_mul5_word digits)"
proof -
  have carry_bound: "(if digits = [] then 0 else last digits div 2) < 10"
  proof (cases "digits = []")
    case True
    then show ?thesis by simp
  next
    case False
    have digit: "last digits < 10"
      using assms last_in_set[OF False] by (simp add: list_all_iff)
    then show ?thesis using False by simp
  qed
  show ?thesis
    using mahler_cf_local_columns_exact[OF assms, of 0] carry_bound
    by (simp add: mahler_cf_full_step_def mahler_cf_mul5_word_def
        reflected_trim_high_def Let_def split: if_splits)
qed

lemma mahler_cf_cell_is_decimal:
  "mahler_cf_mul5_cell current low < 10"
  by (simp add: mahler_cf_mul5_cell_def)

theorem mahler_cf_cell_tile:
  "overlap_recursive k mahler_cf_mul5_cell source i =
    overlap_run mahler_cf_mul5_cell (2^k) source i"
  by (rule overlap_recursive_exact)

theorem mahler_cf_cell_complete_halo:
  assumes "\<And>j. i \<le> j \<Longrightarrow> j \<le> i + 2^k \<Longrightarrow> left j = right j"
  shows "overlap_recursive k mahler_cf_mul5_cell left i =
    overlap_recursive k mahler_cf_mul5_cell right i"
  using overlap_run_local[OF assms]
  by (simp only: mahler_cf_cell_tile)

theorem mahler_cf_cell_chronology:
  "overlap_run mahler_cf_mul5_cell (a+b) source i =
    overlap_run mahler_cf_mul5_cell b
      (\<lambda>j. overlap_run mahler_cf_mul5_cell a source j) i"
  by (rule overlap_run_add)

fun mahler_cf_adjacent :: "nat list \<Rightarrow> nat list" where
  "mahler_cf_adjacent [] = []"
| "mahler_cf_adjacent [a] = []"
| "mahler_cf_adjacent (a # b # rest) =
    mahler_cf_mul5_cell b a # mahler_cf_adjacent (b # rest)"

lemma mahler_cf_adjacent_columns:
  "mahler_cf_adjacent (previous # digits @ [0]) =
    mahler_cf_local_columns previous digits @
      [(if digits = [] then previous div 2 else last digits div 2) mod 10]"
  by (induction digits arbitrary: previous)
    (auto simp: mahler_cf_mul5_cell_def split: list.splits)

lemma mahler_cf_adjacent_zeros:
  "mahler_cf_adjacent (replicate (Suc k) 0) = replicate k 0"
  by (induction k) (auto simp: mahler_cf_mul5_cell_def)

lemma mahler_cf_adjacent_leading_zeros [simp]:
  "mahler_cf_adjacent (0 # replicate k 0) = replicate k 0"
  using mahler_cf_adjacent_zeros[of k] by (simp only: replicate.simps)

lemma mahler_cf_adjacent_high_zeros:
  "mahler_cf_adjacent (digits @ replicate (Suc k) 0) =
    mahler_cf_adjacent (digits @ [0]) @ replicate k 0"
  by (induction digits rule: mahler_cf_adjacent.induct)
    (auto simp: mahler_cf_adjacent_zeros)

lemma mahler_cf_adjacent_low_zeros:
  "mahler_cf_adjacent (replicate (Suc k) 0 @ digits) =
    replicate k 0 @ mahler_cf_adjacent (0 # digits)"
  by (induction k) (auto simp: mahler_cf_mul5_cell_def split: list.splits)

lemma mahler_cf_adjacent_padding:
  "mahler_cf_adjacent (replicate (Suc k) 0 @ digits @ replicate (Suc k) 0) =
    replicate k 0 @ mahler_cf_full_step digits @ replicate k 0"
  using mahler_cf_adjacent_low_zeros[of k "digits @ replicate (Suc k) 0"]
    mahler_cf_adjacent_high_zeros[of "0 # digits" k]
    mahler_cf_adjacent_columns[of 0 digits]
  by (simp add: mahler_cf_full_step_def append_assoc)


fun mahler_cf_adjacent_iter :: "nat \<Rightarrow> nat list \<Rightarrow> nat list" where
  "mahler_cf_adjacent_iter 0 digits = digits"
| "mahler_cf_adjacent_iter (Suc n) digits =
    mahler_cf_adjacent_iter n (mahler_cf_adjacent digits)"

fun mahler_cf_full_steps :: "nat \<Rightarrow> nat list \<Rightarrow> nat list" where
  "mahler_cf_full_steps 0 digits = digits"
| "mahler_cf_full_steps (Suc n) digits =
    mahler_cf_full_steps n (mahler_cf_full_step digits)"

theorem mahler_cf_padded_multitick:
  "mahler_cf_adjacent_iter steps
      (replicate steps 0 @ digits @ replicate steps 0) =
    mahler_cf_full_steps steps digits"
proof (induction steps arbitrary: digits)
  case 0
  then show ?case by simp
next
  case (Suc steps)
  have initial:
    "mahler_cf_adjacent (replicate (Suc steps) 0 @ digits @ replicate (Suc steps) 0) =
      replicate steps 0 @ mahler_cf_full_step digits @ replicate steps 0"
    by (rule mahler_cf_adjacent_padding)
  show ?case
    using Suc.IH[of "mahler_cf_full_step digits"] initial
    by (simp only: mahler_cf_adjacent_iter.simps mahler_cf_full_steps.simps)
qed

lemma mahler_cf_full_step_value:
  assumes "list_all (\<lambda>digit. digit < 10) digits"
  shows "decimal_lsd_value (mahler_cf_full_step digits) = 5 * decimal_lsd_value digits"
  using mahler_cf_full_step_exact[OF assms] reflected_trim_high_value
    mahler_cf_mul5_word_value by metis

lemma mahler_cf_local_columns_digits:
  "list_all (\<lambda>digit. digit < 10) (mahler_cf_local_columns previous digits)"
  by (induction digits arbitrary: previous)
    (auto simp: mahler_cf_cell_is_decimal)

lemma mahler_cf_full_step_digits:
  assumes "list_all (\<lambda>digit. digit < 10) digits"
  shows "list_all (\<lambda>digit. digit < 10) (mahler_cf_full_step digits)"
proof (cases "digits = []")
  case True
  then show ?thesis by (simp add: mahler_cf_full_step_def)
next
  case False
  have "last digits < 10"
    using assms last_in_set[OF False] by (simp add: list_all_iff)
  then show ?thesis
    using mahler_cf_local_columns_digits[of 0 digits]
    by (simp add: mahler_cf_full_step_def False)
qed

theorem mahler_cf_multitick_source_value:
  assumes decimal: "list_all (\<lambda>digit. digit < 10) source"
  shows "decimal_lsd_value (mahler_cf_full_steps ticks source) =
    5^ticks * decimal_lsd_value source"
  using decimal
  by (induction ticks arbitrary: source)
    (auto simp: mahler_cf_full_step_value mahler_cf_full_step_digits
      power_Suc algebra_simps)

theorem mahler_cf_multitick_pow5_publisher:
  "decimal_lsd_value
      (reflected_trim_high (mahler_cf_adjacent_iter ticks
        (replicate ticks 0 @ mahler_cf_pow5_word n @ replicate ticks 0))) =
    5^(n+ticks)"
  using mahler_cf_multitick_source_value[OF mahler_cf_pow5_word_consumer(2), of ticks n]
  by (simp only: reflected_trim_high_value mahler_cf_padded_multitick
      mahler_cf_pow5_word_consumer power_add mult.commute)

lemma mahler_cf_adjacent_length:
  "length (mahler_cf_adjacent digits) = length digits - 1"
  by (induction digits rule: mahler_cf_adjacent.induct) simp_all

lemma mahler_cf_adjacent_nth:
  assumes "Suc i < length digits"
  shows "mahler_cf_adjacent digits ! i =
    mahler_cf_mul5_cell (digits ! Suc i) (digits ! i)"
  using assms
proof (induction digits arbitrary: i rule: mahler_cf_adjacent.induct)
  case 1
  then show ?case by simp
next
  case (2 a)
  then show ?case by simp
next
  case (3 a b rest)
  then show ?case by (cases i) auto
qed

lemma mahler_cf_adjacent_iter_length:
  "length (mahler_cf_adjacent_iter ticks digits) = length digits - ticks"
  by (induction ticks arbitrary: digits)
    (simp_all add: mahler_cf_adjacent_length)

lemma mahler_cf_adjacent_reverse_nth:
  assumes "i < length digits - 1"
  shows "rev (mahler_cf_adjacent digits) ! i =
    mahler_cf_mul5_cell (rev digits ! i) (rev digits ! Suc i)"
proof -
  have bound: "Suc (length digits - 2 - i) < length digits"
    using assms by arith
  have a: "i < length (mahler_cf_adjacent digits)"
    using assms by (simp add: mahler_cf_adjacent_length)
  have b: "i < length digits" "Suc i < length digits" using assms by arith+
  have one: "length (mahler_cf_adjacent digits) - Suc i = length digits - 2 - i"
    using assms by (simp only: mahler_cf_adjacent_length; arith)
  have two: "length digits - Suc i = Suc (length digits - 2 - i)"
    using assms by arith
  have three: "length digits - Suc (Suc i) = length digits - 2 - i"
    using assms by arith
  show ?thesis
    using mahler_cf_adjacent_nth[OF bound]
    by (simp only: rev_nth[OF a] rev_nth[OF b(1)] rev_nth[OF b(2)] one two three)
qed

theorem mahler_cf_overlap_matches_padded_word:
  assumes "ticks < length digits"
  shows "rev (mahler_cf_adjacent_iter ticks digits) =
    map (overlap_run mahler_cf_mul5_cell ticks ((!) (rev digits)))
      [0..<length digits - ticks]"
  using assms
proof (induction ticks arbitrary: digits)
  case 0
  then show ?case using map_nth[of "rev digits"] by simp
next
  case (Suc ticks)
  let ?next = "mahler_cf_adjacent digits"
  have next_bound: "ticks < length ?next"
    using Suc.prems by (simp add: mahler_cf_adjacent_length)
  have nested: "rev (mahler_cf_adjacent_iter ticks ?next) =
      map (overlap_run mahler_cf_mul5_cell ticks ((!) (rev ?next)))
        [0..<length ?next - ticks]"
    by (rule Suc.IH[OF next_bound])
  have local_eq: "overlap_run mahler_cf_mul5_cell ticks ((!) (rev ?next)) i =
      overlap_run mahler_cf_mul5_cell ticks
        (\<lambda>j. overlap_run mahler_cf_mul5_cell 1 ((!) (rev digits)) j) i"
    if "i < length digits - Suc ticks" for i
  proof (rule overlap_run_local)
    fix j assume "i \<le> j" "j \<le> i + ticks"
    then have bound: "j < length digits - 1" using that by arith
    show "rev ?next ! j = overlap_run mahler_cf_mul5_cell 1 ((!) (rev digits)) j"
      using mahler_cf_adjacent_reverse_nth[OF bound] by simp
  qed
  have runs: "overlap_run mahler_cf_mul5_cell ticks
        (\<lambda>j. overlap_run mahler_cf_mul5_cell 1 ((!) (rev digits)) j) i =
      overlap_run mahler_cf_mul5_cell (Suc ticks) ((!) (rev digits)) i" for i
    using overlap_run_add[of mahler_cf_mul5_cell 1 ticks "(!) (rev digits)" i]
    by simp
  have same_map:
    "map (overlap_run mahler_cf_mul5_cell ticks ((!) (rev ?next)))
        [0..<length digits - Suc ticks] =
      map (overlap_run mahler_cf_mul5_cell (Suc ticks) ((!) (rev digits)))
        [0..<length digits - Suc ticks]"
  proof (rule map_cong[OF refl])
    fix i
    assume "i \<in> set [0..<length digits - Suc ticks]"
    then have bound: "i < length digits - Suc ticks" by simp
    show "overlap_run mahler_cf_mul5_cell ticks ((!) (rev ?next)) i =
      overlap_run mahler_cf_mul5_cell (Suc ticks) ((!) (rev digits)) i"
      using local_eq[OF bound] runs[of i] by simp
  qed
  have lengths: "length ?next - ticks = length digits - Suc ticks"
    by (simp add: mahler_cf_adjacent_length)
  show ?case using nested same_map
    by (simp only: mahler_cf_adjacent_iter.simps lengths)
qed

theorem mahler_cf_temporal_tile_selected_output:
  fixes input :: "nat list" and n ticks :: nat
  assumes ticks: "0 < ticks"
  defines "input \<equiv> replicate ticks 0 @ mahler_cf_pow5_word n @ replicate ticks 0"
  shows "rev (mahler_cf_full_steps ticks (mahler_cf_pow5_word n)) =
    map (overlap_run mahler_cf_mul5_cell ticks ((!) (rev input)))
      [0..<length input - ticks]"
proof -
  have bounded: "ticks < length input"
    using ticks by (simp add: input_def)
  show ?thesis
    using mahler_cf_overlap_matches_padded_word[OF bounded]
    by (simp only: input_def mahler_cf_padded_multitick)
qed

theorem mahler_cf_temporal_tile_ordered_consumer:
  fixes input msd :: "nat list" and n ticks :: nat
  assumes ticks: "0 < ticks"
  defines "input \<equiv> replicate ticks 0 @ mahler_cf_pow5_word n @ replicate ticks 0"
    and "msd \<equiv> dropWhile ((=) 0)
      (map (overlap_run mahler_cf_mul5_cell ticks ((!) (rev input)))
        [0..<length input - ticks])"
  shows "mahler_cf_word (take width (drop start msd)) =
    mahler_cf_word (take width
      (drop start
        (rev (reflected_trim_high
          (mahler_cf_full_steps ticks (mahler_cf_pow5_word n))))))"
  using mahler_cf_temporal_tile_selected_output[OF ticks, of n]
  by (simp only: input_def msd_def reflected_reverse_trim_high)

lemma mahler_cf_full_step_as_adjacent:
  "mahler_cf_full_step digits = mahler_cf_adjacent (0 # digits @ [0])"
  using mahler_cf_adjacent_columns[of 0 digits]
  by (simp add: mahler_cf_full_step_def)

lemma mahler_cf_full_step_append_zeros:
  "mahler_cf_full_step (digits @ replicate z 0) =
    mahler_cf_full_step digits @ replicate z 0"
proof -
  have high:
    "mahler_cf_adjacent ((0 # digits) @ replicate (Suc z) 0) =
      mahler_cf_adjacent ((0 # digits) @ [0]) @ replicate z 0"
    by (rule mahler_cf_adjacent_high_zeros)
  have zeros: "replicate z (0::nat) @ [0] = replicate (Suc z) 0"
    by (simp add: replicate_append_same)
  show ?thesis using high
    by (simp only: mahler_cf_full_step_as_adjacent append_assoc zeros append_Cons)
qed

lemma mahler_cf_full_step_source_suffix:
  assumes "list_all (\<lambda>d. d < 10) digits"
  shows "\<exists>z\<le>1. mahler_cf_full_step digits = mahler_cf_mul5_word digits @ replicate z 0"
proof -
  obtain emitted carry where run: "decimal_block_run 5 digits 0 = (emitted, carry)"
    by (cases "decimal_block_run 5 digits 0") auto
  have bound: "carry < 10"
    using reflected_digit_pass_carry_bound[of 5 digits 0] assms run by simp
  have exact:
    "mahler_cf_full_step digits = emitted @ [carry]"
    using mahler_cf_local_columns_exact[OF assms, of 0] run bound
    by (auto simp: mahler_cf_full_step_def)
  show ?thesis using exact run bound
    by (cases "carry = 0")
      (auto simp: mahler_cf_mul5_word_def Let_def intro!: exI[of _ 0] exI[of _ 1])
qed

theorem mahler_cf_full_steps_pow5_padding:
  "\<exists>z. mahler_cf_full_steps ticks (mahler_cf_pow5_word n @ replicate padding 0) =
    mahler_cf_pow5_word (n+ticks) @ replicate z 0"
proof (induction ticks arbitrary: n padding)
  case 0
  then show ?case by simp
next
  case (Suc ticks)
  have decimal: "list_all (\<lambda>d. d < 10) (mahler_cf_pow5_word n)"
    by (rule mahler_cf_pow5_word_consumer)
  obtain z where next_step:
    "mahler_cf_full_step (mahler_cf_pow5_word n) =
      mahler_cf_pow5_word (Suc n) @ replicate z 0"
    using mahler_cf_full_step_source_suffix[OF decimal] by auto
  have first:
    "mahler_cf_full_step (mahler_cf_pow5_word n @ replicate padding 0) =
      mahler_cf_pow5_word (Suc n) @ replicate (z+padding) 0"
    using next_step by (simp add: mahler_cf_full_step_append_zeros replicate_add append_assoc)
  show ?case using Suc.IH[of "Suc n" "z+padding"]
    by (simp only: mahler_cf_full_steps.simps first add_Suc_right add_Suc_shift)
qed

lemma mahler_cf_trim_high_zeros:
  "reflected_trim_high (digits @ replicate z 0) = reflected_trim_high digits"
proof -
  have discard: "dropWhile ((=) (0::nat)) (replicate z 0 @ xs) =
      dropWhile ((=) 0) xs" for xs
    by (induction z) simp_all
  show ?thesis by (simp add: reflected_trim_high_def discard)
qed

theorem mahler_cf_full_steps_pow5_exact_word:
  "reflected_trim_high (mahler_cf_full_steps ticks (mahler_cf_pow5_word n)) =
    reflected_trim_high (mahler_cf_pow5_word (n+ticks))"
proof -
  obtain z where "mahler_cf_full_steps ticks (mahler_cf_pow5_word n) =
      mahler_cf_pow5_word (n+ticks) @ replicate z 0"
    using mahler_cf_full_steps_pow5_padding[of ticks n 0] by auto
  then show ?thesis by (simp only: mahler_cf_trim_high_zeros)
qed

theorem mahler_cf_dyadic_tile_ordered_consumer:
  fixes ticks k n :: nat and input :: "nat list"
  defines "ticks \<equiv> 2^k"
    and "input \<equiv> replicate ticks 0 @ mahler_cf_pow5_word n @ replicate ticks 0"
  shows "mahler_cf_word
      (take width (drop start (dropWhile ((=) 0)
        (map (overlap_recursive k mahler_cf_mul5_cell ((!) (rev input)))
          [0..<length input - ticks])))) =
    mahler_cf_word (take width (drop start
      (rev (reflected_trim_high (mahler_cf_full_steps ticks (mahler_cf_pow5_word n))))))"
proof -
  have positive: "0 < ticks" by (simp add: ticks_def)
  have selected:
    "mahler_cf_word (take width (drop start (dropWhile ((=) 0)
      (map (overlap_run mahler_cf_mul5_cell ticks ((!) (rev input)))
        [0..<length input - ticks])))) =
     mahler_cf_word (take width (drop start
       (rev (reflected_trim_high (mahler_cf_full_steps ticks (mahler_cf_pow5_word n))))))"
    using mahler_cf_temporal_tile_ordered_consumer[
      where ticks=ticks and n=n, OF positive]
    by (simp only: input_def)
  have same_action:
    "overlap_recursive k mahler_cf_mul5_cell ((!) (rev input)) =
      overlap_run mahler_cf_mul5_cell (2^k) ((!) (rev input))"
    by (rule ext) (rule mahler_cf_cell_tile)
  show ?thesis using selected
    by (simp only: same_action ticks_def)
qed

theorem mahler_cf_dyadic_physical_consumer:
  fixes input :: "nat list" and k n :: nat
  defines "input \<equiv> replicate (2^k) 0 @ mahler_cf_pow5_word n @ replicate (2^k) 0"
  shows "mahler_cf_word
      (take width (drop start (dropWhile ((=) 0)
        (map (overlap_recursive k mahler_cf_mul5_cell ((!) (rev input)))
          [0..<length input - 2^k])))) =
    mahler_cf_word (take width (drop start
      (rev (reflected_trim_high (mahler_cf_pow5_word (n+2^k))))))"
  using mahler_cf_dyadic_tile_ordered_consumer[where k=k and n=n]
    mahler_cf_full_steps_pow5_exact_word[of "2^k" n]
  by (simp only: input_def)

ML \<open>
  val checked = @{thms mahler_cf_local_columns_exact mahler_cf_full_step_exact
    mahler_cf_cell_is_decimal mahler_cf_cell_tile mahler_cf_cell_complete_halo
    mahler_cf_cell_chronology mahler_cf_padded_multitick
    mahler_cf_multitick_pow5_publisher mahler_cf_overlap_matches_padded_word
    mahler_cf_temporal_tile_selected_output mahler_cf_temporal_tile_ordered_consumer
    mahler_cf_dyadic_tile_ordered_consumer mahler_cf_full_steps_pow5_exact_word
    mahler_cf_dyadic_physical_consumer};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Mahler ×5 temporal tile depends on an oracle";
  val _ = if Thm_Deps.has_skip_proof checked
    then error "Skipped Mahler ×5 temporal tile proof" else ();
\<close>

end
