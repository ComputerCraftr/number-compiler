theory Reverse_Punctured_Run_Pairing
  imports Reverse_Punctured_T2_Coefficients
begin

text \<open>The production output owner pairs opposite ends of a run-compressed
decimal word. It advances two run cursors by the minimum of their remaining
run lengths and the remaining half-width. This theory refines that compact
zipper to the first half of the literal reflected pair-sum word. It does not
prove the separate temporal event partition or unrestricted T2 closure.\<close>

type_synonym punctured_runs = "(nat \<times> nat) list"

definition punctured_pair_sum :: "nat \<times> nat \<Rightarrow> nat" where
  "punctured_pair_sum pair = fst pair + snd pair"

definition punctured_positive_runs :: "punctured_runs \<Rightarrow> bool" where
  "punctured_positive_runs runs \<longleftrightarrow>
    (\<forall>run\<in>set runs. 0 < snd run)"

definition punctured_run_width :: "punctured_runs \<Rightarrow> nat" where
  "punctured_run_width runs = sum_list (map snd runs)"

fun punctured_push_reversed ::
  "punctured_runs \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> punctured_runs" where
  "punctured_push_reversed [] symbol count = [(symbol,count)]"
| "punctured_push_reversed ((head_symbol,head_count)#tail) symbol count =
    (if head_symbol = symbol
     then (symbol, head_count + count)#tail
     else (symbol,count)#(head_symbol,head_count)#tail)"

fun punctured_coalesce_aux ::
  "punctured_runs \<Rightarrow> punctured_runs \<Rightarrow> punctured_runs" where
  "punctured_coalesce_aux [] reversed = rev reversed"
| "punctured_coalesce_aux ((symbol,count)#runs) reversed =
    punctured_coalesce_aux runs
      (punctured_push_reversed reversed symbol count)"

definition punctured_coalesce :: "punctured_runs \<Rightarrow> punctured_runs" where
  "punctured_coalesce runs = punctured_coalesce_aux runs []"

fun punctured_run_advance ::
  "nat \<Rightarrow> punctured_runs \<Rightarrow> punctured_runs" where
  "punctured_run_advance 0 runs = runs"
| "punctured_run_advance (Suc amount) [] = []"
| "punctured_run_advance (Suc amount) ((symbol,count)#runs) =
    (if Suc amount < count
     then (symbol, count - Suc amount)#runs
     else runs)"

function punctured_run_zip ::
  "punctured_runs \<Rightarrow> punctured_runs \<Rightarrow> nat \<Rightarrow> punctured_runs" where
  "punctured_run_zip left right 0 = []"
| "punctured_run_zip [] right (Suc remaining) = []"
| "punctured_run_zip (left_head#left_tail) [] (Suc remaining) = []"
| "punctured_run_zip ((left_symbol,left_count)#left_tail)
      ((right_symbol,right_count)#right_tail) (Suc remaining) =
    (if left_count = 0 \<or> right_count = 0 then [] else
      (let amount = min (Suc remaining) (min left_count right_count)
       in (left_symbol + right_symbol, amount) #
          punctured_run_zip
            (punctured_run_advance amount
              ((left_symbol,left_count)#left_tail))
            (punctured_run_advance amount
              ((right_symbol,right_count)#right_tail))
            (Suc remaining - amount)))"
  by pat_completeness auto
termination
proof (relation "measure (\<lambda>(left,right,remaining). remaining)")
  show "wf (measure (\<lambda>(left,right,remaining). remaining))"
    by simp
next
  fix left_symbol left_count left_tail right_symbol right_count right_tail
    remaining amount
  assume nonzero: "\<not> (left_count = 0 \<or> right_count = 0)"
    and selected:
      "amount = min (Suc remaining) (min left_count right_count)"
  have left_count_positive: "0 < left_count" using nonzero by simp
  have right_count_positive: "0 < right_count" using nonzero by simp
  have amount_positive: "0 < amount"
    using left_count_positive right_count_positive selected
    by (simp add: min_def)
  show "((punctured_run_advance amount
        ((left_symbol,left_count)#left_tail),
      punctured_run_advance amount
        ((right_symbol,right_count)#right_tail),
      Suc remaining - amount),
      ((left_symbol,left_count)#left_tail,
       (right_symbol,right_count)#right_tail, Suc remaining))
      \<in> measure (\<lambda>(left,right,remaining). remaining)"
    using amount_positive by (simp; arith)
qed

definition punctured_pair_mirror_half :: "punctured_runs \<Rightarrow> punctured_runs" where
  "punctured_pair_mirror_half runs = punctured_coalesce
    (punctured_run_zip runs (rev runs)
      ((punctured_run_width runs + 1) div 2))"

definition punctured_decimal_runs :: "punctured_runs \<Rightarrow> punctured_runs" where
  "punctured_decimal_runs runs =
    punctured_emit_compact_runs False runs @
      (if punctured_runs_exit False runs then [(1,1)] else [])"

lemma punctured_run_emit_compact_positive:
  "punctured_positive_runs
      (punctured_run_emit_compact incoming symbol count)"
proof (cases count)
  case 0
  then show ?thesis
    by (simp add: punctured_run_emit_compact_def punctured_positive_runs_def)
next
  case (Suc n)
  then show ?thesis
  proof (cases n)
    case 0
    then show ?thesis using Suc
      by (simp add: punctured_run_emit_compact_def punctured_positive_runs_def)
  next
    case (Suc m)
    then show ?thesis using Suc
      by (simp add: punctured_run_emit_compact_def punctured_positive_runs_def)
  qed
qed

lemma punctured_emit_compact_runs_positive:
  "punctured_positive_runs (punctured_emit_compact_runs incoming runs)"
proof (induction runs arbitrary: incoming)
  case Nil
  then show ?case by (simp add: punctured_positive_runs_def)
next
  case (Cons run runs)
  obtain symbol count where run: "run = (symbol,count)"
    by (cases run) auto
  have head_positive:
    "punctured_positive_runs
       (punctured_run_emit_compact incoming symbol count)"
    by (rule punctured_run_emit_compact_positive)
  have tail_positive:
    "punctured_positive_runs
       (punctured_emit_compact_runs
          (if count = 0 then incoming else punctured_run_exit symbol incoming)
          runs)"
    by (rule Cons.IH)
  have joined_positive:
    "punctured_positive_runs
      (punctured_run_emit_compact incoming symbol count @
        punctured_emit_compact_runs
          (if count = 0 then incoming else punctured_run_exit symbol incoming)
          runs)"
    using head_positive tail_positive
    by (auto simp: punctured_positive_runs_def)
  have equation:
    "punctured_emit_compact_runs incoming ((symbol,count)#runs) =
      punctured_run_emit_compact incoming symbol count @
        punctured_emit_compact_runs
          (if count = 0 then incoming else punctured_run_exit symbol incoming)
          runs"
    by simp
  show ?case using joined_positive equation run by simp
qed

lemma punctured_decimal_runs_positive:
  "punctured_positive_runs (punctured_decimal_runs runs)"
  using punctured_emit_compact_runs_positive[of False runs]
  by (auto simp: punctured_decimal_runs_def punctured_positive_runs_def)

lemma punctured_decimal_runs_expansion:
  assumes valid: "\<forall>run\<in>set runs. fst run < 19"
  shows "punctured_expand_runs (punctured_decimal_runs runs) =
    digits (punctured_expand_runs runs)"
proof -
  have normalized:
    "punctured_expand_runs (punctured_emit_compact_runs False runs) @
        (if punctured_runs_exit False runs then [1] else []) =
      digits (punctured_expand_runs runs)"
    by (rule punctured_compact_run_decimal_normalization[OF valid])
  show ?thesis
  proof (cases "punctured_runs_exit False runs")
    case True
    then show ?thesis using normalized
      by (simp add: punctured_decimal_runs_def punctured_expand_runs_append)
  next
    case False
    then show ?thesis using normalized
      by (simp add: punctured_decimal_runs_def punctured_expand_runs_append)
  qed
qed

lemma punctured_run_width_exact:
  "punctured_run_width runs = length (punctured_expand_runs runs)"
proof (induction runs)
  case Nil
  then show ?case by (simp add: punctured_run_width_def)
next
  case (Cons pair runs)
  obtain symbol count where pair: "pair = (symbol,count)"
    by (cases pair) auto
  show ?case using Cons.IH pair
    by (simp add: punctured_run_width_def)
qed

lemma punctured_push_reversed_expansion:
  "punctured_expand_runs (rev (punctured_push_reversed reversed symbol count)) =
    punctured_expand_runs (rev reversed) @ replicate count symbol"
proof (induction reversed)
  case Nil
  then show ?case by simp
next
  case (Cons pair reversed)
  obtain head_symbol head_count where pair: "pair = (head_symbol,head_count)"
    by (cases pair) auto
  show ?case using Cons.IH pair
    by (auto split: if_splits
        simp: punctured_push_reversed.simps punctured_expand_runs_append
          replicate_add)
qed

lemma punctured_coalesce_aux_expansion:
  "punctured_expand_runs (punctured_coalesce_aux runs reversed) =
    punctured_expand_runs (rev reversed) @ punctured_expand_runs runs"
proof (induction runs arbitrary: reversed)
  case Nil
  then show ?case by simp
next
  case (Cons pair runs)
  obtain symbol count where pair: "pair = (symbol,count)"
    by (cases pair) auto
  have recursive:
    "punctured_expand_runs
       (punctured_coalesce_aux runs
          (punctured_push_reversed reversed symbol count)) =
     punctured_expand_runs
       (rev (punctured_push_reversed reversed symbol count)) @
       punctured_expand_runs runs"
    by (rule Cons.IH)
  have pushed:
    "punctured_expand_runs
       (rev (punctured_push_reversed reversed symbol count)) =
     punctured_expand_runs (rev reversed) @ replicate count symbol"
    by (rule punctured_push_reversed_expansion)
  show ?case using recursive pushed pair
    by (simp add: punctured_expand_runs_append)
qed

lemma punctured_coalesce_expansion:
  "punctured_expand_runs (punctured_coalesce runs) = punctured_expand_runs runs"
  by (simp add: punctured_coalesce_def punctured_coalesce_aux_expansion)

lemma punctured_advance_cons:
  assumes positive: "0 < count" and bound: "amount \<le> count"
  shows "punctured_run_advance amount ((symbol,count)#runs) =
    (if amount < count then (symbol,count - amount)#runs else runs)"
  using bound positive
  by (cases amount; cases count; simp_all; arith)

lemma punctured_advance_expansion:
  assumes positive: "0 < count" and bound: "amount \<le> count"
  shows "punctured_expand_runs (punctured_run_advance amount
      ((symbol,count)#runs)) =
    drop amount (replicate count symbol @ punctured_expand_runs runs)"
  using positive bound
  by (subst punctured_advance_cons[OF positive bound])
     (auto simp: punctured_expand_runs_append)

lemma punctured_advance_positive:
  assumes all_positive: "punctured_positive_runs ((symbol,count)#runs)"
      and bound: "amount \<le> count"
  shows "punctured_positive_runs
      (punctured_run_advance amount ((symbol,count)#runs))"
  using all_positive bound
  by (auto simp: punctured_positive_runs_def
      punctured_advance_cons split: if_splits)

lemma punctured_zip_drop:
  assumes left_bound: "amount \<le> length left"
      and right_bound: "amount \<le> length right"
  shows "zip (drop amount left) (drop amount right) =
    drop amount (zip left right)"
  using left_bound right_bound
proof (induction amount arbitrary: left right)
  case 0
  then show ?case by simp
next
  case (Suc amount)
  then obtain left_head left_tail where left: "left = left_head#left_tail"
    by (cases left) auto
  obtain right_head right_tail where right: "right = right_head#right_tail"
    using Suc.prems by (cases right) auto
  have left_tail_bound: "amount \<le> length left_tail"
    using Suc.prems left by simp
  have right_tail_bound: "amount \<le> length right_tail"
    using Suc.prems right by simp
  show ?case using Suc.IH[OF left_tail_bound right_tail_bound] left right
    by simp
qed

lemma punctured_take_split:
  assumes bound: "prefix \<le> extent"
  shows "take extent word = take prefix word @
    take (extent - prefix) (drop prefix word)"
proof -
  have decomposition: "extent = prefix + (extent - prefix)"
    using bound by arith
  have take_argument:
    "take extent word = take (prefix + (extent - prefix)) word"
    using decomposition by (rule arg_cong)
  have take_sum:
    "take (prefix + (extent - prefix)) word =
      take prefix word @ take (extent - prefix) (drop prefix word)"
    by (rule take_add)
  show ?thesis by (rule trans[OF take_argument take_sum])
qed

lemma punctured_take_zip_replicates:
  assumes left_bound: "prefix \<le> left_count"
      and right_bound: "prefix \<le> right_count"
  shows "take prefix
      (map punctured_pair_sum
        (zip (replicate left_count left_symbol @ left_tail)
             (replicate right_count right_symbol @ right_tail))) =
    replicate prefix (left_symbol + right_symbol)"
  using left_bound right_bound
proof (induction prefix arbitrary: left_count right_count left_tail right_tail)
  case 0
  then show ?case by simp
next
  case (Suc prefix)
  then obtain left_rest where left_count: "left_count = Suc left_rest"
    by (cases left_count) auto
  obtain right_rest where right_count: "right_count = Suc right_rest"
    using Suc.prems by (cases right_count) auto
  have left_rest_bound: "prefix \<le> left_rest"
    using Suc.prems left_count by simp
  have right_rest_bound: "prefix \<le> right_rest"
    using Suc.prems right_count by simp
  show ?case using Suc.IH[OF left_rest_bound right_rest_bound]
      left_count right_count
    by (simp add: punctured_pair_sum_def)
qed

lemma punctured_run_zip_expansion:
  assumes left_positive: "punctured_positive_runs left"
      and right_positive: "punctured_positive_runs right"
  shows "punctured_expand_runs (punctured_run_zip left right amount) =
    take amount (map punctured_pair_sum
      (zip (punctured_expand_runs left) (punctured_expand_runs right)))"
  using left_positive right_positive
proof (induction amount arbitrary: left right rule: less_induct)
  case (less amount)
  show ?case
  proof (cases amount)
    case 0
    then show ?thesis by simp
  next
    case (Suc remaining)
    show ?thesis
    proof (cases left)
      case Nil
      note left_empty = Nil
      show ?thesis using Suc left_empty by simp
    next
      case (Cons left_run left_tail)
      note left_case = Cons
      obtain left_symbol left_count where left_run:
        "left_run = (left_symbol,left_count)"
        by (cases left_run) auto
      show ?thesis
      proof (cases right)
        case Nil
        note right_empty = Nil
        show ?thesis using Suc left_case right_empty by simp
      next
        case (Cons right_run right_tail)
        note right_case = Cons
        obtain right_symbol right_count where right_run:
          "right_run = (right_symbol,right_count)"
          by (cases right_run) auto
        have left_current_positive:
          "punctured_positive_runs ((left_symbol,left_count)#left_tail)"
          using less.prems left_case left_run
          by (simp add: punctured_positive_runs_def)
        have right_current_positive:
          "punctured_positive_runs ((right_symbol,right_count)#right_tail)"
          using less.prems right_case right_run
          by (simp add: punctured_positive_runs_def)
        have left_count_positive: "0 < left_count"
          using left_current_positive
          by (auto simp: punctured_positive_runs_def)
        have right_count_positive: "0 < right_count"
          using right_current_positive
          by (auto simp: punctured_positive_runs_def)
        let ?chunk = "min (Suc remaining) (min left_count right_count)"
        have chunk_positive: "0 < ?chunk"
          using left_count_positive right_count_positive by simp
        have chunk_total: "?chunk \<le> Suc remaining" by simp
        have chunk_left: "?chunk \<le> left_count" by simp
        have chunk_right: "?chunk \<le> right_count" by simp
        let ?left = "punctured_run_advance ?chunk
          ((left_symbol,left_count)#left_tail)"
        let ?right = "punctured_run_advance ?chunk
          ((right_symbol,right_count)#right_tail)"
        let ?rest = "Suc remaining - ?chunk"
        have rest_bound: "?rest < Suc remaining"
          using chunk_positive by arith
        have rest_less_amount: "?rest < amount"
          using rest_bound Suc by simp
        have left_rest_positive: "punctured_positive_runs ?left"
          by (rule punctured_advance_positive[OF left_current_positive chunk_left])
        have right_rest_positive: "punctured_positive_runs ?right"
          by (rule punctured_advance_positive[OF right_current_positive chunk_right])
        have recursive:
          "punctured_expand_runs (punctured_run_zip ?left ?right ?rest) =
            take ?rest (map punctured_pair_sum
              (zip (punctured_expand_runs ?left)
                (punctured_expand_runs ?right)))"
          using less.IH rest_less_amount
            left_rest_positive right_rest_positive by blast
        have left_expansion:
          "punctured_expand_runs ((left_symbol,left_count)#left_tail) =
             replicate left_count left_symbol @
               punctured_expand_runs left_tail"
          by simp
        have right_expansion:
          "punctured_expand_runs ((right_symbol,right_count)#right_tail) =
             replicate right_count right_symbol @
               punctured_expand_runs right_tail"
          by simp
        have left_advance:
          "punctured_expand_runs ?left = drop ?chunk
            (punctured_expand_runs ((left_symbol,left_count)#left_tail))"
          using punctured_advance_expansion[OF left_count_positive chunk_left]
          by simp
        have right_advance:
          "punctured_expand_runs ?right = drop ?chunk
            (punctured_expand_runs ((right_symbol,right_count)#right_tail))"
          using punctured_advance_expansion[OF right_count_positive chunk_right]
          by simp
        have left_length: "?chunk \<le>
            length (punctured_expand_runs ((left_symbol,left_count)#left_tail))"
          using chunk_left by simp
        have right_length: "?chunk \<le>
            length (punctured_expand_runs ((right_symbol,right_count)#right_tail))"
          using chunk_right by simp
        have zip_drop:
          "zip (drop ?chunk
               (punctured_expand_runs ((left_symbol,left_count)#left_tail)))
             (drop ?chunk
               (punctured_expand_runs ((right_symbol,right_count)#right_tail))) =
           drop ?chunk (zip
             (punctured_expand_runs ((left_symbol,left_count)#left_tail))
             (punctured_expand_runs ((right_symbol,right_count)#right_tail)))"
          by (rule punctured_zip_drop[OF left_length right_length])
        have mapped_zip_drop:
          "map punctured_pair_sum
            (zip (drop ?chunk
               (punctured_expand_runs ((left_symbol,left_count)#left_tail)))
             (drop ?chunk
               (punctured_expand_runs ((right_symbol,right_count)#right_tail)))) =
           drop ?chunk (map punctured_pair_sum
             (zip
               (punctured_expand_runs ((left_symbol,left_count)#left_tail))
               (punctured_expand_runs ((right_symbol,right_count)#right_tail))))"
          using zip_drop by (simp add: drop_map)
        have prefix:
          "take ?chunk (map punctured_pair_sum (zip
             (punctured_expand_runs ((left_symbol,left_count)#left_tail))
             (punctured_expand_runs ((right_symbol,right_count)#right_tail)))) =
           replicate ?chunk (left_symbol + right_symbol)"
          using punctured_take_zip_replicates[OF chunk_left chunk_right]
          by (simp add: left_expansion right_expansion punctured_pair_sum_def)
        let ?word = "map punctured_pair_sum (zip
          (punctured_expand_runs ((left_symbol,left_count)#left_tail))
          (punctured_expand_runs ((right_symbol,right_count)#right_tail)))"
        have dropped_word:
          "drop ?chunk ?word = map punctured_pair_sum
            (zip (punctured_expand_runs ?left)
              (punctured_expand_runs ?right))"
          using mapped_zip_drop left_advance right_advance
          by (simp only: left_advance right_advance mapped_zip_drop)
        have rhs:
          "take (Suc remaining) ?word =
            replicate ?chunk (left_symbol + right_symbol) @
              take ?rest (map punctured_pair_sum
                (zip (punctured_expand_runs ?left)
                  (punctured_expand_runs ?right)))"
        proof -
          have "take (Suc remaining) ?word =
                take ?chunk ?word @ take ?rest (drop ?chunk ?word)"
              by (rule punctured_take_split[OF chunk_total])
          also have "... = replicate ?chunk (left_symbol + right_symbol) @
                take ?rest (map punctured_pair_sum
                  (zip (punctured_expand_runs ?left)
                    (punctured_expand_runs ?right)))"
              by (simp only: prefix dropped_word)
          finally show ?thesis .
        qed
        have lhs:
          "punctured_expand_runs (punctured_run_zip
              ((left_symbol,left_count)#left_tail)
              ((right_symbol,right_count)#right_tail) (Suc remaining)) =
            replicate ?chunk (left_symbol + right_symbol) @
              punctured_expand_runs (punctured_run_zip ?left ?right ?rest)"
          using left_case right_case Suc left_run right_run
          by (simp add: punctured_run_zip.simps Let_def)
        show ?thesis using lhs rhs recursive left_case right_case Suc
            left_run right_run
          by simp
      qed
    qed
  qed
qed

lemma punctured_expand_rev_runs:
  "punctured_expand_runs (rev runs) = rev (punctured_expand_runs runs)"
proof (induction runs)
  case Nil
  then show ?case by simp
next
  case (Cons pair runs)
  obtain symbol count where pair: "pair = (symbol,count)"
    by (cases pair) auto
  show ?case using Cons.IH pair
    by (simp add: punctured_expand_runs_append rev_append)
qed

lemma punctured_pair_mirror_half_expansion:
  assumes positive: "punctured_positive_runs runs"
  shows "punctured_expand_runs (punctured_pair_mirror_half runs) =
    take ((punctured_run_width runs + 1) div 2)
      (map punctured_pair_sum
        (zip (punctured_expand_runs runs)
          (rev (punctured_expand_runs runs))))"
proof -
  have reverse_positive: "punctured_positive_runs (rev runs)"
    using positive by (simp add: punctured_positive_runs_def)
  have zipped:
    "punctured_expand_runs (punctured_run_zip runs (rev runs)
      ((punctured_run_width runs + 1) div 2)) =
     take ((punctured_run_width runs + 1) div 2)
       (map punctured_pair_sum
         (zip (punctured_expand_runs runs)
           (punctured_expand_runs (rev runs))))"
    by (rule punctured_run_zip_expansion[OF positive reverse_positive])
  show ?thesis
    using zipped punctured_coalesce_expansion punctured_expand_rev_runs
      punctured_run_width_exact
    by (simp add: punctured_pair_mirror_half_def)
qed

lemma punctured_pair_mirror_half_length:
  assumes positive: "punctured_positive_runs runs"
  shows "length (punctured_expand_runs (punctured_pair_mirror_half runs)) =
    (punctured_run_width runs + 1) div 2"
proof -
  let ?word = "punctured_expand_runs runs"
  let ?half = "(punctured_run_width runs + 1) div 2"
  have width: "punctured_run_width runs = length ?word"
    by (rule punctured_run_width_exact)
  have half_bound: "?half \<le> length ?word"
    using width by presburger
  have expansion:
    "punctured_expand_runs (punctured_pair_mirror_half runs) =
      take ?half (map punctured_pair_sum (zip ?word (rev ?word)))"
    by (rule punctured_pair_mirror_half_expansion[OF positive])
  show ?thesis using expansion half_bound by simp
qed

lemma punctured_symmetric_words_equal_by_half:
  assumes same_length: "length left = length right"
      and left_symmetric: "rev left = left"
      and right_symmetric: "rev right = right"
      and same_half:
        "take ((length left + 1) div 2) left =
          take ((length right + 1) div 2) right"
  shows "left = right"
proof (rule nth_equalityI)
  show "length left = length right" by (rule same_length)
next
  fix index
  assume index_bound: "index < length left"
  let ?half = "(length left + 1) div 2"
  let ?mirror = "length left - Suc index"
  have half_bound: "length left \<le> 2 * ?half" by presburger
  have half_le_length: "?half \<le> length left" by presburger
  show "left ! index = right ! index"
  proof (cases "index < ?half")
    case True
    have right_half: "(length right + 1) div 2 = ?half"
      using same_length by simp
    have prefix_equal:
      "take ?half left = take ?half right"
      using same_half right_half by simp
    have left_take: "take ?half left ! index = left ! index"
      using True index_bound by simp
    have right_take: "take ?half right ! index = right ! index"
      using True index_bound same_length by simp
    show ?thesis using prefix_equal left_take right_take by metis
  next
    case False
    have mirror_bound: "?mirror < ?half"
      using False index_bound half_bound by presburger
    have mirror_in_range: "?mirror < length left"
      using mirror_bound half_le_length by presburger
    have left_reflected: "left ! index = left ! ?mirror"
    proof -
      have "left ! index = rev left ! index"
        using left_symmetric by simp
      also have "... = left ! ?mirror"
        using rev_nth[OF index_bound] by (simp add: algebra_simps)
      finally show ?thesis .
    qed
    have right_index_bound: "index < length right"
      using index_bound same_length by simp
    have right_mirror_bound: "?mirror < length right"
      using mirror_in_range same_length by simp
    have right_reflected: "right ! index = right ! ?mirror"
    proof -
      have "right ! index = rev right ! index"
        using right_symmetric by simp
      also have "... = right ! ?mirror"
        using rev_nth[OF right_index_bound] same_length
        by (simp add: algebra_simps)
      finally show ?thesis .
    qed
    have right_half: "(length right + 1) div 2 = ?half"
      using same_length by simp
    have prefix_equal: "take ?half left = take ?half right"
      using same_half right_half by simp
    have prefix_at_mirror:
      "take ?half left ! ?mirror = take ?half right ! ?mirror"
      using prefix_equal by simp
    have "left ! ?mirror = right ! ?mirror"
      using prefix_at_mirror mirror_bound mirror_in_range right_mirror_bound
      by simp
    then show ?thesis using left_reflected right_reflected by simp
  qed
qed

lemma punctured_q19_decode_half_reconstructs:
  assumes symmetric: "rev word = word"
  shows "punctured_q19_decode_half
      (take ((length word + 1) div 2) word)
      (length word mod 2 = 1) = word"
proof -
  let ?half = "(length word + 1) div 2"
  let ?is_odd = "length word mod 2 = 1"
  let ?decoded = "punctured_q19_decode_half (take ?half word) ?is_odd"
  have half_bound: "?half \<le> length word" by presburger
  have decoded_symmetric: "rev ?decoded = ?decoded"
    by (rule punctured_q19_decode_half_symmetric)
  have decoded_length: "length ?decoded = length word"
  proof -
    have half_length: "length (take ?half word) = ?half"
      using half_bound by simp
    have formula: "length ?decoded =
        2 * length (take ?half word) - (if ?is_odd then 1 else 0)"
      by (rule punctured_q19_decode_half_length)
    show ?thesis using formula half_length by (simp; presburger)
  qed
  have half_prefix: "take ?half ?decoded = take ?half word"
    by (simp add: punctured_q19_decode_half_def)
  have half_prefix_at_length:
    "take ((length ?decoded + 1) div 2) ?decoded =
      take ((length word + 1) div 2) word"
    using half_prefix decoded_length by simp
  show ?thesis
    by (rule punctured_symmetric_words_equal_by_half[OF
        decoded_length decoded_symmetric symmetric half_prefix_at_length])
qed

theorem punctured_run_pairing_decodes_second_step:
  assumes positive: "punctured_positive_runs runs"
      and source: "punctured_expand_runs runs = digits (step ss)"
  shows "punctured_q19_decode_half
      (punctured_expand_runs (punctured_pair_mirror_half runs))
      (length (punctured_expand_runs runs) mod 2 = 1) =
    step (step ss)"
proof -
  have width:
    "punctured_run_width runs = length (step (step ss))"
    using source by (simp add: punctured_run_width_exact step_def)
  have pair_sums:
    "map punctured_pair_sum
       (zip (punctured_expand_runs runs)
         (rev (punctured_expand_runs runs))) = step (step ss)"
  proof -
    have map_pair_sum:
      "map punctured_pair_sum
          (zip (digits (step ss)) (rev (digits (step ss)))) =
        map (\<lambda>(left,right). left + right)
          (zip (digits (step ss)) (rev (digits (step ss))))"
      by (rule map_cong) (auto simp: punctured_pair_sum_def split: prod.splits)
    show ?thesis using source map_pair_sum
      by (simp only: source step_def map_pair_sum)
  qed
  have half:
    "punctured_expand_runs (punctured_pair_mirror_half runs) =
      take ((length (step (step ss)) + 1) div 2) (step (step ss))"
    using punctured_pair_mirror_half_expansion[OF positive] width pair_sums
    by simp
  have decoded_symmetric:
    "rev (step (step ss)) = step (step ss)"
    by (rule step_symmetric)
  have decoded_length:
    "length (step (step ss)) = length (punctured_expand_runs runs)"
    using source by simp
  have decode:
    "punctured_q19_decode_half
      (take ((length (step (step ss)) + 1) div 2) (step (step ss)))
      (length (step (step ss)) mod 2 = 1) = step (step ss)"
    by (rule punctured_q19_decode_half_reconstructs[OF decoded_symmetric])
  show ?thesis using half decode decoded_length by simp
qed

corollary punctured_compact_runs_pairing_decodes_second_step:
  assumes bounded: "\<forall>run\<in>set runs. fst run < 19"
      and source: "punctured_expand_runs runs = step ss"
  shows "punctured_q19_decode_half
      (punctured_expand_runs
        (punctured_pair_mirror_half (punctured_decimal_runs runs)))
      (length (punctured_expand_runs (punctured_decimal_runs runs)) mod 2 = 1) =
    step (step ss)"
proof -
  have decimal_word:
    "punctured_expand_runs (punctured_decimal_runs runs) = digits (step ss)"
    using punctured_decimal_runs_expansion[OF bounded] source by simp
  have decimal_positive:
    "punctured_positive_runs (punctured_decimal_runs runs)"
    by (rule punctured_decimal_runs_positive)
  have paired:
    "punctured_q19_decode_half
      (punctured_expand_runs
        (punctured_pair_mirror_half (punctured_decimal_runs runs)))
      (length (punctured_expand_runs (punctured_decimal_runs runs)) mod 2 = 1) =
      step (step ss)"
    by (rule punctured_run_pairing_decodes_second_step[OF decimal_positive])
       (simp add: decimal_word)
  show ?thesis by (rule paired)
qed

ML \<open>
  val checked = @{thms punctured_coalesce_expansion
    punctured_run_zip_expansion punctured_pair_mirror_half_expansion
    punctured_pair_mirror_half_length punctured_q19_decode_half_reconstructs
    punctured_run_pairing_decodes_second_step
    punctured_decimal_runs_expansion
    punctured_compact_runs_pairing_decodes_second_step};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Punctured run pairing depends on a theorem oracle";
\<close>

end
