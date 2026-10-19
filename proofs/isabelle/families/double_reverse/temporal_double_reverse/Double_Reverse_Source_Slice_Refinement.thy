theory Double_Reverse_Source_Slice_Refinement
  imports Double_Reverse_Source_Window_Refinement
begin

text \<open>The runtime `DoubleReverseTemporalEngine.part` routine drains an
ordered interval worklist.  This recursive definition is its extensional
normal form: CONCAT tasks are split at the left-child seam, and REPEAT tasks
emit a partial first child, a whole repeated middle, and a partial last child
in the same left-to-right order.  The task stack, cache, and arena-issued
indices are implementation details; this theory proves the returned grammar
denotes the requested finite source slice.  In particular, it does not
re-prove arena issuance or memo ownership.\<close>

fun double_reverse_source_slp_part ::
    "double_reverse_source_slp \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
      double_reverse_source_slp" where
  "double_reverse_source_slp_part Double_Reverse_Source_Empty begin end =
    Double_Reverse_Source_Empty"
| "double_reverse_source_slp_part (Double_Reverse_Source_Term digit) begin end =
    (if begin < end then Double_Reverse_Source_Term digit
     else Double_Reverse_Source_Empty)"
| "double_reverse_source_slp_part
      (Double_Reverse_Source_Concat left right) begin end =
    (let seam = double_reverse_source_slp_length left in
     if end \<le> seam then
       double_reverse_source_slp_part left begin end
     else if seam \<le> begin then
       double_reverse_source_slp_part right (begin-seam) (end-seam)
     else
       Double_Reverse_Source_Concat
         (double_reverse_source_slp_part left begin seam)
         (double_reverse_source_slp_part right 0 (end-seam)))"
| "double_reverse_source_slp_part
      (Double_Reverse_Source_Repeat child count) begin end =
    (if begin = end then Double_Reverse_Source_Empty
     else let child_length = double_reverse_source_slp_length child in
       if child_length = 0 then Double_Reverse_Source_Empty
       else let first_copy = begin div child_length;
                first_offset = begin mod child_length;
                last_copy = end div child_length;
                last_offset = end mod child_length
            in if first_copy = last_copy then
              double_reverse_source_slp_part child first_offset last_offset
            else Double_Reverse_Source_Concat
              (if first_offset = 0 then Double_Reverse_Source_Empty
               else double_reverse_source_slp_part child first_offset child_length)
              (Double_Reverse_Source_Concat
                (Double_Reverse_Source_Repeat child
                  (last_copy-first_copy-(if first_offset = 0 then 0 else 1)))
                (if last_offset = 0 then Double_Reverse_Source_Empty
                 else double_reverse_source_slp_part child 0 last_offset)))"

lemma double_reverse_source_repeat_word_add:
  "double_reverse_source_repeat_word word (left+right) =
    double_reverse_source_repeat_word word left @
      double_reverse_source_repeat_word word right"
  by (induction left) simp_all

lemma double_reverse_source_repeat_word_drop:
  assumes positive: "0 < length word"
      and bound: "begin < count * length word"
  shows "drop begin (double_reverse_source_repeat_word word count) =
    drop (begin mod length word) word @
      double_reverse_source_repeat_word word
        (count - begin div length word - 1)"
proof -
  let ?length = "length word"
  let ?first = "begin div ?length"
  let ?offset = "begin mod ?length"
  let ?tail = "count - ?first - 1"
  have first_bound: "?first < count"
    using bound positive by (meson div_less_iff_less_mult)
  have count_split: "count = ?first + Suc ?tail"
    using first_bound by arith
  have word_split:
    "double_reverse_source_repeat_word word count =
      double_reverse_source_repeat_word word ?first @
        (word @ double_reverse_source_repeat_word word ?tail)"
  proof -
    have count_argument:
      "double_reverse_source_repeat_word word count =
        double_reverse_source_repeat_word word (?first + Suc ?tail)"
      by (rule arg_cong[where f="double_reverse_source_repeat_word word",
          OF count_split])
    have repeated_prefix:
      "double_reverse_source_repeat_word word (?first + Suc ?tail) =
        double_reverse_source_repeat_word word ?first @
          double_reverse_source_repeat_word word (Suc ?tail)"
      by (rule double_reverse_source_repeat_word_add)
    show ?thesis
      using count_argument repeated_prefix by simp
  qed
  have begin_split: "begin = ?first * ?length + ?offset"
    by (metis div_mult_mod_eq mult.commute)
  have prefix_length:
    "length (double_reverse_source_repeat_word word ?first) =
      ?first * ?length"
    by (simp add: double_reverse_source_repeat_word_length)
  have offset_bound: "?offset < ?length"
    using positive by simp
  have offset_decomposition:
    "begin = ?first * ?length + ?offset"
    using begin_split by simp
  have dropped_index: "begin - ?first * ?length = ?offset"
    using begin_split by arith
  have next_copy_decomposition:
    "(?first+1) * ?length = ?first * ?length + ?length"
    by (simp add: algebra_simps)
  have begin_after_prefix:
    "length (double_reverse_source_repeat_word word ?first) \<le> begin"
    using prefix_length begin_split by arith
  have begin_before_next: "begin < (?first+1) * ?length"
  proof -
    have "begin < ?first * ?length + ?length"
      using offset_decomposition offset_bound by arith
    then show ?thesis using next_copy_decomposition by arith
  qed
  show ?thesis
    using word_split begin_split dropped_index prefix_length offset_bound
      begin_after_prefix begin_before_next positive
    by (simp add: double_reverse_source_repeat_word_length drop_append)
qed

lemma double_reverse_source_repeat_word_take:
  assumes positive: "0 < length word"
      and copies: "middle \<le> copies"
      and tail: "tail \<le> length word"
      and available: "tail = 0 \<or> middle < copies"
  shows "take (middle * length word + tail)
      (double_reverse_source_repeat_word word copies) =
    double_reverse_source_repeat_word word middle @ take tail word"
proof -
  have split:
    "double_reverse_source_repeat_word word copies =
      double_reverse_source_repeat_word word middle @
        double_reverse_source_repeat_word word (copies-middle)"
  proof -
    have decomposition: "copies = middle + (copies-middle)"
      using copies by arith
    have repeat_decomposition:
      "double_reverse_source_repeat_word word copies =
        double_reverse_source_repeat_word word (middle + (copies-middle))"
      by (rule arg_cong[OF decomposition])
    have repeat_add:
      "double_reverse_source_repeat_word word (middle + (copies-middle)) =
        double_reverse_source_repeat_word word middle @
          double_reverse_source_repeat_word word (copies-middle)"
      by (rule double_reverse_source_repeat_word_add)
    show ?thesis by (rule trans[OF repeat_decomposition repeat_add])
  qed
  have suffix:
    "take tail (double_reverse_source_repeat_word word (copies-middle)) =
      take tail word"
  proof (cases "tail=0")
    case True
    then show ?thesis by simp
  next
    case False
    have middle_lt: "middle < copies"
      using available False by blast
    have rest_positive: "0 < copies-middle"
      using middle_lt by arith
    then obtain rest where rest_succ: "copies-middle = Suc rest"
      by (cases "copies-middle") auto
    have repeated:
      "double_reverse_source_repeat_word word (copies-middle) =
        word @ double_reverse_source_repeat_word word rest"
      using rest_succ by simp
    show ?thesis
      using tail repeated by (simp add: take_append)
  qed
  show ?thesis
    using split suffix positive tail
    by (simp add: double_reverse_source_repeat_word_length take_append)
qed

lemma double_reverse_source_repeat_word_slice:
  assumes positive: "0 < length word"
      and interval: "begin < end"
      and bound: "end \<le> count * length word"
  defines "first_copy \<equiv> begin div length word"
      and "offset \<equiv> begin mod length word"
      and "last_copy \<equiv> end div length word"
      and "last_offset \<equiv> end mod length word"
  shows "take (end-begin) (drop begin
      (double_reverse_source_repeat_word word count)) =
    (if first_copy = last_copy then
       take (last_offset-offset) (drop offset word)
     else (if offset = 0 then [] else drop offset word) @
       double_reverse_source_repeat_word word
         (last_copy-first_copy-(if offset = 0 then 0 else 1)) @
       take last_offset word)"
proof -
  have begin_bound: "begin < count * length word"
    using interval bound by arith
  have first_bound: "first_copy < count"
    using begin_bound positive unfolding first_copy_def
    by (meson div_less_iff_less_mult)
  have last_bound: "last_copy \<le> count"
  proof -
    have quotient_bound:
      "end div length word \<le>
        (count * length word) div length word"
      by (rule div_le_mono[OF bound])
    have quotient_count:
      "(count * length word) div length word = count"
      using positive by simp
    show ?thesis
      using quotient_bound quotient_count unfolding last_copy_def by simp
  qed
  have begin_decomp: "begin = first_copy * length word + offset"
    unfolding first_copy_def offset_def
    by (metis div_mult_mod_eq mult.commute)
  have end_decomp: "end = last_copy * length word + last_offset"
    unfolding last_copy_def last_offset_def
    by (metis div_mult_mod_eq mult.commute)
  have last_offset_bound: "last_offset < length word"
    unfolding last_offset_def using positive by simp
  have dropped_raw:
    "drop begin (double_reverse_source_repeat_word word count) =
      drop (begin mod length word) word @
        double_reverse_source_repeat_word word
          (count - begin div length word - 1)"
  proof (rule double_reverse_source_repeat_word_drop[OF positive])
    show "begin < count * length word" using interval bound by arith
  qed
  have dropped:
    "drop begin (double_reverse_source_repeat_word word count) =
      drop offset word @ double_reverse_source_repeat_word word (count-first_copy-1)"
    using dropped_raw unfolding first_copy_def offset_def by simp
  show ?thesis
  proof (cases "first_copy = last_copy")
    case True
    have same_copy_product:
      "first_copy * length word = last_copy * length word"
      using True by simp
    have offset_le: "offset \<le> last_offset"
      using interval begin_decomp end_decomp same_copy_product by arith
    have short: "last_offset-offset \<le> length (drop offset word)"
      using offset_le last_offset_bound by (simp add: offset_def)
    show ?thesis
      using dropped True short
      by (simp add: begin_decomp end_decomp take_append)
  next
    case different: False
    have first_lt_last: "first_copy < last_copy"
    proof -
      have quotient_order:
        "begin div length word \<le> end div length word"
        using interval by (simp add: div_le_mono)
      show ?thesis
        using quotient_order different
        unfolding first_copy_def last_copy_def by arith
    qed
    have prefix_length: "length (drop offset word) = length word-offset"
      unfolding offset_def by simp
    have offset_bound: "offset < length word"
      unfolding offset_def using positive by simp
    have last_lt_count: "last_copy < count" if "last_offset > 0"
    proof -
      have not_equal: "last_copy \<noteq> count"
      proof
        assume equal: "last_copy = count"
        have equal_product:
          "last_copy * length word = count * length word"
          using equal by simp
        have end_form:
          "end = count * length word + last_offset"
          using end_decomp equal_product by simp
        show False using bound end_form that by arith
      qed
      show ?thesis using last_bound not_equal by arith
    qed
    show ?thesis
    proof (cases "offset=0")
      case aligned: True
      have product_difference:
        "(last_copy-first_copy)*length word = last_copy*length word-first_copy*length word"
        using first_lt_last by (simp add: diff_mult_distrib)
      have first_product_le:
        "first_copy*length word \<le> last_copy*length word"
      proof -
        have copy_order: "first_copy \<le> last_copy"
          using first_lt_last by simp
        show ?thesis by (rule mult_le_mono1[OF copy_order])
      qed
      have interval_length:
        "end-begin = (last_copy-first_copy)*length word + last_offset"
        using begin_decomp end_decomp aligned product_difference first_product_le
        by arith
      have enough_middle: "last_copy-first_copy \<le> count-first_copy"
        using first_bound last_bound by arith
      have weak_last_bound: "last_offset \<le> length word"
        using last_offset_bound by arith
      have tail_split: "count-first_copy = Suc (count-first_copy-1)"
        using first_bound by arith
      have suffix_available:
        "last_offset=0 \<or> last_copy-first_copy < count-first_copy"
      proof (cases "last_offset=0")
        case True
        then show ?thesis by simp
      next
        case False
        have strict: "last_copy<count" by (rule last_lt_count) (use False in arith)
        have copy_order: "first_copy \<le> last_copy"
          using first_lt_last by simp
        show ?thesis using False strict copy_order by arith
      qed
      have remainder:
        "take ((last_copy-first_copy)*length word + last_offset)
          (double_reverse_source_repeat_word word (count-first_copy)) =
         double_reverse_source_repeat_word word (last_copy-first_copy) @
           take last_offset word"
        by (rule double_reverse_source_repeat_word_take
          [OF positive enough_middle weak_last_bound suffix_available])
      have dropped_aligned:
        "drop begin (double_reverse_source_repeat_word word count) =
          double_reverse_source_repeat_word word (count-first_copy)"
        using dropped aligned tail_split
        by (simp add: double_reverse_source_repeat_word_add)
      show ?thesis
        using dropped_aligned aligned interval_length remainder
        by (simp add: take_append)
    next
      case unaligned: False
      let ?middle = "last_copy-first_copy-1"
      have first_succ_le_last: "first_copy+1 \<le> last_copy"
        using first_lt_last by arith
      have middle_difference: "last_copy-first_copy-1 = last_copy-(first_copy+1)"
        using first_lt_last by arith
      have middle_product:
        "?middle*length word =
          last_copy*length word-(first_copy+1)*length word"
        unfolding middle_difference
        by (simp add: diff_mult_distrib)
      have first_succ_product:
        "(first_copy+1)*length word = first_copy*length word + length word"
        by (simp add: algebra_simps)
      have first_succ_product_le:
        "(first_copy+1)*length word \<le> last_copy*length word"
      proof -
        have "first_copy+1 \<le> last_copy" by (rule first_succ_le_last)
        then have "(first_copy+1)*length word \<le> last_copy*length word"
          by (rule mult_le_mono1)
        then show ?thesis by (simp add: mult.commute)
      qed
      have interval_length:
        "end-begin = (length word-offset) +
          ?middle*length word + last_offset"
        using begin_decomp end_decomp first_lt_last unaligned offset_bound
          middle_product first_succ_product first_succ_product_le
        by arith
      have enough_middle: "?middle \<le> count-first_copy-1"
        using first_bound last_bound first_lt_last by arith
      have weak_last_bound: "last_offset \<le> length word"
        using last_offset_bound by arith
      have suffix_available:
        "last_offset=0 \<or> ?middle < count-first_copy-1"
      proof (cases "last_offset=0")
        case True
        then show ?thesis by simp
      next
        case False
        have strict: "last_copy<count" by (rule last_lt_count) (use False in arith)
        show ?thesis using False strict first_succ_le_last by arith
      qed
      have prefix_drop:
        "take (length word-offset) (drop offset word) = drop offset word"
        using offset_def unaligned by simp
      have remainder:
        "take (?middle*length word + last_offset)
          (double_reverse_source_repeat_word word (count-first_copy-1)) =
         double_reverse_source_repeat_word word ?middle @ take last_offset word"
        by (rule double_reverse_source_repeat_word_take
          [OF positive enough_middle weak_last_bound suffix_available])
      show ?thesis
        using dropped interval_length prefix_length prefix_drop remainder
          unaligned different first_lt_last
        by (simp add: take_append)
    qed
  qed
qed

theorem double_reverse_source_slp_part_exact:
  assumes interval: "begin \<le> end"
      and bound: "end \<le> double_reverse_source_slp_length source"
  shows "double_reverse_source_slp_word
      (double_reverse_source_slp_part source begin end) =
    take (end-begin) (drop begin (double_reverse_source_slp_word source))"
  using interval bound
proof (induction source arbitrary: "begin" "end")
  case Double_Reverse_Source_Empty
  then show ?case by simp
next
  case (Double_Reverse_Source_Term digit)
  then show ?case by (cases "begin"; cases "end"; simp)
next
  case (Double_Reverse_Source_Concat left right)
  let ?seam = "double_reverse_source_slp_length left"
  have left_length: "length (double_reverse_source_slp_word left) = ?seam"
    by (rule double_reverse_source_slp_word_length)
  have right_length: "length (double_reverse_source_slp_word right) =
      double_reverse_source_slp_length right"
    by (rule double_reverse_source_slp_word_length)
  have concat_bound:
    "end \<le> ?seam + double_reverse_source_slp_length right"
    using Double_Reverse_Source_Concat.prems(2) by simp
  show ?case
  proof (cases "end \<le> ?seam")
    case True
    have left_bound:
      "end \<le> double_reverse_source_slp_length left"
      using True by simp
    have left_exact:
      "double_reverse_source_slp_word
          (double_reverse_source_slp_part left begin end) =
        take (end-begin) (drop begin (double_reverse_source_slp_word left))"
      by (rule Double_Reverse_Source_Concat.IH(1)
          [OF Double_Reverse_Source_Concat.prems(1) left_bound])
    have begin_before_seam: "begin \<le> ?seam"
      using Double_Reverse_Source_Concat.prems(1) True by arith
    have slice_before_seam: "end-begin \<le> ?seam-begin"
      using Double_Reverse_Source_Concat.prems(1) True by arith
    show ?thesis using left_exact True left_length
        begin_before_seam slice_before_seam
      by (simp add: double_reverse_source_slp_length.simps
          drop_append take_append Let_def)
  next
    case end_after: False
    show ?thesis
    proof (cases "?seam \<le> begin")
      case True
      have right_interval:
        "begin-?seam \<le> end-?seam"
        using Double_Reverse_Source_Concat.prems(1) by arith
      have right_bound:
        "end-?seam \<le> double_reverse_source_slp_length right"
        using concat_bound by arith
      have right_exact:
        "double_reverse_source_slp_word
          (double_reverse_source_slp_part right (begin-?seam) (end-?seam)) =
         take ((end-?seam)-(begin-?seam))
          (drop (begin-?seam) (double_reverse_source_slp_word right))"
        by (rule Double_Reverse_Source_Concat.IH(2)
          [OF right_interval right_bound])
      have seam_before_end: "?seam \<le> end"
        using Double_Reverse_Source_Concat.prems(1) True by arith
      have seam_strict_before_end: "?seam < end"
        using end_after by arith
      have shifted_span:
        "(end-?seam)-(begin-?seam) = end-begin"
        using Double_Reverse_Source_Concat.prems(1) True by arith
      show ?thesis using right_exact True left_length
          seam_before_end seam_strict_before_end shifted_span
        by (simp add: double_reverse_source_slp_length.simps
            drop_append take_append Let_def)
    next
      case False
      have begin_before: "begin < ?seam" using False by simp
      have left_interval: "begin \<le> ?seam"
        using begin_before by arith
      have left_child_bound:
        "?seam \<le> double_reverse_source_slp_length left"
        by simp
      have left_exact:
        "double_reverse_source_slp_word
          (double_reverse_source_slp_part left begin ?seam) =
         take (?seam-begin) (drop begin (double_reverse_source_slp_word left))"
        by (rule Double_Reverse_Source_Concat.IH(1)
          [OF left_interval left_child_bound])
      have right_interval: "0 \<le> end-?seam"
        using end_after by arith
      have right_child_bound:
        "end-?seam \<le> double_reverse_source_slp_length right"
        using concat_bound end_after by arith
      have right_exact_raw:
        "double_reverse_source_slp_word
          (double_reverse_source_slp_part right 0 (end-?seam)) =
         take ((end-?seam)-0)
           (drop 0 (double_reverse_source_slp_word right))"
        by (rule Double_Reverse_Source_Concat.IH(2)
          [OF right_interval right_child_bound])
      have right_exact:
        "double_reverse_source_slp_word
          (double_reverse_source_slp_part right 0 (end-?seam)) =
         take (end-?seam) (drop 0 (double_reverse_source_slp_word right))"
        using right_exact_raw by simp
      have left_tail_length:
        "length (drop begin (double_reverse_source_slp_word left)) =
          ?seam-begin"
        using begin_before left_length by simp
      have span_split:
        "end-begin = (?seam-begin) + (end-?seam)"
        using begin_before end_after by arith
      show ?thesis using left_exact right_exact begin_before end_after left_length
          left_tail_length span_split
        by (simp add: double_reverse_source_slp_length.simps
            drop_append take_append Let_def)
    qed
  qed
next
  case (Double_Reverse_Source_Repeat child count)
  let ?child_length = "double_reverse_source_slp_length child"
  let ?word = "double_reverse_source_slp_word child"
  have child_length: "length ?word = ?child_length"
    by (rule double_reverse_source_slp_word_length)
  have repeat_word:
    "double_reverse_source_slp_word
      (Double_Reverse_Source_Repeat child count) =
      double_reverse_source_repeat_word ?word count"
    by simp
  show ?case
  proof (cases "begin = end")
    case True
    then show ?thesis by (simp add: Let_def)
  next
    case nonempty: False
    have positive: "0 < ?child_length"
      using Double_Reverse_Source_Repeat.prems nonempty by (cases ?child_length) auto
    have positive_word: "0 < length ?word"
      using positive child_length by simp
    let ?first = "begin div ?child_length"
    let ?offset = "begin mod ?child_length"
    let ?last = "end div ?child_length"
    let ?last_offset = "end mod ?child_length"
    have strict_interval: "begin < end"
      using Double_Reverse_Source_Repeat.prems(1) nonempty by arith
    have repeated_bound: "end \<le> count * ?child_length"
      using Double_Reverse_Source_Repeat.prems(2) by simp
    have repeated_word_bound: "end \<le> count * length ?word"
      using repeated_bound child_length by simp
    have last_offset_bound: "?last_offset < ?child_length"
      using positive by simp
    have repeated_slice:
      "take (end-begin) (drop begin
          (double_reverse_source_repeat_word ?word count)) =
        (if ?first = ?last then
           take (?last_offset-?offset) (drop ?offset ?word)
         else (if ?offset=0 then [] else drop ?offset ?word) @
           double_reverse_source_repeat_word ?word
             (?last-?first-(if ?offset=0 then 0 else 1)) @
           take ?last_offset ?word)"
      using double_reverse_source_repeat_word_slice
        [OF positive_word strict_interval repeated_word_bound]
        child_length
      by simp
    show ?thesis
    proof (cases "?first = ?last")
      case same: True
      have begin_decomposition:
        "begin = ?first * ?child_length + ?offset"
        by (metis div_mult_mod_eq mult.commute)
      have end_decomposition:
        "end = ?last * ?child_length + ?last_offset"
        by (metis div_mult_mod_eq mult.commute)
      have same_product:
        "?first * ?child_length = ?last * ?child_length"
        using same by simp
      have offset_order: "?offset \<le> ?last_offset"
        using Double_Reverse_Source_Repeat.prems(1)
          begin_decomposition end_decomposition same_product
        by arith
      have end_bound: "?last_offset \<le> ?child_length"
        using last_offset_bound by simp
      have part_exact:
        "double_reverse_source_slp_word
          (double_reverse_source_slp_part child ?offset ?last_offset) =
         take (?last_offset-?offset) (drop ?offset ?word)"
        by (rule Double_Reverse_Source_Repeat.IH[OF offset_order end_bound])
      have slice_exact:
        "take (end-begin) (drop begin
            (double_reverse_source_repeat_word ?word count)) =
         take (?last_offset-?offset) (drop ?offset ?word)"
        using repeated_slice same offset_order child_length
        by simp
      show ?thesis using same part_exact slice_exact child_length repeat_word
        by (simp add: Let_def)
    next
      case different: False
      have begin_before_end: "begin < end"
        using Double_Reverse_Source_Repeat.prems(1) nonempty by arith
      have quotient_order: "?first \<le> ?last"
        using begin_before_end by (simp add: div_le_mono)
      have first_lt_last: "?first < ?last"
        using quotient_order different by arith
      have prefix_exact:
        "double_reverse_source_slp_word
          (if ?offset=0 then Double_Reverse_Source_Empty
           else double_reverse_source_slp_part child ?offset ?child_length) =
         (if ?offset=0 then [] else drop ?offset ?word)"
      proof (cases "?offset=0")
        case True
        then show ?thesis by simp
      next
        case False
        have offset_bound: "?offset < ?child_length"
          using positive by simp
        have offset_interval: "?offset \<le> ?child_length"
          using offset_bound by simp
        have child_length_bound: "?child_length \<le> ?child_length"
          by simp
        have child_part:
          "double_reverse_source_slp_word
            (double_reverse_source_slp_part child ?offset ?child_length) =
           take (?child_length-?offset) (drop ?offset ?word)"
          using Double_Reverse_Source_Repeat.IH
            [OF offset_interval child_length_bound] by simp
        show ?thesis using False child_part child_length
          by simp
      qed
      have suffix_exact:
        "double_reverse_source_slp_word
          (if ?last_offset=0 then Double_Reverse_Source_Empty
           else double_reverse_source_slp_part child 0 ?last_offset) =
         take ?last_offset ?word"
      proof (cases "?last_offset=0")
        case True
        then show ?thesis by simp
      next
        case False
        have tail_bound: "?last_offset \<le> ?child_length"
          using positive by simp
        have zero_bound: "0 \<le> ?last_offset"
          by simp
        have child_part_raw:
          "double_reverse_source_slp_word
            (double_reverse_source_slp_part child 0 ?last_offset) =
           take (?last_offset-0) (drop 0 ?word)"
          using Double_Reverse_Source_Repeat.IH
            [OF zero_bound tail_bound] by simp
        have child_part:
          "double_reverse_source_slp_word
            (double_reverse_source_slp_part child 0 ?last_offset) =
           take ?last_offset (drop 0 ?word)"
          using child_part_raw by simp
        show ?thesis using False child_part by simp
      qed
      have middle:
        "double_reverse_source_slp_word
          (Double_Reverse_Source_Repeat child
            (?last-?first-(if ?offset=0 then 0 else 1))) =
         double_reverse_source_repeat_word ?word
            (?last-?first-(if ?offset=0 then 0 else 1))"
        by simp
      have slice_exact:
        "take (end-begin) (drop begin
            (double_reverse_source_repeat_word ?word count)) =
          (if ?offset=0 then [] else drop ?offset ?word) @
           double_reverse_source_repeat_word ?word
            (?last-?first-(if ?offset=0 then 0 else 1)) @
           take ?last_offset ?word"
        using repeated_slice different child_length by simp
      have part_shape:
        "double_reverse_source_slp_part
           (Double_Reverse_Source_Repeat child count) begin end =
         Double_Reverse_Source_Concat
           (if ?offset=0 then Double_Reverse_Source_Empty
            else double_reverse_source_slp_part child ?offset ?child_length)
           (Double_Reverse_Source_Concat
             (Double_Reverse_Source_Repeat child
               (?last-?first-(if ?offset=0 then 0 else 1)) )
             (if ?last_offset=0 then Double_Reverse_Source_Empty
              else double_reverse_source_slp_part child 0 ?last_offset))"
        using nonempty positive different
        by (simp only: double_reverse_source_slp_part.simps Let_def; simp)
      have part_word:
        "double_reverse_source_slp_word
           (double_reverse_source_slp_part
             (Double_Reverse_Source_Repeat child count) begin end) =
         (if ?offset=0 then [] else drop ?offset ?word) @
           double_reverse_source_repeat_word ?word
             (?last-?first-(if ?offset=0 then 0 else 1)) @
           take ?last_offset ?word"
        using part_shape prefix_exact middle suffix_exact
        by (simp only: double_reverse_source_slp_word.simps)
      have part_eq_slice:
        "double_reverse_source_slp_word
           (double_reverse_source_slp_part
             (Double_Reverse_Source_Repeat child count) begin end) =
         take (end-begin)
           (drop begin (double_reverse_source_repeat_word ?word count))"
      proof -
        have slice_back:
          "(if ?offset=0 then [] else drop ?offset ?word) @
             double_reverse_source_repeat_word ?word
               (?last-?first-(if ?offset=0 then 0 else 1)) @
             take ?last_offset ?word =
           take (end-begin)
             (drop begin (double_reverse_source_repeat_word ?word count))"
          using slice_exact by (rule sym)
        show ?thesis by (rule trans[OF part_word slice_back])
      qed
      show ?thesis using part_eq_slice repeat_word by simp
    qed
  qed
qed

lemma double_reverse_source_slp_part_length:
  assumes interval: "begin \<le> end"
      and bound: "end \<le> double_reverse_source_slp_length source"
  shows "double_reverse_source_slp_length
      (double_reverse_source_slp_part source begin end) = end-begin"
proof -
  have exact:
    "double_reverse_source_slp_word
      (double_reverse_source_slp_part source begin end) =
     take (end-begin) (drop begin (double_reverse_source_slp_word source))"
    by (rule double_reverse_source_slp_part_exact[OF interval bound])
  have drop_bound:
    "end-begin \<le> length (drop begin (double_reverse_source_slp_word source))"
    using interval bound
    by (simp add: double_reverse_source_slp_word_length; arith)
  have exact_length:
    "length (double_reverse_source_slp_word
        (double_reverse_source_slp_part source begin end)) =
      length (take (end-begin)
        (drop begin (double_reverse_source_slp_word source)))"
    by (rule arg_cong[where f=length, OF exact])
  have part_word_length:
    "length (double_reverse_source_slp_word
        (double_reverse_source_slp_part source begin end)) =
      double_reverse_source_slp_length
        (double_reverse_source_slp_part source begin end)"
    by (rule double_reverse_source_slp_word_length)
  have take_length:
    "length (take (end-begin)
        (drop begin (double_reverse_source_slp_word source))) = end-begin"
    using drop_bound by simp
  show ?thesis using exact_length part_word_length take_length by simp
qed

theorem double_reverse_pointed_source_window_slp_part_exact:
  fixes source :: "double_reverse_source_slp"
    and origin :: int
    and radius :: nat
    and source_word :: "nat list"
    and "begin" :: int
    and count :: nat
    and first :: nat
    and middle_length :: nat
    and middle :: "double_reverse_source_slp"
  defines "source_word \<equiv> double_reverse_source_slp_word source"
      and "begin \<equiv> origin-int radius"
      and "count \<equiv> 2*radius+1"
      and "first \<equiv> double_reverse_source_window_first begin"
      and "middle_length \<equiv>
        double_reverse_source_window_middle_length source_word begin count"
      and "middle \<equiv>
        (if middle_length=0 then Double_Reverse_Source_Empty
         else double_reverse_source_slp_part source first (first+middle_length))"
  shows "double_reverse_source_slp_word
      (double_reverse_source_window_slp source_word begin count middle) =
    double_reverse_pointed_source_window source_word origin radius"
proof -
  have geometry:
    "middle_length=0 \<or> first+middle_length \<le> length source_word"
    unfolding middle_length_def first_def source_word_def
    by (rule double_reverse_source_window_fragment_geometry(2))
  have part_exact:
    "double_reverse_source_slp_word middle =
      take middle_length (drop first source_word)"
  proof (cases "middle_length=0")
    case True
    then show ?thesis by (simp add: middle_def)
  next
    case False
    have part_bound: "first+middle_length \<le> length source_word"
      using geometry False by blast
    have source_length:
      "length source_word = double_reverse_source_slp_length source"
      by (simp add: source_word_def double_reverse_source_slp_word_length)
    have exact_raw:
      "double_reverse_source_slp_word
        (double_reverse_source_slp_part source first (first+middle_length)) =
       take ((first+middle_length)-first)
         (drop first (double_reverse_source_slp_word source))"
    proof (rule double_reverse_source_slp_part_exact)
      show "first \<le> first+middle_length" by simp
      show "first+middle_length \<le> double_reverse_source_slp_length source"
        using part_bound source_length by simp
    qed
    have exact_raw_normalized:
      "double_reverse_source_slp_word
        (double_reverse_source_slp_part source first (first+middle_length)) =
       take middle_length (drop first (double_reverse_source_slp_word source))"
      using exact_raw by simp
    have exact: "double_reverse_source_slp_word
        (double_reverse_source_slp_part source first (first+middle_length)) =
       take middle_length (drop first source_word)"
      using exact_raw_normalized by (simp add: source_word_def)
    show ?thesis using False exact by (simp add: middle_def)
  qed
  have part_for_window:
    "double_reverse_source_slp_word middle =
      take (double_reverse_source_window_middle_length source_word
        (origin-int radius) (2*radius+1))
        (drop (double_reverse_source_window_first (origin-int radius))
          source_word)"
    using part_exact
    unfolding middle_length_def first_def begin_def count_def
    by simp
  show ?thesis
    using double_reverse_pointed_source_window_slp_exact[OF part_for_window]
    unfolding source_word_def begin_def count_def by simp
qed

ML \<open>
  val checked = @{thms double_reverse_source_slp_part_length
    double_reverse_source_repeat_word_drop
    double_reverse_source_repeat_word_take
    double_reverse_source_repeat_word_slice
    double_reverse_source_slp_part_exact
    double_reverse_pointed_source_window_slp_part_exact};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Double-reverse source-slice refinement depends on an oracle";
  val _ = if Thm_Deps.has_skip_proof checked
    then error "Double-reverse source-slice refinement contains skip_proof"
    else ();
\<close>

end
