theory Double_Reverse_Source_Window_Refinement
  imports Double_Reverse_Bitplane_Refinement
begin

text \<open>This theory gives a list semantics to the production source SLP node
shapes EMPTY, TERM, CONCAT, and REPEAT.  Its phase certificate models the
runtime worklist's distinct (grammar node, phase modulo motif length) states.
For REPEAT, it checks the first min(count, phase-cycle) child phases; the
cycle lemma below proves these cover every copy's phase.  A certificate is
about the complete finite SLP row only; it gives no periodicity claim outside
that row.\<close>

datatype double_reverse_source_slp =
    Double_Reverse_Source_Empty
  | Double_Reverse_Source_Term nat
  | Double_Reverse_Source_Concat
      double_reverse_source_slp double_reverse_source_slp
  | Double_Reverse_Source_Repeat double_reverse_source_slp nat

fun double_reverse_source_repeat_word :: "nat list \<Rightarrow> nat \<Rightarrow> nat list" where
  "double_reverse_source_repeat_word word 0 = []"
| "double_reverse_source_repeat_word word (Suc count) =
    word @ double_reverse_source_repeat_word word count"

fun double_reverse_source_slp_word :: "double_reverse_source_slp \<Rightarrow> nat list" where
  "double_reverse_source_slp_word Double_Reverse_Source_Empty = []"
| "double_reverse_source_slp_word (Double_Reverse_Source_Term digit) = [digit]"
| "double_reverse_source_slp_word (Double_Reverse_Source_Concat left right) =
    double_reverse_source_slp_word left @ double_reverse_source_slp_word right"
| "double_reverse_source_slp_word (Double_Reverse_Source_Repeat child count) =
    double_reverse_source_repeat_word
      (double_reverse_source_slp_word child) count"

fun double_reverse_source_slp_length :: "double_reverse_source_slp \<Rightarrow> nat" where
  "double_reverse_source_slp_length Double_Reverse_Source_Empty = 0"
| "double_reverse_source_slp_length (Double_Reverse_Source_Term _) = 1"
| "double_reverse_source_slp_length (Double_Reverse_Source_Concat left right) =
    double_reverse_source_slp_length left + double_reverse_source_slp_length right"
| "double_reverse_source_slp_length (Double_Reverse_Source_Repeat child count) =
    count * double_reverse_source_slp_length child"

lemma double_reverse_source_repeat_word_length:
  "length (double_reverse_source_repeat_word word count) = count * length word"
  by (induction count) (simp_all add: algebra_simps)

lemma double_reverse_source_slp_word_length:
  "length (double_reverse_source_slp_word source) =
    double_reverse_source_slp_length source"
  by (induction source)
    (simp_all add: double_reverse_source_repeat_word_length)

definition double_reverse_source_phase_cycle :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "double_reverse_source_phase_cycle period child_length =
    (if child_length mod period = 0 then 1
     else period div gcd period (child_length mod period))"

lemma double_reverse_source_phase_cycle_positive:
  assumes period: "0 < period"
  shows "0 < double_reverse_source_phase_cycle period child_length"
proof (cases "child_length mod period = 0")
  case True
  then show ?thesis
    by (simp add: double_reverse_source_phase_cycle_def)
next
  case False
  let ?g = "gcd period (child_length mod period)"
  have remainder_positive: "0 < child_length mod period"
    using False by arith
  have remainder_bound: "child_length mod period < period"
    using period by simp
  have gcd_bound: "?g \<le> child_length mod period"
    using remainder_positive by simp
  have gcd_less: "?g < period"
    using gcd_bound remainder_bound by arith
  have gcd_positive: "0 < ?g"
    using period by (simp add: gcd_pos_nat)
  have quotient_positive: "0 < period div ?g"
  proof (rule ccontr)
    assume not_positive: "\<not> 0 < period div ?g"
    have quotient_zero: "period div ?g = 0"
      using not_positive by arith
    have decomposition:
      "period = period div ?g * ?g + period mod ?g"
      by (metis div_mult_mod_eq mult.commute)
    have remainder_small: "period mod ?g < ?g"
      using gcd_positive by simp
    have contradiction: "period < ?g"
      using quotient_zero decomposition remainder_small by arith
    show False using contradiction gcd_less by arith
  qed
  show ?thesis
    using quotient_positive False
    by (simp add: double_reverse_source_phase_cycle_def)
qed

lemma double_reverse_source_phase_cycle_annihilates:
  assumes period: "0 < period"
  shows "(double_reverse_source_phase_cycle period child_length * child_length)
    mod period = 0"
proof (cases "child_length mod period = 0")
  case True
  then show ?thesis
    by (simp add: double_reverse_source_phase_cycle_def)
next
  case False
  let ?g = "gcd period (child_length mod period)"
  have gcd_divides_period: "?g dvd period" by simp
  have gcd_divides_remainder: "?g dvd child_length mod period" by simp
  have child_decomposition:
    "child_length = (child_length div period) * period + child_length mod period"
    by (metis div_mult_mod_eq mult.commute)
  have gcd_divides_first:
    "?g dvd (child_length div period) * period"
    using gcd_divides_period by simp
  have gcd_divides_length: "?g dvd child_length"
    using dvd_add[OF gcd_divides_first gcd_divides_remainder]
      child_decomposition by simp
  have period_factor:
    "period div ?g * ?g = period"
    by (rule dvd_div_mult_self[OF gcd_divides_period])
  have length_factor:
    "child_length div ?g * ?g = child_length"
    by (rule dvd_div_mult_self[OF gcd_divides_length])
  have product_factor:
    "period div ?g * child_length = period * (child_length div ?g)"
  proof -
    have first:
      "period div ?g * child_length =
        period div ?g * (child_length div ?g * ?g)"
      by (rule arg_cong[OF length_factor[symmetric]])
    have middle:
      "period div ?g * (child_length div ?g * ?g) =
        (period div ?g * ?g) * (child_length div ?g)"
      by (simp add: algebra_simps)
    have last:
      "(period div ?g * ?g) * (child_length div ?g) =
        period * (child_length div ?g)"
      by (simp only: period_factor)
    show ?thesis using first middle last by simp
  qed
  show ?thesis
    using product_factor False
    by (simp add: double_reverse_source_phase_cycle_def)
qed

lemma double_reverse_source_phase_cycle_representative:
  assumes period: "0 < period"
      and copy: "copy < count"
  obtains representative where
    "representative < min count
      (double_reverse_source_phase_cycle period child_length)"
    "(phase + copy * child_length) mod period =
      (phase + representative * child_length) mod period"
proof -
  let ?cycle = "double_reverse_source_phase_cycle period child_length"
  let ?representative = "copy mod ?cycle"
  have cycle_positive: "0 < ?cycle"
    by (rule double_reverse_source_phase_cycle_positive[OF period])
  have representative_cycle:
    "?representative < ?cycle"
    using cycle_positive by (rule mod_less_divisor)
  have copy_decomposition:
    "copy = ?cycle * (copy div ?cycle) + ?representative"
    by (metis div_mult_mod_eq mult.commute)
  have representative_copy: "?representative \<le> copy"
    using copy_decomposition by arith
  have representative_count: "?representative < count"
    using copy representative_copy by arith
  have representative_bound:
    "?representative < min count ?cycle"
    using representative_count representative_cycle by simp
  have cycle_multiple:
    "(?cycle * child_length) mod period = 0"
    by (rule double_reverse_source_phase_cycle_annihilates[OF period])
  have shifted_multiple:
    "((copy div ?cycle) * (?cycle * child_length)) mod period = 0"
  proof -
    have reduced:
      "((copy div ?cycle) * (?cycle * child_length)) mod period =
        ((copy div ?cycle) * ((?cycle * child_length) mod period)) mod period"
      by (rule mod_mult_right_eq[symmetric])
    show ?thesis using reduced cycle_multiple by simp
  qed
  have exponent_decomposition:
    "phase + copy * child_length =
      (phase + ?representative * child_length) +
        (copy div ?cycle) * (?cycle * child_length)"
  proof -
    have expanded:
      "copy * child_length =
        (?cycle * (copy div ?cycle) + ?representative) * child_length"
      by (rule arg_cong[OF copy_decomposition])
    have distributed:
      "copy * child_length =
        (?cycle * (copy div ?cycle)) * child_length +
          ?representative * child_length"
      using expanded by (simp only: add_mult_distrib)
    have regrouped:
      "(?cycle * (copy div ?cycle)) * child_length =
        (copy div ?cycle) * (?cycle * child_length)"
      by (simp add: ac_simps)
    have product:
      "copy * child_length =
        ?representative * child_length +
          (copy div ?cycle) * (?cycle * child_length)"
      using distributed regrouped by (simp add: add.commute)
    show ?thesis using product by (simp add: algebra_simps)
  qed
  have phase_equality:
    "(phase + copy * child_length) mod period =
      (phase + ?representative * child_length) mod period"
  proof -
    have add_mod:
      "((phase + ?representative * child_length) +
          (copy div ?cycle) * (?cycle * child_length)) mod period =
        ((phase + ?representative * child_length) mod period +
          ((copy div ?cycle) * (?cycle * child_length)) mod period) mod period"
      by (rule mod_add_eq[symmetric])
    have exponent_mod:
      "(phase + copy * child_length) mod period =
        ((phase + ?representative * child_length) +
          (copy div ?cycle) * (?cycle * child_length)) mod period"
      by (rule arg_cong[OF exponent_decomposition])
    have remainder_mod:
      "((phase + ?representative * child_length) +
          (copy div ?cycle) * (?cycle * child_length)) mod period =
        (phase + ?representative * child_length) mod period"
      using add_mod shifted_multiple by simp
    show ?thesis by (rule trans[OF exponent_mod remainder_mod])
  qed
  show thesis
    by (rule that[OF representative_bound phase_equality])
qed

definition double_reverse_source_matches_motif ::
    "nat list \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> bool" where
  "double_reverse_source_matches_motif motif phase row \<longleftrightarrow>
    motif \<noteq> [] \<and>
    (\<forall>i<length row. row ! i = double_reverse_ring_digit motif (phase + i))"

lemma double_reverse_ring_digit_phase_rebase:
  assumes motif: "motif \<noteq> []"
  shows "double_reverse_ring_digit motif (phase mod length motif + offset) =
    double_reverse_ring_digit motif (phase + offset)"
  using motif
  by (simp add: double_reverse_ring_digit_def mod_add_left_eq)

lemma double_reverse_source_matches_phase_mod:
  assumes motif: "motif \<noteq> []"
  shows "double_reverse_source_matches_motif motif (phase mod length motif) row =
    double_reverse_source_matches_motif motif phase row"
  using motif double_reverse_ring_digit_phase_rebase[OF motif, of phase]
  unfolding double_reverse_source_matches_motif_def
  by (auto simp: double_reverse_ring_digit_phase_rebase)

lemma double_reverse_source_matches_append:
  assumes left: "double_reverse_source_matches_motif motif phase first"
      and right: "double_reverse_source_matches_motif motif
        (phase + length first) second"
  shows "double_reverse_source_matches_motif motif phase (first @ second)"
proof -
  have motif: "motif \<noteq> []"
    using left by (simp add: double_reverse_source_matches_motif_def)
  have cells:
    "(first @ second) ! i = double_reverse_ring_digit motif (phase + i)"
    if "i < length (first @ second)" for i
  proof (cases "i < length first")
    case True
    have first_value: "first ! i = double_reverse_ring_digit motif (phase + i)"
      using left True by (simp add: double_reverse_source_matches_motif_def)
    have appended_value: "(first @ second) ! i = first ! i"
      using True by (simp add: nth_append)
    show ?thesis using appended_value first_value by simp
  next
    case False
    have first_bound: "length first \<le> i" using False by arith
    have second_index: "i - length first < length second"
      using that first_bound by simp
    have second_value:
      "second ! (i - length first) =
        double_reverse_ring_digit motif (phase + length first + (i - length first))"
      using right second_index
      by (simp add: double_reverse_source_matches_motif_def)
    have index: "phase + length first + (i - length first) = phase + i"
      using first_bound by arith
    show ?thesis using False second_value index by (simp add: nth_append)
  qed
  show ?thesis
    using motif cells
    by (auto simp: double_reverse_source_matches_motif_def)
qed

lemma double_reverse_source_matches_repeat:
  assumes motif: "motif \<noteq> []"
      and copies:
        "\<forall>copy<count. \<forall>i<length word.
          word ! i = double_reverse_ring_digit motif
            (phase + copy * length word + i)"
  shows "double_reverse_source_matches_motif motif phase
    (double_reverse_source_repeat_word word count)"
  using copies
proof (induction count arbitrary: phase)
  case 0
  then show ?case
    using motif by (simp add: double_reverse_source_matches_motif_def)
next
  case (Suc count)
  have head_cells:
    "word ! i = double_reverse_ring_digit motif (phase + i)"
    if "i < length word" for i
    using Suc.prems[rule_format, of 0 i] that by simp
  have head:
    "double_reverse_source_matches_motif motif phase word"
    using motif head_cells
    by (simp add: double_reverse_source_matches_motif_def)
  have tail_copies:
    "\<forall>copy<count. \<forall>i<length word.
      word ! i = double_reverse_ring_digit motif
        ((phase + length word) + copy * length word + i)"
  proof (intro allI impI)
    fix copy i
    assume copy: "copy < count" and index: "i < length word"
    have original:
      "word ! i = double_reverse_ring_digit motif
        (phase + (Suc copy) * length word + i)"
      using Suc.prems copy index by blast
    have exponent:
      "phase + (Suc copy) * length word + i =
        (phase + length word) + copy * length word + i"
      by (simp add: algebra_simps)
    have same_digit:
      "double_reverse_ring_digit motif
          (phase + (Suc copy) * length word + i) =
        double_reverse_ring_digit motif
          ((phase + length word) + copy * length word + i)"
      by (rule arg_cong[OF exponent])
    show "word ! i = double_reverse_ring_digit motif
        ((phase + length word) + copy * length word + i)"
      by (rule trans[OF original same_digit])
  qed
  have tail:
    "double_reverse_source_matches_motif motif (phase + length word)
      (double_reverse_source_repeat_word word count)"
    using Suc.IH[OF tail_copies] motif by simp
  show ?case
    using double_reverse_source_matches_append[OF head tail]
    by simp
qed

fun double_reverse_source_slp_phase_certificate ::
    "nat list \<Rightarrow> double_reverse_source_slp \<Rightarrow> nat \<Rightarrow> bool" where
  "double_reverse_source_slp_phase_certificate motif
      Double_Reverse_Source_Empty phase = True"
| "double_reverse_source_slp_phase_certificate motif
      (Double_Reverse_Source_Term digit) phase =
    (motif \<noteq> [] \<and> digit = double_reverse_ring_digit motif phase)"
| "double_reverse_source_slp_phase_certificate motif
      (Double_Reverse_Source_Concat left right) phase =
    (double_reverse_source_slp_phase_certificate motif left phase \<and>
     double_reverse_source_slp_phase_certificate motif right
       ((phase + double_reverse_source_slp_length left) mod length motif))"
| "double_reverse_source_slp_phase_certificate motif
      (Double_Reverse_Source_Repeat child count) phase =
    (motif \<noteq> [] \<and>
     (\<forall>copy<min count
        (double_reverse_source_phase_cycle (length motif)
          (double_reverse_source_slp_length child)).
       double_reverse_source_slp_phase_certificate motif child
         ((phase + copy * double_reverse_source_slp_length child) mod
           length motif)))"

theorem double_reverse_source_slp_phase_certificate_sound:
  assumes motif: "motif \<noteq> []"
      and certificate:
        "double_reverse_source_slp_phase_certificate motif source phase"
  shows "double_reverse_source_matches_motif motif phase
    (double_reverse_source_slp_word source)"
  using certificate
proof (induction source arbitrary: phase)
  case Double_Reverse_Source_Empty
  then show ?case
    using motif by (simp add: double_reverse_source_matches_motif_def)
next
  case (Double_Reverse_Source_Term digit)
  then show ?case
    using motif by (simp add: double_reverse_source_matches_motif_def)
next
  case (Double_Reverse_Source_Concat left right)
  have left_certificate:
    "double_reverse_source_slp_phase_certificate motif left phase"
    using Double_Reverse_Source_Concat.prems by simp
  have right_certificate:
    "double_reverse_source_slp_phase_certificate motif right
      ((phase + double_reverse_source_slp_length left) mod length motif)"
    using Double_Reverse_Source_Concat.prems by simp
  have left_match:
    "double_reverse_source_matches_motif motif phase
      (double_reverse_source_slp_word left)"
    by (rule Double_Reverse_Source_Concat.IH(1)[OF left_certificate])
  have right_match:
    "double_reverse_source_matches_motif motif
      (phase + double_reverse_source_slp_length left)
      (double_reverse_source_slp_word right)"
    using Double_Reverse_Source_Concat.IH(2)[OF right_certificate] motif
    by (simp add: double_reverse_source_matches_phase_mod)
  have left_word_length:
    "length (double_reverse_source_slp_word left) =
      double_reverse_source_slp_length left"
    by (rule double_reverse_source_slp_word_length)
  have right_match_at_append:
    "double_reverse_source_matches_motif motif
      (phase + length (double_reverse_source_slp_word left))
      (double_reverse_source_slp_word right)"
    using right_match left_word_length by simp
  show ?case
    using double_reverse_source_matches_append[OF left_match right_match_at_append]
    by simp
next
  case (Double_Reverse_Source_Repeat child count)
  have motif_period: "0 < length motif"
    using motif by simp
  have all_copies:
    "\<forall>copy<count. double_reverse_source_slp_phase_certificate motif child
      ((phase + copy * double_reverse_source_slp_length child) mod length motif)"
  proof (intro allI impI)
    fix copy
    assume copy: "copy < count"
    obtain representative where bound:
      "representative < min count
        (double_reverse_source_phase_cycle (length motif)
          (double_reverse_source_slp_length child))"
      and equal:
        "(phase + copy * double_reverse_source_slp_length child) mod length motif =
          (phase + representative * double_reverse_source_slp_length child) mod
            length motif"
      by (rule double_reverse_source_phase_cycle_representative[
        OF motif_period copy])
    have representative_certificate:
      "double_reverse_source_slp_phase_certificate motif child
        ((phase + representative * double_reverse_source_slp_length child) mod
          length motif)"
      using Double_Reverse_Source_Repeat.prems bound by simp
    show "double_reverse_source_slp_phase_certificate motif child
      ((phase + copy * double_reverse_source_slp_length child) mod length motif)"
      using representative_certificate equal by simp
  qed
  have child_matches:
    "\<forall>copy<count. \<forall>i<length (double_reverse_source_slp_word child).
      double_reverse_source_slp_word child ! i =
        double_reverse_ring_digit motif
          (phase + copy * double_reverse_source_slp_length child + i)"
  proof (intro allI impI)
    fix copy i
    assume copy: "copy < count" and
      index: "i < length (double_reverse_source_slp_word child)"
    have cert:
      "double_reverse_source_slp_phase_certificate motif child
        ((phase + copy * double_reverse_source_slp_length child) mod length motif)"
      using all_copies copy by blast
    have match:
      "double_reverse_source_matches_motif motif
        ((phase + copy * double_reverse_source_slp_length child) mod length motif)
        (double_reverse_source_slp_word child)"
      by (rule Double_Reverse_Source_Repeat.IH[OF cert])
    have checked:
      "double_reverse_source_slp_word child ! i =
        double_reverse_ring_digit motif
          (((phase + copy * double_reverse_source_slp_length child) mod
            length motif) + i)"
      using match index
      by (simp add: double_reverse_source_matches_motif_def)
    show "double_reverse_source_slp_word child ! i =
        double_reverse_ring_digit motif
          (phase + copy * double_reverse_source_slp_length child + i)"
      using checked motif
      by (simp add: double_reverse_ring_digit_phase_rebase)
  qed
  have child_word_length:
    "length (double_reverse_source_slp_word child) =
      double_reverse_source_slp_length child"
    by (rule double_reverse_source_slp_word_length)
  have child_matches_repeat:
    "\<forall>copy<count. \<forall>i<length (double_reverse_source_slp_word child).
      double_reverse_source_slp_word child ! i =
        double_reverse_ring_digit motif
          (phase + copy * length (double_reverse_source_slp_word child) + i)"
  proof (intro allI impI)
    fix copy i
    assume copy: "copy < count" and
      index: "i < length (double_reverse_source_slp_word child)"
    have checked:
      "double_reverse_source_slp_word child ! i =
        double_reverse_ring_digit motif
          (phase + copy * double_reverse_source_slp_length child + i)"
      using child_matches copy index by blast
    show "double_reverse_source_slp_word child ! i =
        double_reverse_ring_digit motif
          (phase + copy * length (double_reverse_source_slp_word child) + i)"
      using checked child_word_length by simp
  qed
  have repeated:
    "double_reverse_source_matches_motif motif phase
      (double_reverse_source_repeat_word
        (double_reverse_source_slp_word child) count)"
    by (rule double_reverse_source_matches_repeat[OF motif child_matches_repeat])
  show ?case using repeated by simp
qed

definition double_reverse_zero_extended_source_window ::
    "nat list \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> nat list" where
  "double_reverse_zero_extended_source_window source begin count =
    map (\<lambda>offset.
      if 0 \<le> begin + int offset \<and>
          begin + int offset < int (length source)
      then source ! nat (begin + int offset) else 0) [0..<count]"

definition double_reverse_pointed_source_window ::
    "nat list \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> nat list" where
  "double_reverse_pointed_source_window source origin radius =
    double_reverse_zero_extended_source_window source
      (origin - int radius) (2 * radius + 1)"

lemma double_reverse_zero_extended_source_window_length:
  "length (double_reverse_zero_extended_source_window source begin count) = count"
  by (simp add: double_reverse_zero_extended_source_window_def)

lemma double_reverse_zero_extended_source_window_nth:
  assumes index: "index < count"
  shows "double_reverse_zero_extended_source_window source begin count ! index =
    (if 0 \<le> begin + int index \<and>
        begin + int index < int (length source)
     then source ! nat (begin + int index) else 0)"
  using index
  by (simp add: double_reverse_zero_extended_source_window_def)

lemma double_reverse_pointed_source_window_length:
  "length (double_reverse_pointed_source_window source origin radius) =
    2 * radius + 1"
  by (simp add: double_reverse_pointed_source_window_def
      double_reverse_zero_extended_source_window_length)

lemma double_reverse_pointed_source_window_nth:
  assumes index: "index < 2 * radius + 1"
  shows "double_reverse_pointed_source_window source origin radius ! index =
    (if 0 \<le> origin - int radius + int index \<and>
        origin - int radius + int index < int (length source)
     then source ! nat (origin - int radius + int index) else 0)"
  using index
  by (simp add: double_reverse_pointed_source_window_def
      double_reverse_zero_extended_source_window_nth)

definition double_reverse_source_window_left_zeros :: "int \<Rightarrow> nat \<Rightarrow> nat" where
  "double_reverse_source_window_left_zeros begin count =
    min count (nat (max 0 (-begin)))"

definition double_reverse_source_window_right_zeros ::
    "nat list \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> nat" where
  "double_reverse_source_window_right_zeros source begin count =
    min (count - double_reverse_source_window_left_zeros begin count)
      (nat (max 0 (begin + int count - int (length source))))"

definition double_reverse_source_window_middle_length ::
    "nat list \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> nat" where
  "double_reverse_source_window_middle_length source begin count =
    count - double_reverse_source_window_left_zeros begin count -
      double_reverse_source_window_right_zeros source begin count"

definition double_reverse_source_window_first :: "int \<Rightarrow> nat" where
  "double_reverse_source_window_first begin = nat (max 0 begin)"

definition double_reverse_source_window_fragments ::
    "nat list \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> nat list" where
  "double_reverse_source_window_fragments source begin count =
    replicate (double_reverse_source_window_left_zeros begin count) 0 @
      take (double_reverse_source_window_middle_length source begin count)
        (drop (double_reverse_source_window_first begin) source) @
      replicate (double_reverse_source_window_right_zeros source begin count) 0"

definition double_reverse_source_window_slp ::
    "nat list \<Rightarrow> int \<Rightarrow> nat \<Rightarrow>
      double_reverse_source_slp \<Rightarrow> double_reverse_source_slp" where
  "double_reverse_source_window_slp source begin count middle =
    Double_Reverse_Source_Concat
      (Double_Reverse_Source_Repeat (Double_Reverse_Source_Term 0)
        (double_reverse_source_window_left_zeros begin count))
      (Double_Reverse_Source_Concat middle
        (Double_Reverse_Source_Repeat (Double_Reverse_Source_Term 0)
          (double_reverse_source_window_right_zeros source begin count)))"

lemma double_reverse_source_window_fragment_geometry:
  shows
    "double_reverse_source_window_left_zeros begin count +
      double_reverse_source_window_middle_length source begin count +
      double_reverse_source_window_right_zeros source begin count = count"
    and
    "double_reverse_source_window_middle_length source begin count = 0 \<or>
      double_reverse_source_window_first begin +
        double_reverse_source_window_middle_length source begin count \<le>
          length source"
proof -
  let ?left = "double_reverse_source_window_left_zeros begin count"
  let ?right = "double_reverse_source_window_right_zeros source begin count"
  let ?middle = "double_reverse_source_window_middle_length source begin count"
  let ?first = "double_reverse_source_window_first begin"
  let ?end = "begin + int count"
  have left_bound: "?left \<le> count"
    by (simp add: double_reverse_source_window_left_zeros_def)
  have right_bound: "?right \<le> count - ?left"
    by (simp add: double_reverse_source_window_right_zeros_def)
  show "?left + ?middle + ?right = count"
    using left_bound right_bound
    by (simp add: double_reverse_source_window_middle_length_def
        add.commute)
  show "?middle = 0 \<or> ?first + ?middle \<le> length source"
    unfolding double_reverse_source_window_left_zeros_def
      double_reverse_source_window_right_zeros_def
      double_reverse_source_window_middle_length_def
      double_reverse_source_window_first_def
    by (cases "begin < 0"; cases "?end \<le> 0";
        cases "?end \<le> int (length source)";
        cases "begin < int (length source)";
        auto simp: min_def max_def split: if_splits; arith)
qed

lemma double_reverse_source_window_middle_slice_length:
  "length (take (double_reverse_source_window_middle_length source begin count)
    (drop (double_reverse_source_window_first begin) source)) =
    double_reverse_source_window_middle_length source begin count"
proof -
  have extent:
    "double_reverse_source_window_middle_length source begin count = 0 \<or>
      double_reverse_source_window_first begin +
        double_reverse_source_window_middle_length source begin count \<le>
          length source"
    by (rule double_reverse_source_window_fragment_geometry(2))
  show ?thesis
  proof (cases "double_reverse_source_window_middle_length source begin count = 0")
    case True
    then show ?thesis by simp
  next
    case False
    have middle_bound:
      "double_reverse_source_window_middle_length source begin count \<le>
        length source - double_reverse_source_window_first begin"
      using extent False by arith
    have take_length:
      "length (take (double_reverse_source_window_middle_length source begin count)
        (drop (double_reverse_source_window_first begin) source)) =
       min (double_reverse_source_window_middle_length source begin count)
         (length (drop (double_reverse_source_window_first begin) source))"
      by simp
    show ?thesis
    proof (rule trans[OF take_length])
      show "min (double_reverse_source_window_middle_length source begin count)
          (length (drop (double_reverse_source_window_first begin) source)) =
        double_reverse_source_window_middle_length source begin count"
        using middle_bound by simp
    qed
  qed
qed

lemma double_reverse_source_window_fragment_word_length:
  "length (double_reverse_source_window_fragments source begin count) = count"
proof -
  show ?thesis
    using double_reverse_source_window_fragment_geometry(1)
      double_reverse_source_window_middle_slice_length
    by (simp add: double_reverse_source_window_fragments_def add.assoc)
qed

lemma double_reverse_source_window_coordinate_trichotomy:
  assumes index: "index < count"
  shows
    "(index < double_reverse_source_window_left_zeros begin count \<and>
        begin + int index < 0) \<or>
     (double_reverse_source_window_left_zeros begin count \<le> index \<and>
        index < double_reverse_source_window_left_zeros begin count +
          double_reverse_source_window_middle_length source begin count \<and>
        begin + int index =
          int (double_reverse_source_window_first begin +
            (index - double_reverse_source_window_left_zeros begin count)) \<and>
        0 \<le> begin + int index \<and>
        begin + int index < int (length source)) \<or>
     (double_reverse_source_window_left_zeros begin count +
        double_reverse_source_window_middle_length source begin count
          \<le> index \<and>
      int (length source) \<le> begin + int index)"
proof -
  show ?thesis
    using index
    unfolding double_reverse_source_window_left_zeros_def
      double_reverse_source_window_right_zeros_def
      double_reverse_source_window_middle_length_def
      double_reverse_source_window_first_def
    by (cases "begin < 0";
        cases "begin + int count \<le> 0";
        cases "begin + int count \<le> int (length source)";
        cases "begin < int (length source)";
        simp_all add: min_def max_def; arith)
qed

lemma double_reverse_source_window_cell_classification:
  assumes index: "index < count"
  shows "double_reverse_zero_extended_source_window source begin count ! index =
    (if index < double_reverse_source_window_left_zeros begin count then 0
     else if index < double_reverse_source_window_left_zeros begin count +
          double_reverse_source_window_middle_length source begin count
     then source ! (double_reverse_source_window_first begin +
          (index - double_reverse_source_window_left_zeros begin count))
     else 0)"
proof -
  have selected:
    "double_reverse_zero_extended_source_window source begin count ! index =
      (if 0 \<le> begin + int index \<and>
          begin + int index < int (length source)
       then source ! nat (begin + int index) else 0)"
    by (rule double_reverse_zero_extended_source_window_nth[OF index])
  have coordinates:
    "(index < double_reverse_source_window_left_zeros begin count \<and>
        begin + int index < 0) \<or>
     (double_reverse_source_window_left_zeros begin count \<le> index \<and>
        index < double_reverse_source_window_left_zeros begin count +
          double_reverse_source_window_middle_length source begin count \<and>
        begin + int index =
          int (double_reverse_source_window_first begin +
            (index - double_reverse_source_window_left_zeros begin count)) \<and>
        0 \<le> begin + int index \<and>
        begin + int index < int (length source)) \<or>
     (double_reverse_source_window_left_zeros begin count +
        double_reverse_source_window_middle_length source begin count
          \<le> index \<and>
      int (length source) \<le> begin + int index)"
    by (rule double_reverse_source_window_coordinate_trichotomy[OF index])
  have translated_index:
    "double_reverse_source_window_left_zeros begin count \<le> index \<Longrightarrow>
     index < double_reverse_source_window_left_zeros begin count +
       double_reverse_source_window_middle_length source begin count \<Longrightarrow>
     nat (begin + int index) =
      double_reverse_source_window_first begin +
        (index - double_reverse_source_window_left_zeros begin count)"
  proof -
    assume left_bound:
      "double_reverse_source_window_left_zeros begin count \<le> index"
    assume middle_bound:
      "index < double_reverse_source_window_left_zeros begin count +
        double_reverse_source_window_middle_length source begin count"
    have middle_coordinates:
      "begin + int index =
        int (double_reverse_source_window_first begin +
          (index - double_reverse_source_window_left_zeros begin count))"
      using coordinates left_bound middle_bound by arith
    have "nat (begin + int index) =
        nat (int (double_reverse_source_window_first begin +
          (index - double_reverse_source_window_left_zeros begin count)))"
      by (rule arg_cong[where f=nat, OF middle_coordinates])
    then show ?thesis by simp
  qed
  show ?thesis
    using selected coordinates translated_index by auto
qed

lemma double_reverse_source_window_fragments_nth:
  assumes index: "index < count"
  shows "double_reverse_source_window_fragments source begin count ! index =
    (if index < double_reverse_source_window_left_zeros begin count then 0
     else if index < double_reverse_source_window_left_zeros begin count +
          double_reverse_source_window_middle_length source begin count
     then source ! (double_reverse_source_window_first begin +
          (index - double_reverse_source_window_left_zeros begin count))
     else 0)"
proof -
  let ?left = "double_reverse_source_window_left_zeros begin count"
  let ?middle = "double_reverse_source_window_middle_length source begin count"
  let ?first = "double_reverse_source_window_first begin"
  have middle_slice:
    "length (take ?middle (drop ?first source)) = ?middle"
    by (rule double_reverse_source_window_middle_slice_length)
  have prefix_length:
    "length (replicate ?left 0 @ take ?middle (drop ?first source)) =
      ?left + ?middle"
    using middle_slice by simp
  show ?thesis
  proof (cases "index < ?left")
    case True
    then show ?thesis
      unfolding double_reverse_source_window_fragments_def
      by (simp add: nth_append nth_replicate)
  next
    case not_left: False
    have after_left: "?left \<le> index" using not_left by arith
    show ?thesis
    proof (cases "index < ?left + ?middle")
      case inside: True
      have middle_offset: "index - ?left < ?middle"
        using after_left inside by arith
      have middle_positive: "0 < ?middle"
        using after_left inside by arith
      have extent:
        "?first + ?middle \<le> length source"
      proof -
        have geometry:
          "?middle=0 \<or> ?first + ?middle \<le> length source"
          by (rule double_reverse_source_window_fragment_geometry(2))
        have middle_nonzero: "?middle \<noteq> 0"
          using middle_positive by arith
        show ?thesis using geometry middle_nonzero by blast
      qed
      have source_index: "?first + (index - ?left) < length source"
        using extent middle_offset by arith
      show ?thesis
        using after_left inside middle_slice prefix_length
          middle_offset source_index
        unfolding double_reverse_source_window_fragments_def
        by (simp add: nth_append nth_replicate nth_take nth_drop)
    next
      case outside: False
      have after_middle: "?left + ?middle \<le> index"
        using outside by arith
      have geometry:
        "?left + ?middle + double_reverse_source_window_right_zeros
          source begin count = count"
        by (rule double_reverse_source_window_fragment_geometry(1))
      have right_offset:
        "index - (?left + ?middle) <
          double_reverse_source_window_right_zeros source begin count"
        using index geometry after_middle by arith
      have tail_start: "\<not> (index - ?left < ?middle)"
        using after_middle by arith
      show ?thesis
        using after_middle prefix_length right_offset tail_start
        unfolding double_reverse_source_window_fragments_def
        by (simp add: nth_append nth_replicate)
    qed
  qed
qed

theorem double_reverse_source_window_fragments_exact:
  "double_reverse_source_window_fragments source begin count =
    double_reverse_zero_extended_source_window source begin count"
proof (rule nth_equalityI)
  show "length (double_reverse_source_window_fragments source begin count) =
    length (double_reverse_zero_extended_source_window source begin count)"
    by (simp add: double_reverse_source_window_fragment_word_length
        double_reverse_zero_extended_source_window_length)
  fix index
  assume index:
    "index < length (double_reverse_source_window_fragments source begin count)"
  have index_bound: "index < count"
    using index
    by (simp add: double_reverse_source_window_fragment_word_length)
  show "double_reverse_source_window_fragments source begin count ! index =
    double_reverse_zero_extended_source_window source begin count ! index"
    using index_bound
    by (simp add: double_reverse_source_window_fragments_nth
        double_reverse_source_window_cell_classification)
qed

lemma double_reverse_source_repeat_zero_word:
  "double_reverse_source_repeat_word [0] count = replicate count 0"
  by (induction count) simp_all

theorem double_reverse_source_window_slp_has_fragment_word:
  assumes part:
    "double_reverse_source_slp_word middle =
      take (double_reverse_source_window_middle_length source begin count)
        (drop (double_reverse_source_window_first begin) source)"
  shows "double_reverse_source_slp_word
      (double_reverse_source_window_slp source begin count middle) =
    double_reverse_source_window_fragments source begin count"
  using part
  by (simp add: double_reverse_source_window_slp_def
      double_reverse_source_repeat_zero_word
      double_reverse_source_window_fragments_def)

theorem double_reverse_source_window_slp_exact:
  assumes part:
    "double_reverse_source_slp_word middle =
      take (double_reverse_source_window_middle_length source begin count)
        (drop (double_reverse_source_window_first begin) source)"
  shows "double_reverse_source_slp_word
      (double_reverse_source_window_slp source begin count middle) =
    double_reverse_zero_extended_source_window source begin count"
proof -
  have first:
    "double_reverse_source_slp_word
        (double_reverse_source_window_slp source begin count middle) =
      double_reverse_source_window_fragments source begin count"
    by (rule double_reverse_source_window_slp_has_fragment_word[OF part])
  have second:
    "double_reverse_source_window_fragments source begin count =
      double_reverse_zero_extended_source_window source begin count"
    by (rule double_reverse_source_window_fragments_exact)
  show ?thesis using first second by simp
qed

theorem double_reverse_pointed_source_window_slp_exact:
  assumes part:
    "double_reverse_source_slp_word middle =
      take (double_reverse_source_window_middle_length source
        (origin - int radius) (2 * radius + 1))
        (drop (double_reverse_source_window_first (origin - int radius)) source)"
  shows "double_reverse_source_slp_word
      (double_reverse_source_window_slp source (origin - int radius)
        (2 * radius + 1) middle) =
    double_reverse_pointed_source_window source origin radius"
  using double_reverse_source_window_slp_exact[OF part]
  by (simp add: double_reverse_pointed_source_window_def)

theorem double_reverse_source_window_certificate_refines_ring:
  assumes extracted:
      "double_reverse_source_slp_word window =
        double_reverse_pointed_source_window source origin radius"
      and motif: "motif \<noteq> []"
      and certificate:
        "double_reverse_source_slp_phase_certificate motif window 0"
  shows "double_reverse_row_matches_ring
    (double_reverse_pointed_source_window source origin radius) motif"
proof -
  have whole_row:
    "double_reverse_source_matches_motif motif 0
      (double_reverse_source_slp_word window)"
    by (rule double_reverse_source_slp_phase_certificate_sound[OF motif certificate])
  show ?thesis
    using whole_row extracted
    by (simp add: double_reverse_row_matches_ring_def
        double_reverse_source_matches_motif_def)
qed

theorem double_reverse_source_window_bitplane_point_refines_ring:
  assumes part:
      "double_reverse_source_slp_word middle =
        take (double_reverse_source_window_middle_length source
          (origin - int radius) (2 * radius + 1))
          (drop (double_reverse_source_window_first (origin - int radius)) source)"
      and motif: "motif \<noteq> []"
      and certificate:
        "double_reverse_source_slp_phase_certificate motif
          (double_reverse_source_window_slp source (origin - int radius)
            (2 * radius + 1) middle) 0"
      and positive: "0 < count"
      and radius: "radius = steps + count div 2"
      and index: "i < count"
      and decimal: "double_reverse_decimal_row
        (double_reverse_pointed_source_window source origin radius)"
      and digit: "digit < 10"
  shows "bit (double_reverse_bitplane_row_run steps
      (double_reverse_decimal_planes
        (double_reverse_pointed_source_window source origin radius))
      (length (double_reverse_pointed_source_window source origin radius)) ! digit)
      (i + (if even count then 1 else 0)) \<longleftrightarrow>
    double_reverse_ring_digit (double_reverse_ring_inward_run steps motif)
      (i + (if even count then 1 else 0)) = digit"
proof -
  have source_window:
    "length (double_reverse_pointed_source_window source origin radius) =
      2*(steps + count div 2) + 1"
    using radius
    by (simp add: double_reverse_pointed_source_window_length)
  have extracted:
    "double_reverse_source_slp_word
      (double_reverse_source_window_slp source (origin - int radius)
        (2 * radius + 1) middle) =
      double_reverse_pointed_source_window source origin radius"
    by (rule double_reverse_pointed_source_window_slp_exact[OF part])
  have row_matches:
    "double_reverse_row_matches_ring
      (double_reverse_pointed_source_window source origin radius) motif"
    by (rule double_reverse_source_window_certificate_refines_ring
      [OF extracted motif certificate])
  show ?thesis
    by (rule double_reverse_bitplane_window_periodic_ring_exact
      [OF positive source_window index decimal row_matches digit])
qed

ML \<open>
  val checked = @{thms double_reverse_source_phase_cycle_positive
    double_reverse_source_phase_cycle_annihilates
    double_reverse_source_phase_cycle_representative
    double_reverse_source_matches_repeat
    double_reverse_source_slp_phase_certificate_sound
    double_reverse_source_window_fragment_geometry
    double_reverse_source_window_middle_slice_length
    double_reverse_source_window_fragment_word_length
    double_reverse_source_window_fragments_exact
    double_reverse_source_window_slp_has_fragment_word
    double_reverse_source_window_slp_exact
    double_reverse_pointed_source_window_slp_exact
    double_reverse_source_window_certificate_refines_ring
    double_reverse_source_window_bitplane_point_refines_ring};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Double-reverse source-window refinement depends on an oracle";
  val _ = if Thm_Deps.has_skip_proof checked
    then error "Double-reverse source-window refinement contains skip_proof"
    else ();
\<close>

end
