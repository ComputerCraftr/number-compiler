theory Mahler_Continued_Fraction_Refinement
  imports Mahler_Joint_Quotient_Algebra
    "Shared_Carry_Dynamics.Ordered_Matrix_Program_Algebra"
begin

text \<open>A finite ×5 source band is projected from one dyadic lift. The
source admits no temporal extension merely from a matching output digit.\<close>

lemma mahler_cf_scaled_source_remainder:
  fixes source base divisor blocks :: nat
  assumes "divisor > 0"
  shows "(base * (source mod (divisor * blocks)) div divisor) mod base =
    (base * source div divisor) mod base"
proof -
  have decomposition: "source = source mod (divisor * blocks) +
      divisor * blocks * (source div (divisor * blocks))"
    using div_mult_mod_eq[of source "divisor * blocks"]
    by (simp add: algebra_simps)
  have "base * source = base * (source mod (divisor * blocks) +
      divisor * blocks * (source div (divisor * blocks)))"
    by (rule arg_cong[OF decomposition])
  also have "... = base * (source mod (divisor * blocks)) +
      divisor * (base * blocks * (source div (divisor * blocks)))"
    by (simp add: algebra_simps)
  finally have rearranged: "base * source = base * (source mod (divisor * blocks)) +
      divisor * (base * blocks * (source div (divisor * blocks)))" .
  show ?thesis using assms by (subst rearranged) (simp add: mult.assoc)
qed

lemma mahler_cf_lifted_source_row:
  fixes exponent cut rows time width base lift :: nat
  assumes "time < rows"
  defines "base \<equiv> 10^width"
    and "lift \<equiv> (10^width * (5^exponent mod 2^(cut+rows-1))) div 2^cut"
  shows "(lift div 2^time) mod base =
    (base * 5^exponent div 2^(cut+time)) mod base"
proof -
  have positive: "0 < rows" using assms(1) by auto
  have bounded: "time \<le> rows-1" using assms(1) by (cases rows) auto
  have full: "time + (rows-1-time) = rows-1" using bounded by simp
  have split: "cut+rows-1 = cut+(rows-1)"
    using positive by (simp add: Nat.add_diff_assoc)
  have index: "cut+rows-1 = (cut+time)+(rows-1-time)"
    by (simp only: split add.assoc full)
  have product: "2^(cut+rows-1) = (2::nat)^(cut+time) * 2^(rows-1-time)"
    by (simp only: index power_add)
  have valid: "(2::nat)^(cut+time) > 0" by simp
  have equality:
    "(base * (5^exponent mod (2^(cut+time) * 2^(rows-1-time))) div
        2^(cut+time)) mod base =
      (base * 5^exponent div 2^(cut+time)) mod base"
    by (rule mahler_cf_scaled_source_remainder[OF valid])
  show ?thesis using equality product
    by (simp add: lift_def base_def div_mult2_eq[symmetric] power_add[symmetric])
qed

lemma mahler_cf_ten_power:
  "(10::nat)^n = 5^n * 2^n"
proof -
  have "(10::nat) = 5*2" by simp
  then show ?thesis by (simp only: power_mult_distrib)
qed

lemma mahler_cf_physical_row:
  fixes exponent cut rows time width base lift :: nat
  assumes time: "time < rows" and width: "width \<le> cut + time"
  defines "base \<equiv> 10^width"
    and "lift \<equiv> (10^width * (5^exponent mod 2^(cut+rows-1))) div 2^cut"
  shows "(lift div 2^time) mod base =
    (5^(exponent+cut+time) div 10^(cut+time-width)) mod base"
proof -
  have power_decomposition:
    "exponent+cut+time = (cut+time-width)+(width+exponent)"
    using width by arith
  have divisor_decomposition: "cut+time = width + (cut+time-width)"
    using width by arith
  have physical:
    "5^(exponent+cut+time) div 10^(cut+time-width) =
      (5::nat)^(width+exponent) div 2^(cut+time-width)"
    by (simp only: power_decomposition power_add mahler_cf_ten_power;
        simp add: mult.commute)
  have cut_power: "(2::nat)^(cut+time) = 2^width * 2^(cut+time-width)"
    using arg_cong[OF divisor_decomposition, where f="(\<lambda>n. (2::nat)^n)"]
    by (simp only: power_add)
  have dyadic:
    "(10^width * 5^exponent) div 2^(cut+time) =
      (5::nat)^(width+exponent) div 2^(cut+time-width)"
    by (subst cut_power)
      (simp add: power_add mahler_cf_ten_power mult.assoc mult.commute mult.left_commute)
  show ?thesis using mahler_cf_lifted_source_row[
      where exponent=exponent and cut=cut and rows=rows and time=time and width=width]
      time
    by (simp add: base_def lift_def physical dyadic)
qed

lemma mahler_cf_significant_last_cut:
  fixes exponent cut rows :: nat
  assumes "1 \<le> cut" "cut \<le> exponent" "1 \<le> rows"
  shows "10^(cut+rows-2) \<le> (5::nat)^(exponent+rows-1) \<longleftrightarrow>
    2^(cut+rows-2) \<le> (5::nat)^(exponent-cut+1)"
proof -
  have decomposition:
    "exponent+rows-1 = (cut+rows-2)+(exponent-cut+1)"
    using assms by arith
  show ?thesis
    by (simp only: decomposition power_add mahler_cf_ten_power;
        simp add: mult.commute)
qed

lemma mahler_cf_last_cut_covers_all_rows:
  fixes exponent cut rows time :: nat
  assumes cut: "1 \<le> cut" and inside: "time < rows"
    and last: "10^(cut+rows-2) \<le> (5::nat)^(exponent+rows-1)"
  shows "10^(cut+time-1) \<le> (5::nat)^(exponent+time)"
proof -
  let ?rest = "rows-1-time"
  have exponent_decomposition: "exponent+rows-1 = (exponent+time)+?rest"
    using inside by arith
  have cut_decomposition: "cut+rows-2 = (cut+time-1)+?rest"
    using inside cut by arith
  have bound: "(5::nat)^?rest \<le> 10^?rest" by (rule power_mono) simp_all
  have scale: "(5::nat)^(exponent+time) * 5^?rest \<le>
      5^(exponent+time) * 10^?rest"
    by (rule mult_left_mono[OF bound]) simp
  have initial: "10^(cut+time-1) * 10^?rest \<le>
      (5::nat)^(exponent+time) * 5^?rest"
    using last by (simp only: exponent_decomposition cut_decomposition power_add)
  have "10^(cut+time-1) * 10^?rest \<le>
      (5::nat)^(exponent+time) * 10^?rest"
    by (rule order_trans[OF initial scale])
  then show ?thesis by simp
qed

lemma mahler_cf_observed_remainder:
  fixes source divisor factor base :: nat
  assumes positive: "divisor > 0" and divides: "base dvd factor"
  shows "((source mod (divisor*factor)) div divisor) mod base =
    (source div divisor) mod base"
proof -
  have "(source mod (divisor*factor)) div divisor = (source div divisor) mod factor"
    using positive by (simp add: mod_mult2_eq)
  then show ?thesis using mod_mod_cancel[OF divides, of "source div divisor"] by simp
qed

lemma mahler_cf_period_observations:
  fixes source base rows period time :: nat
  assumes positive: "0 < period" and inside: "time < rows-period"
    and equal: "source mod (base * 2^(rows-period-1)) =
      (source div 2^period) mod (base * 2^(rows-period-1))"
  shows "(source div 2^time) mod base =
    (source div 2^(period+time)) mod base"
proof -
  have index: "rows-period-1 = time + (rows-period-1-time)"
    using inside by arith
  have period_power:
    "(2::nat)^(rows-period-1) = 2^time * 2^(rows-period-1-time)"
    using arg_cong[OF index, where f="(\<lambda>n. (2::nat)^n)"]
    by (simp only: power_add)
  have factored:
    "base * (2::nat)^(rows-period-1) =
      2^time * (base * 2^(rows-period-1-time))"
    by (simp only: period_power; simp add: mult.assoc mult.commute)
  have divides: "base dvd base * (2::nat)^(rows-period-1-time)" by simp
  have left: "((source mod (base*2^(rows-period-1))) div 2^time) mod base =
      (source div 2^time) mod base"
    unfolding factored by (rule mahler_cf_observed_remainder[OF _ divides]) simp
  have right_remainder:
    "(((source div 2^period) mod (base*2^(rows-period-1))) div 2^time) mod base =
      ((source div 2^period) div 2^time) mod base"
    unfolding factored by (rule mahler_cf_observed_remainder[OF _ divides]) simp
  have right:
    "(((source div 2^period) mod (base*2^(rows-period-1))) div 2^time) mod base =
      (source div 2^(period+time)) mod base"
    using right_remainder by (simp add: div_mult2_eq power_add)
  show ?thesis using equal left right by simp
qed

lemma mahler_cf_left_child_row:
  fixes source base left time :: nat
  assumes inside: "time < left"
  shows "((source mod (base * 2^(left-1))) div 2^time) mod base =
    (source div 2^time) mod base"
proof -
  have index: "left-1 = time + (left-1-time)" using inside by arith
  have power: "(2::nat)^(left-1) = 2^time * 2^(left-1-time)"
    using arg_cong[OF index, where f="(\<lambda>n. (2::nat)^n)"]
    by (simp only: power_add)
  have factored: "base * (2::nat)^(left-1) =
      2^time * (base * 2^(left-1-time))"
    by (simp only: power; simp add: mult.assoc mult.commute)
  have divides: "base dvd base * (2::nat)^(left-1-time)" by simp
  show ?thesis unfolding factored
    by (rule mahler_cf_observed_remainder[OF _ divides]) simp
qed

lemma mahler_cf_right_child_row:
  fixes source base left time :: nat
  shows "((source div 2^left) div 2^time) mod base =
    (source div 2^(left+time)) mod base"
  by (simp add: div_mult2_eq power_add)

lemma mahler_cf_periodic_index:
  fixes period total index :: nat and f :: "nat \<Rightarrow> 'a"
  assumes positive: "0 < period" and in_range: "index < total"
    and periodic: "\<And>i. i+period < total \<Longrightarrow> f (i+period) = f i"
  shows "f index = f (index mod period)"
  using in_range
proof (induction index rule: less_induct)
  case (less index)
  show ?case
  proof (cases "index < period")
    case True
    then show ?thesis by simp
  next
    case False
    have below: "period \<le> index" using False by simp
    have previous: "index-period < index" using positive below by simp
    have previous_in_range: "index-period < total"
      using less.prems by (meson diff_le_self le_less_trans)
    have step: "index-period+period = index" using below by simp
    have "(index-period) mod period = ((index-period)+period) mod period"
      by simp
    also have "... = index mod period" by (simp only: step)
    finally have rest_mod: "(index-period) mod period = index mod period" .
    have "f index = f (index-period)"
      using periodic[of "index-period"] less.prems step by simp
    also have "... = f ((index-period) mod period)"
      by (rule less.IH[OF previous previous_in_range])
    also have "... = f (index mod period)" by (simp only: rest_mod)
    finally show ?thesis .
  qed
qed

lemma mahler_cf_repeat_length:
  "length (concat (replicate copies word)) = copies * length word"
  by (induction copies) simp_all

lemma mahler_cf_repeat_nth:
  assumes nonempty: "word \<noteq> []" and index: "i < copies * length word"
  shows "(concat (replicate copies word)) ! i = word ! (i mod length word)"
  using index
proof (induction copies arbitrary: i)
  case 0
  then show ?case by simp
next
  case (Suc copies)
  let ?length = "length word"
  have positive: "0 < ?length" using nonempty by simp
  show ?case
  proof (cases "i < ?length")
    case True
    then show ?thesis by (simp add: nth_append)
  next
    case False
    have above: "?length \<le> i" using False by simp
    have smaller: "i-?length < copies * ?length"
      using Suc.prems above by (simp add: less_diff_conv2 add.commute)
    have split: "i-?length + ?length = i" using above by simp
    have "(i-?length) mod ?length = ((i-?length)+?length) mod ?length"
      by simp
    also have "... = i mod ?length" by (simp only: split)
    finally have same_mod: "(i-?length) mod ?length = i mod ?length" .
    show ?thesis using Suc.IH[OF smaller] False same_mod
      by (simp add: nth_append)
  qed
qed

lemma mahler_cf_periodic_list:
  fixes period total :: nat and f :: "nat \<Rightarrow> 'a"
  assumes positive: "0 < period" and period_fits: "period \<le> total"
    and periodic: "\<And>i. i+period < total \<Longrightarrow> f (i+period) = f i"
  shows "map f [0..<total] =
    concat (replicate (total div period) (map f [0..<period])) @
      take (total mod period) (map f [0..<period])"
proof (rule nth_equalityI)
  let ?copies = "total div period"
  let ?tail = "total mod period"
  let ?block = "map f [0..<period]"
  have remainder: "?tail < period" using positive by simp
  have decomposition: "?copies * period + ?tail = total"
    using div_mult_mod_eq[of total period] by simp
  show "length (map f [0..<total]) =
    length (concat (replicate ?copies ?block) @ take ?tail ?block)"
    using remainder decomposition by (simp add: mahler_cf_repeat_length)
next
  fix i
  assume inside: "i < length (map f [0..<total])"
  let ?copies = "total div period"
  let ?tail = "total mod period"
  let ?block = "map f [0..<period]"
  have i_lt: "i < total" using inside by simp
  have remainder: "?tail < period" using positive by simp
  have decomposition: "?copies * period + ?tail = total"
    using div_mult_mod_eq[of total period] by simp
  have residue: "i mod period < period" using positive by simp
  have point: "f i = f (i mod period)"
  proof (rule mahler_cf_periodic_index[where f=f and period=period and total=total])
    show "0 < period" by (rule positive)
    show "i < total" by (rule i_lt)
    fix j
    assume "j+period < total"
    then show "f (j+period) = f j" by (rule periodic)
  qed
  show "(map f [0..<total]) ! i =
    (concat (replicate ?copies ?block) @ take ?tail ?block) ! i"
  proof (cases "i < ?copies * period")
    case True
    have repeated_length:
      "(concat (replicate ?copies ?block)) ! i = ?block ! (i mod length ?block)"
      by (rule mahler_cf_repeat_nth) (use positive True in simp_all)
    have repeated:
      "(concat (replicate ?copies ?block)) ! i = ?block ! (i mod period)"
      using repeated_length by simp
    show ?thesis using True point repeated residue i_lt
      by (simp add: nth_append mahler_cf_repeat_length)
  next
    case False
    have above: "?copies * period \<le> i" using False by simp
    have tail_index: "i - ?copies * period < ?tail"
      using i_lt decomposition above by (simp add: less_diff_conv2 add.commute)
    have tail_below: "i - ?copies * period < period"
      by (rule less_trans[OF tail_index remainder])
    have split: "i - ?copies * period + ?copies * period = i"
      using above by simp
    have "i mod period = (i - ?copies * period + ?copies * period) mod period"
      by (simp only: split)
    also have "... = (i - ?copies * period) mod period" by simp
    also have "... = i - ?copies * period" using tail_below by simp
    finally have residue_tail: "i mod period = i - ?copies * period" .
    show ?thesis using point tail_index tail_below residue_tail above i_lt
      by (simp add: nth_append mahler_cf_repeat_length)
  qed
qed

definition mahler_cf_digit :: "nat \<Rightarrow> nat ordered_matrix2" where
  "mahler_cf_digit digit = Ordered_Matrix2 (digit+1) 1 1 0"

definition mahler_cf_word :: "nat list \<Rightarrow> nat ordered_matrix2" where
  "mahler_cf_word digits = ordered_matrix2_word (rev (map mahler_cf_digit digits))"

lemma mahler_cf_word_append:
  "mahler_cf_word (left @ right) =
    ordered_matrix2_multiply (mahler_cf_word left) (mahler_cf_word right)"
  by (simp add: mahler_cf_word_def ordered_matrix2_word_append)

lemma mahler_cf_word_repeat:
  "mahler_cf_word (concat (replicate count word)) =
    ordered_matrix2_power (mahler_cf_word word) count"
proof (induction count)
  case 0
  then show ?case by (simp add: mahler_cf_word_def)
next
  case (Suc count)
  have "replicate (Suc count) word = replicate count word @ [word]"
    by (simp only: replicate_Suc replicate_append_same)
  then show ?case by (simp add: mahler_cf_word_append Suc.IH)
qed

definition mahler_cf_decimal_digits :: "nat \<Rightarrow> nat \<Rightarrow> nat list" where
  "mahler_cf_decimal_digits width value =
    map (\<lambda>position. value div 10^(width-1-position) mod 10) [0..<width]"

lemma mahler_cf_concat_repeated_rows:
  "concat (concat (replicate copies rows)) =
    concat (replicate copies (concat rows))"
  by (induction copies) simp_all

theorem mahler_cf_band_split_consumer:
  fixes source width left right :: nat
  assumes positive: "0 < left"
  defines "base \<equiv> 10^width"
    and "left_source \<equiv> source mod (10^width * 2^(left-1))"
    and "right_source \<equiv> source div 2^left"
  shows "mahler_cf_word (concat (map (\<lambda>time.
      mahler_cf_decimal_digits width ((source div 2^time) mod base))
        [0..<left+right])) =
    ordered_matrix2_multiply
      (mahler_cf_word (concat (map (\<lambda>time.
        mahler_cf_decimal_digits width ((left_source div 2^time) mod base))
          [0..<left])))
      (mahler_cf_word (concat (map (\<lambda>time.
        mahler_cf_decimal_digits width ((right_source div 2^time) mod base))
          [0..<right])))"
proof -
  let ?full = "\<lambda>time. mahler_cf_decimal_digits width
    ((source div 2^time) mod base)"
  let ?left = "\<lambda>time. mahler_cf_decimal_digits width
    ((left_source div 2^time) mod base)"
  let ?right = "\<lambda>time. mahler_cf_decimal_digits width
    ((right_source div 2^time) mod base)"
  have left_rows: "map ?full [0..<left] = map ?left [0..<left]"
  proof (rule map_cong[OF refl])
    fix time
    assume "time \<in> set [0..<left]"
    then have "time < left" by simp
    then show "?full time = ?left time"
      using mahler_cf_left_child_row[where source=source and base=base
        and left=left and time=time]
      by (simp add: base_def left_source_def)
  qed
  have right_rows: "map ?full [left..<left+right] = map ?right [0..<right]"
  proof -
    have indices: "[left..<left+right] = map (\<lambda>i. i+left) [0..<right]"
      using map_add_upt[of left right] by (simp add: add.commute)
    show ?thesis unfolding indices
      by (simp add: right_source_def mahler_cf_right_child_row add.commute)
  qed
  have source_rows: "map ?full [0..<left+right] =
      map ?left [0..<left] @ map ?right [0..<right]"
    using upt_add_eq_append[of 0 left right] left_rows right_rows by simp
  show ?thesis using source_rows
    by (simp only: concat_append mahler_cf_word_append)
qed

theorem mahler_cf_periodic_band_power:
  fixes source width rows period :: nat
  assumes positive: "0 < period" and fits: "period \<le> rows"
    and equal: "source mod (10^width * 2^(rows-period-1)) =
      (source div 2^period) mod (10^width * 2^(rows-period-1))"
  shows "mahler_cf_word (concat (map (\<lambda>time.
      mahler_cf_decimal_digits width ((source div 2^time) mod 10^width))
        [0..<rows])) =
    ordered_matrix2_multiply
      (ordered_matrix2_power (mahler_cf_word (concat (map (\<lambda>time.
        mahler_cf_decimal_digits width ((source div 2^time) mod 10^width))
        [0..<period]))) (rows div period))
      (mahler_cf_word (concat (take (rows mod period) (map (\<lambda>time.
        mahler_cf_decimal_digits width ((source div 2^time) mod 10^width))
        [0..<period]))))"
proof -
  let ?row = "\<lambda>time. mahler_cf_decimal_digits width
    ((source div 2^time) mod 10^width)"
  have row_period:
    "?row (time+period) = ?row time" if "time+period < rows" for time
  proof -
    have inside: "time < rows-period" using that by arith
    have "(source div 2^time) mod 10^width =
      (source div 2^(period+time)) mod 10^width"
      by (rule mahler_cf_period_observations[OF positive inside equal])
    then show ?thesis by (simp add: add.commute)
  qed
  have sequence:
    "map ?row [0..<rows] =
      concat (replicate (rows div period) (map ?row [0..<period])) @
      take (rows mod period) (map ?row [0..<period])"
    by (rule mahler_cf_periodic_list[OF positive fits]) (rule row_period)
  show ?thesis using sequence
    by (simp only: mahler_cf_concat_repeated_rows concat_append
        mahler_cf_word_append mahler_cf_word_repeat)
qed

theorem mahler_cf_rotated_source_period:
  fixes source width rows period phase :: nat
  assumes positive: "0 < period" and phase: "phase < period"
    and adjoining: "2*period \<le> rows"
    and equal: "source mod (10^width * 2^(rows-period-1)) =
      (source div 2^period) mod (10^width * 2^(rows-period-1))"
  defines "row \<equiv> (\<lambda>time. mahler_cf_decimal_digits width
    ((source div 2^time) mod 10^width))"
  shows "map row [phase..<phase+period] =
    rotate phase (map row [0..<period])"
    "mahler_cf_word (concat (map row [phase..<phase+period])) =
      ordered_matrix2_multiply
        (mahler_cf_word (concat (drop phase (map row [0..<period]))))
        (mahler_cf_word (concat (take phase (map row [0..<period]))))"
proof -
  have source_period: "row (time+period) = row time"
    if "time < period" for time
  proof -
    have inside: "time < rows-period" using that adjoining by arith
    show ?thesis using mahler_cf_period_observations[OF positive inside equal]
      by (simp only: row_def add.commute)
  qed
  have rotated: "map row [phase..<phase+period] =
      rotate phase (map row [0..<period])"
  proof (rule nth_equalityI)
    show "length (map row [phase..<phase+period]) =
      length (rotate phase (map row [0..<period]))" by simp
    fix i assume "i < length (map row [phase..<phase+period])"
    then have i: "i < period" by simp
    have upper: "phase+i < 2*period" using phase i by arith
    have mod_index: "(phase+i) mod period =
        (if phase+i < period then phase+i else phase+i-period)"
    proof (cases "phase+i < period")
      case True
      then show ?thesis by simp
    next
      case False
      have diff: "phase+i-period < period" using upper by arith
      have decomp: "phase+i = period + (phase+i-period)" using False by arith
      have rem: "(phase+i) mod period = phase+i-period"
      proof -
        have "(phase+i) mod period = (period+(phase+i-period)) mod period"
          by (rule arg_cong[OF decomp, where f="\<lambda>x. x mod period"])
        also have "... = (phase+i-period) mod period"
          by (rule mod_add_self1)
        also have "... = phase+i-period" by (rule mod_less[OF diff])
        finally show ?thesis .
      qed
      show ?thesis using False rem by simp
    qed
    have same: "row (phase+i) = row ((phase+i) mod period)"
    proof (cases "phase+i < period")
      case True
      then show ?thesis by (simp add: mod_index)
    next
      case False
      have inner: "phase+i-period < period" using upper by arith
      have shifted: "(phase+i-period)+period = phase+i" using False by arith
      show ?thesis using source_period[OF inner] False
        by (simp add: mod_index shifted)
    qed
    show "map row [phase..<phase+period] ! i =
      rotate phase (map row [0..<period]) ! i"
      using i positive same by (simp add: nth_rotate)
  qed
  show "map row [phase..<phase+period] = rotate phase (map row [0..<period])"
    by (rule rotated)
  show "mahler_cf_word (concat (map row [phase..<phase+period])) =
      ordered_matrix2_multiply
        (mahler_cf_word (concat (drop phase (map row [0..<period]))))
        (mahler_cf_word (concat (take phase (map row [0..<period]))))"
    using rotated phase positive
    by (simp add: rotate_drop_take concat_append mahler_cf_word_append)
qed

theorem mahler_cf_lifted_word_consumer:
  fixes exponent cut rows width lift :: nat
  assumes width: "width \<le> cut"
  defines "lift \<equiv>
    (10^width * (5^exponent mod 2^(cut+rows-1))) div 2^cut"
  shows "mahler_cf_word (concat (map (\<lambda>time.
      mahler_cf_decimal_digits width ((lift div 2^time) mod 10^width)) [0..<rows])) =
    mahler_cf_word (concat (map (\<lambda>time.
      mahler_cf_decimal_digits width
        ((5^(exponent+cut+time) div 10^(cut+time-width)) mod 10^width))
      [0..<rows]))"
proof -
  have equal: "(lift div 2^time) mod 10^width =
    (5^(exponent+cut+time) div 10^(cut+time-width)) mod 10^width"
    if "time < rows" for time
    using mahler_cf_physical_row[where exponent=exponent and cut=cut
      and rows=rows and time=time and width=width] width that
    by (simp add: lift_def)
  have equal_rows:
    "map (\<lambda>time. mahler_cf_decimal_digits width
      ((lift div 2^time) mod 10^width)) [0..<rows] =
     map (\<lambda>time. mahler_cf_decimal_digits width
      ((5^(exponent+cut+time) div 10^(cut+time-width)) mod 10^width)) [0..<rows]"
  proof (rule map_cong[OF refl])
    fix time
    assume "time \<in> set [0..<rows]"
    then have "time < rows" by simp
    then show "mahler_cf_decimal_digits width ((lift div 2^time) mod 10^width) =
      mahler_cf_decimal_digits width
        ((5^(exponent+cut+time) div 10^(cut+time-width)) mod 10^width)"
      using equal by simp
  qed
  show ?thesis by (simp only: equal_rows)
qed

theorem mahler_cf_band_selected_source_refinement:
  fixes exponent cut rows width lift :: nat
  assumes cut: "1 \<le> cut" "cut \<le> exponent"
    and span: "1 \<le> rows" "1 \<le> width" "width \<le> cut"
    and significant: "2^(cut+rows-2) \<le> (5::nat)^(exponent-cut+1)"
  defines "lift \<equiv>
    (10^width * (5^(exponent-cut) mod 2^(cut+rows-1))) div 2^cut"
  shows "mahler_cf_word (concat (map (\<lambda>time.
      mahler_cf_decimal_digits width ((lift div 2^time) mod 10^width)) [0..<rows])) =
    mahler_cf_word (concat (map (\<lambda>time.
      mahler_cf_decimal_digits width
        ((5^(exponent+time) div 10^(cut+time-width)) mod 10^width))
      [0..<rows]))"
    and "\<forall>time<rows. 10^(cut+time-1) \<le> (5::nat)^(exponent+time)"
proof -
  have substituted: "exponent-cut+cut+time = exponent+time" for time
    using cut(2) by arith
  show "mahler_cf_word (concat (map (\<lambda>time.
      mahler_cf_decimal_digits width ((lift div 2^time) mod 10^width)) [0..<rows])) =
    mahler_cf_word (concat (map (\<lambda>time.
      mahler_cf_decimal_digits width
        ((5^(exponent+time) div 10^(cut+time-width)) mod 10^width))
      [0..<rows]))"
    using mahler_cf_lifted_word_consumer[OF span(3),
      where exponent="exponent-cut" and rows=rows] cut
    by (simp add: lift_def substituted)
  have last: "10^(cut+rows-2) \<le> (5::nat)^(exponent+rows-1)"
    using mahler_cf_significant_last_cut[OF cut span(1)] significant by blast
  show "\<forall>time<rows. 10^(cut+time-1) \<le> (5::nat)^(exponent+time)"
    using mahler_cf_last_cut_covers_all_rows[OF cut(1) _ last] by blast
qed

lemma mahler_cf_same_endpoint_lift:
  fixes k width cut rows :: nat
  assumes rows: "2 \<le> rows"
  shows "(10^width * ((5::nat)^k mod 2^((cut+1)+(rows-1)-1))) div 2^(cut+1) =
    ((10^width * (5^k mod 2^(cut+rows-1))) div 2^cut) div 2"
proof -
  have endpoint: "(cut+1)+(rows-1)-1 = cut+rows-1" using rows by arith
  show ?thesis by (simp only: endpoint power_add power_one div_mult2_eq power_one_right)
qed

lemma mahler_cf_same_endpoint_significant_guard:
  fixes k cut rows :: nat
  assumes rows: "2 \<le> rows"
  shows "(2::nat)^((cut+1)+(rows-1)-2) \<le> 5^(k+1) \<longleftrightarrow>
    (2::nat)^(cut+rows-2) \<le> 5^(k+1)"
  using rows by simp

lemma mahler_cf_same_endpoint_physical_guard:
  fixes exponent cut rows :: nat
  assumes rows: "2 \<le> rows"
  shows "10^((cut+1)+(rows-1)-2) \<le> (5::nat)^((exponent+1)+(rows-1)-1) \<longleftrightarrow>
    10^(cut+rows-2) \<le> (5::nat)^(exponent+rows-1)"
proof -
  have c: "(cut+1)+(rows-1)-2 = cut+rows-2" using rows by arith
  have e: "(exponent+1)+(rows-1)-1 = exponent+rows-1" using rows by arith
  show ?thesis by (simp only: c e)
qed

definition mahler_cf_integer_digit :: "nat \<Rightarrow> int ordered_matrix2" where
  "mahler_cf_integer_digit d = Ordered_Matrix2 (int d + 1) 1 1 0"

definition mahler_cf_integer_word :: "nat list \<Rightarrow> int ordered_matrix2" where
  "mahler_cf_integer_word digits = ordered_matrix2_word (rev (map mahler_cf_integer_digit digits))"

fun mahler_cf_integer_determinant :: "int ordered_matrix2 \<Rightarrow> int" where
  "mahler_cf_integer_determinant (Ordered_Matrix2 a b c d) = a*d-b*c"

lemma mahler_cf_integer_determinant_multiply:
  "mahler_cf_integer_determinant (ordered_matrix2_multiply a b) =
    mahler_cf_integer_determinant a * mahler_cf_integer_determinant b"
  by (cases a; cases b) (simp add: algebra_simps)

lemma mahler_cf_integer_word_determinant:
  "mahler_cf_integer_determinant (mahler_cf_integer_word digits) = (-1)^(length digits)"
proof (induction digits)
  case Nil
  then show ?case by (simp add: mahler_cf_integer_word_def ordered_matrix2_identity_def)
next
  case (Cons a digits)
  have row: "mahler_cf_integer_word (a # digits) = ordered_matrix2_multiply (mahler_cf_integer_digit a) (mahler_cf_integer_word digits)"
    by (simp add: mahler_cf_integer_word_def ordered_matrix2_word_append)
  show ?case by (simp add: row mahler_cf_integer_determinant_multiply mahler_cf_integer_digit_def Cons.IH)
qed

definition mahler_cf_integer_adjugate :: "nat \<Rightarrow> int ordered_matrix2 \<Rightarrow> int ordered_matrix2" where
  "mahler_cf_integer_adjugate width matrix = (case matrix of Ordered_Matrix2 a b c d \<Rightarrow>
    Ordered_Matrix2 (((-1)^width)*d) (-(((-1)^width)*b))
      (-(((-1)^width)*c)) (((-1)^width)*a))"

lemma mahler_cf_integer_adjugate_inverse_left:
  assumes width: "length digits = width"
  shows "ordered_matrix2_multiply (mahler_cf_integer_adjugate width (mahler_cf_integer_word digits))
    (mahler_cf_integer_word digits) = ordered_matrix2_identity"
proof -
  obtain a b c d where mat: "mahler_cf_integer_word digits = Ordered_Matrix2 a b c d"
    by (cases "mahler_cf_integer_word digits") auto
  have det: "a*d-b*c = (-1)^width"
    using mahler_cf_integer_word_determinant[of digits] width by (simp only: mat mahler_cf_integer_determinant.simps)
  have square: "((-1::int)^width)^2 = 1"
    by (simp add: power_mult[symmetric])
  have scaled: "(a*d-b*c) * (-1)^width = 1"
    using det square by (simp add: power2_eq_square)
  show ?thesis
    using scaled by (simp add: mat mahler_cf_integer_adjugate_def ordered_matrix2_identity_def algebra_simps; arith)
qed

lemma mahler_cf_integer_word_append:
  "mahler_cf_integer_word (left @ right) = ordered_matrix2_multiply (mahler_cf_integer_word left) (mahler_cf_integer_word right)"
  by (simp add: mahler_cf_integer_word_def ordered_matrix2_word_append)

fun mahler_cf_matrix_to_integer :: "nat ordered_matrix2 \<Rightarrow> int ordered_matrix2" where
  "mahler_cf_matrix_to_integer (Ordered_Matrix2 a b c d) = Ordered_Matrix2 (int a) (int b) (int c) (int d)"

lemma mahler_cf_matrix_to_integer_multiply:
  "mahler_cf_matrix_to_integer (ordered_matrix2_multiply a b) =
    ordered_matrix2_multiply (mahler_cf_matrix_to_integer a) (mahler_cf_matrix_to_integer b)"
  by (cases a; cases b) simp

lemma mahler_cf_matrix_to_integer_word:
  "mahler_cf_matrix_to_integer (ordered_matrix2_word a) = ordered_matrix2_word (map mahler_cf_matrix_to_integer a)"
  by (induction a) (simp_all add: mahler_cf_matrix_to_integer_multiply ordered_matrix2_identity_def)

lemma mahler_cf_natural_word_to_integer:
  "mahler_cf_matrix_to_integer (mahler_cf_word digits) = mahler_cf_integer_word digits"
proof -
  have digit: "mahler_cf_matrix_to_integer (mahler_cf_digit d) = mahler_cf_integer_digit d" for d
    by (simp add: mahler_cf_digit_def mahler_cf_integer_digit_def)
  have digit_comp: "(mahler_cf_matrix_to_integer \<circ> mahler_cf_digit) = mahler_cf_integer_digit"
    by (rule ext) (simp only: comp_apply digit)
  show ?thesis
    by (simp add: mahler_cf_word_def mahler_cf_integer_word_def mahler_cf_matrix_to_integer_word rev_map map_map digit_comp)
qed

lemma mahler_cf_integer_tail_from_word:
  assumes width: "length left = width"
  shows "ordered_matrix2_multiply
      (mahler_cf_integer_adjugate width (mahler_cf_matrix_to_integer (mahler_cf_word left)))
      (mahler_cf_matrix_to_integer (mahler_cf_word (left @ right))) =
    mahler_cf_matrix_to_integer (mahler_cf_word right)"
  using mahler_cf_integer_adjugate_inverse_left[OF width]
  by (simp only: mahler_cf_natural_word_to_integer mahler_cf_integer_word_append
      ordered_matrix2_multiply_associative[symmetric] ordered_matrix2_identity_left)

definition mahler_cf_moving_cut_word :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list" where
  "mahler_cf_moving_cut_word q width rows = concat (map (\<lambda>t.
    mahler_cf_decimal_digits width ((q div 2^t) mod 10^width)) [0..<rows])"

lemma mahler_cf_moving_cut_word_successor:
  "mahler_cf_moving_cut_word q width (Suc rows) =
    mahler_cf_decimal_digits width (q mod 10^width) @ mahler_cf_moving_cut_word (q div 2) width rows"
  by (simp only: mahler_cf_moving_cut_word_def map_upt_Suc concat.simps power_0 div_by_1 power_Suc div_mult2_eq mult.commute)

lemma mahler_cf_moving_cut_word_exact_tail:
  "ordered_matrix2_multiply
      (mahler_cf_integer_adjugate width
        (mahler_cf_matrix_to_integer (mahler_cf_word (mahler_cf_decimal_digits width (q mod 10^width)))))
      (mahler_cf_matrix_to_integer (mahler_cf_word (mahler_cf_moving_cut_word q width (Suc rows)))) =
    mahler_cf_matrix_to_integer (mahler_cf_word (mahler_cf_moving_cut_word (q div 2) width rows))"
  by (simp only: mahler_cf_moving_cut_word_successor
      mahler_cf_integer_tail_from_word[of _ width] mahler_cf_decimal_digits_def length_map length_upt
      diff_zero)

theorem mahler_cf_moving_cut_source_transport:
  fixes exponent cut rows width :: nat
  assumes source: "1 \<le> cut" "cut \<le> exponent" "2 \<le> rows"
    "1 \<le> width" "width \<le> cut"
    and significant: "2^(cut+rows-2) \<le> (5::nat)^(exponent-cut+1)"
  defines "q \<equiv> (10^width * (5^(exponent-cut) mod 2^(cut+rows-1))) div 2^cut"
    and "q_next \<equiv> (10^width * (5^((exponent+1)-(cut+1)) mod
        2^((cut+1)+(rows-1)-1))) div 2^(cut+1)"
  shows "q_next = q div 2"
    and "2^((cut+1)+(rows-1)-2) \<le> (5::nat)^((exponent+1)-(cut+1)+1)"
    and "ordered_matrix2_multiply
      (mahler_cf_integer_adjugate width
        (mahler_cf_matrix_to_integer (mahler_cf_word (mahler_cf_decimal_digits width (q mod 10^width)))))
      (mahler_cf_matrix_to_integer (mahler_cf_word (mahler_cf_moving_cut_word q width rows))) =
    mahler_cf_matrix_to_integer (mahler_cf_word (mahler_cf_moving_cut_word q_next width (rows-1)))"
proof -
  have diff: "(exponent+1)-(cut+1) = exponent-cut" by arith
  show q_shift: "q_next = q div 2"
    using mahler_cf_same_endpoint_lift[where k="exponent-cut" and width=width and cut=cut and rows=rows, OF source(3)]
    by (simp only: q_next_def q_def diff)
  show "2^((cut+1)+(rows-1)-2) \<le> (5::nat)^((exponent+1)-(cut+1)+1)"
    using significant mahler_cf_same_endpoint_significant_guard[where k="exponent-cut" and cut=cut and rows=rows, OF source(3)]
    by (simp only: diff)
  obtain n where rows: "rows = Suc n" using source(3) by (cases rows) auto
  show "ordered_matrix2_multiply
      (mahler_cf_integer_adjugate width
        (mahler_cf_matrix_to_integer (mahler_cf_word (mahler_cf_decimal_digits width (q mod 10^width)))))
      (mahler_cf_matrix_to_integer (mahler_cf_word (mahler_cf_moving_cut_word q width rows))) =
    mahler_cf_matrix_to_integer (mahler_cf_word (mahler_cf_moving_cut_word q_next width (rows-1)))"
    using mahler_cf_moving_cut_word_exact_tail[of width q n] by (simp add: rows q_shift)
qed

theorem mahler_cf_moving_cut_source_prepend:
  fixes exponent cut rows width q q_next low_bit :: nat
  assumes source: "1 \<le> cut" "cut \<le> exponent" "2 \<le> rows"
    "1 \<le> width" "width \<le> cut"
    and significant: "2^(cut+rows-2) \<le> (5::nat)^(exponent-cut+1)"
  defines "q \<equiv> (10^width * (5^(exponent-cut) mod 2^(cut+rows-1))) div 2^cut"
    and "q_next \<equiv> (10^width * (5^(exponent-cut) mod 2^(cut+rows-1))) div 2^(cut+1)"
    and "low_bit \<equiv> (10^width * (5^(exponent-cut) mod 2^(cut+1)) div 2^cut) mod 2"
  shows "q = 2*q_next + low_bit"
    and "mahler_cf_word (mahler_cf_moving_cut_word q width rows) =
      ordered_matrix2_multiply
        (mahler_cf_word (mahler_cf_decimal_digits width (q mod 10^width)))
        (mahler_cf_word (mahler_cf_moving_cut_word q_next width (rows-1)))"
proof -
  have shift: "q_next = q div 2"
    unfolding q_def q_next_def
    by (simp only: power_add power_one div_mult2_eq power_one_right)
  have base_even: "(2::nat) dvd 10^width"
    using source(4) by (cases width) auto
  have qmod: "q mod 10^width =
      (10^width * 5^(exponent-cut) div 2^cut) mod 10^width"
  proof -
    have exponent: "cut + rows - 1 = cut + (rows - 1)" using source(3) by simp
    have "((10::nat)^width * (5^(exponent-cut) mod (2^cut * 2^(rows-1))) div 2^cut) mod 10^width =
        (10^width * 5^(exponent-cut) div 2^cut) mod 10^width"
      by (rule mahler_cf_scaled_source_remainder) simp
    then show ?thesis by (simp only: q_def exponent power_add)
  qed
  have positive: "(2::nat)^cut > 0" by simp
  have lowmod: "((10::nat)^width * (5^(exponent-cut) mod 2^(cut+1)) div 2^cut) mod 10^width =
      (10^width * 5^(exponent-cut) div 2^cut) mod 10^width"
    using mahler_cf_scaled_source_remainder[where divisor="2^cut" and base="10^width"
      and source="5^(exponent-cut)" and blocks=2, OF positive]
    by (simp only: power_add power_one_right)
  have low_bit_eq: "q mod 2 = low_bit"
    using qmod lowmod by (metis low_bit_def mod_mod_cancel[OF base_even])
  show "q = 2*q_next + low_bit"
    using div_mult_mod_eq[of q 2] by (simp add: shift low_bit_eq algebra_simps)
  obtain n where rows: "rows = Suc n" using source(3) by (cases rows) auto
  show "mahler_cf_word (mahler_cf_moving_cut_word q width rows) =
      ordered_matrix2_multiply
        (mahler_cf_word (mahler_cf_decimal_digits width (q mod 10^width)))
        (mahler_cf_word (mahler_cf_moving_cut_word q_next width (rows-1)))"
    by (simp add: rows shift mahler_cf_moving_cut_word_successor mahler_cf_word_append)
qed

text \<open>The finite source cut must be significant at every requested row.
The final-cut inequality is a necessary and sufficient check because the
width deficit can only increase by zero or one at each multiplication.\<close>

ML \<open>
  val checked = @{thms mahler_cf_scaled_source_remainder
    mahler_cf_lifted_source_row mahler_cf_physical_row
    mahler_cf_significant_last_cut mahler_cf_last_cut_covers_all_rows
    mahler_cf_left_child_row mahler_cf_right_child_row mahler_cf_band_split_consumer
    mahler_cf_period_observations
    mahler_cf_word_append mahler_cf_word_repeat mahler_cf_periodic_band_power
    mahler_cf_rotated_source_period
    mahler_cf_lifted_word_consumer
    mahler_cf_band_selected_source_refinement
    mahler_cf_integer_word_determinant mahler_cf_integer_adjugate_inverse_left
    mahler_cf_moving_cut_source_transport mahler_cf_moving_cut_source_prepend};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Mahler CF refinement depends on an oracle";
  val _ = if Thm_Deps.has_skip_proof checked
    then error "Skipped Mahler CF refinement proof" else ();
\<close>

end
