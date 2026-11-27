theory Reflected_Wave_Readout
  imports Reflected_Physical_Parity Reflected_E_Word Reflected_Diagonal_Wave
begin

definition reflected_signed_source :: "nat list \<Rightarrow> int \<Rightarrow> nat" where
  "reflected_signed_source word i =
    (if i < 0 then 0 else reflected_padded_source word (nat i))"

fun reflected_me_word :: "nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat list" where
  "reflected_me_word m 0 source = source"
| "reflected_me_word m (Suc t) source =
    (if even t then reflected_padded_multiply m (reflected_me_word m t source)
     else reflected_padded_E m (reflected_me_word m t source))"

lemma reflected_me_word_decimal:
  assumes m: "m = 2 \<or> m = 5" and digits: "reflected_decimal source"
  shows "reflected_decimal (reflected_me_word m t source)"
  by (induction t) (auto intro: reflected_padded_multiply_decimal[OF m]
      reflected_padded_E_decimal[OF m] digits)

lemma reflected_signed_M:
  assumes m: "m = 2 \<or> m = 5" and digits: "reflected_decimal source"
  shows "reflected_signed_source (reflected_padded_multiply m source) i =
    reflected_alternating_gate m 0 (reflected_signed_source source (i - 1))
      (reflected_signed_source source i)"
proof (cases "i < 0")
  case True
  then show ?thesis
    by (simp add: reflected_signed_source_def reflected_alternating_gate_def)
next
  case False
  note nonnegative = False
  show ?thesis
  proof (cases "i = 0")
    case True
    show ?thesis using reflected_padded_multiply_M_source[OF m digits, of 0] True
      by (simp add: reflected_signed_source_def reflected_alternating_gate_def
          reflected_M_digit_def reflected_previous_def)
  next
    case False
    have pos: "0 < i" using nonnegative False by simp
    have index: "nat (i - 1) = nat i - 1" using pos by (simp add: nat_diff_distrib)
    have nonzero: "nat i \<noteq> 0" using pos by simp
    show ?thesis using reflected_padded_multiply_M_source[OF m digits, of "nat i"] pos index nonzero
      by (simp add: reflected_signed_source_def reflected_alternating_gate_def
          reflected_M_digit_def reflected_previous_def)
  qed
qed

lemma reflected_signed_E:
  assumes m: "m = 2 \<or> m = 5" and digits: "reflected_decimal source"
  shows "reflected_signed_source (reflected_padded_E m source) i =
    reflected_alternating_gate m 1 (reflected_signed_source source (i - 1))
      (reflected_signed_source source i)"
proof (cases "i < 0")
  case True
  then show ?thesis
    by (simp add: reflected_signed_source_def reflected_alternating_gate_def)
next
  case False
  note nonnegative = False
  show ?thesis
  proof (cases "i = 0")
    case True
    show ?thesis using reflected_padded_E_source_digit[OF m digits, of 0] True
      by (simp add: reflected_signed_source_def reflected_alternating_gate_def
          reflected_E_digit_def reflected_previous_def)
  next
    case False
    have pos: "0 < i" using nonnegative False by simp
    have index: "nat (i - 1) = nat i - 1" using pos by (simp add: nat_diff_distrib)
    have nonzero: "nat i \<noteq> 0" using pos by simp
    show ?thesis using reflected_padded_E_source_digit[OF m digits, of "nat i"] pos index nonzero
      by (simp add: reflected_signed_source_def reflected_alternating_gate_def
          reflected_E_digit_def reflected_previous_def)
  qed
qed

theorem reflected_single_run_me_word:
  assumes m: "m = 2 \<or> m = 5" and digits: "reflected_decimal source"
  shows "reflected_single_run (reflected_alternating_gate m) t
      (reflected_signed_source source) i = reflected_signed_source (reflected_me_word m t source) i"
proof (induction t arbitrary: i)
  case 0
  then show ?case by simp
next
  case (Suc t)
  have valid: "reflected_decimal (reflected_me_word m t source)"
    by (rule reflected_me_word_decimal[OF m digits])
  show ?case using Suc.IH[of "i - 1"] Suc.IH[of i]
    reflected_signed_M[OF m valid, of i] reflected_signed_E[OF m valid, of i]
    by (cases "even t") (simp_all add: reflected_alternating_gate_def)
qed

lemma reflected_me_word_even:
  "reflected_me_word m (2*k) source = reflected_padded_H_iter m k source"
  by (induction k) (simp_all add: reflected_padded_H_def)

lemma reflected_me_word_odd:
  "reflected_me_word m (2*k+1) source =
    reflected_padded_multiply m (reflected_padded_H_iter m k source)"
  by (simp add: reflected_me_word_even)

theorem reflected_wave_odd_physical:
  assumes m: "m=2 \<or> m=5" and digits: "reflected_decimal seed"
    and canonical: "reflected_trim_high seed = seed"
  shows "(reflected_physical_word m ^^ (2*k+1)) seed =
    reflected_emit m (reflected_me_word m (2*k) (rev seed))"
  using reflected_odd_endpoint[OF m digits canonical, of k]
  by (simp only: reflected_me_word_even)

theorem reflected_wave_even_physical:
  assumes m: "m=2 \<or> m=5" and digits: "reflected_decimal seed"
  shows "(reflected_physical_word m ^^ (2*k+2)) seed =
    reflected_emit m (reflected_me_word m (2*k) (reflected_padded_E m seed))"
  using reflected_even_endpoint[OF m digits, of k]
  by (simp only: reflected_me_word_even)

definition reflected_wave_trim :: "nat list \<Rightarrow> nat list" where
  "reflected_wave_trim raw = rev (dropWhile ((=) 0) (rev (dropWhile ((=) 0) raw)))"

definition reflected_wave_oriented :: "nat \<Rightarrow> nat list \<Rightarrow> nat list" where
  "reflected_wave_oriented ticks raw =
    (if odd ticks then rev (reflected_wave_trim raw) else reflected_wave_trim raw)"

definition reflected_wave_physical_readout :: "nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat list" where
  "reflected_wave_physical_readout m ticks raw =
    (let core = reflected_wave_oriented ticks raw in
      if core = [] then [0]
      else if last core mod m \<noteq> 0 then core @ [0] else core)"

lemma reflected_msf_append_zero:
  "reflected_msf_value (word @ [0]) = 10 * reflected_msf_value word"
  by (simp add: reflected_msf_value_def)

lemma reflected_msf_mod_last:
  assumes m: "m = 2 \<or> m = 5" and nonempty: "word \<noteq> []"
  shows "reflected_msf_value word mod m = last word mod m"
proof -
  obtain prefix digit where word: "word = prefix @ [digit]"
    using nonempty by (cases word rule: rev_cases) auto
  have divisor: "m dvd (10::nat)" using m by auto
  have product: "m dvd 10 * decimal_lsd_value (rev prefix)"
    by (rule dvd_mult2[OF divisor])
  have zero: "(10 * decimal_lsd_value (rev prefix)) mod m = 0"
    using product by (simp only: dvd_eq_mod_eq_0)
  have rest: "(digit + 10 * decimal_lsd_value (rev prefix)) mod m = digit mod m"
    using mod_add_right_eq[of digit "10 * decimal_lsd_value (rev prefix)" m] zero by simp
  show ?thesis using rest by (simp add: word reflected_msf_value_def)
qed

lemma reflected_wave_readout_value:
  assumes m: "m = 2 \<or> m = 5"
    and nonempty: "reflected_wave_oriented ticks raw \<noteq> []"
  defines "core \<equiv> reflected_msf_value (reflected_wave_oriented ticks raw)"
  shows "reflected_msf_value (reflected_wave_physical_readout m ticks raw) =
    (if m dvd core then core else 10 * core)"
  using reflected_msf_mod_last[OF m nonempty] nonempty
  by (simp add: reflected_wave_physical_readout_def core_def Let_def dvd_eq_mod_eq_0
      reflected_msf_append_zero)

theorem reflected_wave_readout_restores:
  assumes m: "m = 2 \<or> m = 5" and last: "\<not> 10 dvd reversed"
    and nonempty: "reflected_wave_oriented ticks raw \<noteq> []"
    and core: "reflected_msf_value (reflected_wave_oriented ticks raw) =
      (if 10 dvd m * reversed then (m * reversed) div 10 else m * reversed)"
  shows "reflected_msf_value (reflected_wave_physical_readout m ticks raw) = m * reversed"
proof -
  have restore: "m * reversed =
    (if m dvd (if 10 dvd m * reversed then (m * reversed) div 10 else m * reversed)
      then (if 10 dvd m * reversed then (m * reversed) div 10 else m * reversed)
      else 10 * (if 10 dvd m * reversed then (m * reversed) div 10 else m * reversed))"
    by (rule diagonal_table_trailing_zero(1)[OF m last])
  have observed: "reflected_msf_value (reflected_wave_physical_readout m ticks raw) =
    (if m dvd reflected_msf_value (reflected_wave_oriented ticks raw)
      then reflected_msf_value (reflected_wave_oriented ticks raw)
      else 10 * reflected_msf_value (reflected_wave_oriented ticks raw))"
    by (rule reflected_wave_readout_value[OF m nonempty])
  show ?thesis using observed restore by (simp only: core)
qed

lemma reflected_wave_readout_all_zero:
  "reflected_wave_oriented ticks raw = [] \<Longrightarrow>
    reflected_wave_physical_readout m ticks raw = [0]"
  by (simp add: reflected_wave_physical_readout_def Let_def)

lemma reflected_readout_pad_decimal:
  "reflected_pad_equiv x y \<Longrightarrow> reflected_decimal x \<and> reflected_decimal y"
  by (induction rule: reflected_pad_equiv.induct) (auto simp: list_all_iff)

lemma reflected_wave_padding_equiv:
  assumes m: "m=2 \<or> m=5" and digits: "reflected_decimal seed"
  shows "reflected_pad_equiv (reflected_me_word m t (rev seed))
    (if even t then rev ((reflected_physical_word m ^^ t) seed)
     else (reflected_physical_word m ^^ t) seed)"
proof (induction t)
  case 0
  then show ?case using digits by (simp add: reflected_pad_equiv.same)
next
  case (Suc t)
  let ?p = "(reflected_physical_word m ^^ t) seed"
  let ?next = "reflected_padded_multiply m (rev ?p)"
  have valid: "reflected_decimal ?p"
    using reflected_readout_pad_decimal[OF Suc.IH]
    by (cases "even t") (auto simp: list_all_iff)
  have next_valid: "reflected_decimal ?next"
    by (rule reflected_padded_multiply_decimal[OF m]) (use valid in simp)
  have trim: "reflected_pad_equiv ?next (reflected_trim_high ?next)"
    by (rule reflected_pad_equiv.symmetric[OF reflected_pad_trim_high[OF next_valid]])
  show ?case
  proof (cases "even t")
    case True
    have eq: "reflected_pad_equiv (reflected_me_word m t (rev seed)) (rev ?p)"
      using Suc.IH True by simp
    have mul: "reflected_pad_equiv
      (reflected_padded_multiply m (reflected_me_word m t (rev seed))) ?next"
      by (rule reflected_pad_multiply[OF m eq])
    show ?thesis using reflected_pad_equiv.compose[OF mul trim] True
      by (simp add: funpow_Suc_right reflected_physical_word_def)
  next
    case False
    have eq: "reflected_pad_equiv (reflected_me_word m t (rev seed)) ?p"
      using Suc.IH False by simp
    have mul: "reflected_pad_equiv
      (reflected_padded_E m (reflected_me_word m t (rev seed))) (rev ?next)"
      unfolding reflected_padded_E_def
      by (rule reflected_pad_reverse[OF reflected_pad_multiply[OF m reflected_pad_reverse[OF eq]]])
    have rtrim: "reflected_pad_equiv (rev ?next) (rev (reflected_trim_high ?next))"
      by (rule reflected_pad_reverse[OF trim])
    show ?thesis using reflected_pad_equiv.compose[OF mul rtrim] False
      by (simp add: funpow_Suc_right reflected_physical_word_def)
  qed
qed

lemma reflected_wave_trim_low_zero [simp]:
  "reflected_wave_trim (0 # word) = reflected_wave_trim word"
  by (simp add: reflected_wave_trim_def)

lemma reflected_wave_trim_high_zero [simp]:
  "reflected_wave_trim (word @ [0]) = reflected_wave_trim word"
  by (induction word) (auto simp: reflected_wave_trim_def)

lemma reflected_wave_trim_padding:
  "reflected_pad_equiv x y \<Longrightarrow> reflected_wave_trim x = reflected_wave_trim y"
  by (induction rule: reflected_pad_equiv.induct) auto

theorem reflected_wave_physical_core:
  assumes "m=2 \<or> m=5" "reflected_decimal seed"
  shows "reflected_wave_oriented t (reflected_me_word m t (rev seed)) =
    (if odd t then rev (reflected_wave_trim ((reflected_physical_word m ^^ t) seed))
     else reflected_wave_trim (rev ((reflected_physical_word m ^^ t) seed)))"
  using reflected_wave_trim_padding[OF reflected_wave_padding_equiv[OF assms, of t]]
  by (cases "even t") (simp_all add: reflected_wave_oriented_def)

lemma reflected_wave_trim_value:
  "decimal_lsd_value (reflected_wave_trim word) =
    decimal_lsd_value (reflected_trim_low word)"
  by (simp only: reflected_wave_trim_def reflected_trim_low_def
      reflected_trim_high_def[symmetric] reflected_trim_high_value)

lemma reflected_wave_oriented_physical_value:
  assumes canonical: "reflected_trim_high word = word"
  shows "reflected_msf_value
    (if odd t then rev (reflected_wave_trim word)
      else reflected_wave_trim (rev word)) =
    decimal_lsd_value (reflected_trim_low word)"
proof (cases "odd t")
  case True
  then show ?thesis by (simp add: reflected_msf_value_def reflected_wave_trim_value)
next
  case False
  have trim: "dropWhile ((=) 0) (rev word) = rev word"
    using arg_cong[where f=rev, OF canonical] by (simp add: reflected_trim_high_def)
  show ?thesis using False trim
    by (simp add: reflected_msf_value_def reflected_wave_trim_def reflected_trim_low_def)
qed

lemma reflected_trim_low_one_zero:
  assumes digits: "reflected_decimal word"
    and positive: "0 < decimal_lsd_value word"
    and no_two: "\<not> 100 dvd decimal_lsd_value word"
  shows "decimal_lsd_value (reflected_trim_low word) =
    (if 10 dvd decimal_lsd_value word then decimal_lsd_value word div 10
     else decimal_lsd_value word)"
proof (cases word)
  case Nil
  with positive show ?thesis by simp
next
  case (Cons digit rest)
  note word = Cons
  have bound: "digit < 10" using digits Cons by simp
  show ?thesis
  proof (cases "digit = 0")
    case False
    have positive_digit: "0 < digit" using False by simp
    have not_dvd: "\<not> 10 dvd digit"
      using bound positive_digit by (meson dvd_imp_le less_irrefl less_le_trans)
    show ?thesis using Cons False not_dvd
      by (simp add: reflected_trim_low_def algebra_simps)
  next
    case True
    show ?thesis
    proof (cases rest)
      case Nil
      with word True positive show ?thesis by simp
    next
      case (Cons digit2 tail)
      have next_nonzero: "digit2 \<noteq> 0"
      proof
        assume "digit2 = 0"
        with no_two word Cons True show False
          by (simp add: algebra_simps)
      qed
      show ?thesis using word Cons True next_nonzero
        by (simp add: reflected_trim_low_def)
    qed
  qed
qed

lemma reflected_physical_at_most_one_zero:
  fixes m reversed :: nat
  assumes m: "m = 2 \<or> m = 5" and last: "\<not> 10 dvd reversed"
  shows "\<not> 100 dvd m * reversed"
proof
  assume "100 dvd m * reversed"
  then obtain k where eq: "m * reversed = 100 * k" unfolding dvd_def by blast
  show False
  proof (cases "m = 2")
    case True
    then have "reversed = 50 * k" using eq by arith
    then show False using last by simp
  next
    case False
    then have "m = 5" using m by simp
    then have "reversed = 20 * k" using eq by arith
    then show False using last by simp
  qed
qed

theorem reflected_wave_core_quotient:
  fixes m reversed :: nat
  assumes m: "m=2 \<or> m=5" and digits: "reflected_decimal seed"
    and canonical: "reflected_trim_high ((reflected_physical_word m ^^ t) seed) =
      (reflected_physical_word m ^^ t) seed"
    and last: "\<not> 10 dvd reversed"
    and physical: "decimal_lsd_value ((reflected_physical_word m ^^ t) seed) = m * reversed"
  shows "reflected_msf_value (reflected_wave_oriented t (reflected_me_word m t (rev seed))) =
    (if 10 dvd m * reversed then (m * reversed) div 10 else m * reversed)"
proof -
  let ?p = "(reflected_physical_word m ^^ t) seed"
  have valid: "reflected_decimal ?p"
    using reflected_readout_pad_decimal[OF reflected_wave_padding_equiv[OF m digits, of t]]
    by (cases "even t") (auto simp: list_all_iff)
  have positive_reversed: "0 < reversed" using last by (cases reversed) simp_all
  have positive: "0 < decimal_lsd_value ?p" using physical m positive_reversed by auto
  have no_two: "\<not> 100 dvd decimal_lsd_value ?p"
    using reflected_physical_at_most_one_zero[OF m last] physical by simp
  have relation: "reflected_msf_value (reflected_wave_oriented t (reflected_me_word m t (rev seed))) =
    decimal_lsd_value (reflected_trim_low ?p)"
    using reflected_wave_physical_core[OF m digits, of t]
      reflected_wave_oriented_physical_value[OF canonical, of t] by simp
  show ?thesis using relation reflected_trim_low_one_zero[OF valid positive no_two] physical by simp
qed

theorem reflected_wave_positive_readout:
  fixes m reversed :: nat
  assumes m: "m=2 \<or> m=5" and digits: "reflected_decimal seed"
    and canonical: "reflected_trim_high ((reflected_physical_word m ^^ t) seed) =
      (reflected_physical_word m ^^ t) seed"
    and last: "\<not> 10 dvd reversed"
    and physical: "decimal_lsd_value ((reflected_physical_word m ^^ t) seed) = m * reversed"
  shows "reflected_msf_value (reflected_wave_physical_readout m t (reflected_me_word m t (rev seed))) = m * reversed"
proof -
  have core: "reflected_msf_value (reflected_wave_oriented t (reflected_me_word m t (rev seed))) =
    (if 10 dvd m * reversed then (m * reversed) div 10 else m * reversed)"
    by (rule reflected_wave_core_quotient[OF m digits canonical last physical])
  have pos: "0 < reversed" using last by (cases reversed) simp_all
  have physical_pos: "0 < m * reversed" using m pos by auto
  have quotient_pos: "0 < (if 10 dvd m * reversed then (m * reversed) div 10 else m * reversed)"
  proof (cases "10 dvd m * reversed")
    case True
    then have "10 \<le> m * reversed" using physical_pos by (rule dvd_imp_le)
    then show ?thesis using True by simp
  next
    case False
    then show ?thesis using physical_pos by simp
  qed
  have nonempty: "reflected_wave_oriented t (reflected_me_word m t (rev seed)) \<noteq> []"
    using core quotient_pos by (auto simp: reflected_msf_value_def)
  show ?thesis by (rule reflected_wave_readout_restores[OF m last nonempty core])
qed

lemma reflected_zero_value_digits:
  "decimal_lsd_value word = 0 \<Longrightarrow> list_all ((=) 0) word"
  by (induction word) auto

lemma reflected_wave_trim_all_zero:
  "list_all ((=) 0) word \<Longrightarrow> reflected_wave_trim word = []"
  by (induction word) (auto simp: reflected_wave_trim_def)

theorem reflected_wave_zero_readout:
  assumes m: "m=2 \<or> m=5" and digits: "reflected_decimal seed"
    and zero: "decimal_lsd_value ((reflected_physical_word m ^^ t) seed) = 0"
  shows "reflected_msf_value (reflected_wave_physical_readout m t (reflected_me_word m t (rev seed))) = 0"
proof -
  let ?p = "(reflected_physical_word m ^^ t) seed"
  have allzero: "list_all ((=) 0) ?p" by (rule reflected_zero_value_digits[OF zero])
  have trim: "reflected_wave_trim ?p = []" by (rule reflected_wave_trim_all_zero[OF allzero])
  have rtrim: "reflected_wave_trim (rev ?p) = []"
    by (rule reflected_wave_trim_all_zero) (use allzero in simp)
  have empty: "reflected_wave_oriented t (reflected_me_word m t (rev seed)) = []"
    using reflected_wave_physical_core[OF m digits, of t] trim rtrim by simp
  show ?thesis using reflected_wave_readout_all_zero[OF empty] by (simp add: reflected_msf_value_def)
qed

lemma reflected_msf_mod_ten_last:
  assumes "word \<noteq> []"
  shows "reflected_msf_value word mod 10 = last word mod 10"
proof -
  obtain prefix digit where word: "word = prefix @ [digit]"
    using assms by (cases word rule: rev_cases) auto
  show ?thesis by (simp add: word reflected_msf_value_def)
qed

lemma reflected_canonical_msf_not_ten:
  assumes valid: "reflected_decimal word" and canonical: "reflected_trim_high word = word"
    and nonempty: "word \<noteq> []"
  shows "\<not> 10 dvd reflected_msf_value word"
proof -
  have trim: "dropWhile ((=) 0) (rev word) = rev word"
    using arg_cong[where f=rev, OF canonical] by (simp add: reflected_trim_high_def)
  have positive: "last word > 0"
    using trim nonempty by (simp add: dropWhile_eq_self_iff hd_rev)
  have lt: "last word < 10"
    using valid nonempty by (auto simp: list_all_iff dest: last_in_set)
  show ?thesis using reflected_msf_mod_ten_last[OF nonempty] positive lt
    by (simp add: dvd_eq_mod_eq_0)
qed

theorem reflected_wave_source_readout:
  assumes m: "m=2 \<or> m=5" and digits: "reflected_decimal seed"
    and initial: "reflected_trim_high seed = seed"
  shows "reflected_msf_value (reflected_wave_physical_readout m (Suc t)
      (reflected_me_word m (Suc t) (rev seed))) =
    decimal_lsd_value ((reflected_physical_word m ^^ (Suc t)) seed)"
proof -
  let ?prev = "(reflected_physical_word m ^^ t) seed"
  let ?next = "(reflected_physical_word m ^^ (Suc t)) seed"
  have prev_valid: "reflected_decimal ?prev"
    using reflected_readout_pad_decimal[OF reflected_wave_padding_equiv[OF m digits, of t]]
    by (cases "even t") (auto simp: list_all_iff)
  have prev_canonical: "reflected_trim_high ?prev = ?prev"
  proof (cases t)
    case 0
    then show ?thesis using initial by simp
  next
    case (Suc k)
    then show ?thesis by (simp add: funpow_Suc_right reflected_trim_high_def reflected_physical_word_def)
  qed
  have next_canonical: "reflected_trim_high ?next = ?next"
    by (simp add: funpow_Suc_right reflected_trim_high_def reflected_physical_word_def)
  have next_value: "decimal_lsd_value ?next = m * reflected_msf_value ?prev"
    by (simp add: funpow_Suc_right reflected_physical_word_value)
  show ?thesis
  proof (cases "?prev = []")
    case True
    then have zero: "decimal_lsd_value ?next = 0"
      using next_value by (simp add: reflected_msf_value_def)
    show ?thesis using reflected_wave_zero_readout[OF m digits zero] zero by simp
  next
    case False
    have not_ten: "\<not> 10 dvd reflected_msf_value ?prev"
      by (rule reflected_canonical_msf_not_ten[OF prev_valid prev_canonical False])
    show ?thesis using reflected_wave_positive_readout[OF m digits next_canonical not_ten next_value]
      next_value by simp
  qed
qed


lemma reflected_me_word_length:
  "length (reflected_me_word m t source) = length source + t"
  by (induction t) (simp_all add: reflected_padded_E_def reflected_padded_multiply_length)

theorem reflected_fringe_word_readout:
  fixes grid :: "int \<Rightarrow> int \<Rightarrow> nat"
  assumes m: "m=2 \<or> m=5" and digits: "reflected_decimal seed"
    and canonical: "reflected_trim_high seed = seed"
    and inlet: "\<And>i. grid i (s-i) = reflected_signed_source (rev seed) i"
    and step: "\<And>u v. s<u+v \<Longrightarrow> u+v\<le>s+int (Suc t) \<Longrightarrow>
      grid u v = reflected_alternating_gate m (nat (u+v-s-1))
        (grid (u-1) v) (grid u (v-1))"
  defines "raw \<equiv> map (\<lambda>i. grid (int i) (s+int (Suc t)-int i))
    [0..<length (reflected_me_word m (Suc t) (rev seed))]"
  shows "reflected_msf_value (reflected_wave_physical_readout m (Suc t) raw) =
    decimal_lsd_value ((reflected_physical_word m ^^ (Suc t)) seed)"
proof -
  let ?word = "reflected_me_word m (Suc t) (rev seed)"
  have exact: "raw = ?word"
  proof (rule nth_equalityI)
    show "length raw = length ?word" by (simp add: raw_def)
    fix i assume i: "i < length raw"
    have bound: "i < length ?word" using i by (simp add: raw_def)
    have grid: "grid (int i) (s + int (Suc t) - int i) =
      reflected_single_run (reflected_alternating_gate m) (Suc t)
        (reflected_signed_source (rev seed)) (int i)"
      by (rule diagonal_fringe_local_refinement[OF inlet step])
    have source: "reflected_single_run (reflected_alternating_gate m) (Suc t)
        (reflected_signed_source (rev seed)) (int i) = ?word ! i"
      using reflected_single_run_me_word[OF m, of "rev seed" "Suc t" "int i"] digits bound
      by (simp add: reflected_signed_source_def reflected_padded_source_def list_all_iff)
    show "raw ! i = ?word ! i" using grid source bound by (simp add: raw_def)
  qed
  show ?thesis using reflected_wave_source_readout[OF m digits canonical, of t] exact by simp
qed

ML \<open>
  val checked = @{thms reflected_single_run_me_word reflected_wave_odd_physical reflected_wave_even_physical reflected_wave_readout_restores reflected_wave_readout_all_zero reflected_wave_padding_equiv reflected_wave_physical_core reflected_wave_oriented_physical_value reflected_trim_low_one_zero reflected_physical_at_most_one_zero reflected_wave_core_quotient reflected_wave_positive_readout reflected_wave_zero_readout reflected_wave_source_readout reflected_me_word_length reflected_fringe_word_readout};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Reflected wave readout depends on an oracle";
  val _ = if Thm_Deps.has_skip_proof checked
    then error "Skipped reflected wave readout proof" else ();
\<close>

end
