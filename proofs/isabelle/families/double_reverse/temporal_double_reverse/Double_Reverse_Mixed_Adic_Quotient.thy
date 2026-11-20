theory Double_Reverse_Mixed_Adic_Quotient
  imports Double_Reverse_Powered_Border_Transfer
    Double_Reverse_Four_Port_Numeric_Refinement
begin

declare decimal_reverse.simps[simp del]
declare decimal_digit_count.simps[simp del]

text \<open>
The outer two-cell border is closed for either inward carry.  This theory
proves the residue quotient for the abstract physical clock attached to that
border.  The quotient concerns the physical residue modulo 99 and the
four-phase, width-growth clock.  It does not encode interior carry words.
\<close>

definition double_reverse_outer_growth :: "nat \<Rightarrow> nat" where
  "double_reverse_outer_growth phase =
    (if phase mod 4 = 0 \<or> phase mod 4 = 3 then 1 else 0)"

definition double_reverse_mixed_residue_step ::
    "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<times> nat \<times> nat" where
  "double_reverse_mixed_residue_step phase width_parity residue =
    ((phase + 1) mod 4,
     (width_parity + double_reverse_outer_growth phase) mod 2,
     ((if width_parity mod 2 = 0 then 20 else 2) * residue) mod 99)"

fun double_reverse_mixed_residue_run ::
    "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<times> nat \<times> nat" where
  "double_reverse_mixed_residue_run 0 phase width_parity residue =
    (phase mod 4, width_parity mod 2, residue mod 99)"
| "double_reverse_mixed_residue_run (Suc ticks) phase width_parity residue =
    (case double_reverse_mixed_residue_step phase width_parity residue of
      (next_phase, next_width_parity, next_residue) \<Rightarrow>
        double_reverse_mixed_residue_run ticks next_phase
          next_width_parity next_residue)"

definition double_reverse_mixed_residue_class ::
    "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<times> nat \<times> nat option" where
  "double_reverse_mixed_residue_class phase width_parity residue =
    (phase mod 4, residue mod 99,
      if residue mod 11 = 0 then None else Some (width_parity mod 2))"

lemma double_reverse_ten_power_mod99_parity:
  "(10::nat)^exponent mod 99 = (if even exponent then 1 else 10)"
proof (induction exponent)
  case 0
  then show ?case by simp
next
  case (Suc exponent)
  have power_product:
    "(10::nat) ^ Suc exponent mod 99 =
      (10 * ((10::nat) ^ exponent mod 99)) mod 99"
    by (simp add: power_Suc mod_mult_right_eq mult.commute)
  have ten_residue: "(10::nat) mod 99 = 10 mod 99" by simp
  have prior_power_residue:
    "((10::nat) ^ exponent mod 99) mod 99 =
      (if even exponent then 1 else 10) mod 99"
    using Suc.IH by simp
  have product_residue:
    "(10 * ((10::nat) ^ exponent mod 99)) mod 99 =
      (10 * (if even exponent then 1 else 10)) mod 99"
    by (rule mod_mult_cong[OF ten_residue prior_power_residue])
  have step:
    "(10::nat) ^ Suc exponent mod 99 =
      (10 * ((10::nat) ^ exponent mod 99)) mod 99"
    by (rule power_product)
  show ?case using step product_residue
    by (cases "even exponent") simp_all
qed

lemma decimal_reverse_mod99_width_parity:
  "decimal_reverse source mod 99 =
    ((if even (decimal_digit_count source) then 10 else 1) * source) mod 99"
proof (induction source rule: less_induct)
  case (less source)
  show ?case
  proof (cases "source < 10")
    case True
    then show ?thesis by (simp add: decimal_reverse.simps decimal_digit_count.simps)
  next
    case False
    let ?quotient = "source div 10"
    let ?digit = "source mod 10"
    have quotient_less: "?quotient < source"
      using False by simp
    have quotient_width:
      "decimal_digit_count source = Suc (decimal_digit_count ?quotient)"
      using False by (simp add: decimal_digit_count.simps)
    have quotient_reversal:
      "decimal_reverse ?quotient mod 99 =
        ((if even (decimal_digit_count ?quotient) then 10 else 1) *
          ?quotient) mod 99"
      by (rule less.IH[OF quotient_less])
    have power:
      "(10::nat)^(decimal_digit_count source - 1) mod 99 =
        (if even (decimal_digit_count ?quotient) then 1 else 10)"
      using quotient_width
      by (simp add: double_reverse_ten_power_mod99_parity)
    have source_split: "source = 10 * ?quotient + ?digit"
      using div_mult_mod_eq[of source 10] by (simp add: mult.commute)
    have reverse_step:
      "decimal_reverse source =
        ?digit * 10^(decimal_digit_count source - 1) +
          decimal_reverse ?quotient"
      using False by (simp add: decimal_reverse.simps)
    have digit_mod:
      "(?digit * 10^(decimal_digit_count source - 1)) mod 99 =
        (?digit * (if even (decimal_digit_count ?quotient) then 1 else 10)) mod 99"
    proof -
      have digit_residue: "?digit mod 99 = ?digit mod 99" by simp
      have power_residue:
        "(10::nat)^(decimal_digit_count source - 1) mod (99::nat) =
          (if even (decimal_digit_count ?quotient) then (1::nat) else 10) mod (99::nat)"
      proof -
        have factor_bound:
          "(if even (decimal_digit_count ?quotient) then (1::nat) else 10) < 99"
          by (cases "even (decimal_digit_count ?quotient)") simp_all
        show ?thesis using power factor_bound
          by (simp only: power mod_less)
      qed
      show ?thesis
        by (rule mod_mult_cong[OF digit_residue power_residue])
    qed
    have odd_width:
      "even (decimal_digit_count ?quotient) \<Longrightarrow>
        decimal_reverse source mod 99 = (10 * ?quotient + ?digit) mod 99"
    proof -
      assume quotient_even: "even (decimal_digit_count ?quotient)"
      have digit:
        "(?digit * 10^(decimal_digit_count source - 1)) mod 99 = ?digit mod 99"
        using digit_mod quotient_even by simp
      have rest:
        "decimal_reverse ?quotient mod 99 = (10 * ?quotient) mod 99"
        using quotient_reversal quotient_even by simp
      have joined:
        "(?digit * 10^(decimal_digit_count source - 1) +
          decimal_reverse ?quotient) mod 99 =
          (?digit + 10 * ?quotient) mod 99"
        by (rule mod_add_cong[OF digit rest])
      show ?thesis unfolding reverse_step
        using joined by (simp only: add.commute)
    qed
    have even_width:
      "odd (decimal_digit_count ?quotient) \<Longrightarrow>
        decimal_reverse source mod 99 = (100 * ?quotient + 10 * ?digit) mod 99"
    proof -
      assume quotient_odd: "odd (decimal_digit_count ?quotient)"
      have ten_times_digit:
        "(10 * ?digit) mod 99 =
          (?digit * 10^(decimal_digit_count source - 1)) mod 99"
        using digit_mod quotient_odd quotient_width by simp
      have hundred_times_quotient:
        "(100 * ?quotient) mod 99 =
          decimal_reverse ?quotient mod 99"
      proof -
        have factor: "(100::nat) mod 99 = 1 mod 99" by simp
        have product:
          "(100 * ?quotient) mod 99 = (1 * ?quotient) mod 99"
          by (rule mod_mult_cong[OF factor]) (rule refl)
        show ?thesis using product quotient_reversal quotient_odd by simp
      qed
      have joined:
        "(?digit * 10^(decimal_digit_count source - 1) +
          decimal_reverse ?quotient) mod 99 =
          (10 * ?digit + 100 * ?quotient) mod 99"
        by (rule mod_add_cong[OF ten_times_digit[symmetric] hundred_times_quotient[symmetric]])
      show ?thesis unfolding reverse_step
        using joined by (simp only: add.commute)
    qed
    show ?thesis
    proof (cases "even (decimal_digit_count ?quotient)")
      case True
      have count_odd: "odd (decimal_digit_count source)"
        using quotient_width True by simp
      have reverse: "decimal_reverse source mod 99 =
          (10 * ?quotient + ?digit) mod 99"
        by (rule odd_width[OF True])
      show ?thesis
        using reverse source_split count_odd by simp
    next
      case False
      then have quotient_odd: "odd (decimal_digit_count ?quotient)"
        by simp
      have count_even: "even (decimal_digit_count source)"
        using quotient_width quotient_odd by simp
      have reverse: "decimal_reverse source mod 99 =
          (100 * ?quotient + 10 * ?digit) mod 99"
        by (rule even_width[OF quotient_odd])
      have reconstructed: "10 * source = 100 * ?quotient + 10 * ?digit"
      proof -
        have "10 * source = 10 * (10 * ?quotient + ?digit)"
          by (rule arg_cong[where f="\<lambda>x. 10*x"]) (rule source_split)
        also have "... = 100 * ?quotient + 10 * ?digit"
          by (simp only: distrib_left mult.assoc[symmetric]; simp)
        finally show ?thesis .
      qed
      show ?thesis using reverse count_even
        by (simp only: if_P reconstructed)
    qed
  qed
qed

theorem double_reverse_physical_mod99_step:
  "double_reverse_T source mod 99 =
    ((if even (decimal_digit_count source) then 20 else 2) * source) mod 99"
proof -
  have two_mod: "(2::nat) mod 99 = 2 mod 99" by simp
  have reversal_mod:
    "decimal_reverse source mod 99 =
      ((if even (decimal_digit_count source) then 10 else 1) * source) mod 99"
    by (rule decimal_reverse_mod99_width_parity)
  have product:
    "(2 * decimal_reverse source) mod 99 =
      (2 * ((if even (decimal_digit_count source) then 10 else 1) * source)) mod 99"
    by (rule mod_mult_cong[OF two_mod reversal_mod])
  have multiplier:
    "2 * ((if even (decimal_digit_count source) then 10 else 1) * source) =
     (if even (decimal_digit_count source) then 20 else 2) * source"
    by (cases "even (decimal_digit_count source)"; simp add: mult.assoc[symmetric])
  show ?thesis unfolding double_reverse_T_def
    using product by (simp only: multiplier)
qed

lemma double_reverse_closed_border_growth_matches_mixed_clock:
  assumes edge: "edge \<in> double_reverse_closed_border"
  shows "double_reverse_border_width_growth edge =
    double_reverse_outer_growth (double_reverse_border_phase edge)"
proof -
  let ?phase = "double_reverse_border_phase edge"
  have phase_bound: "?phase < 4"
    using edge by (auto simp: double_reverse_closed_border_def
        double_reverse_border_phase_def split: prod.splits)
  have kernel_growth:
    "double_reverse_border_width_growth edge =
      fst (double_reverse_border_physical_births ?phase) +
      snd (double_reverse_border_physical_births ?phase)"
    by (rule double_reverse_closed_border_growth_matches_width[OF edge])
  have phase_cases: "?phase = 0 \<or> ?phase = 1 \<or> ?phase = 2 \<or> ?phase = 3"
    using phase_bound by arith
  have controller_growth:
    "fst (double_reverse_border_physical_births ?phase) +
      snd (double_reverse_border_physical_births ?phase) =
      double_reverse_outer_growth ?phase"
    using phase_cases
    by (auto simp: double_reverse_outer_growth_def
        double_reverse_border_physical_births_def)
  show ?thesis
    using kernel_growth controller_growth by simp
qed

text \<open>This is the concrete consumer bridge: the phase is read from the
kernel-checked border edge, its growth is the kernel-checked physical width
increment, and its residue is the actual numeric successor.  The explicit
width projection premise is the remaining source-admission obligation; the
abstract quotient does not manufacture it.\<close>

theorem double_reverse_physical_mixed_adic_projection_step:
  assumes edge: "edge \<in> double_reverse_closed_border"
      and inward: "inward < 2"
      and width_projection:
        "decimal_digit_count (double_reverse_T source) mod 2 =
          (decimal_digit_count source +
            double_reverse_border_width_growth edge) mod 2"
  shows
    "(double_reverse_border_phase
        (double_reverse_border_target edge inward),
      decimal_digit_count (double_reverse_T source) mod 2,
      double_reverse_T source mod 99) =
      double_reverse_mixed_residue_step
        (double_reverse_border_phase edge)
        (decimal_digit_count source mod 2) source"
proof -
  have phase_step:
    "double_reverse_border_phase
        (double_reverse_border_target edge inward) =
      (double_reverse_border_phase edge + 1) mod 4"
    by (rule double_reverse_closed_border_phase_step[OF edge inward])
  have width_step:
    "decimal_digit_count (double_reverse_T source) mod 2 =
      (decimal_digit_count source mod 2 +
        double_reverse_outer_growth (double_reverse_border_phase edge)) mod 2"
  proof -
    have growth_mod:
      "double_reverse_border_width_growth edge mod 2 =
        double_reverse_outer_growth (double_reverse_border_phase edge) mod 2"
      using double_reverse_closed_border_growth_matches_mixed_clock[OF edge]
      by simp
    have count_mod:
      "decimal_digit_count source mod 2 = decimal_digit_count source mod 2"
      by (rule refl)
    have sum_mod:
      "(decimal_digit_count source + double_reverse_border_width_growth edge) mod 2 =
        (decimal_digit_count source +
          double_reverse_outer_growth (double_reverse_border_phase edge)) mod 2"
      by (rule mod_add_cong[OF count_mod growth_mod])
    have reduced:
      "(decimal_digit_count source mod 2 +
         double_reverse_outer_growth (double_reverse_border_phase edge)) mod 2 =
       (decimal_digit_count source +
         double_reverse_outer_growth (double_reverse_border_phase edge)) mod 2"
      by (rule mod_add_left_eq)
    show ?thesis using width_projection sum_mod reduced by metis
  qed
  have residue_step:
    "double_reverse_T source mod 99 =
      ((if decimal_digit_count source mod 2 = 0 then 20 else 2) *
        source) mod 99"
    using double_reverse_physical_mod99_step[of source]
    by (simp only: even_iff_mod_2_eq_zero)
  show ?thesis
    using phase_step width_step residue_step
    unfolding double_reverse_mixed_residue_step_def
    by (simp add: double_reverse_outer_growth_def
        mod_mult_right_eq mod_mult_left_eq)
qed

text \<open>The physical source is admitted by its canonical decimal word and
its final digit is bound to the selected border. The word-to-width theorem
then supplies the width premise of the quotient projection.\<close>

theorem double_reverse_canonical_mixed_adic_projection_step:
  assumes edge: "edge \<in> double_reverse_closed_border"
      and inward: "inward < 2"
      and canonical: "double_reverse_canonical_source source"
      and edge_digit: "last source = (case edge of (a,b,y,z) \<Rightarrow> z)"
  shows
    "(double_reverse_border_phase (double_reverse_border_target edge inward),
      decimal_digit_count (double_reverse_T (double_reverse_msf_value source)) mod 2,
      double_reverse_T (double_reverse_msf_value source) mod 99) =
      double_reverse_mixed_residue_step (double_reverse_border_phase edge)
        (decimal_digit_count (double_reverse_msf_value source) mod 2)
        (double_reverse_msf_value source)"
proof -
  have nonempty: "source \<noteq> []" and decimal:
    "list_all (\<lambda>d. d < 10) source" and high: "hd source > 0"
    using canonical by (auto simp: double_reverse_canonical_source_def)
  have width_rev:
    "decimal_digit_count (double_reverse_lsf_value (rev source)) = length (rev source)"
    by (rule double_reverse_decimal_digits_lsf_value)
       (use nonempty decimal high in \<open>auto simp: last_rev\<close>)
  have width: "decimal_digit_count (double_reverse_msf_value source) = length source"
    using width_rev unfolding double_reverse_msf_value_def by simp
  have growth: "threshold5_digit (last source) = double_reverse_border_width_growth edge"
    using edge_digit by (cases edge; auto simp: threshold5_digit_def
      double_reverse_border_width_growth_def split: prod.splits)
  have projection:
    "decimal_digit_count (double_reverse_T (double_reverse_msf_value source)) mod 2 =
      (decimal_digit_count (double_reverse_msf_value source) +
        double_reverse_border_width_growth edge) mod 2"
    using double_reverse_canonical_source_step_width[OF canonical] width growth by simp
  show ?thesis
    by (rule double_reverse_physical_mixed_adic_projection_step[OF edge inward projection])
qed


definition double_reverse_word_border :: "nat list \<Rightarrow> double_reverse_boundary_edge" where
  "double_reverse_word_border word =
    (hd word, hd (tl word), hd (tl (rev word)), last word)"

theorem double_reverse_canonical_successor_border:
  assumes source: "source = [a,b] @ interior @ [y,z]"
      and canonical: "double_reverse_canonical_source source"
      and edge: "(a,b,y,z) \<in> double_reverse_closed_border"
  shows "\<exists>next_word inward. inward < 2 \<and>
    double_reverse_canonical_source next_word \<and>
    double_reverse_msf_value next_word = double_reverse_T (double_reverse_msf_value source) \<and>
    double_reverse_word_border next_word = double_reverse_border_target (a,b,y,z) inward"
proof -
  have decimal: "list_all (\<lambda>d. d < 10) source"
    using canonical by (simp add: double_reverse_canonical_source_def)
  have bounds: "a < 10" "b < 10" "y < 10" "z < 10"
      "list_all (\<lambda>d. d < 10) interior"
    using decimal source by (auto simp: list_all_iff)
  obtain middle inward where carry: "inward \<le> 1" and pass:
    "double_reverse_forward_pass source 0 =
      (((2*a mod 10) # ((2*b + threshold5_digit a) mod 10) # middle) @
          [(2*y + inward) mod 10, (2*z + threshold5_digit y) mod 10],
       threshold5_digit z)"
    using double_reverse_forward_physical_border[OF bounds] source by auto
  let ?emitted = "fst (double_reverse_forward_pass source 0) @
      (if snd (double_reverse_forward_pass source 0) = 1 then [1] else [])"
  have emitted:
    "list_all (\<lambda>d. d < 10) ?emitted \<and> ?emitted \<noteq> [] \<and>
     last ?emitted > 0 \<and> double_reverse_lsf_value ?emitted =
       double_reverse_T (double_reverse_msf_value source)"
    using double_reverse_canonical_successor_decimal_word[OF canonical] by auto
  have edges:
    "(a,b,y,z) = (1,7,4,2) \<or> (a,b,y,z) = (1,7,6,8) \<or>
     (a,b,y,z) = (1,7,8,8) \<or> (a,b,y,z) = (4,8,4,2) \<or>
     (a,b,y,z) = (4,8,6,8) \<or> (a,b,y,z) = (4,8,8,8) \<or>
     (a,b,y,z) = (4,9,4,2) \<or> (a,b,y,z) = (4,9,6,8) \<or>
     (a,b,y,z) = (4,9,8,8)"
    using edge by (simp add: double_reverse_closed_border_def)
  have incoming: "inward = 0 \<or> inward = 1" using carry by arith
  have first: "hd ?emitted > 0"
    using pass edges incoming by (auto simp: threshold5_digit_def)
  have next_canonical: "double_reverse_canonical_source (rev ?emitted)"
    using emitted first
    by (auto simp: double_reverse_canonical_source_def list_all_iff hd_rev last_rev)
  have target: "double_reverse_word_border (rev ?emitted) =
      double_reverse_border_target (a,b,y,z) inward"
    using pass edges incoming by (auto simp: double_reverse_word_border_def
      double_reverse_border_target_def threshold5_digit_def)
  have value_fact: "double_reverse_msf_value (rev ?emitted) =
      double_reverse_T (double_reverse_msf_value source)"
    using emitted by (simp add: double_reverse_msf_value_def)
  have inward_bound: "inward < 2" using carry by arith
  show ?thesis
    by (intro exI[of _ "rev ?emitted"] exI[of _ inward] conjI)
       (rule inward_bound next_canonical value_fact target)+
qed

lemma double_reverse_word_four_split:
  assumes "4 \<le> length source"
  obtains a b interior y z where
    "source = [a,b] @ interior @ [y,z]"
proof -
  obtain a rest where first: "source = a # rest"
    using assms by (cases source) auto
  obtain b tail where second: "rest = b # tail"
    using assms first by (cases rest) auto
  have tail_long: "2 \<le> length tail"
    using assms first second by simp
  obtain prefix z where third: "tail = prefix @ [z]"
    using tail_long by (cases tail rule: rev_cases) auto
  have prefix_nonempty: "prefix \<noteq> []"
    using tail_long third by auto
  obtain interior y where fourth: "prefix = interior @ [y]"
    using prefix_nonempty by (cases prefix rule: rev_cases) auto
  show ?thesis
    by (rule that[of a b interior y z]) (simp add: first second third fourth)
qed

lemma double_reverse_canonical_source_word_width:
  assumes "double_reverse_canonical_source source"
  shows "decimal_digit_count (double_reverse_msf_value source) = length source"
proof -
  have decimal: "list_all (\<lambda>d. d < 10) (rev source)"
    and nonempty: "rev source \<noteq> []" and high: "last (rev source) > 0"
    using assms by (auto simp: double_reverse_canonical_source_def last_rev)
  have "decimal_digit_count (double_reverse_lsf_value (rev source)) = length (rev source)"
    by (rule double_reverse_decimal_digits_lsf_value[OF decimal nonempty high])
  then show ?thesis by (simp add: double_reverse_msf_value_def)
qed

lemma double_reverse_successor_word_long:
  assumes source: "double_reverse_canonical_source source"
      and next_word: "double_reverse_canonical_source next_word"
      and value_fact: "double_reverse_msf_value next_word = double_reverse_T (double_reverse_msf_value source)"
      and long: "4 \<le> length source"
  shows "4 \<le> length next_word"
proof -
  have next_width: "decimal_digit_count (double_reverse_msf_value next_word) = length next_word"
    by (rule double_reverse_canonical_source_word_width[OF next_word])
  have step: "decimal_digit_count (double_reverse_T (double_reverse_msf_value source)) =
      length source + threshold5_digit (last source)"
    by (rule double_reverse_canonical_source_step_width[OF source])
  have equal_counts:
    "decimal_digit_count (double_reverse_msf_value next_word) =
      decimal_digit_count (double_reverse_T (double_reverse_msf_value source))"
    by (rule arg_cong[OF value_fact])
  have next_length:
    "length next_word = length source + threshold5_digit (last source)"
    using next_width equal_counts step by simp
  show ?thesis using next_length long by arith
qed

lemma double_reverse_mixed_residue_run_mod99:
  "double_reverse_mixed_residue_run ticks phase width (residue mod 99) =
    double_reverse_mixed_residue_run ticks phase width residue"
  by (cases ticks)
     (simp_all add: double_reverse_mixed_residue_step_def mod_mult_right_eq)

theorem double_reverse_mixed_adic_physical_run:
  assumes canonical: "double_reverse_canonical_source source"
      and long: "4 \<le> length source"
      and admitted: "double_reverse_word_border source \<in> double_reverse_closed_border"
  shows "\<exists>final. double_reverse_canonical_source final \<and>
    4 \<le> length final \<and>
    double_reverse_word_border final \<in> double_reverse_closed_border \<and>
    double_reverse_msf_value final = double_reverse_T_run ticks (double_reverse_msf_value source) \<and>
    double_reverse_mixed_residue_run ticks
      (double_reverse_border_phase (double_reverse_word_border source))
      (decimal_digit_count (double_reverse_msf_value source) mod 2)
      (double_reverse_msf_value source) =
      (double_reverse_border_phase (double_reverse_word_border final),
       decimal_digit_count (double_reverse_msf_value final) mod 2,
       double_reverse_msf_value final mod 99)"
  using canonical long admitted
proof (induction ticks arbitrary: source)
  case 0
  have phase_bound:
    "double_reverse_border_phase (double_reverse_word_border source) < 4"
    by (cases "double_reverse_word_border source")
       (auto simp: double_reverse_border_phase_def split: prod.splits)
  show ?case using 0 by (intro exI[of _ source])
    (simp add: double_reverse_T_run_def phase_bound)
next
  case (Suc ticks)
  obtain a b interior y z where shape: "source = [a,b] @ interior @ [y,z]"
    by (rule double_reverse_word_four_split[OF Suc.prems(2)]) blast
  have border: "double_reverse_word_border source = (a,b,y,z)"
    by (simp add: double_reverse_word_border_def shape)
  have edge: "(a,b,y,z) \<in> double_reverse_closed_border"
    using Suc.prems(3) border by simp
  obtain next_word inward where inward: "inward < 2"
      and next_word: "double_reverse_canonical_source next_word"
      and value_fact: "double_reverse_msf_value next_word = double_reverse_T (double_reverse_msf_value source)"
      and next_border: "double_reverse_word_border next_word = double_reverse_border_target (a,b,y,z) inward"
    using double_reverse_canonical_successor_border[OF shape Suc.prems(1) edge] by blast
  have next_long: "4 \<le> length next_word"
    by (rule double_reverse_successor_word_long[OF Suc.prems(1) next_word value_fact Suc.prems(2)])
  have next_edge: "double_reverse_word_border next_word \<in> double_reverse_closed_border"
    using double_reverse_closed_border_ingress_closed[OF edge inward] next_border by simp
  have last_digit: "last source = (case (a,b,y,z) of (a,b,y,z) \<Rightarrow> z)"
    by (simp add: shape)
  have projection:
    "(double_reverse_border_phase (double_reverse_word_border next_word),
      decimal_digit_count (double_reverse_msf_value next_word) mod 2,
      double_reverse_msf_value next_word mod 99) =
      double_reverse_mixed_residue_step (double_reverse_border_phase (double_reverse_word_border source))
        (decimal_digit_count (double_reverse_msf_value source) mod 2)
        (double_reverse_msf_value source)"
    using double_reverse_canonical_mixed_adic_projection_step[OF edge inward Suc.prems(1) last_digit]
      border next_border value_fact by simp
  have run_step:
    "double_reverse_mixed_residue_run (Suc ticks)
      (double_reverse_border_phase (double_reverse_word_border source))
      (decimal_digit_count (double_reverse_msf_value source) mod 2)
      (double_reverse_msf_value source) =
     double_reverse_mixed_residue_run ticks
      (double_reverse_border_phase (double_reverse_word_border next_word))
      (decimal_digit_count (double_reverse_msf_value next_word) mod 2)
      (double_reverse_msf_value next_word)"
    using projection
    by (simp only: double_reverse_mixed_residue_run.simps projection[symmetric]
        prod.case double_reverse_mixed_residue_run_mod99)
  obtain final where conclusion: "double_reverse_canonical_source final"
      "4 \<le> length final" "double_reverse_word_border final \<in> double_reverse_closed_border"
      "double_reverse_msf_value final = double_reverse_T_run ticks (double_reverse_msf_value next_word)"
      "double_reverse_mixed_residue_run ticks
        (double_reverse_border_phase (double_reverse_word_border next_word))
        (decimal_digit_count (double_reverse_msf_value next_word) mod 2)
        (double_reverse_msf_value next_word) =
        (double_reverse_border_phase (double_reverse_word_border final),
         decimal_digit_count (double_reverse_msf_value final) mod 2,
         double_reverse_msf_value final mod 99)"
    using Suc.IH[OF next_word next_long next_edge] by blast
  show ?case using conclusion run_step value_fact
    by (intro exI[of _ final])
      (simp add: double_reverse_T_run_def funpow_Suc_right funpow_swap1
        split: prod.splits)
qed

lemma double_reverse_mixed_residue_factor_congruent:
  fixes width1 width2 residue1 residue2 :: nat
  assumes residue: "residue1 mod 99 = residue2 mod 99"
      and width_or_divisibility:
        "width1 mod 2 = width2 mod 2 \<or> residue1 mod 11 = 0"
  shows "((if width1 mod 2 = 0 then 20 else 2) * residue1) mod 99 =
    ((if width2 mod 2 = 0 then 20 else 2) * residue2) mod 99"
proof (cases "width1 mod 2 = width2 mod 2")
  case True
  have factor:
    "(if width1 mod 2 = 0 then (20::nat) else 2) =
      (if width2 mod 2 = 0 then (20::nat) else 2)"
    using True by simp
  have factor_mod:
    "(if width1 mod 2 = 0 then (20::nat) else 2) mod (99::nat) =
      (if width2 mod 2 = 0 then (20::nat) else 2) mod (99::nat)"
    using factor by simp
  show ?thesis
    by (rule mod_mult_cong[OF factor_mod residue])
next
  case False
  have divisible: "residue1 mod 11 = 0"
    using False width_or_divisibility by blast
  obtain quotient where residue1: "residue1 = 11 * quotient"
    using divisible by (metis dvd_def mod_eq_0_iff_dvd)
  have factor_congruence: "(220::nat) mod 99 = 22 mod 99" by simp
  have scaled: "(220 * quotient) mod 99 = (22 * quotient) mod 99"
  proof (rule mod_mult_cong[OF factor_congruence])
    show "quotient mod 99 = quotient mod 99" by (rule refl)
  qed
  have factor_equal:
    "((if width1 mod 2 = 0 then 20 else 2) * residue1) mod 99 =
      ((if width2 mod 2 = 0 then 20 else 2) * residue1) mod 99"
    using False residue1 scaled
    by (cases "width1 mod 2 = 0"; cases "width2 mod 2 = 0")
       (simp_all add: mult.assoc[symmetric])
  have second:
    "((if width2 mod 2 = 0 then 20 else 2) * residue1) mod 99 =
      ((if width2 mod 2 = 0 then 20 else 2) * residue2) mod 99"
  proof (rule mod_mult_cong)
    show "(if width2 mod 2 = 0 then 20 else 2) mod 99 =
      (if width2 mod 2 = 0 then 20 else 2) mod 99" by simp
    show "residue1 mod 99 = residue2 mod 99" by (rule residue)
  qed
  show ?thesis using factor_equal second by simp
qed

lemma double_reverse_width_parity_erasure_successor:
  fixes phase1 phase2 width1 width2 residue1 residue2 :: nat
  assumes phase: "phase1 mod 4 = phase2 mod 4"
      and phase1_canonical: "phase1 < 4"
      and phase2_canonical: "phase2 < 4"
      and width1_canonical: "width1 < 2"
      and width2_canonical: "width2 < 2"
      and residue: "residue1 mod 99 = residue2 mod 99"
      and width_or_divisibility:
        "width1 mod 2 = width2 mod 2 \<or> residue1 mod 11 = 0"
  shows "double_reverse_mixed_residue_class
      (fst (double_reverse_mixed_residue_step phase1 width1 residue1))
      (fst (snd (double_reverse_mixed_residue_step phase1 width1 residue1)))
      (snd (snd (double_reverse_mixed_residue_step phase1 width1 residue1))) =
    double_reverse_mixed_residue_class
      (fst (double_reverse_mixed_residue_step phase2 width2 residue2))
      (fst (snd (double_reverse_mixed_residue_step phase2 width2 residue2)))
      (snd (snd (double_reverse_mixed_residue_step phase2 width2 residue2)))"
proof -
  have same_phase: "phase1 = phase2"
    using phase
    by (simp only: mod_less[OF phase1_canonical] mod_less[OF phase2_canonical])
  have next_phase:
    "(phase1 + 1) mod 4 = (phase2 + 1) mod 4"
    using same_phase by simp
  have next_residue:
    "((if width1 mod 2 = 0 then 20 else 2) * residue1) mod 99 =
      ((if width2 mod 2 = 0 then 20 else 2) * residue2) mod 99"
    by (rule double_reverse_mixed_residue_factor_congruent
      [OF residue width_or_divisibility])
  show ?thesis
  proof (cases "width1 mod 2 = width2 mod 2")
    case True
    have same_growth:
      "double_reverse_outer_growth phase1 =
        double_reverse_outer_growth phase2"
      using same_phase by simp
    have same_width: "width1 = width2"
      using True
      by (simp only: mod_less[OF width1_canonical] mod_less[OF width2_canonical])
    have same_next_width:
      "(width1 + double_reverse_outer_growth phase1) mod 2 =
        (width2 + double_reverse_outer_growth phase2) mod 2"
      using same_width same_growth by simp
    show ?thesis
      using same_phase next_phase next_residue same_growth same_next_width
      by (simp add: double_reverse_mixed_residue_step_def
          double_reverse_mixed_residue_class_def double_reverse_outer_growth_def)
  next
    case False
    have divisible: "residue1 mod 11 = 0"
      using False width_or_divisibility by blast
    have next_divisible:
      "((if width1 mod 2 = 0 then 20 else 2) * residue1) mod 99 mod 11 = 0"
    proof -
      have factor_congruent:
        "(if width1 mod 2 = 0 then (20::nat) else 2) mod 11 =
          (if width1 mod 2 = 0 then 20 else 2) mod 11" by simp
      have residue_zero: "residue1 mod 11 = (0::nat) mod 11"
        using divisible by simp
      have product_zero:
        "((if width1 mod 2 = 0 then 20 else 2) * residue1) mod 11 =
          ((if width1 mod 2 = 0 then 20 else 2) * 0) mod 11"
        by (rule mod_mult_cong[OF factor_congruent residue_zero])
      have quotient_mod:
        "(((if width1 mod 2 = 0 then 20 else 2) * residue1) mod 99) mod 11 =
          ((if width1 mod 2 = 0 then 20 else 2) * residue1) mod 11"
        by (rule mod_mod_cancel) simp
      show ?thesis using product_zero quotient_mod by simp
    qed
    have next_divisible2:
      "((if width2 mod 2 = 0 then 20 else 2) * residue2) mod 99 mod 11 = 0"
    proof -
      have same_mod11:
        "((if width1 mod 2 = 0 then 20 else 2) * residue1) mod 99 mod 11 =
          ((if width2 mod 2 = 0 then 20 else 2) * residue2) mod 99 mod 11"
        using next_residue by (rule arg_cong[where f="\<lambda>value. value mod 11"])
      show ?thesis using same_mod11 next_divisible by simp
    qed
    have left_class:
      "double_reverse_mixed_residue_class
          (fst (double_reverse_mixed_residue_step phase1 width1 residue1))
          (fst (snd (double_reverse_mixed_residue_step phase1 width1 residue1)))
          (snd (snd (double_reverse_mixed_residue_step phase1 width1 residue1))) =
        ((phase1 + 1) mod 4,
          ((if width1 mod 2 = 0 then 20 else 2) * residue1) mod 99, None)"
      using next_divisible
      by (simp add: double_reverse_mixed_residue_class_def
          double_reverse_mixed_residue_step_def)
    have right_class:
      "double_reverse_mixed_residue_class
          (fst (double_reverse_mixed_residue_step phase2 width2 residue2))
          (fst (snd (double_reverse_mixed_residue_step phase2 width2 residue2)))
          (snd (snd (double_reverse_mixed_residue_step phase2 width2 residue2))) =
        ((phase2 + 1) mod 4,
          ((if width2 mod 2 = 0 then 20 else 2) * residue2) mod 99, None)"
      using next_divisible2
      by (simp add: double_reverse_mixed_residue_class_def
          double_reverse_mixed_residue_step_def)
    show ?thesis using left_class right_class next_phase next_residue by simp
  qed
qed

lemma double_reverse_mixed_residue_four_then:
  assumes phase: "phase < 4" and width: "width_parity < 2"
  shows "double_reverse_mixed_residue_run (Suc (Suc (Suc (Suc ticks))))
      phase width_parity residue =
    double_reverse_mixed_residue_run ticks phase width_parity
      ((160 * residue) mod 99)"
proof -
  have phase_cases: "phase = 0 \<or> phase = 1 \<or> phase = 2 \<or> phase = 3"
    using phase by arith
  have width_cases: "width_parity = 0 \<or> width_parity = 1"
    using width by arith
  have factors: "(16000::nat) mod 99 = 160 mod 99" by simp
  have reduce: "(16000 * residue) mod 99 = (160 * residue) mod 99"
  proof (rule mod_mult_cong[OF factors])
    show "residue mod 99 = residue mod 99" by (rule refl)
  qed
  show ?thesis
    using phase_cases width_cases
    by (elim disjE; simp add: double_reverse_mixed_residue_step_def
        double_reverse_outer_growth_def mod_mult_right_eq mult.assoc[symmetric] reduce;
        simp only: numeral_2_eq_2)
qed

lemma double_reverse_mixed_residue_four_step_periodic:
  assumes phase: "phase < 4" and width: "width_parity < 2"
  shows "double_reverse_mixed_residue_run (4 * periods) phase width_parity residue =
    (phase, width_parity, ((160 ^ periods) * residue) mod 99)"
proof (induction periods arbitrary: residue)
  case 0
  show ?case using phase width by simp
next
  case (Suc periods)
  have count: "4 * Suc periods = Suc (Suc (Suc (Suc (4 * periods))))" by simp
  have step:
    "double_reverse_mixed_residue_run (4 * Suc periods) phase width_parity residue =
     double_reverse_mixed_residue_run (4 * periods) phase width_parity
       ((160 * residue) mod 99)"
    unfolding count by (rule double_reverse_mixed_residue_four_then[OF phase width])
  have product: "160 ^ periods * (160 * residue) = 160 ^ Suc periods * residue"
    by (simp only: power_Suc mult.assoc mult.left_commute)
  show ?case
    unfolding step Suc.IH[of "(160 * residue) mod 99"]
    by (simp only: mod_mult_right_eq product)
qed

text \<open>The period theorem above is a law of the finite boundary quotient.  A
physical consumer still needs a theorem connecting its complete source word
and width seam to this state transition.\<close>

ML \<open>
  val checked = @{thms double_reverse_width_parity_erasure_successor
    double_reverse_mixed_residue_four_then
    double_reverse_mixed_residue_four_step_periodic
    double_reverse_physical_mod99_step
    double_reverse_closed_border_growth_matches_mixed_clock
    double_reverse_physical_mixed_adic_projection_step
    double_reverse_canonical_mixed_adic_projection_step
    double_reverse_canonical_successor_border
    double_reverse_mixed_adic_physical_run};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Mixed-adic outer quotient depends on an oracle, including skip_proof";
\<close>

end
