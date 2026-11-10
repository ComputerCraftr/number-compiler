theory Reverse_Center11_Source_Refinement
  imports Reverse_Center11_Controlled_Action Reverse_196_Residue_Quotient
    Reverse_Laurent_Producer_Refinement
begin

text \<open>This source-owned bridge extracts center and carry ports from the
actual reverse/add producer, proves the emitted half residues for every
nonempty source, and lifts that refinement by induction over actual successors.
It does not infer a future port word from modular returns.\<close>

definition reverse_center11_bool_value :: "bool \<Rightarrow> nat" where
  "reverse_center11_bool_value carry = (if carry then 1 else 0)"

definition reverse_center11_source_port :: "nat list \<Rightarrow> reverse_center11_port" where
  "reverse_center11_source_port source =
    (let center = length source div 2;
         coefficient = (if center < length source then source ! center else 0);
         incoming = carry_out False (take center source);
         outgoing = carry_out False (take (Suc center) source)
     in \<lparr>reverse_center11_odd_width = odd (length source),
          reverse_center11_growth = carry_out False source,
          reverse_center11_coefficient = coefficient,
          reverse_center11_carry_in = reverse_center11_bool_value incoming,
          reverse_center11_carry_out = reverse_center11_bool_value outgoing\<rparr>)"

definition reverse_center11_half_pair11 :: "nat list \<Rightarrow> int \<times> int" where
  "reverse_center11_half_pair11 word =
    (int (decimal_list_value (drop (length word div 2) word) mod 11),
     int (decimal_list_value
       (rev (take ((length word + 1) div 2) word)) mod 11))"

lemma reverse_center11_decimal_word_identity:
  assumes digits: "\<forall>x\<in>set word. x < 10"
  shows "digits word = word"
proof -
  have emitted: "emit False word = word"
    using digits
    by (induction word) (auto simp: domain_def split: if_splits)
  have no_growth: "carry_out False word = False"
    using digits
    by (induction word)
      (auto simp: carry_out_def domain_def split: if_splits)
  show ?thesis using emitted no_growth by (simp add: digits_def)
qed

lemma reverse_center11_source_port_admitted:
  assumes valid: "valid_pair source"
  shows "reverse_center11_port_admitted
      (reverse_center11_source_port source)"
proof -
  have nonempty: "source \<noteq> []"
    using valid by (simp add: valid_pair_def)
  have bounded: "\<forall>value\<in>set source. value \<le> 18"
    using valid by (simp add: valid_pair_def)
  let ?center = "length source div 2"
  have index: "?center < length source"
    using nonempty by (cases source) auto
  have coefficient: "source ! ?center \<le> 18"
    using bounded index by auto
  have split:
    "take (Suc ?center) source = take ?center source @ [source ! ?center]"
    by (rule take_Suc_conv_app_nth[OF index])
  have outgoing:
    "carry_out False (take (Suc ?center) source) =
       carry_apply (domain (source ! ?center))
         (carry_out False (take ?center source))"
    using split by (simp add: carry_out_append carry_out_def)
  let ?incoming = "carry_out False (take ?center source)"
  let ?outgoing = "carry_out False (take (Suc ?center) source)"
  have threshold:
    "?outgoing = (10 \<le> source ! ?center + reverse_center11_bool_value ?incoming)"
    using outgoing by (simp add: reverse_center11_bool_value_def
      carry_apply_decimal_threshold)
  have quotient:
    "reverse_center11_bool_value ?outgoing =
      (source ! ?center + reverse_center11_bool_value ?incoming) div 10"
    using threshold coefficient
    by (cases ?incoming; cases ?outgoing;
        simp_all add: reverse_center11_bool_value_def; presburger)
  have incoming_bound:
    "reverse_center11_bool_value ?incoming \<le> 1"
    by (cases ?incoming) (simp_all add: reverse_center11_bool_value_def)
  have outgoing_bound:
    "reverse_center11_bool_value ?outgoing \<le> 1"
    by (cases ?outgoing) (simp_all add: reverse_center11_bool_value_def)
  have quotient_bound:
    "(source ! ?center + reverse_center11_bool_value ?incoming) div 10 \<le> 1"
    using coefficient incoming_bound by arith
  show ?thesis
    using coefficient incoming_bound outgoing_bound quotient quotient_bound index
    by (simp add: reverse_center11_source_port_def
        reverse_center11_port_admitted_def Let_def)
qed

theorem reverse_center11_source_port_publisher:
  assumes valid: "valid_pair source"
  shows "reverse_center11_port_admitted
      (reverse_center11_source_port source)"
    and "reverse_two_port_publisher source = step source"
  using reverse_center11_source_port_admitted[OF valid]
    reverse_two_port_publisher_refines_step[OF valid] by simp_all

theorem reverse_center11_next_source_publisher:
  assumes valid: "valid_pair source"
  shows "reverse_center11_port_admitted
      (reverse_center11_source_port (step source))"
    and "reverse_two_port_publisher (step source) = step (step source)"
    and "step source = map (\<lambda>(a,b). a+b)
      (zip (digits source) (rev (digits source)))"
proof -
  have next_valid: "valid_pair (step source)"
    by (rule valid_pair_successor[OF valid])
  show port:
    "reverse_center11_port_admitted
      (reverse_center11_source_port (step source))"
    by (rule reverse_center11_source_port_admitted[OF next_valid])
  show "reverse_two_port_publisher (step source) = step (step source)"
    by (rule reverse_two_port_publisher_refines_step[OF next_valid])
  show "step source = map (\<lambda>(a,b). a+b)
      (zip (digits source) (rev (digits source)))"
    by (simp add: step_def)
qed

theorem reverse_center11_source_port_width_seam:
  "odd (length (step source)) =
    (odd (length source) \<noteq> carry_out False source)"
  by (simp add: length_digits_exact)

text \<open>These two exact emitter identities are the prefix and suffix
bridges needed to interpret a center port in the normalized physical output.
The prefix equation carries the low-side overflow as a signed decimal term;
the suffix equation absorbs that same carry into the high side, including the
optional leading growth digit.  They make no period or repeated-source claim.\<close>

lemma reverse_center11_emit_take:
  assumes bound: "m \<le> length source"
  shows "take m (emit carry source) = emit carry (take m source)"
  using bound
proof (induction m arbitrary: carry source)
  case 0
  then show ?case by simp
next
  case (Suc m)
  then obtain digit tail where source: "source = digit # tail"
    by (cases source) auto
  have tail_bound: "m \<le> length tail"
    using Suc.prems source by simp
  have tail:
    "take m (emit (carry_apply (domain digit) carry) tail) =
      emit (carry_apply (domain digit) carry) (take m tail)"
    by (rule Suc.IH[OF tail_bound])
  show ?case
    using tail source by simp
qed

lemma reverse_center11_emit_drop:
  assumes bound: "m \<le> length source"
  shows "drop m (emit carry source) =
    emit (carry_out carry (take m source)) (drop m source)"
proof -
  have split: "source = take m source @ drop m source"
    by simp
  have emitted:
    "emit carry source = emit carry (take m source) @
      emit (carry_out carry (take m source)) (drop m source)"
    using emit_append[of carry "take m source" "drop m source"] split
    by simp
  show ?thesis
    using emitted bound by (simp add: length_emit)
qed

lemma reverse_center11_normalized_prefix_balance:
  assumes bound: "m \<le> length source"
      and digits: "\<forall>x\<in>set source. x \<le> 18"
  shows "decimal_list_value (take m (digits source)) +
      10^m * reverse_center11_bool_value
        (carry_out False (take m source)) =
    decimal_list_value (take m source)"
proof -
  have emitted:
    "take m (digits source) = emit False (take m source)"
    using bound reverse_center11_emit_take[OF bound, where carry=False]
    by (simp add: digits_def length_emit)
  have prefix_bound: "\<forall>x\<in>set (take m source). x \<le> 18"
    using digits by (meson in_set_takeD)
  have balance:
    "decimal_list_value (emit False (take m source)) +
       10^length (take m source) *
         (if carry_out False (take m source) then 1 else 0) =
     decimal_list_value (take m source)"
    using emit_decimal_balance[OF prefix_bound, where carry=False]
    by simp
  show ?thesis
    using emitted balance bound by (simp add: reverse_center11_bool_value_def)
qed

lemma reverse_center11_mod11_carry_adjust:
  fixes base mask carry :: int
  assumes bit: "carry = 0 \<or> carry = 1"
  shows "(base - 99 * mask - 10 * carry) mod 11 =
      (base + carry) mod 11"
proof -
  have rearrange:
    "base - 99 * mask - 10 * carry =
      (base + carry) + (-(9 * mask + carry)) * 11"
    by (simp add: algebra_simps)
  show ?thesis
    by (simp only: rearrange mod_mult_self1)
qed

lemma reverse_center11_emitted_reversed_prefix_mod11:
  assumes bound: "m \<le> length source"
      and digits: "\<forall>x\<in>set source. x \<le> 18"
  shows "decimal_list_value (rev (take m (digits source))) mod 11 =
    (decimal_list_value (rev (take m source)) +
      reverse_center11_bool_value (carry_out False (take m source))) mod 11"
proof -
  have emitted:
    "take m (digits source) = emit False (take m source)"
    using bound reverse_center11_emit_take[OF bound, where carry=False]
    by (simp add: digits_def length_emit)
  have prefix_bound: "\<forall>x\<in>set (take m source). x \<le> 18"
    using digits by (meson in_set_takeD)
  have defect:
    "int (decimal_list_value (rev (take m source))) -
      int (decimal_list_value (rev (emit False (take m source)))) =
      99 * int (reverse_laurent_internal_carry_mask (take m source)) +
        10 * int (carry_bit (carry_out False (take m source)))"
    by (rule reverse_laurent_reflected_carry_defect[OF prefix_bound])
  have carry_equal:
    "carry_bit (carry_out False (take m source)) =
      reverse_center11_bool_value (carry_out False (take m source))"
    by (simp add: carry_bit_def reverse_center11_bool_value_def)
  have carry_value:
    "reverse_center11_bool_value (carry_out False (take m source)) \<le> 1"
    by (cases "carry_out False (take m source)")
      (simp_all add: reverse_center11_bool_value_def)
  have adjusted:
    "int (decimal_list_value (rev (emit False (take m source)))) mod 11 =
      (int (decimal_list_value (rev (take m source))) +
        int (reverse_center11_bool_value (carry_out False (take m source)))) mod 11"
  proof -
    have carry_cases:
      "int (reverse_center11_bool_value (carry_out False (take m source))) = 0
       \<or> int (reverse_center11_bool_value (carry_out False (take m source))) = 1"
      by (cases "carry_out False (take m source)")
        (simp_all add: reverse_center11_bool_value_def)
    have exact:
      "int (decimal_list_value (rev (emit False (take m source)))) =
        int (decimal_list_value (rev (take m source))) -
          99 * int (reverse_laurent_internal_carry_mask (take m source)) -
          10 * int (reverse_center11_bool_value (carry_out False (take m source)))"
      using defect carry_equal by linarith
    have adjust:
      "(int (decimal_list_value (rev (take m source))) -
          99 * int (reverse_laurent_internal_carry_mask (take m source)) -
          10 * int (reverse_center11_bool_value (carry_out False (take m source)))
        ) mod 11 =
        (int (decimal_list_value (rev (take m source))) +
          int (reverse_center11_bool_value (carry_out False (take m source)))
        ) mod 11"
      using reverse_center11_mod11_carry_adjust[where
        base="int (decimal_list_value (rev (take m source)))"
        and mask="int (reverse_laurent_internal_carry_mask (take m source))"
        and carry="int (reverse_center11_bool_value (carry_out False (take m source)))"]
        carry_cases by blast
    show ?thesis
      using exact adjust by simp
  qed
  show ?thesis
    using emitted adjusted
  proof -
    have integer_eq:
      "int (decimal_list_value (rev (take m (digits source))) mod 11) =
       int ((decimal_list_value (rev (take m source)) +
         reverse_center11_bool_value (carry_out False (take m source))) mod 11)"
      using adjusted emitted by (simp add: of_nat_mod)
    show ?thesis using integer_eq by (simp only: of_nat_eq_iff)
  qed
qed

lemma reverse_center11_normalized_suffix_balance:
  assumes bound: "m \<le> length source"
      and digits: "\<forall>x\<in>set source. x \<le> 18"
  shows "decimal_list_value (drop m (digits source)) =
    decimal_list_value (drop m source) +
      reverse_center11_bool_value (carry_out False (take m source))"
proof -
  have emitted:
    "drop m (emit False source) =
      emit (carry_out False (take m source)) (drop m source)"
    by (rule reverse_center11_emit_drop[OF bound])
  have full:
    "digits source = emit False source @
      (if carry_out False source then [1] else [])"
    by (simp add: digits_def)
  have split:
    "digits source = emit False (take m source) @
      emit (carry_out False (take m source)) (drop m source) @
        (if carry_out False source then [1] else [])"
    using full emit_append[of False "take m source" "drop m source"]
      by (simp add: carry_out_append)
  have suffix:
    "drop m (digits source) =
      emit (carry_out False (take m source)) (drop m source) @
        (if carry_out False source then [1] else [])"
    using split bound by (simp add: length_emit)
  have suffix_bound: "\<forall>x\<in>set (drop m source). x \<le> 18"
    using digits by (meson in_set_dropD)
  have balance:
    "decimal_list_value
        (emit (carry_out False (take m source)) (drop m source)) +
      10^length (drop m source) *
        (if carry_out (carry_out False (take m source)) (drop m source)
         then 1 else 0) =
      decimal_list_value (drop m source) +
        (if carry_out False (take m source) then 1 else 0)"
    by (rule emit_decimal_balance[OF suffix_bound,
      where carry="carry_out False (take m source)"])
  have terminal:
    "carry_out (carry_out False (take m source)) (drop m source) =
      carry_out False source"
    using carry_out_append[of False "take m source" "drop m source"]
      by (simp add: carry_out_append)
  show ?thesis
  proof (cases "carry_out False source")
    case True
    show ?thesis
      using suffix balance terminal True
      by (cases "carry_out False (take m source)")
        (simp_all add: decimal_list_value_append
          reverse_center11_bool_value_def)
  next
    case False
    show ?thesis
      using suffix balance terminal False
      by (cases "carry_out False (take m source)")
        (simp_all add: decimal_list_value_append
          reverse_center11_bool_value_def)
  qed
qed

lemma reverse_center11_reflected_pair_prefix_value:
  assumes pair:
    "paired = map (\<lambda>(a,b). a+b) (zip source (rev source))"
  shows "decimal_list_value
      (rev (take ((length source + 1) div 2) paired)) =
    decimal_list_value (drop (length source div 2) source) +
      decimal_list_value
        (rev (take ((length source + 1) div 2) source))"
proof -
  let ?h = "length source div 2"
  let ?m = "(length source + 1) div 2"
  have h_m: "length source - ?h = ?m"
    using conjunct1[OF reverse_center11_half_widths[where source=source]] .
  have m_bound: "?m \<le> length source"
    using h_m by arith
  have paired_length: "length paired = length source"
    using pair by simp
  have reflected_pairs:
    "rev (take ?m paired) =
      map (\<lambda>(a,b). a+b) (zip (drop ?h source) (rev (take ?m source)))"
    by (rule reverse_center11_reflected_pair_prefix_structure[OF pair])
  have equal_length: "length (drop ?h source) =
      length (rev (take ?m source))"
    using h_m by simp
  have paired_prefix_value:
    "decimal_list_value
        (map (\<lambda>(a,b). a+b)
          (zip (drop ?h source) (rev (take ?m source)))) =
      decimal_list_value (drop ?h source) +
        decimal_list_value (rev (take ?m source))"
    by (rule decimal_list_value_zip_add[OF equal_length])
  show ?thesis using reflected_pairs paired_prefix_value by simp
qed

lemma reverse_center11_step_reflected_prefix_value:
  "decimal_list_value
      (rev (take ((length (digits source) + 1) div 2) (step source))) =
    decimal_list_value (drop (length (digits source) div 2) (digits source)) +
      decimal_list_value
        (rev (take ((length (digits source) + 1) div 2) (digits source)))"
  by (rule reverse_center11_reflected_pair_prefix_value[OF step_def])

lemma reverse_center11_palindrome_half_slices:
  assumes palindrome: "rev paired = paired"
      and lengths: "length paired = length source"
  defines "h \<equiv> length source div 2"
      and "m \<equiv> (length source + 1) div 2"
  shows "drop h paired = rev (take m paired)"
      and "drop m paired = rev (take h paired)"
proof -
  have hm: "length source - h = m"
    using conjunct1[OF reverse_center11_half_widths[where source=source]]
    by (simp add: h_def m_def)
  have mh: "length source - m = h"
    using conjunct2[OF reverse_center11_half_widths[where source=source]]
    by (simp add: h_def m_def)
  show "drop h paired = rev (take m paired)"
    using palindrome lengths mh by (simp add: rev_take)
  show "drop m paired = rev (take h paired)"
    using palindrome lengths hm by (simp add: rev_take)
qed

lemma reverse_center11_odd_center_prefix_value:
  fixes h :: nat and paired :: "nat list" and prefix_total :: nat
  assumes center: "h < length paired"
      and prefix: "decimal_list_value (rev (take (Suc h) paired)) = prefix_total"
  shows "prefix_total = paired ! h +
      10 * decimal_list_value (rev (take h paired))"
proof -
  have split:
    "take (Suc h) paired = take h paired @ [paired ! h]"
    by (rule take_Suc_conv_app_nth[OF center])
  show ?thesis
    using prefix split
    by (simp add: decimal_list_value_append algebra_simps)
qed

lemma reverse_center11_odd_shortened_suffix_mod11:
  fixes total_value center_value suffix_value :: nat
  assumes decomposition: "total_value = center_value + 10 * suffix_value"
  shows "int suffix_value mod 11 =
    (int center_value - int total_value) mod 11"
proof -
  have difference:
    "int total_value - int center_value = 10 * int suffix_value"
    using decomposition by simp
  have scaled_exact:
    "10 * (int total_value - int center_value) = 100 * int suffix_value"
    using difference by simp
  have hundred_product:
    "100 * int suffix_value =
      int suffix_value + (9 * int suffix_value) * 11"
    by (simp add: algebra_simps)
  have scaled:
    "(10 * (int total_value - int center_value)) mod 11 =
      int suffix_value mod 11"
    by (simp only: scaled_exact hundred_product mod_mult_self1)
  have negated:
    "(10 * (int total_value - int center_value)) mod 11 =
      (int center_value - int total_value) mod 11"
  proof -
    have rearrange:
      "10 * (int total_value - int center_value) =
        (int center_value - int total_value) +
          (int total_value - int center_value) * 11"
      by (simp add: algebra_simps)
    show ?thesis by (simp only: rearrange mod_mult_self1)
  qed
  show ?thesis using scaled negated by simp
qed

theorem reverse_center11_source_half_refinement:
  assumes nonempty: "source \<noteq> []"
  shows "fst (reverse_center11_half_pair11 (digits (step source))) =
      fst (reverse_center11_tick (reverse_center11_source_port (step source))
        (fst (reverse_center11_half_pair11 (digits source)),
         snd (reverse_center11_half_pair11 (digits source)), 0)) \<and>
    snd (reverse_center11_half_pair11 (digits (step source))) =
      fst (snd (reverse_center11_tick (reverse_center11_source_port (step source))
        (fst (reverse_center11_half_pair11 (digits source)),
         snd (reverse_center11_half_pair11 (digits source)), 0)))"
proof -
  let ?digits = "digits source"
  let ?paired = "step source"
  let ?h = "length ?digits div 2"
  let ?m = "(length ?digits + 1) div 2"
  let ?raw_a = "decimal_list_value (drop ?h ?digits)"
  let ?raw_b = "decimal_list_value (rev (take ?m ?digits))"
  let ?a = "int (?raw_a mod 11)"
  let ?b = "int (?raw_b mod 11)"
  let ?ci = "reverse_center11_bool_value (carry_out False (take ?h ?paired))"
  let ?co = "reverse_center11_bool_value
      (carry_out False (take (Suc ?h) ?paired))"
  let ?center = "?paired ! ?h"
  let ?growth = "carry_out False ?paired"

  have digits_nonempty: "?digits \<noteq> []"
    using nonempty by (simp add: digits_def)
  have digits_length_pos: "0 < length ?digits"
    using digits_nonempty by simp
  have h_lt_digits: "?h < length ?digits"
    using digits_length_pos by (simp add: div_less_dividend)
  have paired_length: "length ?paired = length ?digits"
    by (simp add: step_def)
  have paired_palindrome: "rev ?paired = ?paired"
    by (rule step_symmetric)
  have paired_bound: "\<forall>x\<in>set ?paired. x \<le> 18"
  proof
    fix x
    assume "x \<in> set ?paired"
    then show "x \<le> 18" by (rule step_bounded)
  qed
  have paired_source:
    "?paired = map (\<lambda>(a,b). a+b) (zip ?digits (rev ?digits))"
    by (simp add: step_def)
  have reflected_prefix:
    "decimal_list_value (rev (take ?m ?paired)) = ?raw_a + ?raw_b"
    by (rule reverse_center11_reflected_pair_prefix_value[OF paired_source])
  have half_slices:
    "drop ?h ?paired = rev (take ?m ?paired)"
    "drop ?m ?paired = rev (take ?h ?paired)"
  proof -
    show "drop ?h ?paired = rev (take ?m ?paired)"
      by (rule reverse_center11_palindrome_half_slices(1)[OF
        paired_palindrome paired_length])
    show "drop ?m ?paired = rev (take ?h ?paired)"
      by (rule reverse_center11_palindrome_half_slices(2)[OF
        paired_palindrome paired_length])
  qed
  have half_widths:
    "length ?digits - ?h = ?m"
    "length ?digits - ?m = ?h"
    using reverse_center11_half_widths[where source="?digits"] by simp_all
  have center_index: "?h < length ?paired"
    using h_lt_digits paired_length by simp
  have h_bound: "?h \<le> length ?paired"
    using paired_length by presburger
  have suc_h_bound: "Suc ?h \<le> length ?paired"
    using h_lt_digits paired_length by simp
  have port_fields:
    "reverse_center11_source_port ?paired =
      \<lparr>reverse_center11_odd_width = odd (length ?digits),
       reverse_center11_growth = ?growth,
       reverse_center11_coefficient = ?center,
       reverse_center11_carry_in = ?ci,
       reverse_center11_carry_out = ?co\<rparr>"
    using paired_length center_index
    by (simp add: reverse_center11_source_port_def Let_def)
  have suffix_at_h:
    "decimal_list_value (drop ?h (digits ?paired)) =
      decimal_list_value (drop ?h ?paired) + ?ci"
    using reverse_center11_normalized_suffix_balance[OF h_bound paired_bound]
    by (simp add: reverse_center11_bool_value_def)
  have suffix_at_suc_h:
    "decimal_list_value (drop (Suc ?h) (digits ?paired)) =
      decimal_list_value (drop (Suc ?h) ?paired) + ?co"
    using reverse_center11_normalized_suffix_balance[OF suc_h_bound paired_bound]
    by (simp add: reverse_center11_bool_value_def)
  have prefix_at_h:
    "decimal_list_value (rev (take ?h (digits ?paired))) mod 11 =
      (decimal_list_value (rev (take ?h ?paired)) + ?ci) mod 11"
    using reverse_center11_emitted_reversed_prefix_mod11[OF h_bound paired_bound]
    by (simp add: reverse_center11_bool_value_def)
  have prefix_at_suc_h:
    "decimal_list_value (rev (take (Suc ?h) (digits ?paired))) mod 11 =
      (decimal_list_value (rev (take (Suc ?h) ?paired)) + ?co) mod 11"
    using reverse_center11_emitted_reversed_prefix_mod11[OF suc_h_bound paired_bound]
    by (simp add: reverse_center11_bool_value_def)

  have x_mod:
    "int (?raw_a + ?raw_b) mod 11 = (?a + ?b) mod 11"
    by (simp add: of_nat_mod mod_add_eq algebra_simps)
  have sum_ci:
    "int (?raw_a + ?raw_b + ?ci) mod 11 =
      (?a + ?b + int ?ci) mod 11"
    using mod_add_cong[OF x_mod refl] by (simp add: of_nat_add)
  have sum_co:
    "int (?raw_a + ?raw_b + ?co) mod 11 =
      (?a + ?b + int ?co) mod 11"
    using mod_add_cong[OF x_mod refl] by (simp add: of_nat_add)
  have center_minus_co:
    "int (?center + 10 * (?raw_a + ?raw_b) + ?co) mod 11 =
      (int ?center - ?a - ?b + int ?co) mod 11"
  proof -
    have ten_sum_mod:
      "(10 * int (?raw_a + ?raw_b)) mod 11 =
        (10 * (?a + ?b)) mod 11"
      by (rule mod_mult_cong[OF refl x_mod])
    have center_sum_mod:
      "(int ?center + 10 * int (?raw_a + ?raw_b)) mod 11 =
        (int ?center + 10 * (?a + ?b)) mod 11"
      by (rule mod_add_cong[OF refl ten_sum_mod])
    have center_sum_co_mod:
      "((int ?center + 10 * int (?raw_a + ?raw_b)) + int ?co) mod 11 =
        ((int ?center + 10 * (?a + ?b)) + int ?co) mod 11"
      by (rule mod_add_cong[OF center_sum_mod refl])
    have transported:
      "int (?center + 10 * (?raw_a + ?raw_b) + ?co) mod 11 =
        (int ?center + 10 * (?a + ?b) + int ?co) mod 11"
      using center_sum_co_mod by (simp add: of_nat_add)
    have named_negation:
      "(10 * ?a + 10 * ?b + (int ?center + int ?co)) mod 11 =
        (int ?center - ?a - ?b + int ?co) mod 11"
      by (rule reverse_center11_mod11_negated_pair)
    show ?thesis using transported named_negation
      by (simp add: algebra_simps)
  qed

  have even_extension:
    "decimal_list_value (rev (take (Suc ?h) ?paired)) =
      ?center + 10 * (?raw_a + ?raw_b)"
    if even_width: "even (length ?digits)"
  proof -
    have m_eq: "?m = ?h"
      using even_width by simp
    have prefix: "decimal_list_value (rev (take ?h ?paired)) = ?raw_a + ?raw_b"
      using reflected_prefix m_eq by simp
    have extension:
      "decimal_list_value (rev (take (Suc ?h) ?paired)) =
        ?center + 10 * decimal_list_value (rev (take ?h ?paired))"
      by (rule reverse_center11_odd_center_prefix_value[OF center_index]) simp
    show ?thesis using extension prefix by simp
  qed

  have odd_short_decomposition:
    "?raw_a + ?raw_b = ?center +
      10 * decimal_list_value (drop (Suc ?h) ?paired)"
    if odd_width: "odd (length ?digits)"
  proof -
    have m_eq: "?m = Suc ?h"
      using odd_width by simp
    have center_prefix:
      "decimal_list_value (rev (take (Suc ?h) ?paired)) = ?raw_a + ?raw_b"
      using reflected_prefix m_eq by (simp only: m_eq)
    have center_split:
      "?raw_a + ?raw_b = ?center +
        10 * decimal_list_value (rev (take ?h ?paired))"
      by (rule reverse_center11_odd_center_prefix_value[OF center_index center_prefix])
    have suffix_slice:
      "drop (Suc ?h) ?paired = rev (take ?h ?paired)"
      using half_slices m_eq by simp
    show ?thesis using center_split suffix_slice by simp
  qed

  have short_plus_co:
    "int (decimal_list_value (drop (Suc ?h) ?paired) + ?co) mod 11 =
      (int ?center - ?a - ?b + int ?co) mod 11"
    if odd_width: "odd (length ?digits)"
  proof -
    have decomposition: "?raw_a + ?raw_b = ?center +
        10 * decimal_list_value (drop (Suc ?h) ?paired)"
      by (rule odd_short_decomposition[OF odd_width])
    have short_mod:
      "int (decimal_list_value (drop (Suc ?h) ?paired)) mod 11 =
        (int ?center - int (?raw_a + ?raw_b)) mod 11"
      by (rule reverse_center11_odd_shortened_suffix_mod11[OF decomposition])
    have center_difference_mod:
      "(int ?center - int (?raw_a + ?raw_b)) mod 11 =
        (int ?center - (?a + ?b)) mod 11"
      by (rule mod_diff_cong[OF refl x_mod])
    have increment_mod:
      "(int (decimal_list_value (drop (Suc ?h) ?paired)) + int ?co) mod 11 =
        ((int ?center - int (?raw_a + ?raw_b)) + int ?co) mod 11"
      by (rule mod_add_cong[OF short_mod refl])
    have transported_mod:
      "((int ?center - int (?raw_a + ?raw_b)) + int ?co) mod 11 =
        ((int ?center - (?a + ?b)) + int ?co) mod 11"
      by (rule mod_add_cong[OF center_difference_mod refl])
    show ?thesis using increment_mod transported_mod
      by (simp add: of_nat_add algebra_simps)
  qed

  have output_half_index:
    "length (digits ?paired) div 2 =
       (if odd (length ?digits) \<and> ?growth then Suc ?h else ?h)"
    by (cases "odd (length ?digits)"; cases ?growth;
        simp add: length_digits_exact paired_length; presburger)
  have output_prefix_index:
    "(length (digits ?paired) + 1) div 2 =
       (if even (length ?digits) \<and> \<not> ?growth then ?h else Suc ?h)"
    by (cases "even (length ?digits)"; cases ?growth;
        simp add: length_digits_exact paired_length; presburger)

  have first_unshortened:
    "fst (reverse_center11_half_pair11 (digits ?paired)) =
      (?a + ?b + int ?ci) mod 11"
    if not_odd_growth: "\<not> (odd (length ?digits) \<and> ?growth)"
  proof -
    have index: "length (digits ?paired) div 2 = ?h"
      using output_half_index not_odd_growth by simp
    have raw_suffix: "decimal_list_value (drop ?h ?paired) = ?raw_a + ?raw_b"
      using half_slices reflected_prefix by simp
    have unshortened_suffix_value:
      "decimal_list_value (drop ?h (digits ?paired)) = ?raw_a + ?raw_b + ?ci"
      using suffix_at_h raw_suffix by simp
    show ?thesis using unshortened_suffix_value index sum_ci
      by (simp add: reverse_center11_half_pair11_def of_nat_mod)
  qed
  have first_shortened:
    "fst (reverse_center11_half_pair11 (digits ?paired)) =
      (int ?center - ?a - ?b + int ?co) mod 11"
    if odd_growth: "odd (length ?digits) \<and> ?growth"
  proof -
    have index: "length (digits ?paired) div 2 = Suc ?h"
      using output_half_index odd_growth by simp
    have shortened_suffix_value:
      "decimal_list_value (drop (Suc ?h) (digits ?paired)) =
        decimal_list_value (drop (Suc ?h) ?paired) + ?co"
      by (rule suffix_at_suc_h)
    show ?thesis using shortened_suffix_value index
        short_plus_co[OF odd_growth[THEN conjunct1]]
      by (simp add: reverse_center11_half_pair11_def of_nat_mod)
  qed

  have second_even_no_growth:
    "snd (reverse_center11_half_pair11 (digits ?paired)) =
      (?a + ?b + int ?ci) mod 11"
    if even_no_growth: "even (length ?digits) \<and> \<not> ?growth"
  proof -
    have index: "(length (digits ?paired) + 1) div 2 = ?h"
      using output_prefix_index even_no_growth by simp
    have raw_prefix: "decimal_list_value (rev (take ?h ?paired)) = ?raw_a + ?raw_b"
      using reflected_prefix even_no_growth half_widths by simp
    have unshortened_prefix_value:
      "decimal_list_value (rev (take ?h (digits ?paired))) mod 11 =
        (?raw_a + ?raw_b + ?ci) mod 11"
      using prefix_at_h raw_prefix by simp
    show ?thesis using unshortened_prefix_value index sum_ci
      by (simp add: reverse_center11_half_pair11_def of_nat_mod)
  qed
  have second_even_growth:
    "snd (reverse_center11_half_pair11 (digits ?paired)) =
      (int ?center - ?a - ?b + int ?co) mod 11"
    if even_growth: "even (length ?digits) \<and> ?growth"
  proof -
    have index: "(length (digits ?paired) + 1) div 2 = Suc ?h"
      using output_prefix_index even_growth by simp
    have raw_prefix:
      "decimal_list_value (rev (take (Suc ?h) ?paired)) =
        ?center + 10 * (?raw_a + ?raw_b)"
      by (rule even_extension[OF even_growth[THEN conjunct1]])
    have extended_prefix_value:
      "decimal_list_value (rev (take (Suc ?h) (digits ?paired))) mod 11 =
        (?center + 10 * (?raw_a + ?raw_b) + ?co) mod 11"
      using prefix_at_suc_h raw_prefix by simp
    show ?thesis using extended_prefix_value index center_minus_co
      by (simp add: reverse_center11_half_pair11_def of_nat_mod)
  qed
  have second_odd:
    "snd (reverse_center11_half_pair11 (digits ?paired)) =
      (?a + ?b + int ?co) mod 11"
    if odd_width: "odd (length ?digits)"
  proof -
    have index: "(length (digits ?paired) + 1) div 2 = Suc ?h"
      using output_prefix_index odd_width by simp
    have raw_prefix:
      "decimal_list_value (rev (take (Suc ?h) ?paired)) = ?raw_a + ?raw_b"
      using reflected_prefix odd_width half_widths by simp
    have odd_prefix_value:
      "decimal_list_value (rev (take (Suc ?h) (digits ?paired))) mod 11 =
        (?raw_a + ?raw_b + ?co) mod 11"
      using prefix_at_suc_h raw_prefix by simp
    show ?thesis using odd_prefix_value index sum_co
      by (simp add: reverse_center11_half_pair11_def of_nat_mod)
  qed

  have first_target:
    "fst (reverse_center11_half_pair11 (digits ?paired)) =
      (if ?growth \<and> odd (length ?digits)
       then int ?center - ?a - ?b + int ?co else ?a + ?b + int ?ci) mod 11"
    by (rule reverse_center11_two_branch_if[OF first_shortened first_unshortened])
  have second_target:
    "snd (reverse_center11_half_pair11 (digits ?paired)) =
      (if ?growth \<and> \<not> odd (length ?digits)
       then int ?center - ?a - ?b + int ?co
       else if odd (length ?digits) then ?a + ?b + int ?co
       else ?a + ?b + int ?ci) mod 11"
    by (rule reverse_center11_nat_parity_growth_if[OF
      second_odd second_even_growth second_even_no_growth])
  have source_state:
    "(fst (reverse_center11_half_pair11 ?digits),
      snd (reverse_center11_half_pair11 ?digits), 0) = (?a, ?b, 0)"
    by (simp add: reverse_center11_half_pair11_def)
  have tick_first:
    "fst (reverse_center11_tick (reverse_center11_source_port ?paired)
      (fst (reverse_center11_half_pair11 ?digits),
       snd (reverse_center11_half_pair11 ?digits), 0)) =
      (if ?growth \<and> odd (length ?digits)
       then int ?center - ?a - ?b + int ?co else ?a + ?b + int ?ci) mod 11"
    using reverse_center11_tick_first_projection[where
      port="reverse_center11_source_port ?paired" and a="?a" and b="?b" and e=0]
      port_fields source_state
    by (simp only: reverse_center11_tick_first_projection source_state
      port_fields reverse_center11_port.select_convs)
  have tick_second:
    "fst (snd (reverse_center11_tick (reverse_center11_source_port ?paired)
      (fst (reverse_center11_half_pair11 ?digits),
       snd (reverse_center11_half_pair11 ?digits), 0))) =
      (if ?growth \<and> \<not> odd (length ?digits)
       then int ?center - ?a - ?b + int ?co
       else if odd (length ?digits) then ?a + ?b + int ?co
       else ?a + ?b + int ?ci) mod 11"
    using reverse_center11_tick_second_projection[where
      port="reverse_center11_source_port ?paired" and a="?a" and b="?b" and e=0]
      port_fields source_state
    by (simp only: reverse_center11_tick_second_projection source_state
      port_fields reverse_center11_port.select_convs)
  show ?thesis
    using first_target second_target tick_first tick_second
    by (simp add: conj_commute)
qed

lemma reverse_center11_step_nonempty:
  assumes "source \<noteq> []"
  shows "step source \<noteq> []"
  using assms by (simp add: step_def digits_def)
lemma reverse_center11_step_source_port_admitted:
  assumes source_nonempty: "source \<noteq> []"
  shows "reverse_center11_port_admitted
      (reverse_center11_source_port (step source))"
    and "reverse_two_port_publisher (step source) = step (step source)"
proof -
  have paired_nonempty: "step source \<noteq> []"
    by (rule reverse_center11_step_nonempty[OF source_nonempty])
  have paired_palindrome: "rev (step source) = step source"
    by (rule step_symmetric)
  have paired_bound: "\<forall>x\<in>set (step source). x \<le> 18"
  proof
    fix x
    assume "x \<in> set (step source)"
    then show "x \<le> 18" by (rule step_bounded)
  qed
  have paired_valid: "valid_pair (step source)"
    using paired_nonempty paired_palindrome paired_bound
    by (simp add: valid_pair_def)
  show "reverse_center11_port_admitted
      (reverse_center11_source_port (step source))"
    by (rule reverse_center11_source_port_admitted[OF paired_valid])
  show "reverse_two_port_publisher (step source) = step (step source)"
    by (rule reverse_two_port_publisher_refines_step[OF paired_valid])
qed

fun reverse_center11_source_ports ::
    "nat list \<Rightarrow> nat \<Rightarrow> reverse_center11_port list" where
  "reverse_center11_source_ports source 0 = []"
| "reverse_center11_source_ports source (Suc n) =
    reverse_center11_source_port (step source) #
      reverse_center11_source_ports (step source) n"

definition reverse_center11_source_half_increment ::
    "nat list \<Rightarrow> int" where
  "reverse_center11_source_half_increment source =
    (fst (reverse_center11_half_pair11 (digits (step source))) -
     snd (reverse_center11_half_pair11 (digits (step source)))) mod 11"

fun reverse_center11_source_half_trace ::
    "nat list \<Rightarrow> nat \<Rightarrow> int list" where
  "reverse_center11_source_half_trace source 0 = []"
| "reverse_center11_source_half_trace source (Suc n) =
    reverse_center11_source_half_increment source #
      reverse_center11_source_half_trace (step source) n"

lemma reverse_center11_source_ports_admitted:
  assumes nonempty: "source \<noteq> []"
  shows "\<forall>port\<in>set (reverse_center11_source_ports source n).
      reverse_center11_port_admitted port"
  using nonempty
proof (induction n arbitrary: source)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have successor_nonempty: "step source \<noteq> []"
    by (rule reverse_center11_step_nonempty[OF Suc.prems])
  have head:
    "reverse_center11_port_admitted
      (reverse_center11_source_port (step source))"
    by (rule reverse_center11_step_source_port_admitted(1)[OF Suc.prems])
  have tail:
    "\<forall>port\<in>set (reverse_center11_source_ports (step source) n).
      reverse_center11_port_admitted port"
    by (rule Suc.IH[OF successor_nonempty])
  show ?case using head tail by simp
qed

lemma reverse_center11_source_run_refinement:
  assumes nonempty: "source \<noteq> []"
  shows "reverse_center11_run (reverse_center11_source_ports source n)
      (fst (reverse_center11_half_pair11 (digits source)),
       snd (reverse_center11_half_pair11 (digits source)), 0) =
    (fst (reverse_center11_half_pair11 (digits (run step n source))),
     snd (reverse_center11_half_pair11 (digits (run step n source))),
     sum_list (reverse_center11_source_half_trace source n) mod 11)"
  using nonempty
proof (induction n arbitrary: source)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have successor_nonempty: "step source \<noteq> []"
    by (rule reverse_center11_step_nonempty[OF Suc.prems])
  have one_step:
    "reverse_center11_tick (reverse_center11_source_port (step source))
        (fst (reverse_center11_half_pair11 (digits source)),
         snd (reverse_center11_half_pair11 (digits source)), 0) =
      (fst (reverse_center11_half_pair11 (digits (step source))),
       snd (reverse_center11_half_pair11 (digits (step source))),
       reverse_center11_source_half_increment source mod 11)"
  proof -
    let ?tick = "reverse_center11_tick (reverse_center11_source_port (step source))
      (fst (reverse_center11_half_pair11 (digits source)),
       snd (reverse_center11_half_pair11 (digits source)), 0)"
    obtain first second accumulated where tick: "?tick = (first,second,accumulated)"
      by (cases ?tick) auto
    have refinement:
      "fst (reverse_center11_half_pair11 (digits (step source))) = first"
      "snd (reverse_center11_half_pair11 (digits (step source))) = second"
      using reverse_center11_source_half_refinement[OF Suc.prems] tick by simp_all
    have accumulated:
      "accumulated =
        (fst (reverse_center11_half_pair11 (digits (step source))) -
         snd (reverse_center11_half_pair11 (digits (step source)))) mod 11"
      using tick refinement reverse_center11_tick_accumulator_projection[of
        "reverse_center11_source_port (step source)"
        "fst (reverse_center11_half_pair11 (digits source))"
        "snd (reverse_center11_half_pair11 (digits source))" 0]
      by simp
    show ?thesis using tick refinement accumulated
      by (simp add: reverse_center11_source_half_increment_def)
  qed
  have induction:
    "reverse_center11_run (reverse_center11_source_ports (step source) n)
        (fst (reverse_center11_half_pair11 (digits (step source))),
         snd (reverse_center11_half_pair11 (digits (step source))), 0) =
      (fst (reverse_center11_half_pair11 (digits (run step n (step source)))),
       snd (reverse_center11_half_pair11 (digits (run step n (step source)))),
       sum_list (reverse_center11_source_half_trace (step source) n) mod 11)"
    by (rule Suc.IH[OF successor_nonempty])
  have shifted:
    "reverse_center11_run (reverse_center11_source_ports (step source) n)
        (fst (reverse_center11_half_pair11 (digits (step source))),
         snd (reverse_center11_half_pair11 (digits (step source))),
         reverse_center11_source_half_increment source mod 11) =
      (fst (reverse_center11_half_pair11 (digits (run step n (step source)))),
       snd (reverse_center11_half_pair11 (digits (run step n (step source)))),
       (sum_list (reverse_center11_source_half_trace (step source) n) +
          reverse_center11_source_half_increment source) mod 11)"
    using reverse_center11_run_accumulator_shift[of
      "reverse_center11_source_ports (step source) n"
      "fst (reverse_center11_half_pair11 (digits (step source)))"
      "snd (reverse_center11_half_pair11 (digits (step source)))" 0
      "reverse_center11_source_half_increment source"] induction
    by (simp only: fst_conv snd_conv add_0_left mod_add_left_eq)
  show ?case
    using one_step shifted
    by (simp add: reverse_center11_source_ports.simps
        reverse_center11_source_half_trace.simps run.simps
        reverse_center11_run.simps algebra_simps)
qed

ML \<open>
val checked = @{thms reverse_center11_source_half_refinement
  reverse_center11_source_ports_admitted
  reverse_center11_source_run_refinement
  reverse_center11_step_source_port_admitted
  reverse_center11_next_source_publisher
  reverse_center11_decimal_word_identity};
val _ = if null (Thm_Deps.all_oracles checked) then ()
  else error "Reverse centered source-half refinement depends on an oracle";
val _ = if Thm_Deps.has_skip_proof checked
  then error "Skipped reverse centered source-half refinement proof" else ();
\<close>

end
