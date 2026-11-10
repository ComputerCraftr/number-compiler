theory Double_Reverse_Seed196_Source_Low_Band_Refinement
  imports Double_Reverse_Seed196_Low_Band_Refinement
begin

theorem double_reverse_seed196_generation16_low5_anchor:
  "double_reverse_T_run 16 196 mod 100000 = 73488"
proof -
  have step1: "double_reverse_T 196 = 1382"
    by (simp add: double_reverse_T_def double_reverse_reverse10.simps
        double_reverse_decimal_digits.simps)
  have step2: "double_reverse_T 1382 = 5662"
    by (simp add: double_reverse_T_def double_reverse_reverse10.simps
        double_reverse_decimal_digits.simps)
  have step3: "double_reverse_T 5662 = 5330"
    by (simp add: double_reverse_T_def double_reverse_reverse10.simps
        double_reverse_decimal_digits.simps)
  have step4: "double_reverse_T 5330 = 670"
    by (simp add: double_reverse_T_def double_reverse_reverse10.simps
        double_reverse_decimal_digits.simps)
  have step5: "double_reverse_T 670 = 152"
    by (simp add: double_reverse_T_def double_reverse_reverse10.simps
        double_reverse_decimal_digits.simps)
  have step6: "double_reverse_T 152 = 502"
    by (simp add: double_reverse_T_def double_reverse_reverse10.simps
        double_reverse_decimal_digits.simps)
  have step7: "double_reverse_T 502 = 410"
    by (simp add: double_reverse_T_def double_reverse_reverse10.simps
        double_reverse_decimal_digits.simps)
  have step8: "double_reverse_T 410 = 28"
    by (simp add: double_reverse_T_def double_reverse_reverse10.simps
        double_reverse_decimal_digits.simps)
  have step9: "double_reverse_T 28 = 164"
    by (simp add: double_reverse_T_def double_reverse_reverse10.simps
        double_reverse_decimal_digits.simps)
  have step10: "double_reverse_T 164 = 922"
    by (simp add: double_reverse_T_def double_reverse_reverse10.simps
        double_reverse_decimal_digits.simps)
  have step11: "double_reverse_T 922 = 458"
    by (simp add: double_reverse_T_def double_reverse_reverse10.simps
        double_reverse_decimal_digits.simps)
  have step12: "double_reverse_T 458 = 1708"
    by (simp add: double_reverse_T_def double_reverse_reverse10.simps
        double_reverse_decimal_digits.simps)
  have step13: "double_reverse_T 1708 = 16142"
    by (simp add: double_reverse_T_def double_reverse_reverse10.simps
        double_reverse_decimal_digits.simps)
  have step14: "double_reverse_T 16142 = 48322"
    by (simp add: double_reverse_T_def double_reverse_reverse10.simps
        double_reverse_decimal_digits.simps)
  have step15: "double_reverse_T 48322 = 44768"
    by (simp add: double_reverse_T_def double_reverse_reverse10.simps
        double_reverse_decimal_digits.simps)
  have step16: "double_reverse_T 44768 = 173488"
    by (simp add: double_reverse_T_def double_reverse_reverse10.simps
        double_reverse_decimal_digits.simps)
  let ?suc16 = "Suc ( Suc ( Suc ( Suc (
    Suc ( Suc ( Suc ( Suc (
      Suc ( Suc ( Suc ( Suc (
        Suc ( Suc ( Suc ( Suc (0))))))))))))))))"
  have sixteen_as_suc: "(16::nat) = ?suc16"
    by (simp add: eval_nat_numeral)
  have iterated:
    "(double_reverse_T ^^ ?suc16) 196 = 173488"
    by (simp only: funpow.simps comp_apply id_apply step1 step2 step3 step4
        step5 step6 step7 step8 step9 step10 step11 step12 step13 step14
        step15 step16)
  have endpoint: "double_reverse_T_run 16 196 = 173488"
    unfolding double_reverse_T_run_def
    using iterated sixteen_as_suc by (simp only: sixteen_as_suc iterated)
  show ?thesis using endpoint by simp
qed

lemma double_reverse_seed196_phase_guard_is_admitted:
  assumes guard: "u \<in> double_reverse_seed196_phase_guards blocks"
  shows "u \<in> double_reverse_seed196_entry_guards \<union>
      double_reverse_seed196_first_guards \<union>
      double_reverse_seed196_second_guards \<union>
      double_reverse_seed196_third_guards"
proof -
  have bound: "double_reverse_seed196_phase_index blocks \<le> 3"
    by (rule double_reverse_seed196_phase_index_bound)
  have cases:
    "double_reverse_seed196_phase_index blocks = 0 \<or>
      double_reverse_seed196_phase_index blocks = 1 \<or>
      double_reverse_seed196_phase_index blocks = 2 \<or>
      double_reverse_seed196_phase_index blocks = 3"
    using bound by arith
  from cases guard show ?thesis
    by (elim disjE; simp_all add: double_reverse_seed196_phase_guards_def)
qed

lemma double_reverse_seed196_four_block_source_guard:
  "double_reverse_T_run (16 + 4 * blocks) 196 mod 100000
    \<in> double_reverse_seed196_phase_guards blocks"
proof (induction blocks)
  case 0
  then show ?case
    using double_reverse_seed196_generation16_low5_anchor
    by (simp add: double_reverse_seed196_phase_guards_def
        double_reverse_seed196_phase_index_def
        double_reverse_seed196_entry_guards_def)
next
  case (Suc blocks)
  let ?source = "double_reverse_T_run (16 + 4 * blocks) 196"
  let ?low = "?source mod 100000"
  have admitted:
    "?low \<in> double_reverse_seed196_entry_guards \<union>
      double_reverse_seed196_first_guards \<union>
      double_reverse_seed196_second_guards \<union>
      double_reverse_seed196_third_guards"
    by (rule double_reverse_seed196_phase_guard_is_admitted[OF Suc.IH])
  have next_low:
    "double_reverse_T_run 4 ?source mod 100000 =
      double_reverse_seed196_phi5 ?low
        (threshold5_digit ((?source div 100000) mod 10) = 1)"
    by (rule double_reverse_seed196_four_step_source_exact[OF _ admitted];
        simp)
  have next_guard:
    "double_reverse_seed196_phi5 ?low
        (threshold5_digit ((?source div 100000) mod 10) = 1)
      \<in> double_reverse_seed196_phase_guards (Suc blocks)"
    by (rule double_reverse_seed196_guard_successor[OF Suc.IH])
  have time:
    "double_reverse_T_run (16 + 4 * Suc blocks) 196 =
      double_reverse_T_run 4 ?source"
    using double_reverse_T_run_source_root_square[of "16 + 4 * blocks" 4 196]
    by (simp add: algebra_simps)
  show ?case using next_low next_guard time by simp
qed

lemma double_reverse_seed196_phase_guard_low4:
  assumes guard: "u \<in> double_reverse_seed196_phase_guards blocks"
  shows "u mod 10000 =
    (if double_reverse_seed196_phase_index blocks = 0 then 3488
     else if double_reverse_seed196_phase_index blocks = 1 then 1568
     else if double_reverse_seed196_phase_index blocks = 2 then 988
     else 8388)"
proof -
  have bound: "double_reverse_seed196_phase_index blocks \<le> 3"
    by (rule double_reverse_seed196_phase_index_bound)
  have cases:
    "double_reverse_seed196_phase_index blocks = 0 \<or>
      double_reverse_seed196_phase_index blocks = 1 \<or>
      double_reverse_seed196_phase_index blocks = 2 \<or>
      double_reverse_seed196_phase_index blocks = 3"
    using bound by arith
  from cases guard show ?thesis
    by (elim disjE; auto simp: double_reverse_seed196_phase_guards_def
      double_reverse_seed196_entry_guards_def
      double_reverse_seed196_first_guards_def
      double_reverse_seed196_second_guards_def
      double_reverse_seed196_third_guards_def)
qed

lemma double_reverse_seed196_phase_guard_pair_low4:
  assumes guard: "u \<in> double_reverse_seed196_phase_guards blocks"
  shows "double_reverse_seed196_first_pair_low6 u upper_high mod 10000 =
    (if double_reverse_seed196_phase_index blocks = 0 then 7342
     else if double_reverse_seed196_phase_index blocks = 1 then 742
     else if double_reverse_seed196_phase_index blocks = 2 then 7542
     else 5342)"
proof -
  have bound: "double_reverse_seed196_phase_index blocks \<le> 3"
    by (rule double_reverse_seed196_phase_index_bound)
  have cases:
    "double_reverse_seed196_phase_index blocks = 0 \<or>
      double_reverse_seed196_phase_index blocks = 1 \<or>
      double_reverse_seed196_phase_index blocks = 2 \<or>
      double_reverse_seed196_phase_index blocks = 3"
    using bound by arith
  from cases show ?thesis
  proof (elim disjE)
    assume zero: "double_reverse_seed196_phase_index blocks = 0"
    have entry: "u \<in> double_reverse_seed196_entry_guards"
      using guard zero by (simp add: double_reverse_seed196_phase_guards_def)
    have pair: "double_reverse_seed196_first_pair_low6 u upper_high mod 10000 = 7342"
      by (rule double_reverse_seed196_entry_guard_step(4)[OF entry])
    show ?thesis using pair zero by simp
  next
    assume one: "double_reverse_seed196_phase_index blocks = 1"
    have first: "u \<in> double_reverse_seed196_first_guards"
      using guard one by (simp add: double_reverse_seed196_phase_guards_def)
    have pair: "double_reverse_seed196_first_pair_low6 u upper_high mod 10000 = 742"
      by (rule double_reverse_seed196_first_guard_step(4)[OF first])
    show ?thesis using pair one by simp
  next
    assume two: "double_reverse_seed196_phase_index blocks = 2"
    have second: "u \<in> double_reverse_seed196_second_guards"
      using guard two by (simp add: double_reverse_seed196_phase_guards_def)
    have pair: "double_reverse_seed196_first_pair_low6 u upper_high mod 10000 = 7542"
      by (rule double_reverse_seed196_second_guard_step(4)[OF second])
    show ?thesis using pair two by simp
  next
    assume three: "double_reverse_seed196_phase_index blocks = 3"
    have third: "u \<in> double_reverse_seed196_third_guards"
      using guard three by (simp add: double_reverse_seed196_phase_guards_def)
    have pair: "double_reverse_seed196_first_pair_low6 u upper_high mod 10000 = 5342"
      by (rule double_reverse_seed196_third_guard_step(4)[OF third])
    show ?thesis using pair three by simp
  qed
qed

lemma double_reverse_seed196_phase_guard_low5_bound:
  assumes guard: "u \<in> double_reverse_seed196_phase_guards blocks"
  shows "1000 \<le> u"
proof -
  have bound: "double_reverse_seed196_phase_index blocks \<le> 3"
    by (rule double_reverse_seed196_phase_index_bound)
  have cases:
    "double_reverse_seed196_phase_index blocks = 0 \<or>
      double_reverse_seed196_phase_index blocks = 1 \<or>
      double_reverse_seed196_phase_index blocks = 2 \<or>
      double_reverse_seed196_phase_index blocks = 3"
    using bound by arith
  from cases guard show ?thesis
    by (elim disjE; auto simp: double_reverse_seed196_phase_guards_def
      double_reverse_seed196_entry_guards_def
      double_reverse_seed196_first_guards_def
      double_reverse_seed196_second_guards_def
      double_reverse_seed196_third_guards_def)
qed

lemma double_reverse_seed196_phase_guard_pair_low6_bound:
  assumes guard: "u \<in> double_reverse_seed196_phase_guards blocks"
  shows "1000 \<le> double_reverse_seed196_first_pair_low6 u upper_high"
proof -
  have admitted:
    "u \<in> double_reverse_seed196_entry_guards \<union>
      double_reverse_seed196_first_guards \<union>
      double_reverse_seed196_second_guards \<union>
      double_reverse_seed196_third_guards"
    by (rule double_reverse_seed196_phase_guard_is_admitted[OF guard])
  have finite_source_cases:
    "u = 73488 \<or> u = 11568 \<or> u = 21568 \<or> u = 31568 \<or>
      u = 41568 \<or> u = 60988 \<or> u = 80988 \<or>
      u = 28388 \<or> u = 48388"
    using admitted by (auto simp: double_reverse_seed196_entry_guards_def
      double_reverse_seed196_first_guards_def
      double_reverse_seed196_second_guards_def
      double_reverse_seed196_third_guards_def)
  show ?thesis
  proof (cases upper_high)
    case False
    have concrete_bounds:
      "1000 \<le> double_reverse_seed196_first_pair_low6 73488 False \<and>
       1000 \<le> double_reverse_seed196_first_pair_low6 11568 False \<and>
       1000 \<le> double_reverse_seed196_first_pair_low6 21568 False \<and>
       1000 \<le> double_reverse_seed196_first_pair_low6 31568 False \<and>
       1000 \<le> double_reverse_seed196_first_pair_low6 41568 False \<and>
       1000 \<le> double_reverse_seed196_first_pair_low6 60988 False \<and>
       1000 \<le> double_reverse_seed196_first_pair_low6 80988 False \<and>
       1000 \<le> double_reverse_seed196_first_pair_low6 28388 False \<and>
       1000 \<le> double_reverse_seed196_first_pair_low6 48388 False"
      by (simp add: double_reverse_seed196_first_pair_low6_def
          double_reverse_decimal_threshold_mask.simps threshold5_digit_def)
    from finite_source_cases concrete_bounds False show ?thesis
      by (elim disjE; simp)
  next
    case True
    have concrete_bounds:
      "1000 \<le> double_reverse_seed196_first_pair_low6 73488 True \<and>
       1000 \<le> double_reverse_seed196_first_pair_low6 11568 True \<and>
       1000 \<le> double_reverse_seed196_first_pair_low6 21568 True \<and>
       1000 \<le> double_reverse_seed196_first_pair_low6 31568 True \<and>
       1000 \<le> double_reverse_seed196_first_pair_low6 41568 True \<and>
       1000 \<le> double_reverse_seed196_first_pair_low6 60988 True \<and>
       1000 \<le> double_reverse_seed196_first_pair_low6 80988 True \<and>
       1000 \<le> double_reverse_seed196_first_pair_low6 28388 True \<and>
       1000 \<le> double_reverse_seed196_first_pair_low6 48388 True"
      by (simp add: double_reverse_seed196_first_pair_low6_def
          double_reverse_decimal_threshold_mask.simps threshold5_digit_def)
    from finite_source_cases concrete_bounds True show ?thesis
      by (elim disjE; simp)
  qed
qed

theorem double_reverse_seed196_four_block_source_low4:
  "double_reverse_T_run (16 + 4 * blocks) 196 mod 10000 =
    (if double_reverse_seed196_phase_index blocks = 0 then 3488
     else if double_reverse_seed196_phase_index blocks = 1 then 1568
     else if double_reverse_seed196_phase_index blocks = 2 then 988
     else 8388)"
proof -
  have guard: "double_reverse_T_run (16 + 4 * blocks) 196 mod 100000
      \<in> double_reverse_seed196_phase_guards blocks"
    by (rule double_reverse_seed196_four_block_source_guard)
  have ten_thousand_dvd_hundred_thousand: "10000 dvd (100000::nat)"
    by simp
  have output_reduction:
    "double_reverse_T_run (16 + 4 * blocks) 196 mod 10000 =
      (double_reverse_T_run (16 + 4 * blocks) 196 mod 100000) mod 10000"
    by (rule mod_mod_cancel[symmetric, OF ten_thousand_dvd_hundred_thousand])
  have guarded_low4:
    "(double_reverse_T_run (16 + 4 * blocks) 196 mod 100000) mod 10000 =
      (if double_reverse_seed196_phase_index blocks = 0 then 3488
       else if double_reverse_seed196_phase_index blocks = 1 then 1568
       else if double_reverse_seed196_phase_index blocks = 2 then 988 else 8388)"
    by (rule double_reverse_seed196_phase_guard_low4[OF guard])
  show ?thesis using output_reduction guarded_low4 by simp
qed

theorem double_reverse_seed196_pair_sheet_source_low4:
  "double_reverse_T_run (18 + 4 * blocks) 196 mod 10000 =
    (if double_reverse_seed196_phase_index blocks = 0 then 7342
     else if double_reverse_seed196_phase_index blocks = 1 then 742
     else if double_reverse_seed196_phase_index blocks = 2 then 7542
     else 5342)"
proof -
  let ?source = "double_reverse_T_run (16 + 4 * blocks) 196"
  let ?low = "?source mod 100000"
  let ?upper = "threshold5_digit ((?source div 100000) mod 10) = 1"
  have guard: "?low \<in> double_reverse_seed196_phase_guards blocks"
    by (rule double_reverse_seed196_four_block_source_guard)
  have admitted: "?low \<in> double_reverse_seed196_entry_guards \<union>
      double_reverse_seed196_first_guards \<union>
      double_reverse_seed196_second_guards \<union>
      double_reverse_seed196_third_guards"
    by (rule double_reverse_seed196_phase_guard_is_admitted[OF guard])
  have first_pair:
    "double_reverse_T_run 2 ?source mod 1000000 =
      double_reverse_seed196_first_pair_low6 ?low ?upper"
    by (rule double_reverse_seed196_first_pair_source_exact[OF _ _];
        simp add: double_reverse_seed196_guard_unit_digit[OF admitted])
  have pair_low4:
    "double_reverse_seed196_first_pair_low6 ?low ?upper mod 10000 =
      (if double_reverse_seed196_phase_index blocks = 0 then 7342
       else if double_reverse_seed196_phase_index blocks = 1 then 742
       else if double_reverse_seed196_phase_index blocks = 2 then 7542
       else 5342)"
    by (rule double_reverse_seed196_phase_guard_pair_low4[OF guard])
  have ten_thousand_dvd_million: "10000 dvd (1000000::nat)"
    by simp
  have first_pair_reduction:
    "(double_reverse_T_run 2 ?source mod 1000000) mod 10000 =
      double_reverse_T_run 2 ?source mod 10000"
    by (rule mod_mod_cancel[OF ten_thousand_dvd_million])
  have first_pair_mod:
    "(double_reverse_T_run 2 ?source mod 1000000) mod 10000 =
      double_reverse_seed196_first_pair_low6 ?low ?upper mod 10000"
    by (rule arg_cong[where f="\<lambda>value::nat. value mod 10000",
        OF first_pair])
  have low4_transport:
    "double_reverse_T_run 2 ?source mod 10000 =
      double_reverse_seed196_first_pair_low6 ?low ?upper mod 10000"
    by (rule trans[OF sym[OF first_pair_reduction] first_pair_mod])
  have time:
    "double_reverse_T_run (18 + 4 * blocks) 196 =
      double_reverse_T_run 2 ?source"
    using double_reverse_T_run_source_root_square[of "16 + 4 * blocks" 2 196]
    by (simp add: algebra_simps)
  show ?thesis using low4_transport pair_low4 time by simp
qed

lemma double_reverse_seed196_four_block_source_width:
  "1000 \<le> double_reverse_T_run (16 + 4 * blocks) 196"
proof -
  let ?source = "double_reverse_T_run (16 + 4 * blocks) 196"
  have guard: "?source mod 100000 \<in>
      double_reverse_seed196_phase_guards blocks"
    by (rule double_reverse_seed196_four_block_source_guard)
  have low_bound: "1000 \<le> ?source mod 100000"
    by (rule double_reverse_seed196_phase_guard_low5_bound[OF guard])
  have mod_bound: "?source mod 100000 \<le> ?source"
    by (rule mod_less_eq_dividend)
  show ?thesis by (rule le_trans[OF low_bound mod_bound])
qed

lemma double_reverse_seed196_pair_sheet_source_width:
  "1000 \<le> double_reverse_T_run (18 + 4 * blocks) 196"
proof -
  let ?source = "double_reverse_T_run (16 + 4 * blocks) 196"
  let ?low = "?source mod 100000"
  let ?upper = "threshold5_digit ((?source div 100000) mod 10) = 1"
  have guard: "?low \<in> double_reverse_seed196_phase_guards blocks"
    by (rule double_reverse_seed196_four_block_source_guard)
  have admitted:
    "?low \<in> double_reverse_seed196_entry_guards \<union>
      double_reverse_seed196_first_guards \<union>
      double_reverse_seed196_second_guards \<union>
      double_reverse_seed196_third_guards"
    by (rule double_reverse_seed196_phase_guard_is_admitted[OF guard])
  have unit: "?low mod 10 = 8"
    by (rule double_reverse_seed196_guard_unit_digit[OF admitted])
  have pair_bound:
    "1000 \<le> double_reverse_seed196_first_pair_low6 ?low ?upper"
    by (rule double_reverse_seed196_phase_guard_pair_low6_bound[OF guard])
  have first_pair:
    "double_reverse_T_run 2 ?source mod 1000000 =
      double_reverse_seed196_first_pair_low6 ?low ?upper"
    by (rule double_reverse_seed196_first_pair_source_exact[OF _ unit]; simp)
  have output_low_bound:
    "1000 \<le> double_reverse_T_run 2 ?source mod 1000000"
    using pair_bound first_pair by simp
  have output_mod_bound:
    "double_reverse_T_run 2 ?source mod 1000000 \<le>
      double_reverse_T_run 2 ?source"
    by (rule mod_less_eq_dividend)
  have pair_output_bound:
    "1000 \<le> double_reverse_T_run 2 ?source"
    by (rule le_trans[OF output_low_bound output_mod_bound])
  have time:
    "double_reverse_T_run (18 + 4 * blocks) 196 =
      double_reverse_T_run 2 ?source"
    using double_reverse_T_run_source_root_square[of "16 + 4 * blocks" 2 196]
    by (simp add: algebra_simps)
  show ?thesis using pair_output_bound time by simp
qed

lemma double_reverse_seed196_even_generation_decomposition:
  fixes generation :: nat
  assumes even: "generation mod 2 = 0"
      and admitted: "generation \<ge> 16"
  shows "((generation - 16) mod 4 = 0 \<and>
      generation = 16 + 4 * ((generation - 16) div 4)) \<or>
    ((generation - 16) mod 4 = 2 \<and>
      generation = 18 + 4 * ((generation - 16) div 4))"
proof -
  let ?tail = "generation - 16"
  let ?blocks = "?tail div 4"
  have split: "?tail = 4 * ?blocks + ?tail mod 4"
    using div_mult_mod_eq[of ?tail 4] by (simp add: mult.commute)
  have generation_split: "generation = 16 + ?tail"
    using admitted by simp
  have generation_mod:
    "generation mod 2 = (16 + ?tail) mod 2"
    by (rule arg_cong[where f="\<lambda>r::nat. r mod 2", OF generation_split])
  have sixteen_mod: "(16::nat) mod 2 = (0::nat) mod 2"
    by simp
  have offset_mod: "(16 + ?tail) mod 2 = (0 + ?tail) mod 2"
    by (rule mod_add_cong[OF sixteen_mod refl])
  have tail_even: "?tail mod 2 = 0"
    using even generation_mod offset_mod by simp
  have two_dvd_four: "2 dvd (4::nat)"
    by simp
  have remainder_even: "(?tail mod 4) mod 2 = 0"
    using mod_mod_cancel[OF two_dvd_four] tail_even by simp
  have remainder_bound: "?tail mod 4 < 4"
    by (rule mod_less_divisor) simp
  have remainder_values:
    "?tail mod 4 = 0 \<or> ?tail mod 4 = 1 \<or>
      ?tail mod 4 = 2 \<or> ?tail mod 4 = 3"
    using remainder_bound by arith
  have remainder_cases: "?tail mod 4 = 0 \<or> ?tail mod 4 = 2"
    using remainder_even remainder_values by auto
  from remainder_cases show ?thesis
  proof (elim disjE)
    assume zero: "?tail mod 4 = 0"
    have tail_block: "?tail = 4 * ?blocks"
      using split zero by simp
    have shifted: "16 + ?tail = 16 + 4 * ?blocks"
      by (rule arg_cong[where f="\<lambda>r::nat. 16 + r", OF tail_block])
    have generation_block: "generation = 16 + 4 * ?blocks"
      by (rule trans[OF generation_split shifted])
    show ?thesis using generation_block zero by blast
  next
    assume two: "?tail mod 4 = 2"
    have tail_pair: "?tail = 4 * ?blocks + 2"
      using split two by simp
    have shifted: "16 + ?tail = 16 + (4 * ?blocks + 2)"
      by (rule arg_cong[where f="\<lambda>r::nat. 16 + r", OF tail_pair])
    have generation_pair: "generation = 18 + 4 * ?blocks"
      using generation_split shifted by (simp add: algebra_simps)
    show ?thesis using generation_pair two by blast
  qed
qed

theorem double_reverse_seed196_even_generation_source_width:
  assumes even: "generation mod 2 = 0"
      and admitted: "generation \<ge> 16"
  shows "1000 \<le> double_reverse_T_run generation 196"
proof -
  have decomposition:
    "((generation - 16) mod 4 = 0 \<and>
        generation = 16 + 4 * ((generation - 16) div 4)) \<or>
      ((generation - 16) mod 4 = 2 \<and>
        generation = 18 + 4 * ((generation - 16) div 4))"
    by (rule double_reverse_seed196_even_generation_decomposition[OF even admitted])
  from decomposition show ?thesis
  proof (elim disjE)
    assume block_case:
      "(generation - 16) mod 4 = 0 \<and>
        generation = 16 + 4 * ((generation - 16) div 4)"
    let ?blocks = "(generation - 16) div 4"
    have generation_block: "generation = 16 + 4 * ?blocks"
      using block_case by blast
    have source_bound:
      "1000 \<le> double_reverse_T_run (16 + 4 * ?blocks) 196"
      by (rule double_reverse_seed196_four_block_source_width)
    show ?thesis using generation_block source_bound by simp
  next
    assume pair_case:
      "(generation - 16) mod 4 = 2 \<and>
        generation = 18 + 4 * ((generation - 16) div 4)"
    let ?blocks = "(generation - 16) div 4"
    have generation_pair: "generation = 18 + 4 * ?blocks"
      using pair_case by blast
    have source_bound:
      "1000 \<le> double_reverse_T_run (18 + 4 * ?blocks) 196"
      by (rule double_reverse_seed196_pair_sheet_source_width)
    show ?thesis using generation_pair source_bound by simp
  qed
qed

theorem double_reverse_seed196_even_generation_source_low4:
  assumes even: "generation mod 2 = 0"
      and admitted: "generation \<ge> 16"
  shows "double_reverse_T_run generation 196 mod 10000 =
    (if (generation - 16) mod 4 = 0 then
       (if double_reverse_seed196_phase_index
            ((generation - 16) div 4) = 0 then 3488
        else if double_reverse_seed196_phase_index
            ((generation - 16) div 4) = 1 then 1568
        else if double_reverse_seed196_phase_index
            ((generation - 16) div 4) = 2 then 988 else 8388)
     else
       (if double_reverse_seed196_phase_index
            ((generation - 16) div 4) = 0 then 7342
        else if double_reverse_seed196_phase_index
            ((generation - 16) div 4) = 1 then 742
        else if double_reverse_seed196_phase_index
            ((generation - 16) div 4) = 2 then 7542 else 5342))"
proof -
  let ?tail = "generation - 16"
  let ?blocks = "?tail div 4"
  have decomposition:
    "(?tail mod 4 = 0 \<and> generation = 16 + 4 * ?blocks) \<or>
      (?tail mod 4 = 2 \<and> generation = 18 + 4 * ?blocks)"
    by (rule double_reverse_seed196_even_generation_decomposition[OF even admitted])
  from decomposition show ?thesis
  proof (elim disjE)
    assume block_case:
      "?tail mod 4 = 0 \<and> generation = 16 + 4 * ?blocks"
    have zero: "?tail mod 4 = 0" using block_case by blast
    have generation_block: "generation = 16 + 4 * ?blocks"
      using block_case by blast
    show ?thesis using generation_block zero
      double_reverse_seed196_four_block_source_low4[of ?blocks]
      by simp
  next
    assume pair_case:
      "?tail mod 4 = 2 \<and> generation = 18 + 4 * ?blocks"
    have two: "?tail mod 4 = 2" using pair_case by blast
    have generation_pair: "generation = 18 + 4 * ?blocks"
      using pair_case by blast
    show ?thesis using generation_pair two
      double_reverse_seed196_pair_sheet_source_low4[of ?blocks]
      by simp
  qed
qed

lemmas double_reverse_seed196_source_low_band_audit_bundle =
  double_reverse_seed196_phase_guard_is_admitted
  double_reverse_seed196_four_block_source_guard
  double_reverse_seed196_phase_guard_low4
  double_reverse_seed196_phase_guard_pair_low4
  double_reverse_seed196_phase_guard_low5_bound
  double_reverse_seed196_phase_guard_pair_low6_bound
  double_reverse_seed196_four_block_source_low4
  double_reverse_seed196_pair_sheet_source_low4
  double_reverse_seed196_four_block_source_width
  double_reverse_seed196_pair_sheet_source_width
  double_reverse_seed196_even_generation_decomposition
  double_reverse_seed196_even_generation_source_width
  double_reverse_seed196_even_generation_source_low4
  double_reverse_seed196_generation16_low5_anchor

ML \<open>
  val checked = @{thms double_reverse_seed196_source_low_band_audit_bundle};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Seed-196 source low-band refinement has oracle dependencies, including skip_proof";
\<close>

end
