theory Reverse_Q19_Half_Field_Step
  imports Reverse_Native_Hinge_Successor Reverse_Native_Slab_Core
begin

text \<open>The folded Q19 half is read from both ends of the same emitted
source.  The carry at the middle and the final physical carry are kept
separate; they determine the right-hand emission and the width change.\<close>

lemma q19_symmetric_odd_reconstruction:
  fixes field :: "nat list"
  assumes symmetric: "rev field = field"
    and width: "length field = 2 * n + 1"
    and low: "take n field = half"
    and center: "field ! n = middle"
  shows "field = half @ [middle] @ rev half"
proof -
  have index: "n < length field" using width by arith
  have prefix: "take (Suc n) field = half @ [middle]"
    using take_Suc_conv_app_nth[OF index] low center by simp
  have reconstructed:
    "punctured_q19_decode_half (reverse_laurent_source_half field)
      (reverse_laurent_source_odd field) = field"
    by (rule reverse_laurent_half_reconstructs_symmetric_source[OF symmetric])
  show ?thesis using reconstructed width prefix
    by (simp add: reverse_laurent_source_half_def reverse_laurent_source_odd_def
        punctured_q19_decode_half_def)
qed

lemma q19_symmetric_even_reconstruction:
  fixes field :: "nat list"
  assumes symmetric: "rev field = field"
    and width: "length field = 2 * n"
    and low: "take n field = half"
  shows "field = half @ rev half"
proof -
  have reconstructed:
    "punctured_q19_decode_half (reverse_laurent_source_half field)
      (reverse_laurent_source_odd field) = field"
    by (rule reverse_laurent_half_reconstructs_symmetric_source[OF symmetric])
  show ?thesis using reconstructed width low
    by (simp add: reverse_laurent_source_half_def reverse_laurent_source_odd_def
        punctured_q19_decode_half_def)
qed

theorem q19_half_birth_even:
  assumes nonempty: "w \<noteq> []"
    and birth: "carry_out False (w @ rev w)"
    and L_def: "L = emit False w"
    and H_def: "H = rev (emit (carry_out False w) (rev w))"
    and half_def: "half = map (\<lambda>(a,b). a+b) (zip L (take (length w) (1#H)))"
  shows "take (length w) (step (w @ rev w)) = half"
    and "step (w @ rev w) ! length w = 2 * last H"
    and "length (step (w @ rev w)) = 2 * length w + 1"
    and "step (w @ rev w) = half @ [2 * last H] @ rev half"
proof -
  have end_carry: "carry_out (carry_out False w) (rev w)"
    using birth by (simp add: carry_out_append)
  have low: "reverse_native_hinge_next_half w (carry_out False w) =
      take (length w) (step (w @ rev w))"
    using hinge_physical_list_half[of w "[]"] by (simp add: carry_out_def)
  have next_half: "reverse_native_hinge_next_half w (carry_out False w) = half"
    using hinge_emit_general[of w "carry_out False w"] end_carry
    by (simp add: L_def H_def half_def rev_append)
  have hlow: "take (length w) (step (w @ rev w)) = half"
    using low next_half by simp
  have hcenter: "step (w @ rev w) ! length w = 2 * last H"
    using nonempty end_carry
    by (simp add: step_def digits_def emit_append carry_out_append H_def
        nth_append last_conv_nth rev_nth)
  have hwidth: "length (step (w @ rev w)) = 2 * length w + 1"
    using birth by (simp add: length_digits_exact)
  show "take (length w) (step (w @ rev w)) = half" by (rule hlow)
  show "step (w @ rev w) ! length w = 2 * last H" by (rule hcenter)
  show "length (step (w @ rev w)) = 2 * length w + 1" by (rule hwidth)
  show "step (w @ rev w) = half @ [2 * last H] @ rev half"
    by (rule q19_symmetric_odd_reconstruction[OF step_symmetric hwidth hlow hcenter])
qed

theorem q19_half_quiet_odd:
  assumes quiet: "\<not> carry_out False (w @ [z] @ rev w)"
    and c_def: "c = carry_out False w"
    and m_def: "m = (z + (if c then 1 else 0)) mod 10"
    and L_def: "L = emit False w"
    and H_def: "H = rev (emit (carry_apply (domain z) c) (rev w))"
    and half_def: "half = map (\<lambda>(a,b). a+b) (zip L H)"
  shows "take (length w) (step (w @ [z] @ rev w)) = half"
    and "step (w @ [z] @ rev w) ! length w = 2 * m"
    and "length (step (w @ [z] @ rev w)) = 2 * length w + 1"
    and "step (w @ [z] @ rev w) = half @ [2 * m] @ rev half"
proof -
  have end_carry: "\<not> carry_out (carry_apply (domain z) c) (rev w)"
    using quiet by (simp add: carry_out_append carry_out_def c_def)
  have low: "reverse_native_hinge_next_half w (carry_apply (domain z) c) =
      take (length w) (step (w @ [z] @ rev w))"
    using hinge_physical_list_half[of w "[z]"] by (simp add: carry_out_def c_def)
  have next_half: "reverse_native_hinge_next_half w (carry_apply (domain z) c) = half"
    using hinge_emit_general[of w "carry_apply (domain z) c"] end_carry
    by (simp add: L_def H_def half_def rev_append)
  have hlow: "take (length w) (step (w @ [z] @ rev w)) = half"
    using low next_half by simp
  have hcenter: "step (w @ [z] @ rev w) ! length w = 2 * m"
    using quiet by (simp add: step_def digits_def emit_append carry_out_append
       carry_out_def c_def m_def nth_append rev_nth)
  have hwidth: "length (step (w @ [z] @ rev w)) = 2 * length w + 1"
    using quiet by (simp add: length_digits_exact)
  show "take (length w) (step (w @ [z] @ rev w)) = half" by (rule hlow)
  show "step (w @ [z] @ rev w) ! length w = 2 * m" by (rule hcenter)
  show "length (step (w @ [z] @ rev w)) = 2 * length w + 1" by (rule hwidth)
  show "step (w @ [z] @ rev w) = half @ [2 * m] @ rev half"
    by (rule q19_symmetric_odd_reconstruction[OF step_symmetric hwidth hlow hcenter])
qed

theorem q19_half_birth_odd:
  assumes nonempty: "w \<noteq> []"
    and birth: "carry_out False (w @ [z] @ rev w)"
    and c_def: "c = carry_out False w"
    and m_def: "m = (z + (if c then 1 else 0)) mod 10"
    and L_def: "L = emit False w"
    and H_def: "H = rev (emit (carry_apply (domain z) c) (rev w))"
    and half_def: "half = map (\<lambda>(a,b). a+b) (zip L (take (length w) (1#H)))"
  shows "take (length w) (step (w @ [z] @ rev w)) = half"
    and "step (w @ [z] @ rev w) ! length w = m + last H"
    and "length (step (w @ [z] @ rev w)) = 2 * (length w + 1)"
    and "step (w @ [z] @ rev w) =
      (half @ [m + last H]) @ rev (half @ [m + last H])"
proof -
  have end_carry: "carry_out (carry_apply (domain z) c) (rev w)"
    using birth by (simp add: carry_out_append carry_out_def c_def)
  have low: "reverse_native_hinge_next_half w (carry_apply (domain z) c) =
      take (length w) (step (w @ [z] @ rev w))"
    using hinge_physical_list_half[of w "[z]"] by (simp add: carry_out_def c_def)
  have next_half: "reverse_native_hinge_next_half w (carry_apply (domain z) c) = half"
    using hinge_emit_general[of w "carry_apply (domain z) c"] end_carry
    by (simp add: L_def H_def half_def rev_append)
  have hlow: "take (length w) (step (w @ [z] @ rev w)) = half"
    using low next_half by simp
  have hcenter: "step (w @ [z] @ rev w) ! length w = m + last H"
    using nonempty birth by (simp add: step_def digits_def emit_append carry_out_append
        carry_out_def H_def c_def m_def nth_append last_conv_nth rev_nth)
  have hwidth: "length (step (w @ [z] @ rev w)) = 2 * (length w + 1)"
    using birth by (simp add: length_digits_exact algebra_simps)
  show "take (length w) (step (w @ [z] @ rev w)) = half" by (rule hlow)
  show "step (w @ [z] @ rev w) ! length w = m + last H" by (rule hcenter)
  show "length (step (w @ [z] @ rev w)) = 2 * (length w + 1)" by (rule hwidth)
  have prefix: "take (Suc (length w)) (step (w @ [z] @ rev w)) =
      half @ [m + last H]"
  proof -
    have index: "length w < length (step (w @ [z] @ rev w))"
      using hwidth by arith
    show ?thesis
      using take_Suc_conv_app_nth[OF index] hlow hcenter by simp
  qed
  show "step (w @ [z] @ rev w) =
      (half @ [m + last H]) @ rev (half @ [m + last H])"
  proof (rule q19_symmetric_even_reconstruction[OF step_symmetric,
      where n="Suc (length w)" and half="half @ [m + last H]"])
    show "length (step (w @ [z] @ rev w)) = 2 * Suc (length w)"
      using birth by (simp add: length_digits_exact algebra_simps)
    show "take (Suc (length w)) (step (w @ [z] @ rev w)) =
        half @ [m + last H]" by (rule prefix)
  qed
qed


definition q19_six_phase_symbol :: "nat \<Rightarrow> bool" where
  "q19_six_phase_symbol s \<longleftrightarrow>
    s = 2 \<or> s = 4 \<or> s = 8 \<or> s = 16 \<or> s = 14 \<or> s = 10"

definition q19_six_phase_next :: "nat \<Rightarrow> nat" where
  "q19_six_phase_next s = 2 * ((s + (if 10 \<le> s then 1 else 0)) mod 10)"

lemma q19_six_phase_reset:
  assumes "q19_six_phase_symbol s"
  shows "carry_apply (domain s) inlet = (10 \<le> s)"
  using assms unfolding q19_six_phase_symbol_def domain_def
  by (cases inlet; auto)

lemma q19_six_phase_return:
  "q19_six_phase_next 2 = 4"
  "q19_six_phase_next 4 = 8"
  "q19_six_phase_next 8 = 16"
  "q19_six_phase_next 16 = 14"
  "q19_six_phase_next 14 = 10"
  "q19_six_phase_next 10 = 2"
  by (simp_all add: q19_six_phase_next_def)

theorem q19_uniform_reset_physical_cell:
  assumes valid: "valid_pair (before @ [s, s, s] @ after)"
    and symbol: "q19_six_phase_symbol s"
  shows "step (before @ [s, s, s] @ after) ! (length before + 1) =
    q19_six_phase_next s"
proof -
  let ?source = "before @ [s, s, s] @ after"
  let ?prefix = "before @ [s]"
  let ?suffix = "s # after"
  have bounded: "\<forall>x\<in>set ?source. x < 19"
  proof
    fix x assume "x \<in> set ?source"
    then have "x \<le> 18" using valid by (auto simp: valid_pair_def)
    then show "x < 19" by arith
  qed
  have prefix: "\<forall>x\<in>set ?prefix. x < 19" using bounded by auto
  have suffix: "\<forall>x\<in>set ?suffix. x < 19" using bounded by auto
  have cell: "s < 19" using symbol by (auto simp: q19_six_phase_symbol_def)
  have left: "carry_out False ?prefix = (10 \<le> s)"
    using q19_six_phase_reset[OF symbol, of "carry_out False before"]
    by (simp add: carry_out_append carry_out_def)
  have right: "carry_out False (rev ?suffix) = (10 \<le> s)"
    using q19_six_phase_reset[OF symbol, of "carry_out False (rev after)"]
    by (simp add: carry_out_append carry_out_def)
  have through: "carry_apply (domain s) (10 \<le> s) = (10 \<le> s)"
    by (rule q19_six_phase_reset[OF symbol])
  have selected:
    "reverse_emit (reverse_left_fold ?prefix) s (reverse_right_fold ?suffix) =
      q19_six_phase_next s"
  proof (cases "carry_out False ?source")
    case True
    have emitted: "reverse_emit (reverse_left_fold ?prefix) s (reverse_right_fold ?suffix) =
      growth_pair_step s (last ?prefix) (carry_bit (carry_out False ?prefix))
        (carry_bit (carry_apply (domain s) (carry_out False (rev ?suffix))))"
      by (rule reverse_emit_growth_interior[OF prefix suffix cell _])
        (use True in \<open>simp_all add: carry_out_append carry_out_def\<close>)
    show ?thesis using emitted left right through
      by (simp add: growth_pair_step_def carry_bit_def q19_six_phase_next_def)
  next
    case False
    have emitted: "reverse_emit (reverse_left_fold ?prefix) s (reverse_right_fold ?suffix) =
      mirror_pair_step s (carry_bit (carry_out False ?prefix))
        (carry_bit (carry_out False (rev ?suffix)))"
      by (rule reverse_emit_no_growth_cell[OF prefix suffix cell])
        (use False in \<open>simp add: carry_out_append carry_out_def\<close>)
    show ?thesis using emitted left right
      by (simp add: mirror_pair_step_def carry_bit_def q19_six_phase_next_def)
  qed
  show ?thesis using slab_core_physical_scan[OF valid, of "length before + 1"] selected
    by (simp add: nth_append take_append drop_append)
qed


theorem q19_uniform_reset_physical_at:
  assumes valid: "valid_pair source" and positive: "0 < i"
    and bound: "Suc i < length source"
    and cell: "source ! (i - 1) = s" "source ! i = s" "source ! Suc i = s"
    and symbol: "q19_six_phase_symbol s"
  shows "step source ! i = q19_six_phase_next s"
proof -
  let ?before = "take (i - 1) source"
  let ?after = "drop (Suc (Suc i)) source"
  have ibound: "i < length source" using bound by arith
  have prior: "i - 1 < length source" using positive ibound by arith
  have take1: "take i source = ?before @ [source ! (i - 1)]"
    using take_Suc_conv_app_nth[OF prior] positive by simp
  have take2: "take (Suc i) source = ?before @ [source ! (i - 1), source ! i]"
    using take_Suc_conv_app_nth[OF ibound] take1 by simp
  have split: "source = ?before @ [s, s, s] @ ?after"
    using id_take_nth_drop[OF bound] take2 cell by simp
  have len: "length ?before + 1 = i" using positive ibound by simp
  have valid': "valid_pair (?before @ [s, s, s] @ ?after)"
    using valid split by simp
  show ?thesis using q19_uniform_reset_physical_cell[OF valid' symbol] split len by simp
qed

lemma q19_six_phase_symbol_next:
  assumes "q19_six_phase_symbol s"
  shows "q19_six_phase_symbol (q19_six_phase_next s)"
  using assms by (auto simp: q19_six_phase_symbol_def q19_six_phase_next_def)

lemma q19_six_phase_symbol_iterated:
  "q19_six_phase_symbol ((q19_six_phase_next ^^ n) 2)"
proof (induction n)
  case 0
  then show ?case by (simp add: q19_six_phase_symbol_def)
next
  case (Suc n)
  then show ?case using q19_six_phase_symbol_next by simp
qed

theorem q19_uniform_two_causal_return:
  assumes valid: "valid_pair source"
    and left: "ticks \<le> i"
    and right: "i + ticks < length source"
    and initial: "\<And>j. i - ticks \<le> j \<Longrightarrow> j \<le> i + ticks \<Longrightarrow> source ! j = 2"
  shows "run step ticks source ! i = (q19_six_phase_next ^^ ticks) 2"
  using left right initial
proof (induction ticks arbitrary: i)
  case 0
  then show ?case by simp
next
  case (Suc ticks)
  let ?value = "(q19_six_phase_next ^^ ticks) 2"
  let ?current = "run step ticks source"
  have width: "length source \<le> length ?current"
    using reverse_add_run_width_bounds[of source ticks] by simp
  have valid_current: "valid_pair ?current" by (rule valid_pair_run[OF valid])
  have positive: "0 < i" using Suc.prems(1) by arith
  have bound: "Suc i < length ?current" using Suc.prems(2) width by arith
  have at: "?current ! j = ?value" if near: "i - 1 \<le> j" "j \<le> Suc i" for j
  proof -
    have lower: "ticks \<le> j" using Suc.prems(1) near by arith
    have upper: "j + ticks < length source" using Suc.prems(2) near by arith
    have initial': "source ! k = 2"
      if "j - ticks \<le> k" "k \<le> j + ticks" for k
      using Suc.prems(3)[of k] Suc.prems(1) near that by simp
    show ?thesis by (rule Suc.IH[OF lower upper initial'])
  qed
  have local: "?current ! (i - 1) = ?value" "?current ! i = ?value"
      "?current ! Suc i = ?value"
    using at[of "i - 1"] at[of i] at[of "Suc i"] positive by auto
  have next_cell: "step ?current ! i = q19_six_phase_next ?value"
    by (rule q19_uniform_reset_physical_at[OF valid_current positive bound local
        q19_six_phase_symbol_iterated])
  show ?case using next_cell by (simp add: run_commutes_with_step funpow_swap1)
qed

corollary q19_uniform_two_six_tick_return:
  assumes valid: "valid_pair source" and left: "6 \<le> i"
    and right: "i + 6 < length source"
    and initial: "\<And>j. i - 6 \<le> j \<Longrightarrow> j \<le> i + 6 \<Longrightarrow> source ! j = 2"
  shows "run step 6 source ! i = 2"
proof -
  have six: "(6::nat) = Suc (Suc (Suc (Suc (Suc (Suc 0)))))" by simp
  show ?thesis
    using q19_uniform_two_causal_return[OF valid left right initial]
    by (simp only: six funpow.simps comp_apply id_apply q19_six_phase_return)
qed


ML \<open>
  val checked = @{thms q19_half_birth_even q19_half_quiet_odd q19_half_birth_odd
    q19_uniform_reset_physical_at q19_uniform_two_causal_return
    q19_uniform_two_six_tick_return};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Q19 half-field step depends on an oracle";
  val _ = if Thm_Deps.has_skip_proof checked then
    error "Skipped Q19 half-field step proof" else ();
\<close>

end
