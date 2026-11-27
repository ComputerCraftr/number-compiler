theory Reverse_Native_Slab_Core
  imports Reverse_Native_Slab_Clock
begin

text \<open>The local packet assumes the authenticated reset-core carry at
both inlets.  It does not establish the complete source collars or choose the
physical clock.  The first physical birth erases the 8/17 lift distinction;
the later three interior steps then use a true carry at each inlet.\<close>

definition slab_core_bit :: "bool \<Rightarrow> nat" where
  "slab_core_bit b = (if b then 1 else 0)"

definition slab_core_initial :: "bool \<Rightarrow> bool \<Rightarrow> nat" where
  "slab_core_initial a b = 18 - slab_core_bit a - slab_core_bit b"

definition slab_core_birth :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "slab_core_birth a b = reverse_native_slab_birth a b True True"

definition slab_core_quiet :: "nat \<Rightarrow> nat" where
  "slab_core_quiet a = reverse_native_slab_quiet a True True"

definition slab_core_clock_admitted :: "bool list \<Rightarrow> bool" where
  "slab_core_clock_admitted clock \<longleftrightarrow>
    clock = [True, False, True, True] \<or>
    clock = [True, True, True, False]"

lemma slab_core_clock_guard:
  "slab_core_clock_admitted [True, False, True, True]"
  "slab_core_clock_admitted [True, True, True, False]"
  "\<not> slab_core_clock_admitted [True, False, True, False]"
  by (simp_all add: slab_core_clock_admitted_def)

lemma slab_core_true_carry:
  assumes "10 \<le> s"
  shows "carry_apply (domain s) incoming"
  using assms by (simp add: domain_def)

lemma slab_core_prefix_saturation:
  assumes "10 \<le> s"
  shows "carry_out incoming (prefix @ [s])"
  using slab_core_true_carry[OF assms, of "carry_out incoming prefix"]
  by (simp add: carry_out_append carry_out_def)

lemma slab_core_outer_forces_birth:
  assumes valid: "valid_pair source" and outer: "10 \<le> hd source"
  shows "carry_out False source"
proof -
  have nonempty: "source \<noteq> []" and symmetric: "rev source = source"
    using valid by (auto simp: valid_pair_def)
  obtain prefix symbol where split: "source = prefix @ [symbol]"
    using nonempty by (cases source rule: rev_cases) auto
  have "last source = hd source" using nonempty symmetric by (metis hd_rev)
  then have "10 \<le> symbol" using split outer by simp
  then show ?thesis using split slab_core_prefix_saturation by metis
qed

theorem slab_core_selected_emission:
  assumes prefix: "\<forall>x\<in>set (before @ [left]). x < 19"
      and suffix: "\<forall>x\<in>set (right # after). x < 19"
      and current: "10 \<le> s" "s < 19"
      and neighbours: "10 \<le> left" "10 \<le> right"
  defines "grows \<equiv> carry_out
    (carry_apply (domain s) (carry_out False (before @ [left]))) (right # after)"
  shows "reverse_emit (reverse_left_fold (before @ [left])) s
      (reverse_right_fold (right # after)) =
    (if grows then slab_core_birth left s else slab_core_quiet s)"
proof -
  have left: "carry_out False (before @ [left])"
    by (rule slab_core_prefix_saturation[OF neighbours(1)])
  have right: "carry_out False (rev (right # after))"
    using slab_core_prefix_saturation[OF neighbours(2), of False "rev after"] by simp
  have through: "carry_apply (domain s) (carry_out False (rev (right # after)))"
    by (rule slab_core_true_carry[OF current(1)])
  show ?thesis
  proof (cases grows)
    case True
    have result: "reverse_emit (reverse_left_fold (before @ [left])) s
        (reverse_right_fold (right # after)) =
      growth_pair_step s (last (before @ [left])) (carry_bit (carry_out False (before @ [left])))
        (carry_bit (carry_apply (domain s) (carry_out False (rev (right # after)))))"
      by (rule reverse_emit_growth_interior[OF prefix suffix current(2) _])
        (use True in \<open>simp_all add: grows_def\<close>)
    show ?thesis using result True left through
      by (simp add: slab_core_birth_def reverse_native_slab_birth_def
          reverse_native_slab_digit_def growth_pair_step_def carry_bit_def)
  next
    case False
    have result: "reverse_emit (reverse_left_fold (before @ [left])) s
        (reverse_right_fold (right # after)) =
      mirror_pair_step s (carry_bit (carry_out False (before @ [left])))
        (carry_bit (carry_out False (rev (right # after))))"
      by (rule reverse_emit_no_growth_cell[OF prefix suffix current(2)])
        (use False in \<open>simp add: grows_def\<close>)
    show ?thesis using result False left right
      by (simp add: slab_core_quiet_def reverse_native_slab_quiet_def
          reverse_native_slab_digit_def mirror_pair_step_def carry_bit_def)
  qed
qed

lemma slab_core_source_birth:
  assumes "reverse_native_slab_source_symbol a"
      and "reverse_native_slab_source_symbol b"
  shows "reverse_native_slab_birth a b (9 < a) (9 < b) =
    slab_core_initial (a \<noteq> 18) (b \<noteq> 18)"
  using assms unfolding reverse_native_slab_source_symbol_def
    reverse_native_slab_birth_def reverse_native_slab_digit_def
    slab_core_initial_def slab_core_bit_def carry_bit_def
  by auto

theorem slab_core_first_selected_birth:
  assumes prefix: "\<forall>x\<in>set (before @ [left]). x < 19"
      and suffix: "\<forall>x\<in>set after. x < 19"
      and source: "reverse_native_slab_source_symbol left"
        "reverse_native_slab_source_symbol s"
      and growth: "carry_out
        (carry_apply (domain s) (carry_out False (before @ [left]))) after"
  shows "reverse_emit (reverse_left_fold (before @ [left])) s
      (reverse_right_fold after) = slab_core_initial (left \<noteq> 18) (s \<noteq> 18)"
proof -
  have cell: "s < 19" using source(2)
    by (auto simp: reverse_native_slab_source_symbol_def)
  have left: "carry_out False (before @ [left]) = (9 < left)"
    using reverse_native_slab_source_reset[OF source(1), of "carry_out False before"]
    by (simp add: carry_out_append carry_out_def)
  have through: "carry_apply (domain s) (carry_out False (rev after)) = (9 < s)"
    by (rule reverse_native_slab_source_reset[OF source(2)])
  have result: "reverse_emit (reverse_left_fold (before @ [left])) s
      (reverse_right_fold after) =
    growth_pair_step s left (carry_bit (9 < left)) (carry_bit (9 < s))"
    using reverse_emit_growth_interior[OF prefix suffix cell _ growth] left through
    by simp
  show ?thesis using result slab_core_source_birth[OF source]
    by (simp add: slab_core_initial_def slab_core_bit_def
        reverse_native_slab_birth_def reverse_native_slab_digit_def
        growth_pair_step_def)
qed

lemma slab_core_second_reset:
  assumes "16 \<le> a" "a \<le> 18" "16 \<le> b" "b \<le> 18"
  shows "14 \<le> slab_core_quiet a \<and> slab_core_quiet a \<le> 18"
    and "14 \<le> slab_core_birth a b \<and> slab_core_birth a b \<le> 18"
proof -
  have aa: "a = 16 \<or> a = 17 \<or> a = 18" using assms by arith
  have bb: "b = 16 \<or> b = 17 \<or> b = 18" using assms by arith
  show "14 \<le> slab_core_quiet a \<and> slab_core_quiet a \<le> 18"
    using aa unfolding slab_core_quiet_def reverse_native_slab_quiet_def
      reverse_native_slab_digit_def carry_bit_def by auto
  show "14 \<le> slab_core_birth a b \<and> slab_core_birth a b \<le> 18"
    using aa bb unfolding slab_core_birth_def reverse_native_slab_birth_def
      reverse_native_slab_digit_def carry_bit_def by auto
qed

lemma slab_core_third_reset:
  assumes "14 \<le> a" "a \<le> 18" "14 \<le> b" "b \<le> 18"
  shows "10 \<le> slab_core_quiet a \<and> slab_core_quiet a \<le> 18"
    and "10 \<le> slab_core_birth a b \<and> slab_core_birth a b \<le> 18"
proof -
  have aa: "a = 14 \<or> a = 15 \<or> a = 16 \<or> a = 17 \<or> a = 18"
    using assms by arith
  have bb: "b = 14 \<or> b = 15 \<or> b = 16 \<or> b = 17 \<or> b = 18"
    using assms by arith
  show "10 \<le> slab_core_quiet a \<and> slab_core_quiet a \<le> 18"
    using aa unfolding slab_core_quiet_def reverse_native_slab_quiet_def
      reverse_native_slab_digit_def carry_bit_def by auto
  show "10 \<le> slab_core_birth a b \<and> slab_core_birth a b \<le> 18"
    using aa bb unfolding slab_core_birth_def reverse_native_slab_birth_def
      reverse_native_slab_digit_def carry_bit_def by auto
qed

lemma slab_core_1011_packet:
  fixes a b c d :: bool
    and u v w x y :: nat
  defines "u \<equiv> slab_core_initial c d"
    and "v \<equiv> slab_core_initial b c"
    and "w \<equiv> slab_core_initial a b"
    and "x \<equiv> slab_core_birth (slab_core_quiet u) (slab_core_quiet v)"
    and "y \<equiv> slab_core_birth (slab_core_quiet v) (slab_core_quiet w)"
  shows "slab_core_birth x y = 18 - 2 * (slab_core_bit a + 3 * slab_core_bit b +
      3 * slab_core_bit c + slab_core_bit d) \<and>
    reverse_native_slab_digit x True =
      9 - 2 * (slab_core_bit b + 2 * slab_core_bit c + slab_core_bit d)"
  unfolding u_def v_def w_def x_def y_def slab_core_initial_def slab_core_bit_def
    slab_core_birth_def slab_core_quiet_def reverse_native_slab_birth_def
    reverse_native_slab_quiet_def reverse_native_slab_digit_def carry_bit_def
  by (cases a; cases b; cases c; cases d; simp_all)

lemma slab_core_1110_packet:
  fixes a b c d :: bool
    and u v w x y z :: nat
  defines "u \<equiv> slab_core_initial c d"
    and "v \<equiv> slab_core_initial b c"
    and "w \<equiv> slab_core_initial a b"
    and "x \<equiv> slab_core_birth u v"
    and "y \<equiv> slab_core_birth v w"
    and "z \<equiv> slab_core_birth x y"
  shows "slab_core_quiet z = 18 - 2 * (slab_core_bit a + 3 * slab_core_bit b +
      3 * slab_core_bit c + slab_core_bit d) \<and>
    reverse_native_slab_digit z True =
      9 - (slab_core_bit a + 3 * slab_core_bit b +
      3 * slab_core_bit c + slab_core_bit d)"
  unfolding u_def v_def w_def x_def y_def z_def slab_core_initial_def slab_core_bit_def
    slab_core_birth_def slab_core_quiet_def reverse_native_slab_birth_def
    reverse_native_slab_quiet_def reverse_native_slab_digit_def carry_bit_def
  by (cases a; cases b; cases c; cases d; simp_all)

lemma slab_core_physical_scan:
  assumes valid: "valid_pair source" and positive: "0 < i" and index: "i < length source"
  shows "reverse_emit (reverse_left_fold (take i source)) (source ! i)
    (reverse_right_fold (drop (Suc i) source)) = step source ! i"
proof (cases "carry_out False source")
  case True
  show ?thesis using reverse_two_port_scan_nth[of i "source @ [19]"]
      reverse_two_port_scan_growth[OF valid True] index
    by (simp add: nth_append take_append drop_append)
next
  case False
  show ?thesis using reverse_two_port_scan_nth[of i "source @ [19]"]
      reverse_two_port_scan_no_growth[OF valid False] index
    by (simp add: reverse_two_port_scan_length nth_append take_append drop_append
        length_digits_exact)
qed

theorem slab_core_physical_step_cell:
  assumes valid: "valid_pair (before @ [left, s, right] @ after)"
      and bounds: "10 \<le> left" "10 \<le> s" "s < 19" "10 \<le> right"
  shows "step (before @ [left, s, right] @ after) ! (length before + 1) =
    (if carry_out False (before @ [left, s, right] @ after)
     then slab_core_birth left s else slab_core_quiet s)"
proof -
  let ?source = "before @ [left, s, right] @ after"
  let ?i = "length before + 1"
  have positive: "0 < ?i" by simp
  have index: "?i < length ?source" by simp
  have admitted: "\<forall>x\<in>set ?source. x < 19"
  proof
    fix x assume "x \<in> set ?source"
    then have "x \<le> 18" using valid by (auto simp: valid_pair_def)
    then show "x < 19" by arith
  qed
  have prefix: "\<forall>x\<in>set (before @ [left]). x < 19" using admitted by auto
  have suffix: "\<forall>x\<in>set (right # after). x < 19" using admitted by auto
  have selected:
    "reverse_emit (reverse_left_fold (before @ [left])) s
      (reverse_right_fold (right # after)) =
    (if carry_out False ?source then slab_core_birth left s else slab_core_quiet s)"
    using slab_core_selected_emission[OF prefix suffix bounds(2,3,1,4)]
    by (simp add: carry_out_append carry_out_def)
  show ?thesis
    using slab_core_physical_scan[OF valid positive index] selected
    by (simp add: nth_append take_append drop_append)
qed

text \<open>At coefficient 4 the false-inlet successor carry has a genuine
bilinear term.  On the mixed inputs the successor is EQ-9, so its carry
still depends on the next physical inlet; a zero-inlet observation is not
a substitute for the complete carry response.\<close>

lemma slab_core_four_successor_carry:
  "carry_apply (domain (reverse_native_slab_quiet 4 a b)) False = (a \<and> b) \<and>
   reverse_native_slab_quiet 4 False False = 8 \<and>
   reverse_native_slab_quiet 4 True False = 9 \<and>
   reverse_native_slab_quiet 4 False True = 9 \<and>
   reverse_native_slab_quiet 4 True True = 10 \<and>
   carry_apply (domain (reverse_native_slab_quiet 4 True False)) True \<and>
   carry_apply (domain (reverse_native_slab_quiet 4 False True)) True"
  by (cases a; cases b; simp_all add: reverse_native_slab_quiet_def
      reverse_native_slab_digit_def carry_bit_def domain_def)

lemma slab_core_four_no_affine_witness:
  fixes c u v :: bool
  shows "\<not> (\<forall>a b. (a \<and> b) = ((c \<noteq> (u \<and> a)) \<noteq> (v \<and> b)))"
proof
  assume h: "\<forall>a b. (a \<and> b) = ((c \<noteq> (u \<and> a)) \<noteq> (v \<and> b))"
  have ff: "\<not> c" using h[rule_format, of False False] by simp
  have tf: "c = u" using h[rule_format, of True False] by simp
  have ft: "c = v" using h[rule_format, of False True] by simp
  have tt: "(c \<noteq> u) \<noteq> v" using h[rule_format, of True True] by simp
  show False using ff tf ft tt by simp
qed


ML \<open>
  val checked = @{thms slab_core_source_birth slab_core_second_reset
    slab_core_third_reset slab_core_1011_packet slab_core_1110_packet
    slab_core_clock_guard slab_core_true_carry slab_core_prefix_saturation
    slab_core_outer_forces_birth
    slab_core_selected_emission slab_core_first_selected_birth slab_core_physical_scan
    slab_core_physical_step_cell slab_core_four_successor_carry
    slab_core_four_no_affine_witness};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Reverse native slab core depends on an oracle";
  val _ = if Thm_Deps.has_skip_proof checked
    then error "Skipped reverse native slab core proof" else ();
\<close>

end
