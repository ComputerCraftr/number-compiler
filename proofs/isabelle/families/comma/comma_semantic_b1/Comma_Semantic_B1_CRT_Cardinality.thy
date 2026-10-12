theory Comma_Semantic_B1_CRT_Cardinality
  imports Comma_Semantic_B1_CRT_Partition_Completeness Comma_CRT_Equivalence
begin

text \<open>
The cardinality certificate for an admitted CRT column is obtained from
finite residue fibres.  A child admitted at Suc level is invariant under a
clock translation whose residue is zero at every later CRT coordinate.
Chinese-remainder replacement supplies such a translation for every desired
current residue.  The translations give genuine cyclic bijections between
residue slices; no clock phase list is constructed.
\<close>

definition comma_semantic_b1_crt_residue_slice ::
    "nat \<Rightarrow> nat \<Rightarrow> nat set \<Rightarrow> nat set" where
  "comma_semantic_b1_crt_residue_slice period digit cells =
    {phase. phase<924 \<and> phase mod period=digit \<and> phase\<in>cells}"

fun comma_semantic_b1_crt_column_mass :: "comma_crt_column \<Rightarrow> nat" where
  "comma_semantic_b1_crt_column_mass (Comma_CRT_Bool value) =
    (if value then 924 else 0)"
| "comma_semantic_b1_crt_column_mass (Comma_CRT_Node level children) =
    sum_list (map comma_semantic_b1_crt_column_mass children) div
      comma_crt_period level"

lemma comma_semantic_b1_crt_card_advance:
  assumes bounded: "cells\<subseteq>{..<924}"
  shows "card (comma_semantic_b1_column_advance shift cells)=card cells"
proof -
  let ?advanced = "comma_semantic_b1_column_advance shift cells"
  let ?f = "\<lambda>phase. (phase+shift) mod 924"
  let ?g = "\<lambda>phase.
    (phase+comma_semantic_b1_inverse_shift shift) mod 924"
  have cells_finite: "finite cells"
    by (rule finite_subset[OF bounded]) simp
  have advanced_bounded: "?advanced\<subseteq>{..<924}"
    by (auto simp: comma_semantic_b1_column_advance_def)
  have advanced_finite: "finite ?advanced"
    by (rule finite_subset[OF advanced_bounded]) simp
  have f_map: "?f ` ?advanced \<subseteq> cells"
    by (auto simp: comma_semantic_b1_column_advance_def)
  have g_map: "?g ` cells \<subseteq> ?advanced"
  proof (rule image_subsetI)
    fix phase
    assume phase: "phase\<in>cells"
    have phase_bound: "phase<924" using bounded phase by blast
    have inverse_bound: "?g phase<924" by simp
    have cancel:
        "(?g phase+shift) mod 924=phase"
      using comma_semantic_b1_inverse_shift_cancel_right[of phase shift]
        phase_bound by simp
    show "?g phase\<in>?advanced"
      using phase inverse_bound cancel
      by (simp add: comma_semantic_b1_column_advance_def)
  qed
  have f_inj: "inj_on ?f ?advanced"
  proof (intro inj_onI)
    fix left right
    assume left: "left\<in>?advanced"
      and right: "right\<in>?advanced"
      and equal: "?f left=?f right"
    have left_bound: "left<924"
      using left by (auto simp: comma_semantic_b1_column_advance_def)
    have right_bound: "right<924"
      using right by (auto simp: comma_semantic_b1_column_advance_def)
    have cancel:
        "(?f left+comma_semantic_b1_inverse_shift shift) mod 924 =
          (?f right+comma_semantic_b1_inverse_shift shift) mod 924"
      using equal by simp
    have left_recovered:
        "(?f left+comma_semantic_b1_inverse_shift shift) mod 924=left"
      using comma_semantic_b1_cancel_shift[of left shift] left_bound
      by simp
    have right_recovered:
        "(?f right+comma_semantic_b1_inverse_shift shift) mod 924=right"
      using comma_semantic_b1_cancel_shift[of right shift] right_bound
      by simp
    show "left=right" using cancel left_recovered right_recovered by simp
  qed
  have g_inj: "inj_on ?g cells"
  proof (intro inj_onI)
    fix left right
    assume left: "left\<in>cells"
      and right: "right\<in>cells"
      and equal: "?g left=?g right"
    have left_bound: "left<924" using bounded left by blast
    have right_bound: "right<924" using bounded right by blast
    have cancel:
        "(?g left+shift) mod 924=(?g right+shift) mod 924"
      using equal by simp
    have left_recovered:
        "(?g left+shift) mod 924=left"
      using comma_semantic_b1_inverse_shift_cancel_right[of left shift]
        left_bound by simp
    have right_recovered:
        "(?g right+shift) mod 924=right"
      using comma_semantic_b1_inverse_shift_cancel_right[of right shift]
        right_bound by simp
    show "left=right" using cancel left_recovered right_recovered by simp
  qed
  show ?thesis
    by (rule card_bij_eq[OF f_inj f_map g_inj g_map advanced_finite cells_finite])
qed

lemma comma_semantic_b1_crt_target_residue:
  fixes period source target :: nat
  assumes period: "0<period"
    and source: "source<period"
    and target: "target<period"
  shows "(target+(source+period-target) mod period) mod period=source"
proof -
  have source_mod: "source mod period=source" using source by simp
  have target_mod: "target mod period=target" using target by simp
  have algebra: "target+(source+period-target)=source+period"
    using target by arith
  have residue_step:
      "(target+(source+period-target) mod period) mod period =
        ((target mod period)+((source+period-target) mod period)) mod period"
    by (simp add: target_mod)
  also have
      "((target mod period)+((source+period-target) mod period)) mod period =
        (target+(source+period-target)) mod period"
    by (rule mod_add_eq)
  also have "(target+(source+period-target)) mod period=source"
    using algebra source by simp
  finally show "(target+(source+period-target) mod period) mod period=source" .
qed

lemma comma_semantic_b1_crt_residue_add_iff:
  fixes period residue source target delta :: nat
  assumes period: "0<period"
    and residue: "residue<period"
    and source: "source<period"
    and target: "target<period"
    and delta:
      "delta mod period=(source+period-target) mod period"
  shows "((residue+delta) mod period=source) \<longleftrightarrow>
    residue=target"
proof -
  have target_value:
      "(target+delta) mod period=source"
  proof -
    have reduced:
        "(target+delta) mod period =
          (target+((source+period-target) mod period)) mod period"
    proof -
      have add_mod:
          "(target+delta) mod period =
            (target mod period+delta mod period) mod period"
        by (rule mod_add_eq[symmetric])
      also have "... =
          (target mod period+((source+period-target) mod period)) mod period"
        using delta by simp
      also have "... =
          (target+((source+period-target) mod period)) mod period"
        using target by simp
      finally show ?thesis .
    qed
    show ?thesis using reduced
      comma_semantic_b1_crt_target_residue[OF period source target]
      by simp
  qed
  show ?thesis
  proof
    assume equal: "(residue+delta) mod period=source"
    have left_cong: "[residue+delta=source] (mod period)"
      using equal source by (simp add: cong_def)
    have right_cong: "[target+delta=source] (mod period)"
      using target_value source by (simp add: cong_def)
    have same_cong: "[residue+delta=target+delta] (mod period)"
      by (rule cong_trans[OF left_cong])
         (rule cong_sym[OF right_cong])
    have residue_cong: "[residue=target] (mod period)"
      using same_cong by (simp add: cong_add_rcancel_nat)
    show "residue=target"
      by (rule cong_less_modulus_unique_nat[OF residue_cong residue target])
  next
    assume equal: "residue=target"
    show "(residue+delta) mod period=source"
      using equal target_value by simp
  qed
qed

lemma comma_semantic_b1_crt_eval_shift_invariant:
  fixes level phase shift :: nat and child :: comma_crt_column
  assumes admitted: "comma_crt_admitted (Suc level) child"
    and level: "level<4"
    and later_zero:
      "\<And>later. level<later \<Longrightarrow> later<4 \<Longrightarrow>
        shift mod comma_crt_period later=0"
  shows "comma_crt_eval ((phase+shift) mod 924) child =
    comma_crt_eval phase child"
proof -
  have later_residue:
      "\<And>later. Suc level\<le>later \<Longrightarrow> later<4 \<Longrightarrow>
        (phase+shift) mod comma_crt_period later =
          phase mod comma_crt_period later"
  proof -
    fix later
    assume lower: "Suc level\<le>later" and later: "later<4"
    have level_later: "level<later" using lower by arith
    have zero: "shift mod comma_crt_period later=0"
      by (rule later_zero[OF level_later later])
    have period_positive: "0<comma_crt_period later"
      by (rule comma_crt_period_positive[OF later])
    show "(phase+shift) mod comma_crt_period later =
        phase mod comma_crt_period later"
    proof -
      have add_mod:
          "(phase+shift) mod comma_crt_period later =
            (phase mod comma_crt_period later+
              shift mod comma_crt_period later) mod
                comma_crt_period later"
        by (rule mod_add_eq[symmetric])
      also have "... =
          (phase mod comma_crt_period later+0) mod
            comma_crt_period later"
        using zero by simp
      also have "... = phase mod comma_crt_period later"
        using period_positive by simp
      finally show ?thesis .
    qed
  qed
  have equal:
      "comma_crt_eval (phase+shift) child=comma_crt_eval phase child"
    by (rule comma_semantic_b1_crt_eval_equal_on_later_residues[OF admitted])
       (rule later_residue)
  have periodic:
      "comma_crt_eval ((phase+shift) mod 924) child =
        comma_crt_eval (phase+shift) child"
    using comma_crt_eval_periodic[OF admitted] by simp
  show ?thesis using periodic equal by simp
qed

lemma comma_semantic_b1_crt_residue_slice_advance:
  assumes period_divides: "period dvd 924"
    and period_positive: "0<period"
    and source: "source<period"
    and target: "target<period"
    and delta:
      "delta mod period=(source+period-target) mod period"
    and invariant:
      "\<forall>phase<924.
        phase\<in>cells \<longleftrightarrow>
          (phase+delta) mod 924\<in>cells"
  shows "comma_semantic_b1_column_advance delta
      (comma_semantic_b1_crt_residue_slice period source cells) =
    comma_semantic_b1_crt_residue_slice period target cells"
proof (rule set_eqI)
  fix phase
  show "phase\<in>comma_semantic_b1_column_advance delta
      (comma_semantic_b1_crt_residue_slice period source cells) \<longleftrightarrow>
    phase\<in>comma_semantic_b1_crt_residue_slice period target cells"
  proof (cases "phase<924")
    case False
    then show ?thesis
      by (simp add: comma_semantic_b1_column_advance_def
        comma_semantic_b1_crt_residue_slice_def)
  next
    case True
    have residue_outer:
        "((phase+delta) mod 924) mod period=(phase+delta) mod period"
      using period_divides by (simp add: mod_mod_cancel[OF period_divides])
    have residue_inner:
        "(phase+delta) mod period=(phase mod period+delta) mod period"
      by (rule mod_add_left_eq[symmetric])
    have residue_bound: "phase mod period<period"
      using period_positive by simp
    have residue_transport:
        "((phase+delta) mod 924) mod period =
          ((phase mod period+delta) mod period)"
      using residue_outer residue_inner by simp
    have residue_left:
        "(((phase+delta) mod 924) mod period=source) \<longleftrightarrow>
          ((phase mod period+delta) mod period=source)"
      using residue_transport by simp
    have residue_exact:
        "((phase mod period+delta) mod period=source) \<longleftrightarrow>
          phase mod period=target"
      by (rule comma_semantic_b1_crt_residue_add_iff[
        OF period_positive residue_bound source target delta])
    have residue_iff:
        "((phase+delta) mod 924) mod period=source \<longleftrightarrow>
          phase mod period=target"
      using residue_left residue_exact by simp
    have cells_iff:
        "(phase+delta) mod 924\<in>cells \<longleftrightarrow> phase\<in>cells"
      using invariant True by blast
    show ?thesis
      using True residue_iff cells_iff
      by (simp add: comma_semantic_b1_column_advance_def
        comma_semantic_b1_crt_residue_slice_def)
  qed
qed

lemma comma_semantic_b1_crt_residue_slice_card_equal:
  assumes period_divides: "period dvd 924"
    and period_positive: "0<period"
    and source: "source<period"
    and target: "target<period"
    and cells_bounded: "cells\<subseteq>{..<924}"
    and delta:
      "delta mod period=(source+period-target) mod period"
    and invariant:
      "\<forall>phase<924.
        phase\<in>cells \<longleftrightarrow>
          (phase+delta) mod 924\<in>cells"
  shows "card (comma_semantic_b1_crt_residue_slice period source cells) =
    card (comma_semantic_b1_crt_residue_slice period target cells)"
proof -
  have slice_bounded:
      "comma_semantic_b1_crt_residue_slice period source cells\<subseteq>{..<924}"
    by (auto simp: comma_semantic_b1_crt_residue_slice_def)
  have advanced:
      "comma_semantic_b1_column_advance delta
        (comma_semantic_b1_crt_residue_slice period source cells) =
      comma_semantic_b1_crt_residue_slice period target cells"
    by (rule comma_semantic_b1_crt_residue_slice_advance[
      OF period_divides period_positive source target delta invariant])
  have card_advanced:
      "card (comma_semantic_b1_column_advance delta
        (comma_semantic_b1_crt_residue_slice period source cells)) =
      card (comma_semantic_b1_crt_residue_slice period source cells)"
    by (rule comma_semantic_b1_crt_card_advance[OF slice_bounded])
  show ?thesis using advanced card_advanced by simp
qed

lemma comma_semantic_b1_crt_residue_slices_partition:
  assumes period_positive: "0<period"
    and cells_bounded: "cells\<subseteq>{..<924}"
  shows "cells =
    (\<Union>digit\<in>{..<period}.
      comma_semantic_b1_crt_residue_slice period digit cells)"
proof (rule set_eqI)
  fix phase
  show "phase\<in>cells \<longleftrightarrow>
    phase\<in>(\<Union>digit\<in>{..<period}.
      comma_semantic_b1_crt_residue_slice period digit cells)"
  proof
    assume phase: "phase\<in>cells"
    have phase_bound: "phase<924" using cells_bounded phase by blast
    have digit_bound: "phase mod period<period"
      by (simp add: period_positive)
    have member:
        "phase\<in>comma_semantic_b1_crt_residue_slice period
          (phase mod period) cells"
      using phase phase_bound by (simp add: comma_semantic_b1_crt_residue_slice_def)
    show "phase\<in>(\<Union>digit\<in>{..<period}.
        comma_semantic_b1_crt_residue_slice period digit cells)"
      using digit_bound member by blast
  next
    assume phase:
      "phase\<in>(\<Union>digit\<in>{..<period}.
        comma_semantic_b1_crt_residue_slice period digit cells)"
    then obtain digit where digit: "digit<period"
      and member:
        "phase\<in>comma_semantic_b1_crt_residue_slice period digit cells"
      by auto
    show "phase\<in>cells"
      using member by (simp add: comma_semantic_b1_crt_residue_slice_def)
  qed
qed

lemma comma_semantic_b1_crt_residue_slice_card_div:
  assumes admitted: "comma_crt_admitted (Suc level) child"
    and level: "level<4"
    and digit: "digit<comma_crt_period level"
  shows "card (comma_semantic_b1_crt_residue_slice
      (comma_crt_period level) digit (comma_crt_set child)) =
    card (comma_crt_set child) div comma_crt_period level \<and>
    card (comma_crt_set child) =
      comma_crt_period level *
        card (comma_semantic_b1_crt_residue_slice
          (comma_crt_period level) digit (comma_crt_set child))"
proof -
  let ?period = "comma_crt_period level"
  let ?cells = "comma_crt_set child"
  have period_positive: "0<?period"
    by (rule comma_crt_period_positive[OF level])
  have period_divides: "?period dvd 924"
    by (rule comma_crt_period_divides[OF level])
  have cells_bounded: "?cells\<subseteq>{..<924}"
    by (auto simp: comma_crt_set_def)
  have equal_slices:
      "\<forall>target<?period.
        card (comma_semantic_b1_crt_residue_slice ?period digit ?cells) =
        card (comma_semantic_b1_crt_residue_slice ?period target ?cells)"
  proof (intro allI impI)
    fix target
    assume target: "target<?period"
    have replacement_digit:
        "(digit+?period-target) mod ?period<?period"
      by (simp add: period_positive)
    have replacement:
        "\<exists>delta<924.
          delta mod ?period=(digit+?period-target) mod ?period \<and>
          (\<forall>later. level<later \<longrightarrow> later<4 \<longrightarrow>
            delta mod comma_crt_period later=0 mod comma_crt_period later)"
      using comma_semantic_b1_crt_partition_phase_replacement[
        OF level replacement_digit, of 0]
      by blast
    obtain delta where delta_bound: "delta<924"
      and delta_residue: "delta mod ?period=(digit+?period-target) mod ?period"
      and delta_later:
        "\<And>later. level<later \<Longrightarrow> later<4 \<Longrightarrow>
          delta mod comma_crt_period later=0 mod comma_crt_period later"
      using replacement by blast
    have delta_later_zero:
        "\<And>later. level<later \<Longrightarrow> later<4 \<Longrightarrow>
          delta mod comma_crt_period later=0"
    proof -
      fix later
      assume lower_later: "level<later" and later: "later<4"
      have period_later: "0<comma_crt_period later"
        by (rule comma_crt_period_positive[OF later])
      have equation: "delta mod comma_crt_period later=0 mod comma_crt_period later"
        by (rule delta_later[OF lower_later later])
      with period_later show "delta mod comma_crt_period later=0"
        by simp
    qed
    have invariant:
        "\<forall>phase<924.
          phase\<in>?cells \<longleftrightarrow>
            (phase+delta) mod 924\<in>?cells"
    proof (intro allI impI)
      fix phase :: nat
      assume phase: "phase<924"
      have eval:
          "comma_crt_eval ((phase+delta) mod 924) child =
            comma_crt_eval phase child"
        by (rule comma_semantic_b1_crt_eval_shift_invariant[
          OF admitted level delta_later_zero])
      show "phase\<in>?cells \<longleftrightarrow>
          (phase+delta) mod 924\<in>?cells"
        using phase eval by (simp add: comma_crt_set_def)
    qed
    show "card (comma_semantic_b1_crt_residue_slice ?period digit ?cells) =
        card (comma_semantic_b1_crt_residue_slice ?period target ?cells)"
      by (rule comma_semantic_b1_crt_residue_slice_card_equal[
        OF period_divides period_positive digit target cells_bounded
          delta_residue invariant])
  qed
  have union:
      "(\<Union>target\<in>{..< ?period}.
        comma_semantic_b1_crt_residue_slice ?period target ?cells) = ?cells"
    by (rule sym[OF comma_semantic_b1_crt_residue_slices_partition[
      OF period_positive cells_bounded]])
  have card_union_raw:
      "card (\<Union>target\<in>{..< ?period}.
          comma_semantic_b1_crt_residue_slice ?period target ?cells) =
        (\<Sum>target\<in>{..< ?period}.
          card (comma_semantic_b1_crt_residue_slice ?period target ?cells))"
  proof (rule card_UN_disjoint)
    show "finite {..< ?period}" by simp
    show "\<forall>target\<in>{..< ?period}.
        finite (comma_semantic_b1_crt_residue_slice ?period target ?cells)"
      by (auto simp: comma_semantic_b1_crt_residue_slice_def)
    show "\<forall>i\<in>{..< ?period}. \<forall>j\<in>{..< ?period}.
        i\<noteq>j \<longrightarrow>
          comma_semantic_b1_crt_residue_slice ?period i ?cells \<inter>
            comma_semantic_b1_crt_residue_slice ?period j ?cells = {}"
      by (auto simp: comma_semantic_b1_crt_residue_slice_def)
  qed
  have card_union:
      "card ?cells =
        (\<Sum>target\<in>{..< ?period}.
          card (comma_semantic_b1_crt_residue_slice ?period target ?cells))"
  proof -
    have union_card:
        "card ?cells = card (\<Union>target\<in>{..< ?period}.
          comma_semantic_b1_crt_residue_slice ?period target ?cells)"
      by (rule sym[OF arg_cong[OF union, of card]])
    show ?thesis by (rule trans[OF union_card card_union_raw])
  qed
  have card_sum:
      "(\<Sum>target\<in>{..< ?period}.
          card (comma_semantic_b1_crt_residue_slice ?period target ?cells)) =
        ?period * card (comma_semantic_b1_crt_residue_slice
          ?period digit ?cells)"
  proof -
    have equal_sum:
        "(\<Sum>target\<in>{..< ?period}.
            card (comma_semantic_b1_crt_residue_slice ?period target ?cells)) =
         (\<Sum>target\<in>{..< ?period}.
            card (comma_semantic_b1_crt_residue_slice ?period digit ?cells))"
    proof (rule sum.cong[OF refl])
      fix target
      assume target: "target\<in>{..< ?period}"
      have target_bound: "target<?period" using target by simp
      show "card (comma_semantic_b1_crt_residue_slice ?period target ?cells) =
          card (comma_semantic_b1_crt_residue_slice ?period digit ?cells)"
        by (rule sym[OF equal_slices[rule_format, OF target_bound]])
    qed
    have constant_sum:
        "(\<Sum>target\<in>{..< ?period}.
            card (comma_semantic_b1_crt_residue_slice ?period digit ?cells)) =
         ?period * card (comma_semantic_b1_crt_residue_slice
           ?period digit ?cells)"
      by (simp add: sum_constant)
    show ?thesis by (rule trans[OF equal_sum constant_sum])
  qed
  have multiple:
      "card ?cells = ?period *
        card (comma_semantic_b1_crt_residue_slice ?period digit ?cells)"
    by (rule trans[OF card_union card_sum])
  have quotient_rewrite:
      "card ?cells div ?period =
        (?period * card (comma_semantic_b1_crt_residue_slice
          ?period digit ?cells)) div ?period"
    by (rule arg_cong[OF multiple])
  have quotient_cancel:
      "(?period * card (comma_semantic_b1_crt_residue_slice
          ?period digit ?cells)) div ?period =
        card (comma_semantic_b1_crt_residue_slice ?period digit ?cells)"
    using period_positive by (simp add: div_mult_self_is_m)
  have quotient:
      "card (comma_semantic_b1_crt_residue_slice ?period digit ?cells) =
        card ?cells div ?period"
  proof -
    have chain:
        "card ?cells div ?period =
          card (comma_semantic_b1_crt_residue_slice ?period digit ?cells)"
      by (rule trans[OF quotient_rewrite quotient_cancel])
    show ?thesis by (rule sym[OF chain])
  qed
  show ?thesis using quotient multiple by blast
qed

ML \<open>
  val _ = Thm.consolidate @{thms comma_semantic_b1_crt_residue_slice_card_div};
  val _ = Comma_Proof_Profile.report
    "Semantic B1 CRT cardinality stage=residue-slice-card-div-complete";
\<close>

lemma comma_semantic_b1_crt_column_card_mass:
  assumes admitted: "comma_crt_admitted lower column"
  shows "card (comma_crt_set column) =
    comma_semantic_b1_crt_column_mass column"
  using admitted
proof (induction column arbitrary: lower)
  case (Comma_CRT_Bool payload)
  then show ?case
    by (simp add: comma_crt_set_def comma_semantic_b1_crt_column_mass.simps)
next
  case (Comma_CRT_Node level children)
  have level: "level<4"
    and width: "length children=comma_crt_period level"
    and children_admitted:
      "list_all (comma_crt_admitted (Suc level)) children"
    using Comma_CRT_Node.prems by (auto simp: list_all_iff)
  have period_positive: "0<comma_crt_period level"
    by (rule comma_crt_period_positive[OF level])
  have node_union:
      "comma_crt_set (Comma_CRT_Node level children) =
        (\<Union>digit\<in>{..<comma_crt_period level}.
          comma_semantic_b1_crt_residue_slice (comma_crt_period level) digit
            (comma_crt_set (children!digit)))"
  proof (rule set_eqI)
    fix phase
    show "phase\<in>comma_crt_set (Comma_CRT_Node level children) \<longleftrightarrow>
      phase\<in>(\<Union>digit\<in>{..<comma_crt_period level}.
        comma_semantic_b1_crt_residue_slice (comma_crt_period level) digit
          (comma_crt_set (children!digit)))"
    proof
      assume phase: "phase\<in>comma_crt_set (Comma_CRT_Node level children)"
      have phase_bound: "phase<924"
        using phase by (simp add: comma_crt_set_def)
      have digit_bound:
          "phase mod comma_crt_period level<length children"
        using period_positive width by simp
      have digit_period:
          "phase mod comma_crt_period level<comma_crt_period level"
        using period_positive by simp
      have child_eval:
          "comma_crt_eval phase
            (children!(phase mod comma_crt_period level))"
        using phase level width digit_bound by (simp add: comma_crt_set_def
          comma_crt_eval_node_selected nth_map)
      have member:
          "phase\<in>comma_semantic_b1_crt_residue_slice
            (comma_crt_period level) (phase mod comma_crt_period level)
            (comma_crt_set (children!(phase mod comma_crt_period level)))"
        using phase_bound child_eval by
          (simp add: comma_crt_set_def
            comma_semantic_b1_crt_residue_slice_def)
      show "phase\<in>(\<Union>digit\<in>{..<comma_crt_period level}.
          comma_semantic_b1_crt_residue_slice (comma_crt_period level) digit
            (comma_crt_set (children!digit)))"
        using digit_period member by blast
    next
      assume phase:
        "phase\<in>(\<Union>digit\<in>{..<comma_crt_period level}.
          comma_semantic_b1_crt_residue_slice (comma_crt_period level) digit
            (comma_crt_set (children!digit)))"
      then obtain digit where digit:
          "digit<comma_crt_period level"
        and member:
          "phase\<in>comma_semantic_b1_crt_residue_slice
            (comma_crt_period level) digit
            (comma_crt_set (children!digit))"
        by auto
      have phase_member:
          "phase<924 \<and> phase mod comma_crt_period level=digit \<and>
            comma_crt_eval phase (children!digit)"
        using member by (simp add: comma_semantic_b1_crt_residue_slice_def
          comma_crt_set_def)
      show "phase\<in>comma_crt_set (Comma_CRT_Node level children)"
        using phase_member width digit level
        by (simp add: comma_crt_set_def comma_crt_eval_node_selected)
    qed
  qed
  have union_card_raw:
      "card (\<Union>digit\<in>{..<comma_crt_period level}.
          comma_semantic_b1_crt_residue_slice
            (comma_crt_period level) digit
            (comma_crt_set (children!digit))) =
        (\<Sum>digit\<in>{..<comma_crt_period level}.
          card (comma_semantic_b1_crt_residue_slice
            (comma_crt_period level) digit
            (comma_crt_set (children!digit))))"
  proof (rule card_UN_disjoint)
    show "finite {..<comma_crt_period level}" by simp
    show "\<forall>digit\<in>{..<comma_crt_period level}.
        finite (comma_semantic_b1_crt_residue_slice
          (comma_crt_period level) digit
          (comma_crt_set (children!digit)))"
      by (auto simp: comma_semantic_b1_crt_residue_slice_def)
    show "\<forall>i\<in>{..<comma_crt_period level}.
        \<forall>j\<in>{..<comma_crt_period level}. i\<noteq>j \<longrightarrow>
        comma_semantic_b1_crt_residue_slice
          (comma_crt_period level) i (comma_crt_set (children!i)) \<inter>
        comma_semantic_b1_crt_residue_slice
          (comma_crt_period level) j (comma_crt_set (children!j)) = {}"
      by (auto simp: comma_semantic_b1_crt_residue_slice_def)
  qed
  have union_card:
      "card (comma_crt_set (Comma_CRT_Node level children)) =
        (\<Sum>digit\<in>{..<comma_crt_period level}.
          card (comma_semantic_b1_crt_residue_slice
            (comma_crt_period level) digit
            (comma_crt_set (children!digit))))"
  proof -
    have node_card_union:
        "card (comma_crt_set (Comma_CRT_Node level children)) =
          card (\<Union>digit\<in>{..<comma_crt_period level}.
            comma_semantic_b1_crt_residue_slice
              (comma_crt_period level) digit
              (comma_crt_set (children!digit)))"
      by (rule arg_cong[OF node_union, of card])
    show ?thesis by (rule trans[OF node_card_union union_card_raw])
  qed
  have child_cards:
      "\<forall>digit<comma_crt_period level.
        card (comma_crt_set (children!digit)) =
          comma_semantic_b1_crt_column_mass (children!digit)"
  proof (intro allI impI)
    fix digit
    assume digit: "digit<comma_crt_period level"
    have child_index: "digit<length children"
      using width digit by simp
    have child_admitted:
        "comma_crt_admitted (Suc level) (children!digit)"
      using children_admitted child_index by (simp add: list_all_iff)
    show "card (comma_crt_set (children!digit)) =
        comma_semantic_b1_crt_column_mass (children!digit)"
      by (rule Comma_CRT_Node.IH[OF nth_mem[OF child_index] child_admitted])
  qed
  have slice_facts:
      "\<forall>digit<comma_crt_period level.
        card (comma_semantic_b1_crt_residue_slice
          (comma_crt_period level) digit
          (comma_crt_set (children!digit))) =
        card (comma_crt_set (children!digit)) div
          comma_crt_period level \<and>
        card (comma_crt_set (children!digit)) =
          comma_crt_period level *
            card (comma_semantic_b1_crt_residue_slice
              (comma_crt_period level) digit
              (comma_crt_set (children!digit)))"
  proof (intro allI impI)
    fix digit
    assume digit: "digit<comma_crt_period level"
    have child_index: "digit<length children"
      using width digit by simp
    have child_admitted:
        "comma_crt_admitted (Suc level) (children!digit)"
      using children_admitted child_index by (simp add: list_all_iff)
    show "card (comma_semantic_b1_crt_residue_slice
          (comma_crt_period level) digit
          (comma_crt_set (children!digit))) =
        card (comma_crt_set (children!digit)) div
          comma_crt_period level \<and>
        card (comma_crt_set (children!digit)) =
          comma_crt_period level *
            card (comma_semantic_b1_crt_residue_slice
              (comma_crt_period level) digit
              (comma_crt_set (children!digit)))"
      by (rule comma_semantic_b1_crt_residue_slice_card_div[
        OF child_admitted level digit])
  qed
  have child_mass_multiple:
      "\<forall>digit<comma_crt_period level.
        comma_semantic_b1_crt_column_mass (children!digit) =
        comma_crt_period level *
          card (comma_semantic_b1_crt_residue_slice
            (comma_crt_period level) digit
            (comma_crt_set (children!digit)))"
  proof (intro allI impI)
    fix digit
    assume digit: "digit<comma_crt_period level"
    have child_card:
        "card (comma_crt_set (children!digit)) =
          comma_semantic_b1_crt_column_mass (children!digit)"
      using child_cards digit by blast
    have multiple:
        "card (comma_crt_set (children!digit)) =
          comma_crt_period level *
            card (comma_semantic_b1_crt_residue_slice
              (comma_crt_period level) digit
              (comma_crt_set (children!digit)))"
      using slice_facts digit by blast
    show "comma_semantic_b1_crt_column_mass (children!digit) =
        comma_crt_period level *
          card (comma_semantic_b1_crt_residue_slice
            (comma_crt_period level) digit
            (comma_crt_set (children!digit)))"
      using child_card multiple by simp
  qed
  have card_sum:
      "(\<Sum>digit\<in>{..<comma_crt_period level}.
        card (comma_semantic_b1_crt_residue_slice
          (comma_crt_period level) digit
          (comma_crt_set (children!digit)))) =
       sum_list (map comma_semantic_b1_crt_column_mass children) div
         comma_crt_period level"
  proof -
    have list_sum:
      "sum_list (map comma_semantic_b1_crt_column_mass children) =
        (\<Sum>digit\<in>{..<comma_crt_period level}.
          comma_semantic_b1_crt_column_mass (children!digit))"
      using width by (simp add: sum_list_sum_nth atLeast0LessThan)
    have mass_sum:
      "(\<Sum>digit\<in>{..<comma_crt_period level}.
          comma_semantic_b1_crt_column_mass (children!digit)) =
        comma_crt_period level *
          (\<Sum>digit\<in>{..<comma_crt_period level}.
            card (comma_semantic_b1_crt_residue_slice
              (comma_crt_period level) digit
              (comma_crt_set (children!digit))))"
    proof -
      have mapped_sum:
          "(\<Sum>digit\<in>{..<comma_crt_period level}.
              comma_semantic_b1_crt_column_mass (children!digit)) =
           (\<Sum>digit\<in>{..<comma_crt_period level}.
              comma_crt_period level *
                card (comma_semantic_b1_crt_residue_slice
                  (comma_crt_period level) digit
                  (comma_crt_set (children!digit))))"
      proof (rule sum.cong[OF refl])
        fix digit
        assume digit: "digit\<in>{..<comma_crt_period level}"
        have digit_bound: "digit<comma_crt_period level"
          using digit by simp
        show "comma_semantic_b1_crt_column_mass (children!digit) =
            comma_crt_period level *
              card (comma_semantic_b1_crt_residue_slice
                (comma_crt_period level) digit
                (comma_crt_set (children!digit)))"
          by (rule child_mass_multiple[rule_format, OF digit_bound])
      qed
      have distributed:
          "(\<Sum>digit\<in>{..<comma_crt_period level}.
              comma_crt_period level *
                card (comma_semantic_b1_crt_residue_slice
                  (comma_crt_period level) digit
                  (comma_crt_set (children!digit)))) =
           comma_crt_period level *
             (\<Sum>digit\<in>{..<comma_crt_period level}.
                card (comma_semantic_b1_crt_residue_slice
                  (comma_crt_period level) digit
                  (comma_crt_set (children!digit))))"
        by (simp add: sum_distrib_left)
      show ?thesis by (rule trans[OF mapped_sum distributed])
    qed
    have mass_rewrite:
        "sum_list (map comma_semantic_b1_crt_column_mass children) =
         comma_crt_period level *
           (\<Sum>digit\<in>{..<comma_crt_period level}.
             card (comma_semantic_b1_crt_residue_slice
               (comma_crt_period level) digit
               (comma_crt_set (children!digit))))"
      using list_sum mass_sum by simp
    have mass_div:
        "sum_list (map comma_semantic_b1_crt_column_mass children) div
            comma_crt_period level =
         (comma_crt_period level *
           (\<Sum>digit\<in>{..<comma_crt_period level}.
             card (comma_semantic_b1_crt_residue_slice
               (comma_crt_period level) digit
               (comma_crt_set (children!digit)))) ) div
            comma_crt_period level"
      using mass_rewrite by simp
    have div_cancel:
        "(comma_crt_period level *
           (\<Sum>digit\<in>{..<comma_crt_period level}.
             card (comma_semantic_b1_crt_residue_slice
               (comma_crt_period level) digit
               (comma_crt_set (children!digit)))) ) div
            comma_crt_period level =
         (\<Sum>digit\<in>{..<comma_crt_period level}.
           card (comma_semantic_b1_crt_residue_slice
             (comma_crt_period level) digit
             (comma_crt_set (children!digit))))"
      using period_positive by (simp add: div_mult_self_is_m)
    have chain:
        "sum_list (map comma_semantic_b1_crt_column_mass children) div
            comma_crt_period level =
         (\<Sum>digit\<in>{..<comma_crt_period level}.
           card (comma_semantic_b1_crt_residue_slice
             (comma_crt_period level) digit
             (comma_crt_set (children!digit))))"
      by (rule trans[OF mass_div div_cancel])
    show ?thesis by (rule sym[OF chain])
  qed
  show ?case
  proof -
    have card_mass:
        "card (comma_crt_set (Comma_CRT_Node level children)) =
         sum_list (map comma_semantic_b1_crt_column_mass children) div
           comma_crt_period level"
      by (rule trans[OF union_card card_sum])
    show ?thesis
      using card_mass by (simp only: comma_semantic_b1_crt_column_mass.simps)
  qed
qed

ML \<open>
  val _ = Thm.consolidate @{thms comma_semantic_b1_crt_column_card_mass};
  val _ = Comma_Proof_Profile.report
    "Semantic B1 CRT cardinality stage=column-card-mass-complete";
\<close>

lemma comma_semantic_b1_crt_column_list_card_mass:
  assumes admitted: "list_all (comma_crt_admitted 0) columns"
  shows "sum_list (map card (map comma_crt_set columns)) =
    sum_list (map comma_semantic_b1_crt_column_mass columns)"
  using admitted
proof (induction columns)
  case Nil
  then show ?case by simp
next
  case (Cons column columns)
  note admitted_assm = Cons.prems
  note induct_ih = Cons.IH
  have column_admitted: "comma_crt_admitted 0 column"
    using admitted_assm by simp
  have columns_admitted: "list_all (comma_crt_admitted 0) columns"
    using admitted_assm by simp
  have column_card:
      "card (comma_crt_set column) =
        comma_semantic_b1_crt_column_mass column"
    by (rule comma_semantic_b1_crt_column_card_mass[OF column_admitted])
  show ?case
    using induct_ih[OF columns_admitted] column_card by simp
qed

ML \<open>
  val _ = Thm.consolidate @{thms comma_semantic_b1_crt_column_list_card_mass};
  val _ = Comma_Proof_Profile.report
    "Semantic B1 CRT cardinality stage=column-list-card-mass-complete";
\<close>

lemmas comma_semantic_b1_crt_cardinality_native_clean_bundle =
  comma_semantic_b1_crt_card_advance
  comma_semantic_b1_crt_target_residue
  comma_semantic_b1_crt_residue_add_iff
  comma_semantic_b1_crt_eval_shift_invariant
  comma_semantic_b1_crt_residue_slice_advance
  comma_semantic_b1_crt_residue_slice_card_equal
  comma_semantic_b1_crt_residue_slices_partition
  comma_semantic_b1_crt_residue_slice_card_div
  comma_semantic_b1_crt_column_card_mass
  comma_semantic_b1_crt_column_list_card_mass

ML \<open>
  val checked = @{thms comma_semantic_b1_crt_cardinality_native_clean_bundle};
  val _ = Thm.consolidate checked;
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Semantic B1 CRT cardinality" checked;
\<close>

end
