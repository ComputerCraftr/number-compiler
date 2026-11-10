theory Comma_Guarded_Source_Right_Transport
  imports Comma_Semantic_B1_Entry_Near_Ports
    Comma_Semantic_Weighted_Action
begin

text \<open>
This source-only relation identifies admitted normalized Entry states by
their finite carry-period coordinates, while Near states retain the exact
headroom guard. It is defined before graph bindings or graph validity.
Occurrence shift is transported separately by the source continuation action.
\<close>

definition comma_guarded_source_class_rel ::
    "comma_finite_position \<Rightarrow> comma_finite_position \<Rightarrow> bool" where
  "comma_guarded_source_class_rel left right \<longleftrightarrow>
    comma_round_admitted left \<and> comma_round_admitted right \<and>
    ((\<exists>f x y. left=Comma_Entry f 0 x \<and>
        right=Comma_Entry f 0 y \<and>
        x mod 10 = y mod 10 \<and>
        x mod (comma_finite_period_fast f (x mod 10)) =
          y mod (comma_finite_period_fast f (x mod 10)))
     \<or> (\<exists>f h. left=Comma_Near f 0 h \<and>
        right=Comma_Near f 0 h))"

lemma comma_guarded_source_class_rel_cases:
  assumes rel: "comma_guarded_source_class_rel left right"
  obtains (Entry) f x y where
      "left=Comma_Entry f 0 x"
      "right=Comma_Entry f 0 y"
      "x mod 10 = y mod 10"
      "x mod (comma_finite_period_fast f (x mod 10)) =
        y mod (comma_finite_period_fast f (x mod 10))"
    | (Near) f h where
      "left=Comma_Near f 0 h"
      "right=Comma_Near f 0 h"
  using rel by (auto simp: comma_guarded_source_class_rel_def)

lemma comma_guarded_source_class_rel_normalized:
  assumes rel: "comma_guarded_source_class_rel left right"
  shows "left=comma_source_continuation_base left"
    and "right=comma_source_continuation_base right"
  using rel by (auto simp: comma_guarded_source_class_rel_def)

lemma comma_guarded_entry_headroom_modular_rebase:
  fixes f x y slot delta :: nat
  assumes sector: "1 \<le> f" "f \<le> 9"
    and digit: "x mod 10 = y mod 10"
    and residue:
      "x mod (comma_finite_period_fast f (x mod 10)) =
       y mod (comma_finite_period_fast f (x mod 10))"
  shows "comma_finite_headroom f slot delta x =
    comma_finite_headroom f slot delta y"
proof -
  have shifted_x:
    "comma_finite_headroom f slot delta x =
      comma_finite_headroom f ((slot+delta) mod 924) 0 x"
    by (simp add: comma_finite_headroom_def Let_def)
  have shifted_y:
    "comma_finite_headroom f slot delta y =
      comma_finite_headroom f ((slot+delta) mod 924) 0 y"
    by (simp add: comma_finite_headroom_def Let_def)
  have base:
    "comma_finite_headroom f ((slot+delta) mod 924) 0 x =
      comma_finite_headroom f ((slot+delta) mod 924) 0 y"
    by (rule comma_semantic_b1_entry_headroom_modular_rebase
      [OF sector digit residue])
  show ?thesis using shifted_x shifted_y base by simp
qed

lemma comma_guarded_source_class_rel_period:
  assumes rel: "comma_guarded_source_class_rel left right"
  shows "comma_decisive_sector_period left =
    comma_decisive_sector_period right"
proof -
  have forms:
    "(\<exists>f x y. left=Comma_Entry f 0 x \<and>
        right=Comma_Entry f 0 y \<and> x mod 10=y mod 10 \<and>
        x mod (comma_finite_period_fast f (x mod 10)) =
          y mod (comma_finite_period_fast f (x mod 10))) \<or>
     (\<exists>f h. left=Comma_Near f 0 h \<and> right=Comma_Near f 0 h)"
    using rel by (auto simp: comma_guarded_source_class_rel_def)
  then show ?thesis
  proof
    assume entry:
      "\<exists>f x y. left=Comma_Entry f 0 x \<and>
        right=Comma_Entry f 0 y \<and> x mod 10=y mod 10 \<and>
        x mod (comma_finite_period_fast f (x mod 10)) =
          y mod (comma_finite_period_fast f (x mod 10))"
    then obtain f x y where left: "left=Comma_Entry f 0 x"
      and right: "right=Comma_Entry f 0 y"
      and digit: "x mod 10=y mod 10" by blast
    have period:
      "comma_decisive_sector_period (Comma_Entry f 0 x) =
        comma_decisive_sector_period (Comma_Entry f 0 y)"
      by (rule comma_semantic_b1_entry_local_period_modular_rebase[OF digit])
    show ?thesis using left right period by simp
  next
    assume near: "\<exists>f h. left=Comma_Near f 0 h \<and> right=Comma_Near f 0 h"
    then obtain f h where "left=Comma_Near f 0 h"
      and "right=Comma_Near f 0 h" by blast
    then show ?thesis by simp
  qed
qed

lemma comma_guarded_source_class_rel_port_action:
  assumes rel: "comma_guarded_source_class_rel left right"
  shows "comma_semantic_b1_source_port_action left slot =
    comma_semantic_b1_source_port_action right slot"
proof -
  have forms:
    "(\<exists>f x y. left=Comma_Entry f 0 x \<and>
        right=Comma_Entry f 0 y \<and> x mod 10=y mod 10 \<and>
        x mod (comma_finite_period_fast f (x mod 10)) =
          y mod (comma_finite_period_fast f (x mod 10))) \<or>
     (\<exists>f h. left=Comma_Near f 0 h \<and> right=Comma_Near f 0 h)"
    using rel by (auto simp: comma_guarded_source_class_rel_def)
  then show ?thesis
  proof
    assume entry:
      "\<exists>f x y. left=Comma_Entry f 0 x \<and>
        right=Comma_Entry f 0 y \<and> x mod 10=y mod 10 \<and>
        x mod (comma_finite_period_fast f (x mod 10)) =
          y mod (comma_finite_period_fast f (x mod 10))"
    then obtain f x y where left: "left=Comma_Entry f 0 x"
      and right: "right=Comma_Entry f 0 y"
      and digit: "x mod 10=y mod 10"
      and residue:
        "x mod (comma_finite_period_fast f (x mod 10)) =
          y mod (comma_finite_period_fast f (x mod 10))" by blast
    have admitted_left: "comma_round_admitted (Comma_Entry f 0 x)"
      and admitted_right: "comma_round_admitted (Comma_Entry f 0 y)"
      using rel left right by (auto simp: comma_guarded_source_class_rel_def)
    have normalized_left:
      "left=comma_source_continuation_base left" using left by simp
    have normalized_right:
      "right=comma_source_continuation_base right" using right by simp
    have normalized_entry_left:
      "Comma_Entry f 0 x =
        comma_source_continuation_base (Comma_Entry f 0 x)"
      using normalized_left left by simp
    have normalized_entry_right:
      "Comma_Entry f 0 y =
        comma_source_continuation_base (Comma_Entry f 0 y)"
      using normalized_right right by simp
    have sector: "1 \<le> f" "f \<le> 9"
      using admitted_left by simp_all
    have period:
      "comma_decisive_sector_period (Comma_Entry f 0 x) =
        comma_decisive_sector_period (Comma_Entry f 0 y)"
      by (rule comma_semantic_b1_entry_local_period_modular_rebase[OF digit])
    have positive:
      "0 < comma_decisive_sector_period (Comma_Entry f 0 x)"
      by (rule comma_decisive_sector_period_admitted(1)[OF admitted_left])
    let ?slot = "slot mod comma_decisive_sector_period (Comma_Entry f 0 x)"
    have slot_left:
      "?slot < comma_decisive_sector_period (Comma_Entry f 0 x)"
      using positive by simp
    have slot_right:
      "?slot < comma_decisive_sector_period (Comma_Entry f 0 y)"
      using slot_left period by simp
    have x_near:
      "comma_semantic_b1_source_port_action (Comma_Entry f 0 x) ?slot =
        comma_semantic_b1_entry_near_port_action f x ?slot"
      by (rule comma_semantic_b1_entry_slot_action_near[OF admitted_left slot_left])
    have y_near:
      "comma_semantic_b1_source_port_action (Comma_Entry f 0 y) ?slot =
        comma_semantic_b1_entry_near_port_action f y ?slot"
      by (rule comma_semantic_b1_entry_slot_action_near[OF admitted_right slot_right])
    have control:
      "comma_semantic_b1_entry_near_port_action f x ?slot =
        comma_semantic_b1_entry_near_port_action f y ?slot"
      by (rule comma_semantic_b1_entry_control_port_modular_rebase
        [OF sector digit residue])
    have periodic_left:
      "comma_semantic_b1_source_port_action (Comma_Entry f 0 x) slot =
        comma_semantic_b1_source_port_action (Comma_Entry f 0 x) ?slot"
      by (rule comma_guarded_source_port_action_periodic
        [OF admitted_left normalized_entry_left])
    have periodic_right:
      "comma_semantic_b1_source_port_action (Comma_Entry f 0 y) slot =
        comma_semantic_b1_source_port_action (Comma_Entry f 0 y)
          (slot mod comma_decisive_sector_period (Comma_Entry f 0 y))"
      by (rule comma_guarded_source_port_action_periodic
        [OF admitted_right normalized_entry_right])
    have right_slot:
      "slot mod comma_decisive_sector_period (Comma_Entry f 0 y)=?slot"
      using period by simp
    have periodic_right_x_slot:
      "comma_semantic_b1_source_port_action (Comma_Entry f 0 y) slot =
        comma_semantic_b1_source_port_action (Comma_Entry f 0 y) ?slot"
      using periodic_right right_slot by simp
    show ?thesis
      using left right x_near y_near control periodic_left periodic_right_x_slot
      by simp
  next
    assume near: "\<exists>f h. left=Comma_Near f 0 h \<and> right=Comma_Near f 0 h"
    then obtain f h where "left=Comma_Near f 0 h"
      and "right=Comma_Near f 0 h" by blast
    then show ?thesis by simp
  qed
qed

datatype comma_guarded_action_observation =
    Comma_Guarded_Goto comma_finite_position
  | Comma_Guarded_Exit comma_finite_position
  | Comma_Guarded_Fork nat
  | Comma_Guarded_Landmine
  | Comma_Guarded_Invalid

fun comma_guarded_action_observation_of ::
    "comma_source_continuation_action \<Rightarrow>
      comma_guarded_action_observation" where
  "comma_guarded_action_observation_of (Comma_Continuation_Goto child shift) =
    Comma_Guarded_Goto child"
| "comma_guarded_action_observation_of (Comma_Continuation_Exit child shift) =
    Comma_Guarded_Exit child"
| "comma_guarded_action_observation_of (Comma_Continuation_Fork a shift) =
    Comma_Guarded_Fork a"
| "comma_guarded_action_observation_of (Comma_Continuation_Landmine shift) =
    Comma_Guarded_Landmine"
| "comma_guarded_action_observation_of Comma_Continuation_Invalid =
    Comma_Guarded_Invalid"

fun comma_guarded_action_ordered_children ::
    "comma_source_continuation_action \<Rightarrow> comma_finite_position list" where
  "comma_guarded_action_ordered_children (Comma_Continuation_Goto child shift) =
    [child]"
| "comma_guarded_action_ordered_children (Comma_Continuation_Exit child shift) =
    [child]"
| "comma_guarded_action_ordered_children _ = []"

lemma comma_guarded_action_observation_transport:
  "comma_guarded_action_observation_of
      (comma_source_continuation_transport k action) =
    comma_guarded_action_observation_of action"
  by (cases action) simp_all

lemma comma_guarded_action_ordered_children_transport:
  "comma_guarded_action_ordered_children
      (comma_source_continuation_transport k action) =
    comma_guarded_action_ordered_children action"
  by (cases action) simp_all

lemma comma_guarded_source_class_occurrence_transport:
  assumes class_rel:
      "comma_guarded_source_class_rel
        (comma_source_continuation_base left)
        (comma_source_continuation_base right)"
    and left_admitted: "comma_round_admitted left"
    and right_admitted: "comma_round_admitted right"
    and phase_rebase:
      "(left_phase+comma_source_continuation_shift left) mod 924 =
       (right_phase+comma_source_continuation_shift right) mod 924"
  defines "q \<equiv> (left_phase+comma_source_continuation_shift left) mod 924"
  shows "comma_source_continuation_action_of_packet
      (comma_decisive_endpoint_packet left_phase left) =
        comma_source_continuation_transport
          (comma_source_continuation_shift left)
          (comma_source_continuation_action_at
            (comma_source_continuation_base left) q)"
    and "comma_source_continuation_action_of_packet
      (comma_decisive_endpoint_packet right_phase right) =
        comma_source_continuation_transport
          (comma_source_continuation_shift right)
          (comma_source_continuation_action_at
            (comma_source_continuation_base right) q)"
    and "comma_guarded_action_observation_of
          (comma_source_continuation_action_of_packet
            (comma_decisive_endpoint_packet left_phase left)) =
        comma_guarded_action_observation_of
          (comma_source_continuation_action_of_packet
            (comma_decisive_endpoint_packet right_phase right))"
    and "comma_guarded_action_ordered_children
          (comma_source_continuation_action_of_packet
            (comma_decisive_endpoint_packet left_phase left)) =
        comma_guarded_action_ordered_children
          (comma_source_continuation_action_of_packet
            (comma_decisive_endpoint_packet right_phase right))"
proof -
  have base_left_admitted:
    "comma_round_admitted (comma_source_continuation_base left)"
    by (rule comma_source_continuation_base_admitted[OF left_admitted])
  have base_right_admitted:
    "comma_round_admitted (comma_source_continuation_base right)"
    by (rule comma_source_continuation_base_admitted[OF right_admitted])
  have base_left_normalized:
    "comma_source_continuation_base left =
      comma_source_continuation_base
        (comma_source_continuation_base left)" by simp
  have base_right_normalized:
    "comma_source_continuation_base right =
      comma_source_continuation_base
        (comma_source_continuation_base right)" by simp
  have same_base_action:
    "comma_source_continuation_action_at
        (comma_source_continuation_base left) q =
      comma_source_continuation_action_at
        (comma_source_continuation_base right) q"
  proof -
    have left_port:
      "comma_source_continuation_action_at
          (comma_source_continuation_base left) q =
        comma_semantic_b1_source_port_action
          (comma_source_continuation_base left) q"
      by (rule comma_guarded_source_action_at_port
        [OF base_left_admitted base_left_normalized])
    have right_port:
      "comma_source_continuation_action_at
          (comma_source_continuation_base right) q =
        comma_semantic_b1_source_port_action
          (comma_source_continuation_base right) q"
      by (rule comma_guarded_source_action_at_port
        [OF base_right_admitted base_right_normalized])
    have equal_ports:
      "comma_semantic_b1_source_port_action
          (comma_source_continuation_base left) q =
        comma_semantic_b1_source_port_action
          (comma_source_continuation_base right) q"
      by (rule comma_guarded_source_class_rel_port_action[OF class_rel])
    show ?thesis using left_port right_port equal_ports by simp
  qed
  have left_exact:
    "comma_source_continuation_action_of_packet
        (comma_decisive_endpoint_packet left_phase left) =
      comma_source_continuation_transport
        (comma_source_continuation_shift left)
        (comma_source_continuation_action_at
          (comma_source_continuation_base left) q)"
    using comma_source_continuation_apply_exact[OF left_admitted, of left_phase]
    by (simp add: q_def)
  have right_exact:
    "comma_source_continuation_action_of_packet
        (comma_decisive_endpoint_packet right_phase right) =
      comma_source_continuation_transport
        (comma_source_continuation_shift right)
        (comma_source_continuation_action_at
          (comma_source_continuation_base right) q)"
    using comma_source_continuation_apply_exact[OF right_admitted, of right_phase]
      phase_rebase
    by (simp add: q_def)
  have observed:
    "comma_guarded_action_observation_of
        (comma_source_continuation_transport
          (comma_source_continuation_shift left)
          (comma_source_continuation_action_at
            (comma_source_continuation_base left) q)) =
      comma_guarded_action_observation_of
        (comma_source_continuation_transport
          (comma_source_continuation_shift right)
          (comma_source_continuation_action_at
            (comma_source_continuation_base right) q))"
    using same_base_action
    by (simp add: comma_guarded_action_observation_transport)
  show "comma_source_continuation_action_of_packet
      (comma_decisive_endpoint_packet left_phase left) =
        comma_source_continuation_transport
          (comma_source_continuation_shift left)
          (comma_source_continuation_action_at
            (comma_source_continuation_base left) q)"
    by (rule left_exact)
  show "comma_source_continuation_action_of_packet
      (comma_decisive_endpoint_packet right_phase right) =
        comma_source_continuation_transport
          (comma_source_continuation_shift right)
          (comma_source_continuation_action_at
            (comma_source_continuation_base right) q)"
    by (rule right_exact)
  show "comma_guarded_action_observation_of
      (comma_source_continuation_action_of_packet
        (comma_decisive_endpoint_packet left_phase left)) =
    comma_guarded_action_observation_of
      (comma_source_continuation_action_of_packet
        (comma_decisive_endpoint_packet right_phase right))"
    using left_exact right_exact observed by simp
  show "comma_guarded_action_ordered_children
      (comma_source_continuation_action_of_packet
        (comma_decisive_endpoint_packet left_phase left)) =
    comma_guarded_action_ordered_children
      (comma_source_continuation_action_of_packet
        (comma_decisive_endpoint_packet right_phase right))"
  proof -
    have transported_children:
      "comma_guarded_action_ordered_children
          (comma_source_continuation_transport
            (comma_source_continuation_shift left)
            (comma_source_continuation_action_at
              (comma_source_continuation_base left) q)) =
        comma_guarded_action_ordered_children
          (comma_source_continuation_transport
            (comma_source_continuation_shift right)
            (comma_source_continuation_action_at
              (comma_source_continuation_base right) q))"
      using same_base_action
      by (simp add: comma_guarded_action_ordered_children_transport)
    show ?thesis using left_exact right_exact transported_children by simp
  qed
qed

lemma comma_guarded_source_class_rel_packet_action:
  assumes rel: "comma_guarded_source_class_rel left right"
  shows "comma_source_continuation_action_of_packet
      (comma_decisive_endpoint_packet phase left) =
    comma_source_continuation_action_of_packet
      (comma_decisive_endpoint_packet phase right)"
proof -
  have admitted_left: "comma_round_admitted left"
    and admitted_right: "comma_round_admitted right"
    using rel by (auto simp: comma_guarded_source_class_rel_def)
  have normalized_left: "left=comma_source_continuation_base left"
    and normalized_right: "right=comma_source_continuation_base right"
    using comma_guarded_source_class_rel_normalized[OF rel] by simp_all
  have left_packet:
    "comma_semantic_b1_source_port_action left phase =
      comma_source_continuation_action_of_packet
        (comma_decisive_endpoint_packet phase left)"
    using comma_semantic_b1_source_port_action_packet[OF admitted_left]
      normalized_left by simp
  have right_packet:
    "comma_semantic_b1_source_port_action right phase =
      comma_source_continuation_action_of_packet
        (comma_decisive_endpoint_packet phase right)"
    using comma_semantic_b1_source_port_action_packet[OF admitted_right]
      normalized_right by simp
  show ?thesis
    using left_packet right_packet
      comma_guarded_source_class_rel_port_action[OF rel, of phase]
    by simp
qed

lemma comma_guarded_source_class_rel_complete_observation:
  assumes rel: "comma_guarded_source_class_rel left right"
  shows "comma_semantic_b1_round_output phase left =
    comma_semantic_b1_round_output phase right"
proof -
  have admitted_left: "comma_round_admitted left"
    and admitted_right: "comma_round_admitted right"
    using rel by (auto simp: comma_guarded_source_class_rel_def)
  have normalized_left: "left=comma_source_continuation_base left"
    and normalized_right: "right=comma_source_continuation_base right"
    using comma_guarded_source_class_rel_normalized[OF rel] by simp_all
  have left_output:
    "comma_semantic_b1_source_slot_output phase
      (comma_semantic_b1_source_port_action left phase) =
      comma_semantic_b1_round_output phase left"
    by (rule comma_semantic_b1_port_round_output
      [OF admitted_left normalized_left])
  have right_output:
    "comma_semantic_b1_source_slot_output phase
      (comma_semantic_b1_source_port_action right phase) =
      comma_semantic_b1_round_output phase right"
    by (rule comma_semantic_b1_port_round_output
      [OF admitted_right normalized_right])
  have same_port: "comma_semantic_b1_source_port_action left phase =
      comma_semantic_b1_source_port_action right phase"
    by (rule comma_guarded_source_class_rel_port_action[OF rel])
  show ?thesis using left_output right_output same_port by simp
qed

text \<open>
The B1 round result is already the complete-decade observation: Live carries
the next root, while Stop carries sector distance D. Splitting D as
9*(D div 9)+(D mod 9) exposes precisely the (J,H) pair used by the weighted
transport layer. This is separate from C1 physical recurrence steps.
\<close>

definition comma_guarded_source_weighted_action ::
    "nat \<Rightarrow> comma_finite_position \<Rightarrow>
      comma_semantic_b1_weighted_result" where
  "comma_guarded_source_weighted_action phase source =
    (case comma_semantic_b1_round_output phase source of
       Comma_Semantic_B1_Live root \<Rightarrow>
         Comma_Semantic_B1_Continue root
     | Comma_Semantic_B1_Stop D \<Rightarrow>
         Comma_Semantic_B1_Stop_At (D mod 9) (D div 9)
     | Comma_Semantic_B1_Invalid \<Rightarrow>
         Comma_Semantic_B1_Weighted_Invalid)"

lemma comma_guarded_source_weighted_action_encode:
  "comma_semantic_b1_weighted_encode
      (comma_guarded_source_weighted_action phase source) =
    comma_semantic_b1_round_output phase source"
  by (cases "comma_semantic_b1_round_output phase source")
    (simp_all add: comma_guarded_source_weighted_action_def
      comma_semantic_b1_weighted_encode.simps div_mult_mod_eq)

lemma comma_guarded_source_class_rel_weighted_round:
  assumes rel: "comma_guarded_source_class_rel left right"
  shows "comma_guarded_source_weighted_action phase left =
    comma_guarded_source_weighted_action phase right"
  using comma_guarded_source_class_rel_complete_observation[OF rel, of phase]
  by (simp add: comma_guarded_source_weighted_action_def)

lemma comma_guarded_source_class_rel_weighted_then:
  assumes rel: "comma_guarded_source_class_rel left right"
  shows "comma_semantic_b1_weighted_word_then span
      (\<lambda>p _. comma_guarded_source_weighted_action p left) later phase 0 =
    comma_semantic_b1_weighted_word_then span
      (\<lambda>p _. comma_guarded_source_weighted_action p right) later phase 0"
proof -
  have first_equal:
    "comma_guarded_source_weighted_action phase left =
      comma_guarded_source_weighted_action phase right"
    by (rule comma_guarded_source_class_rel_weighted_round[OF rel])
  show ?thesis using first_equal
    by (cases "comma_guarded_source_weighted_action phase left")
      (simp_all add: comma_semantic_b1_weighted_word_then.simps
        split: comma_semantic_b1_weighted_result.splits)
qed

lemma comma_guarded_source_class_rel_weighted_power_then:
  assumes rel: "comma_guarded_source_class_rel left right"
  shows "comma_semantic_b1_weighted_word_then span
      (\<lambda>p _. comma_guarded_source_weighted_action p left)
      (\<lambda>p root. comma_semantic_b1_weighted_action_power k action p root)
      phase 0 =
    comma_semantic_b1_weighted_word_then span
      (\<lambda>p _. comma_guarded_source_weighted_action p right)
      (\<lambda>p root. comma_semantic_b1_weighted_action_power k action p root)
      phase 0"
  by (rule comma_guarded_source_class_rel_weighted_then[OF rel])

text \<open>
The C1 chart offset is an occurrence potential, not part of the source class
key. The cocycle below is the difference of the exact chart offsets from
comma_c1_b1_entry_occurrence_weight_exact. It is not defined by observing the
weighted transition.
\<close>

definition comma_guarded_entry_chart_potential ::
    "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int" where
  "comma_guarded_entry_chart_potential f offset h =
    - int (comma_cycle_length f * (offset + h))"

definition comma_guarded_c1_carry_morphism_holds ::
    "comma_c1_phase \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
      nat \<Rightarrow> 'a::comm_ring_1 \<Rightarrow> 'a \<Rightarrow> bool" where
  "comma_guarded_c1_carry_morphism_holds C H n width z w \<longleftrightarrow>
    (\<Sum>j<width. of_nat (comma_c1_source_carry_coefficient j C H n)*z^j) =
      decimal_base_z_inverse_kernel w *
        ((\<Sum>j<width. of_nat (comma_c1_source_raw_coefficient j C H n)*z^j) -
         (\<Sum>j<width. of_nat
            (comma_c1_source_normalized_coefficient j C H n)*z^j) -
         (if width=0 then 0 else
           of_nat (comma_c1_source_carry_coefficient (width-1) C H n)*z^width))"

lemma comma_guarded_entry_occurrence_full_certificate:
  fixes f p delta offset h P L cycles steps width :: nat
    and C :: comma_c1_phase
    and source near :: comma_finite_position
    and z w :: "'a::comm_ring_1"
  assumes sector: "1 \<le> f" "f \<le> 9"
    and exponent: "5 \<le> p"
    and source_offset: "offset \<le> 98"
    and characteristic: "(32::'a)=0"
    and inverse_root: "z*w=1"
  defines "C \<equiv> comma_c1_phase_of f offset"
    and "source \<equiv> Comma_Entry f delta offset"
    and "h \<equiv> comma_finite_headroom f (p mod 924) delta offset"
    and "near \<equiv> Comma_Near f delta h"
    and "P \<equiv> comma_finite_period f (offset mod 10)"
    and "L \<equiv> comma_cycle_length f"
    and "cycles \<equiv> (10 ^ (p + delta) - offset - h) div P"
    and "steps \<equiv> cycles * L"
  shows "comma_weighted_step (p mod 924) source =
      Comma_WNext near
        (Comma_Chart_Weight L delta
          (comma_guarded_entry_chart_potential f offset h) P)"
    and "comma_c1_source_admitted C (f * 10 ^ (p + delta - 2))
      (p + delta) steps"
    and "comma_guarded_c1_carry_morphism_holds C
      (f * 10 ^ (p + delta - 2)) steps width z w"
proof -
  have exact_weight:
    "comma_weighted_step (p mod 924) source =
      Comma_WNext near
        (Comma_Chart_Weight L delta (- int (L * (offset + h))) P)"
    using comma_c1_b1_entry_occurrence_weight_exact(1)
      [OF sector(1) sector(2) exponent source_offset characteristic inverse_root]
    by (simp add: source_def near_def h_def L_def P_def)
  have potential_exact:
    "comma_guarded_entry_chart_potential f offset h =
      - int (L * (offset + h))"
    by (simp only: comma_guarded_entry_chart_potential_def L_def)
  have exact_admission:
    "comma_c1_source_admitted C (f * 10 ^ (p + delta - 2))
      (p + delta) steps"
    using comma_c1_b1_entry_occurrence_weight_exact(2)
      [OF sector(1) sector(2) exponent source_offset characteristic inverse_root]
    by (simp add: C_def steps_def cycles_def P_def L_def h_def)
  have exact_morphism:
    "(\<Sum>j<width. of_nat (comma_c1_source_carry_coefficient j C
          (f * 10 ^ (p + delta - 2)) steps)*z^j) =
      decimal_base_z_inverse_kernel w *
        ((\<Sum>j<width. of_nat (comma_c1_source_raw_coefficient j C
             (f * 10 ^ (p + delta - 2)) steps)*z^j) -
         (\<Sum>j<width. of_nat (comma_c1_source_normalized_coefficient j C
             (f * 10 ^ (p + delta - 2)) steps)*z^j) -
         (if width=0 then 0 else
           of_nat (comma_c1_source_carry_coefficient
             (width-1) C (f * 10 ^ (p + delta - 2)) steps)*z^width))"
    using comma_c1_b1_entry_occurrence_weight_exact(3)
      [OF sector(1) sector(2) exponent source_offset characteristic inverse_root]
    by (simp add: C_def steps_def cycles_def P_def L_def h_def)
  show "comma_weighted_step (p mod 924) source =
      Comma_WNext near
        (Comma_Chart_Weight L delta
          (comma_guarded_entry_chart_potential f offset h) P)"
    by (simp only: exact_weight potential_exact)
  show "comma_c1_source_admitted C (f * 10 ^ (p + delta - 2))
      (p + delta) steps"
    by (rule exact_admission)
  show "comma_guarded_c1_carry_morphism_holds C
      (f * 10 ^ (p + delta - 2)) steps width z w"
    using exact_morphism
    by (simp add: comma_guarded_c1_carry_morphism_holds_def)
qed

lemma comma_guarded_entry_chart_potential_cocycle:
  fixes f x y h :: nat
  shows "comma_guarded_entry_chart_potential f x h -
      comma_guarded_entry_chart_potential f y h =
    int (comma_cycle_length f) * (int y - int x)"
  by (simp add: comma_guarded_entry_chart_potential_def algebra_simps)

lemma comma_guarded_entry_occurrence_weight_exact:
  fixes f p delta offset h P L :: nat
    and C :: comma_c1_phase
    and source near :: comma_finite_position
    and z w :: "'a::comm_ring_1"
  assumes sector: "1 \<le> f" "f \<le> 9"
    and exponent: "5 \<le> p"
    and source_offset: "offset \<le> 98"
    and characteristic: "(32::'a)=0"
    and inverse_root: "z*w=1"
  defines "C \<equiv> comma_c1_phase_of f offset"
    and "source \<equiv> Comma_Entry f delta offset"
    and "h \<equiv> comma_finite_headroom f (p mod 924) delta offset"
    and "near \<equiv> Comma_Near f delta h"
    and "P \<equiv> comma_finite_period f (offset mod 10)"
    and "L \<equiv> comma_cycle_length f"
  shows "comma_weighted_step (p mod 924) source =
    Comma_WNext near (Comma_Chart_Weight L delta
      (comma_guarded_entry_chart_potential f offset h) P)"
proof -
  have exact:
    "comma_weighted_step (p mod 924) source =
      Comma_WNext near
        (Comma_Chart_Weight L delta (- int (L * (offset + h))) P)"
    using comma_c1_b1_entry_occurrence_weight_exact(1)
      [OF sector(1) sector(2) exponent source_offset characteristic inverse_root]
    by (simp add: source_def near_def h_def L_def P_def)
  have potential_exact:
    "comma_guarded_entry_chart_potential f offset h =
      - int (L * (offset + h))"
    by (simp only: comma_guarded_entry_chart_potential_def L_def)
  show ?thesis
    by (simp only: exact potential_exact)
qed

lemma comma_guarded_entry_class_occurrence_weight_cocycle:
  fixes f p delta x y :: nat and z w :: "'a::comm_ring_1"
  assumes class_rel:
      "comma_guarded_source_class_rel (Comma_Entry f 0 x)
        (Comma_Entry f 0 y)"
    and exponent: "5 \<le> p"
    and characteristic: "(32::'a)=0"
    and inverse_root: "z*w=1"
  defines "hx \<equiv> comma_finite_headroom f (p mod 924) delta x"
    and "hy \<equiv> comma_finite_headroom f (p mod 924) delta y"
    and "P \<equiv> comma_finite_period f (x mod 10)"
    and "L \<equiv> comma_cycle_length f"
  shows "hx=hy"
    and "comma_weighted_step (p mod 924) (Comma_Entry f delta x) =
      Comma_WNext (Comma_Near f delta hx)
        (Comma_Chart_Weight L delta
          (comma_guarded_entry_chart_potential f x hx) P)"
    and "comma_weighted_step (p mod 924) (Comma_Entry f delta y) =
      Comma_WNext (Comma_Near f delta hy)
        (Comma_Chart_Weight L delta
          (comma_guarded_entry_chart_potential f y hy) P)"
    and "comma_guarded_entry_chart_potential f x hx -
      comma_guarded_entry_chart_potential f y hy =
      int L * (int y - int x)"
proof -
  have sector: "1 \<le> f" "f \<le> 9"
    and x_bound: "x \<le> 98" and y_bound: "y \<le> 98"
    using class_rel by (auto simp: comma_guarded_source_class_rel_def)
  have digit: "x mod 10=y mod 10"
    using class_rel by (auto simp: comma_guarded_source_class_rel_def)
  have residue:
    "x mod (comma_finite_period_fast f (x mod 10)) =
      y mod (comma_finite_period_fast f (x mod 10))"
    using class_rel by (auto simp: comma_guarded_source_class_rel_def)
  have headroom:
    "comma_finite_headroom f (p mod 924) delta x =
      comma_finite_headroom f (p mod 924) delta y"
    by (rule comma_guarded_entry_headroom_modular_rebase
      [OF sector digit residue])
  have period_y:
    "comma_finite_period f (y mod 10) = comma_finite_period f (x mod 10)"
    using digit by simp
  have exact_x:
    "comma_weighted_step (p mod 924) (Comma_Entry f delta x) =
      Comma_WNext (Comma_Near f delta hx)
        (Comma_Chart_Weight L delta
          (comma_guarded_entry_chart_potential f x hx) P)"
    using comma_guarded_entry_occurrence_weight_exact
      [where f=f and p=p and delta=delta and offset=x and z=z and w=w,
        OF sector(1) sector(2) exponent x_bound characteristic inverse_root]
    by (simp only: hx_def P_def L_def)
  have exact_y:
    "comma_weighted_step (p mod 924) (Comma_Entry f delta y) =
      Comma_WNext (Comma_Near f delta hy)
        (Comma_Chart_Weight L delta
          (comma_guarded_entry_chart_potential f y hy) P)"
    using comma_guarded_entry_occurrence_weight_exact
      [where f=f and p=p and delta=delta and offset=y and z=z and w=w,
        OF sector(1) sector(2) exponent y_bound characteristic inverse_root]
    by (simp only: hy_def L_def period_y P_def)
  show "hx=hy" using headroom hx_def hy_def by simp
  show "comma_weighted_step (p mod 924) (Comma_Entry f delta x) =
      Comma_WNext (Comma_Near f delta hx)
        (Comma_Chart_Weight L delta
          (comma_guarded_entry_chart_potential f x hx) P)"
    by (rule exact_x)
  show "comma_weighted_step (p mod 924) (Comma_Entry f delta y) =
      Comma_WNext (Comma_Near f delta hy)
        (Comma_Chart_Weight L delta
          (comma_guarded_entry_chart_potential f y hy) P)"
    by (rule exact_y)
  show "comma_guarded_entry_chart_potential f x hx -
      comma_guarded_entry_chart_potential f y hy =
      int L * (int y - int x)"
    using comma_guarded_entry_chart_potential_cocycle
      [where f=f and x=x and y=y and h=hx]
      headroom by (simp add: hx_def hy_def L_def)
qed

lemma comma_guarded_entry_class_chart_cocycle:
  assumes rel:
      "comma_guarded_source_class_rel (Comma_Entry f 0 x)
        (Comma_Entry f 0 y)"
  shows "comma_guarded_entry_chart_potential f x
       (comma_finite_headroom f phase delta x) -
      comma_guarded_entry_chart_potential f y
       (comma_finite_headroom f phase delta y) =
    int (comma_cycle_length f) * (int y - int x)"
proof -
  obtain xf yf where coords:
      "x=xf" "y=yf" "xf mod 10=yf mod 10"
      "xf mod (comma_finite_period_fast f (xf mod 10)) =
        yf mod (comma_finite_period_fast f (xf mod 10))"
    using rel by (auto simp: comma_guarded_source_class_rel_def)
  have sector: "1 \<le> f" "f \<le> 9"
    and x_bound: "x \<le> 98" and y_bound: "y \<le> 98"
    using rel by (auto simp: comma_guarded_source_class_rel_def)
  have digit: "x mod 10=y mod 10" using coords by simp
  have residue:
    "x mod (comma_finite_period_fast f (x mod 10)) =
      y mod (comma_finite_period_fast f (x mod 10))"
    using coords by simp
  have headroom:
    "comma_finite_headroom f phase delta x =
      comma_finite_headroom f phase delta y"
    by (rule comma_guarded_entry_headroom_modular_rebase
      [OF sector digit residue])
  show ?thesis
    using comma_guarded_entry_chart_potential_cocycle
      [where f=f and x=x and y=y
        and h="comma_finite_headroom f phase delta x"] headroom
    by simp
qed

ML \<open>
  val checked = @{thms comma_guarded_source_class_rel_complete_observation
    comma_guarded_action_ordered_children_transport
    comma_guarded_source_class_rel_weighted_then
    comma_guarded_source_class_rel_weighted_power_then
    comma_guarded_entry_occurrence_full_certificate
    comma_guarded_entry_class_occurrence_weight_cocycle
    comma_guarded_entry_class_chart_cocycle};
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Guarded source action and occurrence transport" checked;
\<close>

end

