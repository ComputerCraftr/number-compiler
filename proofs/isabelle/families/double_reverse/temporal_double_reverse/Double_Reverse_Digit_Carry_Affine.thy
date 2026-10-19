theory Double_Reverse_Digit_Carry_Affine
  imports Double_Reverse_Periodic_Ring_Action
begin

text \<open>A finite, source-driven affine action on the center residue modulo five.
Each action records its number of physical ticks, its exact affine offset, and
its four action-relative carry counts. The phase-count function is read modulo
four; a source-border phase is separate metadata and is not inferred here.
This construction consumes the explicit open ports of a finite stencil trace.
It makes no periodicity or future-source claim.\<close>

record double_reverse_f5_action =
  double_reverse_f5_ticks :: nat
  double_reverse_f5_offset :: nat
  double_reverse_f5_raw_phase_counts :: "nat \<Rightarrow> nat"

definition double_reverse_f5_phase_count ::
    "double_reverse_f5_action \<Rightarrow> nat \<Rightarrow> nat" where
  "double_reverse_f5_phase_count action phase =
    double_reverse_f5_raw_phase_counts action (phase mod 4)"

definition double_reverse_f5_phase_before :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "double_reverse_f5_phase_before phase ticks =
    (phase + 4 - ticks mod 4) mod 4"

definition double_reverse_f5_multiplier :: "double_reverse_f5_action \<Rightarrow> nat" where
  "double_reverse_f5_multiplier action = 2 ^ double_reverse_f5_ticks action mod 5"

definition double_reverse_f5_apply ::
    "double_reverse_f5_action \<Rightarrow> nat \<Rightarrow> nat" where
  "double_reverse_f5_apply action residue =
    (double_reverse_f5_multiplier action * residue +
      double_reverse_f5_offset action) mod 5"

definition double_reverse_f5_bool_value :: "bool \<Rightarrow> nat" where
  "double_reverse_f5_bool_value chosen = (if chosen then 1 else 0)"

definition double_reverse_f5_identity :: "double_reverse_f5_action" where
  "double_reverse_f5_identity =
    \<lparr>double_reverse_f5_ticks = 0,
     double_reverse_f5_offset = 0,
     double_reverse_f5_raw_phase_counts = (\<lambda>_. 0)\<rparr>"

definition double_reverse_f5_first_carry :: "nat \<Rightarrow> bool" where
  "double_reverse_f5_first_carry left = (5 \<le> left)"

definition double_reverse_f5_second_carry :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "double_reverse_f5_second_carry center right =
    (right mod 5 = 3 \<or> right mod 5 = 4 \<or>
      (5 \<le> center \<and> right mod 5 = 2))"

definition double_reverse_f5_two_step ::
    "bool \<Rightarrow> bool \<Rightarrow> double_reverse_f5_action" where
  "double_reverse_f5_two_step first second =
    \<lparr>double_reverse_f5_ticks = 2,
     double_reverse_f5_offset =
       (2 * double_reverse_f5_bool_value first +
         double_reverse_f5_bool_value second) mod 5,
     double_reverse_f5_raw_phase_counts =
       (\<lambda>phase. if phase mod 4 = 0
         then double_reverse_f5_bool_value first
         else if phase mod 4 = 1
           then double_reverse_f5_bool_value second else 0)\<rparr>"

definition double_reverse_f5_stencil_step ::
    "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> double_reverse_f5_action" where
  "double_reverse_f5_stencil_step left center right =
    double_reverse_f5_two_step
      (double_reverse_f5_first_carry left)
      (double_reverse_f5_second_carry center right)"

definition double_reverse_f5_then ::
    "double_reverse_f5_action \<Rightarrow> double_reverse_f5_action \<Rightarrow>
      double_reverse_f5_action" where
  "double_reverse_f5_then earlier later =
    \<lparr>double_reverse_f5_ticks =
        double_reverse_f5_ticks earlier + double_reverse_f5_ticks later,
     double_reverse_f5_offset =
        (double_reverse_f5_multiplier later *
          double_reverse_f5_offset earlier +
          double_reverse_f5_offset later) mod 5,
     double_reverse_f5_raw_phase_counts =
        (\<lambda>phase. double_reverse_f5_phase_count earlier phase +
          double_reverse_f5_phase_count later
            (double_reverse_f5_phase_before phase
              (double_reverse_f5_ticks earlier)))\<rparr>"

lemma double_reverse_f5_residue_phase_before_compose:
  fixes phase earlier later :: nat
  assumes "phase < 4" "earlier < 4" "later < 4"
  shows
    "(((phase + 4 - earlier) mod 4 + 4 - later) mod 4) =
      ((phase + 4 - (earlier + later) mod 4) mod 4)"
proof -
  have phase_cases: "phase = 0 \<or> phase = 1 \<or> phase = 2 \<or> phase = 3"
    using assms(1) by arith
  have earlier_cases:
    "earlier = 0 \<or> earlier = 1 \<or> earlier = 2 \<or> earlier = 3"
    using assms(2) by arith
  have later_cases: "later = 0 \<or> later = 1 \<or> later = 2 \<or> later = 3"
    using assms(3) by arith
  show ?thesis
    using phase_cases earlier_cases later_cases
    by (elim disjE; simp_all)
qed

lemma double_reverse_f5_phase_before_residues:
  "double_reverse_f5_phase_before phase ticks =
    ((phase mod 4 + 4 - ticks mod 4) mod 4)"
proof -
  have ticks_bound: "ticks mod 4 \<le> 4" by simp
  have original_subtraction:
    "phase + 4 - ticks mod 4 = phase + (4 - ticks mod 4)"
    by (rule diff_add_assoc[OF ticks_bound])
  have normalized_subtraction:
    "phase mod 4 + 4 - ticks mod 4 =
      phase mod 4 + (4 - ticks mod 4)"
    by (rule diff_add_assoc[OF ticks_bound])
  show ?thesis
    unfolding double_reverse_f5_phase_before_def
    by (subst original_subtraction; subst normalized_subtraction;
        rule mod_add_left_eq[symmetric])
qed

lemma double_reverse_f5_phase_before_compose:
  "double_reverse_f5_phase_before
      (double_reverse_f5_phase_before phase earlier) later =
    double_reverse_f5_phase_before phase (earlier + later)"
proof -
  have phase_bound: "phase mod 4 < 4" by simp
  have earlier_bound: "earlier mod 4 < 4" by simp
  have later_bound: "later mod 4 < 4" by simp
  have sum_mod:
    "(earlier + later) mod 4 =
      (earlier mod 4 + later mod 4) mod 4"
    by (rule mod_add_eq[symmetric])
  have first_phase:
    "double_reverse_f5_phase_before phase earlier =
      ((phase mod 4 + 4 - earlier mod 4) mod 4)"
    by (rule double_reverse_f5_phase_before_residues)
  have composed_phase:
    "double_reverse_f5_phase_before
        (double_reverse_f5_phase_before phase earlier) later =
      (((phase mod 4 + 4 - earlier mod 4) mod 4 +
        4 - later mod 4) mod 4)"
    using first_phase double_reverse_f5_phase_before_residues[of
      "double_reverse_f5_phase_before phase earlier" later]
    by simp
  have residue_composition:
    "(((phase mod 4 + 4 - earlier mod 4) mod 4 +
        4 - later mod 4) mod 4) =
      ((phase mod 4 + 4 - (earlier mod 4 + later mod 4) mod 4) mod 4)"
    by (rule double_reverse_f5_residue_phase_before_compose[
      OF phase_bound earlier_bound later_bound])
  show ?thesis
    using composed_phase residue_composition sum_mod
      double_reverse_f5_phase_before_residues[of phase "earlier + later"]
    by simp
qed

lemma double_reverse_f5_phase_before_mod [simp]:
  "double_reverse_f5_phase_before (phase mod 4) ticks =
    double_reverse_f5_phase_before phase ticks"
  by (simp add: double_reverse_f5_phase_before_residues)

lemma double_reverse_f5_phase_count_then:
  "double_reverse_f5_phase_count (double_reverse_f5_then earlier later) phase =
    double_reverse_f5_phase_count earlier phase +
      double_reverse_f5_phase_count later
        (double_reverse_f5_phase_before phase
          (double_reverse_f5_ticks earlier))"
  unfolding double_reverse_f5_then_def double_reverse_f5_phase_count_def
  by (simp add: double_reverse_f5_phase_before_residues)

lemma double_reverse_f5_phase_count_then_assoc:
  "double_reverse_f5_phase_count
      (double_reverse_f5_then (double_reverse_f5_then earlier middle) later)
      phase =
    double_reverse_f5_phase_count
      (double_reverse_f5_then earlier (double_reverse_f5_then middle later))
      phase"
proof -
  show ?thesis
    by (simp add: double_reverse_f5_phase_count_then
        double_reverse_f5_phase_count_def
        double_reverse_f5_phase_before_compose
        double_reverse_f5_phase_before_mod
        double_reverse_f5_then_def add.assoc)
qed

lemma double_reverse_f5_two_step_multiplier:
  "double_reverse_f5_multiplier
      (double_reverse_f5_two_step first second) = 4"
  by (simp add: double_reverse_f5_multiplier_def
      double_reverse_f5_two_step_def)

lemma double_reverse_f5_multiplier_then:
  "double_reverse_f5_multiplier (double_reverse_f5_then earlier later) =
    (double_reverse_f5_multiplier earlier *
      double_reverse_f5_multiplier later) mod 5"
  unfolding double_reverse_f5_multiplier_def double_reverse_f5_then_def
  by (simp add: power_add mod_mult_eq ac_simps)

theorem double_reverse_f5_apply_then:
  "double_reverse_f5_apply (double_reverse_f5_then earlier later) residue =
    double_reverse_f5_apply later
      (double_reverse_f5_apply earlier residue)"
proof -
  have multiplier:
    "double_reverse_f5_multiplier
        (double_reverse_f5_then earlier later) =
      (double_reverse_f5_multiplier earlier *
        double_reverse_f5_multiplier later) mod 5"
    by (rule double_reverse_f5_multiplier_then)
  have offset:
    "double_reverse_f5_offset (double_reverse_f5_then earlier later) =
      (double_reverse_f5_multiplier later *
        double_reverse_f5_offset earlier +
        double_reverse_f5_offset later) mod 5"
    by (simp add: double_reverse_f5_then_def)
  have product:
    "(double_reverse_f5_multiplier
        (double_reverse_f5_then earlier later) * residue) mod 5 =
      (double_reverse_f5_multiplier earlier *
        double_reverse_f5_multiplier later * residue) mod 5"
  proof -
    have multiplier_mod:
      "double_reverse_f5_multiplier
          (double_reverse_f5_then earlier later) mod 5 =
        (double_reverse_f5_multiplier earlier *
          double_reverse_f5_multiplier later) mod 5"
      using multiplier by simp
    show ?thesis
      by (rule mod_mult_cong[OF multiplier_mod refl])
  qed
  have offset_term:
    "double_reverse_f5_offset
        (double_reverse_f5_then earlier later) mod 5 =
      (double_reverse_f5_multiplier later *
        double_reverse_f5_offset earlier +
        double_reverse_f5_offset later) mod 5"
    using offset by simp
  have left_normal:
    "double_reverse_f5_apply (double_reverse_f5_then earlier later) residue =
      (double_reverse_f5_multiplier earlier *
        double_reverse_f5_multiplier later * residue +
        double_reverse_f5_multiplier later *
          double_reverse_f5_offset earlier +
        double_reverse_f5_offset later) mod 5"
    unfolding double_reverse_f5_apply_def
    using mod_add_cong[OF product offset_term]
    by (simp add: algebra_simps)
  have inner_product:
    "(double_reverse_f5_multiplier later *
        ((double_reverse_f5_multiplier earlier * residue +
          double_reverse_f5_offset earlier) mod 5)) mod 5 =
      (double_reverse_f5_multiplier later *
        (double_reverse_f5_multiplier earlier * residue +
          double_reverse_f5_offset earlier)) mod 5"
    by (rule mod_mult_right_eq)
  have right_normal:
    "double_reverse_f5_apply later
        (double_reverse_f5_apply earlier residue) =
      (double_reverse_f5_multiplier later *
        double_reverse_f5_multiplier earlier * residue +
        double_reverse_f5_multiplier later *
          double_reverse_f5_offset earlier +
        double_reverse_f5_offset later) mod 5"
    unfolding double_reverse_f5_apply_def
    using mod_add_cong[OF inner_product refl]
    by (simp add: algebra_simps)
  show ?thesis using left_normal right_normal by (simp add: ac_simps)
qed

theorem double_reverse_f5_two_step_apply:
  "double_reverse_f5_apply
      (double_reverse_f5_two_step first second) residue =
    (4*residue +
      2*double_reverse_f5_bool_value first +
      double_reverse_f5_bool_value second) mod 5"
  by (simp add: double_reverse_f5_apply_def
      double_reverse_f5_multiplier_def double_reverse_f5_two_step_def
      double_reverse_f5_bool_value_def)

lemma double_reverse_f5_two_step_phase_counts:
  "(double_reverse_f5_phase_count
      (double_reverse_f5_two_step first second) 0,
    double_reverse_f5_phase_count
      (double_reverse_f5_two_step first second) 1,
    double_reverse_f5_phase_count
      (double_reverse_f5_two_step first second) 2,
    double_reverse_f5_phase_count
      (double_reverse_f5_two_step first second) 3) =
   (double_reverse_f5_bool_value first,
    double_reverse_f5_bool_value second, 0, 0)"
  by (simp add: double_reverse_f5_phase_count_def
      double_reverse_f5_two_step_def)

lemma double_reverse_f5_carry_bits_disjoint:
  fixes center right :: nat
  assumes right: "right < 10"
  shows "\<not> ((right mod 5 = 3 \<or> right mod 5 = 4) \<and>
      (5 \<le> center \<and> right mod 5 = 2))"
  using right by presburger

lemma double_reverse_f5_carry_bits_join:
  assumes right: "right < 10"
  shows "(if right mod 5 = 3 \<or> right mod 5 = 4 then 1 else 0) +
      (if 5 \<le> center \<and> right mod 5 = 2 then 1 else 0) =
    double_reverse_f5_bool_value
      (double_reverse_f5_second_carry center right)"
proof -
  have disjoint: "\<not> ((right mod 5 = 3 \<or> right mod 5 = 4) \<and>
      (5 \<le> center \<and> right mod 5 = 2))"
    by (rule double_reverse_f5_carry_bits_disjoint[OF right])
  show ?thesis
    using disjoint
    unfolding double_reverse_f5_second_carry_def
      double_reverse_f5_bool_value_def
    by (cases "right mod 5 = 3 \<or> right mod 5 = 4";
        cases "5 \<le> center \<and> right mod 5 = 2") auto
qed

theorem double_reverse_f5_two_step_refines_open_stencil:
  assumes digits: "left < 10" "center < 10" "right < 10"
  shows "double_reverse_f5_apply
      (double_reverse_f5_stencil_step left center right) (center mod 5) =
    double_reverse_t2_digit left center right mod 5"
proof -
  let ?leftbit = "double_reverse_f5_bool_value
    (double_reverse_f5_first_carry left)"
  let ?rightbit = "double_reverse_f5_bool_value
    (double_reverse_f5_second_carry center right)"
  have carry_join:
    "(if right mod 5 = 3 \<or> right mod 5 = 4 then 1 else 0) +
      (if 5 \<le> center \<and> right mod 5 = 2 then 1 else 0) = ?rightbit"
    by (rule double_reverse_f5_carry_bits_join[OF digits(3)])
  have stencil:
    "double_reverse_t2_digit left center right mod 5 =
      (4*center + 2*?leftbit + ?rightbit) mod 5"
  proof -
    have exact: "double_reverse_t2_digit left center right =
        (4*center + 2*(if 5 \<le> left then 1 else 0) +
          (if right mod 5 = 3 \<or> right mod 5 = 4 then 1 else 0) +
          (if 5 \<le> center \<and> right mod 5 = 2 then 1 else 0)) mod 10"
      by (rule double_reverse_t2_open_stencil_exact[OF digits])
    have five_dvd_ten: "5 dvd (10::nat)" by simp
    show ?thesis
      using exact carry_join
      by (simp only: exact mod_mod_cancel[OF five_dvd_ten];
          simp add: double_reverse_f5_bool_value_def
            double_reverse_f5_first_carry_def
            double_reverse_f5_second_carry_def carry_join)
  qed
  have multiplier:
    "double_reverse_f5_multiplier
      (double_reverse_f5_stencil_step left center right) = 4"
    by (simp add: double_reverse_f5_multiplier_def
        double_reverse_f5_stencil_step_def double_reverse_f5_two_step_def
        Let_def)
  have center_term:
    "(double_reverse_f5_multiplier
        (double_reverse_f5_stencil_step left center right) *
        (center mod 5)) mod 5 = (4*center) mod 5"
    using multiplier
    by (simp only: multiplier mod_mult_right_eq)
  have carry_term:
    "double_reverse_f5_offset
        (double_reverse_f5_stencil_step left center right) mod 5 =
      (2*?leftbit + ?rightbit) mod 5"
    by (simp add: double_reverse_f5_stencil_step_def double_reverse_f5_two_step_def
        double_reverse_f5_first_carry_def Let_def
        double_reverse_f5_bool_value_def)
  have affine:
    "double_reverse_f5_apply
      (double_reverse_f5_stencil_step left center right) (center mod 5) =
      (4*center + 2*?leftbit + ?rightbit) mod 5"
  proof -
    have sum_congruence:
      "(double_reverse_f5_multiplier
          (double_reverse_f5_stencil_step left center right) *
          (center mod 5) +
        double_reverse_f5_offset
          (double_reverse_f5_stencil_step left center right)) mod 5 =
       (4*center + 2*?leftbit + ?rightbit) mod 5"
      using mod_add_cong[OF center_term carry_term]
      by (simp add: algebra_simps)
    show ?thesis
      unfolding double_reverse_f5_apply_def
      using sum_congruence .
  qed

  show ?thesis using affine stencil by simp
qed

fun double_reverse_f5_open_trace_action ::
    "nat \<Rightarrow> (nat \<times> nat) list \<Rightarrow> double_reverse_f5_action" where
  "double_reverse_f5_open_trace_action center [] =
    double_reverse_f5_identity"
| "double_reverse_f5_open_trace_action center ((left,right)#ports) =
    double_reverse_f5_then
      (double_reverse_f5_stencil_step left center right)
      (double_reverse_f5_open_trace_action
        (double_reverse_t2_digit left center right) ports)"

lemma double_reverse_f5_open_trace_action_ticks:
  "double_reverse_f5_ticks
      (double_reverse_f5_open_trace_action center ports) = 2 * length ports"
proof (induction ports arbitrary: center)
  case Nil
  then show ?case by (simp add: double_reverse_f5_identity_def)
next
  case (Cons port ports)
  obtain left right where port: "port = (left, right)"
    by (cases port) auto
  show ?case
    using Cons.IH[of "double_reverse_t2_digit left center right"]
    by (simp add: port double_reverse_f5_then_def
        double_reverse_f5_stencil_step_def double_reverse_f5_two_step_def
        Let_def algebra_simps)
qed

theorem double_reverse_f5_open_trace_action_refines_trace:
  assumes center: "center < 10"
      and ports: "double_reverse_open_inputs_valid ports"
  shows "double_reverse_f5_apply
      (double_reverse_f5_open_trace_action center ports) (center mod 5) =
    double_reverse_open_stencil_trace center ports mod 5"
  using center ports
proof (induction ports arbitrary: center)
  case Nil
  then show ?case
    by (simp add: double_reverse_f5_apply_def
        double_reverse_f5_multiplier_def double_reverse_f5_identity_def)
next
  case (Cons port ports)
  obtain left right where port: "port = (left,right)"
    by (cases port) auto
  have left: "left < 10"
    using Cons.prems(2)
    unfolding double_reverse_open_inputs_valid_def
    by (auto simp: port)
  have right: "right < 10"
    using Cons.prems(2)
    unfolding double_reverse_open_inputs_valid_def
    by (auto simp: port)
  have rest: "double_reverse_open_inputs_valid ports"
    using Cons.prems(2)
    unfolding double_reverse_open_inputs_valid_def
    by (auto simp: port)
  have next_center:
    "double_reverse_t2_digit left center right < 10"
    by (rule double_reverse_t2_output_bounded)
  have first:
    "double_reverse_f5_apply
       (double_reverse_f5_stencil_step left center right) (center mod 5) =
      double_reverse_t2_digit left center right mod 5"
    by (rule double_reverse_f5_two_step_refines_open_stencil
      [OF left Cons.prems(1) right])
  have tail:
    "double_reverse_f5_apply
       (double_reverse_f5_open_trace_action
          (double_reverse_t2_digit left center right) ports)
       (double_reverse_t2_digit left center right mod 5) =
      double_reverse_open_stencil_trace
        (double_reverse_t2_digit left center right) ports mod 5"
    by (rule Cons.IH[OF next_center rest])
  show ?case
    using first tail
    by (simp add: double_reverse_f5_apply_then port)
qed

text \<open>The phase-count law is separate from the F5 endpoint law: it records
which action-relative physical tick supplied each carry bit. Chronological
composition shifts only the later action's phase origin by the earlier tick
count; source-border phase remains an external authenticated coordinate.\<close>

definition double_reverse_f5_phase_vector ::
    "double_reverse_f5_action \<Rightarrow> nat \<times> nat \<times> nat \<times> nat" where
  "double_reverse_f5_phase_vector action =
    (double_reverse_f5_phase_count action 0,
     double_reverse_f5_phase_count action 1,
     double_reverse_f5_phase_count action 2,
     double_reverse_f5_phase_count action 3)"

theorem double_reverse_f5_phase_vector_two_step:
  "double_reverse_f5_phase_vector
      (double_reverse_f5_two_step first second) =
    (double_reverse_f5_bool_value first,
     double_reverse_f5_bool_value second, 0, 0)"
  by (simp add: double_reverse_f5_phase_vector_def
      double_reverse_f5_phase_count_def double_reverse_f5_two_step_def
      double_reverse_f5_bool_value_def)

theorem double_reverse_f5_phase_vector_then:
  "double_reverse_f5_phase_vector
      (double_reverse_f5_then earlier later) =
    (double_reverse_f5_phase_count earlier 0 +
       double_reverse_f5_phase_count later
         (double_reverse_f5_phase_before 0 (double_reverse_f5_ticks earlier)),
     double_reverse_f5_phase_count earlier 1 +
       double_reverse_f5_phase_count later
         (double_reverse_f5_phase_before 1 (double_reverse_f5_ticks earlier)),
     double_reverse_f5_phase_count earlier 2 +
       double_reverse_f5_phase_count later
         (double_reverse_f5_phase_before 2 (double_reverse_f5_ticks earlier)),
     double_reverse_f5_phase_count earlier 3 +
       double_reverse_f5_phase_count later
         (double_reverse_f5_phase_before 3 (double_reverse_f5_ticks earlier)))"
  by (simp add: double_reverse_f5_phase_vector_def
      double_reverse_f5_phase_count_then)

text \<open>The phase vector also determines the affine offset, but only when
the action is obtained by folding actual source carry bits. For a trace of
four-tick length, a carry in phases 0, 1, 2, and 3 contributes respectively
3, 4, 2, and 1 modulo five. Keeping this theorem on the trace constructor
prevents an arbitrary record with forged phase counts from being treated as
an exact F5 action.\<close>

lemma double_reverse_f5_packed_row_ports_valid:
  assumes halo: "i + 2*steps < length row"
      and decimal: "double_reverse_decimal_row row"
  shows "double_reverse_open_inputs_valid
      (double_reverse_packed_row_ports steps row i)"
  using halo decimal
proof (induction steps arbitrary: row i)
  case 0
  then show ?case
    by (simp add: double_reverse_open_inputs_valid_def)
next
  case (Suc steps)
  have child_halo:
    "i + 2*steps < length (double_reverse_packed_row_step row)"
    using Suc.prems
    by (simp add: double_reverse_packed_row_step_length; arith)
  have child_decimal:
    "double_reverse_decimal_row (double_reverse_packed_row_step row)"
    by (rule double_reverse_packed_row_step_decimal)
  have child:
    "double_reverse_open_inputs_valid
      (double_reverse_packed_row_ports steps
        (double_reverse_packed_row_step row) i)"
    by (rule Suc.IH[OF child_halo child_decimal])
  have left_index: "i+steps < length row"
    using Suc.prems(1) by arith
  have right_index: "i+steps+2 < length row"
    using Suc.prems(1) by arith
  show ?case
    using Suc.prems child left_index right_index
    unfolding double_reverse_open_inputs_valid_def
      double_reverse_decimal_row_def
    by (auto simp: double_reverse_packed_row_ports.simps)
qed

ML \<open>
  val checked = @{thms double_reverse_f5_phase_before_compose
    double_reverse_f5_phase_before_mod
    double_reverse_f5_phase_count_then
    double_reverse_f5_phase_count_then_assoc
    double_reverse_f5_two_step_multiplier
    double_reverse_f5_multiplier_then
    double_reverse_f5_apply_then
    double_reverse_f5_two_step_phase_counts
    double_reverse_f5_two_step_apply
    double_reverse_f5_carry_bits_disjoint
    double_reverse_f5_carry_bits_join
    double_reverse_f5_two_step_refines_open_stencil
    double_reverse_f5_open_trace_action_ticks
    double_reverse_f5_open_trace_action_refines_trace
    double_reverse_f5_phase_vector_two_step
    double_reverse_f5_phase_vector_then
    double_reverse_f5_packed_row_ports_valid};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Double-reverse finite F5 carry action depends on an oracle";
  val _ = if Thm_Deps.has_skip_proof checked
    then error "Skipped double-reverse finite F5 carry action proof" else ();
\<close>

end
