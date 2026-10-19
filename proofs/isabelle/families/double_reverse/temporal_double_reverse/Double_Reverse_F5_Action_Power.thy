theory Double_Reverse_F5_Action_Power
  imports Double_Reverse_Digit_Carry_Affine
    "Shared_Carry_Dynamics.Finite_Transfer_Power"
begin

fun double_reverse_f5_action_power ::
    "double_reverse_f5_action \<Rightarrow> nat \<Rightarrow> double_reverse_f5_action" where
  "double_reverse_f5_action_power action 0 = double_reverse_f5_identity"
| "double_reverse_f5_action_power action (Suc copies) =
    double_reverse_f5_then
      (double_reverse_f5_action_power action copies) action"

fun double_reverse_f5_repeated_residue ::
    "double_reverse_f5_action \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "double_reverse_f5_repeated_residue action 0 residue = residue mod 5"
| "double_reverse_f5_repeated_residue action (Suc copies) residue =
    double_reverse_f5_apply action
      (double_reverse_f5_repeated_residue action copies residue)"

theorem double_reverse_f5_action_power_exact:
  "double_reverse_f5_apply
      (double_reverse_f5_action_power action copies) residue =
    double_reverse_f5_repeated_residue action copies residue"
proof (induction copies arbitrary: residue)
  case 0
  then show ?case
    by (simp add: double_reverse_f5_apply_def
        double_reverse_f5_identity_def double_reverse_f5_multiplier_def)
next
  case (Suc copies)
  show ?case
    by (simp only: double_reverse_f5_action_power.simps
        double_reverse_f5_repeated_residue.simps
        double_reverse_f5_apply_then Suc.IH)
qed

text \<open>The binary transfer bridge below keeps the complete carried action
observable in its state: an F5 residue, physical ticks, and all four phase
counts.  Thus the generic integer-driven binary loop is not being applied to
the endpoint residue alone.  Its relation accumulator acts on the complete
observer state, and its exactness theorem is transported back to the typed
affine action used by the digit consumer.\<close>

datatype double_reverse_f5_residue =
    Double_Reverse_F5_0
  | Double_Reverse_F5_1
  | Double_Reverse_F5_2
  | Double_Reverse_F5_3
  | Double_Reverse_F5_4

fun double_reverse_f5_residue_value :: "double_reverse_f5_residue \<Rightarrow> nat" where
  "double_reverse_f5_residue_value Double_Reverse_F5_0 = 0"
| "double_reverse_f5_residue_value Double_Reverse_F5_1 = 1"
| "double_reverse_f5_residue_value Double_Reverse_F5_2 = 2"
| "double_reverse_f5_residue_value Double_Reverse_F5_3 = 3"
| "double_reverse_f5_residue_value Double_Reverse_F5_4 = 4"

fun double_reverse_f5_residue_of_value :: "nat \<Rightarrow> double_reverse_f5_residue" where
  "double_reverse_f5_residue_of_value value =
    (if value mod 5 = 0 then Double_Reverse_F5_0
     else if value mod 5 = 1 then Double_Reverse_F5_1
     else if value mod 5 = 2 then Double_Reverse_F5_2
     else if value mod 5 = 3 then Double_Reverse_F5_3
     else Double_Reverse_F5_4)"

lemma double_reverse_f5_residue_roundtrip [simp]:
  "double_reverse_f5_residue_of_value
      (double_reverse_f5_residue_value residue) = residue"
  by (cases residue) simp_all

lemma double_reverse_f5_value_roundtrip:
  "double_reverse_f5_residue_value
      (double_reverse_f5_residue_of_value value) = value mod 5"
proof -
  have range: "value mod 5 < 5" by simp
  have cases:
    "value mod 5 = 0 \<or> value mod 5 = 1 \<or> value mod 5 = 2 \<or>
      value mod 5 = 3 \<or> value mod 5 = 4"
    using range by arith
  show ?thesis using cases by (elim disjE; simp_all)
qed

record double_reverse_f5_observer_state =
  double_reverse_f5_observer_residue :: double_reverse_f5_residue
  double_reverse_f5_observer_ticks :: nat
  double_reverse_f5_observer_count0 :: nat
  double_reverse_f5_observer_count1 :: nat
  double_reverse_f5_observer_count2 :: nat
  double_reverse_f5_observer_count3 :: nat

definition double_reverse_f5_advance_observer ::
    "double_reverse_f5_action \<Rightarrow> double_reverse_f5_observer_state
      \<Rightarrow> double_reverse_f5_observer_state" where
  "double_reverse_f5_advance_observer action state =
    \<lparr>double_reverse_f5_observer_residue =
        double_reverse_f5_residue_of_value
          (double_reverse_f5_apply action
            (double_reverse_f5_residue_value
              (double_reverse_f5_observer_residue state))),
     double_reverse_f5_observer_ticks =
        double_reverse_f5_observer_ticks state +
          double_reverse_f5_ticks action,
     double_reverse_f5_observer_count0 =
        double_reverse_f5_observer_count0 state +
          double_reverse_f5_phase_count action
            (double_reverse_f5_phase_before 0
              (double_reverse_f5_observer_ticks state)),
     double_reverse_f5_observer_count1 =
        double_reverse_f5_observer_count1 state +
          double_reverse_f5_phase_count action
            (double_reverse_f5_phase_before 1
              (double_reverse_f5_observer_ticks state)),
     double_reverse_f5_observer_count2 =
        double_reverse_f5_observer_count2 state +
          double_reverse_f5_phase_count action
            (double_reverse_f5_phase_before 2
              (double_reverse_f5_observer_ticks state)),
     double_reverse_f5_observer_count3 =
        double_reverse_f5_observer_count3 state +
          double_reverse_f5_phase_count action
            (double_reverse_f5_phase_before 3
              (double_reverse_f5_observer_ticks state))\<rparr>"

lemma double_reverse_f5_advance_identity:
  "double_reverse_f5_advance_observer double_reverse_f5_identity state = state"
proof (cases state)
  case (fields residue ticks count0 count1 count2 count3)
  then show ?thesis
    by (cases residue; simp add: double_reverse_f5_advance_observer_def
        double_reverse_f5_identity_def double_reverse_f5_apply_def
        double_reverse_f5_multiplier_def
        double_reverse_f5_phase_count_def)
qed

lemma double_reverse_f5_advance_then:
  "double_reverse_f5_advance_observer
      (double_reverse_f5_then earlier later) state =
    double_reverse_f5_advance_observer later
      (double_reverse_f5_advance_observer earlier state)"
proof (cases state)
  case (fields residue ticks count0 count1 count2 count3)
  let ?input = "double_reverse_f5_residue_value residue"
  have apply_join:
    "double_reverse_f5_apply (double_reverse_f5_then earlier later) ?input =
      double_reverse_f5_apply later
        (double_reverse_f5_apply earlier ?input)"
    by (rule double_reverse_f5_apply_then)
  have decode_earlier:
    "double_reverse_f5_residue_value
        (double_reverse_f5_residue_of_value
          (double_reverse_f5_apply earlier ?input)) =
      double_reverse_f5_apply earlier ?input"
  proof -
    have decoded:
      "double_reverse_f5_residue_value
          (double_reverse_f5_residue_of_value
            (double_reverse_f5_apply earlier ?input)) =
        double_reverse_f5_apply earlier ?input mod 5"
      by (rule double_reverse_f5_value_roundtrip)
    show ?thesis
      using decoded
      by (simp only: double_reverse_f5_apply_def mod_mod_trivial)
  qed
  have residue_join:
    "double_reverse_f5_residue_of_value
        (double_reverse_f5_apply (double_reverse_f5_then earlier later) ?input) =
      double_reverse_f5_residue_of_value
        (double_reverse_f5_apply later
          (double_reverse_f5_residue_value
            (double_reverse_f5_residue_of_value
              (double_reverse_f5_apply earlier ?input))))"
    using apply_join decode_earlier by simp
  have ticks_join:
    "double_reverse_f5_ticks (double_reverse_f5_then earlier later) =
      double_reverse_f5_ticks earlier + double_reverse_f5_ticks later"
    by (simp add: double_reverse_f5_then_def)
  have count0:
    "double_reverse_f5_phase_count (double_reverse_f5_then earlier later)
        (double_reverse_f5_phase_before 0 ticks) =
      double_reverse_f5_phase_count earlier
          (double_reverse_f5_phase_before 0 ticks) +
      double_reverse_f5_phase_count later
          (double_reverse_f5_phase_before 0
            (ticks + double_reverse_f5_ticks earlier))"
    by (simp add: double_reverse_f5_phase_count_then
        double_reverse_f5_phase_before_compose)
  have count1:
    "double_reverse_f5_phase_count (double_reverse_f5_then earlier later)
        (double_reverse_f5_phase_before 1 ticks) =
      double_reverse_f5_phase_count earlier
          (double_reverse_f5_phase_before 1 ticks) +
      double_reverse_f5_phase_count later
          (double_reverse_f5_phase_before 1
            (ticks + double_reverse_f5_ticks earlier))"
    by (simp add: double_reverse_f5_phase_count_then
        double_reverse_f5_phase_before_compose)
  have count2:
    "double_reverse_f5_phase_count (double_reverse_f5_then earlier later)
        (double_reverse_f5_phase_before 2 ticks) =
      double_reverse_f5_phase_count earlier
          (double_reverse_f5_phase_before 2 ticks) +
      double_reverse_f5_phase_count later
          (double_reverse_f5_phase_before 2
            (ticks + double_reverse_f5_ticks earlier))"
    by (simp add: double_reverse_f5_phase_count_then
        double_reverse_f5_phase_before_compose)
  have count3:
    "double_reverse_f5_phase_count (double_reverse_f5_then earlier later)
        (double_reverse_f5_phase_before 3 ticks) =
      double_reverse_f5_phase_count earlier
          (double_reverse_f5_phase_before 3 ticks) +
      double_reverse_f5_phase_count later
          (double_reverse_f5_phase_before 3
            (ticks + double_reverse_f5_ticks earlier))"
    by (simp add: double_reverse_f5_phase_count_then
        double_reverse_f5_phase_before_compose)
  show ?thesis
    using fields residue_join ticks_join count0 count1 count2 count3
    by (simp add: double_reverse_f5_advance_observer_def)
qed

definition double_reverse_f5_action_graph ::
    "double_reverse_f5_action \<Rightarrow>
      (double_reverse_f5_observer_state \<times>
       double_reverse_f5_observer_state) set" where
  "double_reverse_f5_action_graph action =
    {(before, after). after =
      double_reverse_f5_advance_observer action before}"

lemma double_reverse_f5_action_graph_identity:
  "double_reverse_f5_action_graph double_reverse_f5_identity = Id"
  unfolding double_reverse_f5_action_graph_def
  using double_reverse_f5_advance_identity by auto

lemma double_reverse_f5_action_graph_then:
  "double_reverse_f5_action_graph (double_reverse_f5_then earlier later) =
    double_reverse_f5_action_graph earlier O
      double_reverse_f5_action_graph later"
  unfolding double_reverse_f5_action_graph_def
  using double_reverse_f5_advance_then by auto

lemma double_reverse_f5_action_graph_power_iff:
  "(before, after) \<in> double_reverse_f5_action_graph action ^^ copies \<longleftrightarrow>
    after = double_reverse_f5_advance_observer
      (double_reverse_f5_action_power action copies) before"
proof (induction copies arbitrary: before after)
  case 0
  then show ?case
    by (simp add: double_reverse_f5_action_graph_def
        double_reverse_f5_action_power.simps
        double_reverse_f5_advance_identity eq_commute)
next
  case (Suc copies)
  show ?case
  proof
    assume path:
      "(before, after) \<in> double_reverse_f5_action_graph action ^^ Suc copies"
    have endpoint:
      "after = double_reverse_f5_advance_observer action
        (double_reverse_f5_advance_observer
          (double_reverse_f5_action_power action copies) before)"
    proof (rule relpow_Suc_E[OF path])
      fix middle
      assume prefix:
        "(before, middle) \<in> double_reverse_f5_action_graph action ^^ copies"
        and edge:
          "(middle, after) \<in> double_reverse_f5_action_graph action"
      have midpoint:
        "middle = double_reverse_f5_advance_observer
          (double_reverse_f5_action_power action copies) before"
        using Suc.IH prefix by blast
      have last_step:
        "after = double_reverse_f5_advance_observer action middle"
        using edge unfolding double_reverse_f5_action_graph_def by blast
      show "after = double_reverse_f5_advance_observer action
          (double_reverse_f5_advance_observer
            (double_reverse_f5_action_power action copies) before)"
        using last_step midpoint by simp
    qed
    show "after = double_reverse_f5_advance_observer
        (double_reverse_f5_action_power action (Suc copies)) before"
      using endpoint
      by (simp add: double_reverse_f5_action_power.simps
          double_reverse_f5_advance_then)
  next
    assume endpoint:
      "after = double_reverse_f5_advance_observer
        (double_reverse_f5_action_power action (Suc copies)) before"
    let ?middle = "double_reverse_f5_advance_observer
      (double_reverse_f5_action_power action copies) before"
    have prefix:
      "(before, ?middle) \<in> double_reverse_f5_action_graph action ^^ copies"
      using Suc.IH by simp
    have edge:
      "(?middle, after) \<in> double_reverse_f5_action_graph action"
      using endpoint
      by (simp add: double_reverse_f5_action_graph_def
          double_reverse_f5_action_power.simps
          double_reverse_f5_advance_then)
    show "(before, after) \<in>
        double_reverse_f5_action_graph action ^^ Suc copies"
      by (rule relpow_Suc_I[OF prefix edge])
  qed
qed

theorem double_reverse_f5_action_graph_power:
  "double_reverse_f5_action_graph
      (double_reverse_f5_action_power action copies) =
    double_reverse_f5_action_graph action ^^ copies"
proof (rule set_eqI)
  fix pair :: "double_reverse_f5_observer_state \<times>
    double_reverse_f5_observer_state"
  obtain before after where pair: "pair = (before, after)"
    by (cases pair) auto
  show "pair \<in> double_reverse_f5_action_graph
      (double_reverse_f5_action_power action copies) \<longleftrightarrow>
    pair \<in> double_reverse_f5_action_graph action ^^ copies"
    using pair double_reverse_f5_action_graph_power_iff[where
      before=before and after=after and action=action and copies=copies]
    by (simp add: double_reverse_f5_action_graph_def)
qed

theorem double_reverse_f5_binary_loop_complete_action:
  assumes reached:
    "transfer_binary_loop_reaches
      (Id, double_reverse_f5_action_graph action, copies)
      (accumulator, current, 0)"
  shows "accumulator = double_reverse_f5_action_graph
      (double_reverse_f5_action_power action copies)"
proof -
  have relation_power:
    "accumulator = double_reverse_f5_action_graph action ^^ copies"
    by (rule transfer_binary_loop_accumulator_exact[OF reached])
  show ?thesis
    using relation_power double_reverse_f5_action_graph_power by simp
qed

corollary double_reverse_f5_binary_loop_terminates_exactly:
  obtains accumulator current where
    "transfer_binary_loop_reaches
      (Id, double_reverse_f5_action_graph action, copies)
      (accumulator, current, 0)"
    "accumulator = double_reverse_f5_action_graph
      (double_reverse_f5_action_power action copies)"
proof -
  obtain accumulator current where reached:
    "transfer_binary_loop_reaches
      (Id, double_reverse_f5_action_graph action, copies)
      (accumulator, current, 0)"
    and relation_power:
    "accumulator = double_reverse_f5_action_graph action ^^ copies"
    using transfer_binary_loop_terminates_exactly[where
      R="double_reverse_f5_action_graph action" and duration=copies]
    by blast
  have action_power:
    "accumulator = double_reverse_f5_action_graph
      (double_reverse_f5_action_power action copies)"
    using relation_power double_reverse_f5_action_graph_power by simp
  show thesis by (rule that[OF reached action_power])
qed

corollary double_reverse_f5_binary_loop_complete_observer:
  assumes reached:
    "transfer_binary_loop_reaches
      (Id, double_reverse_f5_action_graph action, copies)
      (accumulator, current, 0)"
  shows "(initial,
      double_reverse_f5_advance_observer
        (double_reverse_f5_action_power action copies) initial) \<in>
      accumulator"
  using double_reverse_f5_binary_loop_complete_action[OF reached]
  by (simp add: double_reverse_f5_action_graph_def)

definition double_reverse_f5_observer_origin ::
    "nat \<Rightarrow> double_reverse_f5_observer_state" where
  "double_reverse_f5_observer_origin residue =
    \<lparr>double_reverse_f5_observer_residue =
        double_reverse_f5_residue_of_value residue,
     double_reverse_f5_observer_ticks = 0,
     double_reverse_f5_observer_count0 = 0,
     double_reverse_f5_observer_count1 = 0,
     double_reverse_f5_observer_count2 = 0,
     double_reverse_f5_observer_count3 = 0\<rparr>"

ML \<open>
  val checked = @{thms double_reverse_f5_action_power_exact
    double_reverse_f5_action_graph_identity
    double_reverse_f5_action_graph_then
    double_reverse_f5_action_graph_power_iff
    double_reverse_f5_action_graph_power
    double_reverse_f5_binary_loop_complete_action
    double_reverse_f5_binary_loop_terminates_exactly
    double_reverse_f5_binary_loop_complete_observer};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Double-reverse complete F5 action power depends on an oracle";
  val _ = if Thm_Deps.has_skip_proof checked
    then error "Skipped double-reverse complete F5 action power proof" else ();
\<close>

end
