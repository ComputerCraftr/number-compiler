theory Weighted_Partial_Growth_Action
  imports Main
begin

text \<open>This theory specifies the exact algebra for a bounded weighted
partial action of the shape used by reverse/add growth summaries. A lane
retains a live destination or one of the distinct structural outcomes EXIT and
ABSENT, plus the number of growth outputs and the number of consumed steps.
Composition stops at either terminal outcome and adds both counters only while
the second action is live. This generic law does not construct the G161/P7
table, choose a source port schedule, or bridge the devtools audit to a
production source producer.\<close>

datatype 's weighted_growth_target =
    GrowthLive 's
  | GrowthExit
  | GrowthAbsent

datatype 's weighted_growth_lane =
    WeightedGrowthLane "'s weighted_growth_target" nat nat

type_synonym 's weighted_growth_action = "'s \<Rightarrow> 's weighted_growth_lane"

fun weighted_growth_lane_then ::
    "'s weighted_growth_lane \<Rightarrow> 's weighted_growth_action \<Rightarrow>
      's weighted_growth_lane" where
  "weighted_growth_lane_then (WeightedGrowthLane GrowthExit w d) B =
    WeightedGrowthLane GrowthExit w d"
| "weighted_growth_lane_then (WeightedGrowthLane GrowthAbsent w d) B =
    WeightedGrowthLane GrowthAbsent w d"
| "weighted_growth_lane_then (WeightedGrowthLane (GrowthLive s) w d) B =
    (case B s of WeightedGrowthLane target v e \<Rightarrow>
      WeightedGrowthLane target (w+v) (d+e))"

definition weighted_growth_identity :: "'s weighted_growth_action" where
  "weighted_growth_identity s = WeightedGrowthLane (GrowthLive s) 0 0"

definition weighted_growth_then ::
    "'s weighted_growth_action \<Rightarrow> 's weighted_growth_action \<Rightarrow>
      's weighted_growth_action" where
  "weighted_growth_then A B s = weighted_growth_lane_then (A s) B"

lemma weighted_growth_lane_then_exit [simp]:
  "weighted_growth_lane_then (WeightedGrowthLane GrowthExit w d) B =
    WeightedGrowthLane GrowthExit w d"
  by simp

lemma weighted_growth_lane_then_absent [simp]:
  "weighted_growth_lane_then (WeightedGrowthLane GrowthAbsent w d) B =
    WeightedGrowthLane GrowthAbsent w d"
  by simp

lemma weighted_growth_lane_then_live:
  "weighted_growth_lane_then (WeightedGrowthLane (GrowthLive s) w d) B =
    (case B s of WeightedGrowthLane target v e \<Rightarrow>
      WeightedGrowthLane target (w+v) (d+e))"
  by simp

lemma weighted_growth_then_identity [simp]:
  "weighted_growth_then weighted_growth_identity A = A"
  "weighted_growth_then A weighted_growth_identity = A"
proof -
  show "weighted_growth_then weighted_growth_identity A = A"
  proof (rule ext)
    fix s
    obtain target w d where Aeq:
      "A s = WeightedGrowthLane target w d"
      by (cases "A s") auto
    show "weighted_growth_then weighted_growth_identity A s = A s"
      by (simp add: weighted_growth_then_def weighted_growth_identity_def Aeq
          weighted_growth_lane_then.simps)
  qed
  show "weighted_growth_then A weighted_growth_identity = A"
  proof (rule ext)
    fix s
    obtain target w d where Aeq:
      "A s = WeightedGrowthLane target w d"
      by (cases "A s") auto
    have lane:
      "weighted_growth_lane_then (WeightedGrowthLane target w d)
        weighted_growth_identity = WeightedGrowthLane target w d"
      by (cases target; simp add: weighted_growth_identity_def
          weighted_growth_lane_then.simps)
    show "weighted_growth_then A weighted_growth_identity s = A s"
      by (simp add: weighted_growth_then_def Aeq lane)
  qed
qed

lemma weighted_growth_lane_then_assoc:
  "weighted_growth_lane_then
      (weighted_growth_lane_then (WeightedGrowthLane target w d) B) C =
    weighted_growth_lane_then
      (WeightedGrowthLane target w d) (weighted_growth_then B C)"
proof (cases target)
  case GrowthExit
  then show ?thesis by simp
next
  case GrowthAbsent
  then show ?thesis by simp
next
  case (GrowthLive middle)
  note first_live = GrowthLive
  obtain target' w' d' where Bmiddle:
    "B middle = WeightedGrowthLane target' w' d'"
    by (cases "B middle") auto
  show ?thesis
  proof (cases target')
    case GrowthExit
    then show ?thesis
      by (simp add: weighted_growth_then_def weighted_growth_lane_then.simps
          GrowthLive Bmiddle)
  next
    case GrowthAbsent
    then show ?thesis
      by (simp add: weighted_growth_then_def weighted_growth_lane_then.simps
          GrowthLive Bmiddle)
  next
    case (GrowthLive after)
    note second_live = GrowthLive
    obtain target'' w'' d'' where Cafter:
      "C after = WeightedGrowthLane target'' w'' d''"
      by (cases "C after") auto
    show ?thesis
      by (simp add: weighted_growth_then_def weighted_growth_lane_then.simps
          first_live second_live Bmiddle Cafter algebra_simps)
  qed
qed

lemma weighted_growth_then_assoc:
  "weighted_growth_then (weighted_growth_then A B) C =
    weighted_growth_then A (weighted_growth_then B C)"
proof (rule ext)
  fix s
  obtain target w d where Aeq:
    "A s = WeightedGrowthLane target w d"
    by (cases "A s") auto
  show "weighted_growth_then (weighted_growth_then A B) C s =
      weighted_growth_then A (weighted_growth_then B C) s"
    by (simp add: weighted_growth_then_def Aeq
        weighted_growth_lane_then_assoc)
qed

definition weighted_growth_lane_valid :: "'s set \<Rightarrow> 's weighted_growth_lane \<Rightarrow> bool" where
  "weighted_growth_lane_valid S lane \<longleftrightarrow>
    (case lane of WeightedGrowthLane target w d \<Rightarrow>
      w \<le> d \<and> (case target of GrowthLive s \<Rightarrow> s \<in> S
        | GrowthExit \<Rightarrow> True | GrowthAbsent \<Rightarrow> True))"

definition weighted_growth_action_valid ::
    "'s set \<Rightarrow> 's weighted_growth_action \<Rightarrow> bool" where
  "weighted_growth_action_valid S A \<longleftrightarrow>
    (\<forall>s\<in>S. weighted_growth_lane_valid S (A s))"

theorem weighted_growth_then_valid:
  assumes left: "weighted_growth_action_valid S A"
      and right: "weighted_growth_action_valid S B"
  shows "weighted_growth_action_valid S (weighted_growth_then A B)"
proof -
  have lane: "weighted_growth_lane_valid S
      (weighted_growth_lane_then (A s) B)" if "s \<in> S" for s
  proof -
    obtain target w d where left_eq:
      "A s = WeightedGrowthLane target w d"
      by (cases "A s") auto
    have left_valid: "weighted_growth_lane_valid S (A s)"
      using left that by (auto simp: weighted_growth_action_valid_def)
    show ?thesis
    proof (cases target)
      case GrowthExit
      then show ?thesis
        using left_valid left_eq
        by (simp add: weighted_growth_lane_valid_def)
    next
      case GrowthAbsent
      then show ?thesis
        using left_valid left_eq
        by (simp add: weighted_growth_lane_valid_def)
    next
      case (GrowthLive middle)
      have middle_in: "middle \<in> S"
        using left_valid left_eq GrowthLive
        by (simp add: weighted_growth_lane_valid_def)
      have right_valid: "weighted_growth_lane_valid S (B middle)"
        using right middle_in by (auto simp: weighted_growth_action_valid_def)
      obtain target' w' d' where right_eq:
        "B middle = WeightedGrowthLane target' w' d'"
        by (cases "B middle") auto
      show ?thesis
        using left_valid right_valid left_eq right_eq GrowthLive
        by (cases target')
          (auto simp: weighted_growth_lane_valid_def
            weighted_growth_lane_then.simps)
    qed
  qed
  show ?thesis
    using lane by (auto simp: weighted_growth_action_valid_def
      weighted_growth_then_def)
qed

fun weighted_growth_power ::
    "'s weighted_growth_action \<Rightarrow> nat \<Rightarrow> 's weighted_growth_action" where
  "weighted_growth_power A 0 = weighted_growth_identity"
| "weighted_growth_power A (Suc n) =
    weighted_growth_then (weighted_growth_power A n) A"

lemma weighted_growth_power_zero [simp]:
  "weighted_growth_power A 0 = weighted_growth_identity"
  by simp

lemma weighted_growth_power_suc:
  "weighted_growth_power A (Suc n) =
    weighted_growth_then (weighted_growth_power A n) A"
  by simp

theorem weighted_growth_power_valid:
  assumes "weighted_growth_action_valid S A"
  shows "weighted_growth_action_valid S (weighted_growth_power A n)"
  using assms
proof (induction n)
  case 0
  then show ?case
    by (auto simp: weighted_growth_action_valid_def
      weighted_growth_lane_valid_def weighted_growth_identity_def)
next
  case (Suc n)
  then show ?case
    by (simp add: weighted_growth_power_suc weighted_growth_then_valid)
qed

theorem weighted_growth_power_chronological:
  "weighted_growth_power A (m+n) =
    weighted_growth_then (weighted_growth_power A m)
      (weighted_growth_power A n)"
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case
    by (simp add: weighted_growth_power_suc weighted_growth_then_assoc)
qed

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms weighted_growth_lane_then_exit weighted_growth_lane_then_absent
      weighted_growth_lane_then_live weighted_growth_then_identity
      weighted_growth_then_assoc weighted_growth_then_valid
      weighted_growth_power_zero weighted_growth_power_suc
      weighted_growth_power_valid weighted_growth_power_chronological})
    then () else error "Weighted partial growth action depends on an oracle";
\<close>

end
