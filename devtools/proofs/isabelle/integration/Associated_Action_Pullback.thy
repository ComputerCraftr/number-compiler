theory Associated_Action_Pullback
  imports "Temporal_Clock_Jumps.Decimal_Publisher_Constructor" "HOL.Rat"
begin

text \<open>An increasing scalar tropical action has the executable form
\<open>min cap (scale * x + offset)\<close>.  A missing cap means that the affine
value is returned without saturation.  Positive rational scale is the precise
admissibility condition used by composition and threshold pullback.\<close>

record associated_action =
  action_scale :: rat
  action_offset :: rat
  action_cap :: "rat option"

definition associated_action_admitted :: "associated_action \<Rightarrow> bool" where
  "associated_action_admitted A \<longleftrightarrow> 0 < action_scale A"

definition associated_action_apply :: "associated_action \<Rightarrow> rat \<Rightarrow> rat" where
  "associated_action_apply A x =
    (case action_cap A of None \<Rightarrow> action_scale A * x + action_offset A
     | Some c \<Rightarrow> min c (action_scale A * x + action_offset A))"

definition associated_cap_min :: "rat option \<Rightarrow> rat option \<Rightarrow> rat option" where
  "associated_cap_min a b =
    (case a of None \<Rightarrow> b
     | Some x \<Rightarrow> (case b of None \<Rightarrow> Some x | Some y \<Rightarrow> Some (min x y)))"

definition associated_action_identity :: associated_action where
  "associated_action_identity =
    \<lparr>action_scale=1, action_offset=0, action_cap=None\<rparr>"

definition associated_action_then ::
    "associated_action \<Rightarrow> associated_action \<Rightarrow> associated_action" where
  "associated_action_then A B =
    \<lparr>action_scale=action_scale B * action_scale A,
     action_offset=action_scale B * action_offset A + action_offset B,
     action_cap=associated_cap_min (action_cap B)
       (map_option (\<lambda>c. action_scale B * c + action_offset B) (action_cap A))\<rparr>"

lemma associated_action_identity_admitted:
  "associated_action_admitted associated_action_identity"
  by (simp add: associated_action_admitted_def associated_action_identity_def)

lemma associated_action_then_admitted:
  assumes "associated_action_admitted A" "associated_action_admitted B"
  shows "associated_action_admitted (associated_action_then A B)"
  using assms
  by (simp add: associated_action_admitted_def associated_action_then_def mult_pos_pos)

lemma associated_action_apply_identity [simp]:
  "associated_action_apply associated_action_identity x = x"
  by (simp add: associated_action_apply_def associated_action_identity_def)

lemma associated_action_then_identity [simp]:
  "associated_action_then A associated_action_identity = A"
  by (cases "action_cap A"; cases A)
    (simp_all add: associated_action_then_def associated_action_identity_def
      associated_cap_min_def)

lemma associated_action_identity_then [simp]:
  "associated_action_then associated_action_identity A = A"
  by (cases "action_cap A"; cases A)
    (simp_all add: associated_action_then_def associated_action_identity_def
      associated_cap_min_def)

lemma positive_affine_min:
  fixes scale offset x y :: rat
  assumes "0 < scale"
  shows "scale * min x y + offset =
    min (scale*x+offset) (scale*y+offset)"
  using assms
  by (auto simp: min_def split: if_splits; linarith)

lemma positive_affine_min_normalized:
  fixes scale offset cap inner_offset inner_scale x :: rat
  assumes "0 < scale"
  shows "min (offset + cap*scale)
      (offset + (inner_offset*scale + x*(inner_scale*scale))) =
    offset + scale * min cap (inner_offset + x*inner_scale)"
proof -
  have transport: "scale * min cap (inner_offset + x*inner_scale) + offset =
      min (scale*cap+offset)
        (scale*(inner_offset + x*inner_scale)+offset)"
    by (rule positive_affine_min[OF assms])
  show ?thesis using transport
    by (simp add: algebra_simps)
qed

theorem associated_action_apply_then:
  assumes "associated_action_admitted B"
  shows "associated_action_apply (associated_action_then A B) x =
    associated_action_apply B (associated_action_apply A x)"
  using assms
  by (cases "action_cap A"; cases "action_cap B";
      simp add: associated_action_admitted_def associated_action_apply_def
        associated_action_then_def associated_cap_min_def positive_affine_min
        positive_affine_min_normalized algebra_simps
        min.assoc min.left_commute min.commute)

definition associated_action_equiv ::
    "associated_action \<Rightarrow> associated_action \<Rightarrow> bool" (infix "\<approx>\<^sub>A" 50) where
  "A \<approx>\<^sub>A B \<longleftrightarrow> (\<forall>x. associated_action_apply A x = associated_action_apply B x)"

theorem associated_action_then_associative:
  assumes "associated_action_admitted B" "associated_action_admitted C"
  shows "associated_action_then (associated_action_then A B) C \<approx>\<^sub>A
    associated_action_then A (associated_action_then B C)"
proof (unfold associated_action_equiv_def, intro allI)
  fix x
  have BC: "associated_action_admitted (associated_action_then B C)"
    using assms associated_action_then_admitted by blast
  show "associated_action_apply (associated_action_then (associated_action_then A B) C) x =
      associated_action_apply (associated_action_then A (associated_action_then B C)) x"
    by (simp add: associated_action_apply_then[OF assms(1)]
        associated_action_apply_then[OF assms(2)]
        associated_action_apply_then[OF BC])
qed

datatype associated_threshold_demand =
    Impossible
  | Strict rat
  | Weak rat

fun associated_threshold_eval ::
    "associated_threshold_demand \<Rightarrow> rat \<Rightarrow> bool" where
  "associated_threshold_eval Impossible x = False"
| "associated_threshold_eval (Strict t) x = (t < x)"
| "associated_threshold_eval (Weak t) x = (t \<le> x)"

fun associated_threshold_pullback ::
    "associated_action \<Rightarrow> associated_threshold_demand \<Rightarrow>
      associated_threshold_demand" where
  "associated_threshold_pullback A Impossible = Impossible"
| "associated_threshold_pullback A (Strict t) =
    (case action_cap A of
       None \<Rightarrow> Strict ((t - action_offset A) / action_scale A)
     | Some c \<Rightarrow> if c \<le> t then Impossible
         else Strict ((t - action_offset A) / action_scale A))"
| "associated_threshold_pullback A (Weak t) =
    (case action_cap A of
       None \<Rightarrow> Weak ((t - action_offset A) / action_scale A)
     | Some c \<Rightarrow> if c < t then Impossible
         else Weak ((t - action_offset A) / action_scale A))"

lemma strict_affine_pullback:
  fixes scale offset threshold x :: rat
  assumes "0 < scale"
  shows "(threshold-offset)/scale < x \<longleftrightarrow>
    threshold < scale*x+offset"
  using assms
  by (simp add: pos_divide_less_eq algebra_simps)

lemma weak_affine_pullback:
  fixes scale offset threshold x :: rat
  assumes "0 < scale"
  shows "(threshold-offset)/scale \<le> x \<longleftrightarrow>
    threshold \<le> scale*x+offset"
  using assms
  by (simp add: pos_divide_le_eq algebra_simps)

theorem associated_threshold_pullback_exact:
  assumes "associated_action_admitted A"
  shows "associated_threshold_eval (associated_threshold_pullback A D) x =
    associated_threshold_eval D (associated_action_apply A x)"
proof -
  have scale: "0 < action_scale A"
    using assms by (simp add: associated_action_admitted_def)
  show ?thesis
  proof (cases D)
    case Impossible
    then show ?thesis by simp
  next
    case (Strict threshold)
    show ?thesis
    proof (cases "action_cap A")
      case None
      with Strict scale show ?thesis
        by (simp add: associated_action_apply_def strict_affine_pullback)
    next
      case (Some cap)
      with Strict scale show ?thesis
        by (auto simp: associated_action_apply_def strict_affine_pullback min_def
            split: if_splits)
    qed
  next
    case (Weak threshold)
    show ?thesis
    proof (cases "action_cap A")
      case None
      with Weak scale show ?thesis
        by (simp add: associated_action_apply_def weak_affine_pullback)
    next
      case (Some cap)
      with Weak scale show ?thesis
        by (auto simp: associated_action_apply_def weak_affine_pullback min_def
            split: if_splits)
    qed
  qed
qed

theorem associated_threshold_pullback_contravariant:
  assumes "associated_action_admitted A" "associated_action_admitted B"
  shows "associated_threshold_eval
      (associated_threshold_pullback A (associated_threshold_pullback B D)) x =
    associated_threshold_eval
      (associated_threshold_pullback (associated_action_then A B) D) x"
  using associated_threshold_pullback_exact[OF assms(1), of
      "associated_threshold_pullback B D" x]
    associated_threshold_pullback_exact[OF assms(2), of D
      "associated_action_apply A x"]
    associated_threshold_pullback_exact[
      OF associated_action_then_admitted[OF assms], of D x]
    associated_action_apply_then[OF assms(2), of A x]
  by simp

datatype survival_aggregation = AllSurvivors | AnySurvivor

definition all_survival_depth :: "nat list \<Rightarrow> nat option" where
  "all_survival_depth ds = (if ds=[] then None else Some (Min (set ds)))"

definition any_survival_depth :: "nat list \<Rightarrow> nat option" where
  "any_survival_depth ds = (if ds=[] then None else Some (Max (set ds)))"

fun monotone_survival_depth ::
    "survival_aggregation \<Rightarrow> nat list \<Rightarrow> nat option" where
  "monotone_survival_depth AllSurvivors ds = all_survival_depth ds"
| "monotone_survival_depth AnySurvivor ds = any_survival_depth ds"

definition monotone_survival_output ::
    "survival_aggregation \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> bool" where
  "monotone_survival_output aggregation ds level =
    (case monotone_survival_depth aggregation ds of
       None \<Rightarrow> False | Some d \<Rightarrow> level \<le> d)"

lemma all_survival_depth_none_iff [simp]:
  "all_survival_depth ds = None \<longleftrightarrow> ds = []"
  by (simp add: all_survival_depth_def)

lemma any_survival_depth_none_iff [simp]:
  "any_survival_depth ds = None \<longleftrightarrow> ds = []"
  by (simp add: any_survival_depth_def)

lemma all_survival_depth_output:
  "(case all_survival_depth ds of None \<Rightarrow> False | Some d \<Rightarrow> level \<le> d)
    \<longleftrightarrow> ds \<noteq> [] \<and> (\<forall>d\<in>set ds. level \<le> d)"
  by (cases ds) (simp_all add: all_survival_depth_def)

lemma any_survival_depth_output:
  "(case any_survival_depth ds of None \<Rightarrow> False | Some d \<Rightarrow> level \<le> d)
    \<longleftrightarrow> ds \<noteq> [] \<and> (\<exists>d\<in>set ds. level \<le> d)"
  by (cases ds) (simp_all add: any_survival_depth_def Max_ge_iff)

theorem monotone_survival_ALL_min:
  "monotone_survival_output AllSurvivors ds level \<longleftrightarrow>
    ds \<noteq> [] \<and> (\<forall>d\<in>set ds. level \<le> d)"
  by (simp add: monotone_survival_output_def all_survival_depth_output)

theorem monotone_survival_ANY_max:
  "monotone_survival_output AnySurvivor ds level \<longleftrightarrow>
    ds \<noteq> [] \<and> (\<exists>d\<in>set ds. level \<le> d)"
  by (simp add: monotone_survival_output_def any_survival_depth_output)

corollary monotone_survival_empty [simp]:
  "\<not> monotone_survival_output aggregation [] level"
  by (cases aggregation)
    (simp_all add: monotone_survival_output_def all_survival_depth_def
      any_survival_depth_def)

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms associated_action_then_admitted associated_action_apply_then
      associated_action_then_associative associated_threshold_pullback_exact
      associated_threshold_pullback_contravariant monotone_survival_ALL_min
      monotone_survival_ANY_max monotone_survival_empty}) then ()
    else error "Associated action pullback depends on an oracle";
\<close>

end
