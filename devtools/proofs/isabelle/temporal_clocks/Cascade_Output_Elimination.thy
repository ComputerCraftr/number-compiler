theory Cascade_Output_Elimination
  imports Main
begin

text \<open>
  This theory specifies the finite grouped output elimination used by the
  dependency-cascade composer.  A box is a Cartesian selector, not an
  assertion that all selectors have the same output.  Soundness and coverage
  bind the boxes to the actual transition and output functions.  Functionality
  is conditional on the overlap-conflict check used by the executable MDD
  builder; nonempty masks alone do not imply uniqueness.
\<close>

type_synonym ('l1, 'l2, 'r1) left_box = "'l1 set \<times> 'l2 set \<times> 'r1 set"
type_synonym ('l1, 'r2, 'r1) right_box = "'l1 set \<times> 'r2 set \<times> 'r1 set"
type_synonym ('v, 'l1, 'r1) first_box = "'v \<times> 'l1 set \<times> 'r1 set"
type_synonym ('w, 'l2, 'r2) second_box = "'w \<times> 'l2 set \<times> 'r2 set"

definition first_box_member ::
    "('v, 'l1, 'r1) first_box \<Rightarrow> 'v \<Rightarrow> 'l1 \<Rightarrow> 'r1 \<Rightarrow> bool" where
  "first_box_member box v l r =
    (case box of (value, left, right) \<Rightarrow>
      v = value \<and> l \<in> left \<and> r \<in> right)"

definition second_box_member ::
    "('w, 'l2, 'r2) second_box \<Rightarrow> 'w \<Rightarrow> 'l2 \<Rightarrow> 'r2 \<Rightarrow> bool" where
  "second_box_member box w l r =
    (case box of (value, left, right) \<Rightarrow>
      w = value \<and> l \<in> left \<and> r \<in> right)"

definition left_box_member ::
    "('l1, 'l2, 'r1) left_box \<Rightarrow> 'l1 \<Rightarrow> 'l2 \<Rightarrow> 'r1 \<Rightarrow> bool" where
  "left_box_member box l l2 r =
    (case box of (left, middle, right) \<Rightarrow>
      l \<in> left \<and> l2 \<in> middle \<and> r \<in> right)"

definition right_box_member ::
    "('l1, 'r2, 'r1) right_box \<Rightarrow> 'l1 \<Rightarrow> 'r2 \<Rightarrow> 'r1 \<Rightarrow> bool" where
  "right_box_member box l r2 r =
    (case box of (left, middle, right) \<Rightarrow>
      l \<in> left \<and> r2 \<in> middle \<and> r \<in> right)"

definition left_transition_preimage ::
    "('l1 \<Rightarrow> 'a \<Rightarrow> 'l1 option) \<Rightarrow>
      'a \<Rightarrow> 'l1 set \<Rightarrow> 'l1 set" where
  "left_transition_preimage step a target =
    {source. \<exists>after \<in> target. step source a = Some after}"

definition right_transition_preimage ::
    "('r1 \<Rightarrow> 'a \<Rightarrow> 'r1 option) \<Rightarrow>
      'a \<Rightarrow> 'r1 set \<Rightarrow> 'r1 set" where
  "right_transition_preimage step a target =
    {source. \<exists>after \<in> target. step source a = Some after}"

lemma left_transition_preimage_iff:
  "l \<in> left_transition_preimage step a target \<longleftrightarrow>
    (\<exists>after \<in> target. step l a = Some after)"
  by (simp add: left_transition_preimage_def)

lemma right_transition_preimage_iff:
  "r \<in> right_transition_preimage step a target \<longleftrightarrow>
    (\<exists>after \<in> target. step r a = Some after)"
  by (simp add: right_transition_preimage_def)

definition left_lift ::
    "('l1, 'l2, 'r1) left_box \<Rightarrow>
      'l1 \<Rightarrow> 'l2 set \<Rightarrow> 'r1 \<Rightarrow> bool" where
  "left_lift box l middle r =
    (\<exists>l2 \<in> middle. left_box_member box l l2 r)"

definition right_lift ::
    "('l1, 'r2, 'r1) right_box \<Rightarrow>
      'l1 \<Rightarrow> 'r2 set \<Rightarrow> 'r1 \<Rightarrow> bool" where
  "right_lift box l middle r =
    (\<exists>r2 \<in> middle. right_box_member box l r2 r)"

lemma left_lift_iff:
  "left_lift box l middle r \<longleftrightarrow>
    (\<exists>l2. l2 \<in> middle \<and> left_box_member box l l2 r)"
  by (auto simp: left_lift_def)

lemma right_lift_iff:
  "right_lift box l middle r \<longleftrightarrow>
    (\<exists>r2. r2 \<in> middle \<and> right_box_member box l r2 r)"
  by (auto simp: right_lift_def)

definition semantic_two_stage ::
    "('l1 \<Rightarrow> 'a \<Rightarrow> 'l1 option) \<Rightarrow>
     ('r1 \<Rightarrow> 'a \<Rightarrow> 'r1 option) \<Rightarrow>
     ('l1 \<Rightarrow> 'a \<Rightarrow> 'r1 \<Rightarrow> 'v option) \<Rightarrow>
     ('l2 \<Rightarrow> 'v \<Rightarrow> 'r2 \<Rightarrow> 'w option) \<Rightarrow>
     ('l1, 'l2, 'r1) left_box set \<Rightarrow>
     ('l1, 'r2, 'r1) right_box set \<Rightarrow>
     (('l1, 'l2, 'r1) left_box \<times> 'a \<times>
       ('l1, 'r2, 'r1) right_box \<times> 'w) set" where
  "semantic_two_stage left_step right_step first_emit second_emit
      left_context right_context =
    {(left_box, a, right_box, w).
      \<exists>l1 l2 right_before left_after right_after r2 v.
        left_box \<in> left_context \<and>
        right_box \<in> right_context \<and>
        first_emit l1 a right_after = Some v \<and>
        left_step l1 a = Some left_after \<and>
        right_step right_after a = Some right_before \<and>
        left_box_member left_box l1 l2 right_before \<and>
        right_box_member right_box left_after r2 right_after \<and>
        second_emit l2 v r2 = Some w}"

definition lifted_two_stage ::
    "('l1 \<Rightarrow> 'a \<Rightarrow> 'l1 option) \<Rightarrow>
     ('r1 \<Rightarrow> 'a \<Rightarrow> 'r1 option) \<Rightarrow>
     ('a \<Rightarrow> ('v, 'l1, 'r1) first_box set) \<Rightarrow>
     ('v \<Rightarrow> ('w, 'l2, 'r2) second_box set) \<Rightarrow>
     ('l1, 'l2, 'r1) left_box set \<Rightarrow>
     ('l1, 'r2, 'r1) right_box set \<Rightarrow>
     (('l1, 'l2, 'r1) left_box \<times> 'a \<times>
       ('l1, 'r2, 'r1) right_box \<times> 'w) set" where
  "lifted_two_stage left_step right_step first_boxes second_boxes
      left_context right_context =
    {(left_box, a, right_box, w).
      \<exists>first_box second_box l1 right_after left_after right_before v.
        left_box \<in> left_context \<and>
        right_box \<in> right_context \<and>
        first_box \<in> first_boxes a \<and>
        second_box \<in> second_boxes v \<and>
        first_box_member first_box v l1 right_after \<and>
        left_step l1 a = Some left_after \<and>
        right_step right_after a = Some right_before \<and>
        left_lift left_box l1
          (case second_box of (_, left, _) \<Rightarrow> left) right_before \<and>
        right_lift right_box left_after
          (case second_box of (_, _, right) \<Rightarrow> right) right_after \<and>
        (case second_box of (value, left, right) \<Rightarrow> value = w)}"

text \<open>The lifted relation contains only independent Cartesian selector
lifts.  The second-stage output is chosen by the canonical second box; its
soundness below proves that every pair of selected middle states has that
output.  No intermediate word or Cartesian product is materialized.\<close>

definition output_functional ::
    "(('l1, 'l2, 'r1) left_box \<times> 'a \<times>
      ('l1, 'r2, 'r1) right_box \<times> 'w) set \<Rightarrow> bool" where
  "output_functional relation =
    (\<forall>left_box a right_box w1 w2.
      (left_box, a, right_box, w1) \<in> relation \<longrightarrow>
      (left_box, a, right_box, w2) \<in> relation \<longrightarrow> w1 = w2)"

definition overlap_conflict_free ::
    "(('l1, 'l2, 'r1) left_box \<times> 'a \<times>
      ('l1, 'r2, 'r1) right_box \<times> 'w) set \<Rightarrow> bool" where
  "overlap_conflict_free relation =
    (\<not> (\<exists>left_box a right_box w1 w2.
      (left_box, a, right_box, w1) \<in> relation \<and>
      (left_box, a, right_box, w2) \<in> relation \<and> w1 \<noteq> w2))"

theorem overlap_conflict_free_functional:
  assumes "overlap_conflict_free relation"
  shows "output_functional relation"
  using assms by (auto simp: overlap_conflict_free_def output_functional_def)

definition first_boxes_sound ::
    "('l1 \<Rightarrow> 'a \<Rightarrow> 'r1 \<Rightarrow> 'v option) \<Rightarrow>
     ('a \<Rightarrow> ('v, 'l1, 'r1) first_box set) \<Rightarrow> bool" where
  "first_boxes_sound emit boxes =
    (\<forall>a box v l r.
      box \<in> boxes a \<longrightarrow> first_box_member box v l r \<longrightarrow>
      emit l a r = Some v)"

definition first_boxes_cover ::
    "('l1 \<Rightarrow> 'a \<Rightarrow> 'r1 \<Rightarrow> 'v option) \<Rightarrow>
     ('a \<Rightarrow> ('v, 'l1, 'r1) first_box set) \<Rightarrow> bool" where
  "first_boxes_cover emit boxes =
    (\<forall>a l r v. emit l a r = Some v \<longrightarrow>
      (\<exists>box \<in> boxes a. first_box_member box v l r))"

definition second_boxes_sound ::
    "('l2 \<Rightarrow> 'v \<Rightarrow> 'r2 \<Rightarrow> 'w option) \<Rightarrow>
     ('v \<Rightarrow> ('w, 'l2, 'r2) second_box set) \<Rightarrow> bool" where
  "second_boxes_sound emit boxes =
    (\<forall>v box w l r.
      box \<in> boxes v \<longrightarrow> second_box_member box w l r \<longrightarrow>
      emit l v r = Some w)"

definition second_boxes_cover ::
    "('l2 \<Rightarrow> 'v \<Rightarrow> 'r2 \<Rightarrow> 'w option) \<Rightarrow>
     ('v \<Rightarrow> ('w, 'l2, 'r2) second_box set) \<Rightarrow> bool" where
  "second_boxes_cover emit boxes =
    (\<forall>v l r w. emit l v r = Some w \<longrightarrow>
      (\<exists>box \<in> boxes v. second_box_member box w l r))"

theorem lifted_two_stage_semantic_eq:
  assumes "first_boxes_sound first_emit first_boxes"
    and "first_boxes_cover first_emit first_boxes"
    and "second_boxes_sound second_emit second_boxes"
    and "second_boxes_cover second_emit second_boxes"
  shows "lifted_two_stage left_step right_step first_boxes second_boxes
      left_context right_context =
    semantic_two_stage left_step right_step first_emit second_emit
      left_context right_context"
proof (rule set_eqI)
  fix x
  show "x \<in> lifted_two_stage left_step right_step first_boxes second_boxes
      left_context right_context \<longleftrightarrow>
    x \<in> semantic_two_stage left_step right_step first_emit second_emit
      left_context right_context"
  proof
    assume "x \<in> lifted_two_stage left_step right_step first_boxes second_boxes
        left_context right_context"
    then obtain left_box a right_box w first_box second_box l1 right_after
        left_after right_before v where
      x_def: "x = (left_box, a, right_box, w)" and
      memberships:
        "left_box \<in> left_context"
        "right_box \<in> right_context"
        "first_box \<in> first_boxes a"
        "second_box \<in> second_boxes v"
        "first_box_member first_box v l1 right_after"
        "left_step l1 a = Some left_after"
        "right_step right_after a = Some right_before"
        "left_lift left_box l1
          (case second_box of (_, left, _) \<Rightarrow> left) right_before"
        "right_lift right_box left_after
          (case second_box of (_, _, right) \<Rightarrow> right) right_after"
        "case second_box of (value, left, right) \<Rightarrow> value = w"
      unfolding lifted_two_stage_def
      by blast
    obtain l2 where l2:
      "l2 \<in> (case second_box of (_, left, _) \<Rightarrow> left)" and
      left_member: "left_box_member left_box l1 l2 right_before"
      using memberships(8) by (auto simp: left_lift_def)
    obtain r2 where r2:
      "r2 \<in> (case second_box of (_, _, right) \<Rightarrow> right)" and
      right_member: "right_box_member right_box left_after r2 right_after"
      using memberships(9) by (auto simp: right_lift_def)
    have second_member: "second_box_member second_box w l2 r2"
      using memberships(4) memberships(10) l2 r2
      by (cases second_box) (simp add: second_box_member_def)
    have first_output: "first_emit l1 a right_after = Some v"
      using assms(1) memberships(3) memberships(5)
      unfolding first_boxes_sound_def by blast
    have second_output: "second_emit l2 v r2 = Some w"
      using assms(3) memberships(4) second_member
      unfolding second_boxes_sound_def by blast
    show "x \<in> semantic_two_stage left_step right_step first_emit second_emit
        left_context right_context"
      unfolding semantic_two_stage_def
      using x_def memberships(1,2,6,7) left_member right_member
        first_output second_output
      by blast
  next
    assume "x \<in> semantic_two_stage left_step right_step first_emit second_emit
        left_context right_context"
    then obtain left_box a right_box w l1 l2 right_before left_after
        right_after r2 v where
      x_def: "x = (left_box, a, right_box, w)" and
      semantic:
        "left_box \<in> left_context"
        "right_box \<in> right_context"
        "first_emit l1 a right_after = Some v"
        "left_step l1 a = Some left_after"
        "right_step right_after a = Some right_before"
        "left_box_member left_box l1 l2 right_before"
        "right_box_member right_box left_after r2 right_after"
        "second_emit l2 v r2 = Some w"
      unfolding semantic_two_stage_def
      by blast
    obtain first_box where first_box:
      "first_box \<in> first_boxes a"
      "first_box_member first_box v l1 right_after"
      using assms(2) semantic(3)
      unfolding first_boxes_cover_def by blast
    obtain second_box where second_box:
      "second_box \<in> second_boxes v"
      "second_box_member second_box w l2 r2"
      using assms(4) semantic(8)
      unfolding second_boxes_cover_def by blast
    have left_lifted:
        "left_lift left_box l1
          (case second_box of (_, left, _) \<Rightarrow> left) right_before"
      using second_box(2) semantic(6)
      by (cases second_box) (auto simp: left_lift_def second_box_member_def)
    have right_lifted:
        "right_lift right_box left_after
          (case second_box of (_, _, right) \<Rightarrow> right) right_after"
      using second_box(2) semantic(7)
      by (cases second_box) (auto simp: right_lift_def second_box_member_def)
    have second_value:
      "case second_box of (value, left, right) \<Rightarrow> value = w"
      using second_box(2) by (cases second_box) (auto simp: second_box_member_def)
    show "x \<in> lifted_two_stage left_step right_step first_boxes second_boxes
        left_context right_context"
    unfolding lifted_two_stage_def
    using x_def semantic(1,2,4,5) first_box(1,2) second_box(1,2)
      left_lifted right_lifted second_value
    by blast
  qed
qed

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms left_transition_preimage_iff right_transition_preimage_iff
      left_lift_iff right_lift_iff overlap_conflict_free_functional
      lifted_two_stage_semantic_eq}) then ()
    else error "cascade output elimination proof depends on an oracle";
\<close>

end
