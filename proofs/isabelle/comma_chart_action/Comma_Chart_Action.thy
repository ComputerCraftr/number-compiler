theory Comma_Chart_Action
  imports Comma_Round_Weights.Comma_Round_Weights
    Shared_S_Arithmetic.S_Arithmetic_Skew
begin

text \<open>Headroom belongs to a decimal boundary chart. The action retains
scale transport and the affine rebase; its guards retain their relation and
ordered event label. Neither guard reduction nor source admission is inferred
from equality of a scalar minimum. Guard coefficients derived using a digit
phase are valid only on that admitted residue fiber; the generic guard type
does not establish or erase this source condition.\<close>

datatype comma_chart_action = Comma_Chart_Action int int int

fun comma_chart_apply :: "comma_chart_action \<Rightarrow> int \<times> int \<Rightarrow> int \<times> int" where
  "comma_chart_apply (Comma_Chart_Action l a b) (X,H) = (l*X,H+a*X+b)"

fun comma_chart_linear :: "comma_chart_action \<Rightarrow> int skew_transfer" where
  "comma_chart_linear (Comma_Chart_Action l a b) =
    \<lparr>upper=1, offset=a, lower=l\<rparr>"

fun comma_chart_then :: "comma_chart_action \<Rightarrow> comma_chart_action \<Rightarrow> comma_chart_action" where
  "comma_chart_then (Comma_Chart_Action l a b) (Comma_Chart_Action m c d) =
    (let T = shared_skew_then (comma_chart_linear (Comma_Chart_Action l a b))
      (comma_chart_linear (Comma_Chart_Action m c d))
     in Comma_Chart_Action (lower T) (offset T) (b+d))"

lemma comma_chart_then_coefficients [simp]:
  "comma_chart_then (Comma_Chart_Action l a b) (Comma_Chart_Action m c d) =
    Comma_Chart_Action (m*l) (a+l*c) (b+d)"
  by (simp add: shared_skew_then_def Let_def)

declare comma_chart_then.simps [simp del]

lemma comma_chart_then_refines:
  "comma_chart_apply (comma_chart_then A B) x =
    comma_chart_apply B (comma_chart_apply A x)"
  by (cases A; cases B; cases x) (simp add: algebra_simps)

lemma comma_chart_then_assoc:
  "comma_chart_then (comma_chart_then A B) C =
    comma_chart_then A (comma_chart_then B C)"
  by (cases A; cases B; cases C) (simp add: algebra_simps)

lemma comma_chart_identity [simp]:
  "comma_chart_then (Comma_Chart_Action 1 0 0) A = A"
  "comma_chart_then A (Comma_Chart_Action 1 0 0) = A"
  "comma_chart_apply (Comma_Chart_Action 1 0 0) x = x"
proof -
  show "comma_chart_then (Comma_Chart_Action 1 0 0) A = A"
    by (cases A) simp
  show "comma_chart_then A (Comma_Chart_Action 1 0 0) = A"
    by (cases A) simp
  show "comma_chart_apply (Comma_Chart_Action 1 0 0) x = x"
    by (cases x) simp
qed

datatype comma_affine_guard_form = Comma_Affine_Form int int int
datatype comma_guard_relation = Comma_LT | Comma_EQ | Comma_GT | Comma_LE | Comma_GE

type_synonym 'a comma_decorated_guard = "comma_affine_guard_form \<times> comma_guard_relation \<times> 'a"

fun comma_form_value :: "comma_affine_guard_form \<Rightarrow> int \<times> int \<Rightarrow> int" where
  "comma_form_value (Comma_Affine_Form a b c) (X,H) = a*X+b*H+c"

fun comma_relation_holds :: "comma_guard_relation \<Rightarrow> int \<Rightarrow> bool" where
  "comma_relation_holds Comma_LT v = (v<0)"
| "comma_relation_holds Comma_EQ v = (v=0)"
| "comma_relation_holds Comma_GT v = (v>0)"
| "comma_relation_holds Comma_LE v = (v\<le>0)"
| "comma_relation_holds Comma_GE v = (v\<ge>0)"

fun comma_guard_holds :: "'a comma_decorated_guard \<Rightarrow> int \<times> int \<Rightarrow> bool" where
  "comma_guard_holds (form,relation,payload) x =
    comma_relation_holds relation (comma_form_value form x)"

fun comma_form_pullback :: "comma_chart_action \<Rightarrow> comma_affine_guard_form \<Rightarrow> comma_affine_guard_form" where
  "comma_form_pullback (Comma_Chart_Action l a b) (Comma_Affine_Form u v w) =
    Comma_Affine_Form (u*l+v*a) v (w+v*b)"

fun comma_guard_pullback :: "comma_chart_action \<Rightarrow> 'a comma_decorated_guard \<Rightarrow> 'a comma_decorated_guard" where
  "comma_guard_pullback A (form,relation,payload) =
    (comma_form_pullback A form,relation,payload)"

lemma comma_form_transport:
  "comma_form_value (comma_form_pullback A g) x =
    comma_form_value g (comma_chart_apply A x)"
  by (cases A; cases g; cases x) (simp add: algebra_simps)

theorem comma_guard_transport:
  "comma_guard_holds (comma_guard_pullback A g) x =
    comma_guard_holds g (comma_chart_apply A x)"
  by (cases g) (simp add: comma_form_transport split: prod.splits)

lemma comma_form_pullback_compose:
  "comma_form_pullback (comma_chart_then A B) g =
    comma_form_pullback A (comma_form_pullback B g)"
  by (cases A; cases B; cases g) (simp add: algebra_simps)

theorem comma_guard_pullback_compose:
  "comma_guard_pullback (comma_chart_then A B) g =
    comma_guard_pullback A (comma_guard_pullback B g)"
  by (cases g) (simp add: comma_form_pullback_compose split: prod.splits)

lemma comma_guard_relation_payload_preserved:
  "snd (comma_guard_pullback A g) = snd g"
  by (cases g) (simp split: prod.splits)

lemma comma_guard_matching_decorations:
  "map snd (filter (\<lambda>g. comma_guard_holds g x)
      (map (comma_guard_pullback A) G)) =
    map snd (filter (\<lambda>g. comma_guard_holds g (comma_chart_apply A x)) G)"
  by (induction G) (auto simp: comma_guard_transport
    comma_guard_relation_payload_preserved)

lemma comma_guard_first_decoration:
  "map_option snd (List.find (\<lambda>g. comma_guard_holds g x)
      (map (comma_guard_pullback A) G)) =
    map_option snd (List.find
      (\<lambda>g. comma_guard_holds g (comma_chart_apply A x)) G)"
  by (induction G) (auto simp: comma_guard_transport
    comma_guard_relation_payload_preserved)

type_synonym 'a comma_guarded_chart = "comma_chart_action \<times> 'a comma_decorated_guard list"

fun comma_guarded_then :: "'a comma_guarded_chart \<Rightarrow> 'a comma_guarded_chart \<Rightarrow> 'a comma_guarded_chart" where
  "comma_guarded_then (A,GA) (B,GB) =
    (comma_chart_then A B, GA @ map (comma_guard_pullback A) GB)"

lemma comma_guarded_then_assoc:
  "comma_guarded_then (comma_guarded_then A B) C =
    comma_guarded_then A (comma_guarded_then B C)"
  by (cases A; cases B; cases C)
    (simp add: comma_chart_then_assoc comma_guard_pullback_compose
      map_map comp_def append_assoc)

lemma comma_guarded_then_admission:
  "list_all (\<lambda>g. comma_guard_holds g x)
      (snd (comma_guarded_then (A,GA) (B,GB))) =
    (list_all (\<lambda>g. comma_guard_holds g x) GA \<and>
      list_all (\<lambda>g. comma_guard_holds g (comma_chart_apply A x)) GB)"
proof -
  have pulled: "list_all (\<lambda>g. comma_guard_holds g x)
      (map (comma_guard_pullback A) GB) =
    list_all (\<lambda>g. comma_guard_holds g (comma_chart_apply A x)) GB"
    by (induction GB)
      (simp_all only: list.map list_all_Nil_iff list_all_Cons_iff
        comma_guard_transport)
  show ?thesis
    by (simp only: comma_guarded_then.simps snd_conv list_all_append pulled)
qed

text \<open>The following connection refers to the implemented canonical chart
transition. Generic composition alone would not establish seam refinement.\<close>

fun comma_chart_coordinates :: "nat \<Rightarrow> comma_finite_position \<Rightarrow> int \<times> int" where
  "comma_chart_coordinates p (Comma_Entry f delta x) =
    (int (10^(p+delta)),int (10^(p+delta))-int x)"
| "comma_chart_coordinates p (Comma_Near f delta h) =
    (int (10^(p+delta)),int h)"

lemma comma_chart_canonical_entry:
  assumes move: "comma_finite_step r (Comma_Entry f delta x) =
    Comma_Next (Comma_Near g e h)"
  shows "comma_chart_coordinates p (Comma_Near g e h) =
    comma_chart_apply (Comma_Chart_Action 1 (-1) (int x+int h))
      (comma_chart_coordinates p (Comma_Entry f delta x))"
proof -
  have "e=delta" using move
    by (auto simp: comma_finite_step_def comma_weighted_step_def Let_def
      split: if_splits)
  then show ?thesis by (simp add: algebra_simps)
qed

lemma comma_chart_canonical_near:
  assumes move: "comma_finite_step r (Comma_Near f delta h) =
    Comma_Next (Comma_Near g e j)"
  shows "comma_chart_coordinates p (Comma_Near g e j) =
    comma_chart_apply (Comma_Chart_Action 1 0 (int j-int h))
      (comma_chart_coordinates p (Comma_Near f delta h))"
proof -
  have "e=delta" using move
    by (auto simp: comma_finite_step_def comma_weighted_step_def Let_def
      split: if_splits)
  then show ?thesis by (simp add: algebra_simps)
qed

lemma comma_chart_cross_coordinates:
  assumes "h \<le> I"
  shows "comma_chart_coordinates p (Comma_Entry g (delta+k) (I-h)) =
    comma_chart_apply (Comma_Chart_Action (10^k) (10^k) (-int I))
      (comma_chart_coordinates p (Comma_Near f delta h))"
  using assms by (simp add: of_nat_diff power_add algebra_simps)

lemma comma_chart_canonical_seam:
  assumes move: "comma_finite_step r (Comma_Near f delta h) =
    Comma_Next (Comma_Entry g e x)"
  defines "d \<equiv> (10-h mod 10) mod 10"
  defines "I \<equiv> if f<9 then 10*d+f+1 else 10*d+1"
  defines "k \<equiv> if f<9 then 0 else 1"
  shows "comma_chart_coordinates p (Comma_Entry g e x) =
    comma_chart_apply (Comma_Chart_Action (10^k) (10^k) (-int I))
      (comma_chart_coordinates p (Comma_Near f delta h))"
proof -
  have shape: "h \<le> I" "e = delta+k" "x = I-h"
    using move by (auto simp: comma_finite_step_def comma_weighted_step_def
      Let_def d_def I_def k_def split: if_splits; arith)+
  show ?thesis unfolding shape(2,3)
    by (rule comma_chart_cross_coordinates[OF shape(1)])
qed

lemma comma_chart_ordinary_seam_regression:
  "comma_finite_step 5 (Comma_Near 1 0 9) = Comma_Next (Comma_Entry 2 0 3)"
  "comma_chart_apply (Comma_Chart_Action 1 1 (-12)) (100000,9) = (100000,99997)"
  "(9::int)-12 \<noteq> 99997"
  by (simp_all add: comma_finite_step_def comma_weighted_step_def Let_def)

lemma comma_chart_power_seam_regression:
  "comma_finite_step 5 (Comma_Near 9 0 3) = Comma_Next (Comma_Entry 1 1 68)"
  "comma_chart_apply (Comma_Chart_Action 10 10 (-71)) (100000,3) = (1000000,999932)"
  by (simp_all add: comma_finite_step_def comma_weighted_step_def Let_def)

lemma comma_chart_positive_fork_regression:
  "comma_finite_step 5 (Comma_Near 1 0 82) = Comma_Fork 2 0"
  "comma_guard_holds (Comma_Affine_Form 0 1 (-82),Comma_EQ,()) (100000,82)"
  "\<not> comma_guard_holds (Comma_Affine_Form 0 1 (-82),Comma_GT,()) (100000,82)"
  by (simp_all add: comma_finite_step_def comma_weighted_step_def Let_def)

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_chart_then_refines comma_chart_then_assoc comma_chart_identity
      comma_guard_transport comma_guard_pullback_compose
      comma_guard_relation_payload_preserved comma_guard_matching_decorations
      comma_guard_first_decoration comma_guarded_then_assoc
      comma_guarded_then_admission comma_chart_canonical_entry
      comma_chart_canonical_near comma_chart_cross_coordinates
      comma_chart_canonical_seam comma_chart_ordinary_seam_regression
      comma_chart_power_seam_regression comma_chart_positive_fork_regression})
    then () else error "Comma chart transport depends on an oracle";
\<close>
end
