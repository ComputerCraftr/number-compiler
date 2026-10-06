theory Comma_Selected_Return_Blocks
  imports Comma_Branch_Period.Comma_Branch_Period
    Comma_Return_Engine.Comma_Return_Engine
begin

text \<open>A selected-return block is a checked temporal proof certificate, not a
flattened list of boundary visits. Its cached summary gives the admitted
source and target, macro count, and exponent displacement. The decision tree
retains selected fork choices. Certification at each leaf checks the complete
ordered child pair and, for a selected Z child, a proof that the smaller N
sibling terminates. Composition and loop repetition add one summary node;
they do not normalize by traversing the descendant tree. Macro count is not
the literal transition weight: the literal observation below establishes an
existential weight and lower bound. An exact weighted CLI locator still needs
its separate executable refinement.\<close>

datatype comma_selected_choice_tree =
    Comma_Selected_Choice_Empty
  | Comma_Selected_Choice_Leaf bool
  | Comma_Selected_Choice_Join comma_selected_choice_tree comma_selected_choice_tree
  | Comma_Selected_Choice_Repeat comma_selected_choice_tree nat

fun comma_selected_choice_word :: "comma_selected_choice_tree \<Rightarrow> bool list" where
  "comma_selected_choice_word Comma_Selected_Choice_Empty = []"
| "comma_selected_choice_word (Comma_Selected_Choice_Leaf b) = [b]"
| "comma_selected_choice_word (Comma_Selected_Choice_Join A B) =
    comma_selected_choice_word A @ comma_selected_choice_word B"
| "comma_selected_choice_word (Comma_Selected_Choice_Repeat A k) =
    concat (replicate k (comma_selected_choice_word A))"

record comma_selected_return_block =
  selected_block_source :: comma_boundary_state
  selected_block_target :: comma_boundary_state
  selected_block_count :: nat
  selected_block_delta :: nat
  selected_block_choices :: comma_selected_choice_tree

definition comma_selected_block_view ::
  "comma_selected_return_block \<Rightarrow>
    comma_boundary_state \<times> comma_boundary_state \<times> nat \<times> nat \<times>
      comma_selected_choice_tree" where
  "comma_selected_block_view A =
    (selected_block_source A, selected_block_target A,
     selected_block_count A, selected_block_delta A,
     selected_block_choices A)"

definition comma_selected_block_empty ::
  "comma_boundary_state \<Rightarrow> comma_selected_return_block" where
  "comma_selected_block_empty q = \<lparr>
    selected_block_source=q, selected_block_target=q,
    selected_block_count=0, selected_block_delta=0,
    selected_block_choices=Comma_Selected_Choice_Empty\<rparr>"

definition comma_selected_block_leaf ::
  "bool \<Rightarrow> comma_boundary_state \<Rightarrow> comma_boundary_state \<Rightarrow>
    nat \<Rightarrow> comma_selected_return_block" where
  "comma_selected_block_leaf choice q target d = \<lparr>
    selected_block_source=q, selected_block_target=target,
    selected_block_count=1, selected_block_delta=d,
    selected_block_choices=Comma_Selected_Choice_Leaf choice\<rparr>"

definition comma_selected_block_then ::
  "comma_selected_return_block \<Rightarrow> comma_selected_return_block \<Rightarrow>
    comma_selected_return_block" where
  "comma_selected_block_then A B = \<lparr>
    selected_block_source=selected_block_source A,
    selected_block_target=selected_block_target B,
    selected_block_count=selected_block_count A+selected_block_count B,
    selected_block_delta=selected_block_delta A+selected_block_delta B,
    selected_block_choices=Comma_Selected_Choice_Join
      (selected_block_choices A) (selected_block_choices B)\<rparr>"

definition comma_selected_block_repeat ::
  "nat \<Rightarrow> comma_selected_return_block \<Rightarrow> comma_selected_return_block" where
  "comma_selected_block_repeat k A = \<lparr>
    selected_block_source=selected_block_source A,
    selected_block_target=selected_block_target A,
    selected_block_count=k*selected_block_count A,
    selected_block_delta=k*selected_block_delta A,
    selected_block_choices=Comma_Selected_Choice_Repeat
      (selected_block_choices A) k\<rparr>"

definition comma_selected_block_square ::
  "comma_selected_return_block \<Rightarrow> comma_selected_return_block" where
  "comma_selected_block_square A = comma_selected_block_repeat 2 A"

inductive comma_selected_return_certified :: "comma_selected_return_block \<Rightarrow> bool" where
  empty:
    "comma_boundary_valid q \<Longrightarrow>
      comma_selected_return_certified (comma_selected_block_empty q)"
| leaf:
    "comma_boundary_valid q \<Longrightarrow>
     comma_macro_defined q \<Longrightarrow>
     comma_total_macro q=Comma_Fork_At a d \<Longrightarrow>
     comma_total_children q =
       [(Comma_N,a,(snd (snd q)+d) mod 924),
        (Comma_Z,a,(snd (snd q)+d) mod 924)] \<Longrightarrow>
     target = (if choice then (Comma_Z,a,(snd (snd q)+d) mod 924)
       else (Comma_N,a,(snd (snd q)+d) mod 924)) \<Longrightarrow>
     target \<in> set (comma_total_children q) \<Longrightarrow>
     comma_boundary_valid target \<Longrightarrow>
     (choice \<longrightarrow>
       comma_boundary_terminates (Comma_N,a,(snd (snd q)+d) mod 924)) \<Longrightarrow>
     comma_selected_return_certified
       (comma_selected_block_leaf choice q target d)"
| compose:
    "comma_selected_return_certified A \<Longrightarrow>
     comma_selected_return_certified B \<Longrightarrow>
     selected_block_target A=selected_block_source B \<Longrightarrow>
     comma_selected_return_certified (comma_selected_block_then A B)"
| iterate:
    "comma_selected_return_certified A \<Longrightarrow>
     selected_block_source A=selected_block_target A \<Longrightarrow>
     comma_selected_return_certified (comma_selected_block_repeat k A)"

lemma comma_selected_block_leaf_certified:
  assumes valid: "comma_boundary_valid q"
    and defined: "comma_macro_defined q"
    and fork: "comma_total_macro q=Comma_Fork_At a d"
    and ordered: "comma_total_children q =
      [(Comma_N,a,(snd (snd q)+d) mod 924),
       (Comma_Z,a,(snd (snd q)+d) mod 924)]"
    and selected: "target = (if choice then (Comma_Z,a,(snd (snd q)+d) mod 924)
      else (Comma_N,a,(snd (snd q)+d) mod 924))"
    and member: "target \<in> set (comma_total_children q)"
    and target_valid: "comma_boundary_valid target"
    and smaller_terminates: "choice \<Longrightarrow>
      comma_boundary_terminates (Comma_N,a,(snd (snd q)+d) mod 924)"
  shows "comma_selected_return_certified
    (comma_selected_block_leaf choice q target d)"
proof -
  have sibling:
    "choice \<longrightarrow>
      comma_boundary_terminates (Comma_N,a,(snd (snd q)+d) mod 924)"
  proof
    assume selected: "choice"
    show "comma_boundary_terminates (Comma_N,a,(snd (snd q)+d) mod 924)"
      by (rule smaller_terminates[OF selected])
  qed
  show ?thesis
    by (rule comma_selected_return_certified.leaf
      [OF valid defined fork ordered selected member target_valid sibling])
qed

lemma comma_selected_block_N_certified:
  assumes valid: "comma_boundary_valid q"
    and defined: "comma_macro_defined q"
    and fork: "comma_total_macro q=Comma_Fork_At a d"
    and ordered: "comma_total_children q =
      [(Comma_N,a,(snd (snd q)+d) mod 924),
       (Comma_Z,a,(snd (snd q)+d) mod 924)]"
    and target_valid: "comma_boundary_valid
      (Comma_N,a,(snd (snd q)+d) mod 924)"
  shows "comma_selected_return_certified
    (comma_selected_block_leaf False q
      (Comma_N,a,(snd (snd q)+d) mod 924) d)"
proof (rule comma_selected_return_certified.leaf[OF valid defined fork ordered])
  show "(Comma_N,a,(snd (snd q)+d) mod 924) =
      (if False then (Comma_Z,a,(snd (snd q)+d) mod 924)
       else (Comma_N,a,(snd (snd q)+d) mod 924))"
    by simp
  show "(Comma_N,a,(snd (snd q)+d) mod 924) \<in> set (comma_total_children q)"
    using ordered by simp
  show "comma_boundary_valid (Comma_N,a,(snd (snd q)+d) mod 924)"
    by (rule target_valid)
  show "False \<longrightarrow> comma_boundary_terminates
      (Comma_N,a,(snd (snd q)+d) mod 924)"
    by simp
qed

lemma comma_selected_block_Z_certified:
  assumes valid: "comma_boundary_valid q"
    and defined: "comma_macro_defined q"
    and fork: "comma_total_macro q=Comma_Fork_At a d"
    and ordered: "comma_total_children q =
      [(Comma_N,a,(snd (snd q)+d) mod 924),
       (Comma_Z,a,(snd (snd q)+d) mod 924)]"
    and target_valid: "comma_boundary_valid
      (Comma_Z,a,(snd (snd q)+d) mod 924)"
    and smaller_terminates: "comma_boundary_terminates
      (Comma_N,a,(snd (snd q)+d) mod 924)"
  shows "comma_selected_return_certified
    (comma_selected_block_leaf True q
      (Comma_Z,a,(snd (snd q)+d) mod 924) d)"
proof (rule comma_selected_return_certified.leaf[OF valid defined fork ordered])
  show "(Comma_Z,a,(snd (snd q)+d) mod 924) =
      (if True then (Comma_Z,a,(snd (snd q)+d) mod 924)
       else (Comma_N,a,(snd (snd q)+d) mod 924))"
    by simp
  show "(Comma_Z,a,(snd (snd q)+d) mod 924) \<in> set (comma_total_children q)"
    using ordered by simp
  show "comma_boundary_valid (Comma_Z,a,(snd (snd q)+d) mod 924)"
    by (rule target_valid)
  show "True \<longrightarrow> comma_boundary_terminates
      (Comma_N,a,(snd (snd q)+d) mod 924)"
    using smaller_terminates by simp
qed

lemma comma_selected_block_then_certified:
  assumes left: "comma_selected_return_certified A"
    and right: "comma_selected_return_certified B"
    and joins: "selected_block_target A=selected_block_source B"
  shows "comma_selected_return_certified (comma_selected_block_then A B)"
  by (rule comma_selected_return_certified.compose[OF left right joins])

lemma comma_selected_block_repeat_certified:
  assumes block: "comma_selected_return_certified A"
    and loop: "selected_block_source A=selected_block_target A"
  shows "comma_selected_return_certified (comma_selected_block_repeat k A)"
  by (rule comma_selected_return_certified.iterate[OF block loop])

lemma comma_selected_block_square_certified:
  assumes block: "comma_selected_return_certified A"
    and loop: "selected_block_source A=selected_block_target A"
  shows "comma_selected_return_certified (comma_selected_block_square A)"
  unfolding comma_selected_block_square_def
  by (rule comma_selected_block_repeat_certified[OF block loop])

lemma comma_selected_block_source_valid:
  assumes "comma_selected_return_certified A"
  shows "comma_boundary_valid (selected_block_source A)"
  using assms
  by (induction rule: comma_selected_return_certified.induct)
    (auto simp: comma_selected_block_empty_def comma_selected_block_leaf_def
      comma_selected_block_then_def comma_selected_block_repeat_def)

lemma comma_selected_block_target_valid:
  assumes "comma_selected_return_certified A"
  shows "comma_boundary_valid (selected_block_target A)"
  using assms
  by (induction rule: comma_selected_return_certified.induct)
    (auto simp: comma_selected_block_empty_def comma_selected_block_leaf_def
      comma_selected_block_then_def comma_selected_block_repeat_def)

text \<open>This endpoint observation is the application interface for a
composed block. Its proof composes cached source/target/count/displacement
summaries. It does not flatten the decision tree. Literal terms are a separate
demand and may descend through the observation below.\<close>

lemma comma_selected_block_return_path:
  assumes "comma_selected_return_certified A"
  shows "comma_return_path (selected_block_count A)
    (selected_block_source A) (selected_block_target A) (selected_block_delta A)"
  using assms
proof (induction rule: comma_selected_return_certified.induct)
  case (empty q)
  then show ?case
    by (simp add: comma_selected_block_empty_def comma_return_path.empty)
next
  case (leaf q a d target choice)
  have target_valid: "comma_boundary_valid target" using leaf.hyps(7) .
  have base: "comma_return_path 1 q target d"
  proof (cases choice)
    case False
    let ?child = "(Comma_N,a,(snd (snd q)+d) mod 924)"
    have member: "?child \<in>
        set (comma_total_children q)"
      using leaf.hyps(4) by simp
    have target_eq: "target=?child"
      using leaf.hyps(5) False by simp
    have child_valid: "comma_boundary_valid ?child"
      using target_valid target_eq by simp
    have tail: "comma_return_path 0 ?child ?child 0"
      by (rule comma_return_path.empty[OF child_valid])
    have step: "comma_return_path 1 q ?child d"
      using comma_return_path.step[OF leaf.hyps(1,2,3) member tail] by simp
    show ?thesis using step target_eq by simp
  next
    case True
    let ?child = "(Comma_Z,a,(snd (snd q)+d) mod 924)"
    have member: "?child \<in>
        set (comma_total_children q)"
      using leaf.hyps(4) by simp
    have target_eq: "target=?child"
      using leaf.hyps(5) True by simp
    have child_valid: "comma_boundary_valid ?child"
      using target_valid target_eq by simp
    have tail: "comma_return_path 0 ?child ?child 0"
      by (rule comma_return_path.empty[OF child_valid])
    have step: "comma_return_path 1 q ?child d"
      using comma_return_path.step[OF leaf.hyps(1,2,3) member tail] by simp
    show ?thesis using step target_eq by simp
  qed
  then show ?case
    by (simp add: comma_selected_block_leaf_def)
next
  case (compose A B)
  have joined:
    "comma_return_path (selected_block_count A+selected_block_count B)
      (selected_block_source A) (selected_block_target B)
      (selected_block_delta A+selected_block_delta B)"
  proof -
    have right_path:
      "comma_return_path (selected_block_count B)
        (selected_block_target A) (selected_block_target B)
        (selected_block_delta B)"
      using compose.IH(2) compose.hyps(3) by simp
    show ?thesis
      by (rule comma_return_path_append[OF compose.IH(1) right_path])
  qed
  then show ?case by (simp add: comma_selected_block_then_def)
next
  case (iterate A k)
  have loop_path:
    "comma_return_path (selected_block_count A)
      (selected_block_source A) (selected_block_source A)
      (selected_block_delta A)"
    using iterate.IH iterate.hyps(2) by simp
  have repeated:
    "comma_return_path (k*selected_block_count A)
      (selected_block_source A) (selected_block_source A)
      (k*selected_block_delta A)"
    by (rule comma_return_path_repeat[OF loop_path])
  then show ?case using iterate.hyps(2)
    by (simp add: comma_selected_block_repeat_def)
qed

text \<open>Only this observation turns the compact decision tree into the
legacy list-shaped safety relation. Builders should retain the block tree and
request this view only when a consumer needs an explicit choice trace.\<close>

lemma comma_selected_block_choice_path:
  assumes "comma_selected_return_certified A"
  shows "comma_earliest_return_path
    (comma_selected_choice_word (selected_block_choices A))
    (selected_block_count A) (selected_block_source A)
    (selected_block_target A) (selected_block_delta A)"
  using assms
proof (induction rule: comma_selected_return_certified.induct)
  case (empty q)
  then show ?case
    by (simp add: comma_selected_block_empty_def comma_selected_choice_word.simps
      comma_earliest_return_path.empty)
next
  case (leaf q a d target choice)
  have selected_path:
    "comma_earliest_return_path [choice] 1 q target d"
  proof (cases choice)
    case False
    let ?child = "(Comma_N,a,(snd (snd q)+d) mod 924)"
    have member: "?child \<in>
        set (comma_total_children q)"
      using leaf.hyps(4) by simp
    have target_eq: "target=?child"
      using leaf.hyps(5) False by simp
    have valid_target: "comma_boundary_valid ?child"
      using leaf.hyps(7) target_eq by simp
    have tail: "comma_earliest_return_path [] 0
        ?child ?child 0"
      by (rule comma_earliest_return_path.empty[OF valid_target])
    have step: "comma_earliest_return_path [False] 1 q ?child d"
      using comma_earliest_return_path.choose_N
        [OF leaf.hyps(1,2,3) member tail] by simp
    show ?thesis using step target_eq False by simp
  next
    case True
    let ?child = "(Comma_Z,a,(snd (snd q)+d) mod 924)"
    have member: "?child \<in>
        set (comma_total_children q)"
      using leaf.hyps(4) by simp
    have target_eq: "target=?child"
      using leaf.hyps(5) True by simp
    have valid_target: "comma_boundary_valid ?child"
      using leaf.hyps(7) target_eq by simp
    have near_terminates:
      "comma_boundary_terminates (Comma_N,a,(snd (snd q)+d) mod 924)"
      using leaf.hyps(8) True by simp
    have tail: "comma_earliest_return_path [] 0
        ?child ?child 0"
      by (rule comma_earliest_return_path.empty[OF valid_target])
    have step: "comma_earliest_return_path [True] 1 q ?child d"
      using comma_earliest_return_path.choose_Z
        [OF leaf.hyps(1,2,3) member near_terminates tail] by simp
    show ?thesis using step target_eq True by simp
  qed
  then show ?case by (simp add: comma_selected_block_leaf_def)
next
  case (compose A B)
  have joined:
    "comma_earliest_return_path
      (comma_selected_choice_word (selected_block_choices A) @
       comma_selected_choice_word (selected_block_choices B))
      (selected_block_count A+selected_block_count B)
      (selected_block_source A) (selected_block_target B)
      (selected_block_delta A+selected_block_delta B)"
  proof -
    have right_path:
      "comma_earliest_return_path
        (comma_selected_choice_word (selected_block_choices B))
        (selected_block_count B) (selected_block_target A)
        (selected_block_target B) (selected_block_delta B)"
      using compose.IH(2) compose.hyps(3) by simp
    show ?thesis
      by (rule comma_earliest_return_path_append[OF compose.IH(1) right_path])
  qed
  then show ?case by (simp add: comma_selected_block_then_def)
next
  case (iterate A k)
  have loop_path:
    "comma_earliest_return_path
      (comma_selected_choice_word (selected_block_choices A))
      (selected_block_count A) (selected_block_source A)
      (selected_block_source A) (selected_block_delta A)"
    using iterate.IH iterate.hyps(2) by simp
  have repeated:
    "comma_earliest_return_path
      (concat (replicate k (comma_selected_choice_word
        (selected_block_choices A))))
      (k*selected_block_count A) (selected_block_source A)
      (selected_block_source A) (k*selected_block_delta A)"
    by (rule comma_earliest_return_path_repeat[OF loop_path])
  then show ?case using iterate.hyps(2)
    by (simp add: comma_selected_block_repeat_def)
qed

corollary comma_selected_block_literal_application:
  assumes block: "comma_selected_return_certified A"
    and exponent: "5\<le>p"
    and phase: "p mod 924=snd (snd (selected_block_source A))"
  shows "\<exists>w\<ge>selected_block_count A. comma_literal_path w
    (comma_boundary_value (selected_block_source A) p)
    (comma_boundary_value (selected_block_target A)
      (p+selected_block_delta A))"
  using comma_return_path_literal[OF comma_selected_block_return_path[OF block]
      exponent phase] .

lemma comma_selected_block_square_summary:
  "selected_block_source (comma_selected_block_square A)=selected_block_source A"
  "selected_block_target (comma_selected_block_square A)=selected_block_target A"
  "selected_block_count (comma_selected_block_square A)=2*selected_block_count A"
  "selected_block_delta (comma_selected_block_square A)=2*selected_block_delta A"
  by (simp_all add: comma_selected_block_square_def comma_selected_block_repeat_def)

text \<open>These are intentionally explicit one-step projections for the ML
builder. Use them by theorem application/rewriting at the root record only;
adding them to the global simp set would recursively inspect a completed
choice tree and defeat structural sharing.\<close>

lemma comma_selected_block_choice_tree_then:
  "selected_block_choices (comma_selected_block_then A B) =
    Comma_Selected_Choice_Join (selected_block_choices A)
      (selected_block_choices B)"
  by (simp add: comma_selected_block_then_def)

lemma comma_selected_block_choice_tree_repeat:
  "selected_block_choices (comma_selected_block_repeat k A) =
    Comma_Selected_Choice_Repeat (selected_block_choices A) k"
  by (simp add: comma_selected_block_repeat_def)

lemma comma_selected_block_choice_tree_square:
  "selected_block_choices (comma_selected_block_square A) =
    Comma_Selected_Choice_Repeat (selected_block_choices A) 2"
  by (simp add: comma_selected_block_square_def
      comma_selected_block_repeat_def)

lemma comma_selected_block_view_then:
  "comma_selected_block_view (comma_selected_block_then A B) =
    (selected_block_source A, selected_block_target B,
     selected_block_count A+selected_block_count B,
     selected_block_delta A+selected_block_delta B,
     Comma_Selected_Choice_Join
       (selected_block_choices A) (selected_block_choices B))"
  by (simp add: comma_selected_block_view_def comma_selected_block_then_def)

lemma comma_selected_block_view_empty:
  "comma_selected_block_view (comma_selected_block_empty q) =
    (q, q, 0, 0, Comma_Selected_Choice_Empty)"
  by (simp add: comma_selected_block_view_def comma_selected_block_empty_def)

lemma comma_selected_block_view_leaf:
  "comma_selected_block_view (comma_selected_block_leaf choice q target d) =
    (q, target, 1, d, Comma_Selected_Choice_Leaf choice)"
  by (simp add: comma_selected_block_view_def comma_selected_block_leaf_def)

lemma comma_selected_block_view_repeat:
  "comma_selected_block_view (comma_selected_block_repeat k A) =
    (selected_block_source A, selected_block_target A,
     k*selected_block_count A, k*selected_block_delta A,
     Comma_Selected_Choice_Repeat (selected_block_choices A) k)"
  by (simp add: comma_selected_block_view_def comma_selected_block_repeat_def)

lemma comma_selected_block_view_square:
  "comma_selected_block_view (comma_selected_block_square A) =
    (selected_block_source A, selected_block_target A,
     2*selected_block_count A, 2*selected_block_delta A,
     Comma_Selected_Choice_Repeat (selected_block_choices A) 2)"
  by (simp add: comma_selected_block_view_def comma_selected_block_square_def
      comma_selected_block_repeat_def)

text \<open>Optional local simplifier congruences for consumers that normalize a
block view. Supplying these with `cong:` keeps the child tree opaque; they are
not installed globally and are not rewrite rules.\<close>

lemma comma_selected_choice_join_opaque_cong:
  "Comma_Selected_Choice_Join A B = Comma_Selected_Choice_Join A B"
  by (rule refl)

lemma comma_selected_choice_repeat_opaque_cong:
  "Comma_Selected_Choice_Repeat A k = Comma_Selected_Choice_Repeat A k"
  by (rule refl)

lemma comma_selected_block_then_summary:
  "selected_block_source (comma_selected_block_then A B)=selected_block_source A"
  "selected_block_target (comma_selected_block_then A B)=selected_block_target B"
  "selected_block_count (comma_selected_block_then A B)=
    selected_block_count A+selected_block_count B"
  "selected_block_delta (comma_selected_block_then A B)=
    selected_block_delta A+selected_block_delta B"
  by (simp_all add: comma_selected_block_then_def)

lemma comma_selected_block_choice_word_then:
  "comma_selected_choice_word (selected_block_choices
      (comma_selected_block_then A B)) =
    comma_selected_choice_word (selected_block_choices A) @
      comma_selected_choice_word (selected_block_choices B)"
  by (simp add: comma_selected_block_then_def)

lemma comma_selected_block_choice_word_repeat:
  "comma_selected_choice_word (selected_block_choices
      (comma_selected_block_repeat k A)) =
    concat (replicate k (comma_selected_choice_word (selected_block_choices A)))"
  by (simp add: comma_selected_block_repeat_def)

ML_file "selected_block_builder.ML"

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_selected_block_leaf_certified
      comma_selected_block_then_certified comma_selected_block_repeat_certified
      comma_selected_block_square_certified comma_selected_block_return_path
      comma_selected_block_choice_path comma_selected_block_literal_application
      comma_selected_block_choice_tree_then
      comma_selected_block_choice_tree_repeat
      comma_selected_block_choice_tree_square comma_selected_block_view_then
      comma_selected_block_view_empty comma_selected_block_view_leaf
      comma_selected_block_view_repeat comma_selected_block_view_square
      comma_selected_block_N_certified comma_selected_block_Z_certified
      comma_selected_choice_join_opaque_cong
      comma_selected_choice_repeat_opaque_cong})
    then () else error "Selected comma block certificates use an oracle";
\<close>
end
