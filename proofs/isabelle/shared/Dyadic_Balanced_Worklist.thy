theory Dyadic_Balanced_Worklist
  imports Dyadic_Source_Lift
begin

datatype 'effect frame = Need_Left nat nat | Need_Right nat nat 'effect
datatype 'effect phase = Descend nat nat | Return 'effect | Complete 'effect
datatype 'effect machine = Machine "'effect phase" "'effect frame list"
  "((nat * nat) * 'effect) list"

locale dyadic_balanced_worklist =
  fixes leaf :: "nat \<Rightarrow> nat \<Rightarrow> 'effect"
    and transport :: "'effect \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"
    and join :: "nat \<Rightarrow> nat \<Rightarrow> 'effect \<Rightarrow> 'effect \<Rightarrow> 'effect"
    and cache_admit :: "nat \<Rightarrow> nat \<Rightarrow> 'effect \<Rightarrow>
      ((nat * nat) * 'effect) list \<Rightarrow> bool"
begin

text \<open>This is the recursive mathematical specification.  The worklist
below never calls it: it uses only leaf, transport and join.\<close>

function balanced_spec :: "nat \<Rightarrow> nat \<Rightarrow> 'effect" where
  "balanced_spec n r =
     (if n \<le> 64 then leaf n r
      else let l = balanced_left_span n;
               left = balanced_spec l (r mod 2^l);
               right_width = n-l;
               right_residue = transport left r right_width;
               right = balanced_spec right_width right_residue
           in join n r left right)"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>(n,r). n)")
    (auto simp: Let_def)

declare balanced_spec.simps [simp del]

lemma balanced_spec_large:
  assumes "64 < n"
  shows "balanced_spec n r =
    (let l = balanced_left_span n;
         left = balanced_spec l (r mod 2^l);
         right_width = n-l;
         right_residue = transport left r right_width;
         right = balanced_spec right_width right_residue
     in join n r left right)"
proof -
  have no: "\<not> n \<le> 64" using assms by simp
  show ?thesis by (subst balanced_spec.simps) (simp only: no if_False)
qed

definition remember :: "nat \<Rightarrow> nat \<Rightarrow> 'effect \<Rightarrow>
  ((nat * nat) * 'effect) list \<Rightarrow> ((nat * nat) * 'effect) list" where
  "remember n r outcome memo =
    (if map_of memo (n,r) \<noteq> None then memo
     else let after_eviction = take 63 memo in
       if cache_admit n r outcome after_eviction then
         ((n,r),outcome) # after_eviction
       else after_eviction)"

text \<open>Memo entries are scoped to one invocation of this locale: its
leaf, transport and join functions are the pinned law and retention mode.
Eviction removes entries only.  It never changes an effect in flight.\<close>

definition memo_valid :: "((nat * nat) * 'effect) list \<Rightarrow> bool" where
  "memo_valid memo \<longleftrightarrow>
    (\<forall>key outcome. (key,outcome) \<in> set memo \<longrightarrow>
      outcome = balanced_spec (fst key) (snd key))"

lemma memo_lookup_valid:
  assumes "memo_valid memo" "map_of memo (n,r) = Some outcome"
  shows "outcome = balanced_spec n r"
  using assms by (auto simp: memo_valid_def dest: map_of_SomeD)

lemma remember_valid:
  assumes "memo_valid memo" "outcome = balanced_spec n r"
  shows "memo_valid (remember n r outcome memo)"
  using assms unfolding memo_valid_def remember_def
  by (auto simp: Let_def split: if_splits dest: in_set_takeD)

lemma remember_bounded [simp]:
  assumes "length memo \<le> 64"
  shows "length (remember n r outcome memo) \<le> 64"
  using assms by (auto simp: remember_def Let_def split: if_splits)

lemma memo_valid_eviction:
  assumes "memo_valid memo" "set smaller \<subseteq> set memo"
  shows "memo_valid smaller"
  using assms by (auto simp: memo_valid_def)

fun machine_step :: "'effect machine \<Rightarrow> 'effect machine" where
  "machine_step (Machine (Descend n r) frames memo) =
    (case map_of memo (n,r) of
      Some outcome \<Rightarrow> Machine (Return outcome) frames memo
    | None \<Rightarrow>
        if n \<le> 64 then
          (let outcome = leaf n r in
             Machine (Return outcome) frames
               (remember n r outcome memo))
        else
          Machine (Descend (balanced_left_span n)
            (r mod 2^(balanced_left_span n)))
            (Need_Left n r # frames) memo)"
| "machine_step (Machine (Return outcome) [] memo) =
     Machine (Complete outcome) [] memo"
| "machine_step (Machine (Return outcome) (Need_Left n r # frames) memo) =
     Machine (Descend (n-balanced_left_span n)
       (transport outcome r (n-balanced_left_span n)))
       (Need_Right n r outcome # frames) memo"
| "machine_step (Machine (Return outcome) (Need_Right n r left # frames) memo) =
     (let result = join n r left outcome in
        Machine (Return result) frames
          (remember n r result memo))"
| "machine_step (Machine (Complete outcome) frames memo) =
     Machine (Complete outcome) frames memo"

declare Let_def [simp]

fun after_frames :: "'effect frame list \<Rightarrow> 'effect \<Rightarrow> 'effect" where
  "after_frames [] outcome = outcome"
| "after_frames (Need_Left n r # frames) left =
     after_frames frames
       (join n r left
         (balanced_spec (n-balanced_left_span n)
           (transport left r (n-balanced_left_span n))))"
| "after_frames (Need_Right n r left # frames) right =
     after_frames frames (join n r left right)"

fun phase_value :: "'effect phase \<Rightarrow> 'effect" where
  "phase_value (Descend n r) = balanced_spec n r"
| "phase_value (Return outcome) = outcome"
| "phase_value (Complete outcome) = outcome"

definition machine_value :: "'effect machine \<Rightarrow> 'effect" where
  "machine_value machine =
    (case machine of Machine phase frames memo \<Rightarrow>
       after_frames frames (phase_value phase))"

text \<open>A frame records which recursive call is active.  The right frame
stores the complete left effect, not an endpoint word or a supplied branch
itinerary.  The predicate is used only in the proof.\<close>

fun frame_valid :: "'effect frame \<Rightarrow> bool" where
  "frame_valid (Need_Left n r) = (64 < n)"
| "frame_valid (Need_Right n r left) =
     (64 < n \<and> left = balanced_spec (balanced_left_span n)
       (r mod 2^(balanced_left_span n)))"

fun frame_target :: "'effect frame \<Rightarrow> nat * nat" where
  "frame_target (Need_Left n r) = (n,r)"
| "frame_target (Need_Right n r left) = (n,r)"

fun frame_child :: "'effect frame \<Rightarrow> nat * nat" where
  "frame_child (Need_Left n r) =
     (balanced_left_span n, r mod 2^(balanced_left_span n))"
| "frame_child (Need_Right n r left) =
     (n-balanced_left_span n,
      transport left r (n-balanced_left_span n))"

fun frame_chain :: "nat \<Rightarrow> nat \<Rightarrow> 'effect frame list \<Rightarrow> bool" where
  "frame_chain root_n root_r [] = True"
| "frame_chain root_n root_r [frame] =
     (frame_target frame = (root_n,root_r))"
| "frame_chain root_n root_r (inner # outer # rest) =
     (frame_target inner = frame_child outer \<and>
      frame_chain root_n root_r (outer # rest))"

fun top_valid :: "nat \<Rightarrow> nat \<Rightarrow> 'effect phase \<Rightarrow>
  'effect frame list \<Rightarrow> bool" where
  "top_valid root_n root_r phase [] =
     (case phase of Descend n r \<Rightarrow> n=root_n \<and> r=root_r
       | Return outcome \<Rightarrow> outcome=balanced_spec root_n root_r
       | Complete outcome \<Rightarrow> outcome=balanced_spec root_n root_r)"
| "top_valid root_n root_r phase (Need_Left n r # frames) =
     (case phase of Descend span source \<Rightarrow>
          span=balanced_left_span n \<and> source=r mod 2^span
       | Return outcome \<Rightarrow>
          outcome=balanced_spec (balanced_left_span n)
            (r mod 2^(balanced_left_span n))
       | Complete outcome \<Rightarrow> False)"
| "top_valid root_n root_r phase (Need_Right n r left # frames) =
     (case phase of Descend span source \<Rightarrow>
          span=n-balanced_left_span n \<and>
          source=transport left r span
       | Return outcome \<Rightarrow>
          outcome=balanced_spec (n-balanced_left_span n)
            (transport left r (n-balanced_left_span n))
       | Complete outcome \<Rightarrow> False)"

definition machine_invariant :: "nat \<Rightarrow> nat \<Rightarrow> 'effect machine \<Rightarrow> bool" where
  "machine_invariant root_n root_r machine \<longleftrightarrow>
    (case machine of Machine phase frames memo \<Rightarrow>
      memo_valid memo \<and> list_all frame_valid frames \<and>
      frame_chain root_n root_r frames \<and>
      top_valid root_n root_r phase frames \<and>
      machine_value machine = balanced_spec root_n root_r)"

definition initial_machine :: "nat \<Rightarrow> nat \<Rightarrow> 'effect machine" where
  "initial_machine n r = Machine (Descend n r) [] []"

lemma initial_machine_invariant [simp]:
  "machine_invariant n r (initial_machine n r)"
  by (simp add: machine_invariant_def initial_machine_def
    machine_value_def memo_valid_def)

lemma machine_step_preserves_value:
  assumes valid: "memo_valid memo"
  shows "machine_value (machine_step (Machine phase frames memo)) =
    machine_value (Machine phase frames memo)"
proof (cases phase)
  case (Descend n r)
  show ?thesis
  proof (cases "map_of memo (n,r)")
    case (Some outcome)
    then have "outcome = balanced_spec n r"
      by (rule memo_lookup_valid[OF valid])
    with Descend Some show ?thesis
      by (simp add: machine_value_def)
  next
    case None
    show ?thesis
    proof (cases "n \<le> 64")
      case True
      with Descend None show ?thesis
        by (simp add: machine_value_def balanced_spec.simps)
    next
      case False
      then have large: "64 < n" by simp
      with Descend None show ?thesis
        by (simp add: machine_value_def
          balanced_spec_large[OF large] Let_def)
    qed
  qed
next
  case (Return outcome)
  show ?thesis
  proof (cases frames)
    case Nil
    with Return show ?thesis by (simp add: machine_value_def)
  next
    case (Cons head tail)
    then show ?thesis
      using Return by (cases head) (simp_all add: machine_value_def)
  qed
next
  case (Complete outcome)
  then show ?thesis by (simp add: machine_value_def)
qed

lemma right_frame_join_correct:
  assumes frame: "frame_valid (Need_Right n r left)"
    and top: "top_valid root_n root_r (Return right)
      (Need_Right n r left # frames)"
  shows "join n r left right = balanced_spec n r"
  using frame top
  by (simp add: balanced_spec_large Let_def)

lemma frame_chain_push:
  assumes chain: "frame_chain root_n root_r frames"
    and aligned: "top_valid root_n root_r (Descend n r) frames"
  shows "frame_chain root_n root_r (Need_Left n r # frames)"
proof (cases frames)
  case Nil
  with chain aligned show ?thesis by simp
next
  case (Cons head tail)
  then show ?thesis
    using chain aligned by (cases head) simp_all
qed

lemma frame_chain_pop:
  assumes chain: "frame_chain root_n root_r (inner # frames)"
  shows "frame_chain root_n root_r frames"
  using chain by (cases frames rule: list.exhaust) auto

lemma frame_chain_replace_top:
  assumes chain: "frame_chain root_n root_r (old # rest)"
    and same: "frame_target replacement = frame_target old"
  shows "frame_chain root_n root_r (replacement # rest)"
  using chain same by (cases rest rule: list.exhaust) simp_all

lemma top_valid_after_pop:
  assumes chain: "frame_chain root_n root_r (inner # frames)"
    and target: "outcome = balanced_spec (fst (frame_target inner))
        (snd (frame_target inner))"
  shows "top_valid root_n root_r (Return outcome) frames"
proof (cases frames)
  case Nil
  with chain target show ?thesis by (cases inner) simp_all
next
  case (Cons head tail)
  then show ?thesis
    using chain target by (cases head; cases inner) simp_all
qed

lemma top_valid_descend_return:
  assumes top: "top_valid root_n root_r (Descend n r) frames"
    and result: "outcome = balanced_spec n r"
  shows "top_valid root_n root_r (Return outcome) frames"
proof (cases frames)
  case Nil
  with top result show ?thesis by simp
next
  case (Cons head tail)
  with top result show ?thesis
    by (cases head) simp_all
qed

theorem machine_step_preserves_invariant:
  assumes "machine_invariant root_n root_r machine"
  shows "machine_invariant root_n root_r (machine_step machine)"
proof -
  obtain phase frames memo where machine: "machine = Machine phase frames memo"
    by (cases machine) auto
  have memo: "memo_valid memo" and frames: "list_all frame_valid frames"
    and chain: "frame_chain root_n root_r frames"
    and top: "top_valid root_n root_r phase frames"
    and outcome: "machine_value machine = balanced_spec root_n root_r"
    using assms by (auto simp: machine machine_invariant_def)
  have outcome': "machine_value (machine_step machine) = balanced_spec root_n root_r"
    using outcome machine_step_preserves_value[OF memo, of phase frames]
    by (simp add: machine)
  show ?thesis
  proof (cases phase)
    case (Descend n r)
    show ?thesis
    proof (cases "map_of memo (n,r)")
      case (Some v)
      then have "v = balanced_spec n r"
        by (rule memo_lookup_valid[OF memo])
      have oldtop: "top_valid root_n root_r (Descend n r) frames"
        using top Descend by simp
      have newtop: "top_valid root_n root_r (Return v) frames"
        by (rule top_valid_descend_return[OF oldtop \<open>v = balanced_spec n r\<close>])
      with memo frames chain outcome' Descend Some show ?thesis
        by (simp add: machine machine_invariant_def)
    next
      case None
      show ?thesis
      proof (cases "n \<le> 64")
        case True
        have result: "leaf n r = balanced_spec n r"
          using True by (simp add: balanced_spec.simps)
        have oldtop: "top_valid root_n root_r (Descend n r) frames"
          using top Descend by simp
        have newtop: "top_valid root_n root_r (Return (leaf n r)) frames"
          by (rule top_valid_descend_return[OF oldtop result])
        have newmemo: "memo_valid (remember n r (leaf n r) memo)"
          by (rule remember_valid[OF memo result])
        with frames chain outcome' Descend None True newtop show ?thesis
          by (simp add: machine machine_invariant_def)
      next
        case False
        then have large: "64 < n" by simp
        have pushed: "frame_chain root_n root_r
          (Need_Left n r # frames)"
          by (rule frame_chain_push[OF chain]) (use top Descend in simp)
        with memo frames outcome' Descend None large show ?thesis
          by (simp add: machine machine_invariant_def)
      qed
    qed
  next
    case (Return result)
    show ?thesis
    proof (cases frames)
      case Nil
      with memo frames chain top outcome' Return show ?thesis
        by (simp add: machine machine_invariant_def)
    next
      case (Cons frame rest)
      show ?thesis
      proof (cases frame)
        case (Need_Left n r)
        have left_correct: "result = balanced_spec (balanced_left_span n)
          (r mod 2^(balanced_left_span n))"
          using top Return Cons Need_Left by simp
        have large: "64 < n" using frames Cons Need_Left by simp
        have replaced: "frame_chain root_n root_r
          (Need_Right n r result # rest)"
          using chain Cons Need_Left
          by (auto intro: frame_chain_replace_top)
        with memo frames outcome' Return Cons Need_Left
          left_correct large show ?thesis
          by (simp add: machine machine_invariant_def)
      next
        case (Need_Right n r left)
        have correct: "join n r left result = balanced_spec n r"
          using frames top Cons Need_Right Return
          by (auto intro: right_frame_join_correct)
        have oldchain: "frame_chain root_n root_r
          (Need_Right n r left # rest)"
          using chain Cons Need_Right by simp
        have rest_chain: "frame_chain root_n root_r rest"
          by (rule frame_chain_pop[OF oldchain])
        have rest_top: "top_valid root_n root_r
          (Return (join n r left result)) rest"
          by (rule top_valid_after_pop[OF oldchain])
            (simp add: correct)
        have rest_memo: "memo_valid
          (remember n r (join n r left result) memo)"
          by (rule remember_valid[OF memo correct])
        with rest_chain rest_top frames outcome' Cons Need_Right Return
          show ?thesis
          by (simp add: machine machine_invariant_def)
      qed
    qed
  next
    case (Complete result)
    with memo frames chain top outcome' show ?thesis
      by (simp add: machine machine_invariant_def)
  qed
qed

fun machine_steps :: "nat \<Rightarrow> 'effect machine \<Rightarrow> 'effect machine" where
  "machine_steps 0 machine = machine"
| "machine_steps (Suc fuel) machine =
    machine_steps fuel (machine_step machine)"

text \<open>The executable runner stops as soon as Complete is reached.
The static fuel is a totality certificate, not extra runtime iterations.\<close>

fun machine_run :: "nat \<Rightarrow> 'effect machine \<Rightarrow> 'effect machine" where
  "machine_run 0 machine = machine"
| "machine_run (Suc fuel) machine =
    (case machine of Machine phase frames memo \<Rightarrow>
      (case phase of Complete outcome \<Rightarrow> machine
       | _ \<Rightarrow> machine_run fuel (machine_step machine)))"

lemma machine_steps_complete_any [simp]:
  "machine_steps fuel (Machine (Complete outcome) frames memo) =
    Machine (Complete outcome) frames memo"
  by (induction fuel) simp_all

lemma machine_run_matches_steps:
  "machine_run fuel machine = machine_steps fuel machine"
proof (induction fuel arbitrary: machine)
  case 0
  then show ?case by simp
next
  case (Suc fuel)
  show ?case
  proof (cases machine)
    case (Machine phase frames memo)
    then show ?thesis
      by (cases phase) (simp_all add: Suc.IH)
  qed
qed

corollary machine_steps_preserve_invariant:
  "machine_invariant n r machine \<Longrightarrow>
    machine_invariant n r (machine_steps fuel machine)"
  by (induction fuel arbitrary: machine)
    (auto intro: machine_step_preserves_invariant)

corollary completed_machine_correct:
  assumes "machine_steps fuel (initial_machine n r) =
    Machine (Complete outcome) [] memo"
  shows "outcome = balanced_spec n r" "memo_valid memo"
proof -
  have initial: "machine_invariant n r (initial_machine n r)" by simp
  have final: "machine_invariant n r
    (machine_steps fuel (initial_machine n r))"
    by (rule machine_steps_preserve_invariant[OF initial])
  have "machine_invariant n r (Machine (Complete outcome) [] memo)"
    using final assms by simp
  then show "outcome = balanced_spec n r" "memo_valid memo"
    by (simp_all add: machine_invariant_def machine_value_def)
qed

text \<open>The following potential counts newly visited recursive nodes.
A memo hit decreases the potential without constructing a node.  It is a
constructor operation bound, not a claim that big-integer arithmetic is
constant cost.  The Python ledger separately charges operand bit lengths.\<close>

function tree_nodes :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "tree_nodes n r =
    (if n \<le> 64 then 1
     else let l = balanced_left_span n;
              left = balanced_spec l (r mod 2^l)
          in 1 + tree_nodes l (r mod 2^l) +
             tree_nodes (n-l) (transport left r (n-l)))"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>(n,r). n)")
    (auto simp: Let_def)

declare tree_nodes.simps [simp del]

lemma tree_nodes_large:
  assumes "64 < n"
  shows "tree_nodes n r =
    (let l = balanced_left_span n;
         left = balanced_spec l (r mod 2^l)
     in 1 + tree_nodes l (r mod 2^l) +
        tree_nodes (n-l) (transport left r (n-l)))"
proof -
  have no: "\<not> n \<le> 64" using assms by simp
  show ?thesis by (subst tree_nodes.simps) (simp only: no if_False)
qed

lemma tree_nodes_positive [simp]: "0 < tree_nodes n r"
proof (cases "n \<le> 64")
  case True
  then show ?thesis by (subst tree_nodes.simps) simp
next
  case False
  then show ?thesis by (simp add: tree_nodes_large Let_def)
qed

lemma tree_nodes_linear_bound:
  "tree_nodes n r \<le> 2 * max 1 n - 1"
proof (induction n arbitrary: r rule: less_induct)
  case (less n)
  show ?case
  proof (cases "n \<le> 64")
    case True
    then show ?thesis
      by (simp add: tree_nodes.simps)
  next
    case False
    let ?l = "balanced_left_span n"
    let ?right = "n - ?l"
    let ?low = "r mod 2^?l"
    let ?next = "transport (balanced_spec ?l ?low) r ?right"
    have positive: "0 < ?l" "0 < ?right"
      using balanced_left_span_bounds[of n] False by auto
    have bounds:
      "tree_nodes ?l ?low \<le> 2 * ?l - 1"
      "tree_nodes ?right ?next \<le> 2 * ?right - 1"
      using less.IH[of ?l ?low] less.IH[of ?right ?next]
        balanced_left_span_bounds[of n] False positive by auto
    have "tree_nodes n r = 1 + tree_nodes ?l ?low +
      tree_nodes ?right ?next"
      using False by (simp add: tree_nodes_large Let_def)
    also have "\<dots> \<le> 2*n - 1"
      using bounds positive balanced_left_span_bounds[of n]
      by (simp add: False)
    finally show ?thesis using False by simp
  qed
qed

fun frame_work :: "'effect frame \<Rightarrow> nat" where
  "frame_work (Need_Left n r) =
     2 + 3 * tree_nodes (n-balanced_left_span n)
       (transport (balanced_spec (balanced_left_span n)
         (r mod 2^(balanced_left_span n))) r
         (n-balanced_left_span n))"
| "frame_work (Need_Right n r left) = 1"

fun phase_work :: "'effect phase \<Rightarrow> nat" where
  "phase_work (Descend n r) = 3 * tree_nodes n r"
| "phase_work (Return outcome) = 1"
| "phase_work (Complete outcome) = 0"

definition remaining_work :: "'effect machine \<Rightarrow> nat" where
  "remaining_work machine =
     (case machine of Machine phase frames memo \<Rightarrow>
       phase_work phase + sum_list (map frame_work frames))"

lemma frame_work_positive [simp]: "0 < frame_work frame"
  by (cases frame) simp_all

lemma stack_within_remaining_work:
  "length frames \<le> remaining_work (Machine phase frames memo)"
proof (induction frames)
  case Nil
  then show ?case by (simp add: remaining_work_def)
next
  case (Cons head tail)
  have positive: "1 \<le> frame_work head"
    using frame_work_positive[of head] by arith
  have "length tail \<le> phase_work phase +
    sum_list (map frame_work tail)"
    using Cons.IH by (simp add: remaining_work_def)
  then show ?case using positive
    by (simp add: remaining_work_def; linarith)
qed

lemma remaining_work_complete_iff:
  assumes "machine_invariant root_n root_r machine"
  shows "remaining_work machine = 0 \<longleftrightarrow>
    (\<exists>outcome memo. machine = Machine (Complete outcome) [] memo)"
proof (cases machine)
  case (Machine phase frames memo)
  have top: "top_valid root_n root_r phase frames"
    using assms by (simp add: Machine machine_invariant_def)
  show ?thesis
  proof (cases phase)
    case (Descend n r)
    with Machine show ?thesis
      by (simp add: remaining_work_def)
  next
    case (Return outcome)
    with Machine show ?thesis
      by (simp add: remaining_work_def)
  next
    case (Complete outcome)
    show ?thesis
    proof (cases frames)
      case Nil
      with Machine Complete show ?thesis
        by (simp add: remaining_work_def)
    next
      case (Cons head tail)
      with top Complete have False by (cases head) simp_all
      then show ?thesis by simp
    qed
  qed
qed

lemma machine_step_decreases_work:
  assumes invariant: "machine_invariant root_n root_r machine"
    and unfinished: "\<not> (\<exists>outcome memo.
      machine = Machine (Complete outcome) [] memo)"
  shows "remaining_work (machine_step machine) < remaining_work machine"
proof -
  obtain phase frames memo where machine: "machine = Machine phase frames memo"
    by (cases machine) auto
  have valid: "memo_valid memo" and top: "top_valid root_n root_r phase frames"
    and frame: "list_all frame_valid frames"
    using invariant by (auto simp: machine machine_invariant_def)
  show ?thesis
  proof (cases phase)
    case (Descend n r)
    show ?thesis
    proof (cases "map_of memo (n,r)")
      case (Some outcome)
      have positive: "0 < tree_nodes n r" by simp
      with Descend show ?thesis
        using Some by (simp add: machine remaining_work_def; arith)
    next
      case None
      show ?thesis
      proof (cases "n \<le> 64")
        case True
        with Descend None show ?thesis
          by (simp add: machine remaining_work_def tree_nodes.simps)
      next
        case False
        with Descend None show ?thesis
          by (simp add: machine remaining_work_def
            tree_nodes_large Let_def)
      qed
    qed
  next
    case (Return outcome)
    show ?thesis
    proof (cases frames)
      case Nil
      with Return show ?thesis by (simp add: machine remaining_work_def)
    next
      case (Cons head tail)
      show ?thesis
      proof (cases head)
        case (Need_Left n r)
        with Cons Return top show ?thesis
          by (simp add: machine remaining_work_def)
      next
        case (Need_Right n r left)
        with Cons Return show ?thesis
          by (simp add: machine remaining_work_def)
      qed
    qed
  next
    case (Complete outcome)
    show ?thesis
    proof (cases frames)
      case Nil
      with Complete unfinished machine show ?thesis by simp
    next
      case (Cons head tail)
      with top Complete have False by (cases head) simp_all
      then show ?thesis by simp
    qed
  qed
qed

lemma machine_steps_add:
  "machine_steps (first+second) machine =
    machine_steps second (machine_steps first machine)"
  by (induction first arbitrary: machine) simp_all

lemma machine_steps_complete [simp]:
  "machine_steps fuel (Machine (Complete outcome) [] memo) =
    Machine (Complete outcome) [] memo"
  by (induction fuel) simp_all

lemma machine_steps_work_nonincreasing:
  assumes "machine_invariant root_n root_r machine"
  shows "remaining_work (machine_steps fuel machine) \<le>
    remaining_work machine"
  using assms
proof (induction fuel arbitrary: machine)
  case 0
  then show ?case by simp
next
  case (Suc fuel)
  have next_valid: "machine_invariant root_n root_r (machine_step machine)"
    by (rule machine_step_preserves_invariant[OF Suc.prems])
  have step_bound: "remaining_work (machine_step machine) \<le>
    remaining_work machine"
  proof (cases "\<exists>outcome memo.
      machine = Machine (Complete outcome) [] memo")
    case True
    then show ?thesis by auto
  next
    case False
    then show ?thesis
      using machine_step_decreases_work[OF Suc.prems] by simp
  qed
  show ?case
    using Suc.IH[OF next_valid] step_bound by simp
qed

lemma reachable_stack_linear_bound:
  assumes "machine_steps fuel (initial_machine n r) =
    Machine phase frames memo"
  shows "length frames \<le> 6 * max 1 n"
proof -
  have "length frames \<le> remaining_work
      (machine_steps fuel (initial_machine n r))"
    using stack_within_remaining_work[of frames phase memo] assms by simp
  also have "\<dots> \<le> remaining_work (initial_machine n r)"
    by (rule machine_steps_work_nonincreasing[where root_n=n and root_r=r])
      simp
  also have "\<dots> = 3 * tree_nodes n r"
    by (simp add: initial_machine_def remaining_work_def)
  also have "\<dots> \<le> 6 * max 1 n"
    using tree_nodes_linear_bound[of n r] by arith
  finally show ?thesis .
qed

theorem machine_completes_within_work:
  assumes initial: "machine_invariant root_n root_r machine"
  shows "\<exists>outcome memo.
    machine_steps (remaining_work machine) machine =
      Machine (Complete outcome) [] memo"
proof -
  have aux: "remaining_work current = bound \<Longrightarrow>
      machine_invariant root_n root_r current \<Longrightarrow>
      \<exists>outcome memo. machine_steps bound current =
        Machine (Complete outcome) [] memo" for bound current
  proof (induction bound arbitrary: current rule: less_induct)
    case (less bound)
    show ?case
    proof (cases "\<exists>outcome memo. current = Machine (Complete outcome) [] memo")
      case True
      with less.prems show ?thesis by auto
    next
      case False
      let ?next = "machine_step current"
      have next_valid: "machine_invariant root_n root_r ?next"
        by (rule machine_step_preserves_invariant[OF less.prems(2)])
      have smaller: "remaining_work ?next < bound"
        using machine_step_decreases_work[OF less.prems(2) False] less.prems(1) by simp
      obtain outcome memo where completed_eq:
        "machine_steps (remaining_work ?next) ?next =
          Machine (Complete outcome) [] memo"
        using less.IH[OF smaller, of ?next] next_valid by auto
      obtain extra where fuel:
        "bound = Suc (remaining_work ?next + extra)"
        using smaller by (auto simp: less_iff_Suc_add)
      have "machine_steps bound current =
        machine_steps (remaining_work ?next + extra) ?next"
        by (simp add: fuel)
      also have "\<dots> = Machine (Complete outcome) [] memo"
        by (simp add: machine_steps_add completed_eq)
      finally show ?thesis by blast
    qed
  qed
  show ?thesis using aux[where bound="remaining_work machine" and current=machine] initial by simp
qed

lemma machine_step_preserves_memo_bound:
  assumes "machine = Machine phase frames memo" "length memo \<le> 64"
  obtains next_phase next_frames next_memo where
    "machine_step machine = Machine next_phase next_frames next_memo"
    "length next_memo \<le> 64"
proof -
  have shape: "\<exists>next_phase next_frames next_memo.
      machine_step machine = Machine next_phase next_frames next_memo \<and>
      length next_memo \<le> 64"
  proof (cases phase)
    case (Descend n r)
    with assms show ?thesis
      by (cases "map_of memo (n,r)"; cases "n \<le> 64")
        (auto intro: remember_bounded)
  next
    case (Return outcome)
    show ?thesis
    proof (cases frames)
      case Nil
      with assms Return show ?thesis by simp
    next
      case (Cons head tail)
      with assms Return show ?thesis
        by (cases head) (auto intro: remember_bounded)
    qed
  next
    case (Complete outcome)
    with assms show ?thesis by simp
  qed
  then obtain next_phase next_frames next_memo where
    "machine_step machine = Machine next_phase next_frames next_memo"
    "length next_memo \<le> 64" by blast
  then show thesis by (rule that)
qed

lemma machine_steps_memo_bound:
  assumes "machine = Machine phase frames memo" "length memo \<le> 64"
    and "machine_steps fuel machine = Machine final_phase final_frames final_memo"
  shows "length final_memo \<le> 64"
  using assms
proof (induction fuel arbitrary: machine phase frames memo)
  case 0
  then show ?case by simp
next
  case (Suc fuel)
  obtain next_phase next_frames next_memo where next_state:
      "machine_step machine = Machine next_phase next_frames next_memo"
      "length next_memo \<le> 64"
    by (rule machine_step_preserves_memo_bound[OF Suc.prems(1,2)])
  have tail: "machine_steps fuel
      (Machine next_phase next_frames next_memo) =
      Machine final_phase final_frames final_memo"
    using Suc.prems(3) by (simp add: next_state)
  show ?case
    by (rule Suc.IH[OF _ next_state(2) tail]) simp
qed

theorem balanced_worklist_correct_and_bounded:
  "\<exists>memo. machine_steps (3 * tree_nodes n r) (initial_machine n r) =
      Machine (Complete (balanced_spec n r)) [] memo \<and>
      memo_valid memo \<and> length memo \<le> 64"
proof -
  have remaining: "remaining_work (initial_machine n r) =
    3 * tree_nodes n r"
    by (simp add: remaining_work_def initial_machine_def)
  obtain outcome memo where completed_eq:
    "machine_steps (3 * tree_nodes n r) (initial_machine n r) =
      Machine (Complete outcome) [] memo"
    using machine_completes_within_work[of n r "initial_machine n r"]
    by (auto simp: remaining)
  have correct: "outcome = balanced_spec n r" and valid: "memo_valid memo"
    using completed_machine_correct[OF completed_eq] by auto
  have shape: "initial_machine n r = Machine (Descend n r) [] []"
    by (simp add: initial_machine_def)
  have size: "length memo \<le> 64"
    by (rule machine_steps_memo_bound[OF shape _ completed_eq]) simp
  show ?thesis using completed_eq correct valid size by auto
qed

text \<open>The public executable uses a static linear fuel bound.  Its
definition has no occurrence of balanced_spec, tree_nodes or an endpoint
oracle.  The specification is used only to prove that the fallback None
case is unreachable.\<close>

definition execute_balanced :: "nat \<Rightarrow> nat \<Rightarrow> 'effect option" where
  "execute_balanced n r =
    (case machine_run (6 * max 1 n) (initial_machine n r) of
       Machine (Complete outcome) [] memo \<Rightarrow> Some outcome
     | _ \<Rightarrow> None)"

theorem execute_balanced_correct:
  "execute_balanced n r = Some (balanced_spec n r)"
proof -
  obtain memo where completed_eq:
    "machine_steps (3 * tree_nodes n r) (initial_machine n r) =
      Machine (Complete (balanced_spec n r)) [] memo"
    using balanced_worklist_correct_and_bounded[of n r] by blast
  have fuel: "3 * tree_nodes n r \<le> 6 * max 1 n"
    using tree_nodes_linear_bound[of n r] by arith
  obtain extra where extra: "6 * max 1 n = 3 * tree_nodes n r + extra"
    using fuel by (auto simp: le_iff_add)
  have completed: "machine_steps (6 * max 1 n) (initial_machine n r) =
      Machine (Complete (balanced_spec n r)) [] memo"
    by (simp only: extra machine_steps_add completed_eq machine_steps_complete)
  show ?thesis
    by (simp only: execute_balanced_def machine_run_matches_steps completed) simp
qed

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms balanced_left_span_bounds balanced_left_span_largest
      dyadic_balanced_worklist.memo_lookup_valid
      dyadic_balanced_worklist.remember_valid
      dyadic_balanced_worklist.memo_valid_eviction
      dyadic_balanced_worklist.machine_step_preserves_invariant
      dyadic_balanced_worklist.machine_run_matches_steps
      dyadic_balanced_worklist.completed_machine_correct
      dyadic_balanced_worklist.tree_nodes_linear_bound
      dyadic_balanced_worklist.machine_step_decreases_work
      dyadic_balanced_worklist.machine_completes_within_work
      dyadic_balanced_worklist.machine_steps_memo_bound
      dyadic_balanced_worklist.reachable_stack_linear_bound
      dyadic_balanced_worklist.balanced_worklist_correct_and_bounded
      dyadic_balanced_worklist.execute_balanced_correct})
    then () else error "Dyadic balanced worklist depends on an oracle";
\<close>

end

end
