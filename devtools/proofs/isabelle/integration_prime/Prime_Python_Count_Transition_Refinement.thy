theory Prime_Python_Count_Transition_Refinement
  imports Prime_Deterministic_Worklist_Refinement
begin

text \<open>This theory models the control loop of
\<open>CoprimeRankDAG.count\<close> at
\<open>src/number_compiler/sequences/prime/coprime_rank.py:201-314\<close>.
The frame fields are exactly Python's \<open>(depth, limit, expanded)\<close>.
Limits remain signed at this boundary, while memo values are natural because
every value stored by an admitted run is nonnegative.\<close>

datatype python_phi_frame = PythonPhiFrame nat int bool
type_synonym python_phi_key = "nat \<times> int"
type_synonym python_phi_store = "python_phi_key \<Rightarrow> nat option"
type_synonym python_phi_config = "python_phi_frame list \<times> python_phi_store"

datatype python_phi_outcome =
    PythonPhiContinue python_phi_config
  | PythonPhiComplete python_phi_store
  | PythonPhiDependencyMissing

fun python_phi_next ::
    "nat list \<Rightarrow> python_phi_config \<Rightarrow> python_phi_outcome" where
  "python_phi_next ps ([],M) = PythonPhiComplete M"
| "python_phi_next ps (PythonPhiFrame d x ready # S,M) =
    (case M (d,x) of Some v \<Rightarrow> PythonPhiContinue (S,M)
     | None \<Rightarrow>
       if x \<le> 1 \<or> d = 0 then
         PythonPhiContinue (S,M((d,x) \<mapsto> nat x))
       else case d of
         0 \<Rightarrow> PythonPhiContinue (S,M((0,x) \<mapsto> nat x))
       | Suc 0 \<Rightarrow> PythonPhiContinue
           (S,M((1,x) \<mapsto> nat (x - x div int (ps!0))))
       | Suc (Suc n) \<Rightarrow>
           (let parent = Suc n;
                right_x = x div int (ps!parent)
            in if \<not> ready then
                 (let with_parent = PythonPhiFrame d x True # S;
                      with_right = (if M (parent,right_x) = None
                        then PythonPhiFrame parent right_x False # with_parent
                        else with_parent);
                      with_left = (if M (parent,x) = None
                        then PythonPhiFrame parent x False # with_right
                        else with_right)
                  in PythonPhiContinue (with_left,M))
               else
                 (case M (parent,x) of None \<Rightarrow> PythonPhiDependencyMissing
                  | Some left \<Rightarrow>
                    (case M (parent,right_x) of
                       None \<Rightarrow> PythonPhiDependencyMissing
                     | Some right \<Rightarrow> PythonPhiContinue
                         (S,M((d,x) \<mapsto> left-right))))))"

datatype python_count_entry =
    PythonCountReturned nat
  | PythonCountRunning python_phi_config

definition python_count_enter ::
    "python_phi_store \<Rightarrow> nat option \<Rightarrow> nat \<Rightarrow> int
      \<Rightarrow> python_count_entry" where
  "python_count_enter local_store shared d x =
    (case local_store (d,x) of Some value \<Rightarrow> PythonCountReturned value
     | None \<Rightarrow> (case shared of Some value \<Rightarrow> PythonCountReturned value
        | None \<Rightarrow> PythonCountRunning ([PythonPhiFrame d x False],local_store)))"

text \<open>The entry equations isolate the exact local-before-shared lookup
order at Python lines 257-265. The option called \<open>shared\<close> is the result
of the external lease lookup. Its key authentication, charging, and payload
validation deliberately remain outside this pure transition model.\<close>

lemma python_count_local_root_precedes_shared:
  "local_store (d,x) = Some value \<Longrightarrow>
    python_count_enter local_store shared d x = PythonCountReturned value"
  by (simp add: python_count_enter_def)

lemma python_count_shared_root_on_local_miss:
  "local_store (d,x) = None \<Longrightarrow> shared = Some value \<Longrightarrow>
    python_count_enter local_store shared d x = PythonCountReturned value"
  by (simp add: python_count_enter_def)

lemma python_count_cold_root_starts_one_unexpanded_frame:
  "local_store (d,x) = None \<Longrightarrow> shared = None \<Longrightarrow>
    python_count_enter local_store shared d x =
      PythonCountRunning ([PythonPhiFrame d x False],local_store)"
  by (simp add: python_count_enter_def)

lemma python_phi_cached_frame_is_popped:
  "M (d,x) = Some value \<Longrightarrow>
    python_phi_next ps (PythonPhiFrame d x ready # S,M) =
      PythonPhiContinue (S,M)"
  by simp

lemma python_phi_negative_limit_stores_zero:
  assumes absent: "M (d,x) = None" and negative: "x < 0"
  shows "python_phi_next ps (PythonPhiFrame d x ready # S,M) =
    PythonPhiContinue (S,M((d,x) \<mapsto> 0))"
  using assms by simp

lemma python_phi_empty_stack_completes:
  "python_phi_next ps ([],M) = PythonPhiComplete M"
  by simp

inductive python_phi_move ::
    "nat list \<Rightarrow> python_phi_config \<Rightarrow> python_phi_config
      \<Rightarrow> bool" for ps where
  move: "python_phi_next ps C = PythonPhiContinue C' \<Longrightarrow>
    python_phi_move ps C C'"

abbreviation python_phi_moves ::
    "nat list \<Rightarrow> python_phi_config \<Rightarrow> python_phi_config
      \<Rightarrow> bool" where
  "python_phi_moves ps \<equiv> (python_phi_move ps)\<^sup>*\<^sup>*"

lemma python_phi_moves_one:
  "python_phi_next ps C = PythonPhiContinue C' \<Longrightarrow>
    python_phi_moves ps C C'"
  by (intro r_into_rtranclp python_phi_move.move)

lemma python_phi_moves_trans:
  "python_phi_moves ps A B \<Longrightarrow> python_phi_moves ps B C \<Longrightarrow>
    python_phi_moves ps A C"
  by (rule rtranclp_trans)

definition python_store_of :: "phi_store \<Rightarrow> python_phi_store" where
  "python_store_of M = (\<lambda>(d,x).
    if x < 0 then None else M (d,nat x))"

lemma python_store_of_nat [simp]:
  "python_store_of M (d,int x) = M (d,x)"
  by (simp add: python_store_of_def)

lemma python_store_of_update:
  "python_store_of (M((d,x) \<mapsto> value)) =
    (python_store_of M)((d,int x) \<mapsto> value)"
  unfolding fun_eq_iff
proof
  fix key :: python_phi_key
  show "python_store_of (M((d,x) \<mapsto> value)) key =
    ((python_store_of M)((d,int x) \<mapsto> value)) key"
  proof (cases key)
    case (Pair current_depth current_x)
    show ?thesis
    proof (cases "current_x < 0")
      case True
      then show ?thesis using Pair
        by (simp add: python_store_of_def fun_upd_def)
    next
      case False
      have roundtrip: "int (nat current_x) = current_x" using False by simp
      show ?thesis
      proof (cases "current_depth = d \<and> nat current_x = x")
        case True
        then show ?thesis using Pair roundtrip
          by (simp add: python_store_of_def fun_upd_def)
      next
        case False
        then show ?thesis using Pair roundtrip
          by (auto simp: python_store_of_def fun_upd_def)
      qed
    qed
  qed
qed

fun python_frame_of :: "phi_frame \<Rightarrow> python_phi_frame" where
  "python_frame_of (Enter d x) = PythonPhiFrame d (int x) False"
| "python_frame_of (Finish d x) = PythonPhiFrame d (int x) True"

definition python_child_prune ::
    "phi_store \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat
      \<Rightarrow> phi_frame list \<Rightarrow> python_phi_frame list" where
  "python_child_prune M parent x right_x S =
    (if M (parent,x) = None then [PythonPhiFrame parent (int x) False] else []) @
    (if M (parent,right_x) = None
      then [PythonPhiFrame parent (int right_x) False] else []) @
    [PythonPhiFrame (Suc parent) (int x) True] @ map python_frame_of S"

lemma int_nat_division [simp]:
  "int x div int p = int (x div p)"
  by (simp add: of_nat_div)

lemma nat_int_difference [simp]:
  assumes "b \<le> a"
  shows "nat (int a - int b) = a-b"
proof -
  have "nat (int a - int b) = nat (int a) - nat (int b)"
    by (rule nat_diff_distrib) (use assms in simp_all)
  then show ?thesis by simp
qed

text \<open>This is the exact child-push suppression at Python lines 284-291.
It is stronger than an existential run statement: the theorem identifies the
single successor stack for all four combinations of cached left/right child.
The older abstract machine's unconditional expansion is the same list before
\<open>python_child_prune\<close> removes precisely the cached Enter frames.\<close>

theorem python_phi_expand_is_exact_cached_child_pruning:
  assumes root_absent: "M (Suc parent,x) = None"
    and nontrivial: "1 < x"
    and depth: "Suc parent = Suc (Suc n)"
  shows "python_phi_next ps
      (PythonPhiFrame (Suc parent) (int x) False # map python_frame_of S,
        python_store_of M) =
    PythonPhiContinue
      (python_child_prune M parent x (x div (ps!parent)) S,
        python_store_of M)"
  using assms
  by (simp add: python_store_of_def python_child_prune_def Let_def)

corollary python_phi_expand_left_cached_only:
  assumes root_absent: "M (Suc parent,x) = None"
    and nontrivial: "1 < x"
    and depth: "Suc parent = Suc (Suc n)"
    and left: "M (parent,x) = Some left_value"
    and right: "M (parent,x div (ps!parent)) = None"
  shows "python_phi_next ps
      (PythonPhiFrame (Suc parent) (int x) False # map python_frame_of S,
        python_store_of M) =
    PythonPhiContinue
      (PythonPhiFrame parent (int (x div (ps!parent))) False #
       PythonPhiFrame (Suc parent) (int x) True # map python_frame_of S,
       python_store_of M)"
  using python_phi_expand_is_exact_cached_child_pruning[where ps=ps and M=M and parent=parent and x=x and n=n and S=S, OF root_absent nontrivial depth]
    left right by (simp add: python_child_prune_def)

corollary python_phi_expand_right_cached_only:
  assumes root_absent: "M (Suc parent,x) = None"
    and nontrivial: "1 < x"
    and depth: "Suc parent = Suc (Suc n)"
    and left: "M (parent,x) = None"
    and right: "M (parent,x div (ps!parent)) = Some right_value"
  shows "python_phi_next ps
      (PythonPhiFrame (Suc parent) (int x) False # map python_frame_of S,
        python_store_of M) =
    PythonPhiContinue
      (PythonPhiFrame parent (int x) False #
       PythonPhiFrame (Suc parent) (int x) True # map python_frame_of S,
       python_store_of M)"
  using python_phi_expand_is_exact_cached_child_pruning[where ps=ps and M=M and parent=parent and x=x and n=n and S=S, OF root_absent nontrivial depth]
    left right by (simp add: python_child_prune_def)

corollary python_phi_expand_both_children_cached:
  assumes root_absent: "M (Suc parent,x) = None"
    and nontrivial: "1 < x"
    and depth: "Suc parent = Suc (Suc n)"
    and left: "M (parent,x) = Some left_value"
    and right: "M (parent,x div (ps!parent)) = Some right_value"
  shows "python_phi_next ps
      (PythonPhiFrame (Suc parent) (int x) False # map python_frame_of S,
        python_store_of M) =
    PythonPhiContinue
      (PythonPhiFrame (Suc parent) (int x) True # map python_frame_of S,
       python_store_of M)"
  using python_phi_expand_is_exact_cached_child_pruning[where ps=ps and M=M and parent=parent and x=x and n=n and S=S, OF root_absent nontrivial depth]
    left right by (simp add: python_child_prune_def)

lemma python_phi_small_terminal_value:
  assumes valid: "valid_phi_store ps M"
    and depth: "d \<le> length ps"
    and factors: "\<forall>p\<in>set ps. 2 \<le> p"
    and absent: "M (d,x) = None"
    and small: "x \<le> 1"
  shows "python_phi_next ps
      (PythonPhiFrame d (int x) ready # map python_frame_of S,
        python_store_of M) =
    PythonPhiContinue
      (map python_frame_of S,
       (python_store_of M)((d,int x) \<mapsto> numerical_Phi ps d x))"
proof -
  have exact: "x = numerical_Phi ps d x"
    using numerical_Phi_small_input[OF depth factors small] by simp
  show ?thesis using absent small exact
    by (simp add: python_store_of_def fun_upd_def)
qed

lemma python_phi_depth_zero_terminal_value:
  assumes absent: "M (0,x) = None" and nontrivial: "1 < x"
  shows "python_phi_next ps
      (PythonPhiFrame 0 (int x) ready # map python_frame_of S,
        python_store_of M) =
    PythonPhiContinue
      (map python_frame_of S,
       (python_store_of M)((0,int x) \<mapsto> numerical_Phi ps 0 x))"
  using assms by (simp add: python_store_of_def fun_upd_def)

lemma python_phi_depth_one_terminal_value:
  assumes depth: "1 \<le> length ps"
    and factors: "\<forall>p\<in>set ps. 2 \<le> p"
    and absent: "M (1,x) = None"
    and nontrivial: "1 < x"
  shows "python_phi_next ps
      (PythonPhiFrame 1 (int x) ready # map python_frame_of S,
        python_store_of M) =
    PythonPhiContinue
      (map python_frame_of S,
       (python_store_of M)((1,int x) \<mapsto> numerical_Phi ps 1 x))"
  using assms by (simp add: python_store_of_def fun_upd_def
      depth_one_shortcut_exact)

lemma wheel_sift_mono_set:
  assumes "A \<subseteq> B"
  shows "wheel_sift qs A \<subseteq> wheel_sift qs B"
  using assms by (induction qs arbitrary: A B) auto

lemma numerical_Phi_mono_limit:
  assumes bounds: "y \<le> x" and depth: "d \<le> length ps"
    and distinct: "distinct ps" and primes: "\<forall>p\<in>set ps. prime p"
  shows "numerical_Phi ps d y \<le> numerical_Phi ps d x"
proof -
  let ?qs = "rev (take d ps)"
  have y_value: "numerical_Phi ps d y = card (wheel_sift ?qs {1..y})"
    by (rule numerical_Phi_is_sift_card[OF depth distinct primes])
  have x_value: "numerical_Phi ps d x = card (wheel_sift ?qs {1..x})"
    by (rule numerical_Phi_is_sift_card[OF depth distinct primes])
  have subset: "wheel_sift ?qs {1..y} \<subseteq> wheel_sift ?qs {1..x}"
    by (rule wheel_sift_mono_set) (use bounds in auto)
  have finite: "finite (wheel_sift ?qs {1..x})"
    by (rule finite_wheel_sift) simp
  show ?thesis using card_mono[OF finite subset] y_value x_value by simp
qed

lemma python_phi_finish_terminal_value:
  assumes valid: "valid_phi_store ps M"
    and depth: "Suc parent \<le> length ps"
    and parent_pos: "0 < parent"
    and root_absent: "M (Suc parent,x) = None"
    and nontrivial: "1 < x"
    and distinct: "distinct ps"
    and primes: "\<forall>p\<in>set ps. prime p"
    and left: "M (parent,x) = Some l"
    and right: "M (parent,x div (ps!parent)) = Some r"
  shows "python_phi_next ps
      (PythonPhiFrame (Suc parent) (int x) True # map python_frame_of S,
        python_store_of M) =
    PythonPhiContinue
      (map python_frame_of S,
       (python_store_of M)
         ((Suc parent,int x) \<mapsto> numerical_Phi ps (Suc parent) x))"
    "int l - int r = int (numerical_Phi ps (Suc parent) x)"
proof -
  have exact: "l-r = numerical_Phi ps (Suc parent) x"
    by (rule postorder_children_compute_parent[OF depth left right valid])
  have parent_depth: "parent \<le> length ps" using depth by simp
  have right_value: "r = numerical_Phi ps parent (x div (ps!parent))"
    using valid_phi_store_lookup[OF valid right] by simp
  have left_value: "l = numerical_Phi ps parent x"
    using valid_phi_store_lookup[OF valid left] by simp
  have quotient_le: "x div (ps!parent) \<le> x" by simp
  have phi_le: "numerical_Phi ps parent (x div (ps!parent)) \<le>
      numerical_Phi ps parent x"
    by (rule numerical_Phi_mono_limit[OF quotient_le parent_depth distinct primes])
  have right_le: "r \<le> l"
    using phi_le right_value left_value by simp
  have integer_exact: "int l - int r = int (numerical_Phi ps (Suc parent) x)"
    using exact right_le by simp
  show "python_phi_next ps
      (PythonPhiFrame (Suc parent) (int x) True # map python_frame_of S,
        python_store_of M) =
    PythonPhiContinue
      (map python_frame_of S,
       (python_store_of M)
         ((Suc parent,int x) \<mapsto> numerical_Phi ps (Suc parent) x))"
    using left right exact integer_exact parent_pos root_absent nontrivial
    by (cases parent)
      (simp_all add: python_store_of_def fun_upd_def)
  show "int l - int r = int (numerical_Phi ps (Suc parent) x)"
    by (fact integer_exact)
qed

lemma deterministic_phi_eval_preserves_deeper_key:
  assumes deeper: "d < target"
  shows "snd (deterministic_phi_eval ps d x M) (target,y) = M (target,y)"
  using deeper
proof (induction d arbitrary: x M rule: less_induct)
  case (less d)
  show ?case
  proof (cases d)
    case 0
    then show ?thesis using less.prems
      by (cases "M (0,x)") (simp_all add: fun_upd_def)
  next
    case outer: (Suc e)
    show ?thesis
    proof (cases e)
      case zero: 0
      then show ?thesis using outer less.prems
        by (cases "M (1,x)"; cases "x \<le> 1")
          (simp_all add: Let_def fun_upd_def)
    next
      case inner: (Suc n)
      let ?child = "Suc n"
      show ?thesis
      proof (cases "M (d,x)")
        case (Some cached)
        then show ?thesis using outer inner by simp
      next
        case None
        show ?thesis
        proof (cases "x \<le> 1")
          case True
          then show ?thesis using outer inner None less.prems
            by (simp add: fun_upd_def)
        next
          case False
          let ?left = "deterministic_phi_eval ps ?child x M"
          let ?right = "deterministic_phi_eval ps ?child
            (x div (ps!?child)) (snd ?left)"
          let ?value = "fst ?left - fst ?right"
          have child_less: "?child < d" using outer inner by simp
          have child_target: "?child < target"
            using less.prems outer inner by simp
          have left_preserved: "snd ?left (target,y) = M (target,y)"
            by (rule less.IH[OF child_less child_target])
          have right_preserved:
              "snd ?right (target,y) = snd ?left (target,y)"
            by (rule less.IH[OF child_less child_target])
          have evaluation: "snd (deterministic_phi_eval ps d x M) =
              (snd ?right)((d,x) \<mapsto> ?value)"
            using outer inner None False
            by (simp only: deterministic_phi_eval.simps option.simps if_False
                Let_def fst_conv snd_conv)
          show ?thesis using evaluation left_preserved right_preserved less.prems
            by (simp add: fun_upd_def)
        qed
      qed
    qed
  qed
qed

theorem python_phi_pruned_worklist_reaches_evaluator:
  assumes valid: "valid_phi_store ps M"
    and depth: "d \<le> length ps"
    and distinct: "distinct ps"
    and primes: "\<forall>p\<in>set ps. prime p"
  shows "python_phi_moves ps
    (PythonPhiFrame d (int x) False # map python_frame_of S,
      python_store_of M)
    (map python_frame_of S,
      python_store_of (snd (deterministic_phi_eval ps d x M)))"
  using valid depth
proof (induction d arbitrary: x M S rule: less_induct)
  case (less d)
  have factors: "\<forall>p\<in>set ps. 2 \<le> p"
  proof (intro ballI)
    fix p assume member: "p \<in> set ps"
    have "1 < p" by (rule prime_gt_1_nat) (use primes member in blast)
    then show "2 \<le> p" by simp
  qed
  show ?case
  proof (cases "M (d,x)")
    case (Some cached)
    have step: "python_phi_next ps
        (PythonPhiFrame d (int x) False # map python_frame_of S,
          python_store_of M) =
      PythonPhiContinue (map python_frame_of S,python_store_of M)"
      using Some by simp
    have evaluation: "snd (deterministic_phi_eval ps d x M) = M"
      using deterministic_phi_cached_root[where ps=ps and d=d and x=x and
        M=M and v=cached, OF Some] by simp
    show ?thesis using python_phi_moves_one[OF step]
      by (simp only: evaluation)
  next
    case root_absent: None
    show ?thesis
    proof (cases "x \<le> 1")
      case True
      let ?M' = "M((d,x) \<mapsto> x)"
      have step: "python_phi_next ps
          (PythonPhiFrame d (int x) False # map python_frame_of S,
            python_store_of M) =
        PythonPhiContinue (map python_frame_of S,python_store_of ?M')"
        using root_absent True python_store_of_update[of M d x x]
        by (simp add: fun_upd_def)
      have evaluation: "snd (deterministic_phi_eval ps d x M) = ?M'"
      proof (cases d)
        case 0
        then show ?thesis using root_absent by simp
      next
        case (Suc e)
        then show ?thesis using root_absent True
          by (cases e) (simp_all add: Let_def)
      qed
      show ?thesis using python_phi_moves_one[OF step]
        by (simp only: evaluation)
    next
      case False
      have nontrivial: "1 < x" using False by simp
      show ?thesis
      proof (cases d)
        case zero: 0
        let ?M' = "M((0,x) \<mapsto> x)"
        have step: "python_phi_next ps
            (PythonPhiFrame d (int x) False # map python_frame_of S,
              python_store_of M) =
          PythonPhiContinue (map python_frame_of S,python_store_of ?M')"
          using zero root_absent nontrivial python_store_of_update[of M 0 x x]
          by (simp add: fun_upd_def)
        have evaluation: "snd (deterministic_phi_eval ps d x M) = ?M'"
          using zero root_absent by simp
        show ?thesis using python_phi_moves_one[OF step]
          by (simp only: evaluation)
      next
        case outer: (Suc e)
        show ?thesis
        proof (cases e)
          case zero: 0
          let ?value = "x - x div (ps!0)"
          let ?M' = "M((1,x) \<mapsto> ?value)"
          have zero_index: "0 < length ps"
          proof (cases ps)
            case Nil
            then show ?thesis using less.prems(2) outer zero by simp
          next
            case (Cons p rest)
            then show ?thesis by simp
          qed
          have first_member: "ps!0 \<in> set ps"
            by (rule nth_mem[OF zero_index])
          have first_factor: "2 \<le> ps!0"
            using factors first_member by blast
          have step: "python_phi_next ps
              (PythonPhiFrame d (int x) False # map python_frame_of S,
                python_store_of M) =
            PythonPhiContinue (map python_frame_of S,python_store_of ?M')"
            using outer zero root_absent nontrivial first_factor
              python_store_of_update[of M 1 x ?value]
            by (simp add: fun_upd_def)
          have evaluation: "snd (deterministic_phi_eval ps d x M) = ?M'"
            using outer zero root_absent False by (simp add: Let_def)
          show ?thesis using python_phi_moves_one[OF step]
            by (simp only: evaluation)
        next
          case inner: (Suc n)
          let ?child = "Suc n"
          let ?q = "ps!?child"
          let ?right_x = "x div ?q"
          let ?left = "deterministic_phi_eval ps ?child x M"
          let ?right = "deterministic_phi_eval ps ?child ?right_x (snd ?left)"
          let ?value = "fst ?left - fst ?right"
          let ?final = "(snd ?right)((d,x) \<mapsto> ?value)"
          let ?finish_tail = "[Finish d x] @ S"
          let ?right_tail =
            "(if M (?child,?right_x) = None then [Enter ?child ?right_x]
              else []) @ ?finish_tail"
          let ?expanded =
            "(if M (?child,x) = None then [Enter ?child x] else []) @ ?right_tail"
          have child_less: "?child < d" using outer inner by simp
          have child_depth: "?child \<le> length ps"
            using less.prems(2) outer inner by simp
          have parent_shape: "d = Suc ?child" using outer inner by simp
          have child_shape: "Suc ?child = Suc (Suc n)" by simp
          have shaped_root_absent: "M (Suc ?child,x) = None"
            using root_absent parent_shape by simp
          have expand: "python_phi_moves ps
              (PythonPhiFrame d (int x) False # map python_frame_of S,
                python_store_of M)
              (map python_frame_of ?expanded,python_store_of M)"
          proof (rule python_phi_moves_one)
            note one_step = python_phi_expand_is_exact_cached_child_pruning[where ps=ps and M=M
              and parent="?child" and x=x and n=n and S=S,
              OF shaped_root_absent nontrivial child_shape]
            show "python_phi_next ps
                (PythonPhiFrame d (int x) False # map python_frame_of S,
                  python_store_of M) =
              PythonPhiContinue
                (map python_frame_of ?expanded,python_store_of M)"
              using one_step parent_shape
              by (simp add: python_child_prune_def)
          qed
          have left_correct:
              "fst ?left = numerical_Phi ps ?child x \<and>
               valid_phi_store ps (snd ?left) \<and>
               store_extends M (snd ?left)"
            by (rule deterministic_phi_eval_correct[OF less.prems(1)
                  child_depth factors])
          have left_run: "python_phi_moves ps
              (map python_frame_of ?expanded,python_store_of M)
              (map python_frame_of ?right_tail,python_store_of (snd ?left))"
          proof (cases "M (?child,x)")
            case None
            show ?thesis using less.IH[OF child_less, where x=x and M=M and
                S="?right_tail"] less.prems(1) child_depth None
              by simp
          next
            case (Some cached)
            have left_store: "snd ?left = M"
              using deterministic_phi_cached_root[where ps=ps and d="?child"
                and x=x and M=M and v=cached, OF Some] by simp
            show ?thesis using Some left_store by simp
          qed
          have left_valid: "valid_phi_store ps (snd ?left)"
            using left_correct by blast
          have left_extends: "store_extends M (snd ?left)"
            using left_correct by blast
          have right_correct:
              "fst ?right = numerical_Phi ps ?child ?right_x \<and>
               valid_phi_store ps (snd ?right) \<and>
               store_extends (snd ?left) (snd ?right)"
            by (rule deterministic_phi_eval_correct[OF left_valid
                  child_depth factors])
          have right_run: "python_phi_moves ps
              (map python_frame_of ?right_tail,python_store_of (snd ?left))
              (map python_frame_of ?finish_tail,python_store_of (snd ?right))"
          proof (cases "M (?child,?right_x)")
            case None
            show ?thesis using less.IH[OF child_less, where x="?right_x" and
                M="snd ?left" and S="?finish_tail"] left_valid child_depth None
              by simp
          next
            case (Some cached)
            have retained: "snd ?left (?child,?right_x) = Some cached"
              using left_extends Some by (auto simp: store_extends_def)
            have right_store: "snd ?right = snd ?left"
              using deterministic_phi_cached_root[where ps=ps and d="?child"
                and x="?right_x" and M="snd ?left" and v=cached, OF retained]
              by simp
            show ?thesis using Some right_store by simp
          qed
          have right_valid: "valid_phi_store ps (snd ?right)"
            using right_correct by blast
          have right_extends: "store_extends (snd ?left) (snd ?right)"
            using right_correct by blast
          have left_root: "snd ?left (?child,x) = Some (fst ?left)"
            by (rule deterministic_phi_eval_stores_root)
          have left_retained: "snd ?right (?child,x) = Some (fst ?left)"
            using right_extends left_root by (auto simp: store_extends_def)
          have right_root: "snd ?right (?child,?right_x) = Some (fst ?right)"
            by (rule deterministic_phi_eval_stores_root)
          have left_parent_absent: "snd ?left (d,x) = None"
            using deterministic_phi_eval_preserves_deeper_key[OF child_less,
              of ps x M x] root_absent by simp
          have right_parent_absent: "snd ?right (d,x) = None"
            using deterministic_phi_eval_preserves_deeper_key[OF child_less,
              of ps ?right_x "snd ?left" x] left_parent_absent by simp
          have root_value: "?value = numerical_Phi ps d x"
            using left_correct right_correct parent_shape by simp
          have shaped_depth: "Suc ?child \<le> length ps"
            using less.prems(2) parent_shape by simp
          have child_positive: "0 < ?child" by simp
          have shaped_parent_absent: "snd ?right (Suc ?child,x) = None"
            using right_parent_absent parent_shape by simp
          have finish_step: "python_phi_next ps
              (map python_frame_of ?finish_tail,python_store_of (snd ?right)) =
            PythonPhiContinue
              (map python_frame_of S,python_store_of ?final)"
          proof -
            note terminal = python_phi_finish_terminal_value(1)[where ps=ps
              and M="snd ?right" and parent="?child" and x=x
              and l="fst ?left" and r="fst ?right" and S=S,
              OF right_valid shaped_depth child_positive shaped_parent_absent
                nontrivial distinct primes left_retained right_root]
            show ?thesis using terminal
              by (simp only: parent_shape root_value python_store_of_update
                  map_append list.map(1) list.map(2) python_frame_of.simps
                  append_Cons append_Nil)
          qed
          have finish: "python_phi_moves ps
              (map python_frame_of ?finish_tail,python_store_of (snd ?right))
              (map python_frame_of S,python_store_of ?final)"
            by (rule python_phi_moves_one[OF finish_step])
          have through_left: "python_phi_moves ps
              (PythonPhiFrame d (int x) False # map python_frame_of S,
                python_store_of M)
              (map python_frame_of ?right_tail,python_store_of (snd ?left))"
            by (rule python_phi_moves_trans[OF expand left_run])
          have through_right: "python_phi_moves ps
              (PythonPhiFrame d (int x) False # map python_frame_of S,
                python_store_of M)
              (map python_frame_of ?finish_tail,python_store_of (snd ?right))"
            by (rule python_phi_moves_trans[OF through_left right_run])
          have completed: "python_phi_moves ps
              (PythonPhiFrame d (int x) False # map python_frame_of S,
                python_store_of M)
              (map python_frame_of S,python_store_of ?final)"
            by (rule python_phi_moves_trans[OF through_right finish])
          have evaluation: "snd (deterministic_phi_eval ps d x M) = ?final"
            using outer inner root_absent False
            by (simp only: deterministic_phi_eval.simps option.simps if_False
                Let_def fst_conv snd_conv)
          show ?thesis using completed by (simp only: evaluation)
        qed
      qed
    qed
  qed
qed

corollary python_phi_pruned_worklist_completes:
  fixes x :: nat
  assumes valid: "valid_phi_store ps M"
    and depth: "d \<le> length ps"
    and distinct: "distinct ps"
    and primes: "\<forall>p\<in>set ps. prime p"
  defines "M' \<equiv> snd (deterministic_phi_eval ps d x M)"
  shows "python_phi_moves ps
      ([PythonPhiFrame d (int x) False],python_store_of M)
      ([],python_store_of M')"
    "python_phi_next ps ([],python_store_of M') =
      PythonPhiComplete (python_store_of M')"
    "M' (d,x) = Some (numerical_Phi ps d x)"
proof -
  show "python_phi_moves ps
      ([PythonPhiFrame d (int x) False],python_store_of M)
      ([],python_store_of M')"
    using python_phi_pruned_worklist_reaches_evaluator[OF valid depth distinct
      primes, of x "[]"] by (simp add: M'_def)
  show "python_phi_next ps ([],python_store_of M') =
      PythonPhiComplete (python_store_of M')" by simp
  have root: "snd (deterministic_phi_eval ps d x M) (d,x) =
      Some (fst (deterministic_phi_eval ps d x M))"
    by (rule deterministic_phi_eval_stores_root)
  have factors: "\<forall>p\<in>set ps. 2 \<le> p"
  proof (intro ballI)
    fix p assume member: "p \<in> set ps"
    have "1 < p" by (rule prime_gt_1_nat) (use primes member in blast)
    then show "2 \<le> p" by simp
  qed
  note correct = deterministic_phi_eval_correct[where ps=ps and M=M and d=d
    and x=x, OF valid depth factors]
  have root_value: "fst (deterministic_phi_eval ps d x M) = numerical_Phi ps d x"
    using correct by blast
  show "M' (d,x) = Some (numerical_Phi ps d x)"
    using root root_value by (simp add: M'_def)
qed

text \<open>The exported equations cover the actual local root lookup,
optional shared-root return, signed negative terminal, cached-frame pop,
cache-aware child pushes, depth-zero/depth-one terminals, dependency reads,
and exact parent terminal value. The shared option is already-authenticated
input. Lease key construction and validation, work/state charging, publication,
exception cleanup, counters, and mutable-dictionary identity remain separate
runtime obligations; none is inferred from the arithmetic transition.\<close>

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms python_count_local_root_precedes_shared
      python_count_shared_root_on_local_miss
      python_count_cold_root_starts_one_unexpanded_frame
      python_phi_cached_frame_is_popped
      python_phi_negative_limit_stores_zero python_phi_empty_stack_completes
      python_phi_expand_is_exact_cached_child_pruning
      python_phi_expand_left_cached_only python_phi_expand_right_cached_only
      python_phi_expand_both_children_cached
      python_phi_small_terminal_value python_phi_depth_zero_terminal_value
      python_phi_depth_one_terminal_value python_phi_finish_terminal_value
      deterministic_phi_eval_preserves_deeper_key
      python_phi_pruned_worklist_reaches_evaluator
      python_phi_pruned_worklist_completes}) then ()
    else error "Python prime count transition refinement depends on an oracle";
\<close>

end
