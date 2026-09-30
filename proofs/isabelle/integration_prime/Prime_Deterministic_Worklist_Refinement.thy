theory Prime_Deterministic_Worklist_Refinement
  imports Prime_Deterministic_Phi_Refinement
begin

datatype deterministic_phi_outcome =
    PhiContinue phi_config
  | PhiComplete phi_store
  | PhiDependencyMissing

fun deterministic_phi_next ::
    "nat list \<Rightarrow> phi_config \<Rightarrow> deterministic_phi_outcome" where
  "deterministic_phi_next ps ([],M) = PhiComplete M"
| "deterministic_phi_next ps (Enter d x # S,M) =
    (case M (d,x) of Some v \<Rightarrow> PhiContinue (S,M)
     | None \<Rightarrow>
       if x \<le> 1 then PhiContinue (S,M((d,x) \<mapsto> x))
       else case d of
         0 \<Rightarrow> PhiContinue (S,M((0,x) \<mapsto> x))
       | Suc 0 \<Rightarrow> PhiContinue
           (S,M((1,x) \<mapsto> x - x div (ps!0)))
       | Suc (Suc n) \<Rightarrow> PhiContinue
           (Enter (Suc n) x # Enter (Suc n) (x div (ps!(Suc n))) #
             Finish (Suc (Suc n)) x # S,M))"
| "deterministic_phi_next ps (Finish d x # S,M) =
    (case d of 0 \<Rightarrow> PhiDependencyMissing
     | Suc parent \<Rightarrow>
       (case M (parent,x) of None \<Rightarrow> PhiDependencyMissing
        | Some left \<Rightarrow>
          (case M (parent,x div (ps!parent)) of
             None \<Rightarrow> PhiDependencyMissing
           | Some right \<Rightarrow> PhiContinue
               (S,M((d,x) \<mapsto> left-right)))))"

text \<open>The cases below are the exact control branches in
\<open>CoprimeRankDAG.count\<close>.  In particular a cached root or child is
popped without mutation, and depth one is completed without pushing either
recurrence child.\<close>

lemma deterministic_worklist_cached_reuse:
  assumes "M (d,x) = Some value"
  shows "deterministic_phi_next ps (Enter d x # S,M) = PhiContinue (S,M)"
  using assms by simp

lemma deterministic_worklist_small_input:
  assumes valid: "valid_phi_store ps M"
    and depth: "d \<le> length ps"
    and factors: "\<forall>p\<in>set ps. 2 \<le> p"
    and absent: "M (d,x) = None"
    and small: "x \<le> 1"
  defines "M' \<equiv> M((d,x) \<mapsto> x)"
  shows "deterministic_phi_next ps (Enter d x # S,M) = PhiContinue (S,M')"
    "valid_phi_store ps M'"
    "store_extends M M'"
proof -
  have exact: "x = numerical_Phi ps d x"
    using numerical_Phi_small_input[OF depth factors small] by simp
  show "deterministic_phi_next ps (Enter d x # S,M) = PhiContinue (S,M')"
    using absent small by (simp add: M'_def)
  show "valid_phi_store ps M'"
    unfolding M'_def
    by (rule valid_phi_store_update[OF valid depth exact])
  show "store_extends M M'"
    unfolding M'_def
    by (rule exact_update_extends[OF valid depth exact])
qed

lemma deterministic_worklist_depth_one_shortcut:
  assumes valid: "valid_phi_store ps M"
    and depth: "1 \<le> length ps"
    and absent: "M (1,x) = None"
    and nontrivial: "1 < x"
  defines "value \<equiv> x - x div (ps!0)"
    and "M' \<equiv> M((1,x) \<mapsto> x - x div (ps!0))"
  shows "deterministic_phi_next ps (Enter 1 x # S,M) = PhiContinue (S,M')"
    "value = numerical_Phi ps 1 x"
    "valid_phi_store ps M'"
    "store_extends M M'"
proof -
  have exact: "value = numerical_Phi ps 1 x"
    by (simp add: value_def depth_one_shortcut_exact)
  have update_exact: "x - x div (ps!0) = numerical_Phi ps 1 x"
    using exact unfolding value_def .
  show "deterministic_phi_next ps (Enter 1 x # S,M) = PhiContinue (S,M')"
    using absent nontrivial by (simp add: M'_def value_def)
  show "value = numerical_Phi ps 1 x" by (fact exact)
  show "valid_phi_store ps M'"
    unfolding M'_def
    by (rule valid_phi_store_update[OF valid depth update_exact])
  show "store_extends M M'"
    unfolding M'_def
    by (rule exact_update_extends[OF valid depth update_exact])
qed

lemma deterministic_worklist_expand:
  assumes "M (Suc (Suc d),x) = None" "1 < x"
  shows "deterministic_phi_next ps (Enter (Suc (Suc d)) x # S,M) =
    PhiContinue (Enter (Suc d) x #
      Enter (Suc d) (x div (ps!(Suc d))) #
      Finish (Suc (Suc d)) x # S,M)"
  using assms by simp

lemma deterministic_worklist_finish_exact:
  assumes valid: "valid_phi_store ps M"
    and depth: "Suc d \<le> length ps"
    and left: "M (d,x) = Some l"
    and right: "M (d,x div (ps!d)) = Some r"
  defines "M' \<equiv> M((Suc d,x) \<mapsto> l-r)"
  shows "deterministic_phi_next ps (Finish (Suc d) x # S,M) =
      PhiContinue (S,M')"
    "l-r = numerical_Phi ps (Suc d) x"
    "valid_phi_store ps M'"
    "store_extends M M'"
proof -
  have exact: "l-r = numerical_Phi ps (Suc d) x"
    by (rule postorder_children_compute_parent[OF depth left right valid])
  show "deterministic_phi_next ps (Finish (Suc d) x # S,M) =
      PhiContinue (S,M')"
    using left right by (simp add: M'_def)
  show "l-r = numerical_Phi ps (Suc d) x" by (fact exact)
  show "valid_phi_store ps M'"
    unfolding M'_def
    by (rule valid_phi_store_update[OF valid depth exact])
  show "store_extends M M'"
    unfolding M'_def
    by (rule exact_update_extends[OF valid depth exact])
qed

inductive deterministic_phi_move ::
    "nat list \<Rightarrow> phi_config \<Rightarrow> phi_config \<Rightarrow> bool" for ps where
  move: "deterministic_phi_next ps C = PhiContinue C' \<Longrightarrow>
    deterministic_phi_move ps C C'"

abbreviation deterministic_phi_moves ::
    "nat list \<Rightarrow> phi_config \<Rightarrow> phi_config \<Rightarrow> bool" where
  "deterministic_phi_moves ps \<equiv> (deterministic_phi_move ps)\<^sup>*\<^sup>*"

lemma deterministic_phi_moves_one:
  "deterministic_phi_next ps C = PhiContinue C' \<Longrightarrow>
    deterministic_phi_moves ps C C'"
  by (intro r_into_rtranclp deterministic_phi_move.move)

lemma deterministic_phi_moves_trans:
  "deterministic_phi_moves ps A B \<Longrightarrow>
    deterministic_phi_moves ps B C \<Longrightarrow>
    deterministic_phi_moves ps A C"
  by (rule rtranclp_trans)

lemma deterministic_phi_eval_stores_root:
  "snd (deterministic_phi_eval ps d x M) (d,x) =
    Some (fst (deterministic_phi_eval ps d x M))"
proof (induction d arbitrary: x M rule: less_induct)
  case (less d)
  show ?case
  proof (cases d)
    case 0
    then show ?thesis by (cases "M (0,x)") (simp_all add: fun_upd_def)
  next
    case outer: (Suc e)
    show ?thesis
    proof (cases e)
      case zero: 0
      then show ?thesis using outer
        by (cases "M (1,x)"; cases "x \<le> 1")
          (simp_all add: Let_def fun_upd_def)
    next
      case inner: (Suc n)
      show ?thesis
      proof (cases "M (d,x)")
        case (Some cached)
        then show ?thesis using outer inner by simp
      next
        case None
        show ?thesis
        proof (cases "x \<le> 1")
          case True
          then show ?thesis using outer inner None by (simp add: fun_upd_def)
        next
          case False
          let ?left = "deterministic_phi_eval ps (Suc n) x M"
          let ?right = "deterministic_phi_eval ps (Suc n)
            (x div (ps!(Suc n))) (snd ?left)"
          let ?v = "fst ?left - fst ?right"
          have evaluation: "deterministic_phi_eval ps d x M =
              (?v,(snd ?right)((d,x) \<mapsto> ?v))"
            using outer inner None False
            by (simp only: deterministic_phi_eval.simps option.simps if_False
                Let_def fst_conv snd_conv)
          show ?thesis by (simp only: evaluation fst_conv snd_conv fun_upd_same)
        qed
      qed
    qed
  qed
qed

theorem deterministic_phi_worklist_reaches_evaluator:
  assumes valid: "valid_phi_store ps M"
    and depth: "d \<le> length ps"
    and factors: "\<forall>p\<in>set ps. 2 \<le> p"
  shows "deterministic_phi_moves ps (Enter d x # S,M)
    (S,snd (deterministic_phi_eval ps d x M))"
  using valid depth
proof (induction d arbitrary: x M S rule: less_induct)
  case (less d)
  show ?case
  proof (cases d)
    case 0
    show ?thesis
    proof (cases "M (0,x)")
      case (Some cached)
      have step: "deterministic_phi_next ps (Enter d x # S,M) =
          PhiContinue (S,M)" using 0 Some by simp
      have eval: "snd (deterministic_phi_eval ps d x M) = M"
        using 0 Some by simp
      show ?thesis using deterministic_phi_moves_one[OF step] by (simp only: eval)
    next
      case None
      have step: "deterministic_phi_next ps (Enter d x # S,M) =
          PhiContinue (S,M((0,x) \<mapsto> x))"
        using 0 None by simp
      have eval: "snd (deterministic_phi_eval ps d x M) = M((0,x) \<mapsto> x)"
        using 0 None by simp
      show ?thesis using deterministic_phi_moves_one[OF step] by (simp only: eval)
    qed
  next
    case outer: (Suc e)
    show ?thesis
    proof (cases e)
      case zero: 0
      show ?thesis
      proof (cases "M (1,x)")
        case (Some cached)
        have step: "deterministic_phi_next ps (Enter d x # S,M) =
            PhiContinue (S,M)" using outer zero Some by simp
        have eval: "snd (deterministic_phi_eval ps d x M) = M"
          using outer zero Some by simp
        show ?thesis using deterministic_phi_moves_one[OF step] by (simp only: eval)
      next
        case None
        show ?thesis
        proof (cases "x \<le> 1")
          case True
          have step: "deterministic_phi_next ps (Enter d x # S,M) =
              PhiContinue (S,M((1,x) \<mapsto> x))"
            using outer zero None True by simp
          have eval: "snd (deterministic_phi_eval ps d x M) = M((1,x) \<mapsto> x)"
            using outer zero None True by (simp add: Let_def)
          show ?thesis using deterministic_phi_moves_one[OF step] by (simp only: eval)
        next
          case False
          let ?v = "x - x div (ps!0)"
          have step: "deterministic_phi_next ps (Enter d x # S,M) =
              PhiContinue (S,M((1,x) \<mapsto> ?v))"
            using outer zero None False by simp
          have eval: "snd (deterministic_phi_eval ps d x M) = M((1,x) \<mapsto> ?v)"
            using outer zero None False by (simp add: Let_def)
          show ?thesis using deterministic_phi_moves_one[OF step] by (simp only: eval)
        qed
      qed
    next
      case inner: (Suc n)
      let ?child = "Suc n"
      let ?q = "ps!?child"
      have child_less: "?child < d" using outer inner by simp
      have child_depth: "?child \<le> length ps" using less.prems outer inner by simp
      show ?thesis
      proof (cases "M (d,x)")
        case (Some cached)
        have step: "deterministic_phi_next ps (Enter d x # S,M) =
            PhiContinue (S,M)" using Some by simp
        have eval: "snd (deterministic_phi_eval ps d x M) = M"
          using outer inner Some by simp
        show ?thesis using deterministic_phi_moves_one[OF step] by (simp only: eval)
      next
        case None
        show ?thesis
        proof (cases "x \<le> 1")
          case True
          have step: "deterministic_phi_next ps (Enter d x # S,M) =
              PhiContinue (S,M((d,x) \<mapsto> x))"
            using outer inner None True by simp
          have eval: "snd (deterministic_phi_eval ps d x M) = M((d,x) \<mapsto> x)"
            using outer inner None True by simp
          show ?thesis using deterministic_phi_moves_one[OF step] by (simp only: eval)
        next
          case False
          let ?left = "deterministic_phi_eval ps ?child x M"
          let ?right = "deterministic_phi_eval ps ?child (x div ?q) (snd ?left)"
          let ?v = "fst ?left - fst ?right"
          let ?final = "(snd ?right)((d,x) \<mapsto> ?v)"
          let ?tail = "Finish d x # S"
          have expand: "deterministic_phi_moves ps (Enter d x # S,M)
              (Enter ?child x # Enter ?child (x div ?q) # ?tail,M)"
            by (rule deterministic_phi_moves_one)
              (use outer inner None False in simp)
          have left_run: "deterministic_phi_moves ps
              (Enter ?child x # Enter ?child (x div ?q) # ?tail,M)
              (Enter ?child (x div ?q) # ?tail,snd ?left)"
            by (rule less.IH[OF child_less, where x=x and M=M and
                  S="Enter ?child (x div ?q) # ?tail"])
              (use less.prems child_depth factors in auto)
          have left_correct: "fst ?left = numerical_Phi ps ?child x \<and>
              valid_phi_store ps (snd ?left) \<and>
              store_extends M (snd ?left)"
            by (rule deterministic_phi_eval_correct[OF less.prems(1) child_depth factors])
          have right_run: "deterministic_phi_moves ps
              (Enter ?child (x div ?q) # ?tail,snd ?left)
              (?tail,snd ?right)"
            by (rule less.IH[OF child_less])
              (use left_correct child_depth factors in auto)
          have right_correct:
              "fst ?right = numerical_Phi ps ?child (x div ?q) \<and>
               valid_phi_store ps (snd ?right) \<and>
               store_extends (snd ?left) (snd ?right)"
            by (rule deterministic_phi_eval_correct)
              (use left_correct child_depth factors in auto)
          have left_root: "snd ?left (?child,x) = Some (fst ?left)"
            by (rule deterministic_phi_eval_stores_root)
          have left_preserved: "snd ?right (?child,x) = Some (fst ?left)"
            using right_correct left_root by (auto simp: store_extends_def)
          have right_root:
              "snd ?right (?child,x div ?q) = Some (fst ?right)"
            by (rule deterministic_phi_eval_stores_root)
          have finish: "deterministic_phi_moves ps (?tail,snd ?right) (S,?final)"
            by (rule deterministic_phi_moves_one)
              (use outer inner left_preserved right_root in simp)
          have evaluation: "snd (deterministic_phi_eval ps d x M) = ?final"
            using outer inner None False
            by (simp only: deterministic_phi_eval.simps option.simps if_False
                Let_def fst_conv snd_conv)
          have through_left: "deterministic_phi_moves ps (Enter d x # S,M)
              (Enter ?child (x div ?q) # ?tail,snd ?left)"
            by (rule deterministic_phi_moves_trans[OF expand left_run])
          have through_right: "deterministic_phi_moves ps (Enter d x # S,M)
              (?tail,snd ?right)"
            by (rule deterministic_phi_moves_trans[OF through_left right_run])
          have completed: "deterministic_phi_moves ps (Enter d x # S,M)
              (S,?final)"
            by (rule deterministic_phi_moves_trans[OF through_right finish])
          show ?thesis using completed by (simp only: evaluation)
        qed
      qed
    qed
  qed
qed

corollary deterministic_phi_worklist_completes:
  fixes x :: nat
  assumes valid: "valid_phi_store ps M"
    and depth: "d \<le> length ps"
    and factors: "\<forall>p\<in>set ps. 2 \<le> p"
  defines "M' \<equiv> snd (deterministic_phi_eval ps d x M)"
  shows "deterministic_phi_moves ps ([Enter d x],M) ([],M')"
    "deterministic_phi_next ps ([],M') = PhiComplete M'"
    "M' (d,x) = Some (numerical_Phi ps d x)"
    "valid_phi_store ps M'"
    "store_extends M M'"
proof -
  have correct: "fst (deterministic_phi_eval ps d x M) = numerical_Phi ps d x \<and>
      valid_phi_store ps M' \<and> store_extends M M'"
    using deterministic_phi_eval_correct[OF valid depth factors, of x]
    unfolding M'_def .
  show "deterministic_phi_moves ps ([Enter d x],M) ([],M')"
    using deterministic_phi_worklist_reaches_evaluator[OF valid depth factors,
      of x "[]"] by (simp add: M'_def)
  show "deterministic_phi_next ps ([],M') = PhiComplete M'" by simp
  show "M' (d,x) = Some (numerical_Phi ps d x)"
    using deterministic_phi_eval_stores_root[of ps d x M] correct
    by (simp add: M'_def)
  show "valid_phi_store ps M'" using correct by blast
  show "store_extends M M'" using correct by blast
qed

text \<open>The repeated-step theorem proves that the deterministic frame
machine empties its worklist without a missing dependency, returns the exact
root, preserves memo validity and retains every pre-existing exact entry.  The
remaining cross-language simulation must relate Python's mutable stack loop to
@{const deterministic_phi_next}, including its root-only shared lookup,
resource exceptions and cleanup.\<close>

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms deterministic_worklist_cached_reuse
      deterministic_worklist_small_input
      deterministic_worklist_depth_one_shortcut
      deterministic_worklist_expand deterministic_worklist_finish_exact
      deterministic_phi_eval_stores_root
      deterministic_phi_worklist_reaches_evaluator
      deterministic_phi_worklist_completes}) then ()
    else error "Deterministic prime worklist refinement depends on an oracle";
\<close>

end
