theory Prime_Deterministic_Phi_Refinement
  imports "Prime_Wheel_Bridge.Prime_Wheel_Executor"
    "Prime_Wheel_Bridge.Prime_Wheel_Skew_Actions"
begin

text \<open>This evaluator mirrors the arithmetic part of
\<open>CoprimeRankDAG.count\<close>: inspect the requested memo key first, use the
small-input and depth-one shortcuts, and otherwise evaluate the left child
before the divided right child.  Resource limits, shared-cache leases and
Python handle authority are deliberately outside this pure finite evaluator.\<close>

fun deterministic_phi_eval ::
    "nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> phi_store \<Rightarrow>
      nat \<times> phi_store" where
  "deterministic_phi_eval ps 0 x M =
    (case M (0,x) of Some v \<Rightarrow> (v,M)
     | None \<Rightarrow> (x,M((0,x) \<mapsto> x)))"
| "deterministic_phi_eval ps (Suc 0) x M =
    (case M (Suc 0,x) of Some v \<Rightarrow> (v,M)
     | None \<Rightarrow>
       let v = (if x \<le> 1 then x else x - x div (ps!0))
       in (v,M((Suc 0,x) \<mapsto> v)))"
| "deterministic_phi_eval ps (Suc (Suc d)) x M =
    (case M (Suc (Suc d),x) of Some v \<Rightarrow> (v,M)
     | None \<Rightarrow>
       if x \<le> 1 then (x,M((Suc (Suc d),x) \<mapsto> x))
       else
         let left = deterministic_phi_eval ps (Suc d) x M;
             right = deterministic_phi_eval ps (Suc d)
               (x div (ps!(Suc d))) (snd left);
             v = fst left - fst right
         in (v,(snd right)((Suc (Suc d),x) \<mapsto> v)))"

lemma numerical_Phi_zero [simp]: "numerical_Phi ps d 0 = 0"
  by (induct d) simp_all

lemma numerical_Phi_small_input:
  assumes depth: "d \<le> length ps"
    and factors: "\<forall>p\<in>set ps. 2 \<le> p"
    and small: "x \<le> 1"
  shows "numerical_Phi ps d x = x"
  using depth
proof (induct d)
  case 0
  then show ?case by simp
next
  case (Suc d)
  have index: "d < length ps" using Suc.prems by simp
  have factor: "2 \<le> ps!d" using factors index by simp
  have quotient: "x div (ps!d) = 0" using small factor
    by (cases x) auto
  show ?case using Suc.hyps Suc.prems quotient by simp
qed

lemma deterministic_phi_cached_root:
  assumes "M (d,x) = Some v"
  shows "deterministic_phi_eval ps d x M = (v,M)"
proof (cases d)
  case 0
  then show ?thesis using assms by simp
next
  case (Suc d')
  then show ?thesis using assms by (cases d') simp_all
qed

lemma deterministic_phi_depth_one_shortcut:
  assumes "M (1,x) = None" "1 < x"
  shows "deterministic_phi_eval ps 1 x M =
    (x - x div (ps!0), M((1,x) \<mapsto> x - x div (ps!0)))"
  using assms by (simp add: Let_def)

theorem deterministic_phi_eval_correct:
  assumes valid: "valid_phi_store ps M"
    and depth: "d \<le> length ps"
    and factors: "\<forall>p\<in>set ps. 2 \<le> p"
  shows "fst (deterministic_phi_eval ps d x M) = numerical_Phi ps d x \<and>
    valid_phi_store ps (snd (deterministic_phi_eval ps d x M)) \<and>
    store_extends M (snd (deterministic_phi_eval ps d x M))"
  using valid depth
proof (induction d arbitrary: x M rule: less_induct)
  case (less d)
  show ?case
  proof (cases d)
    case 0
    show ?thesis
    proof (cases "M (0,x)")
      case None
      have updated_valid: "valid_phi_store ps (M((0,x) \<mapsto> x))"
        by (rule valid_phi_store_update[OF less.prems(1)]) (use 0 less.prems in auto)
      have extends: "store_extends M (M((0,x) \<mapsto> x))"
        by (rule exact_update_extends[OF less.prems(1)]) (use 0 less.prems in auto)
      show ?thesis using 0 None updated_valid extends
        by (simp add: fun_upd_def)
    next
      case (Some cached)
      have exact: "cached = x"
        using valid_phi_store_lookup[OF less.prems(1) Some] 0 by simp
      show ?thesis using 0 Some exact less.prems(1)
        by (simp add: store_extends_def)
    qed
  next
    case outer: (Suc e)
    show ?thesis
    proof (cases e)
      case zero: 0
      have one_depth: "1 \<le> length ps" using less.prems outer zero by simp
      show ?thesis
      proof (cases "M (1,x)")
        case (Some cached)
        have exact: "cached = numerical_Phi ps 1 x"
          using valid_phi_store_lookup[OF less.prems(1) Some] by simp
        show ?thesis using outer zero Some exact less.prems(1)
          by (simp add: store_extends_def)
      next
        case None
        show ?thesis
        proof (cases "x \<le> 1")
          case True
          have exact: "x = numerical_Phi ps 1 x"
            using numerical_Phi_small_input[OF one_depth factors True] by simp
          have updated_valid: "valid_phi_store ps (M((1,x) \<mapsto> x))"
            by (rule valid_phi_store_update[OF less.prems(1) one_depth exact])
          have extends: "store_extends M (M((1,x) \<mapsto> x))"
            by (rule exact_update_extends[OF less.prems(1) one_depth exact])
          show ?thesis using outer zero None True exact updated_valid extends
            by (simp add: Let_def fun_upd_def)
        next
          case False
          let ?value = "x - x div (ps!0)"
          have exact: "?value = numerical_Phi ps 1 x"
            by (simp add: depth_one_shortcut_exact)
          have updated_valid: "valid_phi_store ps (M((1,x) \<mapsto> ?value))"
            by (rule valid_phi_store_update[OF less.prems(1) one_depth exact])
          have extends: "store_extends M (M((1,x) \<mapsto> ?value))"
            by (rule exact_update_extends[OF less.prems(1) one_depth exact])
          show ?thesis using outer zero None False exact updated_valid extends
            by (simp add: Let_def fun_upd_def)
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
        then have exact: "cached = numerical_Phi ps d x"
          using valid_phi_store_lookup[OF less.prems(1) Some] by simp
        show ?thesis
          using Some exact less.prems outer inner
          by (simp_all add: store_extends_def)
      next
        case None
        show ?thesis
        proof (cases "x \<le> 1")
          case True
          have exact: "numerical_Phi ps d x = x"
            by (rule numerical_Phi_small_input[OF less.prems(2) factors True])
          show ?thesis
            using None True exact less.prems outer inner
              valid_phi_store_update[of ps M d x x]
              exact_update_extends[of ps M d x x]
            by (simp_all add: Let_def fun_upd_def)
        next
          case False
          let ?left = "deterministic_phi_eval ps ?child x M"
          let ?right = "deterministic_phi_eval ps ?child (x div ?q) (snd ?left)"
          have left_value: "fst ?left = numerical_Phi ps ?child x"
            and left_valid: "valid_phi_store ps (snd ?left)"
            and left_extends: "store_extends M (snd ?left)"
            using less.IH[OF child_less, where x=x and M=M]
              less.prems child_depth factors
            by blast+
          have right_value:
              "fst ?right = numerical_Phi ps ?child (x div ?q)"
            and right_valid: "valid_phi_store ps (snd ?right)"
            and right_extends: "store_extends (snd ?left) (snd ?right)"
            using less.IH[OF child_less, where x="x div ?q" and M="snd ?left"]
              left_valid child_depth factors
            by blast+
          let ?value = "fst ?left - fst ?right"
          let ?final = "(snd ?right)((d,x) \<mapsto> ?value)"
          have root_value: "?value = numerical_Phi ps d x"
            using left_value right_value outer inner by simp
          have final_valid: "valid_phi_store ps ?final"
            by (rule valid_phi_store_update[OF right_valid less.prems(2) root_value])
          have right_to_final: "store_extends (snd ?right) ?final"
            by (rule exact_update_extends[OF right_valid less.prems(2) root_value])
          have final_extends: "store_extends M ?final"
            using left_extends right_extends right_to_final
            by (auto simp: store_extends_def)
          have evaluation:
              "deterministic_phi_eval ps d x M = (?value,?final)"
            using None False outer inner
            by (simp only: deterministic_phi_eval.simps option.simps if_False
                Let_def fst_conv snd_conv)
          show ?thesis
            using root_value final_valid final_extends
            by (simp only: evaluation fst_conv snd_conv; blast)
        qed
      qed
    qed
  qed
qed

definition deterministic_fresh_zero_rank ::
    "nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> phi_store
      \<Rightarrow> nat \<times> phi_store" where
  "deterministic_fresh_zero_rank ps parent_depth q width M =
    (let left = deterministic_phi_eval ps parent_depth width M;
         right = deterministic_phi_eval ps parent_depth (width div q) (snd left)
     in (fst left - fst right, snd right))"

theorem deterministic_fresh_zero_rank_correct:
  assumes valid: "valid_phi_store ps M"
    and depth: "parent_depth < length ps"
    and factors: "\<forall>p\<in>set ps. 2 \<le> p"
    and fresh: "q = ps!parent_depth"
  shows "fst (deterministic_fresh_zero_rank ps parent_depth q width M) =
      numerical_Phi ps (Suc parent_depth) width"
    "valid_phi_store ps
      (snd (deterministic_fresh_zero_rank ps parent_depth q width M))"
    "store_extends M
      (snd (deterministic_fresh_zero_rank ps parent_depth q width M))"
proof -
  let ?left = "deterministic_phi_eval ps parent_depth width M"
  let ?right = "deterministic_phi_eval ps parent_depth (width div q) (snd ?left)"
  have parent_depth: "parent_depth \<le> length ps" using depth by simp
  have left_value: "fst ?left = numerical_Phi ps parent_depth width"
    and left_valid: "valid_phi_store ps (snd ?left)"
    and left_extends: "store_extends M (snd ?left)"
    using deterministic_phi_eval_correct[OF valid parent_depth factors, of width]
    by blast+
  have right_value:
      "fst ?right = numerical_Phi ps parent_depth (width div q)"
    and right_valid: "valid_phi_store ps (snd ?right)"
    and right_extends: "store_extends (snd ?left) (snd ?right)"
    using deterministic_phi_eval_correct[OF left_valid parent_depth factors,
      of "width div q"] by blast+
  show "fst (deterministic_fresh_zero_rank ps parent_depth q width M) =
      numerical_Phi ps (Suc parent_depth) width"
    using left_value right_value fresh
    by (simp add: deterministic_fresh_zero_rank_def Let_def)
  show "valid_phi_store ps
      (snd (deterministic_fresh_zero_rank ps parent_depth q width M))"
    using right_valid by (simp add: deterministic_fresh_zero_rank_def Let_def)
  show "store_extends M
      (snd (deterministic_fresh_zero_rank ps parent_depth q width M))"
    using left_extends right_extends
    by (auto simp: deterministic_fresh_zero_rank_def Let_def
        store_extends_def)
qed

corollary deterministic_admitted_fresh_prefix_card:
  assumes prefix: "complete_prime_prefix ps H"
    and depth: "parent_depth < length ps"
    and fresh: "q = ps!parent_depth"
  shows "fst (deterministic_fresh_zero_rank ps parent_depth q width
      (\<lambda>_. None)) =
    card (wheel_sift (rev (take (Suc parent_depth) ps)) {1..width})"
proof -
  have distinct: "distinct ps" and primes: "\<forall>p\<in>set ps. prime p"
    using complete_prime_prefix_distinct_sorted[OF prefix]
      complete_prime_prefix_set[OF prefix] by auto
  have factors: "\<forall>p\<in>set ps. 2 \<le> p"
  proof (intro ballI)
    fix p
    assume member: "p \<in> set ps"
    have "1 < p" by (rule prime_gt_1_nat) (use primes member in blast)
    then show "2 \<le> p" by simp
  qed
  have rank_value: "fst (deterministic_fresh_zero_rank ps parent_depth q width
      (\<lambda>_. None)) = numerical_Phi ps (Suc parent_depth) width"
    by (rule deterministic_fresh_zero_rank_correct(1)[
        OF empty_phi_store_valid depth factors fresh])
  have semantic: "numerical_Phi ps (Suc parent_depth) width =
      card (wheel_sift (rev (take (Suc parent_depth) ps)) {1..width})"
    by (rule numerical_Phi_is_sift_card)
      (use depth distinct primes in auto)
  show ?thesis using rank_value semantic by simp
qed

text \<open>The final corollary consumes a source-derived complete consecutive
prime prefix, chooses its indexed fresh factor, and returns the exact finite
prefix survivor count used by the zero-phase successor consumer.  It does not
assert that an arbitrary factor word is prime or consecutive.  A remaining
cross-language refinement must relate Python memo dictionaries and
\<open>PrimeSuccessorActionID\<close> nodes to this function, and must separately
verify scheduler authority, budgets, leases, general residue ports, and
rank/select traversal.\<close>

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms numerical_Phi_small_input deterministic_phi_cached_root
      deterministic_phi_depth_one_shortcut deterministic_phi_eval_correct
      deterministic_fresh_zero_rank_correct
      deterministic_admitted_fresh_prefix_card}) then ()
    else error "Deterministic prime Phi refinement depends on an oracle";
\<close>

end
