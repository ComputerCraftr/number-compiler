theory Collatz_Physical_Double_Accumulator
  imports Collatz_Boundary_Macros
begin

text \<open>The joint field's successor sum also determines the exact ordered
physical credits and debits.  Every normalized successor is one division
debit; an odd branch contributes its preceding \<open>3*x+1\<close> credit.  The
optional final odd tick is a separate pending event and contributes no
division debit.\<close>

fun collatz_guarded_normalized_credit_word :: "bool list \<Rightarrow> nat \<Rightarrow> nat" where
  "collatz_guarded_normalized_credit_word [] source = 0"
| "collatz_guarded_normalized_credit_word (branch # bits) source =
    (if branch then 2*source+1 else 0) +
      collatz_guarded_normalized_credit_word bits
        (collatz_guarded_normalized_source_step branch source)"

theorem collatz_guarded_normalized_double_accumulator_exact:
  assumes admitted: "collatz_guarded_normalized_word_admitted bits source"
  shows "source + collatz_guarded_normalized_credit_word bits source =
    collatz_guarded_normalized_word_endpoint bits source +
      sum_list (collatz_guarded_normalized_successors bits source)"
using admitted
proof (induction bits arbitrary: source)
  case Nil
  then show ?case by simp
next
  case (Cons branch bits)
  have split_guard:
    "branch = odd source \<and>
      collatz_guarded_normalized_word_admitted bits
        (collatz_guarded_normalized_source_step branch source)"
    using Cons.prems[unfolded
      collatz_guarded_normalized_word_admitted.simps] .
  have branch_eq: "branch = odd source" using split_guard by blast
  have tail_admitted:
    "collatz_guarded_normalized_word_admitted bits
      (collatz_guarded_normalized_source_step branch source)"
    using split_guard by blast
  let ?next = "collatz_guarded_normalized_source_step branch source"
  have atom_credit: "source + (if branch then 2*source+1 else 0) = 2*?next"
  proof (cases branch)
    case True
    have odd_source: "odd source" using branch_eq True by simp
    have even_intermediate: "even (3*source+1)" using odd_source by simp
    have next_value: "?next = (3*source+1) div 2"
      using odd_source branch_eq True
      by (simp add: collatz_guarded_true_step_exact)
    obtain q where q: "3*source+1 = 2*q"
      using even_intermediate by (rule evenE)
    show ?thesis using next_value q True by (simp add: algebra_simps)
  next
    case False
    have even_source: "even source" using branch_eq False by simp
    have next_value: "?next = source div 2"
      using even_source branch_eq False
      by (simp add: collatz_guarded_false_step_exact)
    obtain q where q: "source = 2*q"
      using even_source by (auto elim: evenE)
    show ?thesis using next_value q False by (simp add: algebra_simps)
  qed
  have tail:
    "?next + collatz_guarded_normalized_credit_word bits ?next =
      collatz_guarded_normalized_word_endpoint bits ?next +
        sum_list (collatz_guarded_normalized_successors bits ?next)"
    by (rule Cons.IH[OF tail_admitted])
  show ?case
    using atom_credit tail
    by (simp only: collatz_guarded_normalized_word_endpoint.simps
        collatz_guarded_normalized_successors.simps
        collatz_guarded_normalized_credit_word.simps sum_list.Cons; arith)
qed

corollary collatz_guarded_normalized_credit_closed_form:
  assumes admitted: "collatz_guarded_normalized_word_admitted bits source"
  shows "of_nat (collatz_guarded_normalized_credit_word bits source) =
      (of_nat (sum_list (collatz_guarded_normalized_successors bits source)) :: int) +
      of_nat (collatz_guarded_normalized_word_endpoint bits source) - of_nat source"
proof -
  have natural_conservation:
    "source + collatz_guarded_normalized_credit_word bits source =
      collatz_guarded_normalized_word_endpoint bits source +
        sum_list (collatz_guarded_normalized_successors bits source)"
    by (rule collatz_guarded_normalized_double_accumulator_exact[OF admitted])
  have cast_conservation:
    "of_nat (source + collatz_guarded_normalized_credit_word bits source) =
      of_nat (collatz_guarded_normalized_word_endpoint bits source +
        sum_list (collatz_guarded_normalized_successors bits source))"
    using natural_conservation by simp
  have conservation:
    "(of_nat source :: int) +
      of_nat (collatz_guarded_normalized_credit_word bits source) =
      of_nat (collatz_guarded_normalized_word_endpoint bits source) +
      of_nat (sum_list (collatz_guarded_normalized_successors bits source))"
    using cast_conservation by (simp only: of_nat_add)
  show ?thesis using conservation by linarith
qed

theorem collatz_guarded_joint_action_double_accumulator_exact:
  assumes admitted: "collatz_guarded_normalized_word_admitted bits source"
  shows "(of_nat (collatz_guarded_normalized_credit_word bits source) :: rat) =
      collatz_joint_dyadic_sum (collatz_joint_dyadic_word bits) (of_nat source) +
      collatz_joint_dyadic_endpoint (collatz_joint_dyadic_word bits) (of_nat source) -
      of_nat source"
proof -
  have natural_conservation:
    "source + collatz_guarded_normalized_credit_word bits source =
      collatz_guarded_normalized_word_endpoint bits source +
        sum_list (collatz_guarded_normalized_successors bits source)"
    by (rule collatz_guarded_normalized_double_accumulator_exact[OF admitted])
  have cast_conservation:
    "of_nat (source + collatz_guarded_normalized_credit_word bits source) =
      of_nat (collatz_guarded_normalized_word_endpoint bits source +
        sum_list (collatz_guarded_normalized_successors bits source))"
    using natural_conservation by simp
  have conservation:
    "(of_nat source :: rat) +
      of_nat (collatz_guarded_normalized_credit_word bits source) =
      of_nat (collatz_guarded_normalized_word_endpoint bits source) +
      of_nat (sum_list (collatz_guarded_normalized_successors bits source))"
    using cast_conservation by (simp only: of_nat_add)
  have endpoint:
    "collatz_joint_dyadic_endpoint (collatz_joint_dyadic_word bits) (of_nat source) =
      of_nat (collatz_guarded_normalized_word_endpoint bits source)"
    using collatz_guarded_normalized_word_refines_physical[OF admitted]
    by blast
  have total:
    "collatz_joint_dyadic_sum (collatz_joint_dyadic_word bits) (of_nat source) =
      of_nat (sum_list (collatz_guarded_normalized_successors bits source))"
    by (rule collatz_guarded_joint_action_sums_source_successors[OF admitted])
  show ?thesis using conservation endpoint total by linarith
qed

theorem collatz_guarded_normalized_double_accumulator_pending_exact:
  assumes admitted: "collatz_guarded_normalized_word_admitted bits source"
    and pending: "pending = odd (collatz_guarded_normalized_word_endpoint bits source)"
  shows "source + collatz_guarded_normalized_credit_word bits source +
      (if pending then 2*collatz_guarded_normalized_word_endpoint bits source+1 else 0) =
    (if pending then
      3*collatz_guarded_normalized_word_endpoint bits source+1
     else collatz_guarded_normalized_word_endpoint bits source) +
      sum_list (collatz_guarded_normalized_successors bits source)"
proof -
  have conservation:
    "source + collatz_guarded_normalized_credit_word bits source =
      collatz_guarded_normalized_word_endpoint bits source +
        sum_list (collatz_guarded_normalized_successors bits source)"
    by (rule collatz_guarded_normalized_double_accumulator_exact[OF admitted])
  show ?thesis
  proof (cases pending)
    case False
    then show ?thesis using conservation by simp
  next
    case True
    then show ?thesis using conservation by arith
  qed
qed

theorem collatz_guarded_joint_action_double_accumulator_pending_exact:
  assumes admitted: "collatz_guarded_normalized_word_admitted bits source"
    and pending: "pending = odd (collatz_guarded_normalized_word_endpoint bits source)"
  shows "(of_nat (collatz_guarded_normalized_credit_word bits source) :: rat) +
      (if pending then
        2*collatz_joint_dyadic_endpoint (collatz_joint_dyadic_word bits) (of_nat source) + 1
       else 0) =
    (if pending then
      3*collatz_joint_dyadic_endpoint (collatz_joint_dyadic_word bits) (of_nat source) + 1
     else collatz_joint_dyadic_endpoint (collatz_joint_dyadic_word bits) (of_nat source)) +
      collatz_joint_dyadic_sum (collatz_joint_dyadic_word bits) (of_nat source) -
      of_nat source"
proof -
  have complete:
    "(of_nat (collatz_guarded_normalized_credit_word bits source) :: rat) =
      collatz_joint_dyadic_sum (collatz_joint_dyadic_word bits) (of_nat source) +
      collatz_joint_dyadic_endpoint (collatz_joint_dyadic_word bits) (of_nat source) -
      of_nat source"
    by (rule collatz_guarded_joint_action_double_accumulator_exact[OF admitted])
  have endpoint:
    "collatz_joint_dyadic_endpoint (collatz_joint_dyadic_word bits) (of_nat source) =
      of_nat (collatz_guarded_normalized_word_endpoint bits source)"
    using collatz_guarded_normalized_word_refines_physical[OF admitted]
    by blast
  show ?thesis
  proof (cases pending)
    case False
    then show ?thesis using complete endpoint by simp
  next
    case True
    then show ?thesis using complete endpoint by (simp add: algebra_simps)
  qed
qed

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms collatz_guarded_normalized_double_accumulator_exact
      collatz_guarded_normalized_credit_closed_form
      collatz_guarded_joint_action_double_accumulator_exact
      collatz_guarded_normalized_double_accumulator_pending_exact
      collatz_guarded_joint_action_double_accumulator_pending_exact}) then ()
    else error "Collatz double-accumulator refinement depends on an oracle";
\<close>


end
