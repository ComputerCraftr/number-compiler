theory Collatz_Diagonal_Source_Window_Refinement
  imports Collatz_Physical_Double_Accumulator
    Collatz_Skew_Cylinder_Temporal_Squaring
begin

text \<open>A normalized word is admitted at every source in a sufficiently
deep dyadic cylinder when its number of normalized symbols fits inside that
cylinder. Each symbol consumes one low source bit: an odd symbol is a
two-physical-tick macro whose net affine displacement still consumes one
bit. This is the source-selected producer bridge: the same checked joint
action can be applied at the source and at its lifted window without
reconstructing or guessing a future parity word.\<close>

text \<open>The bounded endpoint-only producer scans the low source residue and
charges one physical tick for an even normalized symbol and two for an odd
symbol. It stops before a symbol that exceeds the remaining physical budget.
The recursive selector below is the mathematical counterpart of that scan;
its input is only the low-bit representative, not a supplied parity word.
For naturals, take_bit is the same low-bit mask as reducing modulo the
corresponding power of two. This theory covers the endpoint-only action;
optional field sums, saved prefixes, and parity-mask packing are outside this
producer refinement.\<close>

fun collatz_bounded_source_window_word :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool list" where
  "collatz_bounded_source_window_word 0 low budget = []"
| "collatz_bounded_source_window_word (Suc fuel) low budget =
    (if even low then
      (if 0 < budget then False #
        collatz_bounded_source_window_word fuel (low div 2) (budget - 1)
       else [])
     else if 1 < budget then
      True # collatz_bounded_source_window_word fuel
        ((3*low+1) div 2) (budget - 2)
     else [])"

definition collatz_source_window_physical_cost :: "bool list \<Rightarrow> nat" where
  "collatz_source_window_physical_cost bits =
    length bits + count_list bits True"

fun collatz_source_window_accumulate ::
    "bool list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
      nat \<times> (nat \<times> nat)" where
  "collatz_source_window_accumulate [] steps gain acc_offset =
    (steps, (gain, acc_offset))"
| "collatz_source_window_accumulate (branch # bits) steps gain acc_offset =
    collatz_source_window_accumulate bits (Suc steps)
      (if branch then 3*gain else gain)
      (if branch then 3*acc_offset + 2^steps else acc_offset)"

lemma collatz_bounded_source_window_word_admitted:
  "collatz_guarded_normalized_word_admitted
      (collatz_bounded_source_window_word fuel low budget) low"
proof (induction fuel arbitrary: low budget)
  case 0
  then show ?case by simp
next
  case (Suc fuel)
  note fuel_IH = Suc.IH
  show ?case
  proof (cases "even low")
    case True
    then show ?thesis
    proof (cases budget)
      case 0
      then show ?thesis using True by simp
    next
      case (Suc remaining)
      have tail:
        "collatz_guarded_normalized_word_admitted
          (collatz_bounded_source_window_word fuel (low div 2) remaining)
          (low div 2)"
        by (rule fuel_IH)
      show ?thesis using True Suc tail
        by (simp add: collatz_guarded_normalized_source_step_def
            collatz_guarded_false_step_exact physical_collatz_def)
    qed
  next
    case False
    then have low_odd: "odd low" by simp
    show ?thesis
    proof (cases budget)
      case 0
      then show ?thesis using False by simp
    next
      case (Suc remaining)
      note budget_Suc = Suc
      show ?thesis
      proof (cases remaining)
        case 0
        then show ?thesis using False budget_Suc by simp
      next
        case (Suc rest)
        have tail:
          "collatz_guarded_normalized_word_admitted
            (collatz_bounded_source_window_word fuel
              ((3*low+1) div 2) rest)
            ((3*low+1) div 2)"
          by (rule fuel_IH)
        have next_source:
          "collatz_guarded_normalized_source_step True low =
            (3*low+1) div 2"
          by (rule collatz_guarded_true_step_exact[OF low_odd])
        show ?thesis using low_odd budget_Suc Suc tail next_source
          by (simp add: collatz_guarded_normalized_word_admitted.simps)
      qed
    qed
  qed
qed

lemma collatz_bounded_source_window_word_length:
  "length (collatz_bounded_source_window_word fuel low budget) \<le> fuel"
proof (induction fuel arbitrary: low budget)
  case 0
  then show ?case by simp
next
  case (Suc fuel)
  note fuel_IH = Suc.IH
  show ?case
  proof (cases "even low")
    case True
    then show ?thesis
    proof (cases budget)
      case 0
      then show ?thesis using True by simp
    next
      case (Suc remaining)
      have tail:
        "length (collatz_bounded_source_window_word fuel (low div 2) remaining)
          \<le> fuel"
        by (rule fuel_IH)
      show ?thesis using True Suc tail by simp
    qed
  next
    case False
    show ?thesis
    proof (cases budget)
      case 0
      then show ?thesis using False by simp
    next
      case (Suc remaining)
      note budget_Suc = Suc
      show ?thesis
      proof (cases remaining)
        case 0
        then show ?thesis using False budget_Suc by simp
      next
        case (Suc rest)
        have tail:
          "length (collatz_bounded_source_window_word fuel
            ((3*low+1) div 2) rest) \<le> fuel"
          by (rule fuel_IH)
        show ?thesis using False budget_Suc Suc tail by simp
      qed
    qed
  qed
qed

lemma collatz_bounded_source_window_word_cost:
  "collatz_source_window_physical_cost
      (collatz_bounded_source_window_word fuel low budget) \<le> budget"
proof (induction fuel arbitrary: low budget)
  case 0
  then show ?case by (simp add: collatz_source_window_physical_cost_def)
next
  case (Suc fuel)
  note fuel_IH = Suc.IH
  show ?case
  proof (cases "even low")
    case True
    then show ?thesis
    proof (cases budget)
      case 0
      then show ?thesis using True
        by (simp add: collatz_source_window_physical_cost_def)
    next
      case (Suc remaining)
      have tail:
        "collatz_source_window_physical_cost
          (collatz_bounded_source_window_word fuel (low div 2) remaining)
          \<le> remaining"
        by (rule fuel_IH)
      show ?thesis using True Suc tail
        by (simp add: collatz_source_window_physical_cost_def; arith)
    qed
  next
    case False
    show ?thesis
    proof (cases budget)
      case 0
      then show ?thesis using False
        by (simp add: collatz_source_window_physical_cost_def)
    next
      case (Suc remaining)
      note budget_Suc = Suc
      show ?thesis
      proof (cases remaining)
        case 0
        then show ?thesis using False budget_Suc
          by (simp add: collatz_source_window_physical_cost_def)
      next
        case (Suc rest)
        have tail:
          "collatz_source_window_physical_cost
            (collatz_bounded_source_window_word fuel
              ((3*low+1) div 2) rest) \<le> rest"
          by (rule fuel_IH)
        show ?thesis using False budget_Suc Suc tail
          by (simp add: collatz_source_window_physical_cost_def; arith)
      qed
    qed
  qed
qed

lemma collatz_source_window_accumulate_refines_word:
  "collatz_source_window_accumulate bits steps gain acc_offset =
    (steps + length bits,
      (joint_dyadic_gain (collatz_joint_dyadic_word bits) * gain,
       joint_dyadic_gain (collatz_joint_dyadic_word bits) * acc_offset +
         2^steps * joint_dyadic_offset (collatz_joint_dyadic_word bits)))"
proof (induction bits arbitrary: steps gain acc_offset)
  case Nil
  then show ?case
    by (simp add: collatz_joint_dyadic_identity_def)
next
  case (Cons branch bits)
  show ?case
    using Cons.IH[of "Suc steps"
      "if branch then 3*gain else gain"
      "if branch then 3*acc_offset + 2^steps else acc_offset"]
    by (cases branch)
      (simp_all add: collatz_joint_dyadic_then_def
        collatz_joint_dyadic_atom_def algebra_simps)
qed

corollary collatz_source_window_accumulate_exact:
  "collatz_source_window_accumulate bits 0 1 0 =
    (length bits,
      (joint_dyadic_gain (collatz_joint_dyadic_word bits),
       joint_dyadic_offset (collatz_joint_dyadic_word bits)))"
  using collatz_source_window_accumulate_refines_word[of bits 0 1 0]
  by simp

lemma collatz_guarded_normalized_step_cylinder:
  assumes branch: "branch = odd source"
      and precision: "0 < p"
  shows "collatz_guarded_normalized_source_step branch
        (source + 2^p*k) =
      collatz_guarded_normalized_source_step branch source +
        2^(p-1) * (if branch then 3*k else k)"
proof (cases branch)
  case False
  have source_even: "even source" using branch False by simp
  have lifted:
    "physical_collatz (source + 2^p*k) =
      physical_collatz source + 2^(p-1)*k"
    by (rule physical_collatz_even_cylinder_step[OF source_even precision])
  show ?thesis using lifted False
    by (simp add: collatz_guarded_normalized_source_step_def)
next
  case True
  have source_odd: "odd source" using branch True by simp
  let ?middle = "physical_collatz source"
  have middle_even: "even ?middle"
    using source_odd by (simp add: physical_collatz_def)
  have first:
    "physical_collatz (source + 2^p*k) =
      ?middle + 2^p*(3*k)"
    by (rule physical_collatz_odd_cylinder_step[OF source_odd precision])
  have second:
    "physical_collatz (?middle + 2^p*(3*k)) =
      physical_collatz ?middle + 2^(p-1)*(3*k)"
    by (rule physical_collatz_even_cylinder_step[OF middle_even precision])
  have iterate_two:
    "(physical_collatz ^^ 2) x = physical_collatz (physical_collatz x)"
    for x by (simp add: numeral_2_eq_2)
  show ?thesis
    using first second True
    by (simp add: collatz_guarded_normalized_source_step_def iterate_two)
qed

lemma collatz_guarded_normalized_window_admitted_lift:
  assumes admitted:
      "collatz_guarded_normalized_word_admitted bits source"
      and duration:
      "length bits \<le> p"
  shows "collatz_guarded_normalized_word_admitted bits
      (source + 2^p*k)"
  using admitted duration
proof (induction bits arbitrary: source p k)
  case Nil
  then show ?case by simp
next
  case (Cons branch bits)
  have split_guard:
    "branch = odd source \<and>
      collatz_guarded_normalized_word_admitted bits
        (collatz_guarded_normalized_source_step branch source)"
    using Cons.prems(1)[unfolded
      collatz_guarded_normalized_word_admitted.simps] .
  have branch_source: "branch = odd source"
    using split_guard by blast
  have tail_admitted:
    "collatz_guarded_normalized_word_admitted bits
      (collatz_guarded_normalized_source_step branch source)"
    using split_guard by blast
  have duration_split: "Suc (length bits) \<le> p"
    using Cons.prems(2) by simp
  have positive: "0 < p"
    using duration_split by arith
  have tail_precision: "length bits \<le> p-1"
    using duration_split positive by arith
  have lifted_parity:
    "odd (source + 2^p*k) = odd source"
  proof -
    obtain q where p: "p = Suc q"
      using positive by (cases p) auto
    show ?thesis using p by simp
  qed
  let ?next = "collatz_guarded_normalized_source_step branch source"
  let ?lift = "(if branch then 3*k else k)"
  have lifted_step:
    "collatz_guarded_normalized_source_step branch (source + 2^p*k) =
      ?next + 2^(p-1)*?lift"
    by (rule collatz_guarded_normalized_step_cylinder[OF branch_source positive])
  have tail_lifted:
    "collatz_guarded_normalized_word_admitted bits
        (?next + 2^(p-1)*?lift)"
    by (rule Cons.IH[OF tail_admitted tail_precision])
  show ?case using branch_source lifted_parity lifted_step tail_lifted
    by (simp only: collatz_guarded_normalized_word_admitted.simps)
qed

theorem collatz_guarded_normalized_source_window_refines_action:
  fixes p k :: nat
  assumes admitted:
      "collatz_guarded_normalized_word_admitted bits source"
      and duration:
      "length bits \<le> p"
  defines "lifted \<equiv> source + 2^p*k"
  shows "collatz_guarded_normalized_word_admitted bits lifted"
    and "collatz_joint_dyadic_endpoint
        (collatz_joint_dyadic_word bits) (of_nat lifted) =
      of_nat (collatz_guarded_normalized_word_endpoint bits lifted)"
    and "collatz_joint_dyadic_sum
        (collatz_joint_dyadic_word bits) (of_nat lifted) =
      of_nat (sum_list (collatz_guarded_normalized_successors bits lifted))"
    and "collatz_guarded_normalized_word_endpoint bits lifted =
      (physical_collatz ^^ (length bits + count_list bits True)) lifted"
proof -
  have lifted_admitted:
    "collatz_guarded_normalized_word_admitted bits lifted"
    unfolding lifted_def
    by (rule collatz_guarded_normalized_window_admitted_lift
      [OF admitted duration])
  show "collatz_guarded_normalized_word_admitted bits lifted"
    by (rule lifted_admitted)
  show "collatz_joint_dyadic_endpoint
      (collatz_joint_dyadic_word bits) (of_nat lifted) =
    of_nat (collatz_guarded_normalized_word_endpoint bits lifted)"
    using collatz_guarded_normalized_word_refines_physical[OF lifted_admitted]
    by blast
  show "collatz_joint_dyadic_sum
      (collatz_joint_dyadic_word bits) (of_nat lifted) =
    of_nat (sum_list (collatz_guarded_normalized_successors bits lifted))"
    by (rule collatz_guarded_joint_action_sums_source_successors[OF lifted_admitted])
  show "collatz_guarded_normalized_word_endpoint bits lifted =
      (physical_collatz ^^ (length bits + count_list bits True)) lifted"
    using collatz_guarded_normalized_word_refines_physical[OF lifted_admitted]
    by blast
qed

theorem collatz_bounded_source_window_producer_exact:
  fixes source budget max_normalized limit low spent target phase :: nat
    and bits :: "bool list"
    and pending :: bool
  assumes source_positive: "0 < source"
    and cap_positive: "0 < max_normalized"
  defines "limit \<equiv> min max_normalized budget"
    and "low \<equiv> take_bit limit source"
    and "bits \<equiv> collatz_bounded_source_window_word limit low budget"
    and "spent \<equiv> collatz_source_window_physical_cost bits"
    and "target \<equiv> collatz_guarded_normalized_word_endpoint bits source"
    and "pending \<equiv>
      (spent < budget \<and> budget - spent = 1 \<and> odd target)"
    and "phase \<equiv> (if pending then 1 else 0)"
  shows "collatz_guarded_normalized_word_admitted bits source"
    and "low = source mod 2^limit"
    and "length bits \<le> limit"
    and "spent = length bits + count_list bits True"
    and "spent \<le> budget"
    and "collatz_source_window_accumulate bits 0 1 0 =
      (length bits,
        (joint_dyadic_gain (collatz_joint_dyadic_word bits),
         joint_dyadic_offset (collatz_joint_dyadic_word bits)))"
    and "fst (snd (collatz_source_window_accumulate bits 0 1 0)) * source +
        snd (snd (collatz_source_window_accumulate bits 0 1 0)) =
      2^(fst (collatz_source_window_accumulate bits 0 1 0)) * target"
    and "pending = (spent + 1 = budget \<and> odd target)"
    and "phase = (if spent + 1 = budget \<and> odd target then 1 else 0)"
    and "spent + phase \<le> budget"
    and "(physical_collatz ^^ (spent + phase)) source =
      (if pending then 3*target+1 else target)"
proof -
  have selected_admitted:
    "collatz_guarded_normalized_word_admitted bits low"
    unfolding bits_def low_def
    by (rule collatz_bounded_source_window_word_admitted)
  have selected_length: "length bits \<le> limit"
    unfolding bits_def low_def
    by (rule collatz_bounded_source_window_word_length)
  have selected_cost:
    "collatz_source_window_physical_cost bits \<le> budget"
    unfolding bits_def low_def
    by (rule collatz_bounded_source_window_word_cost)
  have source_decomposition:
    "source = low + 2^limit * (source div 2^limit)"
    unfolding low_def
    using div_mult_mod_eq[of source "2^limit"]
    by (simp add: take_bit_eq_mod add.commute mult.commute)
  have admitted_lift:
    "collatz_guarded_normalized_word_admitted bits
      (low + 2^limit * (source div 2^limit))"
    by (rule collatz_guarded_normalized_window_admitted_lift
      [OF selected_admitted selected_length])
  have admitted:
    "collatz_guarded_normalized_word_admitted bits source"
    using admitted_lift source_decomposition by simp
  have endpoint_exact:
    "target = (physical_collatz ^^
      (length bits + count_list bits True)) source"
    using collatz_guarded_normalized_word_refines_physical[OF admitted]
    by (simp add: target_def)
  have affine:
    "joint_dyadic_gain (collatz_joint_dyadic_word bits) * source +
        joint_dyadic_offset (collatz_joint_dyadic_word bits) =
      2^length bits * target"
    using collatz_guarded_word_affine_endpoint[OF admitted]
    by (simp add: target_def collatz_joint_dyadic_word_steps)
  have accumulator:
    "collatz_source_window_accumulate bits 0 1 0 =
      (length bits,
        (joint_dyadic_gain (collatz_joint_dyadic_word bits),
         joint_dyadic_offset (collatz_joint_dyadic_word bits)))"
    by (rule collatz_source_window_accumulate_exact)
  have accumulator_affine:
    "fst (snd (collatz_source_window_accumulate bits 0 1 0)) * source +
        snd (snd (collatz_source_window_accumulate bits 0 1 0)) =
      2^(fst (collatz_source_window_accumulate bits 0 1 0)) * target"
    using affine accumulator by simp
  have spent_exact:
    "spent = length bits + count_list bits True"
    unfolding spent_def collatz_source_window_physical_cost_def ..
  have spent_bound: "spent \<le> budget"
    unfolding spent_def using selected_cost .
  have pending_budget:
    "pending = (spent + 1 = budget \<and> odd target)"
    unfolding pending_def
    using spent_bound
    by (cases "spent < budget"; auto; arith)
  have spent_phase_bound: "spent + phase \<le> budget"
  proof (cases pending)
    case False
    then show ?thesis using spent_bound by (simp add: phase_def)
  next
    case True
    then show ?thesis using pending_budget by (simp add: phase_def)
  qed
  have endpoint_odd: "pending \<Longrightarrow> odd target"
    unfolding pending_def by simp
  have physical_endpoint:
    "(physical_collatz ^^ (spent + phase)) source =
      (if pending then 3*target+1 else target)"
  proof (cases pending)
    case False
    then show ?thesis using endpoint_exact
      by (simp add: spent_exact phase_def)
  next
    case True
    have one_tick:
      "(physical_collatz ^^
          (length bits + count_list bits True + 1)) source =
        physical_collatz
          ((physical_collatz ^^
            (length bits + count_list bits True)) source)"
      by (simp add: funpow_add)
    show ?thesis
      using endpoint_exact endpoint_odd[OF True] one_tick True spent_exact
      by (simp add: phase_def physical_collatz_def)
  qed
  show "collatz_guarded_normalized_word_admitted bits source"
    by (rule admitted)
  show "low = source mod 2^limit"
    unfolding low_def by (simp add: take_bit_eq_mod)
  show "length bits \<le> limit"
    by (rule selected_length)
  show "spent = length bits + count_list bits True"
    by (rule spent_exact)
  show "spent \<le> budget"
    by (rule spent_bound)
  show "collatz_source_window_accumulate bits 0 1 0 =
      (length bits,
        (joint_dyadic_gain (collatz_joint_dyadic_word bits),
         joint_dyadic_offset (collatz_joint_dyadic_word bits)))"
    by (rule accumulator)
  show "fst (snd (collatz_source_window_accumulate bits 0 1 0)) * source +
        snd (snd (collatz_source_window_accumulate bits 0 1 0)) =
      2^(fst (collatz_source_window_accumulate bits 0 1 0)) * target"
    by (rule accumulator_affine)
  show "pending = (spent + 1 = budget \<and> odd target)"
    by (rule pending_budget)
  show "phase = (if spent + 1 = budget \<and> odd target then 1 else 0)"
    using pending_budget by (simp add: phase_def)
  show "spent + phase \<le> budget"
    by (rule spent_phase_bound)
  show "(physical_collatz ^^ (spent + phase)) source =
      (if pending then 3*target+1 else target)"
    by (rule physical_endpoint)
qed

theorem collatz_guarded_normalized_window_endpoint_transport:
  assumes admitted:
      "collatz_guarded_normalized_word_admitted bits source"
      and duration:
      "length bits \<le> p"
  shows "collatz_guarded_normalized_word_endpoint bits (source + 2^p*k) =
      collatz_guarded_normalized_word_endpoint bits source +
        3^(count_list bits True) * 2^(p - length bits) * k"
  using admitted duration
proof (induction bits arbitrary: source p k)
  case Nil
  then show ?case by simp
next
  case (Cons branch bits)
  have split_guard:
    "branch = odd source \<and>
      collatz_guarded_normalized_word_admitted bits
        (collatz_guarded_normalized_source_step branch source)"
    using Cons.prems(1)[unfolded
      collatz_guarded_normalized_word_admitted.simps] .
  have branch_source: "branch = odd source"
    using split_guard by blast
  have tail_admitted:
    "collatz_guarded_normalized_word_admitted bits
      (collatz_guarded_normalized_source_step branch source)"
    using split_guard by blast
  have duration_split: "Suc (length bits) \<le> p"
    using Cons.prems(2) by simp
  have positive: "0 < p"
    using duration_split by arith
  have tail_precision: "length bits \<le> p - 1"
    using duration_split by arith
  let ?next = "collatz_guarded_normalized_source_step branch source"
  let ?lift = "(if branch then 3*k else k)"
  have lifted_step:
    "collatz_guarded_normalized_source_step branch (source + 2^p*k) =
      ?next + 2^(p-1)*?lift"
    by (rule collatz_guarded_normalized_step_cylinder[OF branch_source positive])
  have tail:
    "collatz_guarded_normalized_word_endpoint bits
        (?next + 2^(p-1)*?lift) =
      collatz_guarded_normalized_word_endpoint bits ?next +
        3^(count_list bits True) *
          2^((p-1) - length bits) * ?lift"
    using Cons.IH[of ?next "p-1" ?lift]
      tail_admitted tail_precision by blast
  have exponent:
    "(p - 1) - length bits = p - Suc (length bits)"
    using duration_split by arith
  have source_relation:
    "collatz_guarded_normalized_word_endpoint (branch # bits) source =
      collatz_guarded_normalized_word_endpoint bits ?next"
    by simp
  have lifted_relation:
    "collatz_guarded_normalized_word_endpoint (branch # bits)
        (source + 2^p*k) =
      collatz_guarded_normalized_word_endpoint bits
        (?next + 2^(p-1)*?lift)"
    using lifted_step by simp
  show ?case
    using source_relation lifted_relation tail exponent
    by (cases branch) (simp_all add: power_Suc algebra_simps)
qed

ML \<open>
  val checked = @{thms collatz_bounded_source_window_word_admitted
    collatz_bounded_source_window_word_length
    collatz_bounded_source_window_word_cost
    collatz_source_window_accumulate_refines_word
    collatz_source_window_accumulate_exact
    collatz_bounded_source_window_producer_exact
    collatz_guarded_normalized_step_cylinder
    collatz_guarded_normalized_window_admitted_lift
    collatz_guarded_normalized_source_window_refines_action
    collatz_guarded_normalized_window_endpoint_transport};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Collatz source-window refinement depends on an oracle";
  val _ = if Thm_Deps.has_skip_proof checked
    then error "Skipped Collatz source-window refinement proof" else ();
\<close>

end
