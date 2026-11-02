theory Reverse_Mod99_Accumulator_Moore
  imports Reverse_196_Residue_Quotient
begin

text \<open>The clocked accumulator is a quotient of the authenticated decimal
reverse/add producer only after divisibility by eleven has been established.
It preserves the exact mod-99 output pair; it does not represent the full
integer, digit word, carry word, or a future source occurrence.\<close>

record reverse_mod99_accumulator =
  reverse_mod99_odd_phase :: bool
  reverse_mod99_first :: nat
  reverse_mod99_second :: nat

definition reverse_mod99_output :: "reverse_mod99_accumulator \<Rightarrow> nat" where
  "reverse_mod99_output state =
    (reverse_mod99_first state + reverse_mod99_second state) mod 99"

definition reverse_mod99_canonical :: "reverse_mod99_accumulator \<Rightarrow> bool" where
  "reverse_mod99_canonical state \<longleftrightarrow>
    reverse_mod99_first state < 99 \<and> reverse_mod99_second state < 99"

definition reverse_mod99_initial :: "nat \<Rightarrow> reverse_mod99_accumulator" where
  "reverse_mod99_initial source =
    \<lparr>reverse_mod99_odd_phase = False,
      reverse_mod99_first = source mod 99,
      reverse_mod99_second = 0\<rparr>"

lemma reverse_mod99_initial_output:
  "reverse_mod99_output (reverse_mod99_initial source) = source mod 99"
  by (simp add: reverse_mod99_initial_def reverse_mod99_output_def)

definition reverse_mod99_tick ::
    "reverse_mod99_accumulator \<Rightarrow> reverse_mod99_accumulator" where
  "reverse_mod99_tick state =
    (if reverse_mod99_odd_phase state then
      \<lparr>reverse_mod99_odd_phase = False,
        reverse_mod99_first =
          (2 * reverse_mod99_first state + reverse_mod99_second state) mod 99,
        reverse_mod99_second = reverse_mod99_second state mod 99\<rparr>
     else
      \<lparr>reverse_mod99_odd_phase = True,
        reverse_mod99_first = reverse_mod99_first state mod 99,
        reverse_mod99_second =
          (reverse_mod99_first state + 2 * reverse_mod99_second state) mod 99\<rparr>)"

lemma reverse_mod99_output_tick:
  "reverse_mod99_output (reverse_mod99_tick state) =
    (2 * reverse_mod99_output state) mod 99"
proof -
  let ?a = "reverse_mod99_first state"
  let ?b = "reverse_mod99_second state"
  have odd_sum:
    "(((2 * ?a + ?b) mod 99) + ?b mod 99) mod 99 =
      (2 * (?a + ?b)) mod 99"
  proof -
    have first:
      "(((2 * ?a + ?b) mod 99) + ?b mod 99) mod 99 =
        (2 * ?a + ?b + ?b) mod 99"
      by (rule mod_add_eq)
    also have "... = (2 * (?a + ?b)) mod 99"
      by (simp add: algebra_simps)
    finally show ?thesis .
  qed
  have even_sum:
    "(?a mod 99 + (?a + 2 * ?b) mod 99) mod 99 =
      (2 * (?a + ?b)) mod 99"
  proof -
    have first:
      "(?a mod 99 + (?a + 2 * ?b) mod 99) mod 99 =
        (?a + (?a + 2 * ?b)) mod 99"
      by (rule mod_add_eq)
    also have "... = (2 * (?a + ?b)) mod 99"
      by (simp add: algebra_simps)
    finally show ?thesis .
  qed
  have doubled_output:
    "(2 * ((?a + ?b) mod 99)) mod 99 =
      (2 * (?a + ?b)) mod 99"
    by (rule mod_mult_right_eq)
  show ?thesis
  proof (cases "reverse_mod99_odd_phase state")
    case True
    have selected:
      "reverse_mod99_output (reverse_mod99_tick state) =
        (((2 * ?a + ?b) mod 99 + ?b mod 99) mod 99)"
      using True by (simp add: reverse_mod99_tick_def reverse_mod99_output_def)
    show ?thesis
    proof -
      have first:
        "reverse_mod99_output (reverse_mod99_tick state) =
          (((2 * ?a + ?b) mod 99 + ?b mod 99) mod 99)"
        by (rule selected)
      also have "... = (2 * (?a + ?b)) mod 99"
        by (rule odd_sum)
      also have "... = (2 * ((?a + ?b) mod 99)) mod 99"
        by (rule doubled_output[symmetric])
      also have "... = (2 * reverse_mod99_output state) mod 99"
        by (simp add: reverse_mod99_output_def)
      finally show ?thesis .
    qed
  next
    case False
    have selected:
      "reverse_mod99_output (reverse_mod99_tick state) =
        (?a mod 99 + (?a + 2 * ?b) mod 99) mod 99"
      using False by (simp add: reverse_mod99_tick_def reverse_mod99_output_def)
    show ?thesis
    proof -
      have first:
        "reverse_mod99_output (reverse_mod99_tick state) =
          (?a mod 99 + (?a + 2 * ?b) mod 99) mod 99"
        by (rule selected)
      also have "... = (2 * (?a + ?b)) mod 99"
        by (rule even_sum)
      also have "... = (2 * ((?a + ?b) mod 99)) mod 99"
        by (rule doubled_output[symmetric])
      also have "... = (2 * reverse_mod99_output state) mod 99"
        by (simp add: reverse_mod99_output_def)
      finally show ?thesis .
    qed
  qed
qed

lemma reverse_mod99_first_tick_valid:
  assumes "reverse_mod99_first state < 99"
      and "reverse_mod99_second state < 99"
  shows "reverse_mod99_first (reverse_mod99_tick state) < 99"
    and "reverse_mod99_second (reverse_mod99_tick state) < 99"
  using assms
  by (auto simp: reverse_mod99_tick_def)

lemma reverse_mod99_tick_preserves_canonical:
  assumes "reverse_mod99_canonical state"
  shows "reverse_mod99_canonical (reverse_mod99_tick state)"
  using reverse_mod99_first_tick_valid[of state]
    assms unfolding reverse_mod99_canonical_def by blast

lemma reverse_mod99_step_doubles_after_mod11:
  assumes valid: "valid_pair ss"
      and residue: "reverse_add_pair_term ss mod 11 = 0"
  shows "reverse_add_pair_term (step ss) mod 99 =
    (2 * reverse_add_pair_term ss) mod 99"
proof -
  have eleven_scale:
    "(11 * reverse_add_pair_term ss) mod 99 =
      (2 * reverse_add_pair_term ss) mod 99"
  proof -
    have divisible: "11 dvd reverse_add_pair_term ss"
      using residue by (simp add: dvd_eq_mod_eq_0)
    then obtain quotient where
      source: "reverse_add_pair_term ss = 11 * quotient"
      by (rule dvdE)
    have coefficients:
      "((11::nat) * 11) mod 99 = (2 * 11) mod 99"
      by simp
    have products:
      "((11 * 11) * quotient) mod 99 =
        ((2 * 11) * quotient) mod 99"
      by (rule mod_mult_cong[OF coefficients refl])
    show ?thesis using products source by (simp add: algebra_simps)
  qed
  note recurrence = reverse_add_pair_step_mod99[OF valid]
  show ?thesis
    using recurrence eleven_scale
    by (cases "even (length (digits ss))") simp_all
qed

lemma reverse_mod99_step_preserves_mod11_zero:
  assumes valid: "valid_pair ss"
      and residue: "reverse_add_pair_term ss mod 11 = 0"
  shows "reverse_add_pair_term (step ss) mod 11 = 0"
proof -
  let ?source = "reverse_add_pair_term ss"
  let ?factor = "if even (length (digits ss)) then 0 else 2"
  have doubled_from_residue:
    "(2 * (?source mod 11)) mod 11 = (2 * 0) mod 11"
    using residue
    by (rule arg_cong[where f="\<lambda>value. (2 * value) mod 11"])
  have doubled_lift:
    "(2 * ?source) mod 11 = (2 * (?source mod 11)) mod 11"
    by (rule mod_mult_right_eq[symmetric])
  have doubled_zero: "(2 * ?source) mod 11 = 0"
    using doubled_from_residue doubled_lift by simp
  have recurrence:
    "reverse_add_pair_term (step ss) mod 11 =
      (?factor * ?source) mod 11"
    by (rule reverse_add_pair_step_mod11[OF valid])
  show ?thesis
  proof (cases "even (length (digits ss))")
    case True
    then show ?thesis using recurrence by simp
  next
    case False
    then show ?thesis using recurrence doubled_zero by simp
  qed
qed

lemma reverse_mod99_accumulator_refines_source:
  assumes valid: "valid_pair ss"
      and mod11: "reverse_add_pair_term ss mod 11 = 0"
      and output_match: "reverse_mod99_output state =
        reverse_add_pair_term ss mod 99"
  shows "reverse_mod99_output (run reverse_mod99_tick n state) =
    reverse_add_pair_term (run step n ss) mod 99"
  using valid mod11 output_match
proof (induction n arbitrary: ss state)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have next_valid: "valid_pair (step ss)"
    by (rule valid_pair_successor[OF Suc.prems(1)])
  have next_mod11: "reverse_add_pair_term (step ss) mod 11 = 0"
    by (rule reverse_mod99_step_preserves_mod11_zero[OF Suc.prems(1,2)])
  have next_output:
    "reverse_mod99_output (reverse_mod99_tick state) =
      reverse_add_pair_term (step ss) mod 99"
  proof -
    have state_doubles:
      "reverse_mod99_output (reverse_mod99_tick state) =
        (2 * reverse_add_pair_term ss) mod 99"
    proof -
      have first:
        "reverse_mod99_output (reverse_mod99_tick state) =
          (2 * reverse_mod99_output state) mod 99"
        by (rule reverse_mod99_output_tick)
      also have "... =
          (2 * (reverse_add_pair_term ss mod 99)) mod 99"
        using Suc.prems(3) by simp
      also have "... =
          (2 * reverse_add_pair_term ss) mod 99"
        by (rule mod_mult_right_eq)
      finally show ?thesis .
    qed
    have source_doubles:
      "reverse_add_pair_term (step ss) mod 99 =
        (2 * reverse_add_pair_term ss) mod 99"
      by (rule reverse_mod99_step_doubles_after_mod11[OF Suc.prems(1,2)])
    show ?thesis using state_doubles source_doubles by simp
  qed
  have ih:
    "reverse_mod99_output
        (run reverse_mod99_tick n (reverse_mod99_tick state)) =
      reverse_add_pair_term (run step n (step ss)) mod 99"
    by (rule Suc.IH[OF next_valid next_mod11 next_output])
  show ?case using ih by simp
qed

fun reverse_mod99_geometric_weight :: "nat \<Rightarrow> nat" where
  "reverse_mod99_geometric_weight 0 = 0"
| "reverse_mod99_geometric_weight (Suc n) =
    4 * reverse_mod99_geometric_weight n + 1"

fun reverse_mod99_rank_one_weight :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "reverse_mod99_rank_one_weight coupling 0 = 0"
| "reverse_mod99_rank_one_weight coupling (Suc n) =
    (1 + 3 * coupling) * reverse_mod99_rank_one_weight coupling n + coupling"

lemma reverse_mod99_rank_one_weight_identity:
  "3 * reverse_mod99_rank_one_weight coupling n + 1 =
    (1 + 3 * coupling)^n"
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  let ?base = "1 + 3 * coupling"
  have step:
    "3 * reverse_mod99_rank_one_weight coupling (Suc n) + 1 =
      ?base * (3 * reverse_mod99_rank_one_weight coupling n + 1)"
    by (simp add: algebra_simps)
  have power_step: "?base * ?base^n = ?base^(Suc n)"
    by (simp add: power_Suc mult.commute)
  have initial:
    "3 * reverse_mod99_rank_one_weight coupling (Suc n) + 1 =
      ?base * (3 * reverse_mod99_rank_one_weight coupling n + 1)"
    by (rule step)
  also have "... = ?base * ?base^n"
    by (simp only: Suc.IH)
  also have "... = ?base^(Suc n)"
    by (rule power_step)
  finally show ?case .
qed

lemma reverse_mod99_rank_one_weight_one:
  "reverse_mod99_rank_one_weight 1 n = reverse_mod99_geometric_weight n"
  by (induction n) (simp_all add: algebra_simps)

definition reverse_mod99_rank_one_pair_action ::
    "nat \<Rightarrow> nat \<times> nat \<Rightarrow> nat \<times> nat" where
  "reverse_mod99_rank_one_pair_action h pair =
    (let first = fst pair;
         second = snd pair;
         total = (first + second) mod 99
     in ((first + 2 * h * total) mod 99,
         (second + h * total) mod 99))"

lemma reverse_mod99_rank_one_pair_action_residue:
  assumes same: "left mod 99 = right mod 99"
  shows "reverse_mod99_rank_one_pair_action left pair =
    reverse_mod99_rank_one_pair_action right pair"
proof -
  obtain first second where pair: "pair = (first, second)"
    by (cases pair) auto
  let ?total = "(first + second) mod 99"
  have double_factor: "(2 * left) mod 99 = (2 * right) mod 99"
    by (rule mod_mult_cong[OF refl same])
  have first_product:
    "(2 * left * ?total) mod 99 = (2 * right * ?total) mod 99"
    by (rule mod_mult_cong[OF double_factor refl])
  have second_product:
    "(left * ?total) mod 99 = (right * ?total) mod 99"
    by (rule mod_mult_cong[OF same refl])
  have first:
    "(first + 2 * left * ?total) mod 99 =
      (first + 2 * right * ?total) mod 99"
    by (rule mod_add_cong[OF refl first_product])
  have second:
    "(second + left * ?total) mod 99 =
      (second + right * ?total) mod 99"
    by (rule mod_add_cong[OF refl second_product])
  show ?thesis
    unfolding reverse_mod99_rank_one_pair_action_def pair Let_def
    by (simp only: fst_conv snd_conv first second)
qed

lemma reverse_mod99_rank_one_pair_action_compose:
  "reverse_mod99_rank_one_pair_action later
      (reverse_mod99_rank_one_pair_action earlier pair) =
    reverse_mod99_rank_one_pair_action
      (earlier + later + 3 * earlier * later) pair"
proof -
  obtain first second where pair: "pair = (first, second)"
    by (cases pair) auto
  let ?total = "(first + second) mod 99"
  let ?first = "(first + 2 * earlier * ?total) mod 99"
  let ?second = "(second + earlier * ?total) mod 99"
  let ?next_total = "(?first + ?second) mod 99"
  let ?combined = "earlier + later + 3 * earlier * later"
  have flatten:
    "(?first + ?second) mod 99 =
      (first + second + 3 * earlier * ?total) mod 99"
    by (simp only: mod_add_eq; simp add: algebra_simps)
  have initial_total:
    "(first + second) mod 99 = ?total mod 99"
    by simp
  have shifted_total:
    "(first + second + 3 * earlier * ?total) mod 99 =
      (?total + 3 * earlier * ?total) mod 99"
    by (rule mod_add_cong[OF initial_total refl])
  have next_total:
    "?next_total = ((1 + 3 * earlier) * ?total) mod 99"
    using flatten shifted_total by (simp add: algebra_simps)
  have first_residue: "?first mod 99 =
      (first + 2 * earlier * ?total) mod 99"
    by simp
  have total_residue:
    "?next_total mod 99 = ((1 + 3 * earlier) * ?total) mod 99"
    using next_total by simp
  have first_product:
    "(2 * later * ?next_total) mod 99 =
      (2 * later * ((1 + 3 * earlier) * ?total)) mod 99"
    by (rule mod_mult_cong[OF refl total_residue])
  have second_product:
    "(later * ?next_total) mod 99 =
      (later * ((1 + 3 * earlier) * ?total)) mod 99"
    by (rule mod_mult_cong[OF refl total_residue])
  have second_residue:
    "?second mod 99 = (second + earlier * ?total) mod 99"
    by simp
  have first_combine:
    "(?first + 2 * later * ?next_total) mod 99 =
      ((first + 2 * earlier * ?total) +
        2 * later * ((1 + 3 * earlier) * ?total)) mod 99"
    by (rule mod_add_cong[OF first_residue first_product])
  have second_combine:
    "(?second + later * ?next_total) mod 99 =
      ((second + earlier * ?total) +
        later * ((1 + 3 * earlier) * ?total)) mod 99"
    by (rule mod_add_cong[OF second_residue second_product])
  have first_step:
    "(?first + 2 * later * ?next_total) mod 99 =
      (first + 2 * ?combined * ?total) mod 99"
    using first_combine by (simp add: algebra_simps)
  have second_step:
    "(?second + later * ?next_total) mod 99 =
      (second + ?combined * ?total) mod 99"
    using second_combine by (simp add: algebra_simps)
  have nested:
    "reverse_mod99_rank_one_pair_action later
        (reverse_mod99_rank_one_pair_action earlier (first, second)) =
      ((first + 2 * ?combined * ?total) mod 99,
       (second + ?combined * ?total) mod 99)"
    using first_step second_step
    by (simp add: reverse_mod99_rank_one_pair_action_def Let_def)
  have direct:
    "reverse_mod99_rank_one_pair_action ?combined (first, second) =
      ((first + 2 * ?combined * ?total) mod 99,
       (second + ?combined * ?total) mod 99)"
    by (simp add: reverse_mod99_rank_one_pair_action_def Let_def)
  show ?thesis using pair nested direct by simp
qed

fun reverse_mod99_rank_one_pair_iterate ::
    "nat \<Rightarrow> nat \<Rightarrow> nat \<times> nat \<Rightarrow> nat \<times> nat" where
  "reverse_mod99_rank_one_pair_iterate 0 coupling pair = pair"
| "reverse_mod99_rank_one_pair_iterate (Suc n) coupling pair =
    reverse_mod99_rank_one_pair_action coupling
      (reverse_mod99_rank_one_pair_iterate n coupling pair)"

lemma reverse_mod99_rank_one_pair_iterate_exact:
  assumes canonical: "fst pair < 99 \<and> snd pair < 99"
  shows "reverse_mod99_rank_one_pair_iterate n coupling pair =
    reverse_mod99_rank_one_pair_action
      (reverse_mod99_rank_one_weight coupling n) pair"
  using canonical
proof (induction n arbitrary: pair)
  case 0
  then show ?case by (cases pair) (auto simp: reverse_mod99_rank_one_pair_action_def)
next
  case (Suc n)
  let ?weight = "reverse_mod99_rank_one_weight coupling n"
  have iterate:
    "reverse_mod99_rank_one_pair_iterate (Suc n) coupling pair =
      reverse_mod99_rank_one_pair_action coupling
        (reverse_mod99_rank_one_pair_action ?weight pair)"
    using Suc.IH[OF Suc.prems] by simp
  have compose:
    "reverse_mod99_rank_one_pair_action coupling
        (reverse_mod99_rank_one_pair_action ?weight pair) =
      reverse_mod99_rank_one_pair_action
        (?weight + coupling + 3 * ?weight * coupling) pair"
    by (rule reverse_mod99_rank_one_pair_action_compose)
  have weight_eq:
    "reverse_mod99_rank_one_weight coupling (Suc n) =
      ?weight + coupling + 3 * ?weight * coupling"
    by (simp add: algebra_simps)
  have composed:
    "reverse_mod99_rank_one_pair_iterate (Suc n) coupling pair =
      reverse_mod99_rank_one_pair_action
        (?weight + coupling + 3 * ?weight * coupling) pair"
    by (rule trans[OF iterate compose])
  have weight_transport:
    "reverse_mod99_rank_one_pair_action
        (?weight + coupling + 3 * ?weight * coupling) pair =
      reverse_mod99_rank_one_pair_action
        (reverse_mod99_rank_one_weight coupling (Suc n)) pair"
    by (simp only: weight_eq[symmetric])
  show ?case by (rule trans[OF composed weight_transport])
qed

text \<open>The rank-one coefficient is reduced modulo 297 before exact division by three.\<close>

lemma reverse_mod99_rank_one_weight_mod297_div3:
  assumes coupling: "coupling < 99"
  shows "((1 + 3 * coupling)^n mod 297 - 1) div 3 =
    reverse_mod99_rank_one_weight coupling n mod 99"
proof -
  let ?weight = "reverse_mod99_rank_one_weight coupling n"
  let ?residue = "?weight mod 99"
  have decomposition:
    "?weight = 99 * (?weight div 99) + ?residue"
    using div_mult_mod_eq[of ?weight 99] by (simp add: mult.commute)
  have residue_bound: "?residue < 99" by simp
  have numerator:
    "(1 + 3 * coupling)^n =
      297 * (?weight div 99) + (3 * ?residue + 1)"
    using reverse_mod99_rank_one_weight_identity[of coupling n]
      decomposition by linarith
  have canonical: "3 * ?residue + 1 < 297"
    using residue_bound by arith
  have residue:
    "(1 + 3 * coupling)^n mod 297 = 3 * ?residue + 1"
    using numerator canonical by (simp add: algebra_simps)
  have quotient:
    "((3 * ?residue + 1 - 1) div 3) = ?residue"
    by simp
  show ?thesis using residue quotient by simp
qed

lemma reverse_mod99_geometric_weight_mod297_div3:
  "((4^n mod 297 - 1) div 3) mod 99 =
    reverse_mod99_geometric_weight n mod 99"
proof -
  have base: "((1::nat) + 3 * 1)^n = 4^n" by simp
  have coefficient:
    "((1 + 3 * 1)^n mod 297 - 1) div 3 =
      reverse_mod99_rank_one_weight 1 n mod 99"
    by (rule reverse_mod99_rank_one_weight_mod297_div3[of 1 n]) simp
  have general:
    "(((1 + 3 * 1)^n mod 297 - 1) div 3) mod 99 =
      reverse_mod99_rank_one_weight 1 n mod 99"
    by (simp only: coefficient mod_mod_trivial)
  have weight:
    "reverse_mod99_rank_one_weight 1 n mod 99 =
      reverse_mod99_geometric_weight n mod 99"
    by (simp only: reverse_mod99_rank_one_weight_one)
  show ?thesis
    by (simp only: base[symmetric] general weight)
qed

lemma reverse_mod99_rank_one_pair_iterate_mod297:
  assumes coupling: "coupling < 99"
      and canonical: "fst pair < 99 \<and> snd pair < 99"
  shows "reverse_mod99_rank_one_pair_iterate n coupling pair =
    reverse_mod99_rank_one_pair_action
      (((1 + 3 * coupling)^n mod 297 - 1) div 3) pair"
proof -
  have coefficient:
    "((1 + 3 * coupling)^n mod 297 - 1) div 3 =
      reverse_mod99_rank_one_weight coupling n mod 99"
    by (rule reverse_mod99_rank_one_weight_mod297_div3[OF coupling])
  have residue:
    "(((1 + 3 * coupling)^n mod 297 - 1) div 3) mod 99 =
      reverse_mod99_rank_one_weight coupling n mod 99"
    using coefficient by simp
  have actions:
    "reverse_mod99_rank_one_pair_action
        (((1 + 3 * coupling)^n mod 297 - 1) div 3) pair =
      reverse_mod99_rank_one_pair_action
        (reverse_mod99_rank_one_weight coupling n) pair"
    by (rule reverse_mod99_rank_one_pair_action_residue[OF residue])
  have iter:
    "reverse_mod99_rank_one_pair_iterate n coupling pair =
      reverse_mod99_rank_one_pair_action
        (reverse_mod99_rank_one_weight coupling n) pair"
    by (rule reverse_mod99_rank_one_pair_iterate_exact[OF canonical])
  show ?thesis using actions iter by simp
qed

definition reverse_mod99_rank_one_apply ::
    "nat \<Rightarrow> reverse_mod99_accumulator \<Rightarrow> nat" where
  "reverse_mod99_rank_one_apply h state =
    (let total = reverse_mod99_output state
     in ((reverse_mod99_first state + 2 * h * total) mod 99 +
         (reverse_mod99_second state + h * total) mod 99) mod 99)"

lemma reverse_mod99_rank_one_apply_pair_sum:
  "reverse_mod99_rank_one_apply h state =
    (let result = reverse_mod99_rank_one_pair_action h
        (reverse_mod99_first state, reverse_mod99_second state)
     in (fst result + snd result) mod 99)"
  by (simp add: reverse_mod99_rank_one_apply_def
      reverse_mod99_rank_one_pair_action_def reverse_mod99_output_def Let_def)

definition reverse_mod99_rank_one_power_output ::
    "nat \<Rightarrow> nat \<Rightarrow> reverse_mod99_accumulator \<Rightarrow> nat" where
  "reverse_mod99_rank_one_power_output n coupling state =
    reverse_mod99_rank_one_apply
      (reverse_mod99_rank_one_weight coupling n mod 99) state"

lemma reverse_mod99_rank_one_apply_residue:
  assumes "left mod 99 = right mod 99"
  shows "reverse_mod99_rank_one_apply left state =
    reverse_mod99_rank_one_apply right state"
proof -
  let ?pair = "(reverse_mod99_first state, reverse_mod99_second state)"
  have same_pair:
    "reverse_mod99_rank_one_pair_action left ?pair =
      reverse_mod99_rank_one_pair_action right ?pair"
    by (rule reverse_mod99_rank_one_pair_action_residue[OF assms])
  have left_sum:
    "reverse_mod99_rank_one_apply left state =
      (let result = reverse_mod99_rank_one_pair_action left ?pair
       in (fst result + snd result) mod 99)"
    by (rule reverse_mod99_rank_one_apply_pair_sum)
  have right_sum:
    "reverse_mod99_rank_one_apply right state =
      (let result = reverse_mod99_rank_one_pair_action right ?pair
       in (fst result + snd result) mod 99)"
    by (rule reverse_mod99_rank_one_apply_pair_sum)
  show ?thesis using same_pair left_sum right_sum by simp
qed

lemma reverse_mod99_rank_one_power_output_exact:
  "reverse_mod99_rank_one_power_output n coupling state =
    ((1 + 3 * coupling)^n * reverse_mod99_output state) mod 99"
proof -
  let ?a = "reverse_mod99_first state"
  let ?b = "reverse_mod99_second state"
  let ?h = "reverse_mod99_rank_one_weight coupling n"
  let ?s = "reverse_mod99_output state"
  have combine:
    "((?a + 2 * ?h * ?s) mod 99 + (?b + ?h * ?s) mod 99) mod 99 =
     (?a + ?b + 3 * ?h * ?s) mod 99"
    by (simp only: mod_add_eq add.assoc; simp add: algebra_simps)
  have sum_residue: "?s mod 99 = (?a + ?b) mod 99"
    by (simp add: reverse_mod99_output_def)
  have scaled:
    "(3 * ?h * ?s) mod 99 = (3 * ?h * (?a + ?b)) mod 99"
    by (rule mod_mult_cong[OF refl sum_residue])
  have combined:
    "(?a + ?b + 3 * ?h * ?s) mod 99 =
      (?a + ?b + 3 * ?h * (?a + ?b)) mod 99"
    by (rule mod_add_cong[OF refl scaled])
  have product_identity:
    "?a + ?b + 3 * ?h * (?a + ?b) =
      (1 + 3 * coupling)^n * (?a + ?b)"
    using arg_cong[OF reverse_mod99_rank_one_weight_identity[of coupling n],
      where f="\<lambda>value. value * (?a + ?b)"]
    by (simp add: algebra_simps)
  have output_scale:
    "((1 + 3 * coupling)^n * ?s) mod 99 =
      ((1 + 3 * coupling)^n * (?a + ?b)) mod 99"
    by (rule mod_mult_cong[OF refl sum_residue])
  have unnormalized:
    "reverse_mod99_rank_one_apply ?h state =
      ((1 + 3 * coupling)^n * ?s) mod 99"
  proof -
    have first:
      "((?a + 2 * ?h * ?s) mod 99 + (?b + ?h * ?s) mod 99) mod 99 =
        (?a + ?b + 3 * ?h * ?s) mod 99"
      by (rule combine)
    also have "... = (?a + ?b + 3 * ?h * (?a + ?b)) mod 99"
      by (rule combined)
    also have "... = ((1 + 3 * coupling)^n * (?a + ?b)) mod 99"
      by (simp only: product_identity)
    also have "... = ((1 + 3 * coupling)^n * ?s) mod 99"
      by (rule output_scale[symmetric])
    finally show ?thesis
      unfolding reverse_mod99_rank_one_apply_def Let_def .
  qed
  have normalized:
    "reverse_mod99_rank_one_apply (?h mod 99) state =
      reverse_mod99_rank_one_apply ?h state"
    by (rule reverse_mod99_rank_one_apply_residue) simp
  show ?thesis
    unfolding reverse_mod99_rank_one_power_output_def
    using normalized unnormalized by simp
qed

lemma reverse_mod99_rank_one_power_output_mod297:
  assumes coupling: "coupling < 99"
  shows "reverse_mod99_rank_one_apply
      (((1 + 3 * coupling)^n mod 297 - 1) div 3) state =
    ((1 + 3 * coupling)^n * reverse_mod99_output state) mod 99"
proof -
  have coefficient:
    "((1 + 3 * coupling)^n mod 297 - 1) div 3 =
      reverse_mod99_rank_one_weight coupling n mod 99"
    by (rule reverse_mod99_rank_one_weight_mod297_div3[OF coupling])
  have powered_result:
    "reverse_mod99_rank_one_power_output n
        coupling state =
      ((1 + 3 * coupling)^n * reverse_mod99_output state) mod 99"
    by (rule reverse_mod99_rank_one_power_output_exact)
  show ?thesis using coefficient powered_result
    unfolding reverse_mod99_rank_one_power_output_def
    by simp
qed

lemma reverse_mod99_two_tick_coordinates:
  assumes even_phase: "\<not> reverse_mod99_odd_phase state"
  shows "reverse_mod99_odd_phase (reverse_mod99_tick
        (reverse_mod99_tick state)) = False"
    and "reverse_mod99_first (reverse_mod99_tick
        (reverse_mod99_tick state)) =
      (3 * reverse_mod99_first state + 2 * reverse_mod99_second state) mod 99"
    and "reverse_mod99_second (reverse_mod99_tick
        (reverse_mod99_tick state)) =
      (reverse_mod99_first state + 2 * reverse_mod99_second state) mod 99"
proof -
  let ?a = "reverse_mod99_first state"
  let ?b = "reverse_mod99_second state"
  have first_product:
    "(2 * (?a mod 99)) mod 99 = (2 * ?a) mod 99"
    by (rule mod_mult_right_eq)
  have first_coordinate:
    "(2 * (?a mod 99) + (?a + 2 * ?b) mod 99) mod 99 =
      (3 * ?a + 2 * ?b) mod 99"
  proof -
    have first:
      "(2 * (?a mod 99) + (?a + 2 * ?b) mod 99) mod 99 =
        (2 * ?a + (?a + 2 * ?b) mod 99) mod 99"
      by (rule mod_add_cong[OF first_product refl])
    also have "... = (2 * ?a + (?a + 2 * ?b)) mod 99"
      by (rule mod_add_right_eq)
    also have "... = (3 * ?a + 2 * ?b) mod 99"
      by (simp add: algebra_simps)
    finally show ?thesis .
  qed
  have two_tick:
    "reverse_mod99_tick (reverse_mod99_tick state) =
      \<lparr>reverse_mod99_odd_phase = False,
        reverse_mod99_first =
          (2 * (?a mod 99) + (?a + 2 * ?b) mod 99) mod 99,
        reverse_mod99_second = (?a + 2 * ?b) mod 99\<rparr>"
    using even_phase by (simp add: reverse_mod99_tick_def)
  show "reverse_mod99_odd_phase (reverse_mod99_tick
        (reverse_mod99_tick state)) = False"
    using two_tick by simp
  show "reverse_mod99_first (reverse_mod99_tick
        (reverse_mod99_tick state)) =
      (3 * reverse_mod99_first state + 2 * reverse_mod99_second state) mod 99"
    using two_tick first_coordinate by simp
  show "reverse_mod99_second (reverse_mod99_tick
        (reverse_mod99_tick state)) =
      (reverse_mod99_first state + 2 * reverse_mod99_second state) mod 99"
    using two_tick by simp
qed

lemma reverse_mod99_two_tick_output:
  "reverse_mod99_output (reverse_mod99_tick
      (reverse_mod99_tick state)) =
    (4 * reverse_mod99_output state) mod 99"
proof -
  have first:
    "reverse_mod99_output (reverse_mod99_tick
        (reverse_mod99_tick state)) =
      (2 * reverse_mod99_output (reverse_mod99_tick state)) mod 99"
    by (rule reverse_mod99_output_tick)
  also have "... = (2 * ((2 * reverse_mod99_output state) mod 99)) mod 99"
    by (simp only: reverse_mod99_output_tick)
  also have "... = (2 * (2 * reverse_mod99_output state)) mod 99"
    by (rule mod_mult_right_eq)
  also have "... = (4 * reverse_mod99_output state) mod 99"
    by (simp add: algebra_simps)
  finally show ?thesis .
qed

fun reverse_mod99_even_block_run ::
    "nat \<Rightarrow> reverse_mod99_accumulator \<Rightarrow> reverse_mod99_accumulator" where
  "reverse_mod99_even_block_run 0 state = state"
| "reverse_mod99_even_block_run (Suc n) state =
    reverse_mod99_even_block_run n
      (reverse_mod99_tick (reverse_mod99_tick state))"

lemma reverse_mod99_two_tick_pair_action:
  assumes even_phase: "\<not> reverse_mod99_odd_phase state"
  shows "(reverse_mod99_first (reverse_mod99_tick (reverse_mod99_tick state)),
      reverse_mod99_second (reverse_mod99_tick (reverse_mod99_tick state))) =
    reverse_mod99_rank_one_pair_action 1
      (reverse_mod99_first state, reverse_mod99_second state)"
proof -
  let ?a = "reverse_mod99_first state"
  let ?b = "reverse_mod99_second state"
  have first_product:
    "(2 * ((?a + ?b) mod 99)) mod 99 = (2 * (?a + ?b)) mod 99"
    by (rule mod_mult_cong[OF refl]) simp
  have first_coordinate:
    "(?a + 2 * ((?a + ?b) mod 99)) mod 99 =
      (3 * ?a + 2 * ?b) mod 99"
  proof -
    have shift:
      "(?a + 2 * ((?a + ?b) mod 99)) mod 99 =
        (?a + 2 * (?a + ?b)) mod 99"
      by (rule mod_add_cong[OF refl first_product])
    show ?thesis using shift by (simp add: algebra_simps)
  qed
  have second_residue:
    "((?a + ?b) mod 99) mod 99 = (?a + ?b) mod 99"
    by simp
  have second_coordinate:
    "(?b + ((?a + ?b) mod 99)) mod 99 =
      (?a + 2 * ?b) mod 99"
  proof -
    have algebraic_identity: "?b + (?a + ?b) = ?a + 2 * ?b"
      by (simp add: algebra_simps)
    show ?thesis
      by (simp only: mod_add_cong[OF refl second_residue] algebraic_identity)
  qed
  have powered_action:
    "reverse_mod99_rank_one_pair_action 1 (?a, ?b) =
      ((3 * ?a + 2 * ?b) mod 99, (?a + 2 * ?b) mod 99)"
    using first_coordinate second_coordinate
    by (simp only: reverse_mod99_rank_one_pair_action_def Let_def
        fst_conv snd_conv mult_1_right mult_1_left
        first_coordinate second_coordinate)
  show ?thesis
    using reverse_mod99_two_tick_coordinates[OF even_phase] powered_action
    by auto
qed

lemma reverse_mod99_even_block_run_pair_action:
  assumes even_phase: "\<not> reverse_mod99_odd_phase state"
      and canonical: "reverse_mod99_canonical state"
  shows "(reverse_mod99_first (reverse_mod99_even_block_run n state),
      reverse_mod99_second (reverse_mod99_even_block_run n state)) =
    reverse_mod99_rank_one_pair_action
      (reverse_mod99_geometric_weight n)
      (reverse_mod99_first state, reverse_mod99_second state)"
  using even_phase canonical
proof (induction n arbitrary: state)
  case 0
  then show ?case
    by (cases state) (auto simp: reverse_mod99_rank_one_pair_action_def
        reverse_mod99_canonical_def Let_def)
next
  case (Suc n)
  let ?next = "reverse_mod99_tick (reverse_mod99_tick state)"
  have next_phase: "\<not> reverse_mod99_odd_phase ?next"
    using Suc.prems(1) by (simp add: reverse_mod99_tick_def)
  have next_canonical: "reverse_mod99_canonical ?next"
    by (rule reverse_mod99_tick_preserves_canonical[OF
        reverse_mod99_tick_preserves_canonical[OF Suc.prems(2)]])
  have next_pair:
    "(reverse_mod99_first ?next, reverse_mod99_second ?next) =
      reverse_mod99_rank_one_pair_action 1
        (reverse_mod99_first state, reverse_mod99_second state)"
    by (rule reverse_mod99_two_tick_pair_action[OF Suc.prems(1)])
  have iterated_pair:
    "(reverse_mod99_first (reverse_mod99_even_block_run n ?next),
      reverse_mod99_second (reverse_mod99_even_block_run n ?next)) =
      reverse_mod99_rank_one_pair_action
        (reverse_mod99_geometric_weight n)
        (reverse_mod99_first ?next, reverse_mod99_second ?next)"
    by (rule Suc.IH[OF next_phase next_canonical])
  have weight:
    "reverse_mod99_geometric_weight (Suc n) =
      1 + reverse_mod99_geometric_weight n +
        3 * reverse_mod99_geometric_weight n"
    by (simp add: algebra_simps)
  have run_step:
    "(reverse_mod99_first (reverse_mod99_even_block_run (Suc n) state),
      reverse_mod99_second (reverse_mod99_even_block_run (Suc n) state)) =
     (reverse_mod99_first (reverse_mod99_even_block_run n ?next),
      reverse_mod99_second (reverse_mod99_even_block_run n ?next))"
    by simp
  also have "... = reverse_mod99_rank_one_pair_action
      (reverse_mod99_geometric_weight n)
      (reverse_mod99_first ?next, reverse_mod99_second ?next)"
    by (rule iterated_pair)
  also have "... = reverse_mod99_rank_one_pair_action
      (reverse_mod99_geometric_weight n)
      (reverse_mod99_rank_one_pair_action 1
        (reverse_mod99_first state, reverse_mod99_second state))"
    by (simp only: next_pair)
  also have "... = reverse_mod99_rank_one_pair_action
      (1 + reverse_mod99_geometric_weight n +
        3 * reverse_mod99_geometric_weight n)
      (reverse_mod99_first state, reverse_mod99_second state)"
    by (simp only: reverse_mod99_rank_one_pair_action_compose
        mult_1_left mult_1_right)
  also have "... = reverse_mod99_rank_one_pair_action
      (reverse_mod99_geometric_weight (Suc n))
      (reverse_mod99_first state, reverse_mod99_second state)"
    by (simp only: weight[symmetric])
  finally show ?case .
qed

lemma reverse_mod99_even_block_run_output:
  "reverse_mod99_output (reverse_mod99_even_block_run n state) =
    (4^n * reverse_mod99_output state) mod 99"
proof (induction n arbitrary: state)
  case 0
  then show ?case by (simp add: reverse_mod99_output_def)
next
  case (Suc n)
  have next_output:
    "reverse_mod99_output
       (reverse_mod99_tick (reverse_mod99_tick state)) =
     (4 * reverse_mod99_output state) mod 99"
    by (rule reverse_mod99_two_tick_output)
  have reassociated:
    "(4^n * reverse_mod99_output
       (reverse_mod99_tick (reverse_mod99_tick state))) mod 99 =
     (4^n * (4 * reverse_mod99_output state)) mod 99"
    by (rule mod_mult_cong; simp add: next_output)
  show ?case
    using Suc.IH[of "reverse_mod99_tick (reverse_mod99_tick state)"]
      reassociated
    by (simp add: power_Suc algebra_simps)
qed

definition reverse_mod99_rank_one_output ::
    "nat \<Rightarrow> reverse_mod99_accumulator \<Rightarrow> nat" where
  "reverse_mod99_rank_one_output n state =
    reverse_mod99_rank_one_apply
      (reverse_mod99_geometric_weight n) state"

lemma reverse_mod99_rank_one_output_matches_power:
  "reverse_mod99_rank_one_output n state =
    (4^n * reverse_mod99_output state) mod 99"
proof -
  have generic:
    "reverse_mod99_rank_one_power_output n 1 state =
      ((1 + 3 * 1)^n * reverse_mod99_output state) mod 99"
    by (rule reverse_mod99_rank_one_power_output_exact)
  have coefficient:
    "reverse_mod99_geometric_weight n mod 99 =
      (reverse_mod99_rank_one_weight 1 n mod 99) mod 99"
    by (simp only: reverse_mod99_rank_one_weight_one[symmetric] mod_mod_trivial)
  have same:
    "reverse_mod99_rank_one_apply (reverse_mod99_geometric_weight n) state =
      reverse_mod99_rank_one_apply
        (reverse_mod99_rank_one_weight 1 n mod 99) state"
    by (rule reverse_mod99_rank_one_apply_residue[OF coefficient])
  show ?thesis
    using generic same
    unfolding reverse_mod99_rank_one_output_def
      reverse_mod99_rank_one_power_output_def
    by simp
qed

text \<open>The following quotient observes only the scalar sum modulo 99. It is
strictly narrower than the Python accumulator packet, which also exposes the
ordered pair, its difference and phase. In particular, do not use this scalar
observer class as the identity for that richer packet.\<close>

definition reverse_mod99_scalar_observer_class ::
    "reverse_mod99_accumulator \<Rightarrow> nat" where
  "reverse_mod99_scalar_observer_class state = reverse_mod99_output state"

lemma reverse_mod99_scalar_observer_right_congruence:
  assumes same: "reverse_mod99_scalar_observer_class left =
      reverse_mod99_scalar_observer_class right"
  shows "reverse_mod99_scalar_observer_class (reverse_mod99_tick left) =
      reverse_mod99_scalar_observer_class (reverse_mod99_tick right)"
  using same by (simp add: reverse_mod99_scalar_observer_class_def
      reverse_mod99_output_tick)

lemma reverse_mod99_scalar_observer_future_exact:
  assumes same: "reverse_mod99_scalar_observer_class left =
      reverse_mod99_scalar_observer_class right"
  shows "reverse_mod99_scalar_observer_class (run reverse_mod99_tick n left) =
      reverse_mod99_scalar_observer_class (run reverse_mod99_tick n right)"
  using same
proof (induction n arbitrary: left right)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have next_observation:
    "reverse_mod99_scalar_observer_class (reverse_mod99_tick left) =
      reverse_mod99_scalar_observer_class (reverse_mod99_tick right)"
    by (rule reverse_mod99_scalar_observer_right_congruence[OF Suc.prems])
  have tail:
    "reverse_mod99_scalar_observer_class
        (run reverse_mod99_tick n (reverse_mod99_tick left)) =
      reverse_mod99_scalar_observer_class
        (run reverse_mod99_tick n (reverse_mod99_tick right))"
    by (rule Suc.IH[OF next_observation])
  show ?case using tail by simp
qed

lemma reverse_mod99_scalar_observer_future_iff:
  "reverse_mod99_scalar_observer_class left =
      reverse_mod99_scalar_observer_class right \<longleftrightarrow>
    (\<forall>n. reverse_mod99_scalar_observer_class
        (run reverse_mod99_tick n left) =
      reverse_mod99_scalar_observer_class
        (run reverse_mod99_tick n right))"
proof
  assume same: "reverse_mod99_scalar_observer_class left =
      reverse_mod99_scalar_observer_class right"
  show "\<forall>n. reverse_mod99_scalar_observer_class
      (run reverse_mod99_tick n left) =
    reverse_mod99_scalar_observer_class (run reverse_mod99_tick n right)"
    by (rule allI; rule reverse_mod99_scalar_observer_future_exact[OF same])
next
  assume same_future: "\<forall>n. reverse_mod99_scalar_observer_class
      (run reverse_mod99_tick n left) =
    reverse_mod99_scalar_observer_class (run reverse_mod99_tick n right)"
  have at_zero:
    "reverse_mod99_scalar_observer_class
        (run reverse_mod99_tick 0 left) =
      reverse_mod99_scalar_observer_class
        (run reverse_mod99_tick 0 right)"
    using same_future by blast
  show "reverse_mod99_scalar_observer_class left =
      reverse_mod99_scalar_observer_class right"
    using at_zero by simp
qed

ML \<open>
  val checked = @{thms reverse_mod99_output_tick
    reverse_mod99_initial_output
    reverse_mod99_first_tick_valid
    reverse_mod99_tick_preserves_canonical
    reverse_mod99_step_doubles_after_mod11
    reverse_mod99_step_preserves_mod11_zero
    reverse_mod99_accumulator_refines_source
    reverse_mod99_geometric_weight_mod297_div3
    reverse_mod99_rank_one_weight_identity
    reverse_mod99_rank_one_weight_one
    reverse_mod99_rank_one_weight_mod297_div3
    reverse_mod99_rank_one_pair_action_residue
    reverse_mod99_rank_one_pair_action_compose
    reverse_mod99_rank_one_pair_iterate_exact
    reverse_mod99_rank_one_pair_iterate_mod297
    reverse_mod99_rank_one_apply_pair_sum
    reverse_mod99_rank_one_apply_residue
    reverse_mod99_rank_one_power_output_exact
    reverse_mod99_rank_one_power_output_mod297
    reverse_mod99_two_tick_coordinates
    reverse_mod99_two_tick_pair_action
    reverse_mod99_even_block_run_pair_action
    reverse_mod99_two_tick_output
    reverse_mod99_even_block_run_output
    reverse_mod99_rank_one_output_matches_power
    reverse_mod99_scalar_observer_right_congruence
    reverse_mod99_scalar_observer_future_exact
    reverse_mod99_scalar_observer_future_iff};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Reverse modulo-99 accumulator refinement depends on an oracle";
\<close>

end
