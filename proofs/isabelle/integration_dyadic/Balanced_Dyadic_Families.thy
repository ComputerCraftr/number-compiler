theory Balanced_Dyadic_Families
  imports "Shared_S_Arithmetic.Dyadic_Balanced_Arithmetic"
    "Collatz_Cylinder_Refinement.Collatz_Physical_Cylinder_Lift"
    "Antihydra.Antihydra_Arithmetic_Cylinder_Lift"
    "Antihydra_Mahler_Integration.Antihydra_Mahler_Associated_Action"
begin

text \<open>The two production dyadic laws instantiate one numeric balanced
constructor. Their branch labels come from the source trajectory; the
executable effect carries neither a supplied itinerary nor a second safety
state. Mahler is a separate consumer of Antihydra's resulting skew transfer.\<close>

interpretation collatz_balanced: dyadic_arithmetic_constructor
    physical_collatz odd collatz_physical_gain
    "\<lambda>b. if b then 2 else 0"
    "\<lambda>b. if b then 1 else 0"
    "\<lambda>b. if b then 1 else 0"
proof
  show "\<And>x. int (collatz_physical_gain (odd x)) * int x +
      (if odd x then 2 else 0) = 2 * int (physical_collatz x)"
  proof -
    fix x :: nat
    show "int (collatz_physical_gain (odd x)) * int x +
        (if odd x then 2 else 0) = 2 * int (physical_collatz x)"
      by (cases "even x";
          simp add: collatz_physical_gain_def physical_collatz_def;
          presburger)
  qed
qed

interpretation antihydra_balanced: dyadic_arithmetic_constructor
    antihydra_family_step "\<lambda>a. a mod 2" "\<lambda>_. 3"
    "\<lambda>b. - int b" "\<lambda>b. b" "\<lambda>b. 2 - 3 * int b"
proof
  show "\<And>x. int (3::nat) * int x + (- int (x mod 2)) =
      2 * int (antihydra_family_step x)"
    using antihydra_family_step_skew_equation by (simp add: algebra_simps)
qed

lemma collatz_balanced_finite_endpoint:
  "map_option (\<lambda>E. collatz_balanced.effect_apply E x)
      (collatz_balanced.balanced.execute_balanced cache_admit n x) =
    Some ((physical_collatz ^^ n) x)"
  using collatz_balanced.execute_balanced_endpoint
    [where cache_admit=cache_admit and n=n and x=x]
  by (simp add: dyadic_source_orbit_funpow)

theorem collatz_balanced_constructed_endpoint:
  "map_option (\<lambda>E. collatz_balanced.effect_apply E x)
      (collatz_balanced.construct_source_effect cache_admit n x) =
    Some ((physical_collatz ^^ n) x)"
  using collatz_balanced.construct_source_effect_endpoint
    [where cache_admit=cache_admit and n=n and source=x]
  by (simp add: dyadic_source_orbit_funpow)

lemma collatz_physical_prefix_minimum_zero:
  "snd (prefix_summary (\<lambda>b. if b then (1::int) else 0) bs) = 0"
  by (induction bs) (simp_all add: Let_def)

theorem collatz_balanced_finite_minimum_zero:
  "effect_minimum
      (the (collatz_balanced.balanced.execute_balanced cache_admit n x)) = 0"
  using collatz_balanced.execute_balanced_source_effect
    [where cache_admit=cache_admit and n=n and x=x]
    collatz_balanced.effect_word_safety[of
      "dyadic_source_word physical_collatz odd x n"]
    collatz_physical_prefix_minimum_zero[of
      "dyadic_source_word physical_collatz odd x n"]
  by (simp add: collatz_balanced.source_effect_def prod_eq_iff)

theorem collatz_physical_first_negative_unreachable:
  assumes "0 \<le> initial"
  shows "first_negative (\<lambda>b. if b then (1::int) else 0) initial
      (dyadic_source_word physical_collatz odd x n) = None"
  using assms collatz_physical_prefix_minimum_zero[of
      "dyadic_source_word physical_collatz odd x n"]
  by (simp add: first_negative_none_iff prefix_summary_guard_iff)

lemma antihydra_balanced_finite_endpoint:
  "map_option (\<lambda>E. antihydra_balanced.effect_apply E x)
      (antihydra_balanced.balanced.execute_balanced cache_admit n x) =
    Some (antihydra_family_orbit x n)"
  using antihydra_balanced.execute_balanced_endpoint
    [where cache_admit=cache_admit and n=n and x=x]
  by (simp add: antihydra_family_orbit_is_dyadic_source_orbit)

theorem antihydra_balanced_constructed_endpoint:
  "map_option (\<lambda>E. antihydra_balanced.effect_apply E x)
      (antihydra_balanced.construct_source_effect cache_admit n x) =
    Some (antihydra_family_orbit x n)"
  using antihydra_balanced.construct_source_effect_endpoint
    [where cache_admit=cache_admit and n=n and source=x]
  by (simp add: antihydra_family_orbit_is_dyadic_source_orbit)

lemma antihydra_prefix_summary_is_ledger:
  "prefix_summary (\<lambda>b. 2 - 3 * int b) bs =
    (ledger_word_delta bs, ledger_word_minprefix bs)"
proof (induction bs)
  case Nil
  then show ?case by simp
next
  case (Cons b bs)
  have below: "ledger_word_minprefix bs \<le> 0"
    using Cons.IH prefix_summary_minimum_nonpositive[of
      "\<lambda>b. 2 - 3 * int b" bs] by simp
  show ?case using Cons.IH below
    by (simp add: Let_def min_def; linarith)
qed

theorem antihydra_balanced_finite_ledger:
  "effect_delta (the (antihydra_balanced.balanced.execute_balanced cache_admit n x)) =
      antihydra_family_balance x 0 n"
  "effect_minimum (the (antihydra_balanced.balanced.execute_balanced cache_admit n x)) =
      antihydra_family_minimum x 0 n"
proof -
  let ?bs = "antihydra_family_bits x n"
  have effect: "the (antihydra_balanced.balanced.execute_balanced
      cache_admit n x) = antihydra_balanced.effect_word ?bs"
    by (simp add: antihydra_balanced.execute_balanced_source_effect
        antihydra_balanced.source_effect_def
        antihydra_family_bits_are_dyadic_source_word)
  have safety: "(effect_delta (antihydra_balanced.effect_word ?bs),
      effect_minimum (antihydra_balanced.effect_word ?bs)) =
      (ledger_word_delta ?bs, ledger_word_minprefix ?bs)"
    using antihydra_balanced.effect_word_safety[of ?bs]
      antihydra_prefix_summary_is_ledger[of ?bs] by simp
  show "effect_delta (the (antihydra_balanced.balanced.execute_balanced
      cache_admit n x)) = antihydra_family_balance x 0 n"
    using safety by (simp add: effect antihydra_family_balance_def)
  show "effect_minimum (the (antihydra_balanced.balanced.execute_balanced
      cache_admit n x)) = antihydra_family_minimum x 0 n"
    using safety by (simp add: effect antihydra_family_minimum_def)
qed

lemma antihydra_centered_odd_event_word:
  assumes "\<forall>b\<in>set bs. b < 2"
  shows "3 * (int (length bs) - int (sum_list bs)) =
    int (length bs) + ledger_word_delta bs"
  using assms
proof (induction bs)
  case Nil
  then show ?case by simp
next
  case (Cons b bs)
  have bit: "b=0 \<or> b=1" using Cons.prems by auto
  have tail: "3 * (int (length bs) - int (sum_list bs)) =
      int (length bs) + ledger_word_delta bs"
    using Cons.IH Cons.prems by simp
  show ?case using bit tail by (elim disjE; simp; linarith)
qed

text \<open>The support's event field counts odd return values \<open>a\<close>.
Mahler's centered odd values \<open>D=a-1\<close> are the complementary
events; neither count is a second successor state.\<close>

theorem antihydra_balanced_centered_odd_events:
  "3 * (int n - int (effect_events
      (the (antihydra_balanced.balanced.execute_balanced cache_admit n x)))) =
    int n + effect_delta
      (the (antihydra_balanced.balanced.execute_balanced cache_admit n x))"
proof -
  let ?bs = "antihydra_family_bits x n"
  have binary: "\<forall>b\<in>set ?bs. b<2"
    using antihydra_family_bits_binary by blast
  have events: "effect_events
      (the (antihydra_balanced.balanced.execute_balanced cache_admit n x)) =
      sum_list ?bs"
    by (simp add: antihydra_balanced.execute_balanced_source_effect
        antihydra_balanced.source_effect_def
        antihydra_family_bits_are_dyadic_source_word
        antihydra_balanced.effect_word_events)
  show ?thesis
    using antihydra_centered_odd_event_word[OF binary] events
      antihydra_balanced_finite_ledger(1)
        [where cache_admit=cache_admit and n=n and x=x]
    by (simp add: antihydra_family_balance_def)
qed

theorem antihydra_balanced_guarded_finite_apply:
  "antihydra_guarded_block_apply x initial n =
    (if 0 \<le> initial +
         effect_minimum (the (antihydra_balanced.balanced.execute_balanced cache_admit n x))
     then Some (antihydra_balanced.effect_apply
           (the (antihydra_balanced.balanced.execute_balanced cache_admit n x)) x,
           initial + effect_delta
             (the (antihydra_balanced.balanced.execute_balanced cache_admit n x)))
     else None)"
proof -
  let ?E = "the (antihydra_balanced.balanced.execute_balanced cache_admit n x)"
  have endpoint: "antihydra_balanced.effect_apply ?E x =
      antihydra_family_orbit x n"
    using antihydra_balanced_finite_endpoint
      [where cache_admit=cache_admit and n=n and x=x] by auto
  have delta: "effect_delta ?E = antihydra_family_balance x 0 n"
    by (rule antihydra_balanced_finite_ledger(1))
  have minimum: "effect_minimum ?E = antihydra_family_minimum x 0 n"
    by (rule antihydra_balanced_finite_ledger(2))
  show ?thesis using endpoint delta minimum
    by (simp add: antihydra_guarded_block_apply_def antihydra_block_safe_def
        antihydra_family_balance_def antihydra_family_minimum_def)
qed

theorem antihydra_constructed_guarded_finite_apply:
  "antihydra_guarded_block_apply x initial n =
    (if 0 \<le> initial +
         effect_minimum (the (antihydra_balanced.construct_source_effect
           cache_admit n x))
     then Some (antihydra_balanced.effect_apply
           (the (antihydra_balanced.construct_source_effect cache_admit n x)) x,
           initial + effect_delta
             (the (antihydra_balanced.construct_source_effect cache_admit n x)))
     else None)"
  using antihydra_balanced_guarded_finite_apply
    [where cache_admit=cache_admit and x=x and initial=initial and n=n]
  by (simp add: antihydra_balanced.construct_source_effect_correct
      antihydra_balanced.execute_balanced_source_effect)

text \<open>The Mahler consumer reads the same source-bound transfer
coordinates. Its cap remains distinct from the Antihydra ledger minimum.\<close>

definition mahler_action_from_effect :: "dyadic_effect \<Rightarrow> associated_action" where
  "mahler_action_from_effect E =
    (let T = effect_skew E;
         A = of_int (upper T) / of_int (lower T);
         B = -3 * ((of_int (upper T) + of_int (offset T) -
           of_int (lower T)) / of_int (lower T))
     in \<lparr>action_scale=A, action_offset=B,
         action_cap=Some (3/2*A+B)\<rparr>)"

definition mahler_centered_source_fold :: "nat \<Rightarrow> associated_action" where
  "mahler_centered_source_fold n =
    foldl (\<lambda>A b. associated_action_then A (mahler_bit_action (1-b)))
      associated_action_identity (antihydra_family_bits 8 n)"

lemma mahler_negative_cap_step:
  fixes A B :: rat
  assumes "e < 2" "3/2*A+B < 0"
  shows "associated_action_then
      \<lparr>action_scale=A, action_offset=B,
        action_cap=Some (3/2*A+B)\<rparr> (mahler_bit_action e) =
    \<lparr>action_scale=3/2*A,
      action_offset=3/2*B-3*of_nat e/2,
      action_cap=Some (3/2*(3/2*A) + (3/2*B-3*of_nat e/2))\<rparr>"
proof -
  have unsaturated:
    "associated_action_apply (mahler_bit_action e) (3/2*A+B) =
      3/2*(3/2*A+B) - 3*of_nat e/2"
    using mahler_bit_action_negative_unsaturated(1)[OF assms] .
  have "e=0 \<or> e=1" using assms(1) by arith
  then show ?thesis using assms(2) unsaturated
    by (elim disjE;
        simp add: associated_action_then_def associated_cap_min_def
          mahler_bit_action_def min_def algebra_simps;
        linarith)
qed

lemma mahler_effect_step:
  assumes "b < 2" "0 < lower (effect_skew E)"
    "(case action_cap (mahler_action_from_effect E) of
       Some c \<Rightarrow> c < 0 | None \<Rightarrow> False)"
  shows "mahler_action_from_effect
      (effect_then E (antihydra_balanced.effect_atom b)) =
    associated_action_then (mahler_action_from_effect E)
      (mahler_bit_action (1-b))"
proof -
  let ?X = "of_int (upper (effect_skew E)) /
    of_int (lower (effect_skew E)) :: rat"
  let ?Y = "-3 * ((of_int (upper (effect_skew E)) +
    of_int (offset (effect_skew E)) - of_int (lower (effect_skew E))) /
    of_int (lower (effect_skew E))) :: rat"
  have nonzero: "lower (effect_skew E) \<noteq> 0" using assms(2) by simp
  have binary_cases: "b=0 \<or> b=1" using assms(1) by arith
  have A: "of_int (upper (effect_skew
      (effect_then E (antihydra_balanced.effect_atom b)))) /
        of_int (lower (effect_skew
      (effect_then E (antihydra_balanced.effect_atom b)))) =
      (3/2::rat) * (of_int (upper (effect_skew E)) /
        of_int (lower (effect_skew E)))"
    using nonzero unfolding effect_then_def shared_skew_then_def
      antihydra_balanced.effect_atom_def
    by (simp add: field_simps algebra_simps)
  have B: "-3 * ((of_int (upper (effect_skew
      (effect_then E (antihydra_balanced.effect_atom b)))) +
      of_int (offset (effect_skew
      (effect_then E (antihydra_balanced.effect_atom b)))) -
      of_int (lower (effect_skew
      (effect_then E (antihydra_balanced.effect_atom b))))) /
      of_int (lower (effect_skew
      (effect_then E (antihydra_balanced.effect_atom b))))) =
      (3/2::rat) * (-3 * ((of_int (upper (effect_skew E)) +
        of_int (offset (effect_skew E)) - of_int (lower (effect_skew E))) /
        of_int (lower (effect_skew E)))) - 3 * of_nat (1-b)/2"
    using binary_cases nonzero
    unfolding effect_then_def shared_skew_then_def
      antihydra_balanced.effect_atom_def
    by (elim disjE; simp add: field_simps algebra_simps)
  have bit: "1-b < 2" using assms(1) by arith
  have negative: "(3/2::rat) *
      (of_int (upper (effect_skew E)) / of_int (lower (effect_skew E))) +
      (-3 * ((of_int (upper (effect_skew E)) +
        of_int (offset (effect_skew E)) - of_int (lower (effect_skew E))) /
        of_int (lower (effect_skew E)))) < 0"
    using assms(3) nonzero
    by (simp add: mahler_action_from_effect_def Let_def
        field_simps algebra_simps)
  have input: "mahler_action_from_effect E =
      \<lparr>action_scale=?X, action_offset=?Y,
        action_cap=Some (3/2*?X+?Y)\<rparr>"
    by (simp only: mahler_action_from_effect_def Let_def)
  have output_eq: "mahler_action_from_effect
      (effect_then E (antihydra_balanced.effect_atom b)) =
      \<lparr>action_scale=3/2*?X,
        action_offset=3/2*?Y-3*of_nat (1-b)/2,
        action_cap=Some (3/2*(3/2*?X) +
          (3/2*?Y-3*of_nat (1-b)/2))\<rparr>"
    by (simp only: mahler_action_from_effect_def Let_def A B)
  show ?thesis using mahler_negative_cap_step[OF bit negative]
    by (simp only: input output_eq)
qed

lemma mahler_effect_step_negative:
  assumes bit: "b < 2" and denominator: "0 < lower (effect_skew E)"
    and negative: "\<exists>c<0. action_cap (mahler_action_from_effect E) = Some c"
  shows "\<exists>c<0. action_cap (mahler_action_from_effect
      (effect_then E (antihydra_balanced.effect_atom b))) = Some c"
proof -
  let ?A = "of_int (upper (effect_skew E)) / of_int (lower (effect_skew E)) :: rat"
  let ?B = "-3 * ((of_int (upper (effect_skew E)) +
      of_int (offset (effect_skew E)) - of_int (lower (effect_skew E))) /
      of_int (lower (effect_skew E))) :: rat"
  have old: "3/2*?A+?B < 0"
    using negative by (simp add: mahler_action_from_effect_def Let_def)
  have cap_condition: "(case action_cap (mahler_action_from_effect E) of
      Some c \<Rightarrow> c < 0 | None \<Rightarrow> False)"
    using negative by (cases "action_cap (mahler_action_from_effect E)") auto
  have next_bit: "1-b < 2" using bit by arith
  have input_eq: "mahler_action_from_effect E =
      \<lparr>action_scale=?A, action_offset=?B,
        action_cap=Some (3/2*?A+?B)\<rparr>"
    by (simp only: mahler_action_from_effect_def Let_def)
  have composed: "mahler_action_from_effect
      (effect_then E (antihydra_balanced.effect_atom b)) =
      associated_action_then (mahler_action_from_effect E)
        (mahler_bit_action (1-b))"
    by (rule mahler_effect_step[OF bit denominator cap_condition])
  have step_eq: "associated_action_then (mahler_action_from_effect E)
      (mahler_bit_action (1-b)) =
      \<lparr>action_scale=3/2*?A,
        action_offset=3/2*?B-3*of_nat (1-b)/2,
        action_cap=Some (3/2*(3/2*?A) +
          (3/2*?B-3*of_nat (1-b)/2))\<rparr>"
    using mahler_negative_cap_step[OF next_bit old]
    by (simp only: input_eq)
  have next_cap: "action_cap (mahler_action_from_effect
      (effect_then E (antihydra_balanced.effect_atom b))) =
      Some (3/2*(3/2*?A) + (3/2*?B - 3*of_nat (1-b)/2))"
    using composed step_eq by simp
  have "3/2*(3/2*?A) + (3/2*?B - 3*of_nat (1-b)/2) < 0"
  proof -
    have nonnegative: "(0::rat) \<le> of_nat (1-b)" by simp
    show ?thesis using old nonnegative by linarith
  qed
  with next_cap show ?thesis by blast
qed

lemma mahler_centered_source_fold_step:
  "mahler_centered_source_fold (Suc n) =
    associated_action_then (mahler_centered_source_fold n)
      (mahler_bit_action (1 - antihydra_family_orbit 8 n mod 2))"
proof -
  have bits: "antihydra_family_bits 8 (Suc n) =
      antihydra_family_bits 8 n @ [antihydra_family_orbit 8 n mod 2]"
    using antihydra_family_bits_append[of 8 n 1] by simp
  show ?thesis
    by (simp only: mahler_centered_source_fold_def bits
        foldl_append foldl.simps)
qed

lemma antihydra_source_effect_step:
  "antihydra_balanced.source_effect (Suc n) 8 =
    effect_then (antihydra_balanced.source_effect n 8)
      (antihydra_balanced.effect_atom
        (antihydra_family_orbit 8 n mod 2))"
proof -
  have one: "antihydra_balanced.source_effect 1 y =
      antihydra_balanced.effect_atom (y mod 2)" for y
    by (simp add: antihydra_balanced.source_effect_def
        effect_then_identity effect_admitted_def
        antihydra_balanced.effect_atom_def)
  show ?thesis
    using antihydra_balanced.source_effect_append
      [where a=n and b=1 and x=8]
    by (simp only: Suc_eq_plus1 one
        antihydra_family_orbit_is_dyadic_source_orbit)
qed

lemma mahler_source_two_base:
  "mahler_centered_source_fold 2 = mahler_source_two_prefix"
  "mahler_action_from_effect (antihydra_balanced.source_effect 2 8) =
      mahler_source_two_prefix"
proof -
  have bits: "antihydra_family_bits 8 2 = [0,0]"
    by (subst numeral_2_eq_2) (simp add: antihydra_family_step_def)
  have dyadic_bits:
    "dyadic_source_word antihydra_family_step (\<lambda>a. a mod 2) 8 2 = [0,0]"
    by (subst numeral_2_eq_2) (simp add: antihydra_family_step_def)
  show "mahler_centered_source_fold 2 = mahler_source_two_prefix"
    by (simp add: mahler_centered_source_fold_def bits
        mahler_source_two_prefix_def)
  show "mahler_action_from_effect (antihydra_balanced.source_effect 2 8) =
      mahler_source_two_prefix"
    by (simp add: mahler_action_from_effect_def
        mahler_source_two_prefix_exact
        antihydra_balanced.source_effect_def dyadic_bits
        antihydra_balanced.effect_atom_def effect_then_def
        effect_identity_def shared_skew_then_def shared_skew_identity_def
        Let_def)
qed

theorem mahler_centered_source_fold_is_demanded_effect:
  "mahler_centered_source_fold (2+k) =
    mahler_action_from_effect (antihydra_balanced.source_effect (2+k) 8)"
  "\<exists>c<0. action_cap
    (mahler_action_from_effect (antihydra_balanced.source_effect (2+k) 8)) = Some c"
proof (induction k)
  case 0
  then show "mahler_centered_source_fold (2+0) =
      mahler_action_from_effect (antihydra_balanced.source_effect (2+0) 8)"
    using mahler_source_two_base by simp
  show "\<exists>c<0. action_cap
      (mahler_action_from_effect
        (antihydra_balanced.source_effect (2+0) 8)) = Some c"
    by (simp add: mahler_source_two_base mahler_source_first_two_caps)
next
  case (Suc k)
  let ?n = "2+k"
  let ?E = "antihydra_balanced.source_effect ?n 8"
  let ?b = "antihydra_family_orbit 8 ?n mod 2"
  have bit: "?b < 2" by simp
  have denominator: "0 < lower (effect_skew ?E)"
    by (simp only: antihydra_balanced.source_effect_def
        antihydra_balanced.effect_word_denominator
        dyadic_source_word_length; simp)
  have negative: "\<exists>c<0. action_cap (mahler_action_from_effect ?E) = Some c"
    by (rule Suc.IH(2))
  have cap_condition: "(case action_cap (mahler_action_from_effect ?E) of
      Some c \<Rightarrow> c < 0 | None \<Rightarrow> False)"
    using negative by (cases "action_cap (mahler_action_from_effect ?E)") auto
  have transported_step: "mahler_action_from_effect
      (effect_then ?E (antihydra_balanced.effect_atom ?b)) =
      associated_action_then (mahler_action_from_effect ?E)
        (mahler_bit_action (1-?b))"
    by (rule mahler_effect_step[OF bit denominator cap_condition])
  show "mahler_centered_source_fold (2+Suc k) =
      mahler_action_from_effect (antihydra_balanced.source_effect (2+Suc k) 8)"
    using Suc.IH(1) transported_step
    by (simp add: mahler_centered_source_fold_step
        antihydra_source_effect_step)
  show "\<exists>c<0. action_cap
      (mahler_action_from_effect
        (antihydra_balanced.source_effect (2+Suc k) 8)) = Some c"
    using mahler_effect_step_negative[OF bit denominator negative]
    by (simp add: antihydra_source_effect_step)
qed

lemma mahler_source_eight_initial_caps:
  "action_cap (mahler_centered_source_fold 0) = None"
  "action_cap (mahler_centered_source_fold 1) = Some (3/4)"
  by (simp_all add: mahler_centered_source_fold_def
      mahler_source_first_two_caps mahler_bit_action_admitted
      antihydra_family_step_def associated_action_identity_def
      mahler_bit_action_def associated_action_then_def
      associated_cap_min_def)

theorem mahler_source_eight_cap_failure_iff:
  "(\<exists>c\<le>(0::rat). action_cap (mahler_centered_source_fold n) = Some c)
    \<longleftrightarrow> 2 \<le> n"
proof
  assume failed: "\<exists>c\<le>(0::rat).
      action_cap (mahler_centered_source_fold n) = Some c"
  show "2 \<le> n"
  proof (rule ccontr)
    assume "\<not> 2 \<le> n"
    then have "n=0 \<or> n=1" by arith
    with failed mahler_source_eight_initial_caps show False by auto
  qed
next
  assume lower: "2 \<le> n"
  define k where "k=n-2"
  have extent: "n=2+k" using lower unfolding k_def by arith
  obtain c where "c<0" and cap:
      "action_cap (mahler_centered_source_fold (2+k)) = Some c"
    using mahler_centered_source_fold_is_demanded_effect(1,2)[of k]
    by auto
  with extent show "\<exists>c\<le>(0::rat).
      action_cap (mahler_centered_source_fold n) = Some c" by auto
qed

corollary mahler_source_eight_first_failure_index:
  "(LEAST n. \<exists>c\<le>(0::rat).
      action_cap (mahler_centered_source_fold n) = Some c) = 2"
  by (simp only: mahler_source_eight_cap_failure_iff;
      rule Least_equality; simp)

theorem mahler_centered_source_fold_is_demanded_projection:
  fixes cache_admit n
  assumes "2 \<le> n"
  defines "E \<equiv> the (antihydra_balanced.balanced.execute_balanced cache_admit n 8)"
  shows "mahler_centered_source_fold n =
    mahler_demanded_projection n
      (upper (effect_skew E)) (offset (effect_skew E))
      (lower (effect_skew E))"
proof -
  define k where "k=n-2"
  have n: "n=2+k" using assms(1) unfolding k_def by arith
  have effect: "E = antihydra_balanced.source_effect n 8"
    by (simp add: E_def antihydra_balanced.execute_balanced_source_effect)
  show ?thesis using mahler_centered_source_fold_is_demanded_effect(1)[of k]
    by (simp add: n effect mahler_action_from_effect_def
        mahler_demanded_projection_def Let_def)
qed

theorem mahler_centered_source_fold_all_prefixes:
  fixes cache_admit n
  defines "E \<equiv> the (antihydra_balanced.construct_source_effect cache_admit n 8)"
  shows "mahler_centered_source_fold n =
    mahler_demanded_projection n
      (upper (effect_skew E)) (offset (effect_skew E))
      (lower (effect_skew E))"
proof (cases "2 \<le> n")
  case True
  have projection: "mahler_centered_source_fold n =
      mahler_demanded_projection n
        (upper (effect_skew (the
          (antihydra_balanced.balanced.execute_balanced cache_admit n 8))))
        (offset (effect_skew (the
          (antihydra_balanced.balanced.execute_balanced cache_admit n 8))))
        (lower (effect_skew (the
          (antihydra_balanced.balanced.execute_balanced cache_admit n 8))))"
    using mahler_centered_source_fold_is_demanded_projection
      [where cache_admit=cache_admit and n=n] True by simp
  show ?thesis using projection
    by (simp add: E_def antihydra_balanced.construct_source_effect_correct
        antihydra_balanced.execute_balanced_source_effect)
next
  case False
  then have "n=0 \<or> n=1" by arith
  then show ?thesis
    by (elim disjE;
        simp add: E_def antihydra_balanced.construct_source_effect_correct
          mahler_centered_source_fold_def
          mahler_demanded_projection_def
          antihydra_balanced.source_effect_def
          antihydra_balanced.effect_atom_def effect_then_def
          effect_identity_def shared_skew_then_def shared_skew_identity_def
          mahler_bit_action_def associated_action_identity_def
          antihydra_family_step_def associated_action_then_def
          associated_cap_min_def Let_def)
qed

theorem mahler_constructed_source_eight_cap_failure_iff:
  fixes cache_admit n
  defines "E \<equiv> the (antihydra_balanced.construct_source_effect cache_admit n 8)"
  shows "(\<exists>c\<le>(0::rat). action_cap
      (mahler_demanded_projection n
        (upper (effect_skew E)) (offset (effect_skew E))
        (lower (effect_skew E))) = Some c) \<longleftrightarrow> 2 \<le> n"
proof -
  have projection: "mahler_centered_source_fold n =
      mahler_demanded_projection n
        (upper (effect_skew E)) (offset (effect_skew E))
        (lower (effect_skew E))"
    using mahler_centered_source_fold_all_prefixes
      [where cache_admit=cache_admit and n=n] by (simp add: E_def)
  show ?thesis using projection mahler_source_eight_cap_failure_iff[of n]
    by simp
qed

lemma antihydra_balanced_mahler_from_transfer:
  fixes cache_admit n
  assumes "2 \<le> n"
  defines "E \<equiv> the (antihydra_balanced.balanced.execute_balanced cache_admit n 8)"
  shows "mahler_centered_source_fold n =
    associated_action_then mahler_source_two_prefix
      (mahler_source_tail
        (of_int (upper (effect_skew E)) /
          of_int (lower (effect_skew E)))
        (-3 * ((of_int (upper (effect_skew E)) +
          of_int (offset (effect_skew E)) -
          of_int (lower (effect_skew E))) /
          of_int (lower (effect_skew E)))))"
proof -
  have projection: "mahler_centered_source_fold n =
      mahler_demanded_projection n
        (upper (effect_skew E)) (offset (effect_skew E))
        (lower (effect_skew E))"
    using mahler_centered_source_fold_is_demanded_projection
      [where cache_admit=cache_admit and n=n] assms(1)
    by (simp add: E_def)
  show ?thesis using projection assms(1)
    by (simp add: mahler_demanded_projection_def Let_def
        mahler_source_coefficients_determine_action)
qed

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms collatz_balanced_finite_endpoint
      collatz_balanced_constructed_endpoint
      collatz_physical_prefix_minimum_zero
      collatz_balanced_finite_minimum_zero
      collatz_physical_first_negative_unreachable
      antihydra_balanced_finite_endpoint
      antihydra_balanced_constructed_endpoint
      antihydra_prefix_summary_is_ledger
      antihydra_balanced_finite_ledger
      antihydra_centered_odd_event_word
      antihydra_balanced_centered_odd_events
      antihydra_balanced_guarded_finite_apply
      antihydra_constructed_guarded_finite_apply
      mahler_negative_cap_step mahler_effect_step
      mahler_effect_step_negative mahler_centered_source_fold_step
      antihydra_source_effect_step mahler_source_two_base
      mahler_centered_source_fold_is_demanded_effect
      mahler_source_eight_initial_caps mahler_source_eight_cap_failure_iff
      mahler_source_eight_first_failure_index
      mahler_centered_source_fold_is_demanded_projection
      mahler_centered_source_fold_all_prefixes
      mahler_constructed_source_eight_cap_failure_iff
      antihydra_balanced_mahler_from_transfer})
    then () else error "Balanced dyadic family bridge depends on an oracle";
\<close>

end
