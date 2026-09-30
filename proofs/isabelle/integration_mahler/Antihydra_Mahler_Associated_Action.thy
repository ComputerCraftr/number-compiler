theory Antihydra_Mahler_Associated_Action
  imports "Associated_Action_Core.Associated_Action_Pullback"
    "Antihydra.Antihydra_Mahler_Skew"
begin

text \<open>The production Mahler consumer indexes its bit actions by the
centered parity \<open>e = D mod 2\<close>.  The Antihydra arithmetic cylinder stores
the complementary return bit \<open>b = 1-e\<close>.  These predicates therefore
remain separate even when both are read from the same authenticated source
cylinder.\<close>

definition mahler_bit_action :: "nat \<Rightarrow> associated_action" where
  "mahler_bit_action e =
    \<lparr>action_scale=3/2, action_offset=-(3 * of_nat e)/2,
     action_cap=Some (if e=0 then 9/4 else 3/4)\<rparr>"

lemma mahler_bit_action_admitted:
  "associated_action_admitted (mahler_bit_action e)"
  by (simp add: associated_action_admitted_def mahler_bit_action_def)

lemma mahler_bit_action_negative_unsaturated:
  assumes "e < 2" "x < 0"
  shows "associated_action_apply (mahler_bit_action e) x =
      3/2*x - (3 * of_nat e)/2"
    "associated_action_apply (mahler_bit_action e) x < 0"
proof -
  have bit: "e=0 \<or> e=1" using assms(1) by arith
  show "associated_action_apply (mahler_bit_action e) x =
      3/2*x - (3 * of_nat e)/2"
    using bit assms(2)
    by (elim disjE; simp add: associated_action_apply_def
        mahler_bit_action_def min_def; linarith)
  show "associated_action_apply (mahler_bit_action e) x < 0"
    using bit assms(2)
    by (elim disjE; simp add: associated_action_apply_def
        mahler_bit_action_def min_def; linarith)
qed


text \<open>
  A source-selected positive odd event is the chronological word one followed
  by q-1 zero symbols. Its saturated consumer has a closed action; the proof
  below removes the predicate-bit fold after q has been authenticated by the
  source classifier. It does not authenticate q from a supplied event word or
  establish an all-time source barrier. Index zero is explicitly identity.
\<close>

definition mahler_odd_event_zero_tail :: "nat \<Rightarrow> associated_action" where
  "mahler_odd_event_zero_tail n =
    foldl associated_action_then (mahler_bit_action 1)
      (replicate n (mahler_bit_action 0))"

lemma mahler_odd_event_zero_tail_exact:
  "mahler_odd_event_zero_tail n =
    \<lparr>action_scale=(3/2)^(Suc n), action_offset=-((3/2)^(Suc n)),
      action_cap=Some (min (9/4) ((3/4)*(3/2)^n))\<rparr>"
proof -
  have run: "foldl associated_action_then
      \<lparr>action_scale=3/2, action_offset=-(3/2), action_cap=Some (3/4)\<rparr>
      (replicate n \<lparr>action_scale=3/2, action_offset=0, action_cap=Some (9/4)\<rparr>) =
    \<lparr>action_scale=(3/2)^n*(3/2), action_offset=(3/2)^n*(-(3/2)),
      action_cap=Some (if n=0 then 3/4 else min (9/4) ((3/2)^n*(3/4)))\<rparr>"
    by (rule associated_action_dilation_tail) simp_all
  show ?thesis using run
    by (cases "n=0"; simp add: mahler_odd_event_zero_tail_def mahler_bit_action_def
        power_Suc algebra_simps min_def)
qed

definition mahler_maximal_odd_event :: "nat \<Rightarrow> associated_action" where
  "mahler_maximal_odd_event q =
    (if q=0 then associated_action_identity else mahler_odd_event_zero_tail (q-1))"

lemma mahler_maximal_odd_event_identity:
  "mahler_maximal_odd_event 0 = associated_action_identity"
  by (simp add: mahler_maximal_odd_event_def)

theorem mahler_maximal_odd_event_word_refinement:
  assumes "0 < q"
  shows "mahler_maximal_odd_event q =
    foldl associated_action_then associated_action_identity
      (map mahler_bit_action ([1] @ replicate (q-1) 0))"
  using assms
  by (simp add: mahler_maximal_odd_event_def mahler_odd_event_zero_tail_def)

theorem mahler_maximal_odd_event_closed:
  assumes "0 < q"
  shows "mahler_maximal_odd_event q =
    \<lparr>action_scale=(3/2)^q, action_offset=-((3/2)^q),
      action_cap=Some (min (9/4) ((3/4)*(3/2)^(q-1)))\<rparr>"
  using assms
  by (simp add: mahler_maximal_odd_event_def mahler_odd_event_zero_tail_exact)

corollary mahler_maximal_odd_event_closed_scale:
  assumes "0 < q"
  shows "mahler_maximal_odd_event q =
    \<lparr>action_scale=(3/2)^q, action_offset=-((3/2)^q),
      action_cap=Some (min (9/4) ((3/2)^q/2))\<rparr>"
proof -
  have power: "((3/2)::rat)^q = (3/2)*(3/2)^(q-1)"
    using power_Suc[of "(3/2)::rat" "q-1"] assms by simp
  have cap: "((3/2)::rat)^q/2 = (3/4)*(3/2)^(q-1)"
    using power by linarith
  show ?thesis
    using mahler_maximal_odd_event_closed[OF assms]
    by (simp only: cap)
qed

corollary mahler_maximal_odd_event_apply:
  assumes "0 < q"
  shows "associated_action_apply (mahler_maximal_odd_event q) margin =
    min (min (9/4) ((3/4)*(3/2)^(q-1))) ((3/2)^q*(margin-1))"
  by (simp add: mahler_maximal_odd_event_closed[OF assms]
      associated_action_apply_def algebra_simps)

definition mahler_source_two_prefix :: associated_action where
  "mahler_source_two_prefix =
    associated_action_then (mahler_bit_action 1) (mahler_bit_action 1)"

lemma mahler_source_two_prefix_exact:
  "mahler_source_two_prefix =
    \<lparr>action_scale=9/4, action_offset=-15/4, action_cap=Some (-3/8)\<rparr>"
  by (simp add: mahler_source_two_prefix_def mahler_bit_action_def
      associated_action_then_def associated_cap_min_def min_def)

definition mahler_source_tail :: "rat \<Rightarrow> rat \<Rightarrow> associated_action" where
  "mahler_source_tail A B =
    \<lparr>action_scale=A/(9/4),
     action_offset=B - (A/(9/4)) * (-15/4), action_cap=None\<rparr>"

lemma mahler_source_tail_admitted:
  assumes "0 < A"
  shows "associated_action_admitted (mahler_source_tail A B)"
  using assms
  by (simp add: associated_action_admitted_def mahler_source_tail_def)

theorem mahler_source_coefficients_determine_action:
  "associated_action_then mahler_source_two_prefix (mahler_source_tail A B) =
    \<lparr>action_scale=A, action_offset=B,
     action_cap=Some (3/2*A+B)\<rparr>"
  by (simp add: mahler_source_two_prefix_exact mahler_source_tail_def
      associated_action_then_def associated_cap_min_def min_def;
      linarith)

corollary mahler_source_cap_from_centered_transfer:
  fixes upper offset lower :: int
    and A Bc B :: rat
  assumes "lower \<noteq> 0"
  defines "A \<equiv> of_int upper / of_int lower"
    and "Bc \<equiv> (of_int upper + of_int offset - of_int lower) / of_int lower"
    and "B \<equiv> -3 * Bc"
  shows "action_cap
      (associated_action_then mahler_source_two_prefix (mahler_source_tail A B)) =
    Some (3/2*A+B)"
  by (simp add: mahler_source_coefficients_determine_action)

lemma mahler_source_first_two_caps:
  "action_cap (mahler_bit_action 1) = Some (3/4)"
  "action_cap mahler_source_two_prefix = Some (-3/8)"
  "(0::rat) < 3/4"
  "(-3/8::rat) < 0"
  by (simp_all add: mahler_bit_action_def mahler_source_two_prefix_exact)

theorem centered_word_11_has_distinct_mahler_and_ledger_outcomes:
  "action_cap mahler_source_two_prefix = Some (-3/8) \<and>
    sk_minprefix (skew_word [0,0]) = 0 \<and>
    sk_delta (skew_word [0,0]) = 4"
  by (simp add: mahler_source_two_prefix_exact skew_atom_def skew_identity_def
      skew_then_def)

text \<open>The production demand now reads the authenticated dyadic root's
three integer transfer coordinates directly. This is the executable
calculation in AntihydraArithmeticImageWorkspace.project; it does not
construct a second associated-action arena. The source/prefix checks are
admission premises of the consumer, and the first-failure index remains a
different output from the ledger minimum.\<close>

definition mahler_demanded_projection ::
  "nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> associated_action" where
  "mahler_demanded_projection n u_coeff o_coeff d_coeff =
    (let A = of_int u_coeff / of_int d_coeff;
         B = -3 * ((of_int u_coeff + of_int o_coeff - of_int d_coeff)
           / of_int d_coeff)
     in \<lparr>action_scale=A, action_offset=B,
       action_cap=(if n=0 then None else if n=1 then Some (3/4)
                   else Some (3/2*A+B))\<rparr>)"

theorem demanded_projection_reuses_two_prefix:
  fixes upper offset lower :: int
  assumes "2 \<le> n" "lower \<noteq> 0"
  defines "A \<equiv> of_int upper / of_int lower"
    and "B \<equiv> -3 * ((of_int upper + of_int offset - of_int lower)
      / of_int lower)"
  shows "mahler_demanded_projection n upper offset lower =
    associated_action_then mahler_source_two_prefix (mahler_source_tail A B)"
  using assms by (simp add: mahler_demanded_projection_def
    mahler_source_coefficients_determine_action Let_def)

lemma demanded_projection_pinned_prefix:
  "mahler_demanded_projection 0 1 0 1 =
     \<lparr>action_scale=1, action_offset=0, action_cap=None\<rparr>"
  "mahler_demanded_projection 1 3 0 2 = mahler_bit_action 1"
  "mahler_demanded_projection 2 9 0 4 = mahler_source_two_prefix"
  by (simp_all add: mahler_demanded_projection_def mahler_bit_action_def
    mahler_source_two_prefix_exact Let_def)

theorem demanded_projection_negative_cap_scope:
  fixes upper offset lower :: int
  assumes "2 \<le> n" "lower \<noteq> 0"
    "3/2 * (of_int upper / of_int lower) -
      3 * ((of_int upper + of_int offset - of_int lower)
        / of_int lower) < (0::rat)"
  shows "\<exists>cap<0. action_cap
    (mahler_demanded_projection n upper offset lower) = Some cap"
proof -
  let ?A = "(of_int upper / of_int lower :: rat)"
  let ?C = "((of_int upper + of_int offset - of_int lower)
    / of_int lower :: rat)"
  have cap: "action_cap (mahler_demanded_projection n upper offset lower) =
      Some (3/2 * ?A - 3 * ?C)"
    using assms(1)
    by (simp add: mahler_demanded_projection_def Let_def algebra_simps
      add_divide_distrib[symmetric])
  have negative: "(3/2::rat) * ?A - 3 * ?C < 0"
    by (rule assms(3))
  show ?thesis using cap negative by blast
qed

text \<open>The new production projection checks the source root, seed eight,
law, extent and centered prefix before using this formula. Those runtime
checks still need a refinement map from the exact Python handles to these
assumptions. The algebra does not turn ledger safety into Mahler margin
positivity or establish an all-time invariant.\<close>

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms mahler_bit_action_admitted mahler_bit_action_negative_unsaturated
      mahler_odd_event_zero_tail_exact
      mahler_maximal_odd_event_identity mahler_maximal_odd_event_word_refinement
      mahler_maximal_odd_event_closed mahler_maximal_odd_event_closed_scale
      mahler_maximal_odd_event_apply
      mahler_source_two_prefix_exact mahler_source_tail_admitted
      mahler_source_coefficients_determine_action
      mahler_source_cap_from_centered_transfer mahler_source_first_two_caps
      centered_word_11_has_distinct_mahler_and_ledger_outcomes
      demanded_projection_reuses_two_prefix demanded_projection_pinned_prefix
      demanded_projection_negative_cap_scope}) then ()
    else error "Antihydra Mahler associated action depends on an oracle";
\<close>

end
