theory Antihydra_Mahler_Associated_Action
  imports "Associated_Action_Core.Associated_Action_Pullback"
    "Antihydra.Antihydra_Mahler_Skew"
    "Shared_Growth_Arithmetic.Homogeneous_Growth_Scale"
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

text \<open>
  The integer normal form used by the Mahler consumer stores the denominator
  and gain exponents separately from the affine numerator.  This keeps the
  composition arithmetic integral until the final associated-action view:
  denominator \<open>2^(R+2)\<close>, gain \<open>4*3^R\<close>, offset numerator
  \<open>B\<close>, and optional cap numerator \<open>C\<close>.
\<close>

record mahler_nf =
  nf_R :: nat
  nf_B :: int
  nf_C :: "int option"

definition mahler_nf_den :: "nat \<Rightarrow> int" where
  "mahler_nf_den R = 2^(R+2)"

definition mahler_nf_gain :: "nat \<Rightarrow> int" where
  "mahler_nf_gain R = 4*3^R"

definition mahler_nf_action :: "mahler_nf \<Rightarrow> associated_action" where
  "mahler_nf_action A =
    \<lparr>action_scale = of_int (mahler_nf_gain (nf_R A)) /
        of_int (mahler_nf_den (nf_R A)),
     action_offset = of_int (nf_B A) /
        of_int (mahler_nf_den (nf_R A)),
     action_cap = map_option
       (\<lambda>C. of_int C / of_int (mahler_nf_den (nf_R A))) (nf_C A)\<rparr>"

definition mahler_nf_then :: "mahler_nf \<Rightarrow> mahler_nf \<Rightarrow> mahler_nf" where
  "mahler_nf_then A B =
    \<lparr>nf_R = nf_R A + nf_R B,
     nf_B = 3^(nf_R B) * nf_B A + 2^(nf_R A) * nf_B B,
     nf_C = (case (nf_C A, nf_C B) of
       (None, None) \<Rightarrow> None
     | (None, Some Cb) \<Rightarrow> Some (2^(nf_R A) * Cb)
     | (Some Ca, None) \<Rightarrow>
         Some (3^(nf_R B) * Ca + 2^(nf_R A) * nf_B B)
     | (Some Ca, Some Cb) \<Rightarrow>
         Some (min (3^(nf_R B) * Ca + 2^(nf_R A) * nf_B B)
                    (2^(nf_R A) * Cb)))\<rparr>"

definition mahler_nf_identity :: mahler_nf where
  "mahler_nf_identity = \<lparr>nf_R=0, nf_B=0, nf_C=None\<rparr>"

text \<open>The exponent stored by the live integer normal form is also its
homogeneous growth extent.  The projection forgets affine numerator and cap
data only for the growth consumer; the complete normal form remains the owner
for source-dependent arithmetic.\<close>

definition mahler_temporal_growth_extent :: "nat \<Rightarrow> homogeneous_growth_scale" where
  "mahler_temporal_growth_extent R =
    homogeneous_growth_power mahler_temporal_growth_unit R"

definition mahler_nf_growth_projection :: "mahler_nf \<Rightarrow> homogeneous_growth_scale" where
  "mahler_nf_growth_projection A = mahler_temporal_growth_extent (nf_R A)"

lemma mahler_temporal_growth_extent_pair:
  "mahler_temporal_growth_extent R = \<lparr>growths=R, halvings=R\<rparr>"
  by (simp add: mahler_temporal_growth_extent_def
      homogeneous_growth_power_def mahler_temporal_growth_unit_def)

theorem mahler_nf_extent_projection:
  "mahler_nf_growth_projection A =
    \<lparr>growths=nf_R A, halvings=nf_R A\<rparr>"
  by (simp add: mahler_nf_growth_projection_def
      mahler_temporal_growth_extent_pair)

theorem mahler_nf_growth_projection_then:
  "mahler_nf_growth_projection (mahler_nf_then A B) =
    homogeneous_growth_then (mahler_nf_growth_projection A)
      (mahler_nf_growth_projection B)"
  by (cases A; cases B; simp add: mahler_nf_growth_projection_def
      mahler_temporal_growth_extent_def mahler_nf_then_def
      homogeneous_growth_power_def homogeneous_growth_then_def
      mahler_temporal_growth_unit_def algebra_simps)

theorem mahler_nf_live_scale_exact:
  "action_scale (mahler_nf_action A) =
    homogeneous_growth_ratio (mahler_nf_growth_projection A)"
  by (simp add: mahler_nf_action_def mahler_nf_growth_projection_def
      mahler_temporal_growth_extent_def mahler_nf_gain_def mahler_nf_den_def
      homogeneous_growth_ratio_def homogeneous_growth_power_def
      mahler_temporal_growth_unit_def field_simps power_add algebra_simps)

theorem mahler_nf_growth_power_exact:
  "homogeneous_growth_ratio (mahler_nf_growth_projection A) =
    (3/2::rat)^(nf_R A)"
  using mahler_nf_live_scale_exact[of A]
  by (simp add: mahler_temporal_extent_exact
      mahler_nf_growth_projection_def mahler_temporal_growth_extent_def)

lemma mahler_nf_growth_projection_radix_slope:
  "homogeneous_growth_radix_slope (mahler_nf_growth_projection A) b =
    of_nat (nf_R A) * (ln 3 - ln 2) / ln (of_nat b)"
  by (simp add: homogeneous_growth_radix_slope_def
      mahler_nf_extent_projection algebra_simps)

lemma mahler_nf_then_identity:
  "mahler_nf_then mahler_nf_identity A = A"
  "mahler_nf_then A mahler_nf_identity = A"
proof -
  show "mahler_nf_then mahler_nf_identity A = A"
    by (cases A; cases "nf_C A";
        simp_all add: mahler_nf_then_def mahler_nf_identity_def)
  show "mahler_nf_then A mahler_nf_identity = A"
    by (cases A; cases "nf_C A";
        simp_all add: mahler_nf_then_def mahler_nf_identity_def)
qed

lemma mahler_nf_action_admitted:
  "associated_action_admitted (mahler_nf_action A)"
  by (simp add: associated_action_admitted_def mahler_nf_action_def
      mahler_nf_gain_def mahler_nf_den_def)

theorem mahler_nf_identity_action:
  "mahler_nf_action mahler_nf_identity = associated_action_identity"
  by (simp add: mahler_nf_action_def mahler_nf_identity_def
      mahler_nf_gain_def mahler_nf_den_def associated_action_identity_def)

theorem mahler_nf_action_then:
  "mahler_nf_action (mahler_nf_then A B) =
    associated_action_then (mahler_nf_action A) (mahler_nf_action B)"
  by (cases A; cases B; cases "nf_C A"; cases "nf_C B";
      simp add: mahler_nf_action_def mahler_nf_then_def
        mahler_nf_gain_def mahler_nf_den_def associated_action_then_def
        associated_cap_min_def power_add field_simps of_int_min
        min_mult_distrib_left min_mult_distrib_right
        min_divide_distrib_right
        algebra_simps split: option.splits)

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


text \<open>The complete centered-11 consumer has a negative cap. Every legal
later bit has nonpositive offset and positive cap, so no later saturation can
replace the transported negative cap. This induction concerns the actual bit
actions, not an artificially chosen uncapped tail with matching coefficients.
It justifies the cap reduction once the admitted source's affine coefficients
and initial two centered bits have been established.\<close>

definition mahler_negative_cap_invariant :: "associated_action \<Rightarrow> bool" where
  "mahler_negative_cap_invariant A \<longleftrightarrow>
    action_cap A = Some (3/2 * action_scale A + action_offset A) \<and>
    3/2 * action_scale A + action_offset A < 0"

lemma mahler_negative_cap_preserved:
  assumes "mahler_negative_cap_invariant A" "e < 2"
  shows "mahler_negative_cap_invariant
    (associated_action_then A (mahler_bit_action e))"
proof -
  have bit: "e=0 \<or> e=1" using assms(2) by arith
  show ?thesis using assms(1) bit
    by (elim disjE; auto simp: mahler_negative_cap_invariant_def
        associated_action_then_def mahler_bit_action_def
        associated_cap_min_def min_def; linarith)
qed

lemma mahler_negative_cap_fold:
  assumes "mahler_negative_cap_invariant A"
    "list_all (\<lambda>e. e < 2) bits"
  shows "mahler_negative_cap_invariant
    (foldl associated_action_then A (map mahler_bit_action bits))"
  using assms
  by (induction bits arbitrary: A)
    (auto intro: mahler_negative_cap_preserved)

theorem mahler_centered_11_actual_tail_cap:
  assumes "list_all (\<lambda>e. e < 2) bits"
  defines "A \<equiv> foldl associated_action_then mahler_source_two_prefix
    (map mahler_bit_action bits)"
  shows "action_cap A = Some (3/2 * action_scale A + action_offset A)"
    "3/2 * action_scale A + action_offset A < 0"
proof -
  have prefix: "mahler_negative_cap_invariant mahler_source_two_prefix"
    by (simp add: mahler_negative_cap_invariant_def
        mahler_source_two_prefix_exact)
  have invariant: "mahler_negative_cap_invariant A"
    using mahler_negative_cap_fold[OF prefix assms(1)]
    by (simp only: A_def)
  then show "action_cap A = Some (3/2 * action_scale A + action_offset A)"
    "3/2 * action_scale A + action_offset A < 0"
    by (simp_all add: mahler_negative_cap_invariant_def)
qed

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms mahler_bit_action_admitted mahler_nf_action_admitted
      mahler_nf_then_identity mahler_nf_identity_action mahler_nf_action_then
      mahler_temporal_growth_extent_pair mahler_nf_extent_projection
      mahler_nf_growth_projection_then mahler_nf_live_scale_exact
      mahler_nf_growth_power_exact mahler_nf_growth_projection_radix_slope
      mahler_bit_action_negative_unsaturated
      mahler_negative_cap_preserved mahler_negative_cap_fold
      mahler_centered_11_actual_tail_cap
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
