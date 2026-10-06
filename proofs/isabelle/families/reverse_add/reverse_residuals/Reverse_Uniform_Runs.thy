theory Reverse_Uniform_Runs
  imports Reverse_Invariant
begin

text \<open>Counted pair coefficients, not decimal digits. These equations hold
for arbitrary natural run lengths; there is no finite-width enumeration.\<close>

text \<open>The domain-plane evaluator demands one incoming carry at a time.
Its memo key must include that carry. These spatial laws preserve all incoming
cases; they do not normalize a composition of successive reverse/add actions.\<close>

fun region_incoming_carries :: "bool \<Rightarrow> carry_domain list \<Rightarrow> bool list" where
  "region_incoming_carries c [] = []"
| "region_incoming_carries c (d#ds) = c # region_incoming_carries (carry_apply d c) ds"

lemma carry_domain_idempotent:
  "carry_apply d (carry_apply d c) = carry_apply d c"
  by (cases d) simp_all

lemma region_carry_run_output:
  "region_incoming_carries c (replicate (Suc n) d) =
    c # replicate n (carry_apply d c)"
  by (induction n arbitrary: c) (simp_all add: carry_domain_idempotent)

lemma region_carry_run_exit:
  "fold carry_apply (replicate (Suc n) d) c = carry_apply d c"
  by (induction n arbitrary: c) (simp_all add: carry_domain_idempotent)

lemma region_carry_spatial_join:
  "region_incoming_carries c (ds @ es) =
    region_incoming_carries c ds @
    region_incoming_carries (fold carry_apply ds c) es"
  by (induction ds arbitrary: c) simp_all

lemma region_carry_emission_refinement:
  "emit c ss = map (\<lambda>(s,b). (s + (if b then 1 else 0)) mod 10)
    (zip ss (region_incoming_carries c (map domain ss)))"
  by (induction ss arbitrary: c) simp_all

lemma emit_uniform_below:
  assumes "s < 9"
  shows "emit False (replicate n s) = replicate n s"
  using assms by (induction n) (simp_all add: domain_def)

lemma carry_uniform_below:
  assumes "s < 9"
  shows "carry_out False (replicate n s) = False"
  using assms by (induction n) (simp_all add: carry_out_def domain_def)

lemma pair_uniform:
  "map (\<lambda>(a,b). a+b) (zip (replicate n s) (replicate n s)) =
    replicate n (2*(s::nat))"
  by (induction n) simp_all

theorem uniform_below_successor:
  assumes "s < 9"
  shows "step (replicate n s) = replicate n (2*(s::nat))"
  using assms by (simp add: step_def digits_def emit_uniform_below
      carry_uniform_below pair_uniform)

lemma emit_sixteen_true:
  "emit True (replicate n 16) = replicate n 7"
  by (induction n) (simp_all add: domain_def)

lemma carry_sixteen_true:
  "carry_out True (replicate n 16) = True"
  by (induction n) (simp_all add: carry_out_def domain_def)

lemma sixteen_digits:
  "digits (replicate (Suc n) 16) = 6 # replicate n 7 @ [1]"
proof -
  have c: "carry_out False (replicate (Suc n) 16) = True"
  proof -
    have "carry_out False (replicate (Suc n) 16) =
        carry_out True (replicate n 16)"
      by (simp add: carry_out_def domain_def)
    then show ?thesis by (simp add: carry_sixteen_true)
  qed
  show ?thesis
    by (simp only: digits_def c if_True; simp add: domain_def emit_sixteen_true)
qed

lemma sum_uniform_tail:
  "map (\<lambda>(a,b). a+b)
    (zip (replicate n s @ [a]) (replicate n s @ [b])) =
    replicate n (2*(s::nat)) @ [a+b]"
  by (induction n) simp_all

theorem uniform_sixteen_growth:
  "step (replicate (Suc n) 16) = 7 # replicate n 14 @ [7]"
  by (simp only: step_def sixteen_digits; simp add: sum_uniform_tail)

theorem repunit_four_events:
  "run step 4 (replicate (Suc n) 2) = 7 # replicate n 14 @ [7]"
proof -
  have a: "step (replicate (Suc n) 2) = replicate (Suc n) 4"
    using uniform_below_successor[of 2 "Suc n"] by simp
  have b: "step (replicate (Suc n) 4) = replicate (Suc n) 8"
    using uniform_below_successor[of 4 "Suc n"] by simp
  have c: "step (replicate (Suc n) 8) = replicate (Suc n) 16"
    using uniform_below_successor[of 8 "Suc n"] by simp
  have four: "run step 4 s = step (step (step (step s)))" for s
    by (simp add: eval_nat_numeral)
  show ?thesis by (simp only: four a b c uniform_sixteen_growth)
qed

theorem repunit_domain_phases:
  "map domain (replicate n 2) = replicate n Below"
  "map domain (replicate n 4) = replicate n Below"
  "map domain (replicate n 8) = replicate n Below"
  "map domain (replicate n 16) = replicate n Above"
  by (simp_all add: domain_def)

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms uniform_below_successor uniform_sixteen_growth repunit_four_events
      repunit_domain_phases region_carry_run_output region_carry_run_exit
      region_carry_spatial_join region_carry_emission_refinement}) then ()
    else error "Uniform run proof depends on an oracle";
\<close>

end
