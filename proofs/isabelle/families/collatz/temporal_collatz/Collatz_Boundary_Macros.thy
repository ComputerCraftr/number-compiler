theory Collatz_Boundary_Macros
  imports Collatz_Physical_Cylinder_Lift
begin

text \<open>Exact guard lemmas for the four finite boundary templates used by the
Collatz production macro selector.  The divisibility assumptions state only
that the selected finite word is admissible; this theory does not assert that
the repetition count is maximal or prove any convergence property.\<close>

lemma collatz_guarded_false_step_exact:
  assumes even_source: "even x"
  shows "collatz_guarded_normalized_source_step False x = x div 2"
  using even_source
  by (simp add: collatz_guarded_normalized_source_step_def
      physical_collatz_def)

lemma collatz_guarded_true_step_exact:
  assumes odd_source: "odd x"
  shows "collatz_guarded_normalized_source_step True x = (3*x+1) div 2"
proof -
  have first_tick: "physical_collatz x = 3*x+1"
    using odd_source by (simp add: physical_collatz_def)
  have even_after: "even (3*x+1)"
    using odd_source by simp
  have second_tick:
      "physical_collatz (3*x+1) = (3*x+1) div 2"
    using even_after by (simp add: physical_collatz_def)
  have two: "2 = Suc (Suc 0)" by simp
  have iterate_two:
      "(physical_collatz ^^ 2) x =
        physical_collatz (physical_collatz x)"
    by (simp only: two funpow.simps comp_apply id_apply)
  show ?thesis
    unfolding collatz_guarded_normalized_source_step_def
    using iterate_two first_tick second_tick by simp
qed

lemma collatz_guarded_true_step_plus_one:
  assumes odd_source: "odd x"
  shows "collatz_guarded_normalized_source_step True x + 1 =
      3 * ((x+1) div 2)"
proof -
  obtain k where x: "x = 2*k+1"
    using odd_source by (rule oddE)
  show ?thesis
    using x odd_source
    by (simp add: collatz_guarded_true_step_exact algebra_simps)
qed

lemma collatz_guarded_normalized_word_admitted_append:
  "collatz_guarded_normalized_word_admitted (left @ right) x \<longleftrightarrow>
    collatz_guarded_normalized_word_admitted left x \<and>
    collatz_guarded_normalized_word_admitted right
      (collatz_guarded_normalized_word_endpoint left x)"
  by (induction left arbitrary: x) simp_all

lemma collatz_guarded_normalized_word_endpoint_append:
  "collatz_guarded_normalized_word_endpoint (left @ right) x =
    collatz_guarded_normalized_word_endpoint right
      (collatz_guarded_normalized_word_endpoint left x)"
  by (induction left arbitrary: x) simp_all

lemma collatz_guarded_false_run_exact:
  assumes divisible: "2^n dvd x"
  shows "collatz_guarded_normalized_word_admitted (replicate n False) x \<and>
    collatz_guarded_normalized_word_endpoint (replicate n False) x =
      x div 2^n"
  using divisible
proof (induction n arbitrary: x)
  case 0
  then show ?case by simp
next
  case (Suc n)
  obtain k where x: "x = 2^(Suc n)*k"
    using Suc.prems unfolding dvd_def by blast
  have even_x: "even x"
    using x by simp
  have first_step:
      "collatz_guarded_normalized_source_step False x = 2^n*k"
    using collatz_guarded_false_step_exact[OF even_x] x
    by (simp add: power_Suc algebra_simps)
  have tail_divisible: "2^n dvd 2^n*k"
    unfolding dvd_def by blast
  have tail:
      "collatz_guarded_normalized_word_admitted (replicate n False) (2^n*k) \<and>
       collatz_guarded_normalized_word_endpoint (replicate n False) (2^n*k) =
         (2^n*k) div 2^n"
    by (rule Suc.IH[OF tail_divisible])
  have first_guard: "False = odd x"
    using even_x by simp
  have endpoint:
      "collatz_guarded_normalized_word_endpoint (replicate (Suc n) False) x = k"
    using tail first_step
    by (simp add: first_guard collatz_guarded_normalized_word_endpoint.simps)
  have quotient: "x div 2^(Suc n) = k"
    using x by (simp add: power_Suc mult.assoc)
  show ?case
    using tail first_step first_guard endpoint quotient
    by (simp add: collatz_guarded_normalized_word_admitted.simps
        collatz_guarded_normalized_word_endpoint.simps)
qed

lemma collatz_guarded_true_run_admitted:
  assumes divisible: "2^n dvd x+1"
  shows "collatz_guarded_normalized_word_admitted (replicate n True) x"
  using divisible
proof (induction n arbitrary: x)
  case 0
  then show ?case by simp
next
  case (Suc n)
  obtain k where x_plus: "x+1 = 2^(Suc n)*k"
    using Suc.prems unfolding dvd_def by blast
  let ?half = "2^n*k"
  have x_plus_two: "x+1 = 2*?half"
    using x_plus by (simp add: power_Suc mult.assoc)
  have even_successor: "even (Suc x)"
    using x_plus_two by simp
  have odd_x: "odd x"
    using even_successor by (simp add: even_Suc)
  have half: "(x+1) div 2 = ?half"
    using x_plus_two by simp
  have next_plus: "collatz_guarded_normalized_source_step True x + 1 =
      2^n*(3*k)"
    using collatz_guarded_true_step_plus_one[OF odd_x] half
    by (simp add: mult.assoc)
  have tail_divisible:
      "2^n dvd collatz_guarded_normalized_source_step True x + 1"
    using next_plus unfolding dvd_def by blast
  have tail:
      "collatz_guarded_normalized_word_admitted (replicate n True)
        (collatz_guarded_normalized_source_step True x)"
    by (rule Suc.IH[OF tail_divisible])
  show ?case
    using odd_x tail
    by (simp add: collatz_guarded_normalized_word_admitted.simps)
qed

lemma collatz_guarded_one_zero_pair:
  assumes exponent: "2 \<le> n"
  shows
    "collatz_guarded_normalized_word_admitted [True,False]
       (1+2^n*k) \<and>
     collatz_guarded_normalized_word_endpoint [True,False]
       (1+2^n*k) = 1+3*2^(n-2)*k"
proof -
  obtain e where n: "n = 2+e"
    using exponent by (metis le_iff_add add.commute)
  let ?x = "1+2^n*k"
  have odd_x: "odd ?x"
    by (simp add: n power_add)
  have first_numerator:
      "3*(1+2^(2+e)*k)+1 = 2*(2*(1+3*2^e*k))"
    by (simp add: power_add algebra_simps)
  have first_value:
      "collatz_guarded_normalized_source_step True ?x =
        2*(1+3*2^e*k)"
    using collatz_guarded_true_step_exact[OF odd_x] first_numerator n
    by simp
  have even_first:
      "even (collatz_guarded_normalized_source_step True ?x)"
    using first_value by simp
  have second_value:
      "collatz_guarded_normalized_source_step False
        (collatz_guarded_normalized_source_step True ?x) =
        1+3*2^e*k"
    using collatz_guarded_false_step_exact[OF even_first] first_value
    by simp
  show ?thesis
    using odd_x even_first first_value second_value n
    by (simp add: collatz_guarded_normalized_word_admitted.simps
        collatz_guarded_normalized_word_endpoint.simps)
qed

fun collatz_421_tail :: "nat \<Rightarrow> bool list" where
  "collatz_421_tail 0 = [True]"
| "collatz_421_tail (Suc n) = [True,False] @ collatz_421_tail n"

definition collatz_421_word :: "nat \<Rightarrow> bool list" where
  "collatz_421_word r = [False,False] @ collatz_421_tail (r-1)"

lemma collatz_421_tail_admitted:
  "collatz_guarded_normalized_word_admitted (collatz_421_tail n)
    (1+2^(2*n+1)*k)"
proof (induction n arbitrary: k)
  case 0
  have divisible: "2^1 dvd (1+2^1*k)+1"
    unfolding dvd_def by (rule exI[where x="1+k"]) simp
  show ?case
    using collatz_guarded_true_run_admitted[OF divisible] by simp
next
  case (Suc n)
  have pair_result:
      "collatz_guarded_normalized_word_admitted [True,False]
        (1+2^(2*(Suc n)+1)*k) \<and>
       collatz_guarded_normalized_word_endpoint [True,False]
        (1+2^(2*(Suc n)+1)*k) =
          1+3*2^(2*(Suc n)+1-2)*k"
    by (rule collatz_guarded_one_zero_pair) arith
  have pair:
      "collatz_guarded_normalized_word_admitted [True,False]
        (1+2^(2*(Suc n)+1)*k)"
    using pair_result by simp
  have pair_exponent: "2*(Suc n)+1-2=2*n+1"
    by arith
  have pair_endpoint:
      "collatz_guarded_normalized_word_endpoint [True,False]
        (1+2^(2*(Suc n)+1)*k) = 1+2^(2*n+1)*(3*k)"
    using pair_result pair_exponent by (simp add: algebra_simps)
  have tail:
      "collatz_guarded_normalized_word_admitted (collatz_421_tail n)
        (1+2^(2*n+1)*(3*k))"
    by (rule Suc.IH)
  show ?case
    using pair pair_endpoint tail
    by (simp add: collatz_421_tail.simps
        collatz_guarded_normalized_word_admitted_append)
qed

lemma collatz_421_tail_length:
  "length (collatz_421_tail n) = 2*n+1"
  by (induction n) simp_all

lemma collatz_421_tail_true_count:
  "count_list (collatz_421_tail n) True = n+1"
  by (induction n) simp_all

theorem collatz_421_macro_guard:
  assumes positive: "0 < r"
    and source: "source mod 40 = 4"
    and source_large: "4 < source"
    and divisor: "2^(2*r+1) dvd source-4"
  shows "collatz_guarded_normalized_word_admitted
      (collatz_421_word r) source"
proof -
  obtain n where r: "r = Suc n"
    using positive by (cases r) auto
  obtain k where difference: "source-4 = 2^(2*r+1)*k"
    using divisor unfolding dvd_def by blast
  have source_form: "source = 4+2^(2*r+1)*k"
    using difference source_large by arith
  have exponent: "2*r+1 = 2+(2*n+1)"
    using r by arith
  have source_factor: "source = 4*(1+2^(2*n+1)*k)"
    using source_form r exponent
    by (simp add: power_add algebra_simps)
  have prefix_divisible: "2^2 dvd source"
    unfolding source_factor dvd_def
    by (rule exI[where x="1+2^(2*n+1)*k"]) simp
  have prefix_result:
      "collatz_guarded_normalized_word_admitted (replicate 2 False) source \<and>
       collatz_guarded_normalized_word_endpoint (replicate 2 False) source =
         source div 2^2"
    using collatz_guarded_false_run_exact[OF prefix_divisible] .
  have prefix_admitted:
      "collatz_guarded_normalized_word_admitted [False,False] source"
  proof -
    have two: "(2::nat) = Suc (Suc 0)" by simp
    have list: "replicate 2 False = [False,False]"
      unfolding two by (simp only: replicate.simps)
    show ?thesis
      using prefix_result list by (metis conjunct1)
  qed
  have prefix_endpoint:
      "collatz_guarded_normalized_word_endpoint [False,False] source =
        1+2^(2*n+1)*k"
  proof -
    have two: "(2::nat) = Suc (Suc 0)" by simp
    have list: "replicate 2 False = [False,False]"
      unfolding two by (simp only: replicate.simps)
    have run_endpoint:
        "collatz_guarded_normalized_word_endpoint (replicate 2 False) source =
          source div 2^2"
      using prefix_result by blast
    have quotient: "source div 2^2 = 1+2^(2*n+1)*k"
      using source_factor by (simp add: power_add algebra_simps)
    show ?thesis using run_endpoint quotient list by simp
  qed
  have tail: "collatz_guarded_normalized_word_admitted
      (collatz_421_tail n) (1+2^(2*n+1)*k)"
    by (rule collatz_421_tail_admitted)
  have admitted:
    "collatz_guarded_normalized_word_admitted
       ([False,False] @ collatz_421_tail n) source"
    using prefix_admitted tail prefix_endpoint
    by (simp add: collatz_guarded_normalized_word_admitted_append)
  show ?thesis
    using admitted r
    by (simp add: collatz_421_word_def)
qed

lemma collatz_421_macro_duration:
  assumes positive: "0 < r"
  shows "length (collatz_421_word r) +
    count_list (collatz_421_word r) True = 3*r+1"
proof -
  obtain n where r: "r = Suc n"
    using positive by (cases r) auto
  show ?thesis
    using r collatz_421_tail_length[of n]
      collatz_421_tail_true_count[of n]
    by (simp add: collatz_421_word_def)
qed

definition collatz_4721_word :: "nat \<Rightarrow> bool list" where
  "collatz_4721_word r = False # replicate (2*r) True"

theorem collatz_4721_macro_guard:
  assumes positive: "0 < r"
    and source: "source mod 40 = 14"
    and divisor: "2^(2*r+1) dvd source+2"
  shows "collatz_guarded_normalized_word_admitted
      (collatz_4721_word r) source"
proof -
  have source_split: "(source div 40)*40 + source mod 40 = source"
    by (rule div_mult_mod_eq)
  have source_decomp: "source = 40*(source div 40)+14"
    using source_split source by (simp add: algebra_simps)
  have source_twice:
      "source = 2*(20*(source div 40)+7)"
    using source_decomp by arith
  have even_source: "even source"
    by (subst source_twice) simp
  obtain m where source_form: "source=2*m"
    using even_source by (rule evenE)
  obtain k where quotient:
      "source+2=2^(2*r+1)*k"
    using divisor unfolding dvd_def by blast
  have half_plus_one: "source div 2+1=2^(2*r)*k"
  proof -
    have "2*(m+1)=2*(2^(2*r)*k)"
      using quotient source_form by (simp add: power_Suc algebra_simps)
    then have "m+1=2^(2*r)*k"
      by arith
    then show ?thesis using source_form by simp
  qed
  have tail_divisible: "2^(2*r) dvd (source div 2)+1"
    unfolding half_plus_one dvd_def by blast
  have tail:
      "collatz_guarded_normalized_word_admitted (replicate (2*r) True)
        (source div 2)"
    by (rule collatz_guarded_true_run_admitted[OF tail_divisible])
  have first: "False=odd source"
    using even_source by simp
  have admitted:
      "collatz_guarded_normalized_word_admitted
         (False # replicate (2*r) True) source"
    using first tail
    by (simp add: collatz_guarded_normalized_word_admitted.simps
        collatz_guarded_normalized_source_step_def physical_collatz_def)
  show ?thesis
    using admitted by (simp add: collatz_4721_word_def)
qed

lemma collatz_count_list_replicate_true:
  "count_list (replicate n True) True = n"
  by (induction n) simp_all

lemma collatz_count_list_replicate_false:
  "count_list (replicate n False) True = 0"
  by (induction n) simp_all

lemma collatz_4721_macro_duration:
  "length (collatz_4721_word r) +
    count_list (collatz_4721_word r) True = 4*r+1"
  by (simp add: collatz_4721_word_def collatz_count_list_replicate_true)

definition collatz_630_word :: "nat \<Rightarrow> bool list" where
  "collatz_630_word r = [False,True] @ replicate r False"

lemma collatz_630_prefix_exact:
  "collatz_guarded_normalized_word_admitted [False,True] (20*k+6) \<and>
   collatz_guarded_normalized_word_endpoint [False,True] (20*k+6) =
     5*(3*k+1)"
proof -
  have even_source: "even (20*k+6)" by simp
  have after_even:
      "collatz_guarded_normalized_source_step False (20*k+6)=10*k+3"
    using collatz_guarded_false_step_exact[OF even_source] by simp
  have odd_after: "odd (10*k+3)" by simp
  have odd_numerator:
      "3*(10*k+3)+1=2*(5*(3*k+1))"
    by (simp add: algebra_simps)
  have after_odd:
      "collatz_guarded_normalized_source_step True (10*k+3)=5*(3*k+1)"
    using collatz_guarded_true_step_exact[OF odd_after] odd_numerator
    by simp
  show ?thesis
    using even_source after_even odd_after after_odd
    by (simp add: collatz_guarded_normalized_word_admitted.simps
        collatz_guarded_normalized_word_endpoint.simps)
qed

theorem collatz_630_macro_guard:
  assumes positive: "0 < r"
    and source: "source=20*k+6"
    and divisor: "2^r dvd 3*k+1"
  shows "collatz_guarded_normalized_word_admitted
      (collatz_630_word r) source"
proof -
  obtain t where t: "3*k+1=2^r*t"
    using divisor unfolding dvd_def by blast
  have tail_divisible: "2^r dvd 5*(3*k+1)"
    unfolding t dvd_def
    by (rule exI[where x="5*t"])
       (simp add: mult.assoc mult.commute mult.left_commute)
  have tail:
      "collatz_guarded_normalized_word_admitted (replicate r False)
        (5*(3*k+1))"
    by (rule collatz_guarded_false_run_exact[OF tail_divisible, THEN conjunct1])
  have prefix:
      "collatz_guarded_normalized_word_admitted [False,True] (20*k+6) \<and>
       collatz_guarded_normalized_word_endpoint [False,True] (20*k+6) =
         5*(3*k+1)"
    by (rule collatz_630_prefix_exact)
  have admitted:
      "collatz_guarded_normalized_word_admitted
        ([False,True] @ replicate r False) (20*k+6)"
    using prefix tail
    by (simp add: collatz_guarded_normalized_word_admitted_append)
  show ?thesis using admitted source
    by (simp add: collatz_630_word_def collatz_count_list_replicate_false)
qed

lemma collatz_630_macro_duration:
  "length (collatz_630_word r) +
    count_list (collatz_630_word r) True = r+3"
  by (simp add: collatz_630_word_def)

definition collatz_989_word :: "nat \<Rightarrow> bool list" where
  "collatz_989_word r = replicate r True"

theorem collatz_989_macro_guard:
  assumes positive: "0 < r"
    and source: "source mod 10 = 9"
    and divisor: "2^r dvd source+1"
  shows "collatz_guarded_normalized_word_admitted
      (collatz_989_word r) source"
  using collatz_guarded_true_run_admitted[OF divisor]
  by (simp add: collatz_989_word_def collatz_count_list_replicate_true)

lemma collatz_989_macro_duration:
  "length (collatz_989_word r) +
    count_list (collatz_989_word r) True = 2*r"
  by (simp add: collatz_989_word_def collatz_count_list_replicate_true)

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms collatz_guarded_false_step_exact collatz_guarded_true_step_exact
      collatz_guarded_true_step_plus_one
      collatz_guarded_normalized_word_admitted_append
      collatz_guarded_normalized_word_endpoint_append
      collatz_guarded_false_run_exact collatz_guarded_true_run_admitted
      collatz_guarded_one_zero_pair collatz_421_tail_admitted
      collatz_421_tail_length collatz_421_tail_true_count
      collatz_421_macro_guard collatz_421_macro_duration
      collatz_4721_macro_guard collatz_4721_macro_duration
      collatz_630_prefix_exact collatz_630_macro_guard collatz_630_macro_duration
      collatz_989_macro_guard collatz_989_macro_duration})
    then () else error "Collatz boundary macro refinement depends on an oracle";
\<close>

end
