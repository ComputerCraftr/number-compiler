theory Collatz_Terminal_Power_Two_Refinement
  imports Collatz_Boundary_Macros Collatz_Physical_One_Cycle
begin

text \<open>A certified terminal preimage has one exact source-guarded finite action.
This theorem pulls back from the equation \<open>3*x+1=2^e\<close>; it does not
assert that other sources eventually satisfy that equation. The normalized
action has one odd event followed by its exact dyadic descent. Its physical
duration includes the forced even tick after the odd event.\<close>

theorem collatz_terminal_power_two_preimage_action:
  fixes x e :: nat
  assumes nontrivial: "1 < x"
    and terminal: "3*x+1 = 2^e"
  shows "collatz_guarded_normalized_word_admitted
      (True # replicate (e-1) False) x \<and>
    collatz_guarded_normalized_word_endpoint
      (True # replicate (e-1) False) x = 1 \<and>
    length (True # replicate (e-1) False) = e \<and>
    count_list (True # replicate (e-1) False) True = 1 \<and>
    length (True # replicate (e-1) False) +
      count_list (True # replicate (e-1) False) True = e+1"
proof -
  have exponent_positive: "0 < e"
  proof (cases e)
    case 0
    then have equation: "3*x+1 = 1" using terminal by simp
    then show ?thesis using nontrivial by arith
  next
    case (Suc n)
    then show ?thesis by simp
  qed
  obtain n where exponent: "e = Suc n"
    using exponent_positive by (cases e) auto
  have numerator: "3*x+1 = 2 * 2^n"
    using terminal exponent by (simp add: power_Suc)
  have even_numerator: "even (3*x+1)"
    using numerator by simp
  have odd_source: "odd x"
    using even_numerator by presburger
  have first_step:
    "collatz_guarded_normalized_source_step True x = 2^n"
    using collatz_guarded_true_step_exact[OF odd_source] numerator by simp
  have tail:
    "collatz_guarded_normalized_word_admitted (replicate n False) (2^n) \<and>
      collatz_guarded_normalized_word_endpoint (replicate n False) (2^n) = 1"
    using collatz_guarded_false_run_exact[of n "2^n"] by simp
  have word:
    "True # replicate (e-1) False = True # replicate n False"
    using exponent by simp
  have admitted:
    "collatz_guarded_normalized_word_admitted
      (True # replicate (e-1) False) x"
    using word first_step odd_source tail
    by (simp add: collatz_guarded_normalized_word_admitted.simps)
  have endpoint:
    "collatz_guarded_normalized_word_endpoint
      (True # replicate (e-1) False) x = 1"
    using word first_step tail
    by (simp add: collatz_guarded_normalized_word_endpoint.simps)
  have event_count:
    "length (True # replicate (e-1) False) = e \<and>
      count_list (True # replicate (e-1) False) True = 1"
    using exponent by simp
  show ?thesis using admitted endpoint event_count by simp
qed

corollary collatz_terminal_power_two_physical_endpoint:
  fixes x e :: nat
  assumes nontrivial: "1 < x"
    and terminal: "3*x+1 = 2^e"
  shows "(physical_collatz ^^ (e+1)) x = 1"
proof -
  have action:
    "collatz_guarded_normalized_word_admitted
        (True # replicate (e-1) False) x \<and>
      collatz_guarded_normalized_word_endpoint
        (True # replicate (e-1) False) x = 1 \<and>
      length (True # replicate (e-1) False) +
        count_list (True # replicate (e-1) False) True = e+1"
    using collatz_terminal_power_two_preimage_action[OF nontrivial terminal]
    by blast
  have refinement:
    "collatz_guarded_normalized_word_endpoint
        (True # replicate (e-1) False) x =
          (physical_collatz ^^
            (length (True # replicate (e-1) False) +
              count_list (True # replicate (e-1) False) True)) x"
    using collatz_guarded_normalized_word_refines_physical[
        OF conjunct1[OF action]] by blast
  have endpoint_one:
    "collatz_guarded_normalized_word_endpoint
        (True # replicate (e-1) False) x = 1"
    using conjunct1[OF conjunct2[OF action]] .
  have duration:
    "length (True # replicate (e-1) False) +
      count_list (True # replicate (e-1) False) True = e+1"
    using conjunct2[OF conjunct2[OF action]] .
  have duration_action:
    "(physical_collatz ^^
      (length (True # replicate (e-1) False) +
        count_list (True # replicate (e-1) False) True)) x = 1"
  proof -
    have "(physical_collatz ^^
        (length (True # replicate (e-1) False) +
          count_list (True # replicate (e-1) False) True)) x =
        collatz_guarded_normalized_word_endpoint
          (True # replicate (e-1) False) x"
      by (rule sym[OF refinement])
    also have "... = 1" using endpoint_one .
    finally show ?thesis .
  qed
  have duration_transport:
    "(physical_collatz ^^
      (length (True # replicate (e-1) False) +
        count_list (True # replicate (e-1) False) True)) x =
      (physical_collatz ^^ (e+1)) x"
    by (rule arg_cong[where f="\<lambda>d. (physical_collatz ^^ d) x"])
      (rule duration)
  have "(physical_collatz ^^ (e+1)) x =
      (physical_collatz ^^
        (length (True # replicate (e-1) False) +
          count_list (True # replicate (e-1) False) True)) x"
    by (rule duration_transport[symmetric])
  also have "... = 1" by (rule duration_action)
  finally show ?thesis .
qed

theorem collatz_terminal_power_two_high_fiber_action:
  fixes x e q :: nat
  assumes nontrivial: "1 < x"
    and terminal: "3*x+1 = 2^e"
  shows "collatz_guarded_normalized_word_admitted
      (True # replicate (e-1) False) (x+2^e*q) \<and>
    collatz_guarded_normalized_word_endpoint
      (True # replicate (e-1) False) (x+2^e*q) = 1+3*q \<and>
    length (True # replicate (e-1) False) = e \<and>
    count_list (True # replicate (e-1) False) True = 1 \<and>
    length (True # replicate (e-1) False) +
      count_list (True # replicate (e-1) False) True = e+1"
proof -
  have exponent_positive: "0 < e"
  proof (cases e)
    case 0
    then have equation: "3*x+1 = 1" using terminal by simp
    then show ?thesis using nontrivial by arith
  next
    case (Suc n)
    then show ?thesis by simp
  qed
  obtain n where exponent: "e = Suc n"
    using exponent_positive by (cases e) auto
  have base_numerator: "3*x+1 = 2 * 2^n"
    using terminal exponent by (simp add: power_Suc)
  have even_numerator: "even (3*x+1)"
    using base_numerator by simp
  have odd_source: "odd x"
    using even_numerator by presburger
  have even_lift: "even (2^e*q)"
    using exponent by (simp add: power_Suc)
  have lifted_odd: "odd (x+2^e*q)"
    using odd_source even_lift by simp
  have lifted_numerator:
    "3*(x+2^e*q)+1 = 2*(2^n*(1+3*q))"
    using base_numerator exponent by (simp add: power_Suc algebra_simps)
  have first_step:
    "collatz_guarded_normalized_source_step True (x+2^e*q) =
      2^n*(1+3*q)"
    using collatz_guarded_true_step_exact[OF lifted_odd] lifted_numerator
    by simp
  have tail:
    "collatz_guarded_normalized_word_admitted
        (replicate n False) (2^n*(1+3*q)) \<and>
      collatz_guarded_normalized_word_endpoint
        (replicate n False) (2^n*(1+3*q)) = 1+3*q"
    using collatz_guarded_false_run_exact[of n "2^n*(1+3*q)"] by simp
  have word:
    "True # replicate (e-1) False = True # replicate n False"
    using exponent by simp
  have event_counts:
    "length (True # replicate (e-1) False) = e \<and>
      count_list (True # replicate (e-1) False) True = 1 \<and>
      length (True # replicate (e-1) False) +
        count_list (True # replicate (e-1) False) True = e+1"
    using exponent by simp
  show ?thesis
    using word first_step lifted_odd tail event_counts
    by (simp add: collatz_guarded_normalized_word_admitted.simps
        collatz_guarded_normalized_word_endpoint.simps)
qed

corollary collatz_terminal_power_two_cycle_suffix:
  fixes x e t :: nat
  assumes nontrivial: "1 < x"
    and terminal: "3*x+1 = 2^e"
  shows "(physical_collatz ^^ (e+1+t)) x =
    (physical_collatz ^^ t) 1"
proof -
  have physical_endpoint:
    "(physical_collatz ^^ (e+1)) x = 1"
    by (rule collatz_terminal_power_two_physical_endpoint[OF nontrivial terminal])
  have duration_order: "e+1+t = t+(e+1)"
    by arith
  have "(physical_collatz ^^ (e+1+t)) x =
      (physical_collatz ^^ (t+(e+1))) x"
    by (rule arg_cong[where f="\<lambda>d. (physical_collatz ^^ d) x"])
      (rule duration_order)
  also have "... = (physical_collatz ^^ t)
      ((physical_collatz ^^ (e+1)) x)"
    by (simp only: funpow_add o_apply)
  also have "... = (physical_collatz ^^ t) 1"
    by (rule arg_cong[where f="\<lambda>z. (physical_collatz ^^ t) z"])
      (rule physical_endpoint)
  finally show ?thesis .
qed

corollary collatz_terminal_power_two_cycle_phase:
  fixes x e t :: nat
  assumes nontrivial: "1 < x"
    and terminal: "3*x+1 = 2^e"
  shows "(physical_collatz ^^ (e+1+t)) x = collatz_one_cycle_phase t"
  using collatz_terminal_power_two_cycle_suffix[OF nontrivial terminal]
    physical_collatz_one_cycle_phase[of t]
  by simp

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms collatz_terminal_power_two_preimage_action
      collatz_terminal_power_two_high_fiber_action
      collatz_terminal_power_two_physical_endpoint
      collatz_terminal_power_two_cycle_suffix
      collatz_terminal_power_two_cycle_phase})
    then () else error "Collatz terminal preimage refinement depends on an oracle";
\<close>

end
