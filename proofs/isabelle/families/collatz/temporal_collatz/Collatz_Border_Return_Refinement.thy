theory Collatz_Border_Return_Refinement
  imports Collatz_Boundary_Macros
begin

text \<open>The local border return is a source-guarded arithmetic identity.
Its normalized word has two odd symbols, so the physical clock is two ticks
larger than the normalized word length.  These lemmas certify the selected
finite return only; they do not establish that every source reaches this
border or that repeated returns converge.\<close>

lemma physical_collatz_two_on_10q3:
  "(physical_collatz ^^ 2) (10*q+3) = 5*(3*q+1)"
proof -
  have two: "2 = Suc (Suc 0)" by simp
  have iter:
    "(physical_collatz ^^ 2) (10*q+3) =
      physical_collatz (physical_collatz (10*q+3))"
    by (simp only: two funpow.simps comp_apply id_apply)
  show ?thesis using iter by (simp add: physical_collatz_def algebra_simps)
qed

lemma physical_collatz_two_on_5_odd:
  assumes "odd u"
  shows "(physical_collatz ^^ 2) (5*u) = (15*u+1) div 2"
proof -
  have two: "2 = Suc (Suc 0)" by simp
  have iter:
    "(physical_collatz ^^ 2) (5*u) =
      physical_collatz (physical_collatz (5*u))"
    by (simp only: two funpow.simps comp_apply id_apply)
  have odd_source: "odd (5*u)" using assms by simp
  have even_image: "even (3*(5*u)+1)" using odd_source by simp
  show ?thesis using iter odd_source even_image
    by (simp add: physical_collatz_def algebra_simps)
qed

theorem collatz_border_return_endpoint:
  fixes q j u :: nat
  assumes factor: "3*q+1 = 2^j*u"
    and odd_u: "odd u"
  shows "(physical_collatz ^^ (j+2)) (10*q+3) = 5*u"
    and "(physical_collatz ^^ (j+4)) (10*q+3) = (15*u+1) div 2"
proof -
  have first_two:
    "(physical_collatz ^^ 2) (10*q+3) = 5*(2^j*u)"
    using physical_collatz_two_on_10q3 factor by simp
  have split_power:
    "(physical_collatz ^^ (j+2)) (10*q+3) =
      (physical_collatz ^^ j)
        ((physical_collatz ^^ 2) (10*q+3))"
    by (simp only: funpow_add comp_apply)
  have reduced:
    "(physical_collatz ^^ (j+2)) (10*q+3) =
      (physical_collatz ^^ j) (2^j*(5*u))"
    using split_power first_two by (simp add: algebra_simps)
  show first: "(physical_collatz ^^ (j+2)) (10*q+3) = 5*u"
    using physical_collatz_removes_dyadic_prefix[of j "5*u"] reduced
    by simp
  have split_last:
    "(physical_collatz ^^ (j+4)) (10*q+3) =
      (physical_collatz ^^ 2)
        ((physical_collatz ^^ (j+2)) (10*q+3))"
  proof -
    have exponent: "j+4 = 2+(j+2)" by simp
    show ?thesis by (simp only: exponent funpow_add comp_apply)
  qed
  show "(physical_collatz ^^ (j+4)) (10*q+3) = (15*u+1) div 2"
    using split_last first physical_collatz_two_on_5_odd[OF odd_u]
    by simp
qed

lemma collatz_border_return_normalized_word:
  assumes factor: "3*q+1 = 2^j*u"
    and odd_u: "odd u"
  defines "word \<equiv> True # replicate j False @ [True]"
  shows "collatz_guarded_normalized_word_admitted word (10*q+3)"
    and "collatz_guarded_normalized_word_endpoint word (10*q+3) =
      (15*u+1) div 2"
    and "length word + count_list word True = j+4"
proof -
  have odd_source: "odd (10*q+3)" by simp
  have first:
    "collatz_guarded_normalized_source_step True (10*q+3) =
      5*(2^j*u)"
    using collatz_guarded_true_step_exact[OF odd_source] factor
    by (simp add: algebra_simps)
  have first_admitted:
    "collatz_guarded_normalized_word_admitted [True] (10*q+3)"
    using odd_source first
    by (simp add: collatz_guarded_normalized_word_admitted.simps
        collatz_guarded_normalized_source_step_def)
  have divisible: "2^j dvd 2^j*(5*u)"
    by (rule dvdI[where k="5*u"]) simp
  have middle:
    "collatz_guarded_normalized_word_admitted (replicate j False)
        (2^j*(5*u)) \<and>
      collatz_guarded_normalized_word_endpoint (replicate j False)
        (2^j*(5*u)) = 5*u"
    using collatz_guarded_false_run_exact[OF divisible] by simp
  have terminal_odd: "odd (5*u)" using odd_u by simp
  have terminal:
    "collatz_guarded_normalized_word_admitted [True] (5*u)"
    using terminal_odd
    by (simp add: collatz_guarded_normalized_word_admitted.simps)
  have middle_endpoint:
    "collatz_guarded_normalized_word_endpoint (replicate j False)
        (5*(2^j*u)) = 5*u"
    using middle by (simp add: algebra_simps)
  have word_eq: "word = [True] @ replicate j False @ [True]"
    using word_def by simp
  show admitted: "collatz_guarded_normalized_word_admitted word (10*q+3)"
    using first_admitted middle terminal middle_endpoint first word_eq
    by (simp add: collatz_guarded_normalized_word_admitted_append mult_ac)
  have endpoint:
    "collatz_guarded_normalized_word_endpoint word (10*q+3) =
      (15*u+1) div 2"
  proof -
    have final:
      "collatz_guarded_normalized_word_endpoint [True] (5*u) =
        (15*u+1) div 2"
      using collatz_guarded_true_step_exact[OF terminal_odd]
      by (simp add: collatz_guarded_normalized_word_endpoint.simps
          collatz_guarded_normalized_source_step_def)
    show ?thesis
      using first middle_endpoint final word_eq
      by (simp add: collatz_guarded_normalized_word_endpoint_append
          algebra_simps)
  qed
  show "collatz_guarded_normalized_word_endpoint word (10*q+3) =
      (15*u+1) div 2"
    by (rule endpoint)
  show "length word + count_list word True = j+4"
    using word_eq by simp
qed

lemma collatz_border_return_3_port:
  fixes k :: nat
  shows "(15*(4*k+3)+1) div 2 = 10*(3*k+2)+3 \<and>
    (3*(4*k+3)-1) div 4 = 3*k+2"
  by presburger

lemma collatz_border_return_8_exit_4:
  fixes k :: nat
  shows
  "(15*(8*k+1)+1) div 2 = 20*(3*k)+8"
  by (simp add: algebra_simps)

lemma collatz_border_return_8_exit_9:
  fixes k :: nat
  shows
  "(15*(8*k+5)+1) div 2 = 20*(3*k+1)+18"
  by (simp add: algebra_simps)

lemma collatz_physical_8_to_4:
  "physical_collatz (20*k+8) = 10*k+4"
  by (simp add: physical_collatz_def)

lemma collatz_physical_8_to_9_to_8:
  "physical_collatz (20*k+18) = 10*k+9 \<and>
    physical_collatz (10*k+9) = 30*k+28"
  by (simp add: physical_collatz_def)

theorem collatz_border_return_physical_clock:
  assumes factor: "3*q+1 = 2^j*u"
    and odd_u: "odd u"
  defines "word \<equiv> True # replicate j False @ [True]"
  shows "(physical_collatz ^^ (length word + count_list word True))
      (10*q+3) = (15*u+1) div 2"
proof -
  have duration: "length word + count_list word True = j+4"
    using word_def by simp
  have clock:
    "(physical_collatz ^^ (length word + count_list word True)) (10*q+3) =
      (physical_collatz ^^ (j+4)) (10*q+3)"
    by (rule arg_cong[where f="\<lambda>n. (physical_collatz ^^ n) (10*q+3)"])
      (rule duration)
  show ?thesis
    using clock collatz_border_return_endpoint(2)[OF factor odd_u] by simp
qed

text \<open>Output alignment: if the selected last odd edge lands in residue
9 modulo 20, its immediate predecessor is the 8-port residue 18 modulo 20.
An initial source ending in 9 has no predecessor requirement.\<close>

lemma physical_collatz_reached_nine_has_eight_predecessor:
  assumes reached: "physical_collatz x mod 10 = 9"
  shows "even x \<and> x mod 20 = 18"
proof -
  have even_x: "even x"
  proof (rule ccontr)
    assume "\<not> even x"
    then have "odd x" by simp
    then obtain q where x: "x = 2*q+1" by (auto elim: oddE)
    have "physical_collatz x mod 10 \<noteq> 9"
      using x by (simp add: physical_collatz_def; presburger)
    then show False using reached by contradiction
  qed
  obtain q where x: "x = 2*q" using even_x by (auto elim: evenE)
  have q_mod: "q mod 10 = 9" using reached x
    by (simp add: physical_collatz_def)
  have q_form: "q = 10*(q div 10)+9"
    using div_mult_mod_eq[of q 10] q_mod by presburger
  have x_form: "x = 20*(q div 10)+18"
    using x q_form by (simp add: algebra_simps)
  show ?thesis using even_x x_form by simp
qed

ML \<open>
  val checked = @{thms physical_collatz_two_on_10q3
    physical_collatz_two_on_5_odd collatz_border_return_endpoint
    collatz_border_return_normalized_word collatz_border_return_physical_clock
    collatz_border_return_3_port collatz_border_return_8_exit_4
    collatz_border_return_8_exit_9 collatz_physical_8_to_4
    collatz_physical_8_to_9_to_8
    physical_collatz_reached_nine_has_eight_predecessor};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Collatz border-return refinement depends on an oracle";
\<close>

end
