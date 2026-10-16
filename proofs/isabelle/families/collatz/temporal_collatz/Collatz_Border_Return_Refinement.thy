theory Collatz_Border_Return_Refinement
  imports Collatz_Boundary_Macros "Shared_S_Arithmetic.S_Arithmetic_Skew"
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

text \<open>The same selected return is an integer affine action with normalized
length j+2, gain 9, and offset 3+2^(j+1).  Its next named 3-border is
conditional: the returned endpoint is odd exactly on the u mod 4 = 3 port.\<close>

theorem collatz_border_return_affine_numerator:
  fixes q j u :: nat
  assumes factor: "3*q+1 = 2^j*u"
      and odd_u: "odd u"
  shows "9*(10*q+3) + (3+2^(j+1)) =
    2^(j+2) * ((15*u+1) div 2)"
proof -
  have numerator:
    "9*(10*q+3) + (3+2^(j+1)) = 2^(j+1)*(15*u+1)"
    using factor by (simp add: algebra_simps)
  have remainder: "(15*u+1) mod 2 = 0"
    using odd_u by simp
  have even_numerator: "even (15*u+1)"
    using odd_u by simp
  obtain half_numerator where numerator_factor:
    "15*u+1 = 2*half_numerator"
    using even_numerator by (elim evenE)
  have quotient: "(15*u+1) div 2 = half_numerator"
    using numerator_factor by simp
  have half: "2*((15*u+1) div 2) = 15*u+1"
    using numerator_factor quotient by simp
  have denominator:
    "2^(j+2) * ((15*u+1) div 2) = 2^(j+1)*(15*u+1)"
  proof -
    have exponent: "(2::nat)^(j+2) = (2::nat)^(j+1)*2"
      by (simp add: power_Suc mult.commute)
    have scaled_half:
      "2^(j+1) * (2*((15*u+1) div 2)) = 2^(j+1)*(15*u+1)"
      by (rule arg_cong[where f="\<lambda>z::nat. 2^(j+1)*z"]; rule half)
    show ?thesis
      using exponent scaled_half by (simp only: exponent mult.assoc scaled_half)
  qed
  show ?thesis using numerator denominator by simp
qed

lemma collatz_border_return_3_port_iff_odd_endpoint:
  fixes u :: nat
  assumes odd_u: "odd u"
  shows "u mod 4 = 3 \<longleftrightarrow> odd ((15*u+1) div 2)"
proof -
  have decomposition: "(u div 4)*4 + u mod 4 = u"
    by (simp add: div_mult_mod_eq mult.commute)
  have remainder_bound: "u mod (4::nat) < 4" by simp
  have remainder_mod: "(u mod 4) mod 2 = u mod 2"
    by (rule mod_mod_cancel) simp
  have remainder_odd: "odd (u mod 4)"
  proof -
    have mod_two: "u mod 2 = 1"
      using odd_u by (simp only: odd_iff_mod_2_eq_one)
    have reduced: "(u mod 4) mod 2 = 1"
      using remainder_mod mod_two by simp
    show ?thesis using reduced
      by (simp only: odd_iff_mod_2_eq_one)
  qed
  obtain r where remainder: "u mod 4 = 2*r+1"
    using remainder_odd by (rule oddE)
  have r_bound: "r \<le> 1" using remainder remainder_bound by arith
  have r_cases: "r=0 \<or> r=1" using r_bound by arith
  have ports:
    "u mod 4 = 1 \<or> u mod 4 = 3"
    using remainder r_cases by auto
  show ?thesis
  proof
    assume port: "u mod 4 = 3"
    have source: "u = 4*(u div 4)+3"
      using decomposition port by (simp add: algebra_simps)
    show "odd ((15*u+1) div 2)"
      using source by (simp; presburger)
  next
    assume endpoint: "odd ((15*u+1) div 2)"
    show "u mod 4 = 3"
    proof (rule ccontr)
      assume not_port: "u mod 4 \<noteq> 3"
      have port_one: "u mod 4 = 1" using ports not_port by blast
      have source: "u = 4*(u div 4)+1"
        using decomposition port_one by (simp add: algebra_simps)
      have even_endpoint: "\<not> odd ((15*u+1) div 2)"
        using source by (simp; presburger)
      show False using endpoint even_endpoint by contradiction
    qed
  qed
qed

corollary collatz_border_return_3_port_exact_gate:
  assumes factor: "3*q+1 = 2^j*u"
      and odd_u: "odd u"
  shows "u mod 4 = 3 \<longleftrightarrow>
    odd ((physical_collatz ^^ (j+4)) (10*q+3))"
proof -
  have endpoint:
    "(physical_collatz ^^ (j+4)) (10*q+3) = (15*u+1) div 2"
    using collatz_border_return_endpoint[OF factor odd_u] by blast
  show ?thesis
    using collatz_border_return_3_port_iff_odd_endpoint[OF odd_u] endpoint
    by simp
qed

lemma collatz_border_return_3_port:
  fixes k :: nat
  shows "(15*(4*k+3)+1) div 2 = 10*(3*k+2)+3 \<and>
    (3*(4*k+3)-1) div 4 = 3*k+2"
  by presburger

text \<open>The 3-port is also the exact upper-coordinate transition for the
next source-selected 6305 return.  This bridge uses the issued odd endpoint
digit to recover the quotient and the next multiplication-by-three numerator;
it does not select the next valuation in advance.\<close>

theorem collatz_border_return_3_upper_numerator:
  fixes u :: nat
  assumes port: "u mod 4 = 3"
  shows "(15*u+1) div 2 = 10*(3*(u div 4)+2)+3"
    and "3*(3*(u div 4)+2)+1 = (9*u+1) div 4"
proof -
  have divmod: "(u div 4)*4 + u mod 4 = u"
    by (rule div_mult_mod_eq)
  have source: "u = 4*(u div 4)+3"
    using divmod port by (simp add: mult.commute)
  have first_numerator:
    "15*u+1 = 2*(10*(3*(u div 4)+2)+3)"
    using source by (simp add: algebra_simps)
  show first: "(15*u+1) div 2 = 10*(3*(u div 4)+2)+3"
    by (simp only: first_numerator; simp)
  have second_numerator:
    "9*u+1 = 4*(3*(3*(u div 4)+2)+1)"
    using source by (simp add: algebra_simps)
  show second: "3*(3*(u div 4)+2)+1 = (9*u+1) div 4"
    by (simp only: second_numerator; simp)
qed

theorem collatz_border_return_3_successor_split:
  fixes u :: nat
  assumes port: "u mod 4 = 3"
  defines "q' \<equiv> 3*(u div 4)+2"
  shows "3*q'+1 = (9*u+1) div 4"
    and "9*u+1 = 2^(collatz_source_valuation q' + 2) *
        collatz_accelerated_target q'"
    and "odd (collatz_accelerated_target q')"
proof -
  have upper: "3*q'+1 = (9*u+1) div 4"
    using collatz_border_return_3_upper_numerator(2)[OF port]
    by (simp add: q'_def)
  show "3*q'+1 = (9*u+1) div 4" by (rule upper)
  have residue: "(9*u+1) mod 4 = 0"
    using port by presburger
  have divmod: "((9*u+1) div 4)*4 + (9*u+1) mod 4 = 9*u+1"
    by (rule div_mult_mod_eq)
  have divmod_zero: "((9*u+1) div 4)*4 + 0 = 9*u+1"
    using divmod by (simp only: residue)
  have numerator_division: "((9*u+1) div 4)*4 = 9*u+1"
    using divmod_zero by simp
  have numerator: "9*u+1 = ((9*u+1) div 4)*4"
    by (rule sym[OF numerator_division])
  have numerator': "9*u+1 = 4*(3*q'+1)"
    using numerator upper by (simp add: mult.commute)
  have split:
    "3*q'+1 = 2^(collatz_source_valuation q') *
      collatz_accelerated_target q'"
    by (rule collatz_source_split_exact)
  show "9*u+1 = 2^(collatz_source_valuation q' + 2) *
      collatz_accelerated_target q'"
    using numerator' split by (simp add: power_add algebra_simps)
  show "odd (collatz_accelerated_target q')"
    by (rule collatz_accelerated_target_odd)
qed

lemma collatz_border_return_endpoint_mod5:
  fixes u :: nat
  assumes odd_u: "odd u"
  shows "((15*u+1) div 2) mod 5 = 3"
proof -
  obtain k where u: "u = 2*k+1"
    using odd_u by (rule oddE)
  have quotient: "(15*u+1) div 2 = 15*k+8"
    using u by (simp add: algebra_simps)
  have factor: "15*k = 5*(3*k)"
    by (simp add: algebra_simps)
  have multiple: "(15*k) mod 5 = 0"
    by (simp only: factor mod_mult_self1_is_0)
  have residue: "(15*k+8) mod 5 =
      ((15*k) mod 5 + 8 mod 5) mod 5"
    by (rule mod_add_eq[symmetric])
  show ?thesis
    using quotient multiple residue by simp
qed

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

text \<open>This is the exact one-step radix-6 preimage at the odd source
boundary.  The factor 3 is not invertible modulo 6: the target residue 2
pulls back to the smaller source modulus 4, while residue 0 modulo 3 is
impossible.  This is a finite congruence fact, not authority for a later
named-family repetition count.\<close>

lemma collatz_odd_step_radix6_preimage:
  fixes x :: nat
  assumes odd_x: "odd x"
  shows "((3*x+1) div 2) mod 6 = 2 \<longleftrightarrow> x mod 4 = 1"
    and "((3*x+1) div 2) mod 3 \<noteq> 0"
proof -
  obtain k where x_eq: "x = 2*k+1" using odd_x by (auto elim: oddE)
  show "((3*x+1) div 2) mod 6 = 2 \<longleftrightarrow> x mod 4 = 1"
    using x_eq by presburger
  have odd_step: "(3*x+1) div 2 = 3*k+2"
    using x_eq by presburger
  have odd_step_mod3: "(3*k+2) mod 3 = 2"
    by (simp only: mod_mult_self4) simp
  show "((3*x+1) div 2) mod 3 \<noteq> 0"
    using odd_step odd_step_mod3 by simp
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

text \<open>The runtime's joined border action is a finite, admitted word of
normalized source steps. Its affine transfer composes associatively, while
source admission supplies each step equation. This theorem refines only the
given finite word and its exact physical clock; it does not establish a
selector, a cache protocol, bounded discovery work, or eventual termination.\<close>

definition collatz_skew_atom :: "bool \<Rightarrow> int skew_transfer" where
  "collatz_skew_atom branch =
    (if branch then \<lparr>upper=3, offset=1, lower=2\<rparr>
     else \<lparr>upper=1, offset=0, lower=2\<rparr>)"

fun collatz_skew_word :: "bool list \<Rightarrow> int skew_transfer" where
  "collatz_skew_word [] = shared_skew_identity"
| "collatz_skew_word (branch # tail) =
    shared_skew_then (collatz_skew_atom branch) (collatz_skew_word tail)"

lemma collatz_skew_word_append:
  "collatz_skew_word (first @ second) =
    shared_skew_then (collatz_skew_word first) (collatz_skew_word second)"
  by (induction first)
    (simp_all add: shared_skew_associative)

lemma collatz_skew_atom_refines_admitted_step:
  assumes admitted: "branch = odd source"
  shows "upper (collatz_skew_atom branch) * int source +
      offset (collatz_skew_atom branch) =
    lower (collatz_skew_atom branch) *
      int (collatz_guarded_normalized_source_step branch source)"
proof (cases branch)
  case True
  then have odd_source: "odd source" using admitted by simp
  have step:
    "collatz_guarded_normalized_source_step True source =
      (3*source+1) div 2"
    by (rule collatz_guarded_true_step_exact[OF odd_source])
  have even_image: "even (3*source+1)" using odd_source by simp
  have natural_equation:
    "3*source+1 = 2*((3*source+1) div 2)"
    using even_image by presburger
  have equation:
    "3 * int source + 1 =
      2 * int (collatz_guarded_normalized_source_step True source)"
    using natural_equation step by simp
  show ?thesis using equation True
    by (simp add: collatz_skew_atom_def)
next
  case False
  then have even_source: "even source" using admitted by simp
  have step:
    "collatz_guarded_normalized_source_step False source = source div 2"
    by (rule collatz_guarded_false_step_exact[OF even_source])
  have natural_equation: "source = 2*(source div 2)"
    using even_source by presburger
  have equation:
    "int source =
      2 * int (collatz_guarded_normalized_source_step False source)"
    using natural_equation step by simp
  show ?thesis using equation False
    by (simp add: collatz_skew_atom_def)
qed

theorem collatz_guarded_skew_word_finite_refinement:
  assumes admitted: "collatz_guarded_normalized_word_admitted bits source"
  shows "upper (collatz_skew_word bits) * int source +
      offset (collatz_skew_word bits) =
    lower (collatz_skew_word bits) *
      int (collatz_guarded_normalized_word_endpoint bits source)"
    and "collatz_guarded_normalized_word_endpoint bits source =
      (physical_collatz ^^ (length bits + count_list bits True)) source"
proof -
  show affine:
    "upper (collatz_skew_word bits) * int source +
      offset (collatz_skew_word bits) =
      lower (collatz_skew_word bits) *
        int (collatz_guarded_normalized_word_endpoint bits source)"
    using admitted
  proof (induction bits arbitrary: source)
    case Nil
    then show ?case by (simp add: shared_skew_identity_def)
  next
    case (Cons branch tail)
    have branch_guard: "branch = odd source"
      using Cons.prems[unfolded
        collatz_guarded_normalized_word_admitted.simps] by blast
    have tail_admitted:
      "collatz_guarded_normalized_word_admitted tail
        (collatz_guarded_normalized_source_step branch source)"
      using Cons.prems[unfolded
        collatz_guarded_normalized_word_admitted.simps] by blast
    have head:
      "upper (collatz_skew_atom branch) * int source +
        offset (collatz_skew_atom branch) =
        lower (collatz_skew_atom branch) *
          int (collatz_guarded_normalized_source_step branch source)"
      by (rule collatz_skew_atom_refines_admitted_step[OF branch_guard])
    have tail_exact:
      "upper (collatz_skew_word tail) *
          int (collatz_guarded_normalized_source_step branch source) +
        offset (collatz_skew_word tail) =
        lower (collatz_skew_word tail) *
          int (collatz_guarded_normalized_word_endpoint tail
            (collatz_guarded_normalized_source_step branch source))"
      by (rule Cons.IH[OF tail_admitted])
    have composed:
      "upper (shared_skew_then (collatz_skew_atom branch)
          (collatz_skew_word tail)) * int source +
        offset (shared_skew_then (collatz_skew_atom branch)
          (collatz_skew_word tail)) =
       lower (shared_skew_then (collatz_skew_atom branch)
          (collatz_skew_word tail)) *
        int (collatz_guarded_normalized_word_endpoint (branch # tail) source)"
      using shared_skew_transport[OF head tail_exact]
      by (simp add: collatz_guarded_normalized_word_endpoint.simps)
    show ?case using composed by simp
  qed
  show "collatz_guarded_normalized_word_endpoint bits source =
      (physical_collatz ^^ (length bits + count_list bits True)) source"
    using collatz_guarded_normalized_word_refines_physical[OF admitted]
    by blast
qed

ML \<open>
  val checked = @{thms physical_collatz_two_on_10q3
    physical_collatz_two_on_5_odd collatz_border_return_endpoint
    collatz_border_return_normalized_word collatz_border_return_physical_clock
    collatz_border_return_affine_numerator
    collatz_border_return_3_port_iff_odd_endpoint
    collatz_border_return_3_port_exact_gate
    collatz_border_return_3_port collatz_border_return_3_upper_numerator
    collatz_border_return_3_successor_split
    collatz_border_return_endpoint_mod5 collatz_border_return_8_exit_4
    collatz_border_return_8_exit_9 collatz_physical_8_to_4
    collatz_physical_8_to_9_to_8
    physical_collatz_reached_nine_has_eight_predecessor
    collatz_skew_word_append collatz_skew_atom_refines_admitted_step
    collatz_guarded_skew_word_finite_refinement};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Collatz border-return refinement depends on an oracle";
\<close>

end
