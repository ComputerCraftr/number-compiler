theory Mahler_Punctured_Valuation_Run_Refinement
  imports Mahler_Source_Cylinder_Transport
    "Antihydra.Antihydra_Arithmetic_Cylinder_Lift"
    "Antihydra.Antihydra_Exact_Run_Candidate_Refinement"
    "Collatz_Cylinder_Refinement.Collatz_Cylinder_Constructor"
begin

text \<open>The production exact-run fallback contracts homogeneous parity
runs of the centered source D=h-1.  These lemmas establish that each
valuation-selected contraction has the same exact endpoint and ordered
Antihydra parity word as the family orbit.  They do not claim that an
unrepresented odd-macro selector is complete, nor do they transfer an exact
source action to a different source.\<close>

lemma antihydra_source_zero_fixed_run:
  "mahler_orbit 0 n = 0 \<and>
    antihydra_family_orbit 0 n = 0 \<and>
    antihydra_family_bits 0 n = replicate n 0 \<and>
    antihydra_family_orbit 1 n = 1 \<and>
    antihydra_family_bits 1 n = replicate n 1"
  by (induct n) (simp_all add: antihydra_family_step_def mahler_D_step_def)

theorem antihydra_odd_valuation_run_endpoint:
  assumes source: "D+1 = 2^run_steps*u"
      and positive: "0 < u"
  shows "mahler_orbit D run_steps =
    3^run_steps*((D+1) div 2^run_steps)-1"
proof -
  have quotient: "(D+1) div 2^run_steps = u"
    using source by (simp add: mult.commute div_mult_self1)
  have run:
    "antihydra_family_orbit (D+1) run_steps = 3^run_steps*u"
    using antihydra_family_orbit_cylinder_transport[of 0 run_steps u] source
      antihydra_source_zero_fixed_run[of run_steps]
    by simp
  have centered:
    "antihydra_family_orbit (D+1) run_steps =
      mahler_orbit D run_steps + 1"
    by (rule antihydra_family_centered_orbit)
  have product_positive:
    "0 < 3^run_steps*((D+1) div 2^run_steps)"
    using quotient positive by simp
  have equation:
    "mahler_orbit D run_steps + 1 =
      3^run_steps*((D+1) div 2^run_steps)"
    using run centered quotient by simp
  show ?thesis using equation product_positive by arith
qed

theorem antihydra_even_zero_run_endpoint:
  assumes source: "D = 2^k*u"
      and within: "run_steps \<le> k"
  shows "mahler_orbit D run_steps =
    3^run_steps*(D div 2^run_steps)"
proof -
  have not_less: "\<not> k < run_steps" using within by simp
  have exponent_split: "k = run_steps + (k-run_steps)"
    using add_diff_inverse_nat[OF not_less] by simp
  have power_split:
    "(2::nat)^k = 2^run_steps * 2^(k-run_steps)"
  proof -
    have "(2::nat)^k = 2^(run_steps + (k-run_steps))"
      by (rule arg_cong[OF exponent_split])
    also have "... = 2^run_steps * 2^(k-run_steps)"
      by (simp only: power_add)
    finally show ?thesis .
  qed
  have source_factored:
    "D = 2^run_steps * (2^(k-run_steps)*u)"
  proof -
    have "D = 2^k*u" using source .
    also have "... = (2^run_steps * 2^(k-run_steps))*u"
      by (simp only: power_split)
    also have "... = 2^run_steps * (2^(k-run_steps)*u)"
      by (simp add: mult.assoc)
    finally show ?thesis .
  qed
  have power_nonzero: "(2::nat)^run_steps \<noteq> 0" by simp
  have quotient: "D div 2^run_steps = u*2^(k-run_steps)"
  proof -
    have quotient_factored:
      "(2^run_steps * (2^(k-run_steps)*u)) div
        (2^run_steps * 1) = (2^(k-run_steps)*u) div 1"
      by (rule div_mult_mult1[OF power_nonzero])
    show ?thesis using source_factored quotient_factored
      by (simp add: mult.commute)
  qed
  have run:
    "mahler_orbit (2^k*u) run_steps = u*2^(k-run_steps)*3^run_steps"
    by (rule even_source_run[OF within])
  show ?thesis using source quotient run by (simp add: algebra_simps)
qed

theorem antihydra_even_terminal_run_endpoint:
  assumes source: "D = 2^k*u"
      and odd_cofactor: "odd u"
  shows "mahler_orbit D (Suc k) =
      3^(Suc k)*(D div 2^(Suc k)) + (3^(Suc k)+1) div 2"
proof -
  have quotient:
    "D div 2^(Suc k) = u div 2"
  proof -
    have denominator: "(2::nat)^(Suc k) = 2^k * 2"
      by (simp add: power_Suc mult.commute)
    have nested:
      "(2^k*u) div 2^(Suc k) = ((2^k*u) div 2^k) div 2"
      by (simp only: denominator div_mult2_eq)
    have reduced: "(2^k*u) div 2^k = u"
      by (simp add: div_mult_self1 mult.commute)
    show ?thesis using source nested reduced by simp
  qed
  have selected:
    "2*mahler_orbit (2^k*u) (Suc k) = 3^(Suc k)*u+1"
    by (rule source_selected_event_endpoint[OF odd_cofactor])
  have odd_power: "odd ((3::nat)^(Suc k))" by simp
  have next_even: "((3::nat)^(Suc k)+1) mod 2 = 0"
    using odd_power by (simp add: odd_iff_mod_2_eq_one)
  have division:
    "(((3::nat)^(Suc k)+1) div 2) * 2 = (3::nat)^(Suc k)+1"
    using div_mult_mod_eq[of "(3::nat)^(Suc k)+1" 2] next_even by simp
  have half:
    "(2::nat)*(((3::nat)^(Suc k)+1) div 2) = (3::nat)^(Suc k)+1"
    using division by (simp add: mult.commute)
  have cofactor:
    "u = 2*(u div 2)+1"
    using odd_cofactor
    by (simp add: odd_iff_mod_2_eq_one; presburger)
  have twice_rhs:
    "(2::nat)*((3::nat)^(Suc k)*(u div 2)+
        ((3::nat)^(Suc k)+1) div 2) =
      (3::nat)^(Suc k)*u+1"
  proof -
    have first:
      "(2::nat)*((3::nat)^(Suc k)*(u div 2)) =
        (3::nat)^(Suc k)*((2::nat)*(u div 2))"
      by (simp add: algebra_simps)
    have second:
      "(2::nat)*(((3::nat)^(Suc k)+1) div 2) =
        (3::nat)^(Suc k)+1"
      using half by simp
    have combine:
      "(3::nat)^(Suc k)*((2::nat)*(u div 2)) +
          ((3::nat)^(Suc k)+1) =
        (3::nat)^(Suc k)*((2::nat)*(u div 2)+1)+1"
      by (simp add: algebra_simps)
    have finish:
      "(3::nat)^(Suc k)*((2::nat)*(u div 2)+1)+1 =
        (3::nat)^(Suc k)*u+1"
      using cofactor by simp
    have "(2::nat)*((3::nat)^(Suc k)*(u div 2)+
        ((3::nat)^(Suc k)+1) div 2) =
        (2::nat)*((3::nat)^(Suc k)*(u div 2)) +
          (2::nat)*(((3::nat)^(Suc k)+1) div 2)"
      by (simp only: distrib_left)
    also have "... =
        (3::nat)^(Suc k)*((2::nat)*(u div 2)) +
          ((3::nat)^(Suc k)+1)"
      using first second by simp
    also have "... =
        (3::nat)^(Suc k)*((2::nat)*(u div 2)+1)+1"
      by (rule combine)
    also have "... = (3::nat)^(Suc k)*u+1"
      by (rule finish)
    finally show ?thesis .
  qed
  have doubled:
    "(2::nat)*mahler_orbit (2^k*u) (Suc k) =
      (2::nat)*(3^(Suc k)*(u div 2)+(3^(Suc k)+1) div 2)"
    by (rule trans[OF selected twice_rhs[symmetric]])
  have two_nonzero: "(2::nat) \<noteq> 0" by simp
  have cancellation:
    "(2::nat)*mahler_orbit (2^k*u) (Suc k) =
        (2::nat)*(3^(Suc k)*(u div 2)+(3^(Suc k)+1) div 2) \<longleftrightarrow>
      mahler_orbit (2^k*u) (Suc k) =
        3^(Suc k)*(u div 2)+(3^(Suc k)+1) div 2"
    using two_nonzero by (rule mult_left_cancel)
  have equality:
    "mahler_orbit (2^k*u) (Suc k) =
      3^(Suc k)*(u div 2)+(3^(Suc k)+1) div 2"
    using doubled cancellation by blast
  show ?thesis using source quotient equality by simp
qed

theorem antihydra_odd_run_word_exact:
  assumes source: "D+1 = 2^run_steps*u"
  shows "antihydra_family_bits (D+1) run_steps = replicate run_steps 0"
proof -
  have transported:
    "antihydra_family_bits (0 + 2^run_steps*u) run_steps =
      antihydra_family_bits 0 run_steps"
    by (rule antihydra_family_bits_cylinder_transport)
  show ?thesis
    using source transported antihydra_source_zero_fixed_run[of run_steps]
    by simp
qed

theorem antihydra_even_zero_run_word_exact:
  assumes source: "D = 2^k*u"
      and within: "run_steps \<le> k"
  shows "antihydra_family_bits (D+1) run_steps = replicate run_steps 1"
proof -
  have exponent_split:
    "k = run_steps + (k-run_steps)"
    using within by arith
  have power_split:
    "(2::nat)^k = 2^run_steps * 2^(k-run_steps)"
  proof -
    have "(2::nat)^(run_steps + (k-run_steps)) =
        2^run_steps * 2^(k-run_steps)"
      by (simp only: power_add)
    then show ?thesis using exponent_split by simp
  qed
  have source_split:
    "D+1 = 1 + 2^run_steps*(2^(k-run_steps)*u)"
    using source power_split by (simp add: algebra_simps)
  have transported:
    "antihydra_family_bits
        (1 + 2^run_steps*(2^(k-run_steps)*u)) run_steps =
      antihydra_family_bits 1 run_steps"
    by (rule antihydra_family_bits_cylinder_transport)
  show ?thesis
    using source_split transported antihydra_source_zero_fixed_run[of run_steps]
    by simp
qed

theorem antihydra_even_terminal_run_word_exact:
  assumes source: "D = 2^k*u"
      and odd_cofactor: "odd u"
  shows "antihydra_family_bits (D+1) (Suc k) = replicate k 1 @ [0]"
proof -
  have prefix:
    "antihydra_family_bits (D+1) k = replicate k 1"
    by (rule antihydra_even_zero_run_word_exact[OF source le_refl])
  have odd_endpoint:
    "odd (mahler_orbit D k)"
  proof -
    have run: "mahler_orbit D k = u*3^k"
      using source even_source_run[of k k u] by (simp add: mult.commute)
    have odd_power: "odd ((3::nat)^k)" by simp
    have odd_product: "odd (u*3^k)"
      using odd_cofactor odd_power by simp
    show ?thesis using run odd_product by simp
  qed
  have centered:
    "antihydra_family_orbit (D+1) k = mahler_orbit D k + 1"
    by (rule antihydra_family_centered_orbit)
  have last:
    "antihydra_family_orbit (D+1) k mod 2 = 0"
    using odd_endpoint centered by simp
  show ?thesis
    using prefix last antihydra_family_bits_Suc_right[of "D+1" k]
    by simp
qed

text \<open>The run boundary can be selected from the exact source by the
same recursive two-adic splitter used by the Collatz cylinder constructor.
These are the concrete source-selected cases consumed by the punctured
Mahler leaf: an odd centered source selects the zero run of D+1, while a
positive even centered source selects its one run and the following event.
The zero source is handled separately because its two-adic valuation is not
defined by strip_twos.\<close>

theorem antihydra_source_selected_odd_zero_run:
  assumes odd_source: "odd D"
  shows "mahler_orbit D (fst (strip_twos (D+1))) =
      3^(fst (strip_twos (D+1))) *
        ((D+1) div 2^(fst (strip_twos (D+1)))) - 1"
    and "antihydra_family_bits (D+1) (fst (strip_twos (D+1))) =
      replicate (fst (strip_twos (D+1))) 0"
    and "int (3^(fst (strip_twos (D+1)))) =
      sk_A (antihydra_arithmetic_block (D+1)
        (fst (strip_twos (D+1))))"
    and "antihydra_exact_run_offset (D+1) (fst (strip_twos (D+1))) =
      sk_J (antihydra_arithmetic_block (D+1)
        (fst (strip_twos (D+1))))"
    and "int (2^(fst (strip_twos (D+1)))) =
      sk_D (antihydra_arithmetic_block (D+1)
        (fst (strip_twos (D+1))))"
    and "antihydra_exact_run_odd_symbols (D+1)
        (fst (strip_twos (D+1))) =
      count_list (antihydra_family_bits (D+1)
        (fst (strip_twos (D+1)))) 1"
    and "sk_delta (antihydra_arithmetic_block (D+1)
        (fst (strip_twos (D+1)))) =
      antihydra_family_balance (D+1) 0 (fst (strip_twos (D+1)))"
    and "sk_minprefix (antihydra_arithmetic_block (D+1)
        (fst (strip_twos (D+1)))) =
      antihydra_family_minimum (D+1) 0 (fst (strip_twos (D+1)))"
proof -
  obtain k u where split: "strip_twos (D+1) = (k,u)"
    by (cases "strip_twos (D+1)") auto
  have split_suc: "strip_twos (Suc D) = (k,u)"
    using split by simp
  have positive_source: "0 < D+1" by simp
  have decomposition:
    "Suc D = 2^(fst (strip_twos (Suc D))) * snd (strip_twos (Suc D)) \<and>
      odd (snd (strip_twos (Suc D)))"
    using strip_twos_spec[OF positive_source] by simp
  have source: "D+1 = 2^k*u"
    and odd_u: "odd u"
    using decomposition split_suc by auto
  have positive_u: "0 < u"
    using source by (cases u) auto
  have endpoint:
    "mahler_orbit D k = 3^k*((D+1) div 2^k)-1"
    by (rule antihydra_odd_valuation_run_endpoint[OF source positive_u])
  have word:
    "antihydra_family_bits (D+1) k = replicate k 0"
    by (rule antihydra_odd_run_word_exact[OF source])
  have observed:
    "mahler_orbit D k + 1 = antihydra_family_orbit (D+1) k"
    using antihydra_family_centered_orbit[of D k] by simp
  have fields:
    "int (3^k) = sk_A (antihydra_arithmetic_block (D+1) k)"
    "antihydra_exact_run_offset (D+1) k =
      sk_J (antihydra_arithmetic_block (D+1) k)"
    "int (2^k) = sk_D (antihydra_arithmetic_block (D+1) k)"
    "antihydra_exact_run_odd_symbols (D+1) k =
      count_list (antihydra_family_bits (D+1) k) 1"
    "sk_delta (antihydra_arithmetic_block (D+1) k) =
      antihydra_family_balance (D+1) 0 k"
    "sk_minprefix (antihydra_arithmetic_block (D+1) k) =
      antihydra_family_minimum (D+1) 0 k"
    using antihydra_exact_run_candidate_fields[OF observed] .
  show "mahler_orbit D (fst (strip_twos (D+1))) =
      3^(fst (strip_twos (D+1))) *
        ((D+1) div 2^(fst (strip_twos (D+1)))) - 1"
    using endpoint split by simp
  show "antihydra_family_bits (D+1) (fst (strip_twos (D+1))) =
      replicate (fst (strip_twos (D+1))) 0"
    using word split by simp
  show "int (3^(fst (strip_twos (D+1)))) =
      sk_A (antihydra_arithmetic_block (D+1)
        (fst (strip_twos (D+1))))"
    using fields split by simp
  show "antihydra_exact_run_offset (D+1) (fst (strip_twos (D+1))) =
      sk_J (antihydra_arithmetic_block (D+1)
        (fst (strip_twos (D+1))))"
    using fields split by simp
  show "int (2^(fst (strip_twos (D+1)))) =
      sk_D (antihydra_arithmetic_block (D+1)
        (fst (strip_twos (D+1))))"
    using fields split by simp
  show "antihydra_exact_run_odd_symbols (D+1)
        (fst (strip_twos (D+1))) =
      count_list (antihydra_family_bits (D+1)
        (fst (strip_twos (D+1)))) 1"
    using fields split by simp
  show "sk_delta (antihydra_arithmetic_block (D+1)
        (fst (strip_twos (D+1)))) =
      antihydra_family_balance (D+1) 0 (fst (strip_twos (D+1)))"
    using fields split by simp
  show "sk_minprefix (antihydra_arithmetic_block (D+1)
        (fst (strip_twos (D+1)))) =
      antihydra_family_minimum (D+1) 0 (fst (strip_twos (D+1)))"
    using fields split by simp
qed

theorem antihydra_source_selected_even_terminal_run:
  assumes positive_source: "0 < D"
      and even_source: "even D"
  shows "mahler_orbit D (Suc (fst (strip_twos D))) =
      3^(Suc (fst (strip_twos D))) *
        (D div 2^(Suc (fst (strip_twos D)))) +
          (3^(Suc (fst (strip_twos D)))+1) div 2"
    and "antihydra_family_bits (D+1) (Suc (fst (strip_twos D))) =
      replicate (fst (strip_twos D)) 1 @ [0]"
    and "0 < fst (strip_twos D)"
proof -
  obtain k u where split: "strip_twos D = (k,u)"
    by (cases "strip_twos D") auto
  have source: "D = 2^k*u" and odd_u: "odd u"
    using strip_twos_spec[OF positive_source] by (simp_all add: split)
  have k_positive: "0 < k"
  proof (cases k)
    case 0
    then have "D = u" using source by simp
    then show ?thesis using odd_u even_source by simp
  next
    case (Suc j)
    then show ?thesis by simp
  qed
  have endpoint: "mahler_orbit D (Suc k) =
      3^(Suc k)*(D div 2^(Suc k)) + (3^(Suc k)+1) div 2"
    by (rule antihydra_even_terminal_run_endpoint[OF source odd_u])
  have word:
    "antihydra_family_bits (D+1) (Suc k) = replicate k 1 @ [0]"
    by (rule antihydra_even_terminal_run_word_exact[OF source odd_u])
  show "mahler_orbit D (Suc (fst (strip_twos D))) =
      3^(Suc (fst (strip_twos D))) *
        (D div 2^(Suc (fst (strip_twos D)))) +
          (3^(Suc (fst (strip_twos D)))+1) div 2"
    using endpoint split by simp
  show "antihydra_family_bits (D+1) (Suc (fst (strip_twos D))) =
      replicate (fst (strip_twos D)) 1 @ [0]"
    using word split by simp
  show "0 < fst (strip_twos D)"
    using k_positive split by simp
qed

text \<open>The exact source selector still has to prove the cofactor
factorizations from any runtime-specific trailing-zero count implementation
and prove where the odd-macro selector begins and ends. The two selector
theorems above establish the maximal strip_twos-selected homogeneous prefix
and the terminal event directly from the exact source. They do not claim
that the odd-macro selector is complete or that a source action transports
to another source.\<close>

ML \<open>
  val checked = @{thms antihydra_family_orbit_cylinder_transport
    antihydra_family_bits_cylinder_transport
    antihydra_odd_valuation_run_endpoint
    antihydra_even_zero_run_endpoint
    antihydra_even_terminal_run_endpoint
    antihydra_odd_run_word_exact
    antihydra_even_zero_run_word_exact
    antihydra_even_terminal_run_word_exact
    antihydra_source_selected_odd_zero_run
    antihydra_source_selected_even_terminal_run
    antihydra_source_zero_fixed_run};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Antihydra valuation-run refinement depends on an oracle";
  val _ = if Thm_Deps.has_skip_proof checked
    then error "Skipped Antihydra valuation-run proof" else ();
\<close>

end
