theory Fermat_Binomial_Unit_Producer
  imports Fermat_Dyadic_Unit_Pivot "HOL-Number_Theory.Modular_Inverse"
    "HOL-Library.Log_Nat"
begin

text \<open>
A small executable model of the Python 2-adic binomial source.  The state
advances the binomial coefficient and signed accumulator together, using one
odd inverse per term.  The stop-guard theorem and concrete evaluations below
cover only levels 1 through 6 at the complete-window precisions used by the
F1--F3 counter certificates.  They establish no unrestricted source or
primality theorem.
\<close>

function fermat_two_valuation :: "nat \<Rightarrow> nat" where
  "fermat_two_valuation 0 = 0"
| "fermat_two_valuation (Suc n) =
     (if even (Suc n) then
        Suc (fermat_two_valuation ((Suc n) div 2)) else 0)"
  by pat_completeness auto
termination
  by (relation "measure id") (auto simp: div_less_dividend odd_pos)

definition fermat_odd_part :: "nat \<Rightarrow> nat" where
  "fermat_odd_part j = j div 2 ^ fermat_two_valuation j"

definition fermat_binomial_modulus :: "nat \<Rightarrow> nat" where
  "fermat_binomial_modulus p = 2 ^ p"

definition fermat_binomial_inverse :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "fermat_binomial_inverse p j =
    nat (modular_inverse (int (fermat_binomial_modulus p))
      (int (fermat_odd_part j)))"

definition fermat_binomial_choose_step ::
    "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "fermat_binomial_choose_step t p j current_coeff =
    (current_coeff * (2 ^ (t - fermat_two_valuation j) *
       fermat_binomial_inverse p j + fermat_binomial_modulus p - 1)) mod
       fermat_binomial_modulus p"

definition fermat_binomial_term_step ::
    "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "fermat_binomial_term_step p j current_coeff =
    (2 ^ (2 * (j - 1) - fermat_two_valuation j) * current_coeff *
       fermat_binomial_inverse p j) mod fermat_binomial_modulus p"

definition fermat_binomial_accumulator_step ::
    "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "fermat_binomial_accumulator_step p j accumulator term =
    (if odd j then
       (accumulator + fermat_binomial_modulus p - term) mod
         fermat_binomial_modulus p
     else (accumulator + term) mod fermat_binomial_modulus p)"

fun fermat_binomial_source_state ::
    "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<times> nat" where
  "fermat_binomial_source_state t p 0 = (1, 0)"
| "fermat_binomial_source_state t p (Suc k) =
    (case fermat_binomial_source_state t p k of
       (current_coeff, accumulator) \<Rightarrow>
         (fermat_binomial_choose_step t p (Suc k) current_coeff,
          fermat_binomial_accumulator_step p (Suc k) accumulator
            (fermat_binomial_term_step p (Suc k) current_coeff)))"

definition fermat_binomial_accumulator_stream ::
    "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "fermat_binomial_accumulator_stream t p q =
    snd (fermat_binomial_source_state t p q)"

definition fermat_binomial_python_stops ::
    "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "fermat_binomial_python_stops t p j =
    (p \<le> 2 * (j - 1) - (floorlog 2 j - 1) \<or>
      (t < floorlog 2 j \<and> 2 ^ t < j))"

lemma fermat_binomial_python_continues_through_support:
  assumes level: "0 < t"
    and precision: "2 * (2 ^ t - 1) < p"
    and positive: "0 < j"
    and bound: "j \<le> 2 ^ t"
  shows "\<not> fermat_binomial_python_stops t p j"
proof -
  have first_guard:
    "2 * (j - 1) - (floorlog 2 j - 1) < p"
    using precision bound by arith
  show ?thesis
    using first_guard bound
    by (simp add: fermat_binomial_python_stops_def)
qed

lemma fermat_binomial_python_stops_after_support:
  assumes level: "0 < t"
  shows "fermat_binomial_python_stops t p (2 ^ t + 1)"
proof -
  have lower: "(2::nat) ^ t \<le> 2 ^ t + 1" by simp
  have base: "(2::nat) > 1" by simp
  have bit_length: "Suc t \<le> floorlog 2 (2 ^ t + 1)"
    using floorlog_ge_SucI[OF lower base] .
  show ?thesis
    using bit_length by (simp add: fermat_binomial_python_stops_def)
qed

lemma fermat_unit_complete_width_exceeds_source_scale:
  assumes range: "1 \<le> t" "t \<le> 6"
  shows "2 * (2 ^ t - 1) < fermat_unit_complete_width t"
proof -
  have cases:
    "t = 1 \<or> t = 2 \<or> t = 3 \<or> t = 4 \<or> t = 5 \<or> t = 6"
    using range by arith
  show ?thesis
    using cases
    by (elim disjE; simp add: fermat_unit_complete_width_def)
qed

lemma fermat_bounded_source_precision_values:
  "(fermat_unit_complete_width 1, fermat_unit_complete_width 2,
    fermat_unit_complete_width 3, fermat_unit_complete_width 4,
    fermat_unit_complete_width 5, fermat_unit_complete_width 6) =
    (3, 8, 20, 45, 95, 196)"
  by code_simp

lemma fermat_bounded_python_parameter_bounds:
  "(\<forall>t\<in>{1..6}. t < fermat_unit_complete_width t \<and>
      (\<forall>j\<in>{1..2^t}.
        fermat_two_valuation j \<le> t \<and>
        fermat_two_valuation j \<le> 2 * (j - 1)))"
proof -
  have parameter_list:
    "list_all (\<lambda>t. t < fermat_unit_complete_width t \<and>
        list_all (\<lambda>j. fermat_two_valuation j \<le> t \<and>
          fermat_two_valuation j \<le> 2 * (j - 1)) [1..<Suc (2^t)])
      [1..<Suc 6]"
    by code_simp
  have level_set: "set [1..<Suc 6] = {1..6}"
    by (auto simp: set_upt less_Suc_eq_le)
  have support_set: "set [1..<Suc (2^t)] = {1..2^t}" for t :: nat
    by (auto simp: set_upt less_Suc_eq_le)
  show ?thesis using parameter_list
    unfolding list_all_iff
    by (simp only: level_set support_set)
qed

lemma fermat_binomial_source_state_successor:
  assumes "fermat_binomial_source_state t p k = (coefficient, accumulator)"
  shows "fermat_binomial_source_state t p (Suc k) =
    (fermat_binomial_choose_step t p (Suc k) coefficient,
      fermat_binomial_accumulator_step p (Suc k) accumulator
        (fermat_binomial_term_step p (Suc k) coefficient))"
  using assms by simp

lemma fermat_two_valuation_positive:
  "0 < j \<Longrightarrow> fermat_two_valuation j =
    (if even j then Suc (fermat_two_valuation (j div 2)) else 0)"
  by (cases j) simp_all

lemma fermat_unit_numeral_step:
  "1 < t \<Longrightarrow> fermat_dyadic_unit t =
    fermat_dyadic_unit (t-1) + 2^t * fermat_dyadic_unit (t-1)^2"
  by (cases t) (auto simp: fermat_dyadic_unit_successor_exact)

lemma fermat_binomial_inverse_certificate:
  fixes candidate :: int
  assumes range: "candidate \<in> {0..<int (2^p)}"
    and inverse: "[int (fermat_odd_part j) * candidate = 1] (mod int (2^p))"
  shows "fermat_binomial_inverse p j = nat candidate"
  using modular_inverse_int_eqI[OF range inverse]
  by (simp add: fermat_binomial_inverse_def fermat_binomial_modulus_def)

text \<open>Certify each predecessor once. Numeric conversion never receives
an unevaluated recursive source state. The conversion produces kernel equality
proofs; it neither imports precomputed values nor uses an evaluation oracle.\<close>

method_setup fermat_source_steps = \<open>
  Scan.succeed (fn ctxt => SIMPLE_METHOD' (SUBGOAL (fn (goal, i) =>
    let
      val (lhs, _) = HOLogic.dest_eq (HOLogic.dest_Trueprop goal);
      val (_, arguments) = strip_comb lhs;
      val (t, p, count) = (case arguments of [t, p, n] =>
          (t, p, snd (HOLogic.dest_number n))
        | _ => error "Expected a concrete Fermat accumulator stream");
      val arithmetic = ctxt |> Simplifier.add_simps
        @{thms fermat_binomial_choose_step_def fermat_binomial_term_step_def
          fermat_binomial_accumulator_step_def
          fermat_binomial_modulus_def fermat_odd_part_def
          fermat_two_valuation_positive fermat_unit_numeral_step
          Cong.cong_def Let_def};
      fun odd_part n = if n mod 2 = 0 then odd_part (n div 2) else n;
      fun bezout a b = if b = 0 then (1, 0) else
        let val (x, y) = bezout b (a mod b)
        in (y, x - (a div b) * y) end;
      val modulus = Integer.pow (snd (HOLogic.dest_number p)) 2;
      fun inverse_fact position =
        let
          val candidate = #1 (bezout (odd_part position) modulus) mod modulus;
          val j = HOLogic.mk_number @{typ nat} position;
          val value = HOLogic.mk_number @{typ int} candidate;
          val certificate = Drule.infer_instantiate ctxt
            [(("p", 0), Thm.cterm_of ctxt p), (("j", 0), Thm.cterm_of ctxt j),
             (("candidate", 0), Thm.cterm_of ctxt value)]
            @{thm fermat_binomial_inverse_certificate};
          val statement = Thm.concl_of certificate;
        in Goal.prove ctxt [] [] statement (fn _ =>
          resolve_tac ctxt [certificate] 1 THEN ALLGOALS (simp_tac arithmetic)) end;
      val initial = Drule.infer_instantiate ctxt
        [(("t", 0), Thm.cterm_of ctxt t), (("p", 0), Thm.cterm_of ctxt p)]
        @{thm fermat_binomial_source_state.simps(1)};
      fun numeral (Const (@{const_name Suc}, _) $ n) = numeral n
        | numeral n = can HOLogic.dest_number n;
      fun advance position previous =
        let
          val step = @{thm fermat_binomial_source_state_successor} OF [previous];
          val equation = @{thm eq_reflection} OF [step];
          val (state_function, successor_index) = Thm.dest_comb (Thm.lhs_of equation);
          val canonical_index = HOLogic.mk_number @{typ nat} position;
          val index_statement = HOLogic.mk_Trueprop
            (HOLogic.mk_eq (Thm.term_of successor_index, canonical_index));
          val index_proof = Goal.prove ctxt [] [] index_statement
            (fn {context, ...} => simp_tac context 1);
          val index = Thm.combination (Thm.reflexive state_function)
            (@{thm eq_reflection} OF [index_proof]);
          val inverse = inverse_fact position;
          val inverse_function = Thm.cterm_of ctxt
            (@{term fermat_binomial_inverse} $ p);
          val inverse_index = Thm.combination (Thm.reflexive inverse_function)
            (@{thm eq_reflection} OF [index_proof]);
          val successor_inverse = @{thm meta_eq_to_obj_eq} OF
            [Thm.transitive inverse_index (@{thm eq_reflection} OF [inverse])];
          val normalized_inverses = map (Simplifier.simplify arithmetic)
            [inverse, successor_inverse];
          val result = Simplifier.rewrite
            (arithmetic |> Simplifier.add_simps normalized_inverses) (Thm.rhs_of equation);
          val (coefficient, accumulator) = HOLogic.dest_prod
            (Thm.term_of (Thm.rhs_of result));
          val _ = if numeral coefficient andalso numeral accumulator then ()
            else error "Fermat transition did not produce a closed numeric state";
          val closed = Thm.transitive (Thm.symmetric index)
            (Thm.transitive equation result);
        in @{thm meta_eq_to_obj_eq} OF [closed] end;
      val completed = fold advance (1 upto count) initial;
      val selected = put_simpset HOL_basic_ss ctxt
        |> Simplifier.add_simps [@{thm fermat_binomial_accumulator_stream_def}, completed];
      fun finish (remaining, j) =
        if Term.exists_subterm (fn Const (name, _) =>
            name = @{const_name fermat_binomial_source_state} | _ => false) remaining
        then error ("Closed Fermat source was not consumed: " ^
          Syntax.string_of_term ctxt remaining)
        else SOLVED' (simp_tac arithmetic) j;
    in (simp_tac selected THEN_ALL_NEW SUBGOAL finish) i end)))
\<close>

lemma fermat_bounded_source_values:
  "fermat_binomial_accumulator_stream 1 3 2 =
      fermat_dyadic_unit 1 mod 2^3"
  "fermat_binomial_accumulator_stream 2 8 4 =
      fermat_dyadic_unit 2 mod 2^8"
  "fermat_binomial_accumulator_stream 3 20 8 =
      fermat_dyadic_unit 3 mod 2^20"
  "fermat_binomial_accumulator_stream 4 45 16 =
      fermat_dyadic_unit 4 mod 2^45"
  "fermat_binomial_accumulator_stream 5 95 32 =
      fermat_dyadic_unit 5 mod 2^95"
  "fermat_binomial_accumulator_stream 6 196 64 =
      fermat_dyadic_unit 6 mod 2^196"
  by fermat_source_steps+

theorem fermat_bounded_python_source_exact:
  assumes range: "1 \<le> t" "t \<le> 6"
  defines "p \<equiv> fermat_unit_complete_width t"
  shows "fermat_binomial_accumulator_stream t p (2 ^ t) =
      fermat_dyadic_unit t mod (2 ^ p)"
    and "(\<forall>j\<in>{1..2 ^ t}. \<not> fermat_binomial_python_stops t p j)"
    and "fermat_binomial_python_stops t p (2 ^ t + 1)"
    and "t < p \<and> (\<forall>j\<in>{1..2 ^ t}.
      fermat_two_valuation j \<le> t \<and>
      fermat_two_valuation j \<le> 2 * (j - 1))"
proof -
  have level: "0 < t" using range by arith
  have parameter_bounds:
    "t < fermat_unit_complete_width t \<and>
      (\<forall>j\<in>{1..2 ^ t}.
        fermat_two_valuation j \<le> t \<and>
        fermat_two_valuation j \<le> 2 * (j - 1))"
    using fermat_bounded_python_parameter_bounds range by auto
  have cases:
    "t = 1 \<or> t = 2 \<or> t = 3 \<or> t = 4 \<or> t = 5 \<or> t = 6"
    using range by arith
  have source_one:
    "fermat_binomial_accumulator_stream 1 (fermat_unit_complete_width 1) (2^1) =
      fermat_dyadic_unit 1 mod 2^(fermat_unit_complete_width 1)"
    using fermat_bounded_source_values(1)
    by (simp add: fermat_unit_complete_width_def)
  have source_two:
    "fermat_binomial_accumulator_stream 2 (fermat_unit_complete_width 2) (2^2) =
      fermat_dyadic_unit 2 mod 2^(fermat_unit_complete_width 2)"
    using fermat_bounded_source_values(2)
    by (simp add: fermat_unit_complete_width_def)
  have source_three:
    "fermat_binomial_accumulator_stream 3 (fermat_unit_complete_width 3) (2^3) =
      fermat_dyadic_unit 3 mod 2^(fermat_unit_complete_width 3)"
    using fermat_bounded_source_values(3)
    by (simp add: fermat_unit_complete_width_def)
  have source_four:
    "fermat_binomial_accumulator_stream 4 (fermat_unit_complete_width 4) (2^4) =
      fermat_dyadic_unit 4 mod 2^(fermat_unit_complete_width 4)"
    using fermat_bounded_source_values(4)
    by (simp add: fermat_unit_complete_width_def)
  have source_five:
    "fermat_binomial_accumulator_stream 5 (fermat_unit_complete_width 5) (2^5) =
      fermat_dyadic_unit 5 mod 2^(fermat_unit_complete_width 5)"
    using fermat_bounded_source_values(5)
    by (simp add: fermat_unit_complete_width_def)
  have source_six:
    "fermat_binomial_accumulator_stream 6 (fermat_unit_complete_width 6) (2^6) =
      fermat_dyadic_unit 6 mod 2^(fermat_unit_complete_width 6)"
    using fermat_bounded_source_values(6)
    by (simp add: fermat_unit_complete_width_def)
  show "fermat_binomial_accumulator_stream t p (2 ^ t) =
      fermat_dyadic_unit t mod (2 ^ p)"
    using cases source_one source_two source_three source_four source_five source_six
    unfolding p_def
    by (elim disjE; simp_all add: fermat_unit_complete_width_def)
  have scale: "2 * (2 ^ t - 1) < p"
    using fermat_unit_complete_width_exceeds_source_scale[OF range]
    unfolding p_def .
  show "\<forall>j\<in>{1..2 ^ t}. \<not> fermat_binomial_python_stops t p j"
    using fermat_binomial_python_continues_through_support[OF level scale]
    by auto
  show "fermat_binomial_python_stops t p (2 ^ t + 1)"
    by (rule fermat_binomial_python_stops_after_support[OF level])
  show "t < p \<and> (\<forall>j\<in>{1..2 ^ t}.
      fermat_two_valuation j \<le> t \<and>
      fermat_two_valuation j \<le> 2 * (j - 1))"
    using parameter_bounds unfolding p_def .
qed

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms fermat_binomial_python_continues_through_support
      fermat_binomial_python_stops_after_support
      fermat_unit_complete_width_exceeds_source_scale
      fermat_bounded_source_precision_values
      fermat_bounded_python_parameter_bounds
      fermat_bounded_source_values
      fermat_bounded_python_source_exact}) then ()
    else error "Bounded Fermat binomial source laws depend on an oracle";
\<close>

end
