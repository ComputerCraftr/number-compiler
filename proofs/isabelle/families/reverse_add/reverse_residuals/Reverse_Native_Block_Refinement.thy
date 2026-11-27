theory Reverse_Native_Block_Refinement
  imports Reverse_Laurent_Producer_Refinement
begin

text \<open>The bounded native decimal block starts by normalizing its Q19
coefficient source once. It then performs @{term "duration - 1"} ordinary
decimal reverse/add transitions and pairizes the final digits. This bridge
identifies that final re-symmetrization with the next exact Q19 field. The
finite trace records the scalar decimal value at the pre-pair and completed-
pair boundaries; an observed endpoint does not license repetition beyond
this finite duration.\<close>

lemma punctured_expand_singleton_runs:
  "punctured_expand_runs (map (\<lambda>symbol. (symbol, 1)) symbols) = symbols"
  by (induction symbols) simp_all

lemma reverse_add_run_last_step:
  assumes duration_positive: "0 < duration"
  shows "step (run step (duration - 1) source) = run step duration source"
proof -
  have duration_split: "duration = Suc (duration - 1)"
    using duration_positive by simp
  have run_to_step:
    "run step duration source = step (run step (duration - 1) source)"
  proof -
    have "run step duration source =
        run step (Suc (duration - 1)) source"
      by (rule arg_cong[OF duration_split,
          where f="\<lambda>n. run step n source"])
    also have "... = run step (duration - 1) (step source)"
      by simp
    also have "... = step (run step (duration - 1) source)"
      by (rule run_commutes_with_step)
    finally show ?thesis .
  qed
  show ?thesis by (rule run_to_step[symmetric])
qed

theorem reverse_laurent_native_block_final_pair_refines:
  assumes initial_valid: "valid_pair initial"
      and duration_positive: "0 < duration"
  defines "current \<equiv> run step (duration - 1) initial"
  shows "punctured_q19_decode_half
      (punctured_expand_runs
        (punctured_pair_mirror_half
          (punctured_decimal_runs
            (reverse_laurent_full_runs
              (map (\<lambda>symbol. (symbol, 1))
                (reverse_laurent_source_half current))
              (reverse_laurent_source_odd current)))))
      (punctured_run_width
        (punctured_decimal_runs
          (reverse_laurent_full_runs
            (map (\<lambda>symbol. (symbol, 1))
              (reverse_laurent_source_half current))
            (reverse_laurent_source_odd current))) mod 2 = 1) =
        run step duration initial \<and>
    reverse_two_port_publisher
      (punctured_q19_decode_half
        (reverse_laurent_source_half current)
        (reverse_laurent_source_odd current)) =
      run step duration initial \<and>
    length (run step duration initial) = length (digits current) \<and>
    reverse_add_pair_finite_trace initial duration ! (duration - 1) =
      reverse_add_pair_term current \<and>
    reverse_add_pair_finite_trace initial duration ! duration =
      reverse_add_pair_term (run step duration initial)"
proof -
  have current_valid: "valid_pair current"
    unfolding current_def
    by (rule valid_pair_run[OF initial_valid])
  have current_symmetric: "rev current = current"
    using current_valid by (simp add: valid_pair_def)
  have current_nonempty: "current \<noteq> []"
    using current_valid by (simp add: valid_pair_def)
  have current_half:
    "punctured_q19_decode_half
      (reverse_laurent_source_half current)
      (reverse_laurent_source_odd current) = current"
    by (rule reverse_laurent_half_reconstructs_symmetric_source
      [OF current_symmetric])
  have current_half_nonempty:
    "reverse_laurent_source_half current \<noteq> []"
  proof -
    have current_length_positive: "0 < length current"
      using current_nonempty by simp
    have half_length_positive:
      "0 < (length current + 1) div 2"
      using current_length_positive by presburger
    show ?thesis
      unfolding reverse_laurent_source_half_def
      using current_nonempty half_length_positive by simp
  qed
  let ?half = "map (\<lambda>symbol. (symbol, 1))
      (reverse_laurent_source_half current)"
  have half_nonempty: "?half \<noteq> []"
    using current_half_nonempty by simp
  have half_positive: "punctured_positive_runs ?half"
    by (simp add: punctured_positive_runs_def)
  have source_half_subset:
    "set (reverse_laurent_source_half current) \<subseteq> set current"
    unfolding reverse_laurent_source_half_def
    by (rule set_take_subset)
  have half_bounded: "\<forall>run\<in>set ?half. fst run \<le> 18"
    using current_valid source_half_subset
    by (auto simp: valid_pair_def)
  have decoded_half:
    "punctured_q19_decode_half (punctured_expand_runs ?half)
      (reverse_laurent_source_odd current) = current"
    using current_half punctured_expand_singleton_runs by simp
  have one_tick:
    "punctured_q19_decode_half
        (punctured_expand_runs
          (punctured_pair_mirror_half
            (punctured_decimal_runs
              (reverse_laurent_full_runs ?half
                (reverse_laurent_source_odd current)))))
        (punctured_run_width
          (punctured_decimal_runs
            (reverse_laurent_full_runs ?half
              (reverse_laurent_source_odd current))) mod 2 = 1) =
      step (punctured_q19_decode_half (punctured_expand_runs ?half)
        (reverse_laurent_source_odd current))"
    using reverse_laurent_half_tape_tick_refines_step
      [where half="?half" and is_odd="reverse_laurent_source_odd current"]
      half_nonempty half_positive half_bounded
    by simp
  have successor:
    "step current = run step duration initial"
    unfolding current_def
    by (rule reverse_add_run_last_step[OF duration_positive])
  have endpoint:
    "punctured_q19_decode_half
      (punctured_expand_runs
        (punctured_pair_mirror_half
          (punctured_decimal_runs
            (reverse_laurent_full_runs ?half
              (reverse_laurent_source_odd current)))))
      (punctured_run_width
        (punctured_decimal_runs
          (reverse_laurent_full_runs ?half
            (reverse_laurent_source_odd current))) mod 2 = 1) =
      run step duration initial"
    using one_tick decoded_half successor by simp
  have q19_endpoint:
    "reverse_two_port_publisher
        (punctured_q19_decode_half
          (reverse_laurent_source_half current)
          (reverse_laurent_source_odd current)) =
      run step duration initial"
    using reverse_laurent_q19_publisher_refines_source[OF current_valid]
      successor by simp
  have endpoint_width:
    "length (run step duration initial) = length (digits current)"
  proof -
    have "length (run step duration initial) = length (step current)"
      by (rule arg_cong[OF successor[symmetric]])
    also have "... = length (digits current)"
      by (rule length_step_exact)
    finally show ?thesis .
  qed
  have before_trace:
    "reverse_add_pair_finite_trace initial duration ! (duration - 1) =
      reverse_add_pair_term current"
    unfolding current_def
    by (rule reverse_add_pair_finite_trace_at) simp
  have endpoint_trace:
    "reverse_add_pair_finite_trace initial duration ! duration =
      reverse_add_pair_term (run step duration initial)"
    by (rule reverse_add_pair_finite_trace_at) simp
  show ?thesis
    using endpoint q19_endpoint endpoint_width before_trace endpoint_trace
    by (simp add: current_def)
qed

text \<open>The Python finite block has a scalar phase between Q19-normalized
source digits and the final pair publication.  Model that phase as an exact
least-significant-digit-first word transition; do not identify it with a
CPython Decimal implementation theorem.  The following refinement shows the
word loop follows the same finite source run, and the existing checked
half-tape theorem identifies its final re-pairing with the next pair state.\<close>

definition reverse_add_decimal_digit_step :: "nat list \<Rightarrow> nat list" where
  "reverse_add_decimal_digit_step ds =
    digits (map (\<lambda>(left, right). left + right) (zip ds (rev ds)))"

fun reverse_add_decimal_digit_run :: "nat \<Rightarrow> nat list \<Rightarrow> nat list" where
  "reverse_add_decimal_digit_run 0 ds = ds"
| "reverse_add_decimal_digit_run (Suc n) ds =
    reverse_add_decimal_digit_run n (reverse_add_decimal_digit_step ds)"

lemma reverse_add_decimal_digit_step_on_pair:
  "reverse_add_decimal_digit_step (digits source) = digits (step source)"
  by (simp add: reverse_add_decimal_digit_step_def step_def)

theorem reverse_add_decimal_digit_run_refines_pair_run:
  "reverse_add_decimal_digit_run n (digits source) =
    digits (run step n source)"
proof (induction n arbitrary: source)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have next_digits:
    "reverse_add_decimal_digit_step (digits source) = digits (step source)"
    by (rule reverse_add_decimal_digit_step_on_pair)
  show ?case
    using Suc.IH[of "step source"] next_digits
    by simp
qed

theorem reverse_add_decimal_tick_value:
  assumes valid: "valid_pair source"
  shows "decimal_list_value (digits source) +
      decimal_list_value (rev (digits source)) =
    reverse_add_pair_term (step source)"
proof -
  have successor:
    "reverse_add_pair_term (step source) =
      reverse_add_pair_term source + reverse_add_pair_reverse source"
    by (rule reverse_add_completed_pair_successor[OF valid])
  show ?thesis
    using successor
    by (simp add: reverse_add_pair_term_def reverse_add_pair_reverse_def)
qed

theorem reverse_laurent_native_block_scalar_to_pair:
  assumes initial_valid: "valid_pair initial"
      and duration_positive: "0 < duration"
  defines "current \<equiv> run step (duration - 1) initial"
  shows "reverse_add_decimal_digit_run (duration - 1) (digits initial) =
        digits current \<and>
    decimal_list_value (digits current) +
      decimal_list_value (rev (digits current)) =
        reverse_add_pair_term (run step duration initial) \<and>
    reverse_two_port_publisher
      (punctured_q19_decode_half
        (reverse_laurent_source_half current)
        (reverse_laurent_source_odd current)) =
      run step duration initial"
proof -
  have current_valid: "valid_pair current"
    unfolding current_def
    by (rule valid_pair_run[OF initial_valid])
  have digit_path:
    "reverse_add_decimal_digit_run (duration - 1) (digits initial) =
      digits current"
    unfolding current_def
    by (rule reverse_add_decimal_digit_run_refines_pair_run)
  have successor_exact: "step current = run step duration initial"
    unfolding current_def
    by (rule reverse_add_run_last_step[OF duration_positive])
  have scalar_tick:
    "decimal_list_value (digits current) +
      decimal_list_value (rev (digits current)) =
        reverse_add_pair_term (run step duration initial)"
  proof -
    have scalar_value:
      "decimal_list_value (digits current) +
        decimal_list_value (rev (digits current)) =
          reverse_add_pair_term (step current)"
      by (rule reverse_add_decimal_tick_value[OF current_valid])
    show ?thesis using scalar_value successor_exact by simp
  qed
  have q19:
    "reverse_two_port_publisher
      (punctured_q19_decode_half
        (reverse_laurent_source_half current)
        (reverse_laurent_source_odd current)) =
      run step duration initial"
    using reverse_laurent_q19_publisher_refines_source[OF current_valid]
      successor_exact by simp
  show ?thesis using digit_path scalar_tick q19 by blast
qed


text \<open>The native endpoint stores the low-side digits and one symmetric
half of the successor pair field.  These facts reconstruct the opposite digit
without storing an intermediate row.  The source controls the birth bit.\<close>

lemma reverse_native_pair_at_physical_digit:
  assumes "i < length (digits source)"
  shows "step source ! i = digits source ! i +
    digits source ! (length (digits source) - Suc i)"
  using assms by (simp add: step_def rev_nth)

lemma reverse_native_opposite_digit_from_pair:
  assumes "i < length (digits source)"
  shows "digits source ! (length (digits source) - Suc i) =
    step source ! i - digits source ! i"
  using reverse_native_pair_at_physical_digit[OF assms] by simp

lemma reverse_native_center_pair_even:
  assumes "odd (length (digits source))"
  shows "even (step source ! (length (digits source) div 2))"
proof -
  have bound: "length (digits source) div 2 < length (digits source)"
    using assms by presburger
  have center: "length (digits source) - Suc (length (digits source) div 2) =
      length (digits source) div 2"
    using assms by presburger
  show ?thesis using reverse_native_pair_at_physical_digit[OF bound] center by simp
qed

theorem reverse_native_folded_endpoint_clock:
  assumes initial_valid: "valid_pair initial" and duration: "0 < duration"
  defines "current \<equiv> run step (duration - 1) initial"
    and "endpoint \<equiv> run step duration initial"
  shows "valid_pair endpoint \<and>
    punctured_q19_decode_half (reverse_laurent_source_half endpoint)
      (reverse_laurent_source_odd endpoint) = endpoint \<and>
    length endpoint = length current + (if carry_out False current then 1 else 0) \<and>
    (reverse_laurent_source_odd endpoint =
      (reverse_laurent_source_odd current \<noteq> carry_out False current)) \<and>
    (\<forall>i < length (digits current).
      digits current ! (length (digits current) - Suc i) =
        endpoint ! i - digits current ! i) \<and>
    (reverse_laurent_source_odd endpoint \<longrightarrow>
      even (endpoint ! (length endpoint div 2)))"
proof -
  have successor: "endpoint = step current"
    unfolding endpoint_def current_def
    using reverse_add_run_last_step[OF duration, of initial] by simp
  have symmetric: "rev endpoint = endpoint"
    unfolding successor by (rule step_symmetric)
  have valid: "valid_pair endpoint"
    unfolding endpoint_def by (rule valid_pair_run[OF initial_valid])
  have width: "length endpoint =
      length current + (if carry_out False current then 1 else 0)"
    unfolding successor by (simp add: length_digits_exact)
  have decode: "punctured_q19_decode_half (reverse_laurent_source_half endpoint)
      (reverse_laurent_source_odd endpoint) = endpoint"
    by (rule reverse_laurent_half_reconstructs_symmetric_source[OF symmetric])
  have parity: "reverse_laurent_source_odd endpoint =
      (reverse_laurent_source_odd current \<noteq> carry_out False current)"
    using width by (cases "carry_out False current")
      (simp_all add: reverse_laurent_source_odd_def)
  have opposite: "\<forall>i < length (digits current).
      digits current ! (length (digits current) - Suc i) =
        endpoint ! i - digits current ! i"
    unfolding successor using reverse_native_opposite_digit_from_pair by blast
  have center: "reverse_laurent_source_odd endpoint \<longrightarrow>
      even (endpoint ! (length endpoint div 2))"
    unfolding successor reverse_laurent_source_odd_def
    using reverse_native_center_pair_even[of current] by simp
  show ?thesis using valid decode width parity opposite center by blast
qed

text \<open>Two physical pair publishers form a bounded receiving contract.
The first physical carry is the low bit. The next carry is the high bit.
The source is decoded from its issued symmetric half before either pass.\<close>

definition reverse_native_two_pass_ports :: "nat list \<Rightarrow> nat list \<times> nat" where
  "reverse_native_two_pass_ports source =
    (let decoded = punctured_q19_decode_half (reverse_laurent_source_half source)
          (reverse_laurent_source_odd source);
         first = reverse_two_port_publisher decoded;
         port = (if carry_out False decoded then 1 else 0) +
           2 * (if carry_out False first then 1 else 0)
     in (reverse_two_port_publisher first, port))"

theorem reverse_native_two_pass_source_ports:
  assumes valid: "valid_pair source"
  defines "result \<equiv> reverse_native_two_pass_ports source"
  shows "fst result = step (step source) \<and>
    snd result mod 2 = (if carry_out False source then 1 else 0) \<and>
    snd result div 2 = (if carry_out False (step source) then 1 else 0) \<and>
    length (fst result) = length source + snd result mod 2 + snd result div 2 \<and>
    valid_pair (fst result)"
proof -
  have symmetric: "rev source = source" using valid by (simp add: valid_pair_def)
  have decoded: "punctured_q19_decode_half (reverse_laurent_source_half source)
      (reverse_laurent_source_odd source) = source"
    by (rule reverse_laurent_half_reconstructs_symmetric_source[OF symmetric])
  have first: "reverse_two_port_publisher source = step source"
    by (rule reverse_two_port_publisher_refines_step[OF valid])
  have first_valid: "valid_pair (step source)"
    by (rule valid_pair_successor[OF valid])
  have second: "reverse_two_port_publisher (step source) = step (step source)"
    by (rule reverse_two_port_publisher_refines_step[OF first_valid])
  show ?thesis using valid
    by (simp add: result_def reverse_native_two_pass_ports_def Let_def decoded first second
        length_step_exact length_digits_exact valid_pair_successor)
qed

lemma reverse_native_two_pass_birth_order_distinguishes:
  "snd (reverse_native_two_pass_ports [18]) mod 2 = 1 \<and>
   snd (reverse_native_two_pass_ports [18]) div 2 = 0 \<and>
   snd (reverse_native_two_pass_ports [9,9]) mod 2 = 0 \<and>
   snd (reverse_native_two_pass_ports [9,9]) div 2 = 1"
proof -
  have a: "valid_pair [18]" and b: "valid_pair [9,9]"
    by (simp_all add: valid_pair_def)
  note first = reverse_native_two_pass_source_ports[OF a]
  note second = reverse_native_two_pass_source_ports[OF b]
  show ?thesis using first second
    by (simp add: carry_out_def domain_def)
qed

ML \<open>
  val checked = @{thms punctured_expand_singleton_runs
    reverse_add_run_last_step
    reverse_laurent_native_block_final_pair_refines
    reverse_add_decimal_digit_run_refines_pair_run
    reverse_add_decimal_tick_value
    reverse_laurent_native_block_scalar_to_pair
    reverse_native_opposite_digit_from_pair reverse_native_center_pair_even
    reverse_native_folded_endpoint_clock reverse_native_two_pass_source_ports
    reverse_native_two_pass_birth_order_distinguishes};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Reverse native block refinement depends on an oracle";
  val _ = if Thm_Deps.has_skip_proof checked
    then error "Skipped reverse native block refinement proof" else ();
\<close>

end
