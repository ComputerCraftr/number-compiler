theory Five_Reverse_Window_Consumer
  imports Five_Reverse_Prefix_Bridge
begin

text \<open>The border recurrence mirrors the finite Python port evaluator.
Its optional result preserves the evaluator's refusal when its geometric
preconditions do not hold. This theorem only certifies the four source-bound
rows already proved for seed 196; it does not certify every table row or a
repeatable action.\<close>

definition five_reverse_reverse_three :: "nat \<Rightarrow> nat" where
  "five_reverse_reverse_three value =
    (value mod 10) * 100 + ((value div 10) mod 10) * 10 +
      (value div 100)"

definition five_reverse_guarded_border_action ::
    "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
      ((nat \<times> nat) \<times> nat) option" where
  "five_reverse_guarded_border_action head3 tail3 inlet =
    (let raw = 5 * five_reverse_reverse_three tail3 + inlet
     in if 100 \<le> head3 \<and> head3 \<le> 999 \<and>
          tail3 \<le> 999 \<and> inlet \<le> 4 \<and> 100 \<le> raw
        then Some
          ((if 1000 \<le> raw then raw div 10 else raw,
            (5 * five_reverse_reverse_three head3) mod 1000),
           if 1000 \<le> raw then 1 else 0)
        else None)"

definition five_reverse_port_border_action ::
    "nat \<times> (nat \<times> nat) \<times> (nat \<times> nat) \<Rightarrow>
      (((nat \<times> nat) \<times> nat) option) \<times> (nat \<times> nat)" where
  "five_reverse_port_border_action port =
    (case port of (inlet, (head3, tail3), target) \<Rightarrow>
      (five_reverse_guarded_border_action head3 tail3 inlet, target))"

definition five_reverse_port_action_growth ::
    "nat \<times> (nat \<times> nat) \<times> (nat \<times> nat) \<Rightarrow> nat option" where
  "five_reverse_port_action_growth port =
    map_option snd (fst (five_reverse_port_border_action port))"

theorem five_reverse_seed196_window_border_actions:
  "map five_reverse_port_border_action
      (map (five_reverse_window_port 196) [180..<184]) =
    [(Some ((348,215),0),(348,215)),
     (Some ((256,215),1),(256,215)),
     (Some ((256,260),1),(256,260)),
     (Some ((311,260),0),(311,260))]"
  unfolding five_reverse_seed196_window_orbit_anchor
  by (tactic \<open>asm_full_simp_tac
      (Shared_Closed_Arithmetic.natural_context \<^context>
        |> Simplifier.add_simps @{thms five_reverse_port_border_action_def
          five_reverse_guarded_border_action_def five_reverse_reverse_three_def
          list.map upt_rec_numeral}) 1\<close>)

theorem five_reverse_seed196_window_digit_widths:
  "decimal_digit_count (five_reverse_orbit 180 196) = 47 \<and>
   decimal_digit_count (five_reverse_orbit 181 196) = 47 \<and>
   decimal_digit_count (five_reverse_orbit 182 196) = 48 \<and>
   decimal_digit_count (five_reverse_orbit 183 196) = 49 \<and>
   decimal_digit_count (five_reverse_orbit 184 196) = 49"
  using five_reverse_seed196_orbit_180 five_reverse_seed196_orbit_181
    five_reverse_seed196_orbit_182 five_reverse_seed196_orbit_183
    five_reverse_seed196_orbit_184
  by (tactic \<open>asm_full_simp_tac
      (Shared_Closed_Arithmetic.natural_context \<^context>
        |> Simplifier.add_simps @{thms five_reverse_seed196_orbit_180
          five_reverse_seed196_orbit_181 five_reverse_seed196_orbit_182
          five_reverse_seed196_orbit_183 five_reverse_seed196_orbit_184
          decimal_digit_count.simps}) 1\<close>)

theorem five_reverse_seed196_window_physical_width_growth:
  "map (\<lambda>generation.
      decimal_digit_count (five_reverse_orbit (Suc generation) 196) -
        decimal_digit_count (five_reverse_orbit generation 196))
      [180..<184] = [0,1,1,0]"
  by (tactic \<open>asm_full_simp_tac
      (Shared_Closed_Arithmetic.natural_context \<^context>
        |> Simplifier.add_simps @{thms five_reverse_seed196_window_digit_widths
          list.map upt_rec_numeral}) 1\<close>)

theorem five_reverse_seed196_window_action_growth_matches_width:
  "map five_reverse_port_action_growth
      (map (five_reverse_window_port 196) [180..<184]) =
    map (\<lambda>generation. Some
      (decimal_digit_count (five_reverse_orbit (Suc generation) 196) -
        decimal_digit_count (five_reverse_orbit generation 196)))
      [180..<184]"
  unfolding five_reverse_seed196_window_orbit_anchor
  by (tactic \<open>asm_full_simp_tac
      (Shared_Closed_Arithmetic.natural_context \<^context>
        |> Simplifier.add_simps @{thms five_reverse_port_action_growth_def
          five_reverse_port_border_action_def
          five_reverse_guarded_border_action_def
          five_reverse_reverse_three_def map_option_case option.case
          five_reverse_seed196_window_digit_widths list.map upt_rec_numeral}) 1\<close>)

ML \<open>
  val checked = @{thms five_reverse_reverse_three_def
    five_reverse_guarded_border_action_def
    five_reverse_port_border_action_def five_reverse_port_action_growth_def
    five_reverse_seed196_window_border_actions
    five_reverse_seed196_window_digit_widths
    five_reverse_seed196_window_physical_width_growth
    five_reverse_seed196_window_action_growth_matches_width};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Five-reverse finite border consumer depends on an oracle";
  val _ = if Thm_Deps.has_skip_proof checked
    then error "Skipped five-reverse finite border-consumer proof" else ();
\<close>

end
