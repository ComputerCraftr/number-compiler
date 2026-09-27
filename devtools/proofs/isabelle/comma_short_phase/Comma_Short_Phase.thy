theory Comma_Short_Phase
  imports Comma_Round_Totality.Comma_Round_Closure
begin

text \<open>Short phases are arithmetic cache keys for canonical Entry moves.
They do not identify absolute exponent gains or evaluated literal weights.
The power table exponent is rotated by 919, as in the canonical definition.\<close>

lemma comma_power_residue_rotated:
  "comma_power_residue P r =
    mod_exp (10::nat) (5 + ((r + 919) mod comma_short_period P)) P"
proof -
  have shift: "r + 924 - 5 = r + 919" by arith
  show ?thesis by (simp only: comma_power_residue_def shift)
qed

lemma comma_power_residue_short_cong:
  assumes phase: "r1 mod comma_short_period P = r2 mod comma_short_period P"
  shows "comma_power_residue P r1 = comma_power_residue P r2"
proof -
  have rotated: "(r1 + 919) mod comma_short_period P =
    (r2 + 919) mod comma_short_period P"
  proof -
    have "(r1 + 919) mod comma_short_period P =
      (r1 mod comma_short_period P + 919) mod comma_short_period P"
      by (rule mod_add_left_eq[symmetric])
    also have "... = (r2 mod comma_short_period P + 919) mod comma_short_period P"
      by (simp only: phase)
    also have "... = (r2 + 919) mod comma_short_period P"
      by (rule mod_add_left_eq)
    finally show ?thesis .
  qed
  show ?thesis by (simp only: comma_power_residue_rotated rotated)
qed

lemma comma_entry_short_period_divides:
  assumes f: "1 \<le> f" "f \<le> 9"
  shows "comma_short_period (comma_finite_period f (x mod 10)) dvd 924"
proof -
  have catalog: "comma_finite_period f (x mod 10) \<in> comma_cycle_displacements"
    using comma_finite_period_in_catalog[rule_format, of f "x mod 10"] f by auto
  show ?thesis using comma_short_period_catalog[OF catalog] by blast
qed

lemma comma_entry_headroom_short_phase:
  assumes f: "1 \<le> f" "f \<le> 9"
    and phase: "(r1 + d1) mod comma_short_period (comma_finite_period f (x mod 10)) =
      (r2 + d2) mod comma_short_period (comma_finite_period f (x mod 10))"
  shows "comma_finite_headroom f r1 d1 x = comma_finite_headroom f r2 d2 x"
proof -
  let ?P = "comma_finite_period f (x mod 10)"
  let ?T = "comma_short_period ?P"
  have divides: "?T dvd 924" by (rule comma_entry_short_period_divides[OF f])
  have reduced: "((r1+d1) mod 924) mod ?T = ((r2+d2) mod 924) mod ?T"
    using phase by (simp only: mod_mod_cancel[OF divides])
  have power: "comma_power_residue ?P ((r1+d1) mod 924) =
    comma_power_residue ?P ((r2+d2) mod 924)"
    by (rule comma_power_residue_short_cong[OF reduced])
  show ?thesis by (simp only: comma_finite_headroom_def Let_def power)
qed

lemma comma_finite_entry_short_phase_transport:
  assumes f: "1 \<le> f" "f \<le> 9"
    and phase: "(r1 + d1) mod comma_short_period (comma_finite_period f (x mod 10)) =
      (r2 + d2) mod comma_short_period (comma_finite_period f (x mod 10))"
  shows "(comma_finite_step r1 (Comma_Entry f d1 x) = Comma_Next (Comma_Near f d1 h)) =
    (comma_finite_step r2 (Comma_Entry f d2 x) = Comma_Next (Comma_Near f d2 h))"
  using comma_entry_headroom_short_phase[OF f phase]
  by (simp add: comma_finite_step_def comma_weighted_step_def Let_def)

lemma comma_finite_entry_short_phase_shift:
  assumes f: "1 \<le> f" "f \<le> 9"
  shows "comma_finite_step r (Comma_Entry f delta x) =
    comma_shift_move delta
      (comma_finite_step ((r+delta) mod comma_short_period
        (comma_finite_period f (x mod 10))) (Comma_Entry f 0 x))"
proof -
  let ?T = "comma_short_period (comma_finite_period f (x mod 10))"
  have phase: "(r+delta) mod ?T = (((r+delta) mod ?T)+0) mod ?T" by simp
  have headroom: "comma_finite_headroom f r delta x =
    comma_finite_headroom f ((r+delta) mod ?T) 0 x"
    by (rule comma_entry_headroom_short_phase[OF f phase])
  show ?thesis using headroom
    by (simp add: comma_finite_step_def comma_weighted_step_def Let_def)
qed

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_power_residue_rotated comma_power_residue_short_cong
      comma_entry_headroom_short_phase comma_finite_entry_short_phase_transport
      comma_finite_entry_short_phase_shift})
    then () else error "Comma short-phase transport depends on an oracle";
\<close>
end
