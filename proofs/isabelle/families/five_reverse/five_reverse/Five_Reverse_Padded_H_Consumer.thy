theory Five_Reverse_Padded_H_Consumer
  imports Five_Reverse_Reflected_H
begin

text \<open>The even inlet and odd-track successor publish the same physical
endpoint for every source and every finite H horizon. This connects the
independently proved source-orbit formulas; the concrete tile evaluator
still requires its own refinement to the H iteration.\<close>

theorem five_reverse_padded_even_inlet_agrees_with_odd_successor:
  "5 * five_reflected_normalize
      (five_reflected_H_iter t (five_reflected_E seed)) =
    five_reverse_step
      (5 * five_reflected_normalize
        (five_reflected_H_iter t (decimal_reverse seed)))"
proof -
  have count: "2*t+2 = Suc (2*t+1)" by simp
  have successor:
    "five_reverse_orbit (2*t+2) seed =
      five_reverse_step (five_reverse_orbit (2*t+1) seed)"
    by (simp only: count five_reverse_orbit.simps)
  show ?thesis
    using successor five_reflected_orbit_even[of t seed]
      five_reflected_orbit_odd[of t seed] by simp
qed

ML \<open>
  val checked = @{thms five_reverse_padded_even_inlet_agrees_with_odd_successor};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Padded H consumer proof depends on an oracle";
  val _ = if Thm_Deps.has_skip_proof checked
    then error "Skipped padded H consumer proof" else ();
\<close>

end
