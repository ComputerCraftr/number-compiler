theory Five_Reverse_Moving_Cut_Limits
  imports Five_Reverse_Digit_Field Five_Reverse_Reflected_H
begin

text \<open>
The physical three-place field uses a normalized two-digit suffix.  The
mod-225 field alone cannot select that suffix or its mod-1125 lift.  The
second result records the precise cutoff and charged work in the existing
bounded H evaluator; it does not assert that the first larger precision is
nonzero, nor does it prove a global lower bound for other algorithms.
\<close>

theorem five_field_third_place_needs_source:
  "five_digit_field (five_reverse_orbit 1 2) mod 225 =
    five_digit_field (five_reverse_orbit 1 11) mod 225 \<and>
   five_digit_field (five_reverse_orbit 1 2) mod 1125 = 50 \<and>
   five_digit_field (five_reverse_orbit 1 11) mod 1125 = 275"
  by (simp add: five_reverse_step_def decimal_reverse.simps decimal_digit_count.simps
      five_digit_field_equation five_digit_block_width_def)

theorem five_h_9967_cutoff_and_checked_work:
  fixes k source :: nat
  shows "(k \<le> 2491 \<longrightarrow>
      five_reflected_H_iter 4983 source mod 10^k = 0) \<and>
    (2*k > 4983 \<longrightarrow> 4983*k \<ge> 12417636)"
proof
  show "k \<le> 2491 \<longrightarrow>
      five_reflected_H_iter 4983 source mod 10^k = 0"
    by (intro impI; rule five_reflected_H_iter_cutoff; linarith)
  show "2*k > 4983 \<longrightarrow> 4983*k \<ge> 12417636"
    by linarith
qed

ML \<open>
  val checked = @{thms five_field_third_place_needs_source
    five_h_9967_cutoff_and_checked_work};
  val _ = if null (Thm_Deps.all_oracles checked) then () else error "moving cut uses an oracle";
  val _ = if Thm_Deps.has_skip_proof checked then error "moving cut has skipped proofs" else ();
\<close>
end
