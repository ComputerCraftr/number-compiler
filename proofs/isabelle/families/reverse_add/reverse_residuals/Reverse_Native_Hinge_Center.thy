theory Reverse_Native_Hinge_Center
  imports Reverse_Native_Block_Refinement
begin

text \<open>The shift on a physical width birth exposes one more high-side
digit at the old cut. The compiled single-level response supplies that
digit, including the carry digit 1 when the outside half is empty.\<close>

theorem reverse_native_hinge_middle_word:
  fixes half middle :: "nat list" and a b :: bool and high :: nat and physical :: "nat list"
  defines "a \<equiv> carry_out False half" and "b \<equiv> carry_out a middle"
    and "high \<equiv> snd (reverse_native_hinge1_compile half b)"
    and "physical \<equiv> half @ middle @ rev half"
  shows "carry_out False physical = (high \<noteq> 0)"
    and "take (length middle + (if high=0 then 0 else 1)) (drop (length half) (digits physical)) =
      emit a middle @ (if high=0 then [] else [high-1])"
proof -
  let ?born = "carry_out b (rev half)"
  have clock: "carry_out False physical = ?born"
    by (simp add: physical_def b_def a_def carry_out_append)
  have response: "high = (if ?born then
      (if half=[] then 2 else 1 + (last half + (if b then 1 else 0)) mod 10) else 0)"
    using reverse_native_hinge1_source_response[of half b] by (simp add: high_def)
  show "carry_out False physical = (high \<noteq> 0)" by (simp add: clock response)
  let ?suffix = "emit b (rev half) @ (if ?born then [1] else [])"
  have word: "digits physical = emit False half @ emit a middle @ ?suffix"
    unfolding digits_def using clock by (simp add: physical_def a_def b_def emit_append carry_out_append)
  have exposed: "take (if high=0 then 0 else 1) ?suffix = (if high=0 then [] else [high-1])"
  proof (cases half rule: rev_cases)
    case Nil
    then show ?thesis by (simp add: response carry_out_def)
  next
    case (snoc ys s)
    then show ?thesis by (cases ?born; cases b) (simp_all add: response snoc)
  qed
  have drop: "drop (length half) (digits physical) = emit a middle @ ?suffix"
    by (simp add: word)
  have prefix: "take (length middle + k) (emit a middle @ xs) = emit a middle @ take k xs" for k xs
    by (simp add: take_append)
  show "take (length middle + (if high=0 then 0 else 1)) (drop (length half) (digits physical)) =
      emit a middle @ (if high=0 then [] else [high-1])"
    by (simp only: drop prefix exposed)
qed

ML \<open>
  val checked = @{thms reverse_native_hinge_middle_word};
  val _ = if null (Thm_Deps.all_oracles checked) then () else error "Compiled middle-word oracle";
  val _ = if Thm_Deps.has_skip_proof checked then error "Skipped compiled middle-word proof" else ();
\<close>
end
