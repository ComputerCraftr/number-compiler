theory Comma_Future_M204_Source_Join
  imports Comma_Future_M204_Source_Code
begin

lemma comma_future_m204_source_join_encoded:
  assumes valid: "comma_boundary_valid q"
    and code: "code = comma_parametric_typed_mask_code
      (comma_phase_program_full_action_output (snd (snd q))
        (comma_decisive_endpoint_round (snd (snd q)) (comma_finite_initial q)))"
    and source: "comma_future_m204_source_output D q = Some (J,delta)"
  shows "code \<noteq> 0 \<and> (if code\<le>46 then
      1+J+9*delta = D ((snd (snd q)+1) mod 924) (code-1)+10
    else 1+J+9*delta = code-46)"
proof -
  note exact = comma_future_m204_source_encoded_output[OF valid code]
  have nonzero: "code\<noteq>0" using exact source by (cases "code=0") auto
  show ?thesis
  proof (cases "code\<le>46")
    case True
    let ?v = "D ((snd (snd q)+1) mod 924) (code-1)"
    have parts: "J=?v mod 9" "delta=1+?v div 9"
      using exact source nonzero True by (simp_all add: Let_def)
    have identity: "?v mod 9 + 9*(?v div 9) = ?v"
      using div_mult_mod_eq[of ?v 9] by (simp add: mult.commute)
    have "1+J+9*delta = ?v+10" using parts identity by arith
    with nonzero True show ?thesis by simp
  next
    case False
    have parts: "J=code-47" "delta=0"
      using exact source nonzero False by simp_all
    have "47\<le>code" using False by arith
    then have "1+J+9*delta=code-46" using parts by arith
    with nonzero False show ?thesis by simp
  qed
qed

lemma comma_future_m204_decode_join:
  fixes J delta :: nat
  assumes "J<9"
  shows "1+J+9*delta\<noteq>0"
    "(1+J+9*delta-1) mod 9=J"
    "(1+J+9*delta-1) div 9=delta"
  using assms by (simp_all add: mod_add_left_eq div_add1_eq)

end
