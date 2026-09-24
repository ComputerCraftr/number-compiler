theory Comma_Macro_Refinement
  imports Comma_Macro_Constructor
begin

text \<open>The macro's cycle count is interpreted against the literal comma-child
relation.  In particular, a cached macro result is not itself a proof that
its intermediate weighted steps were legal.\<close>

lemma comma_cycle_length_admitted:
  assumes f: "1 \<le> f" "f \<le> 9"
  shows "0 < comma_cycle_length f"
    "10 dvd comma_cycle_length f * f"
proof -
  let ?g = "gcd f 10"
  have g_pos: "0 < ?g" by simp
  have g_ten: "?g dvd 10" by simp
  have g_f: "?g dvd f" by simp
  obtain a where ten: "10 = ?g * a"
    using g_ten by (auto simp: dvd_def)
  obtain b where fv: "f = ?g * b"
    using g_f by (auto simp: dvd_def)
  have a_pos: "0 < a" using ten by (cases a) auto
  have length: "comma_cycle_length f = a"
  proof -
    have "comma_cycle_length f = 10 div ?g"
      by (simp add: comma_cycle_length_def)
    also have "... = (?g * a) div ?g" using ten by simp
    also have "... = a" using g_pos by simp
    finally show ?thesis .
  qed
  show "0 < comma_cycle_length f" using length a_pos by simp
  have "comma_cycle_length f * f = a * (?g * b)"
    using length fv by simp
  also have "... = (?g * a) * b" by (simp add: mult_ac)
  also have "... = 10 * b" using ten by simp
  finally have "comma_cycle_length f * f = 10 * b" .
  then show "10 dvd comma_cycle_length f * f" by simp
qed

lemma comma_period_displacement_admitted:
  assumes "0 < f" "0 < L"
  shows "0 < comma_period_displacement f d L"
proof -
  obtain j where L: "L = Suc j" using assms(2)
    by (cases L) auto
  show ?thesis using assms(1)
    by (simp add: L comma_period_displacement_succ)
qed

lemma comma_fixed_iter_complete_cycles:
  assumes closes: "10 dvd L * f"
  shows "comma_fixed_iter f (c * L) k =
    k + c * comma_period_displacement f (k mod 10) L"
proof -
  have "comma_period_displacement f (k mod 10) (c * L) =
    c * comma_period_displacement f (k mod 10) L"
    using comma_period_displacement_repeated[OF closes,
      of "k mod 10" c 0]
    by (simp add: comma_period_displacement_def)
  then show ?thesis by (simp add: comma_fixed_iter_displacement)
qed

lemma comma_singleton_step_chart:
  fixes H d f' p' :: nat and same :: bool
  assumes source: "comma_sector f p k" and exponent: "2 \<le> p"
    and singleton: "comma_large_children f p k = [target]"
  defines "H \<equiv> comma_headroom f p k"
    and "d \<equiv> k mod 10"
    and "same \<equiv> (if f < 9 then H > 10 * d + f + 1
      else H > 10 * d + 9)"
    and "f' \<equiv> (if same then f else if f < 9 then f + 1 else 1)"
    and "p' \<equiv> (if same \<or> f < 9 then p else Suc p)"
  shows "comma_child k target" "comma_sector f' p' target" "2 \<le> p'"
proof -
  show "comma_child k target"
    using comma_large_children_complete[OF source exponent, of target]
      singleton by simp
  show "2 \<le> p'" using exponent by (simp add: p'_def)
  show "comma_sector f' p' target"
  proof (cases "f < 9")
    case True
    have less_nine: "f < 9" using True .
    let ?low = "k + 10 * d + f"
    let ?high = "?low + 1"
    let ?threshold = "10 * d + f + 1"
    show ?thesis
    proof (cases "H > ?threshold")
      case True
      have target_eq: "target = ?low"
        using singleton less_nine True
        by (simp add: comma_large_children_def H_def d_def Let_def)
      have "comma_sector f p ?low"
        using comma_current_sector_candidate[OF source less_nine]
          True by (simp add: H_def d_def)
      then show ?thesis
        using less_nine True target_eq by (simp add: f'_def p'_def same_def)
    next
      case False
      have unequal: "H \<noteq> ?threshold"
        using singleton less_nine False
        by (auto simp: comma_large_children_def H_def d_def Let_def)
      have atmost: "H \<le> ?threshold" using False by simp
      have target_eq: "target = ?high"
        using singleton less_nine False unequal
        by (simp add: comma_large_children_def H_def d_def Let_def)
      have "comma_sector (f + 1) p ?high"
        using comma_below_nine_next_sector_candidate[OF source less_nine exponent]
          atmost by (simp add: H_def d_def)
      then show ?thesis
        using less_nine False target_eq by (simp add: f'_def p'_def same_def)
    qed
  next
    case False
    have nine: "f = 9" using source False
      by (auto simp: comma_sector_def)
    let ?low = "k + 10 * d + 9"
    let ?high = "k + 10 * d + 1"
    show ?thesis
    proof (cases "H > 10 * d + 9")
      case True
      have target_eq: "target = ?low"
        using singleton True nine
        by (simp add: comma_large_children_def H_def d_def Let_def)
      have "comma_sector 9 p ?low"
        using comma_nine_same_sector_candidate[OF source[unfolded nine]]
          True nine by (simp add: H_def d_def)
      then show ?thesis
        using nine True target_eq by (simp add: f'_def p'_def same_def)
    next
      case False
      have low: "H \<le> 10 * d + 1"
        using singleton False nine
        by (auto simp: comma_large_children_def H_def d_def Let_def
            split: if_splits)
      have target_eq: "target = ?high"
        using singleton False nine low
        by (simp add: comma_large_children_def H_def d_def Let_def)
      have "comma_sector 1 (Suc p) ?high"
        using comma_nine_power_crossing_candidate
          [OF source[unfolded nine] exponent] low nine
        by (simp add: H_def d_def)
      then show ?thesis
        using nine False target_eq by (simp add: f'_def p'_def same_def)
    qed
  qed
qed

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_cycle_length_admitted comma_period_displacement_admitted
      comma_fixed_iter_complete_cycles comma_singleton_step_chart})
    then () else error "Comma macro refinement depends on an oracle";
\<close>

end
