theory Reverse_EQ_Clock_Transport
  imports Reverse_EQ_Phase_Guard
begin


text \<open>These observations retain the actual pair source, both ordered
carry inlets, and the physical source clock.  The temporal theorem describes
one selected interior cell at each physical generation.\<close>

definition reverse_eq_growth_observation :: "nat list \<Rightarrow> nat \<Rightarrow> nat" where
  "reverse_eq_growth_observation source i =
    reverse_eq_phase_digit (source ! i) (carry_out False (take i source)) +
    reverse_eq_phase_digit (last (take i source))
      (carry_apply (domain (source ! i))
        (carry_out False (rev (drop (Suc i) source))))"

theorem reverse_eq_growth_source_cell:
  assumes valid: "valid_pair source"
      and growth: "carry_out False source"
      and positive: "0 < i" and index: "i < length source"
  shows "step source ! i = reverse_eq_growth_observation source i"
proof -
  have admitted: "\<forall>x\<in>set source. x < 19"
    using valid by (auto simp: valid_pair_def)
  have prefix: "\<forall>x\<in>set (take i source). x < 19"
    using admitted by (meson in_set_takeD)
  have suffix: "\<forall>x\<in>set (drop (Suc i) source). x < 19"
    using admitted by (meson in_set_dropD)
  have cell: "source ! i < 19" using admitted index by simp
  have interior: "take i source \<noteq> []"
    using positive index by (cases source; cases i; auto)
  have branch:
    "carry_out
      (carry_apply (domain (source ! i)) (carry_out False (take i source)))
      (drop (Suc i) source)"
    using carry_out_split_nth[OF index, of False] growth by simp
  have scan:
    "reverse_emit (reverse_left_fold (take i source)) (source ! i)
       (reverse_right_fold (drop (Suc i) source)) = step source ! i"
    using reverse_two_port_scan_nth[of i "source @ [19]"]
      reverse_two_port_scan_growth[OF valid growth] index
    by (simp add: nth_append take_append drop_append)
  show ?thesis
    using reverse_eq_phase_source_growth_interior[OF prefix suffix cell interior branch]
      scan
    by (simp add: reverse_eq_growth_observation_def)
qed

lemma reverse_eq_growth_backward_reset:
  assumes reset: "reset < 19" "reset \<noteq> 9"
  shows "carry_out right (rev (near @ reset # far)) =
    carry_out (9 < reset) (rev near)"
proof -
  have forced:
    "carry_apply (domain reset) (carry_out right (rev far)) = (9 < reset)"
    using reverse_eq_reset_independent_carry[OF reset,
        of "carry_out right (rev far)"]
      reverse_eq_phase_carry_exact[OF reset(1),
        of "carry_out right (rev far)"] by simp
  show ?thesis using forced
    by (simp add: carry_out_append carry_out_def)
qed

theorem reverse_eq_physical_clock_observation:
  assumes valid: "valid_pair source"
      and positive: "0 < i" and index: "i < length (run step t source)"
  shows "(if carry_out False (run step t source)
     then reverse_eq_growth_observation (run step t source) i = 9
     else reverse_eq_mask False False (run step t source) ! i) =
    (step (run step t source) ! i = 9)"
proof -
  have current: "valid_pair (run step t source)"
    using valid by (rule valid_pair_run)
  show ?thesis
  proof (cases "carry_out False (run step t source)")
    case True
    show ?thesis using True
      reverse_eq_growth_source_cell[OF current True positive index] by simp
  next
    case False
    show ?thesis using False
      reverse_eq_mask_quiet_source_cell[OF current False index] by simp
  qed
qed

text \<open>The ordered observations cover successive physical clocks, even
when the width changes between observations.  Each clock supplies its own
source, index and ordered carry inlets; no inlet is transported across a
reset merely because two observations have the same EQ value.\<close>

theorem reverse_eq_physical_clock_observations:
  assumes valid: "valid_pair source"
      and positive: "0 < i"
      and indices: "\<And>k. k < n \<Longrightarrow> i < length (run step (t + k) source)"
  shows "map (\<lambda>k. if carry_out False (run step (t + k) source)
       then reverse_eq_growth_observation (run step (t + k) source) i = 9
       else reverse_eq_mask False False (run step (t + k) source) ! i) [0..<n] =
    map (\<lambda>k. step (run step (t + k) source) ! i = 9) [0..<n]"
proof (rule map_cong[OF refl])
  fix k assume "k \<in> set [0..<n]"
  then have bound: "k < n" by simp
  show "(if carry_out False (run step (t + k) source)
       then reverse_eq_growth_observation (run step (t + k) source) i = 9
       else reverse_eq_mask False False (run step (t + k) source) ! i) =
      (step (run step (t + k) source) ! i = 9)"
    by (rule reverse_eq_physical_clock_observation[OF valid positive indices[OF bound]])
qed

text \<open>A complete quiet EQ response determines the full physical pair
successor, not merely an equality of masks.  This is the physical side of
the inverse separator; a separate theorem must still connect its four-bit
grammar fold to this premise.\<close>

theorem reverse_eq_quiet_complete_endpoint:
  assumes valid: "valid_pair source"
      and quiet: "\<not> carry_out False source"
      and complete: "reverse_eq_mask False False source = replicate (length source) True"
  shows "step source = replicate (length source) 9"
proof (rule nth_equalityI)
  show "length (step source) = length (replicate (length source) 9)"
    using quiet by (simp add: length_digits_exact)
  fix i assume "i < length (step source)"
  then have bound: "i < length source"
    using quiet by (simp add: length_digits_exact)
  have "reverse_eq_mask False False source ! i"
    using complete bound by simp
  then show "step source ! i = replicate (length source) 9 ! i"
    using reverse_eq_mask_quiet_source_cell[OF valid quiet bound] bound by simp
qed


theorem reverse_eq_grammar_complete_endpoint:
  assumes valid: "valid_pair (reverse_eq_source_word source)"
      and quiet: "\<not> carry_out False (reverse_eq_source_word source)"
      and complete: "snd (snd (reverse_eq_source_action source)) False False =
        replicate (length (reverse_eq_source_word source)) True"
  shows "step (reverse_eq_source_word source) =
    replicate (length (reverse_eq_source_word source)) 9"
proof (rule reverse_eq_quiet_complete_endpoint[OF valid quiet])
  show "reverse_eq_mask False False (reverse_eq_source_word source) =
      replicate (length (reverse_eq_source_word source)) True"
    using complete reverse_eq_source_grammar_action[of source]
    by (simp add: reverse_eq_action_word_def)
qed

theorem reverse_eq_outer_seventeen_two_ticks:
  assumes valid: "valid_pair source" and outer: "hd source = 17"
  shows "carry_out False source"
    and "\<not> carry_out False (step source)"
    and "hd (step (step source)) = 16 \<or> hd (step (step source)) = 17"
proof -
  have first: "carry_out False source"
    by (rule reverse_eq_source_outer_seventeen_forces_birth[OF valid outer])
  have nonempty: "source \<noteq> []" using valid by (simp add: valid_pair_def)
  have next_valid: "valid_pair (step source)" by (rule valid_pair_successor[OF valid])
  have next_outer: "hd (step source) = 8"
    using source_growth_edge_successor[OF nonempty first] outer by simp
  have quiet: "\<not> carry_out False (step source)"
  proof
    assume growth: "carry_out False (step source)"
    have "9 \<le> hd (step source)"
      by (rule source_growth_requires_edge(1)[OF next_valid growth])
    with next_outer show False by simp
  qed
  have lower: "2 * hd (step source) \<le> hd (step (step source))"
    by (rule source_nongrowth_outer_coefficient_bounds(1)[OF next_valid quiet])
  have upper: "hd (step (step source)) \<le> 2 * hd (step source) + 1"
    by (rule source_nongrowth_outer_coefficient_bounds(2)[OF next_valid quiet])
  show "carry_out False source" by (rule first)
  show "\<not> carry_out False (step source)" by (rule quiet)
  show "hd (step (step source)) = 16 \<or> hd (step (step source)) = 17"
    using lower upper next_outer by arith
qed

fun inverse_eq_walk :: "nat list \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool" where
  "inverse_eq_walk [] a r = (a = r)"
| "inverse_eq_walk (s # xs) a r =
    (s \<in> {4, 9, 14} \<and> carry_apply (domain s) (\<not> a) = r \<and>
      inverse_eq_walk xs (carry_apply (domain s) a) (\<not> a))"

lemma inverse_eq_paired_emit:
  assumes "inverse_eq_walk xs a r"
  shows "carry_out a (xs @ rev xs) = r \<and>
    map (\<lambda>(x,y). x + y) (zip (emit a (xs @ rev xs)) (rev (emit a (xs @ rev xs)))) =
      replicate (length (xs @ rev xs)) 9"
  using assms(1)
proof (induction xs arbitrary: a r)
  case Nil
  then show ?case by (simp add: carry_out_def)
next
  case (Cons s xs)
  let ?inner = "xs @ rev xs"
  let ?left = "carry_apply (domain s) a"
  have steps: "s \<in> {4, 9, 14}" "carry_apply (domain s) (\<not> a) = r"
    "inverse_eq_walk xs ?left (\<not> a)" using Cons.prems by simp_all
  have ih: "carry_out ?left ?inner = (\<not> a) \<and>
    map (\<lambda>(x,y). x + y) (zip (emit ?left ?inner) (rev (emit ?left ?inner))) =
      replicate (length ?inner) 9"
    by (rule Cons.IH[OF steps(3)])
  have digit: "(s + (if a then 1 else 0)) mod 10 +
      (s + (if \<not> a then 1 else 0)) mod 10 = 9"
    using steps(1) by (cases a; auto)
  show ?case using steps ih digit
    by (cases a; auto simp: carry_out_append carry_out_def emit_append zip_append
        replicate_add replicate_append_same)
qed

definition inverse_eq_phase :: "bool \<Rightarrow> bool \<Rightarrow> nat" where
  "inverse_eq_phase a r = (if a then (if r then 3 else 0) else (if r then 2 else 1))"

fun inverse_eq_atom :: "nat \<Rightarrow> nat \<Rightarrow> nat option" where
  "inverse_eq_atom s phase =
    (if s = 4 \<and> phase \<in> {0,1} then Some ((phase + 1) mod 4)
     else if s = 14 \<and> phase \<in> {2,3} then Some ((phase + 1) mod 4)
     else if s = 9 \<and> phase \<in> {0,2} then Some phase else None)"

lemma inverse_eq_atom_physical:
  "inverse_eq_atom s (inverse_eq_phase a r) =
    (if s \<in> {4,9,14} \<and> carry_apply (domain s) (\<not> a) = r
     then Some (inverse_eq_phase (carry_apply (domain s) a) (\<not> a))
     else None)"
  by (cases a; cases r; auto simp: inverse_eq_phase_def domain_def)

fun inverse_eq_phase_run :: "nat list \<Rightarrow> nat \<Rightarrow> nat option" where
  "inverse_eq_phase_run [] phase = Some phase"
| "inverse_eq_phase_run (s # xs) phase =
    (case inverse_eq_atom s phase of None \<Rightarrow> None
     | Some next \<Rightarrow> inverse_eq_phase_run xs next)"

lemma inverse_eq_phase_walk:
  "inverse_eq_walk xs a r \<longleftrightarrow>
    (\<exists>phase \<in> {1,3}. inverse_eq_phase_run xs (inverse_eq_phase a r) = Some phase)"
proof (induction xs arbitrary: a r)
  case Nil
  then show ?case by (cases a; cases r; simp add: inverse_eq_phase_def)
next
  case (Cons s xs)
  then show ?case
    by (simp only: inverse_eq_walk.simps inverse_eq_phase_run.simps
        inverse_eq_atom_physical; auto split: if_splits)
qed

lemma inverse_eq_phase_run_append:
  "inverse_eq_phase_run (xs @ ys) phase =
    (case inverse_eq_phase_run xs phase of None \<Rightarrow> None
     | Some next \<Rightarrow> inverse_eq_phase_run ys next)"
  by (induction xs arbitrary: phase) (auto split: option.splits)

lemma inverse_eq_nines_emit [simp]:
  "emit False (replicate n 9) = replicate n 9"
  by (induction n) (simp_all add: domain_def)

lemma inverse_eq_nines_carry [simp]:
  "carry_out False (replicate n 9) = False"
  by (induction n) (simp_all add: carry_out_def domain_def)

theorem inverse_eq_physical_two_ticks:
  assumes "inverse_eq_walk xs False False"
  shows "step (step (xs @ rev xs)) = replicate (length (xs @ rev xs)) 18"
proof -
  have first: "step (xs @ rev xs) = replicate (length (xs @ rev xs)) 9"
    using inverse_eq_paired_emit[OF assms]
    by (simp add: step_def digits_def)
  show ?thesis
    apply (subst first)
    by (simp add: step_def digits_def)
qed

corollary inverse_eq_phase_physical_two_ticks:
  assumes "\<exists>phase \<in> {1,3}. inverse_eq_phase_run xs 1 = Some phase"
  shows "step (step (xs @ rev xs)) = replicate (length (xs @ rev xs)) 18"
proof (rule inverse_eq_physical_two_ticks)
  show "inverse_eq_walk xs False False"
    using assms inverse_eq_phase_walk[of xs False False]
    by (simp add: inverse_eq_phase_def)
qed

ML \<open>
  val checked = @{thms reverse_eq_growth_source_cell reverse_eq_growth_backward_reset
    reverse_eq_physical_clock_observation reverse_eq_physical_clock_observations
    reverse_eq_quiet_complete_endpoint reverse_eq_grammar_complete_endpoint
    reverse_eq_outer_seventeen_two_ticks inverse_eq_paired_emit
    inverse_eq_atom_physical inverse_eq_phase_walk inverse_eq_phase_run_append
    inverse_eq_physical_two_ticks inverse_eq_phase_physical_two_ticks};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Reverse EQ clock transport depends on an oracle";
  val _ = if Thm_Deps.has_skip_proof checked
    then error "Skipped reverse EQ clock transport proof" else ();
\<close>

end
