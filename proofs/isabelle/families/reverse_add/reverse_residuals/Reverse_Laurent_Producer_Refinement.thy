theory Reverse_Laurent_Producer_Refinement
  imports Reverse_Laurent_Source_Refinement Reverse_Punctured_Run_Pairing
begin

text \<open>This bridge proves one source-bound pair-field tick by mirroring and
normalizing the half tape, pairing emitted digits, and decoding the next field.
It assumes no endpoint equality; different run partitions agree because
normalization and pairing depend only on the exact expanded word.\<close>

definition reverse_laurent_drop_last_run_symbol ::
    "punctured_runs \<Rightarrow> punctured_runs" where
  "reverse_laurent_drop_last_run_symbol runs =
    rev (punctured_run_advance 1 (rev runs))"

definition reverse_laurent_full_runs ::
    "punctured_runs \<Rightarrow> bool \<Rightarrow> punctured_runs" where
  "reverse_laurent_full_runs half is_odd =
    half @ rev (if is_odd then
      reverse_laurent_drop_last_run_symbol half else half)"

fun reverse_laurent_switches_from ::
    "nat \<Rightarrow> bool \<Rightarrow> punctured_runs \<Rightarrow> nat list" where
  "reverse_laurent_switches_from position incoming [] = []"
| "reverse_laurent_switches_from position incoming ((symbol,run_length)#runs) =
    (let following =
        (if run_length = 0 then incoming else punctured_run_exit symbol incoming)
     in (if following = incoming then [] else [Suc position]) @
       reverse_laurent_switches_from (position + run_length) following runs)"

definition reverse_laurent_switches :: "punctured_runs \<Rightarrow> nat list" where
  "reverse_laurent_switches runs =
    reverse_laurent_switches_from 0 False runs"

fun reverse_laurent_carry_trace :: "bool \<Rightarrow> punctured_runs \<Rightarrow> bool list" where
  "reverse_laurent_carry_trace incoming [] = []"
| "reverse_laurent_carry_trace incoming ((symbol,run_length)#runs) =
    (let following =
        (if run_length = 0 then incoming
         else punctured_run_exit symbol incoming)
     in replicate run_length following @
       reverse_laurent_carry_trace following runs)"

lemma reverse_laurent_radix19_carries_append:
  "radix19_carries (left @ right) incoming =
    radix19_carries left incoming @
      radix19_carries right (radix19_final_carry left incoming)"
  by (induction left arbitrary: incoming) simp_all

lemma reverse_laurent_radix19_carries_replicate:
  fixes count :: nat
  shows "radix19_carries (replicate count symbol) incoming =
    replicate count (punctured_run_exit symbol incoming)"
  by (induction count arbitrary: incoming)
    (simp_all add: punctured_run_exit_def carry_domain_idempotent)

lemma reverse_laurent_radix19_final_replicate:
  fixes count :: nat
  shows "radix19_final_carry (replicate count symbol) incoming =
    (if count = 0 then incoming else punctured_run_exit symbol incoming)"
  by (induction count arbitrary: incoming)
    (simp_all add: punctured_run_exit_def carry_domain_idempotent)

lemma reverse_laurent_carry_trace_refines_radix19:
  "reverse_laurent_carry_trace incoming runs =
    radix19_carries (punctured_expand_runs runs) incoming"
proof (induction runs arbitrary: incoming)
  case Nil
  then show ?case by simp
next
  case (Cons run runs)
  obtain symbol run_length where run: "run = (symbol,run_length)"
    by (cases run) auto
  let ?following =
    "(if run_length = 0 then incoming else
      punctured_run_exit symbol incoming)"
  have run_carries:
    "radix19_carries (replicate run_length symbol) incoming =
      replicate run_length ?following"
  proof -
    have exact_run:
      "radix19_carries (replicate run_length symbol) incoming =
        replicate run_length (punctured_run_exit symbol incoming)"
      by (rule reverse_laurent_radix19_carries_replicate)
    show ?thesis
    proof (cases run_length)
      case 0
      then show ?thesis using exact_run by simp
    next
      case (Suc count)
      have following:
        "?following = punctured_run_exit symbol incoming"
        using Suc by simp
      show ?thesis using exact_run following by simp
    qed
  qed
  have run_exit:
    "radix19_final_carry (replicate run_length symbol) incoming =
      ?following"
  proof -
    have exact_exit:
      "radix19_final_carry (replicate run_length symbol) incoming =
        (if run_length = 0 then incoming else punctured_run_exit symbol incoming)"
      by (rule reverse_laurent_radix19_final_replicate)
    show ?thesis using exact_exit by simp
  qed
  have tail:
    "reverse_laurent_carry_trace ?following runs =
      radix19_carries (punctured_expand_runs runs) ?following"
    by (rule Cons.IH)
  show ?case using run_carries run_exit tail
    by (simp add: run reverse_laurent_radix19_carries_append Let_def)
qed

lemma reverse_laurent_radix19_final_matches_carry_out:
  "radix19_final_carry symbols incoming = carry_out incoming symbols"
  by (induction symbols arbitrary: incoming)
     (simp_all add: carry_out_def)

lemma reverse_laurent_radix19_carries_last:
  assumes nonempty: "symbols \<noteq> []"
  shows "last (radix19_carries symbols incoming) =
    radix19_final_carry symbols incoming"
  using nonempty
proof (induction symbols arbitrary: incoming)
  case Nil
  then show ?case by simp
next
  case (Cons symbol symbols)
  let ?next = "carry_apply (domain symbol) incoming"
  show ?case using Cons.IH[of ?next]
    by (cases symbols) simp_all
qed

definition reverse_laurent_internal_carry_mask :: "nat list \<Rightarrow> nat" where
  "reverse_laurent_internal_carry_mask symbols =
    decimal_list_value (rev (map carry_bit
      (butlast (radix19_carries symbols False))))"

lemma reverse_laurent_internal_mask_snoc:
  "reverse_laurent_internal_carry_mask (symbols @ [symbol]) =
    carry_bit (carry_out False symbols) +
      10 * reverse_laurent_internal_carry_mask symbols"
proof (cases symbols)
  case Nil
  then show ?thesis
    by (simp add: reverse_laurent_internal_carry_mask_def
        reverse_laurent_radix19_final_matches_carry_out
        carry_out_def carry_bit_def)
next
  case (Cons first rest)
  have nonempty: "symbols \<noteq> []" using Cons by simp
  have last_carry:
    "last (radix19_carries symbols False) = carry_out False symbols"
    using reverse_laurent_radix19_carries_last[OF nonempty]
    by (simp add: reverse_laurent_radix19_final_matches_carry_out)
  have trace_nonempty: "radix19_carries symbols False \<noteq> []"
    using Cons by (cases symbols) simp_all
  have prefix_split:
    "radix19_carries symbols False =
      butlast (radix19_carries symbols False) @
        [carry_out False symbols]"
  proof -
    have split:
      "radix19_carries symbols False =
        butlast (radix19_carries symbols False) @
          [last (radix19_carries symbols False)]"
      by (rule sym, rule append_butlast_last_id[OF trace_nonempty])
    have terminal:
      "[last (radix19_carries symbols False)] =
        [carry_out False symbols]"
      using last_carry by simp
    show ?thesis using split terminal by simp
  qed
  have appended_trace:
    "radix19_carries (symbols @ [symbol]) False =
      radix19_carries symbols False @
        [carry_out False (symbols @ [symbol])]"
    by (simp add: reverse_laurent_radix19_carries_append
        reverse_laurent_radix19_final_matches_carry_out
        carry_out_append carry_out_def)
  have new_internal:
    "reverse_laurent_internal_carry_mask (symbols @ [symbol]) =
      decimal_list_value
        (rev (map carry_bit (radix19_carries symbols False)))"
    using appended_trace trace_nonempty
    by (simp add: reverse_laurent_internal_carry_mask_def)
  have old_split:
    "map carry_bit (radix19_carries symbols False) =
      map carry_bit (butlast (radix19_carries symbols False)) @
        [carry_bit (carry_out False symbols)]"
  proof -
    have mapped:
      "map carry_bit (radix19_carries symbols False) =
        map carry_bit
          (butlast (radix19_carries symbols False) @
            [carry_out False symbols])"
      by (rule arg_cong[OF prefix_split, where f="map carry_bit"])
    show ?thesis using mapped
      by (simp only: map_append list.map)
  qed
  have old_value:
    "decimal_list_value
        (rev (map carry_bit (radix19_carries symbols False))) =
      carry_bit (carry_out False symbols) +
        10 * reverse_laurent_internal_carry_mask symbols"
    using old_split
    by (simp add: reverse_laurent_internal_carry_mask_def
        decimal_list_value.simps)
  show ?thesis
    using new_internal old_value by simp
qed

lemma reverse_laurent_emitted_reverse_value_snoc:
  "decimal_list_value (rev (emit False (symbols @ [symbol]))) =
    (symbol + carry_bit (carry_out False symbols)) mod 10 +
      10 * decimal_list_value (rev (emit False symbols))"
  by (simp add: emit_append carry_out_def carry_bit_def)

lemma reverse_laurent_raw_reverse_value_snoc:
  "decimal_list_value (rev (symbols @ [symbol])) =
    symbol + 10 * decimal_list_value (rev symbols)"
  by simp

theorem reverse_laurent_reflected_carry_defect:
  assumes bounded: "\<forall>symbol\<in>set symbols. symbol \<le> 18"
  shows "int (decimal_list_value (rev symbols)) -
      int (decimal_list_value (rev (emit False symbols))) =
    99 * int (reverse_laurent_internal_carry_mask symbols) +
      10 * int (carry_bit (carry_out False symbols))"
proof -
  have recurrence:
    "(\<forall>item\<in>set symbols. item \<le> 18) \<longrightarrow>
      int (decimal_list_value (rev symbols)) -
        int (decimal_list_value (rev (emit False symbols))) =
      99 * int (reverse_laurent_internal_carry_mask symbols) +
        10 * int (carry_bit (carry_out False symbols))"
  proof (induction symbols rule: rev_induct)
    case Nil
    then show ?case
      by (simp add: reverse_laurent_internal_carry_mask_def
          carry_bit_def carry_out_def)
  next
    case (snoc symbol symbols)
    show ?case
    proof
      assume all_bounded: "\<forall>item\<in>set (symbols @ [symbol]). item \<le> 18"
      have symbol_bound: "symbol \<le> 18"
        using all_bounded by auto
      have prefix_bound: "\<forall>item\<in>set symbols. item \<le> 18"
        using all_bounded by auto
      have prefix:
        "int (decimal_list_value (rev symbols)) -
            int (decimal_list_value (rev (emit False symbols))) =
          99 * int (reverse_laurent_internal_carry_mask symbols) +
            10 * int (carry_bit (carry_out False symbols))"
        by (rule mp[OF snoc.IH prefix_bound])
      let ?incoming = "carry_out False symbols"
      let ?following = "carry_apply (domain symbol) ?incoming"
      have digit_balance:
        "int symbol + int (carry_bit ?incoming) =
          int ((symbol + carry_bit ?incoming) mod 10) +
            10 * int (carry_bit ?following)"
      proof -
        have balance:
          "(symbol + carry_bit ?incoming) mod 10 +
            10 * carry_bit ?following =
          symbol + carry_bit ?incoming"
          using carry_digit_balance[OF symbol_bound, of ?incoming]
          by (simp add: carry_bit_def)
        show ?thesis using balance by simp
      qed
      have carry_step:
        "carry_out False (symbols @ [symbol]) = ?following"
        by (simp add: carry_out_append carry_out_def)
      have mask_step:
        "reverse_laurent_internal_carry_mask (symbols @ [symbol]) =
          carry_bit ?incoming +
            10 * reverse_laurent_internal_carry_mask symbols"
        by (simp add: reverse_laurent_internal_mask_snoc)
      have raw_step:
        "decimal_list_value (rev (symbols @ [symbol])) =
          symbol + 10 * decimal_list_value (rev symbols)"
        by (rule reverse_laurent_raw_reverse_value_snoc)
      have emitted_step:
        "decimal_list_value (rev (emit False (symbols @ [symbol]))) =
          (symbol + carry_bit ?incoming) mod 10 +
            10 * decimal_list_value (rev (emit False symbols))"
        by (rule reverse_laurent_emitted_reverse_value_snoc)
      show "int (decimal_list_value (rev (symbols @ [symbol]))) -
          int (decimal_list_value (rev (emit False (symbols @ [symbol])))) =
        99 * int (reverse_laurent_internal_carry_mask (symbols @ [symbol])) +
          10 * int (carry_bit (carry_out False (symbols @ [symbol])))"
        using prefix digit_balance carry_step mask_step raw_step emitted_step
        by (simp add: algebra_simps)
    qed
  qed
  show ?thesis by (rule mp[OF recurrence bounded])
qed

theorem reverse_laurent_aligned_carry_defect:
  assumes valid: "valid_pair symbols"
  shows "int (reverse_add_pair_term symbols) -
      int (reverse_add_pair_reverse symbols div
        10^(carry_bit (carry_out False symbols))) =
    99 * int (reverse_laurent_internal_carry_mask symbols) +
      10 * int (carry_bit (carry_out False symbols))"
proof -
  have bounded: "\<forall>symbol\<in>set symbols. symbol \<le> 18"
    using valid by (auto simp: valid_pair_def)
  have symmetric: "rev symbols = symbols"
    using valid by (simp add: valid_pair_def)
  have term_value:
    "reverse_add_pair_term symbols =
      decimal_list_value (rev symbols)"
  proof -
    have preserved:
      "decimal_list_value (digits symbols) =
        decimal_list_value symbols"
      by (rule digits_preserve_decimal_value[OF bounded])
    show ?thesis using preserved symmetric
      by (simp add: reverse_add_pair_term_def)
  qed
  have reverse_cut:
    "reverse_add_pair_reverse symbols div
        10^(carry_bit (carry_out False symbols)) =
      decimal_list_value (rev (emit False symbols))"
  proof (cases "carry_out False symbols")
    case False
    then show ?thesis
      by (simp add: reverse_add_pair_reverse_def digits_def
          carry_bit_def carry_out_def)
  next
    case True
    have reverse_value:
      "reverse_add_pair_reverse symbols =
        1 + 10 * decimal_list_value (rev (emit False symbols))"
      using True
      by (simp add: reverse_add_pair_reverse_def digits_def
          carry_bit_def carry_out_def)
    show ?thesis
      using reverse_value True
      by (simp add: div_add1_eq mult.commute carry_bit_def carry_out_def)
  qed
  have defect:
    "int (decimal_list_value (rev symbols)) -
      int (decimal_list_value (rev (emit False symbols))) =
      99 * int (reverse_laurent_internal_carry_mask symbols) +
        10 * int (carry_bit (carry_out False symbols))"
    by (rule reverse_laurent_reflected_carry_defect[OF bounded])
  show ?thesis using term_value reverse_cut defect by simp
qed

corollary reverse_laurent_aligned_carry_defect_mod:
  assumes valid: "valid_pair symbols"
  shows "(int (reverse_add_pair_term symbols) -
      int (reverse_add_pair_reverse symbols div
        10^(carry_bit (carry_out False symbols)))) mod
      (99::int) =
    (10 * int (carry_bit (carry_out False symbols))) mod 99"
proof -
  have exact_defect: "int (reverse_add_pair_term symbols) -
      int (reverse_add_pair_reverse symbols div
        10^(carry_bit (carry_out False symbols))) =
      99 * int (reverse_laurent_internal_carry_mask symbols) +
        10 * int (carry_bit (carry_out False symbols))"
    by (rule reverse_laurent_aligned_carry_defect[OF valid])
  show ?thesis using exact_defect by simp
qed

fun reverse_laurent_switch_trace :: "nat \<Rightarrow> bool \<Rightarrow> bool list \<Rightarrow> nat list" where
  "reverse_laurent_switch_trace position incoming [] = []"
| "reverse_laurent_switch_trace position incoming (following#trace) =
    (if following = incoming then [] else [Suc position]) @
      reverse_laurent_switch_trace (Suc position) following trace"

definition reverse_laurent_switch_trace_exit :: "bool \<Rightarrow> bool list \<Rightarrow> bool" where
  "reverse_laurent_switch_trace_exit incoming trace =
    foldl (\<lambda>_ following. following) incoming trace"

lemma reverse_laurent_switch_trace_exit_replicate:
  fixes count :: nat
  shows "reverse_laurent_switch_trace_exit incoming
      (replicate count following) =
    (if count = 0 then incoming else following)"
  by (induction count arbitrary: incoming)
     (simp_all add: reverse_laurent_switch_trace_exit_def)

fun reverse_laurent_replay_switch_word ::
    "nat \<Rightarrow> bool \<Rightarrow> nat list \<Rightarrow> bool list" where
  "reverse_laurent_replay_switch_word 0 incoming switches = []"
| "reverse_laurent_replay_switch_word (Suc width) incoming [] =
    incoming # reverse_laurent_replay_switch_word width incoming []"
| "reverse_laurent_replay_switch_word (Suc width) incoming
      (position#switches) =
    (if position = 1 then (\<not> incoming) #
        reverse_laurent_replay_switch_word width (\<not> incoming)
          (map (\<lambda>switch. switch - 1) switches)
     else incoming #
        reverse_laurent_replay_switch_word width incoming
          (map (\<lambda>switch. switch - 1) (position#switches)))"

definition reverse_laurent_switch_internal_mask ::
    "nat \<Rightarrow> nat list \<Rightarrow> nat" where
  "reverse_laurent_switch_internal_mask width switches =
    decimal_list_value (rev (map carry_bit
      (butlast (reverse_laurent_replay_switch_word width False switches))))"


lemma reverse_laurent_carry_trace_length:
  "length (reverse_laurent_carry_trace incoming runs) =
    punctured_run_width runs"
  by (induction runs arbitrary: incoming)
     (auto simp: punctured_run_width_def Let_def split: prod.splits)

lemma reverse_laurent_switch_trace_append:
  "reverse_laurent_switch_trace position incoming (left @ right) =
    reverse_laurent_switch_trace position incoming left @
      reverse_laurent_switch_trace (position + length left)
        (reverse_laurent_switch_trace_exit incoming left) right"
proof (induction left arbitrary: position incoming)
  case Nil
  then show ?case by (simp add: reverse_laurent_switch_trace_exit_def)
next
  case (Cons following left)
  have exit_head:
    "reverse_laurent_switch_trace_exit incoming (following # left) =
      reverse_laurent_switch_trace_exit following left"
    by (simp add: reverse_laurent_switch_trace_exit_def)
  show ?case using Cons.IH[of "Suc position" following] exit_head
    by (cases "following = incoming") (simp_all add: add.commute)
qed

lemma reverse_laurent_switch_trace_replicate:
  fixes count :: nat
  shows "reverse_laurent_switch_trace position incoming (replicate count following) =
    (if count = 0 \<or> incoming = following then [] else [Suc position])"
proof (induction count arbitrary: position incoming)
  case 0
  then show ?case by simp
next
  case (Suc count)
  show ?case
  proof (cases "incoming = following")
    case True
    then show ?thesis using Suc.IH[of "Suc position" following]
      by simp
  next
    case False
    have stable:
      "reverse_laurent_switch_trace (Suc position) following
          (replicate count following) = []"
      using Suc.IH[of "Suc position" following] by simp
    show ?thesis using False stable by simp
  qed
qed

lemma reverse_laurent_switch_trace_shift:
  "reverse_laurent_switch_trace (Suc position) incoming trace =
    map Suc (reverse_laurent_switch_trace position incoming trace)"
  by (induction trace arbitrary: position incoming)
     (simp_all add: add_Suc)

lemma reverse_laurent_switch_trace_positions_above:
  "position < switch"
  if "switch \<in> set (reverse_laurent_switch_trace position incoming trace)"
  using that
proof (induction trace arbitrary: position incoming switch)
  case Nil
  then show ?case by simp
next
  case (Cons following trace)
  show ?case
  proof (cases "following = incoming")
    case True
    have member:
      "switch \<in> set (reverse_laurent_switch_trace (Suc position)
        following trace)"
      using Cons.prems True by simp
    have "Suc position < switch"
      using Cons.IH[where position="Suc position" and incoming=following
          and switch=switch] member .
    then show ?thesis
      by simp
  next
    case False
    have member_or:
      "switch = Suc position \<or>
        switch \<in> set (reverse_laurent_switch_trace (Suc position)
          following trace)"
      using Cons.prems False by simp
    then show ?thesis
    proof
      assume "switch = Suc position"
      then show ?thesis by simp
    next
      assume member:
        "switch \<in> set (reverse_laurent_switch_trace (Suc position)
          following trace)"
      have "Suc position < switch"
        using Cons.IH[where position="Suc position" and incoming=following
            and switch=switch] member .
      then show ?thesis by simp
    qed
  qed
qed

lemma reverse_laurent_replay_switch_trace_exact:
  "reverse_laurent_replay_switch_word (length trace) incoming
      (reverse_laurent_switch_trace 0 incoming trace) = trace"
proof (induction trace arbitrary: incoming)
  case Nil
  then show ?case by simp
next
  case (Cons following trace)
  have shifted:
    "reverse_laurent_switch_trace 1 following trace =
      map Suc (reverse_laurent_switch_trace 0 following trace)"
    using reverse_laurent_switch_trace_shift[where position=0] by simp
  have replay_tail:
    "reverse_laurent_replay_switch_word (length trace) following
        (reverse_laurent_switch_trace 0 following trace) = trace"
    by (rule Cons.IH)
  show ?case
  proof (cases "following = incoming")
    case True
    have switches:
      "reverse_laurent_switch_trace 0 incoming (following # trace) =
        map Suc (reverse_laurent_switch_trace 0 following trace)"
      using True shifted by simp
    show ?thesis
    proof (cases "reverse_laurent_switch_trace 0 following trace")
      case Nil
      then show ?thesis using switches True replay_tail
        by simp
    next
      case (Cons first rest)
      have tail_word:
        "reverse_laurent_switch_trace 0 following trace = first # rest"
        using Cons by simp
      have positive:
        "0 < first"
        using reverse_laurent_switch_trace_positions_above[where position=0
            and incoming=following and trace=trace and switch=first]
          Cons by simp
      have tail:
        "reverse_laurent_replay_switch_word (length trace) following
            (first # rest) = trace"
        using replay_tail Cons by simp
      have unshifted_tail:
        "map (\<lambda>switch. switch - 1) (map Suc rest) = rest"
        by (simp add: comp_def)
      show ?thesis using switches True tail_word positive tail unshifted_tail
        by simp
    qed
  next
    case False
    have following_state: "following = (\<not> incoming)"
      using False by (cases incoming; cases following; simp_all)
    have switches:
      "reverse_laurent_switch_trace 0 incoming (following # trace) =
        1 # map Suc (reverse_laurent_switch_trace 0 following trace)"
      using False following_state shifted by simp
    show ?thesis
    proof (cases "reverse_laurent_switch_trace 0 following trace")
      case Nil
      then show ?thesis using switches False following_state replay_tail
        by simp
    next
      case (Cons first rest)
      have tail_word:
        "reverse_laurent_switch_trace 0 following trace = first # rest"
        using Cons by simp
      have positive:
        "0 < first"
        using reverse_laurent_switch_trace_positions_above[where position=0
            and incoming=following and trace=trace and switch=first]
          Cons by simp
      have tail:
        "reverse_laurent_replay_switch_word (length trace) following
            (first # rest) = trace"
        using replay_tail Cons by simp
      have unshifted_tail:
        "map (\<lambda>switch. switch - 1) (map Suc rest) = rest"
        by (simp add: comp_def)
      show ?thesis using switches False following_state tail_word positive
          tail unshifted_tail
        by simp
    qed
  qed
qed

lemma reverse_laurent_switches_are_trace_changes:
  "reverse_laurent_switches_from position incoming runs =
    reverse_laurent_switch_trace position incoming
      (reverse_laurent_carry_trace incoming runs)"
proof (induction runs arbitrary: position incoming)
  case Nil
  then show ?case by simp
next
  case (Cons run runs)
  obtain symbol run_length where run: "run = (symbol,run_length)"
    by (cases run) auto
  show ?case
  proof (cases run_length)
    case 0
    then show ?thesis using Cons.IH[of position incoming]
      by (simp add: run Let_def)
  next
    case (Suc count)
    let ?following = "punctured_run_exit symbol incoming"
    have first:
      "reverse_laurent_switch_trace position incoming
          (replicate run_length ?following) =
        (if ?following = incoming then [] else [Suc position])"
      using reverse_laurent_switch_trace_replicate[of position incoming
          run_length ?following] Suc by simp
    have tail:
      "reverse_laurent_switches_from (position + run_length) ?following runs =
        reverse_laurent_switch_trace (position + run_length) ?following
          (reverse_laurent_carry_trace ?following runs)"
      by (rule Cons.IH)
    have run_exit:
      "reverse_laurent_switch_trace_exit incoming
          (replicate run_length ?following) = ?following"
      using reverse_laurent_switch_trace_exit_replicate[where count=run_length
          and incoming=incoming and following="?following"] Suc by simp
    have appended:
      "reverse_laurent_switch_trace position incoming
          (replicate run_length ?following @
            reverse_laurent_carry_trace ?following runs) =
        reverse_laurent_switch_trace position incoming
            (replicate run_length ?following) @
          reverse_laurent_switch_trace (position + run_length) ?following
            (reverse_laurent_carry_trace ?following runs)"
      using reverse_laurent_switch_trace_append[where position=position
          and incoming=incoming and left="replicate run_length ?following"
          and right="reverse_laurent_carry_trace ?following runs"]
        run_exit by simp
    show ?thesis using first tail appended Suc
      by (simp add: run Let_def)
  qed
qed

theorem reverse_laurent_switches_are_canonical_carry_trace:
  "reverse_laurent_switches runs =
    reverse_laurent_switch_trace 0 False
      (reverse_laurent_carry_trace False runs)"
  by (simp add: reverse_laurent_switches_def
      reverse_laurent_switches_are_trace_changes)

theorem reverse_laurent_switches_are_radix19_carry_changes:
  "reverse_laurent_switches runs =
    reverse_laurent_switch_trace 0 False
      (radix19_carries (punctured_expand_runs runs) False)"
  using reverse_laurent_switches_are_canonical_carry_trace
    reverse_laurent_carry_trace_refines_radix19 by simp

theorem reverse_laurent_switch_fold_recovers_internal_mask:
  "reverse_laurent_switch_internal_mask (punctured_run_width runs)
      (reverse_laurent_switches runs) =
    reverse_laurent_internal_carry_mask (punctured_expand_runs runs)"
proof -
  have trace_length:
    "punctured_run_width runs =
      length (reverse_laurent_carry_trace False runs)"
    by (rule reverse_laurent_carry_trace_length[symmetric])
  have trace_switches:
    "reverse_laurent_switches runs =
      reverse_laurent_switch_trace 0 False
        (reverse_laurent_carry_trace False runs)"
    by (rule reverse_laurent_switches_are_canonical_carry_trace)
  have replay:
    "reverse_laurent_replay_switch_word
        (punctured_run_width runs) False
        (reverse_laurent_switches runs) =
      reverse_laurent_carry_trace False runs"
    using reverse_laurent_replay_switch_trace_exact[of
        "reverse_laurent_carry_trace False runs" False]
      trace_length trace_switches
    by simp
  have literal_trace:
    "radix19_carries (punctured_expand_runs runs) False =
      reverse_laurent_carry_trace False runs"
    by (rule reverse_laurent_carry_trace_refines_radix19[symmetric])
  show ?thesis
    unfolding reverse_laurent_switch_internal_mask_def
      reverse_laurent_internal_carry_mask_def
    using replay literal_trace by simp
qed

lemma reverse_laurent_python_carry_branch:
  assumes symbol: "symbol \<le> 18"
  shows "punctured_run_exit symbol incoming =
    (if symbol = 9 then incoming else 10 \<le> symbol)"
  using symbol
  by (cases incoming; auto simp: punctured_run_exit_def domain_def)

lemma reverse_laurent_advance_preserves_symbols:
  "set (map fst (punctured_run_advance 1 runs)) \<subseteq>
    set (map fst runs)"
proof (cases runs)
  case Nil
  then show ?thesis by simp
next
  case (Cons run rest)
  obtain symbol run_length where run: "run = (symbol,run_length)"
    by (cases run) auto
  show ?thesis using Cons run
    by (cases run_length) (auto simp: punctured_run_advance.simps)
qed

lemma reverse_laurent_drop_last_expansion:
  assumes nonempty: "runs \<noteq> []"
      and positive: "punctured_positive_runs runs"
  shows "punctured_expand_runs
      (reverse_laurent_drop_last_run_symbol runs) =
    butlast (punctured_expand_runs runs)"
proof -
  have reverse_positive: "punctured_positive_runs (rev runs)"
    using positive by (simp add: punctured_positive_runs_def)
  have reverse_nonempty: "rev runs \<noteq> []"
    using nonempty by simp
  obtain run rest where reverse_runs: "rev runs = run # rest"
    using reverse_nonempty by (cases "rev runs") auto
  obtain symbol run_length where run: "run = (symbol,run_length)"
    by (cases run) auto
  have count_positive: "0 < run_length"
    using reverse_positive reverse_runs run
    by (auto simp: punctured_positive_runs_def)
  have one_le_count: "1 \<le> run_length"
    using count_positive by simp
  have advance_cell:
    "punctured_expand_runs (punctured_run_advance 1 ((symbol,run_length)#rest)) =
      drop 1 (punctured_expand_runs ((symbol,run_length)#rest))"
  proof -
    have advanced:
      "punctured_expand_runs (punctured_run_advance 1
          ((symbol,run_length)#rest)) =
        drop 1 (replicate run_length symbol @
          punctured_expand_runs rest)"
      by (rule punctured_advance_expansion[OF count_positive one_le_count])
    show ?thesis using advanced by simp
  qed
  have advance:
    "punctured_expand_runs (punctured_run_advance 1 (rev runs)) =
      drop 1 (punctured_expand_runs (rev runs))"
    using advance_cell reverse_runs run by simp
  show ?thesis
    using advance
    by (simp add: reverse_laurent_drop_last_run_symbol_def
        punctured_expand_rev_runs rev_drop butlast_conv_take)
qed

lemma reverse_laurent_full_runs_expand:
  assumes nonempty: "half \<noteq> []"
      and positive: "punctured_positive_runs half"
  shows "punctured_expand_runs
      (reverse_laurent_full_runs half is_odd) =
    punctured_q19_decode_half (punctured_expand_runs half) is_odd"
proof (cases is_odd)
  case False
  then show ?thesis
    by (simp add: reverse_laurent_full_runs_def
        punctured_expand_runs_append punctured_expand_rev_runs
        punctured_q19_decode_half_def)
next
  case True
  have tail:
    "punctured_expand_runs
        (reverse_laurent_drop_last_run_symbol half) =
      butlast (punctured_expand_runs half)"
    by (rule reverse_laurent_drop_last_expansion[OF nonempty positive])
  show ?thesis using True tail
    by (simp add: reverse_laurent_full_runs_def
        punctured_expand_runs_append punctured_expand_rev_runs
        punctured_q19_decode_half_def)
qed

lemma reverse_laurent_drop_last_positive:
  assumes nonempty: "runs \<noteq> []"
      and positive: "punctured_positive_runs runs"
  shows "punctured_positive_runs
      (reverse_laurent_drop_last_run_symbol runs)"
proof -
  have reverse_positive: "punctured_positive_runs (rev runs)"
    using positive by (simp add: punctured_positive_runs_def)
  have reverse_nonempty: "rev runs \<noteq> []"
    using nonempty by simp
  obtain run rest where reverse_runs: "rev runs = run # rest"
    using reverse_nonempty by (cases "rev runs") auto
  obtain symbol run_length where run: "run = (symbol,run_length)"
    by (cases run) auto
  have count_positive: "0 < run_length"
    using reverse_positive reverse_runs run
    by (auto simp: punctured_positive_runs_def)
  have one_le_count: "1 \<le> run_length"
    using count_positive by simp
  have reverse_head_positive:
    "punctured_positive_runs ((symbol,run_length)#rest)"
    using reverse_positive reverse_runs run by simp
  have advanced_head_positive:
    "punctured_positive_runs
      (punctured_run_advance 1 ((symbol,run_length)#rest))"
    by (rule punctured_advance_positive
        [OF reverse_head_positive one_le_count])
  have advanced_positive:
    "punctured_positive_runs (punctured_run_advance 1 (rev runs))"
    using advanced_head_positive reverse_runs run by simp
  show ?thesis using advanced_positive
    by (simp add: reverse_laurent_drop_last_run_symbol_def
        punctured_positive_runs_def)
qed

lemma reverse_laurent_full_runs_positive:
  assumes nonempty: "half \<noteq> []"
      and positive: "punctured_positive_runs half"
  shows "punctured_positive_runs
      (reverse_laurent_full_runs half is_odd)"
proof (cases is_odd)
  case False
  then show ?thesis using positive
    by (auto simp: reverse_laurent_full_runs_def
        punctured_positive_runs_def)
next
  case True
  have tail:
    "punctured_positive_runs
        (reverse_laurent_drop_last_run_symbol half)"
    by (rule reverse_laurent_drop_last_positive[OF nonempty positive])
  show ?thesis using positive tail True
    by (auto simp: reverse_laurent_full_runs_def
        punctured_positive_runs_def)
qed

lemma reverse_laurent_full_runs_symbols_bounded:
  assumes bounded: "\<forall>run\<in>set half. fst run < 19"
  shows "\<forall>run\<in>set
      (reverse_laurent_full_runs half is_odd). fst run < 19"
proof -
  have drop_symbols:
    "set (map fst (reverse_laurent_drop_last_run_symbol half)) \<subseteq>
      set (map fst half)"
    unfolding reverse_laurent_drop_last_run_symbol_def
    using reverse_laurent_advance_preserves_symbols[of "rev half"]
    by (simp add: rev_map)
  have bounded_symbols: "\<forall>symbol\<in>set (map fst half). symbol < 19"
    using bounded by auto
  have drop_bounded:
    "\<forall>symbol\<in>set (map fst
        (reverse_laurent_drop_last_run_symbol half)). symbol < 19"
    using drop_symbols bounded_symbols by blast
  show ?thesis using bounded drop_bounded
    by (auto simp: reverse_laurent_full_runs_def)
qed

lemma reverse_laurent_switches_from_parity:
  "odd (length (reverse_laurent_switches_from position incoming runs)) =
    (punctured_runs_exit incoming runs \<noteq> incoming)"
proof (induction runs arbitrary: position incoming)
  case Nil
  then show ?case by simp
next
  case (Cons run runs)
  obtain symbol run_length where run: "run = (symbol,run_length)"
    by (cases run) auto
  show ?case unfolding run
    by (cases run_length; cases incoming;
        cases "punctured_run_exit symbol incoming";
        simp_all add: Let_def Cons.IH)
qed

lemma reverse_laurent_switches_give_terminal_carry:
  "odd (length (reverse_laurent_switches runs)) =
    carry_out False (punctured_expand_runs runs)"
proof -
  have parity:
    "odd (length (reverse_laurent_switches_from 0 False runs)) =
      (punctured_runs_exit False runs \<noteq> False)"
    by (rule reverse_laurent_switches_from_parity)
  have exit:
    "punctured_runs_exit False runs =
      carry_out False (punctured_expand_runs runs)"
    by (rule punctured_runs_exit_refines_literal)
  show ?thesis using parity exit
    by (simp add: reverse_laurent_switches_def)
qed

theorem reverse_laurent_half_tape_tick_refines_step:
  fixes half :: punctured_runs and is_odd :: bool
    and source :: "nat list"
    and source_runs normalized_runs target_half_runs :: punctured_runs
  assumes half_nonempty: "half \<noteq> []"
      and half_positive: "punctured_positive_runs half"
      and half_bounded: "\<forall>run\<in>set half. fst run \<le> 18"
  defines "source \<equiv>
      punctured_q19_decode_half (punctured_expand_runs half) is_odd"
      and "source_runs \<equiv> reverse_laurent_full_runs half is_odd"
      and "normalized_runs \<equiv> punctured_decimal_runs source_runs"
      and "target_half_runs \<equiv>
        punctured_pair_mirror_half normalized_runs"
  shows "punctured_q19_decode_half
      (punctured_expand_runs target_half_runs)
      (punctured_run_width normalized_runs mod 2 = 1) = step source"
proof -
  have source_runs_exact:
    "punctured_expand_runs source_runs = source"
    unfolding source_def source_runs_def
    by (rule reverse_laurent_full_runs_expand[OF half_nonempty half_positive])
  have half_strict: "\<forall>run\<in>set half. fst run < 19"
    using half_bounded by (auto; arith)
  have source_runs_bounded: "\<forall>run\<in>set source_runs. fst run < 19"
    unfolding source_runs_def
    by (rule reverse_laurent_full_runs_symbols_bounded[OF half_strict])
  have normalized_expansion:
    "punctured_expand_runs normalized_runs = digits source"
    using punctured_decimal_runs_expansion[OF source_runs_bounded]
    by (simp only: normalized_runs_def source_runs_exact)
  have normalized_positive: "punctured_positive_runs normalized_runs"
    unfolding normalized_runs_def
    by (rule punctured_decimal_runs_positive)
  have normalized_width:
    "punctured_run_width normalized_runs = length (digits source)"
    using punctured_run_width_exact[of normalized_runs]
      normalized_expansion by simp
  have target_half_expansion:
    "punctured_expand_runs target_half_runs =
      take ((length (digits source) + 1) div 2) (step source)"
  proof -
    have paired:
      "map punctured_pair_sum
          (zip (punctured_expand_runs normalized_runs)
            (rev (punctured_expand_runs normalized_runs))) =
        step source"
      using normalized_expansion
      by (auto simp: step_def punctured_pair_sum_def split: prod.splits)
    show ?thesis
      unfolding target_half_runs_def
      using punctured_pair_mirror_half_expansion[OF normalized_positive]
        paired normalized_width
      by simp
  qed
  have source_step_symmetric: "rev (step source) = step source"
    by (rule step_symmetric)
  have normalized_step_length: "length (digits source) = length (step source)"
    by (simp add: length_step_exact)
  have target_half_exact:
    "punctured_expand_runs target_half_runs =
      take ((length (step source) + 1) div 2) (step source)"
    using target_half_expansion by (simp only: normalized_step_length)
  have reconstructed:
    "punctured_q19_decode_half
      (take ((length (step source) + 1) div 2) (step source))
      (length (step source) mod 2 = 1) = step source"
    by (rule punctured_q19_decode_half_reconstructs[OF source_step_symmetric])
  have phase:
    "(punctured_run_width normalized_runs mod 2 = 1) =
      (length (step source) mod 2 = 1)"
    by (simp only: normalized_width normalized_step_length)
  show ?thesis by (simp only: target_half_exact phase reconstructed)
qed

ML \<open>
  val checked = @{thms reverse_laurent_drop_last_expansion
    reverse_laurent_full_runs_expand reverse_laurent_full_runs_positive
    reverse_laurent_full_runs_symbols_bounded
    reverse_laurent_python_carry_branch
    reverse_laurent_carry_trace_length
    reverse_laurent_radix19_carries_append
    reverse_laurent_radix19_carries_replicate
    reverse_laurent_radix19_final_replicate
    reverse_laurent_carry_trace_refines_radix19
    reverse_laurent_radix19_final_matches_carry_out
    reverse_laurent_radix19_carries_last
    reverse_laurent_internal_mask_snoc
    reverse_laurent_emitted_reverse_value_snoc
    reverse_laurent_raw_reverse_value_snoc
    reverse_laurent_reflected_carry_defect
    reverse_laurent_aligned_carry_defect
    reverse_laurent_aligned_carry_defect_mod
    reverse_laurent_switch_trace_append
    reverse_laurent_switch_trace_replicate
    reverse_laurent_switch_trace_shift
    reverse_laurent_switch_trace_positions_above
    reverse_laurent_replay_switch_trace_exact
    reverse_laurent_switches_are_trace_changes
    reverse_laurent_switches_are_canonical_carry_trace
    reverse_laurent_switches_are_radix19_carry_changes
    reverse_laurent_switch_fold_recovers_internal_mask
    reverse_laurent_switches_from_parity
    reverse_laurent_switches_give_terminal_carry
    reverse_laurent_half_tape_tick_refines_step
    punctured_compact_run_decimal_normalization
    punctured_pair_mirror_half_expansion};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Reverse Laurent producer refinement depends on an oracle";
\<close>

end
