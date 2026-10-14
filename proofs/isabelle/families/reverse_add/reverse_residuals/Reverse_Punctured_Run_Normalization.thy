theory Reverse_Punctured_Run_Normalization
  imports Reverse_Uniform_Runs
begin

text \<open>The Q19 punctured producer normalizes a constant-symbol run by
emitting its first digit with the incoming carry, then reusing the stable
outgoing carry for the remaining positions.  This theory proves that local
run operation and its chronological composition equal the existing literal
decimal emitter.  It does not prove the event partition or the T2 pair-field
refinement.\<close>

definition punctured_carry_value :: "bool \<Rightarrow> nat" where
  "punctured_carry_value carry = (if carry then 1 else 0)"

definition punctured_run_exit :: "nat \<Rightarrow> bool \<Rightarrow> bool" where
  "punctured_run_exit symbol incoming =
    carry_apply (domain symbol) incoming"

definition punctured_run_first_digit :: "nat \<Rightarrow> bool \<Rightarrow> nat" where
  "punctured_run_first_digit symbol incoming =
    symbol + punctured_carry_value incoming -
      10 * punctured_carry_value (punctured_run_exit symbol incoming)"

definition punctured_run_following_digit :: "nat \<Rightarrow> bool \<Rightarrow> nat" where
  "punctured_run_following_digit symbol incoming =
    symbol + punctured_carry_value (punctured_run_exit symbol incoming) -
      10 * punctured_carry_value (punctured_run_exit symbol incoming)"

definition punctured_run_emit :: "bool \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list" where
  "punctured_run_emit incoming symbol count =
    (if count = 0 then [] else
      punctured_run_first_digit symbol incoming #
        replicate (count - 1) (punctured_run_following_digit symbol incoming))"

lemma punctured_digit_normal_form:
  assumes symbol: "symbol < 19"
  shows "symbol + punctured_carry_value incoming -
      10 * punctured_carry_value (carry_apply (domain symbol) incoming) =
    (symbol + punctured_carry_value incoming) mod 10"
proof -
  have symbol_cases:
    "symbol = 0 \<or> symbol = 1 \<or> symbol = 2 \<or> symbol = 3 \<or>
     symbol = 4 \<or> symbol = 5 \<or> symbol = 6 \<or> symbol = 7 \<or>
     symbol = 8 \<or> symbol = 9 \<or> symbol = 10 \<or> symbol = 11 \<or>
     symbol = 12 \<or> symbol = 13 \<or> symbol = 14 \<or> symbol = 15 \<or>
     symbol = 16 \<or> symbol = 17 \<or> symbol = 18"
    using symbol by arith
  show ?thesis using symbol_cases
    by (elim disjE; cases incoming;
        simp add: punctured_carry_value_def domain_def)
qed

lemma emit_replicate_exact:
  "emit incoming (replicate count symbol) =
    (if count = 0 then [] else
      (symbol + punctured_carry_value incoming) mod 10 #
        replicate (count - 1)
          ((symbol + punctured_carry_value (carry_apply (domain symbol) incoming)) mod 10))"
proof (induction count arbitrary: incoming)
  case 0
  then show ?case by simp
next
  case (Suc count)
  let ?following = "carry_apply (domain symbol) incoming"
  have stable: "carry_apply (domain symbol) ?following = ?following"
    by (rule carry_domain_idempotent)
  show ?case
  proof (cases count)
    case 0
    then show ?thesis using Suc.IH[of ?following] stable
      by (simp add: punctured_carry_value_def)
  next
    case (Suc n)
    then show ?thesis using Suc.IH[of ?following] stable
      by (simp add: punctured_carry_value_def)
  qed
qed

lemma carry_out_replicate_exact:
  "carry_out incoming (replicate count symbol) =
    (if count = 0 then incoming else punctured_run_exit symbol incoming)"
proof (induction count arbitrary: incoming)
  case 0
  then show ?case by (simp add: carry_out_def)
next
  case (Suc count)
  let ?following = "punctured_run_exit symbol incoming"
  have stable: "punctured_run_exit symbol ?following = ?following"
    by (simp add: punctured_run_exit_def carry_domain_idempotent)
  show ?case using Suc.IH[of ?following] stable
    by (simp add: carry_out_def punctured_run_exit_def)
qed

theorem punctured_run_emit_refines_literal:
  assumes symbol: "symbol < 19"
  shows "punctured_run_emit incoming symbol count =
    emit incoming (replicate count symbol)"
proof (cases count)
  case 0
  then show ?thesis by (simp add: punctured_run_emit_def)
next
  case (Suc n)
  have first:
    "punctured_run_first_digit symbol incoming =
      (symbol + punctured_carry_value incoming) mod 10"
    using punctured_digit_normal_form[OF symbol, of incoming]
    by (simp add: punctured_run_first_digit_def punctured_run_exit_def)
  have outgoing:
    "punctured_run_exit symbol incoming =
      carry_apply (domain symbol) incoming"
    by (simp add: punctured_run_exit_def)
  have following:
    "punctured_run_following_digit symbol incoming =
      (symbol + punctured_carry_value (carry_apply (domain symbol) incoming)) mod 10"
  proof -
    have stable:
      "carry_apply (domain symbol) (punctured_run_exit symbol incoming) =
        punctured_run_exit symbol incoming"
      by (simp add: punctured_run_exit_def carry_domain_idempotent)
    have normalized:
      "symbol + punctured_carry_value (punctured_run_exit symbol incoming) -
          10 * punctured_carry_value
            (carry_apply (domain symbol) (punctured_run_exit symbol incoming)) =
        (symbol + punctured_carry_value (punctured_run_exit symbol incoming)) mod 10"
      using punctured_digit_normal_form[OF symbol, of "punctured_run_exit symbol incoming"] .
    show ?thesis using stable normalized
      by (simp add: punctured_run_following_digit_def punctured_run_exit_def)
  qed
  show ?thesis
    using first following
      emit_replicate_exact[of incoming count symbol]
    by (simp add: punctured_run_emit_def Suc)
qed

fun punctured_expand_runs :: "(nat \<times> nat) list \<Rightarrow> nat list" where
  "punctured_expand_runs [] = []"
| "punctured_expand_runs ((symbol,count)#runs) =
    replicate count symbol @ punctured_expand_runs runs"

definition punctured_run_emit_compact ::
  "bool \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) list" where
  "punctured_run_emit_compact incoming symbol count =
    (if count = 0 then [] else
      (punctured_run_first_digit symbol incoming, 1) #
        (if count \<le> 1 then [] else
          [(punctured_run_following_digit symbol incoming, count - 1)]))"

lemma punctured_run_emit_compact_exact:
  "punctured_expand_runs (punctured_run_emit_compact incoming symbol count) =
    punctured_run_emit incoming symbol count"
proof (cases count)
  case 0
  then show ?thesis
    by (simp add: punctured_run_emit_compact_def punctured_run_emit_def)
next
  case (Suc n)
  then show ?thesis
  proof (cases n)
    case 0
    then show ?thesis
      using Suc
      by (simp add: punctured_run_emit_compact_def punctured_run_emit_def)
  next
    case (Suc m)
    then show ?thesis
      using Suc
      by (simp add: punctured_run_emit_compact_def punctured_run_emit_def)
  qed
qed

lemma punctured_expand_runs_append:
  "punctured_expand_runs (left @ right) =
    punctured_expand_runs left @ punctured_expand_runs right"
proof (induction left)
  case Nil
  then show ?case by simp
next
  case (Cons pair left)
  obtain symbol count where pair: "pair = (symbol,count)"
    by (cases pair) auto
  show ?case using pair Cons.IH by simp
qed

fun punctured_emit_compact_runs ::
  "bool \<Rightarrow> (nat \<times> nat) list \<Rightarrow> (nat \<times> nat) list" where
  "punctured_emit_compact_runs incoming [] = []"
| "punctured_emit_compact_runs incoming ((symbol,count)#runs) =
    punctured_run_emit_compact incoming symbol count @
      punctured_emit_compact_runs
        (if count = 0 then incoming else punctured_run_exit symbol incoming) runs"

fun punctured_emit_runs :: "bool \<Rightarrow> (nat \<times> nat) list \<Rightarrow> nat list" where
  "punctured_emit_runs incoming [] = []"
| "punctured_emit_runs incoming ((symbol,count)#runs) =
    punctured_run_emit incoming symbol count @
      punctured_emit_runs
        (if count = 0 then incoming else punctured_run_exit symbol incoming) runs"

fun punctured_runs_exit :: "bool \<Rightarrow> (nat \<times> nat) list \<Rightarrow> bool" where
  "punctured_runs_exit incoming [] = incoming"
| "punctured_runs_exit incoming ((symbol,count)#runs) =
    punctured_runs_exit
      (if count = 0 then incoming else punctured_run_exit symbol incoming) runs"

lemma emit_append_exact:
  "emit incoming (first @ second) =
    emit incoming first @ emit (carry_out incoming first) second"
  by (induction first arbitrary: incoming)
    (simp_all add: carry_out_append carry_out_def)

theorem punctured_emit_runs_refines_literal:
  assumes valid: "\<forall>run\<in>set runs. fst run < 19"
  shows "punctured_emit_runs incoming runs =
    emit incoming (punctured_expand_runs runs)"
  using valid
proof (induction runs arbitrary: incoming)
  case Nil
  then show ?case by simp
next
  case (Cons run runs)
  obtain symbol count where run: "run = (symbol,count)"
    by (cases run) auto
  have symbol: "symbol < 19" using Cons.prems run by auto
  have tail_valid: "\<forall>tail\<in>set runs. fst tail < 19"
    using Cons.prems by auto
  have exit:
    "(if count = 0 then incoming else punctured_run_exit symbol incoming) =
      carry_out incoming (replicate count symbol)"
    using carry_out_replicate_exact[of incoming count symbol]
    by (cases count) simp_all
  have tail:
    "punctured_emit_runs (carry_out incoming (replicate count symbol)) runs =
      emit (carry_out incoming (replicate count symbol))
        (punctured_expand_runs runs)"
    using Cons.IH[OF tail_valid] .
  show ?case
    unfolding punctured_emit_runs.simps punctured_expand_runs.simps run
    by (simp only: punctured_run_emit_refines_literal[OF symbol] tail
        emit_append_exact exit)
qed

theorem punctured_compact_runs_decode:
  "punctured_expand_runs (punctured_emit_compact_runs incoming runs) =
    punctured_emit_runs incoming runs"
proof (induction runs arbitrary: incoming)
  case Nil
  then show ?case by simp
next
  case (Cons run runs)
  obtain symbol count where run: "run = (symbol,count)"
    by (cases run) auto
  have tail:
    "punctured_expand_runs
        (punctured_emit_compact_runs
          (if count = 0 then incoming else punctured_run_exit symbol incoming) runs) =
      punctured_emit_runs
        (if count = 0 then incoming else punctured_run_exit symbol incoming) runs"
    by (rule Cons.IH)
  show ?case
    unfolding punctured_emit_compact_runs.simps punctured_emit_runs.simps run
    by (simp only: punctured_expand_runs_append punctured_run_emit_compact_exact tail)
qed

theorem punctured_runs_exit_refines_literal:
  "punctured_runs_exit incoming runs =
    carry_out incoming (punctured_expand_runs runs)"
proof (induction runs arbitrary: incoming)
  case Nil
  then show ?case by (simp add: carry_out_def)
next
  case (Cons run runs)
  obtain symbol count where run: "run = (symbol,count)"
    by (cases run) auto
  have exit:
    "(if count = 0 then incoming else punctured_run_exit symbol incoming) =
      carry_out incoming (replicate count symbol)"
    using carry_out_replicate_exact[of incoming count symbol]
    by (cases count) simp_all
  have tail:
    "punctured_runs_exit (carry_out incoming (replicate count symbol)) runs =
      carry_out (carry_out incoming (replicate count symbol))
        (punctured_expand_runs runs)"
    using Cons.IH .
  show ?case
    unfolding punctured_runs_exit.simps punctured_expand_runs.simps run
    by (simp only: tail exit carry_out_append)
qed

corollary punctured_run_decimal_normalization:
  assumes valid: "\<forall>run\<in>set runs. fst run < 19"
  shows "punctured_emit_runs False runs @
      (if punctured_runs_exit False runs then [1] else []) =
    digits (punctured_expand_runs runs)"
  using punctured_emit_runs_refines_literal[OF valid]
    punctured_runs_exit_refines_literal[of False runs]
  by (simp add: digits_def)

corollary punctured_compact_run_decimal_normalization:
  assumes valid: "\<forall>run\<in>set runs. fst run < 19"
  shows "punctured_expand_runs (punctured_emit_compact_runs False runs) @
      (if punctured_runs_exit False runs then [1] else []) =
    digits (punctured_expand_runs runs)"
  using punctured_run_decimal_normalization[OF valid]
    punctured_compact_runs_decode[of False runs]
  by simp

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms punctured_digit_normal_form emit_replicate_exact
      carry_out_replicate_exact punctured_run_emit_refines_literal
      punctured_emit_runs_refines_literal punctured_runs_exit_refines_literal
      punctured_run_decimal_normalization punctured_run_emit_compact_exact
      punctured_compact_runs_decode punctured_compact_run_decimal_normalization})
    then () else error "Punctured decimal run normalization depends on an oracle";
\<close>

end
