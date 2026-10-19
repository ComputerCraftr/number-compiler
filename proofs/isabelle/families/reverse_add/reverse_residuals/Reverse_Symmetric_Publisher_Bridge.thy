theory Reverse_Symmetric_Publisher_Bridge
  imports Reverse_Symmetric_Transfer Reverse_196_Publisher_Refinement
begin

text \<open>
The production Q19 row builder receives the current pair sum q, a carry from
the low side, and a correlated transfer for the deeper symmetric region. Its
middle witness is checked as K_q o F o K_q on both carry inputs. This bridge
connects that checked decomposition to the exact no-growth and growth pair
emission laws and to the terminal carry of the emitted upper border word.
It does not assert that a finite port word repeats on future sources.
\<close>

fun reverse_q19_upper_scan :: "nat list \<Rightarrow> bool \<Rightarrow>
    nat list \<times> bool" where
  "reverse_q19_upper_scan [] incoming = ([],incoming)"
| "reverse_q19_upper_scan (pair_sum # pair_sums) incoming =
    (let (digits,terminal) = reverse_q19_upper_scan pair_sums
        (carry_apply (domain pair_sum) incoming)
     in ((pair_sum + carry_bit incoming) mod 10 # digits,terminal))"

definition reverse_q19_upper_source :: "nat list \<Rightarrow> bool \<Rightarrow> nat list" where
  "reverse_q19_upper_source pair_sums incoming =
    rev (fst (reverse_q19_upper_scan (rev pair_sums) incoming))"

definition reverse_q19_emitted_pair ::
    "nat \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow>
      nat \<times> nat" where
  "reverse_q19_emitted_pair q previous_pair growth low_carry reflected_carry =
    ((q + carry_bit low_carry) mod 10,
      if growth then
        (previous_pair + carry_bit
          (carry_apply (domain q) reflected_carry)) mod 10
      else (q + carry_bit reflected_carry) mod 10)"

lemma reverse_q19_reflected_transfer_exact:
  assumes transfer:
    "\<And>incoming. transfer incoming =
      carry_apply (domain q)
        (deeper (carry_apply (domain q) incoming))"
  shows "reverse_reflected_carry_pair q deeper low_carry =
    (deeper (carry_apply (domain q) low_carry), transfer low_carry)"
  using transfer
  by (simp add: reverse_reflected_carry_pair_components)

text \<open>The production transfer validator compares both Boolean inputs.
Since a carry action has domain @{typ bool}, extensional equality below is
exactly that two-input validation, not equality on a sample carry.\<close>

lemma reverse_q19_transfer_extensional:
  assumes both_inputs:
    "transfer False = carry_apply (domain q) (deeper (carry_apply (domain q) False))"
    "transfer True = carry_apply (domain q) (deeper (carry_apply (domain q) True))"
  shows "\<And>incoming. transfer incoming =
      carry_apply (domain q)
        (deeper (carry_apply (domain q) incoming))"
proof -
  fix incoming
  show "transfer incoming = carry_apply (domain q)
      (deeper (carry_apply (domain q) incoming))"
    using both_inputs by (cases incoming) simp_all
qed

lemma reverse_q19_emitted_pair_sum:
  "fst (reverse_q19_emitted_pair q previous_pair growth low_carry reflected_carry) +
      snd (reverse_q19_emitted_pair q previous_pair growth low_carry reflected_carry) =
    (if growth then
      growth_pair_step q previous_pair (carry_bit low_carry)
        (carry_bit (carry_apply (domain q) reflected_carry))
     else mirror_pair_step q (carry_bit low_carry)
        (carry_bit reflected_carry))"
  by (cases growth)
    (simp_all add: reverse_q19_emitted_pair_def growth_pair_step_def
      mirror_pair_step_def carry_bit_def)

lemma reverse_q19_upper_scan_is_emission_and_carry:
  "reverse_q19_upper_scan pair_sums incoming =
    (emit incoming pair_sums, carry_out incoming pair_sums)"
proof (induction pair_sums arbitrary: incoming)
  case Nil
  have carry_empty: "carry_out incoming [] = incoming"
    unfolding carry_out_def by (simp only: fold_Nil id_apply)
  show ?case using carry_empty by simp
next
  case (Cons pair_sum pair_sums)
  show ?case
    using Cons.IH[of "carry_apply (domain pair_sum) incoming"]
    by (simp add: carry_apply_decimal_threshold
        carry_bit_def carry_out_def)
qed

theorem reverse_q19_upper_loop_emits_source_and_terminal_growth:
  "reverse_q19_upper_scan (rev pair_sums) incoming =
      (emit incoming (rev pair_sums),
        carry_out incoming (rev pair_sums))"
  by (rule reverse_q19_upper_scan_is_emission_and_carry)

lemma reverse_q19_upper_source_length:
  "length (reverse_q19_upper_source pair_sums incoming) = length pair_sums"
  using reverse_q19_upper_loop_emits_source_and_terminal_growth
  by (simp add: reverse_q19_upper_source_def)

lemma reverse_q19_upper_source_last:
  assumes nonempty: "pair_sums \<noteq> []"
  shows "last (reverse_q19_upper_source pair_sums incoming) =
    (last pair_sums + carry_bit incoming) mod 10"
proof -
  have scan:
    "reverse_q19_upper_scan (rev pair_sums) incoming =
      (emit incoming (rev pair_sums), carry_out incoming (rev pair_sums))"
    by (rule reverse_q19_upper_loop_emits_source_and_terminal_growth)
  have reverse_nonempty: "rev pair_sums \<noteq> []"
    using nonempty by simp
  then obtain first rest where reverse: "rev pair_sums = first # rest"
    by (cases "rev pair_sums") auto
  have first_is_hd: "first = hd (rev pair_sums)"
    using reverse by simp
  have hd_is_last: "hd (rev pair_sums) = last pair_sums"
    by (rule hd_rev)
  have first_is_last: "first = last pair_sums"
    using first_is_hd hd_is_last by simp
  have emission_nonempty: "emit incoming (rev pair_sums) \<noteq> []"
    using reverse by simp
  have emission_first:
    "hd (emit incoming (rev pair_sums)) =
      (last pair_sums + carry_bit incoming) mod 10"
  proof -
    have "hd (emit incoming (rev pair_sums)) =
        (first + carry_bit incoming) mod 10"
      using reverse by (simp add: emit.simps carry_bit_def)
    also have "... = (last pair_sums + carry_bit incoming) mod 10"
      using first_is_last by simp
    finally show ?thesis .
  qed
  have source_is_reverse_emission:
    "reverse_q19_upper_source pair_sums incoming =
      rev (emit incoming (rev pair_sums))"
    unfolding reverse_q19_upper_source_def using scan by simp
  have last_reverse_emission:
    "last (rev (emit incoming (rev pair_sums))) =
      hd (emit incoming (rev pair_sums))"
    by (rule last_rev)
  show ?thesis
    using source_is_reverse_emission last_reverse_emission emission_first
    by simp
qed

theorem reverse_q19_emitted_growth_pair_matches_upper_source:
  assumes nonempty: "pair_sums \<noteq> []"
      and previous: "previous_pair = last pair_sums"
  shows "snd (reverse_q19_emitted_pair q previous_pair True low_carry reflected_carry) =
    last (reverse_q19_upper_source pair_sums
      (carry_apply (domain q) reflected_carry))"
proof -
  have upper_last:
    "last (reverse_q19_upper_source pair_sums
        (carry_apply (domain q) reflected_carry)) =
      (last pair_sums + carry_bit
        (carry_apply (domain q) reflected_carry)) mod 10"
    by (rule reverse_q19_upper_source_last[OF nonempty])
  show ?thesis using previous upper_last
    by (simp add: reverse_q19_emitted_pair_def)
qed

lemma reverse_q19_upper_loop_terminal_growth:
  "snd (reverse_q19_upper_scan (rev pair_sums) incoming) =
    carry_out incoming (rev pair_sums)"
  using reverse_q19_upper_loop_emits_source_and_terminal_growth by simp

text \<open>The list-level model follows the right-to-left carry recurrence used
by `_candidate_pairs`. Its scan theorem relates that modeled word and final
carry to the abstract `emit` and `carry_out` definitions. This is a semantic
correspondence for the recurrence, not a code-extraction theorem or a claim
that a finite port word can be repeated on future sources.\<close>

ML \<open>
  val checked = @{thms reverse_q19_reflected_transfer_exact
    reverse_q19_transfer_extensional reverse_q19_emitted_pair_sum
    reverse_q19_upper_source_length reverse_q19_upper_source_last
    reverse_q19_emitted_growth_pair_matches_upper_source
    reverse_q19_upper_scan_is_emission_and_carry
    reverse_q19_upper_loop_emits_source_and_terminal_growth
    reverse_q19_upper_loop_terminal_growth};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Reverse Q19 symmetric publisher bridge depends on an oracle";
  val _ = if Thm_Deps.has_skip_proof checked
    then error "Skipped Reverse Q19 symmetric publisher bridge proof" else ();
\<close>

end
