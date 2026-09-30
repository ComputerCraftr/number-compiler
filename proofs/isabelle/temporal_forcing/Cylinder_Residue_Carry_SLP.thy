theory Cylinder_Residue_Carry_SLP
  imports Cylinder_Forcing_Alphabet
begin

text \<open>
  Finite scan and composition laws for the supplied pair-residue grammar used
  by the residue carry SLP.  The word is an input to these theorems: validity
  does not authenticate a source word, prove temporal closure, or provide a
  pumping argument.
\<close>

record residue_carry_outcome =
  residue_final_carry :: nat
  residue_outgoing :: "nat list"
  residue_jumps :: "int list"

fun residue_carry_scan :: "nat list \<Rightarrow> nat \<Rightarrow> residue_carry_outcome" where
  "residue_carry_scan [] incoming =
    \<lparr>residue_final_carry = incoming,
     residue_outgoing = [], residue_jumps = []\<rparr>"
| "residue_carry_scan (pair#pairs) incoming =
    (let following = forcing_carry_step pair incoming;
         tail = residue_carry_scan pairs following
     in \<lparr>residue_final_carry = residue_final_carry tail,
          residue_outgoing = following # residue_outgoing tail,
          residue_jumps = (int following - int incoming) # residue_jumps tail\<rparr>)"

record residue_carry_summary =
  residue_low :: residue_carry_outcome
  residue_high :: residue_carry_outcome

definition residue_summary :: "nat list \<Rightarrow> residue_carry_summary" where
  "residue_summary pairs =
    \<lparr>residue_low = residue_carry_scan pairs 0,
     residue_high = residue_carry_scan pairs 1\<rparr>"

definition residue_summary_at ::
    "residue_carry_summary \<Rightarrow> nat \<Rightarrow> residue_carry_outcome" where
  "residue_summary_at summary incoming =
    (if incoming = 0 then residue_low summary else residue_high summary)"

definition residue_outcome_compose ::
    "residue_carry_outcome \<Rightarrow> residue_carry_summary \<Rightarrow>
      residue_carry_outcome" where
  "residue_outcome_compose before after =
    (let second = residue_summary_at after (residue_final_carry before)
     in \<lparr>residue_final_carry = residue_final_carry second,
          residue_outgoing = residue_outgoing before @ residue_outgoing second,
          residue_jumps = residue_jumps before @ residue_jumps second\<rparr>)"

definition residue_summary_compose ::
    "residue_carry_summary \<Rightarrow> residue_carry_summary \<Rightarrow>
      residue_carry_summary" where
  "residue_summary_compose before after =
    \<lparr>residue_low = residue_outcome_compose (residue_low before) after,
     residue_high = residue_outcome_compose (residue_high before) after\<rparr>"

lemma forcing_carry_step_bit:
  "forcing_carry_step pair incoming = 0 \<or>
    forcing_carry_step pair incoming = 1"
  by (simp add: forcing_carry_step_def split: if_splits)

lemma residue_scan_final_bit:
  assumes "incoming = 0 \<or> incoming = 1"
  shows "residue_final_carry (residue_carry_scan pairs incoming) = 0 \<or>
    residue_final_carry (residue_carry_scan pairs incoming) = 1"
  using assms
proof (induction pairs arbitrary: incoming)
  case Nil
  then show ?case by simp
next
  case (Cons pair pairs)
  have next_bit: "forcing_carry_step pair incoming = 0 \<or>
      forcing_carry_step pair incoming = 1"
    by (rule forcing_carry_step_bit)
  show ?case using Cons.IH[OF next_bit] by (simp add: Let_def)
qed

lemma residue_summary_at_scan:
  assumes "incoming = 0 \<or> incoming = 1"
  shows "residue_summary_at (residue_summary pairs) incoming =
    residue_carry_scan pairs incoming"
  using assms
  by (auto simp: residue_summary_at_def residue_summary_def)

theorem residue_scan_append:
  assumes incoming_bit: "incoming = 0 \<or> incoming = 1"
  shows "residue_carry_scan (before @ after) incoming =
    residue_outcome_compose (residue_carry_scan before incoming)
      (residue_summary after)"
  using incoming_bit
proof (induction before arbitrary: incoming)
  case Nil
  then show ?case
    by (cases "incoming = 0")
       (simp_all add: residue_outcome_compose_def residue_summary_at_def
          residue_summary_def Let_def)
next
  case (Cons pair before)
  let ?following = "forcing_carry_step pair incoming"
  have bit: "?following = 0 \<or> ?following = 1"
    by (rule forcing_carry_step_bit)
  show ?case
    using Cons.IH[OF bit] bit
    by (auto simp: residue_outcome_compose_def residue_summary_at_scan Let_def)
qed

theorem residue_summary_append:
  "residue_summary (before @ after) =
    residue_summary_compose (residue_summary before) (residue_summary after)"
  by (cases "residue_summary before"; cases "residue_summary after")
     (simp add: residue_summary_def residue_summary_compose_def
        residue_scan_append residue_outcome_compose_def)

lemma residue_summary_compose_at:
  assumes "incoming = 0 \<or> incoming = 1"
  shows "residue_summary_at (residue_summary_compose before after) incoming =
    residue_outcome_compose (residue_summary_at before incoming) after"
  using assms
  by (auto simp: residue_summary_at_def residue_summary_compose_def)

theorem residue_summary_compose_associative:
  "residue_summary_compose (residue_summary_compose first second) third =
    residue_summary_compose first (residue_summary_compose second third)"
proof (cases first; cases second; cases third)
  show ?thesis
    by (simp add: residue_summary_compose_def residue_outcome_compose_def
        residue_summary_at_def Let_def split: if_splits)
qed

lemma residue_scan_lengths:
  "length (residue_outgoing (residue_carry_scan pairs incoming)) = length pairs \<and>
   length (residue_jumps (residue_carry_scan pairs incoming)) = length pairs"
  by (induction pairs arbitrary: incoming) (simp_all add: Let_def)

theorem residue_interior_jumps_telescope:
  "sum_list (residue_jumps (residue_carry_scan pairs incoming)) =
    int (residue_final_carry (residue_carry_scan pairs incoming)) - int incoming"
proof (induction pairs arbitrary: incoming)
  case Nil
  then show ?case by simp
next
  case (Cons pair pairs)
  show ?case using Cons.IH[of "forcing_carry_step pair incoming"]
    by (simp add: Let_def)
qed

definition residue_closed_jumps :: "nat list \<Rightarrow> nat \<Rightarrow> int list" where
  "residue_closed_jumps pairs incoming =
    residue_jumps (residue_carry_scan pairs incoming) @
      [- int (residue_final_carry (residue_carry_scan pairs incoming))]"

theorem residue_closed_jumps_balance:
  "sum_list (residue_closed_jumps pairs incoming) = - int incoming"
  using residue_interior_jumps_telescope[of pairs incoming]
  by (simp add: residue_closed_jumps_def)

fun residue_closed_difference :: "nat \<Rightarrow> nat list \<Rightarrow> int list" where
  "residue_closed_difference incoming [] = [- int incoming]"
| "residue_closed_difference incoming (outgoing#rest) =
    (int outgoing - int incoming) # residue_closed_difference outgoing rest"

theorem residue_closed_jumps_exact:
  "residue_closed_jumps pairs incoming =
    residue_closed_difference incoming
      (residue_outgoing (residue_carry_scan pairs incoming))"
proof (induction pairs arbitrary: incoming)
  case Nil
  then show ?case by (simp add: residue_closed_jumps_def)
next
  case (Cons pair pairs)
  let ?following = "forcing_carry_step pair incoming"
  show ?case
    using Cons.IH[of ?following]
    by (simp add: residue_closed_jumps_def Let_def)
qed

corollary residue_empty_high_closed_boundary:
  "residue_closed_jumps [] 1 = [-1] \<and>
    sum_list (residue_closed_jumps [] 1) = -1"
  by (simp add: residue_closed_jumps_def)

fun residue_repeat_word :: "nat list \<Rightarrow> nat \<Rightarrow> nat list" where
  "residue_repeat_word pairs 0 = []"
| "residue_repeat_word pairs (Suc count) =
    residue_repeat_word pairs count @ pairs"

definition residue_identity_summary :: residue_carry_summary where
  "residue_identity_summary = residue_summary []"

fun residue_summary_power :: "residue_carry_summary \<Rightarrow> nat \<Rightarrow>
    residue_carry_summary" where
  "residue_summary_power summary 0 = residue_identity_summary"
| "residue_summary_power summary (Suc count) =
    residue_summary_compose (residue_summary_power summary count) summary"

theorem residue_summary_repeat:
  "residue_summary (residue_repeat_word pairs count) =
    residue_summary_power (residue_summary pairs) count"
  by (induction count)
     (simp_all add: residue_identity_summary_def residue_summary_append)

lemma residue_repeat_word_add:
  "residue_repeat_word pairs (left+right) =
    residue_repeat_word pairs left @ residue_repeat_word pairs right"
  by (induction right) simp_all

theorem residue_summary_power_add:
  "residue_summary_power (residue_summary pairs) (left+right) =
    residue_summary_compose
      (residue_summary_power (residue_summary pairs) left)
      (residue_summary_power (residue_summary pairs) right)"
  by (simp only: residue_summary_repeat[symmetric] residue_repeat_word_add
      residue_summary_append)

corollary residue_summary_power_double:
  "residue_summary_power (residue_summary pairs) (2*count) =
    residue_summary_compose
      (residue_summary_power (residue_summary pairs) count)
      (residue_summary_power (residue_summary pairs) count)"
proof -
  have twice: "2*count = count+count" by arith
  show ?thesis unfolding twice by (rule residue_summary_power_add)
qed

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
      @{thms residue_scan_append residue_summary_append
        residue_summary_compose_associative residue_interior_jumps_telescope
        residue_closed_jumps_balance residue_closed_jumps_exact
        residue_empty_high_closed_boundary
        residue_summary_repeat residue_summary_power_add
        residue_summary_power_double})
    then () else error "Residue carry SLP laws depend on an oracle";
\<close>

end
