theory Double_Reverse_Periodic_Ring_Action
  imports Double_Reverse_Temporal_Refinement
begin

theorem double_reverse_T_run_source_root_square:
  "double_reverse_T_run (first + second) source =
    double_reverse_T_run second (double_reverse_T_run first source)"
proof -
  have exponent: "first + second = second + first"
    by (simp add: add.commute)
  show ?thesis
    unfolding double_reverse_T_run_def
    by (simp only: exponent funpow_add comp_apply)
qed

corollary double_reverse_T_run_actual_midpoint_square:
  "double_reverse_T_run (2 * steps) source =
    double_reverse_T_run steps (double_reverse_T_run steps source)"
proof -
  have "2 * steps = steps + steps" by simp
  then show ?thesis by (simp only: double_reverse_T_run_source_root_square)
qed

text \<open>The NC15 periodic-core executor applies the exact T-squared local
digit law to a finite cyclic word after an external source certificate proves
that the demanded causal cones stay inside a periodic interior.  This theory
formalizes that finite action and its temporal powering.  A cycle premise is
an explicit certificate input: the finite ring itself does not prove that an
arbitrary integer source has a periodic interior or an indefinitely recurring
finite-source boundary.\<close>

definition double_reverse_ring_digit :: "nat list \<Rightarrow> nat \<Rightarrow> nat" where
  "double_reverse_ring_digit word i = word ! (i mod length word)"

definition double_reverse_ring_step :: "nat list \<Rightarrow> nat list" where
  "double_reverse_ring_step word =
    map (\<lambda>i. double_reverse_t2_digit
      (double_reverse_ring_digit word (i + length word - 1))
      (double_reverse_ring_digit word i)
      (double_reverse_ring_digit word (i + 1))) [0..<length word]"

lemma double_reverse_ring_step_length:
  "length (double_reverse_ring_step word) = length word"
  by (simp add: double_reverse_ring_step_def)

lemma double_reverse_ring_step_cell:
  assumes "i < length word"
  shows "double_reverse_ring_step word ! i =
    double_reverse_t2_digit
      (double_reverse_ring_digit word (i + length word - 1))
      (double_reverse_ring_digit word i)
      (double_reverse_ring_digit word (i + 1))"
  using assms
  by (simp add: double_reverse_ring_step_def double_reverse_ring_digit_def)

lemma double_reverse_ring_step_digits:
  assumes "i < length word"
  shows "double_reverse_ring_step word ! i < 10"
  using double_reverse_ring_step_cell[OF assms]
  by (simp add: double_reverse_t2_digit_def)

lemma double_reverse_open_right_carry_is_five_residue:
  assumes digits: "center < 10" "right < 10"
  shows "(if (2*right + threshold5_digit center) mod 10 \<ge> 5
      then (1::nat) else 0) =
    (if right mod 5 = 3 \<or> right mod 5 = 4 then 1 else 0) +
    (if 5 \<le> center \<and> right mod 5 = 2 then 1 else 0)"
  using digits
  by (cases "center < 5";
      simp add: threshold5_digit_def; presburger)

text \<open>This cell law is the open-stencil bridge: the three decimal digits
are supplied by an externally admitted causal halo, and the proof converts the
two-pass carry expression to the radix-five selector used by the Moore bank.
It has no cyclic-neighbor, repeated-input, or infinite-source premise.\<close>

theorem double_reverse_t2_open_stencil_exact:
  assumes digits: "left < 10" "center < 10" "right < 10"
  shows "double_reverse_t2_digit left center right =
    (4*center + 2*(if 5 \<le> left then 1 else 0) +
      (if right mod 5 = 3 \<or> right mod 5 = 4 then 1 else 0) +
      (if 5 \<le> center \<and> right mod 5 = 2 then 1 else 0)) mod 10"
proof -
  have carry:
    "(if (2*right + threshold5_digit center) mod 10 \<ge> 5
        then (1::nat) else 0) =
      (if right mod 5 = 3 \<or> right mod 5 = 4 then 1 else 0) +
      (if 5 \<le> center \<and> right mod 5 = 2 then 1 else 0)"
    by (rule double_reverse_open_right_carry_is_five_residue[OF digits(2,3)])
  show ?thesis
    using carry
    by (simp add: double_reverse_t2_digit_def threshold5_digit_def)
qed

text \<open>The production open bank consumes a finite, source-issued pair of
exterior digits at every time step.  This fold keeps those inlets explicit;
invalid ports refuse rather than being wrapped around a finite ring or
defaulted to zero.\<close>

definition double_reverse_open_inputs_valid :: "(nat \<times> nat) list \<Rightarrow> bool" where
  "double_reverse_open_inputs_valid inputs \<longleftrightarrow>
    list_all (\<lambda>ports. fst ports < 10 \<and> snd ports < 10) inputs"

fun double_reverse_open_stencil_trace :: "nat \<Rightarrow> (nat \<times> nat) list \<Rightarrow> nat" where
  "double_reverse_open_stencil_trace center [] = center"
| "double_reverse_open_stencil_trace center ((left,right)#inputs) =
    double_reverse_open_stencil_trace
      (double_reverse_t2_digit left center right) inputs"

fun double_reverse_open_stencil_guarded ::
    "nat \<Rightarrow> (nat \<times> nat) list \<Rightarrow> nat option" where
  "double_reverse_open_stencil_guarded center [] =
    (if center < 10 then Some center else None)"
| "double_reverse_open_stencil_guarded center ((left,right)#inputs) =
    (if center < 10 \<and> left < 10 \<and> right < 10
     then double_reverse_open_stencil_guarded
       (double_reverse_t2_digit left center right) inputs
     else None)"

lemma double_reverse_t2_output_bounded:
  "double_reverse_t2_digit left center right < 10"
  by (simp add: double_reverse_t2_digit_def)

theorem double_reverse_open_stencil_trace_append:
  "double_reverse_open_stencil_trace center (prefix @ suffix) =
    double_reverse_open_stencil_trace
      (double_reverse_open_stencil_trace center prefix) suffix"
proof (induction prefix arbitrary: center)
  case Nil
  then show ?case by simp
next
  case (Cons ports prefix)
  obtain left right where ports: "ports = (left,right)" by (cases ports) auto
  show ?case
    using Cons.IH[of "double_reverse_t2_digit left center right"]
    by (simp add: ports)
qed

theorem double_reverse_open_stencil_guarded_exact:
  "double_reverse_open_stencil_guarded center inputs =
    (if center < 10 \<and> double_reverse_open_inputs_valid inputs
     then Some (double_reverse_open_stencil_trace center inputs) else None)"
proof (induction inputs arbitrary: center)
  case Nil
  then show ?case by (simp add: double_reverse_open_inputs_valid_def)
next
  case (Cons ports inputs)
  obtain left right where ports: "ports = (left,right)" by (cases ports) auto
  have bounded: "double_reverse_t2_digit left center right < 10"
    by (rule double_reverse_t2_output_bounded)
  show ?case
    using Cons.IH[of "double_reverse_t2_digit left center right"] bounded
    by (cases "center < 10"; cases "left < 10"; cases "right < 10";
        simp add: ports double_reverse_open_inputs_valid_def)
qed

definition double_reverse_ring_run :: "nat \<Rightarrow> nat list \<Rightarrow> nat list" where
  "double_reverse_ring_run steps word =
    (double_reverse_ring_step ^^ steps) word"

lemma double_reverse_ring_run_add:
  "double_reverse_ring_run (first + second) word =
    double_reverse_ring_run second (double_reverse_ring_run first word)"
proof -
  have exponent: "first + second = second + first"
    by (simp add: add.commute)
  show ?thesis
    unfolding double_reverse_ring_run_def
    by (simp only: exponent funpow_add comp_apply)
qed

definition double_reverse_ring_cycle :: "nat \<Rightarrow> nat list \<Rightarrow> bool" where
  "double_reverse_ring_cycle period word \<longleftrightarrow>
    0 < period \<and> double_reverse_ring_run period word = word"

theorem double_reverse_ring_cycle_repeats:
  assumes cycle: "double_reverse_ring_cycle period word"
  shows "double_reverse_ring_run (period * count) word = word"
proof (induction count)
  case 0
  then show ?case by (simp add: double_reverse_ring_run_def)
next
  case (Suc count)
  have cycle_step: "double_reverse_ring_run period word = word"
    using cycle by (simp add: double_reverse_ring_cycle_def)
  have arithmetic: "period * Suc count = period * count + period"
    by (simp add: algebra_simps)
  show ?case
    using Suc.IH cycle_step
    by (simp only: arithmetic double_reverse_ring_run_add Suc.IH cycle_step)
qed

theorem double_reverse_ring_cycle_future_periodic:
  assumes cycle: "double_reverse_ring_cycle period word"
  shows "double_reverse_ring_run (time + period) word =
    double_reverse_ring_run time word"
proof -
  have state_cycle: "double_reverse_ring_run period word = word"
    using cycle by (simp add: double_reverse_ring_cycle_def)
  have reindex: "time + period = period + time" by (simp add: add.commute)
  have cyclic:
    "double_reverse_ring_run (period + time) word =
      double_reverse_ring_run time
        (double_reverse_ring_run period word)"
    by (rule double_reverse_ring_run_add)
  have final_state:
    "double_reverse_ring_run time
        (double_reverse_ring_run period word) =
      double_reverse_ring_run time word"
    using state_cycle by simp
  show ?thesis
    by (subst reindex; simp only: cyclic final_state)
qed

corollary double_reverse_ring_observation_periodic:
  assumes cycle: "double_reverse_ring_cycle period word"
      and coordinate: "i < length word"
  shows "double_reverse_ring_run (time + period) word ! i =
    double_reverse_ring_run time word ! i"
  using double_reverse_ring_cycle_future_periodic[OF cycle, of time]
  by simp

text \<open>Thus a certified ring cycle is a complete future quotient for the
ring's emitted digit word, and any projection of that word inherits the same
powered action.  Connecting a finite source interval to this ring remains a
separate causal-halo refinement obligation; the ring-period theorem alone is
not authority to publish digits outside that certified interval.\<close>

ML \<open>
  val checked = @{thms double_reverse_ring_step_length
    double_reverse_T_run_source_root_square
    double_reverse_T_run_actual_midpoint_square
    double_reverse_ring_step_cell double_reverse_ring_step_digits
    double_reverse_open_right_carry_is_five_residue
    double_reverse_t2_open_stencil_exact double_reverse_t2_output_bounded
    double_reverse_open_stencil_trace_append
    double_reverse_open_stencil_guarded_exact
    double_reverse_ring_run_add double_reverse_ring_cycle_repeats
    double_reverse_ring_cycle_future_periodic
    double_reverse_ring_observation_periodic};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Double-reverse periodic ring action depends on an oracle";
\<close>

end
