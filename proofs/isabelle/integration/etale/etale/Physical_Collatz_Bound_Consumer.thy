theory Physical_Collatz_Bound_Consumer
  imports Skew_Cylinder_Observers
begin

text \<open>
  This theory checks the finite output consumer compiled by
  sequences/collatz/physical_output_quotient.py.  A left state is one of the
  six states of CollatzPhysicalBlockEffect, a source and right symbol are in
  the padded binary alphabet {0,1,2}, and 2 is blank.  The runtime's original
  source binding remains outside this local finite table and is not modeled by
  an invented identifier in this theory.
\<close>

definition collatz_current :: "nat \<Rightarrow> nat" where
  "collatz_current symbol = (if symbol = 2 then 0 else symbol)"

definition collatz_previous :: "nat \<Rightarrow> nat" where
  "collatz_previous left = (left - 2) div 2"

definition collatz_carry :: "nat \<Rightarrow> nat" where
  "collatz_carry left = (left - 2) mod 2"

text \<open>
  This is the arithmetic specification of
  CollatzPhysicalBlockEffect.output_consumer.  True selects the adjacent
  higher source symbol.  False publishes the accompanying local value.
\<close>

definition physical_output_consumer :: "nat \<Rightarrow> nat \<Rightarrow> bool \<times> nat" where
  "physical_output_consumer left symbol =
    (if left = 0 then
       (if symbol = 2 then (False, 2)
        else if symbol = 0 then (True, 0)
        else (False, (symbol + 1) mod 2))
     else if left = 1 then (True, 0)
     else
       (let total = collatz_current symbol + collatz_previous left + collatz_carry left
        in if symbol = 2 \<and> total = 0 then (False, 2)
           else (False, total mod 2)))"

definition physical_emit :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "physical_emit left symbol right =
    (let consumer = physical_output_consumer left symbol
     in if fst consumer then right else snd consumer)"

text \<open>
  These are the two tuples compiled by collatz_physical_leaf_output: one tuple
  tells select whether to read the right port, and the other is its local
  branch.  They are written out here rather than defined through the consumer,
  so the refinement theorem checks the production table rather than unfolding
  a restatement of it.
\<close>

definition compiled_uses_right :: "nat \<Rightarrow> bool list" where
  "compiled_uses_right symbol =
    (if symbol = 0 then [True, True, False, False, False, False]
     else if symbol = 1 then [False, True, False, False, False, False]
     else [False, True, False, False, False, False])"

definition compiled_local_output :: "nat \<Rightarrow> nat list" where
  "compiled_local_output symbol =
    (if symbol = 0 then [0, 0, 0, 1, 1, 0]
     else if symbol = 1 then [0, 0, 1, 0, 0, 1]
     else [2, 0, 2, 1, 1, 0])"

definition compiled_physical_publisher :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "compiled_physical_publisher symbol left right =
    (if compiled_uses_right symbol ! left then right
     else compiled_local_output symbol ! left)"

lemma less_six_cases:
  fixes n :: nat
  assumes "n < 6"
  shows "n = 0 \<or> n = 1 \<or> n = 2 \<or> n = 3 \<or> n = 4 \<or> n = 5"
  using assms by arith

lemma odd_state_cases:
  fixes n :: nat
  assumes "2 \<le> n" "n < 6"
  shows "n = 2 \<or> n = 3 \<or> n = 4 \<or> n = 5"
  using assms by arith

lemma less_three_cases:
  fixes n :: nat
  assumes "n < 3"
  shows "n = 0 \<or> n = 1 \<or> n = 2"
  using assms by arith

lemma less_two_cases:
  fixes n :: nat
  assumes "n < 2"
  shows "n = 0 \<or> n = 1"
  using assms by arith

text \<open>
  Exact left-boundary transition of CollatzPhysicalBlockEffect.advance.  State
  0 is START, state 1 is EVEN, and states 2--5 encode (previous, carry).
\<close>

definition physical_left_advance :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "physical_left_advance left symbol =
    (if left = 0 then
       (if symbol = 2 then 0 else if symbol = 0 then 1 else 5)
     else if left = 1 then 1
     else
       (let current = collatz_current symbol;
            total = current + collatz_previous left + collatz_carry left
        in 2 + 2 * current + total div 2))"

lemma physical_left_advance_closed:
  assumes "left < 6" "symbol < 3"
  shows "physical_left_advance left symbol < 6"
  using less_six_cases[OF assms(1)] less_three_cases[OF assms(2)]
  by (elim disjE)
     (simp_all add: physical_left_advance_def collatz_current_def
       collatz_previous_def collatz_carry_def)

lemma physical_left_advance_leaves_start:
  assumes "0 < left" "left < 6" "symbol < 3"
  shows "0 < physical_left_advance left symbol"
  using less_six_cases[OF assms(2)] less_three_cases[OF assms(3)] assms(1)
  by (elim disjE)
     (simp_all add: physical_left_advance_def collatz_current_def
       collatz_previous_def collatz_carry_def)

definition physical_odd_event :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "physical_odd_event left symbol = (if left = 0 \<and> symbol = 1 then 1 else 0)"

fun physical_scan_events :: "nat \<Rightarrow> nat list \<Rightarrow> nat" where
  "physical_scan_events left [] = 0"
| "physical_scan_events left (symbol # symbols) =
    physical_odd_event left symbol +
      physical_scan_events (physical_left_advance left symbol) symbols"

lemma physical_scan_events_after_start:
  assumes "0 < left" "left < 6" "\<forall>symbol \<in> set symbols. symbol < 3"
  shows "physical_scan_events left symbols = 0"
  using assms
proof (induction symbols arbitrary: left)
  case Nil
  then show ?case by simp
next
  case (Cons symbol symbols)
  have symbol: "symbol < 3" using Cons.prems by simp
  have closed: "physical_left_advance left symbol < 6"
    using physical_left_advance_closed Cons.prems(2) symbol by blast
  have positive: "0 < physical_left_advance left symbol"
    using physical_left_advance_leaves_start Cons.prems(1,2) symbol by blast
  have tail: "physical_scan_events (physical_left_advance left symbol) symbols = 0"
    using Cons.IH[OF positive closed] Cons.prems(3) by simp
  show ?case using Cons.prems(1) tail
    by (simp add: physical_odd_event_def)
qed

theorem physical_low_boundary_owns_odd_event:
  assumes "head < 2" "\<forall>symbol \<in> set tail. symbol < 3"
  shows "physical_scan_events 0 (head # tail) = (if head = 1 then 1 else 0)"
proof -
  have cases: "head = 0 \<or> head = 1" using less_two_cases assms(1) by blast
  then show ?thesis
  proof
    assume head: "head = 0"
    have "physical_scan_events 1 tail = 0"
      using physical_scan_events_after_start[of 1 tail] assms(2) by simp
    then show ?thesis
      by (simp add: head physical_odd_event_def physical_left_advance_def)
  next
    assume head: "head = 1"
    have "physical_scan_events 5 tail = 0"
      using physical_scan_events_after_start[of 5 tail] assms(2) by simp
    then show ?thesis
      by (simp add: head physical_odd_event_def physical_left_advance_def)
  qed
qed

theorem physical_nonstart_owns_no_odd_event:
  assumes "0 < left" "left < 6" "\<forall>symbol \<in> set symbols. symbol < 3"
  shows "physical_scan_events left symbols = 0"
  using physical_scan_events_after_start assms by blast

lemma physical_blank_exterior_owns_no_odd_event:
  "physical_scan_events 0 (replicate n 2) = 0"
  by (induction n)
     (simp_all add: physical_odd_event_def physical_left_advance_def)

lemma compiled_consumer_table:
  assumes "left < 6" "symbol < 3"
  shows
    "(compiled_uses_right symbol ! left, compiled_local_output symbol ! left) =
      physical_output_consumer left symbol"
  using less_six_cases[OF assms(1)] less_three_cases[OF assms(2)]
  by (elim disjE)
     (simp_all add: compiled_uses_right_def compiled_local_output_def
       physical_output_consumer_def collatz_current_def collatz_previous_def
       collatz_carry_def)

theorem compiled_publisher_refines_physical_emit:
  assumes "left < 6" "symbol < 3" "right < 3"
  shows "compiled_physical_publisher symbol left right =
    physical_emit left symbol right"
proof -
  obtain uses local where consumer:
    "physical_output_consumer left symbol = (uses, local)"
    by (cases "physical_output_consumer left symbol") blast
  have compiled:
    "(compiled_uses_right symbol ! left, compiled_local_output symbol ! left) =
      (uses, local)"
    using compiled_consumer_table[OF assms(1,2)] by (simp add: consumer)
  then have uses:
      "compiled_uses_right symbol ! left = uses"
    and local:
      "compiled_local_output symbol ! left = local"
    by simp_all
  show ?thesis
    by (simp add: compiled_physical_publisher_def physical_emit_def consumer uses local)
qed

definition compiled_output_pullback ::
  "nat \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "compiled_output_pullback symbol demand left right =
    demand (compiled_physical_publisher symbol left right)"

definition physical_output_pullback ::
  "nat \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "physical_output_pullback symbol demand left right =
    demand (physical_emit left symbol right)"

theorem compiled_pullback_refines_physical_emit:
  assumes "left < 6" "symbol < 3" "right < 3"
  shows "compiled_output_pullback symbol demand left right =
    physical_output_pullback symbol demand left right"
  using compiled_publisher_refines_physical_emit[OF assms]
  by (simp add: compiled_output_pullback_def physical_output_pullback_def)

lemma compiled_pullback_factors_through_selected_port:
  "compiled_output_pullback symbol demand left right =
    (if compiled_uses_right symbol ! left then demand right
     else demand (compiled_local_output symbol ! left))"
  by (simp add: compiled_output_pullback_def compiled_physical_publisher_def)

text \<open>The even phase reads exactly the adjacent higher symbol.\<close>

lemma compiled_even_shift:
  assumes "symbol < 3" "right < 3"
  shows "compiled_physical_publisher symbol 1 right = right"
  using assms by (simp add: compiled_physical_publisher_def compiled_uses_right_def)

text \<open>
  States 2--5 encode (previous bit, carry) in the same order as the Python
  implementation.  Except for the settled blank state, the local output is
  the low bit of current + previous + carry.
\<close>

lemma compiled_odd_carry:
  assumes "2 \<le> left" "left < 6" "symbol < 3"
  defines sum_value_def:
    "sum_value \<equiv> collatz_current symbol + collatz_previous left + collatz_carry left"
  shows "compiled_physical_publisher symbol left right =
    (if symbol = 2 \<and> sum_value = 0 then 2 else sum_value mod 2)"
  using odd_state_cases[OF assms(1,2)] less_three_cases[OF assms(3)] sum_value_def
  by (elim disjE)
     (simp_all add: compiled_physical_publisher_def compiled_uses_right_def
       compiled_local_output_def collatz_current_def collatz_previous_def
       collatz_carry_def)

ML \<open>
  val _ = if null (Thm_Deps.all_oracles @{thms
    less_six_cases odd_state_cases less_three_cases less_two_cases
    physical_left_advance_closed physical_left_advance_leaves_start
    physical_scan_events_after_start physical_low_boundary_owns_odd_event
    physical_nonstart_owns_no_odd_event physical_blank_exterior_owns_no_odd_event
    compiled_consumer_table
    compiled_publisher_refines_physical_emit
    compiled_pullback_refines_physical_emit
    compiled_pullback_factors_through_selected_port
    compiled_even_shift
    compiled_odd_carry})
  then () else error "Physical Collatz bound consumer oracle dependency";
\<close>

end
