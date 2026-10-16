theory Double_Reverse_Birth_Layer_Refinement
  imports Double_Reverse_Periodic_Ring_Action
begin

text \<open>A birth-layer state stores equal-length strips at the current
canonical decimal boundaries.  Its two ports are the next source digits
inward from those boundaries.  Projection therefore moves each boundary
inward by one pair and turns the removed pair into the outer layer's next
port.  The results below concern an explicitly supplied finite input trace;
they do not assert that a seed supplies a periodic trace forever.\<close>

record double_reverse_birth_state =
  birth_left_strip :: "nat list"
  birth_right_strip :: "nat list"
  birth_edge_phase :: nat

definition double_reverse_birth_left_digit ::
    "nat list \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> nat" where
  "double_reverse_birth_left_digit strip inward i =
    (if i < 0 then 0
     else if nat i < length strip then strip ! nat i
     else if nat i = length strip then inward else 0)"

definition double_reverse_birth_right_digit ::
    "nat list \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> nat" where
  "double_reverse_birth_right_digit strip inward i =
    (if i = -1 then inward
     else if 0 \<le> i \<and> nat i < length strip then strip ! nat i
     else 0)"

definition double_reverse_birth_left_cell ::
    "nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "double_reverse_birth_left_cell strip inward births j =
    double_reverse_t2_digit
      (double_reverse_birth_left_digit strip inward
        (int j - int births - 1))
      (double_reverse_birth_left_digit strip inward
        (int j - int births))
      (double_reverse_birth_left_digit strip inward
        (int j + 1 - int births))"

definition double_reverse_birth_right_cell ::
    "nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "double_reverse_birth_right_cell strip inward births j =
    double_reverse_t2_digit
      (double_reverse_birth_right_digit strip inward
        (int j + int births - 1))
      (double_reverse_birth_right_digit strip inward
        (int j + int births))
      (double_reverse_birth_right_digit strip inward
        (int j + int births + 1))"

definition double_reverse_birth_left_step ::
    "nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list" where
  "double_reverse_birth_left_step strip inward births =
    map (double_reverse_birth_left_cell strip inward births) [0..<length strip]"

definition double_reverse_birth_right_step ::
    "nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list" where
  "double_reverse_birth_right_step strip inward births =
    map (double_reverse_birth_right_cell strip inward births) [0..<length strip]"

definition double_reverse_birth_advance ::
    "double_reverse_birth_state \<Rightarrow> nat \<times> nat \<Rightarrow>
      double_reverse_birth_state" where
  "double_reverse_birth_advance state ports =
    \<lparr>birth_left_strip = double_reverse_birth_left_step
        (birth_left_strip state) (fst ports)
        (double_reverse_left_birth (birth_edge_phase state)),
      birth_right_strip = double_reverse_birth_right_step
        (birth_right_strip state) (snd ports)
        (double_reverse_right_birth (birth_edge_phase state)),
      birth_edge_phase = (birth_edge_phase state + 2) mod 4\<rparr>"

definition double_reverse_birth_project ::
    "double_reverse_birth_state \<Rightarrow> double_reverse_birth_state" where
  "double_reverse_birth_project state =
    \<lparr>birth_left_strip = butlast (birth_left_strip state),
      birth_right_strip = tl (birth_right_strip state),
      birth_edge_phase = birth_edge_phase state\<rparr>"

definition double_reverse_birth_project_port ::
    "double_reverse_birth_state \<Rightarrow> nat \<times> nat" where
  "double_reverse_birth_project_port state =
    (last (birth_left_strip state), hd (birth_right_strip state))"

lemma double_reverse_birth_left_digit_project:
  assumes length: "length strip = Suc k"
      and bound: "i \<le> int k"
  shows "double_reverse_birth_left_digit (butlast strip) (last strip) i =
    double_reverse_birth_left_digit strip inward i"
proof (cases "i < 0")
  case True
  then show ?thesis
    by (simp add: double_reverse_birth_left_digit_def)
next
  case False
  have nonnegative: "0 \<le> i" using False by arith
  have nat_bound: "nat i \<le> k" using nonnegative bound by presburger
  show ?thesis
  proof (cases "nat i < k")
    case True
    then show ?thesis
    proof -
      have index_bound: "nat i < length (butlast strip)"
        using True length by simp
      have index_value: "butlast strip ! nat i = strip ! nat i"
        by (rule nth_butlast[OF index_bound])
      show ?thesis
        using True length index_value
        by (simp add: double_reverse_birth_left_digit_def)
    qed
  next
    case False
    then have endpoint: "nat i = k" using nat_bound by arith
    have strip_nonempty: "strip \<noteq> []" using length by auto
    have last_formula: "last strip = strip ! (length strip - 1)"
      by (rule last_conv_nth[OF strip_nonempty])
    have last_value: "last strip = strip ! k"
      using last_formula length by simp
    show ?thesis
      using endpoint length last_value False
      by (simp add: double_reverse_birth_left_digit_def)
  qed
qed

lemma double_reverse_birth_right_digit_project:
  assumes nonempty: "strip \<noteq> []"
      and bound: "-1 \<le> i"
  shows "double_reverse_birth_right_digit (tl strip) (hd strip) i =
    double_reverse_birth_right_digit strip inward (i + 1)"
proof (cases "i = -1")
  case True
  have head_value: "hd strip = strip ! 0"
    by (rule hd_conv_nth[OF nonempty])
  show ?thesis
    using True nonempty head_value
    by (simp add: double_reverse_birth_right_digit_def)
next
  case False
  have nonnegative: "0 \<le> i" using bound False by arith
  have successor: "nat (i + 1) = Suc (nat i)"
    using nonnegative by simp
  have tail_length: "length (tl strip) = length strip - 1" by simp
  show ?thesis
  proof (cases "nat i < length (tl strip)")
    case True
    have inside: "Suc (nat i) < length strip"
      using True tail_length by arith
    have tail_bound: "nat i < length strip - 1"
      using inside by arith
    have tail_value: "tl strip ! nat i = strip ! Suc (nat i)"
      by (rule nth_tl[OF True])
    show ?thesis
      using nonnegative successor inside tail_bound tail_value
      by (simp add: double_reverse_birth_right_digit_def)
  next
    case False
    have outside: "\<not> Suc (nat i) < length strip"
      using False tail_length by arith
    have tail_outside: "\<not> nat i < length strip - 1"
      using outside by arith
    show ?thesis
      using nonnegative successor outside tail_outside
      by (simp add: double_reverse_birth_right_digit_def)
  qed
qed

lemma double_reverse_birth_left_cell_project:
  assumes length: "length strip = Suc k"
      and position: "j < k"
      and births: "births \<le> 1"
  shows "double_reverse_birth_left_cell strip inward births j =
    double_reverse_birth_left_cell (butlast strip) (last strip) births j"
proof -
  have before_bound: "int j - int births - 1 \<le> int k"
    using position births by presburger
  have center_bound: "int j - int births \<le> int k"
    using position births by presburger
  have after_bound: "int j + 1 - int births \<le> int k"
    using position births by presburger
  have before:
    "double_reverse_birth_left_digit (butlast strip) (last strip)
        (int j - int births - 1) =
      double_reverse_birth_left_digit strip inward
        (int j - int births - 1)"
    by (rule double_reverse_birth_left_digit_project[OF length before_bound])
  have center:
    "double_reverse_birth_left_digit (butlast strip) (last strip)
        (int j - int births) =
      double_reverse_birth_left_digit strip inward (int j - int births)"
    by (rule double_reverse_birth_left_digit_project[OF length center_bound])
  have after:
    "double_reverse_birth_left_digit (butlast strip) (last strip)
        (int j + 1 - int births) =
      double_reverse_birth_left_digit strip inward (int j + 1 - int births)"
    by (rule double_reverse_birth_left_digit_project[OF length after_bound])
  show ?thesis
    using before center after
    by (simp add: double_reverse_birth_left_cell_def)
qed

lemma double_reverse_birth_right_cell_project:
  assumes nonempty: "strip \<noteq> []"
  shows "double_reverse_birth_right_cell (tl strip) (hd strip) births j =
    double_reverse_birth_right_cell strip inward births (Suc j)"
proof -
  let ?q = "int j + int births"
  have before_bound: "-1 \<le> ?q - 1" by simp
  have center_bound: "-1 \<le> ?q" by simp
  have after_bound: "-1 \<le> ?q + 1" by simp
  have before_aux:
    "double_reverse_birth_right_digit (tl strip) (hd strip) (?q - 1) =
      double_reverse_birth_right_digit strip inward ((?q - 1) + 1)"
    by (rule double_reverse_birth_right_digit_project[OF nonempty before_bound])
  have before:
    "double_reverse_birth_right_digit (tl strip) (hd strip) (?q - 1) =
      double_reverse_birth_right_digit strip inward ?q"
    using before_aux by simp
  have center:
    "double_reverse_birth_right_digit (tl strip) (hd strip) ?q =
      double_reverse_birth_right_digit strip inward (?q + 1)"
    by (rule double_reverse_birth_right_digit_project[OF nonempty center_bound])
  have after_aux:
    "double_reverse_birth_right_digit (tl strip) (hd strip) (?q + 1) =
      double_reverse_birth_right_digit strip inward ((?q + 1) + 1)"
    by (rule double_reverse_birth_right_digit_project[OF nonempty after_bound])
  have after:
    "double_reverse_birth_right_digit (tl strip) (hd strip) (?q + 1) =
      double_reverse_birth_right_digit strip inward (?q + 2)"
  proof -
    have shift: "?q + 2 = (?q + 1) + 1" by arith
    show ?thesis using after_aux shift by (simp only: after_aux shift)
  qed
  show ?thesis
    using before center after
    by (simp add: double_reverse_birth_right_cell_def algebra_simps)
qed

lemma double_reverse_birth_left_step_project:
  assumes length: "length strip = Suc k"
      and nontrivial: "0 < k"
      and births: "births \<le> 1"
  shows "butlast (double_reverse_birth_left_step strip inward births) =
    double_reverse_birth_left_step (butlast strip) (last strip) births"
proof (rule nth_equalityI)
  show "length (butlast (double_reverse_birth_left_step strip inward births)) =
      length (double_reverse_birth_left_step (butlast strip) (last strip) births)"
    using length by (simp add: double_reverse_birth_left_step_def)
next
  fix j
  assume j:
    "j < length (butlast (double_reverse_birth_left_step strip inward births))"
  have position: "j < k"
    using j length by (simp add: double_reverse_birth_left_step_def)
  have cell:
    "double_reverse_birth_left_cell strip inward births j =
      double_reverse_birth_left_cell (butlast strip) (last strip) births j"
    by (rule double_reverse_birth_left_cell_project[OF length position births])
  show "butlast (double_reverse_birth_left_step strip inward births) ! j =
      double_reverse_birth_left_step (butlast strip) (last strip) births ! j"
    using cell position length nontrivial
    by (simp add: double_reverse_birth_left_step_def)
qed

lemma double_reverse_birth_right_step_project:
  assumes length: "length strip = Suc k"
      and nontrivial: "0 < k"
  shows "tl (double_reverse_birth_right_step strip inward births) =
    double_reverse_birth_right_step (tl strip) (hd strip) births"
proof (rule nth_equalityI)
  show "length (tl (double_reverse_birth_right_step strip inward births)) =
      length (double_reverse_birth_right_step (tl strip) (hd strip) births)"
    using length by (simp add: double_reverse_birth_right_step_def)
next
  fix j
  assume j:
    "j < length (tl (double_reverse_birth_right_step strip inward births))"
  have position: "j < k"
    using j length by (simp add: double_reverse_birth_right_step_def)
  have nonempty: "strip \<noteq> []" using length by auto
  have cell:
    "double_reverse_birth_right_cell (tl strip) (hd strip) births j =
      double_reverse_birth_right_cell strip inward births (Suc j)"
    by (rule double_reverse_birth_right_cell_project[OF nonempty])
  have parent_step_length:
    "length (double_reverse_birth_right_step strip inward births) = Suc k"
    using length by (simp add: double_reverse_birth_right_step_def)
  have tail_bound:
    "j < length (tl (double_reverse_birth_right_step strip inward births))"
    using position parent_step_length by simp
  have tail_index:
    "tl (double_reverse_birth_right_step strip inward births) ! j =
      double_reverse_birth_right_step strip inward births ! Suc j"
    by (rule nth_tl[OF tail_bound])
  have parent_map_index:
    "map (double_reverse_birth_right_cell strip inward births)
        [0..<length strip] ! Suc j =
      double_reverse_birth_right_cell strip inward births (Suc j)"
  proof -
    have raw:
      "map (double_reverse_birth_right_cell strip inward births)
          [0..<length strip] ! Suc j =
        double_reverse_birth_right_cell strip inward births (0 + Suc j)"
    proof (rule nth_map_upt)
      show "Suc j < length strip - 0"
        using position length by arith
    qed
    show ?thesis using raw by simp
  qed
  have parent_index:
    "double_reverse_birth_right_step strip inward births ! Suc j =
      double_reverse_birth_right_cell strip inward births (Suc j)"
    using parent_map_index
    by (simp only: double_reverse_birth_right_step_def)
  have child_step_length: "length (tl strip) = k"
    using length by simp
  have child_map_index:
    "map (double_reverse_birth_right_cell (tl strip) (hd strip) births)
        [0..<length (tl strip)] ! j =
      double_reverse_birth_right_cell (tl strip) (hd strip) births j"
  proof -
    have raw:
      "map (double_reverse_birth_right_cell (tl strip) (hd strip) births)
          [0..<length (tl strip)] ! j =
        double_reverse_birth_right_cell (tl strip) (hd strip) births (0 + j)"
    proof (rule nth_map_upt)
      show "j < length (tl strip) - 0"
        using position child_step_length by arith
    qed
    show ?thesis using raw by simp
  qed
  have child_index:
    "double_reverse_birth_right_step (tl strip) (hd strip) births ! j =
      double_reverse_birth_right_cell (tl strip) (hd strip) births j"
    using child_map_index
    by (simp only: double_reverse_birth_right_step_def)
  show "tl (double_reverse_birth_right_step strip inward births) ! j =
      double_reverse_birth_right_step (tl strip) (hd strip) births ! j"
    using tail_index parent_index child_index cell by simp
qed

theorem double_reverse_birth_layer_step_commutes:
  assumes left_length:
      "length (birth_left_strip state) = Suc k"
      and right_length:
      "length (birth_right_strip state) = Suc k"
      and nontrivial: "0 < k"
      and phase: "birth_edge_phase state < 4"
  shows "double_reverse_birth_project
      (double_reverse_birth_advance state ports) =
    double_reverse_birth_advance
      (double_reverse_birth_project state)
      (double_reverse_birth_project_port state)"
proof -
  have left_birth: "double_reverse_left_birth (birth_edge_phase state) \<le> 1"
    using phase by (simp add: double_reverse_left_birth_def)
  have right_nonempty: "birth_right_strip state \<noteq> []"
    using right_length by auto
  have left:
    "butlast (double_reverse_birth_left_step (birth_left_strip state)
        (fst ports) (double_reverse_left_birth (birth_edge_phase state))) =
      double_reverse_birth_left_step (butlast (birth_left_strip state))
        (last (birth_left_strip state))
        (double_reverse_left_birth (birth_edge_phase state))"
    by (rule double_reverse_birth_left_step_project[OF left_length nontrivial left_birth])
  have right:
    "tl (double_reverse_birth_right_step (birth_right_strip state)
        (snd ports) (double_reverse_right_birth (birth_edge_phase state))) =
      double_reverse_birth_right_step (tl (birth_right_strip state))
        (hd (birth_right_strip state))
        (double_reverse_right_birth (birth_edge_phase state))"
    by (rule double_reverse_birth_right_step_project[OF right_length nontrivial])
  show ?thesis
    using left right
    by (cases state; simp add: double_reverse_birth_project_def
        double_reverse_birth_advance_def double_reverse_birth_project_port_def)
qed

fun double_reverse_birth_run ::
    "double_reverse_birth_state \<Rightarrow> (nat \<times> nat) list \<Rightarrow>
      double_reverse_birth_state" where
  "double_reverse_birth_run state [] = state"
| "double_reverse_birth_run state (ports # inputs) =
    double_reverse_birth_run (double_reverse_birth_advance state ports) inputs"

fun double_reverse_birth_projected_inputs ::
    "double_reverse_birth_state \<Rightarrow> (nat \<times> nat) list \<Rightarrow>
      (nat \<times> nat) list" where
  "double_reverse_birth_projected_inputs state [] = []"
| "double_reverse_birth_projected_inputs state (ports # inputs) =
    double_reverse_birth_project_port state #
      double_reverse_birth_projected_inputs
        (double_reverse_birth_advance state ports) inputs"

lemma double_reverse_birth_advance_lengths:
  "length (birth_left_strip (double_reverse_birth_advance state ports)) =
      length (birth_left_strip state) \<and>
    length (birth_right_strip (double_reverse_birth_advance state ports)) =
      length (birth_right_strip state)"
  by (simp add: double_reverse_birth_advance_def
      double_reverse_birth_left_step_def double_reverse_birth_right_step_def)

theorem double_reverse_birth_layer_trace_commutes:
  assumes left_length: "length (birth_left_strip state) \<ge> 2"
      and equal_length:
        "length (birth_left_strip state) = length (birth_right_strip state)"
      and phase: "birth_edge_phase state < 4"
  shows "double_reverse_birth_project (double_reverse_birth_run state inputs) =
    double_reverse_birth_run (double_reverse_birth_project state)
      (double_reverse_birth_projected_inputs state inputs)"
  using left_length equal_length phase
proof (induction inputs arbitrary: state)
  case Nil
  then show ?case by simp
next
  case (Cons ports inputs)
  let ?next = "double_reverse_birth_advance state ports"
  have left_exact:
    "length (birth_left_strip state) = Suc (length (birth_left_strip state) - 1)"
    using Cons.prems(1) by simp
  have right_exact:
    "length (birth_right_strip state) = Suc (length (birth_left_strip state) - 1)"
  proof -
    have same: "length (birth_left_strip state) = length (birth_right_strip state)"
      using Cons.prems(2) .
    show ?thesis
      using same left_exact by simp
  qed
  have layer_nontrivial: "0 < length (birth_left_strip state) - 1"
    using Cons.prems(1) by arith
  have step:
    "double_reverse_birth_project ?next =
      double_reverse_birth_advance (double_reverse_birth_project state)
        (double_reverse_birth_project_port state)"
    by (rule double_reverse_birth_layer_step_commutes
        [OF left_exact right_exact layer_nontrivial Cons.prems(3)])
  have next_lengths:
    "length (birth_left_strip ?next) \<ge> 2 \<and>
      length (birth_left_strip ?next) = length (birth_right_strip ?next)"
    using Cons.prems(1,2) double_reverse_birth_advance_lengths[of state ports]
    by auto
  have next_phase: "birth_edge_phase ?next < 4"
    by (simp add: double_reverse_birth_advance_def)
  have next_left_length: "length (birth_left_strip ?next) \<ge> 2"
    using next_lengths by blast
  have next_equal_lengths:
    "length (birth_left_strip ?next) = length (birth_right_strip ?next)"
    using next_lengths by blast
  have induction:
    "double_reverse_birth_project (double_reverse_birth_run ?next inputs) =
      double_reverse_birth_run (double_reverse_birth_project ?next)
        (double_reverse_birth_projected_inputs ?next inputs)"
    by (rule Cons.IH[OF next_left_length next_equal_lengths next_phase])
  show ?case
    using step induction
    by simp
qed

text \<open>A conditional model includes both a complete birth-ring state and
the position in its declared input motif.  Its cycle theorem below powers
only that pair.  It neither infers a motif from a finite source prefix nor
authorizes applying it outside the prefix that issued those ports.\<close>

definition double_reverse_birth_model_step ::
    "(nat \<times> nat) list \<Rightarrow>
      (double_reverse_birth_state \<times> nat) \<Rightarrow>
      (double_reverse_birth_state \<times> nat)" where
  "double_reverse_birth_model_step motif model =
    (double_reverse_birth_advance (fst model)
        (motif ! (snd model mod length motif)),
      (snd model + 1) mod length motif)"

definition double_reverse_birth_model_run ::
    "nat \<Rightarrow> (nat \<times> nat) list \<Rightarrow>
      (double_reverse_birth_state \<times> nat) \<Rightarrow>
      (double_reverse_birth_state \<times> nat)" where
  "double_reverse_birth_model_run steps motif model =
    (double_reverse_birth_model_step motif ^^ steps) model"

definition double_reverse_birth_model_cycle ::
    "nat \<Rightarrow> (nat \<times> nat) list \<Rightarrow>
      (double_reverse_birth_state \<times> nat) \<Rightarrow> bool" where
  "double_reverse_birth_model_cycle period motif model \<longleftrightarrow>
    motif \<noteq> [] \<and> 0 < period \<and>
    double_reverse_birth_model_run period motif model = model"

lemma double_reverse_birth_model_run_add:
  "double_reverse_birth_model_run (first + second) motif model =
    double_reverse_birth_model_run second motif
      (double_reverse_birth_model_run first motif model)"
proof -
  have exponent: "first + second = second + first"
    by (simp add: add.commute)
  show ?thesis
    unfolding double_reverse_birth_model_run_def
    by (simp only: exponent funpow_add comp_apply)
qed

theorem double_reverse_birth_conditional_return_repeats:
  assumes cycle: "double_reverse_birth_model_cycle period motif model"
  shows "double_reverse_birth_model_run (period * count) motif model = model"
proof (induction count)
  case 0
  then show ?case
    by (simp add: double_reverse_birth_model_run_def)
next
  case (Suc count)
  have step: "double_reverse_birth_model_run period motif model = model"
    using cycle by (simp add: double_reverse_birth_model_cycle_def)
  have exponent: "period * Suc count = period * count + period"
    by (simp add: algebra_simps)
  show ?case
    using Suc.IH step
    by (simp only: exponent double_reverse_birth_model_run_add Suc.IH step)
qed

theorem double_reverse_birth_conditional_future_periodic:
  assumes cycle: "double_reverse_birth_model_cycle period motif model"
  shows "double_reverse_birth_model_run (time + period) motif model =
    double_reverse_birth_model_run time motif model"
proof -
  have state_cycle: "double_reverse_birth_model_run period motif model = model"
    using cycle by (simp add: double_reverse_birth_model_cycle_def)
  have reindex: "time + period = period + time"
    by (simp add: add.commute)
  have action:
    "double_reverse_birth_model_run (period + time) motif model =
      double_reverse_birth_model_run time motif
        (double_reverse_birth_model_run period motif model)"
    by (rule double_reverse_birth_model_run_add)
  show ?thesis
    by (subst reindex; simp only: action state_cycle)
qed

corollary double_reverse_birth_conditional_state_periodic:
  assumes cycle: "double_reverse_birth_model_cycle period motif model"
  shows "fst (double_reverse_birth_model_run (time + period) motif model) =
    fst (double_reverse_birth_model_run time motif model)"
  using double_reverse_birth_conditional_future_periodic[OF cycle]
  by simp

text \<open>The conditional return theorem is a finite-state powering result for
an explicit motif.  A source certificate must separately establish every
inlet through its demanded horizon; finite agreement is not an infinite
source-language theorem.\<close>

ML \<open>
  val checked = @{thms double_reverse_birth_left_digit_project
    double_reverse_birth_right_digit_project
    double_reverse_birth_left_cell_project
    double_reverse_birth_right_cell_project
    double_reverse_birth_left_step_project
    double_reverse_birth_right_step_project
    double_reverse_birth_layer_step_commutes
    double_reverse_birth_advance_lengths
    double_reverse_birth_layer_trace_commutes
    double_reverse_birth_model_run_add
    double_reverse_birth_conditional_return_repeats
    double_reverse_birth_conditional_future_periodic
    double_reverse_birth_conditional_state_periodic};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Double-reverse birth layer refinement depends on an oracle";
\<close>

end
