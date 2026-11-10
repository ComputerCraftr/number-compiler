theory Double_Reverse_Centered_Word_Action
  imports Double_Reverse_Centered_Harmonic_Action
begin

text \<open>Finite chronological center-driver word laws.  These compose only
source-admitted finite words; they do not infer future repetition.\<close>

fun double_reverse_center_driver_ports_word ::
    "double_reverse_center_four_driver list \<Rightarrow> (nat \<times> nat) list" where
  "double_reverse_center_driver_ports_word [] = []"
| "double_reverse_center_driver_ports_word (driver # drivers) =
    double_reverse_center_four_ports driver @
      double_reverse_center_driver_ports_word drivers"

fun double_reverse_center_driver_word_valid ::
    "double_reverse_center_four_driver list \<Rightarrow> bool" where
  "double_reverse_center_driver_word_valid [] = True"
| "double_reverse_center_driver_word_valid (driver # drivers) =
    (double_reverse_center_four_driver_valid driver \<and>
      double_reverse_center_driver_word_valid drivers)"

definition double_reverse_center_driver_word_result ::
    "nat \<Rightarrow> double_reverse_center_four_driver list \<Rightarrow> nat" where
  "double_reverse_center_driver_word_result center drivers =
    double_reverse_open_stencil_trace center
      (double_reverse_center_driver_ports_word drivers)"

fun double_reverse_center_driver_forcing_word ::
    "nat \<Rightarrow> double_reverse_center_four_driver list \<Rightarrow> nat list" where
  "double_reverse_center_driver_forcing_word center [] = []"
| "double_reverse_center_driver_forcing_word center (driver # drivers) =
    double_reverse_center_four_forcing center driver #
      double_reverse_center_driver_forcing_word
        (double_reverse_center_four_result center driver) drivers"

fun double_reverse_center_weighted_mod10 :: "nat list \<Rightarrow> nat" where
  "double_reverse_center_weighted_mod10 [] = 0"
| "double_reverse_center_weighted_mod10 (weight # weights) =
    (16 ^ length weights * weight +
      double_reverse_center_weighted_mod10 weights) mod 10"

lemma double_reverse_center_driver_forcing_word_length:
  "length (double_reverse_center_driver_forcing_word center drivers) =
    length drivers"
  by (induction drivers arbitrary: center) simp_all

lemma double_reverse_center_driver_ports_word_valid:
  assumes "double_reverse_center_driver_word_valid drivers"
  shows "double_reverse_open_inputs_valid
    (double_reverse_center_driver_ports_word drivers)"
  using assms
proof (induction drivers)
  case Nil
  then show ?case
    by (simp add: double_reverse_center_driver_ports_word.simps
        double_reverse_open_inputs_valid_def)
next
  case (Cons driver drivers)
  have driver_valid: "double_reverse_center_four_driver_valid driver"
    using Cons.prems by simp
  have drivers_valid: "double_reverse_center_driver_word_valid drivers"
    using Cons.prems by simp
  have head:
    "double_reverse_open_inputs_valid
      (double_reverse_center_four_ports driver)"
    by (rule double_reverse_center_four_ports_valid[OF driver_valid])
  have tail:
    "double_reverse_open_inputs_valid
      (double_reverse_center_driver_ports_word drivers)"
    by (rule Cons.IH[OF drivers_valid])
  show ?case
    using head tail
    by (simp add: double_reverse_center_driver_ports_word.simps
        double_reverse_open_inputs_valid_def)
qed

lemma double_reverse_center_driver_ports_word_append:
  "double_reverse_center_driver_ports_word (first @ second) =
    double_reverse_center_driver_ports_word first @
      double_reverse_center_driver_ports_word second"
  by (induction first) (simp_all add: append_assoc)

lemma double_reverse_center_driver_word_result_append:
  "double_reverse_center_driver_word_result center (first @ second) =
    double_reverse_center_driver_word_result
      (double_reverse_center_driver_word_result center first) second"
  unfolding double_reverse_center_driver_word_result_def
  by (simp add: double_reverse_center_driver_ports_word_append
      double_reverse_open_stencil_trace_append)

lemma double_reverse_center_driver_word_result_cons:
  "double_reverse_center_driver_word_result center (driver # drivers) =
    double_reverse_center_driver_word_result
      (double_reverse_center_four_result center driver) drivers"
proof -
  have append:
    "double_reverse_center_driver_word_result center ([driver] @ drivers) =
      double_reverse_center_driver_word_result
        (double_reverse_center_driver_word_result center [driver]) drivers"
    by (rule double_reverse_center_driver_word_result_append)
  have one:
    "double_reverse_center_driver_word_result center [driver] =
      double_reverse_center_four_result center driver"
    by (simp add: double_reverse_center_driver_word_result_def
        double_reverse_center_driver_ports_word.simps
        double_reverse_center_four_result_def)
  show ?thesis using append one by simp
qed

lemma double_reverse_center_driver_word_forcing_append:
  "double_reverse_center_driver_forcing_word center (first @ second) =
    double_reverse_center_driver_forcing_word center first @
      double_reverse_center_driver_forcing_word
        (double_reverse_center_driver_word_result center first) second"
proof (induction first arbitrary: center)
  case Nil
  then show ?case
    by (simp add: double_reverse_center_driver_word_result_def)
next
  case (Cons driver first)
  have result_cons:
    "double_reverse_center_driver_word_result center (driver # first) =
      double_reverse_center_driver_word_result
        (double_reverse_center_four_result center driver) first"
    by (rule double_reverse_center_driver_word_result_cons)
  show ?case using Cons.IH result_cons by simp
qed

theorem double_reverse_center_driver_word_weighted_mod10:
  assumes center: "center < 10"
      and drivers: "double_reverse_center_driver_word_valid word"
  shows "double_reverse_center_driver_word_result center word =
    (16 ^ length word * center +
      double_reverse_center_weighted_mod10
        (double_reverse_center_driver_forcing_word center word)) mod 10"
  using center drivers
proof (induction word arbitrary: center)
  case Nil
  then show ?case
    by (simp add: double_reverse_center_driver_word_result_def)
next
  case (Cons action word)
  let ?next = "double_reverse_center_four_result center action"
  let ?forcing = "double_reverse_center_four_forcing center action"
  have action_valid:
    "double_reverse_center_four_driver_valid action"
    using Cons.prems(2) by simp
  have tail_valid:
    "double_reverse_center_driver_word_valid word"
    using Cons.prems(2) by simp
  have next_bound: "?next < 10"
    by (rule double_reverse_center_four_result_bounded)
  have action_exact:
    "?next = (16 * center + ?forcing) mod 10"
    by (rule double_reverse_center_forced_four_physical_steps
      [OF Cons.prems(1) action_valid])
  have tail_exact:
    "double_reverse_center_driver_word_result ?next word =
      (16 ^ length word * ?next +
        double_reverse_center_weighted_mod10
          (double_reverse_center_driver_forcing_word ?next word)) mod 10"
    by (rule Cons.IH[OF next_bound tail_valid])
  have joined_result:
    "double_reverse_center_driver_word_result center (action # word) =
      double_reverse_center_driver_word_result ?next word"
    by (rule double_reverse_center_driver_word_result_cons)
  have joined_forcing:
    "double_reverse_center_driver_forcing_word center (action # word) =
      ?forcing # double_reverse_center_driver_forcing_word ?next word"
    by simp
  have weighted_head:
    "double_reverse_center_weighted_mod10
        (?forcing # double_reverse_center_driver_forcing_word ?next word) =
      (16 ^ length word * ?forcing +
        double_reverse_center_weighted_mod10
          (double_reverse_center_driver_forcing_word ?next word)) mod 10"
    by (simp add: double_reverse_center_driver_forcing_word_length)
  have scaled:
    "(16 ^ length word * ?next +
        double_reverse_center_weighted_mod10
          (double_reverse_center_driver_forcing_word ?next word)) mod 10 =
      (16 ^ length word * (16 * center + ?forcing) +
        double_reverse_center_weighted_mod10
          (double_reverse_center_driver_forcing_word ?next word)) mod 10"
  proof -
    have next_mod: "?next mod 10 = (16 * center + ?forcing) mod 10"
      using action_exact by simp
    have product:
      "(16 ^ length word * ?next) mod 10 =
        (16 ^ length word * (16 * center + ?forcing)) mod 10"
      by (rule mod_mult_cong[OF refl next_mod])
    show ?thesis
      by (rule mod_add_cong[OF product refl])
  qed
  have power:
    "(16::nat) ^ length word * 16 = (16::nat) ^ Suc (length word)"
    by (simp add: power_Suc mult.commute)
  have distribute:
    "16 ^ length word * (16 * center + ?forcing) +
        double_reverse_center_weighted_mod10
          (double_reverse_center_driver_forcing_word ?next word) =
      16 ^ Suc (length word) * center +
        (16 ^ length word * ?forcing +
          double_reverse_center_weighted_mod10
            (double_reverse_center_driver_forcing_word ?next word))"
    using power by (simp add: algebra_simps)
  show ?case
    using joined_result joined_forcing tail_exact scaled weighted_head distribute
    by (simp add: mod_add_right_eq)
qed

lemma double_reverse_center_driver_word_result_bounded:
  assumes center: "center < 10"
      and valid: "double_reverse_center_driver_word_valid drivers"
  shows "double_reverse_center_driver_word_result center drivers < 10"
  using double_reverse_center_driver_word_weighted_mod10[OF center valid]
  by simp

theorem double_reverse_center_driver_word_f5_refines:
  assumes center: "center < 10"
      and drivers: "double_reverse_center_driver_word_valid word"
  shows "double_reverse_f5_apply
      (double_reverse_f5_open_trace_action center
        (double_reverse_center_driver_ports_word word)) (center mod 5) =
    double_reverse_center_driver_word_result center word mod 5"
proof -
  have ports:
    "double_reverse_open_inputs_valid
      (double_reverse_center_driver_ports_word word)"
    by (rule double_reverse_center_driver_ports_word_valid[OF drivers])
  show ?thesis
    using double_reverse_f5_open_trace_action_refines_trace[OF center ports]
    by (simp add: double_reverse_center_driver_word_result_def)
qed

theorem double_reverse_center_f5_chronological_application:
  assumes center: "center < 10"
      and first: "double_reverse_center_driver_word_valid earlier"
      and second: "double_reverse_center_driver_word_valid later"
  shows "double_reverse_f5_apply
      (double_reverse_f5_open_trace_action center
        (double_reverse_center_driver_ports_word (earlier @ later)))
      (center mod 5) =
    double_reverse_f5_apply
      (double_reverse_f5_open_trace_action
        (double_reverse_center_driver_word_result center earlier)
        (double_reverse_center_driver_ports_word later))
      (double_reverse_f5_apply
        (double_reverse_f5_open_trace_action center
          (double_reverse_center_driver_ports_word earlier))
        (center mod 5))"
proof -
  have earlier_bound:
    "double_reverse_center_driver_word_result center earlier < 10"
    by (rule double_reverse_center_driver_word_result_bounded[OF center first])
  have joined_valid:
    "double_reverse_center_driver_word_valid (earlier @ later)"
    using first second by (induction earlier) auto
  have whole:
    "double_reverse_f5_apply
      (double_reverse_f5_open_trace_action center
        (double_reverse_center_driver_ports_word (earlier @ later)))
      (center mod 5) =
      double_reverse_center_driver_word_result center (earlier @ later) mod 5"
    by (rule double_reverse_center_driver_word_f5_refines[OF center joined_valid])
  have left:
    "double_reverse_f5_apply
      (double_reverse_f5_open_trace_action center
        (double_reverse_center_driver_ports_word earlier)) (center mod 5) =
      double_reverse_center_driver_word_result center earlier mod 5"
    by (rule double_reverse_center_driver_word_f5_refines[OF center first])
  have right:
    "double_reverse_f5_apply
      (double_reverse_f5_open_trace_action
        (double_reverse_center_driver_word_result center earlier)
        (double_reverse_center_driver_ports_word later))
      (double_reverse_center_driver_word_result center earlier mod 5) =
      double_reverse_center_driver_word_result
        (double_reverse_center_driver_word_result center earlier) later mod 5"
    by (rule double_reverse_center_driver_word_f5_refines
      [OF earlier_bound second])
  have joined:
    "double_reverse_center_driver_word_result center (earlier @ later) =
      double_reverse_center_driver_word_result
        (double_reverse_center_driver_word_result center earlier) later"
    by (rule double_reverse_center_driver_word_result_append)
  show ?thesis
    using whole left right joined
    by simp
qed

lemma double_reverse_mod5_unwrap:
  fixes a b :: nat
  assumes a_bound: "a < 5"
      and b_bound: "b < 5"
  shows "(((a + b) mod 5 + 5 - a) mod 5) = b"
proof -
  show ?thesis
  proof (cases "a + b < 5")
    case True
    have sum_mod: "(a + b) mod 5 = a + b"
      using True by simp
    have subtract: "a + b + 5 - a = b + 5"
      using a_bound b_bound by arith
    show ?thesis using b_bound by (simp only: sum_mod subtract; simp)
  next
    case False
    have lower: "5 \<le> a + b" using False by simp
    have reduced_bound: "a + b - 5 < 5"
      using a_bound b_bound lower by arith
    have shifted: "(a + b) mod 5 = (a + b - 5) mod 5"
      by (rule le_mod_geq[OF lower])
    have sum_mod: "(a + b) mod 5 = a + b - 5"
      using shifted reduced_bound by simp
    have subtract: "a + b - 5 + 5 - a = b"
      using lower by arith
    show ?thesis using b_bound by (simp only: sum_mod subtract; simp)
  qed
qed

lemma double_reverse_mod5_subtract_compose:
  fixes a b c :: nat
  assumes a_bound: "a < 5"
      and b_bound: "b < 5"
      and c_bound: "c < 5"
  shows "(((b + 5 - a) mod 5 + (c + 5 - b) mod 5) mod 5) =
    (c + 5 - a) mod 5"
proof -
  have joined:
    "((b + 5 - a) mod 5 + (c + 5 - b) mod 5) mod 5 =
      ((b + 5 - a) + (c + 5 - b)) mod 5"
    by (rule mod_add_eq)
  have sums:
    "(b + 5 - a) + (c + 5 - b) = c + 10 - a"
    using a_bound b_bound c_bound by arith
  have shift:
    "c + 10 - a = (c + 5 - a) + 5"
    using a_bound c_bound by arith
  have periodic: "((c + 5 - a) + 5) mod 5 = (c + 5 - a) mod 5"
    by (simp add: mod_add_eq)
  show ?thesis
    by (rule trans[OF joined]; simp only: sums shift periodic)
qed

theorem double_reverse_center_driver_four_forcing_mod5:
  assumes center: "center < 10"
      and driver: "double_reverse_center_four_driver_valid action"
  shows "double_reverse_center_four_forcing center action mod 5 =
    (double_reverse_center_four_result center action mod 5 + 5 -
      center mod 5) mod 5"
proof -
  have exact:
    "double_reverse_center_four_result center action =
      (16 * center + double_reverse_center_four_forcing center action) mod 10"
    by (rule double_reverse_center_forced_four_physical_steps[OF center driver])
  have five_dvd_ten: "5 dvd (10::nat)" by simp
  have drop_mod10:
    "((16 * center + double_reverse_center_four_forcing center action) mod 10)
        mod 5 =
      (16 * center + double_reverse_center_four_forcing center action) mod 5"
    by (rule mod_mod_cancel[OF five_dvd_ten])
  have result_mod:
    "double_reverse_center_four_result center action mod 5 =
      (16 * center + double_reverse_center_four_forcing center action) mod 5"
    using exact drop_mod10 by simp
  have sixteen_mod: "(16::nat) mod 5 = 1 mod 5" by simp
  have scale:
    "(16 * center) mod 5 = (1 * center) mod 5"
    by (rule mod_mult_cong[OF sixteen_mod refl])
  have scale_simp: "(1 * center) mod 5 = center mod 5"
    by simp
  have scale_final: "(16 * center) mod 5 = center mod 5"
    by (rule trans[OF scale scale_simp])
  have combined:
    "(16 * center + double_reverse_center_four_forcing center action) mod 5 =
      (center + double_reverse_center_four_forcing center action) mod 5"
    by (rule mod_add_cong[OF scale_final refl])
  have split:
    "(center + double_reverse_center_four_forcing center action) mod 5 =
      (center mod 5 +
        double_reverse_center_four_forcing center action mod 5) mod 5"
    by (rule mod_add_eq[symmetric])
  have result_residue:
    "double_reverse_center_four_result center action mod 5 =
      (center mod 5 +
        double_reverse_center_four_forcing center action mod 5) mod 5"
    using result_mod combined split scale_simp by simp
  have center_residue: "center mod 5 < 5" by simp
  have force_residue:
    "double_reverse_center_four_forcing center action mod 5 < 5"
    by simp
  have subtract:
    "((double_reverse_center_four_result center action mod 5 + 5 -
        center mod 5) mod 5) =
      double_reverse_center_four_forcing center action mod 5"
    by (simp only: result_residue
        double_reverse_mod5_unwrap[OF center_residue force_residue])
  show ?thesis by (rule sym[OF subtract])
qed

theorem double_reverse_center_driver_word_forcing_telescopes_mod5:
  assumes center: "center < 10"
      and drivers: "double_reverse_center_driver_word_valid word"
  shows "sum_list (double_reverse_center_driver_forcing_word center word) mod 5 =
    (double_reverse_center_driver_word_result center word mod 5 + 5 -
      center mod 5) mod 5"
  using center drivers
proof (induction word arbitrary: center)
  case Nil
  then show ?case
    by (simp add: double_reverse_center_driver_word_result_def)
next
  case (Cons action word)
  have action_valid:
    "double_reverse_center_four_driver_valid action"
    using Cons.prems(2) by simp
  have word_valid: "double_reverse_center_driver_word_valid word"
    using Cons.prems(2) by simp
  have first:
    "double_reverse_center_four_forcing center action mod 5 =
      (double_reverse_center_four_result center action mod 5 + 5 -
        center mod 5) mod 5"
    by (rule double_reverse_center_driver_four_forcing_mod5
      [OF Cons.prems(1) action_valid])
  have next_bound: "double_reverse_center_four_result center action < 10"
    by (rule double_reverse_center_four_result_bounded)
  have tail:
    "sum_list (double_reverse_center_driver_forcing_word
        (double_reverse_center_four_result center action) word) mod 5 =
      (double_reverse_center_driver_word_result
        (double_reverse_center_four_result center action) word mod 5 + 5 -
        double_reverse_center_four_result center action mod 5) mod 5"
    by (rule Cons.IH[OF next_bound word_valid])
  let ?start = "center mod 5"
  let ?middle = "double_reverse_center_four_result center action mod 5"
  let ?finish =
    "double_reverse_center_driver_word_result
      (double_reverse_center_four_result center action) word mod 5"
  have start_bound: "?start < 5" by simp
  have middle_bound: "?middle < 5" by simp
  have finish_bound: "?finish < 5" by simp
  have joined_residues:
    "(double_reverse_center_four_forcing center action +
      sum_list (double_reverse_center_driver_forcing_word
        (double_reverse_center_four_result center action) word)) mod 5 =
      (((?middle + 5 - ?start) mod 5) +
        (?finish + 5 - ?middle) mod 5) mod 5"
  proof -
    have split:
      "(double_reverse_center_four_forcing center action +
        sum_list (double_reverse_center_driver_forcing_word
          (double_reverse_center_four_result center action) word)) mod 5 =
       (double_reverse_center_four_forcing center action mod 5 +
        sum_list (double_reverse_center_driver_forcing_word
          (double_reverse_center_four_result center action) word) mod 5) mod 5"
      by (rule mod_add_eq[symmetric])
    show ?thesis by (simp only: split first tail)
  qed
  have composed_residues:
    "(((?middle + 5 - ?start) mod 5) +
        (?finish + 5 - ?middle) mod 5) mod 5 =
      (?finish + 5 - ?start) mod 5"
    by (rule double_reverse_mod5_subtract_compose
      [OF start_bound middle_bound finish_bound])
  have forcing_cons:
    "double_reverse_center_driver_forcing_word center (action # word) =
      double_reverse_center_four_forcing center action #
        double_reverse_center_driver_forcing_word
          (double_reverse_center_four_result center action) word"
    by simp
  have append:
    "double_reverse_center_driver_word_result center (action # word) =
      double_reverse_center_driver_word_result
        (double_reverse_center_four_result center action) word"
    by (rule double_reverse_center_driver_word_result_cons)
  show ?case
    using joined_residues composed_residues forcing_cons append
    by simp
qed

lemma double_reverse_center_driver_forcing_parity:
  assumes center: "center < 10"
      and driver: "double_reverse_center_four_driver_valid action"
  shows "double_reverse_center_four_forcing center action mod 2 =
    double_reverse_center_four_result center action mod 2"
proof -
  have exact:
    "double_reverse_center_four_result center action =
      (16 * center + double_reverse_center_four_forcing center action) mod 10"
    by (rule double_reverse_center_forced_four_physical_steps[OF center driver])
  have two_dvd_ten: "2 dvd (10::nat)" by simp
  have drop_mod10:
    "((16 * center + double_reverse_center_four_forcing center action) mod 10)
        mod 2 =
      (16 * center + double_reverse_center_four_forcing center action) mod 2"
    by (rule mod_mod_cancel[OF two_dvd_ten])
  have result_mod:
    "double_reverse_center_four_result center action mod 2 =
      (16 * center + double_reverse_center_four_forcing center action) mod 2"
    using exact drop_mod10 by simp
  have center_even: "(16 * center) mod 2 = (0::nat) mod 2" by simp
  have split:
    "(16 * center + double_reverse_center_four_forcing center action) mod 2 =
      (0 + double_reverse_center_four_forcing center action) mod 2"
    by (rule mod_add_cong[OF center_even refl])
  show ?thesis using result_mod split by simp
qed

theorem double_reverse_center_driver_word_terminal_parity:
  assumes center: "center < 10"
      and drivers: "double_reverse_center_driver_word_valid word"
      and nonempty: "word \<noteq> []"
  shows "last (double_reverse_center_driver_forcing_word center word) mod 2 =
    double_reverse_center_driver_word_result center word mod 2"
proof -
  have prefix_valid:
    "double_reverse_center_driver_word_valid (butlast word)"
    using drivers
    by (induction word) (auto split: list.splits)
  have terminal_valid:
    "double_reverse_center_four_driver_valid (last word)"
    using drivers nonempty
    by (induction word) (auto split: list.splits)
  have prefix_bound:
    "double_reverse_center_driver_word_result center (butlast word) < 10"
    by (rule double_reverse_center_driver_word_result_bounded[OF center prefix_valid])
  have split: "word = butlast word @ [last word]"
    by (rule sym[OF append_butlast_last_id[OF nonempty]])
  have result_rebase:
    "double_reverse_center_driver_word_result center word =
      double_reverse_center_driver_word_result center
        (butlast word @ [last word])"
    by (rule arg_cong[OF split])
  have forcing_split:
    "double_reverse_center_driver_forcing_word center word =
      double_reverse_center_driver_forcing_word center (butlast word) @
        [double_reverse_center_four_forcing
          (double_reverse_center_driver_word_result center (butlast word))
          (last word)]"
  proof -
    have rebase:
      "double_reverse_center_driver_forcing_word center word =
        double_reverse_center_driver_forcing_word center
          (butlast word @ [last word])"
      by (rule arg_cong[OF split])
    have joined:
      "double_reverse_center_driver_forcing_word center
          (butlast word @ [last word]) =
        double_reverse_center_driver_forcing_word center (butlast word) @
          double_reverse_center_driver_forcing_word
            (double_reverse_center_driver_word_result center (butlast word))
            [last word]"
      by (rule double_reverse_center_driver_word_forcing_append)
    have singleton:
      "double_reverse_center_driver_forcing_word
          (double_reverse_center_driver_word_result center (butlast word))
          [last word] =
        [double_reverse_center_four_forcing
          (double_reverse_center_driver_word_result center (butlast word))
          (last word)]"
      by simp
    have joined_final:
      "double_reverse_center_driver_forcing_word center
          (butlast word @ [last word]) =
        double_reverse_center_driver_forcing_word center (butlast word) @
          [double_reverse_center_four_forcing
            (double_reverse_center_driver_word_result center (butlast word))
            (last word)]"
      using joined singleton by simp
    show ?thesis by (rule trans[OF rebase joined_final])
  qed
  have result_split:
    "double_reverse_center_driver_word_result center word =
      double_reverse_center_four_result
        (double_reverse_center_driver_word_result center (butlast word))
        (last word)"
  proof -
    have joined:
      "double_reverse_center_driver_word_result center
          (butlast word @ [last word]) =
        double_reverse_center_driver_word_result
          (double_reverse_center_driver_word_result center (butlast word))
          [last word]"
      by (rule double_reverse_center_driver_word_result_append)
    have singleton:
      "double_reverse_center_driver_word_result
          (double_reverse_center_driver_word_result center (butlast word))
          [last word] =
        double_reverse_center_four_result
          (double_reverse_center_driver_word_result center (butlast word))
          (last word)"
    proof -
      have cons:
        "double_reverse_center_driver_word_result
            (double_reverse_center_driver_word_result center (butlast word))
            (last word # []) =
          double_reverse_center_driver_word_result
            (double_reverse_center_four_result
              (double_reverse_center_driver_word_result center (butlast word))
              (last word)) []"
        by (rule double_reverse_center_driver_word_result_cons)
      show ?thesis using cons
        by (simp add: double_reverse_center_driver_word_result_def
            double_reverse_center_driver_ports_word.simps)
    qed
    have joined_final:
      "double_reverse_center_driver_word_result center
          (butlast word @ [last word]) =
        double_reverse_center_four_result
          (double_reverse_center_driver_word_result center (butlast word))
          (last word)"
      by (rule trans[OF joined singleton])
    show ?thesis by (rule trans[OF result_rebase joined_final])
  qed
  show ?thesis
    using double_reverse_center_driver_forcing_parity
      [OF prefix_bound terminal_valid]
      forcing_split result_split
    by simp
qed

ML \<open>
  val checked = @{thms double_reverse_center_driver_ports_word_valid
    double_reverse_center_driver_ports_word_append
    double_reverse_center_driver_forcing_word_length
    double_reverse_center_driver_word_result_append
    double_reverse_center_driver_word_result_cons
    double_reverse_center_driver_word_forcing_append
    double_reverse_center_driver_word_weighted_mod10
    double_reverse_center_driver_word_result_bounded
    double_reverse_center_driver_word_f5_refines
    double_reverse_center_f5_chronological_application
    double_reverse_mod5_unwrap
    double_reverse_mod5_subtract_compose
    double_reverse_center_driver_four_forcing_mod5
    double_reverse_center_driver_word_forcing_telescopes_mod5
    double_reverse_center_driver_forcing_parity
    double_reverse_center_driver_word_terminal_parity};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Double-reverse centered word action depends on an oracle";
  val _ = if Thm_Deps.has_skip_proof checked
    then error "Skipped double-reverse centered word action proof" else ();
\<close>

end
