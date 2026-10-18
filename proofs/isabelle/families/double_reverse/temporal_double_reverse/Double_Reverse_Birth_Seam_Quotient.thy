theory Double_Reverse_Birth_Seam_Quotient
  imports Double_Reverse_Birth_Layer_Refinement
begin

text \<open>The complete next K-bank depends on the two inward ports only through
the exact outputs at active seam cells. Birth on a side shields its port.
This is a one-step right congruence, not a claim of periodic source inlets.\<close>

definition double_reverse_birth_left_seam_output ::
    "double_reverse_birth_state \<Rightarrow> nat \<Rightarrow> nat option" where
  "double_reverse_birth_left_seam_output state inward =
    (if double_reverse_left_birth (birth_edge_phase state) = 0
     then Some (double_reverse_birth_left_cell
       (birth_left_strip state) inward 0
       (length (birth_left_strip state) - 1))
     else None)"

definition double_reverse_birth_right_seam_output ::
    "double_reverse_birth_state \<Rightarrow> nat \<Rightarrow> nat option" where
  "double_reverse_birth_right_seam_output state inward =
    (if double_reverse_right_birth (birth_edge_phase state) = 0
     then Some (double_reverse_birth_right_cell
       (birth_right_strip state) inward 0 0)
     else None)"

definition double_reverse_birth_seam_gate ::
    "double_reverse_birth_state \<Rightarrow> nat \<times> nat \<Rightarrow>
      nat option \<times> nat option" where
  "double_reverse_birth_seam_gate state ports =
    (double_reverse_birth_left_seam_output state (fst ports),
     double_reverse_birth_right_seam_output state (snd ports))"

lemma double_reverse_birth_left_digit_below_independent:
  assumes "i < int (length strip)"
  shows "double_reverse_birth_left_digit strip first i =
    double_reverse_birth_left_digit strip second i"
  using assms
  by (auto simp: double_reverse_birth_left_digit_def split: if_splits; arith)

lemma double_reverse_birth_right_digit_nonnegative_independent:
  assumes "0 \<le> i"
  shows "double_reverse_birth_right_digit strip first i =
    double_reverse_birth_right_digit strip second i"
  using assms
  by (auto simp: double_reverse_birth_right_digit_def split: if_splits; arith)

lemma double_reverse_birth_left_cell_interior_independent:
  assumes position: "j < length strip"
      and births: "births \<le> 1"
      and interior: "births = 1 \<or> Suc j < length strip"
  shows "double_reverse_birth_left_cell strip first births j =
    double_reverse_birth_left_cell strip second births j"
proof -
  have before: "int j - int births - 1 < int (length strip)"
    using position births interior by arith
  have center: "int j - int births < int (length strip)"
    using position births interior by arith
  have after: "int j + 1 - int births < int (length strip)"
    using position births interior by arith
  have before_equal:
    "double_reverse_birth_left_digit strip first
        (int j - int births - 1) =
      double_reverse_birth_left_digit strip second
        (int j - int births - 1)"
    by (rule double_reverse_birth_left_digit_below_independent[OF before])
  have center_equal:
    "double_reverse_birth_left_digit strip first (int j - int births) =
      double_reverse_birth_left_digit strip second (int j - int births)"
    by (rule double_reverse_birth_left_digit_below_independent[OF center])
  have after_equal:
    "double_reverse_birth_left_digit strip first
        (int j + 1 - int births) =
      double_reverse_birth_left_digit strip second
        (int j + 1 - int births)"
    by (rule double_reverse_birth_left_digit_below_independent[OF after])
  show ?thesis
    unfolding double_reverse_birth_left_cell_def
    using before_equal center_equal after_equal
    by simp
qed

lemma double_reverse_birth_right_cell_interior_independent:
  assumes position: "j < length strip"
      and births: "births \<le> 1"
      and interior: "births = 1 \<or> 0 < j"
  shows "double_reverse_birth_right_cell strip first births j =
    double_reverse_birth_right_cell strip second births j"
proof -
  have before: "0 \<le> int j + int births - 1"
    using births interior by arith
  have center: "0 \<le> int j + int births"
    by simp
  have after: "0 \<le> int j + int births + 1"
    by simp
  have before_equal:
    "double_reverse_birth_right_digit strip first
        (int j + int births - 1) =
      double_reverse_birth_right_digit strip second
        (int j + int births - 1)"
    by (rule double_reverse_birth_right_digit_nonnegative_independent[OF before])
  have center_equal:
    "double_reverse_birth_right_digit strip first (int j + int births) =
      double_reverse_birth_right_digit strip second (int j + int births)"
    by (rule double_reverse_birth_right_digit_nonnegative_independent[OF center])
  have after_equal:
    "double_reverse_birth_right_digit strip first
        (int j + int births + 1) =
      double_reverse_birth_right_digit strip second
        (int j + int births + 1)"
    by (rule double_reverse_birth_right_digit_nonnegative_independent[OF after])
  show ?thesis
    unfolding double_reverse_birth_right_cell_def
    using before_equal center_equal after_equal
    by simp
qed

lemma double_reverse_birth_left_step_nth:
  assumes "j < length strip"
  shows "double_reverse_birth_left_step strip inward births ! j =
    double_reverse_birth_left_cell strip inward births j"
  using assms
  by (simp add: double_reverse_birth_left_step_def nth_map_upt)

lemma double_reverse_birth_right_step_nth:
  assumes "j < length strip"
  shows "double_reverse_birth_right_step strip inward births ! j =
    double_reverse_birth_right_cell strip inward births j"
  using assms
  by (simp add: double_reverse_birth_right_step_def nth_map_upt)

lemma double_reverse_birth_left_step_seam_iff:
  assumes nonempty: "strip \<noteq> []"
      and births: "births \<le> 1"
  shows "double_reverse_birth_left_step strip first births =
      double_reverse_birth_left_step strip second births \<longleftrightarrow>
    (if births = 0
     then Some (double_reverse_birth_left_cell strip first births
          (length strip - 1)) =
       Some (double_reverse_birth_left_cell strip second births
          (length strip - 1))
     else None = None)"
proof (cases "births = 0")
  case True
  have terminal_bound: "length strip - 1 < length strip"
    using nonempty by simp
  have first_terminal:
    "double_reverse_birth_left_step strip first births ! (length strip - 1) =
      double_reverse_birth_left_cell strip first births (length strip - 1)"
    by (rule double_reverse_birth_left_step_nth[OF terminal_bound])
  have second_terminal:
    "double_reverse_birth_left_step strip second births ! (length strip - 1) =
      double_reverse_birth_left_cell strip second births (length strip - 1)"
    by (rule double_reverse_birth_left_step_nth[OF terminal_bound])
  show ?thesis
  proof
    assume equal:
      "double_reverse_birth_left_step strip first births =
        double_reverse_birth_left_step strip second births"
    have terminal:
      "double_reverse_birth_left_cell strip first births (length strip - 1) =
        double_reverse_birth_left_cell strip second births (length strip - 1)"
      using equal first_terminal second_terminal by simp
    show "(if births = 0
      then Some (double_reverse_birth_left_cell strip first births
          (length strip - 1)) =
        Some (double_reverse_birth_left_cell strip second births
          (length strip - 1))
      else None = None)"
      using terminal by (simp add: True)
  next
    assume terminal:
      "(if births = 0
       then Some (double_reverse_birth_left_cell strip first births
            (length strip - 1)) =
         Some (double_reverse_birth_left_cell strip second births
            (length strip - 1))
       else None = None)"
    have terminal_cells:
      "double_reverse_birth_left_cell strip first births (length strip - 1) =
        double_reverse_birth_left_cell strip second births (length strip - 1)"
      using terminal by (simp add: True)
    show "double_reverse_birth_left_step strip first births =
      double_reverse_birth_left_step strip second births"
    proof (rule nth_equalityI)
      show "length (double_reverse_birth_left_step strip first births) =
        length (double_reverse_birth_left_step strip second births)"
        by (simp add: double_reverse_birth_left_step_def)
    next
      fix j
      assume position: "j < length (double_reverse_birth_left_step strip first births)"
      have bound: "j < length strip"
        using position by (simp add: double_reverse_birth_left_step_def)
      show "double_reverse_birth_left_step strip first births ! j =
        double_reverse_birth_left_step strip second births ! j"
      proof (cases "j = length strip - 1")
        case True
        then show ?thesis
          using terminal_cells first_terminal second_terminal by simp
      next
        case False
        have interior: "Suc j < length strip"
          using bound False by arith
        have cell:
          "double_reverse_birth_left_cell strip first births j =
            double_reverse_birth_left_cell strip second births j"
          by (rule double_reverse_birth_left_cell_interior_independent
              [OF bound births]) (use interior in simp)
        show ?thesis
          using cell by (simp add: double_reverse_birth_left_step_nth bound)
      qed
    qed
  qed
next
  case False
  have one: "births = 1" using births False by arith
  have equal:
    "double_reverse_birth_left_step strip first births =
      double_reverse_birth_left_step strip second births"
  proof (rule nth_equalityI)
    show "length (double_reverse_birth_left_step strip first births) =
      length (double_reverse_birth_left_step strip second births)"
      by (simp add: double_reverse_birth_left_step_def)
  next
    fix j
    assume position: "j < length (double_reverse_birth_left_step strip first births)"
    have bound: "j < length strip"
      using position by (simp add: double_reverse_birth_left_step_def)
    have cell:
      "double_reverse_birth_left_cell strip first births j =
        double_reverse_birth_left_cell strip second births j"
      by (rule double_reverse_birth_left_cell_interior_independent
          [OF bound births])
        (use one in simp)
    show "double_reverse_birth_left_step strip first births ! j =
      double_reverse_birth_left_step strip second births ! j"
      using cell by (simp add: double_reverse_birth_left_step_nth bound)
  qed
  show ?thesis using equal False by simp
qed

lemma double_reverse_birth_right_step_seam_iff:
  assumes nonempty: "strip \<noteq> []"
      and births: "births \<le> 1"
  shows "double_reverse_birth_right_step strip first births =
      double_reverse_birth_right_step strip second births \<longleftrightarrow>
    (if births = 0
     then Some (double_reverse_birth_right_cell strip first births 0) =
       Some (double_reverse_birth_right_cell strip second births 0)
     else None = None)"
proof (cases "births = 0")
  case True
  have first_terminal:
    "double_reverse_birth_right_step strip first births ! 0 =
      double_reverse_birth_right_cell strip first births 0"
    by (rule double_reverse_birth_right_step_nth) (use nonempty in simp)
  have second_terminal:
    "double_reverse_birth_right_step strip second births ! 0 =
      double_reverse_birth_right_cell strip second births 0"
    by (rule double_reverse_birth_right_step_nth) (use nonempty in simp)
  show ?thesis
  proof
    assume equal:
      "double_reverse_birth_right_step strip first births =
        double_reverse_birth_right_step strip second births"
    have terminal:
      "double_reverse_birth_right_cell strip first births 0 =
        double_reverse_birth_right_cell strip second births 0"
      using equal first_terminal second_terminal by simp
    show "(if births = 0
      then Some (double_reverse_birth_right_cell strip first births 0) =
        Some (double_reverse_birth_right_cell strip second births 0)
      else None = None)"
      using terminal by (simp add: True)
  next
    assume terminal:
      "(if births = 0
       then Some (double_reverse_birth_right_cell strip first births 0) =
         Some (double_reverse_birth_right_cell strip second births 0)
       else None = None)"
    have terminal_cells:
      "double_reverse_birth_right_cell strip first births 0 =
        double_reverse_birth_right_cell strip second births 0"
      using terminal by (simp add: True)
    show "double_reverse_birth_right_step strip first births =
      double_reverse_birth_right_step strip second births"
    proof (rule nth_equalityI)
      show "length (double_reverse_birth_right_step strip first births) =
        length (double_reverse_birth_right_step strip second births)"
        by (simp add: double_reverse_birth_right_step_def)
    next
      fix j
      assume position: "j < length (double_reverse_birth_right_step strip first births)"
      have bound: "j < length strip"
        using position by (simp add: double_reverse_birth_right_step_def)
      show "double_reverse_birth_right_step strip first births ! j =
        double_reverse_birth_right_step strip second births ! j"
      proof (cases "j = 0")
        case True
        then show ?thesis
          using terminal_cells first_terminal second_terminal by simp
      next
        case False
        have interior: "0 < j" using False by simp
        have cell:
          "double_reverse_birth_right_cell strip first births j =
            double_reverse_birth_right_cell strip second births j"
          by (rule double_reverse_birth_right_cell_interior_independent
              [OF bound births]) (use interior in simp)
        show ?thesis
          using cell by (simp add: double_reverse_birth_right_step_nth bound)
      qed
    qed
  qed
next
  case False
  have one: "births = 1" using births False by arith
  have equal:
    "double_reverse_birth_right_step strip first births =
      double_reverse_birth_right_step strip second births"
  proof (rule nth_equalityI)
    show "length (double_reverse_birth_right_step strip first births) =
      length (double_reverse_birth_right_step strip second births)"
      by (simp add: double_reverse_birth_right_step_def)
  next
    fix j
    assume position: "j < length (double_reverse_birth_right_step strip first births)"
    have bound: "j < length strip"
      using position by (simp add: double_reverse_birth_right_step_def)
    have cell:
      "double_reverse_birth_right_cell strip first births j =
        double_reverse_birth_right_cell strip second births j"
      by (rule double_reverse_birth_right_cell_interior_independent
          [OF bound births])
        (use one in simp)
    show "double_reverse_birth_right_step strip first births ! j =
      double_reverse_birth_right_step strip second births ! j"
      using cell by (simp add: double_reverse_birth_right_step_nth bound)
  qed
  show ?thesis using equal False by simp
qed

theorem double_reverse_birth_advance_seam_iff:
  assumes left_nonempty: "birth_left_strip state \<noteq> []"
      and right_nonempty: "birth_right_strip state \<noteq> []"
  shows "double_reverse_birth_advance state first_ports =
      double_reverse_birth_advance state second_ports \<longleftrightarrow>
    double_reverse_birth_seam_gate state first_ports =
      double_reverse_birth_seam_gate state second_ports"
proof -
  have left_birth:
    "double_reverse_left_birth (birth_edge_phase state) \<le> 1"
    by (simp add: double_reverse_left_birth_def)
  have right_birth:
    "double_reverse_right_birth (birth_edge_phase state) \<le> 1"
    by (simp add: double_reverse_right_birth_def)
  have left_exact:
    "double_reverse_birth_left_step (birth_left_strip state)
        (fst first_ports) (double_reverse_left_birth (birth_edge_phase state)) =
      double_reverse_birth_left_step (birth_left_strip state)
        (fst second_ports) (double_reverse_left_birth (birth_edge_phase state))
      \<longleftrightarrow>
      (if double_reverse_left_birth (birth_edge_phase state) = 0
       then Some (double_reverse_birth_left_cell (birth_left_strip state)
          (fst first_ports) (double_reverse_left_birth (birth_edge_phase state))
          (length (birth_left_strip state) - 1)) =
        Some (double_reverse_birth_left_cell (birth_left_strip state)
          (fst second_ports) (double_reverse_left_birth (birth_edge_phase state))
          (length (birth_left_strip state) - 1))
       else None = None)"
    by (rule double_reverse_birth_left_step_seam_iff[OF left_nonempty left_birth])
  have left:
    "double_reverse_birth_left_step (birth_left_strip state)
        (fst first_ports) (double_reverse_left_birth (birth_edge_phase state)) =
      double_reverse_birth_left_step (birth_left_strip state)
        (fst second_ports) (double_reverse_left_birth (birth_edge_phase state))
      \<longleftrightarrow>
      double_reverse_birth_left_seam_output state (fst first_ports) =
      double_reverse_birth_left_seam_output state (fst second_ports)"
  proof (cases "double_reverse_left_birth (birth_edge_phase state) = 0")
    case True
    then show ?thesis using left_exact
      by (simp add: double_reverse_birth_left_seam_output_def)
  next
    case False
    have one: "double_reverse_left_birth (birth_edge_phase state) = 1"
      using left_birth False by arith
    show ?thesis using left_exact False one
      by (simp add: double_reverse_birth_left_seam_output_def)
  qed
  have right_exact:
    "double_reverse_birth_right_step (birth_right_strip state)
        (snd first_ports) (double_reverse_right_birth (birth_edge_phase state)) =
      double_reverse_birth_right_step (birth_right_strip state)
        (snd second_ports) (double_reverse_right_birth (birth_edge_phase state))
      \<longleftrightarrow>
      (if double_reverse_right_birth (birth_edge_phase state) = 0
       then Some (double_reverse_birth_right_cell (birth_right_strip state)
          (snd first_ports) (double_reverse_right_birth (birth_edge_phase state)) 0) =
        Some (double_reverse_birth_right_cell (birth_right_strip state)
          (snd second_ports) (double_reverse_right_birth (birth_edge_phase state)) 0)
       else None = None)"
    by (rule double_reverse_birth_right_step_seam_iff[OF right_nonempty right_birth])
  have right:
    "double_reverse_birth_right_step (birth_right_strip state)
        (snd first_ports) (double_reverse_right_birth (birth_edge_phase state)) =
      double_reverse_birth_right_step (birth_right_strip state)
        (snd second_ports) (double_reverse_right_birth (birth_edge_phase state))
      \<longleftrightarrow>
      double_reverse_birth_right_seam_output state (snd first_ports) =
      double_reverse_birth_right_seam_output state (snd second_ports)"
  proof (cases "double_reverse_right_birth (birth_edge_phase state) = 0")
    case True
    then show ?thesis using right_exact
      by (simp add: double_reverse_birth_right_seam_output_def)
  next
    case False
    have one: "double_reverse_right_birth (birth_edge_phase state) = 1"
      using right_birth False by arith
    show ?thesis using right_exact False one
      by (simp add: double_reverse_birth_right_seam_output_def)
  qed
  show ?thesis
    using left right
    by (simp add: double_reverse_birth_advance_def
        double_reverse_birth_seam_gate_def)
qed

ML \<open>
  val checked = @{thms double_reverse_birth_left_digit_below_independent
    double_reverse_birth_right_digit_nonnegative_independent
    double_reverse_birth_left_cell_interior_independent
    double_reverse_birth_right_cell_interior_independent
    double_reverse_birth_left_step_nth
    double_reverse_birth_right_step_nth
    double_reverse_birth_left_step_seam_iff
    double_reverse_birth_right_step_seam_iff
    double_reverse_birth_advance_seam_iff};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Double-reverse seam quotient depends on an oracle";
\<close>

end
