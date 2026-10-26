theory Double_Reverse_Outer_Port_Quotient
  imports Double_Reverse_Periodic_Ring_Action
    Double_Reverse_Birth_Seam_Quotient
begin

text \<open>
An outer-ring inlet is not generally identified by its decimal digit.  The
left inlet is observed through the right-neighbour carry of the T-squared
stencil, and the right inlet through its left-neighbour threshold.  A birth
on the corresponding side removes that inlet from the outer-ring update.
This finite one-step quotient is only for checking the supplied successor
ring; the target-producing inner pair still uses its exact inlet digits.
\<close>

definition double_reverse_outer_left_response :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "double_reverse_outer_left_response center inlet =
    (if (2*inlet + threshold5_digit center) mod 10 \<ge> 5 then 1 else 0)"

definition double_reverse_outer_right_response :: "nat \<Rightarrow> nat" where
  "double_reverse_outer_right_response inlet =
    (if 5 \<le> inlet then 1 else 0)"

lemma double_reverse_mod10_add_cancel_bounded:
  fixes base first second :: nat
  assumes first_bound: "first < 10"
      and second_bound: "second < 10"
  shows "(base + first) mod 10 = (base + second) mod 10 \<longleftrightarrow>
    first = second"
proof -
  have cancel: "(base + first) mod 10 = (base + second) mod 10 \<longleftrightarrow>
      first mod 10 = second mod 10"
  proof (cases "second \<le> first")
    case True
    have sums: "base + second \<le> base + first" using True by simp
    show ?thesis
      using mod_eq_dvd_iff_nat[OF sums, of 10]
        mod_eq_dvd_iff_nat[OF True, of 10] by simp
  next
    case False
    then have order: "first \<le> second" by simp
    have sums: "base + first \<le> base + second" using order by simp
    have reverse: "(base + second) mod 10 = (base + first) mod 10 \<longleftrightarrow>
        second mod 10 = first mod 10"
      using mod_eq_dvd_iff_nat[OF sums, of 10]
        mod_eq_dvd_iff_nat[OF order, of 10] by simp
    show ?thesis using reverse by metis
  qed
  show ?thesis using cancel first_bound second_bound by simp
qed

lemma double_reverse_outer_t2_right_response_iff:
  "double_reverse_t2_digit left center first =
      double_reverse_t2_digit left center second \<longleftrightarrow>
    double_reverse_outer_left_response center first =
      double_reverse_outer_left_response center second"
proof -
  let ?base = "4*center + 2*(if 5 \<le> left then 1 else 0)"
  have first_output:
    "double_reverse_t2_digit left center first =
      (?base + double_reverse_outer_left_response center first) mod 10"
    by (simp add: double_reverse_t2_digit_def
        double_reverse_outer_left_response_def threshold5_digit_def)
  have second_output:
    "double_reverse_t2_digit left center second =
      (?base + double_reverse_outer_left_response center second) mod 10"
    by (simp add: double_reverse_t2_digit_def
        double_reverse_outer_left_response_def threshold5_digit_def)
  have first_bound:
    "double_reverse_outer_left_response center first < 10"
    by (simp add: double_reverse_outer_left_response_def)
  have second_bound:
    "double_reverse_outer_left_response center second < 10"
    by (simp add: double_reverse_outer_left_response_def)
  have output_iff:
    "(?base + double_reverse_outer_left_response center first) mod 10 =
      (?base + double_reverse_outer_left_response center second) mod 10 \<longleftrightarrow>
     double_reverse_outer_left_response center first =
       double_reverse_outer_left_response center second"
    by (rule double_reverse_mod10_add_cancel_bounded[OF first_bound second_bound])
  show ?thesis using output_iff by (simp add: first_output second_output)
qed

lemma double_reverse_outer_t2_left_response_iff:
  "double_reverse_t2_digit first center right =
      double_reverse_t2_digit second center right \<longleftrightarrow>
    double_reverse_outer_right_response first =
      double_reverse_outer_right_response second"
proof -
  let ?carry =
    "(if (2*right + threshold5_digit center) mod 10 \<ge> 5 then 1 else 0)"
  let ?base = "4*center + ?carry"
  have first_output:
    "double_reverse_t2_digit first center right =
      (?base + 2*double_reverse_outer_right_response first) mod 10"
    by (simp add: double_reverse_t2_digit_def
        double_reverse_outer_right_response_def threshold5_digit_def algebra_simps)
  have second_output:
    "double_reverse_t2_digit second center right =
      (?base + 2*double_reverse_outer_right_response second) mod 10"
    by (simp add: double_reverse_t2_digit_def
        double_reverse_outer_right_response_def threshold5_digit_def algebra_simps)
  have first_response_bound: "double_reverse_outer_right_response first < 2"
    by (simp add: double_reverse_outer_right_response_def)
  have second_response_bound: "double_reverse_outer_right_response second < 2"
    by (simp add: double_reverse_outer_right_response_def)
  have first_bound: "2*double_reverse_outer_right_response first < 10"
    using first_response_bound by arith
  have second_bound: "2*double_reverse_outer_right_response second < 10"
    using second_response_bound by arith
  have output_iff:
    "(?base + 2*double_reverse_outer_right_response first) mod 10 =
      (?base + 2*double_reverse_outer_right_response second) mod 10 \<longleftrightarrow>
     double_reverse_outer_right_response first =
       double_reverse_outer_right_response second"
  proof -
    have bounded_iff:
      "(?base + 2*double_reverse_outer_right_response first) mod 10 =
        (?base + 2*double_reverse_outer_right_response second) mod 10 \<longleftrightarrow>
       2*double_reverse_outer_right_response first =
         2*double_reverse_outer_right_response second"
      by (rule double_reverse_mod10_add_cancel_bounded[OF first_bound second_bound])
    show ?thesis using bounded_iff by simp
  qed
  show ?thesis using output_iff by (simp add: first_output second_output)
qed

lemma double_reverse_outer_left_representative_response:
  "double_reverse_outer_left_response center
      (if double_reverse_outer_left_response center inlet = 1 then 3 else 0) =
    double_reverse_outer_left_response center inlet"
  unfolding double_reverse_outer_left_response_def threshold5_digit_def
  by (cases "5 \<le> center"; cases "5 \<le>
      (2*inlet + (if 5 \<le> center then 1 else 0)) mod 10") simp_all

lemma double_reverse_outer_right_representative_response:
  "double_reverse_outer_right_response
      (if double_reverse_outer_right_response inlet = 1 then 5 else 0) =
    double_reverse_outer_right_response inlet"
  unfolding double_reverse_outer_right_response_def by simp

definition double_reverse_outer_port_class ::
    "double_reverse_birth_state \<Rightarrow> nat \<times> nat \<Rightarrow> nat \<times> nat" where
  "double_reverse_outer_port_class state ports =
    (if double_reverse_left_birth (birth_edge_phase state) = 0
     then double_reverse_outer_left_response (last (birth_left_strip state))
       (fst ports) else 0,
     if double_reverse_right_birth (birth_edge_phase state) = 0
     then double_reverse_outer_right_response (snd ports) else 0)"

definition double_reverse_outer_port_representative ::
    "double_reverse_birth_state \<Rightarrow> nat \<times> nat \<Rightarrow> nat \<times> nat" where
  "double_reverse_outer_port_representative state ports =
    (if fst (double_reverse_outer_port_class state ports) = 1 then 3 else 0,
     if snd (double_reverse_outer_port_class state ports) = 1 then 5 else 0)"

lemma double_reverse_birth_left_seam_response_iff:
  assumes nonempty: "strip \<noteq> []"
  shows "double_reverse_birth_left_cell strip first 0 (length strip - 1) =
      double_reverse_birth_left_cell strip second 0 (length strip - 1) \<longleftrightarrow>
    double_reverse_outer_left_response (last strip) first =
      double_reverse_outer_left_response (last strip) second"
proof -
  let ?j = "length strip - 1"
  let ?before = "int ?j - 1"
  let ?center = "int ?j"
  have before_bound: "?before < int (length strip)"
    using nonempty by arith
  have center_bound: "?center < int (length strip)"
    using nonempty by simp
  have before_independent:
    "double_reverse_birth_left_digit strip first ?before =
      double_reverse_birth_left_digit strip second ?before"
    by (rule double_reverse_birth_left_digit_below_independent[OF before_bound])
  have center_independent:
    "double_reverse_birth_left_digit strip first ?center =
      double_reverse_birth_left_digit strip second ?center"
    by (rule double_reverse_birth_left_digit_below_independent[OF center_bound])
  have center_last:
    "double_reverse_birth_left_digit strip first ?center = last strip"
  proof -
    have index: "nat ?center = length strip - 1" by simp
    have nth_last: "last strip = strip ! (length strip - 1)"
      using nonempty by (simp add: last_conv_nth)
    show ?thesis
      using index nth_last center_bound nonempty
      by (simp add: double_reverse_birth_left_digit_def)
  qed
  have after: "?center + 1 = int (length strip)"
    using nonempty by (cases strip) auto
  have first_inlet:
    "double_reverse_birth_left_digit strip first (?center + 1) = first"
    unfolding after by (simp add: double_reverse_birth_left_digit_def)
  have second_inlet:
    "double_reverse_birth_left_digit strip second (?center + 1) = second"
    unfolding after by (simp add: double_reverse_birth_left_digit_def)
  have first_cell:
    "double_reverse_birth_left_cell strip first 0 ?j =
      double_reverse_t2_digit
        (double_reverse_birth_left_digit strip first ?before)
        (double_reverse_birth_left_digit strip first ?center) first"
    by (simp only: double_reverse_birth_left_cell_def of_nat_0 diff_zero first_inlet)
  have second_cell:
    "double_reverse_birth_left_cell strip second 0 ?j =
      double_reverse_t2_digit
        (double_reverse_birth_left_digit strip second ?before)
        (double_reverse_birth_left_digit strip second ?center) second"
    by (simp only: double_reverse_birth_left_cell_def of_nat_0 diff_zero second_inlet)
  show ?thesis
    using before_independent center_independent center_last
      double_reverse_outer_t2_right_response_iff[of
        "double_reverse_birth_left_digit strip first ?before"
        "double_reverse_birth_left_digit strip first ?center" first second]
    by (simp only: first_cell second_cell before_independent[symmetric]
        center_independent[symmetric] center_last)
qed

lemma double_reverse_birth_right_seam_response_iff:
  assumes nonempty: "strip \<noteq> []"
  shows "double_reverse_birth_right_cell strip first 0 0 =
      double_reverse_birth_right_cell strip second 0 0 \<longleftrightarrow>
    double_reverse_outer_right_response first =
      double_reverse_outer_right_response second"
proof -
  have center_independent:
    "double_reverse_birth_right_digit strip first 0 =
      double_reverse_birth_right_digit strip second 0"
    by (rule double_reverse_birth_right_digit_nonnegative_independent) simp
  have right_independent:
    "double_reverse_birth_right_digit strip first 1 =
      double_reverse_birth_right_digit strip second 1"
    by (rule double_reverse_birth_right_digit_nonnegative_independent) simp
  have first_cell:
    "double_reverse_birth_right_cell strip first 0 0 =
      double_reverse_t2_digit first
        (double_reverse_birth_right_digit strip first 0)
        (double_reverse_birth_right_digit strip first 1)"
    by (simp add: double_reverse_birth_right_cell_def
        double_reverse_birth_right_digit_def)
  have second_cell:
    "double_reverse_birth_right_cell strip second 0 0 =
      double_reverse_t2_digit second
        (double_reverse_birth_right_digit strip second 0)
        (double_reverse_birth_right_digit strip second 1)"
    by (simp add: double_reverse_birth_right_cell_def
        double_reverse_birth_right_digit_def)
  show ?thesis
    using center_independent right_independent nonempty
      double_reverse_outer_t2_left_response_iff[of first
        "double_reverse_birth_right_digit strip first 0"
        "double_reverse_birth_right_digit strip first 1" second]
    by (simp add: first_cell second_cell)
qed

lemma double_reverse_outer_port_seam_gate_iff:
  assumes left_nonempty: "birth_left_strip state \<noteq> []"
      and right_nonempty: "birth_right_strip state \<noteq> []"
  shows "double_reverse_birth_seam_gate state first_ports =
      double_reverse_birth_seam_gate state second_ports \<longleftrightarrow>
    double_reverse_outer_port_class state first_ports =
      double_reverse_outer_port_class state second_ports"
proof -
  have left_birth:
    "double_reverse_left_birth (birth_edge_phase state) \<le> 1"
    by (simp add: double_reverse_left_birth_def)
  have right_birth:
    "double_reverse_right_birth (birth_edge_phase state) \<le> 1"
    by (simp add: double_reverse_right_birth_def)
  have left:
    "double_reverse_birth_left_seam_output state (fst first_ports) =
        double_reverse_birth_left_seam_output state (fst second_ports) \<longleftrightarrow>
      fst (double_reverse_outer_port_class state first_ports) =
        fst (double_reverse_outer_port_class state second_ports)"
  proof (cases "double_reverse_left_birth (birth_edge_phase state) = 0")
    case True
    then show ?thesis
      using double_reverse_birth_left_seam_response_iff[OF left_nonempty,
        of "fst first_ports" "fst second_ports"]
      by (simp add: double_reverse_birth_left_seam_output_def
          double_reverse_outer_port_class_def)
  next
    case False
    then have one: "double_reverse_left_birth (birth_edge_phase state) = 1"
      using left_birth by arith
    then show ?thesis
      by (simp add: double_reverse_birth_left_seam_output_def
          double_reverse_outer_port_class_def)
  qed
  have right:
    "double_reverse_birth_right_seam_output state (snd first_ports) =
        double_reverse_birth_right_seam_output state (snd second_ports) \<longleftrightarrow>
      snd (double_reverse_outer_port_class state first_ports) =
        snd (double_reverse_outer_port_class state second_ports)"
  proof (cases "double_reverse_right_birth (birth_edge_phase state) = 0")
    case True
    then show ?thesis
      using double_reverse_birth_right_seam_response_iff[OF right_nonempty,
        of "snd first_ports" "snd second_ports"]
      by (simp add: double_reverse_birth_right_seam_output_def
          double_reverse_outer_port_class_def)
  next
    case False
    then have one: "double_reverse_right_birth (birth_edge_phase state) = 1"
      using right_birth by arith
    then show ?thesis
      by (simp add: double_reverse_birth_right_seam_output_def
          double_reverse_outer_port_class_def)
  qed
  show ?thesis
    using left right
    by (simp add: double_reverse_birth_seam_gate_def prod_eq_iff)
qed

theorem double_reverse_outer_port_advance_iff:
  assumes left_nonempty: "birth_left_strip state \<noteq> []"
      and right_nonempty: "birth_right_strip state \<noteq> []"
  shows "double_reverse_birth_advance state first_ports =
      double_reverse_birth_advance state second_ports \<longleftrightarrow>
    double_reverse_outer_port_class state first_ports =
      double_reverse_outer_port_class state second_ports"
  using double_reverse_birth_advance_seam_iff[OF left_nonempty right_nonempty]
    double_reverse_outer_port_seam_gate_iff[OF left_nonempty right_nonempty]
  by blast

theorem double_reverse_outer_port_representative_exact:
  fixes ports :: "nat \<times> nat"
  assumes left_nonempty: "birth_left_strip state \<noteq> []"
      and right_nonempty: "birth_right_strip state \<noteq> []"
  defines "representative \<equiv>
    double_reverse_outer_port_representative state ports"
  shows "double_reverse_birth_advance state ports =
    double_reverse_birth_advance state representative"
proof -
  have class_eq:
    "double_reverse_outer_port_class state ports =
      double_reverse_outer_port_class state representative"
  proof -
    have left:
      "fst (double_reverse_outer_port_class state representative) =
        fst (double_reverse_outer_port_class state ports)"
      unfolding representative_def double_reverse_outer_port_representative_def
        double_reverse_outer_port_class_def
      using double_reverse_outer_left_representative_response[of
        "last (birth_left_strip state)" "fst ports"]
      by (cases "double_reverse_left_birth (birth_edge_phase state) = 0") simp_all
    have right:
      "snd (double_reverse_outer_port_class state representative) =
        snd (double_reverse_outer_port_class state ports)"
      unfolding representative_def double_reverse_outer_port_representative_def
        double_reverse_outer_port_class_def
      using double_reverse_outer_right_representative_response[of "snd ports"]
      by (cases "double_reverse_right_birth (birth_edge_phase state) = 0") simp_all
    show ?thesis using left right by (metis prod_eqI)
  qed
  show ?thesis
    by (rule iffD2[OF double_reverse_outer_port_advance_iff[OF
        left_nonempty right_nonempty]]) (use class_eq in simp)
qed

theorem double_reverse_outer_port_row_pointwise:
  fixes ports :: "nat \<times> nat"
  assumes left_nonempty: "birth_left_strip state \<noteq> []"
      and right_nonempty: "birth_right_strip state \<noteq> []"
      and left_index: "i < length (birth_left_strip state)"
      and right_index: "j < length (birth_right_strip state)"
  defines "representative \<equiv>
    double_reverse_outer_port_representative state ports"
  shows "double_reverse_birth_left_step (birth_left_strip state)
        (fst ports) (double_reverse_left_birth (birth_edge_phase state)) ! i =
      double_reverse_birth_left_step (birth_left_strip state)
        (fst representative) (double_reverse_left_birth (birth_edge_phase state)) ! i
    \<and>
    double_reverse_birth_right_step (birth_right_strip state)
        (snd ports) (double_reverse_right_birth (birth_edge_phase state)) ! j =
      double_reverse_birth_right_step (birth_right_strip state)
        (snd representative) (double_reverse_right_birth (birth_edge_phase state)) ! j"
proof -
  have advance:
    "double_reverse_birth_advance state ports =
      double_reverse_birth_advance state representative"
    unfolding representative_def
    by (rule double_reverse_outer_port_representative_exact
        [OF left_nonempty right_nonempty])
  have left:
    "double_reverse_birth_left_step (birth_left_strip state)
        (fst ports) (double_reverse_left_birth (birth_edge_phase state)) =
      double_reverse_birth_left_step (birth_left_strip state)
        (fst representative) (double_reverse_left_birth (birth_edge_phase state))"
    using advance by (simp add: double_reverse_birth_advance_def)
  have right:
    "double_reverse_birth_right_step (birth_right_strip state)
        (snd ports) (double_reverse_right_birth (birth_edge_phase state)) =
      double_reverse_birth_right_step (birth_right_strip state)
        (snd representative) (double_reverse_right_birth (birth_edge_phase state))"
    using advance by (simp add: double_reverse_birth_advance_def)
  show ?thesis using left_index right_index left right by simp
qed

ML \<open>
  val checked = @{thms double_reverse_outer_t2_right_response_iff
    double_reverse_outer_t2_left_response_iff
    double_reverse_outer_left_representative_response
    double_reverse_outer_right_representative_response
    double_reverse_birth_left_seam_response_iff
    double_reverse_birth_right_seam_response_iff
    double_reverse_outer_port_seam_gate_iff
    double_reverse_outer_port_advance_iff
    double_reverse_outer_port_representative_exact
    double_reverse_outer_port_row_pointwise};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Double-reverse outer-port quotient depends on an oracle";
  val _ = if Thm_Deps.has_skip_proof checked
    then error "Skipped double-reverse outer-port quotient proof" else ();
\<close>

end
