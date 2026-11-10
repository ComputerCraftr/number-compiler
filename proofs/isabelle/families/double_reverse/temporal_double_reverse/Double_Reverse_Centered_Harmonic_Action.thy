theory Double_Reverse_Centered_Harmonic_Action
  imports Double_Reverse_F5_Action_Power
    Double_Reverse_Source_Window_Refinement
    Double_Reverse_Centered_Half_Mod11
begin

text \<open>A four-step center driver is an explicit finite pair of adjacent
open-stencil ports.  The definitions below expand those ports through the
actual first-pass and T-squared digit rules.  They do not issue a source
certificate, infer a future driver, or authorize repetition.\<close>

record double_reverse_center_four_driver =
  double_reverse_center_left_1 :: nat
  double_reverse_center_right_1 :: nat
  double_reverse_center_left_2 :: nat
  double_reverse_center_right_2 :: nat

definition double_reverse_center_four_ports ::
    "double_reverse_center_four_driver \<Rightarrow> (nat \<times> nat) list" where
  "double_reverse_center_four_ports driver =
    [(double_reverse_center_left_1 driver,
      double_reverse_center_right_1 driver),
     (double_reverse_center_left_2 driver,
      double_reverse_center_right_2 driver)]"

definition double_reverse_center_four_middle ::
    "nat \<Rightarrow> double_reverse_center_four_driver \<Rightarrow> nat" where
  "double_reverse_center_four_middle center driver =
    double_reverse_t2_digit
      (double_reverse_center_left_1 driver) center
      (double_reverse_center_right_1 driver)"

definition double_reverse_center_four_result ::
    "nat \<Rightarrow> double_reverse_center_four_driver \<Rightarrow> nat" where
  "double_reverse_center_four_result center driver =
    double_reverse_open_stencil_trace center
      (double_reverse_center_four_ports driver)"

definition double_reverse_center_four_forcing ::
    "nat \<Rightarrow> double_reverse_center_four_driver \<Rightarrow> nat" where
  "double_reverse_center_four_forcing center driver =
    8 * threshold5_digit (double_reverse_center_left_1 driver) +
    4 * double_reverse_f5_bool_value
      (double_reverse_f5_second_carry center
        (double_reverse_center_right_1 driver)) +
    2 * threshold5_digit (double_reverse_center_left_2 driver) +
    double_reverse_f5_bool_value
      (double_reverse_f5_second_carry
        (double_reverse_center_four_middle center driver)
        (double_reverse_center_right_2 driver))"

definition double_reverse_center_four_driver_valid ::
    "double_reverse_center_four_driver \<Rightarrow> bool" where
  "double_reverse_center_four_driver_valid driver \<longleftrightarrow>
    double_reverse_center_left_1 driver < 10 \<and>
    double_reverse_center_right_1 driver < 10 \<and>
    double_reverse_center_left_2 driver < 10 \<and>
    double_reverse_center_right_2 driver < 10"

definition double_reverse_center_four_driver_from_row ::
    "nat list \<Rightarrow> nat \<Rightarrow> double_reverse_center_four_driver" where
  "double_reverse_center_four_driver_from_row row position =
    \<lparr>double_reverse_center_left_1 = row ! (position + 1),
     double_reverse_center_right_1 = row ! (position + 3),
     double_reverse_center_left_2 =
       double_reverse_packed_row_step row ! position,
     double_reverse_center_right_2 =
       double_reverse_packed_row_step row ! (position + 2)\<rparr>"

lemma double_reverse_center_four_ports_valid:
  assumes "double_reverse_center_four_driver_valid driver"
  shows "double_reverse_open_inputs_valid
    (double_reverse_center_four_ports driver)"
  using assms
  by (simp add: double_reverse_center_four_driver_valid_def
      double_reverse_center_four_ports_def
      double_reverse_open_inputs_valid_def)

lemma double_reverse_center_four_driver_from_row_ports:
  "double_reverse_center_four_ports
      (double_reverse_center_four_driver_from_row row position) =
    double_reverse_packed_row_ports 2 row position"
proof -
  have two: "(2::nat) = Suc (Suc 0)"
    by simp
  have step_count:
    "double_reverse_packed_row_ports 2 row position =
      double_reverse_packed_row_ports (Suc (Suc 0)) row position"
    by (rule arg_cong[OF two])
  have expanded:
    "double_reverse_packed_row_ports (Suc (Suc 0)) row position =
      [(row ! (position + 1), row ! (position + 3)),
       (double_reverse_packed_row_step row ! position,
        double_reverse_packed_row_step row ! (position + 2))]"
  proof -
    have position_three:
      "position + 3 = Suc (Suc (Suc position))"
      by simp
    show ?thesis
      by (simp add: double_reverse_packed_row_ports.simps position_three)
  qed
  have ports_two:
    "double_reverse_packed_row_ports 2 row position =
      [(row ! (position + 1), row ! (position + 3)),
       (double_reverse_packed_row_step row ! position,
        double_reverse_packed_row_step row ! (position + 2))]"
    by (rule trans[OF step_count expanded])
  show ?thesis
    by (simp add: double_reverse_center_four_ports_def
        double_reverse_center_four_driver_from_row_def ports_two)
qed

lemma double_reverse_center_four_driver_from_row_valid:
  assumes halo: "position + 4 < length row"
      and decimal: "double_reverse_decimal_row row"
  shows "double_reverse_center_four_driver_valid
      (double_reverse_center_four_driver_from_row row position)"
proof -
  have ports:
    "double_reverse_open_inputs_valid
      (double_reverse_packed_row_ports 2 row position)"
  proof -
    have halo4: "position + 2 * 2 < length row"
      using halo by simp
    show ?thesis
      by (rule double_reverse_f5_packed_row_ports_valid[OF halo4 decimal])
  qed
  have same:
    "double_reverse_center_four_ports
        (double_reverse_center_four_driver_from_row row position) =
      double_reverse_packed_row_ports 2 row position"
    by (rule double_reverse_center_four_driver_from_row_ports)
  have driver_ports:
    "double_reverse_open_inputs_valid
      (double_reverse_center_four_ports
        (double_reverse_center_four_driver_from_row row position))"
    by (subst same, rule ports)
  show ?thesis
    using driver_ports
    by (simp add: double_reverse_center_four_driver_valid_def
        double_reverse_center_four_ports_def
        double_reverse_open_inputs_valid_def
        double_reverse_center_four_driver_from_row_def)
qed

theorem double_reverse_center_four_driver_source_row_refines:
  assumes halo: "position + 4 < length row"
      and decimal: "double_reverse_decimal_row row"
  shows "double_reverse_center_four_result (row ! (position + 2))
      (double_reverse_center_four_driver_from_row row position) =
    double_reverse_packed_row_run 2 row ! position"
proof -
  have point:
    "double_reverse_packed_row_run 2 row ! position =
      double_reverse_open_stencil_trace (row ! (position + 2))
        (double_reverse_packed_row_ports 2 row position)"
  proof -
    have halo4: "position + 2 * 2 < length row"
      using halo by simp
    show ?thesis
      by (rule double_reverse_packed_row_point_is_open_trace[OF halo4 decimal])
  qed
  have ports:
    "double_reverse_center_four_ports
        (double_reverse_center_four_driver_from_row row position) =
      double_reverse_packed_row_ports 2 row position"
    by (rule double_reverse_center_four_driver_from_row_ports)
  show ?thesis
    using point ports
    by (simp add: double_reverse_center_four_result_def)
qed

theorem double_reverse_center_four_driver_pointed_source_window_refines:
  assumes part:
      "double_reverse_source_slp_word middle =
        take (double_reverse_source_window_middle_length source
          (origin - int radius) (2 * radius + 1))
          (drop (double_reverse_source_window_first
            (origin - int radius)) source)"
      and halo:
        "position + 4 < length
          (double_reverse_pointed_source_window source origin radius)"
      and decimal:
        "double_reverse_decimal_row
          (double_reverse_pointed_source_window source origin radius)"
  shows "double_reverse_center_four_result
      (double_reverse_source_slp_word
        (double_reverse_source_window_slp source
          (origin - int radius) (2 * radius + 1) middle) ! (position + 2))
      (double_reverse_center_four_driver_from_row
        (double_reverse_source_slp_word
          (double_reverse_source_window_slp source
            (origin - int radius) (2 * radius + 1) middle)) position) =
    double_reverse_packed_row_run 2
      (double_reverse_pointed_source_window source origin radius) ! position"
proof -
  let ?row = "double_reverse_source_slp_word
    (double_reverse_source_window_slp source
      (origin - int radius) (2 * radius + 1) middle)"
  let ?pointed = "double_reverse_pointed_source_window source origin radius"
  have extracted:
    "?row = ?pointed"
    by (rule double_reverse_pointed_source_window_slp_exact[OF part])
  have row_halo: "position + 4 < length ?row"
    using halo extracted by simp
  have row_decimal: "double_reverse_decimal_row ?row"
    using decimal extracted by simp
  have row_action:
    "double_reverse_center_four_result (?row ! (position + 2))
      (double_reverse_center_four_driver_from_row ?row position) =
      double_reverse_packed_row_run 2 ?row ! position"
    by (rule double_reverse_center_four_driver_source_row_refines
      [OF row_halo row_decimal])
  show ?thesis using row_action extracted by simp
qed

theorem double_reverse_center_four_driver_one_pointed_window_refines:
  assumes part:
      "double_reverse_source_slp_word middle =
        take (double_reverse_source_window_middle_length source
          (origin - int 2) 5)
          (drop (double_reverse_source_window_first (origin - int 2)) source)"
      and decimal:
        "double_reverse_decimal_row
          (double_reverse_pointed_source_window source origin 2)"
  shows "double_reverse_center_four_result
      (double_reverse_source_slp_word
        (double_reverse_source_window_slp source (origin - int 2) 5 middle) ! 2)
      (double_reverse_center_four_driver_from_row
        (double_reverse_source_slp_word
          (double_reverse_source_window_slp source (origin - int 2) 5 middle)) 0) =
    double_reverse_packed_window_crop
      (double_reverse_packed_row_run 2
        (double_reverse_pointed_source_window source origin 2)) 1 ! 0"
proof -
  let ?row = "double_reverse_source_slp_word
    (double_reverse_source_window_slp source (origin - int 2) 5 middle)"
  let ?pointed = "double_reverse_pointed_source_window source origin 2"
  have extracted: "?row = ?pointed"
    using double_reverse_pointed_source_window_slp_exact[where radius=2] part
    by simp
  have row_decimal: "double_reverse_decimal_row ?row"
    using decimal extracted by simp
  have action_open:
    "double_reverse_center_four_result (?row ! 2)
      (double_reverse_center_four_driver_from_row ?row 0) =
      double_reverse_open_stencil_trace (?row ! 2)
        (double_reverse_packed_row_ports 2 ?row 0)"
    by (simp add: double_reverse_center_four_result_def
        double_reverse_center_four_driver_from_row_ports)
  have crop_open:
    "double_reverse_packed_window_crop
        (double_reverse_packed_row_run 2 ?row) 1 ! 0 =
      double_reverse_open_stencil_trace (?row ! 2)
        (double_reverse_packed_row_ports 2 ?row 0)"
  proof -
    have source_window: "length ?row = 2 * (2 + 1 div 2) + 1"
      using extracted by (simp add: double_reverse_pointed_source_window_length)
    have crop_raw:
      "double_reverse_packed_window_crop
          (double_reverse_packed_row_run 2 ?row) 1 ! 0 =
        double_reverse_open_stencil_trace
          (?row ! (0 + (if even (1::nat) then 1 else 0) + 2))
          (double_reverse_packed_row_ports 2 ?row
            (0 + (if even (1::nat) then 1 else 0)))"
    proof (rule double_reverse_packed_window_point_refines_open_trace
        [where steps=2 and count=1 and i=0])
      show "(0::nat) < 1" by simp
      show "length ?row = 2 * (2 + 1 div 2) + 1"
        by (rule source_window)
      show "(0::nat) < 1" by simp
      show "double_reverse_decimal_row ?row"
        by (rule row_decimal)
    qed
    have center_position:
      "(0::nat) + (if even (1::nat) then 1 else 0) + 2 = 2"
      by simp
    have port_position:
      "(0::nat) + (if even (1::nat) then 1 else 0) = 0"
      by simp
    have center_digit:
      "?row ! (0 + (if even (1::nat) then 1 else 0) + 2) = ?row ! 2"
      by (rule arg_cong[OF center_position])
    have ports:
      "double_reverse_packed_row_ports 2 ?row
          (0 + (if even (1::nat) then 1 else 0)) =
        double_reverse_packed_row_ports 2 ?row 0"
      by (rule arg_cong[OF port_position])
    have traces:
      "double_reverse_open_stencil_trace
          (?row ! (0 + (if even (1::nat) then 1 else 0) + 2))
          (double_reverse_packed_row_ports 2 ?row
            (0 + (if even (1::nat) then 1 else 0))) =
        double_reverse_open_stencil_trace (?row ! 2)
          (double_reverse_packed_row_ports 2 ?row 0)"
      by (rule arg_cong2[OF center_digit ports])
    show ?thesis by (rule trans[OF crop_raw traces])
  qed
  show ?thesis
    using action_open crop_open extracted by simp
qed

lemma double_reverse_center_four_expands_physical_digits:
  "double_reverse_f5_physical_digit_path center
      (double_reverse_center_four_ports driver) =
    [center,
     double_reverse_first_pass_cell
       (double_reverse_center_left_1 driver) center,
     double_reverse_center_four_middle center driver,
     double_reverse_first_pass_cell
       (double_reverse_center_left_2 driver)
       (double_reverse_center_four_middle center driver),
     double_reverse_center_four_result center driver]"
  by (simp add: double_reverse_f5_physical_digit_path.simps
      double_reverse_center_four_ports_def
      double_reverse_center_four_middle_def
      double_reverse_center_four_result_def
      double_reverse_open_stencil_trace.simps)

lemma double_reverse_center_affine_four_compose:
  fixes center h1 l1 h2 l2 :: nat
  shows
    "(4 * ((4 * center + 2 * h1 + l1) mod 10) +
        2 * h2 + l2) mod 10 =
      (16 * center + 8 * h1 + 4 * l1 + 2 * h2 + l2) mod 10"
proof -
  let ?inner = "4 * center + 2 * h1 + l1"
  let ?tail = "2 * h2 + l2"
  have inner_mod: "(?inner mod 10) mod 10 = ?inner mod 10"
    by simp
  have product:
    "(4 * (?inner mod 10)) mod 10 = (4 * ?inner) mod 10"
    by (rule mod_mult_cong[OF refl inner_mod])
  have joined:
    "(4 * (?inner mod 10) + ?tail) mod 10 =
      (4 * ?inner + ?tail) mod 10"
    by (rule mod_add_cong[OF product refl])
  have expanded:
    "4 * ?inner + ?tail =
      16 * center + 8 * h1 + 4 * l1 + 2 * h2 + l2"
    by (simp add: algebra_simps)
  show ?thesis using joined expanded by (simp add: add.assoc)
qed

lemma double_reverse_center_four_result_bounded:
  "double_reverse_center_four_result center driver < 10"
  unfolding double_reverse_center_four_result_def
    double_reverse_center_four_ports_def
  by (simp add: double_reverse_open_stencil_trace.simps
      double_reverse_t2_output_bounded)

theorem double_reverse_center_forced_four_physical_steps:
  assumes center: "center < 10"
      and driver: "double_reverse_center_four_driver_valid driver"
  shows "double_reverse_center_four_result center driver =
    (16 * center + double_reverse_center_four_forcing center driver) mod 10"
proof -
  let ?left1 = "double_reverse_center_left_1 driver"
  let ?right1 = "double_reverse_center_right_1 driver"
  let ?left2 = "double_reverse_center_left_2 driver"
  let ?right2 = "double_reverse_center_right_2 driver"
  let ?middle = "double_reverse_center_four_middle center driver"
  let ?carry1 =
    "double_reverse_f5_bool_value
      (double_reverse_f5_second_carry center ?right1)"
  let ?carry3 =
    "double_reverse_f5_bool_value
      (double_reverse_f5_second_carry ?middle ?right2)"
  have left1: "?left1 < 10"
    using driver by (simp add: double_reverse_center_four_driver_valid_def)
  have right1: "?right1 < 10"
    using driver by (simp add: double_reverse_center_four_driver_valid_def)
  have left2: "?left2 < 10"
    using driver by (simp add: double_reverse_center_four_driver_valid_def)
  have right2: "?right2 < 10"
    using driver by (simp add: double_reverse_center_four_driver_valid_def)
  have middle_bound: "?middle < 10"
    unfolding double_reverse_center_four_middle_def
    by (rule double_reverse_t2_output_bounded)
  have middle_exact:
    "?middle =
      (4 * center + 2 * threshold5_digit ?left1 + ?carry1) mod 10"
  proof -
    have stencil:
      "double_reverse_t2_digit ?left1 center ?right1 =
        (4 * center + 2 * (if 5 \<le> ?left1 then 1 else 0) +
          (if ?right1 mod 5 = 3 \<or> ?right1 mod 5 = 4 then 1 else 0) +
          (if 5 \<le> center \<and> ?right1 mod 5 = 2 then 1 else 0)) mod 10"
      by (rule double_reverse_t2_open_stencil_exact[OF left1 center right1])
    show ?thesis
      using stencil
      by (simp add: double_reverse_center_four_middle_def
          double_reverse_f5_second_carry_def
          double_reverse_f5_bool_value_def threshold5_digit_def)
  qed
  have result_exact:
    "double_reverse_center_four_result center driver =
      (4 * ?middle + 2 * threshold5_digit ?left2 + ?carry3) mod 10"
  proof -
    have stencil:
      "double_reverse_t2_digit ?left2 ?middle ?right2 =
        (4 * ?middle + 2 * (if 5 \<le> ?left2 then 1 else 0) +
          (if ?right2 mod 5 = 3 \<or> ?right2 mod 5 = 4 then 1 else 0) +
          (if 5 \<le> ?middle \<and> ?right2 mod 5 = 2 then 1 else 0)) mod 10"
      by (rule double_reverse_t2_open_stencil_exact[OF left2 middle_bound right2])
    show ?thesis
      using stencil
      by (simp add: double_reverse_center_four_result_def
          double_reverse_center_four_ports_def
          double_reverse_open_stencil_trace.simps
          double_reverse_center_four_middle_def
          double_reverse_f5_second_carry_def
          double_reverse_f5_bool_value_def threshold5_digit_def)
  qed
  have composed:
    "(4 * ?middle + 2 * threshold5_digit ?left2 + ?carry3) mod 10 =
      (16 * center + 8 * threshold5_digit ?left1 + 4 * ?carry1 +
        2 * threshold5_digit ?left2 + ?carry3) mod 10"
  proof -
    have outer_middle:
      "\<And>tail. (4 * ?middle + 2 * threshold5_digit ?left2 + tail) mod 10 =
        (4 * ((4 * center + 2 * threshold5_digit ?left1 + ?carry1) mod 10) +
          2 * threshold5_digit ?left2 + tail) mod 10"
      using middle_exact by (simp only: middle_exact)
    have outer:
      "(4 * ?middle + 2 * threshold5_digit ?left2 + ?carry3) mod 10 =
        (4 * ((4 * center + 2 * threshold5_digit ?left1 + ?carry1) mod 10) +
          2 * threshold5_digit ?left2 + ?carry3) mod 10"
      by (rule outer_middle)
    have affine:
      "(4 * ((4 * center + 2 * threshold5_digit ?left1 + ?carry1) mod 10) +
          2 * threshold5_digit ?left2 + ?carry3) mod 10 =
        (16 * center + 8 * threshold5_digit ?left1 + 4 * ?carry1 +
          2 * threshold5_digit ?left2 + ?carry3) mod 10"
      by (rule double_reverse_center_affine_four_compose)
    show ?thesis by (rule trans[OF outer affine])
  qed
  show ?thesis
    using result_exact composed
    by (simp add: double_reverse_center_four_forcing_def add.assoc)
qed

theorem double_reverse_center_forced_four_step_digit_expansion:
  assumes center: "center < 10"
      and driver: "double_reverse_center_four_driver_valid driver"
  shows "double_reverse_f5_physical_digit_path center
      (double_reverse_center_four_ports driver) ! 4 =
    (16 * center + double_reverse_center_four_forcing center driver) mod 10"
  using double_reverse_center_forced_four_physical_steps[OF center driver]
  by (simp add: double_reverse_center_four_expands_physical_digits)

ML \<open>
  val checked = @{thms double_reverse_center_forced_four_physical_steps
    double_reverse_center_four_driver_from_row_valid
    double_reverse_center_four_driver_pointed_source_window_refines
    double_reverse_center_four_driver_one_pointed_window_refines
    double_reverse_center_forced_four_step_digit_expansion
    double_reverse_centered_half_mod11_uses_only_mod99
    double_reverse_centered_even_half_word_projection
    double_reverse_centered_odd_half_word_projection
    double_reverse_mod99_action_centered_half_projection};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Double-reverse centered harmonic action depends on an oracle";
  val _ = if Thm_Deps.has_skip_proof checked
    then error "Skipped double-reverse centered harmonic action proof" else ();
\<close>

end
