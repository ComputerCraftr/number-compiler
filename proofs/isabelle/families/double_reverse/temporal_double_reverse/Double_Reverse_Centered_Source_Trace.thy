theory Double_Reverse_Centered_Source_Trace
  imports Double_Reverse_Centered_Word_Action
begin

text \<open>A bounded driver word is extracted from successive packed-row
windows.  Each word element owns two packed updates, hence four physical
updates.  The source-window bridge below preserves the finite halo and does
not confer recurrence or infinite-period authority.\<close>

fun double_reverse_center_driver_word_from_row ::
    "nat \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow>
      double_reverse_center_four_driver list" where
  "double_reverse_center_driver_word_from_row 0 row position = []"
| "double_reverse_center_driver_word_from_row (Suc blocks) row position =
    double_reverse_center_four_driver_from_row row (position + 2 * blocks) #
      double_reverse_center_driver_word_from_row blocks
        (double_reverse_packed_row_run 2 row) position"

lemma double_reverse_center_driver_word_from_row_length:
  "length (double_reverse_center_driver_word_from_row blocks row position) =
    blocks"
  by (induction blocks arbitrary: row) simp_all

lemma double_reverse_packed_row_run_add:
  "double_reverse_packed_row_run (first + second) row =
    double_reverse_packed_row_run second
      (double_reverse_packed_row_run first row)"
proof (induction first arbitrary: second row)
  case 0
  then show ?case by simp
next
  case (Suc first)
  have nested:
    "double_reverse_packed_row_run (first + second)
        (double_reverse_packed_row_step row) =
      double_reverse_packed_row_run second
        (double_reverse_packed_row_run first
          (double_reverse_packed_row_step row))"
    by (rule Suc.IH)
  show ?case using nested by simp
qed

lemma double_reverse_packed_row_run_decimal:
  assumes decimal: "double_reverse_decimal_row row"
  shows "double_reverse_decimal_row
    (double_reverse_packed_row_run steps row)"
  using decimal
proof (induction steps arbitrary: row)
  case 0
  then show ?case by simp
next
  case (Suc steps)
  have child_decimal:
    "double_reverse_decimal_row
      (double_reverse_packed_row_run steps
        (double_reverse_packed_row_step row))"
    by (rule Suc.IH[OF double_reverse_packed_row_step_decimal])
  show ?case using child_decimal by simp
qed

theorem double_reverse_center_driver_word_from_row_is_valid:
  assumes extent: "position + 4 * blocks < length row"
      and decimal: "double_reverse_decimal_row row"
  shows "double_reverse_center_driver_word_valid
    (double_reverse_center_driver_word_from_row blocks row position)"
  using extent decimal
proof (induction blocks arbitrary: row)
  case 0
  then show ?case by simp
next
  case (Suc blocks)
  let ?driver_position = "position + 2 * blocks"
  let ?next_row = "double_reverse_packed_row_run 2 row"
  have driver_extent: "?driver_position + 4 < length row"
    using Suc.prems(1) by arith
  have driver_valid:
    "double_reverse_center_four_driver_valid
      (double_reverse_center_four_driver_from_row row ?driver_position)"
    by (rule double_reverse_center_four_driver_from_row_valid
      [OF driver_extent Suc.prems(2)])
  have enough: "4 \<le> length row"
    using Suc.prems(1) by arith
  have enough_two: "2 * 2 \<le> length row"
    using enough by simp
  have length_next: "length ?next_row = length row - 4"
  proof -
    have "length ?next_row = length row - 2 * 2"
      by (rule double_reverse_packed_row_run_length[OF enough_two])
    then show ?thesis by simp
  qed
  have next_extent: "position + 4 * blocks < length ?next_row"
    using Suc.prems(1) length_next by arith
  have next_decimal: "double_reverse_decimal_row ?next_row"
    by (rule double_reverse_packed_row_run_decimal[OF Suc.prems(2)])
  have rest_valid:
    "double_reverse_center_driver_word_valid
      (double_reverse_center_driver_word_from_row blocks ?next_row position)"
    by (rule Suc.IH[OF next_extent next_decimal])
  show ?case using driver_valid rest_valid by simp
qed

theorem double_reverse_center_driver_word_from_row_exact:
  assumes extent: "position + 4 * blocks < length row"
      and decimal: "double_reverse_decimal_row row"
  shows "double_reverse_center_driver_word_result
      (row ! (position + 2 * blocks))
      (double_reverse_center_driver_word_from_row blocks row position) =
    double_reverse_packed_row_run (2 * blocks) row ! position"
  using extent decimal
proof (induction blocks arbitrary: row)
  case 0
  then show ?case
    by (simp add: double_reverse_center_driver_word_result_def)
next
  case (Suc blocks)
  let ?driver_position = "position + 2 * blocks"
  let ?driver =
    "double_reverse_center_four_driver_from_row row ?driver_position"
  let ?next_row = "double_reverse_packed_row_run 2 row"
  let ?rest =
    "double_reverse_center_driver_word_from_row blocks ?next_row position"
  have driver_extent: "?driver_position + 4 < length row"
    using Suc.prems(1) by arith
  have driver_exact:
    "double_reverse_center_four_result
        (row ! (?driver_position + 2)) ?driver =
      double_reverse_packed_row_run 2 row ! ?driver_position"
    by (rule double_reverse_center_four_driver_source_row_refines
      [OF driver_extent Suc.prems(2)])
  have enough: "4 \<le> length row"
    using Suc.prems(1) by arith
  have enough_two: "2 * 2 \<le> length row"
    using enough by simp
  have length_next: "length ?next_row = length row - 4"
  proof -
    have "length ?next_row = length row - 2 * 2"
      by (rule double_reverse_packed_row_run_length[OF enough_two])
    then show ?thesis by simp
  qed
  have next_extent: "position + 4 * blocks < length ?next_row"
    using Suc.prems(1) length_next by arith
  have next_decimal: "double_reverse_decimal_row ?next_row"
    by (rule double_reverse_packed_row_run_decimal[OF Suc.prems(2)])
  have rest_exact:
    "double_reverse_center_driver_word_result
        (?next_row ! (position + 2 * blocks)) ?rest =
      double_reverse_packed_row_run (2 * blocks) ?next_row ! position"
    by (rule Suc.IH[OF next_extent next_decimal])
  have one_driver:
    "double_reverse_center_driver_word_result
        (row ! (?driver_position + 2)) [?driver] =
      double_reverse_center_four_result
        (row ! (?driver_position + 2)) ?driver"
    by (simp add: double_reverse_center_driver_word_result_def
        double_reverse_center_driver_ports_word.simps
        double_reverse_center_four_result_def)
  have joined:
    "double_reverse_center_driver_word_result
        (row ! (position + 2 * Suc blocks))
        (double_reverse_center_driver_word_from_row
          (Suc blocks) row position) =
      double_reverse_center_driver_word_result
        (double_reverse_packed_row_run 2 row ! ?driver_position) ?rest"
  proof -
    have start: "position + 2 * Suc blocks = ?driver_position + 2"
      by (simp add: algebra_simps)
    have append:
      "double_reverse_center_driver_word_result
          (row ! (?driver_position + 2)) ([?driver] @ ?rest) =
        double_reverse_center_driver_word_result
          (double_reverse_center_driver_word_result
            (row ! (?driver_position + 2)) [?driver]) ?rest"
      by (rule double_reverse_center_driver_word_result_append)
    show ?thesis using append one_driver driver_exact start by simp
  qed
  have run_join:
    "double_reverse_packed_row_run (2 * blocks) ?next_row ! position =
      double_reverse_packed_row_run (2 * Suc blocks) row ! position"
  proof -
    have run_add:
      "double_reverse_packed_row_run (2 + 2 * blocks) row =
        double_reverse_packed_row_run (2 * blocks) ?next_row"
      by (rule double_reverse_packed_row_run_add)
    have exponent: "2 + 2 * blocks = 2 * Suc blocks" by simp
    show ?thesis by (simp only: run_add[symmetric] exponent)
  qed
  show ?case using joined rest_exact run_join by simp
qed

theorem double_reverse_center_driver_word_from_source_window_exact:
  assumes part:
      "double_reverse_source_slp_word middle =
        take (double_reverse_source_window_middle_length source
          (origin - int (2 * blocks)) (2 * (2 * blocks) + 1))
          (drop (double_reverse_source_window_first
            (origin - int (2 * blocks))) source)"
      and decimal:
        "double_reverse_decimal_row
          (double_reverse_pointed_source_window source origin (2 * blocks))"
  shows "double_reverse_center_driver_word_valid
      (double_reverse_center_driver_word_from_row blocks
        (double_reverse_source_slp_word
          (double_reverse_source_window_slp source
            (origin - int (2 * blocks)) (2 * (2 * blocks) + 1) middle)) 0) \<and>
    double_reverse_center_driver_word_result
      (double_reverse_source_slp_word
        (double_reverse_source_window_slp source
          (origin - int (2 * blocks)) (2 * (2 * blocks) + 1) middle) !
          (2 * blocks))
      (double_reverse_center_driver_word_from_row blocks
        (double_reverse_source_slp_word
          (double_reverse_source_window_slp source
            (origin - int (2 * blocks)) (2 * (2 * blocks) + 1) middle)) 0) =
    double_reverse_packed_row_run (2 * blocks)
      (double_reverse_pointed_source_window source origin (2 * blocks)) ! 0"
proof -
  let ?row = "double_reverse_pointed_source_window source origin (2 * blocks)"
  let ?slp_row = "double_reverse_source_slp_word
    (double_reverse_source_window_slp source
      (origin - int (2 * blocks)) (2 * (2 * blocks) + 1) middle)"
  have extracted: "?slp_row = ?row"
    by (rule double_reverse_pointed_source_window_slp_exact[OF part])
  have extent: "0 + 4 * blocks < length ?row"
    by (simp add: double_reverse_pointed_source_window_length; arith)
  have valid:
    "double_reverse_center_driver_word_valid
      (double_reverse_center_driver_word_from_row blocks ?row 0)"
    by (rule double_reverse_center_driver_word_from_row_is_valid
      [OF extent decimal])
  have exact:
    "double_reverse_center_driver_word_result (?row ! (0 + 2 * blocks))
      (double_reverse_center_driver_word_from_row blocks ?row 0) =
      double_reverse_packed_row_run (2 * blocks) ?row ! 0"
    by (rule double_reverse_center_driver_word_from_row_exact
      [OF extent decimal])
  show ?thesis using valid exact extracted by simp
qed

theorem double_reverse_center_source_window_weighted_endpoint:
  assumes part:
      "double_reverse_source_slp_word middle =
        take (double_reverse_source_window_middle_length source
          (origin - int (2 * blocks)) (2 * (2 * blocks) + 1))
          (drop (double_reverse_source_window_first
            (origin - int (2 * blocks))) source)"
      and decimal:
        "double_reverse_decimal_row
          (double_reverse_pointed_source_window source origin (2 * blocks))"
  shows "double_reverse_packed_row_run (2 * blocks)
      (double_reverse_pointed_source_window source origin (2 * blocks)) ! 0 =
    (16 ^ blocks *
        (double_reverse_pointed_source_window source origin (2 * blocks) !
          (2 * blocks)) +
      double_reverse_center_weighted_mod10
        (double_reverse_center_driver_forcing_word
          (double_reverse_pointed_source_window source origin (2 * blocks) !
            (2 * blocks))
          (double_reverse_center_driver_word_from_row blocks
            (double_reverse_pointed_source_window source origin (2 * blocks)) 0)))
      mod 10"
proof -
  let ?row = "double_reverse_pointed_source_window source origin (2 * blocks)"
  let ?slp_row = "double_reverse_source_slp_word
    (double_reverse_source_window_slp source
      (origin - int (2 * blocks)) (2 * (2 * blocks) + 1) middle)"
  have extracted: "?slp_row = ?row"
    by (rule double_reverse_pointed_source_window_slp_exact[OF part])
  have slp_length: "length ?slp_row = 2 * (2 * blocks) + 1"
    using extracted by (simp add: double_reverse_pointed_source_window_length)
  have center_index: "2 * blocks < length ?slp_row"
    using slp_length by arith
  have decimal_slp: "double_reverse_decimal_row ?slp_row"
    using decimal extracted by simp
  have center_slp: "?slp_row ! (2 * blocks) < 10"
    using decimal_slp center_index
    unfolding double_reverse_decimal_row_def by blast
  have bridge:
    "double_reverse_center_driver_word_valid
        (double_reverse_center_driver_word_from_row blocks ?slp_row 0) \<and>
      double_reverse_center_driver_word_result
        (?slp_row ! (2 * blocks))
        (double_reverse_center_driver_word_from_row blocks ?slp_row 0) =
      double_reverse_packed_row_run (2 * blocks) ?row ! 0"
    by (rule double_reverse_center_driver_word_from_source_window_exact
      [OF part decimal])
  have drivers:
    "double_reverse_center_driver_word_valid
      (double_reverse_center_driver_word_from_row blocks ?slp_row 0)"
    using bridge by simp
  have weighted_exact:
    "double_reverse_center_driver_word_result (?slp_row ! (2 * blocks))
      (double_reverse_center_driver_word_from_row blocks ?slp_row 0) =
    (16 ^ length (double_reverse_center_driver_word_from_row blocks
        ?slp_row 0) * (?slp_row ! (2 * blocks)) +
      double_reverse_center_weighted_mod10
        (double_reverse_center_driver_forcing_word
          (?slp_row ! (2 * blocks))
          (double_reverse_center_driver_word_from_row blocks ?slp_row 0)))
      mod 10"
    by (rule double_reverse_center_driver_word_weighted_mod10
      [OF center_slp drivers])
  have word_length:
    "length (double_reverse_center_driver_word_from_row blocks ?slp_row 0) =
      blocks"
    by (rule double_reverse_center_driver_word_from_row_length)
  have weighted:
    "double_reverse_center_driver_word_result (?slp_row ! (2 * blocks))
      (double_reverse_center_driver_word_from_row blocks ?slp_row 0) =
    (16 ^ blocks * (?slp_row ! (2 * blocks)) +
      double_reverse_center_weighted_mod10
        (double_reverse_center_driver_forcing_word
          (?slp_row ! (2 * blocks))
          (double_reverse_center_driver_word_from_row blocks ?slp_row 0)))
      mod 10"
    using weighted_exact word_length by simp
  show ?thesis using weighted bridge extracted by simp
qed

ML \<open>
  val checked = @{thms double_reverse_center_driver_word_from_row_length
    double_reverse_packed_row_run_add
    double_reverse_packed_row_run_decimal
    double_reverse_center_driver_word_from_row_is_valid
    double_reverse_center_driver_word_from_row_exact
    double_reverse_center_driver_word_from_source_window_exact
    double_reverse_center_source_window_weighted_endpoint};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Double-reverse centered source trace depends on an oracle";
  val _ = if Thm_Deps.has_skip_proof checked
    then error "Skipped double-reverse centered source trace proof" else ();
\<close>

end
