theory Cylinder_Source_Coboundary
  imports Cylinder_Coboundary_Publisher
    "Reverse_Residuals.Reverse_196_Publisher_Refinement"
begin

text \<open>
  Source binding for the whole-function coboundary.  The carry function is
  reconstructed from the exact prefix fold of a finite source list; it is not
  an independently supplied carry oracle or a temporal grammar claim.
\<close>

definition source_coefficient ::
    "nat list => int => int" where
  "source_coefficient ss i =
    (if 0 \<le> i \<and> i < int (length ss)
     then int (ss ! nat i) else 0)"

definition source_carry_state ::
    "nat list => int => int" where
  "source_carry_state ss i =
    (if 0 \<le> i \<and> i \<le> int (length ss)
     then int (carry_bit (carry_out False (take (nat i) ss))) else 0)"

definition source_carry_out ::
    "nat list => int => int" where
  "source_carry_out ss i =
    (if cylinder_window (length ss) i
     then source_carry_state ss (i + 1) else 0)"

text \<open>
  The source list here is the 196 pair field, rather than the already
  emitted decimal digit stream.  Pair coefficients can be as large as 18
  (for example the live field [7,18,7]); the decimal bound belongs only to
  @{term emit}.  Keeping this distinction explicit prevents the bridge from
  silently excluding the production source.
\<close>

definition source_pair_valid :: "nat list => bool" where
  "source_pair_valid ss = (\<forall>x\<in>set ss. x < 19)"

lemma source_carry_encoding:
  "cylinder_carry_encoding (length ss) (source_carry_state ss)
      (source_carry_out ss)"
  unfolding cylinder_carry_encoding_def source_carry_out_def by simp

lemma source_initial_carry:
  "source_carry_state ss 0 = 0"
  by (simp add: source_carry_state_def carry_bit_def carry_out_def)

lemma source_prefix_step:
  assumes bound: "j < length ss"
  shows "carry_out False (take (Suc j) ss) =
    carry_apply (domain (ss ! j)) (carry_out False (take j ss))"
proof -
  have take_step: "take (Suc j) ss = take j ss @ [ss ! j]"
    using take_Suc_conv_app_nth[OF bound] .
  show ?thesis
    using take_step by (simp add: carry_out_append carry_out_def)
qed

lemma source_pair_bound:
  assumes valid: "source_pair_valid ss" and bound: "j < length ss"
  shows "ss ! j < 19"
proof -
  have member: "ss ! j \<in> set ss" using nth_mem[OF bound] .
  show ?thesis
    using valid member unfolding source_pair_valid_def by blast
qed

lemma source_pair_valid_of_valid_pair:
  assumes valid: "valid_pair ss"
  shows "source_pair_valid ss"
  using valid by (auto simp: valid_pair_def source_pair_valid_def)

lemma source_pair_symmetric_of_valid_pair:
  assumes valid: "valid_pair ss"
  shows "rev ss = ss"
  using valid by (simp add: valid_pair_def)

lemma source_pair_valid_196:
  "source_pair_valid (run step n [7,18,7])"
  using source_pair_valid_of_valid_pair all_196_pair_fields_valid by blast

lemma source_carry_at:
  assumes "j \<le> length ss"
  shows "source_carry_state ss (int j) =
    int (carry_bit (carry_out False (take j ss)))"
  using assms by (simp add: source_carry_state_def)

lemma source_local_carry_div:
  assumes "s < 19"
  shows "int (carry_bit (carry_apply (domain s) c)) =
    (int s + int (carry_bit c)) div 10"
  using assms
  by (cases c; auto simp: carry_bit_def carry_from_domain split: if_splits; arith)

lemma source_carry_step_div:
  assumes valid: "source_pair_valid ss" and bound: "j < length ss"
  shows "source_carry_state ss (int j + 1) =
    (int (ss ! j) + source_carry_state ss (int j)) div 10"
proof -
  have current: "j \<le> length ss" using bound by simp
  have following: "Suc j \<le> length ss" using bound by simp
  show ?thesis
    using source_carry_at[OF current] source_carry_at[OF following]
      source_prefix_step[OF bound]
      source_local_carry_div[OF source_pair_bound[OF valid bound],
        of "carry_out False (take j ss)"]
    by (simp add: add.commute)
qed

lemma source_carry_div_bound:
  assumes valid: "source_pair_valid ss" and bound: "j < length ss"
  shows "0 \<le> (int (ss ! j) + source_carry_state ss (int j)) div 10
      \<and> (int (ss ! j) + source_carry_state ss (int j)) div 10 \<le> 1"
proof -
  have bounds: "0 \<le> int j" "int j + 1 \<le> int (length ss)"
    using bound by arith+
  have state_bounds:
      "0 \<le> source_carry_state ss (int j + 1)
        \<and> source_carry_state ss (int j + 1) \<le> 1"
    unfolding source_carry_state_def
    using bounds by (simp add: carry_bit_def)
  have division:
      "(int (ss ! j) + source_carry_state ss (int j)) div 10 =
        source_carry_state ss (int j + 1)"
    using source_carry_step_div[OF valid bound] by simp
  have lower: "0 \<le> source_carry_state ss (int j + 1)"
    using state_bounds by blast
  have upper: "source_carry_state ss (int j + 1) \<le> 1"
    using state_bounds by blast
  show ?thesis using division lower upper by linarith
qed

lemma source_coboundary_active:
  assumes valid: "source_pair_valid ss" and bound: "j < length ss"
  shows "cylinder_normalized 10 (source_coefficient ss)
      (source_carry_out ss) (int j) =
    (int (ss ! j) +
      int (carry_bit (carry_out False (take j ss)))) mod 10"
proof -
  have active: "cylinder_window (length ss) (int j)"
    unfolding cylinder_window_def using bound by simp
  have normalized:
    "cylinder_normalized 10 (source_coefficient ss)
        (source_carry_out ss) (int j) =
      source_coefficient ss (int j) + source_carry_state ss (int j) -
        10 * source_carry_state ss (int j + 1)"
    using cylinder_normalized_active
      [OF source_carry_encoding source_initial_carry active] .
  have next_carry: "source_carry_state ss (int j + 1) =
      (int (ss ! j) + source_carry_state ss (int j)) div 10"
    using source_carry_step_div[OF valid bound] .
  have coeff:
    "source_coefficient ss (int j) = int (ss ! j)"
    unfolding source_coefficient_def using bound by simp
  have carry:
    "source_carry_state ss (int j) =
      int (carry_bit (carry_out False (take j ss)))"
    unfolding source_carry_state_def using bound by simp
  have split:
    "int (ss ! j) + int (carry_bit (carry_out False (take j ss))) =
      10 * ((int (ss ! j) +
        int (carry_bit (carry_out False (take j ss)))) div 10) +
      (int (ss ! j) +
        int (carry_bit (carry_out False (take j ss)))) mod 10"
    using div_mult_mod_eq[of
      "int (ss ! j) + int (carry_bit (carry_out False (take j ss)))" 10]
    by (simp add: algebra_simps)
  show ?thesis
    using split by (simp only: normalized next_carry coeff carry; linarith)
qed

lemma source_coefficient_nth:
  assumes bound: "j < length ss"
  shows "source_coefficient ss (int j) = int (ss ! j)"
  unfolding source_coefficient_def using bound by simp

lemma source_196_coboundary_active:
  assumes bound: "j < length (run step n [7,18,7])"
  shows "cylinder_normalized 10
      (source_coefficient (run step n [7,18,7]))
      (source_carry_out (run step n [7,18,7])) (int j) =
    (int ((run step n [7,18,7]) ! j) +
      int (carry_bit (carry_out False
        (take j (run step n [7,18,7]))))) mod 10"
  using source_coboundary_active[OF source_pair_valid_196 bound] .

lemma source_emitted_nth:
  assumes bound: "j < length ss"
  shows "emit False ss ! j =
    (ss ! j + carry_bit (carry_out False (take j ss))) mod 10"
  using emit_nth_carry_prefix[OF bound, of False]
  by (simp add: carry_bit_def)

theorem source_coboundary_emit:
  assumes valid: "source_pair_valid ss" and bound: "j < length ss"
  shows "cylinder_normalized 10 (source_coefficient ss)
    (source_carry_out ss) (int j) = int (emit False ss ! j)"
  using source_coboundary_active[OF valid bound] source_emitted_nth[OF bound]
  by (simp add: of_nat_mod)

text \<open>
  The preceding two lemmas identify the whole-function coboundary with the
  actual primitive source emission at every active coordinate.  They do not
  assert a bounded successor grammar or a temporal powering theorem.
\<close>

ML \<open>
  val checked = @{thms source_carry_encoding source_initial_carry
    source_prefix_step source_carry_step_div source_carry_div_bound
    source_coboundary_active source_196_coboundary_active
    source_emitted_nth source_coboundary_emit source_pair_valid_of_valid_pair
    source_pair_valid_196 source_coefficient_nth};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Source coboundary bridge depends on an oracle";
\<close>

end
