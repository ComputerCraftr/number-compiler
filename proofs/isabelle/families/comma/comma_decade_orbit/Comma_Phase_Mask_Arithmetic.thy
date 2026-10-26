theory Comma_Phase_Mask_Arithmetic
  imports Comma_Decade_Masks
begin

text \<open>Checked packed clock arithmetic is owned beside the phase-mask laws.
Response constructors and graph consumers share these proofs and conversions;
no response evaluator or source-specific certificate is imported here.\<close>

lemma comma_rotate_phase_one_bounded:
  assumes bounded: "take_bit 924 (bits::nat)=bits"
  shows "comma_rotate_phase 1 bits =
    drop_bit 1 bits OR push_bit 923 (take_bit 1 bits)"
proof -
  have wider: "take_bit 925 bits=bits"
  proof -
    have "take_bit 925 bits=take_bit 925 (take_bit 924 bits)"
      by (simp only: bounded)
    also have "...=take_bit 924 bits" by simp
    also have "...=bits" by (rule bounded)
    finally show ?thesis .
  qed
  show ?thesis using bounded wider
    by (simp add: comma_rotate_phase_def Let_def take_bit_drop_bit take_bit_push_bit)
qed

definition comma_indexed_phase_union ::
  "(nat \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> nat list \<Rightarrow> nat" where
  "comma_indexed_phase_union P words = comma_mask_union
    (map (\<lambda>(k,bits). comma_phase_mask (P k) AND bits)
      (zip [0..<length words] words))"

lemma comma_indexed_phase_union_member:
  "comma_phase_member (comma_indexed_phase_union P words) r =
    (\<exists>k<length words. P k r \<and> comma_phase_member (words!k) r)"
proof -
  have bounded: "\<And>bits. comma_phase_member bits r \<Longrightarrow> r<924"
    by (simp add: comma_phase_member_def)
  show ?thesis
    unfolding comma_indexed_phase_union_def
    apply (simp only: comma_mask_union_member set_map)
    apply (auto simp: comma_phase_member_and comma_phase_mask_member set_zip
      dest: bounded)
    subgoal for k
      apply (rule exI[where x=k])
      apply (rule exI[where x="words!k"])
      apply (rule conjI)
       apply (rule exI[where x=k])
       apply simp
      using bounded by auto
    done
qed


text \<open>A guard certificate covers every bit position, including zero
high bits. Binary concatenation repeats one short period; it does not execute
a predicate at each of the 924 phases. Positive shift is the established
pullback rotation: position r tests (r+shift) mod period.\<close>
definition comma_guard_pattern :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "comma_guard_pattern period residue width bits =
    (\<forall>r. bit bits r = (r<width \<and> r mod period=residue))"

lemma comma_guard_single_period:
  assumes "residue<period"
  shows "comma_guard_pattern period residue period (2^residue)"
  unfolding comma_guard_pattern_def
proof
  fix r
  show "bit (2^residue::nat) r = (r<period \<and> r mod period=residue)"
    using assms by (cases "r<period") (auto simp: bit_simps)
qed

lemma comma_guard_join:
  assumes lower: "comma_guard_pattern period residue width a"
    and upper: "comma_guard_pattern period residue height b"
    and aligned: "period dvd width"
  shows "comma_guard_pattern period residue (width+height) (a OR push_bit width b)"
  unfolding comma_guard_pattern_def
proof
  fix r
  have first: "bit a r=(r<width \<and> r mod period=residue)"
    using lower by (simp add: comma_guard_pattern_def)
  have second: "bit b (r-width)=(r-width<height \<and> (r-width) mod period=residue)"
    using upper by (simp add: comma_guard_pattern_def)
  show "bit (a OR push_bit width b) r =
    (r<width+height \<and> r mod period=residue)"
  proof (cases "r<width")
    case True
    then show ?thesis using first by (auto simp: bit_simps)
  next
    case False
    have lower_bound: "width\<le>r" using False by arith
    have decomposition: "r=(r-width)+width" using lower_bound by arith
    have remainder: "r mod period=(r-width) mod period"
    proof -
      have "r mod period=((r-width)+width) mod period"
        by (rule arg_cong[OF decomposition])
      also have "...=((r-width)+width mod period) mod period"
        by (rule mod_add_right_eq[symmetric])
      also have "...=(r-width) mod period" using aligned by simp
      finally show ?thesis .
    qed
    have extent: "(r-width<height)=(r<width+height)" using lower_bound by arith
    show ?thesis using False lower_bound first second remainder extent
      by (simp add: bit_simps)
  qed
qed

lemma comma_guard_pattern_phase_class:
  assumes pattern: "comma_guard_pattern period residue 924 bits"
    and divides: "period dvd 924"
  shows "comma_rotate_phase shift bits=comma_phase_class period shift residue"
proof (rule bit_eqI)
  fix r
  show "bit (comma_rotate_phase shift bits) r =
    bit (comma_phase_class period shift residue) r"
  proof (cases "r<924")
    case True
    have rotated: "comma_phase_member (comma_rotate_phase shift bits) r=
      comma_phase_member bits ((r+shift) mod 924)"
      by (rule comma_rotate_phase_member[OF True])
    have periodic: "((r+shift) mod 924) mod period=(r+shift) mod period"
      by (rule mod_mod_cancel[OF divides])
    show ?thesis using rotated True pattern
      by (simp add: comma_phase_member_def comma_guard_pattern_def
        comma_phase_class_def comma_phase_mask_bit periodic)
  next
    case False
    then show ?thesis
      by (simp add: comma_rotate_phase_def Let_def bit_simps
        comma_phase_class_def comma_phase_mask_bit)
  qed
qed

lemma comma_guard_push_one_numeral:
  "push_bit 1 (numeral k :: nat) = numeral (Num.Bit0 k)"
  by (simp only: One_nat_def push_bit_Suc_numeral push_bit_0_id id_def)

lemma comma_guard_full_phase:
  "comma_phase_class 1 0 0 = (mask 924 :: nat)"
  by (rule bit_eqI)
    (simp add: comma_phase_class_def comma_phase_mask_bit bit_simps)

lemma comma_mask_and_zero: "(a::nat) AND 0 = 0"
  by (rule bit_eqI) (simp add: bit_simps)
lemma comma_mask_and_self: "(a::nat) AND a = a"
  by (rule bit_eqI) (simp add: bit_simps)
lemma comma_mask_or_zero: "(a::nat) OR 0 = a"
  by (rule bit_eqI) (simp add: bit_simps)
lemma comma_mask_or_self: "(a::nat) OR a = a"
  by (rule bit_eqI) (simp add: bit_simps)
lemma comma_mask_and_swap: "(a::nat) AND b = b AND a"
  by (rule bit_eqI) (auto simp: bit_simps)
lemma comma_mask_or_swap: "(a::nat) OR b = b OR a"
  by (rule bit_eqI) (auto simp: bit_simps)

text \<open>Full-mask shortcuts require a checked width certificate. A phase
class supplies it without comparing or evaluating its closed 924-bit numeral.
These rules make no assumption about arbitrary natural-number mask inputs.\<close>
lemma comma_mask_phase_class_bounded:
  assumes source: "comma_phase_class period shift k=a"
  shows "take_bit 924 a=a"
proof -
  have trimmed: "take_bit 924 (comma_phase_class period shift k)=
    comma_phase_class period shift k"
    by (rule bit_eqI)
      (simp add: comma_phase_class_def comma_phase_mask_bit bit_simps)
  show ?thesis using trimmed by (simp only: source)
qed

lemma comma_mask_and_full:
  assumes bounded: "take_bit 924 (a::nat)=a"
    and full: "mask 924=full"
  shows "a AND full=a"
proof -
  have "a AND mask 924=a"
    by (rule trans[OF take_bit_eq_mask[symmetric] bounded])
  then show ?thesis by (simp only: full)
qed

lemma comma_mask_and_preserves_bounded:
  assumes left: "take_bit 924 (a::nat)=a"
    and right: "take_bit 924 b=b"
  shows "take_bit 924 (a AND b)=a AND b"
  using left right by (simp add: take_bit_and)

lemma comma_mask_or_full:
  assumes bounded: "take_bit 924 (a::nat)=a"
    and full: "mask 924=full"
  shows "a OR full=full"
proof -
  have "take_bit 924 a OR mask 924=(mask 924::nat)"
    by (rule bit_eqI) (auto simp: bit_simps)
  then show ?thesis by (simp only: bounded full)
qed

lemma comma_guard_shifted_pattern:
  assumes pattern: "comma_guard_pattern period target 924 bits"
    and positive: "0<period"
    and phase: "list_all (\<lambda>i. ((i+shift) mod period=residue)=(i=target)) [0..<period]"
  shows "comma_phase_class period shift residue=bits"
proof (rule bit_eqI)
  fix r
  have local_phase: "((r mod period+shift) mod period=residue)=(r mod period=target)"
    using phase positive by (auto simp: list_all_iff)
  show "bit (comma_phase_class period shift residue) r=bit bits r"
    using pattern local_phase
    by (simp add: comma_phase_class_def comma_phase_mask_bit
      comma_guard_pattern_def mod_add_left_eq)
qed

lemma comma_guard_drop_one_numeral:
  "drop_bit 1 (numeral (Num.Bit0 k) :: nat) = numeral k"
  "drop_bit 1 (numeral (Num.Bit1 k) :: nat) = numeral k"
  by (simp_all only: One_nat_def drop_bit_Suc_bit0 drop_bit_Suc_bit1 drop_bit_0 id_def)

lemma comma_guard_take_num_one:
  "take_bit_num 1 Num.One = Some Num.One"
  "take_bit_num 1 (Num.Bit0 k) = None"
  "take_bit_num 1 (Num.Bit1 k) = Some Num.One"
  by (simp_all only: One_nat_def take_bit_num_simps option.case)

lemma comma_guard_take_one_one:
  "take_bit 1 (1 :: nat) = 1"
  by simp

lemma comma_guard_take_one_numeral:
  "take_bit 1 (numeral (Num.Bit0 k) :: nat) = 0"
  "take_bit 1 (numeral (Num.Bit1 k) :: nat) = 1"
  by (simp_all only: One_nat_def take_bit_Suc_bit0 take_bit_Suc_bit1
      take_bit_0 mult_zero_left add_0_left)


ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_indexed_phase_union_member comma_guard_single_period
      comma_guard_join comma_guard_pattern_phase_class comma_guard_shifted_pattern})
    then () else error "Packed phase arithmetic depends on an oracle";
\<close>

ML_file "phase_mask_arithmetic.ML"

end
