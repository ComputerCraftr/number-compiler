theory Comma_Sector_Response_Check
  imports Comma_Sector_Response Comma_Frobenius_Entry.Comma_Frobenius_Entry
begin

text \<open>Local branch equations for the symbolic response constructor.
This evaluator shares the existing arithmetic kernel and does not unfold a
response tree, traverse the 924 phase population, or assert mask coverage.\<close>
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

primrec comma_response_mask ::
  "comma_round_result \<Rightarrow> comma_sector_response \<Rightarrow> nat" where
  "comma_response_mask desired (Comma_Response_Leaf result)=
    (if desired=result then mask 924 else 0)"
| "comma_response_mask desired (Comma_Response_Phases f delta x children)=
    comma_indexed_phase_union
      (\<lambda>k r. comma_entry_alphabet_phase f r delta x=k)
      (map (comma_response_mask desired) children) OR
    (if desired=Comma_Round_Invalid then comma_phase_mask
      (\<lambda>r. length children\<le>comma_entry_alphabet_phase f r delta x) else 0)"

text \<open>The Invalid arm makes the projection total even for malformed
phase nodes with missing children. A complete symbolic constructor never
needs to fill missing branches with an assumed safe result. All mask joins
are functions of already constructed child masks, so the proof applies to
shared DAG implementations without expanding a response tree.\<close>
lemma comma_response_mask_member:
  "comma_phase_member (comma_response_mask desired response) r =
    (r<924 \<and> comma_response_value r response=desired)"
proof (induction response arbitrary: desired r)
  case (Comma_Response_Leaf result)
  then show ?case
    by (cases "desired=result") (auto simp: comma_phase_full_mask)
next
  case (Comma_Response_Phases f delta x children)
  have child: "\<And>k. k<length children \<Longrightarrow>
      comma_phase_member (comma_response_mask desired (children!k)) r =
      (r<924 \<and> comma_response_value r (children!k)=desired)"
    using Comma_Response_Phases.IH by (simp add: nth_mem)
  show ?case
    by (auto simp: comma_phase_member_or comma_indexed_phase_union_member
      comma_phase_mask_member child Let_def
      nth_map split: if_splits)
qed

lemma comma_entry_response_mask_refines:
  "comma_phase_member
    (comma_response_mask desired (comma_build_sector_response 9 (Comma_Entry 1 0 x))) r =
    (r<924 \<and> comma_fast_round_aux 9 r (Comma_Entry 1 0 x)=desired)"
  by (simp only: comma_response_mask_member comma_sector_response_refines)

lemma comma_sector_clause_refines:
  assumes sector: "1\<le>f" "f\<le>9" "x\<le>98"
    and phase: "comma_entry_alphabet_phase f r 0 x=k"
    and clause: "comma_fast_step 0
      (Comma_Near f 0 (comma_entry_alphabet_endpoint f x k))=event"
  shows "comma_fast_round_aux (Suc n) r (Comma_Entry f 0 x)=
    (case event of
      Comma_Next target \<Rightarrow>
        if comma_round_crossing
          (Comma_Near f 0 (comma_entry_alphabet_endpoint f x k)) target
        then Comma_Round_Cross target else comma_fast_round_aux n r target
    | Comma_Fork a d \<Rightarrow> Comma_Round_Fork a d
    | Comma_Landmine d \<Rightarrow> Comma_Round_Landmine d
    | Comma_Invalid \<Rightarrow> Comma_Round_Invalid)"
proof -
  have target: "comma_fast_sector_target r (Comma_Entry f 0 x)=
    Comma_Near f 0 (comma_entry_alphabet_endpoint f x k)"
    using sector phase by (simp only: comma_sector_entry_alphabet; simp)
  have step: "comma_fast_step (r mod 924)
    (Comma_Near f 0 (comma_entry_alphabet_endpoint f x k))=event"
    using clause by (simp only: comma_fast_step.simps)
  show ?thesis by (simp only: comma_response_round_successor target Let_def step)
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

lemma comma_guard_take_one_numeral:
  "take_bit 1 (numeral (Num.Bit0 k) :: nat) = 0"
  "take_bit 1 (numeral (Num.Bit1 k) :: nat) = 1"
  by (simp_all only: One_nat_def take_bit_Suc_bit0 take_bit_Suc_bit1
      take_bit_0 mult_zero_left add_0_left)

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_indexed_phase_union_member comma_response_mask_member
      comma_entry_response_mask_refines comma_sector_clause_refines
      comma_guard_single_period comma_guard_join comma_guard_pattern_phase_class
      comma_guard_push_one_numeral comma_guard_full_phase
      comma_mask_and_zero comma_mask_and_self comma_mask_or_zero comma_mask_or_self
      comma_mask_and_swap comma_mask_or_swap
      comma_mask_phase_class_bounded comma_mask_and_full comma_mask_or_full
      comma_guard_shifted_pattern comma_guard_drop_one_numeral
      comma_guard_take_num_one comma_guard_take_one_numeral}) then ()
    else error "Symbolic sector mask refinement depends on an oracle";
\<close>

ML_file "sector_response_check.ML"

end
