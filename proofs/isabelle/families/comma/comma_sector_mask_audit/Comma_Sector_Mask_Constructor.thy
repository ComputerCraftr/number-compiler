theory Comma_Sector_Mask_Constructor
  imports Comma_Sparse_Core.Comma_Sector_Rows_Core
begin

unbundle bit_operations_syntax

fun comma_sector_round_key :: "comma_round_result \<Rightarrow> nat list" where
  "comma_sector_round_key (Comma_Round_Fork a d) = [1,a,d]"
| "comma_sector_round_key (Comma_Round_Landmine d) = [2,d]"
| "comma_sector_round_key (Comma_Round_Cross (Comma_Entry f delta offset)) =
    [3,0,f,delta,offset]"
| "comma_sector_round_key (Comma_Round_Cross (Comma_Near f delta headroom)) =
    [3,1,f,delta,headroom]"
| "comma_sector_round_key Comma_Round_Invalid = [0]"

lemma comma_sector_round_key_injective:
  assumes equal: "comma_sector_round_key left = comma_sector_round_key right"
  shows "left=right"
proof -
  have cross: "comma_sector_round_key (Comma_Round_Cross p) =
    3 # (case p of Comma_Entry f d x \<Rightarrow> [0,f,d,x]
      | Comma_Near f d h \<Rightarrow> [1,f,d,h])" for p
    by (cases p) simp_all
  show ?thesis
    using equal
    by (cases left; cases right; auto simp: cross split: comma_finite_position.splits)
qed


lemma comma_sector_mask_depth:
  assumes "f\<le>9"
  shows "10-f=Suc (9-f)" and "10-Suc f=9-f"
  using assms by arith+

lemma comma_sector_mask_clause:
  assumes sector: "1\<le>f" "f\<le>9" "x\<le>98"
    and phase: "comma_entry_alphabet_phase f r 0 x=k"
    and clause: "comma_fast_step 0
      (Comma_Near f 0 (comma_entry_alphabet_endpoint f x k))=event"
  shows "comma_sector_mask_value f x r=
    (case event of
      Comma_Next target \<Rightarrow>
        if comma_round_crossing (Comma_Near f 0 (comma_entry_alphabet_endpoint f x k)) target
        then Comma_Round_Cross target else comma_fast_round_aux (9-f) r target
    | Comma_Fork a d \<Rightarrow> Comma_Round_Fork a d
    | Comma_Landmine d \<Rightarrow> Comma_Round_Landmine d
    | Comma_Invalid \<Rightarrow> Comma_Round_Invalid)"
  unfolding comma_sector_mask_value_def
  by (simp only: comma_sector_mask_depth(1)[OF sector(2)]
      comma_sector_clause_refines[OF sector phase clause])

lemma comma_sector_guard_phase:
  assumes period: "period=comma_short_period (comma_finite_period_fast f (x mod 10))"
    and guard: "comma_phase_member (comma_phase_class period 919 k) r"
  shows "comma_entry_alphabet_phase f r 0 x=k"
proof -
  have phase: "r<924" and selected: "(r+919) mod period=k"
    using guard by (auto simp: comma_phase_class_def comma_phase_mask_member)
  show ?thesis using selected phase
    by (simp add: comma_entry_alphabet_phase_def period)
qed

lemma comma_sector_guard_phase_checked:
  assumes period: "period=comma_short_period (comma_finite_period_fast f (x mod 10))"
    and guard_eq: "comma_phase_class period 919 k=bits"
    and member: "comma_phase_member bits r"
  shows "comma_entry_alphabet_phase f r 0 x=k"
  apply (rule comma_sector_guard_phase[OF period])
  using member by (simp only: guard_eq)

lemma comma_sector_mask_fork:
  assumes sector: "1\<le>f" "f\<le>9" "x\<le>98"
    and guard: "\<And>r. comma_phase_member bits r \<Longrightarrow> comma_entry_alphabet_phase f r 0 x=k"
    and clause: "comma_fast_step 0 (Comma_Near f 0 (comma_entry_alphabet_endpoint f x k))=Comma_Fork a d"
  shows "comma_sector_rows_refine (comma_sector_mask_value f x) bits [(Comma_Round_Fork a d,bits)]"
proof (rule comma_sector_rows_singleton)
  fix r assume selected: "comma_phase_member bits r"
  show "comma_sector_mask_value f x r=Comma_Round_Fork a d"
    using comma_sector_mask_clause[OF sector guard[OF selected] clause] by simp
qed

lemma comma_sector_mask_landmine:
  assumes sector: "1\<le>f" "f\<le>9" "x\<le>98"
    and guard: "\<And>r. comma_phase_member bits r \<Longrightarrow> comma_entry_alphabet_phase f r 0 x=k"
    and clause: "comma_fast_step 0 (Comma_Near f 0 (comma_entry_alphabet_endpoint f x k))=Comma_Landmine d"
  shows "comma_sector_rows_refine (comma_sector_mask_value f x) bits [(Comma_Round_Landmine d,bits)]"
proof (rule comma_sector_rows_singleton)
  fix r assume selected: "comma_phase_member bits r"
  show "comma_sector_mask_value f x r=Comma_Round_Landmine d"
    using comma_sector_mask_clause[OF sector guard[OF selected] clause] by simp
qed

lemma comma_sector_mask_invalid:
  assumes sector: "1\<le>f" "f\<le>9" "x\<le>98"
    and guard: "\<And>r. comma_phase_member bits r \<Longrightarrow> comma_entry_alphabet_phase f r 0 x=k"
    and clause: "comma_fast_step 0 (Comma_Near f 0 (comma_entry_alphabet_endpoint f x k))=Comma_Invalid"
  shows "comma_sector_rows_refine (comma_sector_mask_value f x) bits [(Comma_Round_Invalid,bits)]"
proof (rule comma_sector_rows_singleton)
  fix r assume selected: "comma_phase_member bits r"
  show "comma_sector_mask_value f x r=Comma_Round_Invalid"
    using comma_sector_mask_clause[OF sector guard[OF selected] clause] by simp
qed

lemma comma_sector_mask_cross:
  assumes sector: "1\<le>f" "f\<le>9" "x\<le>98"
    and guard: "\<And>r. comma_phase_member bits r \<Longrightarrow> comma_entry_alphabet_phase f r 0 x=k"
    and clause: "comma_fast_step 0 (Comma_Near f 0 (comma_entry_alphabet_endpoint f x k))=Comma_Next target"
    and crossing: "comma_round_crossing (Comma_Near f 0 (comma_entry_alphabet_endpoint f x k)) target"
  shows "comma_sector_rows_refine (comma_sector_mask_value f x) bits [(Comma_Round_Cross target,bits)]"
proof (rule comma_sector_rows_singleton)
  fix r assume selected: "comma_phase_member bits r"
  show "comma_sector_mask_value f x r=Comma_Round_Cross target"
    using comma_sector_mask_clause[OF sector guard[OF selected] clause] crossing by simp
qed

lemma comma_sector_mask_successor:
  assumes sector: "1\<le>f" "f\<le>9" "x\<le>98"
    and guard: "\<And>r. comma_phase_member bits r \<Longrightarrow> comma_entry_alphabet_phase f r 0 x=k"
    and clause: "comma_fast_step 0 (Comma_Near f 0 (comma_entry_alphabet_endpoint f x k))=
      Comma_Next (Comma_Entry (Suc f) 0 y)"
    and crossing: "\<not>comma_round_crossing (Comma_Near f 0 (comma_entry_alphabet_endpoint f x k))
      (Comma_Entry (Suc f) 0 y)"
    and child: "comma_sector_rows_refine (comma_sector_mask_value (Suc f) y) scope rows"
  shows "comma_sector_rows_refine (comma_sector_mask_value f x) (bits AND scope)
    (comma_sector_rows_restrict bits rows)"
proof (rule comma_sector_rows_restrict_refines[OF child])
  fix r assume selected: "comma_phase_member bits r"
  have equation: "comma_sector_mask_value f x r=
      comma_fast_round_aux (9-f) r (Comma_Entry (Suc f) 0 y)"
    using comma_sector_mask_clause[OF sector guard[OF selected] clause] crossing by simp
  have target_eq: "comma_sector_mask_value (Suc f) y r=
    comma_fast_round_aux (9-f) r (Comma_Entry (Suc f) 0 y)"
    by (simp only: comma_sector_mask_value_def comma_sector_mask_depth(2)[OF sector(2)])
  show "comma_sector_mask_value f x r=comma_sector_mask_value (Suc f) y r"
    by (rule trans[OF equation target_eq[symmetric]])
qed

text \<open>A period-one noncrossing clause forwards the complete response
function. This is source rebinding, not equality of a projected terminal label;
its masks and all later consumers can be shared before row construction.\<close>
lemma comma_sector_mask_period_one_forward:
  assumes sector: "1\<le>f" "f\<le>9" "x\<le>98"
    and period: "comma_short_period (comma_finite_period_fast f (x mod 10))=1"
    and clause: "comma_fast_step 0 (Comma_Near f 0 (comma_entry_alphabet_endpoint f x 0))=
      Comma_Next (Comma_Entry (Suc f) 0 y)"
    and crossing: "\<not>comma_round_crossing (Comma_Near f 0 (comma_entry_alphabet_endpoint f x 0))
      (Comma_Entry (Suc f) 0 y)"
  shows "comma_sector_mask_value f x=comma_sector_mask_value (Suc f) y"
proof (rule ext)
  fix r
  have phase: "comma_entry_alphabet_phase f r 0 x=0"
    by (simp only: comma_entry_alphabet_phase_def period mod_by_1)
  show "comma_sector_mask_value f x r=comma_sector_mask_value (Suc f) y r"
    using comma_sector_mask_clause[OF sector phase clause] crossing
    by (simp only: comma_finite_move.case if_False comma_sector_mask_value_def
        comma_sector_mask_depth(2)[OF sector(2)])
qed


lemma comma_sector_mask_successor_singleton:
  assumes sector: "1\<le>f" "f\<le>9" "x\<le>98"
    and guard: "\<And>r. comma_phase_member bits r \<Longrightarrow> comma_entry_alphabet_phase f r 0 x=k"
    and clause: "comma_fast_step 0 (Comma_Near f 0 (comma_entry_alphabet_endpoint f x k))=
      Comma_Next (Comma_Entry (Suc f) 0 y)"
    and crossing: "\<not>comma_round_crossing (Comma_Near f 0 (comma_entry_alphabet_endpoint f x k))
      (Comma_Entry (Suc f) 0 y)"
    and child: "comma_sector_rows_refine (comma_sector_mask_value (Suc f) y) scope [(out,scope)]"
    and mask: "bits AND scope=combined"
  shows "comma_sector_rows_refine (comma_sector_mask_value f x) combined [(out,combined)]"
  using comma_sector_mask_successor[where bits=bits, OF sector guard clause crossing child]
  by (simp only: comma_sector_rows_restrict_def list.map case_prod_conv mask)

text \<open>Short-phase assembly needs every branch, including branches whose
computed word is zero. Coverage is checked separately from terminal equality.
No default outcome is supplied for omitted alternatives.\<close>
lemma comma_sector_mask_short_coverage:
  assumes sector: "1\<le>f" "f\<le>9" "x\<le>98"
    and period: "period=comma_short_period (comma_finite_period_fast f (x mod 10))"
    and rows: "\<And>k. k<period \<Longrightarrow>
      comma_sector_rows_refine (comma_sector_mask_value f x)
        (comma_phase_class period 919 k) (branches k)"
  shows "comma_sector_rows_refine (comma_sector_mask_value f x) (mask 924)
    (concat (map branches [0..<period]))"
proof -
  have positive: "0<period"
    using comma_entry_alphabet_phase_bound[OF sector(1,2), where r=0 and delta=0 and x=x] period by arith
  have full: "\<And>r. comma_phase_member (mask 924) r =
    comma_phase_member (comma_mask_union (map (\<lambda>k. comma_phase_class period 919 k) [0..<period])) r"
    using positive by (auto simp: comma_phase_full_mask comma_mask_union_member
      comma_phase_class_def comma_phase_mask_member)
  have assembled: "comma_sector_rows_refine (comma_sector_mask_value f x)
    (comma_mask_union (map (\<lambda>k. comma_phase_class period 919 k) [0..<period]))
    (concat (map branches [0..<period]))"
  proof -
    have result: "comma_sector_rows_refine (comma_sector_mask_value f x)
      (comma_mask_union (map fst (map (\<lambda>k. (comma_phase_class period 919 k,branches k)) [0..<period])))
      (concat (map snd (map (\<lambda>k. (comma_phase_class period 919 k,branches k)) [0..<period])))"
      by (rule comma_sector_rows_concat) (use rows in auto)
    show ?thesis using result by (simp add: comp_def)
  qed
  show ?thesis using assembled by (simp only: comma_sector_rows_refine_def full; blast)
qed

lemma comma_sector_mask_entry_control:
  assumes rows: "comma_sector_rows_refine (comma_sector_mask_value 1 x) (mask 924) rows"
    and member: "(out,bits)\<in>set rows" "comma_phase_member bits r"
  shows "comma_decade_decode r out=comma_fast_decade_control (Comma_Decade r x)"
proof -
  have eq: "comma_sector_mask_value 1 x r=out"
    using rows member unfolding comma_sector_rows_refine_def by blast
  show ?thesis
    using eq by (simp only: comma_sector_mask_value_def comma_fast_decade_control.simps; simp)
qed

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_sector_mask_period_one_forward comma_sector_rows_rebind
      comma_sector_rows_restrict_refines comma_sector_rows_merge_equal
      comma_sector_rows_join_checked comma_sector_rows_merge_singletons
      comma_sector_mask_successor_singleton comma_sector_guard_phase_checked
      comma_sector_mask_clause comma_sector_mask_fork comma_sector_mask_landmine
      comma_sector_mask_cross comma_sector_mask_successor
      comma_sector_mask_short_coverage comma_sector_mask_entry_control
      comma_sector_round_key_injective})
    then () else error "Sector row constructor depends on an oracle";
\<close>
ML_file "sector_mask_constructor.ML"

end
