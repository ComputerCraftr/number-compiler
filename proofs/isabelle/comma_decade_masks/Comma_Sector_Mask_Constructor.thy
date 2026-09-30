theory Comma_Sector_Mask_Constructor
  imports Comma_Sector_Response_Check
begin

unbundle bit_operations_syntax

type_synonym comma_sector_rows = "(comma_round_result \<times> nat) list"

definition comma_sector_rows_refine ::
  "(nat \<Rightarrow> comma_round_result) \<Rightarrow> nat \<Rightarrow> comma_sector_rows \<Rightarrow> bool" where
  "comma_sector_rows_refine F scope rows =
    ((\<forall>r. comma_phase_member scope r =
      (\<exists>out bits. (out,bits)\<in>set rows \<and> comma_phase_member bits r)) \<and>
     (\<forall>out bits r. (out,bits)\<in>set rows \<longrightarrow>
       comma_phase_member bits r \<longrightarrow> F r=out))"

definition comma_sector_mask_value :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> comma_round_result" where
  "comma_sector_mask_value f x r=comma_fast_round_aux (10-f) r (Comma_Entry f 0 x)"

definition comma_sector_rows_restrict :: "nat \<Rightarrow> comma_sector_rows \<Rightarrow> comma_sector_rows" where
  "comma_sector_rows_restrict guard rows=map (\<lambda>(out,bits). (out,guard AND bits)) rows"

lemma comma_sector_rows_singleton:
  assumes equation: "\<And>r. comma_phase_member scope r \<Longrightarrow> F r=out"
  shows "comma_sector_rows_refine F scope [(out,scope)]"
  using equation by (auto simp: comma_sector_rows_refine_def)

lemma comma_sector_rows_restrict_member:
  "(out,bits)\<in>set (comma_sector_rows_restrict guard rows) =
    (\<exists>old. (out,old)\<in>set rows \<and> bits=guard AND old)"
proof
  assume member: "(out,bits)\<in>set (comma_sector_rows_restrict guard rows)"
  then obtain item where item: "item\<in>set rows"
    "(out,bits)=(case item of (a,b) \<Rightarrow> (a,guard AND b))"
    unfolding comma_sector_rows_restrict_def by auto
  obtain a b where pair: "item=(a,b)" by (cases item) auto
  have equal: "out=a" "bits=guard AND b" using item(2) by (simp_all add: pair)
  show "\<exists>old. (out,old)\<in>set rows \<and> bits=guard AND old"
    apply (rule exI[where x=b])
    using item(1) equal by (simp add: pair)
next
  assume "\<exists>old. (out,old)\<in>set rows \<and> bits=guard AND old"
  then obtain old where old: "(out,old)\<in>set rows" "bits=guard AND old" by blast
  have image: "(out,bits)\<in>
    (\<lambda>(a,b). (a,guard AND b)) ` set rows"
    apply (rule image_eqI[where x="(out,old)"])
     using old(2) apply simp
    using old(1) by assumption
  show "(out,bits)\<in>set (comma_sector_rows_restrict guard rows)"
    using image by (simp only: comma_sector_rows_restrict_def set_map)
qed

lemma comma_sector_rows_restrict_refines:
  assumes rows: "comma_sector_rows_refine G scope rows"
    and transport: "\<And>r. comma_phase_member guard r \<Longrightarrow> F r=G r"
  shows "comma_sector_rows_refine F (guard AND scope) (comma_sector_rows_restrict guard rows)"
proof -
  have cover: "\<And>r. comma_phase_member scope r =
    (\<exists>out bits. (out,bits)\<in>set rows \<and> comma_phase_member bits r)"
    using rows by (simp only: comma_sector_rows_refine_def; blast)
  have exact_value: "\<And>out bits r. (out,bits)\<in>set rows \<Longrightarrow>
    comma_phase_member bits r \<Longrightarrow> G r=out"
    using rows by (simp only: comma_sector_rows_refine_def; blast)
  have covered: "comma_phase_member (guard AND scope) r =
    (\<exists>out bits. (out,bits)\<in>set (comma_sector_rows_restrict guard rows) \<and>
      comma_phase_member bits r)" for r
  proof
    assume input: "comma_phase_member (guard AND scope) r"
    have both: "comma_phase_member guard r \<and> comma_phase_member scope r"
      using input by (simp only: comma_phase_member_and)
    have guard: "comma_phase_member guard r" by (rule conjunct1[OF both])
    have scope: "comma_phase_member scope r" by (rule conjunct2[OF both])
    obtain out bits where member: "(out,bits)\<in>set rows" "comma_phase_member bits r"
      using scope cover[of r] by blast
    have target: "(out,guard AND bits)\<in>set (comma_sector_rows_restrict guard rows)"
      by (simp only: comma_sector_rows_restrict_member; rule exI[where x=bits]; simp add: member(1))
    have bit: "comma_phase_member (guard AND bits) r"
      using guard member(2) by (simp only: comma_phase_member_and)
    show "\<exists>out bits. (out,bits)\<in>set (comma_sector_rows_restrict guard rows) \<and>
      comma_phase_member bits r" using target bit by blast
  next
    assume "\<exists>out bits. (out,bits)\<in>set (comma_sector_rows_restrict guard rows) \<and>
      comma_phase_member bits r"
    then obtain out bits where member: "(out,bits)\<in>set (comma_sector_rows_restrict guard rows)"
      "comma_phase_member bits r" by blast
    obtain old where old: "(out,old)\<in>set rows" "bits=guard AND old"
      using member(1) by (simp only: comma_sector_rows_restrict_member; blast)
    have both: "comma_phase_member guard r \<and> comma_phase_member old r"
      using member(2) by (simp only: old(2) comma_phase_member_and)
    have guard: "comma_phase_member guard r" by (rule conjunct1[OF both])
    have oldbit: "comma_phase_member old r" by (rule conjunct2[OF both])
    have scope: "comma_phase_member scope r" using cover[of r] old(1) oldbit by blast
    show "comma_phase_member (guard AND scope) r" using guard scope by (simp only: comma_phase_member_and)
  qed
  have exact_rows: "\<And>out bits r. (out,bits)\<in>set (comma_sector_rows_restrict guard rows) \<Longrightarrow>
    comma_phase_member bits r \<Longrightarrow> F r=out"
  proof -
    fix out bits r
    assume member: "(out,bits)\<in>set (comma_sector_rows_restrict guard rows)"
      and bit: "comma_phase_member bits r"
    obtain old where old: "(out,old)\<in>set rows" "bits=guard AND old"
      using member by (simp only: comma_sector_rows_restrict_member; blast)
    have both: "comma_phase_member guard r \<and> comma_phase_member old r"
      using bit by (simp only: old(2) comma_phase_member_and)
    have guard: "comma_phase_member guard r" by (rule conjunct1[OF both])
    have oldbit: "comma_phase_member old r" by (rule conjunct2[OF both])
    show "F r=out" using transport[OF guard] exact_value[OF old(1) oldbit] by simp
  qed
  show ?thesis unfolding comma_sector_rows_refine_def
    by (intro conjI allI impI; use covered exact_rows in blast)
qed

lemma comma_sector_rows_join:
  assumes left: "comma_sector_rows_refine F a A"
    and right: "comma_sector_rows_refine F b B"
  shows "comma_sector_rows_refine F (a OR b) (A@B)"
  using left right
  by (auto simp: comma_sector_rows_refine_def comma_phase_member_or)

text \<open>The packed producer supplies closed arithmetic equations explicitly.
These rules only transport their checked results into row certificates.\<close>
lemma comma_sector_rows_join_checked:
  assumes left: "comma_sector_rows_refine F a A"
    and right: "comma_sector_rows_refine F b B"
    and mask: "a OR b=c"
  shows "comma_sector_rows_refine F c (A@B)"
  using comma_sector_rows_join[OF left right] by (simp only: mask)

lemma comma_sector_rows_refine_by_outputs:
  "comma_sector_rows_refine F scope rows =
    ((\<forall>r. comma_phase_member scope r =
      (\<exists>out bits. (out,bits)\<in>set rows \<and> comma_phase_member bits r)) \<and>
     (\<forall>out r. (\<exists>bits. (out,bits)\<in>set rows \<and> comma_phase_member bits r) \<longrightarrow> F r=out))"
  unfolding comma_sector_rows_refine_def by blast

lemma comma_sector_rows_cons_member:
  "(\<exists>bits. (target,bits)\<in>set ((out,word)#rows) \<and> comma_phase_member bits r) =
    ((target=out \<and> comma_phase_member word r) \<or>
     (\<exists>bits. (target,bits)\<in>set rows \<and> comma_phase_member bits r))"
  by auto

text \<open>Equal terminal outcomes may be merged by OR of their phase words.
No response tree or ancestor trace is needed by this rule. The result equality
is exact: crossing position, fork digit and exponent delta all remain present.\<close>
lemma comma_sector_rows_merge_equal:
  "comma_sector_rows_refine F scope ((out,a)#(out,b)#rows) =
    comma_sector_rows_refine F scope ((out,a OR b)#rows)"
proof -
  have members: "(\<exists>bits. (target,bits)\<in>set ((out,a)#(out,b)#rows) \<and> comma_phase_member bits r) =
    (\<exists>bits. (target,bits)\<in>set ((out,a OR b)#rows) \<and> comma_phase_member bits r)" for target r
    by (simp only: comma_sector_rows_cons_member comma_phase_member_or; blast)
  show ?thesis by (simp only: comma_sector_rows_refine_by_outputs members)
qed

lemma comma_sector_rows_merge_singletons:
  assumes A: "comma_sector_rows_refine F a [(out,a)]"
    and B: "comma_sector_rows_refine F b [(out,b)]"
    and mask: "a OR b=c"
  shows "comma_sector_rows_refine F c [(out,c)]"
proof -
  have joined: "comma_sector_rows_refine F (a OR b) [(out,a),(out,b)]"
    using comma_sector_rows_join[OF A B] by (simp only: append_Cons append_Nil)
  have merged: "comma_sector_rows_refine F (a OR b) [(out,a OR b)]"
    using joined by (simp only: comma_sector_rows_merge_equal)
  show ?thesis using merged by (simp only: mask)
qed

lemma comma_sector_rows_concat:
  assumes clauses: "\<And>scope rows. (scope,rows)\<in>set pieces \<Longrightarrow>
    comma_sector_rows_refine F scope rows"
  shows "comma_sector_rows_refine F (comma_mask_union (map fst pieces))
    (concat (map snd pieces))"
  using clauses
proof (induction pieces)
  case Nil
  show ?case by (simp add: comma_sector_rows_refine_def)
next
  case (Cons item pieces)
  obtain scope rows where item: "item=(scope,rows)" by (cases item) auto
  have head: "comma_sector_rows_refine F scope rows" using Cons.prems by (simp add: item)
  have tail: "comma_sector_rows_refine F (comma_mask_union (map fst pieces))
    (concat (map snd pieces))" by (rule Cons.IH) (use Cons.prems in auto)
  show ?case using comma_sector_rows_join[OF head tail] by (simp add: item)
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

lemma comma_sector_rows_rebind:
  assumes "F=G" "comma_sector_rows_refine G scope rows"
  shows "comma_sector_rows_refine F scope rows"
  using assms by simp

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
      comma_sector_mask_short_coverage comma_sector_mask_entry_control})
    then () else error "Sector row constructor depends on an oracle";
\<close>
end
