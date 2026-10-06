theory Comma_Native_Summary
  imports Comma_Sparse_Core.Comma_Sparse_Temporal_Composition
    Comma_Decade_Residual_Core.Comma_Decade_Residual_Core
    Comma_Terminal_Weight.Comma_Terminal_Weight
begin

ML_file "../comma_entry_arithmetic/proof_profile.ML"

ML \<open>
  structure Comma_Native_Summary_Profile =
  struct
    val started = Time.now ()
    fun checkpoint stage = Comma_Proof_Profile.report
      ("Native summary stage=" ^ stage ^ " elapsed_ms=" ^
        Comma_Proof_Profile.elapsed_ms started)
  end
  val _ = Comma_Native_Summary_Profile.checkpoint "theory-entered"
\<close>

text \<open>A sparse word is a finite, phase-indexed representation of one
powered decade response. Lookup is the executable consumer: the whole-fiber
refinement supplies both coverage and exact response semantics. The
all-stop property is a separate constructor obligation that each concrete
child instance must establish. No rank table or bounded round evaluator is
part of this interface.\<close>

fun comma_sparse_lookup :: "comma_sparse_word \<Rightarrow> nat \<Rightarrow> comma_word_result option" where
  "comma_sparse_lookup [] r = None"
| "comma_sparse_lookup ((out,bits)#rows) r =
    (if comma_phase_member bits r then Some out else comma_sparse_lookup rows r)"

lemma comma_relation_from_rendered_list:
  fixes relation :: "'a \<Rightarrow> bool"
    and render :: "'b \<Rightarrow> 'a"
    and labels :: "'a list"
    and children :: "'b list"
  assumes exact: "\<forall>v. relation v \<longleftrightarrow> v\<in>set labels"
    and rendered: "set (map render children)=set labels"
  shows "\<forall>v. relation v \<longleftrightarrow>
    (\<exists>child\<in>set children. v=render child)"
  using exact rendered by auto

lemma comma_sparse_lookup_some_witness:
  assumes "comma_sparse_lookup rows r=Some out"
  shows "\<exists>bits. (out,bits)\<in>set rows \<and> comma_phase_member bits r"
  using assms by (induction rows) (auto split: if_splits prod.splits)

lemma comma_sparse_lookup_witness_some:
  assumes "\<exists>out bits. (out,bits)\<in>set rows \<and> comma_phase_member bits r"
  shows "\<exists>out. comma_sparse_lookup rows r=Some out"
  using assms
proof (induction rows)
  case Nil
  then show ?case by simp
next
  case (Cons item rows)
  obtain head_out head_bits where item: "item=(head_out,head_bits)"
    by (cases item) auto
  show ?case
  proof (cases "comma_phase_member head_bits r")
    case True
    then show ?thesis by (simp add: item)
  next
    case False
    have tail_hit:
      "\<exists>out bits. (out,bits)\<in>set rows \<and> comma_phase_member bits r"
      using Cons.prems False item by auto
    obtain out where result: "comma_sparse_lookup rows r=Some out"
      using Cons.IH[OF tail_hit] by blast
    show ?thesis using result False by (simp add: item)
  qed
qed

lemma comma_sparse_lookup_refines_phase:
  assumes refined: "comma_sparse_refines F rows"
    and phase: "r<924"
  shows "\<exists>out. comma_sparse_lookup rows r=Some out \<and> F r=out"
proof -
  have cover: "\<exists>out bits. (out,bits)\<in>set rows \<and> comma_phase_member bits r"
    by (rule comma_sparse_refines_cover[OF refined phase])
  obtain out where lookup: "comma_sparse_lookup rows r=Some out"
    using comma_sparse_lookup_witness_some[OF cover] by blast
  obtain bits where member: "(out,bits)\<in>set rows" "comma_phase_member bits r"
    using comma_sparse_lookup_some_witness[OF lookup] by blast
  have selected: "comma_sparse_has rows r out"
    using member unfolding comma_sparse_has_def by blast
  have exact: "F r=out"
    using comma_sparse_refines_at[OF refined phase, of out] selected by blast
  show ?thesis using lookup exact by blast
qed

definition comma_sparse_decade_summary ::
  "(nat \<Rightarrow> comma_sparse_word) \<Rightarrow> comma_decade_state \<Rightarrow> comma_decade_residual option" where
  "comma_sparse_decade_summary rows s =
    (case s of Comma_Decade r x \<Rightarrow>
      if comma_decade_admitted s then
        (case comma_sparse_lookup (rows (comma_offset_orbit x)) r of
          Some (Comma_Word_Stop h terminal) \<Rightarrow> Some (h,terminal)
        | _ \<Rightarrow> None)
      else None)"

text \<open>The boundary consumer needs the terminal position as one exact
natural. This lookup encodes a selected Stop row directly; it does not first
construct the legacy option pair returned by @{const comma_sparse_decade_summary}.
The pair-valued API remains available for exact child-rendering proofs, while
the native boundary path consumes this weighted result and decodes only when
the terminal child constructor is needed.\<close>

definition comma_sparse_lookup_terminal_weight ::
    "comma_sparse_word \<Rightarrow> nat \<Rightarrow> nat option" where
  "comma_sparse_lookup_terminal_weight rows r =
    (case comma_sparse_lookup rows r of
      Some (Comma_Word_Stop height terminal) \<Rightarrow>
        (if comma_terminal_weight_admitted terminal then
          Some (comma_terminal_weight_encode height terminal)
         else None)
    | _ \<Rightarrow> None)"

lemma comma_sparse_lookup_terminal_weight_stop:
  assumes admitted: "comma_terminal_weight_admitted terminal"
    and lookup:
    "comma_sparse_lookup rows r=Some (Comma_Word_Stop height terminal)"
  shows "comma_sparse_lookup_terminal_weight rows r=
    Some (comma_terminal_weight_encode height terminal)"
  using lookup admitted by (simp add: comma_sparse_lookup_terminal_weight_def)

lemma comma_sparse_lookup_terminal_weight_rejects_invalid:
  assumes invalid: "\<not> comma_terminal_weight_admitted terminal"
    and lookup:
      "comma_sparse_lookup rows r=Some (Comma_Word_Stop height terminal)"
  shows "comma_sparse_lookup_terminal_weight rows r=None"
  using lookup invalid
  by (simp add: comma_sparse_lookup_terminal_weight_def)

corollary comma_sparse_lookup_terminal_weight_rejects_malformed_fork:
  assumes lookup:
      "comma_sparse_lookup rows r=Some (Comma_Word_Stop height (Comma_Terminal_Fork a))"
    and malformed: "a<2 \<or> 9<a"
  shows "comma_sparse_lookup_terminal_weight rows r=None"
proof -
  have invalid:
    "\<not> comma_terminal_weight_admitted (Comma_Terminal_Fork a)"
    using malformed by (auto simp: comma_terminal_weight_admitted_def)
  show ?thesis
    by (rule comma_sparse_lookup_terminal_weight_rejects_invalid[OF invalid lookup])
qed

lemma comma_sparse_lookup_terminal_weight_some_witness:
  assumes weight: "comma_sparse_lookup_terminal_weight rows r=Some D"
  obtains height terminal where
    "comma_sparse_lookup rows r=Some (Comma_Word_Stop height terminal)"
    "comma_terminal_weight_admitted terminal"
    "D=comma_terminal_weight_encode height terminal"
  using weight
  by (cases "comma_sparse_lookup rows r";
      auto simp: comma_sparse_lookup_terminal_weight_def
        split: option.splits comma_word_result.splits if_splits)

definition comma_sparse_decade_weight_summary ::
    "(nat \<Rightarrow> comma_sparse_word) \<Rightarrow>
      comma_decade_state \<Rightarrow> nat option" where
  "comma_sparse_decade_weight_summary rows s =
    (case s of Comma_Decade r x \<Rightarrow>
      if comma_decade_admitted s then
        comma_sparse_lookup_terminal_weight (rows (comma_offset_orbit x)) r
      else None)"

lemma comma_sparse_decade_weight_summary_of_exact:
  assumes summary:
    "comma_sparse_decade_summary rows s=Some (height,terminal)"
    and terminal: "comma_terminal_weight_admitted terminal"
  shows "comma_sparse_decade_weight_summary rows s=
    Some (comma_terminal_weight_encode height terminal)"
proof (cases s)
  case (Comma_Decade r x)
  have admitted: "comma_decade_admitted (Comma_Decade r x)"
    using summary by (simp only: comma_sparse_decade_summary_def Comma_Decade
      comma_decade_state.case option.distinct
      split: if_splits option.splits comma_word_result.splits)
  have lookup:
    "comma_sparse_lookup (rows (comma_offset_orbit x)) r=
      Some (Comma_Word_Stop height terminal)"
    using summary admitted by (simp only: comma_sparse_decade_summary_def Comma_Decade
      comma_decade_state.case if_True option.inject prod.inject
      comma_word_result.inject comma_word_result.distinct option.distinct
      split: option.splits comma_word_result.splits)
  have weighted:
    "comma_sparse_lookup_terminal_weight (rows (comma_offset_orbit x)) r=
      Some (comma_terminal_weight_encode height terminal)"
    by (rule comma_sparse_lookup_terminal_weight_stop[OF terminal lookup])
  show ?thesis using summary weighted
    by (simp only: comma_sparse_decade_weight_summary_def Comma_Decade
      comma_decade_state.case admitted if_True weighted)
qed

lemma comma_sparse_decade_weight_summary_witness:
  assumes weight:
    "comma_sparse_decade_weight_summary rows s=Some D"
  obtains height terminal where
    "comma_sparse_decade_summary rows s=Some (height,terminal)"
    "comma_terminal_weight_admitted terminal"
    "D=comma_terminal_weight_encode height terminal"
proof (cases s)
  case (Comma_Decade r x)
  have admitted: "comma_decade_admitted (Comma_Decade r x)"
    using weight by (simp only: comma_sparse_decade_weight_summary_def Comma_Decade
      comma_decade_state.case option.distinct split: if_splits)
  obtain height terminal where lookup:
    "comma_sparse_lookup (rows (comma_offset_orbit x)) r=
      Some (Comma_Word_Stop height terminal)"
    and terminal_admitted: "comma_terminal_weight_admitted terminal"
    and encoded: "D=comma_terminal_weight_encode height terminal"
    by (rule comma_sparse_lookup_terminal_weight_some_witness[of
      "rows (comma_offset_orbit x)" r D])
      (use weight admitted in \<open>simp only: comma_sparse_decade_weight_summary_def
        Comma_Decade comma_decade_state.case admitted if_True
        option.distinct option.inject prod.inject comma_word_result.inject
        comma_word_result.distinct\<close>)
  have summary: "comma_sparse_decade_summary rows (Comma_Decade r x)=
      Some (height,terminal)"
    using admitted lookup by (simp add: comma_sparse_decade_summary_def)
  have summary_source:
    "comma_sparse_decade_summary rows s=Some (height,terminal)"
    using Comma_Decade summary by simp
  show thesis
    by (rule that[OF summary_source terminal_admitted encoded])
qed

ML \<open>Comma_Native_Summary_Profile.checkpoint "before-total-exact"\<close>

theorem comma_sparse_decade_summary_total_exact:
  assumes powers: "\<forall>i<46. comma_sparse_refines
      (\<lambda>r. comma_orbit_word 5 r i) (rows i)"
    and stops: "\<forall>i<46. \<forall>out bits. (out,bits)\<in>set (rows i) \<longrightarrow>
      (\<exists>h terminal. out=Comma_Word_Stop h terminal \<and> h\<le>26)"
    and valid: "comma_decade_admitted s"
  shows "\<exists>h terminal. comma_sparse_decade_summary rows s=Some (h,terminal) \<and>
    h\<le>26 \<and> comma_decade_exact_summary s h terminal"
proof -
  obtain r x where state: "s=Comma_Decade r x" by (cases s)
  have phase: "r<924" and offset: "x\<le>90"
    using valid by (simp_all only: state comma_decade_admitted.simps)
  let ?i = "comma_offset_orbit x"
  have fiber: "?i<46" by (rule comma_offset_orbit_bound)
  have lookup:
    "\<exists>out. comma_sparse_lookup (rows ?i) r=Some out \<and>
      comma_orbit_word 5 r ?i=out"
    by (rule comma_sparse_lookup_refines_phase[OF powers[rule_format, OF fiber] phase])
  then obtain out where found:
    "comma_sparse_lookup (rows ?i) r=Some out"
    "comma_orbit_word 5 r ?i=out" by blast
  obtain h terminal where stop:
    "out=Comma_Word_Stop h terminal" "h\<le>26"
    using stops[rule_format, OF fiber] comma_sparse_lookup_some_witness[OF found(1)]
    by blast
  have orbit_value: "comma_orbit_word 5 r ?i=Comma_Word_Stop h terminal"
    by (rule trans[OF found(2) stop(1)])
  have admitted: "comma_decade_admitted (Comma_Decade r x)"
    using valid state by simp
  have projection_refinement:
    "comma_word_project comma_offset_orbit
      (comma_decade_block_power 5 (Comma_Decade r x)) =
        comma_orbit_word 5 r (comma_offset_orbit x)"
    by (rule comma_orbit_word_refines[OF admitted])
  ML_prf \<open>Comma_Native_Summary_Profile.checkpoint "before-total-exact-projection-compose"\<close>
  have projection:
    "comma_word_project comma_offset_orbit
      (comma_decade_block_power 5 (Comma_Decade r x)) =
        Comma_Word_Stop h terminal"
    by (rule trans[OF projection_refinement orbit_value])
  ML_prf \<open>Comma_Native_Summary_Profile.checkpoint "after-projection-compose"\<close>
  have powered_stop:
    "comma_decade_block_power 5 (Comma_Decade r x)=Comma_Block_Stop h terminal"
    by (rule iffD1[OF comma_word_project_stop_iff projection])
  ML_prf \<open>Comma_Native_Summary_Profile.checkpoint "after-powered-stop"\<close>
  have exact: "comma_decade_exact_summary (Comma_Decade r x) h terminal"
    by (rule comma_decade_block_power_stop(2)[OF powered_stop])
  ML_prf \<open>Comma_Native_Summary_Profile.checkpoint "after-exact"\<close>
  have summary:
    "comma_sparse_decade_summary rows s=Some (h,terminal)"
    using found(1) stop(1) admitted state
    by (simp only: comma_sparse_decade_summary_def state admitted found(1) stop(1)
        comma_decade_state.case option.case comma_word_result.case if_True)
  ML_prf \<open>Comma_Native_Summary_Profile.checkpoint "after-summary"\<close>
  have exact_source: "comma_decade_exact_summary s h terminal"
    using exact by (simp only: state)
  show ?thesis
    by (intro exI[of _ h] exI[of _ terminal] conjI;
        rule summary stop(2) exact_source)
qed

theorem comma_sparse_decade_weight_summary_total_exact:
  assumes powers: "\<forall>i<46. comma_sparse_refines
      (\<lambda>r. comma_orbit_word 5 r i) (rows i)"
    and stops: "\<forall>i<46. \<forall>out bits. (out,bits)\<in>set (rows i) \<longrightarrow>
      (\<exists>height terminal. out=Comma_Word_Stop height terminal \<and> height\<le>26)"
    and valid: "comma_decade_admitted s"
  shows "\<exists>D. comma_sparse_decade_weight_summary rows s=Some D \<and>
    comma_decade_weighted_stop s D \<and> D\<le>242"
proof -
  obtain height terminal where summary:
    "comma_sparse_decade_summary rows s=Some (height,terminal)"
    and height_bound: "height\<le>26"
    and exact: "comma_decade_exact_summary s height terminal"
    using comma_sparse_decade_summary_total_exact[OF powers stops valid] by blast
  have terminal_admitted: "comma_terminal_weight_admitted terminal"
    by (rule comma_decade_exact_summary_terminal_admitted[OF exact])
  let ?D = "comma_terminal_weight_encode height terminal"
  have selected: "comma_sparse_decade_weight_summary rows s=Some ?D"
    by (rule comma_sparse_decade_weight_summary_of_exact[OF summary terminal_admitted])
  have decoded: "comma_terminal_weight_decode ?D=(height,terminal)"
    by (rule comma_terminal_weight_decode_encode[OF terminal_admitted])
  have decoded_exact:
    "comma_decade_exact_summary s
      (fst (comma_terminal_weight_decode ?D))
      (snd (comma_terminal_weight_decode ?D))"
    using exact decoded by simp
  have weighted_stop: "comma_decade_weighted_stop s ?D"
    by (rule iffD2[OF comma_decade_weighted_stop_iff_decoded_exact[of s ?D]
      decoded_exact])
  have digit_bound: "comma_terminal_weight_digit terminal<9"
    by (rule comma_terminal_weight_digit_bound[OF terminal_admitted])
  have bound: "?D\<le>242"
    using height_bound digit_bound
    by (simp add: comma_terminal_weight_encode_def; arith)
  show ?thesis using selected weighted_stop bound by blast
qed

theorem comma_sparse_decade_weight_summary_complete_exact:
  assumes powers: "\<forall>i<46. comma_sparse_refines
      (\<lambda>r. comma_orbit_word 5 r i) (rows i)"
    and stops: "\<forall>i<46. \<forall>out bits. (out,bits)\<in>set (rows i) \<longrightarrow>
      (\<exists>height terminal. out=Comma_Word_Stop height terminal \<and> height\<le>26)"
    and valid: "comma_decade_admitted s"
  obtains D height terminal where
    "comma_sparse_decade_weight_summary rows s=Some D"
    "comma_terminal_weight_decode D=(height,terminal)"
    "comma_sparse_decade_summary rows s=Some (height,terminal)"
proof -
  obtain height terminal where summary:
    "comma_sparse_decade_summary rows s=Some (height,terminal)"
    and height_bound: "height\<le>26"
    and exact: "comma_decade_exact_summary s height terminal"
    using comma_sparse_decade_summary_total_exact[OF powers stops valid] by blast
  have terminal_admitted: "comma_terminal_weight_admitted terminal"
    by (rule comma_decade_exact_summary_terminal_admitted[OF exact])
  let ?D = "comma_terminal_weight_encode height terminal"
  have selected: "comma_sparse_decade_weight_summary rows s=Some ?D"
    by (rule comma_sparse_decade_weight_summary_of_exact[OF summary terminal_admitted])
  have decoded: "comma_terminal_weight_decode ?D=(height,terminal)"
    by (rule comma_terminal_weight_decode_encode[OF terminal_admitted])
  show thesis
    by (rule that[OF selected decoded summary])
qed

ML \<open>
  val _ = Comma_Native_Summary_Profile.checkpoint "before-oracle-audit";
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_sparse_lookup_refines_phase
      comma_relation_from_rendered_list
      comma_sparse_decade_summary_total_exact
      comma_sparse_lookup_terminal_weight_stop
      comma_sparse_lookup_terminal_weight_rejects_invalid
      comma_sparse_lookup_terminal_weight_rejects_malformed_fork
      comma_sparse_lookup_terminal_weight_some_witness
      comma_sparse_decade_weight_summary_of_exact
      comma_sparse_decade_weight_summary_witness
      comma_sparse_decade_weight_summary_total_exact
      comma_sparse_decade_weight_summary_complete_exact})
    then () else error "Native sparse summary refinement depends on an oracle";
  val _ = Comma_Native_Summary_Profile.checkpoint "after-oracle-audit";
\<close>

end
