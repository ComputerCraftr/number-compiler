theory Comma_Native_Summary_Instance
  imports Comma_Sparse_Power_Instance.Comma_Sparse_Power_Instance
    Comma_Native_Boundary.Comma_Native_Boundary
begin


text \<open>The concrete B32 sparse certificate is the sole provider for the
native decade summary. Its checked fiber refinements give phase coverage and exact
outputs; its stop bound rules out live and invalid results. The generic
lookup then supplies the exact inductive summary consumed by the physical
occurrence lift.\<close>

lemma comma_native_B32_refines_all:
  "\<forall>i<46. comma_sparse_refines
    (\<lambda>r. comma_orbit_word 5 r i)
    (comma_checked_sparse_B32_rows i)"
proof (intro allI impI)
  fix i assume "i<46"
  then show "comma_sparse_refines
      (\<lambda>r. comma_orbit_word 5 r i)
      (comma_checked_sparse_B32_rows i)"
    by (rule comma_checked_sparse_B32_refines)
qed

lemma comma_native_B32_stop26_all:
  "\<forall>i<46. \<forall>out bits.
    (out,bits)\<in>set (comma_checked_sparse_B32_rows i) \<longrightarrow>
    (\<exists>h terminal. out=Comma_Word_Stop h terminal \<and> h\<le>26)"
proof (intro allI impI)
  fix i out bits
  assume fiber: "i<46"
    and member: "(out,bits)\<in>set (comma_checked_sparse_B32_rows i)"
  have stops: "comma_sparse_power_rows_stop26 (comma_checked_sparse_B32_rows i)"
    by (rule comma_checked_sparse_B32_stop26[OF fiber])
  show "\<exists>h terminal. out=Comma_Word_Stop h terminal \<and> h\<le>26"
    using comma_sparse_power_rows_stop26_member[OF stops member] by blast
qed

definition comma_native_decade_summary ::
  "comma_decade_state \<Rightarrow> comma_decade_residual option" where
  "comma_native_decade_summary s =
    comma_sparse_decade_summary comma_checked_sparse_B32_rows s"

theorem comma_native_decade_summary_total_exact:
  assumes "comma_decade_admitted s"
  shows "\<exists>h terminal.
    comma_native_decade_summary s=Some (h,terminal) \<and>
    h\<le>26 \<and> comma_decade_exact_summary s h terminal"
  using comma_sparse_decade_summary_total_exact
      [OF comma_native_B32_refines_all comma_native_B32_stop26_all assms]
  by (simp add: comma_native_decade_summary_def)

theorem comma_native_decade_summary_ordered_occurrence:
  assumes "x\<le>90" "5\<le>p"
  obtains h terminal w t where
    "comma_native_decade_summary (Comma_Decade (p mod 924) x) = Some (h,terminal)"
    "h\<le>26"
    "comma_literal_path w (comma_chart_value p (Comma_Entry 1 0 x))
      (comma_chart_value (p+h) t)"
    "comma_large_children (comma_sector_number t) (p+h) (comma_chart_value (p+h) t)
      = comma_summary_ordered_children terminal (p+h)"
    "\<And>v. comma_child (comma_chart_value (p+h) t) v \<longleftrightarrow>
      v\<in>set (comma_summary_ordered_children terminal (p+h))"
proof -
  obtain h terminal w t where generic:
    "comma_sparse_decade_summary comma_checked_sparse_B32_rows
      (Comma_Decade (p mod 924) x) = Some (h,terminal)"
    "h\<le>26"
    "comma_literal_path w (comma_chart_value p (Comma_Entry 1 0 x))
      (comma_chart_value (p+h) t)"
    "comma_large_children (comma_sector_number t) (p+h) (comma_chart_value (p+h) t)
      = comma_summary_ordered_children terminal (p+h)"
    "\<And>v. comma_child (comma_chart_value (p+h) t) v \<longleftrightarrow>
      v\<in>set (comma_summary_ordered_children terminal (p+h))"
    using comma_sparse_summary_ordered_occurrence
      [OF comma_native_B32_refines_all comma_native_B32_stop26_all assms] .
  have summary:
    "comma_native_decade_summary (Comma_Decade (p mod 924) x) = Some (h,terminal)"
    using generic(1) by (simp only: comma_native_decade_summary_def)
  show thesis
    by (rule that[OF summary generic(2,3,4,5)])
qed

theorem comma_native_boundary_ordered_occurrence:
  assumes valid: "comma_boundary_valid q"
    and exponent: "5\<le>p"
    and phase: "p mod 924=snd (snd q)"
  obtains outcome endpoint w where
    "comma_unique_literal_path w (comma_boundary_value q p) endpoint"
    "comma_native_boundary_children q outcome =
      (case outcome of Comma_Landmine_At d \<Rightarrow> []
       | Comma_Fork_At a d \<Rightarrow>
          [(Comma_N,a,(snd (snd q)+d) mod 924),
           (Comma_Z,a,(snd (snd q)+d) mod 924)])"
    "\<And>v. comma_child endpoint v \<longleftrightarrow>
      (\<exists>child\<in>set (comma_native_boundary_children q outcome).
        v=comma_boundary_value child (p+comma_native_outcome_delta outcome))"
proof -
  show thesis
    by (rule comma_sparse_boundary_ordered_occurrence
      [OF comma_native_B32_refines_all comma_native_B32_stop26_all assms])
qed

definition comma_native_B32_boundary_step ::
  "comma_boundary_state \<Rightarrow> comma_finite_outcome option" where
  "comma_native_B32_boundary_step = comma_native_boundary_step comma_checked_sparse_B32_rows"

theorem comma_native_B32_boundary_step_ordered_occurrence:
  assumes "comma_boundary_valid q" "5\<le>p" "p mod 924=snd (snd q)"
  obtains outcome endpoint w where
    "comma_native_B32_boundary_step q=Some outcome"
    "comma_unique_literal_path w (comma_boundary_value q p) endpoint"
    "\<And>v. comma_child endpoint v \<longleftrightarrow>
      (\<exists>child\<in>set (comma_native_boundary_children q outcome).
        v=comma_boundary_value child (p+comma_native_outcome_delta outcome))"
proof -
  obtain outcome endpoint w where result:
    "comma_native_boundary_step comma_checked_sparse_B32_rows q=Some outcome"
    "comma_unique_literal_path w (comma_boundary_value q p) endpoint"
    "\<And>v. comma_child endpoint v \<longleftrightarrow>
      (\<exists>child\<in>set (comma_native_boundary_children q outcome).
        v=comma_boundary_value child (p+comma_native_outcome_delta outcome))"
    using comma_sparse_boundary_ordered_occurrence_step
      [OF comma_native_B32_refines_all comma_native_B32_stop26_all assms] by blast
  have step: "comma_native_B32_boundary_step q=Some outcome"
    using result(1) by (simp only: comma_native_B32_boundary_step_def)
  show thesis by (rule that[OF step result(2,3)])
qed

text \<open>Concrete wrapper for the generic native boundary projection.  This
keeps the B32 provider and all of its checked premises explicit at the
consumer boundary; it does not assert rank descent or use the legacy total
macro.  The separate Entry wrapper below is used for the 10\<^sup>5+x root
slice, which is not a N/Z boundary occurrence.\<close>

theorem comma_native_B32_infinite_path_projects_admitted_child:
  assumes valid: "comma_boundary_valid q"
    and exponent: "5\<le>p"
    and phase: "p mod 924=snd (snd q)"
    and path: "comma_native_infinite_literal_path
      (comma_boundary_value q p) stream"
  obtains outcome endpoint w child where
    "comma_native_B32_boundary_step q=Some outcome"
    "comma_unique_literal_path w
      (comma_boundary_value q p) endpoint"
    "child\<in>set (comma_native_boundary_children q outcome)"
    "stream (Suc w)=comma_boundary_value child
      (p+comma_native_outcome_delta outcome)"
    "comma_native_infinite_literal_path
      (comma_boundary_value child (p+comma_native_outcome_delta outcome))
      (\<lambda>j. stream (w+Suc j))"
    "comma_boundary_valid child"
    "(p+comma_native_outcome_delta outcome) mod 924=
      snd (snd child)"
proof -
  obtain outcome endpoint w child where result:
    "comma_native_boundary_step comma_checked_sparse_B32_rows q=Some outcome"
    "comma_unique_literal_path w (comma_boundary_value q p) endpoint"
    "child\<in>set (comma_native_boundary_children q outcome)"
    "stream (Suc w)=comma_boundary_value child
      (p+comma_native_outcome_delta outcome)"
    "comma_native_infinite_literal_path
      (comma_boundary_value child (p+comma_native_outcome_delta outcome))
      (\<lambda>j. stream (w+Suc j))"
    "comma_boundary_valid child"
    "(p+comma_native_outcome_delta outcome) mod 924=snd (snd child)"
    using comma_native_infinite_path_projects_admitted_child
      [OF comma_native_B32_refines_all comma_native_B32_stop26_all
        valid exponent phase path] by blast
  have step:
    "comma_native_B32_boundary_step q=Some outcome"
    using result(1) by (simp only: comma_native_B32_boundary_step_def)
  show thesis
    by (rule that[OF step result(2-7)])
qed

text \<open>The root slice starts at an Entry value 10\<^sup>5+x, so applying the
N/Z boundary theorem there would be a type/semantic error.  This wrapper
projects an arbitrary literal continuation through the already checked
native decade summary and its unique Entry prefix, then exposes the exact
next literal and its tail.  No boundary rank or forest claim is made here.\<close>

theorem comma_native_B32_entry_infinite_path_projects:
  assumes offset: "x\<le>90"
    and exponent: "5\<le>p"
    and path: "path 0=comma_chart_value p (Comma_Entry 1 0 x) \<and>
      (\<forall>j. comma_child (path j) (path (Suc j)))"
  obtains h terminal weight t child where
    "comma_native_decade_summary
      (Comma_Decade (p mod 924) x)=Some (h,terminal)"
    "h\<le>26"
    "comma_unique_literal_path weight
      (comma_chart_value p (Comma_Entry 1 0 x))
      (comma_chart_value (p+h) t)"
    "path weight=comma_chart_value (p+h) t"
    "child\<in>set (comma_summary_ordered_children terminal (p+h))"
    "path (Suc weight)=child"
    "comma_native_infinite_literal_path child
      (\<lambda>j. path (weight+Suc j))"
proof -
  obtain h terminal weight t where generic:
    "comma_sparse_decade_summary comma_checked_sparse_B32_rows
      (Comma_Decade (p mod 924) x)=Some (h,terminal)"
    "h\<le>26"
    "comma_unique_literal_path weight
      (comma_chart_value p (Comma_Entry 1 0 x))
      (comma_chart_value (p+h) t)"
    "comma_large_children (comma_sector_number t) (p+h)
      (comma_chart_value (p+h) t)=
      comma_summary_ordered_children terminal (p+h)"
    "\<And>v. comma_child (comma_chart_value (p+h) t) v \<longleftrightarrow>
      v\<in>set (comma_summary_ordered_children terminal (p+h))"
    using comma_sparse_summary_unique_ordered_occurrence
      [OF comma_native_B32_refines_all comma_native_B32_stop26_all
        offset exponent] by blast
  have summary:
    "comma_native_decade_summary (Comma_Decade (p mod 924) x)=Some (h,terminal)"
    using generic(1) by (simp only: comma_native_decade_summary_def)
  have initial:
      "path 0=comma_chart_value p (Comma_Entry 1 0 x)"
    using path by blast
  have edges: "\<And>j. comma_child (path j) (path (Suc j))"
    using path by blast
  have prefix: "comma_literal_path weight
      (comma_chart_value p (Comma_Entry 1 0 x)) (path weight)"
    using comma_native_infinite_path_prefix[where path=path and n=weight, OF edges]
      initial by simp
  have endpoint: "path weight=comma_chart_value (p+h) t"
    by (rule comma_unique_literal_path_endpoint[OF generic(3) prefix])
  have next_child:
      "comma_child (comma_chart_value (p+h) t) (path (Suc weight))"
    using edges[of weight] endpoint by simp
  have member: "path (Suc weight)\<in>
      set (comma_summary_ordered_children terminal (p+h))"
    using generic(5)[of "path (Suc weight)"] next_child endpoint by simp
  have tail_start:
    "(\<lambda>j. path (weight+Suc j)) 0=path (Suc weight)" by simp
  have tail_edges:
    "comma_child ((\<lambda>j. path (weight+Suc j)) j)
      ((\<lambda>j. path (weight+Suc j)) (Suc j))" for j
    using edges[of "weight+Suc j"] by (simp add: add.assoc)
  have tail:
    "comma_native_infinite_literal_path (path (Suc weight))
      (\<lambda>j. path (weight+Suc j))"
    using tail_start tail_edges
    by (simp add: comma_native_infinite_literal_path_def)
  show thesis
    by (rule that[OF summary generic(2) generic(3) endpoint
      member refl tail])
qed

text \<open>Conditional rank adapter.  The B32 data and occurrence theorems do
not themselves prove rank descent, so this theorem deliberately leaves that
obligation as an explicit premise.  It is the only missing premise needed
to specialize the generic well-founded native theorem; no candidate rank is
silently substituted here.\<close>

theorem comma_native_B32_ranked_state_no_infinite_path_if_descend:
  fixes rank :: "comma_boundary_state \<Rightarrow> nat option"
  assumes descend: "\<And>source exponent k a d child.
      comma_boundary_valid source \<Longrightarrow>
      5\<le>exponent \Longrightarrow
      exponent mod 924=snd (snd source) \<Longrightarrow
      rank source=Some k \<Longrightarrow
      comma_native_B32_boundary_step source=Some (Comma_Fork_At a d) \<Longrightarrow
      child\<in>set (comma_native_boundary_children source (Comma_Fork_At a d)) \<Longrightarrow
      (\<exists>j<k. rank child=Some j)"
    and valid: "comma_boundary_valid q"
    and exponent: "5\<le>p"
    and phase: "p mod 924=snd (snd q)"
    and ranked: "rank q=Some k"
  shows "\<not>comma_native_infinite_literal_path
    (comma_boundary_value q p) stream"
proof (rule comma_native_ranked_state_no_infinite_path
  [OF comma_native_B32_refines_all comma_native_B32_stop26_all])
  show "\<And>source exponent k a d child.
      comma_boundary_valid source \<Longrightarrow>
      5\<le>exponent \Longrightarrow
      exponent mod 924=snd (snd source) \<Longrightarrow
      rank source=Some k \<Longrightarrow
      comma_native_boundary_step comma_checked_sparse_B32_rows source=
        Some (Comma_Fork_At a d) \<Longrightarrow
      child\<in>set (comma_native_boundary_children source (Comma_Fork_At a d)) \<Longrightarrow
      (\<exists>j<k. rank child=Some j)"
    using descend by (simp only: comma_native_B32_boundary_step_def)
  show "comma_boundary_valid q" by fact
  show "5\<le>p" by fact
  show "p mod 924=snd (snd q)" by fact
  show "rank q=Some k" by fact
qed

ML \<open>
  val concrete = @{thms comma_native_B32_refines_all comma_native_B32_stop26_all
    comma_native_decade_summary_total_exact
    comma_native_decade_summary_ordered_occurrence
    comma_native_boundary_ordered_occurrence
    comma_native_B32_boundary_step_ordered_occurrence
    comma_native_B32_infinite_path_projects_admitted_child
    comma_native_B32_entry_infinite_path_projects
    comma_native_B32_ranked_state_no_infinite_path_if_descend}
  val _ = if null (Thm_Deps.all_oracles concrete) then ()
    else error "Native B32 summary instance depends on an oracle"
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Native B32 summary instance" concrete
\<close>

end
