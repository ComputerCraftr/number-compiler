theory Comma_Symbolic_Near_Cut
  imports Comma_Symbolic_Entry_Cut
begin

text \<open>Split an already admitted strict Near prefix. The selected
headroom is reconstructed from the finite periodic displacement rather than
an indexed occurrence list. The decisive terminal edge is outside the cut.\<close>

lemma comma_symbolic_near_prefix_split:
  assumes path: "comma_near_prefix n f h t" and bound: "j \<le> n"
  shows "\<exists>u. comma_near_prefix j f h u \<and>
    comma_near_prefix (n-j) f u t"
  using path bound
proof (induction j arbitrary: n h)
  case 0
  then show ?case by auto
next
  case (Suc j)
  then obtain m where n: "n = Suc m" by (cases n) auto
  obtain v0 where step: "comma_finite_step 0 (Comma_Near f 0 h) =
      Comma_Next (Comma_Near f 0 v0)"
    and tail: "comma_near_prefix m f v0 t"
    using Suc.prems n by auto
  have "j \<le> m" using Suc.prems n by simp
  then obtain u where left: "comma_near_prefix j f v0 u"
    and right: "comma_near_prefix (m-j) f u t"
    using Suc.IH[OF tail] by blast
  have "comma_near_prefix (Suc j) f h u" using step left by simp
  moreover have "comma_near_prefix (n-Suc j) f u t" using right n by simp
  ultimately show ?case by blast
qed

definition comma_symbolic_near_cut :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_symbolic_near_cut f h j =
    h - comma_period_displacement f ((10 - h mod 10) mod 10) j"

theorem comma_symbolic_near_cut_exact:
  fixes f p delta h t n j :: nat
  assumes sector: "1 \<le> f" "f \<le> 9"
    and exponent: "5 \<le> p" and headroom: "1 \<le> h" "h \<le> 540"
    and prefix: "comma_near_prefix n f h t" and bound: "j \<le> n"
  defines "u \<equiv> comma_symbolic_near_cut f h j"
  shows "comma_literal_path j (comma_chart_value p (Comma_Near f delta h))
      (comma_chart_value p (Comma_Near f delta u))"
    and "comma_literal_path (n-j) (comma_chart_value p (Comma_Near f delta u))
      (comma_chart_value p (Comma_Near f delta t))"
proof -
  obtain v where left: "comma_near_prefix j f h v"
    and right: "comma_near_prefix (n-j) f v t"
    using comma_symbolic_near_prefix_split[OF prefix bound] by blast
  have exact: "h = v + comma_period_displacement f ((10 - h mod 10) mod 10) j"
    by (rule comma_near_prefix_displacement_refines[OF sector headroom refl left])
  have uv: "u = v" using exact by (simp add: u_def comma_symbolic_near_cut_def)
  have vb: "1 \<le> v \<and> v \<le> 540"
  proof (cases "j=0")
    case True
    have eq: "v = h" using left True by simp
    show ?thesis using eq headroom by simp
  next
    case False
    have reserve: "(if f < 9 then 2 else 1) \<le> v"
      by (rule comma_near_prefix_endpoint_reserve[OF sector headroom _ left]) (use False in simp)
    show ?thesis using reserve exact headroom by (cases "f<9") arith+
  qed
  have vbounds: "1 \<le> v" "v \<le> 540" using vb by auto
  show "comma_literal_path j (comma_chart_value p (Comma_Near f delta h))
      (comma_chart_value p (Comma_Near f delta u))"
    using comma_c1_near_chart_prefix_refinement(3)[OF sector exponent headroom left, where delta=delta]
    by (simp add: uv)
  show "comma_literal_path (n-j) (comma_chart_value p (Comma_Near f delta u))
      (comma_chart_value p (Comma_Near f delta t))"
    using comma_c1_near_chart_prefix_refinement(3)[OF sector exponent vbounds right, where delta=delta]
    by (simp add: uv)
qed


text \<open>The composed statement ends at the strict first-sector
preterminal. It does not select a physical child of a fork.\<close>

theorem comma_symbolic_first_sector_near_cut:
  fixes f p delta offset elapsed t j h steps n :: nat
    and event :: comma_finite_move
  assumes sector: "1 \<le> f" "f \<le> 9" and exponent: "5 \<le> p"
    and offset: "offset \<le> 98"
    and packet: "comma_c1_first_sector f p delta offset = (elapsed,t,event)"
  defines "h \<equiv> comma_finite_headroom f (p mod 924) delta offset"
    and "steps \<equiv> ((10 ^ (p + delta) - offset - h) div
      comma_finite_period f (offset mod 10)) * comma_cycle_length f"
    and "n \<equiv> fst (comma_near_closed_germ f h)"
  assumes bound: "j \<le> n"
  shows "comma_literal_path (steps+j) (comma_chart_value p (Comma_Entry f delta offset))
      (comma_chart_value p (Comma_Near f delta (comma_symbolic_near_cut f h j)))"
    and "comma_literal_path (elapsed-(steps+j))
      (comma_chart_value p (Comma_Near f delta (comma_symbolic_near_cut f h j)))
      (comma_chart_value p (Comma_Near f delta t))"
proof -
  have h: "1 \<le> h" "h \<le> 540"
    using comma_finite_entry_headroom_admitted[OF sector exponent offset, of delta]
    by (simp_all add: h_def)
  have first: "comma_literal_path steps (comma_chart_value p (Comma_Entry f delta offset))
      (comma_chart_value p (Comma_Near f delta h))"
    using comma_fused_entry_prefix_consumer(3)[OF sector exponent offset, where delta=delta]
    by (simp add: h_def steps_def)
  have prefix: "comma_near_prefix n f h t" and elapsed: "elapsed=steps+n"
    using comma_c1_first_sector_source[OF sector exponent offset packet]
    by (simp_all add: h_def steps_def n_def)
  have near: "comma_literal_path j (comma_chart_value p (Comma_Near f delta h))
      (comma_chart_value p (Comma_Near f delta (comma_symbolic_near_cut f h j)))"
    and tail: "comma_literal_path (n-j)
      (comma_chart_value p (Comma_Near f delta (comma_symbolic_near_cut f h j)))
      (comma_chart_value p (Comma_Near f delta t))"
    using comma_symbolic_near_cut_exact[OF sector exponent h prefix bound, where delta=delta]
    by simp_all
  show "comma_literal_path (steps+j) (comma_chart_value p (Comma_Entry f delta offset))
      (comma_chart_value p (Comma_Near f delta (comma_symbolic_near_cut f h j)))"
    by (rule comma_literal_path_append[OF first near])
  show "comma_literal_path (elapsed-(steps+j))
      (comma_chart_value p (Comma_Near f delta (comma_symbolic_near_cut f h j)))
      (comma_chart_value p (Comma_Near f delta t))"
    using tail elapsed by simp
qed

ML \<open>
  val checked = @{thms comma_symbolic_near_prefix_split
    comma_symbolic_near_cut_exact comma_symbolic_first_sector_near_cut};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Symbolic Near cut used an oracle";
  val _ = if Thm_Deps.has_skip_proof checked then
    error "Symbolic Near cut used a skipped proof" else ();
\<close>

end
