theory Comma_Decade_Blocks
  imports Comma_Decade_Residual_Core.Comma_Decade_Residual_Core
begin

text \<open>These finite spatial layers implement demanded source lookup
against the canonical rank-free block semantics. They provide no candidate
rank, totality assertion or alternative residual owner.\<close>

text \<open>A layer has exactly the 91 admitted offsets. Malformed layers
and out-of-domain lookup fail closed rather than relying on unspecified nth.\<close>

definition comma_decade_layer_lookup :: "comma_decade_block_result list \<Rightarrow> nat \<Rightarrow> comma_decade_block_result" where
  "comma_decade_layer_lookup layer x =
    (if length layer=91 \<and> x<91 then layer!x else Comma_Block_Invalid)"

definition comma_decade_layer_correct :: "nat \<Rightarrow> nat \<Rightarrow> comma_decade_block_result list \<Rightarrow> bool" where
  "comma_decade_layer_correct k r layer =
    (length layer=91 \<and> (\<forall>x<91. layer!x=comma_decade_block_power k (Comma_Decade r x)))"

definition comma_decade_base_layer :: "nat \<Rightarrow> comma_decade_block_result list" where
  "comma_decade_base_layer r=map (\<lambda>x. comma_decade_block_atom (Comma_Decade r x)) [0..<91]"

lemma comma_decade_base_layer_correct:
  "comma_decade_layer_correct 0 r (comma_decade_base_layer r)"
  by (simp add: comma_decade_layer_correct_def comma_decade_base_layer_def)

lemma comma_decade_layer_lookup_correct:
  assumes "comma_decade_layer_correct k r layer" "x<91"
  shows "comma_decade_layer_lookup layer x=comma_decade_block_power k (Comma_Decade r x)"
  using assms by (simp add: comma_decade_layer_correct_def comma_decade_layer_lookup_def)

fun comma_decade_layer_resume ::
  "nat \<Rightarrow> comma_decade_block_result list \<Rightarrow> comma_decade_state \<Rightarrow> comma_decade_block_result" where
  "comma_decade_layer_resume phase layer (Comma_Decade r x)=
    (if phase<924 \<and> r=phase then comma_decade_layer_lookup layer x else Comma_Block_Invalid)"

definition comma_decade_layer_square ::
  "nat \<Rightarrow> nat \<Rightarrow> comma_decade_block_result list \<Rightarrow>
   comma_decade_block_result list \<Rightarrow> comma_decade_block_result list" where
  "comma_decade_layer_square k r left right =
    (if r<924 \<and> length left=91 \<and> length right=91 then
      map (\<lambda>answer. comma_decade_block_then (2^k) answer
        (comma_decade_layer_resume ((r+2^k) mod 924) right)) left
     else [])"

theorem comma_decade_layer_square_correct:
  assumes phase: "r<924"
    and left: "comma_decade_layer_correct k r left"
    and right: "comma_decade_layer_correct k ((r+2^k) mod 924) right"
  shows "comma_decade_layer_correct (Suc k) r (comma_decade_layer_square k r left right)"
proof -
  have lengths: "length left=91" "length right=91"
    using left right by (simp_all add: comma_decade_layer_correct_def)
  have point: "\<And>x. x<91 \<Longrightarrow>
    (comma_decade_layer_square k r left right)!x=
      comma_decade_block_power (Suc k) (Comma_Decade r x)"
  proof -
    fix x :: nat assume x: "x<91"
    have admitted: "comma_decade_admitted (Comma_Decade r x)" using phase x by simp
    have current: "left!x=comma_decade_block_power k (Comma_Decade r x)"
      using left x by (simp add: comma_decade_layer_correct_def)
    have index: "x<length left" using x lengths(1) by simp
    show "(comma_decade_layer_square k r left right)!x=
      comma_decade_block_power (Suc k) (Comma_Decade r x)"
    proof (cases "comma_decade_block_power k (Comma_Decade r x)")
      case (Comma_Block_Live t)
      obtain a b where t: "t=Comma_Decade a b" by (cases t) auto
      have live: "comma_decade_block_power k (Comma_Decade r x)=Comma_Block_Live (Comma_Decade a b)"
        using Comma_Block_Live by (simp only: t)
      have helix: "a=(r+2^k) mod 924" "b<91"
        using comma_decade_block_power_live_helix[OF admitted live] by auto
      have lookup: "comma_decade_layer_resume ((r+2^k) mod 924) right t=
        comma_decade_block_power k t"
        using comma_decade_layer_lookup_correct[OF right helix(2)]
        by (simp add: t helix(1))
      have guard: "r<924 \<and> length left=91 \<and> length right=91" using phase lengths by simp
      show ?thesis
        by (simp only: comma_decade_layer_square_def guard HOL.simp_thms if_True nth_map[OF index]
          current comma_decade_block_power.simps Comma_Block_Live
          comma_decade_block_then.simps lookup)
    qed (simp_all add: comma_decade_layer_square_def phase lengths current nth_map[OF index])
  qed
  show ?thesis using phase lengths point
    by (simp add: comma_decade_layer_correct_def comma_decade_layer_square_def)
qed

fun comma_decade_block_stopped_below :: "nat \<Rightarrow> comma_decade_block_result \<Rightarrow> bool" where
  "comma_decade_block_stopped_below bound (Comma_Block_Stop h terminal)=(h\<le>bound)"
| "comma_decade_block_stopped_below bound _=False"

definition comma_decade_layer_complete :: "nat \<Rightarrow> comma_decade_block_result list \<Rightarrow> bool" where
  "comma_decade_layer_complete bound layer =
    (length layer=91 \<and> list_all (comma_decade_block_stopped_below bound) layer)"

lemma comma_decade_layer_complete_sound:
  assumes correct: "comma_decade_layer_correct k r layer"
    and complete: "comma_decade_layer_complete bound layer" and x: "x<91"
  shows "\<exists>h terminal. comma_decade_block_power k (Comma_Decade r x)=
    Comma_Block_Stop h terminal \<and> h\<le>bound"
proof -
  have length: "length layer=91" using correct by (simp add: comma_decade_layer_correct_def)
  have member: "layer!x \<in> set layer" using x length by simp
  have stopped: "comma_decade_block_stopped_below bound (layer!x)"
    using complete member by (auto simp: comma_decade_layer_complete_def list_all_iff)
  have evaluated: "layer!x=comma_decade_block_power k (Comma_Decade r x)"
    using correct x by (simp add: comma_decade_layer_correct_def)
  show ?thesis using stopped by (cases "layer!x") (auto simp only: comma_decade_block_stopped_below.simps evaluated)
qed

text \<open>The B5 result is conditional on the concrete all-state layer check.
The definitions above do not assert that check succeeds, nor a work bound for
an evaluator that recursively expands these function applications.\<close>


ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_decade_base_layer_correct comma_decade_layer_lookup_correct
      comma_decade_layer_square_correct comma_decade_layer_complete_sound})
    then () else error "Decade layer refinement depends on an oracle";
\<close>
end
