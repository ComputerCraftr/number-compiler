theory Reverse_Native_Slab_Joint
  imports Reverse_Native_Slab_Seam_Ports Reverse_Native_Slab_Collars
begin

definition slab_four_value :: "nat list \<Rightarrow> nat \<Rightarrow> nat" where
  "slab_four_value xs i = 18 - 2 * (slab_core_bit (xs!(i-3) \<noteq> 18) +
    3 * slab_core_bit (xs!(i-2) \<noteq> 18) + 3 * slab_core_bit (xs!(i-1) \<noteq> 18) +
    slab_core_bit (xs!i \<noteq> 18))"

text \<open>The source authorizes a fixed outer collar, a binomial interior,
and a contracting center. Four collar ticks recover the physical center
digit and the entire ordered pair field across either admitted birth schedule.\<close>
theorem slab_joint_four:
  fixes src :: "nat list" and left right z :: nat and rest core :: "nat list"
    and c k inner :: nat and ports :: "nat \<Rightarrow> bool"
    and init product :: "nat list \<times> nat list"
  assumes source: "src = 18 # z # rest" and valid: "valid_pair src"
    and positive: "0 < left" and span: "left + 64 \<le> right"
    and half: "2*right \<le> Suc (length src)"
    and symbols: "\<And>i. left \<le> i \<Longrightarrow> i < right \<Longrightarrow> reverse_native_slab_source_symbol (src!i)"
  defines "c \<equiv> left+8" and "k \<equiv> right-12" and "inner \<equiv> k+4"
    and "ports \<equiv> \<lambda>t::nat. t \<noteq> 0 \<or> 9 < src!c"
    and "init \<equiv> (take c src, slab_center k src)"
    and "product \<equiv> slab_collar_run ports init 4"
    and "core \<equiv> map (slab_four_value src) [c..<inner]"
  shows "(step ^^ 4) src = fst product @ core @ snd product @ rev core @ rev (fst product)"
    and "length ((step ^^ 4) src) = length src + 3"
    and "let last = slab_collar_run ports init 3;
             low = slab_inner_low (snd last) (carry_out (ports 3) (rev (fst last)))
        in low ! (length low div 2) = digits ((step ^^ 3) src) ! (length (digits ((step ^^ 3) src)) div 2)"
proof -
  let ?rows = "\<lambda>t. (step ^^ t) src"
  have small: "left+16 \<le> right" and upper: "right \<le> length src" using half span by arith+
  note seam = slab_outer_source_seam_ports[of z rest left right, folded source]
  have seams: "\<forall>t<4. let row = ?rows t; fixed = c; middle = k+t in
      valid_pair row \<and> fixed < length row \<and> middle < length row \<and>
      (if t=0 then reverse_native_slab_source_symbol (row!fixed) else 9 < row!fixed) \<and>
      (if t=0 then reverse_native_slab_source_symbol (row!middle) else 9 < row!middle)"
    unfolding c_def k_def by (rule seam(4)[OF valid positive small upper symbols])
  have width: "length (step (step (step (step src)))) = length src + 3"
    by (rule seam(3)[OF valid positive small upper symbols])
  show final: "length ((step ^^ 4) src) = length src+3"
    using width by (simp add: eval_nat_numeral)
  have guards: "valid_pair (?rows t) \<and> 2*c < length (?rows t) \<and>
       2*(k+t) < length (?rows t) \<and> ?rows t ! c \<noteq> 9 \<and> ?rows t ! (k+t) \<noteq> 9 \<and>
       ports t = (9 < ?rows t ! c)" if t: "t < 4" for t
  proof -
    have limits: "2*c < length (?rows t)" "2*(k+t) < length (?rows t)"
      unfolding c_def k_def using slab_iter_len[of src t] half span t by arith+
    show ?thesis using spec[OF seams, of t] t limits
      by (cases "t=0") (auto simp: ports_def Let_def reverse_native_slab_source_symbol_def)
  qed
  have collars: "product = (take c (?rows 4), slab_center inner (?rows 4))"
    unfolding product_def init_def inner_def by (rule slab_collar_run_exact[OF guards])
  have ci: "c \<le> inner" and bound: "2*inner \<le> length (?rows 4)"
    using final span half unfolding c_def k_def inner_def by arith+
  have v4: "valid_pair (?rows 4)" using valid
    by (simp add: eval_nat_numeral valid_pair_successor)
  have sym: "rev (?rows 4) = ?rows 4" using v4 by (simp add: valid_pair_def)
  have slice: "core = map (nth (?rows 4)) [c..<inner]"
    unfolding core_def
  proof (rule map_cong)
    show "[c..<inner] = [c..<inner]" by simp
    fix i assume member: "i \<in> set [c..<inner]"
    have lo: "5 < i" and hi: "i+4 < length src"
      using member span upper unfolding c_def inner_def k_def by (simp; arith)+
    have cover: "reverse_native_slab_source_symbol (src!j)"
      if "i-4 \<le> j" "j < i+4" for j
      by (rule symbols) (use member that in \<open>simp add: c_def inner_def k_def; arith\<close>)+
    show "slab_four_value src i = ?rows 4 ! i"
      using slab_outer_physical_four_packet(2)[of z rest i, folded source, OF valid lo hi cover]
      by (simp add: slab_four_value_def eval_nat_numeral)
  qed
  have in_bounds: "inner \<le> length (?rows 4)" using bound by arith
  have taken: "take inner (?rows 4) = take c (?rows 4) @ core"
    proof -
    have cat: "[0..<c] @ [c..<inner] = [0..<inner]"
      using upt_add_eq_append[of 0 c "inner-c"] ci by simp
    have cb: "c \<le> length (?rows 4)" using ci in_bounds by arith
    show ?thesis using arg_cong[OF cat, of "map (nth (?rows 4))"]
      by (simp add: map_nth_upt0 cb in_bounds slice)
  qed
  show "?rows 4 = fst product @ core @ snd product @ rev core @ rev (fst product)"
    using slab_source_split[OF bound sym] by (simp add: collars taken)
  let ?r = "?rows 3"
  let ?last = "slab_collar_run ports init 3"
  have smaller: "t < 3 \<Longrightarrow> t < (4::nat)" for t by simp
  have at3: "?last = (take c ?r, slab_center (k+3) ?r)"
    unfolding init_def by (rule slab_collar_run_exact) (rule guards[OF smaller])
  have src3: "valid_pair ?r" and outer3: "2*c < length ?r" and inner3: "2*(k+3) < length ?r"
    and oc: "?r!c \<noteq> 9" and ic: "?r!(k+3) \<noteq> 9" and port3: "ports 3 = (9 < ?r!c)"
    using guards[of 3] by auto
  have clock3: "carry_out (ports 3) (rev (take c ?r)) = carry_out False ?r"
    using slab_outer_collar_at(1)[OF src3 outer3 oc] port3 by simp
  let ?low = "slab_inner_low (snd ?last) (carry_out (ports 3) (rev (fst ?last)))"
  have inside: "2*Suc (k+3) < length (digits ?r)"
    using slab_iter_len[of src 3] half span by (simp add: length_digits_exact k_def; arith)
  have center: "?low ! (length ?low div 2) = digits ?r ! (length (digits ?r) div 2)"
    using slab_contract_physical_center[OF src3 inner3 ic inside] by (simp add: at3 clock3)
  show "let last = slab_collar_run ports init 3;
            low = slab_inner_low (snd last) (carry_out (ports 3) (rev (fst last)))
        in low ! (length low div 2) = digits ((step ^^ 3) src) ! (length (digits ((step ^^ 3) src)) div 2)"
    using center by (simp only: Let_def)
qed

ML \<open>
  val checked = @{thms slab_joint_four};
  val _ = if null (Thm_Deps.all_oracles checked) then () else error "Joint slab oracle";
  val _ = if Thm_Deps.has_skip_proof checked then error "Skipped joint slab proof" else ();
\<close>
end
