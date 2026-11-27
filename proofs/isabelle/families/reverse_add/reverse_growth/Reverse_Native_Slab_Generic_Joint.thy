theory Reverse_Native_Slab_Generic_Joint
  imports Reverse_Native_Slab_Two_Birth Reverse_Native_Slab_Collars Reverse_Native_Slab_Seam_Ports
begin

definition slab_two_birth_value :: "nat list \<Rightarrow> nat \<Rightarrow> nat" where
  "slab_two_birth_value xs i = 18 - 4 * (slab_core_bit (xs!(i-2) \<noteq> 18) +
    2 * slab_core_bit (xs!(i-1) \<noteq> 18) + slab_core_bit (xs!i \<noteq> 18))"

theorem slab_joint_four_two_birth:
  fixes src :: "nat list" and left right :: nat and core :: "nat list"
    and c k inner :: nat and ports :: "nat \<Rightarrow> bool"
    and init product :: "nat list \<times> nat list"
  assumes valid: "valid_pair src" and growth: "carry_out False src"
    and clock: "(\<not> carry_out False (step src) \<and> carry_out False (step (step src)) \<and> \<not> carry_out False (step (step (step src)))) \<or>
      (\<not> carry_out False (step src) \<and> \<not> carry_out False (step (step src)) \<and> carry_out False (step (step (step src)))) \<or>
      (carry_out False (step src) \<and> \<not> carry_out False (step (step src)) \<and> \<not> carry_out False (step (step (step src))))"
    and positive: "0 < left" and span: "left + 64 \<le> right"
    and half: "2*right \<le> Suc (length src)"
    and symbols: "\<And>i. left \<le> i \<Longrightarrow> i < right \<Longrightarrow> reverse_native_slab_source_symbol (src!i)"
  defines "c \<equiv> left+8" and "k \<equiv> right-12" and "inner \<equiv> k+4"
    and "ports \<equiv> \<lambda>t::nat. t \<noteq> 0 \<or> 9 < src!c"
    and "init \<equiv> (take c src, slab_center k src)"
    and "product \<equiv> slab_collar_run ports init 4"
    and "core \<equiv> map (slab_two_birth_value src) [c..<inner]"
  shows "(step ^^ 4) src = fst product @ core @ snd product @ rev core @ rev (fst product)"
    and "length ((step ^^ 4) src) = length src + 2"
    and "let last = slab_collar_run ports init 3;
             low = slab_inner_low (snd last) (carry_out (ports 3) (rev (fst last)))
        in low ! (length low div 2) = digits ((step ^^ 3) src) ! (length (digits ((step ^^ 3) src)) div 2)"
proof -
  let ?rows = "\<lambda>t. (step ^^ t) src"
  have small: "left+16 \<le> right" and upper: "right \<le> length src" using half span by arith+
  have seams: "\<forall>t<4. let row = ?rows t; fixed = c; middle = k+t in
      valid_pair row \<and> fixed < length row \<and> middle < length row \<and>
      (if t=0 then reverse_native_slab_source_symbol (row!fixed) else 9 < row!fixed) \<and>
      (if t=0 then reverse_native_slab_source_symbol (row!middle) else 9 < row!middle)"
    unfolding c_def k_def by (rule slab_first_birth_source_seam_ports[OF valid growth positive small upper symbols])
  have width: "length (step (step (step (step src)))) = length src + 2"
    using growth clock by (auto simp: length_digits_exact)
  show final: "length ((step ^^ 4) src) = length src+2"
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
    show "slab_two_birth_value src i = ?rows 4 ! i"
      using slab_core_physical_four_two_birth[OF valid lo hi cover growth clock]
      by (simp add: slab_two_birth_value_def eval_nat_numeral)
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

definition slab_source_clock :: "(nat \<Rightarrow> bool) \<Rightarrow> (nat list \<times> nat list) \<Rightarrow> nat \<Rightarrow> bool" where
  "slab_source_clock ports init t = carry_out (ports t) (rev (fst (slab_collar_run ports init t)))"

theorem slab_source_clock_matches_physical:
  fixes src :: "nat list" and left right c k :: nat and ports :: "nat \<Rightarrow> bool"
    and init :: "nat list \<times> nat list"
  assumes valid: "valid_pair src" and growth: "carry_out False src"
    and positive: "0 < left" and span: "left + 64 \<le> right"
    and half: "2*right \<le> Suc (length src)"
    and symbols: "\<And>i. left \<le> i \<Longrightarrow> i < right \<Longrightarrow> reverse_native_slab_source_symbol (src!i)"
  defines "c \<equiv> left+8" and "k \<equiv> right-12"
    and "ports \<equiv> \<lambda>t::nat. t \<noteq> 0 \<or> 9 < src!c"
    and "init \<equiv> (take c src, slab_center k src)"
  assumes t: "t < 4"
  shows "slab_source_clock ports init t = carry_out False ((step ^^ t) src)"
proof -
  let ?rows = "\<lambda>t. (step ^^ t) src"
  have small: "left+16 \<le> right" and upper: "right \<le> length src" using half span by arith+
  have seams: "\<forall>t<4. let row = ?rows t; fixed = c; middle = k+t in
      valid_pair row \<and> fixed < length row \<and> middle < length row \<and>
      (if t=0 then reverse_native_slab_source_symbol (row!fixed) else 9 < row!fixed) \<and>
      (if t=0 then reverse_native_slab_source_symbol (row!middle) else 9 < row!middle)"
    unfolding c_def k_def by (rule slab_first_birth_source_seam_ports[OF valid growth positive small upper symbols])
  have guards: "valid_pair (?rows u) \<and> 2*c < length (?rows u) \<and>
       2*(k+u) < length (?rows u) \<and> ?rows u ! c \<noteq> 9 \<and> ?rows u ! (k+u) \<noteq> 9 \<and>
       ports u = (9 < ?rows u ! c)" if u: "u < 4" for u
  proof -
    have limits: "2*c < length (?rows u)" "2*(k+u) < length (?rows u)"
      unfolding c_def k_def using slab_iter_len[of src u] half span u by arith+
    show ?thesis using spec[OF seams, of u] u limits
      by (cases "u=0") (auto simp: ports_def Let_def reverse_native_slab_source_symbol_def)
  qed
  have run: "slab_collar_run ports init t = (take c (?rows t), slab_center (k+t) (?rows t))"
    unfolding init_def by (rule slab_collar_run_exact) (use guards t in auto)
  have v: "valid_pair (?rows t)" and c: "2*c < length (?rows t)" and reset: "?rows t ! c \<noteq> 9"
    and port: "ports t = (9 < ?rows t ! c)" using guards[OF t] by blast+
  show ?thesis using slab_outer_collar_at(1)[OF v c reset] port
    by (simp add: slab_source_clock_def run)
qed

theorem slab_joint_four_two_birth_from_source_clock:
  fixes src :: "nat list" and left right :: nat and core :: "nat list"
    and c k inner :: nat and ports :: "nat \<Rightarrow> bool"
    and init product :: "nat list \<times> nat list"
  assumes valid: "valid_pair src"

    and positive: "0 < left" and span: "left + 64 \<le> right"
    and half: "2*right \<le> Suc (length src)"
    and symbols: "\<And>i. left \<le> i \<Longrightarrow> i < right \<Longrightarrow> reverse_native_slab_source_symbol (src!i)"
  defines "c \<equiv> left+8" and "k \<equiv> right-12" and "inner \<equiv> k+4"
    and "ports \<equiv> \<lambda>t::nat. t \<noteq> 0 \<or> 9 < src!c"
    and "init \<equiv> (take c src, slab_center k src)"
    and "product \<equiv> slab_collar_run ports init 4"
    and "core \<equiv> map (slab_two_birth_value src) [c..<inner]"
  assumes first: "slab_source_clock ports init 0"
    and clock: "(\<not> slab_source_clock ports init 1 \<and> slab_source_clock ports init 2 \<and> \<not> slab_source_clock ports init 3) \<or>
      (\<not> slab_source_clock ports init 1 \<and> \<not> slab_source_clock ports init 2 \<and> slab_source_clock ports init 3) \<or>
      (slab_source_clock ports init 1 \<and> \<not> slab_source_clock ports init 2 \<and> \<not> slab_source_clock ports init 3)"
  shows "(step ^^ 4) src = fst product @ core @ snd product @ rev core @ rev (fst product)"
    and "length ((step ^^ 4) src) = length src + 2"
    and "let last = slab_collar_run ports init 3;
             low = slab_inner_low (snd last) (carry_out (ports 3) (rev (fst last)))
        in low ! (length low div 2) = digits ((step ^^ 3) src) ! (length (digits ((step ^^ 3) src)) div 2)"
proof -
  have extent: "2*c < length src"
    using span half unfolding c_def by arith
  have reset: "src!c \<noteq> 9"
    using symbols[of c] span unfolding c_def reverse_native_slab_source_symbol_def by auto
  have first_matches: "slab_source_clock ports init 0 = carry_out False src"
    using slab_outer_collar_at(1)[OF valid extent reset]
    by (simp add: slab_source_clock_def init_def ports_def)
  have growth: "carry_out False src" using first first_matches by simp
  have match: "slab_source_clock ports init t = carry_out False ((step ^^ t) src)" if "t < 4" for t
    using slab_source_clock_matches_physical[OF valid growth positive span half symbols that]
    by (simp add: c_def k_def ports_def init_def)
  have physical: "(\<not> carry_out False (step src) \<and> carry_out False (step (step src)) \<and> \<not> carry_out False (step (step (step src)))) \<or>
      (\<not> carry_out False (step src) \<and> \<not> carry_out False (step (step src)) \<and> carry_out False (step (step (step src)))) \<or>
      (carry_out False (step src) \<and> \<not> carry_out False (step (step src)) \<and> \<not> carry_out False (step (step (step src))))"
    using clock match[of 1] match[of 2] match[of 3]
    by (simp add: eval_nat_numeral)
  note joint = slab_joint_four_two_birth[OF valid growth physical positive span half symbols]
  show "(step ^^ 4) src = fst product @ core @ snd product @ rev core @ rev (fst product)"
    using joint(1) by (simp add: c_def k_def inner_def ports_def init_def product_def core_def)
  show "length ((step ^^ 4) src) = length src + 2"
    using joint(2) by simp
  show "let last = slab_collar_run ports init 3;
             low = slab_inner_low (snd last) (carry_out (ports 3) (rev (fst last)))
        in low ! (length low div 2) = digits ((step ^^ 3) src) ! (length (digits ((step ^^ 3) src)) div 2)"
    using joint(3) by (simp add: c_def k_def ports_def init_def)
qed

ML \<open>
  val checked = @{thms slab_source_clock_matches_physical slab_joint_four_two_birth slab_joint_four_two_birth_from_source_clock};
  val _ = if null (Thm_Deps.all_oracles checked) then () else error "Joint slab oracle";
  val _ = if Thm_Deps.has_skip_proof checked then error "Skipped joint slab proof" else ();
\<close>
end
