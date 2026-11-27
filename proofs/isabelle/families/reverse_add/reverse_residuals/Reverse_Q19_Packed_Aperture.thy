theory Reverse_Q19_Packed_Aperture
  imports Reverse_Native_Hinge_Successor Reverse_Q19_Bitplane_Arithmetic
begin

text \<open>A non-EQ pair fixes the returning carry for its outer prefix. A width birth inserts the high digit one before the reversed emissions.\<close>

lemma reverse_native_outer_reset_step:
  fixes outer inner center :: "nat list"
  assumes reset: "r \<noteq> 9"
  defines "b \<equiv> carry_out (9 < r) (rev outer)"
    and "src \<equiv> (outer @ r # inner) @ center @ rev (outer @ r # inner)"
  shows "carry_out False src = b"
    and "take (length outer + (if b then 1 else 0)) (step src) =
        map (\<lambda>(x,y). x+y) (zip (emit False (outer @ [r]))
          ((if b then [1] else []) @ rev (emit (9 < r) (rev outer))))"
proof -
  let ?half = "outer @ r # inner"
  let ?n = "length outer + (if b then 1 else 0)"
  let ?h = "(if b then [1] else []) @ rev (emit (9 < r) (rev outer))"
  have d: "\<And>c. carry_apply (domain r) c = (9 < r)"
    using reset by (auto simp: domain_def)
  have k: "\<And>c. carry_out c (rev ?half) = b"
    by (simp add: b_def carry_out_append reverse_native_carry_out_cons d)
  show birth: "carry_out False src = b" by (simp only: src_def carry_out_append k)
  have low: "take ?n (digits src) = take ?n (emit False (outer @ [r]))"
    by (cases b; simp add: src_def digits_def emit_append take_append)
  have high: "take ?n (rev (digits src)) = ?h"
    using birth by (cases b; simp add: src_def digits_def emit_append d rev_append
        take_append carry_out_append k)
  have trim: "zip (take (length ys) xs) ys = zip xs ys" for xs ys :: "nat list"
    by (induction ys arbitrary: xs; case_tac xs; simp)
  have len: "length ?h = ?n" by (cases b; simp)
  have z: "zip (take ?n (emit False (outer @ [r]))) ?h = zip (emit False (outer @ [r])) ?h"
    by (rule trim[of "?h", unfolded len])
  show "take ?n (step src) = map (\<lambda>(x,y). x+y) (zip (emit False (outer @ [r])) ?h)"
    by (simp only: step_def take_map take_zip low high z)
qed

lemma packed_reset_independent:
  assumes "\<exists>x\<in>set xs. x \<noteq> 9"
  shows "carry_out a xs = carry_out b xs"
proof -
  have "first_reset (rev xs) \<noteq> None"
    using assms by (auto simp: first_reset_none_iff)
  then show ?thesis using carry_out_reverse_first_reset[of a "rev xs"]
    carry_out_reverse_first_reset[of b "rev xs"] by (cases "first_reset (rev xs)") auto
qed

lemma packed_tile_low_digit:
  assumes idx: "j < length xs"
      and guard: "a = [] \<and> u = [] \<or> (\<exists>x\<in>set (take j xs). x \<noteq> 9)"
  shows "emit False (a @ xs @ b) ! (length a + j) =
         emit False (u @ xs @ v) ! (length u + j)"
proof -
  have port: "carry_out (carry_out False a) (take j xs) =
              carry_out (carry_out False u) (take j xs)"
    using guard packed_reset_independent by blast
  show ?thesis using idx port
    by (simp add: emit_append nth_append emit_nth_carry_prefix)
qed

definition packed_tile_output :: "bool \<Rightarrow> bool \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat" where
  "packed_tile_output born outer tile i = emit False tile ! i +
    (if born \<and> i = 0 then (if outer then 1 else 0)
     else emit False (rev tile) ! (length tile - Suc (i - (if born then 1 else 0))))"

theorem packed_tile_physical_column:
  fixes a xs b u v :: "nat list"
  defines "src \<equiv> a @ xs @ b" and "tile \<equiv> u @ xs @ v"
  assumes sym: "rev src = src"
      and pos: "j < length xs"
      and birth: "born = carry_out False src"
      and left: "a=[] \<and> u=[] \<or> (\<exists>x\<in>set (take j xs). x\<noteq>9)"
      and seam: "born \<and> j=0 \<longrightarrow> a=[] \<and> u=[]"
      and right: "\<not> (born \<and> j=0) \<longrightarrow>
        (\<exists>x\<in>set (take (length xs - Suc (j - (if born then 1 else 0))) (rev xs)). x\<noteq>9)"
  shows "step src ! (length a + j) =
         packed_tile_output born (a=[]) tile (length u + j)"
proof -
  let ?i = "length a + j"
  let ?d = "if born then 1::nat else 0"
  have lb: "?i < length src" using pos by (simp add: src_def)
  have dl: "length (digits src) = length src + ?d" by (simp add: digits_def birth)
  have revsrc: "src = rev b @ rev xs @ rev a"
    using sym by (simp add: src_def)
  have low: "digits src ! ?i = emit False tile ! (length u + j)"
    using packed_tile_low_digit[OF pos left, of b v] lb by (simp add: src_def tile_def digits_def nth_append)
  have base: "step src ! ?i = digits src ! ?i + digits src ! (length (digits src) - Suc ?i)"
    using lb dl by (simp add: step_def rev_nth)
  show ?thesis
  proof (cases "born \<and> j=0")
    case True
    then have origin: "a=[]" "u=[]" using seam by auto
    have h: "digits src ! (length (digits src) - Suc ?i) = 1"
      using True dl origin birth by (simp add: digits_def nth_append)
    show ?thesis unfolding base low h using True origin by (simp add: packed_tile_output_def)
  next
    case False
    let ?n = "length xs - Suc (j - ?d)"
    have n: "?n < length (rev xs)" using pos False by (cases born; simp; arith)
    have revguard: "rev b=[] \<and> rev v=[] \<or> (\<exists>x\<in>set (take ?n (rev xs)). x\<noteq>9)"
      using right False by simp
    have eq: "emit False src ! (length b + ?n) =
              emit False (rev tile) ! (length v + ?n)"
      using packed_tile_low_digit[OF n revguard, of "rev a" "rev u"] by (simp only: revsrc tile_def rev_append length_rev append_assoc)
    have sizes: "length src = length a + length xs + length b"
      "length tile = length u + length xs + length v" by (simp_all add: src_def tile_def)
    have inds1: "length (digits src) - Suc ?i = length b + ?n"
      using sizes(1) pos False dl by (cases born; simp_all; presburger)
    have inds2: "length tile - Suc (length u + j - ?d) = length v + ?n"
      using sizes(2) pos False by (cases born; simp_all; presburger)
    have inds3: "length b + ?n < length src" using sizes(1) n by simp
    note inds = inds1 inds2 inds3
    have high: "digits src ! (length (digits src) - Suc ?i) = emit False (rev tile) ! (length v + ?n)"
      using inds eq by (simp add: digits_def nth_append)
    have edge: "\<not> (born \<and> length u+j=0)" using False by auto
    show ?thesis by (simp only: base low high packed_tile_output_def edge if_False inds2)
  qed
qed
definition q19_slice where
  "q19_slice k n xs = take n (drop k xs)"

definition q19_lane_agrees where
  "q19_lane_agrees off lo hi tile src \<longleftrightarrow> lo \<le> hi \<and> hi \<le> length tile \<and>
    off + hi \<le> length src \<and> q19_slice lo (hi-lo) tile = q19_slice (off+lo) (hi-lo) src"

lemma q19_slice_split:
  assumes "i \<le> j"
  shows "take i xs @ q19_slice i (j-i) xs @ drop j xs = xs"
  using append_take_drop_id[of "j-i" "drop i xs"] assms by (simp add: q19_slice_def)

definition packed_tile_guard where
  "packed_tile_guard off lo hi xs born start finish \<longleftrightarrow>
     lo \<le> start \<and> start \<le> finish \<and> finish \<le> hi \<and>
     (\<forall>i\<in>{start..<finish}. let j = i-lo in
       ((off=0 \<and> lo=0) \<or> (\<exists>x\<in>set (take j xs). x\<noteq>9)) \<and>
       ((born \<and> j=0) \<longrightarrow> off=0 \<and> lo=0) \<and>
       (\<not> (born \<and> j=0) \<longrightarrow>
         (\<exists>x\<in>set (take (length xs-Suc (j-(if born then 1 else 0))) (rev xs)). x\<noteq>9)))"

definition packed_tile_step where
  "packed_tile_step born outer tile =
    map (packed_tile_output born outer tile) [0..<length tile]"

lemma packed_tile_step_agrees:
  assumes same: "q19_lane_agrees off lo hi tile src" and sym: "rev src=src"
    and clock: "born=carry_out False src"
    and g: "packed_tile_guard off lo hi (q19_slice lo (hi-lo) tile) born start finish"
  shows "q19_lane_agrees off start finish (packed_tile_step born (off=0) tile) (step src)"
proof -
  let ?xs = "q19_slice lo (hi-lo) tile"
  let ?a = "take (off+lo) src" and ?u = "take lo tile"
  let ?b = "drop (off+hi) src" and ?v = "drop hi tile"
  have lim: "lo\<le>hi" "hi\<le>length tile" "off+hi\<le>length src"
    "q19_slice (off+lo) (hi-lo) src=?xs" using same by (simp_all add: q19_lane_agrees_def)
  have s: "?a @ ?xs @ ?b=src" using q19_slice_split[of "off+lo" "off+hi" src] lim by simp
  have t: "?u @ ?xs @ ?v=tile" using q19_slice_split[OF lim(1), of tile] .
  have lens: "length ?a=off+lo" "length ?u=lo" "length ?xs=hi-lo"
    using lim by (simp_all add: q19_slice_def)
  have bound: "lo\<le>start" "start\<le>finish" "finish\<le>hi" using g by (auto simp: packed_tile_guard_def)
  have at: "step src ! (off+i) = packed_tile_output born (off=0) tile i"
    if i: "start\<le>i" "i<finish" for i
  proof -
    let ?j = "i-lo"
    have ge: "lo\<le>i" "i<hi" using i bound by arith+
    have j: "?j<length ?xs" using lens ge by simp
    have eq: "length ?a + ?j=off+i" "length ?u + ?j=i" using ge by (simp only: lens; arith)+
    have ii: "i \<in> {start..<finish}" using i by simp
    note guards = g[unfolded packed_tile_guard_def, THEN conjunct2, THEN conjunct2,
      THEN conjunct2, THEN bspec, OF ii, simplified Let_def]
    have empty: "off=0 \<and> lo=0 \<Longrightarrow> ?a=[] \<and> ?u=[]" by simp
    have left: "(?a=[] \<and> ?u=[]) \<or> (\<exists>x\<in>set (take ?j ?xs). x\<noteq>9)"
      and seam: "born \<and> ?j=0 \<longrightarrow> ?a=[] \<and> ?u=[]"
      and right: "\<not> (born \<and> ?j=0) \<longrightarrow> (\<exists>x\<in>set
        (take (length ?xs-Suc (?j-(if born then 1 else 0))) (rev ?xs)). x\<noteq>9)"
      using guards empty by blast+
    have h: "step src ! (off+i)=packed_tile_output born (?a=[]) tile i"
      using packed_tile_physical_column[where a="?a" and xs="?xs" and b="?b" and u="?u" and v="?v"
        and born=born and j="?j", unfolded s t, OF sym j clock left seam right] by (simp only: eq)
    show ?thesis using h ge lens(1) by (cases "i=0"; auto simp: packed_tile_output_def)
  qed
  let ?next = "packed_tile_step born (off=0) tile"
  have l: "length ?next=length tile" "length src\<le>length (step src)"
    by (simp_all add: packed_tile_step_def step_def digits_def)
  have project: "packed_tile_output born (off=0) tile (start+i)=step src!(off+start+i)"
    if "i<finish-start" for i
    using at[of "start+i"] that by (simp add: add.assoc)
  have equal: "q19_slice start (finish-start) ?next =
      q19_slice (off+start) (finish-start) (step src)"
    using bound lim l project
    by (intro nth_equalityI; simp add: q19_slice_def packed_tile_step_def)
  show ?thesis using bound lim l equal by (auto simp: q19_lane_agrees_def)
qed
fun packed_widths :: "nat list \<Rightarrow> nat \<Rightarrow> bool list" where
  "packed_widths src 0=[]"
| "packed_widths src (Suc n)=carry_out False src # packed_widths (step src) n"

fun packed_tile_run where
  "packed_tile_run off lo hi tile [] = Some (lo,hi,tile)"
| "packed_tile_run off lo hi tile ((born,start,finish)#actions) =
     (if packed_tile_guard off lo hi (q19_slice lo (hi-lo) tile) born start finish
      then packed_tile_run off start finish (packed_tile_step born (off=0) tile) actions
      else None)"

theorem packed_tile_run_physical:
  assumes initial: "q19_lane_agrees off lo hi tile src" "rev src=src"
    and clocks: "map fst actions=packed_widths src (length actions)"
    and issued: "packed_tile_run off lo hi tile actions=Some (l,h,out)"
  shows "q19_lane_agrees off l h out (run step (length actions) src)"
  using assms
proof (induction actions arbitrary: lo hi tile src)
  case Nil then show ?case by simp
next
  case (Cons action tail)
  obtain born start finish where a: "action=(born,start,finish)" by (cases action) auto
  have g: "packed_tile_guard off lo hi (q19_slice lo (hi-lo) tile) born start finish"
    and rest: "packed_tile_run off start finish (packed_tile_step born (off=0) tile) tail=Some (l,h,out)"
    using Cons.prems(4) by (auto simp: a split: if_splits)
  have b: "born=carry_out False src" and clocks: "map fst tail=packed_widths (step src) (length tail)"
    using Cons.prems(3) by (simp_all add: a)
  have advance: "q19_lane_agrees off start finish (packed_tile_step born (off=0) tile) (step src)"
    by (rule packed_tile_step_agrees[OF Cons.prems(1,2) b g])
  show ?case using Cons.IH[OF advance step_symmetric clocks rest] by simp
qed
inductive q19_outer_clock :: "nat list \<Rightarrow> bool list \<Rightarrow> bool" where
  empty_clock: "q19_outer_clock prefix []"
| append_clock: "r\<noteq>9 \<Longrightarrow> born=carry_out (9<r) (rev front) \<Longrightarrow>
    q19_outer_clock (map (\<lambda>(x,y). x+y) (zip (emit False (front@[r]))
       ((if born then [1] else []) @ rev (emit (9<r) (rev front))))) bs \<Longrightarrow>
    q19_outer_clock (front @ r # rest) (born#bs)"

theorem q19_outer_clock_physical:
  assumes issue: "q19_outer_clock prefix bs" and sym: "rev src=src"
      and size: "2*length prefix\<le>length src" and exact: "take (length prefix) src=prefix"
  shows "bs=packed_widths src (length bs)"
  using issue sym size exact
proof (induction arbitrary: src rule: q19_outer_clock.induct)
  case empty_clock then show ?case by simp
next
  case (append_clock r born front bs rest)
  let ?w = "front@[r]"
  let ?k = "length ?w"
  let ?middle = "take (length src-2*?k) (drop ?k src)"
  have bound: "2*?k\<le>length src" using append_clock.prems(2) by simp
  have pre: "take ?k src=?w"
    using arg_cong[OF append_clock.prems(3), of "take ?k"] by simp
  have back_end: "drop (length src-?k) src=rev ?w"
    using rev_take[of ?k src] append_clock.prems(1) pre by simp
  have mid: "?middle @ drop (length src-?k) src = drop ?k src"
  proof -
    have ix: "?k + (length src-2*?k) = length src-?k" using bound by arith
    show ?thesis using append_take_drop_id[of "length src-2*?k" "drop ?k src"]
      by (simp only: drop_drop add.commute[of "length src-2*?k" ?k] ix)
  qed
  have src: "src=(front@r#[]) @ ?middle @ rev (front@r#[])"
    using mid pre back_end append_take_drop_id[of ?k src] by simp
  let ?n = "length front+(if born then 1 else 0)"
  let ?new = "map (\<lambda>(x,y). x+y) (zip (emit False ?w)
       ((if born then [1] else []) @ rev (emit (9<r) (rev front))))"
  have b: "carry_out False src=born" and w: "take ?n (step src)=?new"
    using reverse_native_outer_reset_step[where outer=front and inner="[]" and center="?middle" and r=r, OF append_clock.hyps(1)] append_clock.hyps(2)
    by (simp_all only: src[symmetric] append_Nil)
  have len: "length ?new=?n" by (cases born; simp)
  have sz: "2*length ?new\<le>length (step src)" using bound
    by (cases born; simp add: len step_def digits_def; arith)
  have tail: "bs=packed_widths (step src) (length bs)"
    by (rule append_clock.IH[OF step_symmetric sz]; simp only: len w)
  have cons: "born # bs = carry_out False src # packed_widths (step src) (length bs)"
    unfolding b by (rule arg_cong[OF tail])
  show ?case using cons by simp
qed
text \<open>Two reset witnesses cover a contiguous word. Their arithmetic
bounds are the ones used by the bitplane aperture, including the inward
shift of the reflected digit when the physical width grows.\<close>

lemma packed_reset_aperture:
  fixes xs :: "nat list"
  assumes n: "hi=lo+length xs"
      and resets: "f<length xs" "r<length xs" "xs!f\<noteq>9" "xs!r\<noteq>9"
      and ends: "lo\<le>start" "start\<le>finish" "finish\<le>hi"
        "off=0 \<and> lo=0 \<or> lo+f<start"
        "finish\<le>lo+r+(if born then 1 else 0)"
  shows "packed_tile_guard off lo hi xs born start finish"
proof -
  have guard: "((off=0 \<and> lo=0) \<or> (\<exists>x\<in>set (take (i-lo) xs). x\<noteq>9)) \<and>
      ((born \<and> i-lo=0) \<longrightarrow> off=0 \<and> lo=0) \<and>
      (\<not> (born \<and> i-lo=0) \<longrightarrow>
       (\<exists>x\<in>set (take (length xs-Suc ((i-lo)-(if born then 1 else 0))) (rev xs)). x\<noteq>9))"
      if i: "start\<le>i" "i<finish" for i
  proof -
    have first: "xs!f \<in> set (take (i-lo) xs)" if "lo+f < start"
      using nth_mem[of f "take (i-lo) xs"] resets that i by simp
    have last: "xs!r \<in> set (take (length xs-Suc ((i-lo)-(if born then 1 else 0))) (rev xs))"
      if pos: "\<not> (born \<and> i-lo=0)"
    proof -
      let ?last = "length xs - Suc r"
      let ?count = "length xs - Suc ((i-lo)-(if born then 1 else 0))"
      have less: "?last < ?count" using ends i pos resets by (cases born; simp_all; arith)
      have posr: "?last<length xs" using resets by arith
      have rev: "rev xs ! ?last=xs!r" using posr resets by (simp add: rev_nth)
      show ?thesis using nth_mem[of ?last "take ?count (rev xs)"] less posr rev by simp
    qed
    show ?thesis using ends(4) i resets(3,4) first last by auto
  qed
  show ?thesis unfolding packed_tile_guard_def Let_def
    apply (intro conjI ends ballI)
    using guard by (metis atLeastLessThan_iff)+
qed
theorem reverse_native_packed_four_physical:
  assumes "rev src=src" "2*length front\<le>length src" "take (length front) src=front"
    and clock: "q19_outer_clock front (map fst actions)"
    and tile: "q19_lane_agrees off lo hi inlet src"
    and four: "length actions=4"
    and issued: "packed_tile_run off lo hi inlet actions=Some (l,h,out)"
  shows "q19_slice l (h-l) out = q19_slice (off+l) (h-l) (run step 4 src)"
proof -
  have c: "map fst actions=packed_widths src (length actions)"
    using q19_outer_clock_physical[OF clock assms(1-3)] by simp
  show ?thesis using packed_tile_run_physical[OF tile assms(1) c issued]
    by (simp add: q19_lane_agrees_def four)
qed

lemma packed_physical_width_sum:
  "length (run step n src) = length src + length (filter id (packed_widths src n))"
proof (induction n arbitrary: src)
  case 0 then show ?case by simp
next
  case (Suc n)
  then show ?case using Suc.IH[of "step src"]
    by (cases "carry_out False src"; simp add: length_digits_exact)
qed

corollary reverse_native_four_width_readout:
  assumes src: "valid_pair src" and size: "2*length front\<le>length src"
    and initial: "take (length front) src=front" and clock: "q19_outer_clock front clocks"
    and four: "length clocks=4"
  defines "out \<equiv> run step 4 src"
  shows "length out=length src+length (filter id clocks)"
    and "punctured_q19_decode_half (reverse_laurent_source_half out)
          (reverse_laurent_source_odd out)=out"
    and "reverse_laurent_source_odd out \<Longrightarrow> even (out!(length out div 2))"
proof -
  have sym: "rev src=src" using src by (simp add: valid_pair_def)
  have c: "clocks=packed_widths src 4"
    using q19_outer_clock_physical[OF clock sym size initial] four by simp
  show "length out=length src+length (filter id clocks)"
    by (simp only: out_def c packed_physical_width_sum)
  have pos: "0 < (4::nat)" by simp
  note endpoint = reverse_native_folded_endpoint_clock[OF src pos]
  show "punctured_q19_decode_half (reverse_laurent_source_half out)
      (reverse_laurent_source_odd out)=out" and
    "reverse_laurent_source_odd out \<Longrightarrow> even (out!(length out div 2))"
    unfolding out_def using endpoint by blast+
qed

ML \<open>
  val thms = @{thms q19_plane_machine_source_carry q19_plane_machine_reverse_word
    q19_plane_two_physical_digits reverse_native_outer_reset_step packed_reset_aperture
    packed_tile_physical_column q19_outer_clock_physical reverse_native_packed_four_physical reverse_native_four_width_readout};
  val _ = if null (Thm_Deps.all_oracles thms) andalso not (Thm_Deps.has_skip_proof thms)
    then () else error "Untrusted packed reverse/add action";
\<close>

end
