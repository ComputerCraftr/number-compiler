theory Reverse_Q19_UV_Admission
  imports Main
begin

datatype uv_scan = ScanStart | ScanOuter | ScanWord nat bool bool bool
  | ScanCenter | ScanAccept | ScanDead

fun uv_next :: "nat list \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> uv_scan \<Rightarrow> uv_scan" where
  "uv_next u v x ScanStart = (if x=19 then ScanOuter else ScanDead)"
| "uv_next u v x ScanOuter = (if x=17 then ScanWord 0 True True False else ScanDead)"
| "uv_next u v x (ScanWord i a b seen) =
    (if i=0 \<and> seen \<and> x=11 then ScanCenter else
       let p = (a \<and> u!i=x); q=(b \<and> v!i=x) in
         if \<not>(p \<or> q) then ScanDead else
         if i=33 then ScanWord 0 True True True else ScanWord (Suc i) p q seen)"
| "uv_next u v x ScanCenter = (if x=21 then ScanAccept else ScanDead)"
| "uv_next u v x ScanAccept = ScanDead"
| "uv_next u v x ScanDead = ScanDead"

definition complete_uv :: "nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> bool" where
  "complete_uv u v xs \<longleftrightarrow>
    (\<exists>ts. ts \<noteq> [] \<and> set ts \<subseteq> {u,v} \<and> xs=[19,17]@concat ts@[11])"

fun uv_invariant where
  "uv_invariant u v ScanStart xs = (xs=[])"
| "uv_invariant u v ScanOuter xs = (xs=[19])"
| "uv_invariant u v (ScanWord i a b seen) xs =
    (\<exists>ts w. set ts \<subseteq> {u,v} \<and> xs=[19,17]@concat ts@w \<and> (seen=(ts\<noteq>[]))
      \<and> length w=i \<and> i<34 \<and> (a \<longrightarrow> w=take i u) \<and> (b \<longrightarrow> w=take i v))"
| "uv_invariant u v ScanCenter xs = complete_uv u v xs"
| "uv_invariant u v ScanAccept xs = (\<exists>ys. xs=ys@[21] \<and> complete_uv u v ys)"
| "uv_invariant u v ScanDead xs = True"

lemma uv_wordI:
  assumes "set ts \<subseteq> {u,v}" "xs=[19,17]@concat ts@w"
    "seen=(ts\<noteq>[])" "length w=i" "i<34"
    "a \<longrightarrow> w=take i u" "b \<longrightarrow> w=take i v"
  shows "uv_invariant u v (ScanWord i a b seen) xs"
  using assms by (auto intro!: exI[of _ ts] exI[of _ w])

lemma uv_guard_step:
  assumes lengths: "length u=34" "length v=34"
      and prior: "uv_invariant u v state xs"
  shows "uv_invariant u v (uv_next u v x state) (xs@[x])"
proof (cases state)
  case ScanOuter
  with prior show ?thesis
    by (auto intro!: exI[of _ "[]"] simp: ScanOuter)
next
  case (ScanWord i a b seen)
  from prior obtain ts w where facts: "set ts \<subseteq> {u,v}" "xs=[19,17]@concat ts@w"
    "seen=(ts\<noteq>[])" "length w=i" "i<34" "a \<longrightarrow> w=take i u" "b \<longrightarrow> w=take i v"
    unfolding ScanWord by auto
  have advance_u: "a \<and> u!i=x \<Longrightarrow> w@[x]=take (Suc i) u"
    using lengths facts by (simp add: take_Suc_conv_app_nth)
  have advance_v: "b \<and> v!i=x \<Longrightarrow> w@[x]=take (Suc i) v"
    using lengths facts by (simp add: take_Suc_conv_app_nth)
  show ?thesis
  proof (cases "i=0 \<and> seen \<and> x=11")
    case True
    with facts show ?thesis unfolding ScanWord by (auto simp: complete_uv_def)
  next
    case no_center: False
    show ?thesis
    proof (cases "(a \<and> u!i=x) \<or> (b \<and> v!i=x)")
      case False
      with no_center show ?thesis by (auto simp: ScanWord Let_def)
    next
      case viable: True
      show ?thesis
      proof (cases "i=33")
        case True
        then have "Suc i=34" by simp
        with viable advance_u advance_v lengths have "w@[x] \<in> {u,v}" by auto
        then have valid: "set (ts@[w@[x]]) \<subseteq> {u,v}" using facts by auto
        have trans: "uv_next u v x state=ScanWord 0 True True True"
          unfolding ScanWord using no_center viable True by (auto simp: Let_def)
        show ?thesis unfolding trans
          by (rule uv_wordI[where ts="ts@[w@[x]]" and w="[]"]) (use facts valid in auto)
      next
        case False
        have trans: "uv_next u v x state=ScanWord (Suc i) (a \<and> u!i=x) (b \<and> v!i=x) seen"
          unfolding ScanWord using no_center viable False by (auto simp: Let_def)
        show ?thesis unfolding trans
          by (rule uv_wordI[where ts=ts and w="w@[x]"]) (use facts advance_u advance_v False in auto)
      qed
    qed
  qed
qed (use prior in \<open>auto split: if_splits\<close>)

theorem uv_guard_accepts_only_ordered_tiles:
  assumes "length u=34" "length v=34" "fold (uv_next u v) xs ScanStart=ScanAccept"
  shows "\<exists>ts. ts\<noteq>[] \<and> set ts \<subseteq> {u,v} \<and> xs=[19,17]@concat ts@[11,21]"
proof -
  have "uv_invariant u v (fold (uv_next u v) ys ScanStart) ys" for ys
    by (induction ys rule: rev_induct) (simp_all add: uv_guard_step[OF assms(1,2)])
  from this[of xs] assms(3) show ?thesis by (auto simp: complete_uv_def)
qed

ML \<open>
  val checked = @{thms uv_guard_accepts_only_ordered_tiles};
  val _ = if null (Thm_Deps.all_oracles checked) then () else error "UV source guard oracle";
  val _ = if Thm_Deps.has_skip_proof checked then error "UV source guard skipped proof" else ();
\<close>
end
