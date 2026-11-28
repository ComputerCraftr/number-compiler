theory Reverse_Q19_Birth_Ingress
  imports Reverse_Q19_Mixed_EQ_Phase
begin

text \<open>The first-birth border carries are kept as two ordered inlet
responses. An unresolved response is the identity carry, not a zero carry.
The recurrence below is finite and does not infer future width or a return.
The physical cell equation is separately source-bound; connecting an entire
source aperture to this folded port remains an additional obligation.\<close>

datatype q19_bi_reset = BI_Identity | BI_Zero | BI_One

fun q19_bi_apply :: "q19_bi_reset \<Rightarrow> bool \<Rightarrow> bool" where
  "q19_bi_apply BI_Identity b = b"
| "q19_bi_apply BI_Zero b = False"
| "q19_bi_apply BI_One b = True"

definition q19_bi_domain :: "nat \<Rightarrow> q19_bi_reset" where
  "q19_bi_domain s = (if s < 9 then BI_Zero else if s = 9 then BI_Identity else BI_One)"

lemma q19_bi_domain_exact:
  "q19_bi_apply (q19_bi_domain s) b = carry_apply (domain s) b"
  by (simp add: q19_bi_domain_def domain_def split: if_splits)

record q19_bi_state =
  bi_left :: bool
  bi_previous :: nat
  bi_zero :: q19_bi_reset
  bi_one :: q19_bi_reset

definition q19_bi_bit :: "bool \<Rightarrow> nat" where
  "q19_bi_bit b = (if b then 1 else 0)"

lemma q19_bi_source_carry_exact:
  assumes "s < 19"
  shows "q19_bi_bit (carry_apply (domain s) b) = (s + q19_bi_bit b) div 10"
proof -
  have cases: "s=0 \<or> s=1 \<or> s=2 \<or> s=3 \<or> s=4 \<or> s=5 \<or> s=6 \<or> s=7 \<or> s=8 \<or> s=9 \<or>
    s=10 \<or> s=11 \<or> s=12 \<or> s=13 \<or> s=14 \<or> s=15 \<or> s=16 \<or> s=17 \<or> s=18"
    using assms by arith
  show ?thesis using cases
    by (elim disjE; cases b; simp_all add: q19_bi_bit_def domain_def)
qed

definition q19_bi_response :: "q19_bi_state \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool" where
  "q19_bi_response st b d = q19_bi_apply (if b then bi_one st else bi_zero st) d"

definition q19_bi_step :: "q19_bi_state \<Rightarrow> nat \<Rightarrow> q19_bi_state" where
  "q19_bi_step st s = (let
     low = (s + q19_bi_bit (bi_left st)) mod 10;
     pick = (\<lambda>b. let j = carry_apply (domain s) b;
                       old = (if j then bi_one st else bi_zero st);
                       v = low + (bi_previous st + q19_bi_bit j) mod 10
                   in if old = BI_Identity then q19_bi_domain v else old)
   in \<lparr>bi_left = carry_apply (domain s) (bi_left st),
       bi_previous = s mod 10, bi_zero = pick False, bi_one = pick True\<rparr>)"

lemma q19_bi_step_response:
  "q19_bi_response (q19_bi_step st s) b d =
   q19_bi_response st (carry_apply (domain s) b)
     (carry_apply (domain ((s + q19_bi_bit (bi_left st)) mod 10 +
       (bi_previous st + q19_bi_bit (carry_apply (domain s) b)) mod 10)) d)"
  by (cases b; cases "bi_zero st"; cases "bi_one st";
      simp_all add: q19_bi_step_def q19_bi_response_def Let_def q19_bi_domain_exact
        split: if_splits)

fun q19_bi_reference :: "bool \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool \<times> bool" where
  "q19_bi_reference c p [] b d = (b,d)"
| "q19_bi_reference c p (s#ss) b d = (let
      (inside, prior) = q19_bi_reference (carry_apply (domain s) c) (s mod 10) ss b d;
      j = carry_apply (domain s) inside;
      v = (s + q19_bi_bit c) mod 10 + (p + q19_bi_bit j) mod 10
    in (j, carry_apply (domain v) prior))"

theorem q19_bi_ordered_fold:
  "q19_bi_response (foldl q19_bi_step st ss) b d =
   (case q19_bi_reference (bi_left st) (bi_previous st) ss b d of
      (inner, born) \<Rightarrow> q19_bi_response st inner born)"
proof (induction ss arbitrary: st b d)
  case Nil
  then show ?case by simp
next
  case (Cons s ss)
  have left: "bi_left (q19_bi_step st s) = carry_apply (domain s) (bi_left st)"
    by (simp add: q19_bi_step_def Let_def)
  have previous: "bi_previous (q19_bi_step st s) = s mod 10"
    by (simp add: q19_bi_step_def Let_def)
  obtain inner born where inside:
    "q19_bi_reference (carry_apply (domain s) (bi_left st)) (s mod 10) ss b d = (inner,born)"
    by (cases "q19_bi_reference (carry_apply (domain s) (bi_left st)) (s mod 10) ss b d") auto
  have IH: "q19_bi_response (foldl q19_bi_step (q19_bi_step st s) ss) b d =
      q19_bi_response (q19_bi_step st s) inner born"
    using Cons.IH[of "q19_bi_step st s" b d] inside
    by (simp only: left previous prod.case)
  show ?case using IH inside
    by (simp only: foldl_Cons q19_bi_reference.simps Let_def prod.case q19_bi_step_response)
qed

definition q19_bi_initial :: "nat \<Rightarrow> q19_bi_state" where
  "q19_bi_initial q = \<lparr>bi_left = carry_apply (domain q) True,
      bi_previous = q mod 10, bi_zero = BI_Identity, bi_one = BI_Identity\<rparr>"

lemma q19_bi_singleton_successor_closed:
  assumes "bi_zero st = r" "bi_one st = r" "r \<noteq> BI_Identity"
  shows "bi_zero (q19_bi_step st s) = r" "bi_one (q19_bi_step st s) = r"
proof -
  show "bi_zero (q19_bi_step st s) = r"
    using assms by (cases r; simp add: q19_bi_step_def Let_def)
  show "bi_one (q19_bi_step st s) = r"
    using assms by (cases r; simp add: q19_bi_step_def Let_def)
qed

theorem q19_bi_singleton_prefix_extension:
  assumes "bi_zero st = r" "bi_one st = r" "r \<noteq> BI_Identity"
  shows "bi_zero (foldl q19_bi_step st ss) = r"
    and "bi_one (foldl q19_bi_step st ss) = r"
proof -
  have both: "bi_zero (foldl q19_bi_step st ss) = r \<and>
      bi_one (foldl q19_bi_step st ss) = r"
    using assms
    by (induction ss arbitrary: st) (auto intro: q19_bi_singleton_successor_closed)
  show "bi_zero (foldl q19_bi_step st ss) = r" using both by simp
  show "bi_one (foldl q19_bi_step st ss) = r" using both by simp
qed

theorem q19_bi_singleton_all_inlets:
  assumes "bi_zero (foldl q19_bi_step (q19_bi_initial q) ss) = r"
      and "bi_one (foldl q19_bi_step (q19_bi_initial q) ss) = r"
      and "r = BI_Zero \<or> r = BI_One"
  shows "snd (q19_bi_reference (carry_apply (domain q) True) (q mod 10) ss b d) =
    (r = BI_One)"
proof -
  have fixed: "q19_bi_response (foldl q19_bi_step (q19_bi_initial q) ss) b d = (r = BI_One)"
    using assms by (cases r; cases b; simp add: q19_bi_response_def)
  obtain inner born where inside:
    "q19_bi_reference (carry_apply (domain q) True) (q mod 10) ss b d = (inner,born)"
    by (cases "q19_bi_reference (carry_apply (domain q) True) (q mod 10) ss b d") auto
  have left: "bi_left (q19_bi_initial q) = carry_apply (domain q) True"
    by (simp add: q19_bi_initial_def)
  have previous: "bi_previous (q19_bi_initial q) = q mod 10"
    by (simp add: q19_bi_initial_def)
  have order: "q19_bi_response (foldl q19_bi_step (q19_bi_initial q) ss) b d =
      q19_bi_response (q19_bi_initial q) inner born"
    using q19_bi_ordered_fold[of "q19_bi_initial q" ss b d]
    by (simp only: left previous inside prod.case)
  have initial: "q19_bi_response (q19_bi_initial q) inner born = born"
    by (cases inner; simp add: q19_bi_initial_def q19_bi_response_def)
  show ?thesis using fixed inside order initial by simp
qed

theorem q19_bi_physical_source_cell:
  assumes "valid_pair source" "0 < i" "i < length source" "carry_out False source"
  shows "step source ! i =
    (source ! i + q19_bi_bit (carry_out False (take i source))) mod 10 +
    (source ! (i - 1) + q19_bi_bit
      (carry_apply (domain (source ! i))
        (carry_out False (rev (drop (Suc i) source))))) mod 10"
  using q19_mixed_actual_source_cell[OF assms(1-3)] assms(4)
  by (simp add: q19_mixed_digit_def q19_mixed_bit_carry q19_bi_bit_def carry_bit_def)

ML \<open>
  val checked = @{thms q19_bi_domain_exact q19_bi_source_carry_exact q19_bi_step_response q19_bi_ordered_fold
    q19_bi_singleton_successor_closed q19_bi_singleton_prefix_extension
    q19_bi_singleton_all_inlets q19_bi_physical_source_cell};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Q19 birth ingress depends on an oracle";
  val _ = if Thm_Deps.has_skip_proof checked then
    error "Q19 birth ingress has skipped proofs" else ();
\<close>

end
