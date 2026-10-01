theory Reverse_196_Two_Port_Refinement
  imports Mirror_Pair_Step
begin

text \<open>This is the semantic form of production BaseBlockEffect(10).
The left port retains incoming carry, the previous pair coefficient and the
blank/sink flags.  The right port retains the forward and reflected carry
functions.  Output is published only after both scans have reached the cell.\<close>

record reverse_left_port =
  rp_carry :: bool
  rp_previous :: "nat option"
  rp_blank_seen :: bool
  rp_sink :: bool

record reverse_right_port =
  rp_forward :: carry_domain
  rp_backward :: carry_domain

definition reverse_left_initial :: reverse_left_port where
  "reverse_left_initial = \<lparr>rp_carry=False, rp_previous=None,
    rp_blank_seen=False, rp_sink=False\<rparr>"

definition reverse_right_initial :: reverse_right_port where
  "reverse_right_initial =
    \<lparr>rp_forward=Equal, rp_backward=Equal\<rparr>"

definition reverse_left_advance ::
    "reverse_left_port \<Rightarrow> nat \<Rightarrow> reverse_left_port" where
  "reverse_left_advance l s =
    (if rp_sink l then l
     else if s = 19 then l\<lparr>rp_blank_seen := True\<rparr>
     else if rp_blank_seen l then
       \<lparr>rp_carry=False, rp_previous=None,
         rp_blank_seen=True, rp_sink=True\<rparr>
     else \<lparr>rp_carry=carry_apply (domain s) (rp_carry l),
       rp_previous=Some s, rp_blank_seen=False, rp_sink=False\<rparr>)"

definition reverse_right_advance ::
    "reverse_right_port \<Rightarrow> nat \<Rightarrow> reverse_right_port" where
  "reverse_right_advance r s =
    (if s = 19 then r else
      \<lparr>rp_forward=carry_then (rp_forward r) (domain s),
       rp_backward=carry_then (domain s) (rp_backward r)\<rparr>)"

fun reverse_right_fold :: "nat list \<Rightarrow> reverse_right_port" where
  "reverse_right_fold [] = reverse_right_initial"
| "reverse_right_fold (s#ss) =
    reverse_right_advance (reverse_right_fold ss) s"

fun reverse_left_fold_from ::
    "reverse_left_port \<Rightarrow> nat list \<Rightarrow> reverse_left_port" where
  "reverse_left_fold_from l [] = l"
| "reverse_left_fold_from l (s#ss) =
    reverse_left_fold_from (reverse_left_advance l s) ss"

definition reverse_left_fold :: "nat list \<Rightarrow> reverse_left_port" where
  "reverse_left_fold ss = reverse_left_fold_from reverse_left_initial ss"

lemma carry_out_append_one:
  "carry_out c (xs@[s]) = carry_apply (domain s) (carry_out c xs)"
  by (simp add: carry_out_def fold_append)

theorem reverse_right_fold_forward:
  "carry_apply (rp_forward (reverse_right_fold ss)) c =
    carry_out c (filter (\<lambda>s. s \<noteq> 19) ss)"
proof (induct ss arbitrary: c)
  case Nil
  then show ?case by (cases c; simp_all add: reverse_right_initial_def carry_out_def)
next
  case (Cons s ss)
  show ?case
  proof (cases "s=19")
    case True
    then show ?thesis using Cons.hyps[of c]
      by (simp add: reverse_right_advance_def)
  next
    case False
    then show ?thesis
      using Cons.hyps[of "carry_apply (domain s) c"]
      by (simp add: reverse_right_advance_def carry_then_apply carry_out_def)
  qed
qed

theorem reverse_right_fold_backward:
  "carry_apply (rp_backward (reverse_right_fold ss)) c =
    carry_out c (rev (filter (\<lambda>s. s \<noteq> 19) ss))"
proof (induct ss arbitrary: c)
  case Nil
  then show ?case by (cases c; simp_all add: reverse_right_initial_def carry_out_def)
next
  case (Cons s ss)
  show ?case
  proof (cases "s=19")
    case True
    then show ?thesis using Cons.hyps[of c]
      by (simp add: reverse_right_advance_def)
  next
    case False
    then show ?thesis using Cons.hyps[of c]
      by (simp add: reverse_right_advance_def carry_then_apply
          carry_out_append_one)
  qed
qed

corollary reverse_right_fold_valid_carries:
  assumes "\<forall>s\<in>set ss. s<19"
  shows "carry_apply (rp_forward (reverse_right_fold ss)) c = carry_out c ss"
    "carry_apply (rp_backward (reverse_right_fold ss)) c = carry_out c (rev ss)"
proof -
  have filtered: "filter (\<lambda>s. s \<noteq> 19) ss = ss"
    using assms by (induct ss) auto
  show "carry_apply (rp_forward (reverse_right_fold ss)) c = carry_out c ss"
    using reverse_right_fold_forward[of ss c] filtered by simp
  show "carry_apply (rp_backward (reverse_right_fold ss)) c = carry_out c (rev ss)"
    using reverse_right_fold_backward[of ss c] filtered by simp
qed

lemma reverse_left_fold_from_append:
  "reverse_left_fold_from l (xs@[s]) =
    reverse_left_advance (reverse_left_fold_from l xs) s"
  by (induct xs arbitrary: l) simp_all

theorem reverse_left_fold_valid_prefix:
  assumes valid: "\<forall>s\<in>set ss. s < 19"
  shows "rp_carry (reverse_left_fold ss) = carry_out False ss"
    "rp_previous (reverse_left_fold ss) =
      (if ss=[] then None else Some (last ss))"
    "\<not> rp_blank_seen (reverse_left_fold ss)"
    "\<not> rp_sink (reverse_left_fold ss)"
proof -
  have combined:
    "(\<forall>s\<in>set ss. s<19) \<longrightarrow>
      rp_carry (reverse_left_fold ss) = carry_out False ss \<and>
      rp_previous (reverse_left_fold ss) =
        (if ss=[] then None else Some (last ss)) \<and>
      \<not> rp_blank_seen (reverse_left_fold ss) \<and>
      \<not> rp_sink (reverse_left_fold ss)"
  proof (induct ss rule: rev_induct)
    case Nil
    then show ?case
      by (simp add: reverse_left_fold_def reverse_left_initial_def carry_out_def)
  next
    case (snoc s ss)
    show ?case
    proof
      assume admitted: "\<forall>x\<in>set (ss@[s]). x<19"
      have slt: "s<19" and prefix: "\<forall>x\<in>set ss. x<19"
        using admitted by auto
      have IH: "rp_carry (reverse_left_fold ss) = carry_out False ss"
        "rp_previous (reverse_left_fold ss) =
          (if ss=[] then None else Some (last ss))"
        "\<not> rp_blank_seen (reverse_left_fold ss)"
        "\<not> rp_sink (reverse_left_fold ss)"
        using snoc.hyps prefix by blast+
      have fold_snoc: "reverse_left_fold (ss@[s]) =
          reverse_left_advance (reverse_left_fold ss) s"
        by (simp add: reverse_left_fold_def reverse_left_fold_from_append)
      show "rp_carry (reverse_left_fold (ss@[s])) = carry_out False (ss@[s]) \<and>
        rp_previous (reverse_left_fold (ss@[s])) =
          (if ss@[s]=[] then None else Some (last (ss@[s]))) \<and>
        \<not> rp_blank_seen (reverse_left_fold (ss@[s])) \<and>
        \<not> rp_sink (reverse_left_fold (ss@[s]))"
        using IH slt
        by (simp add: fold_snoc reverse_left_advance_def carry_out_append_one)
    qed
  qed
  from combined valid show
    "rp_carry (reverse_left_fold ss) = carry_out False ss"
    "rp_previous (reverse_left_fold ss) =
      (if ss=[] then None else Some (last ss))"
    "\<not> rp_blank_seen (reverse_left_fold ss)"
    "\<not> rp_sink (reverse_left_fold ss)"
    by blast+
qed

definition reverse_operands ::
    "reverse_left_port \<Rightarrow> nat \<Rightarrow> reverse_right_port
      \<Rightarrow> (nat \<times> bool \<times> nat \<times> bool) option" where
  "reverse_operands l s r =
    (if rp_sink l then None
     else if s = 19 then
       (if \<not> rp_blank_seen l \<and> rp_previous l \<noteq> None \<and> rp_carry l
        then Some (the (rp_previous l),False,1,False) else None)
     else let action = domain s;
              carry_after = carry_apply action (rp_carry l)
       in if \<not> carry_apply (rp_forward r) carry_after
          then Some (s,rp_carry l,s,carry_apply (rp_backward r) False)
          else case rp_previous l of
            None \<Rightarrow> Some (s,False,1,False)
          | Some previous \<Rightarrow>
              Some (s,rp_carry l,previous,
                carry_apply (carry_then action (rp_backward r)) False))"

definition reverse_emit ::
    "reverse_left_port \<Rightarrow> nat \<Rightarrow> reverse_right_port \<Rightarrow> nat"
where
  "reverse_emit l s r =
    (case reverse_operands l s r of None \<Rightarrow> 19
     | Some (a,c,b,d) \<Rightarrow>
       ((a + (if c then 1 else 0)) mod 10) +
       ((b + (if d then 1 else 0)) mod 10))"

fun reverse_two_port_scan_from ::
    "reverse_left_port \<Rightarrow> nat list \<Rightarrow> nat list" where
  "reverse_two_port_scan_from l [] = []"
| "reverse_two_port_scan_from l (s#ss) =
    reverse_emit l s (reverse_right_fold ss) #
      reverse_two_port_scan_from (reverse_left_advance l s) ss"

definition reverse_two_port_scan :: "nat list \<Rightarrow> nat list" where
  "reverse_two_port_scan ss =
    reverse_two_port_scan_from reverse_left_initial ss"

fun strip_blank_tail :: "nat list \<Rightarrow> nat list" where
  "strip_blank_tail [] = []"
| "strip_blank_tail (s#ss) =
    (case strip_blank_tail ss of [] \<Rightarrow> (if s=19 then [] else [s])
     | x#xs \<Rightarrow> s#x#xs)"

definition reverse_two_port_publisher :: "nat list \<Rightarrow> nat list" where
  "reverse_two_port_publisher ss =
    strip_blank_tail (reverse_two_port_scan (ss@[19]))"

lemma reverse_two_port_scan_from_length:
  "length (reverse_two_port_scan_from l ss) = length ss"
  by (induct ss arbitrary: l) simp_all

lemma reverse_two_port_scan_length:
  "length (reverse_two_port_scan ss) = length ss"
  by (simp add: reverse_two_port_scan_def reverse_two_port_scan_from_length)

lemma reverse_two_port_scan_drop_prefix_from:
  "drop (length xs) (reverse_two_port_scan_from l (xs@ys)) =
    reverse_two_port_scan_from (reverse_left_fold_from l xs) ys"
  by (induct xs arbitrary: l) simp_all

lemma reverse_two_port_scan_prefix_boundary:
  "drop (length xs)
      (reverse_two_port_scan_from reverse_left_initial (xs@ys)) =
    reverse_two_port_scan_from (reverse_left_fold xs) ys"
  by (simp add: reverse_left_fold_def reverse_two_port_scan_drop_prefix_from)

lemma reverse_196_scan_0:
  "reverse_two_port_scan [7,18,7,19] = [15,16,15,19]"
  by (simp add: reverse_two_port_scan_def reverse_left_initial_def
      reverse_right_initial_def reverse_left_advance_def
      reverse_right_advance_def reverse_operands_def reverse_emit_def
      carry_then_def domain_def Let_def)

lemma reverse_196_scan_1:
  "reverse_two_port_scan [15,16,15,19] = [6,13,13,6]"
  by (simp add: reverse_two_port_scan_def reverse_left_initial_def
      reverse_right_initial_def reverse_left_advance_def
      reverse_right_advance_def reverse_operands_def reverse_emit_def
      carry_then_def domain_def Let_def)

lemma reverse_196_scan_2:
  "reverse_two_port_scan [6,13,13,6,19] = [13,7,7,13,19]"
  by (simp add: reverse_two_port_scan_def reverse_left_initial_def
      reverse_right_initial_def reverse_left_advance_def
      reverse_right_advance_def reverse_operands_def reverse_emit_def
      carry_then_def domain_def Let_def)

lemma reverse_196_step_1:
  "step [15,16,15] = [6,13,13,6]"
  by (simp add: step_def digits_def carry_out_def domain_def)

lemma reverse_196_step_2:
  "step [6,13,13,6] = [13,7,7,13]"
  by (simp add: step_def digits_def carry_out_def domain_def)

definition reverse_196_reachable :: "nat \<Rightarrow> nat list" where
  "reverse_196_reachable n = run step n [7,18,7]"

lemma reverse_196_reachable_0 [simp]:
  "reverse_196_reachable 0 = [7,18,7]"
  by (simp add: reverse_196_reachable_def)

lemma reverse_196_reachable_1 [simp]:
  "reverse_196_reachable 1 = [15,16,15]"
proof -
  have duration: "1 = Suc 0" by simp
  show ?thesis unfolding reverse_196_reachable_def duration
    by (simp only: run.simps initial_196_successor)
qed

lemma reverse_196_reachable_2 [simp]:
  "reverse_196_reachable 2 = [6,13,13,6]"
proof -
  have duration: "2 = Suc (Suc 0)" by simp
  show ?thesis unfolding reverse_196_reachable_def duration
    by (simp only: run.simps initial_196_successor reverse_196_step_1)
qed

lemma reverse_196_reachable_3 [simp]:
  "reverse_196_reachable 3 = [13,7,7,13]"
proof -
  have duration: "3 = Suc (Suc (Suc 0))" by simp
  show ?thesis unfolding reverse_196_reachable_def duration
    by (simp only: run.simps initial_196_successor reverse_196_step_1
        reverse_196_step_2)
qed

theorem reverse_two_port_refines_source_generated_196_prefix:
  assumes "n < 3"
  shows "reverse_two_port_publisher (reverse_196_reachable n) =
    reverse_196_reachable (Suc n)"
proof -
  have cases: "n=0 \<or> n=1 \<or> n=2" using assms by arith
  have publisher0:
      "reverse_two_port_publisher [7,18,7] = [15,16,15]"
    by (simp add: reverse_two_port_publisher_def reverse_196_scan_0)
  have publisher1:
      "reverse_two_port_publisher [15,16,15] = [6,13,13,6]"
    by (simp add: reverse_two_port_publisher_def reverse_196_scan_1)
  have publisher2:
      "reverse_two_port_publisher [6,13,13,6] = [13,7,7,13]"
    by (simp add: reverse_two_port_publisher_def reverse_196_scan_2)
  from cases show ?thesis
  proof (elim disjE)
    assume n: "n=0"
    have next0: "Suc 0 = 1" by simp
    show ?thesis using publisher0
      by (simp only: n next0 reverse_196_reachable_0 reverse_196_reachable_1)
  next
    assume n: "n=1"
    have next1: "Suc 1 = 2" by simp
    show ?thesis using publisher1
      by (simp only: n next1 reverse_196_reachable_1 reverse_196_reachable_2)
  next
    assume n: "n=2"
    have next2: "Suc 2 = 3" by simp
    show ?thesis using publisher2
      by (simp only: n next2 reverse_196_reachable_2 reverse_196_reachable_3)
  qed
qed

text \<open>The theorem above binds the exact production-shaped two-port
publisher to the first three states generated from source 196.  It is not an
unbounded reachable-image closure theorem.  Extending the prefix requires a
general proof that the two-port scan equals @{term step} on every valid pair
field, including growth and blank-tail publication.\<close>

text \<open>A blank cell is not the identity on the left producer port: it marks
the beginning of the blank tail.  It is nevertheless a finite idempotent
residual.  The right producer port ignores blank cells, and only the first
blank can publish a terminal carry digit.\<close>

definition reverse_left_blank_residual ::
    "reverse_left_port \<Rightarrow> reverse_left_port" where
  "reverse_left_blank_residual l = reverse_left_advance l 19"

definition reverse_right_blank_residual ::
    "reverse_right_port \<Rightarrow> reverse_right_port" where
  "reverse_right_blank_residual r = reverse_right_advance r 19"

lemma reverse_left_blank_residual_idempotent:
  "reverse_left_blank_residual (reverse_left_blank_residual l) =
    reverse_left_blank_residual l"
  by (cases l) (simp add: reverse_left_blank_residual_def
      reverse_left_advance_def)

lemma reverse_left_blank_residual_not_identity:
  "reverse_left_blank_residual reverse_left_initial \<noteq>
    reverse_left_initial"
  by (simp add: reverse_left_blank_residual_def reverse_left_initial_def
      reverse_left_advance_def)

lemma reverse_right_blank_residual_identity:
  "reverse_right_blank_residual r = r"
  by (simp add: reverse_right_blank_residual_def reverse_right_advance_def)

lemma reverse_emit_first_blank_exact:
  "reverse_emit l 19 r =
    (if rp_sink l then 19
     else if \<not> rp_blank_seen l \<and> rp_previous l \<noteq> None
          \<and> rp_carry l
     then the (rp_previous l) mod 10 + 1
     else 19)"
  by (cases l) (auto simp: reverse_emit_def reverse_operands_def
      split: if_splits option.splits)

lemma reverse_emit_after_first_blank_is_blank:
  "reverse_emit (reverse_left_blank_residual l) 19 r = 19"
  by (cases l) (auto simp: reverse_left_blank_residual_def
      reverse_left_advance_def reverse_emit_def reverse_operands_def
      split: if_splits option.splits)

lemma reverse_right_fold_blank_ray:
  "reverse_right_fold (replicate n 19) = reverse_right_initial"
  by (induct n) (simp_all add: reverse_right_advance_def)

lemma reverse_left_blank_residual_advance:
  "reverse_left_advance l 19 = reverse_left_blank_residual l"
  by (simp add: reverse_left_blank_residual_def)

lemma reverse_two_port_scan_from_blank_residual:
  "reverse_two_port_scan_from (reverse_left_blank_residual l)
      (replicate n 19) = replicate n 19"
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have stable:
    "reverse_left_advance (reverse_left_blank_residual l) 19 =
      reverse_left_blank_residual l"
    using reverse_left_blank_residual_idempotent[of l]
    by (simp only: reverse_left_blank_residual_def)
  show ?case
    using Suc.IH
    by (simp only: replicate_Suc reverse_two_port_scan_from.simps
        reverse_right_fold_blank_ray reverse_emit_after_first_blank_is_blank
        stable Suc.IH)
qed

lemma reverse_two_port_scan_from_blank_ray:
  "reverse_two_port_scan_from l (replicate (Suc n) 19) =
    [reverse_emit l 19 reverse_right_initial] @ replicate n 19"
proof -
  have split:
    "reverse_two_port_scan_from l (replicate (Suc n) 19) =
      reverse_emit l 19 (reverse_right_fold (replicate n 19)) #
        reverse_two_port_scan_from
          (reverse_left_blank_residual l) (replicate n 19)"
    by (simp only: replicate_Suc reverse_two_port_scan_from.simps
        reverse_left_blank_residual_advance)
  show ?thesis
    using split
    by (simp only: reverse_right_fold_blank_ray
        reverse_two_port_scan_from_blank_residual append.simps)
qed

text \<open>The following lemmas apply only to an explicit exterior suffix of
blank pair cells. They do not classify a temporal-machine EXIT state or infer
that a source occurrence has such an exterior. The right carry port ignores
that suffix, while the left port and output retain the first blank boundary.\<close>

lemma reverse_right_fold_append_blank_ray:
  "reverse_right_fold (xs @ replicate n 19) = reverse_right_fold xs"
  by (induction xs) (simp_all add: reverse_right_advance_def
      reverse_right_fold_blank_ray)

lemma reverse_two_port_scan_active_blank_exterior:
  "reverse_two_port_scan_from l (xs @ replicate (Suc n) 19) =
    reverse_two_port_scan_from l (xs@[19]) @ replicate n 19"
proof (induction xs arbitrary: l)
  case Nil
  have blank_ray:
    "reverse_two_port_scan_from l (replicate (Suc n) 19) =
      [reverse_emit l 19 reverse_right_initial] @ replicate n 19"
    by (rule reverse_two_port_scan_from_blank_ray)
  have singleton:
    "reverse_two_port_scan_from l [19] =
      [reverse_emit l 19 reverse_right_initial]"
    by (simp add: reverse_two_port_scan_from.simps)
  show ?case using blank_ray singleton by simp
next
  case (Cons s xs)
  have left_fold:
    "reverse_right_fold (xs @ replicate (Suc n) 19) = reverse_right_fold xs"
    by (rule reverse_right_fold_append_blank_ray)
  have right_fold:
    "reverse_right_fold (xs@[19]) = reverse_right_fold xs"
    using reverse_right_fold_append_blank_ray[of xs 1] by simp
  have suffix:
    "reverse_two_port_scan_from (reverse_left_advance l s)
        (xs @ replicate (Suc n) 19) =
      reverse_two_port_scan_from (reverse_left_advance l s) (xs@[19]) @
        replicate n 19"
    using Cons.IH[of "reverse_left_advance l s"] .
  show ?case
    using suffix left_fold right_fold
    by (simp only: append.simps reverse_two_port_scan_from.simps(2))
qed

lemma reverse_strip_blank_tail_extra:
  "strip_blank_tail (xs@[19]) = strip_blank_tail xs"
  by (induction xs) simp_all

lemma reverse_strip_blank_tail_append_ray:
  "strip_blank_tail (xs @ replicate n 19) = strip_blank_tail xs"
proof (induction n arbitrary: xs)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have split:
    "xs @ replicate (Suc n) 19 = (xs@[19]) @ replicate n 19"
    by (simp add: append_assoc)
  have suffix:
    "strip_blank_tail ((xs@[19]) @ replicate n 19) = strip_blank_tail (xs@[19])"
    using Suc.IH[of "xs@[19]"] .
  show ?case
    using split suffix reverse_strip_blank_tail_extra[of xs]
    by simp
qed

lemma reverse_two_port_publisher_active_blank_exterior:
  "reverse_two_port_publisher (xs @ replicate n 19) =
    reverse_two_port_publisher xs"
proof -
  have scan:
    "reverse_two_port_scan ((xs @ replicate n 19)@[19]) =
      reverse_two_port_scan (xs@[19]) @ replicate n 19"
    using reverse_two_port_scan_active_blank_exterior[of
      reverse_left_initial xs n]
    by (simp add: reverse_two_port_scan_def append_assoc
        replicate_append_same)
  show ?thesis
    unfolding reverse_two_port_publisher_def
    by (simp only: scan reverse_strip_blank_tail_append_ray)
qed

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms carry_then_apply carry_out_append_one reverse_right_fold_forward
      reverse_right_fold_backward reverse_right_fold_valid_carries
      reverse_left_fold_from_append reverse_left_fold_valid_prefix
      reverse_two_port_scan_from_length
      reverse_two_port_scan_length
      reverse_two_port_scan_drop_prefix_from reverse_two_port_scan_prefix_boundary
      reverse_196_scan_0 reverse_196_scan_1 reverse_196_scan_2
      reverse_196_step_1 reverse_196_step_2
      reverse_196_reachable_0 reverse_196_reachable_1
      reverse_196_reachable_2 reverse_196_reachable_3
      reverse_two_port_refines_source_generated_196_prefix
      reverse_left_blank_residual_idempotent
      reverse_left_blank_residual_not_identity
      reverse_right_blank_residual_identity
      reverse_emit_first_blank_exact reverse_emit_after_first_blank_is_blank
      reverse_right_fold_blank_ray reverse_left_blank_residual_advance
      reverse_two_port_scan_from_blank_residual
      reverse_two_port_scan_from_blank_ray
      reverse_right_fold_append_blank_ray reverse_two_port_scan_active_blank_exterior
      reverse_strip_blank_tail_extra reverse_strip_blank_tail_append_ray
      reverse_two_port_publisher_active_blank_exterior}) then ()
    else error "Reverse 196 two-port refinement depends on an oracle";
\<close>

end
