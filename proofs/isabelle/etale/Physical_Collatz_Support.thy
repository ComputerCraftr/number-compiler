theory Physical_Collatz_Support
  imports Physical_Collatz_Clock Skew_Cylinder_Observers
begin

text \<open>A physical support program retains the ordered branch support of a
source-bound Collatz computation.  It is more informative than the endpoint
and the two branch counts: concatenation records chronological order, while
evaluation projects that order into any chosen S-arithmetic coefficient
semiring.\<close>

datatype physical_support =
    Support_Id
  | Support_Even
  | Support_Odd
  | Support_Then physical_support physical_support

fun support_eval ::
  "'a::comm_semiring_1 \<Rightarrow> 'a \<Rightarrow> physical_support
    \<Rightarrow> 'a skew_transfer"
where
  "support_eval s z Support_Id = skew_identity"
| "support_eval s z Support_Even =
    \<lparr>upper=1, offset=0, lower=z\<rparr>"
| "support_eval s z Support_Odd =
    \<lparr>upper=s, offset=1, lower=1\<rparr>"
| "support_eval s z (Support_Then A B) =
    skew_then (support_eval s z A) (support_eval s z B)"

lemma support_eval_composition:
  "support_eval s z (Support_Then A B) =
    skew_then (support_eval s z A) (support_eval s z B)"
  by simp

lemma support_eval_reassociation:
  "support_eval s z (Support_Then (Support_Then A B) C) =
    support_eval s z (Support_Then A (Support_Then B C))"
  by (simp add: skew_associative)

theorem support_eval_mapping:
  fixes f :: "'a::comm_semiring_1 \<Rightarrow> 'b::comm_semiring_1"
  assumes zero: "f 0 = 0"
    and one: "f 1 = 1"
    and plus: "\<And>x y. f (x+y) = f x + f y"
    and times: "\<And>x y. f (x*y) = f x * f y"
  shows "skew_map f (support_eval s z P) =
    support_eval (f s) (f z) P"
proof (induction P)
  case Support_Id
  then show ?case by (simp add: skew_map_def skew_identity_def shared_skew_identity_def zero one)
next
  case Support_Even
  then show ?case by (simp add: skew_map_def zero one)
next
  case Support_Odd
  then show ?case by (simp add: skew_map_def zero one)
next
  case (Support_Then P Q)
  have mapped:
    "skew_map f
       (skew_then (support_eval s z P) (support_eval s z Q)) =
     skew_then (skew_map f (support_eval s z P))
       (skew_map f (support_eval s z Q))"
    by (rule observer_commutes_with_composition[OF plus times])
  show ?case using mapped Support_Then.IH by simp
qed

fun physical_support_program :: "nat \<Rightarrow> nat \<Rightarrow> physical_support"
where
  "physical_support_program 0 x = Support_Id"
| "physical_support_program (Suc n) x =
    Support_Then
      (if even x then Support_Even else Support_Odd)
      (physical_support_program n (physical_next x))"

text \<open>The program is generated from the successive physical sources.
There is no parity word supplied by a caller.\<close>

theorem physical_support_eval_matrix:
  "support_eval (3::int) 2 (physical_support_program n x) =
    physical_matrix n x"
proof (induction n arbitrary: x)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case
    by (cases "even x")
      (simp_all add: physical_atom_def)
qed

lemma physical_support_program_4:
  "physical_support_program 3 4 =
    Support_Then Support_Even
      (Support_Then Support_Even
        (Support_Then Support_Odd Support_Id))"
proof -
  have duration: "(3::nat) = Suc (Suc (Suc 0))" by simp
  show ?thesis unfolding duration by (simp add: physical_next_def)
qed

lemma physical_support_program_5:
  "physical_support_program 3 5 =
    Support_Then Support_Odd
      (Support_Then Support_Even
        (Support_Then Support_Even Support_Id))"
proof -
  have duration: "(3::nat) = Suc (Suc (Suc 0))" by simp
  show ?thesis unfolding duration by (simp add: physical_next_def)
qed

lemma physical_sources_4_5_same_normalization:
  "(physical_next ^^ 3) 4 = 4"
  "(physical_next ^^ 3) 5 = 4"
  "physical_odd_count 3 4 = 1"
  "physical_odd_count 3 5 = 1"
proof -
  have duration: "(3::nat) = Suc (Suc (Suc 0))" by simp
  show "(physical_next ^^ 3) 4 = 4"
    unfolding duration by (simp add: physical_next_def)
  show "(physical_next ^^ 3) 5 = 4"
    unfolding duration by (simp add: physical_next_def)
  show "physical_odd_count 3 4 = 1"
    unfolding duration by (simp add: physical_next_def)
  show "physical_odd_count 3 5 = 1"
    unfolding duration by (simp add: physical_next_def)
qed

lemma physical_sources_4_5_distinct_support_offsets:
  "offset (support_eval (1::int) 2 (physical_support_program 3 4)) = 4"
  "offset (support_eval (1::int) 2 (physical_support_program 3 5)) = 1"
  using physical_support_program_4 physical_support_program_5
  by (simp_all add: skew_then_def shared_skew_then_def skew_identity_def shared_skew_identity_def)

text \<open>The three-tick equations are the smallest mathematical witness.
The eight-tick equations below are the corresponding normalized-consumer
merge: both sources have reached 1 with two odd and six even ticks.\<close>

lemma physical_sources_4_5_eight_tick_merge:
  "(physical_next ^^ 8) 4 = 1"
  "(physical_next ^^ 8) 5 = 1"
  "physical_odd_count 8 4 = 2"
  "physical_odd_count 8 5 = 2"
proof -
  have duration: "(8::nat) =
      Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))" by simp
  show "(physical_next ^^ 8) 4 = 1"
    unfolding duration by (simp add: physical_next_def)
  show "(physical_next ^^ 8) 5 = 1"
    unfolding duration by (simp add: physical_next_def)
  show "physical_odd_count 8 4 = 2"
    unfolding duration by (simp add: physical_next_def)
  show "physical_odd_count 8 5 = 2"
    unfolding duration by (simp add: physical_next_def)
qed

lemma physical_sources_4_5_eight_tick_support_offsets:
  "offset (support_eval (1::int) 2 (physical_support_program 8 4)) = 20"
  "offset (support_eval (1::int) 2 (physical_support_program 8 5)) = 17"
proof -
  have duration: "(8::nat) =
      Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))" by simp
  show "offset (support_eval (1::int) 2
      (physical_support_program 8 4)) = 20"
    unfolding duration
    by (simp add: physical_next_def skew_then_def shared_skew_then_def skew_identity_def shared_skew_identity_def)
  show "offset (support_eval (1::int) 2
      (physical_support_program 8 5)) = 17"
    unfolding duration
    by (simp add: physical_next_def skew_then_def shared_skew_then_def skew_identity_def shared_skew_identity_def)
qed

theorem endpoint_and_weight_do_not_determine_support:
  "(physical_next ^^ 3) 4 = (physical_next ^^ 3) 5 \<and>
   physical_odd_count 3 4 = physical_odd_count 3 5 \<and>
   offset (support_eval (1::int) 2 (physical_support_program 3 4)) \<noteq>
     offset (support_eval (1::int) 2 (physical_support_program 3 5))"
  using physical_sources_4_5_same_normalization
    physical_sources_4_5_distinct_support_offsets by simp

text \<open>The last theorem is an exact loss-of-information result for the
endpoint-plus-weight normalization.  It is not a counterexample to a common
shadow cylinder: the support programs are concrete semantic representatives.
The mapping theorem proves coefficient-semiring specialization of the skew
evaluation.  Specific directional, Hasse, cyclic, negacyclic, and tropical
codomains and their homomorphism laws are not defined or proved here.\<close>

ML \<open>
 val _ = if null (Thm_Deps.all_oracles @{thms
   support_eval_composition support_eval_reassociation support_eval_mapping
   physical_support_eval_matrix physical_support_program_4
   physical_support_program_5 physical_sources_4_5_same_normalization
   physical_sources_4_5_distinct_support_offsets
   physical_sources_4_5_eight_tick_merge
   physical_sources_4_5_eight_tick_support_offsets
   endpoint_and_weight_do_not_determine_support})
   then () else error "Physical Collatz support oracle dependency";
\<close>

end
