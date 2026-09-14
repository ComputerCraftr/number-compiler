theory S_Arithmetic_Skew
  imports Main
begin

text \<open>The common triangular action has no family, source admission or
primality hypothesis. Family records retain their additional boundary data.\<close>

record 'a skew_transfer =
  upper :: 'a
  offset :: 'a
  lower :: 'a

definition shared_skew_then :: "'a::comm_semiring_1 skew_transfer \<Rightarrow>
    'a skew_transfer \<Rightarrow> 'a skew_transfer" where
  "shared_skew_then A B = \<lparr>upper = upper B * upper A,
    offset = upper B * offset A + lower A * offset B,
    lower = lower B * lower A\<rparr>"

definition shared_skew_identity :: "'a::comm_semiring_1 skew_transfer" where
  "shared_skew_identity = \<lparr>upper=1, offset=0, lower=1\<rparr>"

lemma shared_skew_associative:
  "shared_skew_then (shared_skew_then A B) C =
    shared_skew_then A (shared_skew_then B C)"
  by (cases A; cases B; cases C)
    (simp add: shared_skew_then_def algebra_simps)

lemma shared_skew_identities [simp]:
  "shared_skew_then shared_skew_identity A = A"
  "shared_skew_then A shared_skew_identity = A"
  by (cases A; simp add: shared_skew_then_def shared_skew_identity_def)+

lemma shared_skew_transport:
  fixes A B :: "'a::comm_ring_1 skew_transfer"
  assumes first: "upper A*x + offset A = lower A*y"
    and second: "upper B*y + offset B = lower B*z"
  shows "upper (shared_skew_then A B)*x + offset (shared_skew_then A B) =
    lower (shared_skew_then A B)*z"
proof -
  have "upper B * (upper A*x + offset A) + lower A * offset B =
      lower A * (upper B*y + offset B)"
    using first by (simp add: algebra_simps)
  also have "... = lower A * (lower B*z)" using second by simp
  finally show ?thesis by (simp add: shared_skew_then_def algebra_simps)
qed

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms shared_skew_associative shared_skew_identities shared_skew_transport})
    then () else error "Shared skew core oracle dependency";
\<close>
end
