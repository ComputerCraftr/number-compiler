theory Special_Frobenius_Defect_Bridge
  imports Etale_Primality_Bridge
begin

text \<open>A terminal support publisher must produce one candidate-ring
defect E.  Its substantive refinement obligation is local: on every prime
component of N, vanishing of E must be equivalent to the family terminal
stride condition.  The theorems below prove that this exact invariant turns
the single global divisibility (or gcd) observation into the primality bit.
They do not assume or construct such a publisher.\<close>

theorem fermat_terminal_defect_bridge:
  fixes B N E :: nat
  assumes B: "0 < B" and N: "N = B*B+1"
    and local: "\<And>q. prime q \<Longrightarrow> q dvd N \<Longrightarrow>
      (q dvd E \<longleftrightarrow> B dvd q-1)"
  shows "prime N \<longleftrightarrow> N dvd E"
proof
  assume prime: "prime N"
  have threshold: "\<forall>q. prime q \<and> q dvd N \<longrightarrow> B dvd q-1"
    by (rule iffD1[OF fermat_half_threshold_iff_prime[OF B N] prime])
  have atN: "prime N \<and> N dvd N \<longrightarrow> B dvd N-1"
    using threshold by (rule spec)
  have stride: "B dvd N-1"
    using atN prime by simp
  have localN: "N dvd E \<longleftrightarrow> B dvd N-1"
    by (rule local[OF prime]) simp
  show "N dvd E" using localN stride by simp
next
  assume global: "N dvd E"
  have all: "\<forall>q. prime q \<and> q dvd N \<longrightarrow> B dvd q-1"
  proof (intro allI impI)
    fix q assume q: "prime q \<and> q dvd N"
    then have qp: "prime q" and qN: "q dvd N" by auto
    have "q dvd E" using qN global by (rule dvd_trans)
    then show "B dvd q-1" using local[OF qp qN] by simp
  qed
  show "prime N"
    by (rule iffD2[OF fermat_half_threshold_iff_prime[OF B N] all])
qed

theorem mersenne_terminal_defect_bridge:
  fixes C N E :: nat
  assumes C: "1 < C" and N: "N+1 = 2*C*C"
    and local: "\<And>q. prime q \<Longrightarrow> q dvd N \<Longrightarrow>
      (q dvd E \<longleftrightarrow> 2*C dvd q-1 \<or> 2*C dvd q+1)"
  shows "prime N \<longleftrightarrow> N dvd E"
proof
  assume prime: "prime N"
  have threshold: "\<forall>q. prime q \<and> q dvd N \<longrightarrow>
      2*C dvd q-1 \<or> 2*C dvd q+1"
    by (rule iffD1[OF mersenne_half_threshold_iff_prime[OF C N] prime])
  have atN: "prime N \<and> N dvd N \<longrightarrow>
      2*C dvd N-1 \<or> 2*C dvd N+1"
    using threshold by (rule spec)
  have stride: "2*C dvd N-1 \<or> 2*C dvd N+1"
    using atN prime by simp
  have localN: "N dvd E \<longleftrightarrow> 2*C dvd N-1 \<or> 2*C dvd N+1"
    by (rule local[OF prime]) simp
  show "N dvd E" using localN stride by simp
next
  assume global: "N dvd E"
  have all: "\<forall>q. prime q \<and> q dvd N \<longrightarrow>
      2*C dvd q-1 \<or> 2*C dvd q+1"
  proof (intro allI impI)
    fix q assume q: "prime q \<and> q dvd N"
    then have qp: "prime q" and qN: "q dvd N" by auto
    have "q dvd E" using qN global by (rule dvd_trans)
    then show "2*C dvd q-1 \<or> 2*C dvd q+1"
      using local[OF qp qN] by simp
  qed
  show "prime N"
    by (rule iffD2[OF mersenne_half_threshold_iff_prime[OF C N] all])
qed

lemma gcd_full_iff_divides:
  fixes N E :: nat
  shows "gcd N E = N \<longleftrightarrow> N dvd E"
proof
  assume equal: "gcd N E = N"
  show "N dvd E" using gcd_dvd2[of N E] by (simp only: equal)
next
  assume "N dvd E"
  then show "gcd N E = N" by simp
qed

corollary fermat_terminal_gcd_iff_prime:
  fixes B N E :: nat
  assumes "0 < B" "N = B*B+1"
    "\<And>q. prime q \<Longrightarrow> q dvd N \<Longrightarrow>
      (q dvd E \<longleftrightarrow> B dvd q-1)"
  shows "prime N \<longleftrightarrow> gcd N E = N"
  using fermat_terminal_defect_bridge[OF assms]
  by (simp add: gcd_full_iff_divides)

corollary mersenne_terminal_gcd_iff_prime:
  fixes C N E :: nat
  assumes "1 < C" "N+1 = 2*C*C"
    "\<And>q. prime q \<Longrightarrow> q dvd N \<Longrightarrow>
      (q dvd E \<longleftrightarrow> 2*C dvd q-1 \<or> 2*C dvd q+1)"
  shows "prime N \<longleftrightarrow> gcd N E = N"
  using mersenne_terminal_defect_bridge[OF assms]
  by (simp add: gcd_full_iff_divides)

corollary terminal_proper_gcd_prints_factor:
  fixes N E :: nat
  assumes "1 < gcd N E" "gcd N E < N"
  shows "N = gcd N E * (N div gcd N E)"
    "1 < N div gcd N E" "\<not> prime N"
  by (rule coefficient_gcd_prints_exact_factor[OF assms])+

text \<open>The remaining P0 is therefore a construction/refinement theorem,
not another primality equivalence: production must derive E from the powered
source-bound shadow action and prove the local equivalence assumed above.
A supplied quadratic etale root, including D=0, does not provide this E.\<close>

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms fermat_terminal_defect_bridge mersenne_terminal_defect_bridge
      gcd_full_iff_divides fermat_terminal_gcd_iff_prime
      mersenne_terminal_gcd_iff_prime terminal_proper_gcd_prints_factor}) then ()
    else error "Special Frobenius defect bridge depends on an oracle";
\<close>

end
