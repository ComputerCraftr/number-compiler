theory Comma_Decade_Orbit_Arithmetic
  imports Main
begin

ML \<open>
structure Comma_Decade_Orbit_Arithmetic_Profile =
struct
  val started = Time.now ()
  fun report stage =
    let
      val destination = getenv "COMMA_PROFILE_LOG"
      val line = "Decade orbit arithmetic stage=" ^ stage ^ " elapsed_ms=" ^
        LargeInt.toString (Time.toMilliseconds (Time.- (Time.now (), started)))
    in
      if destination = "" then ()
      else
        (Output.physical_stderr (line ^ "\n");
          if destination = "1" then ()
          else File.append (Path.explode destination) (line ^ "\n"))
    end
end
val _ = Comma_Decade_Orbit_Arithmetic_Profile.report "entered"
\<close>

text \<open>Subtraction is signed before reduction modulo 460. Natural
truncated subtraction would not give the sector-1 orbit invariant.\<close>

definition comma_digit_orbit_sum :: "nat \<Rightarrow> int" where
  "comma_digit_orbit_sum d=5*(int d)^2-4*int d"

definition comma_offset_orbit :: "nat \<Rightarrow> nat" where
  "comma_offset_orbit x=nat ((int x-comma_digit_orbit_sum (x mod 10)) mod 460) div 10"

lemma comma_digit_orbit_sum_step:
  "comma_digit_orbit_sum (Suc d)-comma_digit_orbit_sum d=10*int d+1"
  by (simp add: comma_digit_orbit_sum_def power2_eq_square algebra_simps)

lemma comma_digit_orbit_sum_wrap:
  "comma_digit_orbit_sum 10=460" "comma_digit_orbit_sum 0=0"
  by (simp_all add: comma_digit_orbit_sum_def)

lemma comma_offset_orbit_bound:
  "comma_offset_orbit x<46"
proof -
  have bound: "(int x-comma_digit_orbit_sum (x mod 10)) mod 460<460" by simp
  have "nat ((int x-comma_digit_orbit_sum (x mod 10)) mod 460)<460"
    using bound by simp
  then show ?thesis unfolding comma_offset_orbit_def by arith
qed

lemma comma_offset_orbit_step:
  "comma_offset_orbit (x+10*(x mod 10)+1)=comma_offset_orbit x"
proof -
  let ?d = "x mod 10"
  have digit: "?d<10" by simp
  have next_digit: "(x+10*?d+1) mod 10=(?d+1) mod 10"
    by (simp add: mod_add_left_eq mod_Suc_eq)
  show ?thesis
  proof (cases "?d=9")
    case True
    have wrapped: "(x+91) mod 10=0"
      using next_digit True by (simp add: add.commute)
    have residual: "(int x+91) mod 460=(int x-369) mod 460"
    proof -
      have shift: "int x+91=(int x-369)+460" by simp
      show ?thesis by (subst shift) (rule mod_add_self2)
    qed
    show ?thesis
      by (simp add: comma_offset_orbit_def True wrapped comma_digit_orbit_sum_def residual algebra_simps)
  next
    case False
    have bound: "?d+1<10" using digit False by arith
    have difference: "comma_digit_orbit_sum (?d+1)-comma_digit_orbit_sum ?d=10*int ?d+1"
      using comma_digit_orbit_sum_step[of ?d] by simp
    have step: "comma_digit_orbit_sum (?d+1)=comma_digit_orbit_sum ?d+10*int ?d+1"
      using difference by linarith
    have advanced: "(x+10*?d+1) mod 10=?d+1"
      using next_digit mod_less[OF bound] by simp
    show ?thesis
      by (simp only: comma_offset_orbit_def advanced step;
        simp add: algebra_simps)
  qed
qed

lemma comma_digit_orbit_sum_mod10:
  assumes digit: "d<10"
  shows "comma_digit_orbit_sum d mod 10=int d"
proof -
  have general:
    "comma_digit_orbit_sum d mod (10::int)=int d mod (10::int)"
  proof (induction d)
    case 0 then show ?case by (simp add: comma_digit_orbit_sum_def)
  next
    case (Suc d)
    let ?S = "comma_digit_orbit_sum d"
    have step: "comma_digit_orbit_sum (Suc d)=?S+10*int d+1"
      using comma_digit_orbit_sum_step[of d] by linarith
    have pair_mod: "(?S+10*int d) mod (10::int)=(int d+0) mod (10::int)"
      by (rule mod_add_cong[OF Suc.IH]; simp)
    have sum_mod: "(?S+10*int d+1) mod (10::int)=(int d+0+1) mod (10::int)"
      by (rule mod_add_cong[OF pair_mod refl])
    show ?case using step sum_mod by (simp add: add.commute)
  qed
  have nat_digit: "d mod 10=d" using digit by simp
  show ?thesis using general nat_digit by simp
qed

lemma comma_nat_mod460_subtract:
  fixes B a :: nat
  assumes B_bound: "B<460" and a_bound: "a\<le>91"
  shows "nat ((int B-int a) mod (460::int)) =
    (if B<a then 460+B-a else B-a)"
proof (cases "B<a")
  case False
  have order: "a\<le>B" using False by simp
  have difference_bound: "B-a<460" using B_bound order by arith
  have cast: "int (B-a)=int B-int a"
    by (rule of_nat_diff[OF order])
  have residue: "(int B-int a) mod (460::int)=int (B-a)"
    using cast difference_bound by (simp add: mod_less)
  show ?thesis using False residue by simp
next
  case True
  have order: "a\<le>460+B"
    using a_bound by arith
  have difference_bound: "460+B-a<460"
    using True by arith
  have cast: "int (460+B-a)=int B-int a+460"
  proof -
    have difference: "int ((460+B)-a)=int (460+B)-int a"
      by (rule of_nat_diff[OF order])
    show ?thesis using difference by (simp add: algebra_simps)
  qed
  have wrap_mod:
    "int (460+B-a) mod (460::int)=(int B-int a) mod (460::int)"
    by (subst cast) (rule mod_add_self2)
  have residue: "(int B-int a) mod (460::int)=int (460+B-a)"
  proof -
    have reduced: "int (460+B-a) mod (460::int)=int (460+B-a)"
      using difference_bound by (simp add: mod_less)
    show ?thesis by (rule trans[OF wrap_mod[symmetric] reduced])
  qed
  show ?thesis using True residue by simp
qed

ML \<open>
  val helper_claims = @{thms comma_digit_orbit_sum_def comma_offset_orbit_def
    comma_digit_orbit_sum_step comma_digit_orbit_sum_wrap
    comma_offset_orbit_bound comma_offset_orbit_step
    comma_digit_orbit_sum_mod10 comma_nat_mod460_subtract};
  val _ = Thm.consolidate helper_claims;
  val _ = Comma_Decade_Orbit_Arithmetic_Profile.report "claims consolidated";
  val _ = if null (Thm_Deps.all_oracles helper_claims) then ()
    else error "Decade orbit arithmetic depends on an oracle";
\<close>

end
