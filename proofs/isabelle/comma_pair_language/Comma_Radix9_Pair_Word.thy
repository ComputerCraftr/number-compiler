theory Comma_Radix9_Pair_Word
  imports Comma_Recursive_Pair_Language
begin

text \<open>The radix-nine observation is a skew residue of the ordered pair
word. Exact domain/residue decoding is separate from this block observation:
a block residue does not determine the word, its endpoint, or branch safety.
The list evaluator below is a specification, not a production constructor.\<close>

definition comma_radix9_decode :: "carry_domain \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_radix9_decode D a=(case D of Below \<Rightarrow> a mod 9
    | Equal \<Rightarrow> 9
    | Above \<Rightarrow> (if a mod 9=0 then 18 else 9+a mod 9))"

lemma comma_radix9_domain_exact:
  assumes "s\<le>18"
  shows "comma_radix9_decode (domain s) (s mod 9)=s"
proof -
  have "s=0 \<or> s=1 \<or> s=2 \<or> s=3 \<or> s=4 \<or> s=5 \<or> s=6 \<or>
    s=7 \<or> s=8 \<or> s=9 \<or> s=10 \<or> s=11 \<or> s=12 \<or> s=13 \<or>
    s=14 \<or> s=15 \<or> s=16 \<or> s=17 \<or> s=18" using assms by arith
  then show ?thesis by (auto simp: comma_radix9_decode_def domain_def)
qed

lemma comma_radix9_defect:
  "(int s-9) mod 9=int (s mod 9)"
  by (simp add: zmod_int)

lemma comma_native19_radix9_roundtrip:
  assumes "comma_native19_admitted q"
  shows "comma_radix9_decode (domain (comma_native19_decode q))
      (comma_native19_decode q mod 9)=comma_native19_decode q"
  by (rule comma_radix9_domain_exact[OF comma_native19_range[OF assms]])

text \<open>Only the length phase modulo six is needed to compose F9.
The full length remains occurrence data.\<close>
lemma comma_radix9_length_phase:
  "(2::nat)^n mod 9=2^(n mod 6) mod 9"
  by (rule comma_residue_power_phase) simp_all

definition comma_radix9_merge :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_radix9_merge n a b=(a+2^n*b) mod 9"

lemma comma_radix9_merge_closed:
  "comma_radix9_merge n a b<9"
  by (simp add: comma_radix9_merge_def)

lemma comma_radix9_merge_phase:
  "comma_radix9_merge n a b=comma_radix9_merge (n mod 6) a b"
proof -
  have product: "(2^n*b) mod 9=(2^(n mod 6)*b) mod 9"
    by (rule mod_mult_cong[OF comma_radix9_length_phase refl])
  show ?thesis unfolding comma_radix9_merge_def
    by (rule mod_add_cong[OF refl product])
qed

lemma comma_radix9_merge_assoc:
  "comma_radix9_merge (n+m) (comma_radix9_merge n a b) c =
    comma_radix9_merge n a (comma_radix9_merge m b c)"
  by (simp add: comma_radix9_merge_def power_add mod_simps
    comma_pair_affine_residue algebra_simps)

fun comma_radix9_eval :: "nat list \<Rightarrow> nat" where
  "comma_radix9_eval []=0"
| "comma_radix9_eval (s#ss)=comma_radix9_merge 1 (s mod 9) (comma_radix9_eval ss)"

lemma comma_radix9_eval_closed: "comma_radix9_eval xs<9"
  by (cases xs) (simp_all add: comma_radix9_merge_closed)

lemma comma_radix9_eval_append:
  "comma_radix9_eval (xs@ys)=comma_radix9_merge (length xs)
    (comma_radix9_eval xs) (comma_radix9_eval ys)"
proof (induction xs)
  case Nil
  then show ?case using comma_radix9_eval_closed[of ys]
    by (simp add: comma_radix9_merge_def)
next
  case (Cons x xs)
  then show ?case using comma_radix9_merge_assoc[of 1 "length xs"
    "x mod 9" "comma_radix9_eval xs" "comma_radix9_eval ys"] by simp
qed

corollary comma_radix9_eval_square:
  "comma_radix9_eval (xs@xs)=comma_radix9_merge (length xs mod 6)
    (comma_radix9_eval xs) (comma_radix9_eval xs)"
  using comma_radix9_eval_append[of xs xs] comma_radix9_merge_phase by metis

ML \<open>
  val checked = @{thms comma_radix9_domain_exact comma_radix9_defect
    comma_native19_radix9_roundtrip comma_radix9_length_phase
    comma_radix9_merge_closed comma_radix9_merge_assoc
    comma_radix9_eval_append comma_radix9_eval_square};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Radix-nine word depends on an oracle";
\<close>
end
