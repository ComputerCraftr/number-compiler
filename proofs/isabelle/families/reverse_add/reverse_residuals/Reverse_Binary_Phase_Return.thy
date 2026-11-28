theory Reverse_Binary_Phase_Return
  imports Main
begin

text \<open>Read least-significant-first binary digits as integers. Reversing the
list reads the same fixed-width word in the other direction, including its zeroes.\<close>

fun binary_run_value :: "int list \<Rightarrow> int" where
  "binary_run_value [] = 0"
| "binary_run_value (x # xs) = x + 2 * binary_run_value xs"

lemma binary_run_append:
  "binary_run_value (xs @ ys) = binary_run_value xs + 2^length xs * binary_run_value ys"
  by (induction xs) (simp_all add: power_Suc algebra_simps)

lemma binary_run_ones:
  "binary_run_value (replicate n 1) = 2^n - 1"
  by (induction n) (simp_all add: power_Suc algebra_simps)

lemma binary_run_zeroes:
  "binary_run_value (replicate n 0) = 0"
  by (induction n) simp_all

text \<open>The run parameter is indexed by j = k - 2 so every listed run is
positive. The four MSD-first words cover the two binary entries.\<close>

definition binary_return_0 :: "nat \<Rightarrow> int list" where
  "binary_return_0 j = [1,0] @ replicate (Suc (Suc (Suc j))) 1 @ [0,1] @ replicate (Suc (Suc (Suc j))) 0"

definition binary_return_1 :: "nat \<Rightarrow> int list" where
  "binary_return_1 j = [1,1] @ replicate (Suc j) 0 @ [1,0,0,0] @ replicate (Suc j) 1 @ [0,1]"

definition binary_return_2 :: "nat \<Rightarrow> int list" where
  "binary_return_2 j = [1,0] @ replicate (Suc (Suc (Suc j))) 1 @ [0,1] @ replicate (Suc (Suc (Suc (Suc j)))) 0"

definition binary_return_3 :: "nat \<Rightarrow> int list" where
  "binary_return_3 j = [1,1] @ replicate (Suc (Suc (Suc j))) 0 @ [1,0] @ replicate (Suc (Suc j)) 1 @ [0,1]"

theorem binary_return_physical_successors:
  "binary_run_value (rev (binary_return_0 j)) + binary_run_value (binary_return_0 j) =
    binary_run_value (rev (binary_return_1 j))"
  "binary_run_value (rev (binary_return_1 j)) + binary_run_value (binary_return_1 j) =
    binary_run_value (rev (binary_return_2 j))"
  "binary_run_value (rev (binary_return_2 j)) + binary_run_value (binary_return_2 j) =
    binary_run_value (rev (binary_return_3 j))"
  "binary_run_value (rev (binary_return_3 j)) + binary_run_value (binary_return_3 j) =
    binary_run_value (rev (binary_return_0 (Suc j)))"
  by (simp only: binary_return_0_def binary_return_1_def binary_return_2_def
      binary_return_3_def rev_append rev_replicate rev.simps binary_run_append
      binary_run_value.simps binary_run_ones binary_run_zeroes length_append
      list.size length_replicate power_add power_Suc power_0
      append_Nil append_Cons; simp add: algebra_simps)+

lemma binary_return_seed_entries:
  "binary_run_value (rev (binary_return_0 0)) = 744"
  "binary_run_value (rev (binary_return_0 3)) = 48960"
  by (simp_all add: binary_return_0_def numeral_eq_Suc)

fun binary_physical_path :: "int \<Rightarrow> int list list \<Rightarrow> int \<Rightarrow> bool" where
  "binary_physical_path x [] y = (x = y)"
| "binary_physical_path x (w # ws) y =
    (w \<noteq> [] \<and> hd w = 1 \<and> set w \<subseteq> {0,1} \<and> binary_run_value (rev w) = x
     \<and> binary_physical_path (x + binary_run_value w) ws y)"

lemma binary_physical_seed_22:
  "\<exists>ws. length ws = 8 \<and> binary_physical_path 22 ws 744"
  apply (rule exI[where x="[
    [1,0,1,1,0],
    [1,0,0,0,1,1],
    [1,0,1,0,1,0,0],
    [1,1,0,1,0,0,1],
    [1,0,1,1,0,1,0,0],
    [1,1,1,0,0,0,0,1],
    [1,0,1,1,0,1,0,0,0],
    [1,1,0,0,1,0,1,0,1]]"])
  by simp

lemma binary_physical_seed_1:
  "\<exists>ws. length ws = 21 \<and> binary_physical_path 1 ws 48960"
  apply (rule exI[where x="[
    [1],
    [1,0],
    [1,1],
    [1,1,0],
    [1,0,0,1],
    [1,0,0,1,0],
    [1,1,0,1,1],
    [1,1,0,1,1,0],
    [1,0,1,0,0,0,1],
    [1,0,0,1,0,1,1,0],
    [1,1,1,1,1,1,1,1],
    [1,1,1,1,1,1,1,1,0],
    [1,0,1,1,1,1,1,1,0,1],
    [1,0,1,1,1,1,1,1,0,1,0],
    [1,0,0,0,1,1,1,1,0,1,1,1],
    [1,0,1,1,1,1,1,1,0,1,0,0,0],
    [1,1,0,1,0,1,1,1,0,0,1,0,1],
    [1,0,1,1,1,1,1,1,0,1,0,0,0,0],
    [1,1,0,0,1,0,1,1,0,0,1,1,0,1],
    [1,0,1,1,1,1,1,1,0,1,0,0,0,0,0],
    [1,1,0,0,0,1,0,1,0,0,1,1,1,0,1]]"])
  by simp

ML \<open>
  val checked = @{thms binary_return_physical_successors binary_return_seed_entries binary_physical_seed_22 binary_physical_seed_1};
  val _ = if null (Thm_Deps.all_oracles checked) andalso
    not (Thm_Deps.has_skip_proof checked) then () else error "Unchecked binary return";
\<close>

end
