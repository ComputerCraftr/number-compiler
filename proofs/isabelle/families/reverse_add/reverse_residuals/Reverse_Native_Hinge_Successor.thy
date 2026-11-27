theory Reverse_Native_Hinge_Successor
  imports Reverse_Native_Block_Refinement
begin

lemma hinge_high_snoc:
  "take (Suc (length xs)) ((if B then [1] else []) @ rev xs @ [y]) =
   take (length xs) ((if B then [1] else []) @ rev xs) @
    [if B then (case xs of [] \<Rightarrow> 1 | x#_ \<Rightarrow> x) else y]"
  by (cases B; cases xs) (simp_all add: take_append)

lemma hinge_zip_snoc [simp]:
  assumes "length xs = length ys"
  shows "zip (xs @ [x]) (ys @ [y]) = zip xs ys @ [(x,y)]"
  using assms by (induction xs arbitrary: ys) (case_tac ys; auto)+

lemma hinge_emit_general:
  "reverse_native_hinge_next_half half b =
    map (\<lambda>(x,y). x+y) (zip (emit False half)
      (take (length half) (rev (emit b (rev half) @
       (if carry_out b (rev half) then [1] else [])))))"
proof (induction half arbitrary: b rule: rev_induct)
  case Nil then show ?case by (simp add: reverse_native_hinge_next_half_def)
next
  case (snoc s half)
  let ?inlet = "carry_apply (domain s) b"
  let ?B = "carry_out ?inlet (rev half)"
  let ?xs = "emit ?inlet (rev half)"
  have q: "reverse_native_hinge1_compile half ?inlet =
    (carry_out False half,
     if ?B then (if half = [] then 2 else 1 + (last half + (if ?inlet then 1 else 0)) mod 10) else 0)"
    using reverse_native_hinge1_source_response[of half ?inlet]
    by (cases "reverse_native_hinge1_compile half ?inlet") auto
  have h: "(case ?xs of [] \<Rightarrow> 1 | x # _ \<Rightarrow> x) =
    (if half = [] then 1 else (last half + (if ?inlet then 1 else 0)) mod 10)"
    by (cases half rule: rev_cases) simp_all
  let ?old = "take (length half) ((if ?B then [1] else []) @ rev ?xs)"
  let ?digit = "(s + (if b then 1 else 0)) mod 10"
  let ?tail = "if ?B then (if half = [] then 1 else (last half + (if ?inlet then 1 else 0)) mod 10) else ?digit"
  have len: "length ?old = length half"
    by (cases ?B) (simp_all add: length_take min_def)
  have high0: "take (Suc (length half)) ((if ?B then [1] else []) @ rev ?xs @ [?digit]) = ?old @ [?tail]"
    using hinge_high_snoc[of ?xs ?B ?digit] h by (simp only: length_emit length_rev h)
  have high: "take (length (half @ [s]))
      (rev (emit b (rev (half @ [s])) @
        (if carry_out b (rev (half @ [s])) then [1] else []))) = ?old @ [?tail]"
    using high0
    by (cases ?B) (simp_all only: rev_append rev.simps append_Cons append_Nil emit.simps reverse_native_carry_out_cons
        length_append list.size add_Suc_right add_0_right append_assoc if_True if_False)
  have pair: "map (\<lambda>(x,y). x+y) (zip (emit False half @ [(s + (if carry_out False half then 1 else 0)) mod 10]) (?old @ [?tail])) =
       map (\<lambda>(x,y). x+y) (zip (emit False half) ?old) @
       [(s + (if carry_out False half then 1 else 0)) mod 10 + ?tail]"
  proof -
    have eq: "zip (emit False half @ [(s + (if carry_out False half then 1 else 0)) mod 10]) (?old @ [?tail]) =
       zip (emit False half) ?old @ [((s + (if carry_out False half then 1 else 0)) mod 10, ?tail)]"
      by (rule hinge_zip_snoc) (simp only: length_emit len)
    show ?thesis by (simp only: eq map_append list.map split_beta fst_conv snd_conv)
  qed
  have lhs: "reverse_native_hinge_next_half (half @ [s]) b =
    reverse_native_hinge_next_half half ?inlet @ [(s + (if carry_out False half then 1 else 0)) mod 10 + ?tail]"
    by (simp add: reverse_native_hinge_next_half_snoc q Let_def split: if_splits)
  have rhs: "map (\<lambda>(x,y). x+y) (zip (emit False (half @ [s]))
      (take (length (half @ [s])) (rev (emit b (rev (half @ [s])) @
       (if carry_out b (rev (half @ [s])) then [1] else []))))) =
    map (\<lambda>(x,y). x+y) (zip (emit False half) ?old) @
      [(s + (if carry_out False half then 1 else 0)) mod 10 + ?tail]"
    by (simp only: high emit_append emit.simps append_Nil pair)
  have ih: "reverse_native_hinge_next_half half ?inlet = map (\<lambda>(x,y). x+y) (zip (emit False half) ?old)"
    using snoc.IH[of ?inlet] by (cases ?B) (simp_all only: rev_append rev.simps if_True if_False append_Nil)
  show ?case by (simp only: lhs rhs ih)
qed

lemma hinge_physical_list_half:
  "reverse_native_hinge_next_half half (carry_out (carry_out False half) center) =
    take (length half) (step (half @ center @ rev half))"
proof -
  let ?source = "half @ center @ rev half"
  let ?b = "carry_out (carry_out False half) center"
  let ?end = "emit ?b (rev half) @ (if carry_out ?b (rev half) then [1] else [])"
  have low: "take (length half) (digits ?source) = emit False half"
    by (simp add: digits_def emit_append carry_out_append)
  have high: "take (length half) (rev (digits ?source)) = take (length half) (rev ?end)"
    by (simp add: digits_def emit_append carry_out_append rev_append take_append min_def)
  have target: "take (length half) (step ?source) =
      map (\<lambda>(x,y). x+y) (zip (take (length half) (digits ?source))
         (take (length half) (rev (digits ?source))))"
    by (simp only: step_def take_map take_zip)
  show ?thesis using hinge_emit_general[of half ?b] low high target by simp
qed

lemma reverse_native_hinge_physical_half:
  "reverse_native_hinge_next_half half (reverse_native_hinge_inner_inlet half center) =
    take (length half) (step (reverse_native_hinge_source half center))"
proof -
  note middle = reverse_native_center_inlet_exact
  show ?thesis
    using hinge_physical_list_half[of half "case center of None \<Rightarrow> [] | Some d \<Rightarrow> [2*d]"]
    by (cases center) (simp_all add: reverse_native_hinge_source_def reverse_native_hinge_inner_inlet_def carry_out_def middle)
qed
ML \<open>
  val thms = @{thms hinge_emit_general hinge_physical_list_half reverse_native_hinge_physical_half};
  val _ = if null (Thm_Deps.all_oracles thms) andalso not (Thm_Deps.has_skip_proof thms)
    then () else error "hinge physical proof audit failed";
\<close>
end
