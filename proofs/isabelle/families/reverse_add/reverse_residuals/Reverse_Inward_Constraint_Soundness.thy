theory Reverse_Inward_Constraint_Soundness
  imports Reverse_Carry_Harmonic_Ports
begin

text \<open>
This theory specifies the soundness boundary for finite inward constraints.
The concrete Python propagator uses finite decimal/carry masks and repeatedly
removes values without local factor support. This theory formalizes the
support-filter contract and proves that any concrete assignment satisfying
the factors survives every narrowing round. It is a semantic contract for the
implementation, not a line-by-line refinement of the Python loops. It does
not establish that arc consistency finds a global assignment, that a
surviving candidate is a trajectory, or that a finite period is authorized
to repeat. The set-based must-value definition below is a logical
specification only; executable must reads use the distinct list matcher
defined later in this theory.

Domains below are sets, so digit-option duplication is idempotent. This
specification does not justify encoding an option list by summing powers of
two when repeated values are present; the executable boundary must use a
set-union/bitwise-OR encoding of the allowed digits.
\<close>

definition inward_digit_option_domain :: "nat list \<Rightarrow> nat set" where
  "inward_digit_option_domain options = set options"

lemma inward_digit_option_domain_duplicate_idempotent:
  "inward_digit_option_domain (options @ options) =
    inward_digit_option_domain options"
  by (simp add: inward_digit_option_domain_def)

definition inward_admitted ::
  "(nat \<Rightarrow> nat set) \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> bool" where
  "inward_admitted domains width row \<longleftrightarrow>
    length row = width \<and> (\<forall>i<width. row ! i \<in> domains i)"

definition inward_supported ::
  "(nat \<Rightarrow> nat set) \<Rightarrow> nat \<Rightarrow>
    (nat list \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "inward_supported domains width factor i value \<longleftrightarrow>
    i < width \<and> (\<exists>row. inward_admitted domains width row \<and>
      factor row \<and> row ! i = value)"

definition inward_may_values ::
  "(nat \<Rightarrow> nat set) \<Rightarrow> nat \<Rightarrow>
    (nat list \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> nat set" where
  "inward_may_values domains width factor i =
    {value. inward_supported domains width factor i value}"

definition inward_must_value ::
  "(nat \<Rightarrow> nat set) \<Rightarrow> nat \<Rightarrow>
    (nat list \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> nat option" where
  "inward_must_value domains width factor i =
    (let values = inward_may_values domains width factor i in
      if (\<exists>value. values = {value})
      then Some (SOME value. values = {value}) else None)"

definition inward_factor_filter ::
  "(nat \<Rightarrow> nat set) \<Rightarrow> nat \<Rightarrow>
    (nat list \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> nat set" where
  "inward_factor_filter domains width factor i =
    (if i < width then
      domains i \<inter> inward_may_values domains width factor i
     else domains i)"

lemma inward_factor_filter_preserves_model:
  assumes admitted: "inward_admitted domains width row"
      and factor: "factor row"
  shows "inward_admitted
      (inward_factor_filter domains width factor) width row"
proof -
  have member: "row ! i \<in> inward_may_values domains width factor i"
    if "i < width" for i
    using admitted factor that
    unfolding inward_may_values_def inward_supported_def
      inward_admitted_def
    by (auto intro!: exI[of _ row])
  show ?thesis
    using admitted member
    unfolding inward_admitted_def inward_factor_filter_def
    by auto
qed

fun inward_filter_sweep ::
  "nat \<Rightarrow> (nat list \<Rightarrow> bool) list \<Rightarrow>
    (nat \<Rightarrow> nat set) \<Rightarrow> (nat \<Rightarrow> nat set)" where
  "inward_filter_sweep width [] domains = domains"
| "inward_filter_sweep width (factor # factors) domains =
    inward_filter_sweep width factors
      (inward_factor_filter domains width factor)"

lemma inward_filter_sweep_preserves_model:
  assumes admitted: "inward_admitted domains width row"
      and factors: "\<forall>factor\<in>set constraints. factor row"
  shows "inward_admitted
      (inward_filter_sweep width constraints domains) width row"
  using admitted factors
proof (induction constraints arbitrary: domains)
  case Nil
  then show ?case by simp
next
  case (Cons factor constraints)
  have head: "factor row" using Cons.prems(2) by auto
  have tail: "\<forall>next\<in>set constraints. next row"
    using Cons.prems(2) by auto
  have next_admitted:
    "inward_admitted (inward_factor_filter domains width factor) width row"
  proof (rule inward_factor_filter_preserves_model)
    show "inward_admitted domains width row" using Cons.prems(1) .
    show "factor row" using head .
  qed
  have tail_admitted:
    "inward_admitted
      (inward_filter_sweep width constraints
        (inward_factor_filter domains width factor)) width row"
  proof (rule Cons.IH)
    show "inward_admitted (inward_factor_filter domains width factor) width row"
      using next_admitted .
    show "\<forall>next\<in>set constraints. next row" using tail .
  qed
  show ?case
    using tail_admitted by simp
qed

fun inward_filter_rounds ::
  "nat \<Rightarrow> nat \<Rightarrow> (nat list \<Rightarrow> bool) list \<Rightarrow>
    (nat \<Rightarrow> nat set) \<Rightarrow> (nat \<Rightarrow> nat set)" where
  "inward_filter_rounds 0 width constraints domains = domains"
| "inward_filter_rounds (Suc rounds) width constraints domains =
    inward_filter_rounds rounds width constraints
      (inward_filter_sweep width constraints domains)"

theorem inward_filter_rounds_preserve_every_concrete_model:
  assumes admitted: "inward_admitted domains width row"
      and constraints: "\<forall>factor\<in>set factors. factor row"
  shows "inward_admitted
      (inward_filter_rounds rounds width factors domains) width row"
  using admitted constraints
proof (induction rounds arbitrary: domains)
  case 0
  then show ?case by simp
next
  case (Suc rounds)
  have after_sweep:
    "inward_admitted (inward_filter_sweep width factors domains) width row"
  proof (rule inward_filter_sweep_preserves_model)
    show "inward_admitted domains width row" using Suc.prems(1) .
    show "\<forall>factor\<in>set factors. factor row" using Suc.prems(2) .
  qed
  have after_rounds:
    "inward_admitted
      (inward_filter_rounds rounds width factors
        (inward_filter_sweep width factors domains)) width row"
  proof (rule Suc.IH)
    show "inward_admitted (inward_filter_sweep width factors domains) width row"
      using after_sweep .
    show "\<forall>factor\<in>set factors. factor row" using Suc.prems(2) .
  qed
  show ?case
    using after_rounds by simp
qed

lemma inward_may_values_contains_model_port:
  assumes admitted: "inward_admitted domains width row"
      and factor: "factor row"
      and port: "i < width"
  shows "row ! i \<in> inward_may_values domains width factor i"
  using admitted factor port
  unfolding inward_may_values_def inward_supported_def inward_admitted_def
  by (auto intro!: exI[of _ row])

lemma inward_must_value_is_supported_singleton:
  assumes read: "inward_must_value domains width factor i = Some value"
  shows "inward_may_values domains width factor i = {value}"
proof -
  let ?values = "inward_may_values domains width factor i"
  have singleton: "\<exists>candidate. ?values = {candidate}"
    and selected: "(SOME candidate. ?values = {candidate}) = value"
    using read unfolding inward_must_value_def
    by (auto simp: Let_def split: if_splits)
  have "?values = {SOME candidate. ?values = {candidate}}"
    using singleton by (rule someI_ex)
  with selected show ?thesis by simp
qed

theorem inward_must_value_matches_any_admitted_model:
  assumes admitted: "inward_admitted domains width row"
      and factor: "factor row"
      and read: "inward_must_value domains width factor i = Some value"
  shows "i < width \<and> value = row ! i"
proof -
  have singleton:
    "inward_may_values domains width factor i = {value}"
  proof (rule inward_must_value_is_supported_singleton)
    show "inward_must_value domains width factor i = Some value" using read .
  qed
  have index: "i < width"
    using singleton unfolding inward_may_values_def inward_supported_def
    by auto
  have port: "row ! i \<in> inward_may_values domains width factor i"
  proof (rule inward_may_values_contains_model_port)
    show "inward_admitted domains width row" using admitted .
    show "factor row" using factor .
    show "i < width" using index .
  qed
  show ?thesis
    using index port singleton by auto
qed

definition inward_list_must_value :: "nat list \<Rightarrow> nat option" where
  "inward_list_must_value xs =
    (case remdups xs of [value] \<Rightarrow> Some value | _ \<Rightarrow> None)"

lemma distinct_list_with_singleton_set:
  assumes distinct: "distinct xs" and singleton: "set xs = {value}"
  shows "xs = [value]"
proof (cases xs)
  case Nil
  then show ?thesis using singleton by auto
next
  case (Cons head tail)
  note outer = Cons
  have head_value: "head = value"
    using singleton outer by auto
  have head_not_in_tail: "head \<notin> set tail"
    using distinct outer by simp
  have tail_subset: "set tail \<subseteq> {value}"
    using singleton outer by auto
  have value_not_in_tail: "value \<notin> set tail"
    using head_not_in_tail head_value by simp
  have tail_shape: "set tail = {} \<or> set tail = {value}"
    using tail_subset by (rule subset_singletonD)
  have tail_empty: "set tail = {}"
  proof -
    from tail_shape show ?thesis
    proof
      assume "set tail = {}"
      then show ?thesis .
    next
      assume "set tail = {value}"
      with value_not_in_tail show ?thesis by blast
    qed
  qed
  have "tail = []" using tail_empty by simp
  with outer head_value show ?thesis by simp
qed

lemma inward_list_must_value_exact:
  "inward_list_must_value xs = Some value \<longleftrightarrow>
    set xs = {value}"
proof
  assume read: "inward_list_must_value xs = Some value"
  then have remdups_eq: "remdups xs = [value]"
    unfolding inward_list_must_value_def
    by (cases "remdups xs") (auto split: list.splits)
  have set_eq: "set (remdups xs) = set xs" by simp
  have set_remdups: "set (remdups xs) = set [value]"
    by (rule arg_cong[OF remdups_eq])
  have "set xs = set [value]"
  proof -
    have "set xs = set (remdups xs)" using set_eq by (rule sym)
    also have "... = set [value]" using set_remdups .
    finally show ?thesis .
  qed
  then show "set xs = {value}" by simp
next
  assume singleton: "set xs = {value}"
  have distinct: "distinct (remdups xs)" by simp
  have set_remdups: "set (remdups xs) = {value}"
  proof -
    have set_eq: "set (remdups xs) = set xs" by simp
    also have "... = {value}" using singleton .
    finally show ?thesis .
  qed
  have "remdups xs = [value]"
    by (rule distinct_list_with_singleton_set[OF distinct set_remdups])
  then show "inward_list_must_value xs = Some value"
    unfolding inward_list_must_value_def by simp
qed

text \<open>The following local factors are the decimal/carry relations used by
the inward solver. They describe one actual addition column, reflected pair,
raw subtraction borrow, carry XOR, or decimal residue. Support propagation is
sound only for these exact relations; a hypothetical pair period is just
another constraint and supplies no temporal authority.\<close>

definition reverse_add_column_factor :: "nat list \<Rightarrow> bool" where
  "reverse_add_column_factor column \<longleftrightarrow>
    length column = 5 \<and> column ! 0 < 10 \<and> column ! 1 < 10 \<and>
    column ! 2 < 2 \<and> column ! 3 < 10 \<and> column ! 4 < 2 \<and>
    column ! 0 + column ! 1 + column ! 2 = column ! 3 + 10 * column ! 4"

text \<open>The following executable boundary enumerates only supplied local
domains. Each list is checked against the decimal/carry alphabet and a length
ceiling before the Cartesian product is constructed. Consequently the work
list contains at most \<open>10 * 10 * 2 * 10 * 2 = 4000\<close> rows. Duplicate
domain entries are harmless: they can duplicate rows but cannot add a
different support value. This is a bounded local support computation, not a
global assignment solver.\<close>

definition reverse_add_column_candidate_rows ::
  "nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow>
    nat list \<Rightarrow> nat list \<Rightarrow> nat list list" where
  "reverse_add_column_candidate_rows d0 d1 d2 d3 d4 =
    [[a,b,c,d,e]. a \<leftarrow> d0, b \<leftarrow> d1, c \<leftarrow> d2,
      d \<leftarrow> d3, e \<leftarrow> d4]"

definition reverse_add_column_candidate_domains ::
  "nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow>
    nat list \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat set" where
  "reverse_add_column_candidate_domains d0 d1 d2 d3 d4 i =
    (if i = 0 then set d0 else if i = 1 then set d1 else
     if i = 2 then set d2 else if i = 3 then set d3 else
     if i = 4 then set d4 else {})"

definition reverse_add_column_candidate_admitted ::
  "nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow>
    nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> bool" where
  "reverse_add_column_candidate_admitted d0 d1 d2 d3 d4 row \<longleftrightarrow>
    inward_admitted (reverse_add_column_candidate_domains d0 d1 d2 d3 d4)
      5 row"

lemma reverse_add_column_candidate_rows_exact:
  "set (reverse_add_column_candidate_rows d0 d1 d2 d3 d4) =
    {row. reverse_add_column_candidate_admitted d0 d1 d2 d3 d4 row}"
proof (rule set_eqI; simp only: mem_Collect_eq)
  fix row
  show "row \<in> set (reverse_add_column_candidate_rows d0 d1 d2 d3 d4) \<longleftrightarrow>
      reverse_add_column_candidate_admitted d0 d1 d2 d3 d4 row"
  proof
    assume member:
      "row \<in> set (reverse_add_column_candidate_rows d0 d1 d2 d3 d4)"
    then obtain a b c d e where
      row: "row = [a,b,c,d,e]" and
      a: "a \<in> set d0" and b: "b \<in> set d1" and
      c: "c \<in> set d2" and d: "d \<in> set d3" and e: "e \<in> set d4"
      unfolding reverse_add_column_candidate_rows_def by auto
    show "reverse_add_column_candidate_admitted d0 d1 d2 d3 d4 row"
      using a b c d e row
      unfolding reverse_add_column_candidate_admitted_def
        reverse_add_column_candidate_domains_def inward_admitted_def
      by (auto simp: nth_Cons_Suc)
  next
    assume admitted:
      "reverse_add_column_candidate_admitted d0 d1 d2 d3 d4 row"
    then have len: "length row = 5"
      unfolding reverse_add_column_candidate_admitted_def inward_admitted_def
      by simp
    have all_slots:
      "\<forall>i<5. row ! i \<in>
        reverse_add_column_candidate_domains d0 d1 d2 d3 d4 i"
      using admitted unfolding reverse_add_column_candidate_admitted_def
        inward_admitted_def by blast
    have slot0: "row ! 0 \<in> set d0"
      using all_slots[rule_format, of 0]
      unfolding reverse_add_column_candidate_domains_def by simp
    have slot1: "row ! 1 \<in> set d1"
      using all_slots[rule_format, of 1]
      unfolding reverse_add_column_candidate_domains_def by simp
    have slot2: "row ! 2 \<in> set d2"
      using all_slots[rule_format, of 2]
      unfolding reverse_add_column_candidate_domains_def by simp
    have slot3: "row ! 3 \<in> set d3"
      using all_slots[rule_format, of 3]
      unfolding reverse_add_column_candidate_domains_def by simp
    have slot4: "row ! 4 \<in> set d4"
      using all_slots[rule_format, of 4]
      unfolding reverse_add_column_candidate_domains_def by simp
    have row_eq: "row = [row ! 0, row ! 1, row ! 2, row ! 3, row ! 4]"
    proof (rule nth_equalityI)
      show "length row = length [row ! 0, row ! 1, row ! 2, row ! 3, row ! 4]"
        using len by simp
    next
      fix j
      assume j_lt: "j < length row"
      have j_lt5: "j < 5" using j_lt len by simp
      then have "j = 0 \<or> j = 1 \<or> j = 2 \<or> j = 3 \<or> j = 4"
        by presburger
      then show "row ! j = [row ! 0, row ! 1, row ! 2, row ! 3, row ! 4] ! j"
        by auto
    qed
    have candidate_membership:
      "row \<in> set (reverse_add_column_candidate_rows d0 d1 d2 d3 d4) \<longleftrightarrow>
       (\<exists>a\<in>set d0. \<exists>b\<in>set d1. \<exists>c\<in>set d2. \<exists>d\<in>set d3.
          row \<in> (\<lambda>e. [a,b,c,d,e]) ` set d4)"
      unfolding reverse_add_column_candidate_rows_def
      by (simp only: set_concat set_map UN_iff bex_simps(7))
    have nested:
      "\<exists>a\<in>set d0. \<exists>b\<in>set d1. \<exists>c\<in>set d2. \<exists>d\<in>set d3.
        row \<in> (\<lambda>e. [a,b,c,d,e]) ` set d4"
    proof (rule bexI[where x="row ! 0"])
      show "\<exists>b\<in>set d1. \<exists>c\<in>set d2. \<exists>d\<in>set d3.
        row \<in> (\<lambda>e. [row ! 0,b,c,d,e]) ` set d4"
      proof (rule bexI[where x="row ! 1"])
        show "\<exists>c\<in>set d2. \<exists>d\<in>set d3.
          row \<in> (\<lambda>e. [row ! 0, row ! 1,c,d,e]) ` set d4"
        proof (rule bexI[where x="row ! 2"])
          show "\<exists>d\<in>set d3.
            row \<in> (\<lambda>e. [row ! 0, row ! 1, row ! 2,d,e]) ` set d4"
          proof (rule bexI[where x="row ! 3"])
            show "row \<in>
                (\<lambda>e. [row ! 0, row ! 1, row ! 2, row ! 3, e]) ` set d4"
            proof (rule image_eqI[where x="row ! 4"])
              show "row = (\<lambda>e. [row ! 0, row ! 1, row ! 2, row ! 3, e])
                  (row ! 4)"
                using row_eq by simp
              show "row ! 4 \<in> set d4" using slot4 .
            qed
            show "row ! 3 \<in> set d3" using slot3 .
          qed
          show "row ! 2 \<in> set d2" using slot2 .
        qed
        show "row ! 1 \<in> set d1" using slot1 .
      qed
      show "row ! 0 \<in> set d0" using slot0 .
    qed
    show "row \<in> set (reverse_add_column_candidate_rows d0 d1 d2 d3 d4)"
      by (rule iffD2[OF candidate_membership nested])
  qed
qed

lemma length_concat_map_uniform:
  assumes uniform: "\<forall>x\<in>set xs. length (f x) = k"
  shows "length (concat (map f xs)) = length xs * k"
  using uniform
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  have head: "length (f x) = k" using Cons.prems by simp
  have tail: "\<forall>y\<in>set xs. length (f y) = k"
    using Cons.prems by auto
  have tail_result: "length (concat (map f xs)) = length xs * k"
    using Cons.IH tail by blast
  have step:
    "length (concat (map f (x # xs))) =
      length (f x) + length (concat (map f xs))"
  proof -
    have "length (concat (map f (x # xs))) =
        sum_list (map length (map f (x # xs)))"
      by (simp add: length_concat)
    also have "... = length (f x) + sum_list (map length (map f xs))"
      by simp
    also have "... = length (f x) + length (concat (map f xs))"
      by (simp add: length_concat)
    finally show ?thesis .
  qed
  show ?case using step head tail_result by simp
qed

lemma reverse_add_column_candidate_rows_length:
  "length (reverse_add_column_candidate_rows d0 d1 d2 d3 d4) =
    length d0 * length d1 * length d2 * length d3 * length d4"
proof -
  have h3:
    "length (concat (map (\<lambda>d. map (\<lambda>e. [a,b,c,d,e]) d4) d3)) =
      length d3 * length d4" for a b c
    by (rule length_concat_map_uniform) simp
  have h2:
    "length (concat (map (\<lambda>c.
      concat (map (\<lambda>d. map (\<lambda>e. [a,b,c,d,e]) d4) d3)) d2)) =
      length d2 * (length d3 * length d4)" for a b
    by (rule length_concat_map_uniform) (simp add: h3)
  have h1:
    "length (concat (map (\<lambda>b. concat (map (\<lambda>c.
      concat (map (\<lambda>d. map (\<lambda>e. [a,b,c,d,e]) d4) d3)) d2)) d1)) =
      length d1 * (length d2 * (length d3 * length d4))" for a
    by (rule length_concat_map_uniform) (simp add: h2)
  have h0:
    "length (concat (map (\<lambda>a. concat (map (\<lambda>b. concat (map (\<lambda>c.
      concat (map (\<lambda>d. map (\<lambda>e. [a,b,c,d,e]) d4) d3)) d2)) d1)) d0)) =
      length d0 * (length d1 * (length d2 * (length d3 * length d4)))"
    by (rule length_concat_map_uniform) (simp add: h1)
  show ?thesis
    using h0 unfolding reverse_add_column_candidate_rows_def
    by (simp add: algebra_simps)
qed

definition reverse_add_column_list_support_values ::
  "nat \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow>
    nat list \<Rightarrow> nat list \<Rightarrow> nat list" where
  "reverse_add_column_list_support_values i d0 d1 d2 d3 d4 =
    map (\<lambda>row. row ! i)
      (filter reverse_add_column_factor
        (reverse_add_column_candidate_rows d0 d1 d2 d3 d4))"

lemma reverse_add_column_list_support_exact:
  assumes index: "i < 5"
  shows "set (reverse_add_column_list_support_values i d0 d1 d2 d3 d4) =
      inward_may_values
        (reverse_add_column_candidate_domains d0 d1 d2 d3 d4)
        5 reverse_add_column_factor i"
  using index reverse_add_column_candidate_rows_exact[of d0 d1 d2 d3 d4]
  unfolding reverse_add_column_list_support_values_def inward_may_values_def
    inward_supported_def reverse_add_column_candidate_admitted_def
    inward_admitted_def
  by auto

definition reverse_add_column_domains_bounded ::
  "nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow>
    nat list \<Rightarrow> nat list \<Rightarrow> bool" where
  "reverse_add_column_domains_bounded d0 d1 d2 d3 d4 \<longleftrightarrow>
    length d0 \<le> 10 \<and> set d0 \<subseteq> {..<10} \<and>
    length d1 \<le> 10 \<and> set d1 \<subseteq> {..<10} \<and>
    length d2 \<le> 2 \<and> set d2 \<subseteq> {..<2} \<and>
    length d3 \<le> 10 \<and> set d3 \<subseteq> {..<10} \<and>
    length d4 \<le> 2 \<and> set d4 \<subseteq> {..<2}"

definition reverse_add_column_bounded_list_support ::
  "nat \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow>
    nat list \<Rightarrow> nat list \<Rightarrow> nat list option" where
  "reverse_add_column_bounded_list_support i d0 d1 d2 d3 d4 =
    (if i < 5 \<and> reverse_add_column_domains_bounded d0 d1 d2 d3 d4
     then Some (reverse_add_column_list_support_values i d0 d1 d2 d3 d4)
     else None)"

lemma reverse_add_column_bounded_support_is_exact:
  assumes index: "i < 5"
      and bounded: "reverse_add_column_domains_bounded d0 d1 d2 d3 d4"
  shows "set (the (reverse_add_column_bounded_list_support
      i d0 d1 d2 d3 d4)) =
      inward_may_values
        (reverse_add_column_candidate_domains d0 d1 d2 d3 d4)
        5 reverse_add_column_factor i"
  using index bounded reverse_add_column_list_support_exact[OF index]
  unfolding reverse_add_column_bounded_list_support_def
  by simp

definition reverse_add_column_bounded_list_must_value ::
  "nat \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow>
    nat list \<Rightarrow> nat list \<Rightarrow> nat option option" where
  "reverse_add_column_bounded_list_must_value i d0 d1 d2 d3 d4 =
    (case reverse_add_column_bounded_list_support i d0 d1 d2 d3 d4 of
      None \<Rightarrow> None
    | Some values \<Rightarrow> Some (inward_list_must_value values))"

lemma reverse_add_column_bounded_list_must_is_supported:
  assumes index: "i < 5"
      and bounded: "reverse_add_column_domains_bounded d0 d1 d2 d3 d4"
      and read:
        "reverse_add_column_bounded_list_must_value i d0 d1 d2 d3 d4 =
          Some (Some value)"
  shows "inward_may_values
      (reverse_add_column_candidate_domains d0 d1 d2 d3 d4)
      5 reverse_add_column_factor i = {value}"
proof -
  have read_values:
    "inward_list_must_value
      (reverse_add_column_list_support_values i d0 d1 d2 d3 d4) = Some value"
    using read index bounded
    unfolding reverse_add_column_bounded_list_must_value_def
      reverse_add_column_bounded_list_support_def
    by simp
  have list_singleton:
    "set (reverse_add_column_list_support_values i d0 d1 d2 d3 d4) = {value}"
    using inward_list_must_value_exact[of
      "reverse_add_column_list_support_values i d0 d1 d2 d3 d4"]
      read_values by blast
  show ?thesis
    using list_singleton reverse_add_column_list_support_exact[OF index]
    by simp
qed

theorem reverse_add_column_bounded_must_matches_concrete_row:
  assumes index: "i < 5"
      and bounded: "reverse_add_column_domains_bounded d0 d1 d2 d3 d4"
      and admitted:
        "inward_admitted
          (reverse_add_column_candidate_domains d0 d1 d2 d3 d4) 5 row"
      and factor: "reverse_add_column_factor row"
      and read:
        "reverse_add_column_bounded_list_must_value i d0 d1 d2 d3 d4 =
          Some (Some value)"
  shows "value = row ! i"
proof -
  have supported:
    "inward_may_values
      (reverse_add_column_candidate_domains d0 d1 d2 d3 d4)
      5 reverse_add_column_factor i = {value}"
    by (rule reverse_add_column_bounded_list_must_is_supported[OF index bounded read])
  have port: "row ! i \<in> inward_may_values
      (reverse_add_column_candidate_domains d0 d1 d2 d3 d4)
      5 reverse_add_column_factor i"
  proof (rule inward_may_values_contains_model_port)
    show "inward_admitted
        (reverse_add_column_candidate_domains d0 d1 d2 d3 d4) 5 row"
      using admitted .
    show "reverse_add_column_factor row" using factor .
    show "i < 5" using index .
  qed
  show ?thesis using port supported by auto
qed

lemma reverse_add_column_bounded_rows_at_most_4000:
  assumes bounded: "reverse_add_column_domains_bounded d0 d1 d2 d3 d4"
  shows "length (reverse_add_column_candidate_rows d0 d1 d2 d3 d4) \<le> 4000"
proof -
  have d0: "length d0 \<le> 10" and d1: "length d1 \<le> 10"
    and d2: "length d2 \<le> 2" and d3: "length d3 \<le> 10"
    and d4: "length d4 \<le> 2"
    using bounded unfolding reverse_add_column_domains_bounded_def by blast+
  have p01: "length d0 * length d1 \<le> 10 * 10"
    by (rule mult_le_mono[OF d0 d1])
  have p012: "length d0 * length d1 * length d2 \<le> 10 * 10 * 2"
    by (rule mult_le_mono[OF p01 d2])
  have p0123:
    "length d0 * length d1 * length d2 * length d3 \<le> 10 * 10 * 2 * 10"
    by (rule mult_le_mono[OF p012 d3])
  have p01234:
    "length d0 * length d1 * length d2 * length d3 * length d4 \<le> 4000"
    using mult_le_mono[OF p0123 d4] by simp
  show ?thesis
    using p01234 by (simp add: reverse_add_column_candidate_rows_length)
qed

definition reverse_pair_sum_factor :: "nat set \<Rightarrow> nat list \<Rightarrow> bool" where
  "reverse_pair_sum_factor allowed pair \<longleftrightarrow>
    length pair = 2 \<and> pair ! 0 < 10 \<and> pair ! 1 < 10 \<and>
    pair ! 0 + pair ! 1 \<in> allowed"

definition reverse_raw_borrow_factor :: "nat list \<Rightarrow> bool" where
  "reverse_raw_borrow_factor column \<longleftrightarrow>
    length column = 4 \<and> column ! 0 < 10 \<and> column ! 1 < 10 \<and>
    column ! 2 < 2 \<and> column ! 3 < 2 \<and>
    column ! 3 = (if column ! 0 < column ! 1 + column ! 2 then 1 else 0)"

definition reverse_carry_xor_factor :: "nat \<Rightarrow> nat list \<Rightarrow> bool" where
  "reverse_carry_xor_factor xor_value ports \<longleftrightarrow>
    length ports = 2 \<and> xor_value < 2 \<and>
    ports ! 0 < 2 \<and> ports ! 1 < 2 \<and>
    xor_value = (if ports ! 0 = ports ! 1 then 0 else 1)"

fun inward_decimal_value :: "nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "inward_decimal_value [] radix target_residue = target_residue mod radix"
| "inward_decimal_value (input_digit # ds) radix target_residue =
    inward_decimal_value ds radix
      ((10 * target_residue + input_digit) mod radix)"

definition reverse_decimal_residue_factor ::
  "nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> bool" where
  "reverse_decimal_residue_factor radix target_residue ds \<longleftrightarrow>
    2 \<le> radix \<and> target_residue < radix \<and>
    (\<forall>input_digit\<in>set ds. input_digit < 10) \<and>
    inward_decimal_value ds radix 0 = target_residue"

lemma reverse_add_column_factor_carry_is_shared_q19_port:
  assumes column: "reverse_add_column_factor column"
  shows "column ! 4 =
    (if 10 \<le> column ! 0 + column ! 1 + column ! 2 then 1 else 0)"
proof -
  have low: "column ! 3 < 10"
    and carry: "column ! 4 < 2"
    and equation:
      "column ! 0 + column ! 1 + column ! 2 = column ! 3 + 10 * column ! 4"
    using column by (auto simp: reverse_add_column_factor_def)
  show ?thesis
  proof (cases "column ! 4 = 0")
    case True
    have total: "column ! 0 + column ! 1 + column ! 2 < 10"
      using equation low True by presburger
    have no_threshold:
      "\<not> (10 \<le> column ! 0 + column ! 1 + column ! 2)"
      using total by presburger
    show ?thesis using True no_threshold by simp
  next
    case False
    have carry_one: "column ! 4 = 1"
      using carry False by presburger
    have total: "10 \<le> column ! 0 + column ! 1 + column ! 2"
      using equation carry_one by presburger
    show ?thesis using carry_one total by simp
  qed
qed

corollary reverse_add_column_carry_matches_q19_pair_action:
  assumes "a \<le> 9" "b \<le> 9"
  shows "(10 \<le> a + b + reverse_q19_carry_bit incoming) =
    reverse_q19_pair_carry (a + b) incoming"
  using reverse_q19_pair_carry_reset[of "a + b" incoming] assms
  unfolding reverse_q19_carry_bit_def
  by (cases incoming; cases "a + b < 9"; cases "a + b = 9"; simp_all; arith)

definition reverse_add_reflected_column ::
  "nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat list" where
  "reverse_add_reflected_column source target carries i =
    [source ! (length source - Suc i), source ! i, carries ! i,
      target ! (length target - Suc i), carries ! Suc i]"

definition reverse_add_reflected_pair :: "nat list \<Rightarrow> nat \<Rightarrow> nat list" where
  "reverse_add_reflected_pair row i =
    [row ! (length row - Suc i), row ! i]"

lemma reverse_add_reflected_column_is_exact_local_factor:
  assumes source_digit_low: "source ! (length source - Suc i) < 10"
      and source_digit_high: "source ! i < 10"
      and target_digit: "target ! (length target - Suc i) < 10"
      and carry_in: "carries ! i < 2"
      and carry_out: "carries ! Suc i < 2"
      and index_source: "i < length source"
      and index_target: "i < length target"
      and index_carries: "Suc i < length carries"
  shows "reverse_add_column_factor
      (reverse_add_reflected_column source target carries i) \<longleftrightarrow>
    source ! (length source - Suc i) + source ! i + carries ! i =
      target ! (length target - Suc i) + 10 * carries ! Suc i"
  using assms
  unfolding reverse_add_column_factor_def reverse_add_reflected_column_def
  by simp

lemma reverse_add_reflected_pair_is_exact_local_factor:
  assumes low: "row ! (length row - Suc i) < 10"
      and high: "row ! i < 10"
  shows "reverse_pair_sum_factor allowed (reverse_add_reflected_pair row i) \<longleftrightarrow>
    row ! (length row - Suc i) + row ! i \<in> allowed"
  using low high
  unfolding reverse_pair_sum_factor_def reverse_add_reflected_pair_def
  by simp

definition reverse_pair_sum_may_values ::
  "nat set \<Rightarrow> nat set \<Rightarrow> nat set \<Rightarrow> nat set" where
  "reverse_pair_sum_may_values low high allowed =
    {sum. \<exists>a\<in>low. \<exists>b\<in>high. sum = a + b \<and> sum \<in> allowed}"

definition reverse_pair_band_may_values ::
  "nat set \<Rightarrow> nat set \<Rightarrow> nat set \<Rightarrow> nat set \<Rightarrow> bool set" where
  "reverse_pair_band_may_values low high allowed band =
    {inside. \<exists>sum\<in>reverse_pair_sum_may_values low high allowed.
      (sum \<in> band) = inside}"

definition reverse_pair_band_must_value ::
  "nat set \<Rightarrow> nat set \<Rightarrow> nat set \<Rightarrow> nat set \<Rightarrow> bool option" where
  "reverse_pair_band_must_value low high allowed band =
    (let values = reverse_pair_band_may_values low high allowed band in
      if values = {False} then Some False
      else if values = {True} then Some True else None)"

lemma reverse_pair_band_must_value_sound:
  assumes read:
      "reverse_pair_band_must_value low high allowed band = Some inside"
  shows "\<forall>sum\<in>reverse_pair_sum_may_values low high allowed.
      sum \<in> band = inside"
  using read
  unfolding reverse_pair_band_must_value_def reverse_pair_band_may_values_def
  by (auto simp: Let_def split: if_splits)

lemma reverse_pair_sum_may_contains_concrete_pair:
  assumes low: "a \<in> low" and high: "b \<in> high"
      and allowed: "a + b \<in> allowed"
  shows "a + b \<in> reverse_pair_sum_may_values low high allowed"
  using low high allowed unfolding reverse_pair_sum_may_values_def by blast

theorem reverse_pair_band_read_respects_concrete_pair:
  assumes low: "a \<in> low"
      and high: "b \<in> high"
      and allowed: "a + b \<in> allowed"
      and read: "reverse_pair_band_must_value low high allowed band = Some inside"
  shows "a + b \<in> band = inside"
proof -
  have sum: "a + b \<in> reverse_pair_sum_may_values low high allowed"
    by (rule reverse_pair_sum_may_contains_concrete_pair[OF low high allowed])
  show ?thesis
    using sum read reverse_pair_band_must_value_sound by blast
qed

text \<open>The may set consists only of values supported by an admitted row and
the exact factor. A must result is emitted only when this set is a singleton.
Consequently an unresolved port remains unresolved; no fallback digit, carry,
borrow, or period is guessed.\<close>

ML \<open>
  val checked = @{thms inward_factor_filter_preserves_model
    inward_filter_sweep_preserves_model
    inward_filter_rounds_preserve_every_concrete_model
    inward_must_value_is_supported_singleton
    inward_must_value_matches_any_admitted_model
    inward_digit_option_domain_duplicate_idempotent
    inward_list_must_value_exact
    reverse_add_column_candidate_rows_exact
    reverse_add_column_list_support_exact
    reverse_add_column_bounded_support_is_exact
    reverse_add_column_bounded_rows_at_most_4000
    reverse_add_column_bounded_must_matches_concrete_row
    reverse_add_column_factor_carry_is_shared_q19_port
    reverse_add_column_carry_matches_q19_pair_action
    reverse_add_reflected_column_is_exact_local_factor
    reverse_pair_band_must_value_sound
    reverse_pair_band_read_respects_concrete_pair};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Inward constraint soundness depends on an oracle";
\<close>

end
