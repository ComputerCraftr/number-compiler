theory Comma_Source_Unique
  imports Comma_Source_Entry.Comma_Source_Entry
    Comma_Literal_Bridge.Comma_Unique_Path
begin

ML_file "../comma_entry_arithmetic/Proof_Dependency_Audit.ML"

lemma comma_source20_tail_unique:
  "comma_unique_literal_path 412985919 100003 19999999918"
proof -
  obtain rows where rows:
    "comma_indexed_trace 5 (Comma_Entry 1 0 3) rows
      (Comma_Fork_At 2 5) (Comma_Near 1 5 82)"
    "sum_list (map fst rows) = 412985919"
    using comma_source20_indexed_tail by blast
  show ?thesis using comma_source_indexed_unique_path[OF rows(1)] rows(2)
    by (simp add: comma_chart_value_def)
qed

lemma comma_source_fixed_sector_unique:
  assumes source: "comma_sector f p k"
    and exponent: "2 \<le> p"
    and upper: "comma_fixed_iter f n k + 1 < (f + 1) * 10 ^ p"
  shows "comma_unique_literal_path n k (comma_fixed_iter f n k)"
proof -
  have edges: "comma_child (comma_fixed_iter f j k) v \<longleftrightarrow>
      v = comma_fixed_iter f (Suc j) k" if index: "j < n" for j v
  proof -
    let ?x = "comma_fixed_iter f j k"
    let ?u = "comma_fixed_iter f (Suc j) k"
    have jn: "j \<le> n" and sn: "Suc j \<le> n" using index by simp_all
    have x_bound: "?x \<le> comma_fixed_iter f n k"
      using comma_source_fixed_iter_mono[OF jn] .
    have u_bound: "?u \<le> comma_fixed_iter f n k"
      using comma_source_fixed_iter_mono[OF sn] .
    have lower: "f * 10 ^ p \<le> ?x"
      using source comma_source_fixed_iter_mono[of 0 j f k]
      by (simp add: comma_sector_def)
    have sector: "comma_sector f p ?x"
      using source lower x_bound upper by (auto simp: comma_sector_def)
    have sum: "?x + comma_headroom f p ?x = (f + 1) * 10 ^ p"
      using comma_sector_headroom[OF sector] .
    have safe: "10 * (?x mod 10) + f + 1 < comma_headroom f p ?x"
      using sum u_bound upper by (simp; arith)
    have f: "f \<le> 9" using sector by (simp add: comma_sector_def)
    have children: "comma_large_children f p ?x = [?u]"
      using safe f by (auto simp: comma_large_children_def Let_def)
    show ?thesis using comma_large_children_complete[OF sector exponent, of v]
      children by simp
  qed
  show ?thesis
    using comma_unique_literal_path_from_points
      [where point="\<lambda>j. comma_fixed_iter f j k" and n=n, OF edges]
    by simp
qed

lemma comma_source_startup_unique_children:
  "comma_child 20 v \<longleftrightarrow> v = 22"
  "comma_child 22 v \<longleftrightarrow> v = 46"
  "comma_child 46 v \<longleftrightarrow> v = 107"
proof -
  have first: "v = 22" if child: "comma_child 20 v"
  proof -
    obtain e p where raw: "comma_sector e p v"
      "v = 20 + 10 * (20 mod 10) + e" "1 \<le> e" "e \<le> 9"
      using comma_child_witness[OF child] by blast
    have facts: "comma_sector e p v" "v = 20 + e"
      "1 \<le> e" "e \<le> 9" using raw by simp_all
    have bounds: "10 ^ (1::nat) \<le> v" "v < 10 ^ Suc (1::nat)"
      using facts by auto
    have p: "p = 1" using comma_decade_exponent_unique
      [OF comma_sector_decade_bounds[OF facts(1)] bounds] .
    show ?thesis using facts by (simp add: p comma_sector_def; arith)
  qed
  have second: "v = 46" if child: "comma_child 22 v"
  proof -
    obtain e p where raw: "comma_sector e p v"
      "v = 22 + 10 * (22 mod 10) + e" "1 \<le> e" "e \<le> 9"
      using comma_child_witness[OF child] by blast
    have facts: "comma_sector e p v" "v = 42 + e"
      "1 \<le> e" "e \<le> 9" using raw by simp_all
    have bounds: "10 ^ (1::nat) \<le> v" "v < 10 ^ Suc (1::nat)"
      using facts by auto
    have p: "p = 1" using comma_decade_exponent_unique
      [OF comma_sector_decade_bounds[OF facts(1)] bounds] .
    show ?thesis using facts by (simp add: p comma_sector_def; arith)
  qed
  have third: "v = 107" if child: "comma_child 46 v"
  proof -
    obtain e p where raw: "comma_sector e p v"
      "v = 46 + 10 * (46 mod 10) + e" "1 \<le> e" "e \<le> 9"
      using comma_child_witness[OF child] by blast
    have facts: "comma_sector e p v" "v = 106 + e"
      "1 \<le> e" "e \<le> 9" using raw by simp_all
    have bounds: "10 ^ (2::nat) \<le> v" "v < 10 ^ Suc (2::nat)"
      using facts by auto
    have p: "p = 2" using comma_decade_exponent_unique
      [OF comma_sector_decade_bounds[OF facts(1)] bounds] .
    show ?thesis using facts by (simp add: p comma_sector_def; arith)
  qed
  show "comma_child 20 v \<longleftrightarrow> v = 22" using first comma_startup(1) by blast
  show "comma_child 22 v \<longleftrightarrow> v = 46" using second comma_startup(2) by blast
  show "comma_child 46 v \<longleftrightarrow> v = 107" using third comma_startup(3) by blast
qed

lemma comma_source_startup_unique:
  "comma_unique_literal_path 3 20 107"
proof -
  have terminal: "comma_unique_literal_path 0 107 107"
    by (rule comma_unique_literal_path.zero)
  have path: "comma_unique_literal_path (Suc (Suc (Suc 0))) 20 107"
    using comma_unique_literal_path.step
      [OF comma_source_startup_unique_children(1)
        comma_unique_literal_path.step
          [OF comma_source_startup_unique_children(2)
            comma_unique_literal_path.step
              [OF comma_source_startup_unique_children(3) terminal]]] .
  show ?thesis unfolding numeral_3_eq_3 by (rule path)
qed

lemma comma_source_small_sector_unique:
  assumes source: "comma_sector f p k"
    and exponent: "2 \<le> p"
    and upper: "comma_fixed_iter f n k + 1 < (f + 1) * 10 ^ p"
    and children: "comma_large_children f p (comma_fixed_iter f n k) = [target]"
  shows "comma_unique_literal_path (Suc n) k target"
proof -
  have first: "comma_unique_literal_path n k (comma_fixed_iter f n k)"
    using comma_source_fixed_sector_unique[OF source exponent upper] .
  have lower: "f * 10 ^ p \<le> comma_fixed_iter f n k"
    using source comma_source_fixed_iter_mono[of 0 n f k]
    by (simp add: comma_sector_def)
  have sector: "comma_sector f p (comma_fixed_iter f n k)"
    using source lower upper by (auto simp: comma_sector_def)
  have edge: "comma_child (comma_fixed_iter f n k) v \<longleftrightarrow> v = target" for v
    using comma_large_children_complete[OF sector exponent, of v] children by simp
  have last: "comma_unique_literal_path (Suc 0) (comma_fixed_iter f n k) target"
    by (rule comma_unique_literal_path.step[OF edge])
      (rule comma_unique_literal_path.zero)
  show ?thesis using comma_unique_literal_path_append[OF first last] by simp
qed

lemma comma_source20_small_unique_00:
  "comma_unique_literal_path 2 107 260"
proof -
  have endpoint: "comma_fixed_iter 1 1 107 = 178"
    using comma_source_fixed_period_eval
      [where L=10 and f=1 and n=1 and t=0 and j=1
        and k=107]
    by (simp add: comma_period_displacement_def comma_source_sum_numeral)
  have result: "comma_unique_literal_path (Suc 1) 107 260"
    apply (rule comma_source_small_sector_unique[where f=1 and p=2])
    apply (simp_all only: endpoint)
    by (simp_all add: comma_sector_def comma_large_children_def
      comma_headroom_def Let_def)
  show ?thesis using result by (simp add: One_nat_def numeral_2_eq_2 numeral_3_eq_3)
qed

lemma comma_source20_small_unique_01:
  "comma_unique_literal_path 3 260 327"
proof -
  have endpoint: "comma_fixed_iter 2 2 260 = 284"
    using comma_source_fixed_period_eval
      [where L=5 and f=2 and n=2 and t=0 and j=2
        and k=260]
    by (simp add: comma_period_displacement_def comma_source_sum_numeral)
  have result: "comma_unique_literal_path (Suc 2) 260 327"
    apply (rule comma_source_small_sector_unique[where f=2 and p=2])
    apply (simp_all only: endpoint)
    by (simp_all add: comma_sector_def comma_large_children_def
      comma_headroom_def Let_def)
  show ?thesis using result by (simp add: One_nat_def numeral_2_eq_2 numeral_3_eq_3)
qed

lemma comma_source20_small_unique_02:
  "comma_unique_literal_path 1 327 401"
proof -
  have endpoint: "comma_fixed_iter 3 0 327 = 327"
    using comma_source_fixed_period_eval
      [where L=10 and f=3 and n=0 and t=0 and j=0
        and k=327]
    by (simp add: comma_period_displacement_def comma_source_sum_numeral)
  have result: "comma_unique_literal_path (Suc 0) 327 401"
    apply (rule comma_source_small_sector_unique[where f=3 and p=2])
    apply (simp_all only: endpoint)
    by (simp_all add: comma_sector_def comma_large_children_def
      comma_headroom_def Let_def)
  show ?thesis using result by (simp add: One_nat_def numeral_2_eq_2 numeral_3_eq_3)
qed

lemma comma_source20_small_unique_03:
  "comma_unique_literal_path 3 401 564"
proof -
  have endpoint: "comma_fixed_iter 4 2 401 = 469"
    using comma_source_fixed_period_eval
      [where L=5 and f=4 and n=2 and t=0 and j=2
        and k=401]
    by (simp add: comma_period_displacement_def comma_source_sum_numeral)
  have result: "comma_unique_literal_path (Suc 2) 401 564"
    apply (rule comma_source_small_sector_unique[where f=4 and p=2])
    apply (simp_all only: endpoint)
    by (simp_all add: comma_sector_def comma_large_children_def
      comma_headroom_def Let_def)
  show ?thesis using result by (simp add: One_nat_def numeral_2_eq_2 numeral_3_eq_3)
qed

lemma comma_source20_small_unique_04:
  "comma_unique_literal_path 1 564 610"
proof -
  have endpoint: "comma_fixed_iter 5 0 564 = 564"
    using comma_source_fixed_period_eval
      [where L=2 and f=5 and n=0 and t=0 and j=0
        and k=564]
    by (simp add: comma_period_displacement_def comma_source_sum_numeral)
  have result: "comma_unique_literal_path (Suc 0) 564 610"
    apply (rule comma_source_small_sector_unique[where f=5 and p=2])
    apply (simp_all only: endpoint)
    by (simp_all add: comma_sector_def comma_large_children_def
      comma_headroom_def Let_def)
  show ?thesis using result by (simp add: One_nat_def numeral_2_eq_2 numeral_3_eq_3)
qed

lemma comma_source20_small_unique_05:
  "comma_unique_literal_path 3 610 709"
proof -
  have endpoint: "comma_fixed_iter 6 2 610 = 682"
    using comma_source_fixed_period_eval
      [where L=5 and f=6 and n=2 and t=0 and j=2
        and k=610]
    by (simp add: comma_period_displacement_def comma_source_sum_numeral)
  have result: "comma_unique_literal_path (Suc 2) 610 709"
    apply (rule comma_source_small_sector_unique[where f=6 and p=2])
    apply (simp_all only: endpoint)
    by (simp_all add: comma_sector_def comma_large_children_def
      comma_headroom_def Let_def)
  show ?thesis using result by (simp add: One_nat_def numeral_2_eq_2 numeral_3_eq_3)
qed

lemma comma_source20_small_unique_06:
  "comma_unique_literal_path 1 709 807"
proof -
  have endpoint: "comma_fixed_iter 7 0 709 = 709"
    using comma_source_fixed_period_eval
      [where L=10 and f=7 and n=0 and t=0 and j=0
        and k=709]
    by (simp add: comma_period_displacement_def comma_source_sum_numeral)
  have result: "comma_unique_literal_path (Suc 0) 709 807"
    apply (rule comma_source_small_sector_unique[where f=7 and p=2])
    apply (simp_all only: endpoint)
    by (simp_all add: comma_sector_def comma_large_children_def
      comma_headroom_def Let_def)
  show ?thesis using result by (simp add: One_nat_def numeral_2_eq_2 numeral_3_eq_3)
qed

lemma comma_source20_small_unique_07:
  "comma_unique_literal_path 2 807 944"
proof -
  have endpoint: "comma_fixed_iter 8 1 807 = 885"
    using comma_source_fixed_period_eval
      [where L=5 and f=8 and n=1 and t=0 and j=1
        and k=807]
    by (simp add: comma_period_displacement_def comma_source_sum_numeral)
  have result: "comma_unique_literal_path (Suc 1) 807 944"
    apply (rule comma_source_small_sector_unique[where f=8 and p=2])
    apply (simp_all only: endpoint)
    by (simp_all add: comma_sector_def comma_large_children_def
      comma_headroom_def Let_def)
  show ?thesis using result by (simp add: One_nat_def numeral_2_eq_2 numeral_3_eq_3)
qed

lemma comma_source20_small_unique_08:
  "comma_unique_literal_path 2 944 1024"
proof -
  have endpoint: "comma_fixed_iter 9 1 944 = 993"
    using comma_source_fixed_period_eval
      [where L=10 and f=9 and n=1 and t=0 and j=1
        and k=944]
    by (simp add: comma_period_displacement_def comma_source_sum_numeral)
  have result: "comma_unique_literal_path (Suc 1) 944 1024"
    apply (rule comma_source_small_sector_unique[where f=9 and p=2])
    apply (simp_all only: endpoint)
    by (simp_all add: comma_sector_def comma_large_children_def
      comma_headroom_def Let_def)
  show ?thesis using result by (simp add: One_nat_def numeral_2_eq_2 numeral_3_eq_3)
qed

lemma comma_source20_small_unique_09:
  "comma_unique_literal_path 22 1024 2037"
proof -
  have endpoint: "comma_fixed_iter 1 21 1024 = 1985"
    using comma_source_fixed_period_eval
      [where L=10 and f=1 and n=21 and t=2 and j=1
        and k=1024]
    by (simp add: comma_period_displacement_def comma_source_sum_numeral)
  have result: "comma_unique_literal_path (Suc 21) 1024 2037"
    apply (rule comma_source_small_sector_unique[where f=1 and p=3])
    apply (simp_all only: endpoint)
    by (simp_all add: comma_sector_def comma_large_children_def
      comma_headroom_def Let_def)
  show ?thesis using result by (simp add: One_nat_def numeral_2_eq_2 numeral_3_eq_3)
qed

lemma comma_source20_small_unique_10:
  "comma_unique_literal_path 19 2037 3026"
proof -
  have endpoint: "comma_fixed_iter 2 18 2037 = 2993"
    using comma_source_fixed_period_eval
      [where L=5 and f=2 and n=18 and t=3 and j=3
        and k=2037]
    by (simp add: comma_period_displacement_def comma_source_sum_numeral)
  have result: "comma_unique_literal_path (Suc 18) 2037 3026"
    apply (rule comma_source_small_sector_unique[where f=2 and p=3])
    apply (simp_all only: endpoint)
    by (simp_all add: comma_sector_def comma_large_children_def
      comma_headroom_def Let_def)
  show ?thesis using result by (simp add: One_nat_def numeral_2_eq_2 numeral_3_eq_3)
qed

lemma comma_source20_small_unique_11:
  "comma_unique_literal_path 21 3026 4050"
proof -
  have endpoint: "comma_fixed_iter 3 20 3026 = 3986"
    using comma_source_fixed_period_eval
      [where L=10 and f=3 and n=20 and t=2 and j=0
        and k=3026]
    by (simp add: comma_period_displacement_def comma_source_sum_numeral)
  have result: "comma_unique_literal_path (Suc 20) 3026 4050"
    apply (rule comma_source_small_sector_unique[where f=3 and p=3])
    apply (simp_all only: endpoint)
    by (simp_all add: comma_sector_def comma_large_children_def
      comma_headroom_def Let_def)
  show ?thesis using result by (simp add: One_nat_def numeral_2_eq_2 numeral_3_eq_3)
qed

lemma comma_source20_small_unique_12:
  "comma_unique_literal_path 23 4050 5063"
proof -
  have endpoint: "comma_fixed_iter 4 22 4050 = 4978"
    using comma_source_fixed_period_eval
      [where L=5 and f=4 and n=22 and t=4 and j=2
        and k=4050]
    by (simp add: comma_period_displacement_def comma_source_sum_numeral)
  have result: "comma_unique_literal_path (Suc 22) 4050 5063"
    apply (rule comma_source_small_sector_unique[where f=4 and p=3])
    apply (simp_all only: endpoint)
    by (simp_all add: comma_sector_def comma_large_children_def
      comma_headroom_def Let_def)
  show ?thesis using result by (simp add: One_nat_def numeral_2_eq_2 numeral_3_eq_3)
qed

lemma comma_source20_small_unique_13:
  "comma_unique_literal_path 16 5063 6024"
proof -
  have endpoint: "comma_fixed_iter 5 15 5063 = 5938"
    using comma_source_fixed_period_eval
      [where L=2 and f=5 and n=15 and t=7 and j=1
        and k=5063]
    by (simp add: comma_period_displacement_def comma_source_sum_numeral)
  have result: "comma_unique_literal_path (Suc 15) 5063 6024"
    apply (rule comma_source_small_sector_unique[where f=5 and p=3])
    apply (simp_all only: endpoint)
    by (simp_all add: comma_sector_def comma_large_children_def
      comma_headroom_def Let_def)
  show ?thesis using result by (simp add: One_nat_def numeral_2_eq_2 numeral_3_eq_3)
qed

lemma comma_source20_small_unique_14:
  "comma_unique_literal_path 23 6024 7063"
proof -
  have endpoint: "comma_fixed_iter 6 22 6024 = 6996"
    using comma_source_fixed_period_eval
      [where L=5 and f=6 and n=22 and t=4 and j=2
        and k=6024]
    by (simp add: comma_period_displacement_def comma_source_sum_numeral)
  have result: "comma_unique_literal_path (Suc 22) 6024 7063"
    apply (rule comma_source_small_sector_unique[where f=6 and p=3])
    apply (simp_all only: endpoint)
    by (simp_all add: comma_sector_def comma_large_children_def
      comma_headroom_def Let_def)
  show ?thesis using result by (simp add: One_nat_def numeral_2_eq_2 numeral_3_eq_3)
qed

lemma comma_source20_small_unique_15:
  "comma_unique_literal_path 19 7063 8037"
proof -
  have endpoint: "comma_fixed_iter 7 18 7063 = 7939"
    using comma_source_fixed_period_eval
      [where L=10 and f=7 and n=18 and t=1 and j=8
        and k=7063]
    by (simp add: comma_period_displacement_def comma_source_sum_numeral)
  have result: "comma_unique_literal_path (Suc 18) 7063 8037"
    apply (rule comma_source_small_sector_unique[where f=7 and p=3])
    apply (simp_all only: endpoint)
    by (simp_all add: comma_sector_def comma_large_children_def
      comma_headroom_def Let_def)
  show ?thesis using result by (simp add: One_nat_def numeral_2_eq_2 numeral_3_eq_3)
qed

lemma comma_source20_small_unique_16:
  "comma_unique_literal_path 17 8037 9044"
proof -
  have endpoint: "comma_fixed_iter 8 16 8037 = 8985"
    using comma_source_fixed_period_eval
      [where L=5 and f=8 and n=16 and t=3 and j=1
        and k=8037]
    by (simp add: comma_period_displacement_def comma_source_sum_numeral)
  have result: "comma_unique_literal_path (Suc 16) 8037 9044"
    apply (rule comma_source_small_sector_unique[where f=8 and p=3])
    apply (simp_all only: endpoint)
    by (simp_all add: comma_sector_def comma_large_children_def
      comma_headroom_def Let_def)
  show ?thesis using result by (simp add: One_nat_def numeral_2_eq_2 numeral_3_eq_3)
qed

lemma comma_source20_small_unique_17:
  "comma_unique_literal_path 19 9044 10057"
proof -
  have endpoint: "comma_fixed_iter 9 18 9044 = 9996"
    using comma_source_fixed_period_eval
      [where L=10 and f=9 and n=18 and t=1 and j=8
        and k=9044]
    by (simp add: comma_period_displacement_def comma_source_sum_numeral)
  have result: "comma_unique_literal_path (Suc 18) 9044 10057"
    apply (rule comma_source_small_sector_unique[where f=9 and p=3])
    apply (simp_all only: endpoint)
    by (simp_all add: comma_sector_def comma_large_children_def
      comma_headroom_def Let_def)
  show ?thesis using result by (simp add: One_nat_def numeral_2_eq_2 numeral_3_eq_3)
qed

lemma comma_source20_small_unique_18:
  "comma_unique_literal_path 217 10057 20025"
proof -
  have endpoint: "comma_fixed_iter 1 216 10057 = 19993"
    using comma_source_fixed_period_eval
      [where L=10 and f=1 and n=216 and t=21 and j=6
        and k=10057]
    by (simp add: comma_period_displacement_def comma_source_sum_numeral)
  have result: "comma_unique_literal_path (Suc 216) 10057 20025"
    apply (rule comma_source_small_sector_unique[where f=1 and p=4])
    apply (simp_all only: endpoint)
    by (simp_all add: comma_sector_def comma_large_children_def
      comma_headroom_def Let_def)
  show ?thesis using result by (simp add: One_nat_def numeral_2_eq_2 numeral_3_eq_3)
qed

lemma comma_source20_small_unique_19:
  "comma_unique_literal_path 192 20025 30030"
proof -
  have endpoint: "comma_fixed_iter 2 191 20025 = 29957"
    using comma_source_fixed_period_eval
      [where L=5 and f=2 and n=191 and t=38 and j=1
        and k=20025]
    by (simp add: comma_period_displacement_def comma_source_sum_numeral)
  have result: "comma_unique_literal_path (Suc 191) 20025 30030"
    apply (rule comma_source_small_sector_unique[where f=2 and p=4])
    apply (simp_all only: endpoint)
    by (simp_all add: comma_sector_def comma_large_children_def
      comma_headroom_def Let_def)
  show ?thesis using result by (simp add: One_nat_def numeral_2_eq_2 numeral_3_eq_3)
qed

lemma comma_source20_small_unique_20:
  "comma_unique_literal_path 209 30030 40038"
proof -
  have endpoint: "comma_fixed_iter 3 208 30030 = 39994"
    using comma_source_fixed_period_eval
      [where L=10 and f=3 and n=208 and t=20 and j=8
        and k=30030]
    by (simp add: comma_period_displacement_def comma_source_sum_numeral)
  have result: "comma_unique_literal_path (Suc 208) 30030 40038"
    apply (rule comma_source_small_sector_unique[where f=3 and p=4])
    apply (simp_all only: endpoint)
    by (simp_all add: comma_sector_def comma_large_children_def
      comma_headroom_def Let_def)
  show ?thesis using result by (simp add: One_nat_def numeral_2_eq_2 numeral_3_eq_3)
qed

lemma comma_source20_small_unique_21:
  "comma_unique_literal_path 226 40038 50023"
proof -
  have endpoint: "comma_fixed_iter 4 225 40038 = 49938"
    using comma_source_fixed_period_eval
      [where L=5 and f=4 and n=225 and t=45 and j=0
        and k=40038]
    by (simp add: comma_period_displacement_def comma_source_sum_numeral)
  have result: "comma_unique_literal_path (Suc 225) 40038 50023"
    apply (rule comma_source_small_sector_unique[where f=4 and p=4])
    apply (simp_all only: endpoint)
    by (simp_all add: comma_sector_def comma_large_children_def
      comma_headroom_def Let_def)
  show ?thesis using result by (simp add: One_nat_def numeral_2_eq_2 numeral_3_eq_3)
qed

lemma comma_source20_small_unique_22:
  "comma_unique_literal_path 167 50023 60019"
proof -
  have endpoint: "comma_fixed_iter 5 166 50023 = 59983"
    using comma_source_fixed_period_eval
      [where L=2 and f=5 and n=166 and t=83 and j=0
        and k=50023]
    by (simp add: comma_period_displacement_def comma_source_sum_numeral)
  have result: "comma_unique_literal_path (Suc 166) 50023 60019"
    apply (rule comma_source_small_sector_unique[where f=5 and p=4])
    apply (simp_all only: endpoint)
    by (simp_all add: comma_sector_def comma_large_children_def
      comma_headroom_def Let_def)
  show ?thesis using result by (simp add: One_nat_def numeral_2_eq_2 numeral_3_eq_3)
qed

lemma comma_source20_small_unique_23:
  "comma_unique_literal_path 179 60019 70064"
proof -
  have endpoint: "comma_fixed_iter 6 178 60019 = 69987"
    using comma_source_fixed_period_eval
      [where L=5 and f=6 and n=178 and t=35 and j=3
        and k=60019]
    by (simp add: comma_period_displacement_def comma_source_sum_numeral)
  have result: "comma_unique_literal_path (Suc 178) 60019 70064"
    apply (rule comma_source_small_sector_unique[where f=6 and p=4])
    apply (simp_all only: endpoint)
    by (simp_all add: comma_sector_def comma_large_children_def
      comma_headroom_def Let_def)
  show ?thesis using result by (simp add: One_nat_def numeral_2_eq_2 numeral_3_eq_3)
qed

lemma comma_source20_small_unique_24:
  "comma_unique_literal_path 192 70064 80009"
proof -
  have endpoint: "comma_fixed_iter 7 191 70064 = 79991"
    using comma_source_fixed_period_eval
      [where L=10 and f=7 and n=191 and t=19 and j=1
        and k=70064]
    by (simp add: comma_period_displacement_def comma_source_sum_numeral)
  have result: "comma_unique_literal_path (Suc 191) 70064 80009"
    apply (rule comma_source_small_sector_unique[where f=7 and p=4])
    apply (simp_all only: endpoint)
    by (simp_all add: comma_sector_def comma_large_children_def
      comma_headroom_def Let_def)
  show ?thesis using result by (simp add: One_nat_def numeral_2_eq_2 numeral_3_eq_3)
qed

lemma comma_source20_small_unique_25:
  "comma_unique_literal_path 172 80009 90046"
proof -
  have endpoint: "comma_fixed_iter 8 171 80009 = 89967"
    using comma_source_fixed_period_eval
      [where L=5 and f=8 and n=171 and t=34 and j=1
        and k=80009]
    by (simp add: comma_period_displacement_def comma_source_sum_numeral)
  have result: "comma_unique_literal_path (Suc 171) 80009 90046"
    apply (rule comma_source_small_sector_unique[where f=8 and p=4])
    apply (simp_all only: endpoint)
    by (simp_all add: comma_sector_def comma_large_children_def
      comma_headroom_def Let_def)
  show ?thesis using result by (simp add: One_nat_def numeral_2_eq_2 numeral_3_eq_3)
qed

lemma comma_source20_small_unique_26:
  "comma_unique_literal_path 185 90046 100003"
proof -
  have endpoint: "comma_fixed_iter 9 184 90046 = 99982"
    using comma_source_fixed_period_eval
      [where L=10 and f=9 and n=184 and t=18 and j=4
        and k=90046]
    by (simp add: comma_period_displacement_def comma_source_sum_numeral)
  have result: "comma_unique_literal_path (Suc 184) 90046 100003"
    apply (rule comma_source_small_sector_unique[where f=9 and p=4])
    apply (simp_all only: endpoint)
    by (simp_all add: comma_sector_def comma_large_children_def
      comma_headroom_def Let_def)
  show ?thesis using result by (simp add: One_nat_def numeral_2_eq_2 numeral_3_eq_3)
qed

lemma comma_source20_to_p5_unique:
  "comma_unique_literal_path 1939 20 100003"
proof -
  have joined_00: "comma_unique_literal_path 5 20 260"
    using comma_unique_literal_path_append[OF comma_source_startup_unique
      comma_source20_small_unique_00] by simp
  have joined_01: "comma_unique_literal_path 8 20 327"
    using comma_unique_literal_path_append[OF joined_00
      comma_source20_small_unique_01] by simp
  have joined_02: "comma_unique_literal_path 9 20 401"
    using comma_unique_literal_path_append[OF joined_01
      comma_source20_small_unique_02] by simp
  have joined_03: "comma_unique_literal_path 12 20 564"
    using comma_unique_literal_path_append[OF joined_02
      comma_source20_small_unique_03] by simp
  have joined_04: "comma_unique_literal_path 13 20 610"
    using comma_unique_literal_path_append[OF joined_03
      comma_source20_small_unique_04] by simp
  have joined_05: "comma_unique_literal_path 16 20 709"
    using comma_unique_literal_path_append[OF joined_04
      comma_source20_small_unique_05] by simp
  have joined_06: "comma_unique_literal_path 17 20 807"
    using comma_unique_literal_path_append[OF joined_05
      comma_source20_small_unique_06] by simp
  have joined_07: "comma_unique_literal_path 19 20 944"
    using comma_unique_literal_path_append[OF joined_06
      comma_source20_small_unique_07] by simp
  have joined_08: "comma_unique_literal_path 21 20 1024"
    using comma_unique_literal_path_append[OF joined_07
      comma_source20_small_unique_08] by simp
  have joined_09: "comma_unique_literal_path 43 20 2037"
    using comma_unique_literal_path_append[OF joined_08
      comma_source20_small_unique_09] by simp
  have joined_10: "comma_unique_literal_path 62 20 3026"
    using comma_unique_literal_path_append[OF joined_09
      comma_source20_small_unique_10] by simp
  have joined_11: "comma_unique_literal_path 83 20 4050"
    using comma_unique_literal_path_append[OF joined_10
      comma_source20_small_unique_11] by simp
  have joined_12: "comma_unique_literal_path 106 20 5063"
    using comma_unique_literal_path_append[OF joined_11
      comma_source20_small_unique_12] by simp
  have joined_13: "comma_unique_literal_path 122 20 6024"
    using comma_unique_literal_path_append[OF joined_12
      comma_source20_small_unique_13] by simp
  have joined_14: "comma_unique_literal_path 145 20 7063"
    using comma_unique_literal_path_append[OF joined_13
      comma_source20_small_unique_14] by simp
  have joined_15: "comma_unique_literal_path 164 20 8037"
    using comma_unique_literal_path_append[OF joined_14
      comma_source20_small_unique_15] by simp
  have joined_16: "comma_unique_literal_path 181 20 9044"
    using comma_unique_literal_path_append[OF joined_15
      comma_source20_small_unique_16] by simp
  have joined_17: "comma_unique_literal_path 200 20 10057"
    using comma_unique_literal_path_append[OF joined_16
      comma_source20_small_unique_17] by simp
  have joined_18: "comma_unique_literal_path 417 20 20025"
    using comma_unique_literal_path_append[OF joined_17
      comma_source20_small_unique_18] by simp
  have joined_19: "comma_unique_literal_path 609 20 30030"
    using comma_unique_literal_path_append[OF joined_18
      comma_source20_small_unique_19] by simp
  have joined_20: "comma_unique_literal_path 818 20 40038"
    using comma_unique_literal_path_append[OF joined_19
      comma_source20_small_unique_20] by simp
  have joined_21: "comma_unique_literal_path 1044 20 50023"
    using comma_unique_literal_path_append[OF joined_20
      comma_source20_small_unique_21] by simp
  have joined_22: "comma_unique_literal_path 1211 20 60019"
    using comma_unique_literal_path_append[OF joined_21
      comma_source20_small_unique_22] by simp
  have joined_23: "comma_unique_literal_path 1390 20 70064"
    using comma_unique_literal_path_append[OF joined_22
      comma_source20_small_unique_23] by simp
  have joined_24: "comma_unique_literal_path 1582 20 80009"
    using comma_unique_literal_path_append[OF joined_23
      comma_source20_small_unique_24] by simp
  have joined_25: "comma_unique_literal_path 1754 20 90046"
    using comma_unique_literal_path_append[OF joined_24
      comma_source20_small_unique_25] by simp
  have joined_26: "comma_unique_literal_path 1939 20 100003"
    using comma_unique_literal_path_append[OF joined_25
      comma_source20_small_unique_26] by simp
  show ?thesis using joined_26 .
qed

theorem comma_source20_to_fork_unique:
  "comma_unique_literal_path 412987858 20 19999999918"
  using comma_unique_literal_path_append[OF comma_source20_to_p5_unique
    comma_source20_tail_unique] by simp

corollary comma_source20_fork_endpoint_unique:
  assumes "comma_literal_path 412987858 20 target"
  shows "target = 19999999918"
  using comma_unique_literal_path_endpoint[OF comma_source20_to_fork_unique assms] .

ML \<open>
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Source-20 exact entry and unique prelude"
    @{thms comma_source20_to_fork comma_source20_to_fork_unique
      comma_source20_fork_endpoint_unique};
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_unique_literal_path_append comma_unique_literal_path_literal
      comma_unique_literal_path_endpoint comma_unique_literal_path_from_points
      comma_source_chart_step_unique comma_source_chart_unique_path
      comma_source_indexed_unique_path comma_source20_tail_unique
      comma_source_fixed_sector_unique comma_source_startup_unique_children
      comma_source_startup_unique comma_source_small_sector_unique
      comma_source20_to_p5_unique comma_source20_to_fork_unique
      comma_source20_fork_endpoint_unique})
    then () else error "Comma unique-prefix proof depends on an oracle";
\<close>

end
