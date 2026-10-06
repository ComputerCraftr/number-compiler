theory Comma_Source_Entry
  imports Comma_Source_Entry_Witness.Comma_Source_Entry_Witness
begin

text \<open>The source-20 entry obligations use the literal child rule and the
canonical weighted chart.  No scalar macro or forest session is imported.
The finite small-exponent prefix uses the existing fixed-phase arithmetic;
its concrete endpoints are proof data, not a second successor engine.\<close>

lemma comma_source_fixed_iter_mono:
  assumes "j \<le> n"
  shows "comma_fixed_iter f j k \<le> comma_fixed_iter f n k"
  using assms
proof (induction n arbitrary: j)
  case 0
  then show ?case by simp
next
  case (Suc n)
  show ?case
  proof (cases "j = Suc n")
    case True
    then show ?thesis by simp
  next
    case False
    then have j: "j \<le> n" using Suc.prems by arith
    have "comma_fixed_iter f j k \<le> comma_fixed_iter f n k"
      using Suc.IH[OF j] .
    also have "... \<le> comma_fixed_iter f (Suc n) k"
      by simp
    finally show ?thesis .
  qed
qed

lemma comma_source_fixed_sector_path:
  assumes source: "comma_sector f p k"
    and upper: "comma_fixed_iter f n k < (f + 1) * 10 ^ p"
  shows "comma_literal_path n k (comma_fixed_iter f n k)"
proof -
  have edge: "comma_child (comma_fixed_iter f j k)
      (comma_fixed_iter f (Suc j) k)" if j: "j < n" for j
  proof -
    have bound: "comma_fixed_iter f (Suc j) k \<le> comma_fixed_iter f n k"
      using comma_source_fixed_iter_mono[of "Suc j" n f k] j by simp
    have lower: "f * 10 ^ p \<le> comma_fixed_iter f (Suc j) k"
      using source comma_source_fixed_iter_mono[of 0 "Suc j" f k]
      by (simp add: comma_sector_def)
    have sector: "comma_sector f p (comma_fixed_iter f (Suc j) k)"
      using source lower bound upper
      by (auto simp: comma_sector_def)
    show ?thesis
      unfolding comma_child_def
      apply (rule exI[where x=f], rule exI[where x=p])
      using sector by simp
  qed
  show ?thesis
    using comma_fixed_iter_literal_path[of n f k] edge by blast
qed

lemma comma_source_fixed_period_eval:
  assumes close: "10 dvd L * f"
    and split: "n = t * L + j"
  shows "comma_fixed_iter f n k =
    k + t * comma_period_displacement f (k mod 10) L +
      comma_period_displacement f (k mod 10) j"
  using comma_period_displacement_repeated[OF close,
      of "k mod 10" t j] split
  by (simp add: comma_fixed_iter_displacement)

lemma comma_source_sum_numeral:
  fixes f :: "nat \<Rightarrow> nat"
  shows "(\<Sum>j< numeral n. f j) =
    (\<Sum>j< pred_numeral n. f j) + f (pred_numeral n)"
  by (subst numeral_eq_Suc, rule sum.lessThan_Suc)

lemma comma_source20_startup:
  "comma_literal_path 3 20 107"
proof -
  have terminal: "comma_literal_path 0 107 107"
    by (rule comma_literal_path.zero)
  have path: "comma_literal_path (Suc (Suc (Suc 0))) 20 107"
    using comma_literal_path.step[OF comma_startup(1)
      comma_literal_path.step[OF comma_startup(2)
        comma_literal_path.step[OF comma_startup(3) terminal]]] .
  show ?thesis unfolding numeral_3_eq_3 by (rule path)
qed

lemma comma_source20_small_sector_00:
  "comma_literal_path 2 107 260"
proof -
  have source: "comma_sector 1 2 107"
    by (simp add: comma_sector_def)
  have endpoint: "comma_fixed_iter 1 1 107 = 178"
    using comma_source_fixed_period_eval
      [where L=10 and f=1 and n=1 and t=0 and j=1
        and k=107]
    by (simp add: comma_period_displacement_def comma_source_sum_numeral)
  have upper: "comma_fixed_iter 1 1 107 < (1 + 1) * 10 ^ 2"
    using endpoint by simp
  have interior: "comma_literal_path 1 107 178"
    using comma_source_fixed_sector_path[OF source upper] endpoint
    by simp
  have crossing: "comma_child 178 260"
    unfolding comma_child_def
    by (rule exI[where x=2], rule exI[where x=2],
        simp add: comma_sector_def)
  show ?thesis using comma_literal_path_snoc[OF interior crossing]
    by (simp add: One_nat_def numeral_2_eq_2 numeral_3_eq_3)
qed

lemma comma_source20_small_sector_01:
  "comma_literal_path 3 260 327"
proof -
  have source: "comma_sector 2 2 260"
    by (simp add: comma_sector_def)
  have endpoint: "comma_fixed_iter 2 2 260 = 284"
    using comma_source_fixed_period_eval
      [where L=5 and f=2 and n=2 and t=0 and j=2
        and k=260]
    by (simp add: comma_period_displacement_def comma_source_sum_numeral)
  have upper: "comma_fixed_iter 2 2 260 < (2 + 1) * 10 ^ 2"
    using endpoint by simp
  have interior: "comma_literal_path 2 260 284"
    using comma_source_fixed_sector_path[OF source upper] endpoint
    by simp
  have crossing: "comma_child 284 327"
    unfolding comma_child_def
    by (rule exI[where x=3], rule exI[where x=2],
        simp add: comma_sector_def)
  show ?thesis using comma_literal_path_snoc[OF interior crossing]
    by (simp add: One_nat_def numeral_2_eq_2 numeral_3_eq_3)
qed

lemma comma_source20_small_sector_02:
  "comma_literal_path 1 327 401"
proof -
  have source: "comma_sector 3 2 327"
    by (simp add: comma_sector_def)
  have endpoint: "comma_fixed_iter 3 0 327 = 327"
    using comma_source_fixed_period_eval
      [where L=10 and f=3 and n=0 and t=0 and j=0
        and k=327]
    by (simp add: comma_period_displacement_def comma_source_sum_numeral)
  have upper: "comma_fixed_iter 3 0 327 < (3 + 1) * 10 ^ 2"
    using endpoint by simp
  have interior: "comma_literal_path 0 327 327"
    using comma_source_fixed_sector_path[OF source upper] endpoint
    by simp
  have crossing: "comma_child 327 401"
    unfolding comma_child_def
    by (rule exI[where x=4], rule exI[where x=2],
        simp add: comma_sector_def)
  show ?thesis using comma_literal_path_snoc[OF interior crossing]
    by (simp add: One_nat_def numeral_2_eq_2 numeral_3_eq_3)
qed

lemma comma_source20_small_sector_03:
  "comma_literal_path 3 401 564"
proof -
  have source: "comma_sector 4 2 401"
    by (simp add: comma_sector_def)
  have endpoint: "comma_fixed_iter 4 2 401 = 469"
    using comma_source_fixed_period_eval
      [where L=5 and f=4 and n=2 and t=0 and j=2
        and k=401]
    by (simp add: comma_period_displacement_def comma_source_sum_numeral)
  have upper: "comma_fixed_iter 4 2 401 < (4 + 1) * 10 ^ 2"
    using endpoint by simp
  have interior: "comma_literal_path 2 401 469"
    using comma_source_fixed_sector_path[OF source upper] endpoint
    by simp
  have crossing: "comma_child 469 564"
    unfolding comma_child_def
    by (rule exI[where x=5], rule exI[where x=2],
        simp add: comma_sector_def)
  show ?thesis using comma_literal_path_snoc[OF interior crossing]
    by (simp add: One_nat_def numeral_2_eq_2 numeral_3_eq_3)
qed

lemma comma_source20_small_sector_04:
  "comma_literal_path 1 564 610"
proof -
  have source: "comma_sector 5 2 564"
    by (simp add: comma_sector_def)
  have endpoint: "comma_fixed_iter 5 0 564 = 564"
    using comma_source_fixed_period_eval
      [where L=2 and f=5 and n=0 and t=0 and j=0
        and k=564]
    by (simp add: comma_period_displacement_def comma_source_sum_numeral)
  have upper: "comma_fixed_iter 5 0 564 < (5 + 1) * 10 ^ 2"
    using endpoint by simp
  have interior: "comma_literal_path 0 564 564"
    using comma_source_fixed_sector_path[OF source upper] endpoint
    by simp
  have crossing: "comma_child 564 610"
    unfolding comma_child_def
    by (rule exI[where x=6], rule exI[where x=2],
        simp add: comma_sector_def)
  show ?thesis using comma_literal_path_snoc[OF interior crossing]
    by (simp add: One_nat_def numeral_2_eq_2 numeral_3_eq_3)
qed

lemma comma_source20_small_sector_05:
  "comma_literal_path 3 610 709"
proof -
  have source: "comma_sector 6 2 610"
    by (simp add: comma_sector_def)
  have endpoint: "comma_fixed_iter 6 2 610 = 682"
    using comma_source_fixed_period_eval
      [where L=5 and f=6 and n=2 and t=0 and j=2
        and k=610]
    by (simp add: comma_period_displacement_def comma_source_sum_numeral)
  have upper: "comma_fixed_iter 6 2 610 < (6 + 1) * 10 ^ 2"
    using endpoint by simp
  have interior: "comma_literal_path 2 610 682"
    using comma_source_fixed_sector_path[OF source upper] endpoint
    by simp
  have crossing: "comma_child 682 709"
    unfolding comma_child_def
    by (rule exI[where x=7], rule exI[where x=2],
        simp add: comma_sector_def)
  show ?thesis using comma_literal_path_snoc[OF interior crossing]
    by (simp add: One_nat_def numeral_2_eq_2 numeral_3_eq_3)
qed

lemma comma_source20_small_sector_06:
  "comma_literal_path 1 709 807"
proof -
  have source: "comma_sector 7 2 709"
    by (simp add: comma_sector_def)
  have endpoint: "comma_fixed_iter 7 0 709 = 709"
    using comma_source_fixed_period_eval
      [where L=10 and f=7 and n=0 and t=0 and j=0
        and k=709]
    by (simp add: comma_period_displacement_def comma_source_sum_numeral)
  have upper: "comma_fixed_iter 7 0 709 < (7 + 1) * 10 ^ 2"
    using endpoint by simp
  have interior: "comma_literal_path 0 709 709"
    using comma_source_fixed_sector_path[OF source upper] endpoint
    by simp
  have crossing: "comma_child 709 807"
    unfolding comma_child_def
    by (rule exI[where x=8], rule exI[where x=2],
        simp add: comma_sector_def)
  show ?thesis using comma_literal_path_snoc[OF interior crossing]
    by (simp add: One_nat_def numeral_2_eq_2 numeral_3_eq_3)
qed

lemma comma_source20_small_sector_07:
  "comma_literal_path 2 807 944"
proof -
  have source: "comma_sector 8 2 807"
    by (simp add: comma_sector_def)
  have endpoint: "comma_fixed_iter 8 1 807 = 885"
    using comma_source_fixed_period_eval
      [where L=5 and f=8 and n=1 and t=0 and j=1
        and k=807]
    by (simp add: comma_period_displacement_def comma_source_sum_numeral)
  have upper: "comma_fixed_iter 8 1 807 < (8 + 1) * 10 ^ 2"
    using endpoint by simp
  have interior: "comma_literal_path 1 807 885"
    using comma_source_fixed_sector_path[OF source upper] endpoint
    by simp
  have crossing: "comma_child 885 944"
    unfolding comma_child_def
    by (rule exI[where x=9], rule exI[where x=2],
        simp add: comma_sector_def)
  show ?thesis using comma_literal_path_snoc[OF interior crossing]
    by (simp add: One_nat_def numeral_2_eq_2 numeral_3_eq_3)
qed

lemma comma_source20_small_sector_08:
  "comma_literal_path 2 944 1024"
proof -
  have source: "comma_sector 9 2 944"
    by (simp add: comma_sector_def)
  have endpoint: "comma_fixed_iter 9 1 944 = 993"
    using comma_source_fixed_period_eval
      [where L=10 and f=9 and n=1 and t=0 and j=1
        and k=944]
    by (simp add: comma_period_displacement_def comma_source_sum_numeral)
  have upper: "comma_fixed_iter 9 1 944 < (9 + 1) * 10 ^ 2"
    using endpoint by simp
  have interior: "comma_literal_path 1 944 993"
    using comma_source_fixed_sector_path[OF source upper] endpoint
    by simp
  have crossing: "comma_child 993 1024"
    unfolding comma_child_def
    by (rule exI[where x=1], rule exI[where x=3],
        simp add: comma_sector_def)
  show ?thesis using comma_literal_path_snoc[OF interior crossing]
    by (simp add: One_nat_def numeral_2_eq_2 numeral_3_eq_3)
qed

lemma comma_source20_small_sector_09:
  "comma_literal_path 22 1024 2037"
proof -
  have source: "comma_sector 1 3 1024"
    by (simp add: comma_sector_def)
  have endpoint: "comma_fixed_iter 1 21 1024 = 1985"
    using comma_source_fixed_period_eval
      [where L=10 and f=1 and n=21 and t=2 and j=1
        and k=1024]
    by (simp add: comma_period_displacement_def comma_source_sum_numeral)
  have upper: "comma_fixed_iter 1 21 1024 < (1 + 1) * 10 ^ 3"
    using endpoint by simp
  have interior: "comma_literal_path 21 1024 1985"
    using comma_source_fixed_sector_path[OF source upper] endpoint
    by simp
  have crossing: "comma_child 1985 2037"
    unfolding comma_child_def
    by (rule exI[where x=2], rule exI[where x=3],
        simp add: comma_sector_def)
  show ?thesis using comma_literal_path_snoc[OF interior crossing]
    by (simp add: One_nat_def numeral_2_eq_2 numeral_3_eq_3)
qed

lemma comma_source20_small_sector_10:
  "comma_literal_path 19 2037 3026"
proof -
  have source: "comma_sector 2 3 2037"
    by (simp add: comma_sector_def)
  have endpoint: "comma_fixed_iter 2 18 2037 = 2993"
    using comma_source_fixed_period_eval
      [where L=5 and f=2 and n=18 and t=3 and j=3
        and k=2037]
    by (simp add: comma_period_displacement_def comma_source_sum_numeral)
  have upper: "comma_fixed_iter 2 18 2037 < (2 + 1) * 10 ^ 3"
    using endpoint by simp
  have interior: "comma_literal_path 18 2037 2993"
    using comma_source_fixed_sector_path[OF source upper] endpoint
    by simp
  have crossing: "comma_child 2993 3026"
    unfolding comma_child_def
    by (rule exI[where x=3], rule exI[where x=3],
        simp add: comma_sector_def)
  show ?thesis using comma_literal_path_snoc[OF interior crossing]
    by (simp add: One_nat_def numeral_2_eq_2 numeral_3_eq_3)
qed

lemma comma_source20_small_sector_11:
  "comma_literal_path 21 3026 4050"
proof -
  have source: "comma_sector 3 3 3026"
    by (simp add: comma_sector_def)
  have endpoint: "comma_fixed_iter 3 20 3026 = 3986"
    using comma_source_fixed_period_eval
      [where L=10 and f=3 and n=20 and t=2 and j=0
        and k=3026]
    by (simp add: comma_period_displacement_def comma_source_sum_numeral)
  have upper: "comma_fixed_iter 3 20 3026 < (3 + 1) * 10 ^ 3"
    using endpoint by simp
  have interior: "comma_literal_path 20 3026 3986"
    using comma_source_fixed_sector_path[OF source upper] endpoint
    by simp
  have crossing: "comma_child 3986 4050"
    unfolding comma_child_def
    by (rule exI[where x=4], rule exI[where x=3],
        simp add: comma_sector_def)
  show ?thesis using comma_literal_path_snoc[OF interior crossing]
    by (simp add: One_nat_def numeral_2_eq_2 numeral_3_eq_3)
qed

lemma comma_source20_small_sector_12:
  "comma_literal_path 23 4050 5063"
proof -
  have source: "comma_sector 4 3 4050"
    by (simp add: comma_sector_def)
  have endpoint: "comma_fixed_iter 4 22 4050 = 4978"
    using comma_source_fixed_period_eval
      [where L=5 and f=4 and n=22 and t=4 and j=2
        and k=4050]
    by (simp add: comma_period_displacement_def comma_source_sum_numeral)
  have upper: "comma_fixed_iter 4 22 4050 < (4 + 1) * 10 ^ 3"
    using endpoint by simp
  have interior: "comma_literal_path 22 4050 4978"
    using comma_source_fixed_sector_path[OF source upper] endpoint
    by simp
  have crossing: "comma_child 4978 5063"
    unfolding comma_child_def
    by (rule exI[where x=5], rule exI[where x=3],
        simp add: comma_sector_def)
  show ?thesis using comma_literal_path_snoc[OF interior crossing]
    by (simp add: One_nat_def numeral_2_eq_2 numeral_3_eq_3)
qed

lemma comma_source20_small_sector_13:
  "comma_literal_path 16 5063 6024"
proof -
  have source: "comma_sector 5 3 5063"
    by (simp add: comma_sector_def)
  have endpoint: "comma_fixed_iter 5 15 5063 = 5938"
    using comma_source_fixed_period_eval
      [where L=2 and f=5 and n=15 and t=7 and j=1
        and k=5063]
    by (simp add: comma_period_displacement_def comma_source_sum_numeral)
  have upper: "comma_fixed_iter 5 15 5063 < (5 + 1) * 10 ^ 3"
    using endpoint by simp
  have interior: "comma_literal_path 15 5063 5938"
    using comma_source_fixed_sector_path[OF source upper] endpoint
    by simp
  have crossing: "comma_child 5938 6024"
    unfolding comma_child_def
    by (rule exI[where x=6], rule exI[where x=3],
        simp add: comma_sector_def)
  show ?thesis using comma_literal_path_snoc[OF interior crossing]
    by (simp add: One_nat_def numeral_2_eq_2 numeral_3_eq_3)
qed

lemma comma_source20_small_sector_14:
  "comma_literal_path 23 6024 7063"
proof -
  have source: "comma_sector 6 3 6024"
    by (simp add: comma_sector_def)
  have endpoint: "comma_fixed_iter 6 22 6024 = 6996"
    using comma_source_fixed_period_eval
      [where L=5 and f=6 and n=22 and t=4 and j=2
        and k=6024]
    by (simp add: comma_period_displacement_def comma_source_sum_numeral)
  have upper: "comma_fixed_iter 6 22 6024 < (6 + 1) * 10 ^ 3"
    using endpoint by simp
  have interior: "comma_literal_path 22 6024 6996"
    using comma_source_fixed_sector_path[OF source upper] endpoint
    by simp
  have crossing: "comma_child 6996 7063"
    unfolding comma_child_def
    by (rule exI[where x=7], rule exI[where x=3],
        simp add: comma_sector_def)
  show ?thesis using comma_literal_path_snoc[OF interior crossing]
    by (simp add: One_nat_def numeral_2_eq_2 numeral_3_eq_3)
qed

lemma comma_source20_small_sector_15:
  "comma_literal_path 19 7063 8037"
proof -
  have source: "comma_sector 7 3 7063"
    by (simp add: comma_sector_def)
  have endpoint: "comma_fixed_iter 7 18 7063 = 7939"
    using comma_source_fixed_period_eval
      [where L=10 and f=7 and n=18 and t=1 and j=8
        and k=7063]
    by (simp add: comma_period_displacement_def comma_source_sum_numeral)
  have upper: "comma_fixed_iter 7 18 7063 < (7 + 1) * 10 ^ 3"
    using endpoint by simp
  have interior: "comma_literal_path 18 7063 7939"
    using comma_source_fixed_sector_path[OF source upper] endpoint
    by simp
  have crossing: "comma_child 7939 8037"
    unfolding comma_child_def
    by (rule exI[where x=8], rule exI[where x=3],
        simp add: comma_sector_def)
  show ?thesis using comma_literal_path_snoc[OF interior crossing]
    by (simp add: One_nat_def numeral_2_eq_2 numeral_3_eq_3)
qed

lemma comma_source20_small_sector_16:
  "comma_literal_path 17 8037 9044"
proof -
  have source: "comma_sector 8 3 8037"
    by (simp add: comma_sector_def)
  have endpoint: "comma_fixed_iter 8 16 8037 = 8985"
    using comma_source_fixed_period_eval
      [where L=5 and f=8 and n=16 and t=3 and j=1
        and k=8037]
    by (simp add: comma_period_displacement_def comma_source_sum_numeral)
  have upper: "comma_fixed_iter 8 16 8037 < (8 + 1) * 10 ^ 3"
    using endpoint by simp
  have interior: "comma_literal_path 16 8037 8985"
    using comma_source_fixed_sector_path[OF source upper] endpoint
    by simp
  have crossing: "comma_child 8985 9044"
    unfolding comma_child_def
    by (rule exI[where x=9], rule exI[where x=3],
        simp add: comma_sector_def)
  show ?thesis using comma_literal_path_snoc[OF interior crossing]
    by (simp add: One_nat_def numeral_2_eq_2 numeral_3_eq_3)
qed

lemma comma_source20_small_sector_17:
  "comma_literal_path 19 9044 10057"
proof -
  have source: "comma_sector 9 3 9044"
    by (simp add: comma_sector_def)
  have endpoint: "comma_fixed_iter 9 18 9044 = 9996"
    using comma_source_fixed_period_eval
      [where L=10 and f=9 and n=18 and t=1 and j=8
        and k=9044]
    by (simp add: comma_period_displacement_def comma_source_sum_numeral)
  have upper: "comma_fixed_iter 9 18 9044 < (9 + 1) * 10 ^ 3"
    using endpoint by simp
  have interior: "comma_literal_path 18 9044 9996"
    using comma_source_fixed_sector_path[OF source upper] endpoint
    by simp
  have crossing: "comma_child 9996 10057"
    unfolding comma_child_def
    by (rule exI[where x=1], rule exI[where x=4],
        simp add: comma_sector_def)
  show ?thesis using comma_literal_path_snoc[OF interior crossing]
    by (simp add: One_nat_def numeral_2_eq_2 numeral_3_eq_3)
qed

lemma comma_source20_small_sector_18:
  "comma_literal_path 217 10057 20025"
proof -
  have source: "comma_sector 1 4 10057"
    by (simp add: comma_sector_def)
  have endpoint: "comma_fixed_iter 1 216 10057 = 19993"
    using comma_source_fixed_period_eval
      [where L=10 and f=1 and n=216 and t=21 and j=6
        and k=10057]
    by (simp add: comma_period_displacement_def comma_source_sum_numeral)
  have upper: "comma_fixed_iter 1 216 10057 < (1 + 1) * 10 ^ 4"
    using endpoint by simp
  have interior: "comma_literal_path 216 10057 19993"
    using comma_source_fixed_sector_path[OF source upper] endpoint
    by simp
  have crossing: "comma_child 19993 20025"
    unfolding comma_child_def
    by (rule exI[where x=2], rule exI[where x=4],
        simp add: comma_sector_def)
  show ?thesis using comma_literal_path_snoc[OF interior crossing]
    by (simp add: One_nat_def numeral_2_eq_2 numeral_3_eq_3)
qed

lemma comma_source20_small_sector_19:
  "comma_literal_path 192 20025 30030"
proof -
  have source: "comma_sector 2 4 20025"
    by (simp add: comma_sector_def)
  have endpoint: "comma_fixed_iter 2 191 20025 = 29957"
    using comma_source_fixed_period_eval
      [where L=5 and f=2 and n=191 and t=38 and j=1
        and k=20025]
    by (simp add: comma_period_displacement_def comma_source_sum_numeral)
  have upper: "comma_fixed_iter 2 191 20025 < (2 + 1) * 10 ^ 4"
    using endpoint by simp
  have interior: "comma_literal_path 191 20025 29957"
    using comma_source_fixed_sector_path[OF source upper] endpoint
    by simp
  have crossing: "comma_child 29957 30030"
    unfolding comma_child_def
    by (rule exI[where x=3], rule exI[where x=4],
        simp add: comma_sector_def)
  show ?thesis using comma_literal_path_snoc[OF interior crossing]
    by (simp add: One_nat_def numeral_2_eq_2 numeral_3_eq_3)
qed

lemma comma_source20_small_sector_20:
  "comma_literal_path 209 30030 40038"
proof -
  have source: "comma_sector 3 4 30030"
    by (simp add: comma_sector_def)
  have endpoint: "comma_fixed_iter 3 208 30030 = 39994"
    using comma_source_fixed_period_eval
      [where L=10 and f=3 and n=208 and t=20 and j=8
        and k=30030]
    by (simp add: comma_period_displacement_def comma_source_sum_numeral)
  have upper: "comma_fixed_iter 3 208 30030 < (3 + 1) * 10 ^ 4"
    using endpoint by simp
  have interior: "comma_literal_path 208 30030 39994"
    using comma_source_fixed_sector_path[OF source upper] endpoint
    by simp
  have crossing: "comma_child 39994 40038"
    unfolding comma_child_def
    by (rule exI[where x=4], rule exI[where x=4],
        simp add: comma_sector_def)
  show ?thesis using comma_literal_path_snoc[OF interior crossing]
    by (simp add: One_nat_def numeral_2_eq_2 numeral_3_eq_3)
qed

lemma comma_source20_small_sector_21:
  "comma_literal_path 226 40038 50023"
proof -
  have source: "comma_sector 4 4 40038"
    by (simp add: comma_sector_def)
  have endpoint: "comma_fixed_iter 4 225 40038 = 49938"
    using comma_source_fixed_period_eval
      [where L=5 and f=4 and n=225 and t=45 and j=0
        and k=40038]
    by (simp add: comma_period_displacement_def comma_source_sum_numeral)
  have upper: "comma_fixed_iter 4 225 40038 < (4 + 1) * 10 ^ 4"
    using endpoint by simp
  have interior: "comma_literal_path 225 40038 49938"
    using comma_source_fixed_sector_path[OF source upper] endpoint
    by simp
  have crossing: "comma_child 49938 50023"
    unfolding comma_child_def
    by (rule exI[where x=5], rule exI[where x=4],
        simp add: comma_sector_def)
  show ?thesis using comma_literal_path_snoc[OF interior crossing]
    by (simp add: One_nat_def numeral_2_eq_2 numeral_3_eq_3)
qed

lemma comma_source20_small_sector_22:
  "comma_literal_path 167 50023 60019"
proof -
  have source: "comma_sector 5 4 50023"
    by (simp add: comma_sector_def)
  have endpoint: "comma_fixed_iter 5 166 50023 = 59983"
    using comma_source_fixed_period_eval
      [where L=2 and f=5 and n=166 and t=83 and j=0
        and k=50023]
    by (simp add: comma_period_displacement_def comma_source_sum_numeral)
  have upper: "comma_fixed_iter 5 166 50023 < (5 + 1) * 10 ^ 4"
    using endpoint by simp
  have interior: "comma_literal_path 166 50023 59983"
    using comma_source_fixed_sector_path[OF source upper] endpoint
    by simp
  have crossing: "comma_child 59983 60019"
    unfolding comma_child_def
    by (rule exI[where x=6], rule exI[where x=4],
        simp add: comma_sector_def)
  show ?thesis using comma_literal_path_snoc[OF interior crossing]
    by (simp add: One_nat_def numeral_2_eq_2 numeral_3_eq_3)
qed

lemma comma_source20_small_sector_23:
  "comma_literal_path 179 60019 70064"
proof -
  have source: "comma_sector 6 4 60019"
    by (simp add: comma_sector_def)
  have endpoint: "comma_fixed_iter 6 178 60019 = 69987"
    using comma_source_fixed_period_eval
      [where L=5 and f=6 and n=178 and t=35 and j=3
        and k=60019]
    by (simp add: comma_period_displacement_def comma_source_sum_numeral)
  have upper: "comma_fixed_iter 6 178 60019 < (6 + 1) * 10 ^ 4"
    using endpoint by simp
  have interior: "comma_literal_path 178 60019 69987"
    using comma_source_fixed_sector_path[OF source upper] endpoint
    by simp
  have crossing: "comma_child 69987 70064"
    unfolding comma_child_def
    by (rule exI[where x=7], rule exI[where x=4],
        simp add: comma_sector_def)
  show ?thesis using comma_literal_path_snoc[OF interior crossing]
    by (simp add: One_nat_def numeral_2_eq_2 numeral_3_eq_3)
qed

lemma comma_source20_small_sector_24:
  "comma_literal_path 192 70064 80009"
proof -
  have source: "comma_sector 7 4 70064"
    by (simp add: comma_sector_def)
  have endpoint: "comma_fixed_iter 7 191 70064 = 79991"
    using comma_source_fixed_period_eval
      [where L=10 and f=7 and n=191 and t=19 and j=1
        and k=70064]
    by (simp add: comma_period_displacement_def comma_source_sum_numeral)
  have upper: "comma_fixed_iter 7 191 70064 < (7 + 1) * 10 ^ 4"
    using endpoint by simp
  have interior: "comma_literal_path 191 70064 79991"
    using comma_source_fixed_sector_path[OF source upper] endpoint
    by simp
  have crossing: "comma_child 79991 80009"
    unfolding comma_child_def
    by (rule exI[where x=8], rule exI[where x=4],
        simp add: comma_sector_def)
  show ?thesis using comma_literal_path_snoc[OF interior crossing]
    by (simp add: One_nat_def numeral_2_eq_2 numeral_3_eq_3)
qed

lemma comma_source20_small_sector_25:
  "comma_literal_path 172 80009 90046"
proof -
  have source: "comma_sector 8 4 80009"
    by (simp add: comma_sector_def)
  have endpoint: "comma_fixed_iter 8 171 80009 = 89967"
    using comma_source_fixed_period_eval
      [where L=5 and f=8 and n=171 and t=34 and j=1
        and k=80009]
    by (simp add: comma_period_displacement_def comma_source_sum_numeral)
  have upper: "comma_fixed_iter 8 171 80009 < (8 + 1) * 10 ^ 4"
    using endpoint by simp
  have interior: "comma_literal_path 171 80009 89967"
    using comma_source_fixed_sector_path[OF source upper] endpoint
    by simp
  have crossing: "comma_child 89967 90046"
    unfolding comma_child_def
    by (rule exI[where x=9], rule exI[where x=4],
        simp add: comma_sector_def)
  show ?thesis using comma_literal_path_snoc[OF interior crossing]
    by (simp add: One_nat_def numeral_2_eq_2 numeral_3_eq_3)
qed

lemma comma_source20_small_sector_26:
  "comma_literal_path 185 90046 100003"
proof -
  have source: "comma_sector 9 4 90046"
    by (simp add: comma_sector_def)
  have endpoint: "comma_fixed_iter 9 184 90046 = 99982"
    using comma_source_fixed_period_eval
      [where L=10 and f=9 and n=184 and t=18 and j=4
        and k=90046]
    by (simp add: comma_period_displacement_def comma_source_sum_numeral)
  have upper: "comma_fixed_iter 9 184 90046 < (9 + 1) * 10 ^ 4"
    using endpoint by simp
  have interior: "comma_literal_path 184 90046 99982"
    using comma_source_fixed_sector_path[OF source upper] endpoint
    by simp
  have crossing: "comma_child 99982 100003"
    unfolding comma_child_def
    by (rule exI[where x=1], rule exI[where x=5],
        simp add: comma_sector_def)
  show ?thesis using comma_literal_path_snoc[OF interior crossing]
    by (simp add: One_nat_def numeral_2_eq_2 numeral_3_eq_3)
qed

lemma comma_source107_to_p5:
  "comma_literal_path 1936 107 100003"
proof -
  have joined_00: "comma_literal_path 2 107 260"
    using comma_source20_small_sector_00 .
  have joined_01: "comma_literal_path 5 107 327"
    using comma_literal_path_append[OF joined_00
      comma_source20_small_sector_01] by simp
  have joined_02: "comma_literal_path 6 107 401"
    using comma_literal_path_append[OF joined_01
      comma_source20_small_sector_02] by simp
  have joined_03: "comma_literal_path 9 107 564"
    using comma_literal_path_append[OF joined_02
      comma_source20_small_sector_03] by simp
  have joined_04: "comma_literal_path 10 107 610"
    using comma_literal_path_append[OF joined_03
      comma_source20_small_sector_04] by simp
  have joined_05: "comma_literal_path 13 107 709"
    using comma_literal_path_append[OF joined_04
      comma_source20_small_sector_05] by simp
  have joined_06: "comma_literal_path 14 107 807"
    using comma_literal_path_append[OF joined_05
      comma_source20_small_sector_06] by simp
  have joined_07: "comma_literal_path 16 107 944"
    using comma_literal_path_append[OF joined_06
      comma_source20_small_sector_07] by simp
  have joined_08: "comma_literal_path 18 107 1024"
    using comma_literal_path_append[OF joined_07
      comma_source20_small_sector_08] by simp
  have joined_09: "comma_literal_path 40 107 2037"
    using comma_literal_path_append[OF joined_08
      comma_source20_small_sector_09] by simp
  have joined_10: "comma_literal_path 59 107 3026"
    using comma_literal_path_append[OF joined_09
      comma_source20_small_sector_10] by simp
  have joined_11: "comma_literal_path 80 107 4050"
    using comma_literal_path_append[OF joined_10
      comma_source20_small_sector_11] by simp
  have joined_12: "comma_literal_path 103 107 5063"
    using comma_literal_path_append[OF joined_11
      comma_source20_small_sector_12] by simp
  have joined_13: "comma_literal_path 119 107 6024"
    using comma_literal_path_append[OF joined_12
      comma_source20_small_sector_13] by simp
  have joined_14: "comma_literal_path 142 107 7063"
    using comma_literal_path_append[OF joined_13
      comma_source20_small_sector_14] by simp
  have joined_15: "comma_literal_path 161 107 8037"
    using comma_literal_path_append[OF joined_14
      comma_source20_small_sector_15] by simp
  have joined_16: "comma_literal_path 178 107 9044"
    using comma_literal_path_append[OF joined_15
      comma_source20_small_sector_16] by simp
  have joined_17: "comma_literal_path 197 107 10057"
    using comma_literal_path_append[OF joined_16
      comma_source20_small_sector_17] by simp
  have joined_18: "comma_literal_path 414 107 20025"
    using comma_literal_path_append[OF joined_17
      comma_source20_small_sector_18] by simp
  have joined_19: "comma_literal_path 606 107 30030"
    using comma_literal_path_append[OF joined_18
      comma_source20_small_sector_19] by simp
  have joined_20: "comma_literal_path 815 107 40038"
    using comma_literal_path_append[OF joined_19
      comma_source20_small_sector_20] by simp
  have joined_21: "comma_literal_path 1041 107 50023"
    using comma_literal_path_append[OF joined_20
      comma_source20_small_sector_21] by simp
  have joined_22: "comma_literal_path 1208 107 60019"
    using comma_literal_path_append[OF joined_21
      comma_source20_small_sector_22] by simp
  have joined_23: "comma_literal_path 1387 107 70064"
    using comma_literal_path_append[OF joined_22
      comma_source20_small_sector_23] by simp
  have joined_24: "comma_literal_path 1579 107 80009"
    using comma_literal_path_append[OF joined_23
      comma_source20_small_sector_24] by simp
  have joined_25: "comma_literal_path 1751 107 90046"
    using comma_literal_path_append[OF joined_24
      comma_source20_small_sector_25] by simp
  have joined_26: "comma_literal_path 1936 107 100003"
    using comma_literal_path_append[OF joined_25
      comma_source20_small_sector_26] by simp
  show ?thesis using joined_26 .
qed

lemma comma_source20_to_p5:
  "comma_literal_path 1939 20 100003"
  using comma_literal_path_append[OF comma_source20_startup
    comma_source107_to_p5] by simp

lemma comma_source20_indexed_tail:
  "\<exists>rows. comma_indexed_trace 5 (Comma_Entry 1 0 3) rows
      (Comma_Fork_At 2 5) (Comma_Near 1 5 82) \<and>
    sum_list (map fst rows) = 412985919"
  using comma_control_trace_indexed[where p=5, simplified, OF comma_source_tail_trace]
    comma_source_tail_shape comma_source_tail_weight by simp

lemma comma_source20_weighted_tail_literal:
  "comma_literal_path 412985919 100003 19999999918"
proof -
  obtain rows where rows:
    "comma_indexed_trace 5 (Comma_Entry 1 0 3) rows
      (Comma_Fork_At 2 5) (Comma_Near 1 5 82)"
    "sum_list (map fst rows) = 412985919"
    using comma_source20_indexed_tail by blast
  have refined: "comma_refined_indexed_trace 5 (Comma_Entry 1 0 3) rows
      (Comma_Fork_At 2 5) (Comma_Near 1 5 82)"
    by (rule comma_indexed_trace_is_refined[OF _ rows(1)]) simp
  show ?thesis
    using comma_refined_indexed_trace_terminal_path[OF refined] rows(2)
    by (simp add: comma_chart_value_def)
qed

text \<open>This proves a literal path to the fork value. Uniqueness of every
preceding child is a separate obligation; the path alone does not establish
that this is the first fork on every possible continuation.\<close>

theorem comma_source20_to_fork:
  "comma_literal_path 412987858 20 19999999918"
  using comma_literal_path_append[OF comma_source20_to_p5
    comma_source20_weighted_tail_literal] by simp

lemma comma_source20_first_fork_children:
  "comma_child 19999999918 target \<longleftrightarrow>
    target = 19999999999 \<or> target = 20000000000"
  using comma_large_children_complete[of 1 10 19999999918 target]
  by (simp add: comma_sector_def comma_large_children_def
    comma_headroom_def Let_def)

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_source_fixed_iter_mono comma_source_fixed_sector_path
      comma_source_fixed_period_eval comma_source20_startup
      comma_source107_to_p5 comma_source20_to_p5
      comma_control_trace_indexed
      comma_source20_indexed_tail comma_source20_weighted_tail_literal
      comma_source20_to_fork comma_source20_first_fork_children})
    then () else error "Comma source-entry proof depends on an oracle";
\<close>

end
