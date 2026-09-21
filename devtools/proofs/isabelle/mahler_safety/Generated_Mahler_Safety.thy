theory Generated_Mahler_Safety
  imports Mahler_Safety_Cylinders
begin

(* Adapted from the supplied 2026-09-20 Mahler safety release.
   Upstream SHA-256: f59bfd518bbf9989b516b303789efb377c45b051213724a41f1d5deeb5e3ad70
   Scope and import changes: docs/research/antihydra-mahler.md. *)

text \<open>Generated exact certificates for fractional offsets t in [0,1/2).
Bounds are closed below and open above. Empty intervals reject the entire
integer-part cylinder. Surviving intervals certify six steps only.\<close>

lemma residue_0_exact:
  fixes t :: real
  assumes t: "0 \<le> t" "t < 1/2"
  shows "safe_prefix 6 (0+t) \<longleftrightarrow> (0 \<le> t \<and> t < (32/729))"
proof -
  have lo: "of_nat 0 \<le> (0::real)+t" using t by simp
  have hi: "(0::real)+t < of_nat 0+1/2" using t by simp
  show ?thesis
    unfolding safe_prefix_exact[OF lo hi] all_upto_six
    using t by (simp add: mahler_D_step_def power_divide; linarith)
qed

lemma residue_1_exact:
  fixes t :: real
  assumes t: "0 \<le> t" "t < 1/2"
  shows "safe_prefix 6 (1+t) \<longleftrightarrow> ((47/81) \<le> t \<and> t < (1/2))"
proof -
  have lo: "of_nat 1 \<le> (1::real)+t" using t by simp
  have hi: "(1::real)+t < of_nat 1+1/2" using t by simp
  show ?thesis
    unfolding safe_prefix_exact[OF lo hi] all_upto_six
    using t by (simp add: mahler_D_step_def power_divide; linarith)
qed

lemma residue_2_exact:
  fixes t :: real
  assumes t: "0 \<le> t" "t < 1/2"
  shows "safe_prefix 6 (2+t) \<longleftrightarrow> ((10/27) \<le> t \<and> t < (1/3))"
proof -
  have lo: "of_nat 2 \<le> (2::real)+t" using t by simp
  have hi: "(2::real)+t < of_nat 2+1/2" using t by simp
  show ?thesis
    unfolding safe_prefix_exact[OF lo hi] all_upto_six
    using t by (simp add: mahler_D_step_def power_divide; linarith)
qed

lemma residue_3_exact:
  fixes t :: real
  assumes t: "0 \<le> t" "t < 1/2"
  shows "safe_prefix 6 (3+t) \<longleftrightarrow> ((437/729) \<le> t \<and> t < (1/2))"
proof -
  have lo: "of_nat 3 \<le> (3::real)+t" using t by simp
  have hi: "(3::real)+t < of_nat 3+1/2" using t by simp
  show ?thesis
    unfolding safe_prefix_exact[OF lo hi] all_upto_six
    using t by (simp add: mahler_D_step_def power_divide; linarith)
qed

lemma residue_4_exact:
  fixes t :: real
  assumes t: "0 \<le> t" "t < 1/2"
  shows "safe_prefix 6 (4+t) \<longleftrightarrow> ((52/243) \<le> t \<and> t < (2/9))"
proof -
  have lo: "of_nat 4 \<le> (4::real)+t" using t by simp
  have hi: "(4::real)+t < of_nat 4+1/2" using t by simp
  show ?thesis
    unfolding safe_prefix_exact[OF lo hi] all_upto_six
    using t by (simp add: mahler_D_step_def power_divide; linarith)
qed

lemma residue_5_exact:
  fixes t :: real
  assumes t: "0 \<le> t" "t < 1/2"
  shows "safe_prefix 6 (5+t) \<longleftrightarrow> ((323/729) \<le> t \<and> t < (35/81))"
proof -
  have lo: "of_nat 5 \<le> (5::real)+t" using t by simp
  have hi: "(5::real)+t < of_nat 5+1/2" using t by simp
  show ?thesis
    unfolding safe_prefix_exact[OF lo hi] all_upto_six
    using t by (simp add: mahler_D_step_def power_divide; linarith)
qed

lemma residue_6_exact:
  fixes t :: real
  assumes t: "0 \<le> t" "t < 1/2"
  shows "safe_prefix 6 (6+t) \<longleftrightarrow> ((26/81) \<le> t \<and> t < (1/3))"
proof -
  have lo: "of_nat 6 \<le> (6::real)+t" using t by simp
  have hi: "(6::real)+t < of_nat 6+1/2" using t by simp
  show ?thesis
    unfolding safe_prefix_exact[OF lo hi] all_upto_six
    using t by (simp add: mahler_D_step_def power_divide; linarith)
qed

lemma residue_7_exact:
  fixes t :: real
  assumes t: "0 \<le> t" "t < 1/2"
  shows "safe_prefix 6 (7+t) \<longleftrightarrow> ((593/729) \<le> t \<and> t < (1/2))"
proof -
  have lo: "of_nat 7 \<le> (7::real)+t" using t by simp
  have hi: "(7::real)+t < of_nat 7+1/2" using t by simp
  show ?thesis
    unfolding safe_prefix_exact[OF lo hi] all_upto_six
    using t by (simp add: mahler_D_step_def power_divide; linarith)
qed

lemma residue_8_exact:
  fixes t :: real
  assumes t: "0 \<le> t" "t < 1/2"
  shows "safe_prefix 6 (8+t) \<longleftrightarrow> ((40/243) \<le> t \<and> t < (4/27))"
proof -
  have lo: "of_nat 8 \<le> (8::real)+t" using t by simp
  have hi: "(8::real)+t < of_nat 8+1/2" using t by simp
  show ?thesis
    unfolding safe_prefix_exact[OF lo hi] all_upto_six
    using t by (simp add: mahler_D_step_def power_divide; linarith)
qed

lemma residue_9_exact:
  fixes t :: real
  assumes t: "0 \<le> t" "t < 1/2"
  shows "safe_prefix 6 (9+t) \<longleftrightarrow> ((13/27) \<le> t \<and> t < (1/2))"
proof -
  have lo: "of_nat 9 \<le> (9::real)+t" using t by simp
  have hi: "(9::real)+t < of_nat 9+1/2" using t by simp
  show ?thesis
    unfolding safe_prefix_exact[OF lo hi] all_upto_six
    using t by (simp add: mahler_D_step_def power_divide; linarith)
qed

lemma residue_10_exact:
  fixes t :: real
  assumes t: "0 \<le> t" "t < 1/2"
  shows "safe_prefix 6 (10+t) \<longleftrightarrow> ((130/243) \<le> t \<and> t < (1/3))"
proof -
  have lo: "of_nat 10 \<le> (10::real)+t" using t by simp
  have hi: "(10::real)+t < of_nat 10+1/2" using t by simp
  show ?thesis
    unfolding safe_prefix_exact[OF lo hi] all_upto_six
    using t by (simp add: mahler_D_step_def power_divide; linarith)
qed

lemma residue_11_exact:
  fixes t :: real
  assumes t: "0 \<le> t" "t < 1/2"
  shows "safe_prefix 6 (11+t) \<longleftrightarrow> ((557/729) \<le> t \<and> t < (1/2))"
proof -
  have lo: "of_nat 11 \<le> (11::real)+t" using t by simp
  have hi: "(11::real)+t < of_nat 11+1/2" using t by simp
  show ?thesis
    unfolding safe_prefix_exact[OF lo hi] all_upto_six
    using t by (simp add: mahler_D_step_def power_divide; linarith)
qed

lemma residue_12_exact:
  fixes t :: real
  assumes t: "0 \<le> t" "t < 1/2"
  shows "safe_prefix 6 (12+t) \<longleftrightarrow> ((212/729) \<le> t \<and> t < (2/9))"
proof -
  have lo: "of_nat 12 \<le> (12::real)+t" using t by simp
  have hi: "(12::real)+t < of_nat 12+1/2" using t by simp
  show ?thesis
    unfolding safe_prefix_exact[OF lo hi] all_upto_six
    using t by (simp add: mahler_D_step_def power_divide; linarith)
qed

lemma residue_13_exact:
  fixes t :: real
  assumes t: "0 \<le> t" "t < 1/2"
  shows "safe_prefix 6 (13+t) \<longleftrightarrow> ((35/81) \<le> t \<and> t < (347/729))"
proof -
  have lo: "of_nat 13 \<le> (13::real)+t" using t by simp
  have hi: "(13::real)+t < of_nat 13+1/2" using t by simp
  show ?thesis
    unfolding safe_prefix_exact[OF lo hi] all_upto_six
    using t by (simp add: mahler_D_step_def power_divide; linarith)
qed

lemma residue_14_exact:
  fixes t :: real
  assumes t: "0 \<le> t" "t < 1/2"
  shows "safe_prefix 6 (14+t) \<longleftrightarrow> ((2/9) \<le> t \<and> t < (194/729))"
proof -
  have lo: "of_nat 14 \<le> (14::real)+t" using t by simp
  have hi: "(14::real)+t < of_nat 14+1/2" using t by simp
  show ?thesis
    unfolding safe_prefix_exact[OF lo hi] all_upto_six
    using t by (simp add: mahler_D_step_def power_divide; linarith)
qed

lemma residue_15_exact:
  fixes t :: real
  assumes t: "0 \<le> t" "t < 1/2"
  shows "safe_prefix 6 (15+t) \<longleftrightarrow> ((65/81) \<le> t \<and> t < (1/2))"
proof -
  have lo: "of_nat 15 \<le> (15::real)+t" using t by simp
  have hi: "(15::real)+t < of_nat 15+1/2" using t by simp
  show ?thesis
    unfolding safe_prefix_exact[OF lo hi] all_upto_six
    using t by (simp add: mahler_D_step_def power_divide; linarith)
qed

lemma residue_16_exact:
  fixes t :: real
  assumes t: "0 \<le> t" "t < 1/2"
  shows "safe_prefix 6 (16+t) \<longleftrightarrow> ((16/243) \<le> t \<and> t < (8/81))"
proof -
  have lo: "of_nat 16 \<le> (16::real)+t" using t by simp
  have hi: "(16::real)+t < of_nat 16+1/2" using t by simp
  show ?thesis
    unfolding safe_prefix_exact[OF lo hi] all_upto_six
    using t by (simp add: mahler_D_step_def power_divide; linarith)
qed

lemma residue_17_exact:
  fixes t :: real
  assumes t: "0 \<le> t" "t < 1/2"
  shows "safe_prefix 6 (17+t) \<longleftrightarrow> ((157/243) \<le> t \<and> t < (1/2))"
proof -
  have lo: "of_nat 17 \<le> (17::real)+t" using t by simp
  have hi: "(17::real)+t < of_nat 17+1/2" using t by simp
  show ?thesis
    unfolding safe_prefix_exact[OF lo hi] all_upto_six
    using t by (simp add: mahler_D_step_def power_divide; linarith)
qed

lemma residue_18_exact:
  fixes t :: real
  assumes t: "0 \<le> t" "t < 1/2"
  shows "safe_prefix 6 (18+t) \<longleftrightarrow> ((106/243) \<le> t \<and> t < (1/3))"
proof -
  have lo: "of_nat 18 \<le> (18::real)+t" using t by simp
  have hi: "(18::real)+t < of_nat 18+1/2" using t by simp
  show ?thesis
    unfolding safe_prefix_exact[OF lo hi] all_upto_six
    using t by (simp add: mahler_D_step_def power_divide; linarith)
qed

lemma residue_19_exact:
  fixes t :: real
  assumes t: "0 \<le> t" "t < 1/2"
  shows "safe_prefix 6 (19+t) \<longleftrightarrow> ((485/729) \<le> t \<and> t < (1/2))"
proof -
  have lo: "of_nat 19 \<le> (19::real)+t" using t by simp
  have hi: "(19::real)+t < of_nat 19+1/2" using t by simp
  show ?thesis
    unfolding safe_prefix_exact[OF lo hi] all_upto_six
    using t by (simp add: mahler_D_step_def power_divide; linarith)
qed

lemma residue_20_exact:
  fixes t :: real
  assumes t: "0 \<le> t" "t < 1/2"
  shows "safe_prefix 6 (20+t) \<longleftrightarrow> ((140/729) \<le> t \<and> t < (52/243))"
proof -
  have lo: "of_nat 20 \<le> (20::real)+t" using t by simp
  have hi: "(20::real)+t < of_nat 20+1/2" using t by simp
  show ?thesis
    unfolding safe_prefix_exact[OF lo hi] all_upto_six
    using t by (simp add: mahler_D_step_def power_divide; linarith)
qed

lemma residue_21_exact:
  fixes t :: real
  assumes t: "0 \<le> t" "t < 1/2"
  shows "safe_prefix 6 (21+t) \<longleftrightarrow> ((1/3) \<le> t \<and> t < (275/729))"
proof -
  have lo: "of_nat 21 \<le> (21::real)+t" using t by simp
  have hi: "(21::real)+t < of_nat 21+1/2" using t by simp
  show ?thesis
    unfolding safe_prefix_exact[OF lo hi] all_upto_six
    using t by (simp add: mahler_D_step_def power_divide; linarith)
qed

lemma residue_22_exact:
  fixes t :: real
  assumes t: "0 \<le> t" "t < 1/2"
  shows "safe_prefix 6 (22+t) \<longleftrightarrow> ((94/243) \<le> t \<and> t < (1/3))"
proof -
  have lo: "of_nat 22 \<le> (22::real)+t" using t by simp
  have hi: "(22::real)+t < of_nat 22+1/2" using t by simp
  show ?thesis
    unfolding safe_prefix_exact[OF lo hi] all_upto_six
    using t by (simp add: mahler_D_step_def power_divide; linarith)
qed

lemma residue_23_exact:
  fixes t :: real
  assumes t: "0 \<le> t" "t < 1/2"
  shows "safe_prefix 6 (23+t) \<longleftrightarrow> ((19/27) \<le> t \<and> t < (1/2))"
proof -
  have lo: "of_nat 23 \<le> (23::real)+t" using t by simp
  have hi: "(23::real)+t < of_nat 23+1/2" using t by simp
  show ?thesis
    unfolding safe_prefix_exact[OF lo hi] all_upto_six
    using t by (simp add: mahler_D_step_def power_divide; linarith)
qed

lemma residue_24_exact:
  fixes t :: real
  assumes t: "0 \<le> t" "t < 1/2"
  shows "safe_prefix 6 (24+t) \<longleftrightarrow> ((104/729) \<le> t \<and> t < (4/27))"
proof -
  have lo: "of_nat 24 \<le> (24::real)+t" using t by simp
  have hi: "(24::real)+t < of_nat 24+1/2" using t by simp
  show ?thesis
    unfolding safe_prefix_exact[OF lo hi] all_upto_six
    using t by (simp add: mahler_D_step_def power_divide; linarith)
qed

lemma residue_25_exact:
  fixes t :: real
  assumes t: "0 \<le> t" "t < 1/2"
  shows "safe_prefix 6 (25+t) \<longleftrightarrow> ((133/243) \<le> t \<and> t < (1/2))"
proof -
  have lo: "of_nat 25 \<le> (25::real)+t" using t by simp
  have hi: "(25::real)+t < of_nat 25+1/2" using t by simp
  show ?thesis
    unfolding safe_prefix_exact[OF lo hi] all_upto_six
    using t by (simp add: mahler_D_step_def power_divide; linarith)
qed

lemma residue_26_exact:
  fixes t :: real
  assumes t: "0 \<le> t" "t < 1/2"
  shows "safe_prefix 6 (26+t) \<longleftrightarrow> ((374/729) \<le> t \<and> t < (1/3))"
proof -
  have lo: "of_nat 26 \<le> (26::real)+t" using t by simp
  have hi: "(26::real)+t < of_nat 26+1/2" using t by simp
  show ?thesis
    unfolding safe_prefix_exact[OF lo hi] all_upto_six
    using t by (simp add: mahler_D_step_def power_divide; linarith)
qed

lemma residue_27_exact:
  fixes t :: real
  assumes t: "0 \<le> t" "t < 1/2"
  shows "safe_prefix 6 (27+t) \<longleftrightarrow> ((53/81) \<le> t \<and> t < (1/2))"
proof -
  have lo: "of_nat 27 \<le> (27::real)+t" using t by simp
  have hi: "(27::real)+t < of_nat 27+1/2" using t by simp
  show ?thesis
    unfolding safe_prefix_exact[OF lo hi] all_upto_six
    using t by (simp add: mahler_D_step_def power_divide; linarith)
qed

lemma residue_28_exact:
  fixes t :: real
  assumes t: "0 \<le> t" "t < 1/2"
  shows "safe_prefix 6 (28+t) \<longleftrightarrow> ((260/729) \<le> t \<and> t < (2/9))"
proof -
  have lo: "of_nat 28 \<le> (28::real)+t" using t by simp
  have hi: "(28::real)+t < of_nat 28+1/2" using t by simp
  show ?thesis
    unfolding safe_prefix_exact[OF lo hi] all_upto_six
    using t by (simp add: mahler_D_step_def power_divide; linarith)
qed

lemma residue_29_exact:
  fixes t :: real
  assumes t: "0 \<le> t" "t < 1/2"
  shows "safe_prefix 6 (29+t) \<longleftrightarrow> ((121/243) \<le> t \<and> t < (13/27))"
proof -
  have lo: "of_nat 29 \<le> (29::real)+t" using t by simp
  have hi: "(29::real)+t < of_nat 29+1/2" using t by simp
  show ?thesis
    unfolding safe_prefix_exact[OF lo hi] all_upto_six
    using t by (simp add: mahler_D_step_def power_divide; linarith)
qed

lemma residue_30_exact:
  fixes t :: real
  assumes t: "0 \<le> t" "t < 1/2"
  shows "safe_prefix 6 (30+t) \<longleftrightarrow> ((70/243) \<le> t \<and> t < (26/81))"
proof -
  have lo: "of_nat 30 \<le> (30::real)+t" using t by simp
  have hi: "(30::real)+t < of_nat 30+1/2" using t by simp
  show ?thesis
    unfolding safe_prefix_exact[OF lo hi] all_upto_six
    using t by (simp add: mahler_D_step_def power_divide; linarith)
qed

lemma residue_31_exact:
  fixes t :: real
  assumes t: "0 \<le> t" "t < 1/2"
  shows "safe_prefix 6 (31+t) \<longleftrightarrow> ((211/243) \<le> t \<and> t < (1/2))"
proof -
  have lo: "of_nat 31 \<le> (31::real)+t" using t by simp
  have hi: "(31::real)+t < of_nat 31+1/2" using t by simp
  show ?thesis
    unfolding safe_prefix_exact[OF lo hi] all_upto_six
    using t by (simp add: mahler_D_step_def power_divide; linarith)
qed

lemma residue_32_exact:
  fixes t :: real
  assumes t: "0 \<le> t" "t < 1/2"
  shows "safe_prefix 6 (32+t) \<longleftrightarrow> ((32/729) \<le> t \<and> t < (16/243))"
proof -
  have lo: "of_nat 32 \<le> (32::real)+t" using t by simp
  have hi: "(32::real)+t < of_nat 32+1/2" using t by simp
  show ?thesis
    unfolding safe_prefix_exact[OF lo hi] all_upto_six
    using t by (simp add: mahler_D_step_def power_divide; linarith)
qed

lemma residue_33_exact:
  fixes t :: real
  assumes t: "0 \<le> t" "t < 1/2"
  shows "safe_prefix 6 (33+t) \<longleftrightarrow> ((455/729) \<le> t \<and> t < (1/2))"
proof -
  have lo: "of_nat 33 \<le> (33::real)+t" using t by simp
  have hi: "(33::real)+t < of_nat 33+1/2" using t by simp
  show ?thesis
    unfolding safe_prefix_exact[OF lo hi] all_upto_six
    using t by (simp add: mahler_D_step_def power_divide; linarith)
qed

lemma residue_34_exact:
  fixes t :: real
  assumes t: "0 \<le> t" "t < 1/2"
  shows "safe_prefix 6 (34+t) \<longleftrightarrow> ((302/729) \<le> t \<and> t < (1/3))"
proof -
  have lo: "of_nat 34 \<le> (34::real)+t" using t by simp
  have hi: "(34::real)+t < of_nat 34+1/2" using t by simp
  show ?thesis
    unfolding safe_prefix_exact[OF lo hi] all_upto_six
    using t by (simp add: mahler_D_step_def power_divide; linarith)
qed

lemma residue_35_exact:
  fixes t :: real
  assumes t: "0 \<le> t" "t < 1/2"
  shows "safe_prefix 6 (35+t) \<longleftrightarrow> ((5/9) \<le> t \<and> t < (1/2))"
proof -
  have lo: "of_nat 35 \<le> (35::real)+t" using t by simp
  have hi: "(35::real)+t < of_nat 35+1/2" using t by simp
  show ?thesis
    unfolding safe_prefix_exact[OF lo hi] all_upto_six
    using t by (simp add: mahler_D_step_def power_divide; linarith)
qed

lemma residue_36_exact:
  fixes t :: real
  assumes t: "0 \<le> t" "t < 1/2"
  shows "safe_prefix 6 (36+t) \<longleftrightarrow> ((188/729) \<le> t \<and> t < (2/9))"
proof -
  have lo: "of_nat 36 \<le> (36::real)+t" using t by simp
  have hi: "(36::real)+t < of_nat 36+1/2" using t by simp
  show ?thesis
    unfolding safe_prefix_exact[OF lo hi] all_upto_six
    using t by (simp add: mahler_D_step_def power_divide; linarith)
qed

lemma residue_37_exact:
  fixes t :: real
  assumes t: "0 \<le> t" "t < 1/2"
  shows "safe_prefix 6 (37+t) \<longleftrightarrow> ((97/243) \<le> t \<and> t < (35/81))"
proof -
  have lo: "of_nat 37 \<le> (37::real)+t" using t by simp
  have hi: "(37::real)+t < of_nat 37+1/2" using t by simp
  show ?thesis
    unfolding safe_prefix_exact[OF lo hi] all_upto_six
    using t by (simp add: mahler_D_step_def power_divide; linarith)
qed

lemma residue_38_exact:
  fixes t :: real
  assumes t: "0 \<le> t" "t < 1/2"
  shows "safe_prefix 6 (38+t) \<longleftrightarrow> ((266/729) \<le> t \<and> t < (1/3))"
proof -
  have lo: "of_nat 38 \<le> (38::real)+t" using t by simp
  have hi: "(38::real)+t < of_nat 38+1/2" using t by simp
  show ?thesis
    unfolding safe_prefix_exact[OF lo hi] all_upto_six
    using t by (simp add: mahler_D_step_def power_divide; linarith)
qed

lemma residue_39_exact:
  fixes t :: real
  assumes t: "0 \<le> t" "t < 1/2"
  shows "safe_prefix 6 (39+t) \<longleftrightarrow> ((187/243) \<le> t \<and> t < (1/2))"
proof -
  have lo: "of_nat 39 \<le> (39::real)+t" using t by simp
  have hi: "(39::real)+t < of_nat 39+1/2" using t by simp
  show ?thesis
    unfolding safe_prefix_exact[OF lo hi] all_upto_six
    using t by (simp add: mahler_D_step_def power_divide; linarith)
qed

lemma residue_40_exact:
  fixes t :: real
  assumes t: "0 \<le> t" "t < 1/2"
  shows "safe_prefix 6 (40+t) \<longleftrightarrow> ((152/729) \<le> t \<and> t < (4/27))"
proof -
  have lo: "of_nat 40 \<le> (40::real)+t" using t by simp
  have hi: "(40::real)+t < of_nat 40+1/2" using t by simp
  show ?thesis
    unfolding safe_prefix_exact[OF lo hi] all_upto_six
    using t by (simp add: mahler_D_step_def power_divide; linarith)
qed

lemma residue_41_exact:
  fixes t :: real
  assumes t: "0 \<le> t" "t < 1/2"
  shows "safe_prefix 6 (41+t) \<longleftrightarrow> ((383/729) \<le> t \<and> t < (1/2))"
proof -
  have lo: "of_nat 41 \<le> (41::real)+t" using t by simp
  have hi: "(41::real)+t < of_nat 41+1/2" using t by simp
  show ?thesis
    unfolding safe_prefix_exact[OF lo hi] all_upto_six
    using t by (simp add: mahler_D_step_def power_divide; linarith)
qed

lemma residue_42_exact:
  fixes t :: real
  assumes t: "0 \<le> t" "t < 1/2"
  shows "safe_prefix 6 (42+t) \<longleftrightarrow> ((422/729) \<le> t \<and> t < (1/3))"
proof -
  have lo: "of_nat 42 \<le> (42::real)+t" using t by simp
  have hi: "(42::real)+t < of_nat 42+1/2" using t by simp
  show ?thesis
    unfolding safe_prefix_exact[OF lo hi] all_upto_six
    using t by (simp add: mahler_D_step_def power_divide; linarith)
qed

lemma residue_43_exact:
  fixes t :: real
  assumes t: "0 \<le> t" "t < 1/2"
  shows "safe_prefix 6 (43+t) \<longleftrightarrow> ((175/243) \<le> t \<and> t < (1/2))"
proof -
  have lo: "of_nat 43 \<le> (43::real)+t" using t by simp
  have hi: "(43::real)+t < of_nat 43+1/2" using t by simp
  show ?thesis
    unfolding safe_prefix_exact[OF lo hi] all_upto_six
    using t by (simp add: mahler_D_step_def power_divide; linarith)
qed

lemma residue_44_exact:
  fixes t :: real
  assumes t: "0 \<le> t" "t < 1/2"
  shows "safe_prefix 6 (44+t) \<longleftrightarrow> ((20/81) \<le> t \<and> t < (2/9))"
proof -
  have lo: "of_nat 44 \<le> (44::real)+t" using t by simp
  have hi: "(44::real)+t < of_nat 44+1/2" using t by simp
  show ?thesis
    unfolding safe_prefix_exact[OF lo hi] all_upto_six
    using t by (simp add: mahler_D_step_def power_divide; linarith)
qed

lemma residue_45_exact:
  fixes t :: real
  assumes t: "0 \<le> t" "t < 1/2"
  shows "safe_prefix 6 (45+t) \<longleftrightarrow> ((347/729) \<le> t \<and> t < (13/27))"
proof -
  have lo: "of_nat 45 \<le> (45::real)+t" using t by simp
  have hi: "(45::real)+t < of_nat 45+1/2" using t by simp
  show ?thesis
    unfolding safe_prefix_exact[OF lo hi] all_upto_six
    using t by (simp add: mahler_D_step_def power_divide; linarith)
qed

lemma residue_46_exact:
  fixes t :: real
  assumes t: "0 \<le> t" "t < 1/2"
  shows "safe_prefix 6 (46+t) \<longleftrightarrow> ((194/729) \<le> t \<and> t < (70/243))"
proof -
  have lo: "of_nat 46 \<le> (46::real)+t" using t by simp
  have hi: "(46::real)+t < of_nat 46+1/2" using t by simp
  show ?thesis
    unfolding safe_prefix_exact[OF lo hi] all_upto_six
    using t by (simp add: mahler_D_step_def power_divide; linarith)
qed

lemma residue_47_exact:
  fixes t :: real
  assumes t: "0 \<le> t" "t < 1/2"
  shows "safe_prefix 6 (47+t) \<longleftrightarrow> ((617/729) \<le> t \<and> t < (1/2))"
proof -
  have lo: "of_nat 47 \<le> (47::real)+t" using t by simp
  have hi: "(47::real)+t < of_nat 47+1/2" using t by simp
  show ?thesis
    unfolding safe_prefix_exact[OF lo hi] all_upto_six
    using t by (simp add: mahler_D_step_def power_divide; linarith)
qed

lemma residue_48_exact:
  fixes t :: real
  assumes t: "0 \<le> t" "t < 1/2"
  shows "safe_prefix 6 (48+t) \<longleftrightarrow> ((80/729) \<le> t \<and> t < (8/81))"
proof -
  have lo: "of_nat 48 \<le> (48::real)+t" using t by simp
  have hi: "(48::real)+t < of_nat 48+1/2" using t by simp
  show ?thesis
    unfolding safe_prefix_exact[OF lo hi] all_upto_six
    using t by (simp add: mahler_D_step_def power_divide; linarith)
qed

lemma residue_49_exact:
  fixes t :: real
  assumes t: "0 \<le> t" "t < 1/2"
  shows "safe_prefix 6 (49+t) \<longleftrightarrow> ((503/729) \<le> t \<and> t < (1/2))"
proof -
  have lo: "of_nat 49 \<le> (49::real)+t" using t by simp
  have hi: "(49::real)+t < of_nat 49+1/2" using t by simp
  show ?thesis
    unfolding safe_prefix_exact[OF lo hi] all_upto_six
    using t by (simp add: mahler_D_step_def power_divide; linarith)
qed

lemma residue_50_exact:
  fixes t :: real
  assumes t: "0 \<le> t" "t < 1/2"
  shows "safe_prefix 6 (50+t) \<longleftrightarrow> ((350/729) \<le> t \<and> t < (1/3))"
proof -
  have lo: "of_nat 50 \<le> (50::real)+t" using t by simp
  have hi: "(50::real)+t < of_nat 50+1/2" using t by simp
  show ?thesis
    unfolding safe_prefix_exact[OF lo hi] all_upto_six
    using t by (simp add: mahler_D_step_def power_divide; linarith)
qed

lemma residue_51_exact:
  fixes t :: real
  assumes t: "0 \<le> t" "t < 1/2"
  shows "safe_prefix 6 (51+t) \<longleftrightarrow> ((151/243) \<le> t \<and> t < (1/2))"
proof -
  have lo: "of_nat 51 \<le> (51::real)+t" using t by simp
  have hi: "(51::real)+t < of_nat 51+1/2" using t by simp
  show ?thesis
    unfolding safe_prefix_exact[OF lo hi] all_upto_six
    using t by (simp add: mahler_D_step_def power_divide; linarith)
qed

lemma residue_52_exact:
  fixes t :: real
  assumes t: "0 \<le> t" "t < 1/2"
  shows "safe_prefix 6 (52+t) \<longleftrightarrow> ((4/27) \<le> t \<and> t < (140/729))"
proof -
  have lo: "of_nat 52 \<le> (52::real)+t" using t by simp
  have hi: "(52::real)+t < of_nat 52+1/2" using t by simp
  show ?thesis
    unfolding safe_prefix_exact[OF lo hi] all_upto_six
    using t by (simp add: mahler_D_step_def power_divide; linarith)
qed

lemma residue_53_exact:
  fixes t :: real
  assumes t: "0 \<le> t" "t < 1/2"
  shows "safe_prefix 6 (53+t) \<longleftrightarrow> ((275/729) \<le> t \<and> t < (97/243))"
proof -
  have lo: "of_nat 53 \<le> (53::real)+t" using t by simp
  have hi: "(53::real)+t < of_nat 53+1/2" using t by simp
  show ?thesis
    unfolding safe_prefix_exact[OF lo hi] all_upto_six
    using t by (simp add: mahler_D_step_def power_divide; linarith)
qed

lemma residue_54_exact:
  fixes t :: real
  assumes t: "0 \<le> t" "t < 1/2"
  shows "safe_prefix 6 (54+t) \<longleftrightarrow> ((314/729) \<le> t \<and> t < (1/3))"
proof -
  have lo: "of_nat 54 \<le> (54::real)+t" using t by simp
  have hi: "(54::real)+t < of_nat 54+1/2" using t by simp
  show ?thesis
    unfolding safe_prefix_exact[OF lo hi] all_upto_six
    using t by (simp add: mahler_D_step_def power_divide; linarith)
qed

lemma residue_55_exact:
  fixes t :: real
  assumes t: "0 \<le> t" "t < 1/2"
  shows "safe_prefix 6 (55+t) \<longleftrightarrow> ((545/729) \<le> t \<and> t < (1/2))"
proof -
  have lo: "of_nat 55 \<le> (55::real)+t" using t by simp
  have hi: "(55::real)+t < of_nat 55+1/2" using t by simp
  show ?thesis
    unfolding safe_prefix_exact[OF lo hi] all_upto_six
    using t by (simp add: mahler_D_step_def power_divide; linarith)
qed

lemma residue_56_exact:
  fixes t :: real
  assumes t: "0 \<le> t" "t < 1/2"
  shows "safe_prefix 6 (56+t) \<longleftrightarrow> ((8/81) \<le> t \<and> t < (104/729))"
proof -
  have lo: "of_nat 56 \<le> (56::real)+t" using t by simp
  have hi: "(56::real)+t < of_nat 56+1/2" using t by simp
  show ?thesis
    unfolding safe_prefix_exact[OF lo hi] all_upto_six
    using t by (simp add: mahler_D_step_def power_divide; linarith)
qed

lemma residue_57_exact:
  fixes t :: real
  assumes t: "0 \<le> t" "t < 1/2"
  shows "safe_prefix 6 (57+t) \<longleftrightarrow> ((431/729) \<le> t \<and> t < (1/2))"
proof -
  have lo: "of_nat 57 \<le> (57::real)+t" using t by simp
  have hi: "(57::real)+t < of_nat 57+1/2" using t by simp
  show ?thesis
    unfolding safe_prefix_exact[OF lo hi] all_upto_six
    using t by (simp add: mahler_D_step_def power_divide; linarith)
qed

lemma residue_58_exact:
  fixes t :: real
  assumes t: "0 \<le> t" "t < 1/2"
  shows "safe_prefix 6 (58+t) \<longleftrightarrow> ((38/81) \<le> t \<and> t < (1/3))"
proof -
  have lo: "of_nat 58 \<le> (58::real)+t" using t by simp
  have hi: "(58::real)+t < of_nat 58+1/2" using t by simp
  show ?thesis
    unfolding safe_prefix_exact[OF lo hi] all_upto_six
    using t by (simp add: mahler_D_step_def power_divide; linarith)
qed

lemma residue_59_exact:
  fixes t :: real
  assumes t: "0 \<le> t" "t < 1/2"
  shows "safe_prefix 6 (59+t) \<longleftrightarrow> ((509/729) \<le> t \<and> t < (1/2))"
proof -
  have lo: "of_nat 59 \<le> (59::real)+t" using t by simp
  have hi: "(59::real)+t < of_nat 59+1/2" using t by simp
  show ?thesis
    unfolding safe_prefix_exact[OF lo hi] all_upto_six
    using t by (simp add: mahler_D_step_def power_divide; linarith)
qed

lemma residue_60_exact:
  fixes t :: real
  assumes t: "0 \<le> t" "t < 1/2"
  shows "safe_prefix 6 (60+t) \<longleftrightarrow> ((76/243) \<le> t \<and> t < (2/9))"
proof -
  have lo: "of_nat 60 \<le> (60::real)+t" using t by simp
  have hi: "(60::real)+t < of_nat 60+1/2" using t by simp
  show ?thesis
    unfolding safe_prefix_exact[OF lo hi] all_upto_six
    using t by (simp add: mahler_D_step_def power_divide; linarith)
qed

lemma residue_61_exact:
  fixes t :: real
  assumes t: "0 \<le> t" "t < 1/2"
  shows "safe_prefix 6 (61+t) \<longleftrightarrow> ((395/729) \<le> t \<and> t < (13/27))"
proof -
  have lo: "of_nat 61 \<le> (61::real)+t" using t by simp
  have hi: "(61::real)+t < of_nat 61+1/2" using t by simp
  show ?thesis
    unfolding safe_prefix_exact[OF lo hi] all_upto_six
    using t by (simp add: mahler_D_step_def power_divide; linarith)
qed

lemma residue_62_exact:
  fixes t :: real
  assumes t: "0 \<le> t" "t < 1/2"
  shows "safe_prefix 6 (62+t) \<longleftrightarrow> ((242/729) \<le> t \<and> t < (26/81))"
proof -
  have lo: "of_nat 62 \<le> (62::real)+t" using t by simp
  have hi: "(62::real)+t < of_nat 62+1/2" using t by simp
  show ?thesis
    unfolding safe_prefix_exact[OF lo hi] all_upto_six
    using t by (simp add: mahler_D_step_def power_divide; linarith)
qed

lemma residue_63_exact:
  fixes t :: real
  assumes t: "0 \<le> t" "t < 1/2"
  shows "safe_prefix 6 (63+t) \<longleftrightarrow> ((665/729) \<le> t \<and> t < (1/2))"
proof -
  have lo: "of_nat 63 \<le> (63::real)+t" using t by simp
  have hi: "(63::real)+t < of_nat 63+1/2" using t by simp
  show ?thesis
    unfolding safe_prefix_exact[OF lo hi] all_upto_six
    using t by (simp add: mahler_D_step_def power_divide; linarith)
qed

definition surviving_residues :: "nat set" where
  "surviving_residues = {0,4,6,9,13,14,16,20,21,24,30,32,37,45,46,52,53,56}"

definition rejected_residues :: "nat set" where
  "rejected_residues = {1,2,3,5,7,8,10,11,12,15,17,18,19,22,23,25,26,27,28,29,31,33,34,35,36,38,39,40,41,42,43,44,47,48,49,50,51,54,55,57,58,59,60,61,62,63}"

theorem residue_partition:
  assumes "r < 64"
  shows "r \<in> surviving_residues \<or> r \<in> rejected_residues"
  using assms
  by (simp add: surviving_residues_def rejected_residues_def; presburger)

theorem residue_counts:
  "card surviving_residues = 18" "card rejected_residues = 46"
  by (simp_all add: surviving_residues_def rejected_residues_def)

theorem rejected_residue_unsafe:
  fixes t :: real
  assumes r: "r \<in> rejected_residues" and t: "0 \<le> t" "t < 1/2"
  shows "\<not> safe_prefix 6 (of_nat r+t)"
  using r t
  by (auto simp: rejected_residues_def residue_1_exact residue_2_exact residue_3_exact residue_5_exact residue_7_exact residue_8_exact residue_10_exact residue_11_exact residue_12_exact residue_15_exact residue_17_exact residue_18_exact residue_19_exact residue_22_exact residue_23_exact residue_25_exact residue_26_exact residue_27_exact residue_28_exact residue_29_exact residue_31_exact residue_33_exact residue_34_exact residue_35_exact residue_36_exact residue_38_exact residue_39_exact residue_40_exact residue_41_exact residue_42_exact residue_43_exact residue_44_exact residue_47_exact residue_48_exact residue_49_exact residue_50_exact residue_51_exact residue_54_exact residue_55_exact residue_57_exact residue_58_exact residue_59_exact residue_60_exact residue_61_exact residue_62_exact residue_63_exact)

theorem rejected_cylinder_unsafe:
  fixes t :: real and k :: nat
  assumes "r \<in> rejected_residues" "0 \<le> t" "t < 1/2"
  shows "\<not> safe_prefix 6 (of_nat r + 64*of_nat k + t)"
  using rejected_residue_unsafe[OF assms] six_step_translation[of "of_nat r+t" k]
  by (simp add: algebra_simps)

theorem rejected_cylinder_not_Z:
  fixes t :: real and k :: nat
  assumes "r \<in> rejected_residues" "0 \<le> t" "t < 1/2"
  shows "\<not> z_candidate (of_nat r + 64*of_nat k + t)"
  using rejected_cylinder_unsafe[OF assms] candidate_prefix by blast

theorem source_seven_not_Z:
  fixes t :: real and k :: nat
  assumes "0 \<le> t" "t < 1/2"
  shows "\<not> z_candidate (7 + 64*of_nat k + t)"
  using rejected_cylinder_not_Z[of 7 t k] assms
  by (simp add: rejected_residues_def)

theorem candidate_residue:
  assumes candidate: "z_candidate x"
  shows "nat (floor x) mod 64 \<in> surviving_residues"
proof -
  let ?D = "nat (floor x)"
  let ?r = "?D mod 64"
  let ?k = "?D div 64"
  have nat_eq: "?r + ?k * 64 = ?D" by (rule mod_div_mult_eq)
  have real_eq: "(of_nat ?D::real) = of_nat ?r + 64*of_nat ?k"
    using arg_cong[OF nat_eq, of "\<lambda>n. (of_nat n::real)"]
    by (simp only: of_nat_add of_nat_mult of_nat_numeral; linarith)
  have decomp: "x = of_nat ?r + 64*of_nat ?k + frac x"
    using candidate_integer_part(1)[OF candidate] real_eq by simp
  have not_rejected: "?r \<notin> rejected_residues"
    using rejected_cylinder_not_Z[of ?r "frac x" ?k]
      candidate_integer_part(2,3)[OF candidate] candidate decomp by auto
  show ?thesis
    using residue_partition[of ?r] not_rejected by simp
qed

theorem candidate_all_time_residues:
  assumes "z_candidate x"
  shows "\<forall>n::nat. nat (floor (x*(3/2)^n)) mod 64 \<in> surviving_residues"
  using candidate_residue candidate_scaled assms by blast

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms residue_0_exact residue_1_exact residue_2_exact residue_3_exact residue_4_exact residue_5_exact residue_6_exact residue_7_exact residue_8_exact residue_9_exact residue_10_exact residue_11_exact residue_12_exact residue_13_exact residue_14_exact residue_15_exact residue_16_exact residue_17_exact residue_18_exact residue_19_exact residue_20_exact residue_21_exact residue_22_exact residue_23_exact residue_24_exact residue_25_exact residue_26_exact residue_27_exact residue_28_exact residue_29_exact residue_30_exact residue_31_exact residue_32_exact residue_33_exact residue_34_exact residue_35_exact residue_36_exact residue_37_exact residue_38_exact residue_39_exact residue_40_exact residue_41_exact residue_42_exact residue_43_exact residue_44_exact residue_45_exact residue_46_exact residue_47_exact residue_48_exact residue_49_exact residue_50_exact residue_51_exact residue_52_exact residue_53_exact residue_54_exact residue_55_exact residue_56_exact residue_57_exact residue_58_exact residue_59_exact residue_60_exact residue_61_exact residue_62_exact residue_63_exact
      rejected_residue_unsafe rejected_cylinder_unsafe rejected_cylinder_not_Z
      source_seven_not_Z residue_partition residue_counts
      candidate_residue candidate_all_time_residues})
    then ()
    else error "Generated safety certificates depend on an oracle";
\<close>

end
