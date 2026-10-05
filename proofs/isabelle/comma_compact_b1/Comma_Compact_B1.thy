theory Comma_Compact_B1
  imports Comma_Decisive_Endpoint_Quotient.Comma_Decisive_Endpoint_Quotient
    Comma_Phase_Scope
begin

unbundle bit_operations_syntax

text \<open>
The B1 data transform follows source-selected endpoint packets.  At each
admitted state it partitions only the incoming phase mask by that state's
checked short period.  One representative packet serves each part; terminal
parts are emitted directly and internal successors are processed recursively.
No 924-phase evaluator, response tree, or theorem-per-phase payload occurs in
this definition.
\<close>

definition comma_compact_packet_mask :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_compact_packet_mask scope period residue =
    scope AND comma_phase_class period 0 residue"

lemma comma_compact_packet_mask_member:
  assumes phase: "r<924" and period: "0<period"
  shows "comma_phase_member (comma_compact_packet_mask scope period residue) r \<longleftrightarrow>
    (comma_phase_member scope r \<and> r mod period=residue)"
  using assms by (simp add: comma_compact_packet_mask_def comma_phase_class_member
    comma_phase_member_and)

datatype comma_compact_b1_plan =
    Comma_Compact_B1_Empty
  | Comma_Compact_B1_Recur comma_finite_position nat
  | Comma_Compact_B1_Emit comma_round_result nat

definition comma_compact_b1_packet_plan ::
    "comma_finite_position \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> comma_compact_b1_plan" where
  "comma_compact_b1_packet_plan source scope period residue =
    (let bits=comma_compact_packet_mask scope period residue in
       if bits=0 then Comma_Compact_B1_Empty
       else let packet=comma_decisive_endpoint_packet residue source;
                target=fst packet;
                move=snd packet
            in case move of
              Comma_Next next \<Rightarrow>
                if comma_round_crossing target next then
                  Comma_Compact_B1_Emit (Comma_Round_Cross next) bits
                else Comma_Compact_B1_Recur next bits
            | Comma_Fork a delta \<Rightarrow>
                Comma_Compact_B1_Emit (Comma_Round_Fork a delta) bits
            | Comma_Landmine delta \<Rightarrow>
                Comma_Compact_B1_Emit (Comma_Round_Landmine delta) bits
            | Comma_Invalid \<Rightarrow>
                Comma_Compact_B1_Emit Comma_Round_Invalid bits)"

definition comma_compact_b1_attach_rows ::
    "comma_compact_b1_plan \<Rightarrow> comma_sector_rows \<Rightarrow> comma_sector_rows" where
  "comma_compact_b1_attach_rows plan child_rows =
    (case plan of
       Comma_Compact_B1_Empty \<Rightarrow> []
     | Comma_Compact_B1_Recur next bits \<Rightarrow> child_rows
     | Comma_Compact_B1_Emit result bits \<Rightarrow> [(result,bits)])"

function comma_compact_b1_rows ::
    "comma_finite_position \<Rightarrow> nat \<Rightarrow> comma_sector_rows" where
  "comma_compact_b1_rows source scope =
    (let bounded_scope=take_bit 924 scope in
     if bounded_scope=0 then [] else if \<not> comma_round_admitted source then
       [(Comma_Round_Invalid,bounded_scope)]
     else let period=comma_decisive_sector_period source in
       concat (map (\<lambda>residue.
         let plan=comma_compact_b1_packet_plan source bounded_scope period residue in
         case plan of
           Comma_Compact_B1_Recur next bits \<Rightarrow>
             comma_compact_b1_attach_rows plan (comma_compact_b1_rows next bits)
         | _ \<Rightarrow> comma_compact_b1_attach_rows plan [])
         [0..<period]))"
  by pat_completeness auto

termination
  by (relation "measure (\<lambda>(source,scope). 9-comma_sector_number source)")
    (auto simp: comma_compact_b1_packet_plan_def comma_compact_b1_attach_rows_def
      comma_decisive_endpoint_packet_def Let_def
      intro: comma_decisive_endpoint_successor_decreases
      split: if_splits prod.splits comma_compact_b1_plan.splits comma_finite_move.splits)

declare comma_compact_b1_rows.simps [simp del]

lemma comma_compact_b1_attach_plan_eval:
  "(case plan of
      Comma_Compact_B1_Recur next bits \<Rightarrow>
        comma_compact_b1_attach_rows plan (children next bits)
    | _ \<Rightarrow> comma_compact_b1_attach_rows plan []) =
    (case plan of
      Comma_Compact_B1_Empty \<Rightarrow> []
    | Comma_Compact_B1_Recur next bits \<Rightarrow> children next bits
    | Comma_Compact_B1_Emit result bits \<Rightarrow> [(result,bits)])"
  by (cases plan) (simp_all add: comma_compact_b1_attach_rows_def)

lemma comma_compact_b1_rows_eval:
  "comma_compact_b1_rows source scope =
    (let bounded_scope=take_bit 924 scope in
     if bounded_scope=0 then [] else if \<not> comma_round_admitted source then
       [(Comma_Round_Invalid,bounded_scope)]
     else let period=comma_decisive_sector_period source in
       concat (map (\<lambda>residue.
         case comma_compact_b1_packet_plan source bounded_scope period residue of
           Comma_Compact_B1_Empty \<Rightarrow> []
         | Comma_Compact_B1_Recur next bits \<Rightarrow>
             comma_compact_b1_rows next bits
         | Comma_Compact_B1_Emit result bits \<Rightarrow> [(result,bits)])
         [0..<period]))"
proof -
  have rows_unfolded:
    "comma_compact_b1_rows source scope =
      (let bounded_scope=take_bit 924 scope in
       if bounded_scope=0 then [] else if \<not> comma_round_admitted source then
         [(Comma_Round_Invalid,bounded_scope)]
       else let period=comma_decisive_sector_period source in
         concat (map (\<lambda>residue.
           let plan=comma_compact_b1_packet_plan source bounded_scope period residue in
           case plan of
             Comma_Compact_B1_Recur next bits \<Rightarrow>
               comma_compact_b1_attach_rows plan
                 (comma_compact_b1_rows next bits)
           | _ \<Rightarrow> comma_compact_b1_attach_rows plan [])
           [0..<period]))"
    by (subst comma_compact_b1_rows.simps) (rule refl)
  show ?thesis
    using rows_unfolded
    by (simp only: Let_def comma_compact_b1_attach_plan_eval)
qed

lemma comma_compact_b1_concat_map_filter_empty:
  assumes empty: "\<And>x. x\<in>set xs \<Longrightarrow> \<not> P x \<Longrightarrow> f x=[]"
  shows "concat (map f (filter P xs))=concat (map f xs)"
  using empty by (induction xs) auto

lemma comma_compact_b1_rows_scope_eval:
  assumes source: "comma_round_admitted source"
    and scope: "comma_phase_scope_admitted p a"
  shows "comma_compact_b1_rows source (comma_phase_class p 0 a) =
    concat (map (\<lambda>residue.
      case comma_compact_b1_packet_plan source (comma_phase_class p 0 a)
          (comma_decisive_sector_period source) residue of
        Comma_Compact_B1_Empty \<Rightarrow> []
      | Comma_Compact_B1_Recur next bits \<Rightarrow>
          comma_compact_b1_rows next bits
      | Comma_Compact_B1_Emit result bits \<Rightarrow> [(result,bits)])
      (filter (\<lambda>residue.
        residue mod gcd p (comma_decisive_sector_period source) =
          a mod gcd p (comma_decisive_sector_period source))
        [0..<comma_decisive_sector_period source]))"
proof -
  let ?period = "comma_decisive_sector_period source"
  let ?compatible = "(\<lambda>residue. residue mod gcd p ?period = a mod gcd p ?period)"
  let ?rows = "(\<lambda>residue.
    case comma_compact_b1_packet_plan source (comma_phase_class p 0 a)
        ?period residue of
      Comma_Compact_B1_Empty \<Rightarrow> []
    | Comma_Compact_B1_Recur next bits \<Rightarrow> comma_compact_b1_rows next bits
    | Comma_Compact_B1_Emit result bits \<Rightarrow> [(result,bits)])"
  have period_pair:
    "0<?period \<and> ?period dvd 924"
    by (rule comma_decisive_sector_period_admitted_pair[OF source])
  have period_divides: "?period dvd 924" using period_pair by blast
  have period_bound: "?period\<le>924"
    by (rule dvd_imp_le[OF period_divides]) simp
  have period_scope:
    "comma_phase_scope_admitted ?period residue" if "residue<?period" for residue
    using period_pair period_bound that
    by (simp add: comma_phase_scope_admitted_def)
  have source_scope: "comma_phase_scope_admitted p a" by fact
  have bounded: "take_bit 924 (comma_phase_class p 0 a)=comma_phase_class p 0 a"
    by (rule comma_phase_scope_bounded)
  have nonzero: "comma_phase_class p 0 a\<noteq>0"
    by (rule comma_phase_scope_nonzero[OF scope])
  have all_rows:
    "comma_compact_b1_rows source (comma_phase_class p 0 a) =
      concat (map ?rows [0..<?period])"
    using comma_compact_b1_rows_eval[of source "comma_phase_class p 0 a"]
      source bounded nonzero by (simp add: Let_def)
  have excluded_empty:
    "?rows residue=[]" if "residue\<in>set [0..<?period]" "\<not> ?compatible residue"
    for residue
  proof -
    have residue_bound: "residue<?period" using that(1) by simp
    have incompatible:
      "a mod gcd p ?period \<noteq> residue mod gcd p ?period"
      using that(2) by auto
    have disjoint:
      "comma_phase_class p 0 a AND comma_phase_class ?period 0 residue=0"
      by (rule comma_phase_scope_disjoint[OF source_scope
          period_scope[OF residue_bound] incompatible])
    have mask_zero:
      "comma_compact_packet_mask (comma_phase_class p 0 a) ?period residue=0"
      using disjoint by (simp add: comma_compact_packet_mask_def)
    have plan_empty:
      "comma_compact_b1_packet_plan source (comma_phase_class p 0 a)
        ?period residue=Comma_Compact_B1_Empty"
      using mask_zero by (simp add: comma_compact_b1_packet_plan_def Let_def)
    show ?thesis using plan_empty by simp
  qed
  have filtered_rows:
    "concat (map ?rows (filter ?compatible [0..<?period])) =
      concat (map ?rows [0..<?period])"
    by (rule comma_compact_b1_concat_map_filter_empty[OF excluded_empty])
  show ?thesis using all_rows filtered_rows by simp
qed

lemma comma_compact_b1_packet_mask_width:
  "take_bit 924 (comma_compact_packet_mask scope period residue) =
    comma_compact_packet_mask scope period residue"
  unfolding comma_compact_packet_mask_def
  by (rule bit_eqI)
    (auto simp: bit_take_bit_iff comma_phase_class_def comma_phase_mask_bit bit_simps)

lemma comma_compact_b1_packet_plan_emit_mask_width:
  assumes plan:
    "comma_compact_b1_packet_plan source scope period residue =
      Comma_Compact_B1_Emit result bits"
  shows "take_bit 924 bits=bits"
  using plan
  by (auto simp: comma_compact_b1_packet_plan_def Let_def
      comma_compact_b1_packet_mask_width
      split: if_splits prod.splits comma_finite_move.splits)

text \<open>The source period theorem is the only phase-quotient premise used by
the constructor.  The endpoint packet theorem transports both target and move
across each residue class; the recursion measure is the decimal sector, not a
runtime fuel parameter.\<close>

lemma comma_compact_b1_packet_masks_union:
  assumes period: "0<period"
  shows "comma_mask_union
      (map (comma_compact_packet_mask scope period) [0..<period]) =
      take_bit 924 scope"
  by (rule bit_eqI)
    (use period in \<open>auto simp: comma_mask_union_bit
      comma_compact_packet_mask_def comma_phase_class_def
      comma_phase_mask_bit bit_and_iff bit_take_bit_iff\<close>)

lemma comma_compact_b1_scope_trim:
  "comma_phase_member (take_bit 924 scope) r=comma_phase_member scope r"
  by (auto simp: comma_phase_member_def bit_take_bit_iff)

lemma comma_compact_b1_rebind_rows:
  assumes rows: "comma_sector_rows_refine G scope rows"
    and agreement: "\<And>r. comma_phase_member scope r \<Longrightarrow> F r=G r"
  shows "comma_sector_rows_refine F scope rows"
  using rows agreement
  unfolding comma_sector_rows_refine_def by blast

lemma comma_compact_b1_packet_result:
  assumes admitted: "comma_round_admitted source"
    and period: "period=comma_decisive_sector_period source"
    and residue: "residue<period"
    and phase: "r<924"
    and member: "comma_phase_member
      (comma_compact_packet_mask scope period residue) r"
  shows "comma_decisive_endpoint_round r source =
    (case comma_compact_b1_packet_plan source scope period residue of
       Comma_Compact_B1_Empty \<Rightarrow> Comma_Round_Invalid
     | Comma_Compact_B1_Recur next bits \<Rightarrow>
         comma_decisive_endpoint_round r next
     | Comma_Compact_B1_Emit result bits \<Rightarrow> result)"
proof -
  have period_positive: "0<comma_decisive_sector_period source"
    by (rule comma_decisive_sector_period_admitted(1)[OF admitted])
  have packet_equal:
    "comma_decisive_endpoint_packet r source =
      comma_decisive_endpoint_packet residue source"
    by (rule comma_decisive_endpoint_packet_period[OF admitted])
      (use comma_compact_packet_mask_member[OF phase period_positive, of scope residue]
        member residue period in auto)
  have step:
    "comma_decisive_endpoint_round r source =
      (case comma_decisive_endpoint_packet r source of
        (target,Comma_Next next) \<Rightarrow>
          if comma_round_crossing target next then Comma_Round_Cross next
          else comma_decisive_endpoint_round r next
      | (target,Comma_Fork a delta) \<Rightarrow> Comma_Round_Fork a delta
      | (target,Comma_Landmine delta) \<Rightarrow> Comma_Round_Landmine delta
      | (target,Comma_Invalid) \<Rightarrow> Comma_Round_Invalid)"
    by (rule comma_decisive_endpoint_round_packet[OF admitted])
  have nonzero: "comma_compact_packet_mask scope period residue\<noteq>0"
    using member by (metis comma_phase_member_zero)
  show ?thesis
    using step packet_equal nonzero
    by (simp add: comma_compact_b1_packet_plan_def Let_def
      comma_compact_packet_mask_member split: prod.splits comma_finite_move.splits)
qed

lemma comma_compact_b1_piece_refines:
  assumes admitted: "comma_round_admitted source"
    and period: "period=comma_decisive_sector_period source"
    and residue: "residue<period"
    and recursive:
      "\<And>next bits. comma_compact_b1_packet_plan source scope period residue =
        Comma_Compact_B1_Recur next bits \<Longrightarrow>
        comma_sector_rows_refine
          (\<lambda>r. comma_decisive_endpoint_round r next) bits child_rows"
  shows "comma_sector_rows_refine
    (\<lambda>r. comma_decisive_endpoint_round r source)
    (comma_compact_packet_mask scope period residue)
    (comma_compact_b1_attach_rows
      (comma_compact_b1_packet_plan source scope period residue) child_rows)"
proof (cases "comma_compact_b1_packet_plan source scope period residue")
  case Comma_Compact_B1_Empty
  then have bits: "comma_compact_packet_mask scope period residue=0"
    by (auto simp: comma_compact_b1_packet_plan_def Let_def
      split: if_splits comma_finite_move.splits)
  show ?thesis
    using bits Comma_Compact_B1_Empty
    by (simp add: comma_sector_rows_refine_def comma_compact_b1_attach_rows_def)
next
  case (Comma_Compact_B1_Recur successor bits)
  have mask: "bits=comma_compact_packet_mask scope period residue"
    using Comma_Compact_B1_Recur
    by (auto simp: comma_compact_b1_packet_plan_def Let_def
      split: if_splits comma_finite_move.splits)
  have child:
    "comma_sector_rows_refine
      (\<lambda>r. comma_decisive_endpoint_round r successor) bits child_rows"
    by (rule recursive[OF Comma_Compact_B1_Recur])
  have agreement:
    "\<And>r. comma_phase_member bits r \<Longrightarrow>
      comma_decisive_endpoint_round r source =
      comma_decisive_endpoint_round r successor"
  proof -
    fix r
    assume member: "comma_phase_member bits r"
    have phase: "r<924"
      using member by (simp add: comma_phase_member_def)
    have packet_output:
      "comma_decisive_endpoint_round r source =
        (case comma_compact_b1_packet_plan source scope period residue of
          Comma_Compact_B1_Empty \<Rightarrow> Comma_Round_Invalid
        | Comma_Compact_B1_Recur target target_bits \<Rightarrow>
            comma_decisive_endpoint_round r target
        | Comma_Compact_B1_Emit result target_bits \<Rightarrow> result)"
      by (rule comma_compact_b1_packet_result[OF admitted period residue phase])
        (simp only: mask[symmetric] member)
    show "comma_decisive_endpoint_round r source =
        comma_decisive_endpoint_round r successor"
      using packet_output Comma_Compact_B1_Recur by simp
  qed
  have rebound:
    "comma_sector_rows_refine
      (\<lambda>r. comma_decisive_endpoint_round r source) bits child_rows"
    by (rule comma_compact_b1_rebind_rows[OF child agreement])
  show ?thesis
    using rebound mask Comma_Compact_B1_Recur
    by (simp add: comma_compact_b1_attach_rows_def)
next
  case (Comma_Compact_B1_Emit result bits)
  have mask: "bits=comma_compact_packet_mask scope period residue"
    using Comma_Compact_B1_Emit
    by (auto simp: comma_compact_b1_packet_plan_def Let_def split: if_splits
      prod.splits comma_finite_move.splits)
  have packet_output:
    "\<And>r. comma_phase_member bits r \<Longrightarrow>
      comma_decisive_endpoint_round r source=result"
  proof -
    fix r
    assume member: "comma_phase_member bits r"
    have phase: "r<924"
      using member by (simp add: comma_phase_member_def)
    have exact:
      "comma_decisive_endpoint_round r source =
        (case comma_compact_b1_packet_plan source scope period residue of
          Comma_Compact_B1_Empty \<Rightarrow> Comma_Round_Invalid
        | Comma_Compact_B1_Recur next target_bits \<Rightarrow>
            comma_decisive_endpoint_round r next
        | Comma_Compact_B1_Emit target_result target_bits \<Rightarrow> target_result)"
      by (rule comma_compact_b1_packet_result[OF admitted period residue phase])
        (simp only: mask[symmetric] member)
    show "comma_decisive_endpoint_round r source=result"
      using exact Comma_Compact_B1_Emit by simp
  qed
  show ?thesis
    using comma_sector_rows_singleton[OF packet_output] mask Comma_Compact_B1_Emit
    by (simp add: comma_compact_b1_attach_rows_def)
qed

lemma comma_compact_b1_recur_admitted_decreases:
  assumes source: "comma_round_admitted source"
    and plan: "comma_compact_b1_packet_plan source scope period residue =
      Comma_Compact_B1_Recur successor bits"
  shows "comma_round_admitted successor \<and>
    9-comma_sector_number successor < 9-comma_sector_number source"
proof -
  let ?packet = "comma_decisive_endpoint_packet residue source"
  have mask_nonzero: "comma_compact_packet_mask scope period residue \<noteq> 0"
    using plan by (auto simp: comma_compact_b1_packet_plan_def Let_def
      split: if_splits prod.splits comma_finite_move.splits)
  have packet_move: "snd ?packet=Comma_Next successor"
    and internal: "\<not> comma_round_crossing (fst ?packet) successor"
    using plan mask_nonzero by (auto simp: comma_compact_b1_packet_plan_def Let_def
      split: if_splits prod.splits comma_finite_move.splits)
  have target_admitted: "comma_round_admitted (fst ?packet)"
    by (rule comma_decisive_packet_target_admitted[OF source])
  have finite: "comma_finite_step (residue mod 924) (fst ?packet)=Comma_Next successor"
    using packet_move by (simp add: comma_decisive_endpoint_packet_def Let_def
      comma_fast_step_correct)
  have next_admitted: "comma_round_admitted successor"
    by (rule comma_round_next_admitted[OF target_admitted finite])
  have target_eq: "fst ?packet=comma_decisive_sector_target residue source"
    by (simp add: comma_decisive_endpoint_packet_def Let_def)
  have fast: "comma_fast_step (residue mod 924)
      (comma_decisive_sector_target residue source)=Comma_Next successor"
    using packet_move target_eq by (simp add: comma_decisive_endpoint_packet_def Let_def)
  have internal': "\<not> comma_round_crossing
      (comma_decisive_sector_target residue source) successor"
    using internal target_eq by simp
  have decrease: "9-comma_sector_number successor < 9-comma_sector_number source"
    by (rule comma_decisive_endpoint_successor_decreases[OF source fast internal'])
  show ?thesis using next_admitted decrease by blast
qed

lemma comma_compact_b1_attach_rows_masks_width:
  assumes emitted: "\<And>result bits. plan=Comma_Compact_B1_Emit result bits \<Longrightarrow>
      take_bit 924 bits=bits"
    and children: "\<forall>out bits. (out,bits)\<in>set child_rows \<longrightarrow>
      take_bit 924 bits=bits"
  shows "\<forall>out bits. (out,bits)\<in>
      set (comma_compact_b1_attach_rows plan child_rows) \<longrightarrow>
      take_bit 924 bits=bits"
  using emitted children
  by (cases plan)
    (auto simp: comma_compact_b1_attach_rows_def)

lemma comma_compact_b1_attach_distribute:
  "(case plan of
      Comma_Compact_B1_Recur successor bits \<Rightarrow>
        comma_compact_b1_attach_rows plan (children successor bits)
    | _ \<Rightarrow> comma_compact_b1_attach_rows plan []) =
    comma_compact_b1_attach_rows plan
      (case plan of
        Comma_Compact_B1_Recur successor bits \<Rightarrow> children successor bits
      | _ \<Rightarrow> [])"
  by (cases plan) simp_all

lemma comma_compact_b1_concat_masks_width:
  assumes pieces:
    "\<And>i out bits. i\<in>set indices \<Longrightarrow> (out,bits)\<in>set (rows i) \<Longrightarrow>
      take_bit 924 bits=bits"
  shows "\<forall>out bits. (out,bits)\<in>set (concat (map rows indices)) \<longrightarrow>
    take_bit 924 bits=bits"
  using pieces by auto

lemma comma_compact_b1_rows_masks_width_rank:
  "\<forall>source scope. 9-comma_sector_number source=n \<longrightarrow>
    (\<forall>out bits. (out,bits)\<in>set (comma_compact_b1_rows source scope) \<longrightarrow>
      take_bit 924 bits=bits)"
proof (induction n rule: less_induct)
  case (less n)
  show ?case
  proof (rule allI, rule allI, rule impI)
    fix source :: comma_finite_position and scope :: nat
    assume rank: "9-comma_sector_number source=n"
    let ?bounded = "take_bit 924 scope"
    show "\<forall>out bits. (out,bits)\<in>set (comma_compact_b1_rows source scope) \<longrightarrow>
        take_bit 924 bits=bits"
    proof (cases "?bounded=0")
      case True
      have empty: "comma_compact_b1_rows source scope=[]"
        using True by (subst comma_compact_b1_rows.simps) simp
      show ?thesis using empty by simp
    next
      case nonzero: False
      show ?thesis
      proof (cases "comma_round_admitted source")
        case False
        have invalid:
          "comma_compact_b1_rows source scope=[(Comma_Round_Invalid,?bounded)]"
          using False nonzero
          by (subst comma_compact_b1_rows.simps)
            (simp only: if_True if_False not_True_eq_False not_False_eq_True Let_def)
        show ?thesis using invalid by simp
      next
        case admitted: True
        let ?period = "comma_decisive_sector_period source"
        let ?plan = "\<lambda>i. comma_compact_b1_packet_plan source ?bounded ?period i"
        let ?children = "\<lambda>i. case ?plan i of
            Comma_Compact_B1_Recur successor bits \<Rightarrow>
              comma_compact_b1_rows successor bits
          | _ \<Rightarrow> []"
        let ?piece = "\<lambda>i. comma_compact_b1_attach_rows (?plan i) (?children i)"
        have child_width:
          "\<And>i successor bits.
            ?plan i=Comma_Compact_B1_Recur successor bits \<Longrightarrow>
            (\<forall>out child_bits. (out,child_bits)\<in>
              set (comma_compact_b1_rows successor bits) \<longrightarrow>
              take_bit 924 child_bits=child_bits)"
        proof -
          fix i successor bits
          assume recur: "?plan i=Comma_Compact_B1_Recur successor bits"
          have descent:
            "comma_round_admitted successor \<and>
              9-comma_sector_number successor<9-comma_sector_number source"
            by (rule comma_compact_b1_recur_admitted_decreases[OF admitted recur])
          have lower: "9-comma_sector_number successor<n"
            using descent rank by arith
          have IH:
            "\<forall>s t. 9-comma_sector_number s=9-comma_sector_number successor \<longrightarrow>
              (\<forall>out child_bits. (out,child_bits)\<in>set
                (comma_compact_b1_rows s t) \<longrightarrow>
                take_bit 924 child_bits=child_bits)"
            by (rule less.IH[OF lower])
          show "\<forall>out child_bits. (out,child_bits)\<in>
              set (comma_compact_b1_rows successor bits) \<longrightarrow>
              take_bit 924 child_bits=child_bits"
            using IH descent by blast
        qed
        have piece_width:
          "\<forall>i\<in>set [0..<?period]. \<forall>out bits. (out,bits)\<in>set (?piece i) \<longrightarrow>
            take_bit 924 bits=bits"
        proof (intro ballI allI impI)
          fix i out bits
          assume index: "i\<in>set [0..<?period]"
            and member: "(out,bits)\<in>set (?piece i)"
          have child_case:
            "\<forall>out child_bits. (out,child_bits)\<in>set (?children i) \<longrightarrow>
              take_bit 924 child_bits=child_bits"
          proof (cases "?plan i")
            case (Comma_Compact_B1_Recur successor child_bits)
            then show ?thesis
              using child_width[of i successor child_bits] by simp
          next
            case Comma_Compact_B1_Empty
            then show ?thesis by simp
          next
            case (Comma_Compact_B1_Emit result emitted_bits)
            then show ?thesis by simp
          qed
          have emitted_case:
            "\<And>result emitted_bits. ?plan i=Comma_Compact_B1_Emit result emitted_bits \<Longrightarrow>
              take_bit 924 emitted_bits=emitted_bits"
            by (rule comma_compact_b1_packet_plan_emit_mask_width)
          have shape:
            "\<forall>row_out row_bits. (row_out,row_bits)\<in>
              set (comma_compact_b1_attach_rows (?plan i) (?children i)) \<longrightarrow>
              take_bit 924 row_bits=row_bits"
            by (rule comma_compact_b1_attach_rows_masks_width
              [where plan="?plan i" and child_rows="?children i",
                OF emitted_case child_case])
          show "take_bit 924 bits=bits"
            using shape member
            by blast
        qed
        have rows_eq:
          "comma_compact_b1_rows source scope=concat (map ?piece [0..<?period])"
        proof -
          have "comma_compact_b1_rows source scope =
              concat (map (\<lambda>residue.
                let plan=comma_compact_b1_packet_plan source ?bounded ?period residue in
                case plan of
                  Comma_Compact_B1_Recur successor bits \<Rightarrow>
                    comma_compact_b1_attach_rows plan
                      (comma_compact_b1_rows successor bits)
                | _ \<Rightarrow> comma_compact_b1_attach_rows plan []) [0..<?period])"
            using admitted nonzero
            by (subst comma_compact_b1_rows.simps)
              (simp only: if_True if_False not_True_eq_False Let_def)
          then show ?thesis
            by (simp only: Let_def comma_compact_b1_attach_distribute)
        qed
        have joined_width:
          "\<forall>out bits. (out,bits)\<in>set (concat (map ?piece [0..<?period])) \<longrightarrow>
            take_bit 924 bits=bits"
          by (rule comma_compact_b1_concat_masks_width
            [where indices="[0..<?period]" and rows="?piece"])
            (rule piece_width[rule_format])
        show ?thesis by (subst rows_eq) (rule joined_width)
      qed
    qed
  qed
qed

lemma comma_compact_b1_rows_masks_width:
  "\<forall>out bits. (out,bits)\<in>set (comma_compact_b1_rows source scope) \<longrightarrow>
    take_bit 924 bits=bits"
proof -
  have rank: "9-comma_sector_number source=9-comma_sector_number source" by simp
  show ?thesis
    using comma_compact_b1_rows_masks_width_rank[of "9-comma_sector_number source"]
      rank by blast
qed


lemma comma_compact_b1_rows_refines_rank:
  "\<forall>source scope. 9-comma_sector_number source=n \<longrightarrow>
    comma_round_admitted source \<longrightarrow>
    comma_sector_rows_refine (\<lambda>r. comma_decisive_endpoint_round r source)
      scope (comma_compact_b1_rows source scope)"
proof (induction n rule: less_induct)
  case (less n)
  show ?case
  proof (intro allI impI)
    fix source :: comma_finite_position and scope :: nat
    assume rank: "9-comma_sector_number source=n"
      and admitted: "comma_round_admitted source"
    let ?bounded = "take_bit 924 scope"
    have trim: "\<And>r. comma_phase_member ?bounded r=comma_phase_member scope r"
      by (rule comma_compact_b1_scope_trim)
    show "comma_sector_rows_refine (\<lambda>r. comma_decisive_endpoint_round r source)
        scope (comma_compact_b1_rows source scope)"
    proof (cases "?bounded=0")
      case True
      have empty: "comma_compact_b1_rows source scope=[]"
        using True by (subst comma_compact_b1_rows.simps) simp
      show ?thesis using empty trim True
        by (auto simp: comma_sector_rows_refine_def)
    next
      case nonzero: False
      let ?period = "comma_decisive_sector_period source"
      have period_positive: "0<?period"
        by (rule comma_decisive_sector_period_admitted(1)[OF admitted])
      let ?plan = "\<lambda>i. comma_compact_b1_packet_plan source ?bounded ?period i"
      let ?mask = "\<lambda>i. comma_compact_packet_mask ?bounded ?period i"
      let ?children = "\<lambda>i. case ?plan i of
          Comma_Compact_B1_Recur next bits \<Rightarrow> comma_compact_b1_rows next bits
        | _ \<Rightarrow> []"
      let ?piece_rows = "\<lambda>i. comma_compact_b1_attach_rows (?plan i) (?children i)"
      let ?pieces = "map (\<lambda>i. (?mask i, ?piece_rows i)) [0..<?period]"
      have root_shape:
        "comma_compact_b1_rows source scope = concat (map (\<lambda>i.
          let plan=comma_compact_b1_packet_plan source ?bounded ?period i in
          case plan of
            Comma_Compact_B1_Recur next bits \<Rightarrow>
              comma_compact_b1_attach_rows plan (comma_compact_b1_rows next bits)
          | _ \<Rightarrow> comma_compact_b1_attach_rows plan []) [0..<?period])"
        using admitted nonzero
        by (subst comma_compact_b1_rows.simps) (simp only: if_True if_False not_True_eq_False Let_def)
      have root_pieces:
        "comma_compact_b1_rows source scope=concat (map snd ?pieces)"
      proof -
        have body_map:
          "map (\<lambda>i. let plan=comma_compact_b1_packet_plan source ?bounded ?period i in
              case plan of
                Comma_Compact_B1_Recur next bits \<Rightarrow>
                  comma_compact_b1_attach_rows plan (comma_compact_b1_rows next bits)
              | _ \<Rightarrow> comma_compact_b1_attach_rows plan []) [0..<?period] =
            map ?piece_rows [0..<?period]"
        proof (rule map_cong)
          show "[0..<?period]=[0..<?period]" by simp
          fix i
          assume "i\<in>set [0..<?period]"
          show "(let plan=comma_compact_b1_packet_plan source ?bounded ?period i in
              case plan of
                Comma_Compact_B1_Recur next bits \<Rightarrow>
                  comma_compact_b1_attach_rows plan (comma_compact_b1_rows next bits)
              | _ \<Rightarrow> comma_compact_b1_attach_rows plan []) = ?piece_rows i"
            by (cases "?plan i")
              (simp_all add: comma_compact_b1_attach_rows_def)
        qed
        have snd_pieces: "map snd ?pieces=map ?piece_rows [0..<?period]"
          by (simp add: map_map)
        show ?thesis by (simp only: root_shape body_map snd_pieces)
      qed
      have masks:
        "comma_mask_union (map fst ?pieces)=?bounded"
        using comma_compact_b1_packet_masks_union[OF period_positive]
        by (simp add: map_map o_def)
      have each_piece:
        "\<And>mask rows. (mask,rows)\<in>set ?pieces \<Longrightarrow>
          comma_sector_rows_refine
            (\<lambda>r. comma_decisive_endpoint_round r source) mask rows"
      proof -
        fix mask rows
        assume member: "(mask,rows)\<in>set ?pieces"
        then obtain i where index: "i<?period"
          and pair: "(mask,rows)=(?mask i,?piece_rows i)"
          by (auto simp: Let_def)
        have recursive:
          "\<And>next bits. ?plan i=Comma_Compact_B1_Recur next bits \<Longrightarrow>
            comma_sector_rows_refine
              (\<lambda>r. comma_decisive_endpoint_round r next)
              bits (?children i)"
        proof -
          fix successor bits
          assume recur: "?plan i=Comma_Compact_B1_Recur successor bits"
          have facts: "comma_round_admitted successor \<and>
              9-comma_sector_number successor<9-comma_sector_number source"
            by (rule comma_compact_b1_recur_admitted_decreases[OF admitted recur])
          have lower: "9-comma_sector_number successor<n"
            using facts rank by arith
          have IH:
            "\<forall>s t. 9-comma_sector_number s=9-comma_sector_number successor \<longrightarrow>
              comma_round_admitted s \<longrightarrow>
              comma_sector_rows_refine
                (\<lambda>r. comma_decisive_endpoint_round r s)
                t (comma_compact_b1_rows s t)"
            by (rule less.IH[OF lower])
          have exact_child:
            "comma_sector_rows_refine
              (\<lambda>r. comma_decisive_endpoint_round r successor)
              bits (comma_compact_b1_rows successor bits)"
            using IH facts by blast
          show "comma_sector_rows_refine
              (\<lambda>r. comma_decisive_endpoint_round r successor)
              bits (?children i)"
            using exact_child recur by (simp add: Let_def)
        qed
        have period_eq: "?period=comma_decisive_sector_period source" by simp
        have refined:
          "comma_sector_rows_refine
            (\<lambda>r. comma_decisive_endpoint_round r source)
            (?mask i) (?piece_rows i)"
          by (rule comma_compact_b1_piece_refines[OF admitted period_eq index recursive])
        show "comma_sector_rows_refine
            (\<lambda>r. comma_decisive_endpoint_round r source) mask rows"
          using pair refined by simp
      qed
      have joined:
        "comma_sector_rows_refine
          (\<lambda>r. comma_decisive_endpoint_round r source)
          ?bounded (comma_compact_b1_rows source scope)"
        using comma_sector_rows_concat[where pieces="?pieces", OF each_piece]
        by (simp only: masks root_pieces[symmetric])
      show ?thesis using joined trim
        by (auto simp: comma_sector_rows_refine_def)
    qed
  qed
qed

theorem comma_compact_b1_rows_refines:
  assumes admitted: "comma_round_admitted source"
  shows "comma_sector_rows_refine
    (\<lambda>r. comma_decisive_endpoint_round r source)
    scope (comma_compact_b1_rows source scope)"
proof -
  have rank: "9-comma_sector_number source=9-comma_sector_number source" by simp
  show ?thesis
    using comma_compact_b1_rows_refines_rank[of "9-comma_sector_number source"]
      rank admitted by blast
qed

definition comma_compact_b1_source_rows :: "nat \<Rightarrow> comma_sector_rows" where
  "comma_compact_b1_source_rows i =
    (if i<46 then
      comma_compact_b1_rows
        (Comma_Entry 1 0 (comma_offset_representatives!i)) (mask 924)
     else [(Comma_Round_Invalid,mask 924)])"

definition comma_compact_b1_sparse_base :: "nat \<Rightarrow> comma_sparse_word" where
  "comma_compact_b1_sparse_base i =
    (if i<46 then comma_sparse_sector_base comma_compact_b1_source_rows i
     else [(Comma_Word_Invalid,mask 924)])"

lemma comma_compact_b1_sparse_source_refines_orbit:
  assumes index: "i<46"
  shows "comma_sparse_refines (\<lambda>r. comma_orbit_word 0 r i)
    (comma_sparse_sector_base
      (\<lambda>_. comma_compact_b1_rows
        (Comma_Entry 1 0 (comma_offset_representatives!i)) (mask 924)) i)"
proof -
  let ?x = "comma_offset_representatives!i"
  let ?source = "Comma_Entry 1 0 ?x"
  let ?rows = "comma_compact_b1_rows ?source (mask 924)"
  let ?sparse = "comma_sparse_sector_base (\<lambda>_. ?rows) i"
  let ?F = "\<lambda>r. comma_decisive_endpoint_round r ?source"
  have offset: "?x\<le>90"
    by (rule comma_orbit_representative_index(1)[OF index])
  have admitted: "comma_round_admitted ?source"
    using offset by simp
  have rows: "comma_sector_rows_refine ?F (mask 924) ?rows"
    by (rule comma_compact_b1_rows_refines[OF admitted])
  have source_projection:
    "comma_sector_base_project (?F r)=comma_orbit_word 0 r i"
    if phase: "r<924" for r
  proof -
    have selector:
      "comma_decisive_B1 r i=comma_sector_base_project (?F r)"
      using phase index by (simp add: comma_decisive_B1_def comma_decisive_B1_source_def)
    have orbit: "comma_decisive_B1 r i=comma_orbit_word 0 r i"
      by (rule comma_decisive_B1_refines_orbit_word[OF phase index])
    show ?thesis using selector orbit by simp
  qed
  show ?thesis
    unfolding comma_sparse_refines_def
  proof (intro allI impI)
    fix r :: nat and out :: comma_word_result
    assume phase: "r<924"
    have has:
      "comma_sparse_has ?sparse r out =
        comma_phase_member
          (comma_sector_output_mask comma_sector_base_project out ?rows) r"
      by (simp add: comma_sparse_sector_base_has)
    have exact_output:
      "comma_phase_member
        (comma_sector_output_mask comma_sector_base_project out ?rows) r =
        (comma_sector_base_project (?F r)=out)"
      by (rule comma_sector_rows_exact_output[OF rows phase,
        where project=comma_sector_base_project and desired=out])
    show "comma_sparse_has ?sparse r out=(comma_orbit_word 0 r i=out)"
      using has exact_output source_projection[OF phase] by simp
  qed
qed

lemma comma_compact_b1_sparse_base_refines:
  assumes index: "i<46"
  shows "comma_sparse_refines
    (\<lambda>r. comma_orbit_word 0 r i) (comma_compact_b1_sparse_base i)"
proof -
  have base_eq:
    "comma_compact_b1_sparse_base i =
      comma_sparse_sector_base
        (\<lambda>_. comma_compact_b1_rows
          (Comma_Entry 1 0 (comma_offset_representatives!i)) (mask 924)) i"
    using index by (simp add: comma_compact_b1_sparse_base_def
      comma_compact_b1_source_rows_def comma_sparse_sector_base_def)
  show ?thesis
    using comma_compact_b1_sparse_source_refines_orbit[OF index] base_eq
    by simp
qed

theorem comma_compact_b1_sparse_power_refines:
  "comma_sparse_refines (\<lambda>r. comma_orbit_word k r i)
    (comma_sparse_power (comma_sparse_admit comma_compact_b1_sparse_base) k i)"
  by (rule comma_sparse_power_refines)
    (rule comma_compact_b1_sparse_base_refines)

ML \<open>
  val checked = @{thms comma_compact_b1_rows_masks_width comma_compact_b1_rows_refines
    comma_compact_b1_recur_admitted_decreases
    comma_compact_b1_sparse_base_refines comma_compact_b1_sparse_power_refines}
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Compact B1 endpoint rows depend on an oracle"
\<close>

end
