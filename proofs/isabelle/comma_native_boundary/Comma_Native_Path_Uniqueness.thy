theory Comma_Native_Path_Uniqueness
  imports Comma_Native_Future
begin

text \<open>For a fixed admitted native action, complete child list and checked
strict rank descent force the same next child on every infinite path. Strong
induction on the queried literal index then transports that uniqueness through
the child exponent and phase. The numerical rank rows are accepted only via
the supplied checked relation; outcomes and children are derived from the
native sparse action.\<close>

theorem comma_native_infinite_paths_agree:
  fixes rows :: "nat \<Rightarrow> comma_sparse_word"
    and rank :: "comma_boundary_state \<Rightarrow> nat option"
  assumes powers: "\<forall>i<46. comma_sparse_refines
      (\<lambda>r. comma_orbit_word 5 r i) (rows i)"
    and stops: "\<forall>i<46. \<forall>out bits. (out,bits)\<in>set (rows i) \<longrightarrow>
      (\<exists>h terminal. out=Comma_Word_Stop h terminal \<and> h\<le>26)"
    and checked: "comma_native_rank_check rank (comma_native_boundary_step rows)"
  shows "\<forall>q p left right. comma_boundary_valid q \<longrightarrow>
      5\<le>p \<longrightarrow> p mod 924=snd (snd q) \<longrightarrow>
      comma_native_infinite_literal_path (comma_boundary_value q p) left \<longrightarrow>
      comma_native_infinite_literal_path (comma_boundary_value q p) right \<longrightarrow>
      (\<forall>n. left n=right n)"
proof -
  have descend: "\<And>source exponent k a d child.
      comma_boundary_valid source \<Longrightarrow>
      5\<le>exponent \<Longrightarrow>
      exponent mod 924=snd (snd source) \<Longrightarrow>
      rank source=Some k \<Longrightarrow>
      comma_native_boundary_step rows source=Some (Comma_Fork_At a d) \<Longrightarrow>
      child\<in>set (comma_native_boundary_children source (Comma_Fork_At a d)) \<Longrightarrow>
      (\<exists>j<k. rank child=Some j)"
  proof -
    fix source exponent k a d child
    assume valid: "comma_boundary_valid source"
      and exponent: "5\<le>exponent"
      and phase: "exponent mod 924=snd (snd source)"
      and ranked: "rank source=Some k"
      and fork: "comma_native_boundary_step rows source=Some (Comma_Fork_At a d)"
      and member: "child\<in>set (comma_native_boundary_children source (Comma_Fork_At a d))"
    have all_ranked:
      "\<forall>v\<in>set (comma_native_boundary_children source (Comma_Fork_At a d)).
        \<exists>j<k. rank v=Some j"
      by (rule comma_native_rank_check_fork_decreases[OF checked valid ranked fork])
    show "\<exists>j<k. rank child=Some j"
      using all_ranked member by blast
  qed
  have ranked_no_path: "\<And>state exponent k trace.
      comma_boundary_valid state \<Longrightarrow>
      5\<le>exponent \<Longrightarrow>
      exponent mod 924=snd (snd state) \<Longrightarrow>
      rank state=Some k \<Longrightarrow>
      \<not>comma_native_infinite_literal_path
        (comma_boundary_value state exponent) trace"
    by (rule comma_native_ranked_state_no_infinite_path[OF powers stops descend])
  ML_prf \<open>Comma_Native_Boundary_Profile.checkpoint "path-agreement-rank-setup"\<close>
  let ?P = "\<lambda>n. \<forall>q p left right.
      comma_boundary_valid q \<longrightarrow>
      5\<le>p \<longrightarrow>
      p mod 924=snd (snd q) \<longrightarrow>
      comma_native_infinite_literal_path (comma_boundary_value q p) left \<longrightarrow>
      comma_native_infinite_literal_path (comma_boundary_value q p) right \<longrightarrow>
      left n=right n"
  have all_indices: "?P n" for n
  proof (induction n rule: less_induct)
    case (less n)
    show ?case
    proof (intro allI impI)
      fix q p left right
      assume valid: "comma_boundary_valid q"
        and exponent: "5\<le>p"
        and phase: "p mod 924=snd (snd q)"
        and left_path: "comma_native_infinite_literal_path
          (comma_boundary_value q p) left"
        and right_path: "comma_native_infinite_literal_path
          (comma_boundary_value q p) right"
      have left_start: "left 0=comma_boundary_value q p"
        using left_path by (auto simp: comma_native_infinite_literal_path_def)
      have left_edges: "comma_child (left j) (left (Suc j))" for j
        using left_path by (auto simp: comma_native_infinite_literal_path_def)
      have right_start: "right 0=comma_boundary_value q p"
        using right_path by (auto simp: comma_native_infinite_literal_path_def)
      have right_edges: "comma_child (right j) (right (Suc j))" for j
        using right_path by (auto simp: comma_native_infinite_literal_path_def)
      obtain outcome endpoint weight where native_step:
          "comma_native_boundary_step rows q=Some outcome"
        and native_children:
          "comma_native_boundary_children q outcome =
            (case outcome of Comma_Landmine_At d \<Rightarrow> []
             | Comma_Fork_At a d \<Rightarrow>
                [(Comma_N,a,(snd (snd q)+d) mod 924),
                 (Comma_Z,a,(snd (snd q)+d) mod 924)])"
        and unique_prefix:
          "comma_unique_literal_path weight (comma_boundary_value q p) endpoint"
        and child_relation: "\<And>v. comma_child endpoint v \<longleftrightarrow>
          (\<exists>child\<in>set (comma_native_boundary_children q outcome).
            v=comma_boundary_value child
              (p+comma_native_outcome_delta outcome))"
        proof (rule comma_sparse_boundary_ordered_occurrence_step
            [OF powers stops valid exponent phase])
          fix found_outcome found_endpoint found_weight
          assume found_step:
              "comma_native_boundary_step rows q=Some found_outcome"
            and found_children:
              "comma_native_boundary_children q found_outcome =
                (case found_outcome of Comma_Landmine_At d \<Rightarrow> []
                 | Comma_Fork_At a d \<Rightarrow>
                    [(Comma_N,a,(snd (snd q)+d) mod 924),
                     (Comma_Z,a,(snd (snd q)+d) mod 924)])"
            and found_unique:
              "comma_unique_literal_path found_weight
                (comma_boundary_value q p) found_endpoint"
            and found_child_relation: "\<And>v. comma_child found_endpoint v \<longleftrightarrow>
              (\<exists>child\<in>set (comma_native_boundary_children q found_outcome).
                v=comma_boundary_value child
                  (p+comma_native_outcome_delta found_outcome))"
          show thesis by (rule that[OF found_step found_children found_unique
            found_child_relation])
        qed
      ML_prf \<open>Comma_Native_Boundary_Profile.checkpoint "path-agreement-occurrence"\<close>
      have left_prefix: "comma_literal_path weight
          (comma_boundary_value q p) (left weight)"
        using comma_infinite_literal_prefix[where path=left and n=weight,
          OF left_edges] left_start by simp
      have right_prefix: "comma_literal_path weight
          (comma_boundary_value q p) (right weight)"
        using comma_infinite_literal_prefix[where path=right and n=weight,
          OF right_edges] right_start by simp
      have left_endpoint: "left weight=endpoint"
        using comma_unique_literal_path_endpoint[OF unique_prefix left_prefix] .
      have right_endpoint: "right weight=endpoint"
        using comma_unique_literal_path_endpoint[OF unique_prefix right_prefix] .
      show "left n=right n"
      proof (cases "n\<le>weight")
        case True
        obtain middle where unique_n:
            "comma_unique_literal_path n (comma_boundary_value q p) middle"
          using comma_unique_literal_path_prefix[OF unique_prefix True] by blast
        ML_prf \<open>Comma_Native_Boundary_Profile.checkpoint "path-agreement-short-prefix"\<close>
        have left_n: "comma_literal_path n (comma_boundary_value q p) (left n)"
          using comma_infinite_literal_prefix[where path=left and n=n,
            OF left_edges] left_start by simp
        have right_n: "comma_literal_path n (comma_boundary_value q p) (right n)"
          using comma_infinite_literal_prefix[where path=right and n=n,
            OF right_edges] right_start by simp
        have left_eq: "left n=middle"
          using comma_unique_literal_path_endpoint[OF unique_n left_n] .
        have right_eq: "right n=middle"
          using comma_unique_literal_path_endpoint[OF unique_n right_n] .
        show ?thesis using left_eq right_eq by simp
      next
        case False
        have weight_before: "Suc weight\<le>n" using False by arith
        let ?m = "n - Suc weight"
        have n_split: "n=Suc weight+?m"
          using weight_before by arith
        have m_less: "?m<n" using weight_before by arith
        have left_edge_after_prefix:
            "comma_child endpoint (left (Suc weight))"
          using left_edges[of weight] left_endpoint by simp
        have right_edge_after_prefix:
            "comma_child endpoint (right (Suc weight))"
          using right_edges[of weight] right_endpoint by simp
        obtain left_child where left_member:
            "left_child\<in>set (comma_native_boundary_children q outcome)"
          and left_value:
            "left (Suc weight)=comma_boundary_value left_child
              (p+comma_native_outcome_delta outcome)"
          using child_relation left_edge_after_prefix by blast
        obtain right_child where right_member:
            "right_child\<in>set (comma_native_boundary_children q outcome)"
          and right_value:
            "right (Suc weight)=comma_boundary_value right_child
              (p+comma_native_outcome_delta outcome)"
          using child_relation right_edge_after_prefix by blast
        ML_prf \<open>Comma_Native_Boundary_Profile.checkpoint "path-agreement-child-observations"\<close>
        obtain outcome' where valid_children_step:
            "comma_native_boundary_step rows q=Some outcome'"
          and valid_children:
            "\<forall>child\<in>set (comma_native_boundary_children q outcome').
              comma_boundary_valid child \<and>
              (p+comma_native_outcome_delta outcome') mod 924=snd (snd child)"
        proof (rule comma_native_boundary_step_children_valid_phase
            [OF powers stops valid exponent phase])
          fix found_outcome
          assume found_step:
              "comma_native_boundary_step rows q=Some found_outcome"
            and found_valid_children:
              "\<forall>child\<in>set (comma_native_boundary_children q found_outcome).
                comma_boundary_valid child \<and>
                (p+comma_native_outcome_delta found_outcome) mod 924=snd (snd child)"
          show thesis by (rule that[OF found_step found_valid_children])
        qed
        have outcome_eq: "outcome'=outcome"
          using native_step valid_children_step by simp
        have fork_outcome: "\<exists>a d. outcome=Comma_Fork_At a d"
        proof (cases outcome)
          case (Comma_Landmine_At d)
          then show ?thesis using left_member native_children by simp
        next
          case (Comma_Fork_At a d)
          then show ?thesis by blast
        qed
        obtain a d where fork: "outcome=Comma_Fork_At a d"
          using fork_outcome by blast
        have fork_step:
            "comma_native_boundary_step rows q=Some (Comma_Fork_At a d)"
          using native_step fork by simp
        have left_member':
            "left_child\<in>set (comma_native_boundary_children q outcome')"
          using left_member outcome_eq by simp
        have right_member':
            "right_child\<in>set (comma_native_boundary_children q outcome')"
          using right_member outcome_eq by simp
        have left_props:
            "comma_boundary_valid left_child \<and>
             (p+comma_native_outcome_delta outcome') mod 924=snd (snd left_child)"
          by (rule bspec[OF valid_children left_member'])
        have right_props:
            "comma_boundary_valid right_child \<and>
             (p+comma_native_outcome_delta outcome') mod 924=snd (snd right_child)"
          by (rule bspec[OF valid_children right_member'])
        have left_valid: "comma_boundary_valid left_child"
          using left_props by blast
        have left_phase: "(p+d) mod 924=snd (snd left_child)"
          using left_props outcome_eq fork by (simp add: comma_native_outcome_delta_def)
        have right_valid: "comma_boundary_valid right_child"
          using right_props by blast
        have right_phase: "(p+d) mod 924=snd (snd right_child)"
          using right_props outcome_eq fork by (simp add: comma_native_outcome_delta_def)
        have next_exponent: "5\<le>p+d" using exponent by simp
        let ?left_tail = "\<lambda>j. left (Suc weight+j)"
        let ?right_tail = "\<lambda>j. right (Suc weight+j)"
        have left_tail_start:
            "?left_tail 0=comma_boundary_value left_child (p+d)"
          using left_value fork by (simp add: comma_native_outcome_delta_def)
        have right_tail_start:
            "?right_tail 0=comma_boundary_value right_child (p+d)"
          using right_value fork by (simp add: comma_native_outcome_delta_def)
        have left_tail_edges:
            "comma_child (?left_tail j) (?left_tail (Suc j))" for j
          using left_edges[of "Suc weight+j"] by (simp add: add.assoc)
        have right_tail_edges:
            "comma_child (?right_tail j) (?right_tail (Suc j))" for j
          using right_edges[of "Suc weight+j"] by (simp add: add.assoc)
        have left_tail:
            "comma_native_infinite_literal_path
              (comma_boundary_value left_child (p+d)) ?left_tail"
          using left_tail_start left_tail_edges
          by (simp add: comma_native_infinite_literal_path_def)
        have right_tail:
            "comma_native_infinite_literal_path
              (comma_boundary_value right_child (p+d)) ?right_tail"
          using right_tail_start right_tail_edges
          by (simp add: comma_native_infinite_literal_path_def)
        have q_unranked: "rank q=None"
        proof (cases "rank q")
          case None then show ?thesis .
        next
          case (Some k)
          have no_path: "\<not>comma_native_infinite_literal_path
              (comma_boundary_value q p) left"
            by (rule ranked_no_path[OF valid exponent phase Some])
          show ?thesis using no_path left_path by contradiction
        qed
        have left_unranked: "rank left_child=None"
        proof (cases "rank left_child")
          case None then show ?thesis .
        next
          case (Some k)
          have no_tail: "\<not>comma_native_infinite_literal_path
              (comma_boundary_value left_child (p+d)) ?left_tail"
            by (rule ranked_no_path[OF left_valid next_exponent left_phase Some])
          show ?thesis using no_tail left_tail by contradiction
        qed
        have right_unranked: "rank right_child=None"
        proof (cases "rank right_child")
          case None then show ?thesis .
        next
          case (Some k)
          have no_tail: "\<not>comma_native_infinite_literal_path
              (comma_boundary_value right_child (p+d)) ?right_tail"
            by (rule ranked_no_path[OF right_valid next_exponent right_phase Some])
          show ?thesis using no_tail right_tail by contradiction
        qed
        obtain only where only_member:
            "only\<in>set (comma_native_boundary_children q (Comma_Fork_At a d))"
          and only_unranked: "rank only=None"
          and only_unique: "\<And>other. other\<in>
              set (comma_native_boundary_children q (Comma_Fork_At a d)) \<Longrightarrow>
              rank other=None \<Longrightarrow> other=only"
          using comma_native_rank_check_unranked_fork_unique
            [OF checked valid q_unranked fork_step] by blast
        have left_fork_member:
            "left_child\<in>set (comma_native_boundary_children q (Comma_Fork_At a d))"
          using left_member fork by simp
        have right_fork_member:
            "right_child\<in>set (comma_native_boundary_children q (Comma_Fork_At a d))"
          using right_member fork by simp
        have left_is_only: "left_child=only"
          by (rule only_unique[OF left_fork_member left_unranked])
        have right_is_only: "right_child=only"
          by (rule only_unique[OF right_fork_member right_unranked])
        have children_equal: "left_child=right_child"
          using left_is_only right_is_only by simp
        have smaller: "?P ?m" using less.IH[OF m_less] .
        have tail_equal: "?left_tail ?m=?right_tail ?m"
          using smaller left_valid next_exponent left_phase left_tail right_tail
            children_equal by blast
        show ?thesis using tail_equal n_split by simp
      qed
    qed
  qed
  show ?thesis
    using all_indices by blast
qed

ML \<open>
  val checked = @{thms comma_unique_literal_path_prefix
    comma_native_infinite_paths_agree}
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Native arbitrary-path uniqueness depends on an oracle"
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Native arbitrary-path uniqueness" checked
\<close>

end
