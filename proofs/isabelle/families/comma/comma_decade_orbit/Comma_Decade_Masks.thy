theory Comma_Decade_Masks
  imports Comma_Decade_Blocks.Comma_Decade_Blocks
begin

unbundle bit_operations_syntax

text \<open>Packed phase words use the pullback orientation: source phase r
reads the right block at r+n. Thus rotate_phase n is a right rotation of the
924-bit word. The same sign must be used by future-safety consumers.\<close>

definition comma_phase_member :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "comma_phase_member bits r = (r<924 \<and> bit bits r)"

definition comma_rotate_phase :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_rotate_phase n bits =
    (let k=n mod 924 in take_bit 924
      (drop_bit k (take_bit 924 bits) OR push_bit (924-k) (take_bit k bits)))"

lemma comma_rotate_phase_member:
  assumes phase: "r<924"
  shows "comma_phase_member (comma_rotate_phase n bits) r =
    comma_phase_member bits ((r+n) mod 924)"
proof -
  let ?k = "n mod 924"
  have k: "?k<924" by simp
  have reduce: "(r+n) mod 924=(r+?k) mod 924"
    by (simp only: mod_add_right_eq)
  show ?thesis
  proof (cases "r+?k<924")
    case True
    have below: "r<924-?k" using True by arith
    have index: "(r+n) mod 924=r+?k" using reduce True by simp
    show ?thesis using phase True below
      apply (simp only: index)
      by (simp add: comma_phase_member_def comma_rotate_phase_def Let_def
        bit_simps add.commute)
  next
    case False
    have lower: "924\<le>r+?k" using False by arith
    have upper: "r+?k-924<924" using phase k by arith
    have shift: "924-?k\<le>r" and small: "r-(924-?k)<?k"
      and position: "r-(924-?k)=r+?k-924"
      using phase k lower by arith+
    have split_index: "r+?k=(r+?k-924)+924" using lower by arith
    have modulo: "(r+?k) mod 924=r+?k-924"
    proof -
      have "(r+?k) mod 924=((r+?k-924)+924) mod 924"
        by (rule arg_cong[OF split_index])
      also have "...=r+?k-924" using upper by simp
      finally show ?thesis .
    qed
    have index: "(r+n) mod 924=r+?k-924" using reduce modulo by simp
    show ?thesis using phase False shift small position upper
      apply (simp only: index)
      by (simp add: comma_phase_member_def comma_rotate_phase_def Let_def
        bit_simps add.commute)
  qed
qed

lemma comma_phase_member_zero [simp]:
  "comma_phase_member 0 r=False"
  by (simp add: comma_phase_member_def bit_simps)

lemma comma_phase_member_and:
  "comma_phase_member (A AND B) r = (comma_phase_member A r \<and> comma_phase_member B r)"
  by (auto simp: comma_phase_member_def bit_simps)

lemma comma_phase_member_or:
  "comma_phase_member (A OR B) r = (comma_phase_member A r \<or> comma_phase_member B r)"
  by (auto simp: comma_phase_member_def bit_simps)

fun comma_mask_union :: "nat list \<Rightarrow> nat" where
  "comma_mask_union []=0"
| "comma_mask_union (m#ms)=m OR comma_mask_union ms"

lemma comma_mask_union_member:
  "comma_phase_member (comma_mask_union masks) r =
    (\<exists>bits\<in>set masks. comma_phase_member bits r)"
  by (induction masks) (auto simp: comma_phase_member_def bit_simps)

text \<open>A local clock predicate has one shared packed-mask constructor.
The bit-list is a finite arithmetic definition, not a list of successor rows.
Symbolic sector construction can branch on these masks before any whole
phase/offset transition table is materialized.\<close>
definition comma_phase_mask :: "(nat \<Rightarrow> bool) \<Rightarrow> nat" where
  "comma_phase_mask P=horner_sum of_bool 2 (map P [0..<924])"

lemma comma_phase_mask_bit:
  "bit (comma_phase_mask P) r = (r<924 \<and> P r)"
  by (cases "r<924")
    (simp_all add: comma_phase_mask_def bit_horner_sum_bit_iff nth_map nth_upt)

lemma comma_phase_mask_member:
  "comma_phase_member (comma_phase_mask P) r = (r<924 \<and> P r)"
  by (simp add: comma_phase_member_def comma_phase_mask_bit)

definition comma_phase_class :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_phase_class period shift k=comma_phase_mask (\<lambda>r. (r+shift) mod period=k)"

lemma comma_phase_class_member:
  "comma_phase_member (comma_phase_class period shift k) r =
    (r<924 \<and> (r+shift) mod period=k)"
  by (simp add: comma_phase_class_def comma_phase_mask_member)

lemma comma_mask_union_bit:
  "bit (comma_mask_union masks) r = (\<exists>m\<in>set masks. bit m r)"
  by (induction masks) (auto simp: bit_simps)

lemma comma_phase_class_partition:
  assumes "0<period"
  shows "comma_mask_union (map (comma_phase_class period shift) [0..<period])=mask 924"
  by (rule bit_eqI)
    (use assms in \<open>auto simp: comma_mask_union_bit comma_phase_class_def comma_phase_mask_bit bit_simps\<close>)

lemma comma_phase_class_disjoint:
  assumes "j\<noteq>k"
  shows "comma_phase_class period shift j AND comma_phase_class period shift k=0"
  by (rule bit_eqI)
    (use assms in \<open>auto simp: comma_phase_class_def comma_phase_mask_bit bit_simps\<close>)

datatype comma_word_result = Comma_Word_Live nat
  | Comma_Word_Stop nat comma_decade_terminal | Comma_Word_Invalid

definition comma_word_then ::
  "nat \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> comma_word_result) \<Rightarrow>
    (nat \<Rightarrow> nat \<Rightarrow> comma_word_result) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> comma_word_result" where
  "comma_word_then n A B r i =
    (case A r i of Comma_Word_Live j \<Rightarrow>
      (case B ((r+n) mod 924) j of
        Comma_Word_Stop h terminal \<Rightarrow> Comma_Word_Stop (n+h) terminal
      | result \<Rightarrow> result)
    | result \<Rightarrow> result)"

definition comma_live_mask_compose ::
  "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> nat) \<Rightarrow>
    (nat \<Rightarrow> nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_live_mask_compose fibers n A B i k =
    comma_mask_union (map (\<lambda>j. A i j AND comma_rotate_phase n (B j k)) [0..<fibers])"

definition comma_stop_mask_compose ::
  "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> nat) \<Rightarrow>
    (nat \<Rightarrow> nat \<Rightarrow> comma_decade_terminal \<Rightarrow> nat) \<Rightarrow>
    (nat \<Rightarrow> nat \<Rightarrow> comma_decade_terminal \<Rightarrow> nat) \<Rightarrow>
    nat \<Rightarrow> nat \<Rightarrow> comma_decade_terminal \<Rightarrow> nat" where
  "comma_stop_mask_compose fibers n live first second i h terminal =
    first i h terminal OR (if n\<le>h then
      comma_mask_union (map (\<lambda>j. live i j AND
        comma_rotate_phase n (second j (h-n) terminal)) [0..<fibers]) else 0)"

lemma comma_live_mask_compose_member:
  assumes "r<924"
  shows "comma_phase_member (comma_live_mask_compose fibers n A B i k) r =
    (\<exists>j<fibers. comma_phase_member (A i j) r \<and>
      comma_phase_member (B j k) ((r+n) mod 924))"
  using assms by (auto simp: comma_live_mask_compose_def comma_mask_union_member
    comma_phase_member_and comma_rotate_phase_member)

lemma comma_stop_mask_compose_member:
  assumes "r<924"
  shows "comma_phase_member (comma_stop_mask_compose fibers n live first second i h terminal) r =
    (comma_phase_member (first i h terminal) r \<or>
      (n\<le>h \<and> (\<exists>j<fibers. comma_phase_member (live i j) r \<and>
        comma_phase_member (second j (h-n) terminal) ((r+n) mod 924))))"
proof (cases "n\<le>h")
  case True
  show ?thesis using assms True
    by (auto simp: comma_stop_mask_compose_def comma_mask_union_member
      comma_phase_member_or comma_phase_member_and comma_rotate_phase_member)
next
  case False
  then show ?thesis
    by (auto simp: comma_stop_mask_compose_def comma_phase_member_def bit_simps)
qed

lemma comma_word_then_live:
  "comma_word_then n A B r i=Comma_Word_Live k \<longleftrightarrow>
    (\<exists>j. A r i=Comma_Word_Live j \<and> B ((r+n) mod 924) j=Comma_Word_Live k)"
  by (auto simp: comma_word_then_def split: comma_word_result.splits)

lemma comma_word_then_stop:
  "comma_word_then n A B r i=Comma_Word_Stop h terminal \<longleftrightarrow>
    (A r i=Comma_Word_Stop h terminal \<or>
      (n\<le>h \<and> (\<exists>j. A r i=Comma_Word_Live j \<and>
        B ((r+n) mod 924) j=Comma_Word_Stop (h-n) terminal)))"
  by (auto simp: comma_word_then_def split: comma_word_result.splits)

definition comma_word_masks_correct ::
  "(nat \<Rightarrow> nat \<Rightarrow> comma_word_result) \<Rightarrow>
    (nat \<Rightarrow> nat \<Rightarrow> nat) \<Rightarrow>
    (nat \<Rightarrow> nat \<Rightarrow> comma_decade_terminal \<Rightarrow> nat) \<Rightarrow> bool" where
  "comma_word_masks_correct F live stop =
    ((\<forall>r<924. \<forall>i j. comma_phase_member (live i j) r = (F r i=Comma_Word_Live j)) \<and>
     (\<forall>r<924. \<forall>i h terminal.
       comma_phase_member (stop i h terminal) r = (F r i=Comma_Word_Stop h terminal)))"

lemma comma_word_masks_compose_correct:
  assumes first: "comma_word_masks_correct A liveA stopA"
    and second: "comma_word_masks_correct B liveB stopB"
    and bounded: "\<And>r i j. r<924 \<Longrightarrow> A r i=Comma_Word_Live j \<Longrightarrow> j<fibers"
  shows "comma_word_masks_correct (comma_word_then n A B)
    (comma_live_mask_compose fibers n liveA liveB)
    (comma_stop_mask_compose fibers n liveA stopA stopB)"
  using first second bounded
  by (auto simp: comma_word_masks_correct_def comma_live_mask_compose_member
    comma_stop_mask_compose_member comma_word_then_live comma_word_then_stop; blast)

lemma comma_phase_rotation_wrap:
  "comma_phase_member (comma_rotate_phase 1 bits) 923=comma_phase_member bits 0"
  using comma_rotate_phase_member[of 923 1 bits] by simp

text \<open>A projected word keeps terminal height and label exactly. Source
fiber validity and live continuation congruence must come from the separately
checked orbit quotient; these definitions do not assert its 46-class bound.\<close>
fun comma_word_project :: "(nat \<Rightarrow> nat) \<Rightarrow> comma_decade_block_result \<Rightarrow> comma_word_result" where
  "comma_word_project fiber (Comma_Block_Live (Comma_Decade r x))=Comma_Word_Live (fiber x)"
| "comma_word_project fiber (Comma_Block_Stop h terminal)=Comma_Word_Stop h terminal"
| "comma_word_project fiber Comma_Block_Invalid=Comma_Word_Invalid"

lemma comma_word_project_stop_iff:
  "comma_word_project fiber result=Comma_Word_Stop h terminal \<longleftrightarrow>
    result=Comma_Block_Stop h terminal"
proof (cases result)
  case (Comma_Block_Live source)
  then show ?thesis by (cases source) simp
next
  case (Comma_Block_Stop height label)
  then show ?thesis by simp
next
  case Comma_Block_Invalid
  then show ?thesis by simp
qed

lemma comma_word_project_then:
  assumes phase: "r<924"
    and live: "\<And>r' x. left=Comma_Block_Live (Comma_Decade r' x) \<Longrightarrow>
      r'=(r+n) mod 924"
    and right: "\<And>r' x. left=Comma_Block_Live (Comma_Decade r' x) \<Longrightarrow>
      comma_word_project fiber (continuation (Comma_Decade r' x))=B r' (fiber x)"
  shows "comma_word_project fiber (comma_decade_block_then n left continuation)=
    comma_word_then n (\<lambda>_ _. comma_word_project fiber left) B r i"
proof (cases left)
  case (Comma_Block_Live source)
  obtain r' x where source: "source=Comma_Decade r' x"
    by (cases source) auto
  have left: "left=Comma_Block_Live (Comma_Decade r' x)"
    using Comma_Block_Live source by simp
  have phase': "r'=(r+n) mod 924" by (rule live[OF left])
  have projected: "B ((r+n) mod 924) (fiber x)=
      comma_word_project fiber (continuation (Comma_Decade r' x))"
    using right[OF left] phase' by simp
  show ?thesis
  proof (cases "continuation (Comma_Decade r' x)")
    case (Comma_Block_Live target)
    obtain r'' x' where target: "target=Comma_Decade r'' x'"
      by (cases target) auto
    show ?thesis by (simp add: left comma_word_then_def projected Comma_Block_Live target)
  next
    case (Comma_Block_Stop h terminal)
    then show ?thesis by (simp add: left comma_word_then_def projected)
  next
    case Comma_Block_Invalid
    then show ?thesis by (simp add: left comma_word_then_def projected)
  qed
next
  case (Comma_Block_Stop h terminal)
  then show ?thesis by (simp add: comma_word_then_def)
next
  case Comma_Block_Invalid
  then show ?thesis by (simp add: comma_word_then_def)
qed

theorem comma_word_project_square:
  assumes valid: "comma_decade_admitted (Comma_Decade r x)"
    and refinement: "\<And>phase offset. comma_decade_admitted (Comma_Decade phase offset) \<Longrightarrow>
      comma_word_project fiber (comma_decade_block_power k (Comma_Decade phase offset))=
        A phase (fiber offset)"
  shows "comma_word_project fiber (comma_decade_block_power (Suc k) (Comma_Decade r x))=
    comma_word_then (2^k) A A r (fiber x)"
proof -
  let ?left = "comma_decade_block_power k (Comma_Decade r x)"
  have phase: "r<924" using valid by simp
  have initial: "comma_word_project fiber ?left=A r (fiber x)"
    by (rule refinement[OF valid])
  have advance: "\<And>r' x'. ?left=Comma_Block_Live (Comma_Decade r' x') \<Longrightarrow>
      r'=(r+2^k) mod 924"
    using comma_decade_block_power_live_helix[OF valid] by blast
  have right: "\<And>r' x'. ?left=Comma_Block_Live (Comma_Decade r' x') \<Longrightarrow>
      comma_word_project fiber (comma_decade_block_power k (Comma_Decade r' x'))=A r' (fiber x')"
  proof -
    fix r' x' assume live: "?left=Comma_Block_Live (Comma_Decade r' x')"
    have helix: "r'=(r+2^k) mod 924 \<and> x'\<le>90"
      by (rule comma_decade_block_power_live_helix[OF valid live])
    have target: "comma_decade_admitted (Comma_Decade r' x')" using helix by simp
    show "comma_word_project fiber (comma_decade_block_power k (Comma_Decade r' x'))=A r' (fiber x')"
      by (rule refinement[OF target])
  qed
  have transport: "comma_word_project fiber
      (comma_decade_block_then (2^k) ?left (comma_decade_block_power k))=
    comma_word_then (2^k) (\<lambda>_ _. comma_word_project fiber ?left) A r (fiber x)"
    apply (rule comma_word_project_then[where r=r and n="2^k"
      and left="?left" and continuation="comma_decade_block_power k"
      and fiber=fiber and B=A and i="fiber x"])
      apply (rule phase)
     apply (rule advance, assumption)
    apply (rule right, assumption)
    done
  show ?thesis
    by (simp only: comma_decade_block_power.simps transport comma_word_then_def initial)
qed

lemma comma_phase_full_mask:
  "comma_phase_member (mask 924) r = (r<924)"
  by (auto simp: comma_phase_member_def bit_simps)

lemma comma_word_stops_from_mask_coverage:
  assumes correct: "comma_word_masks_correct F live stop"
    and phase: "r<924"
    and coverage: "comma_mask_union (map (\<lambda>(h,terminal). stop i h terminal) outputs)=mask 924"
    and bounds: "\<And>h terminal. (h,terminal)\<in>set outputs \<Longrightarrow> h\<le>bound"
  shows "\<exists>h terminal. F r i=Comma_Word_Stop h terminal \<and> h\<le>bound"
proof -
  have member: "comma_phase_member
      (comma_mask_union (map (\<lambda>(h,terminal). stop i h terminal) outputs)) r"
    using coverage phase by (simp only: comma_phase_full_mask)
  obtain h terminal where present: "(h,terminal)\<in>set outputs"
    and bit: "comma_phase_member (stop i h terminal) r"
    using member by (auto simp: comma_mask_union_member)
  have evaluated: "F r i=Comma_Word_Stop h terminal"
    using correct phase bit by (auto simp: comma_word_masks_correct_def)
  show ?thesis using evaluated bounds[OF present] by blast
qed

theorem comma_block_stops_from_mask_coverage:
  assumes valid: "comma_decade_admitted (Comma_Decade r x)"
    and refinement: "comma_word_project fiber (comma_decade_block_power k (Comma_Decade r x))=
      F r (fiber x)"
    and correct: "comma_word_masks_correct F live stop"
    and coverage: "comma_mask_union
      (map (\<lambda>(h,terminal). stop (fiber x) h terminal) outputs)=mask 924"
    and bounds: "\<And>h terminal. (h,terminal)\<in>set outputs \<Longrightarrow> h\<le>bound"
  shows "\<exists>h terminal. comma_decade_block_power k (Comma_Decade r x)=
    Comma_Block_Stop h terminal \<and> h\<le>bound"
proof -
  have phase: "r<924" using valid by simp
  have covered: "\<exists>h terminal. F r (fiber x)=Comma_Word_Stop h terminal \<and> h\<le>bound"
    apply (rule comma_word_stops_from_mask_coverage[where F=F and live=live
      and stop=stop and r=r and i="fiber x" and outputs=outputs and bound=bound])
       apply (rule correct)
      apply (rule phase)
     apply (rule coverage)
    apply (rule bounds, assumption)
    done
  obtain h terminal where terminal: "F r (fiber x)=Comma_Word_Stop h terminal" "h\<le>bound"
    using covered by blast
  have projected: "comma_word_project fiber
      (comma_decade_block_power k (Comma_Decade r x))=Comma_Word_Stop h terminal"
    using refinement terminal(1) by simp
  have raw: "comma_decade_block_power k (Comma_Decade r x)=Comma_Block_Stop h terminal"
    using projected by (simp only: comma_word_project_stop_iff)
  show ?thesis using raw terminal(2) by blast
qed

text \<open>The final mask coverage equations and base quotient refinement
remain proof obligations. No reported Python counts, sparse-mask numerals or
claimed 26-crossing bound are premises of a concrete checked instance here.\<close>

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_rotate_phase_member comma_live_mask_compose_member
      comma_stop_mask_compose_member comma_word_then_live comma_word_then_stop
      comma_word_project_then comma_word_masks_compose_correct comma_phase_rotation_wrap comma_word_project_square comma_word_stops_from_mask_coverage
      comma_block_stops_from_mask_coverage comma_phase_mask_bit
      comma_phase_class_partition comma_phase_class_disjoint}) then () else error "Temporal mask algebra depends on an oracle";
\<close>
end
