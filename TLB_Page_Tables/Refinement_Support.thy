theory   Refinement_Support
imports  L3_LIB.L3_Hoare_Logic
         MMU_Configuration
begin

notation (output) ARM_Monadic.lookup_type.Miss  ("Miss")
notation (output) ARM_Monadic.lookup_type.Incon ("Incon")
notation (output) ARM_Monadic.lookup_type.Hit   ("Hit")

lemma l3_valid_raise'exception[wp, intro!, simp]:
  "l3_valid (\<lambda>s. \<forall>r. P r (if exception s = NoException then s \<lparr>exception := e \<rparr> else s))
           (raise'exception e) P"
  by (wpsimp simp: raise'exception_def)

lemma undefined_False[wp]:
  "l3_valid (\<lambda>_. False) HOL.undefined Q'"
  by (simp add: l3_valid_def)

lemma if_chain [simp]:
  "(if P then f else if Q' then f else g) = (if P \<or> Q' then f else g)"
  by auto

lemma word_2_cases[simp]:
  "(w::2 word) = 0 \<or> w = 1 \<or> w = 2 \<or> w = 3"
  by word_bitwise auto

lemma word_3_cases[simp]:
  "(w::3 word) = 0 \<or>
   w = 1 \<or>
   w = 2 \<or>
   w = 3 \<or>
   w = 4 \<or>
   w = 5 \<or>
   w = 6 \<or>
   w = 7"
  by word_bitwise auto


definition
  "pre_cond s t va  \<equiv> 
          MMU_config_assert_isa s \<and>
          tlb_rel s (typ_tlb t) \<and>
          dtlb_consistent (typ_tlb t) (Addr va) \<and>
          unitlb_consistent (typ_tlb t) (Addr va) "



lemma word_cat_padr [simp]:
  "((ucast (padLr x) :: 32 word) << 16) || va && mask 16 = 
            ((word_cat (padLr x) ((word_extract 15 0 va) :: 16 word)) :: 32 word)"
  apply (clarsimp simp: word_extract_def word_bits_def mask_def) 
  by word_bitwise



lemma word_cat_padr' [simp]:
  "((ucast (padSec x) :: 32 word) << 20) || va && mask 20 = 
      ((word_cat (padSec x) ((word_extract 19 0 va) :: 20 word)) :: 32 word)"
  apply (clarsimp simp: word_extract_def word_bits_def mask_def) 
  by word_bitwise

lemma word_cat_padr'' [simp]:
  "((ucast (padSm x) :: 32 word) << 12) || va && mask 12 = 
      ((word_cat (padSm x) ((word_extract 11 0 va) :: 12 word)) :: 32 word)"
  apply (clarsimp simp: word_extract_def word_bits_def mask_def) 
  by word_bitwise

lemma word_cat_padr''' [simp]:
  "((ucast (padSup x) :: 32 word) << 24) || va && mask 24 = 
      ((word_cat (padSup x) ((word_extract 23 0 va) :: 24 word)) :: 32 word)"
  apply (clarsimp simp: word_extract_def word_bits_def mask_def) 
  by word_bitwise


lemma state_compD:
  "state_comp s t \<Longrightarrow> (ASID (CONTEXTIDR (CP15 s))) = asid t \<and> 
                   (\<lambda>p. (MEM s) (addr_val p)) = heap t \<and> 
                   (Addr (reg'TTBR0 (TTBR0 (CP15 s)))) = ttbr0 t \<and>
                   (reg'PRRR (PRRR (CP15 s))) = prrr t \<and>
                   (reg'NMRR (NMRR (CP15 s))) = nmrr t \<and>
                    excp_typcast(exception  s)  = excpt t"
  by (clarsimp simp: state_comp_def state.defs)

lemma tlb_relD:
  "tlb_rel s t \<Longrightarrow> (ASID (CONTEXTIDR (CP15 s))) = asid t \<and> 
                   (\<lambda>p. (MEM s) (addr_val p)) = heap t \<and> 
                   (Addr (reg'TTBR0 (TTBR0 (CP15 s)))) = ttbr0 t \<and>
                   (reg'PRRR (PRRR (CP15 s))) = prrr t \<and>
                   (reg'NMRR (NMRR (CP15 s))) = nmrr t \<and>
                    excp_typcast(exception  s)  = excpt t \<and>
                    tlbtypcast ` ran (micro_DataTLB s)  \<subseteq> dtlb_set (cstate.more t) \<and> 
                    tlbtypcast ` ran (micro_InstrTLB s) \<subseteq> itlb_set (cstate.more t) \<and> 
                    tlbtypcast ` ran (main_TLB s)       \<subseteq> unitlb_set (cstate.more t)"
  by (clarsimp simp: tlb_rel_def state_comp_def state.defs)


lemma tlb_rel_unitlb_consistent:
  "\<lbrakk>tlb_rel s (typ_tlb t); unitlb_consistent (typ_tlb t) (Addr va) \<rbrakk> \<Longrightarrow>
    consistent0 (\<lambda>p. (MEM s) (addr_val p)) (ASID (CONTEXTIDR (CP15 s)))
      (Addr (reg'TTBR0 (TTBR0 (CP15 s)))) (reg'PRRR (PRRR (CP15 s))) (reg'NMRR (NMRR (CP15 s)))
       (tlbtypcast ` ran (main_TLB s)) (Addr va)"
  apply (drule tlb_relD)
  apply (clarsimp simp: consistent0_def )
  apply (erule disjE)
  defer
  apply (metis leq_Miss tlb_mono)
  by (metis (full_types) TLB.lookup_type.simps(7) less_eq_lookup_type tlb_mono)


lemma tlb_rel_datatlb_consistent:
  "\<lbrakk>tlb_rel s (typ_tlb t); dtlb_consistent (typ_tlb t) (Addr va) \<rbrakk> \<Longrightarrow>
    consistent0 (\<lambda>p. (MEM s) (addr_val p)) (ASID (CONTEXTIDR (CP15 s)))
      (Addr (reg'TTBR0 (TTBR0 (CP15 s)))) (reg'PRRR (PRRR (CP15 s))) (reg'NMRR (NMRR (CP15 s)))
       (tlbtypcast ` ran (micro_DataTLB s)) (Addr va)"
  apply (drule tlb_relD)
  apply (clarsimp simp: consistent0_def )
  apply (erule disjE)
  defer
  apply (metis leq_Miss tlb_mono)
  by (metis (full_types) TLB.lookup_type.simps(7) less_eq_lookup_type tlb_mono)


lemma main_TLB_entry_some_lookup_not_miss:
  "\<lbrakk>main_TLB s i = Some entry; 
      MatchingEntry (ASID (CONTEXTIDR (CP15 s)), va, entry)\<rbrakk> \<Longrightarrow>
    lookup (tlbtypcast ` ran (main_TLB s)) (ASID (CONTEXTIDR (CP15 s))) va \<noteq> TLB.lookup_type.Miss"
  apply (subgoal_tac "entry_set (tlbtypcast ` ran (main_TLB s)) (ASID (CONTEXTIDR (CP15 s))) va \<noteq> {}")
   apply (clarsimp simp: lookup_def)
  apply (subgoal_tac "tlbtypcast entry \<in> (tlbtypcast ` ran (main_TLB s))")
   prefer 2
   apply (clarsimp simp: ran_def, blast)
  apply (clarsimp simp: entry_set_def)
  apply (rule_tac x = "tlbtypcast entry" in exI, clarsimp simp: MatchingEntry_def)
  apply (cases entry; clarsimp  split: if_split_asm)
         apply (rule_tac x = None in exI)
         apply (clarsimp simp: entry_range_tags_def entry_range_def)
         apply (case_tac "tlbtypcast x"; clarsimp simp: word_extract_def word_bits_def mask_def)
         apply (rule imageI,drule_tac t  = "vadLr x1" in sym, simp, word_bitwise)
        apply (rule_tac x = "Some (ASID (CONTEXTIDR (CP15 s)))" in exI)
        apply (clarsimp simp: entry_range_tags_def entry_range_def)
        apply (case_tac "tlbtypcast x"; clarsimp simp: word_extract_def word_bits_def mask_def)
        apply (rule imageI, drule_tac t  = "vadLr x1" in sym, simp, word_bitwise)
       apply (rule_tac x = None in exI)
       apply (clarsimp simp: entry_range_tags_def entry_range_def)
       apply (case_tac "tlbtypcast x"; clarsimp simp: word_extract_def word_bits_def mask_def)
       apply (rule imageI,drule_tac t  = "vadSec x2" in sym, simp, word_bitwise)
      apply (rule_tac x = "Some (ASID (CONTEXTIDR (CP15 s)))" in exI)
      apply (clarsimp simp: entry_range_tags_def entry_range_def)
      apply (case_tac "tlbtypcast x"; clarsimp simp: word_extract_def word_bits_def mask_def)
      apply (rule imageI, drule_tac t  = "vadSec x2" in sym, simp, word_bitwise)
     apply (rule_tac x = None in exI)
     apply (clarsimp simp: entry_range_tags_def entry_range_def)
     apply (case_tac "tlbtypcast x"; clarsimp simp: word_extract_def word_bits_def mask_def)
     apply (rule imageI,drule_tac t  = "vadSm x3" in sym, simp, word_bitwise)
    apply (rule_tac x = "Some (ASID (CONTEXTIDR (CP15 s)))" in exI)
    apply (clarsimp simp: entry_range_tags_def entry_range_def)
    apply (case_tac "tlbtypcast x"; clarsimp simp: word_extract_def word_bits_def mask_def)
    apply (rule imageI, drule_tac t  = "vadSm x3" in sym, simp, word_bitwise)
   apply (rule_tac x = None in exI)
   apply (clarsimp simp: entry_range_tags_def entry_range_def)
   apply (case_tac "tlbtypcast x"; clarsimp simp: word_extract_def word_bits_def mask_def)
   apply (rule imageI,drule_tac t  = "vadSup x4" in sym, simp, word_bitwise)
  apply (rule_tac x = "Some (ASID (CONTEXTIDR (CP15 s)))" in exI)
  apply (clarsimp simp: entry_range_tags_def entry_range_def)
  apply (case_tac "tlbtypcast x"; clarsimp simp: word_extract_def word_bits_def mask_def)
  by (rule imageI, drule_tac t  = "vadSup x4" in sym, simp, word_bitwise)



lemma dtlb_TLB_entry_some_lookup_not_miss:
  "\<lbrakk>micro_DataTLB s i = Some entry; 
      MatchingEntry (ASID (CONTEXTIDR (CP15 s)), va, entry)\<rbrakk> \<Longrightarrow>
    lookup (tlbtypcast ` ran (micro_DataTLB s)) (ASID (CONTEXTIDR (CP15 s))) va \<noteq> TLB.lookup_type.Miss"
  apply (subgoal_tac "entry_set (tlbtypcast ` ran (micro_DataTLB s)) (ASID (CONTEXTIDR (CP15 s))) va \<noteq> {}")
   apply (clarsimp simp: lookup_def)
  apply (subgoal_tac "tlbtypcast entry \<in> (tlbtypcast ` ran (micro_DataTLB s))")
   prefer 2
   apply (clarsimp simp: ran_def, blast)
  apply (clarsimp simp: entry_set_def)
  apply (rule_tac x = "tlbtypcast entry" in exI, clarsimp simp: MatchingEntry_def)
  apply (cases entry; clarsimp  split: if_split_asm)
         apply (rule_tac x = None in exI)
         apply (clarsimp simp: entry_range_tags_def entry_range_def)
         apply (case_tac "tlbtypcast x"; clarsimp simp: word_extract_def word_bits_def mask_def)
         apply (rule imageI,drule_tac t  = "vadLr x1" in sym, simp, word_bitwise)
        apply (rule_tac x = "Some (ASID (CONTEXTIDR (CP15 s)))" in exI)
        apply (clarsimp simp: entry_range_tags_def entry_range_def)
        apply (case_tac "tlbtypcast x"; clarsimp simp: word_extract_def word_bits_def mask_def)
        apply (rule imageI, drule_tac t  = "vadLr x1" in sym, simp, word_bitwise)
       apply (rule_tac x = None in exI)
       apply (clarsimp simp: entry_range_tags_def entry_range_def)
       apply (case_tac "tlbtypcast x"; clarsimp simp: word_extract_def word_bits_def mask_def)
       apply (rule imageI,drule_tac t  = "vadSec x2" in sym, simp, word_bitwise)
      apply (rule_tac x = "Some (ASID (CONTEXTIDR (CP15 s)))" in exI)
      apply (clarsimp simp: entry_range_tags_def entry_range_def)
      apply (case_tac "tlbtypcast x"; clarsimp simp: word_extract_def word_bits_def mask_def)
      apply (rule imageI, drule_tac t  = "vadSec x2" in sym, simp, word_bitwise)
     apply (rule_tac x = None in exI)
     apply (clarsimp simp: entry_range_tags_def entry_range_def)
     apply (case_tac "tlbtypcast x"; clarsimp simp: word_extract_def word_bits_def mask_def)
     apply (rule imageI,drule_tac t  = "vadSm x3" in sym, simp, word_bitwise)
    apply (rule_tac x = "Some (ASID (CONTEXTIDR (CP15 s)))" in exI)
    apply (clarsimp simp: entry_range_tags_def entry_range_def)
    apply (case_tac "tlbtypcast x"; clarsimp simp: word_extract_def word_bits_def mask_def)
    apply (rule imageI, drule_tac t  = "vadSm x3" in sym, simp, word_bitwise)
   apply (rule_tac x = None in exI)
   apply (clarsimp simp: entry_range_tags_def entry_range_def)
   apply (case_tac "tlbtypcast x"; clarsimp simp: word_extract_def word_bits_def mask_def)
   apply (rule imageI,drule_tac t  = "vadSup x4" in sym, simp, word_bitwise)
  apply (rule_tac x = "Some (ASID (CONTEXTIDR (CP15 s)))" in exI)
  apply (clarsimp simp: entry_range_tags_def entry_range_def)
  apply (case_tac "tlbtypcast x"; clarsimp simp: word_extract_def word_bits_def mask_def)
  by (rule imageI, drule_tac t  = "vadSup x4" in sym, simp, word_bitwise)




lemma to_do5':
  "\<lbrakk>main_TLB s i = Some entry; tlb_rel s (typ_tlb t);
        unitlb_consistent (typ_tlb t) (Addr va);
        MatchingEntry (ASID (CONTEXTIDR (CP15 s)), va, entry)\<rbrakk>
       \<Longrightarrow> pt_walk (asid t) (heap t) (ttbr0 t) (prrr t) (nmrr t) (Addr va) = Some (tlbtypcast entry)"
  apply (frule_tac va = va in  tlb_rel_unitlb_consistent, clarsimp)
  apply (thin_tac "unitlb_consistent (typ_tlb t) (Addr va)")
  apply (clarsimp simp: consistent0_def)
  apply (clarsimp simp: main_TLB_entry_some_lookup_not_miss)
  apply (subgoal_tac "lookup (tlbtypcast ` ran (main_TLB s)) (ASID (CONTEXTIDR (CP15 s))) va =
                         TLB.lookup_type.Hit (tlbtypcast entry)")
   apply clarsimp
   apply (frule tlb_relD, simp add: typ_tlb_def cstate.defs)
  apply (subgoal_tac "tlbtypcast entry \<in> entry_set (tlbtypcast ` ran (main_TLB s)) (ASID (CONTEXTIDR (CP15 s))) va")
   apply (subgoal_tac "y = tlbtypcast entry")
    apply clarsimp
   apply (clarsimp simp: lookup_def split: if_split_asm)
  apply (clarsimp simp: entry_set_def MatchingEntry_def entry_range_tags_def)
  apply (cases entry; clarsimp simp: ran_def entry_range_def word_extract_def word_bits_def mask_def split: if_split_asm) 
  by ((rule,force simp: ),(rule_tac x = None in exI, simp, rule imageI, clarsimp,word_bitwise), (rule,force simp: ),
             (rule_tac x = "(Some (ASID (CONTEXTIDR (CP15 s))))" in exI, simp, rule imageI, clarsimp,word_bitwise))+
       


lemma to_do5:
  "\<lbrakk>main_TLB s i = Some entry; tlb_rel s (typ_tlb t);
        unitlb_consistent (typ_tlb t) (Addr va);
        MatchingEntry (ASID (CONTEXTIDR re), va, entry)\<rbrakk>
       \<Longrightarrow> pt_walk (asid t) (heap t) (ttbr0 t) (prrr t) (nmrr t) (Addr va) = Some (tlbtypcast entry)"
  sorry


lemma to_do7':
  "\<lbrakk> micro_DataTLB s i = Some entry; MMU_config_assert_isa s; tlb_rel s (typ_tlb t);
        dtlb_consistent (typ_tlb t) (Addr va);
        MatchingEntry (ASID (CONTEXTIDR (CP15 s)), va, entry)\<rbrakk>
       \<Longrightarrow> pt_walk (asid t) (heap t) (ttbr0 t) (prrr t) (nmrr t) (Addr va) = Some (tlbtypcast entry)"
  apply (frule_tac va = va in  tlb_rel_datatlb_consistent, clarsimp)
  apply (thin_tac "dtlb_consistent (typ_tlb t) (Addr va)")
  apply (clarsimp simp: consistent0_def)
  apply (clarsimp simp: dtlb_TLB_entry_some_lookup_not_miss)
  apply (subgoal_tac "lookup (tlbtypcast ` ran (micro_DataTLB s)) (ASID (CONTEXTIDR (CP15 s))) va =
                         TLB.lookup_type.Hit (tlbtypcast entry)")
   apply clarsimp
   apply (frule tlb_relD, simp add: typ_tlb_def cstate.defs)
  apply (subgoal_tac "tlbtypcast entry \<in> entry_set (tlbtypcast ` ran (micro_DataTLB s)) (ASID (CONTEXTIDR (CP15 s))) va")
   apply (subgoal_tac "y = tlbtypcast entry")
    apply clarsimp
   apply (clarsimp simp: lookup_def split: if_split_asm)
  apply (clarsimp simp: entry_set_def MatchingEntry_def entry_range_tags_def)
  apply (cases entry; clarsimp simp: ran_def entry_range_def word_extract_def word_bits_def mask_def split: if_split_asm) 
  by ((rule,force simp: ),(rule_tac x = None in exI, simp, rule imageI, clarsimp,word_bitwise), (rule,force simp: ),
             (rule_tac x = "(Some (ASID (CONTEXTIDR (CP15 s))))" in exI, simp, rule imageI, clarsimp,word_bitwise))+


lemma to_do7:
  "\<lbrakk> micro_DataTLB b i = Some entry; MMU_config_assert_isa b; tlb_rel b (typ_tlb t);
        dtlb_consistent (typ_tlb t) (Addr va);
        MatchingEntry (ASID (CONTEXTIDR rc), va, entry)\<rbrakk>
       \<Longrightarrow> pt_walk (asid t) (heap t) (ttbr0 t) (prrr t) (nmrr t) (Addr va) = Some (tlbtypcast entry)"

sorry



lemma MMU_config_assert_isa_tlb_update [simp]:
  "MMU_config_assert_isa s \<Longrightarrow> MMU_config_assert_isa (s\<lparr>main_TLB := tlb\<rparr>)"
  by (clarsimp simp: MMU_config_assert_isa_def)

lemma MMU_config_assert_isa_itlb_up [simp]:
  "MMU_config_assert_isa s \<Longrightarrow> MMU_config_assert_isa (s\<lparr>micro_InstrTLB := tlb\<rparr>)"
  by (clarsimp simp: MMU_config_assert_isa_def)

lemma MMU_config_assert_isa_tlb_update' [simp]:
  " MMU_config_assert_isa (s\<lparr>main_TLB := tlb'\<rparr>) \<Longrightarrow> MMU_config_assert_isa (s\<lparr>main_TLB := tlb\<rparr>)"
  by (clarsimp simp: MMU_config_assert_isa_def)


lemma  [simp]:
  "MMU_config_assert_isa (if exception s = NoException then s\<lparr>exception := e\<rparr> else s) = MMU_config_assert_isa s"
  apply (clarsimp simp only: MMU_config_assert_isa_def)
  by force

lemma [simp]:
  "MMU_config_assert_isa (snd (w, snd (x, s))) = MMU_config_assert_isa s"
  apply (clarsimp simp only: MMU_config_assert_isa_def)
  by force


lemma [simp]:
  "exception (snd (w, snd (x,  s))) = 
    exception s"
  by (clarsimp simp: snd_def)

lemma [simp]:
  "MMU_config_assert_isa s \<Longrightarrow> \<not>AFE (VSCTLR (CP15 s))"
  by (clarsimp simp: MMU_config_assert_isa_def)


lemma [simp]:
  "MMU_config_assert_isa s \<Longrightarrow> Architecture s = ARMv7_A"
  by (clarsimp simp: MMU_config_assert_isa_def)


lemma [simp]:
  "MMU_config_assert_isa s \<Longrightarrow> Extensions s = {}"
  by(clarsimp simp only: MMU_config_assert_isa_def)

lemma [simp]:
  "MMU_config_assert_isa s \<Longrightarrow>  PID (FCSEIDR(CP15 s)) = 0"
  by(clarsimp simp only: MMU_config_assert_isa_def)

lemma [simp]:
  "MMU_config_assert_isa s \<Longrightarrow>  PSR.M (CPSR s) \<in> {0x10, 0x1F}"
  by(clarsimp simp only: MMU_config_assert_isa_def)

lemma [simp]:
  "MMU_config_assert_isa s \<Longrightarrow>   \<not>HSCTLR.M (HSCTLR(CP15 s))"
  by(clarsimp simp only: MMU_config_assert_isa_def)

lemma [simp]:
  "MMU_config_assert_isa s \<Longrightarrow> VSCTLR.M (VSCTLR(CP15 s))"
  by(clarsimp simp only: MMU_config_assert_isa_def)

lemma [simp]:
  "MMU_config_assert_isa s \<Longrightarrow> TTBCR.N (TTBCR(CP15 s)) = 0"
  by(clarsimp simp only: MMU_config_assert_isa_def)

lemma [simp]:
  "MMU_config_assert_isa s \<Longrightarrow> \<not>TTBCR.PD0 (TTBCR(CP15 s))"
  by(clarsimp simp only: MMU_config_assert_isa_def)

lemma [simp]:
  "MMU_config_assert_isa s \<Longrightarrow>  \<not>reg'TTBR0 (TTBR0 (CP15 s)) !! 0"
  by(clarsimp simp only: MMU_config_assert_isa_def)

lemma [simp]:
  "MMU_config_assert_isa s \<Longrightarrow> \<not>VSCTLR.EE (VSCTLR(CP15 s))"
  by(clarsimp simp only: MMU_config_assert_isa_def)

lemma [simp]:
  "MMU_config_assert_isa s \<Longrightarrow> VSCTLR.TRE (VSCTLR(CP15 s))"
  by(clarsimp simp only: MMU_config_assert_isa_def)

lemma [simp]:
  "MMU_config_assert_isa (s\<lparr>micro_DataTLB := mictlb,
                           main_TLB := maintlb\<rparr>) = MMU_config_assert_isa s"
  apply (clarsimp simp only: MMU_config_assert_isa_def)
  by force


lemma [simp]:
  "MMU_config_assert_isa s \<Longrightarrow> PSR.M (CPSR s) \<noteq> 0x17"
  apply (simp only: MMU_config_assert_isa_def)
  by force

lemma [simp]:
  "MMU_config_assert_isa s \<Longrightarrow> PSR.M (CPSR s) \<noteq> 0x16"
  apply (simp only: MMU_config_assert_isa_def)
  by force

lemma [simp]:
  "MMU_config_assert_isa s \<Longrightarrow> PSR.M (CPSR s) \<noteq> 0x1A"
  apply (simp only: MMU_config_assert_isa_def)
  by force

lemma [simp]:
  "MMU_config_assert_isa s \<Longrightarrow> PSR.M (CPSR s) \<noteq> 0x11"
  apply (simp only: MMU_config_assert_isa_def)
  by force

lemma [simp]:
  "MMU_config_assert_isa s \<Longrightarrow> PSR.M (CPSR s) \<noteq> 0x12"
  apply (simp only: MMU_config_assert_isa_def)
  by force

lemma [simp]:
  "MMU_config_assert_isa s \<Longrightarrow> PSR.M (CPSR s) \<noteq> 0x1B"
  apply (simp only: MMU_config_assert_isa_def)
  by force

lemma [simp]:
  "MMU_config_assert_isa s \<Longrightarrow> PSR.M (CPSR s) \<noteq> 0x13"
  apply (simp only: MMU_config_assert_isa_def)
  by force

lemma [simp]:
  "MMU_config_assert_isa s \<Longrightarrow> PSR.M (CPSR s) = 0x10 \<or> PSR.M (CPSR s) = 0x1F"
  apply (simp only: MMU_config_assert_isa_def)
  by force


lemma [simp]:
  "e \<noteq> NoException \<Longrightarrow> exception (if exception s = NoException then s \<lparr>exception := e\<rparr> else s) = NoException = False"
  by (clarsimp)

lemma tlb_rel_none_update_preserved:
  "\<lbrakk>tlb_rel s (typ_tlb t)\<rbrakk> \<Longrightarrow> 
       tlb_rel (s\<lparr>micro_InstrTLB := (micro_InstrTLB s)(0 := None), micro_DataTLB := \<lambda>a. if a = 0 then None else micro_DataTLB s a, main_TLB := \<lambda>a. if a = 0 then None else main_TLB s a\<rparr>) (typ_tlb t)"
  apply(unfold tlb_rel_def)
  apply (rule, simp add: state_comp_def)
  apply rule
   apply (rule_tac B = "tlbtypcast ` ran (micro_DataTLB s)" in  subset_trans; simp add: ran_def)
   apply force
  apply rule
   apply (rule_tac B = "tlbtypcast ` ran (micro_InstrTLB s)" in  subset_trans; simp add: ran_def)
   apply force
  apply (rule_tac B = "tlbtypcast ` ran (main_TLB s)" in  subset_trans; simp add: ran_def)
  by force


lemma word_2_cases'[simp]:
  "\<lbrakk>(w::2 word) = 3 ; w = 2; w = 1; w = 0 \<rbrakk> \<Longrightarrow> False"
  by word_bitwise auto


lemma
  "MemType (AddressDescriptor.memattrs
      (addrdesc  (s\<lparr>addrdesc  := p\<rparr> ))) = MemType (AddressDescriptor.memattrs p)"
  by clarsimp



lemma [simp]:
  "word_extract 31 25 (va :: 32 word) = (0 :: 7 word) \<Longrightarrow> 
        word_cat 0 ((word_extract 24 0 va) :: 25 word) = va"
  apply (clarsimp simp:  word_extract_def word_bits_def mask_def word_of_int_def) 
  apply word_bitwise
  by force



lemma [simp]:
  "reg'DACR (DACR (CP15 (if exception (snd s) = NoException then snd s\<lparr>exception := e\<rparr> else snd s))) =   
                          reg'DACR (DACR (CP15 (snd s)))"
  by clarsimp

lemma [simp]:
  "MEM (if exception s = NoException then s\<lparr>exception := e\<rparr> else s) p  = 
     MEM s p"
  by clarsimp




lemma well_formed_state:
  " \<lbrace>\<lambda>s. P s\<rbrace> f  \<lbrace>\<lambda>r s. MMU_config_assert_isa s \<and> Q' r s\<rbrace> \<Longrightarrow> 
                      \<lbrace>\<lambda>s. P s\<rbrace> f \<lbrace>\<lambda>r s. Q' r s\<rbrace>"
  by (clarsimp simp: l3_valid_def)

lemma CheckPermission_config_assert_isa:
  "\<lbrace>MMU_config_assert_isa\<rbrace> CheckPermission (p, va, l, d, iw, ip, f', f'') \<lbrace>\<lambda>_. MMU_config_assert_isa\<rbrace>"
  supply if_cong[cong] if_split[split del] 
  sorry


lemma CurrentModeIsHyp_config_assert_isa:
  "\<lbrace>MMU_config_assert_isa\<rbrace> CurrentModeIsHyp () \<lbrace>\<lambda>_. MMU_config_assert_isa\<rbrace>"
  sorry

lemma 
 "\<lbrace>MMU_config_assert_isa\<rbrace> TranslateAddressVS1Off va \<lbrace>\<lambda>_. MMU_config_assert_isa\<rbrace>"
  sorry

lemma 
  "\<lbrace>MMU_config_assert_isa\<rbrace> TLBResult (a, b, c, d, e, f, g, h, i, j, k, l) \<lbrace>\<lambda>_. MMU_config_assert_isa\<rbrace>"
  sorry


lemma 
  "\<lbrace>MMU_config_assert_isa\<rbrace> FCSETranslate va \<lbrace>\<lambda>_. MMU_config_assert_isa\<rbrace>"
  sorry


lemma CheckDomain_config_assert_isa:
  "\<lbrace>MMU_config_assert_isa\<rbrace> CheckDomain (d, va, l, iw) \<lbrace>\<lambda>_. MMU_config_assert_isa\<rbrace>"
  sorry


lemma 
  "\<lbrace>MMU_config_assert_isa\<rbrace> writing_access_flag (a, b) \<lbrace>\<lambda>_. MMU_config_assert_isa\<rbrace>"
  sorry

lemma
  "\<lbrace>MMU_config_assert_isa\<rbrace> writing_access_flag_first_level (a, b) \<lbrace>\<lambda>_. MMU_config_assert_isa\<rbrace>"
  sorry

lemma 
  "\<lbrace>MMU_config_assert_isa\<rbrace> SecondStageTranslate (ri, r) \<lbrace>\<lambda>_. MMU_config_assert_isa\<rbrace>"
  sorry

lemma 
  "\<lbrace>MMU_config_assert_isa\<rbrace> HaveSecurityExt () \<lbrace>\<lambda>_. MMU_config_assert_isa\<rbrace>"
  sorry

lemma 
  "\<lbrace>MMU_config_assert_isa \<rbrace>  IsSecure ()  \<lbrace>\<lambda>_. MMU_config_assert_isa \<rbrace>"
  sorry

lemma 
  "\<lbrace>MMU_config_assert_isa\<rbrace> HaveVirtExt () \<lbrace>\<lambda>_. MMU_config_assert_isa\<rbrace>"
  sorry

lemma
  "\<lbrace>MMU_config_assert_isa \<rbrace>  HaveMPExt ()  \<lbrace>\<lambda>_. MMU_config_assert_isa \<rbrace>"
  sorry

lemma 
  "\<lbrace>MMU_config_assert_isa \<rbrace>  mem (p, n)  \<lbrace>\<lambda>_. MMU_config_assert_isa \<rbrace>"
  sorry

lemma 
  "\<lbrace>MMU_config_assert_isa \<rbrace>  translation_root va  \<lbrace>\<lambda>_. MMU_config_assert_isa \<rbrace>"
  sorry

lemma translation_mmu_config:
  "\<lbrace>MMU_config_assert_isa\<rbrace> TranslationTableWalkSD (va, a, b) \<lbrace>\<lambda>r s. MMU_config_assert_isa s\<rbrace>"
  sorry


lemma tlb_rel_consistent_lookup_hit:
  "\<lbrakk>tlb_rel s (typ_tlb (t :: 'a tlb_state_scheme)); dtlb_consistent (typ_tlb t) (Addr va);
        lookup (tlbtypcast ` ran (micro_DataTLB s)) (ASID (CONTEXTIDR (CP15 s))) va = TLB.lookup_type.Hit x\<rbrakk>
       \<Longrightarrow> lookup (dtlb_set (tlbs_set t)) (asid t) va = TLB.lookup_type.Hit x"
  apply (drule tlb_relD, clarsimp simp: typ_tlb_def cstate.defs)
  apply (clarsimp simp: consistent0_def ran_def)
  by (metis Hits_le TLB.lookup_type.simps(5) leq_Miss option.sel tlb_mono)


lemma  lookup_leq_hit_incon:
  "\<lbrakk>lookup t a v \<le> lookup t' a v;  lookup t a v = TLB.lookup_type.Hit x\<rbrakk>
       \<Longrightarrow>  lookup t' a v = TLB.lookup_type.Incon \<or> lookup t' a v = TLB.lookup_type.Hit x"
  using less_eq_lookup_type by auto

end