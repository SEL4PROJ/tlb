theory Refinement_Paddr
imports  Refinement_Support

begin

lemma CheckPermission_constant_bool_pre_post [wp]:
  "\<lbrace>\<lambda>s. Q' \<rbrace> 
      CheckPermission (p, va, l, d, iw, ip, f, f')
      \<lbrace>\<lambda>rf s. A' s \<longrightarrow> Q'\<rbrace>"
  supply if_cong[cong] if_split[split del] 
  by (wpsimp simp: CheckPermission_def)


lemma domain_entry_constant_bool_pre_post [wp]:
  "\<lbrace>\<lambda>s. Q'\<rbrace> CheckDomain (de, va, l, iw) 
         \<lbrace>\<lambda>re. if re then (\<lambda>s. Q') else  (\<lambda>s. A' s \<longrightarrow> Q')\<rbrace>"
  supply if_cong[cong] if_split[split del] 
  by (wpsimp simp: CheckDomain_def)


lemma word_2_cases'[simp]:
  "\<lbrakk>(w::2 word) = 3 ; w = 2; w = 1; w = 0 \<rbrakk> \<Longrightarrow> False"
  by word_bitwise auto


definition 

"Q_pt r pa' s \<equiv> (word_extract (Suc (2 * nat (uint (TLBRecord.domain r)))) (2 * nat (uint (TLBRecord.domain r))) (reg'DACR (DACR (CP15 s))) = (3 :: 2 word) \<longrightarrow>
                                 exception s = NoException \<longrightarrow> pa' = Addr (paddress (addrdesc r))) \<and>
                                (word_extract (Suc (2 * nat (uint (TLBRecord.domain r)))) (2 * nat (uint (TLBRecord.domain r))) (reg'DACR (DACR (CP15 s))) \<noteq> (3 :: 2 word) \<longrightarrow>
                                 (word_extract (Suc (2 * nat (uint (TLBRecord.domain r)))) (2 * nat (uint (TLBRecord.domain r))) (reg'DACR (DACR (CP15 s))) = (2 :: 2 word) \<longrightarrow> (\<exists>r. r) \<longrightarrow> pa' = Addr (paddress (addrdesc r))) \<and>
                                 (word_extract (Suc (2 * nat (uint (TLBRecord.domain r)))) (2 * nat (uint (TLBRecord.domain r))) (reg'DACR (DACR (CP15 s))) \<noteq> (2 :: 2 word) \<longrightarrow>
                                  (word_extract (Suc (2 * nat (uint (TLBRecord.domain r)))) (2 * nat (uint (TLBRecord.domain r))) (reg'DACR (DACR (CP15 s))) = (1 :: 2 word) \<longrightarrow> pa' = Addr (paddress (addrdesc r))) \<and>
                                  (word_extract (Suc (2 * nat (uint (TLBRecord.domain r)))) (2 * nat (uint (TLBRecord.domain r))) (reg'DACR (DACR (CP15 s))) \<noteq> (1 :: 2 word) \<longrightarrow>
                                   (word_extract (Suc (2 * nat (uint (TLBRecord.domain r)))) (2 * nat (uint (TLBRecord.domain r))) (reg'DACR (DACR (CP15 s))) = (0 :: 2 word) \<longrightarrow> (\<exists>r. r) \<longrightarrow> pa' = Addr (paddress (addrdesc r))) \<and>
                                   word_extract (Suc (2 * nat (uint (TLBRecord.domain r)))) (2 * nat (uint (TLBRecord.domain r))) (reg'DACR (DACR (CP15 s))) = (0 :: 2 word))))"

lemma [simp]:
  "MemType (AddressDescriptor.memattrs
      (addrdesc  (s\<lparr>addrdesc  := p\<rparr> ))) = MemType (AddressDescriptor.memattrs p)"
  by clarsimp

lemma f_false:
  "\<lbrace>\<lambda>_. False\<rbrace> f \<lbrace>\<lambda>r s. Q'  r s \<rbrace>"
  by (clarsimp simp: l3_valid_def)

lemma TranslateAddressV_pt_walk [wp]:
  " \<lbrace>\<lambda>s. \<exists>(t :: 'a tlb_state_scheme) (t' :: 'a tlb_state_scheme) mematr. 
                 MMU_config_assert_isa s \<and>
                 tlb_rel s (typ_tlb t) \<and>
                 dtlb_consistent (typ_tlb t) (Addr va) \<and>
                 unitlb_consistent (typ_tlb t) (Addr va) \<and>
                 pt_walk_alignement_check (Addr va) siz t = ((pa', mematr), t') \<and> excpt t' = NoExcp \<rbrace> 
            TranslationTableWalkSD   (va, iswrite, siz)
       \<lbrace>\<lambda>r s. Q_pt r pa' s\<rbrace>"
  supply if_cong[cong] if_split[split del] 
  apply (wpsimp simp: TranslationTableWalkSD_def Let_def)
            apply (rule well_formed_state, simp)
            apply (clarsimp simp: TLBResult_def)
 (*           apply (wp)

 apply (clarsimp simp: if_distribR  cong: conj_cong )*)

            apply (wp_once, (clarsimp simp: if_distribR  cong: conj_cong )?)
            apply (wp_once, (clarsimp simp: if_distribR  cong: conj_cong )?)
             apply (wp_once, (clarsimp simp: if_distribR  cong: conj_cong )?)
              apply (wp_once, (clarsimp simp: if_distribR  cong: conj_cong )?)
               apply (wp_once, (clarsimp simp: if_distribR  cong: conj_cong )?)
                apply (wp_once, (clarsimp simp: if_distribR  cong: conj_cong )?)
                 apply (wp_once, (clarsimp simp: if_distribR  cong: conj_cong )?)
                  apply (wp_once, (clarsimp simp: if_distribR  cong: conj_cong )?)
                   apply (wp_once, (clarsimp simp: if_distribR  cong: conj_cong )?)
                    apply (wp_once, (clarsimp simp: if_distribR  cong: conj_cong )?)
                     apply (wp_once, (clarsimp simp: if_distribR  cong: conj_cong )?)
                      apply (wp_once, (clarsimp simp: if_distribR  cong: conj_cong )?)
                       apply (wp_once, (clarsimp simp: if_distribR  cong: conj_cong )?)
                        apply (wp_once, (clarsimp simp: if_distribR  cong: conj_cong )?)
                         apply (wp_once, (clarsimp simp: if_distribR  cong: conj_cong )?)
                          apply (wp_once, (clarsimp simp: if_distribR  cong: conj_cong )?)
                           apply (wp_once, (clarsimp simp: if_distribR  cong: conj_cong )?)
                            apply (wp_once, (clarsimp simp: if_distribR  cong: conj_cong )?)
                             apply (wp_once, (clarsimp simp: if_distribR  cong: conj_cong )?)
                              apply (wp_once, (clarsimp simp: if_distribR  cong: conj_cong )?)
                               apply (wp_once, (clarsimp simp: if_distribR  cong: conj_cong )?)
                                apply (wp_once, (clarsimp simp: if_distribR  cong: conj_cong )?)
                                 apply (wp_once, (clarsimp simp: if_distribR  cong: conj_cong )?)
                                  apply (wp_once, (clarsimp simp: if_distribR  cong: conj_cong )?)
                                   apply (wp_once, (clarsimp simp: if_distribR  cong: conj_cong )?)
                                    apply (wp_once, (clarsimp simp: if_distribR  cong: conj_cong )?)
                                   apply (wp_once, (clarsimp simp: if_distribR  cong: conj_cong )?)
                                    apply (wp_once, (clarsimp simp: if_distribR  cong: conj_cong )?)
                                     apply (wp_once, (clarsimp simp: if_distribR  cong: conj_cong )?)
                                      apply wpsimp
                                     apply wpsimp
                                    apply (wpsimp, clarsimp)
                                   apply wpsimp
                                  apply wpsimp
                                 apply (wpsimp , clarsimp)
                                apply wpsimp
                               apply wpsimp
                              apply wpsimp
                             apply wpsimp
                            apply wpsimp
                           apply wpsimp apply clarsimp
                          apply wpsimp 
                         apply wpsimp apply clarsimp
                        apply wpsimp
                       apply wpsimp apply clarsimp
                      apply wpsimp
                     apply wpsimp apply clarsimp
                    apply wpsimp
                   apply wpsimp apply clarsimp
                  apply wpsimp
                 apply wpsimp apply clarsimp
                apply wpsimp
               apply wpsimp apply clarsimp
              apply wpsimp
             apply wpsimp 
                 apply (rule f_false)
                apply wpsimp
               apply wpsimp 
              apply wpsimp 

                defer
                apply wpsimp 
               apply wpsimp 
              apply wpsimp 
             apply wpsimp 





            apply (clarsimp simp: TLBResult_def)
 (*           apply (wp)

 apply (clarsimp simp: if_distribR  cong: conj_cong )*)

            apply (wp_once, (clarsimp simp: if_distribR  cong: conj_cong )?)
            apply (wp_once, (clarsimp simp: if_distribR  cong: conj_cong )?)
             apply (wp_once, (clarsimp simp: if_distribR  cong: conj_cong )?)
              apply (wp_once, (clarsimp simp: if_distribR  cong: conj_cong )?)
               apply (wp_once, (clarsimp simp: if_distribR  cong: conj_cong )?)
                apply (wp_once, (clarsimp simp: if_distribR  cong: conj_cong )?)
                 apply (wp_once, (clarsimp simp: if_distribR  cong: conj_cong )?)
                  apply (wp_once, (clarsimp simp: if_distribR  cong: conj_cong )?)
                   apply (wp_once, (clarsimp simp: if_distribR  cong: conj_cong )?)
                    apply (wp_once, (clarsimp simp: if_distribR  cong: conj_cong )?)
                     apply (wp_once, (clarsimp simp: if_distribR  cong: conj_cong )?)
                      apply (wp_once, (clarsimp simp: if_distribR  cong: conj_cong )?)
                       apply (wp_once, (clarsimp simp: if_distribR  cong: conj_cong )?)
                        apply (wp_once, (clarsimp simp: if_distribR  cong: conj_cong )?)
                         apply (wp_once, (clarsimp simp: if_distribR  cong: conj_cong )?)
                          apply (wp_once, (clarsimp simp: if_distribR  cong: conj_cong )?)
                           apply (wp_once, (clarsimp simp: if_distribR  cong: conj_cong )?)
                            apply (wp_once, (clarsimp simp: if_distribR  cong: conj_cong )?)
                             apply (wp_once, (clarsimp simp: if_distribR  cong: conj_cong )?)
                              apply (wp_once, (clarsimp simp: if_distribR  cong: conj_cong )?)
                               apply (wp_once, (clarsimp simp: if_distribR  cong: conj_cong )?)
                                apply (wp_once, (clarsimp simp: if_distribR  cong: conj_cong )?)
                                 apply (wp_once, (clarsimp simp: if_distribR  cong: conj_cong )?)
                                  apply (wp_once, (clarsimp simp: if_distribR  cong: conj_cong )?)
                                   apply (wp_once, (clarsimp simp: if_distribR  cong: conj_cong )?)
                                    apply (wp_once, (clarsimp simp: if_distribR  cong: conj_cong )?)
                                   apply (wp_once, (clarsimp simp: if_distribR  cong: conj_cong )?)
                                    apply (wp_once, (clarsimp simp: if_distribR  cong: conj_cong )?)
                                     apply (wp_once, (clarsimp simp: if_distribR  cong: conj_cong )?)
                                      apply wpsimp
                                     apply wpsimp
                                    apply (wpsimp, clarsimp)
                                   apply wpsimp
                                  apply wpsimp
                                 apply (wpsimp , clarsimp)
                                apply wpsimp
                               apply wpsimp
                              apply wpsimp
                             apply wpsimp
                            apply wpsimp
                           apply wpsimp apply clarsimp
                          apply wpsimp 
                         apply wpsimp apply clarsimp
                        apply wpsimp
                       apply wpsimp apply clarsimp
                      apply wpsimp
                     apply wpsimp apply clarsimp
                    apply wpsimp
                   apply wpsimp apply clarsimp
                  apply wpsimp
                 apply wpsimp apply clarsimp
                apply wpsimp
               apply wpsimp apply clarsimp
              apply wpsimp
             apply wpsimp 
                 apply (rule f_false)
                apply wpsimp
               apply wpsimp 
              apply wpsimp 

                defer
                apply wpsimp 
               apply wpsimp 
              apply wpsimp 
             apply wpsimp 



  prefer 9





  sorry








































lemma TranslateAddressV_pt_walk':
  " \<lbrace>\<lambda>s. \<exists>(t :: 'a tlb_state_scheme). MMU_config_assert_isa s \<and>
                 tlb_rel s (typ_tlb t) \<and>
                 dtlb_consistent (typ_tlb t) (Addr va) \<and>
                 unitlb_consistent (typ_tlb t) (Addr va) \<and>
        (\<forall>entry. pt_walk (asid t) (heap t) (ttbr0 t) (prrr t) (nmrr t)  (Addr va) = Some entry \<longrightarrow>
                 pa' = Addr (TLB.va_to_pa va entry)) \<rbrace> 
            TranslationTableWalkSD   (va, iswrite, siz)
       \<lbrace>\<lambda>r s. (word_extract (Suc (2 * nat (uint (TLBRecord.domain r)))) (2 * nat (uint (TLBRecord.domain r))) (reg'DACR (DACR (CP15 s))) = (3 :: 2 word) \<longrightarrow>
                                 exception s = NoException \<longrightarrow> pa' = Addr (paddress (addrdesc r))) \<and>
                                (word_extract (Suc (2 * nat (uint (TLBRecord.domain r)))) (2 * nat (uint (TLBRecord.domain r))) (reg'DACR (DACR (CP15 s))) \<noteq> (3 :: 2 word) \<longrightarrow>
                                 (word_extract (Suc (2 * nat (uint (TLBRecord.domain r)))) (2 * nat (uint (TLBRecord.domain r))) (reg'DACR (DACR (CP15 s))) = (2 :: 2 word) \<longrightarrow> (\<exists>r. r) \<longrightarrow> pa' = Addr (paddress (addrdesc r))) \<and>
                                 (word_extract (Suc (2 * nat (uint (TLBRecord.domain r)))) (2 * nat (uint (TLBRecord.domain r))) (reg'DACR (DACR (CP15 s))) \<noteq> (2 :: 2 word) \<longrightarrow>
                                  (word_extract (Suc (2 * nat (uint (TLBRecord.domain r)))) (2 * nat (uint (TLBRecord.domain r))) (reg'DACR (DACR (CP15 s))) = (1 :: 2 word) \<longrightarrow> pa' = Addr (paddress (addrdesc r))) \<and>
                                  (word_extract (Suc (2 * nat (uint (TLBRecord.domain r)))) (2 * nat (uint (TLBRecord.domain r))) (reg'DACR (DACR (CP15 s))) \<noteq> (1 :: 2 word) \<longrightarrow>
                                   (word_extract (Suc (2 * nat (uint (TLBRecord.domain r)))) (2 * nat (uint (TLBRecord.domain r))) (reg'DACR (DACR (CP15 s))) = (0 :: 2 word) \<longrightarrow> (\<exists>r. r) \<longrightarrow> pa' = Addr (paddress (addrdesc r))) \<and>
                                   word_extract (Suc (2 * nat (uint (TLBRecord.domain r)))) (2 * nat (uint (TLBRecord.domain r))) (reg'DACR (DACR (CP15 s))) = (0 :: 2 word))))\<rbrace>"

  sorry


lemma [simp]:
  "word_extract 31 25 (va :: 32 word) = (0 :: 7 word) \<Longrightarrow> 
        word_cat 0 ((word_extract 24 0 va) :: 25 word) = va"
  apply (clarsimp simp:  word_extract_def word_bits_def mask_def word_of_int_def) 
  apply word_bitwise
  by force

lemma TranslateAddressVS1Off_False: 
  "\<lbrace>\<lambda>_. False\<rbrace> TranslateAddressVS1Off va \<lbrace>Q'\<rbrace>"
  by (clarsimp simp: l3_valid_def)

 

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


lemma mmu_translate_refinement_pa [wp]:
  "\<lbrace>\<lambda>s. \<exists>t mematr . MMU_config_assert_isa s \<and>
                 tlb_rel s (typ_tlb t) \<and>
                 dtlb_consistent (typ_tlb t) (Addr va) \<and>
                 unitlb_consistent (typ_tlb t) (Addr va) \<and>
                 mmu_translate  (Addr va) siz ispriv iswrite True (t :: 'a tlb_state_scheme) = ((pa', mematr), t')\<rbrace>
       TranslateAddress (va, ispriv, iswrite, siz, True) 
   \<lbrace>\<lambda>r s. exception s = NoException \<longrightarrow> pa' = Addr (paddress r)\<rbrace>"
  supply if_cong[cong] if_split[split del] 
  apply (wpsimp simp: TranslateAddress_def write'DataTLB_def write'unified_mainTLB_def)
          apply (wpsimp simp: TranslateAddressV_def)
                  apply (rule well_formed_state, simp)
                  apply (wpsimp simp: CurrentModeIsHyp_def)
                   apply (wpsimp simp: BadMode_def HaveSecurityExt_def HaveVirtExt_def ArchVersion_def cong: conj_cong)
                  apply wpsimp
                 apply wpsimp
                apply (rule well_formed_state, simp)
                apply (clarsimp simp: if_distribR  cong: conj_cong )
                apply (wpsimp simp: CheckDomain_def)
               apply wpsimp
              apply wpsimp
               apply (rule well_formed_state, simp)
               apply (clarsimp simp: if_distribR  cong: conj_cong )
               apply (wpsimp simp: CurrentModeIsHyp_def)
                apply (wpsimp simp: BadMode_def HaveSecurityExt_def HaveVirtExt_def ArchVersion_def cong: conj_cong)
               apply wpsimp
              apply wpsimp
             apply (rule well_formed_state, simp)
             apply (clarsimp simp: if_distribR  cong: conj_cong )
             apply (wpsimp simp: CurrentModeIsHyp_def)
              apply (wpsimp simp: BadMode_def HaveSecurityExt_def HaveVirtExt_def ArchVersion_def cong: conj_cong)
             apply wpsimp
            apply wpsimp
              apply (rule well_formed_state, simp)
              apply (clarsimp simp: if_distribR  cong: conj_cong )
              apply (rule l3_valid_conj_post) 
               apply (rule translation_mmu_config)
              apply (clarsimp split: if_split)
              apply (rule TranslateAddressV_pt_walk' [where ?'a = 'a] )
             apply (rule well_formed_state, simp)
             apply (clarsimp simp: if_distribR  cong: conj_cong)
             apply (rule TranslateAddressVS1Off_False)   (*  should we remove VS1Off altogerher? *)
            apply wpsimp
             apply (rule well_formed_state, simp)
             apply (clarsimp simp: if_distribR  cong: conj_cong )
             apply (wpsimp simp: CurrentModeIsHyp_def)
              apply (wpsimp simp: BadMode_def HaveSecurityExt_def HaveVirtExt_def ArchVersion_def cong: conj_cong)
             apply wpsimp
            apply wpsimp
           apply (rule well_formed_state, simp)
           apply (clarsimp simp: if_distribR  cong: conj_cong )
           apply (wpsimp simp: CurrentModeIsHyp_def)
            apply (wpsimp simp: BadMode_def HaveSecurityExt_def HaveVirtExt_def ArchVersion_def cong: conj_cong)
           apply wpsimp
          apply (rule well_formed_state, simp)
          apply (clarsimp simp: if_distribR  cong: conj_cong )
          apply (wpsimp simp: FCSETranslate_def)
         apply (clarsimp  cong: conj_cong)
         apply (wpsimp simp: lookupTLB_main_def entry_list_main_def mainTLBEntries_def)
         apply (rule for_loop_wp1; wpsimp simp: unified_mainTLB_def)
          apply (rename_tac s entry)
          apply (case_tac a; clarsimp split: if_split)
          apply (drule_tac x = "tlbtypcast entry" in spec)
          apply (subgoal_tac "pt_walk (asid t) (heap t) (ttbr0 t) (prrr t) (nmrr t) (Addr va) = Some (tlbtypcast entry)";
                                 (clarsimp simp: to_do5)?)
          apply (clarsimp simp: TLB.va_to_pa_def ARM_Monadic.va_to_pa_def split: TLBEntry.splits)
         apply (rename_tac entry)
         apply (case_tac a; clarsimp split: if_split)
         apply (drule_tac x = "tlbtypcast entry" in spec)
         apply (subgoal_tac "pt_walk (asid t) (heap t) (ttbr0 t) (prrr t) (nmrr t) (Addr va) = Some (tlbtypcast entry)";
                                (clarsimp simp: to_do5)?)
         apply (clarsimp simp: TLB.va_to_pa_def ARM_Monadic.va_to_pa_def split: TLBEntry.splits)
        apply (wpsimp)
       apply (wpsimp simp: lookupTLB_Data_micro_def entry_list_data_micro_def microDataTLBEntries_def)
       apply (rule for_loop_wp1; wpsimp simp: DataTLB_def)
        apply (rename_tac entry)
        apply (case_tac a; clarsimp split: if_split)
        apply (drule_tac x = "tlbtypcast entry" in spec)
        apply (subgoal_tac "pt_walk (asid t) (heap t) (ttbr0 t) (prrr t) (nmrr t) (Addr va) = Some (tlbtypcast entry)";
                           (clarsimp simp: to_do7)?)
        apply (clarsimp simp: TLB.va_to_pa_def ARM_Monadic.va_to_pa_def split: TLBEntry.splits)
       apply (rename_tac entry)
       apply (case_tac a; clarsimp split: if_split)
       apply (drule_tac x = "tlbtypcast entry" in spec)
       apply (subgoal_tac "pt_walk (asid t) (heap t) (ttbr0 t) (prrr t) (nmrr t) (Addr va) = Some (tlbtypcast entry)";
                              (clarsimp simp: to_do7)?)
       apply (clarsimp simp: TLB.va_to_pa_def ARM_Monadic.va_to_pa_def split: TLBEntry.splits)
      apply (wpsimp)
     apply clarsimp
     apply (wpsimp simp: mainTLB_evict_def write'unified_mainTLB_def mainTLBEntries_def)
     apply (rule for_loop_wp0' ; wpsimp simp: unified_mainTLB_def)
     defer
     apply (wpsimp simp: microDataTLB_evict_def write'DataTLB_def microDataTLBEntries_def)
     apply (rule for_loop_wp0' ; wpsimp simp: DataTLB_def) 
     defer
     apply (wpsimp simp: microInstrTLB_evict_def write'InstrTLB_def microInstrTLBEntries_def)
     apply (rule for_loop_wp0' ; wpsimp simp: InstrTLB_def)
     defer
     apply clarsimp
     apply (rule_tac x = t in exI)
     apply (rule, clarsimp simp: tlb_rel_none_update_preserved)
     apply (rule, clarsimp)
     apply (rule, clarsimp)
     apply (clarsimp)
     apply (clarsimp simp: mmu_translate_tlb_state_ext_def read_state_def Let_def bind_def)
     apply (case_tac "lookup (dtlb_set (tlbs_set t)) (asid t) va"; clarsimp)
       apply (case_tac "lookup (unitlb_set (tlbs_set t)) (asid t) va"; clarsimp)
         apply (clarsimp simp: bind_def update_state_def)
         apply (clarsimp simp: align_dom_perm_entry_check_def align_def Let_def split: if_split_asm)


















  sorry


end