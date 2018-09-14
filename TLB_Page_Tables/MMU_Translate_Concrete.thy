theory MMU_Translate_Concrete
imports  Refinement_Support

begin



(* wp_comb requires validity of A in order to proceed *)

lemma TranslateAddress_exception_mmu_translate [wp]:
  "\<lbrace>\<lambda>s. \<exists>t pa' mematr . MMU_config_assert_isa s \<and>
                 tlb_rel s (typ_tlb t) \<and>
                 dtlb_consistent (typ_tlb t) (Addr va) \<and>
                 unitlb_consistent (typ_tlb t) (Addr va) \<and>
                 mmu_translate  (Addr va) siz ispriv iswrite True (t :: 'a tlb_state_scheme) = ((pa', mematr), t')\<rbrace>
       (TranslateAddress (va , ispriv, iswrite, siz, True))
                 \<lbrace>\<lambda>_ s'. exception s' \<noteq> NoException \<longrightarrow> excpt t' \<noteq> NoExcp\<rbrace>"
  
sorry

lemma l3_valid_TranslateAddress_MMU_config:
  "\<lbrace>\<lambda>s. MMU_config_assert_isa s\<rbrace> TranslateAddress (va, ispriv, iswrite, siz, True) 
       \<lbrace>\<lambda>_ s. MMU_config_assert_isa s\<rbrace>"
  apply (clarsimp simp: l3_valid_def)
  by ((insert mmu_config_TranslateAddress [of va ispriv iswrite siz]) [1],
        force simp: mmu_config_def)


lemmas l3_valid_TranslateAddress_MMU_config' [wp] = 
              l3_valid_TranslateAddress_MMU_config [THEN l3_valid_redunt_post_imp]

lemma TranslateAddressV_pt_walk:
  "\<lbrace>\<lambda>s. \<exists>(t :: 'a tlb_state_scheme). MMU_config_assert_isa s \<and>
                 tlb_rel s (typ_tlb t) \<and>
                 dtlb_consistent (typ_tlb t) (Addr va) \<and>
                 unitlb_consistent (typ_tlb t) (Addr va) \<and>
        (\<forall>entry. pt_walk (asid t) (heap t) (ttbr0 t) (prrr t) (nmrr t)  (Addr va) = Some entry \<longrightarrow>
                 pa' = Addr (TLB.va_to_pa va entry)) \<rbrace> 
            TranslateAddressV(va, ispriv, iswrite,siz) 
       \<lbrace>\<lambda>rg s'. \<forall>x. (\<exists>xa. rg = (x, xa)) \<longrightarrow> exception s' = NoException \<longrightarrow> pa' = Addr (paddress x)\<rbrace>"

sorry






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

lemma CurrentModeIsHyp_bool_pre_post[wp]:
  "\<lbrace>\<lambda>s. pa' = Addr (paddress (addrdesc rb))\<rbrace> CurrentModeIsHyp () \<lbrace>\<lambda>a b. pa' = Addr (paddress (addrdesc rb))\<rbrace>"
  by (wpsimp simp : CurrentModeIsHyp_def BadMode_def HaveSecurityExt_def HaveVirtExt_def ArchVersion_def)



lemma main_thm:
  "\<lbrace>\<lambda>s. MMU_config_assert_isa s \<and>
                 tlb_rel s (typ_tlb t) \<and>
                 dtlb_consistent (typ_tlb t) (Addr va) \<and>
                 unitlb_consistent (typ_tlb t) (Addr va) \<and>
                 mmu_translate  (Addr va) siz ispriv iswrite True (t :: 'a tlb_state_scheme) = ((pa', mematr), t')\<rbrace>
       (TranslateAddress (va , ispriv, iswrite, siz, True))
        \<lbrace>\<lambda>adrdesc s'.
           (exception s' \<noteq> NoException \<longrightarrow> excpt t' \<noteq> NoExcp) \<and>
           (exception s' = NoException \<longrightarrow>
              MMU_config_assert_isa s' \<and> 
              (pa' = Addr (paddress (adrdesc)) \<and> 
               mematr = mematr_typcast (AddressDescriptor.memattrs (adrdesc)) \<and> tlb_rel s' (typ_tlb t') \<and>
               dtlb_consistent (typ_tlb t') (Addr va) \<and> unitlb_consistent (typ_tlb t') (Addr va))) \<rbrace>"
  supply if_cong[cong] if_split[split del] 
    CheckPermission_constant_bool_pre_post [wp]
    domain_entry_constant_bool_pre_post [wp] 
  apply wpsimp
    (*  apply (wpsimp simp: TranslateAddress_def)
             apply (rule CheckPermission_constant_bool_pre_post)
            apply wpsimp
           apply (rule domain_entry_constant_bool_pre_post)
          apply wpsimp  etc *)
    apply (wpsimp simp: TranslateAddress_def write'DataTLB_def write'unified_mainTLB_def)
           apply (wpsimp simp: TranslateAddressV_def)
                apply (wpsimp simp: CurrentModeIsHyp_def BadMode_def HaveSecurityExt_def HaveVirtExt_def ArchVersion_def)
               apply (wpsimp)
              apply (wpsimp simp: CurrentModeIsHyp_def BadMode_def HaveSecurityExt_def HaveVirtExt_def ArchVersion_def)
  apply wpsimp
  apply (rule haha)
  apply clarsimp


  thm domain_entry_constant_bool_pre_post




  thm TranslateAddressVS1Off_def

           apply (rule TranslateAddressV_pt_walk [where ?'a = 'a] )
          apply (wpsimp simp: lookupTLB_main_def entry_list_main_def mainTLBEntries_def)
          apply (rule for_loop_wp1; wpsimp simp: unified_mainTLB_def)
           apply (rename_tac entry)
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
    (* apply (subgoal_tac "(word_of_int (int i) :: 8 word) \<noteq> 0")*)
      apply (rule_tac x = t in exI, clarsimp simp: tlb_rel_def state_comp_def ran_def 
      split: if_split_asm)
       defer
       apply (wpsimp simp: microDataTLB_evict_def)


oops


















end