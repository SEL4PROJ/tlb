theory Refinement
imports  Refinement_Paddr

begin


lemma mmu_translate_refinement_exception [wp]:
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


lemmas mmu_translate_refinement_config [wp] = 
              l3_valid_TranslateAddress_MMU_config [THEN l3_valid_redunt_post_imp]


lemma mmu_translate_refinement_mematr [wp]:
  "\<lbrace>\<lambda>s. \<exists>t pa' . MMU_config_assert_isa s \<and>
                 tlb_rel s (typ_tlb t) \<and>
                 dtlb_consistent (typ_tlb t) (Addr va) \<and>
                 unitlb_consistent (typ_tlb t) (Addr va) \<and>
                 mmu_translate  (Addr va) siz ispriv iswrite True (t :: 'a tlb_state_scheme) = ((pa', mematr), t')\<rbrace>
       TranslateAddress (va, ispriv, iswrite, siz, True) \<lbrace>\<lambda>r s. exception s = NoException \<longrightarrow> mematr = mematr_typcast (AddressDescriptor.memattrs r)\<rbrace>"

  sorry

lemma mmu_translate_refinement_tlb_rel [wp]:
  "\<lbrace>\<lambda>s. \<exists>t pa' mematr . MMU_config_assert_isa s \<and>
                 tlb_rel s (typ_tlb t) \<and>
                 dtlb_consistent (typ_tlb t) (Addr va) \<and>
                 unitlb_consistent (typ_tlb t) (Addr va) \<and>
                 mmu_translate  (Addr va) siz ispriv iswrite True (t :: 'a tlb_state_scheme) = ((pa', mematr), t')\<rbrace>
       TranslateAddress (va, ispriv, iswrite, siz, True) \<lbrace>\<lambda>r s. exception s = NoException \<longrightarrow> tlb_rel s (typ_tlb t') \<rbrace>"

  sorry


lemma mmu_translate_refinement_dtlb_consist [wp]:
  "\<lbrace>\<lambda>s. \<exists>t pa' mematr . MMU_config_assert_isa s \<and>
                 tlb_rel s (typ_tlb t) \<and>
                 dtlb_consistent (typ_tlb t) (Addr va) \<and>
                 unitlb_consistent (typ_tlb t) (Addr va) \<and>
                 mmu_translate  (Addr va) siz ispriv iswrite True (t :: 'a tlb_state_scheme) = ((pa', mematr), t')\<rbrace>
       TranslateAddress (va, ispriv, iswrite, siz, True) \<lbrace>\<lambda>r s. exception s = NoException \<longrightarrow> dtlb_consistent (typ_tlb t') (Addr va) \<rbrace>"

  sorry

lemma mmu_translate_refinement_itlb_consist [wp]:
  "\<lbrace>\<lambda>s. \<exists>t pa' mematr . MMU_config_assert_isa s \<and>
                 tlb_rel s (typ_tlb t) \<and>
                 dtlb_consistent (typ_tlb t) (Addr va) \<and>
                 unitlb_consistent (typ_tlb t) (Addr va) \<and>
                 mmu_translate  (Addr va) siz ispriv iswrite True (t :: 'a tlb_state_scheme) = ((pa', mematr), t')\<rbrace>
       TranslateAddress (va, ispriv, iswrite, siz, True) \<lbrace>\<lambda>r s. exception s = NoException \<longrightarrow>unitlb_consistent (typ_tlb t') (Addr va)\<rbrace>"

  sorry

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
              pa' = Addr (paddress (adrdesc)) \<and> 
               mematr = mematr_typcast (AddressDescriptor.memattrs (adrdesc)) \<and> tlb_rel s' (typ_tlb t') \<and>
               dtlb_consistent (typ_tlb t') (Addr va) \<and> unitlb_consistent (typ_tlb t') (Addr va)) \<rbrace>"
  supply if_cong[cong] if_split[split del] 
  apply wpsimp
  by force


end