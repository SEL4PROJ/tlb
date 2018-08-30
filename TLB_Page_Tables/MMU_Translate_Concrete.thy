theory MMU_Translate_Concrete
imports  L3_LIB.L3_Hoare_Logic
         MMU_Translate_Refine
         MMU_ARM.ARM_Monadic
begin

declare return_def [simp add]

definition 
  MMU_config_assert_isa :: "'a state_scheme \<Rightarrow> bool"
where
  "MMU_config_assert_isa s \<equiv>  Architecture s = ARMv7_A \<and> 
                              Extensions s = {} \<and>
                              PID (FCSEIDR(CP15 s)) = 0 \<and>
                              PSR.M (CPSR s) \<in> {0x10, 0x1F} \<and>
                              \<not>HSCTLR.M (HSCTLR(CP15 s))  \<and>
                              VSCTLR.M (VSCTLR(CP15 s)) \<and>
                              TTBCR.N (TTBCR(CP15 s)) = 0 \<and> 
                              \<not>TTBCR.PD0 (TTBCR(CP15 s))  \<and> 
                              \<not>reg'TTBR0 (TTBR0 (CP15 s)) !! 0 \<and>
                              \<not>VSCTLR.EE (VSCTLR(CP15 s)) \<and>
                              VSCTLR.AFE (VSCTLR(CP15 s)) \<and>
                              VSCTLR.TRE (VSCTLR(CP15 s))"


definition 
  map_mem :: "(32 word \<Rightarrow> 8 word option) \<Rightarrow> (paddr \<Rightarrow> 8 word option)"
where 
  "map_mem m = (\<lambda>x. m (addr_val x))"

term Ftech_TranslateAddress

(*from Gerwin:
    TLB relation (de we have to do eviction in the isabelle version)
     privileged, iswrite, siz of mmu_translate*)


lemma
  "\<lbrakk> MMU_config_assert_isa s ; exception s = NoException;
      (Ftech_TranslateAddress (va , privileged, iswrite, siz)) s = (adrdesc, s');
     mmu_translate v (t :: 'a tlb_state_scheme) = (adrdesc', t') \<rbrakk> \<Longrightarrow> True"

oops

lemma
  "l3_valid (\<lambda>s. MMU_config_assert_isa s \<and>  exception s = NoException )
            (TranslationTableWalkSD (va , iswrite, siz)) 
              (\<lambda>r s'. if exception s' \<noteq> NoException 
                      then ptable_lift (map_mem (MEM s)) (Addr (reg'TTBR0 (TTBR0 (CP15 s)))) (Addr va) = None 
                      else  ptable_lift (map_mem (MEM s)) (Addr (reg'TTBR0 (TTBR0 (CP15 s)))) (Addr va) = Some (Addr  (paddress (addrdesc tlben))))"
  
oops


lemma sanity_check_MMU_config_assert:
  "MMU_config_assert () s = (True, s) \<Longrightarrow> MMU_config_assert_isa s"
  by (clarsimp simp: MMU_config_assert_def MMU_config_assert_isa_def  bind_def split_def read_state_def
                   split:if_split_asm)


definition 
  "mmu_config f \<equiv> 
        (\<forall> s s'. snd (f s) = s' \<longrightarrow>
                 MMU_config_assert_isa s \<longrightarrow> MMU_config_assert_isa s' )"


lemma mmu_config_bind [intro!, simp]:
  "\<lbrakk> mmu_config f; \<forall> x. mmu_config (g x) \<rbrakk> \<Longrightarrow> mmu_config (bind f g)"
  apply (clarsimp simp: mmu_config_def bind_def)
  by (clarsimp simp: split_def)



lemma mmu_config_if_else [intro!, simp]:
  "\<lbrakk> b \<longrightarrow> mmu_config f; \<not>b \<longrightarrow> mmu_config g \<rbrakk> \<Longrightarrow> 
     mmu_config (\<lambda>s. if b then f s else g s ) "
  by (clarsimp simp: mmu_config_def split: if_split_asm)

lemma mmu_config_if_else' [intro!, simp]:
  "\<lbrakk> b \<longrightarrow> mmu_config f; \<not>b \<longrightarrow> mmu_config g \<rbrakk> \<Longrightarrow> 
     mmu_config (if b then f else g ) "
  by (clarsimp simp: mmu_config_def split: if_split_asm)

lemma mmu_config_pair_simp [intro!, simp]:
  "mmu_config (Pair ())"
  by (clarsimp simp: mmu_config_def)
  

lemma mmu_config_read_st_simp [intro!, simp]:
  "mmu_config (read_state f)"
  by (clarsimp simp: mmu_config_def)


lemma mmu_config_update_st_mem_simp [intro!, simp]:
  "mmu_config (update_state (MEM_update v))"
  by (clarsimp simp: mmu_config_def MMU_config_assert_isa_def bind_def read_state_def)


lemma mmu_config_raise_excp [intro!, simp]:
  "mmu_config (raise'exception e)"
  apply (clarsimp simp: mmu_config_def raise'exception_def fst_def snd_def)
  by (clarsimp simp: bind_def read_state_def update_state_def MMU_config_assert_isa_def split: if_split_asm)


lemma mmu_config_pair_simp' [intro!, simp]:
  "mmu_config (Pair p)"
  by (clarsimp simp: mmu_config_def)

lemma mmu_config_pair_raise_excp' [intro!, simp]:
  "mmu_config (case x of None \<Rightarrow> raise'exception (UNPREDICTABLE ''undefined memory'') | Some v \<Rightarrow> Pair v)"
  by (clarsimp split: option.splits)


lemma mmu_config_pair_mem1 [intro!, simp]:
  "mmu_config (mem1 p)"
  apply (clarsimp simp: mem1_def)
  apply (rule mmu_config_bind; clarsimp)
  by (rule mmu_config_bind; clarsimp simp:  option.splits) 
  


lemma mmu_config_pair_mem [intro!, simp]:
  "mmu_config (mem (p, n))"
  by (clarsimp simp: mem_def)
 

lemma mmu_config_pair_write_mem [intro!, simp]:
  "mmu_config (write'mem (bl, p, n))"
  by (clarsimp simp: write'mem_def)


lemma mmu_config_translation_root [intro!, simp]:
  "mmu_config (translation_root va)"
  by (clarsimp simp: translation_root_def)


lemma mmu_config_HaveSecurityExt [intro!, simp]:
  "mmu_config (HaveSecurityExt ())"
  by (clarsimp simp: HaveSecurityExt_def)

lemma mmu_config_level1_desc_address_and_desc:
  "mmu_config (level1_desc_address_and_desc (a, b, mva))"
  sorry

lemma mmu_config_level2_desc_address_and_desc:
  "mmu_config (level2_desc_address_and_desc (b, mva, a))"
  sorry


lemma mmu_config_writing_access_flag:
  "mmu_config (writing_access_flag (a, b, c, d, e ,f, g ,h, i, j,k, l, m))"
  by (clarsimp simp: writing_access_flag_def)

lemma mmu_config_TLBResult:
  "mmu_config (TLBResult (a, b, c, d, e, f, g, h, i, j, k, l))"
  apply (clarsimp simp: TLBResult_def)
  sorry


lemma word_mask_two_bits_false [simp]:
  "\<lbrakk>n < 31; ucast ((w:: 32 word) && 3) \<noteq> (0 :: 2 word); ucast (w && 3) \<noteq> (1 :: 2 word); 
      ucast (w && 3) \<noteq> (2 :: 2 word); ucast (w && 3) \<noteq> (3 :: 2 word)\<rbrakk> \<Longrightarrow> False"
   apply word_bitwise
  by force

lemma remaining_induct_n[simp]:
  "\<lbrakk>word_extract (Suc n) n (w:: 32 word) \<noteq> (0 :: 2 word);
    word_extract (Suc n) n w \<noteq> (1 :: 2 word);
    word_extract (Suc n) n w \<noteq> (2 :: 2 word);
    word_extract (Suc n) n w \<noteq> (3 :: 2 word); (n:: nat) < 32 ;  n < 31 \<rbrakk> \<Longrightarrow> False"
  apply (clarsimp simp: word_extract_def word_bits_def mask_def )
  by (frule_tac w = "(w >> n)" in  word_mask_two_bits_false; clarsimp)


lemma mmu_config_TranslationTableWalkSD:
  "mmu_config  (TranslationTableWalkSD (mva, iswrite, sz))"
  apply (clarsimp simp: TranslationTableWalkSD_def)
  apply (rule, simp)
  apply (clarsimp simp: split_def)
  apply (rule, simp)
  apply (clarsimp, rule+, simp, simp, rule+)
   apply (clarsimp simp: mmu_config_level1_desc_address_and_desc)
  apply (rule+)
   apply clarsimp
   apply safe
     apply (clarsimp simp: Let_def)
     apply (rule)+
      apply (clarsimp simp: mmu_config_level2_desc_address_and_desc)
     apply (rule)
     apply (simp only: split_def, rule+, simp, rule+)
      apply (clarsimp simp: mmu_config_writing_access_flag)
     apply (rule)+
      apply (clarsimp simp: mmu_config_TLBResult)
     apply (rule, simp add: mmu_config_TLBResult)
    apply (clarsimp simp: Let_def, rule+, simp add: mmu_config_level2_desc_address_and_desc)
    apply (rule)+
    apply (simp only: split_def)
    apply (rule)+ apply clarsimp
    apply (rule)+
     apply (clarsimp simp: mmu_config_writing_access_flag)
    apply (rule)+
     apply (clarsimp simp: mmu_config_TLBResult)
    apply (rule)+
    apply (clarsimp simp: mmu_config_TLBResult)
   apply (simp only: Let_def)
   apply (rule)
    apply clarsimp
   apply rule+
       apply clarsimp
      apply clarsimp
     apply clarsimp
    apply clarsimp
   apply rule+
    apply (clarsimp simp: mmu_config_TLBResult)
   apply (clarsimp simp: mmu_config_TLBResult)
  by (drule remaining_induct_n; clarsimp)




(* defs for stating the lemma  *)




lemma
  "l3_valid (\<lambda>s. MMU_config_assert_isa s \<and>  ptable_lift (map_mem (MEM s)) (Addr (reg'TTBR0 (TTBR0 (CP15 s)))) (Addr va) =
        Some p   )
            (TranslationTableWalkSD (va , iswrite, siz)) 
              (\<lambda>r s'. exception s' = NoException \<longrightarrow> addr_val p =  paddress (addrdesc tlben))"
  


oops



end