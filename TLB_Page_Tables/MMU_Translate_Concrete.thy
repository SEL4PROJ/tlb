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
                              \<not>VSCTLR.AFE (VSCTLR(CP15 s)) \<and>  \<comment> \<open>hardware access flag is disabled\<close>
                              VSCTLR.TRE (VSCTLR(CP15 s))"



fun
  mem_typcast :: "TLB.MemType_t \<Rightarrow> ARM_Monadic.MemType_t"
where
  "mem_typcast TLB.MemType_Normal = ARM_Monadic.MemType_Normal"
| "mem_typcast TLB.MemType_Device = ARM_Monadic.MemType_Device"
| "mem_typcast TLB.MemType_StronglyOrdered = ARM_Monadic.MemType_StronglyOrdered"


definition
  mematr_typcast :: "TLB.MemoryAttributes \<Rightarrow> ARM_Monadic.MemoryAttributes"
where
  "mematr_typcast mematr = \<lparr> 
     MemType         = mem_typcast (TLB.MemoryAttributes.MemType mematr),
     innerattrs      = TLB.MemoryAttributes.innerattrs mematr,
     innerhints      = TLB.MemoryAttributes.innerhints mematr,
     innertransient  = TLB.MemoryAttributes.innertransient mematr,
     outerattrs      = TLB.MemoryAttributes.outerattrs mematr,
     outerhints      = TLB.MemoryAttributes.outerhints mematr,
     outershareable  = TLB.MemoryAttributes.outershareable mematr,
     outertransient  = TLB.MemoryAttributes.outertransient mematr,
     shareable       = TLB.MemoryAttributes.shareable mematr\<rparr>"


fun
  excp_typcast :: "ARM_Monadic.exception \<Rightarrow> MMU_Translate_Refine.Exception"
where
  "excp_typcast (ARM_Monadic.ASSERT string)                  = MMU_Translate_Refine.ASSERT string"
| "excp_typcast (ARM_Monadic.IMPLEMENTATION_DEFINED string)  = MMU_Translate_Refine.IMPLEMENTATION_DEFINED string"
| "excp_typcast (ARM_Monadic.MMU_Exception string)           = MMU_Translate_Refine.MMU_Exception string"
| "excp_typcast  ARM_Monadic.NoException                      = MMU_Translate_Refine.NoException "
| "excp_typcast (ARM_Monadic.UNPREDICTABLE string)           = MMU_Translate_Refine.UNPREDICTABLE string"
| "excp_typcast (ARM_Monadic.VFP_EXCEPTION string)           = MMU_Translate_Refine.VFP_EXCEPTION string"



definition
  state_comp :: "state \<Rightarrow> tlbs_set cstate_scheme \<Rightarrow> bool"
where
  "state_comp s t \<equiv>  
      (\<lambda>p. (MEM s) (addr_val p)) = heap t \<and>
      (Addr (reg'TTBR0 (TTBR0 (CP15 s) ) ) ) = ttbr0 t \<and> 
      ASID (CONTEXTIDR (CP15 s) )   = cstate.asid t \<and>
      excp_typcast(exception  s) = cstate.Exception t \<and>      
      (reg'PRRR (PRRR (CP15 s) ) )  = prrr t \<and>
      (reg'NMRR (NMRR (CP15 s) ) )  = nmrr t \<and>
      (reg'DACR (DACR (CP15 s) ) )  = dacr t"

consts tlbtypcastt :: "TLBEntry \<Rightarrow> tlb_entry"

definition
  tlb_rel :: "state \<Rightarrow> tlbs_set cstate_scheme \<Rightarrow> bool"
where
  "tlb_rel s t \<equiv>  state_comp s t \<and>
                  tlbtypcastt ` {entry. \<forall>ad. (micro_DataTLB s) ad = Some entry} \<subseteq> dtlb_set (cstate.more t) \<and> 
                  tlbtypcastt ` {entry. \<forall>ad. (micro_InstrTLB s) ad = Some entry} \<subseteq> itlb_set (cstate.more t) \<and> 
                  tlbtypcastt ` {entry. \<forall>ad. (main_TLB s) ad = Some entry} \<subseteq> unitlb_set (cstate.more t) "


 (*
consistent and exception

 *)

(*

definition
  "consistent0 m asid ttbr0 tlb va \<equiv>
     lookup tlb asid (addr_val va) = Hit (pt_walk asid m ttbr0 va) \<or>
     lookup tlb asid (addr_val va) = Miss"


abbreviation
  "consistent (s::tlb_entry set state_scheme) \<equiv>
               consistent0 (MEM s) (ASID s) (TTBR0 s) (state.more s)"

*)


definition 
  typ_tlb :: "'a tlb_state_scheme \<Rightarrow> tlbs_set cstate_scheme"
where
  "typ_tlb s =  cstate.extend (cstate.truncate s) (tlbs_set s)"



definition 
  map_mem :: "(32 word \<Rightarrow> 8 word option) \<Rightarrow> (paddr \<Rightarrow> 8 word option)"
where 
  "map_mem m = (\<lambda>x. m (addr_val x))"

lemma  
  "\<lbrakk>MMU_config_assert_isa s;  tlb_rel s (typ_tlb t); 
     TranslateAddress (va , ispriv, iswrite, siz, data_exe) s = (adrdesc, s') ; 
     mmu_translate  (Addr va) siz ispriv iswrite data_exe (t :: 'a tlb_state_scheme) = ((pa' , mematr), t')\<rbrakk> \<Longrightarrow>
         Addr (paddress (adrdesc)) = pa' \<and> 
         AddressDescriptor.memattrs (adrdesc) = mematr_typcast mematr \<and>  tlb_rel s' (typ_tlb t')"

(* exception function *)

(* have to change lookup, then consistent, and then exception *)



oops

lemma  
  "\<lbrakk>TranslateAddress (va , privileged, iswrite, siz, data_exe) s = (adrdesc, s'); 
     consistent (typ_det_tlb t) va;  
     tlb_rel (typ_det_tlb s) (typ_det_tlb t)\<rbrakk> \<Longrightarrow>
     let (adrdesc', t') = mmu_translate  (va , privileged, iswrite, siz, data_exe) (t :: 'a tlb_state_scheme)
         in pa' = pa \<and> consistent (typ_det_tlb t') va \<and> tlb_rel (typ_det_tlb s') (typ_det_tlb t')"

definition
  tlb_rel :: "tlb_entry set state_scheme \<Rightarrow> tlb_entry set state_scheme \<Rightarrow> bool"
where
  "tlb_rel s t \<equiv> state.truncate s = state.truncate t \<and> state.more s \<subseteq> state.more t  \<and> no_faults (state.more t)"






lemma
  "\<lbrakk> MMU_config_assert_isa s ; exception s = NoException;
      (TranslateAddress (va , privileged, iswrite, siz)) s = (adrdesc, s');
     mmu_translate v (t :: 'a tlb_state_scheme) = (adrdesc', t') \<rbrakk> \<Longrightarrow> True"

oops

lemma
  "l3_valid (\<lambda>s. MMU_config_assert_isa s \<and>  exception s = NoException )
            (TranslationTableWalkSD (va , iswrite, siz)) 
              (\<lambda>r s'. if exception s' \<noteq> NoException 
                      then ptable_lift (map_mem (MEM s)) (Addr (reg'TTBR0 (TTBR0 (CP15 s) ) ) ) (Addr va) = None 
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