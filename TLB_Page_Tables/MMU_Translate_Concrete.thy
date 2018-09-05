theory MMU_Translate_Concrete
imports  L3_LIB.L3_Hoare_Logic
         MMU_Translate_Refine
         MMU_ARM.ARM_Monadic
        MMU_Configuration
begin

(* write the real lemma, first in terms of l3 *)

term l3_valid

lemma  conj_post:
 "\<lbrakk>l3_valid P' f Q'; l3_valid P' f Q'' \<rbrakk> \<Longrightarrow> l3_valid P' f (\<lambda>r s. Q' r s \<and> Q'' r s)"
  by (simp add: l3_valid_def)

term
  "corres sr r P P' f f'"

lemma
  "corres (\<lambda>s t. MMU_config_assert_isa s \<and> tlb_rel s (typ_tlb t) \<and> dtlb_consistent (typ_tlb t) (Addr va) \<and> unitlb_consistent (typ_tlb t) (Addr va))
          (\<lambda>(pa', mematr) adrdesc. pa' = Addr (paddress (adrdesc)) \<and> 
             mematr = mematr_typcast (AddressDescriptor.memattrs (adrdesc)))
          (\<lambda>_. True) (\<lambda>_. True) 
          (mmu_translate  (Addr va) siz ispriv iswrite True) 
          (TranslateAddress (va , ispriv, iswrite, siz, True))"
  apply (unfold  TranslateAddress_def)
  apply (simp flip: bind_assoc)


oops

(*declare for_loop.simps [simp add]*)

lemma abc:
  "l3_valid (\<lambda>s. P () (snd (mainTLB_evict () s)) ) (mainTLB_evict ()) P"
  apply (clarsimp simp: mainTLB_evict_def)
    apply ((rule wp)+ ; (clarsimp simp: write'unified_mainTLB_def mainTLBEntries_def)?)
    apply ((rule wp)+ ; (clarsimp simp:)?)

sorry

lemma abc':
  "l3_valid (\<lambda>s. P () (snd (microDataTLB_evict () s)) ) (microDataTLB_evict ()) P"
  apply (clarsimp simp: microDataTLB_evict_def)
  apply ((rule wp)+ ; (clarsimp simp: write'DataTLB_def microDataTLBEntries_def)?)
    apply ((rule wp)+ ; (clarsimp simp:)?)
   apply (clarsimp simp: for_loop.simps)
 
sorry

lemma abc'':
  "l3_valid (\<lambda>s. P () (snd (microInstrTLB_evict () s)) ) (microInstrTLB_evict ()) P"

sorry

lemma 
  "l3_valid (\<lambda>s. MMU_config_assert_isa s \<and> tlb_rel s (typ_tlb t) \<and> dtlb_consistent (typ_tlb t) (Addr va) \<and> unitlb_consistent (typ_tlb t) (Addr va))
      (TranslateAddress (va , ispriv, iswrite, siz, True))
        (\<lambda>adrdesc s'. 
           MMU_config_assert_isa s' \<and> 
           (mmu_translate  (Addr va) siz ispriv iswrite True (t :: 'a tlb_state_scheme) = ((pa', mematr), t') \<longrightarrow>
           pa' = Addr (paddress (adrdesc)) \<and> 
           mematr = mematr_typcast (AddressDescriptor.memattrs (adrdesc)) \<and> tlb_rel s' (typ_tlb t') \<and>
           dtlb_consistent (typ_tlb t') (Addr va) \<and> unitlb_consistent (typ_tlb t') (Addr va)))"
  apply (rule conj_post)
   apply (rule_tac P = "MMU_config_assert_isa"  in  wp_pre)
    prefer 2
    apply clarsimp
   apply (clarsimp simp: l3_valid_def)
   apply (insert mmu_config_TranslateAddress [of va ispriv iswrite siz]) [1]
   apply (clarsimp simp: mmu_config_def)
   apply force
  apply (clarsimp simp: TranslateAddress_def)
  apply (rule l3_valid_bind_weak)
  apply ((rule wp)+ ; clarsimp?)
   apply (rule abc)
    apply clarsimp
 apply (rule abc')
    apply clarsimp
apply (rule abc'')
    apply clarsimp
oops
term mainTLB_evict
declare [[show_types]]

lemma
  "l3_valid (\<lambda>s. Q' () (s \<lparr>main_TLB := main_TLB s \<rparr>)  ) (mainTLB_evict ()) Q'"

oops


    apply (clarsimp simp: mainTLB_evict_def)
    apply ((rule wp)+ ; clarsimp?)
      apply (clarsimp simp: write'unified_mainTLB_def)
      apply ((rule wp)+ ; clarsimp?)
     apply (clarsimp simp: mainTLBEntries_def)
    apply (clarsimp simp: for_loop.simps)
     apply ((rule wp)+; (clarsimp simp: unified_mainTLB_def write'unified_mainTLB_def)?)
   
apply clarsimp
 apply (rule wp)+ apply clarsimp
apply (rule wp)
apply (rule wp)
apply (rule wp)
apply (rule wp)
apply (rule wp)
apply (rule wp)
apply (rule wp)
apply (rule wp)

  (*
  apply (rule wp_pre)
  apply (clarsimp simp:  TranslateAddress_def )
  apply (rule wp)+
  apply (clarsimp simp: mainTLB_evict_def)
    apply (rule wp)+
  apply (clarsimp simp: for_loop.simps write'unified_mainTLB_def)
 apply (rule wp)+
  apply (clarsimp simp: microInstrTLBEntries_def)
 apply (clarsimp simp: for_loop.simps unified_mainTLB_def write'unified_mainTLB_def)
  *)
 oops



(*
lemma  
  "\<lbrakk>MMU_config_assert_isa s;  tlb_rel s (typ_tlb t); 
     TranslateAddress (va , ispriv, iswrite, siz, data_exe) s = (adrdesc, s') ; 
     mmu_translate  (Addr va) siz ispriv iswrite data_exe (t :: 'a tlb_state_scheme) = ((pa' , mematr), t')\<rbrakk> \<Longrightarrow>
         pa' = Addr (paddress (adrdesc)) \<and> 
         AddressDescriptor.memattrs (adrdesc) = mematr_typcast' mematr \<and>  tlb_rel s' (typ_tlb t')"
 oops

lemma
  "valid (\<lambda>s. MMU_config_assert_isa s \<and> tlb_rel s (typ_tlb t)) 
     TranslateAddress (va , ispriv, iswrite, siz, data_exe)
     (\<lambda>adrdesc s'. 
     mmu_translate  (Addr va) siz ispriv iswrite data_exe (t :: 'a tlb_state_scheme) = ((pa' , mematr), t') \<longrightarrow>
         pa'    = Addr (paddress (adrdesc)) \<and> 
         mematr = mematr_typcast (AddressDescriptor.memattrs (adrdesc)) \<and> tlb_rel s' (typ_tlb t'))"
*)


  

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