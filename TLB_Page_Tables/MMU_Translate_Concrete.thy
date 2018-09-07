theory MMU_Translate_Concrete
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

lemma is_it:
  "l3_valid (\<lambda>s. \<forall>r. P r 
               (s \<lparr> exception := exception(snd (CheckPermission (a, b, c, d, e, f, g, h) s)) \<rparr>)) 
     (CheckPermission (a, b, c, d, e, f, g, h)) 
        P"
  apply (clarsimp simp: l3_valid_def CheckPermission_def)
  apply safe
     apply (clarsimp simp: trim_state_def extend_state_def read_state_def bind_def)
     apply (clarsimp split: if_split_asm )
             apply (clarsimp simp: trim_state_def extend_state_def read_state_def bind_def update_state_def)
             apply (clarsimp split: if_split_asm )
                    apply (clarsimp simp: trim_state_def extend_state_def read_state_def bind_def update_state_def)
                    apply (clarsimp simp: raise'exception_def trim_state_def extend_state_def read_state_def bind_def update_state_def
      split: if_split_asm )+
             apply (clarsimp simp: word_bit_field_insert_def word_modify_def bitstring_modify_def)
             apply word_bitwise
             apply force
            apply (clarsimp simp: raise'exception_def trim_state_def extend_state_def read_state_def bind_def update_state_def
      split: if_split_asm )+
     apply word_bitwise
     apply force
    apply (clarsimp simp: trim_state_def extend_state_def read_state_def bind_def)
    apply (clarsimp split: if_split_asm )
          apply (clarsimp simp: trim_state_def extend_state_def read_state_def bind_def update_state_def)
          apply (clarsimp split: if_split_asm )
               apply (clarsimp simp: trim_state_def extend_state_def read_state_def bind_def update_state_def)
               apply (clarsimp simp: raise'exception_def trim_state_def extend_state_def read_state_def bind_def update_state_def
      split: if_split_asm )+
          apply (clarsimp simp: word_bit_field_insert_def word_modify_def bitstring_modify_def)
          apply word_bitwise
          apply force
         apply (clarsimp simp: raise'exception_def trim_state_def extend_state_def read_state_def bind_def update_state_def
      split: if_split_asm )+
    apply word_bitwise
    apply force
   apply (clarsimp simp: trim_state_def extend_state_def read_state_def bind_def)
   apply (clarsimp split: if_split_asm )
        apply (clarsimp simp: trim_state_def extend_state_def read_state_def bind_def update_state_def)
        apply (clarsimp split: if_split_asm )
            apply (clarsimp simp: trim_state_def extend_state_def read_state_def bind_def update_state_def)
            apply (clarsimp simp: raise'exception_def trim_state_def extend_state_def read_state_def bind_def update_state_def
      split: if_split_asm )+
        apply (clarsimp simp: word_bit_field_insert_def word_modify_def bitstring_modify_def)
        apply word_bitwise
        apply force
       apply (clarsimp simp: raise'exception_def trim_state_def extend_state_def read_state_def bind_def update_state_def
      split: if_split_asm )+
   apply word_bitwise
   apply force
  apply (clarsimp simp: trim_state_def extend_state_def read_state_def bind_def)
  apply (clarsimp split: if_split_asm )
     apply (clarsimp simp: trim_state_def extend_state_def read_state_def bind_def update_state_def)
     apply (clarsimp split: if_split_asm )
       apply (clarsimp simp: trim_state_def extend_state_def read_state_def bind_def update_state_def)
       apply (clarsimp simp: raise'exception_def trim_state_def extend_state_def read_state_def bind_def update_state_def
      split: if_split_asm )+
     apply (clarsimp simp: word_bit_field_insert_def word_modify_def bitstring_modify_def)
     apply word_bitwise
     apply force
    apply (clarsimp simp: raise'exception_def trim_state_def extend_state_def read_state_def bind_def update_state_def
      split: if_split_asm )+
  apply word_bitwise
  by force

(*
  apply (rule wp_pre)
  apply (clarsimp simp: CheckPermission_def)
  apply safe
  apply (rule wp)+
  apply (word_bitwise)
  apply force
   apply (rule wp)+
  apply (word_bitwise)
  apply force
   apply (rule wp)+
   apply (rule wp_pre)
     apply (rule wp)

    apply (case_tac "AFE (VSCTLR (CP15 (snd s)))"; clarsimp)
     apply (case_tac "word_bit_field_insert 0 0 (1::1 word) (a:: 3 word) = (0:: 3 word)"; clarsimp)
    apply (clarsimp split: if_split_asm)
    apply (case_tac "word_bit_field_insert 0 0 (1::1 word) (a:: 3 word) = (1:: 3 word)"; clarsimp)
    apply (clarsimp split: if_split_asm)
*)

lemma undefined_False[wp]:
  "l3_valid (\<lambda>_. False) HOL.undefined Q'"
  by (simp add: l3_valid_def)

lemma if_chain[simp]:
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

lemma TranslateAddressV_wp[wp]:
  "\<lbrace>\<lambda>s. MMU_config_assert_isa s \<and>
        (\<exists>t mematr t'. tlb_rel s (typ_tlb t) \<and>
           mmu_translate (Addr va) siz ispriv iswrite True t = ((pa', mematr), t'))\<rbrace>
  TranslateAddressV (va, ispriv, iswrite, siz)
  \<lbrace>\<lambda>rg s. \<forall>x. (\<exists>xa. rg = (x, xa)) \<longrightarrow> pa' = Addr (paddress x)\<rbrace>"
  sorry

term for_loop

lemma for_loop_wp0:
  "\<lbrakk> \<And>i. \<lbrakk> start \<le> i; i \<le> end \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> f i \<lbrace>\<lambda>_. P\<rbrace>; start \<le> end \<rbrakk> \<Longrightarrow>
  \<lbrace>P\<rbrace> for_loop (start, end, f) \<lbrace>\<lambda>_. P\<rbrace>"
  apply (induct "(start,end,f)" arbitrary: start rule: for_loop.induct)
  apply (subst for_loop.simps)
  apply clarsimp
  apply wpsimp
   apply force
  apply assumption
  done

thm l3_valid_weak_pre[no_vars]

lemma l3_valid_post:
  "\<lbrakk>\<lbrace>P\<rbrace> f \<lbrace>Q'\<rbrace>; \<And>r s. Q' r s \<Longrightarrow> Q'' r s\<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q''\<rbrace>"
  by (auto simp: l3_valid_def)

lemmas for_loop_wp = for_loop_wp0[THEN l3_valid_post]

lemma refine_paddr:
  "l3_valid
     (\<lambda>s. MMU_config_assert_isa s \<and>
          tlb_rel s (typ_tlb t) \<and>
          dtlb_consistent (typ_tlb t) (Addr va) \<and>
          unitlb_consistent (typ_tlb t) (Addr va) \<and>
          mmu_translate (Addr va) siz ispriv iswrite True t = ((pa', mematr), t'))
     (TranslateAddress (va, ispriv, iswrite, siz, True)) 
          (\<lambda>r s. pa' = Addr (paddress r))"
  supply if_cong[cong] if_split[split del]
   apply (clarsimp simp: TranslateAddress_def)
  apply (wpsimp simp: CheckDomain_def CheckPermission_def write'DataTLB_def
                      write'unified_mainTLB_def)
  apply (simp add: lookupTLB_main_def ds_id_def)
  apply wpsimp
  apply (simp add: entry_list_main_def mainTLBEntries_def)
  apply (wpsimp simp: unified_mainTLB_def)
   apply (case_tac aa; clarsimp)
   apply (rule conjI; clarsimp)
   apply fastforce
  apply (clarsimp split: if_splits)
  apply (rule conjI)
   defer
  apply fastforce
  apply (clarsimp split: if_splits)
  apply (case_tac list; clarsimp)
  

  

               (*  
                apply (rule wp_pre) 
                 apply ((rule wp)+; clarsimp?)
                   
                   apply ((rule wp)+; clarsimp?)
                  apply ((rule wp)+; clarsimp?)
                 apply ((rule wp)+; clarsimp?)
                prefer 2

            *)
               
sorry



(* thm hoare_vcg_split_case_option *)

lemma main_thm:
  "l3_valid (\<lambda>s. MMU_config_assert_isa s \<and> tlb_rel s (typ_tlb t) \<and> dtlb_consistent (typ_tlb t) (Addr va) \<and> 
                  unitlb_consistent (typ_tlb t) (Addr va) \<and>
                mmu_translate  (Addr va) siz ispriv iswrite True (t :: 'a tlb_state_scheme) = ((pa', mematr), t'))
       (TranslateAddress (va , ispriv, iswrite, siz, True))
        (\<lambda>adrdesc s'. 
           MMU_config_assert_isa s' \<and> 
           (pa' = Addr (paddress (adrdesc)) \<and> 
           mematr = mematr_typcast (AddressDescriptor.memattrs (adrdesc)) \<and> tlb_rel s' (typ_tlb t') \<and>
           dtlb_consistent (typ_tlb t') (Addr va) \<and> unitlb_consistent (typ_tlb t') (Addr va)))"
  apply (rule l3_valid_conj_post)
   apply (rule_tac P = "MMU_config_assert_isa"  in  wp_pre; clarsimp simp: l3_valid_def)
   apply ((insert mmu_config_TranslateAddress [of va ispriv iswrite siz]) [1], force simp: mmu_config_def)
  apply (rule l3_valid_conj_post)
   apply (clarsimp simp: refine_paddr)
  
   

oops




lemma is_it':
  "l3_valid (\<lambda>s. \<forall>r. P r (s \<lparr> exception := exception(snd (CheckDomain (a, b, c, d) s)) \<rparr>) ) 
          (CheckDomain (a, b, c, d)) 
            (\<lambda> r s. P r s)"
  apply (clarsimp simp: CheckDomain_def)
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
  apply (rule l3_valid_conj_post)
   apply (rule_tac P = "MMU_config_assert_isa"  in  wp_pre)
    prefer 2
    apply clarsimp
   apply (clarsimp simp: l3_valid_def)
   apply (insert mmu_config_TranslateAddress [of va ispriv iswrite siz]) [1]
   apply (clarsimp simp: mmu_config_def)
   apply force
   apply (clarsimp simp: to_do)

oops




(*


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

*)

end