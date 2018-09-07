theory MMU_Translate_Concrete
imports  L3_LIB.L3_Hoare_Logic
         MMU_Configuration
         "~/verification/l4v/lib/Apply_Trace" 
begin

notation (output) ARM_Monadic.lookup_type.Miss  ("Miss")
notation (output) ARM_Monadic.lookup_type.Incon ("Incon")
notation (output) ARM_Monadic.lookup_type.Hit   ("Hit")

named_theorems wp_case

lemma l3_valid_case_split [wp_case]:
  "\<lbrakk> \<And>a.  x = a \<Longrightarrow>  l3_valid P  (f a) Q'\<rbrakk> \<Longrightarrow> 
     l3_valid P  (case x of a \<Rightarrow> f a) Q'"
  by (clarsimp simp:)


lemma l3_valid_case_split' :
  "\<lbrakk> \<And>a' b' c' d' e' f' g' h'.  (a,b,c,d,e,fd,g,h) = (a',b',c',d',e',f',g', h') \<Longrightarrow> 
                                 l3_valid P  (f a' b' c' d' e' f' g' h') Q'\<rbrakk> \<Longrightarrow> 
     l3_valid P  (case (a,b,c,d,e,fd,g,h) of (a',b',c',d',e',f',g', h') \<Rightarrow> f a' b' c' d' e' f' g' h') Q'"
  by (clarsimp simp:)

lemma l3_valid_case_split'' :
  "\<lbrakk> \<And>a' b' c' d'.  (a,b,c,d) = (a',b',c',d') \<Longrightarrow>
                                 l3_valid P  (f a' b' c' d') Q'\<rbrakk> \<Longrightarrow> 
     l3_valid P  (case (a,b,c,d) of (a',b',c',d') \<Rightarrow> f a' b' c' d') Q'"
  by (clarsimp simp:)


lemma 
  "\<lbrakk> \<And>e. lva = Hit e \<Longrightarrow>  l3_valid P (AH e) Q';
         lva = Incon \<Longrightarrow>  l3_valid P AI Q';
         lva = Miss  \<Longrightarrow>  l3_valid P AM Q'\<rbrakk> \<Longrightarrow> 
          l3_valid P (case lva of Hit e \<Rightarrow> AH e 
                         | Incon \<Rightarrow> AI
                         | Miss \<Rightarrow> AM) Q'"
  by (cases lva; clarsimp)


lemma l3_valid_lookup_cases [wp,intro!, simp]:
  "\<lbrakk> \<And>lva e. lva = Hit e \<Longrightarrow>  l3_valid (P lva e) (fh lva e) (Y lva);
    \<And>lva. lva = Incon \<Longrightarrow>  l3_valid (Q' lva) (fi lva) (Y lva);
    \<And>lva. lva = Miss  \<Longrightarrow>  l3_valid (R' lva) (fm lva) (Y lva) \<rbrakk> \<Longrightarrow> 
          l3_valid (\<lambda>s. (\<forall>e.  lva = Hit e \<longrightarrow>  P lva e s) \<and>
                             (lva = Incon \<longrightarrow>  Q' lva  s)  \<and>
                             (lva = Miss  \<longrightarrow>  R' lva  s))
                     (case lva of Hit e \<Rightarrow> fh lva e 
                        |   Incon \<Rightarrow> fi lva
                        |   Miss \<Rightarrow> fm lva) (Y lva)"
  apply(simp add: l3_valid_def split_def)
  by(case_tac lva, simp_all)


lemma l3_valid_raise'exception[wp, intro!, simp]:
  "l3_valid (\<lambda>s. \<forall>r. if exception s = NoException 
                      then  P r (s \<lparr>exception := e \<rparr>)
                      else  P r s )  (raise'exception e) P"
  apply (clarsimp simp: raise'exception_def)
  apply (rule wp_pre)
  by ((rule wp)+ , simp)
 

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
  sorry

lemma refine_paddr:
  "l3_valid
     (\<lambda>s. MMU_config_assert_isa s \<and>
          tlb_rel s (typ_tlb t) \<and>
          dtlb_consistent (typ_tlb t) (Addr va) \<and>
          unitlb_consistent (typ_tlb t) (Addr va) \<and>
          mmu_translate (Addr va) siz ispriv iswrite True t = ((pa', mematr), t'))
     (TranslateAddress (va, ispriv, iswrite, siz, True)) 
          (\<lambda>r s. pa' = Addr (paddress r))"
  apply (rule wp_pre) 
   apply (clarsimp simp: TranslateAddress_def)
   apply ((rule wp)+; clarsimp?)
              apply (clarsimp simp: CheckPermission_def)
              apply (safe)
                 apply ((rule wp)+; clarsimp?)
                    
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