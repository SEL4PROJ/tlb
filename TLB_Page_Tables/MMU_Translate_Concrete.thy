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


definition
  "pre_cond s t va  \<equiv> 
          MMU_config_assert_isa s \<and>
          tlb_rel s (typ_tlb t) \<and>
          dtlb_consistent (typ_tlb t) (Addr va) \<and>
          unitlb_consistent (typ_tlb t) (Addr va) "


(* keeping the pre_cond as it is for the time being *)
(*
lemma TranslateAddressV_wp:
  "\<lbrace>\<lambda>s. pre_cond s t t' va sz ip iw pa' mat \<rbrace>
         TranslateAddressV (va, ip, iw, sz)
  \<lbrace>\<lambda>rg s. \<forall>x. (\<exists>xa. rg = (x, xa)) \<longrightarrow> pa' = Addr (paddress x)\<rbrace>"
  sorry

*)

(* wp_comb requires validity of A in order to proceed *)

lemma TranslateAddress_exception_mmu_translate [wp]:
  "\<lbrace>\<lambda>s. \<exists>t pa' mematr . MMU_config_assert_isa s \<and>
                 tlb_rel s (typ_tlb t) \<and>
                 dtlb_consistent (typ_tlb t) (Addr va) \<and>
                 unitlb_consistent (typ_tlb t) (Addr va) \<and>
                 mmu_translate  (Addr va) siz ispriv iswrite True (t :: 'a::mmu tlb_state_scheme) = ((pa', mematr), t')\<rbrace>
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


(*  tlb consistency is needed here *)
(*
lemma TranslateAddressV_pt_walk [wp]:
  "\<lbrace>\<lambda>s. \<exists>t. MMU_config_assert_isa s \<and> 
        state_comp s (typ_tlb (t :: 'a tlb_state_scheme)) \<and>
        (\<forall>entry. pt_walk (asid t) (heap t) (ttbr0 t) (prrr t) (nmrr t)  (Addr va) = Some entry \<longrightarrow>
                 pa' = Addr (TLB.va_to_pa va entry)) \<rbrace> 
            TranslateAddressV(va, ispriv, iswrite,siz) 
       \<lbrace>\<lambda>rg s. \<forall>x. (\<exists>xa. rg = (x, xa)) \<longrightarrow> exception s = NoException \<longrightarrow> pa' = Addr (paddress x)\<rbrace>"
sorry
*)

lemma TranslateAddressV_pt_walk [wp]:
  "\<lbrace>\<lambda>s. \<exists>t. MMU_config_assert_isa s \<and>
                 tlb_rel s (typ_tlb (t :: 'a::mmu tlb_state_scheme)) \<and>
                 dtlb_consistent (typ_tlb t) (Addr va) \<and>
                 unitlb_consistent (typ_tlb t) (Addr va) \<and>
        (\<forall>entry. pt_walk (asid t) (heap t) (ttbr0 t) (prrr t) (nmrr t)  (Addr va) = Some entry \<longrightarrow>
                 pa' = Addr (TLB.va_to_pa va entry)) \<rbrace> 
            TranslateAddressV(va, ispriv, iswrite,siz) 
       \<lbrace>\<lambda>rg s. \<forall>x. (\<exists>xa. rg = (x, xa)) \<longrightarrow> exception s = NoException \<longrightarrow> pa' = Addr (paddress x)\<rbrace>"
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



lemma main_thm:
  "\<lbrace>\<lambda>s. MMU_config_assert_isa s \<and>
                 tlb_rel s (typ_tlb t) \<and>
                 dtlb_consistent (typ_tlb t) (Addr va) \<and>
                 unitlb_consistent (typ_tlb t) (Addr va) \<and>
                 mmu_translate  (Addr va) siz ispriv iswrite True (t :: 'a::mmu tlb_state_scheme) = ((pa', mematr), t')\<rbrace>
       (TranslateAddress (va , ispriv, iswrite, siz, True))
        \<lbrace>\<lambda>adrdesc s'.
           (exception s' \<noteq> NoException \<longrightarrow> excpt t' \<noteq> NoExcp) \<and>
           (exception s' = NoException \<longrightarrow>
              MMU_config_assert_isa s' \<and> 
              (pa' = Addr (paddress (adrdesc)) \<and> 
               mematr = mematr_typcast (AddressDescriptor.memattrs (adrdesc)) \<and> tlb_rel s' (typ_tlb t') \<and>
               dtlb_consistent (typ_tlb t') (Addr va) \<and> unitlb_consistent (typ_tlb t') (Addr va))) \<rbrace>"
  supply if_cong[cong] if_split[split del] 
  apply wpsimp
    apply (wpsimp simp: TranslateAddress_def write'DataTLB_def write'unified_mainTLB_def) 
          apply (wpsimp simp: lookupTLB_main_def entry_list_main_def mainTLBEntries_def)
          apply (rule for_loop_wp1; clarsimp?)
           apply (wpsimp simp: unified_mainTLB_def)
           apply (rule; clarsimp)
           apply (clarsimp split: if_split, rule, clarsimp, case_tac a; clarsimp)
    (* provable, if we assume tlbs consistency in the translateaddress lemma *)
           defer 
           apply (wpsimp simp: unified_mainTLB_def)
           apply (rule; clarsimp)
           apply (clarsimp split: if_split, rule, clarsimp, case_tac a; clarsimp)
           defer
           apply (wpsimp simp: lookupTLB_Data_micro_def)
          apply (wpsimp simp: lookupTLB_Data_micro_def entry_list_data_micro_def 
                              microDataTLBEntries_def)
          apply (rule for_loop_wp1; clarsimp?)
           apply (wpsimp simp: DataTLB_def)
           apply (rule; clarsimp)
           apply (clarsimp split: if_split, rule, clarsimp, case_tac a; clarsimp)
           defer
           apply (wpsimp simp: DataTLB_def)
           apply (rule; clarsimp)
           apply (clarsimp split: if_split, rule, clarsimp, case_tac a; clarsimp)
           defer
           apply (wpsimp simp: )
          apply (wpsimp simp: mainTLB_evict_def write'unified_mainTLB_def mainTLBEntries_def)
           apply (rule for_loop_wp2; wpsimp simp: unified_mainTLB_def)
            apply (rule)
             apply (clarsimp simp: MMU_config_assert_isa_def) 
            defer
            apply (rule)
             apply (clarsimp simp: MMU_config_assert_isa_def) 
             defer
             apply (wpsimp simp: )
            apply (wpsimp simp: microDataTLB_evict_def write'DataTLB_def microDataTLBEntries_def)
           apply (rule for_loop_wp2; wpsimp simp: DataTLB_def)
            apply (rule)
             apply (clarsimp simp: MMU_config_assert_isa_def) 
            defer
             apply (rule)
             apply (clarsimp simp: MMU_config_assert_isa_def) 
             defer
             apply (wpsimp simp: )
            apply (wpsimp simp: microInstrTLB_evict_def write'InstrTLB_def microInstrTLBEntries_def)
           apply (rule for_loop_wp2; wpsimp simp: InstrTLB_def)
            apply (rule)
             apply (clarsimp simp: MMU_config_assert_isa_def) 
            defer
             apply (rule)
             apply (clarsimp simp: MMU_config_assert_isa_def) 
             defer
           apply (wpsimp simp: )
           apply (wpsimp simp: TranslateAddress_def write'DataTLB_def write'unified_mainTLB_def)
oops

thm TranslationTableWalkSD_def[simplified]

lemma refine_paddr:
  "l3_valid
     (\<lambda>s. pre_cond s t va)
     (TranslateAddress (va , ispriv, iswrite, siz, True)) 
          (\<lambda>r s. pa' = Addr (paddress r))"
  supply (*if_cong[cong] *) if_split[split del] if_chain[simp del] word_2_cases[simp del] word_3_cases[simp del]
  apply (clarsimp simp: TranslateAddress_def)
  apply_trace (wpsimp simp: CheckDomain_def CheckPermission_def cong: if_cong)
       
        
oops


lemma 
  "\<lbrakk> \<And>i. \<lbrakk> start \<le> i; i \<le> end \<rbrakk> \<Longrightarrow>
  \<lbrace>\<lambda>s. P s \<and> (\<forall>j \<le> i. start \<le> j \<longrightarrow> Q' j s)\<rbrace> f i \<lbrace>\<lambda>_ s. P s \<and> (\<forall>j \<le> end. i \<le> j \<longrightarrow> Q' j s)\<rbrace>;
   start \<le> end \<rbrakk> \<Longrightarrow>
  \<lbrace>\<lambda>s. P s \<and> Q' start s\<rbrace> for_loop (start, end, f) \<lbrace>\<lambda>_ s. P s \<and> (\<forall>j \<le> end. start \<le> j \<longrightarrow> Q' j s)\<rbrace>"
apply (induct "(start,end,f)" arbitrary: start rule: for_loop.induct)
  apply (subst for_loop.simps)
  apply clarsimp
  apply wpsimp
   
oops




(*

          apply (rule TranslateAddressV_wp [of t va sz ip iw pa' mat t'])
         apply wpsimp
          apply (wpsimp simp: lookupTLB_main_def entry_list_main_def mainTLBEntries_def)
          apply (rule for_loop_wp0; clarsimp?)
          apply wpsimp
           apply (wpsimp simp: unified_mainTLB_def )
          apply (rule)+
            apply (case_tac "fst s", clarsimp)
            apply clarsimp
           apply (case_tac "fst s";clarsimp)
          apply (rule)+
          apply (clarsimp split: if_split)
          apply (rule)+
           apply (case_tac aa; clarsimp)
      (*    apply (rule l3_valid_conj_asum_false)
           apply (wpsimp simp: lookupTLB_main_def entry_list_main_def mainTLBEntries_def)
     apply (rule for_loop_wp0; clarsimp)
      apply (wpsimp simp: unified_mainTLB_def)
     apply (clarsimp simp: MatchingEntry_def)
     apply (case_tac x; clarsimp split: if_split)
      apply safe
      apply (case_tac aa; clarsimp) *)

         
      (*    apply (wpsimp simp: TranslateAddressV_def)
                    apply (wpsimp simp:  CheckPermission_def CurrentModeIsHyp_def BadMode_def  HaveSecurityExt_def HaveVirtExt_def
                                          ArchVersion_def CheckDomain_def)+
                 apply (clarsimp simp: TranslationTableWalkSD_def)
     apply (wpsimp simp: Let_def)
     apply (clarsimp simp: TLBResult_def)
         apply (wpsimp)          
   *)


oops
(*
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
   apply (rule for_loop_wp0; wpsimp)
   apply (case_tac aa, clarsimp)
   apply (rule conjI; clarsimp)
    apply force
     apply (clarsimp split: if_splits)
     apply clarsimp
   apply simp
   apply clarsimp
   apply (case_tac a; clarsimp)
   apply (rule conjI; clarsimp)
   apply fastforce
  apply (clarsimp split: if_splits)
  apply (rule conjI)
   defer
  apply fastforce
  apply (clarsimp split: if_splits)
  apply (case_tac list; clarsimp)
  *)

  

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
           (exception_in s' \<longrightarrow> exception_in t') \<and>
           (\<not>exception_in s' \<longrightarrow>
           MMU_config_assert_isa s' \<and> 
           (pa' = Addr (paddress (adrdesc)) \<and> 
           mematr = mematr_typcast (AddressDescriptor.memattrs (adrdesc)) \<and> tlb_rel s' (typ_tlb t') \<and>
           dtlb_consistent (typ_tlb t') (Addr va) \<and> unitlb_consistent (typ_tlb t') (Addr va))))"
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



(*lemma
  " \<And>rc re a b.
       \<lbrace>P398 rc re a
         b\<rbrace> for_loop
             (0, 1,
              \<lambda>i. do {
                   c \<leftarrow> trim_state (unified_mainTLB (word_of_int (int i)));
                   case c of None \<Rightarrow> Pair ()
                   | Some e \<Rightarrow>
                       if MatchingEntry (a, b, e) then do {
        v \<leftarrow> read_state fst;
        v \<leftarrow> do {
            v \<leftarrow> Pair (e, v);
            Pair (case v of (a, b) \<Rightarrow> a # b)
          };
        update_state (\<lambda>s. (v, snd s))
      }
                       else Pair ()
                 }) \<lbrace>\<lambda>r s. (\<forall>x. (case fst s of [] \<Rightarrow> ARM_Monadic.lookup_type.Miss
                                 | [e1] \<Rightarrow> ARM_Monadic.lookup_type.Hit e1
                                 | e1 # aa # lista \<Rightarrow> ARM_Monadic.lookup_type.Incon) =
                                ARM_Monadic.lookup_type.Hit x \<longrightarrow>
                                pa' = Addr (paddress (ARM_Monadic.va_to_pa (va, x)))) \<and>
                           ((case fst s of [] \<Rightarrow> ARM_Monadic.lookup_type.Miss
                             | [e1] \<Rightarrow> ARM_Monadic.lookup_type.Hit e1
                             | e1 # aa # lista \<Rightarrow> ARM_Monadic.lookup_type.Incon) =
                            ARM_Monadic.lookup_type.Incon \<longrightarrow>
                            (\<forall>r. pa' = Addr (paddress r))) \<and>
                           ((case fst s of [] \<Rightarrow> ARM_Monadic.lookup_type.Miss
                             | [e1] \<Rightarrow> ARM_Monadic.lookup_type.Hit e1
                             | e1 # aa # lista \<Rightarrow> ARM_Monadic.lookup_type.Incon) =
                            ARM_Monadic.lookup_type.Miss \<longrightarrow>
                            pre_cond (snd s) t t' va sz ip iw pa' mat)\<rbrace>"
  apply (clarsimp simp: for_loop.simps)
  apply (wpsimp simp: unified_mainTLB_def)
  apply (case_tac aa ; clarsimp)
  apply safe
  oops

*)

*)
end