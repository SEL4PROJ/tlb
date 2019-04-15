theory ARMv7A_Address_Translate_Ref

imports  MMU_Instants_TLB_PDC

begin    



lemma mmu_rel:
  "\<lbrakk> mmu_translate va s = (p, s') \<rbrakk>  \<Longrightarrow> s' = s \<lparr> non_det_tlb := non_det_tlb s' , exception:= exception s' \<rparr>"
   by (clarsimp simp: mmu_translate_non_det_tlb_state_ext_def Let_def  raise'exception_def split:lookup_type.splits if_split_asm)


lemma mmu_sat_rel:
  "\<lbrakk> mmu_translate va s = (p, s') \<rbrakk>  \<Longrightarrow> s' = s \<lparr> sat_tlb := sat_tlb s' , exception:= exception s' \<rparr>"
  by (clarsimp simp: mmu_translate_sat_tlb_state_ext_def Let_def  raise'exception_def split:lookup_type.splits if_split_asm)


lemma mmu_incon_rel:
  "\<lbrakk>  mmu_translate va t = (pa', t')\<rbrakk>  \<Longrightarrow> (t'::'a set_tlb_state_scheme) = t\<lparr>exception := exception t'\<rparr>"
  by (clarsimp simp: mmu_translate_set_tlb_state_ext_def Let_def raise'exception_def split: if_split_asm)

lemma mmu_eq_asid_root_mem:
  "\<lbrakk> mmu_translate va (s::'a non_det_tlb_state_scheme) = (pa , s') \<rbrakk>  \<Longrightarrow>  ASID s = ASID s' \<and> TTBR0 s = TTBR0 s' \<and>  MEM s = MEM s'"
  by (clarsimp simp: mmu_translate_non_det_tlb_state_ext_def Let_def raise'exception_def  split: lookup_type.splits if_split_asm)
 
lemma mmu_sat_eq_asid_root_mem:
  "\<lbrakk> mmu_translate va (s::'a sat_tlb_state_scheme) = (pa , s') \<rbrakk>  \<Longrightarrow> ASID s = ASID s' \<and> TTBR0 s = TTBR0 s' \<and> MEM s = MEM s'"
  by (clarsimp simp: mmu_translate_sat_tlb_state_ext_def Let_def  raise'exception_def split:lookup_type.splits if_split_asm)

lemma mmu_incon_eq_asid_root_mem:
  "\<lbrakk> mmu_translate va (s::'a set_tlb_state_scheme) = (pa , s') \<rbrakk>  \<Longrightarrow> ASID s = ASID s' \<and> TTBR0 s = TTBR0 s' \<and> MEM s = MEM s'"
  by (clarsimp simp: mmu_translate_set_tlb_state_ext_def Let_def  raise'exception_def split:lookup_type.splits if_split_asm)

lemma mmu_translate_sat_tlb_union:
  "mmu_translate v s = (p,t) \<Longrightarrow> 
      fst(sat_tlb t) = fst(sat_tlb s) \<union> the ` {e\<in>pt_walk (ASID s) (MEM s) (TTBR0 s) ` UNIV. \<not>is_fault e} \<and> 
      snd(sat_tlb t) = snd(sat_tlb s) \<union> the ` {e\<in>pdc_walk (ASID s) (MEM s) (TTBR0 s) ` UNIV. \<not>is_fault e}"
  by (clarsimp simp:  mmu_translate_sat_tlb_state_ext_def Let_def raise'exception_def split:lookup_type.splits if_split_asm) 




lemma mmu_translate_saturated_tlb_unchange:
  "\<lbrakk> mmu_translate va s = (pa, s'); saturated (typ_sat_tlb s) \<rbrakk>
       \<Longrightarrow> sat_tlb s' = sat_tlb s"
  apply (clarsimp simp:  mmu_translate_sat_tlb_state_ext_def Let_def saturated_def  raise'exception_def
                  split: lookup_type.splits if_split_asm)
  by (smt subset_pairunion)+


lemma mmu_translate_saturated_tlb_unchange_pair:
  "\<lbrakk> mmu_translate va s = (pa, s'); saturated (typ_sat_tlb s) \<rbrakk>
       \<Longrightarrow> fst(sat_tlb s') = fst(sat_tlb s) \<and> snd(sat_tlb s') = snd(sat_tlb s)"
  apply (clarsimp simp:  mmu_translate_sat_tlb_state_ext_def Let_def saturated_def  raise'exception_def
                  split: lookup_type.splits if_split_asm)
  by blast+


lemma mmu_translate_incon_unchange:
  "\<lbrakk> mmu_translate va t = (aa, ba)\<rbrakk>  \<Longrightarrow> set_tlb ba = set_tlb t"
  by (clarsimp simp: mmu_translate_set_tlb_state_ext_def Let_def raise'exception_def split: if_split_asm)


lemma mmu_translate_saturated_state:
  "mmu_translate v s = (p,t) \<Longrightarrow>   saturated (typ_sat_tlb t)"
  apply (clarsimp simp: mmu_translate_sat_tlb_state_ext_def Let_def split: lookup_type.splits)
    by (clarsimp simp: saturated_def raise'exception_def split:if_split_asm)+

lemma mmu_translate_sat_const_tlb [simp]:
  "saturated (typ_sat_tlb s) \<Longrightarrow> fst(sat_tlb (snd (mmu_translate va s))) = fst(sat_tlb s) \<and>
     snd(sat_tlb (snd (mmu_translate va s))) = snd(sat_tlb s)"
  apply (simp add: mmu_translate_sat_tlb_state_ext_def Let_def raise'exception_def fst_def split: lookup_type.splits)
  using sat_state_tlb by fastforce


lemma mmu_translate_non_det_sat_refine:
  "\<lbrakk> mmu_translate va s = (pa, s'); consistent (typ_sat_tlb t) va; tlb_rel_sat (typ_non_det_tlb s) (typ_sat_tlb t)  \<rbrakk> \<Longrightarrow>
       let (pa', t') = mmu_translate va t
       in pa' = pa \<and> consistent (typ_sat_tlb t') va \<and> tlb_rel_sat (typ_non_det_tlb s') (typ_sat_tlb t')"
  apply (frule (1) tlb_rel_sat_consistent, clarsimp)     
  apply (frule consistent_not_Incon_imp', clarsimp)
  apply (frule tlb_rel_satD, clarsimp)
  apply (insert asid_tlb_mono [of "(fst (non_det_tlb s) - fst (tlb_evict (typ_non_det_tlb s)))"  "fst (sat_tlb t) \<union> the ` {e\<in>pt_walk (ASID s) (MEM s) (TTBR0 s) ` UNIV. \<not>is_fault e}" "ASID s" "( va)"])
  apply (insert asid_pdc_mono [of "(snd (non_det_tlb s) - snd (tlb_evict (typ_non_det_tlb s)))"  "snd (sat_tlb t) \<union> the ` {e\<in>pdc_walk (ASID s) (MEM s) (TTBR0 s) ` UNIV. \<not>is_fault e}" "ASID s" "( va)"])
  apply (insert saturated_tlb_pde [of t] , clarsimp) 
  apply (clarsimp simp: mmu_translate_sat_tlb_state_ext_def  Let_def split: lookup_type.splits)
   apply (subgoal_tac "is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) va)")
    prefer 2
    apply (frule_tac va = va in  sat_miss_fault; clarsimp)
   apply (clarsimp simp: mmu_translate_non_det_tlb_state_ext_def Let_def split:lookup_type.splits)
       apply ((clarsimp simp: raise'exception_def split_def tlb_rel_sat_def typ_sat_tlb_def typ_non_det_tlb_def
        pairsub_def saturated_def state.defs  consistent0'_def  split:if_split_asm); blast)
      apply (metis (no_types, hide_lams) consistent_not_Incon_imp' fst_conv lookup_asid_pdc_incon_minus old.prod.exhaust pairsub_def snd_conv)
     apply (subgoal_tac "lookup_pdc (snd (sat_tlb t)) (ASID s) va = Hit x3")
      prefer 2
      apply (subgoal_tac "snd (non_det_tlb s) - snd (tlb_evict (typ_non_det_tlb s)) \<subseteq> snd (sat_tlb t)", clarsimp simp: pairsub_def less_eq_lookup_type)
      apply (force simp: saturated_def pairsub_def)
     apply (subgoal_tac "lookup_pdc (snd (sat_tlb t) \<union> the ` {e\<in>pdc_walk (ASID s) (MEM s) (TTBR0 s) ` UNIV. \<not>is_fault e})
                            (ASID s) va = Hit x3")
      prefer 2
      apply force
     apply (drule lookup_asid_pdc_hit_union_cases')
     apply (erule disjE, clarsimp)
      apply (drule lookup_pdc_miss_is_fault, clarsimp simp: is_fault_def)
     apply (erule disjE, clarsimp)
     apply clarsimp
     apply (frule lookup_pdc_range_fault_pt_walk)
     apply (drule_tac x = va in bspec)
      apply(clarsimp simp: lookup_asid_pdc_hit_entry_range)
     apply (drule pdc_entry_pt_walk, simp) 
     apply ((clarsimp simp: raise'exception_def split_def tlb_rel_sat_def typ_sat_tlb_def typ_non_det_tlb_def
        pairsub_def saturated_def state.defs  consistent0_def  split:if_split_asm); blast)
    apply (force simp: pairsub_def)
   apply (force simp: pairsub_def)
  apply (subgoal_tac "\<not>is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) va)")
   prefer 2
   apply (clarsimp simp: is_fault_def)
  apply (subgoal_tac "\<not>is_fault (pdc_walk (ASID s) (MEM s) (TTBR0 s) va)")
   prefer 2
   apply (clarsimp simp: no_fault_pt_no_fault_pde)
  apply (subgoal_tac "lookup'' (fst (sat_tlb t)) (ASID s) va = Hit (the (pt_walk (ASID s) (MEM s) (TTBR0 s) va))")
   prefer 2
   apply clarsimp
  apply (subgoal_tac "va_to_pa va y = va_to_pa va (the (pt_walk (ASID s) (MEM s) (TTBR0 s) va))")
   prefer 2
   apply clarsimp
  apply (thin_tac "lookup'' (fst (sat_tlb t)) (ASID s) va = Hit y")
  apply (thin_tac "pt_walk (ASID s) (MEM s) (TTBR0 s) va = Some y")
  apply (simp only:)
  apply (thin_tac "va_to_pa va y = va_to_pa va (the (pt_walk (ASID s) (MEM s) (TTBR0 s) va))")
  apply (clarsimp simp: mmu_translate_non_det_tlb_state_ext_def Let_def split: lookup_type.splits)

      apply (clarsimp simp: tlb_rel_sat_def split_def typ_sat_tlb_def typ_non_det_tlb_def saturated_def pairsub_def lookup_in_tlb state.defs)
      apply blast
     apply (metis (no_types, hide_lams) consistent_not_Incon_imp' fst_conv lookup_asid_pdc_incon_minus old.prod.exhaust pairsub_def snd_conv)
    apply (subgoal_tac "lookup_pdc (snd (sat_tlb t)) (ASID s) va = Hit x3")
     prefer 2
     apply (subgoal_tac "snd (non_det_tlb s) - snd (tlb_evict (typ_non_det_tlb s)) \<subseteq> snd (sat_tlb t)", clarsimp simp: pairsub_def less_eq_lookup_type)
     apply (force simp: saturated_def pairsub_def)
    apply (subgoal_tac "lookup_pdc (snd (sat_tlb t) \<union> the ` {e\<in>pdc_walk (ASID s) (MEM s) (TTBR0 s) ` UNIV. \<not>is_fault e})
                            (ASID s) va = Hit x3")
     prefer 2
     apply force
    apply (drule lookup_asid_pdc_hit_union_cases')
    apply (erule disjE, clarsimp)
     apply (drule lookup_pdc_miss_is_fault, clarsimp simp: is_fault_def)
    apply (erule disjE, clarsimp)
    apply clarsimp
    apply (frule lookup_pdc_range_fault_pt_walk)
    apply (drule_tac x = va in bspec, clarsimp simp: lookup_asid_pdc_hit_entry_range)
    apply (subgoal_tac "pdc_walk (ASID s) (MEM s) (TTBR0 s) va = Some ya")
     prefer 2 
     apply force
    apply (thin_tac " ya = the (pdc_walk (ASID s) (MEM s) (TTBR0 s) va)") 
    apply (drule pdc_entry_pt_walk, simp) 
    apply (clarsimp simp: raise'exception_def split_def tlb_rel_sat_def typ_sat_tlb_def typ_non_det_tlb_def saturated_def state.defs  consistent0_def  pairsub_def split:if_split_asm)
    apply blast
   apply (force simp: pairsub_def)
  apply (subgoal_tac "x3 = the (pt_walk (ASID s) (MEM s) (TTBR0 s) va)")
   apply clarsimp
   apply (clarsimp simp: tlb_rel_sat_def split_def typ_sat_tlb_def typ_non_det_tlb_def saturated_def state.defs pairsub_def lookup_in_tlb)
   apply blast
  apply (clarsimp simp: pairsub_def) 
  apply (subgoal_tac "lookup'' (fst (non_det_tlb s)) (ASID s) va = Hit x3")
  using consistent_not_Incon_imp' apply auto[1]
  apply (subgoal_tac "lookup'' (fst (non_det_tlb s)) (ASID s) va \<noteq> Incon")
   apply (subgoal_tac "fst (non_det_tlb s) - fst (tlb_evict (typ_non_det_tlb s)) \<subseteq> fst (non_det_tlb s)")
  using lookup_asid_tlb_hit_incon_minus apply fastforce
   apply blast
  by (clarsimp simp: consistent0'_def)





lemma mmu_translate_sat_tlb_pdc_incon_refine_pa:
  "\<lbrakk> mmu_translate va s = (pa, s');  mmu_translate va t = (pa', t') ;
           va \<notin> iset (set_tlb t) ; tlb_rel_abs (typ_sat_tlb s) (typ_set_tlb t) \<rbrakk> \<Longrightarrow> 
                                          pa = pa'"
  apply (frule_tac s = s in tlb_rel_abs_consistent ; clarsimp )
  apply (frule tlb_rel_absD , clarsimp)
  apply (clarsimp simp: mmu_translate_set_tlb_state_ext_def mmu_translate_sat_tlb_state_ext_def split_def Let_def)
  apply (subgoal_tac "fst(sat_tlb s) = fst(sat_tlb s) \<union> the ` {e\<in>pt_walk (ASID s) (MEM s) (TTBR0 s) ` UNIV. \<not>is_fault e}")
   prefer 2
   apply (fastforce simp: saturated_def)
  apply (cases "lookup'' (fst (sat_tlb s) \<union> the ` {e\<in>pt_walk (ASID s) (MEM s) (TTBR0 s) ` UNIV. \<not>is_fault e}) (ASID s) va")
    apply clarsimp
    apply (frule_tac va = va in  sat_miss_fault, simp) 
    apply (clarsimp simp: raise'exception_def is_fault_def split:if_split_asm)
   apply (clarsimp simp: consistent0'_def)
  apply (subgoal_tac "x3 = the (pt_walk (ASID s) (MEM s) (TTBR0 s) va)")
   prefer 2
   apply (clarsimp simp: consistent0'_def)
  apply (subgoal_tac "\<not>is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) va)")
   prefer 2
   apply (clarsimp simp: is_fault_def lookup_in_tlb consistent0'_def)
  apply clarsimp
  done


lemma mmu_translate_sat_consistent:
  "\<lbrakk> mmu_translate va s = (pa, s');  consistent (typ_sat_tlb s) va ; saturated (typ_sat_tlb s)\<rbrakk>  \<Longrightarrow>  
                   consistent (typ_sat_tlb s') va"
  apply (subgoal_tac "fst(sat_tlb s) = fst(sat_tlb s) \<union> the ` {e\<in>pt_walk (ASID s) (MEM s) (TTBR0 s) ` UNIV. \<not>is_fault e} \<and>
                      snd(sat_tlb s) = snd(sat_tlb s) \<union> the ` {e\<in>pdc_walk (ASID s) (MEM s) (TTBR0 s) ` UNIV. \<not>is_fault e}")
   prefer 2
   apply (fastforce simp: saturated_def)
  apply (clarsimp simp: mmu_translate_sat_tlb_state_ext_def Let_def  split: lookup_type.splits)
   apply (clarsimp simp: raise'exception_def split:if_split_asm)+
  done



lemma mmu_translate_sat_tlb_pdc_incon_refine_tlb_rel:
  "\<lbrakk> mmu_translate va s = (pa, s');  mmu_translate va t = (pa', t') ;
           va \<notin> iset (set_tlb t) ; tlb_rel_abs (typ_sat_tlb s) (typ_set_tlb t) \<rbrakk> \<Longrightarrow> 
                                          tlb_rel_abs  (typ_sat_tlb s') (typ_set_tlb t')"
  apply (frule_tac s = s in tlb_rel_abs_consistent ; clarsimp )
  apply (frule tlb_rel_absD , clarsimp)
  apply (frule_tac mmu_translate_sat_consistent ; clarsimp simp: tlb_rel_abs_def incon_addrs_def inconsistent_vaddrs_def incoherrent_vaddrs_def)
    (* TLB is not changing as s is already saturated *)
  apply (subgoal_tac "s' = s\<lparr>exception := exception s'\<rparr> \<and> t' = t\<lparr>exception := exception t'\<rparr>")
   apply (subgoal_tac "exception t' = exception s'")
    apply (cases t, cases t, cases s, cases s', clarsimp simp: state.defs saturated_def global_range_def)
   prefer 2
   apply (frule mmu_incon_rel, clarsimp)
   apply (subgoal_tac "sat_tlb s' = sat_tlb s")
    apply (drule mmu_sat_rel, clarsimp)
   apply (metis (no_types, lifting) Un_def fst_def mmu_translate_sat_tlb_union prod_eqI saturated_tlb_pde)
  apply (subgoal_tac "fst(sat_tlb s') = fst(sat_tlb s) \<union> the ` {e\<in>pt_walk (ASID s) (MEM s) (TTBR0 s) ` UNIV. \<not>is_fault e} \<and> 
                      snd(sat_tlb s') = snd(sat_tlb s) \<union> the ` {e\<in>pdc_walk (ASID s) (MEM s) (TTBR0 s) ` UNIV. \<not>is_fault e} \<and> 
                               ASID s' = ASID s  \<and> MEM s' = MEM s \<and> TTBR0 s' = TTBR0 s")
   apply (clarsimp simp: mmu_translate_sat_tlb_state_ext_def split_def Let_def)
   apply (cases "lookup'' (fst(sat_tlb s) \<union> the ` {e\<in>pt_walk (ASID s) (MEM s) (TTBR0 s) ` UNIV. \<not>is_fault e}) (ASID s) va")
     apply clarsimp
     apply (frule_tac va = va in sat_miss_fault, simp add: saturated_def)
      apply (meson lookup_asid_tlb_miss_union)
     apply (clarsimp simp: mmu_translate_set_tlb_state_ext_def raise'exception_def is_fault_def)
     apply (cases"exception s = NoException", simp)  apply (cases t, cases s, cases t', cases s', clarsimp) apply (cases t, cases s, cases t', cases s', clarsimp)
    apply (clarsimp simp: consistent0'_def)
   apply (subgoal_tac "x3 = the (pt_walk (ASID s) (MEM s) (TTBR0 s) va)")
    prefer 2
    apply (clarsimp simp: consistent0'_def)
   apply (subgoal_tac "\<not>is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) va)")
    prefer 2
    apply (clarsimp simp: consistent0'_def is_fault_def lookup_in_asid_tlb)
   apply (simp only: mmu_translate_set_tlb_state_ext_def Let_def is_fault_def)  apply (cases t, cases s, cases t', cases s', clarsimp)
  apply (simp only: mmu_translate_sat_tlb_union mmu_sat_eq_asid_root_mem is_fault_def) 
  done


lemma mmu_translate_sat_tlb_pdc_incon_refine_consistent:
  "\<lbrakk> mmu_translate va s = (pa, s');  mmu_translate va t = (pa', t') ;
           va \<notin> iset (set_tlb t) ; tlb_rel_abs (typ_sat_tlb s) (typ_set_tlb t) \<rbrakk> \<Longrightarrow> 
                                          va \<notin> iset (set_tlb t')"
  apply (frule_tac s = s in tlb_rel_abs_consistent ; clarsimp )
  apply (frule tlb_rel_absD , clarsimp)
  apply (clarsimp simp: mmu_translate_set_tlb_state_ext_def  Let_def mmu_translate_sat_tlb_state_ext_def split_def)
  apply (subgoal_tac "fst(sat_tlb s) = fst(sat_tlb s) \<union> the ` {e\<in>pt_walk (ASID s) (MEM s) (TTBR0 s) ` UNIV. \<not>is_fault e}")
   prefer 2
   apply (fastforce simp: saturated_def)
  apply (cases "lookup'' (fst (sat_tlb s) \<union> the ` {e\<in>pt_walk (ASID s) (MEM s) (TTBR0 s) ` UNIV. \<not>is_fault e}) (ASID s) va")
    apply clarsimp
    apply (frule_tac va = va in  sat_miss_fault, simp) 
    apply (clarsimp simp: raise'exception_def is_fault_def split:if_split_asm)
   apply (clarsimp simp: consistent0'_def)
  apply (subgoal_tac "x3 = the (pt_walk (ASID s) (MEM s) (TTBR0 s) va)")
   prefer 2
   apply (clarsimp simp: consistent0'_def)
  apply (subgoal_tac "\<not>is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) va)")
   prefer 2
   apply (clarsimp simp: is_fault_def lookup_in_tlb consistent0'_def)
  apply clarsimp
  done


lemma mmu_translate_sat_incon_refine:
  "\<lbrakk> mmu_translate va s = (pa, s');  mmu_translate va t = (pa', t') ;
           va \<notin> iset (set_tlb t) ; tlb_rel_abs (typ_sat_tlb s) (typ_set_tlb t) \<rbrakk> \<Longrightarrow> 
                              pa = pa' \<and>  tlb_rel_abs  (typ_sat_tlb s') (typ_set_tlb t')  \<and> 
                              va \<notin> iset (set_tlb t')"
  by (clarsimp simp: mmu_translate_sat_tlb_pdc_incon_refine_pa mmu_translate_sat_tlb_pdc_incon_refine_tlb_rel
      mmu_translate_sat_tlb_pdc_incon_refine_consistent)



lemma mmu_translate_non_det_sat_subset_rel:
  "\<lbrakk> mmu_translate va s = (pa, s'); consistent (typ_sat_tlb t) va; 
       tlb_rel_sat (typ_non_det_tlb s) (typ_sat_tlb t) ; mmu_translate va t = (pa', t')  \<rbrakk> \<Longrightarrow>
         fst(non_det_tlb s') \<subseteq> fst(sat_tlb t') \<and> snd(non_det_tlb s') \<subseteq> snd(sat_tlb t')"
  by (drule_tac t = t in  mmu_translate_non_det_sat_refine [unfolded tlb_rel_sat_def];
           simp add: tlb_rel_sat_def)


lemma mmu_translate_non_det_sat_excp:
  "\<lbrakk> mmu_translate va s = (p, s') ; mmu_translate va t = (p, t') ;
     consistent (typ_sat_tlb t) va; tlb_rel_sat (typ_non_det_tlb s) (typ_sat_tlb t)\<rbrakk>  \<Longrightarrow>  exception s' = exception t'"
  apply (subgoal_tac "tlb_rel_sat (typ_non_det_tlb s') (typ_sat_tlb t')")
   apply (clarsimp simp: tlb_rel_sat_def state.defs)
  apply (drule (2)  mmu_translate_non_det_sat_refine, clarsimp simp: Let_def)
 done

lemma mmu_translate_sat_state_param:
  "\<lbrakk> mmu_translate va t = (pa', t') ; saturated (typ_sat_tlb t) \<rbrakk> \<Longrightarrow>
      state.more t' = state.more t \<and> ASID t' = ASID t \<and> MEM t' = MEM t \<and> TTBR0 t' = TTBR0 t \<and>  saturated (typ_sat_tlb t')"
  apply (frule sat_state_tlb)
  apply (clarsimp simp: mmu_translate_sat_tlb_state_ext_def Let_def raise'exception_def
      state.defs saturated_def split: lookup_type.splits if_split_asm) 
      apply(cases t, cases t', clarsimp simp: subset_antisym)+ 
  done


lemma mmu_translate_non_det_sat_mem_excp:
  "\<lbrakk> mmu_translate va s = (p, s') ; mmu_translate va t = (p', t') ;
     consistent (typ_sat_tlb t) va; tlb_rel_sat (typ_non_det_tlb s) (typ_sat_tlb t)\<rbrakk>  \<Longrightarrow> MEM s' = MEM t' \<and> exception s' = exception t'"
  apply (subgoal_tac "tlb_rel_sat (typ_non_det_tlb s') (typ_sat_tlb t')")
   apply (clarsimp simp: tlb_rel_sat_def state.defs)
  apply (drule (2)  mmu_translate_non_det_sat_refine, clarsimp simp: Let_def)
  done


lemma  mmu_translate_non_det_sat_pa:
  "\<lbrakk> mmu_translate va s = (pa, s'); tlb_rel_sat (typ_non_det_tlb s) (typ_sat_tlb t)  ; consistent (typ_sat_tlb t) va;
         mmu_translate va t = (pa', t')  \<rbrakk> \<Longrightarrow> pa = pa'"
  using mmu_translate_non_det_sat_refine by fastforce

lemma mmu_translate_sat_incon_mem_excp:
  "\<lbrakk> mmu_translate va s = (p, s') ; mmu_translate va t = (p', t') ;
     va \<notin> iset (set_tlb t); tlb_rel_abs (typ_sat_tlb s) (typ_set_tlb t)\<rbrakk>  \<Longrightarrow> MEM s' = MEM t' \<and> exception s' = exception t'"
  apply (subgoal_tac "tlb_rel_abs (typ_sat_tlb s') (typ_set_tlb t')")
   apply (clarsimp simp: tlb_rel_abs_def state.defs)
  by (drule (2)  mmu_translate_sat_incon_refine; clarsimp simp: Let_def)



end