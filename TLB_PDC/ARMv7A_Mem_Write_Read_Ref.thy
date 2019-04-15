theory ARMv7A_Mem_Write_Read_Ref

imports  ARMv7A_Address_Translate_Ref

begin               



lemma  mmu_write_rel:
  "\<lbrakk>mmu_write_size (val,va, sz) s = ((), s')\<rbrakk>   \<Longrightarrow>  s' = s \<lparr> non_det_tlb := non_det_tlb s' , MEM:= MEM s' , exception:= exception s' \<rparr>"
  apply (clarsimp simp:  mmu_write_size_non_det_tlb_state_ext_def Let_def, cases "mmu_translate va s", clarsimp split: if_split_asm)
   apply (drule write_mem_rel, cases "mmu_translate va s" , clarsimp)
   apply (drule mmu_rel, cases s, cases s', case_tac b, clarsimp)
  apply (clarsimp simp: mmu_translate_non_det_tlb_state_ext_def Let_def split: lookup_type.splits)
      by (clarsimp simp: Let_def raise'exception_def split:if_split_asm)+



lemma mmu_write_sat_tlb_disj:
  "\<lbrakk> mmu_write_size (val,va, sz) s = ((), s') \<rbrakk> \<Longrightarrow>
     fst(non_det_tlb s') = fst(pairsub (non_det_tlb s)  (tlb_evict (typ_non_det_tlb s))) \<or>  fst(non_det_tlb s') = fst(pairsub (non_det_tlb s)  (tlb_evict (typ_non_det_tlb s))) \<union> {the (pt_walk (ASID s) (MEM s) (TTBR0 s) va)} \<or>
     fst(non_det_tlb s') = fst(pairsub (non_det_tlb s)  (tlb_evict (typ_non_det_tlb s))) \<union>  the ` (\<lambda>x. pde_tlb_entry x (MEM s) va) ` {x. lookup_pdc  (snd (pairsub (non_det_tlb s) (tlb_evict (typ_non_det_tlb s)))) (ASID s) va = Hit x }"
  apply (clarsimp simp:  mmu_write_size_non_det_tlb_state_ext_def mmu_translate_non_det_tlb_state_ext_def split_def Let_def write_mem_eq_TLB raise'exception_def 
      split: lookup_type.splits split: if_split_asm)
    apply (drule write_mem_eq_TLB state.defs)
    apply (cases s , cases s' ; clarsimp)
   apply (drule write_mem_eq_TLB state.defs)
   apply (cases s , cases s' ; clarsimp)
  apply (drule write_mem_eq_TLB state.defs)
  by (cases s , cases s' ; clarsimp)
 
lemma mmu_write_sat_pdc_disj:
  "\<lbrakk> mmu_write_size (val,va, sz) s = ((), s') \<rbrakk> \<Longrightarrow>
     snd(non_det_tlb s') =  snd (pairsub (non_det_tlb s)  (tlb_evict (typ_non_det_tlb s))) \<or>
         snd(non_det_tlb s') =  snd(pairsub (non_det_tlb s)  (tlb_evict (typ_non_det_tlb s))) \<union> {the (pdc_walk (ASID s) (MEM s) (TTBR0 s) va)}"
  apply (clarsimp simp:  mmu_write_size_non_det_tlb_state_ext_def mmu_translate_non_det_tlb_state_ext_def split_def Let_def write_mem_eq_TLB raise'exception_def 
      split: lookup_type.splits split: if_split_asm)
    apply (drule write_mem_eq_TLB state.defs)
    apply (cases s , cases s' ; clarsimp)
   apply (drule write_mem_eq_TLB state.defs)
   apply (cases s , cases s' ; clarsimp)
  apply (drule write_mem_eq_TLB state.defs)
  by (cases s , cases s' ; clarsimp)



(**************************************************************)

lemma mmu_write_saturated_state:
  "\<lbrakk>mmu_write_size (val,va,sz) s = ((), t)  \<rbrakk>  \<Longrightarrow> saturated (typ_sat_tlb t)"
  apply (clarsimp simp: mmu_write_size_sat_tlb_state_ext_def Let_def)
  apply (case_tac "mmu_translate va s" , clarsimp)
  apply (clarsimp split: if_split_asm)
   apply (case_tac "write'mem1 (val, a, sz) b" , clarsimp)
   apply (subgoal_tac "ASID s = ASID ba \<and> TTBR0 s = TTBR0 ba ")
    apply (clarsimp simp: saturated_def)
   apply (subgoal_tac "ASID s = ASID b \<and> TTBR0 s = TTBR0 b")
    apply clarsimp
    apply (clarsimp simp:  write'mem1_def Let_def)
    apply (clarsimp split: if_split_asm)
    apply (clarsimp simp:  raise'exception_def)
   apply (clarsimp simp: mmu_translate_sat_tlb_state_ext_def Let_def raise'exception_def split:lookup_type.splits if_split_asm)
  using mmu_translate_saturated_state surjective_pairing by blast



lemma mmu_wrtie_sat_rel:
  "\<lbrakk>mmu_write_size (val,va, sz) s = ((), s')\<rbrakk>   \<Longrightarrow> 
      s' = s \<lparr> sat_tlb := sat_tlb s' , MEM:= MEM s' , exception:= exception s' \<rparr>"
  apply (clarsimp simp: mmu_write_size_sat_tlb_state_ext_def Let_def)
  apply (cases "mmu_translate va s" , clarsimp)
  apply (clarsimp split: if_split_asm)
   apply (case_tac " write'mem1 (val, a, sz) b", clarsimp)
   apply (drule write_mem_rel)
   apply (drule mmu_sat_rel)
   apply (cases s, cases s', case_tac a, case_tac b, case_tac ba)
   apply clarsimp
  apply (clarsimp simp: mmu_translate_sat_tlb_state_ext_def Let_def split: lookup_type.splits)
   apply (clarsimp simp: raise'exception_def  split:if_split_asm) 
  by (clarsimp simp: raise'exception_def split:if_split_asm)



lemma mmu_write_tlb_subset:
  "\<lbrakk> mmu_write_size (val,va, sz) s = ((), s'); tlb_rel_sat (typ_non_det_tlb s) (typ_sat_tlb t) ; consistent (typ_sat_tlb t) va ;
        mmu_write_size (val,va, sz) t = ((), t') \<rbrakk> \<Longrightarrow> 
          fst (non_det_tlb s') \<subseteq> fst(sat_tlb t') \<and> snd (non_det_tlb s') \<subseteq> snd (sat_tlb t')"
  apply (frule tlb_rel_satD)
  apply (clarsimp simp:  mmu_write_size_non_det_tlb_state_ext_def , cases "mmu_translate va s" , clarsimp)
  apply (clarsimp simp:  mmu_write_size_sat_tlb_state_ext_def , cases "mmu_translate va t" , clarsimp)
  apply (frule_tac t' = ba and s' = b and t = t and s = s and pa' = aa in mmu_translate_non_det_sat_subset_rel; simp?)
  apply (subgoal_tac "non_det_tlb b = non_det_tlb s'", clarsimp split: if_split_asm)
    apply (case_tac "write'mem1 (val, aa, sz) ba", clarsimp simp:)
    apply (subgoal_tac "state.more bb = state.more ba")
     apply force
    apply (drule write_mem_eq_TLB)  
    apply (drule write_mem_eq_TLB)
    apply (clarsimp simp: typ_sat_tlb_def)
   apply (case_tac "write'mem1 (val, aa, sz) ba", simp)
   apply (subgoal_tac "state.more ba = state.more b")
    apply force
   apply (drule write_mem_eq_TLB)  
   apply (clarsimp simp: typ_sat_tlb_def)
  apply (clarsimp split: if_split_asm)
   apply (drule write_mem_eq_TLB)
   apply (cases s' , case_tac b, clarsimp simp:)
  apply (drule write_mem_eq_TLB)
  by (cases s' , case_tac b, clarsimp simp:)


lemma mmu_write_non_det_sat_mem:
  "\<lbrakk> mmu_write_size (val,va, sz) s = ((), s');  tlb_rel_sat (typ_non_det_tlb s) (typ_sat_tlb t) ; consistent (typ_sat_tlb t) va; 
                   mmu_write_size (val,va, sz) t = ((), t') \<rbrakk> \<Longrightarrow> MEM s' = MEM t'"
  apply (frule tlb_rel_satD)
  apply (clarsimp simp:  mmu_write_size_non_det_tlb_state_ext_def , cases "mmu_translate va s" , clarsimp)
  apply (clarsimp simp:  mmu_write_size_sat_tlb_state_ext_def , cases "mmu_translate va t" , clarsimp)
  apply (subgoal_tac "MEM ba = MEM b \<and>  exception ba = exception b")
   prefer 2
   apply (frule_tac t = t and t' = ba in mmu_translate_non_det_sat_mem_excp; simp)
  apply (subgoal_tac "a = aa")
   prefer 2
   apply (frule  mmu_translate_non_det_sat_pa; simp)
  apply simp
  apply (clarsimp split: if_split_asm)
  apply (case_tac "write'mem1 (val, aa, sz) ba", simp)
  apply (frule_tac t = ba and t' = bb in  write_same_mem, simp, simp)
  by (case_tac bb, cases t', simp)

 

lemma mmu_write_size_non_det_sat_state_trunc:
  "\<lbrakk>mmu_write_size (val,va, sz) s = ((), s'); tlb_rel_sat (typ_non_det_tlb s) (typ_sat_tlb t)  ; consistent (typ_sat_tlb t) va;
     mmu_write_size (val,va, sz) t = ((), t')\<rbrakk> \<Longrightarrow> state.truncate t' = state.truncate s'"
  apply (frule (3)  mmu_write_non_det_sat_mem)
  apply (frule tlb_rel_satD, clarsimp)
  apply (frule mmu_write_rel)
  apply (rotate_tac)
  apply (frule mmu_wrtie_sat_rel)
  apply (clarsimp simp: tlb_rel_sat_def)
  apply (subgoal_tac "exception s' = exception t'")
   apply (cases s, cases t, cases s' , cases t')
   apply (clarsimp simp: state.defs)
  apply (clarsimp simp: mmu_write_size_sat_tlb_state_ext_def mmu_write_size_non_det_tlb_state_ext_def Let_def)
  apply (case_tac "mmu_translate va t" , case_tac "write'mem1 (val, a, sz) b" , clarsimp)
  apply (case_tac "mmu_translate va s" , clarsimp)
  apply (subgoal_tac "exception b = exception bb \<and> a = aa")
   apply (clarsimp split: if_split_asm)
   apply (subgoal_tac "MEM b = MEM bb ")
    apply (frule_tac s="bb" and s'="s'" and t = b and t' = ba in write_same_mem_excep ; clarsimp)
   apply (frule_tac s="s" and s'="bb" and t = t and t' = b and p' = aa in mmu_translate_non_det_sat_mem_excp ; clarsimp simp: consistent0_def tlb_rel_sat_def)
  apply (rule conjI)
   apply (frule_tac s = "s" and s' = "bb" and t = "t" and t' = "b" in   mmu_translate_non_det_sat_excp ; clarsimp simp: tlb_rel_sat_def)
  by (frule_tac t= t and pa' = a and t' = b in mmu_translate_non_det_sat_pa ; clarsimp simp: tlb_rel_sat_def) +




lemma mmu_write_non_det_sat_refine:
  "\<lbrakk> mmu_write_size (val,va, sz) s = ((), s'); tlb_rel_sat (typ_non_det_tlb s) (typ_sat_tlb t)  ; consistent (typ_sat_tlb t) va;
        mmu_write_size (val,va, sz) t = ((), t') \<rbrakk> \<Longrightarrow>  tlb_rel_sat (typ_non_det_tlb s') (typ_sat_tlb t') "
  apply (clarsimp simp: tlb_rel_sat_def)
  apply (clarsimp simp: mmu_write_saturated_state)
  apply (rule conjI)
    prefer 2       
    apply (frule_tac s = s and s' = s' and t = t and t' = t' in mmu_write_tlb_subset; clarsimp simp: tlb_rel_sat_def)
  by (frule_tac s="s" and s'="s'" and t="t" and t'="t'" in mmu_write_size_non_det_sat_state_trunc; clarsimp simp: tlb_rel_sat_def)        
 


(* refinement between saturated and second abstracted model *)


lemma mmu_write_incon_set_rel:
  "\<lbrakk> saturated (typ_sat_tlb s) ; 
       inconsistent_vaddrs (typ_sat_tlb s) \<subseteq> iset(set_tlb t) ;  incoherrent_vaddrs (typ_sat_tlb s) \<subseteq> iset(set_tlb t) ; ASID s = ASID r ; TTBR0 s = TTBR0 r\<rbrakk> \<Longrightarrow>
     inconsistent_vaddrs (typ_sat_tlb (r\<lparr>sat_tlb := pairunion (sat_tlb s) (the ` {e \<in> range (pt_walk (ASID r) (MEM q) (TTBR0 r)). \<not> is_fault e}, 
           the ` {e \<in> range (pdc_walk (ASID r) (MEM q) (TTBR0 r)). \<not> is_fault e})\<rparr>))
           \<subseteq> iset (set_tlb t) \<union> incon_comp (ASID r) (ASID r) (MEM s) (MEM q) (TTBR0 r) (TTBR0 r)"
  apply (clarsimp)
  apply (clarsimp simp: inconsistent_vaddrs_def incon_comp_def ptable_comp_def  incoherrent_vaddrs_def)
  apply (erule disjE)
   apply (drule union_asid_tlb_incon_cases)
   apply (erule disjE, clarsimp simp: asid_tlb_lookup_range_pt_walk_not_incon)
   apply (erule disjE, clarsimp simp: entry_leq_def)
    apply (erule disjE)
     apply (subgoal_tac "is_fault (pt_walk (ASID r) (MEM s) (TTBR0 r) x)")
      apply blast
     apply (clarsimp simp: pt_walk_new_fault_pt_walk_fault)
    apply (erule disjE)
     apply (subgoal_tac "the (pt_walk (ASID r) (MEM q) (TTBR0 r) xc) = the (pt_walk (ASID r) (MEM s) (TTBR0 r) x)")
      apply (case_tac "\<not> is_fault (pt_walk (ASID r) (MEM s) (TTBR0 r) x)")
  using saturatd_lookup_hit_no_fault apply fastforce
      apply blast
     apply (subgoal_tac "the (pt_walk (ASID r) (MEM q) (TTBR0 r) xc) = the (pt_walk (ASID r) (MEM q) (TTBR0 r) x)")
      apply (drule pt_walk_new_equal_pt_walk, simp add: is_fault_def)
     apply (frule  asid_tlb_lookup_range_fault_pt_walk)
     apply (drule_tac x = x in bspec; clarsimp simp: lookup_asid_tlb_hit_entry_range)
    apply (subgoal_tac "is_fault (pt_walk (ASID r) (MEM s) (TTBR0 r) x)") 
     apply blast
    apply clarsimp 
    apply (simp add: pt_walk_new_par_fault_pt_walk_fault) 
  using  asid_tlb_lookup_range_pt_walk_not_incon apply blast
  apply (drule union_asid_pdc_incon_cases)
  apply (erule disjE, clarsimp simp: lookup_pdc_walk_not_incon)
  apply (erule disjE)
   apply clarsimp
   apply (simp add: entry_leq_def)
   apply (erule disjE)
    apply (subgoal_tac "is_fault (pdc_walk (ASID r) (MEM s) (TTBR0 r) x)")
     apply blast
    apply (clarsimp simp: pt_walk_new_fault_pde_walk_fault)
   apply (erule disjE)
    apply (subgoal_tac "the (pdc_walk (ASID r) (MEM q) (TTBR0 r) xc) = the (pdc_walk (ASID r) (MEM s) (TTBR0 r) x)")
     prefer 2
     apply (subgoal_tac "the (pdc_walk (ASID r) (MEM q) (TTBR0 r) xc) = the (pdc_walk (ASID r) (MEM q) (TTBR0 r) x)")
      apply clarsimp
      apply (drule pt_walk_new_equal_pdc_walk, simp add: is_fault_def)
     apply (frule lookup_pdc_range_fault_pt_walk)
     apply (drule_tac x = x in bspec; clarsimp simp: lookup_asid_pdc_hit_entry_range)
     apply (case_tac "\<not> is_fault (pdc_walk (ASID r) (MEM s) (TTBR0 r) x)")
      apply clarsimp
  using saturatd_lookup_pdc_hit_no_fault apply fastforce
  apply blast
  apply (subgoal_tac "the(pdc_walk (ASID r) (MEM q) (TTBR0 r) xc) = the(pdc_walk (ASID r) (MEM s) (TTBR0 r) x)" )
  apply (case_tac "is_fault (pdc_walk (ASID r) (MEM s) (TTBR0 r) x)")
  apply blast
  using saturatd_lookup_pdc_hit_no_fault apply fastforce
  apply (subgoal_tac " the (pdc_walk (ASID r) (MEM q) (TTBR0 r) xc) =  the(pdc_walk (ASID r) (MEM q) (TTBR0 r) x)")
    apply clarsimp
    apply (simp add: pt_walk_partial_full_pdc_walk_eq)
   apply (meson lookup_asid_pdc_hit_entry_range lookup_pdc_range_fault_pt_walk 
               lookup_pdc_range_pt_walk_hit)
  using lookup_pdc_walk_not_incon by blast



lemma  mmu_write_asid_ptcomp_rel:
  "\<lbrakk>saturated (typ_sat_tlb s) ; ASID t = ASID s; MEM t = MEM r; TTBR0 t = TTBR0 s ;
       inconsistent_vaddrs (typ_sat_tlb s) \<subseteq> iset (set_tlb q) ;  incoherrent_vaddrs (typ_sat_tlb s) \<subseteq> iset(set_tlb q)\<rbrakk> \<Longrightarrow>
      incoherrent_vaddrs  (typ_sat_tlb (t\<lparr>sat_tlb := pairunion (sat_tlb s) (the ` {e \<in> range (pt_walk (ASID t) (MEM r) (TTBR0 t)). \<not> is_fault e}, 
          the ` {e \<in> range (pdc_walk (ASID t) (MEM r) (TTBR0 t)). \<not> is_fault e})\<rparr>)) \<subseteq> iset (set_tlb q) \<union> incon_comp (ASID t) (ASID t) (MEM s) (MEM r) (TTBR0 t) (TTBR0 t)"
  apply rule
  apply (clarsimp simp: incoherrent_vaddrs_def  inconsistent_vaddrs_def )
  apply (erule disjE; clarsimp)
   apply (drule lookup_asid_tlb_hit_union_cases')
   apply (erule disjE)
    apply (clarsimp simp: incon_comp_def ptable_comp_def entry_leq_def Let_def)
    apply (subgoal_tac "is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) x)")
     apply blast
    apply (metis (mono_tags, hide_lams) pt_walk_new_equal_pt_walk pt_walk_new_fault_pt_walk_fault pt_walk_new_par_fault_pt_walk_fault)
   apply  (clarsimp simp: asid_tlb_lookup_miss_is_fault_intro)
  apply (drule lookup_asid_pdc_hit_union_cases')
  apply (erule disjE)
   apply (clarsimp simp: incon_comp_def ptable_comp_def entry_leq_def Let_def)
   apply (subgoal_tac "is_fault (pdc_walk (ASID s) (MEM s) (TTBR0 s) x)")
    apply blast
   apply (metis (mono_tags, hide_lams) pt_walk_new_equal_pdc_walk pt_walk_new_fault_pde_walk_fault pt_walk_partial_full_pdc_walk_eq)
  by  (clarsimp simp: lookup_pdc_miss_is_fault_intro)



   

lemma mmu_write_sat_incon_refine:        
  "\<lbrakk> mmu_write_size (val,va, sz) s = ((), s');  mmu_write_size (val,va, sz) t = ((), t'); va \<notin> iset (set_tlb t);
            tlb_rel_abs (typ_sat_tlb s) (typ_set_tlb t)  \<rbrakk> \<Longrightarrow> 
                                  tlb_rel_abs (typ_sat_tlb s') (typ_set_tlb t')"  
  apply (frule_tac s = s in tlb_rel_abs_consistent; clarsimp )
  apply (frule tlb_rel_absD, clarsimp)
  apply (clarsimp simp: mmu_write_size_sat_tlb_state_ext_def  mmu_write_size_set_tlb_state_ext_def)
  apply (cases "mmu_translate va s", cases "mmu_translate va t", clarsimp)
  apply (frule_tac t=t and pa'= aa and t' = ba in mmu_translate_sat_incon_refine; clarsimp) 
  apply (clarsimp simp: tlb_rel_abs_def)
  apply (subgoal_tac "exception b = exception ba")
   prefer 2 apply (case_tac b , case_tac ba , clarsimp simp: state.defs)
  apply (clarsimp split: if_split_asm)
  apply (case_tac "write'mem1 (val, aa, sz) b " , case_tac "write'mem1 (val, aa, sz) ba" , clarsimp simp: Let_def)
  apply (subgoal_tac "state.truncate bb = state.truncate bc")
   prefer 2 
  using write_mem_state_trun_equal apply blast
  apply (rule conjI , clarsimp simp: state.defs) 
  apply (subgoal_tac "MEM bb = MEM bc  \<and> MEM s = MEM b" , simp)
   apply (subgoal_tac "ASID s = ASID b \<and> TTBR0 s = TTBR0 b" , simp)
    apply (subgoal_tac "saturated (typ_sat_tlb b)")
     prefer 2 apply blast
    prefer 2 using mmu_sat_eq_asid_root_mem apply blast
   prefer 2
   apply (rule conjI)
    apply (clarsimp simp: state.defs)
  using mmu_sat_eq_asid_root_mem
   apply blast
  apply (subgoal_tac "ASID b = ASID bb \<and> TTBR0 b = TTBR0 bb")
   apply (rule conjI)
    apply (clarsimp simp: saturated_def)
   apply (simp only: incon_addrs_def)
   apply simp
   apply (rule conjI)
    apply (drule_tac s = b and t = ba and q = bc and r = bb in mmu_write_incon_set_rel; clarsimp)
   apply (rule conjI)
    apply (frule_tac t = bb and r = bc and q = ba and s = b in  mmu_write_asid_ptcomp_rel ; clarsimp simp: )
   prefer 2
   apply (clarsimp simp: write'mem1_def raise'exception_def split: if_split_asm)
  apply (rule conjI)
   apply (clarsimp simp: global_range_def)
   apply (rule conjI)
    apply (simp only: global_entries_union) 
    apply clarsimp
    apply fastforce
   apply (simp only: global_entries_union_pdc) 
   apply clarsimp
   apply (rule conjI)
    apply force 
  using global_entr_pdc_subset_global_entries apply fastforce
  apply clarsimp
  apply (rule conjI)
   apply (clarsimp simp: non_global_to_global [symmetric])
   apply (subgoal_tac "lookup'' (non_global_entries (fst (sat_tlb b) \<union> the ` {e \<in> range (pt_walk (ASID t) (MEM bc) (TTBR0 bb)). \<not> is_fault e})) a v =
                       lookup'' (non_global_entries (fst (sat_tlb b))) a v")
    apply force
   apply (rule lookup_non_global_union_asid_unequal, simp)
  apply (clarsimp simp: non_global_to_global_pdc [symmetric])
  apply (subgoal_tac "lookup_pdc (non_global_entries_pdc (snd (sat_tlb b) \<union> the ` {e \<in> range (pdc_walk (ASID t) (MEM bc) (TTBR0 bb)). \<not> is_fault e})) a v =
                         lookup_pdc (non_global_entries_pdc (snd (sat_tlb b))) a v")
   apply force
  by (rule lookup_non_global_union_asid_unequal_pdc, simp)



   


(* refinement for read theroems *)


lemma  mem_read1_consistent_tlb_rel_non_det:
  " \<lbrakk>mem_read1 (a, sz) s = (val, s');   mem_read1 (a, sz) t = (val', t'); 
               consistent0' (MEM t) (ASID t) (TTBR0 t) (fst (sat_tlb t)) (snd (sat_tlb t)) va; tlb_rel_sat (typ_non_det_tlb s) (typ_sat_tlb t)\<rbrakk>
              \<Longrightarrow> consistent0' (MEM t') (ASID t') (TTBR0 t') (fst (sat_tlb t')) (snd (sat_tlb t')) va \<and> tlb_rel_sat (typ_non_det_tlb s') (typ_sat_tlb t')"
   apply (rule conjI)
   apply (subgoal_tac "MEM t = MEM t' \<and> ASID t = ASID t' \<and> TTBR0 t = TTBR0 t' \<and> sat_tlb t = sat_tlb t'")
    apply (clarsimp simp: consistent0_def)
   prefer 2
   apply (subgoal_tac " exception s' =  exception t'")
    apply (drule mem1_read_exception)
    apply (drule mem1_read_exception)
    apply (clarsimp simp: tlb_rel_sat_def)
    apply (clarsimp simp: saturated_def  state.truncate_def)
    apply (cases s', cases t')
    apply clarsimp
   apply (subgoal_tac "MEM s = MEM t \<and> exception s = exception t")
    apply (thin_tac "consistent0' (MEM t) (ASID t) (TTBR0 t) (fst (sat_tlb t)) (snd (sat_tlb t)) va")    
    apply (thin_tac "tlb_rel_sat (typ_non_det_tlb s) (typ_sat_tlb t)")
    apply (clarsimp simp: mem_read1_def)
    apply (clarsimp split: if_split_asm)
        apply (clarsimp simp: mem1_def raise'exception_def split: option.splits if_split_asm)
       apply (clarsimp simp: mem1_def raise'exception_def split: option.splits if_split_asm)
      apply (clarsimp simp: mem1_def raise'exception_def split: option.splits if_split_asm)
     subgoal
     by (clarsimp simp: mem1_def raise'exception_def split: option.splits if_split_asm)
    apply (clarsimp simp: raise'exception_def split: option.splits if_split_asm)
   apply (clarsimp simp: tlb_rel_sat_def state.defs)
  apply (drule mem1_read_exception)
  apply (drule mem1_read_exception)
  apply (cases t, cases t' , clarsimp)
   done



lemma mmu_read_non_det_sat_rel_cons:
  "\<lbrakk> mmu_read_size (va, sz) s = (val, s'); tlb_rel_sat (typ_non_det_tlb s) (typ_sat_tlb t);
         consistent (typ_sat_tlb t) va; mmu_read_size (va, sz) t = (val', t') \<rbrakk> \<Longrightarrow>  
                     consistent (typ_sat_tlb t') va \<and>  tlb_rel_sat (typ_non_det_tlb s') (typ_sat_tlb t') "
  apply (clarsimp simp: mmu_read_size_sat_tlb_state_ext_def   mmu_read_size_non_det_tlb_state_ext_def Let_def)
  apply (cases "mmu_translate va s", cases "mmu_translate va t", clarsimp)
  apply (drule_tac t = t in mmu_translate_non_det_sat_refine ; clarsimp simp: Let_def mem_read1_consistent_tlb_rel_non_det)
  done

lemma same_mem_read_equal:
  "\<lbrakk>MEM s = MEM t; mem_read1 (pa, sz) s = (val, s'); mem_read1 (pa, sz) t = (val', t')  \<rbrakk> \<Longrightarrow> val = val'"
  apply (clarsimp simp: mem_read1_def)
  apply (clarsimp split: if_split_asm)
      apply (clarsimp simp: mem1_def raise'exception_def split: option.splits if_split_asm)
     apply (clarsimp simp: mem1_def raise'exception_def split: option.splits if_split_asm)
    apply (clarsimp simp: mem1_def raise'exception_def split: option.splits if_split_asm)
  subgoal
    by (clarsimp simp: mem1_def raise'exception_def split: option.splits if_split_asm)
  apply (clarsimp simp: raise'exception_def split: option.splits if_split_asm)
    done


lemma mmu_read_non_det_sat_refine:
  "\<lbrakk>mmu_read_size (va, sz) s = (val, s');  mmu_read_size (va, sz) t = (val', t'); 
              tlb_rel_sat (typ_non_det_tlb s) (typ_sat_tlb t); consistent (typ_sat_tlb t) va\<rbrakk> \<Longrightarrow>  
                     val = val' \<and> tlb_rel_sat (typ_non_det_tlb s') (typ_sat_tlb t') \<and> consistent (typ_sat_tlb t') va  "
  apply (rule conjI)
   apply (clarsimp simp: mmu_read_size_sat_tlb_state_ext_def   mmu_read_size_non_det_tlb_state_ext_def Let_def)
   apply (cases "mmu_translate va s", cases "mmu_translate va t", clarsimp)
   apply (rename_tac pa s'' pa' t'')
   apply (subgoal_tac "pa = pa'", clarsimp)
    apply (subgoal_tac "MEM s'' = MEM t''")
     apply (clarsimp simp: same_mem_read_equal)
  using mmu_translate_non_det_sat_mem_excp apply force
  using mmu_translate_non_det_sat_pa apply force
  apply (frule_tac t = t and t' =t' in  mmu_read_non_det_sat_rel_cons; simp)
  done


lemma mmu_read_sat_const_inter [simp]:
  "saturated (typ_sat_tlb s) \<Longrightarrow> fst(sat_tlb (snd (mmu_read_size v s))) = fst(sat_tlb s) \<and>
       snd(sat_tlb (snd (mmu_read_size v s))) = snd(sat_tlb s)"
   by (clarsimp simp: mmu_read_size_sat_tlb_state_ext_def split_def Let_def
                      mem_read1_def raise'exception_def  split: if_split_asm)


lemma  mem_read1_consistent_tlb_rel_incon:
  "\<lbrakk>mem_read1 (a, sz) s = (val, s'); mem_read1 (a, sz) t = (val', t'); 
             va \<notin> iset (set_tlb t); tlb_rel_abs (typ_sat_tlb s) (typ_set_tlb t)\<rbrakk>
              \<Longrightarrow>  va \<notin> iset (set_tlb t') \<and>  tlb_rel_abs (typ_sat_tlb s') (typ_set_tlb t')"
  apply (rule conjI)
   apply (subgoal_tac "ASID t = ASID t' \<and> iset (set_tlb t) = iset (set_tlb t')")
    apply clarsimp
   apply (drule mem1_read_exception)
   apply (drule mem1_read_exception)
   apply (cases t, cases t')
   apply clarsimp
  apply (subgoal_tac "exception s' =  exception t'")
   apply (drule mem1_read_exception)
   apply (drule mem1_read_exception)
   apply (clarsimp simp: tlb_rel_abs_def)
   apply (rule conjI)
    apply (clarsimp simp: state.defs)
    apply (cases s', cases t')
    apply clarsimp
   apply (rule conjI)
    apply (clarsimp simp:  saturated_def)
   apply (rule conjI)
    apply (clarsimp simp: incon_addrs_def inconsistent_vaddrs_def incoherrent_vaddrs_def)
    apply (cases s', cases t')
    apply clarsimp
   apply (rule conjI)
    apply (clarsimp simp: global_range_def)
    apply (cases s', cases t')
    apply clarsimp   
   apply (cases s', cases t')
   apply clarsimp
  apply (subgoal_tac "MEM s = MEM t \<and> exception s = exception t")
   apply (thin_tac " va \<notin> iset (set_tlb t)")    
   apply (thin_tac " tlb_rel_abs (typ_sat_tlb s) (typ_set_tlb t)")
   apply (clarsimp simp: mem_read1_def)
   apply (clarsimp split: if_split_asm)
       apply (clarsimp simp: mem1_def raise'exception_def split: option.splits if_split_asm)
      apply (clarsimp simp: mem1_def raise'exception_def split: option.splits if_split_asm)
     apply (clarsimp simp: mem1_def raise'exception_def split: option.splits if_split_asm)
    subgoal
    by (clarsimp simp: mem1_def raise'exception_def split: option.splits if_split_asm)
   apply (clarsimp simp: raise'exception_def split: option.splits if_split_asm)
  apply (clarsimp simp: tlb_rel_abs_def state.defs)
  done

find_consts "'a option set \<Rightarrow> 'a option"

lemma mmu_read_sat_incon_rel_con:
  "\<lbrakk> mmu_read_size (va, sz) s = (val, s'); tlb_rel_abs (typ_sat_tlb s) (typ_set_tlb t);
         va \<notin> iset (set_tlb t); mmu_read_size (va, sz) t = (val', t') \<rbrakk> \<Longrightarrow>  
                     va \<notin> iset (set_tlb t') \<and>  tlb_rel_abs (typ_sat_tlb s') (typ_set_tlb t') "
  apply (clarsimp simp: mmu_read_size_sat_tlb_state_ext_def  mmu_read_size_set_tlb_state_ext_def Let_def)
  apply (cases "mmu_translate va s", cases "mmu_translate va t", clarsimp)
  apply (drule_tac t = t and pa' = aa  and t' = ba in mmu_translate_sat_incon_refine ; clarsimp simp: Let_def mem_read1_consistent_tlb_rel_incon)
  done


lemma mmu_read_sat_incon_refine:
  "\<lbrakk> mmu_read_size (va, sz) s = (val, s'); mmu_read_size (va, sz) t = (val', t');
        tlb_rel_abs (typ_sat_tlb s) (typ_set_tlb t); va \<notin> iset (set_tlb t)  \<rbrakk> \<Longrightarrow>  
                    val = val' \<and> tlb_rel_abs (typ_sat_tlb s') (typ_set_tlb t') \<and> va \<notin> iset (set_tlb t')"
  apply (rule conjI)
   apply (clarsimp simp: mmu_read_size_sat_tlb_state_ext_def  mmu_read_size_set_tlb_state_ext_def Let_def)
   apply (cases "mmu_translate va s", cases "mmu_translate va t", clarsimp)
   apply (rename_tac pa s'' pa' t'')
   apply (subgoal_tac "pa = pa'", clarsimp)
    apply (subgoal_tac "MEM s'' = MEM t''")
     apply (clarsimp simp: same_mem_read_equal)
    using mmu_translate_sat_incon_mem_excp apply force
   using mmu_translate_sat_incon_refine apply force
   by (frule_tac t = t and t' =t' in  mmu_read_sat_incon_rel_con; simp)


end