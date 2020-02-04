theory  ARMv7A_Update_TTBR0_Ref

imports 
  ARMv7A_Mem_Write_Read_Ref

begin               



lemma  update_root_non_det_sat_refine:
  "\<lbrakk> update_TTBR0 r (s::'a non_det_tlb_state_scheme) = ((), s') ;  update_TTBR0 r (t::'b sat_tlb_state_scheme) = ((), t'); 
         tlb_rel_sat (typ_non_det_tlb s) (typ_sat_tlb t) \<rbrakk> \<Longrightarrow> 
                  tlb_rel_sat (typ_non_det_tlb s') (typ_sat_tlb t')"
  apply (clarsimp simp: update_TTBR0_non_det_tlb_state_ext_def update_TTBR0_sat_tlb_state_ext_def)
  apply (clarsimp simp: tlb_rel_sat_def  saturated_def)
  apply (cases s, cases t , clarsimp simp: state.defs pairsub_def)
  by blast



lemma update_root_sat_incon_refine:
  "\<lbrakk> update_TTBR0 r (s::'a sat_tlb_state_scheme) = ((), s') ;  update_TTBR0 r (t::'b set_tlb_state_scheme) = ((), t'); 
             tlb_rel_abs (typ_sat_tlb s) (typ_set_tlb t) \<rbrakk> \<Longrightarrow> 
                     tlb_rel_abs (typ_sat_tlb s') (typ_set_tlb t')"
  apply (clarsimp simp: update_TTBR0_sat_tlb_state_ext_def update_TTBR0_set_tlb_state_ext_def tlb_rel_abs_def)
  apply (subgoal_tac "ASID t = ASID s \<and> TTBR0 t = TTBR0 s \<and> MEM t = MEM s")
   prefer 2
   apply (clarsimp simp:  typ_sat_tlb_def state.defs)


  apply (rule conjI)
   apply (cases s, cases t)
  apply (clarsimp simp: typ_sat_tlb_def typ_set_tlb_def state.defs)  


  apply (rule conjI)
   apply (cases s, cases t)
   apply (clarsimp simp: typ_sat_tlb_def typ_set_tlb_def state.defs) 
   apply (clarsimp simp: saturated_def)
  apply (rule conjI)
   apply (clarsimp simp: incon_addrs_def)
   apply (rule conjI)
    apply (clarsimp simp: inconsistent_vaddrs_def incoherrent_vaddrs_def)
    apply (rule conjI; clarsimp)
     apply (drule union_asid_tlb_incon_cases)
     apply (erule disjE, clarsimp simp: asid_tlb_lookup_range_pt_walk_not_incon)
     apply (erule disjE, clarsimp)
      apply (clarsimp simp: incon_comp_def ptable_comp_def Let_def)
      apply (simp only: entry_leq_def)
      apply (erule disjE)
       apply (metis (mono_tags, lifting) mem_Collect_eq pt_walk_new_fault_pt_walk_fault subset_eq)
      apply (erule disjE)
       apply (subgoal_tac "the (pt_walk (ASID s) (MEM s) r xb) = the (pt_walk (ASID s) (MEM s) (TTBR0 s) x)")
        apply (case_tac "\<not>is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) x)")
         apply clarsimp
         using saturatd_lookup_hit_no_fault apply fastforce
        apply blast
       apply (subgoal_tac "the (pt_walk (ASID s) (MEM s) r xb) = the (pt_walk (ASID s) (MEM s) r x)")
        apply clarsimp
        apply (drule pt_walk_new_equal_pt_walk, simp add: is_fault_def)
       apply (frule asid_tlb_lookup_range_fault_pt_walk)
       apply (drule_tac x = x in bspec; clarsimp simp: lookup_asid_tlb_hit_entry_range)
      apply (subgoal_tac "is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) x)") 
       apply blast
      apply (clarsimp simp: pt_walk_new_par_fault_pt_walk_fault)
  using asid_tlb_lookup_range_pt_walk_not_incon apply blast
    apply (drule union_asid_pdc_incon_cases)
    apply (erule disjE)
     apply (clarsimp simp: lookup_pdc_walk_not_incon)
    apply (erule disjE)
     apply (clarsimp simp: incon_comp_def ptable_comp_def Let_def)
     apply (simp only: entry_leq_def)
     apply (erule disjE)
      apply (subgoal_tac "is_fault (pdc_walk (ASID s) (MEM s) (TTBR0 s) x)")
       apply blast
      apply (clarsimp simp: pt_walk_new_fault_pde_walk_fault)
     apply (erule disjE)
      apply (subgoal_tac "the (pdc_walk (ASID s) (MEM s) r xb) = the (pdc_walk (ASID s) (MEM s) (TTBR0 s) x)")
       prefer 2
       apply (subgoal_tac "the (pdc_walk (ASID s) (MEM s) r xb) = the (pdc_walk (ASID s) (MEM s) r x)")
        apply clarsimp
        apply (drule pt_walk_new_equal_pdc_walk, simp add: is_fault_def)
       apply (frule lookup_pdc_range_fault_pt_walk)
       apply (drule_tac x = x in bspec; clarsimp simp: lookup_asid_pdc_hit_entry_range)
      apply (case_tac "\<not> is_fault (pdc_walk (ASID s) (MEM s) (TTBR0 s) x)")
  using saturatd_lookup_pdc_hit_no_fault apply fastforce
      apply blast
     apply (subgoal_tac "the(pdc_walk (ASID s) (MEM s) r xb) = the(pdc_walk (ASID s) (MEM s) (TTBR0 s) x)" )
      apply clarsimp 
      apply (case_tac "is_fault (pdc_walk (ASID s) (MEM s) (TTBR0 s) x)")
       apply blast
  using saturatd_lookup_pdc_hit_no_fault apply fastforce
     apply (subgoal_tac " the (pdc_walk (ASID s) (MEM s) r xb) =  the(pdc_walk (ASID s) (MEM s) r x)")
      apply clarsimp
      apply (simp add: pt_walk_partial_full_pdc_walk_eq)
     apply (frule lookup_pdc_range_fault_pt_walk)
     apply (drule_tac x = x in bspec; clarsimp simp: lookup_asid_pdc_hit_entry_range)
  using lookup_pdc_walk_not_incon apply blast
   apply clarsimp
   apply (clarsimp simp: incoherrent_vaddrs_def  inconsistent_vaddrs_def)
   apply (erule disjE; clarsimp)
    apply (simp only: incon_comp_def ptable_comp_def entry_leq_def)
    apply clarsimp
    apply (erule disjE)
     apply (drule lookup_asid_tlb_hit_union_cases')
     apply (clarsimp simp: asid_tlb_lookup_miss_is_fault_intro pt_walk_new_fault_pt_walk_fault subset_eq)
    apply (erule disjE)
     apply (drule lookup_asid_tlb_hit_union_cases')
     apply (erule disjE)
      apply clarsimp
      apply (case_tac "is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) x)")
       apply blast
      apply (metis (no_types, hide_lams) pt_walk_new_equal_pt_walk)
     apply (erule disjE; clarsimp simp: asid_tlb_lookup_miss_is_fault_intro)
    apply clarsimp 
    apply (simp add: is_fault_def pt_walk_new_no_fault_pt_walk')
   apply (simp only: incon_comp_def ptable_comp_def entry_leq_def)
   apply clarsimp
   apply (erule disjE)
    apply (drule lookup_asid_pdc_hit_union_cases') 
    apply (clarsimp simp: lookup_pdc_miss_is_fault_intro pt_walk_new_fault_pde_walk_fault subset_eq)
   apply (erule disjE)
    apply (drule lookup_asid_pdc_hit_union_cases')
    apply (erule disjE)
     apply clarsimp
     apply (case_tac "is_fault (pdc_walk (ASID s) (MEM s) (TTBR0 s) x)")
      apply blast
     apply (metis pt_walk_new_equal_pdc_walk)
    apply (erule disjE; clarsimp simp: lookup_pdc_miss_is_fault_intro)
   apply clarsimp 
   apply (simp add: is_fault_def pt_walk_new_no_fault_pdc_walk)  
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
  apply (clarsimp)
  apply (rule conjI)
   apply (clarsimp simp: non_global_to_global [symmetric])
   apply (subgoal_tac "lookup'' (non_global_entries (fst (sat_tlb s) \<union> the ` {e \<in> range (pt_walk (ASID s) (MEM s) r). \<not> is_fault e})) a v =
                      lookup'' (non_global_entries (fst (sat_tlb s))) a v")
    apply force
   apply (rule lookup_non_global_union_asid_unequal, simp)
  apply (clarsimp simp: non_global_to_global_pdc [symmetric])
  apply (subgoal_tac "lookup_pdc (non_global_entries_pdc (snd (sat_tlb s) \<union> the ` {e \<in> range (pdc_walk (ASID s) (MEM s) r). \<not> is_fault e})) a v =
                         lookup_pdc (non_global_entries_pdc (snd (sat_tlb s))) a v")
   apply force
  by (rule lookup_non_global_union_asid_unequal_pdc, simp)



end