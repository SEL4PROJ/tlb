theory  ARMv7A_Flush_Ref

imports 
  ARMv7A_Update_ASID_Ref

begin               


lemma  flush_tlb_det_sat_refine:
  "\<lbrakk> flush FlushTLB (s::'a non_det_tlb_state_scheme) = ((), s') ;  flush FlushTLB (t::'b sat_tlb_state_scheme) = ((), t'); 
         tlb_rel_sat (typ_non_det_tlb s) (typ_sat_tlb t) \<rbrakk> \<Longrightarrow> 
                  tlb_rel_sat (typ_non_det_tlb s') (typ_sat_tlb t')"
  apply (clarsimp simp: flush_non_det_tlb_state_ext_def flush_sat_tlb_state_ext_def)
  apply (clarsimp simp: tlb_rel_sat_def saturated_def)
  apply (cases s, cases t , clarsimp simp: state.defs)
  done

lemma  flush_varange_det_sat_refine:
  "\<lbrakk> flush (Flushvarange vset) (s::'a non_det_tlb_state_scheme) = ((), s') ;  flush (Flushvarange vset) (t::'b sat_tlb_state_scheme) = ((), t'); 
         tlb_rel_sat (typ_non_det_tlb s) (typ_sat_tlb t) \<rbrakk> \<Longrightarrow> 
                  tlb_rel_sat (typ_non_det_tlb s') (typ_sat_tlb t')"
  apply (clarsimp simp: flush_non_det_tlb_state_ext_def flush_sat_tlb_state_ext_def flush_tlb_pdc_vset_def)
  apply (clarsimp simp: tlb_rel_sat_def  saturated_def)
  apply (cases s, cases t , clarsimp simp: state.defs )
  by blast



lemma  flush_with_asid_asid_non_det_det_refine:
  "\<lbrakk> flush (FlushASID a) (s::'a non_det_tlb_state_scheme) = ((), s') ;  flush (FlushASID a) (t::'b sat_tlb_state_scheme) = ((), t'); 
         tlb_rel_sat (typ_non_det_tlb s) (typ_sat_tlb t) \<rbrakk> \<Longrightarrow> 
                  tlb_rel_sat (typ_non_det_tlb s') (typ_sat_tlb t')"
  apply (clarsimp simp: flush_non_det_tlb_state_ext_def flush_sat_tlb_state_ext_def flush_tlb_pdc_asid_def)
  apply (clarsimp simp: tlb_rel_sat_def)
  apply (cases s, cases t , clarsimp simp: state.defs saturated_def)
  by blast

lemma  flush_with_asid_asid_varange_non_det_det_refine:
  "\<lbrakk>flush (FlushASIDvarange a vset) (s::'a non_det_tlb_state_scheme) = ((), s') ;  flush (FlushASIDvarange a vset) (t::'b sat_tlb_state_scheme) = ((), t'); 
         tlb_rel_sat (typ_non_det_tlb s) (typ_sat_tlb t) \<rbrakk> \<Longrightarrow> 
                  tlb_rel_sat (typ_non_det_tlb s') (typ_sat_tlb t')"
  apply (clarsimp simp: flush_non_det_tlb_state_ext_def flush_sat_tlb_state_ext_def  flush_tlb_pdc_a_vset_def)
  apply (clarsimp simp: tlb_rel_sat_def)
  apply (cases s, cases t , clarsimp simp: state.defs saturated_def) 
  by blast


lemma  flush_det_sat_refine:
  "\<lbrakk> flush f (s::'a non_det_tlb_state_scheme) = ((), s') ;  flush f (t::'b sat_tlb_state_scheme) = ((), t'); 
         tlb_rel_sat (typ_non_det_tlb s) (typ_sat_tlb t) \<rbrakk> \<Longrightarrow> 
                  tlb_rel_sat (typ_non_det_tlb s') (typ_sat_tlb t')"
  by (cases f; clarsimp simp: flush_tlb_det_sat_refine   flush_varange_det_sat_refine flush_with_asid_asid_non_det_det_refine flush_with_asid_asid_varange_non_det_det_refine) 


lemma  flush_tlb_sat_incon_refine:
  "\<lbrakk> flush FlushTLB (s::'a sat_tlb_state_scheme) = ((), s') ;  flush FlushTLB (t::'b set_tlb_state_scheme) = ((), t'); 
         tlb_rel_abs (typ_sat_tlb s) (typ_set_tlb t) \<rbrakk> \<Longrightarrow> 
                  tlb_rel_abs (typ_sat_tlb s') (typ_set_tlb t')"
  apply (clarsimp simp: flush_sat_tlb_state_ext_def flush_set_tlb_state_ext_def)
  apply (clarsimp simp: tlb_rel_abs_def)
  apply (rule conjI)
   apply (cases s, cases t , clarsimp simp: state.defs)
  apply (rule conjI)
   apply (clarsimp simp: saturated_def)
  apply (rule conjI)
   apply (clarsimp simp: incon_addrs_def)
   apply (rule conjI)
    apply (clarsimp simp: inconsistent_vaddrs_def)
    apply (rule conjI)
  using asid_tlb_lookup_range_pt_walk_not_incon apply force
  using lookup_pdc_walk_not_incon apply force
   apply (clarsimp simp: incoherrent_vaddrs_def)
   apply (rule conjI)
  using asid_tlb_lookup_miss_is_fault_intro apply force
  using lookup_pdc_miss_is_fault_intro apply force
  apply (rule conjI) apply (clarsimp simp: global_range_def) 
   apply (rule conjI)
    apply (cases s, cases t , clarsimp simp:  state.defs)
   apply (subgoal_tac "MEM t = MEM s \<and> TTBR0 t = TTBR0 s \<and> ASID t = ASID s ") 
    apply (simp only:)
    apply(rule global_entr_pdc_subset_global_entries)
   apply (cases s, cases t , clarsimp simp:  state.defs)
  apply (clarsimp simp: non_global_to_global [symmetric]) 
  apply (rule conjI) 
   apply (subgoal_tac "lookup'' (non_global_entries (the ` {e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e})) a v = Miss")
    apply force
   apply (rule asid_unequal_lookup_pt_walk_miss, simp)
  apply (clarsimp simp: non_global_to_global_pdc [symmetric]) 
  apply (subgoal_tac "lookup_pdc (non_global_entries_pdc (the ` {e \<in> range (pdc_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e})) a v = Miss")
   apply force
  by (rule asid_unequal_lookup_pdc_walk_miss, simp)





lemma  flush_varange_sat_incon_refine:
  "\<lbrakk> flush (Flushvarange vset) (s::'a sat_tlb_state_scheme) = ((), s') ;  flush (Flushvarange vset) (t::'b set_tlb_state_scheme) = ((), t'); 
         tlb_rel_abs (typ_sat_tlb s) (typ_set_tlb t) \<rbrakk> \<Longrightarrow> 
                  tlb_rel_abs (typ_sat_tlb s') (typ_set_tlb t')"
  apply (clarsimp simp: flush_sat_tlb_state_ext_def flush_set_tlb_state_ext_def flush_tlb_pdc_vset_def  Let_def)
  apply (clarsimp simp: tlb_rel_abs_def)
  apply (rule conjI)
   apply (cases s, cases t , clarsimp simp: state.defs)
  apply (rule conjI)
   apply (clarsimp simp: saturated_def)
  apply (rule conjI)
   apply (clarsimp simp: incon_addrs_def)
   apply (rule conjI)
    apply (clarsimp simp: inconsistent_vaddrs_def)
    apply (rule conjI)
     apply clarsimp
     apply (rename_tac v)
     apply (rule conjI)
      apply (subgoal_tac "lookup'' (fst(sat_tlb s)  \<union> the ` {e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e}) (ASID s) v = Incon")
       apply (subgoal_tac "lookup'' (fst(sat_tlb s)) (ASID s) v = Incon")
        apply blast
       apply (subgoal_tac "fst(sat_tlb s) \<union> the ` {e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e} = fst(sat_tlb s)")
        apply force
       apply (force simp: saturated_def)
      apply (drule lookup_minus_union_incon, simp)
     apply (drule union_asid_tlb_incon_cases)
     apply (erule disjE, clarsimp simp: asid_tlb_lookup_range_pt_walk_not_incon)
     apply (erule disjE, clarsimp simp:)
  using lookup_asid_tlb_hit_entry_range apply force
     apply (erule disjE, clarsimp simp: asid_tlb_lookup_range_pt_walk_not_incon)
     apply (erule disjE, clarsimp simp: ) 
      apply (drule_tac t = "fst(sat_tlb s)" and a = "ASID s" in  addr_set_minus_lookup_miss, force)
     apply (erule disjE, clarsimp simp: asid_tlb_lookup_range_pt_walk_not_incon)
     apply clarsimp
     apply (drule_tac t = "fst(sat_tlb s)" and a = "ASID s" in  addr_set_minus_lookup_miss, force)
    apply (clarsimp simp: incoherrent_vaddrs_def)
    apply (rename_tac v)
    apply (rule conjI)
     apply (subgoal_tac "lookup_pdc (snd(sat_tlb s)  \<union> the ` {e \<in> range (pdc_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e}) (ASID s) v = Incon")
      apply (subgoal_tac "lookup_pdc (snd(sat_tlb s)) (ASID s) v = Incon")
       apply blast
      apply (subgoal_tac "snd(sat_tlb s) \<union> the ` {e \<in> range (pdc_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e} = snd(sat_tlb s)")
       apply force
      apply (force simp: saturated_def)
     apply (drule lookup_minus_union_incon_pdc, simp)
    apply (drule union_asid_pdc_incon_cases)
    apply (erule disjE, clarsimp simp: lookup_pdc_walk_not_incon)
    apply (erule disjE, clarsimp simp:)
  using lookup_asid_pdc_hit_entry_range apply force
    apply (erule disjE, clarsimp simp: lookup_pdc_walk_not_incon)
    apply (erule disjE, clarsimp simp: ) 
     apply (drule_tac t = "snd(sat_tlb s)" and a = "ASID s" in  addr_set_minus_lookup_miss_pdc, force)
    apply (erule disjE, clarsimp simp: lookup_pdc_walk_not_incon)
    apply clarsimp
    apply (drule_tac t = "snd(sat_tlb s)" and a = "ASID s" in  addr_set_minus_lookup_miss_pdc, force)
   apply (clarsimp simp: incoherrent_vaddrs_def)
   apply (rule conjI) 
    apply (clarsimp)
    apply (rename_tac v x)
    apply (rule conjI)
     apply (drule lookup_asid_tlb_hit_union_cases')
     apply (erule disjE, clarsimp simp: ) 
      apply (subgoal_tac "lookup'' (fst(sat_tlb s)) (ASID s) v = Hit x \<or> lookup'' (fst(sat_tlb s)) (ASID s) v = Incon")
       apply (erule disjE) 
        apply force
       apply (clarsimp simp: inconsistent_vaddrs_def) 
       apply blast
  using lookup_asid_tlb_hit_incon_minus apply force
     apply (erule disjE, clarsimp simp: ) 
      apply (drule asid_tlb_lookup_miss_is_fault_intro, simp)
     apply clarsimp
     apply (drule asid_tlb_lookup_miss_is_fault_intro, simp)
    apply (drule lookup_asid_tlb_hit_union_cases')
    apply (erule disjE, clarsimp simp: )  
     apply (drule_tac t = "fst(sat_tlb s)" and a = "ASID s" in  addr_set_minus_lookup_miss, force)
    apply (erule disjE, clarsimp simp: )   
     apply (drule asid_tlb_lookup_miss_is_fault_intro, simp)
    apply clarsimp
    apply (drule_tac t = "fst(sat_tlb s)" and a = "ASID s" in  addr_set_minus_lookup_miss, force)
   apply (clarsimp)
   apply (rename_tac v x)
   apply (rule conjI)
    apply (drule lookup_asid_pdc_hit_union_cases')
    apply (erule disjE, clarsimp simp: ) 
     apply (subgoal_tac "lookup_pdc (snd(sat_tlb s)) (ASID s) v = Hit x \<or> lookup_pdc (snd(sat_tlb s)) (ASID s) v = Incon")
      apply (erule disjE) 
       apply force
      apply (clarsimp simp: inconsistent_vaddrs_def) 
      apply blast
  using lookup_asid_pdc_hit_incon_minus apply force
    apply (erule disjE, clarsimp simp: )  
     apply (drule lookup_pdc_miss_is_fault_intro, simp)
    apply clarsimp
    apply (drule lookup_pdc_miss_is_fault_intro, simp)
   apply (drule lookup_asid_pdc_hit_union_cases')
   apply (erule disjE, clarsimp simp: )  
    apply (drule_tac t = "snd(sat_tlb s)" and a = "ASID s" in  addr_set_minus_lookup_miss_pdc, force)
   apply (erule disjE, clarsimp simp: )   
    apply (drule lookup_pdc_miss_is_fault_intro, simp)
   apply clarsimp
   apply (drule_tac t = "snd(sat_tlb s)" and a = "ASID s" in  addr_set_minus_lookup_miss_pdc, force)
  apply (rule conjI)
   apply (clarsimp simp: global_range_def)
   apply (rule conjI)
    apply safe [1]
     apply (subgoal_tac " xa \<in> global_entries (fst(sat_tlb s) - (\<Union>v\<in>vset. {e \<in> fst(sat_tlb s). v \<in> range_of e}))")
      apply (subgoal_tac " xa \<in> global_entries (fst(sat_tlb s))")
       apply blast
      apply (clarsimp simp: global_entries_def) 
     apply (clarsimp simp: global_entries_union)    
     apply (cases s, cases t , clarsimp simp: state.defs)
    apply (subgoal_tac " xa \<in> global_entries (fst(sat_tlb s) - (\<Union>v\<in>vset. {e \<in> fst(sat_tlb s). v \<in> range_of e}))")
     prefer 2
     apply (clarsimp simp: global_entries_union)    
     apply (cases s, cases t , clarsimp simp: state.defs)
    apply (clarsimp simp: entry_set_def global_entries_def)
   apply (safe) [1]
    apply (subgoal_tac "x \<notin> (\<Union>x\<in>global_entries_pdc (the ` {e \<in> range (pdc_walk (ASID s) (MEM t) (TTBR0 t)). \<not> is_fault e}). range_of x)")
     apply (subgoal_tac " xa \<in> global_entries_pdc (snd(sat_tlb s) - (\<Union>v\<in>vset. {e \<in> snd(sat_tlb s). v \<in> range_of e}))")
      apply (subgoal_tac " xa \<in> global_entries_pdc (snd(sat_tlb s))")
       apply blast
      apply (clarsimp simp: global_entries_pdc_def) 
     apply (clarsimp simp: global_entries_union_pdc)    
     apply (cases s, cases t , clarsimp simp: state.defs)
    apply (insert global_entr_pdc_subset_global_entries [of "ASID s" "MEM t" "TTBR0 t"])
    apply (cases s, cases t , clarsimp simp: state.defs) apply force
   apply (subgoal_tac "x \<notin> (\<Union>x\<in>global_entries_pdc (the ` {e \<in> range (pdc_walk (ASID s) (MEM t) (TTBR0 t)). \<not> is_fault e}). range_of x)")
    apply (subgoal_tac " xa \<in> global_entries_pdc (snd(sat_tlb s) - (\<Union>v\<in>vset. {e \<in> snd(sat_tlb s). v \<in> range_of e}))")
     prefer 2
     apply (clarsimp simp: global_entries_union_pdc)    
     apply (cases s, cases t , clarsimp simp: state.defs) 
    apply (clarsimp simp: entry_set_def global_entries_pdc_def)
   apply (insert global_entr_pdc_subset_global_entries [of "ASID s" "MEM t" "TTBR0 t"])
   apply (cases s, cases t , clarsimp simp: state.defs) apply force
  apply (clarsimp)
  apply (rule conjI)
   apply (clarsimp simp: non_global_to_global [symmetric])
   apply (case_tac "lookup''(non_global_entries  (fst(sat_tlb s) - (\<Union>v\<in>vset. {e \<in> fst(sat_tlb s). v \<in> range_of e}) \<union>
                                the ` {e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e})) a v"; clarsimp)
    apply (clarsimp simp: non_global_entries_union)
    apply (subgoal_tac "lookup''( non_global_entries  (the ` {e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e})) a v = Miss")
     apply (subgoal_tac "lookup'' (non_global_entries (fst(sat_tlb s) - (\<Union>v\<in>vset. {e \<in>fst(sat_tlb s). v \<in> range_of e}))) a v =  Incon")
      apply (subgoal_tac "lookup'' (non_global_entries (fst(sat_tlb s))) a v = Incon")
       apply (case_tac "v \<in> vset")
        apply (drule_tac t = "fst(sat_tlb s)" and a = a in addr_set_minus_non_global_lookup_miss, clarsimp)
       apply (drule_tac x = a in spec, simp, drule_tac x = v in spec, simp)
       apply (clarsimp simp: lookup_from'_def snap_conv'_def split: if_split_asm option.splits)
      apply (clarsimp simp: non_global_entries_sub)
      apply (drule lookup_asid_tlb_incon_minus, simp)
     apply (meson lookup_asid_tlb_incon_not_miss)
    apply (rule asid_unequal_lookup_pt_walk_miss, simp)
   apply (clarsimp simp: non_global_entries_union)
   apply (subgoal_tac "lookup'' (non_global_entries (the ` {e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e})) a v =  Miss")
    prefer 2
    apply (rule asid_unequal_lookup_pt_walk_miss, simp)
   apply (subgoal_tac "lookup'' (non_global_entries (fst(sat_tlb s) - (\<Union>v\<in>vset. {e \<in> fst(sat_tlb s). v \<in> range_of e})))  a v = Hit x3")
    prefer 2
    apply(drule lookup_asid_tlb_hit_mis_hit; simp)
   apply (subgoal_tac "lookup'' (non_global_entries (fst(sat_tlb s)))  a v = Hit x3 \<or>
                         lookup'' (non_global_entries (fst(sat_tlb s)))  a v = Incon")
    prefer 2
    apply (clarsimp simp: non_global_entries_sub)
    apply (drule lookup_asid_tlb_hit_incon_minus; simp)
   apply (erule disjE)
    prefer 2
    apply (case_tac "v \<in> vset")
     apply (drule_tac t = "fst(sat_tlb s)" and a = a in addr_set_minus_non_global_lookup_miss, clarsimp)
    apply (drule_tac x = a in spec, simp, drule_tac x = v in spec, simp)
    apply (clarsimp simp: lookup_from'_def snap_conv'_def split: if_split_asm option.splits)
   apply (case_tac "v \<in> vset")
    apply (drule_tac t = "fst(sat_tlb s)" and a = a in addr_set_minus_non_global_lookup_miss, clarsimp)
   apply (drule_tac x = a in spec, simp, drule_tac x = v in spec, simp)
   apply (clarsimp simp: lookup_from'_def snap_conv'_def entry_set_def split: if_split_asm option.splits) 
  apply (clarsimp simp: non_global_to_global_pdc [symmetric])
  apply (case_tac "lookup_pdc (non_global_entries_pdc  (snd(sat_tlb s) - (\<Union>v\<in>vset. {e \<in> snd(sat_tlb s). v \<in> range_of e}) \<union>
                                the ` {e \<in> range (pdc_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e})) a v"; clarsimp)
   apply (clarsimp simp: non_global_entries_union_pdc)
   apply (subgoal_tac "lookup_pdc( non_global_entries_pdc  (the ` {e \<in> range (pdc_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e})) a v = Miss")
    apply (subgoal_tac "lookup_pdc (non_global_entries_pdc (snd(sat_tlb s) - (\<Union>v\<in>vset. {e \<in>snd(sat_tlb s). v \<in> range_of e}))) a v =  Incon")
     apply (subgoal_tac "lookup_pdc (non_global_entries_pdc (snd(sat_tlb s))) a v = Incon")
      apply (case_tac "v \<in> vset")
       apply (drule_tac t = "snd(sat_tlb s)" and a = a in addr_set_minus_non_global_lookup_miss_pdc, clarsimp)
      apply (drule_tac x = a in spec, simp, drule_tac x = v in spec, simp)
      apply (clarsimp simp: lookup_from'_def snap_conv'_def split: if_split_asm option.splits)
     apply (clarsimp simp: non_global_entries_sub_pdc)
     apply (drule lookup_asid_pdc_incon_minus, simp)
    apply (meson lookup_asid_pdc_incon_not_miss)
   apply (rule asid_unequal_lookup_pdc_walk_miss, simp)
  apply (clarsimp simp: non_global_entries_union_pdc)
  apply (subgoal_tac "lookup_pdc (non_global_entries_pdc (the ` {e \<in> range (pdc_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e})) a v =  Miss")
   prefer 2
   apply (rule asid_unequal_lookup_pdc_walk_miss, simp)
  apply (subgoal_tac "lookup_pdc (non_global_entries_pdc (snd(sat_tlb s) - (\<Union>v\<in>vset. {e \<in> snd(sat_tlb s). v \<in> range_of e})))  a v = Hit x3")
   prefer 2
   apply(drule lookup_asid_pdc_hit_mis_hit; simp)
  apply (subgoal_tac "lookup_pdc (non_global_entries_pdc (snd(sat_tlb s)))  a v = Hit x3 \<or>
                         lookup_pdc (non_global_entries_pdc (snd(sat_tlb s)))  a v = Incon")
   prefer 2
   apply (clarsimp simp: non_global_entries_sub_pdc)
   apply (drule lookup_asid_pdc_hit_incon_minus; simp)
  apply (erule disjE)
   prefer 2
   apply (case_tac "v \<in> vset")
    apply (drule_tac t = "snd(sat_tlb s)" and a = a in addr_set_minus_non_global_lookup_miss_pdc, clarsimp)
   apply (drule_tac x = a in spec, simp, drule_tac x = v in spec, simp)
   apply (clarsimp simp: lookup_from'_def snap_conv'_def split: if_split_asm option.splits)
  apply (case_tac "v \<in> vset")
   apply (drule_tac t = "snd(sat_tlb s)" and a = a in addr_set_minus_non_global_lookup_miss_pdc, clarsimp)
  apply (drule_tac x = a in spec, simp, drule_tac x = v in spec, simp)
  by (clarsimp simp: lookup_from'_def snap_conv'_def entry_set_def split: if_split_asm option.splits) 






lemma  flush_with_asid_asid_sat_incon_refine:
  "\<lbrakk> flush (FlushASID a) (s::'a sat_tlb_state_scheme) = ((), s') ;  flush (FlushASID a) (t::'b set_tlb_state_scheme) = ((), t'); 
         tlb_rel_abs (typ_sat_tlb s) (typ_set_tlb t) \<rbrakk> \<Longrightarrow> 
                  tlb_rel_abs (typ_sat_tlb s') (typ_set_tlb t')"
  apply (clarsimp simp: flush_sat_tlb_state_ext_def flush_set_tlb_state_ext_def 
      flush_tlb_pdc_asid_def split: if_split_asm)
   apply (clarsimp simp: tlb_rel_abs_def)
   apply (rule conjI)
    apply (cases s, cases t , clarsimp simp: state.defs)
   apply (rule conjI)
    apply (clarsimp simp: saturated_def)
   apply (rule conjI)
    apply (clarsimp simp: incon_addrs_def)
    apply (rule conjI)
     apply (clarsimp simp: inconsistent_vaddrs_def)
     apply (rule conjI) prefer 2 
      apply clarsimp
      apply (rename_tac v)
      apply (drule union_asid_pdc_incon_cases)
      apply (erule disjE, clarsimp simp: lookup_pdc_walk_not_incon)
      apply (erule disjE, clarsimp simp:)
       apply (subgoal_tac "lookup_pdc (snd(sat_tlb s)) (ASID s) v = Hit x \<or> 
                   lookup_pdc (snd(sat_tlb s)) (ASID s) v = Incon")
        prefer 2
  using lookup_asid_pdc_hit_incon_minus apply blast
       apply (erule disjE)
        apply (subgoal_tac "the(pdc_walk (ASID s) (MEM s) (TTBR0 s) xa) = the(pdc_walk (ASID s) (MEM s) (TTBR0 s) v) \<and> 
                   \<not>is_fault (pdc_walk (ASID s) (MEM s) (TTBR0 s) v)")
         prefer 2
         apply (frule asid_pdc_lookup_range_fault_pt_walk')
         apply (drule_tac x = v in bspec) 
  using lookup_asid_pdc_hit_entry_range apply force
         apply clarsimp
        apply clarsimp
        apply (drule_tac b = v and x = x in saturatd_lookup_pdc_hit_no_fault; simp)
       apply blast
      apply (erule disjE, clarsimp simp: lookup_pdc_walk_not_incon)
      apply (erule disjE, clarsimp simp:)
       apply (subgoal_tac "lookup_pdc (snd(sat_tlb s)) (ASID s) v = Incon")
        apply blast
  using lookup_asid_pdc_incon_minus apply force
      apply (erule disjE, clarsimp simp: lookup_pdc_walk_not_incon)
      apply (clarsimp simp:)
      apply (subgoal_tac "lookup_pdc (snd(sat_tlb s)) (ASID s) v = Incon")
       apply blast
  using lookup_asid_pdc_incon_minus apply force
     apply clarsimp
     apply (rename_tac v)
     apply (drule union_asid_tlb_incon_cases)
     apply (erule disjE, clarsimp simp: asid_tlb_lookup_range_pt_walk_not_incon)
     apply (erule disjE, clarsimp simp:)
      apply (subgoal_tac "lookup'' (fst(sat_tlb s)) (ASID s) v = Hit x \<or> lookup'' (fst(sat_tlb s)) (ASID s) v = Incon")
       prefer 2
  subgoal using lookup_asid_tlb_hit_incon_minus by force
      apply (erule disjE)
       apply (subgoal_tac "the(pt_walk (ASID s) (MEM s) (TTBR0 s) xa) = the(pt_walk (ASID s) (MEM s) (TTBR0 s) v) \<and> 
                   \<not>is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) v)")
        prefer 2
        apply (frule asid_tlb_lookup_range_fault_pt_walk')
        apply (drule_tac x = v in bspec) 
  using lookup_asid_tlb_hit_entry_range apply force
        apply clarsimp
       apply clarsimp
       apply (drule_tac b = v and x = x in saturatd_lookup_hit_no_fault; simp)
      apply blast
     apply (erule disjE, clarsimp simp: asid_tlb_lookup_range_pt_walk_not_incon)
     apply (erule disjE, clarsimp simp:)
      apply (subgoal_tac "lookup'' (fst(sat_tlb s)) (ASID s) v = Incon")
       apply blast
  using lookup_asid_tlb_incon_minus apply force
     apply (erule disjE, clarsimp simp: asid_tlb_lookup_range_pt_walk_not_incon)
     apply (clarsimp simp:)
     apply (subgoal_tac "lookup'' (fst(sat_tlb s)) (ASID s) v = Incon")
      apply blast
  using lookup_asid_tlb_incon_minus apply force
    apply (clarsimp simp: incoherrent_vaddrs_def)
    apply (rule conjI) prefer 2 
     apply clarsimp
     apply (rename_tac v x)
     apply (drule lookup_asid_pdc_hit_union_cases')
     apply (erule disjE, clarsimp)
      apply (subgoal_tac "lookup_pdc (snd(sat_tlb s)) (ASID s) v = Hit x \<or> 
                                lookup_pdc (snd(sat_tlb s)) (ASID s) v = Incon")
       prefer 2
       apply(drule lookup_asid_pdc_hit_incon_minus; simp)
      apply (erule disjE)
       apply force
      apply (clarsimp simp: inconsistent_vaddrs_def)
      apply blast
     apply (erule disjE, clarsimp) 
      apply (drule lookup_pdc_miss_is_fault_intro, simp)
     apply clarsimp
     apply (drule lookup_pdc_miss_is_fault_intro, simp)
    apply clarsimp
    apply (rename_tac v x)
    apply (drule lookup_asid_tlb_hit_union_cases')
    apply (erule disjE, clarsimp)
     apply (subgoal_tac "lookup'' (fst(sat_tlb s)) (ASID s) v = Hit x \<or> 
                                lookup'' (fst(sat_tlb s)) (ASID s) v = Incon")
      prefer 2
      apply(drule lookup_asid_tlb_hit_incon_minus; simp)
     apply (erule disjE)
      apply force
     apply (clarsimp simp: inconsistent_vaddrs_def)
     apply blast
    apply (erule disjE, clarsimp)
     apply (drule asid_tlb_lookup_miss_is_fault_intro, simp)
    apply clarsimp
    apply (drule asid_tlb_lookup_miss_is_fault_intro, simp)
   apply (rule conjI)
    apply (clarsimp simp: incon_addrs_def)
    apply (rule conjI)
     apply (clarsimp simp: inconsistent_vaddrs_def)
     apply (rule conjI) prefer 2 
      apply clarsimp
      apply (rename_tac v)
      apply (drule union_asid_pdc_incon_cases)
      apply (erule disjE, clarsimp simp: lookup_pdc_walk_not_incon)
      apply (erule disjE, clarsimp simp: )
       apply (subgoal_tac "lookup_pdc (global_entries_pdc (snd(sat_tlb s))) (ASID s) v = Hit x")
        apply (subgoal_tac "x \<in> global_entries_pdc (snd(sat_tlb s)) \<and>  v \<in> range_of x")
         apply (clarsimp simp: global_range_def)
         apply blast
  using lookup_asid_pdc_hit_entry_range lookup_in_asid_pdc apply force
  apply (subgoal_tac "ASID s = ASID t") prefer 2   apply (clarsimp simp: state.defs)
  using lookup_sub_asid_of_hit_global_pdc apply force
      apply (erule disjE, clarsimp simp: lookup_pdc_walk_not_incon)
      apply (erule disjE, clarsimp simp: lookup_pdc_walk_not_incon)
       apply (subgoal_tac "lookup_pdc (global_entries_pdc (snd(sat_tlb s))) (ASID s) v = Incon")
        apply (clarsimp simp: lookup_def tagged_pdc_entry_set_def entry_set_def global_range_def 
      split: if_split_asm)
        apply blast
 apply (subgoal_tac "ASID s = ASID t") prefer 2   apply (clarsimp simp: state.defs)
  using lookup_sub_asid_of_incon_global_pdc apply force
      apply (erule disjE, clarsimp simp: lookup_pdc_walk_not_incon)
      apply (clarsimp simp: )
      apply (subgoal_tac "lookup_pdc (global_entries_pdc (snd(sat_tlb s))) (ASID s) v = Incon")
       apply (clarsimp simp: lookup_def tagged_pdc_entry_set_def entry_set_def global_range_def split: if_split_asm)
       apply blast
 apply (subgoal_tac "ASID s = ASID t") prefer 2   apply (clarsimp simp: state.defs)
  using lookup_sub_asid_of_incon_global_pdc apply force
     apply clarsimp
     apply (rename_tac v)
     apply (drule union_asid_tlb_incon_cases)
     apply (erule disjE, clarsimp simp: asid_tlb_lookup_range_pt_walk_not_incon)
     apply (erule disjE, clarsimp simp: )
      apply (subgoal_tac "lookup'' (global_entries (fst(sat_tlb s))) (ASID s) v = Hit x")
       apply (subgoal_tac "x \<in> global_entries (fst(sat_tlb s)) \<and>  v \<in> range_of x")
        apply (clarsimp simp: global_range_def)
        apply blast
  using lookup_asid_tlb_hit_entry_range lookup_in_asid_tlb apply force
 apply (subgoal_tac "ASID s = ASID t") prefer 2   apply (clarsimp simp: state.defs)
  using lookup_sub_asid_of_hit_global apply force
     apply (erule disjE, clarsimp simp: asid_tlb_lookup_range_pt_walk_not_incon)
     apply (erule disjE, clarsimp simp: asid_tlb_lookup_range_pt_walk_not_incon)
      apply (subgoal_tac "lookup'' (global_entries (fst(sat_tlb s))) (ASID s) v = Incon")
       apply (clarsimp simp: lookup_def tagged_entry_set_def entry_set_def global_range_def split: if_split_asm)
       apply blast
 apply (subgoal_tac "ASID s = ASID t") prefer 2   apply (clarsimp simp: state.defs)
  using lookup_sub_asid_of_incon_global apply force
     apply (erule disjE, clarsimp simp: asid_tlb_lookup_range_pt_walk_not_incon)
     apply (clarsimp simp: )
     apply (subgoal_tac "lookup'' (global_entries (fst(sat_tlb s))) (ASID s) v = Incon")
      apply (clarsimp simp: lookup_def tagged_entry_set_def entry_set_def global_range_def split: if_split_asm)
      apply blast
 apply (subgoal_tac "ASID s = ASID t") prefer 2   apply (clarsimp simp: state.defs)
  using lookup_sub_asid_of_incon_global apply force
    apply (clarsimp simp: incoherrent_vaddrs_def) apply (rule conjI) prefer 2 
     apply (clarsimp)
     apply (rename_tac v x)
     apply (drule lookup_asid_pdc_hit_union_cases')
     apply (erule disjE, clarsimp)
      apply (subgoal_tac "lookup_pdc (global_entries_pdc (snd(sat_tlb s))) (ASID s) v = Hit x")
       apply (clarsimp simp: lookup_def tagged_pdc_entry_set_def entry_set_def global_range_def split: if_split_asm)
  apply blast
 apply (subgoal_tac "ASID s = ASID t") prefer 2   apply (clarsimp simp: state.defs)
  using lookup_sub_asid_of_hit_global_pdc apply force
     apply (erule disjE, clarsimp)
      apply (drule lookup_pdc_miss_is_fault_intro, simp)
     apply (clarsimp)
     apply (subgoal_tac "lookup_pdc (global_entries_pdc (snd(sat_tlb s))) (ASID s) v = Hit x")
      apply (clarsimp simp: lookup_def tagged_pdc_entry_set_def entry_set_def global_range_def split: if_split_asm)
  apply blast
 apply (subgoal_tac "ASID s = ASID t") prefer 2   apply (clarsimp simp: state.defs)
  using lookup_sub_asid_of_hit_global_pdc apply force
    apply (clarsimp)
    apply (rename_tac v x)
    apply (drule lookup_asid_tlb_hit_union_cases')
    apply (erule disjE, clarsimp)
     apply (subgoal_tac "lookup'' (global_entries (fst(sat_tlb s))) (ASID s) v = Hit x")
      apply (clarsimp simp: lookup_def tagged_entry_set_def entry_set_def global_range_def split: if_split_asm)
  apply blast
 apply (subgoal_tac "ASID s = ASID t") prefer 2   apply (clarsimp simp: state.defs)
  using lookup_sub_asid_of_hit_global apply force
    apply (erule disjE, clarsimp)
     apply (drule asid_tlb_lookup_miss_is_fault_intro, simp)
    apply (clarsimp)
    apply (subgoal_tac "lookup'' (global_entries (fst(sat_tlb s))) (ASID s) v = Hit x")
     apply (clarsimp simp: lookup_def tagged_entry_set_def entry_set_def global_range_def split: if_split_asm)
  apply blast
 apply (subgoal_tac "ASID s = ASID t") prefer 2   apply (clarsimp simp: state.defs)
  using lookup_sub_asid_of_hit_global apply force
   apply (rule conjI) apply (clarsimp simp: global_range_def) apply (rule conjI) prefer 2 
     apply (clarsimp simp: global_entries_union_pdc)
     apply (rule conjI)
      apply (clarsimp simp: global_entries_pdc_def) 
      apply blast
     apply (subgoal_tac "(\<Union>x\<in>global_entries_pdc (the ` {e \<in> range (pdc_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e}). range_of x) \<subseteq>
     (\<Union>x\<in>global_entries_pdc (snd (sat_tlb s)). range_of x)")
      apply force
     apply (subgoal_tac "global_entries_pdc (the ` {e \<in> range (pdc_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e}) \<subseteq> 
  global_entries_pdc (snd (sat_tlb s))")
      apply force
     apply (clarsimp simp: saturated_def global_entries_pdc_def ) 
     apply (cases s, cases t , clarsimp simp: state.defs) apply force
    apply (clarsimp simp: global_entries_union)
    apply (rule conjI)
     apply (clarsimp simp: global_entries_def) 
     apply blast
    apply (subgoal_tac "(\<Union>x\<in>global_entries (the ` {e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e}). range_of x) \<subseteq>
     (\<Union>x\<in>global_entries (fst (sat_tlb s)). range_of x)")
     apply force
    apply (subgoal_tac "global_entries (the ` {e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e}) \<subseteq> 
  global_entries (fst (sat_tlb s))")
     apply force
    apply (clarsimp simp: saturated_def global_entries_def ) 
    apply (cases s, cases t , clarsimp simp: state.defs) apply force
   apply clarsimp
   apply (rule conjI) prefer 2 
    apply (clarsimp simp: non_global_to_global_pdc [symmetric])
 apply (subgoal_tac "ASID s = ASID t") prefer 2   apply (clarsimp simp: state.defs)
    apply (subgoal_tac "lookup_pdc (non_global_entries_pdc (snd(sat_tlb s) - {e \<in> snd(sat_tlb s). 
        asid_of_pdc e = Some (ASID s)} \<union> the ` {e \<in> range (pdc_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e})) aa v =
           lookup_pdc (non_global_entries_pdc (snd(sat_tlb s))) aa v")
     apply clarsimp
    apply (rule asid_unequal_lookup_non_global_asid_flush_pt_walk_pdc, simp)
   apply (clarsimp simp: non_global_to_global [symmetric])
 apply (subgoal_tac "ASID s = ASID t") prefer 2   apply (clarsimp simp: state.defs)
   apply (subgoal_tac "lookup'' (non_global_entries (fst(sat_tlb s) - {e \<in> fst(sat_tlb s). 
        asid_of e = Some (ASID s)} \<union> the ` {e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e})) aa v =
           lookup'' (non_global_entries (fst(sat_tlb s))) aa v")
    apply clarsimp
   apply (rule asid_unequal_lookup_non_global_asid_flush_pt_walk, simp)
  apply (clarsimp simp: tlb_rel_abs_def)
  apply (rule conjI)
   apply (cases s, cases t , clarsimp simp: state.defs)
  apply (rule conjI)
   apply (clarsimp simp: saturated_def)
  apply (rule conjI)
   apply (clarsimp simp: incon_addrs_def)
   apply (rule conjI)
    apply (clarsimp simp: inconsistent_vaddrs_def)  apply (rule conjI) prefer 2 
     apply clarsimp
     apply (rename_tac v)
     apply (drule union_asid_pdc_incon_cases)
     apply (erule disjE, clarsimp simp: lookup_pdc_walk_not_incon)
     apply (erule disjE, clarsimp simp: )
      apply (subgoal_tac "lookup_pdc (snd(sat_tlb s)) (ASID s) v = Hit x")
       prefer 2
 apply (subgoal_tac "ASID s = ASID t") prefer 2   apply (clarsimp simp: state.defs)
       apply (rule_tac a = a  in asid_unequal_lookup_minus_non_global_hit_hit_pdc, simp, simp)
      apply (subgoal_tac "the (pdc_walk (ASID s) (MEM s) (TTBR0 s) xa) = the (pdc_walk (ASID s) (MEM s) (TTBR0 s) v) \<and> 
                      \<not>is_fault (pdc_walk (ASID s) (MEM s) (TTBR0 s) v)")
       apply (clarsimp)
       apply (frule saturatd_lookup_pdc_hit_no_fault, simp, simp, simp)
      apply (frule asid_pdc_lookup_range_fault_pt_walk')
      apply (drule_tac x = v in bspec) 
  using lookup_asid_pdc_hit_entry_range apply force
      apply clarsimp
     apply (erule disjE, clarsimp simp: lookup_pdc_walk_not_incon)
     apply (erule disjE, clarsimp simp:) 
      apply (subgoal_tac "lookup_pdc (snd(sat_tlb s)) (ASID s) v = Incon")
       apply blast 
  using lookup_asid_pdc_incon_minus apply force
     apply (erule disjE, clarsimp simp: lookup_pdc_walk_not_incon)
     apply clarsimp
     apply (subgoal_tac "lookup_pdc (snd(sat_tlb s)) (ASID s) v = Incon")
      apply blast
  using lookup_asid_pdc_incon_minus apply force
    apply clarsimp
    apply (rename_tac v)
    apply (drule union_asid_tlb_incon_cases)
    apply (erule disjE, clarsimp simp: asid_tlb_lookup_range_pt_walk_not_incon)
    apply (erule disjE, clarsimp simp: )
     apply (subgoal_tac "lookup'' (fst(sat_tlb s)) (ASID s) v = Hit x")
      prefer 2
 apply (subgoal_tac "ASID s = ASID t") prefer 2   apply (clarsimp simp: state.defs)
      apply (rule_tac a = a  in asid_unequal_lookup_minus_non_global_hit_hit, simp, simp)
     apply (subgoal_tac "the (pt_walk (ASID s) (MEM s) (TTBR0 s) xa) = the (pt_walk (ASID s) (MEM s) (TTBR0 s) v) \<and> 
                      \<not>is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) v)")
      apply (clarsimp)
      apply (frule saturatd_lookup_hit_no_fault, simp, simp, simp)
     apply (frule asid_tlb_lookup_range_fault_pt_walk')
     apply (drule_tac x = v in bspec) 
  using lookup_asid_tlb_hit_entry_range apply force
     apply clarsimp
    apply (erule disjE, clarsimp simp: asid_tlb_lookup_range_pt_walk_not_incon)
    apply (erule disjE, clarsimp simp:) 
     apply (subgoal_tac "lookup'' (fst(sat_tlb s)) (ASID s) v = Incon")
      apply blast
  using lookup_asid_tlb_incon_minus apply force
    apply (erule disjE, clarsimp simp: asid_tlb_lookup_range_pt_walk_not_incon)
    apply clarsimp
    apply (subgoal_tac "lookup'' (fst(sat_tlb s)) (ASID s) v = Incon")
     apply blast
  using lookup_asid_tlb_incon_minus apply force
   apply (clarsimp simp: incoherrent_vaddrs_def) apply (rule conjI) prefer 2 
    apply (clarsimp)
    apply (rename_tac v x)
    apply (drule lookup_asid_pdc_hit_union_cases')
    apply (erule disjE, clarsimp)
     apply (subgoal_tac "lookup_pdc (snd(sat_tlb s)) (ASID s) v = Hit x")
      apply force
 apply (subgoal_tac "ASID s = ASID t") prefer 2   apply (clarsimp simp: state.defs)
     apply (rule_tac a = a  in asid_unequal_lookup_minus_non_global_hit_hit_pdc, simp, simp)
    apply (erule disjE, clarsimp)
     apply (drule lookup_pdc_miss_is_fault_intro, simp)
    apply clarsimp
    apply (drule lookup_pdc_miss_is_fault_intro, simp)
   apply (clarsimp)
   apply (rename_tac v x)
   apply (drule lookup_asid_tlb_hit_union_cases')
   apply (erule disjE, clarsimp)
    apply (subgoal_tac "lookup'' (fst(sat_tlb s)) (ASID s) v = Hit x")
     apply force
 apply (subgoal_tac "ASID s = ASID t") prefer 2   apply (clarsimp simp: state.defs)
    apply (rule_tac a = a  in asid_unequal_lookup_minus_non_global_hit_hit, simp, simp)
   apply (erule disjE, clarsimp)
    apply (drule asid_tlb_lookup_miss_is_fault_intro, simp)
   apply clarsimp
   apply (drule asid_tlb_lookup_miss_is_fault_intro, simp)
  apply (rule conjI)
   apply (clarsimp simp: global_range_def) apply (rule conjI) prefer 2 
    apply (clarsimp simp: global_entries_union_pdc)
    apply (rule conjI)
     apply (clarsimp simp: global_entries_pdc_def) 
     apply blast
    apply (subgoal_tac "(\<Union>x\<in>global_entries_pdc (the ` {e \<in> range (pdc_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e}). range_of x) \<subseteq>
     (\<Union>x\<in>global_entries_pdc (snd (sat_tlb s)). range_of x)")
     apply force
    apply (subgoal_tac "global_entries_pdc (the ` {e \<in> range (pdc_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e}) \<subseteq> 
  global_entries_pdc (snd (sat_tlb s))")
     apply force
    apply (clarsimp simp: saturated_def global_entries_pdc_def ) 
    apply (cases s, cases t , clarsimp simp: state.defs) apply force
   apply (clarsimp simp: global_entries_union)
   apply (rule conjI)
    apply (clarsimp simp: global_entries_def) 
    apply blast
   apply (subgoal_tac "(\<Union>x\<in>global_entries (the ` {e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e}). range_of x) \<subseteq>
     (\<Union>x\<in>global_entries (fst (sat_tlb s)). range_of x)")
    apply force
   apply (subgoal_tac "global_entries (the ` {e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e}) \<subseteq> 
  global_entries (fst (sat_tlb s))")
    apply force
   apply (clarsimp simp: saturated_def global_entries_def ) 
   apply (cases s, cases t , clarsimp simp: state.defs) apply force
  apply clarsimp
  apply (rule conjI) prefer 2 
   apply (case_tac "aa = a"; clarsimp?)
    apply (clarsimp simp: non_global_to_global_pdc [symmetric])
    apply (subgoal_tac "lookup_pdc (non_global_entries_pdc (snd(sat_tlb s) - {e \<in> snd(sat_tlb s). asid_of_pdc e = Some a} \<union> 
                  the ` {e \<in> range (pdc_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e})) a v = Miss")
     apply clarsimp
    apply (clarsimp simp: non_global_entries_union_pdc)
    apply (subgoal_tac "lookup_pdc (non_global_entries_pdc (snd(sat_tlb s) - {e \<in> snd(sat_tlb s). asid_of_pdc e = Some a})) a v = Miss")
     apply (subgoal_tac "lookup_pdc (non_global_entries_pdc (the ` {e \<in> range (pdc_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e})) a v = Miss")
      apply (rule lookup_asid_pdc_miss_implies_union_miss, simp, simp)
     apply (rule asid_unequal_lookup_pdc_walk_miss, simp)
    apply (rule lookup_non_global_entries_sub_miss_pdc)
   apply (clarsimp simp: non_global_to_global_pdc [symmetric])
   apply (subgoal_tac "lookup_pdc (non_global_entries_pdc (snd(sat_tlb s) - {e \<in> snd(sat_tlb s). asid_of_pdc e = Some a} \<union> the ` {e \<in> range (pdc_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e})) aa v =
                      lookup_pdc (non_global_entries_pdc (snd(sat_tlb s))) aa v")
    apply (clarsimp simp: lookup_from'_def )
   apply (clarsimp simp: non_global_entries_union_pdc)
   apply (clarsimp simp: non_global_entries_sub_pdc)
   apply (subgoal_tac "lookup_pdc (non_global_entries_pdc {e \<in> snd(sat_tlb s). asid_of_pdc e = Some a}) aa v = Miss")
    apply (subgoal_tac "lookup_pdc (non_global_entries_pdc (the ` {e \<in> range (pdc_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e})) aa v = Miss")
     apply (rule lookup_asid_pdc_minus_union, simp, simp)
    apply (rule asid_unequal_lookup_pdc_walk_miss, simp)
   apply (subgoal_tac "tagged_pdc_entry_set (non_global_entries_pdc {e \<in> snd(sat_tlb s). asid_of_pdc e = Some a}) aa v = {}")
    apply (clarsimp simp: lookup_def)
   apply (clarsimp simp: non_global_entries_pdc_def lookup_def tagged_pdc_entry_set_def entry_set_def split: if_split_asm)
  apply (case_tac "aa = a"; clarsimp?)
   apply (clarsimp simp: non_global_to_global [symmetric])
   apply (subgoal_tac "lookup'' (non_global_entries (fst(sat_tlb s) - {e \<in> fst(sat_tlb s). asid_of e = Some a} \<union> the ` {e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e})) a v = Miss")
    apply clarsimp
   apply (clarsimp simp: non_global_entries_union)
   apply (subgoal_tac "lookup'' (non_global_entries (fst(sat_tlb s) - {e \<in> fst(sat_tlb s). asid_of e = Some a})) a v = Miss")
    apply (subgoal_tac "lookup'' (non_global_entries (the ` {e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e})) a v = Miss")
     apply (rule lookup_asid_tlb_miss_union_miss_miss, simp, simp)
    apply (rule asid_unequal_lookup_pt_walk_miss, simp)
   apply (rule lookup_non_global_entries_sub_miss)
  apply (clarsimp simp: non_global_to_global [symmetric])
  apply (subgoal_tac "lookup'' (non_global_entries (fst(sat_tlb s) - {e \<in> fst(sat_tlb s). asid_of e = Some a} \<union> the ` {e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e})) aa v =
                      lookup'' (non_global_entries (fst(sat_tlb s))) aa v")
   apply (clarsimp simp: lookup_from'_def )
  apply (clarsimp simp: non_global_entries_union)
  apply (clarsimp simp: non_global_entries_sub)
  apply (subgoal_tac "lookup'' (non_global_entries {e \<in> fst(sat_tlb s). asid_of e = Some a}) aa v = Miss")
   apply (subgoal_tac "lookup'' (non_global_entries (the ` {e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e})) aa v = Miss")
    apply (rule lookup_asid_tlb_minus_union, simp, simp)
   apply (rule asid_unequal_lookup_pt_walk_miss, simp)
  apply (subgoal_tac "tagged_entry_set (non_global_entries {e \<in> fst(sat_tlb s). asid_of e = Some a}) aa v = {}")
   apply (clarsimp simp: lookup_def)
  by (clarsimp simp: non_global_entries_def lookup_def tagged_entry_set_def entry_set_def split: if_split_asm)




lemma  flush_with_asid_asid_varange_sat_incon_refine:
  "\<lbrakk>flush (FlushASIDvarange a vset) (s::'a sat_tlb_state_scheme) = ((), s') ;  flush (FlushASIDvarange a vset) (t::'b set_tlb_state_scheme) = ((), t'); 
         tlb_rel_abs (typ_sat_tlb s) (typ_set_tlb t) \<rbrakk> \<Longrightarrow> 
                  tlb_rel_abs (typ_sat_tlb s') (typ_set_tlb t')"
  apply (clarsimp simp: flush_sat_tlb_state_ext_def flush_set_tlb_state_ext_def flush_tlb_pdc_a_vset_def Let_def split: if_split_asm)
   apply (clarsimp simp: tlb_rel_abs_def)
   apply (rule conjI)
    apply (cases s, cases t , clarsimp simp: state.defs)
   apply (rule conjI)
    apply (clarsimp simp: saturated_def)
   apply (rule conjI)
    apply (clarsimp simp: incon_addrs_def)
    apply (rule conjI)
     apply (clarsimp simp: inconsistent_vaddrs_def) apply (rule conjI) prefer 2 
      apply clarsimp
      apply (rename_tac v)
      apply (rule conjI)
       apply (drule union_asid_pdc_incon_cases)
       apply (erule disjE, clarsimp simp: lookup_pdc_walk_not_incon)
       apply (erule disjE, clarsimp simp: )
        apply (subgoal_tac " lookup_pdc (snd(sat_tlb s)) (ASID s) v = Hit x \<or> 
                        lookup_pdc (snd(sat_tlb s)) (ASID s) v = Incon")
         prefer 2
  using lookup_asid_pdc_hit_incon_minus apply fastforce
        apply (erule_tac P = "lookup_pdc (snd(sat_tlb s)) (ASID s) v = Hit x " in disjE)
         prefer 2
         apply blast
        apply (subgoal_tac "the(pdc_walk (ASID s) (MEM s) (TTBR0 s) xa) = the(pdc_walk (ASID s) (MEM s) (TTBR0 s) v) \<and> 
                   \<not>is_fault (pdc_walk (ASID s) (MEM s) (TTBR0 s) v)")
         prefer 2
         apply (frule asid_pdc_lookup_range_fault_pt_walk')
         apply (drule_tac x = v in bspec) 
  using lookup_asid_pdc_hit_entry_range apply force
         apply clarsimp
        apply clarsimp
        apply (drule_tac b = v and x = x in saturatd_lookup_pdc_hit_no_fault; simp)
       apply (erule disjE, clarsimp simp: lookup_pdc_walk_not_incon)
       apply (erule disjE, clarsimp simp: )
        apply (subgoal_tac "lookup_pdc (snd(sat_tlb s)) (ASID s) v = Incon")
         apply blast
  using lookup_asid_pdc_incon_minus apply force
       apply (erule disjE, clarsimp simp: lookup_pdc_walk_not_incon)
       apply (clarsimp simp: )
       apply (subgoal_tac "lookup_pdc (snd(sat_tlb s)) (ASID s) v = Incon")
        apply blast
  using lookup_asid_pdc_incon_minus apply force
      apply clarsimp
      apply (drule union_asid_pdc_incon_cases)
      apply (erule disjE, clarsimp simp: lookup_pdc_walk_not_incon)
      apply (erule disjE, clarsimp simp: )
       apply (subgoal_tac "lookup' (global_entries_pdc (snd(sat_tlb s)))  v = Hit x")
        apply (clarsimp simp: lookup_def entry_set_def global_range_def global_entries_pdc_def split: if_split_asm) apply blast
       apply (subgoal_tac "ASID s = ASID t") prefer 2   apply (clarsimp simp: state.defs)
       apply (rule_tac vset = vset in  vaddr_elem_lookup_hit_global_entries_hit_pdc, simp, simp)
      apply (erule disjE, clarsimp simp: lookup_pdc_walk_not_incon)
      apply (erule disjE, clarsimp simp:)
       apply (subgoal_tac "lookup' (global_entries_pdc (snd(sat_tlb s)))  v = Incon")
        apply (clarsimp simp: lookup_def entry_set_def global_range_def split: if_split_asm)
        apply force
       apply (subgoal_tac "ASID s = ASID t") prefer 2   apply (clarsimp simp: state.defs)
       apply (rule_tac vset = vset in  vaddr_elem_lookup_incon_global_entries_incon_pdc, simp, simp)
      apply (erule disjE, clarsimp simp: lookup_pdc_walk_not_incon)
      apply (clarsimp simp:)
      apply (subgoal_tac "lookup' (global_entries_pdc (snd(sat_tlb s)))  v = Incon")
       apply (clarsimp simp: lookup_def entry_set_def global_range_def split: if_split_asm)
       apply blast
      apply (subgoal_tac "ASID s = ASID t") prefer 2   apply (clarsimp simp: state.defs)
      apply (rule_tac vset = vset in  vaddr_elem_lookup_incon_global_entries_incon_pdc, simp, simp)
     apply clarsimp
     apply (rename_tac v)
     apply (rule conjI)
      apply (drule union_asid_tlb_incon_cases)
      apply (erule disjE, clarsimp simp: asid_tlb_lookup_range_pt_walk_not_incon)
      apply (erule disjE, clarsimp simp: )
       apply (subgoal_tac " lookup'' (fst(sat_tlb s)) (ASID s) v = Hit x \<or> 
                        lookup'' (fst(sat_tlb s)) (ASID s) v = Incon")
        prefer 2
  using lookup_asid_tlb_hit_incon_minus apply fastforce
       apply (erule_tac P = "lookup'' (fst(sat_tlb s)) (ASID s) v = Hit x " in disjE)
        prefer 2
        apply blast
       apply (subgoal_tac "the(pt_walk (ASID s) (MEM s) (TTBR0 s) xa) = the(pt_walk (ASID s) (MEM s) (TTBR0 s) v) \<and> 
                   \<not>is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) v)")
        prefer 2
        apply (frule asid_tlb_lookup_range_fault_pt_walk')
        apply (drule_tac x = v in bspec) 
  using lookup_asid_tlb_hit_entry_range apply force
        apply clarsimp
       apply clarsimp
       apply (drule_tac b = v and x = x in saturatd_lookup_hit_no_fault; simp)
      apply (erule disjE, clarsimp simp: asid_tlb_lookup_range_pt_walk_not_incon)
      apply (erule disjE, clarsimp simp: )
       apply (subgoal_tac "lookup'' (fst(sat_tlb s)) (ASID s) v = Incon")
        apply blast
  using lookup_asid_tlb_incon_minus apply force
      apply (erule disjE, clarsimp simp: asid_tlb_lookup_range_pt_walk_not_incon)
      apply (clarsimp simp: )
      apply (subgoal_tac "lookup'' (fst(sat_tlb s)) (ASID s) v = Incon")
       apply blast
  using lookup_asid_tlb_incon_minus apply force
     apply clarsimp
     apply (drule union_asid_tlb_incon_cases)
     apply (erule disjE, clarsimp simp: asid_tlb_lookup_range_pt_walk_not_incon)
     apply (erule disjE, clarsimp simp: )
      apply (subgoal_tac "lookup' (global_entries (fst(sat_tlb s)))  v = Hit x")
       apply (clarsimp simp: lookup_def entry_set_def global_range_def global_entries_def split: if_split_asm) apply blast
      apply (subgoal_tac "ASID s = ASID t") prefer 2   apply (clarsimp simp: state.defs)
      apply (rule_tac vset = vset in  vaddr_elem_lookup_hit_global_entries_hit, simp, simp)
     apply (erule disjE, clarsimp simp: asid_tlb_lookup_range_pt_walk_not_incon)
     apply (erule disjE, clarsimp simp:)
      apply (subgoal_tac "lookup' (global_entries (fst(sat_tlb s)))  v = Incon")
       apply (clarsimp simp: lookup_def entry_set_def global_range_def split: if_split_asm)
       apply force
      apply (subgoal_tac "ASID s = ASID t") prefer 2   apply (clarsimp simp: state.defs)
      apply (rule_tac vset = vset in  vaddr_elem_lookup_incon_global_entries_incon, simp, simp)
     apply (erule disjE, clarsimp simp: asid_tlb_lookup_range_pt_walk_not_incon)
     apply (clarsimp simp:)
     apply (subgoal_tac "lookup' (global_entries (fst(sat_tlb s)))  v = Incon")
      apply (clarsimp simp: lookup_def entry_set_def global_range_def split: if_split_asm)
      apply blast
     apply (subgoal_tac "ASID s = ASID t") prefer 2   apply (clarsimp simp: state.defs)
     apply (rule_tac vset = vset in  vaddr_elem_lookup_incon_global_entries_incon, simp, simp)
    apply (clarsimp simp: incoherrent_vaddrs_def) apply (rule conjI) prefer 2 
     apply clarsimp
     apply (rename_tac v x)
     apply (rule conjI)
      apply (drule lookup_asid_pdc_hit_union_cases')
      apply (erule disjE, clarsimp)
       apply (case_tac "lookup_pdc (snd(sat_tlb s)) (ASID s) v"; clarsimp?)
         apply (simp add: lookup_miss_minus_miss_pdc)
        apply (clarsimp simp: inconsistent_vaddrs_def) apply blast
       apply force
      apply (erule disjE, clarsimp)
       apply (drule lookup_pdc_miss_is_fault_intro, clarsimp)
      apply (clarsimp)
      apply (drule lookup_pdc_miss_is_fault_intro, clarsimp)
     apply clarsimp
     apply (drule lookup_asid_pdc_hit_union_cases')
     apply (erule disjE, clarsimp)
      apply (subgoal_tac "lookup' (global_entries_pdc (snd(sat_tlb s)))  v = Hit x")  
       apply (clarsimp simp: lookup_def entry_set_def global_range_def split: if_split_asm) apply blast
      apply (subgoal_tac "ASID s = ASID t") prefer 2   apply (clarsimp simp: state.defs)
      apply (rule_tac vset = vset in  vaddr_elem_lookup_hit_global_entries_hit_pdc, simp, simp)
     apply (erule disjE, clarsimp)
      apply (drule lookup_pdc_miss_is_fault_intro, clarsimp)
     apply (drule lookup_pdc_miss_is_fault_intro, clarsimp)
    apply clarsimp
    apply (rename_tac v x)
    apply (rule conjI)
     apply (drule lookup_asid_tlb_hit_union_cases')
     apply (erule disjE, clarsimp)
      apply (case_tac "lookup'' (fst(sat_tlb s)) (ASID s) v"; clarsimp?)
        apply (simp add: lookup_miss_minus_miss)
       apply (clarsimp simp: inconsistent_vaddrs_def) apply blast
      apply force
     apply (erule disjE, clarsimp)
      apply (drule asid_tlb_lookup_miss_is_fault_intro, clarsimp)
     apply (clarsimp)
     apply (drule asid_tlb_lookup_miss_is_fault_intro, clarsimp)
    apply clarsimp
    apply (drule lookup_asid_tlb_hit_union_cases')
    apply (erule disjE, clarsimp)
     apply (subgoal_tac "lookup' (global_entries (fst(sat_tlb s)))  v = Hit x")  
      apply (clarsimp simp: lookup_def entry_set_def global_range_def split: if_split_asm) apply blast
     apply (subgoal_tac "ASID s = ASID t") prefer 2   apply (clarsimp simp: state.defs)
     apply (rule_tac vset = vset in  vaddr_elem_lookup_hit_global_entries_hit, simp, simp)
    apply (erule disjE, clarsimp)
     apply (drule asid_tlb_lookup_miss_is_fault_intro, clarsimp)
    apply (drule asid_tlb_lookup_miss_is_fault_intro, clarsimp)
   apply (rule conjI)
    apply (clarsimp simp: global_range_def) apply (rule conjI) prefer 2 
     apply (clarsimp simp: global_entries_union_pdc)
     apply (rule conjI)
      apply (clarsimp simp: global_entries_pdc_def) 
      apply blast
     apply (subgoal_tac "(\<Union>x\<in>global_entries_pdc (the ` {e \<in> range (pdc_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e}). range_of x) \<subseteq>
     (\<Union>x\<in>global_entries_pdc (snd (sat_tlb s)). range_of x)")
      apply force
     apply (subgoal_tac "global_entries_pdc (the ` {e \<in> range (pdc_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e}) \<subseteq> 
  global_entries_pdc (snd (sat_tlb s))")
      apply force
     apply (clarsimp simp: saturated_def global_entries_pdc_def ) 
     apply (cases s, cases t , clarsimp simp: state.defs) apply force
    apply (clarsimp simp: global_entries_union)
    apply (rule conjI)
     apply (clarsimp simp: global_entries_def) 
     apply blast
    apply (subgoal_tac "(\<Union>x\<in>global_entries (the ` {e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e}). range_of x) \<subseteq>
     (\<Union>x\<in>global_entries (fst (sat_tlb s)). range_of x)")
     apply force
    apply (subgoal_tac "global_entries (the ` {e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e}) \<subseteq> 
  global_entries (fst (sat_tlb s))")
     apply force
    apply (clarsimp simp: saturated_def global_entries_def ) 
    apply (cases s, cases t , clarsimp simp: state.defs) apply force
   apply clarsimp
   apply (rule conjI) prefer 2 
    apply (subgoal_tac "ASID s = ASID t") prefer 2   apply (clarsimp simp: state.defs)
    apply (clarsimp simp: non_global_to_global_pdc [symmetric] non_global_entries_union_pdc)
    apply (subgoal_tac "lookup_pdc (non_global_entries_pdc (the ` {e \<in> range (pdc_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e})) aa v = Miss")
     apply (subgoal_tac "lookup_pdc
            (non_global_entries_pdc (snd(sat_tlb s) - (\<Union>x\<in>vset. {e \<in> snd(sat_tlb s). x \<in> range_of e \<and> asid_of_pdc e = Some (ASID s)})) \<union> non_global_entries_pdc (the ` {e \<in> range (pdc_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e})) aa v =
   lookup_pdc
            (non_global_entries_pdc (snd(sat_tlb s) - (\<Union>x\<in>vset. {e \<in> snd(sat_tlb s). x \<in> range_of e \<and> asid_of_pdc e = Some (ASID s)}))) aa v")
      prefer 2 
  using lookup_asid_pdc_miss_union_equal 
      apply auto[1]
     apply clarsimp
     apply (subgoal_tac "lookup_pdc (non_global_entries_pdc (snd(sat_tlb s) - (\<Union>x\<in>vset. {e \<in> snd(sat_tlb s). x \<in> range_of e \<and> asid_of_pdc e = Some (ASID s)}))) aa v \<le> 
                       lookup_pdc (non_global_entries_pdc (snd(sat_tlb s)))  aa v")
  using order_trans apply force
     apply (rule asid_pdc_mono)
     apply (clarsimp simp: non_global_entries_pdc_def)
    apply (rule asid_unequal_lookup_pdc_walk_miss, simp)
   apply (subgoal_tac "ASID s = ASID t") prefer 2   apply (clarsimp simp: state.defs)
   apply (clarsimp simp: non_global_to_global [symmetric] non_global_entries_union)
   apply (subgoal_tac "lookup'' (non_global_entries (the ` {e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e})) aa v = Miss")
    apply (subgoal_tac "lookup''
            (non_global_entries (fst(sat_tlb s) - (\<Union>x\<in>vset. {e \<in> fst(sat_tlb s). x \<in> range_of e \<and> asid_of e = Some (ASID s)})) \<union> non_global_entries (the ` {e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e})) aa v =
   lookup''
            (non_global_entries (fst(sat_tlb s) - (\<Union>x\<in>vset. {e \<in> fst(sat_tlb s). x \<in> range_of e \<and> asid_of e = Some (ASID s)}))) aa v")
     prefer 2
  using lookup_asid_tlb_miss_union_equal 
     apply auto[1]
    apply clarsimp
    apply (subgoal_tac "lookup'' (non_global_entries (fst(sat_tlb s) - (\<Union>x\<in>vset. {e \<in> fst(sat_tlb s). x \<in> range_of e \<and> asid_of e = Some (ASID s)}))) aa v \<le> 
                       lookup'' (non_global_entries (fst(sat_tlb s)))  aa v")
  using order_trans apply force
    apply (rule asid_tlb_mono)
    apply (clarsimp simp: non_global_entries_def)
   apply (rule asid_unequal_lookup_pt_walk_miss, simp)
  apply (subgoal_tac "ASID t = ASID s") prefer 2   apply (clarsimp simp: tlb_rel_abs_def state.defs)
  apply (clarsimp simp: tlb_rel_abs_def)
  apply (rule conjI)
   apply (cases s, cases t , clarsimp simp: state.defs)
  apply (rule conjI)
   apply (clarsimp simp: saturated_def)
  apply (rule conjI)
   apply (clarsimp simp: incon_addrs_def)
   apply (rule conjI)
    apply (clarsimp simp: inconsistent_vaddrs_def)
    apply (rule conjI) prefer 2 
     apply clarsimp
     apply (rename_tac v)
     apply (drule union_asid_pdc_incon_cases)
     apply (erule disjE, clarsimp simp: lookup_pdc_walk_not_incon )
     apply (erule disjE, clarsimp simp: )
      apply (subgoal_tac "lookup_pdc (snd(sat_tlb s)) (ASID s) v = Hit x")
       prefer 2
       apply (subgoal_tac "lookup_pdc (\<Union>v\<in>vset. {e \<in> snd(sat_tlb s). v \<in> range_of e \<and> asid_of_pdc e = Some a}) (ASID s) v = Miss") 
        apply (drule lookup_asid_pdc_minus_hit', simp, simp)
       apply (subgoal_tac "tagged_pdc_entry_set (\<Union>v\<in>vset. {e \<in> snd(sat_tlb s). v \<in> range_of e \<and> asid_of_pdc e = Some a}) (ASID s) v = {}")
        apply (clarsimp simp: lookup_def)
       apply (clarsimp simp: lookup_def tagged_pdc_entry_set_def entry_set_def split: if_split_asm option.splits)
      apply (subgoal_tac "the(pdc_walk (ASID s) (MEM s) (TTBR0 s) xa) = the(pdc_walk (ASID s) (MEM s) (TTBR0 s) v) \<and> 
                   \<not>is_fault (pdc_walk (ASID s) (MEM s) (TTBR0 s) v)")
       prefer 2
       apply (frule asid_pdc_lookup_range_fault_pt_walk')
       apply (drule_tac x = v in bspec) 
  using lookup_asid_pdc_hit_entry_range apply force
       apply clarsimp
      apply clarsimp
      apply (drule_tac b = v and x = x in saturatd_lookup_pdc_hit_no_fault; simp) 
     apply (erule disjE, clarsimp simp: lookup_pdc_walk_not_incon)
     apply (erule disjE, clarsimp)
      apply (subgoal_tac "lookup_pdc (snd(sat_tlb s)) (ASID s) v = Incon")
       apply blast
  using lookup_asid_pdc_incon_minus apply force
     apply (erule disjE, clarsimp simp: lookup_pdc_walk_not_incon)
     apply (subgoal_tac "lookup_pdc (snd(sat_tlb s)) (ASID s) v = Incon")
      apply blast
  using lookup_asid_pdc_incon_minus apply force
    apply clarsimp
    apply (rename_tac v)
    apply (drule union_asid_tlb_incon_cases)
    apply (erule disjE, clarsimp simp: asid_tlb_lookup_range_pt_walk_not_incon)
    apply (erule disjE, clarsimp simp: )
     apply (subgoal_tac "lookup'' (fst(sat_tlb s)) (ASID s) v = Hit x")
      prefer 2
      apply (subgoal_tac "lookup'' (\<Union>v\<in>vset. {e \<in> fst(sat_tlb s). v \<in> range_of e \<and> asid_of e = Some a}) (ASID s) v = Miss")
       apply (drule lookup_asid_tlb_minus_hit', simp, simp)
      apply (subgoal_tac "tagged_entry_set (\<Union>v\<in>vset. {e \<in> fst(sat_tlb s). v \<in> range_of e \<and> asid_of e = Some a}) (ASID s) v = {}")
       apply (clarsimp simp: lookup_def)
      apply (clarsimp simp: lookup_def tagged_entry_set_def entry_set_def split: if_split_asm option.splits)
     apply (subgoal_tac "the(pt_walk (ASID s) (MEM s) (TTBR0 s) xa) = the(pt_walk (ASID s) (MEM s) (TTBR0 s) v) \<and> 
                   \<not>is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) v)")
      prefer 2
      apply (frule asid_tlb_lookup_range_fault_pt_walk')
      apply (drule_tac x = v in bspec) 
  using lookup_asid_tlb_hit_entry_range apply force
      apply clarsimp
     apply clarsimp
     apply (drule_tac b = v and x = x in saturatd_lookup_hit_no_fault; simp)
    apply (erule disjE, clarsimp simp: asid_tlb_lookup_range_pt_walk_not_incon)
    apply (erule disjE, clarsimp)
     apply (subgoal_tac "lookup'' (fst(sat_tlb s)) (ASID s) v = Incon")
      apply blast
  using lookup_asid_tlb_incon_minus apply force
    apply (erule disjE, clarsimp simp: asid_tlb_lookup_range_pt_walk_not_incon)
    apply (subgoal_tac "lookup'' (fst(sat_tlb s)) (ASID s) v = Incon")
     apply blast
  using lookup_asid_tlb_incon_minus apply force
   apply (clarsimp simp: incoherrent_vaddrs_def) apply (rule conjI) prefer 2 
    apply clarsimp
    apply (rename_tac v x)
    apply (drule lookup_asid_pdc_hit_union_cases')
    apply (erule disjE, clarsimp)
     apply (subgoal_tac "lookup_pdc (snd(sat_tlb s)) (ASID s) v = Hit x")
      apply force
     apply (subgoal_tac "lookup_pdc (\<Union>v\<in>vset. {e \<in> snd(sat_tlb s). v \<in> range_of e \<and> asid_of_pdc e = Some a}) (ASID s) v = Miss")
      apply (drule lookup_asid_pdc_minus_hit', simp, simp)
     apply (subgoal_tac "tagged_pdc_entry_set (\<Union>v\<in>vset. {e \<in> snd(sat_tlb s). v \<in> range_of e \<and> asid_of_pdc e = Some a}) (ASID s) v = {}")
      apply (clarsimp simp: lookup_def)
     apply (clarsimp simp: lookup_def tagged_pdc_entry_set_def entry_set_def split: if_split_asm option.splits)
    apply (erule disjE, clarsimp) 
     apply (drule lookup_pdc_miss_is_fault_intro, simp)
    apply (drule lookup_pdc_miss_is_fault_intro, simp)
   apply clarsimp
   apply (rename_tac v x)
   apply (drule lookup_asid_tlb_hit_union_cases')
   apply (erule disjE, clarsimp)
    apply (subgoal_tac "lookup'' (fst(sat_tlb s)) (ASID s) v = Hit x")
     apply force
    apply (subgoal_tac "lookup'' (\<Union>v\<in>vset. {e \<in> fst(sat_tlb s). v \<in> range_of e \<and> asid_of e = Some a}) (ASID s) v = Miss")
     apply (drule lookup_asid_tlb_minus_hit', simp, simp)
    apply (subgoal_tac "tagged_entry_set (\<Union>v\<in>vset. {e \<in> fst(sat_tlb s). v \<in> range_of e \<and> asid_of e = Some a}) (ASID s) v = {}")
     apply (clarsimp simp: lookup_def)
    apply (clarsimp simp: lookup_def tagged_entry_set_def entry_set_def split: if_split_asm option.splits)
   apply (erule disjE, clarsimp)
    apply (drule asid_tlb_lookup_miss_is_fault_intro, simp)
   apply (drule asid_tlb_lookup_miss_is_fault_intro, simp)
  apply (rule conjI)
   apply (clarsimp simp: global_range_def) apply (rule conjI) prefer 2 
    apply (clarsimp simp: global_entries_union_pdc)
    apply (rule conjI)
     apply (clarsimp simp: global_entries_pdc_def) 
     apply blast
    apply (subgoal_tac "(\<Union>x\<in>global_entries_pdc (the ` {e \<in> range (pdc_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e}). range_of x) \<subseteq>
     (\<Union>x\<in>global_entries_pdc (snd (sat_tlb s)). range_of x)")
     apply force
    apply (subgoal_tac "global_entries_pdc (the ` {e \<in> range (pdc_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e}) \<subseteq> 
  global_entries_pdc (snd (sat_tlb s))")
     apply force
    apply (clarsimp simp: saturated_def global_entries_pdc_def ) 
    apply (cases s, cases t , clarsimp simp: state.defs) apply force
   apply (clarsimp simp: global_entries_union)
   apply (rule conjI)
    apply (clarsimp simp: global_entries_def) 
    apply blast
   apply (subgoal_tac "(\<Union>x\<in>global_entries (the ` {e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e}). range_of x) \<subseteq>
     (\<Union>x\<in>global_entries (fst (sat_tlb s)). range_of x)")
    apply force
   apply (subgoal_tac "global_entries (the ` {e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e}) \<subseteq> 
  global_entries (fst (sat_tlb s))")
    apply force
   apply (clarsimp simp: saturated_def global_entries_def ) 
   apply (cases s, cases t , clarsimp simp: state.defs) apply force
  apply (clarsimp) apply (rule conjI) prefer 2 defer
   apply (clarsimp simp: non_global_to_global [symmetric] non_global_entries_union)
   apply (case_tac "aa \<noteq> a"; clarsimp?)
    apply (subgoal_tac "lookup'' (non_global_entries (fst(sat_tlb s) - (\<Union>v\<in>vset. {e \<in> fst(sat_tlb s). v \<in> range_of e \<and> asid_of e = Some a})) \<union> 
                          non_global_entries (the ` {e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e})) aa v =
                       lookup'' (non_global_entries (fst(sat_tlb s))) aa v")
     apply (clarsimp simp: lookup_from'_def)
    apply (clarsimp simp: non_global_entries_sub)
    apply (subgoal_tac "lookup'' (non_global_entries (\<Union>v\<in>vset. {e \<in> fst(sat_tlb s). v \<in> range_of e \<and> asid_of e = Some a}))      aa v = Miss")
     apply (subgoal_tac "lookup'' (non_global_entries (the ` {e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e}))      aa v = Miss")
  using lookup_asid_tlb_minus_union apply force
     apply (rule asid_unequal_lookup_pt_walk_miss, simp)
    apply (subgoal_tac "tagged_entry_set (non_global_entries (\<Union>v\<in>vset. {e \<in> fst(sat_tlb s). v \<in> range_of e \<and> asid_of e = Some a})) aa v = {}")
     apply (clarsimp simp: lookup_def)
    apply (clarsimp simp: non_global_entries_def lookup_def tagged_entry_set_def entry_set_def split: if_split_asm option.splits)
   apply (subgoal_tac "lookup'' (non_global_entries (the ` {e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e})) a v = Miss")
    prefer 2
    apply (rule asid_unequal_lookup_pt_walk_miss, simp)
   apply (subgoal_tac "lookup'' (non_global_entries (fst(sat_tlb s) - (\<Union>v\<in>vset. {e \<in> fst(sat_tlb s). v \<in> range_of e \<and> asid_of e = Some a})) \<union> 
               non_global_entries (the ` {e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e})) a v =
                   lookup'' (non_global_entries (fst(sat_tlb s) - (\<Union>v\<in>vset. {e \<in> fst(sat_tlb s). v \<in> range_of e \<and> asid_of e = Some a}))) a v")
    prefer 2
  using lookup_asid_tlb_miss_union_equal apply force
   apply clarsimp
   apply (drule_tac x = a in spec, simp, drule_tac x = v in spec)
   apply (case_tac "lookup'' (non_global_entries (fst(sat_tlb s))) a v"; clarsimp)
     apply (subgoal_tac "lookup'' (non_global_entries (fst(sat_tlb s) - (\<Union>v\<in>vset. {e \<in> fst(sat_tlb s). v \<in> range_of e \<and> asid_of e = Some a}))) a v = Miss")
      apply force
     apply (clarsimp simp: non_global_entries_sub)
  using lookup_miss_minus_miss 
     apply blast
    apply (case_tac "v \<in> vset")
     apply (subgoal_tac "fst(lookup_from' (\<lambda>a'. if a' = a then (fst (snapshot (set_tlb t) a) - vset, \<lambda>v. if v \<in> vset then Fault else snd (snapshot (set_tlb t) a) v) else snapshot (set_tlb t) a') a v) = Miss")
      prefer 2
      apply (clarsimp simp:  lookup_from'_def snap_conv'_def split: if_split_asm option.splits)
     apply (clarsimp)
     apply (subgoal_tac "tagged_entry_set (non_global_entries (fst(sat_tlb s) - (\<Union>v\<in>vset. {e \<in> fst(sat_tlb s). v \<in> range_of e \<and> asid_of e = Some a}))) a v = {}")
      apply (clarsimp simp: lookup_def)
     apply (clarsimp simp: non_global_entries_def lookup_def tagged_entry_set_def entry_set_def split: if_split_asm option.splits)
    apply (subgoal_tac "fst(lookup_from' (\<lambda>a'. if a' = a then (fst (snapshot (set_tlb t) a) - vset, \<lambda>v. if v \<in> vset then Fault else snd (snapshot (set_tlb t) a) v) else snapshot (set_tlb t) a') a v) = Incon")
     apply force
    apply (clarsimp simp:  lookup_from'_def snap_conv'_def split: if_split_asm option.splits)
   apply (case_tac "v \<in> vset")
    apply (subgoal_tac "lookup'' (non_global_entries (fst(sat_tlb s) - (\<Union>v\<in>vset. {e \<in> fst(sat_tlb s). v \<in> range_of e \<and> asid_of e = Some a}))) a v = Miss")
     apply force
    apply (subgoal_tac "tagged_entry_set (non_global_entries (fst(sat_tlb s) - (\<Union>v\<in>vset. {e \<in> fst(sat_tlb s). v \<in> range_of e \<and> asid_of e = Some a}))) a v = {}")
     apply (clarsimp simp: lookup_def)
    apply (clarsimp simp: non_global_entries_def lookup_def tagged_entry_set_def entry_set_def split: if_split_asm option.splits)
   apply (subgoal_tac "fst(lookup_from' (\<lambda>a'. if a' = a then (fst (snapshot (set_tlb t) a) - vset, \<lambda>v. if v \<in> vset then Fault else snd (snapshot (set_tlb t) a) v) else snapshot (set_tlb t) a') a v)=
                      fst(lookup_from' (snapshot (set_tlb t)) a v)")
    prefer 2
    apply (clarsimp simp:  lookup_from'_def snap_conv'_def split: if_split_asm option.splits)
   apply clarsimp
   apply (case_tac "fst(lookup_from' (snapshot (set_tlb t)) a v)"; clarsimp?)
   apply (clarsimp simp: non_global_entries_sub)
   apply (subgoal_tac "lookup'' (non_global_entries (fst(sat_tlb s)) - non_global_entries (\<Union>v\<in>vset. {e \<in>fst(sat_tlb s). v \<in> range_of e \<and> asid_of e = Some a})) a v = Miss \<or> 
       lookup'' (non_global_entries (fst(sat_tlb s)) - non_global_entries (\<Union>v\<in>vset. {e \<in> fst(sat_tlb s). v \<in> range_of e \<and> asid_of e = Some a})) a v =  Hit x3a ")
    apply (erule disjE)
     apply clarsimp
    apply clarsimp
   apply (rule lookup_miss_minus_miss_hit, simp)
  apply (clarsimp simp: non_global_to_global_pdc [symmetric] non_global_entries_union_pdc)
  apply (case_tac "aa \<noteq> a"; clarsimp?)
   apply (subgoal_tac "lookup_pdc (non_global_entries_pdc (snd(sat_tlb s) - (\<Union>v\<in>vset. {e \<in> snd(sat_tlb s). v \<in> range_of e \<and> asid_of_pdc e = Some a})) \<union> 
                          non_global_entries_pdc (the ` {e \<in> range (pdc_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e})) aa v =
                       lookup_pdc (non_global_entries_pdc (snd(sat_tlb s))) aa v")
    apply (clarsimp simp: lookup_from'_def)
   apply (clarsimp simp: non_global_entries_sub_pdc)
   apply (subgoal_tac "lookup_pdc (non_global_entries_pdc (\<Union>v\<in>vset. {e \<in> snd(sat_tlb s). v \<in> range_of e \<and> asid_of_pdc e = Some a}))      aa v = Miss")
    apply (subgoal_tac "lookup_pdc (non_global_entries_pdc (the ` {e \<in> range (pdc_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e}))      aa v = Miss")
  using lookup_asid_pdc_minus_union apply force
    apply (rule asid_unequal_lookup_pdc_walk_miss, simp)
   apply (subgoal_tac "tagged_pdc_entry_set (non_global_entries_pdc (\<Union>v\<in>vset. {e \<in> snd(sat_tlb s). v \<in> range_of e \<and> asid_of_pdc e = Some a})) aa v = {}")
    apply (clarsimp simp: lookup_def)
   apply (clarsimp simp: non_global_entries_pdc_def lookup_def tagged_pdc_entry_set_def entry_set_def split: if_split_asm option.splits)
  apply (subgoal_tac "lookup_pdc (non_global_entries_pdc (the ` {e \<in> range (pdc_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e})) a v = Miss")
   prefer 2
   apply (rule asid_unequal_lookup_pdc_walk_miss, simp)
  apply (subgoal_tac "lookup_pdc (non_global_entries_pdc (snd(sat_tlb s) - (\<Union>v\<in>vset. {e \<in> snd(sat_tlb s). v \<in> range_of e \<and> asid_of_pdc e = Some a})) \<union> 
               non_global_entries_pdc (the ` {e \<in> range (pdc_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e})) a v =
                   lookup_pdc (non_global_entries_pdc (snd(sat_tlb s) - (\<Union>v\<in>vset. {e \<in> snd(sat_tlb s). v \<in> range_of e \<and> asid_of_pdc e = Some a}))) a v")
   prefer 2
  using lookup_asid_pdc_miss_union_equal apply force
  apply clarsimp
  apply (drule_tac x = a in spec, simp, drule_tac x = v in spec)
  apply (case_tac "lookup_pdc (non_global_entries_pdc (snd(sat_tlb s))) a v"; clarsimp)
    apply (subgoal_tac "lookup_pdc (non_global_entries_pdc (snd(sat_tlb s) - (\<Union>v\<in>vset. {e \<in> snd(sat_tlb s). v \<in> range_of e \<and> asid_of_pdc e = Some a}))) a v = Miss")
     apply force
    apply (clarsimp simp: non_global_entries_sub_pdc)
  using lookup_miss_minus_miss_pdc
    apply blast
   apply (case_tac "v \<in> vset")
    apply (subgoal_tac "snd(lookup_from' (\<lambda>a'. if a' = a then (fst (snapshot (set_tlb t) a) - vset, \<lambda>v. if v \<in> vset then Fault else snd (snapshot (set_tlb t) a) v) else snapshot (set_tlb t) a') a v) = Miss")
     prefer 2
     apply (clarsimp simp:  lookup_from'_def snap_conv'_def split: if_split_asm option.splits)
    apply (clarsimp)
    apply (subgoal_tac "tagged_pdc_entry_set (non_global_entries_pdc (snd(sat_tlb s) - (\<Union>v\<in>vset. {e \<in> snd(sat_tlb s). v \<in> range_of e \<and> asid_of_pdc e = Some a}))) a v = {}")
     apply (clarsimp simp: lookup_def)
    apply (clarsimp simp: non_global_entries_pdc_def lookup_def tagged_pdc_entry_set_def entry_set_def split: if_split_asm option.splits)
   apply (subgoal_tac "snd(lookup_from' (\<lambda>a'. if a' = a then (fst (snapshot (set_tlb t) a) - vset, \<lambda>v. if v \<in> vset then Fault else snd (snapshot (set_tlb t) a) v) else snapshot (set_tlb t) a') a v) = Incon")
    apply force
   apply (clarsimp simp:  lookup_from'_def snap_conv'_def split: if_split_asm option.splits)
  apply (case_tac "v \<in> vset")
   apply (subgoal_tac "lookup_pdc (non_global_entries_pdc (snd(sat_tlb s) - (\<Union>v\<in>vset. {e \<in> snd(sat_tlb s). v \<in> range_of e \<and> asid_of_pdc e = Some a}))) a v = Miss")
    apply force
   apply (subgoal_tac "tagged_pdc_entry_set (non_global_entries_pdc (snd(sat_tlb s) - (\<Union>v\<in>vset. {e \<in> snd(sat_tlb s). v \<in> range_of e \<and> asid_of_pdc e = Some a}))) a v = {}")
    apply (clarsimp simp: lookup_def)
   apply (clarsimp simp: non_global_entries_pdc_def lookup_def tagged_pdc_entry_set_def entry_set_def split: if_split_asm option.splits)
  apply (subgoal_tac "snd(lookup_from' (\<lambda>a'. if a' = a then (fst (snapshot (set_tlb t) a) - vset, \<lambda>v. if v \<in> vset then Fault else snd (snapshot (set_tlb t) a) v) else snapshot (set_tlb t) a') a v)=
                      snd(lookup_from' (snapshot (set_tlb t)) a v)")
   prefer 2
   apply (clarsimp simp:  lookup_from'_def snap_conv'_def split: if_split_asm option.splits)
  apply clarsimp
  apply (case_tac "snd(lookup_from' (snapshot (set_tlb t)) a v)"; clarsimp?)
  apply (clarsimp simp: non_global_entries_sub_pdc)
  apply (subgoal_tac "lookup_pdc (non_global_entries_pdc (snd(sat_tlb s)) - non_global_entries_pdc (\<Union>v\<in>vset. {e \<in>snd(sat_tlb s). v \<in> range_of e \<and> asid_of_pdc e = Some a})) a v = Miss \<or> 
       lookup_pdc (non_global_entries_pdc (snd(sat_tlb s)) - non_global_entries_pdc (\<Union>v\<in>vset. {e \<in> snd(sat_tlb s). v \<in> range_of e \<and> asid_of_pdc e = Some a})) a v =  Hit x3a ")
   apply (erule disjE)
    apply clarsimp
   apply clarsimp
  by (rule lookup_miss_minus_miss_hit_pdc, simp)



lemma  flush_sat_incon_refine:
  "\<lbrakk> flush f (s::'a sat_tlb_state_scheme) = ((), s') ;  flush f (t::'b set_tlb_state_scheme) = ((), t'); 
         tlb_rel_abs (typ_sat_tlb s) (typ_set_tlb t) \<rbrakk> \<Longrightarrow> 
                  tlb_rel_abs (typ_sat_tlb s') (typ_set_tlb t')"
  by (cases f; clarsimp simp: flush_tlb_sat_incon_refine   flush_varange_sat_incon_refine  flush_sat_tlb_state_ext_def flush_tlb_pdc_asid_def
  flush_with_asid_asid_sat_incon_refine flush_with_asid_asid_varange_sat_incon_refine) 




  


end