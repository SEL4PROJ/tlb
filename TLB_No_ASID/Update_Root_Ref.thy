theory Update_Root_Ref

imports  Read_Write_Ref

begin    



lemma  update_root_non_det_det_refine:
  "\<lbrakk> update_TTBR0 r (s::'a non_det_tlb_state_scheme) = ((), s') ;  update_TTBR0 r (t::'b det_tlb_state_scheme) = ((), t'); 
         tlb_rel_det (typ_non_det_tlb s) (typ_det_tlb t) \<rbrakk> \<Longrightarrow> 
                  tlb_rel_det (typ_non_det_tlb s') (typ_det_tlb t')"
  apply (clarsimp simp: update_TTBR0_non_det_tlb_state_ext_def update_TTBR0_det_tlb_state_ext_def)
  apply (clarsimp simp: tlb_rel_det_def  saturated_def)
  by (cases s, cases t , clarsimp simp: state.defs )



lemma  update_root_det_sat_refine:
  "\<lbrakk> update_TTBR0 r (s::'a det_tlb_state_scheme) = ((), s') ;  update_TTBR0 r (t::'b sat_tlb_state_scheme) = ((), t'); 
         tlb_rel_sat (typ_det_tlb s) (typ_sat_tlb t) \<rbrakk> \<Longrightarrow> 
                  tlb_rel_sat (typ_det_tlb s') (typ_sat_tlb t')"
  apply (clarsimp simp: update_TTBR0_det_tlb_state_ext_def update_TTBR0_sat_tlb_state_ext_def)
  apply (clarsimp simp: tlb_rel_sat_def  saturated_def)
  apply (cases s, cases t , clarsimp simp: state.defs)
  by blast



lemma update_root_sat_incon_refine:
  "\<lbrakk> update_TTBR0 r (s::'a sat_tlb_state_scheme) = ((), s') ;  update_TTBR0 r (t::'b set_tlb_state_scheme) = ((), t'); 
             tlb_rel_abs (typ_sat_tlb s) (typ_set_tlb t) \<rbrakk> \<Longrightarrow> 
                     tlb_rel_abs (typ_sat_tlb s') (typ_set_tlb t')"
  apply (clarsimp simp: update_TTBR0_sat_tlb_state_ext_def update_TTBR0_set_tlb_state_ext_def tlb_rel_abs_def)
  apply (subgoal_tac "  TTBR0 t = TTBR0 s \<and> MEM t = MEM s")
   prefer 2
   apply (clarsimp simp:  typ_sat_tlb_def state.defs)
  apply (rule conjI)
   apply (clarsimp simp: typ_sat_tlb_def state.defs)
  apply (clarsimp simp: incon_addrs_def)
  apply (rule conjI)
   apply (clarsimp simp: inconsistent_vaddrs_def incoherrent_vaddrs_def)
   apply (drule union_incon_cases)
   apply (erule disjE, clarsimp simp: lookup_range_pt_walk_not_incon)
   apply (erule disjE, clarsimp)
    apply (clarsimp simp: incon_comp_def ptable_comp_def Let_def)
    apply (erule disjE)
     apply blast
    apply (erule disjE)
     apply (subgoal_tac "the (pt_walk () (MEM s) r xc) = the (pt_walk () (MEM s) (TTBR0 s) x)")
      apply (case_tac "\<not>is_fault (pt_walk ()   (MEM s) (TTBR0 s) x)")
       apply clarsimp
  using saturatd_lookup_hit_no_fault apply fastforce
     apply (subgoal_tac "the (pt_walk ()   (MEM s) r xc) = the (pt_walk ()   (MEM s) r x)")
      apply (force simp: is_fault_def) 
     apply (frule lookup_range_fault_pt_walk)
     apply (drule_tac x = x in bspec; clarsimp simp: lookup_hit_entry_range)
    apply (subgoal_tac "is_fault (pt_walk () (MEM s) (TTBR0 s) x)") 
     apply blast
    apply (erule disjE)
     apply (force simp: is_fault_def) 
    apply clarsimp
    apply (subgoal_tac "the (pt_walk () (MEM s) r xc) = the (pt_walk () (MEM s) r x)")
     prefer 2
  using lookup_hit_entry_range_asid_tags va_entry_set_pt_palk_same apply blast
    apply clarsimp
    apply (subgoal_tac "\<not> is_fault (pt_walk () (MEM s) (TTBR0 s) x)") prefer 2 apply force
    apply (subgoal_tac " xa = the (pt_walk () (MEM s) r x)")
     apply clarsimp
    apply (subgoal_tac "lookup' (sat_tlb s \<union> the ` {e \<in> range (pt_walk () (MEM s) (TTBR0 s)). \<not> is_fault e}) x = Hit xa")
     prefer 2
     apply (clarsimp simp: saturated_def) apply (simp add: sup_absorb1)
    apply (drule lookup_hit_union_cases')
    apply (erule disjE)
     apply clarsimp 
  using saturatd_lookup_hit_no_fault apply fastforce
    apply (erule disjE)
     apply clarsimp 
    apply clarsimp 
  using saturatd_lookup_hit_no_fault apply fastforce
  using lookup_range_pt_walk_not_incon apply blast
  apply (rule conjI)
   apply clarsimp
   apply (clarsimp simp: incoherrent_vaddrs_def  inconsistent_vaddrs_def)
   apply (simp only: incon_comp_def ptable_comp_def)
   apply clarsimp
   apply (drule lookup_hit_union_cases')
   apply (clarsimp simp: lookup_miss_is_fault_intro  subset_eq)
  by (clarsimp simp: saturated_def)




lemma  flush_tlb_non_det_det_refine:
  "\<lbrakk> flush FlushTLB (s::'a non_det_tlb_state_scheme) = ((), s') ;  flush FlushTLB (t::'b det_tlb_state_scheme) = ((), t'); 
         tlb_rel_det (typ_non_det_tlb s) (typ_det_tlb t) \<rbrakk> \<Longrightarrow> 
                  tlb_rel_det (typ_non_det_tlb s') (typ_det_tlb t')"
  apply (clarsimp simp: flush_non_det_tlb_state_ext_def flush_det_tlb_state_ext_def)
  apply (clarsimp simp: tlb_rel_det_def)
  by (cases s, cases t , clarsimp simp: state.defs)


lemma  flush_varange_non_det_det_refine:
  "\<lbrakk>flush (Flushvarange vset) (s::'a non_det_tlb_state_scheme) = ((), s') ;  flush (Flushvarange vset) (t::'b det_tlb_state_scheme) = ((), t'); 
         tlb_rel_det (typ_non_det_tlb s) (typ_det_tlb t) \<rbrakk> \<Longrightarrow> 
                  tlb_rel_det (typ_non_det_tlb s') (typ_det_tlb t')"
  apply (clarsimp simp: flush_non_det_tlb_state_ext_def flush_det_tlb_state_ext_def flush_tlb_vset_def)
  apply (clarsimp simp: tlb_rel_det_def)
  apply (cases s, cases t , clarsimp simp: state.defs) 
  by blast



lemma  flush_non_det_det_refine:
  "\<lbrakk> flush f (s::'a non_det_tlb_state_scheme) = ((), s') ;  flush f (t::'b det_tlb_state_scheme) = ((), t'); 
         tlb_rel_det (typ_non_det_tlb s) (typ_det_tlb t) \<rbrakk> \<Longrightarrow> 
                  tlb_rel_det (typ_non_det_tlb s') (typ_det_tlb t')"
  by (cases f; clarsimp simp: flush_tlb_non_det_det_refine flush_varange_non_det_det_refine ) 


lemma  flush_tlb_non_det_sat_refine:
  "\<lbrakk> flush FlushTLB (s::'a det_tlb_state_scheme) = ((), s') ;  flush FlushTLB (t::'b sat_tlb_state_scheme) = ((), t'); 
         tlb_rel_sat (typ_det_tlb s) (typ_sat_tlb t) \<rbrakk> \<Longrightarrow> 
                  tlb_rel_sat (typ_det_tlb s') (typ_sat_tlb t')"
  apply (clarsimp simp: flush_det_tlb_state_ext_def flush_sat_tlb_state_ext_def)
  apply (clarsimp simp: tlb_rel_sat_def saturated_def)
  apply (cases s, cases t , clarsimp simp: state.defs)
  done

lemma  flush_varange_non_det_sat_refine:
  "\<lbrakk> flush (Flushvarange vset) (s::'a det_tlb_state_scheme) = ((), s') ;  flush (Flushvarange vset) (t::'b sat_tlb_state_scheme) = ((), t'); 
         tlb_rel_sat (typ_det_tlb s) (typ_sat_tlb t) \<rbrakk> \<Longrightarrow> 
                  tlb_rel_sat (typ_det_tlb s') (typ_sat_tlb t')"
  apply (clarsimp simp: flush_det_tlb_state_ext_def flush_sat_tlb_state_ext_def flush_tlb_vset_def)
  apply (clarsimp simp: tlb_rel_sat_def  saturated_def)
  apply (cases s, cases t , clarsimp simp: state.defs )
  by blast

lemma  flush_det_sat_refine:
  "\<lbrakk> flush f (s::'a det_tlb_state_scheme) = ((), s') ;  flush f (t::'b sat_tlb_state_scheme) = ((), t'); 
         tlb_rel_sat (typ_det_tlb s) (typ_sat_tlb t) \<rbrakk> \<Longrightarrow> 
                  tlb_rel_sat (typ_det_tlb s') (typ_sat_tlb t')"
  by (cases f; clarsimp simp: flush_tlb_non_det_sat_refine   flush_varange_non_det_sat_refine ) 

 
lemma flush_tlb_sat_incon_refine:
  "\<lbrakk>flush FlushTLB (s::'a sat_tlb_state_scheme) = ((), s') ;  flush FlushTLB (t::'b set_tlb_state_scheme) = ((), t'); 
             tlb_rel_abs (typ_sat_tlb s) (typ_set_tlb t) \<rbrakk> \<Longrightarrow> 
                     tlb_rel_abs (typ_sat_tlb s') (typ_set_tlb t')"
  apply (clarsimp simp: flush_sat_tlb_state_ext_def  flush_set_tlb_state_ext_def tlb_rel_abs_def)
  apply (rule conjI)
   apply (cases s, cases t, clarsimp simp: state.defs)
  apply (rule conjI)
   apply (clarsimp simp: incon_addrs_def)
   apply (rule conjI)
    apply (clarsimp simp: inconsistent_vaddrs_def lookup_range_pt_walk_not_incon) 
   apply (clarsimp simp: incoherrent_vaddrs_def)
    apply (clarsimp simp: lookup_miss_is_fault_intro)                           
  by (clarsimp simp: saturated_def)


lemma flush_varange_sat_incon_refine:
  "\<lbrakk>flush (Flushvarange vset) (s::'a sat_tlb_state_scheme) = ((), s') ;  flush (Flushvarange vset) (t::'b set_tlb_state_scheme) = ((), t'); 
             tlb_rel_abs (typ_sat_tlb s) (typ_set_tlb t) \<rbrakk> \<Longrightarrow> 
                     tlb_rel_abs (typ_sat_tlb s') (typ_set_tlb t')"
  apply (clarsimp simp: flush_sat_tlb_state_ext_def  flush_set_tlb_state_ext_def tlb_rel_abs_def flush_tlb_vset_def)
  apply (rule conjI)
   apply (cases s, cases t, clarsimp simp: state.defs)
  apply (subgoal_tac "(sat_tlb s) = (sat_tlb s) \<union> 
                              the ` {e \<in> range (pt_walk () (MEM s) (TTBR0 s)). \<not> is_fault e} ")
   prefer 2
   apply (drule sat_state_tlb, clarsimp simp: state.defs)
  apply (rule conjI)
   apply (clarsimp simp: incon_addrs_def)
   apply (rule conjI)
    apply (clarsimp simp: inconsistent_vaddrs_def)
     apply (drule union_incon_cases)
     apply (erule disjE)
      apply (clarsimp simp: lookup_range_pt_walk_not_incon) 
     apply (erule disjE)
      apply clarsimp
      apply (rule conjI)
       prefer 2 using lookup_hit_entry_range apply force
      apply (drule lookup_hit_incon_minus, erule disjE)
       prefer 2
       apply blast
      apply (subgoal_tac "the (pt_walk ()   (MEM s) (TTBR0 s) xc) = the (pt_walk ()   (MEM s) (TTBR0 s) x)")
       prefer 2
       apply (frule lookup_range_fault_pt_walk)
       apply (drule_tac x = x and A = "range_of (the (pt_walk ()   (MEM s) (TTBR0 s) xc))" in bspec; simp add : lookup_hit_entry_range)         
      apply (clarsimp simp: incoherrent_vaddrs_def)  
     apply (frule_tac b = x and x = xa in saturatd_lookup_hit_no_fault, simp) prefer 2 apply force
  apply (smt lookup_hit_entry_range_asid_tags va_entry_set_pt_palk_same')
     apply (erule disjE)
      apply clarsimp
      apply (simp add: lookup_range_pt_walk_not_incon)
     apply (erule disjE)
      prefer 2
      apply (erule disjE, clarsimp) 
  using lookup_range_pt_walk_not_incon apply force
      apply (rule conjI) prefer 2
  subgoal
  proof -
    fix x :: vaddr
    assume "lookup' ((sat_tlb s) - (\<Union>v\<in>vset. {e \<in> (sat_tlb s). v \<in> range_of e}))   x = Incon \<and> lookup' (the ` {e \<in> range (pt_walk ()   (MEM s) (TTBR0 s)). \<not> is_fault e})   x = Miss"
    then have "\<exists>T. lookup' (T - (\<Union>a\<in>vset. {t::unit tlb_entry \<in> T. a \<in> range_of t})) x \<noteq> Miss"
      by (metis lookup_type.simps(3))
    then show "x \<notin> vset"
      using lookup_not_miss_varange by blast
  qed  
  using lookup_incon_minus mem_Collect_eq apply blast
    apply clarsimp apply (rule conjI) prefer 2
  subgoal
  proof -
    fix x :: vaddr and xb :: vaddr
    assume "lookup' ((sat_tlb s) - (\<Union>v\<in>vset. {e \<in> (sat_tlb s). v \<in> range_of e}))   x = Incon"
    then have "\<exists>T . lookup' (T - (\<Union>a\<in>vset. {t::unit tlb_entry \<in> T. a \<in> range_of t}))  x \<noteq> Miss"
      by (metis (full_types) lookup_type.simps(3))
    then show "x \<notin> vset"
      using lookup_not_miss_varange by blast
  qed
  using lookup_incon_minus apply force
   apply (clarsimp simp: incoherrent_vaddrs_def)
    apply (subgoal_tac "lookup' ((sat_tlb s) - (\<Union>v\<in>vset. {e \<in> (sat_tlb s). v \<in> range_of e}))   x = Hit xa")
     prefer 2
     apply (simp add: lookup_miss_is_fault_intro lookup_miss_union_equal)
    apply (drule lookup_hit_incon_minus, erule disjE)
     prefer 2
     apply (clarsimp simp: inconsistent_vaddrs_def)
     apply (rule conjI) 
     apply force
  subgoal
  proof -
    fix x :: vaddr and xa :: "unit tlb_entry"
    assume a1: "is_fault (pt_walk ()   (MEM s) (TTBR0 s) x)"
    assume "lookup' ((sat_tlb s) - (\<Union>v\<in>vset. {e \<in> (sat_tlb s). v \<in> range_of e}) \<union> the ` {e \<in> range (pt_walk () (MEM s) (TTBR0 s)). \<not> is_fault e})   x = Hit xa"
    then have "lookup' ((sat_tlb s) - (\<Union>a\<in>vset. {t \<in> (sat_tlb s). a \<in> range_of t}))   x = Hit xa"
      using a1 by (simp add: lookup_miss_is_fault_intro lookup_miss_union_equal)
    then have "\<exists> T. lookup' (T - (\<Union>a\<in>vset. {t::unit tlb_entry \<in> T. a \<in> range_of t}))  x \<noteq> Miss"
      by (metis lookup_type.simps(5))
    then show "x \<notin> vset"
      using lookup_not_miss_varange by blast
  qed
    apply (rule conjI) apply blast
  subgoal
  proof -
    fix x :: vaddr and xa :: "unit tlb_entry"
    assume a1: "is_fault (pt_walk ()   (MEM s) (TTBR0 s) x)"
    assume "lookup' ((sat_tlb s) - (\<Union>v\<in>vset. {e \<in> (sat_tlb s). v \<in> range_of e}) \<union> the ` {e \<in> range (pt_walk () (MEM s) (TTBR0 s)). \<not> is_fault e})   x = Hit xa"
    then have "lookup' ((sat_tlb s) - (\<Union>a\<in>vset. {t::unit tlb_entry \<in> (sat_tlb s). a \<in> range_of t}))   x = Hit xa"
      using a1 by (simp add: lookup_miss_is_fault_intro lookup_miss_union_equal)
    then show "x \<notin> vset"
      by (metis (mono_tags) lookup_not_miss_varange lookup_type.simps(5))
  qed
  by (clarsimp simp: saturated_def)
 
lemma  flush_sat_incon_refine:
  "\<lbrakk> flush f (s::'a sat_tlb_state_scheme) = ((), s') ;  flush f (t::'b set_tlb_state_scheme) = ((), t'); 
         tlb_rel_abs (typ_sat_tlb s) (typ_set_tlb t) \<rbrakk> \<Longrightarrow> 
                  tlb_rel_abs (typ_sat_tlb s') (typ_set_tlb t')"
  by (cases f; clarsimp simp:   flush_tlb_sat_incon_refine   flush_varange_sat_incon_refine ) 



end