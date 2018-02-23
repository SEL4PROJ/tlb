theory  ARMv7_Update_TTBR0_Ref

imports 
  TLB_Op_Instants

begin               


lemma update_ttbr0_non_det_det_refine:
  "\<lbrakk> update_TTBR0 r (s::tlb_state) = ((), s') ;  update_TTBR0 r (t::tlb_det_state) = ((), t'); 
         tlb_rel (typ_tlb s) (typ_det_tlb t) \<rbrakk> \<Longrightarrow>  tlb_rel (typ_tlb s') (typ_det_tlb t') "
  apply (clarsimp simp: update_TTBR0_tlb_state_ext_def update_TTBR0_tlb_det_state_ext_def tlb_rel_def) 
  apply (rule conjI)
   apply (cases s, cases t , clarsimp simp: state.defs tlb_rel_def) 
  by blast

lemma  update_ttbr0_det_sat_refine:
  "\<lbrakk> update_TTBR0 r (s::tlb_det_state) = ((), s') ;  update_TTBR0 r (t::tlb_sat_state) = ((), t'); 
         tlb_rel_sat (typ_det_tlb s) (typ_sat_tlb t) \<rbrakk> \<Longrightarrow> 
                  tlb_rel_sat (typ_det_tlb s') (typ_sat_tlb t')"
  apply (clarsimp simp: update_TTBR0_tlb_det_state_ext_def update_TTBR0_tlb_sat_state_ext_def)
  apply (clarsimp simp: tlb_rel_sat_def saturated_def )
  apply (cases s, cases t , clarsimp simp: state.defs , force)
done


lemma lookup_range_pt_walk_asid_miss:
  "a \<noteq> a1 \<Longrightarrow> lookup (the ` {e \<in> range (pt_walk a mem ttbr0). \<not> is_fault e}) a1 va = Miss"
  apply (clarsimp simp: lookup_def entry_set_def entry_range_asid_tags_def)
  by force

lemma lookup_range_pt_walk_not_incon':
  "lookup (the ` {e \<in> range (pt_walk asid mem ttbr0). \<not> is_fault e}) asid1 va \<noteq> Incon"
  apply (case_tac "asid = asid1")
   apply (clarsimp simp: lookup_range_pt_walk_not_incon)
  by (clarsimp simp: lookup_range_pt_walk_asid_miss)



lemma lookup_miss_union:
  " lookup (t1 \<union> t2) a va = Miss  \<Longrightarrow>
      (lookup t1 a va = Miss \<and> lookup t2 a va = Miss) "
  apply (clarsimp simp: lookup_def entry_set_def split: if_split_asm)
  by auto
       
lemma sat_miss_fault:
  "\<lbrakk>saturated (typ_sat_tlb s);
      lookup (tlb_sat_set s) (ASID s) b = Miss\<rbrakk> \<Longrightarrow> is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) b)"
  apply (subgoal_tac " lookup (tlb_sat_set s  \<union> the ` {e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e}) (ASID s) (  b) = Miss")
   apply (thin_tac " lookup (tlb_sat_set s) (ASID s) (  b) = Miss")
   apply (drule lookup_miss_union)
   apply clarsimp
   apply (drule lookup_miss_is_fault)
   apply clarsimp
  using sat_state_tlb' by force


lemma lookup_miss_snapshot:
  "lookup t' a v = Miss \<Longrightarrow> 
   snapshot_of_tlb (t \<union> t') a v = snapshot_of_tlb t a v"
  apply (drule_tac t = t in lookup_miss_union_equal)
  by (clarsimp simp: snapshot_of_tlb_def)
  

lemma update_ttbr0_sat_abs_refine':
  "\<lbrakk> update_TTBR0 r (s::tlb_sat_state) = ((), s') ;  update_TTBR0 r (t::tlb_incon_state') = ((), t'); 
             tlb_rel_abs' (typ_sat_tlb s) (typ_incon' t) \<rbrakk> \<Longrightarrow> 
                     tlb_rel_abs' (typ_sat_tlb s') (typ_incon' t')"
  apply (clarsimp simp: update_TTBR0_tlb_sat_state_ext_def update_TTBR0_tlb_incon_state'_ext_def tlb_rel_abs'_def)
  apply (subgoal_tac "ASID t = ASID s \<and> TTBR0 t = TTBR0 s \<and> MEM t = MEM s")
   prefer 2
   apply (clarsimp simp: tlb_rel'_absD typ_sat_tlb_def state.defs)
  apply (rule conjI)
   apply (clarsimp simp: typ_sat_tlb_def "state.defs")
  apply (clarsimp simp: asid_va_incon_tlb_mem_def)
  apply (rule conjI)
   prefer 2
   apply (rule conjI)
    apply (clarsimp simp: asid_va_hit_incon_inter_def asid_va_hit_incon'_def asid_va_hit_incon''_def ptable_comp_def)
    apply (rule conjI)
     apply clarsimp
     apply (subgoal_tac "b \<notin> {va. \<not> is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) va) \<and>
                    \<not> is_fault (pt_walk (ASID s) (MEM s) r va) \<and>
                    pt_walk (ASID s) (MEM s) (TTBR0 s) va \<noteq> pt_walk (ASID s) (MEM s) r va \<or>
                    \<not> is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) va) \<and> is_fault (pt_walk (ASID s) (MEM s) r va)}")
      prefer 2
      apply blast
     apply clarsimp
     apply (erule disjE)
      apply (drule lookup_hit_union_cases')
      apply (erule disjE, clarsimp simp: lookup_miss_is_fault)
      apply (erule disjE, clarsimp)  
       apply (frule lookup_range_fault_pt_walk)
       apply (drule_tac x = b in bspec; clarsimp simp: lookup_hit_entry_range)
      apply (clarsimp, frule lookup_range_fault_pt_walk)
      apply (drule_tac x = b in bspec; clarsimp simp: lookup_hit_entry_range)
     apply (drule lookup_hit_union_cases')
     apply (erule disjE, clarsimp simp: lookup_miss_is_fault)
     apply (erule disjE, clarsimp)
      apply (frule lookup_range_fault_pt_walk)
      apply (drule_tac x = b in bspec; clarsimp simp: lookup_hit_entry_range)
     apply (clarsimp, frule lookup_range_fault_pt_walk)
     apply (drule_tac x = b in bspec; clarsimp simp: lookup_hit_entry_range)
    apply clarsimp
    apply (subgoal_tac "b \<notin> {va. \<not> is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) va) \<and>
                    \<not> is_fault (pt_walk (ASID s) (MEM s) r va) \<and>
                    pt_walk (ASID s) (MEM s) (TTBR0 s) va \<noteq> pt_walk (ASID s) (MEM s) r va \<or>
                    \<not> is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) va) \<and> is_fault (pt_walk (ASID s) (MEM s) r va)}")
     prefer 2
     apply blast
    apply clarsimp
    apply (drule lookup_hit_union_cases')
    apply (erule disjE, blast)
    apply (erule disjE, clarsimp simp: lookup_miss_is_fault_intro)
    apply (clarsimp simp: lookup_miss_is_fault_intro)
   prefer 2
   apply (clarsimp simp:  asid_va_incon_def ptable_comp_def  asid_va_hit_incon_def
      asid_va_hit_incon'_def asid_va_hit_incon''_def)
   apply (case_tac "a = ASID s" , clarsimp)
    prefer 2
    apply (drule union_incon_cases1)
    apply (erule disjE , force)
    apply (clarsimp simp: lookup_range_pt_walk_not_incon')
    apply (erule disjE)
     apply (clarsimp simp: asid_unequal_miss'')
    apply (erule disjE)
     apply (clarsimp simp: asid_unequal_miss'')
    apply blast
   apply (subgoal_tac "b \<notin>{va. \<not> is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) va) \<and>
                    \<not> is_fault (pt_walk (ASID s) (MEM s) r va) \<and>
                    pt_walk (ASID s) (MEM s) (TTBR0 s) va \<noteq> pt_walk (ASID s) (MEM s) r va \<or>
                    \<not> is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) va) \<and> is_fault (pt_walk (ASID s) (MEM s) r va)}")
    prefer 2
    apply blast
   apply clarsimp
   apply (erule disjE, clarsimp)
    apply (drule union_incon_cases1 , clarsimp)
    apply (erule disjE, force)
    apply (erule disjE, clarsimp simp: asid_va_hit_incon_inter_def asid_va_hit_incon'_def asid_va_hit_incon''_def, force) 
    apply (erule disjE, clarsimp simp: lookup_range_pt_walk_not_incon)
    apply (erule disjE, blast)
    apply (erule disjE, clarsimp simp: lookup_range_pt_walk_not_incon, blast)
   apply (erule disjE, clarsimp)
    apply (drule union_incon_cases1 , clarsimp)
    apply (erule disjE, force)
    apply (erule disjE, clarsimp simp: asid_va_hit_incon_inter_def asid_va_hit_incon'_def asid_va_hit_incon''_def, force) 
    apply (erule disjE, clarsimp simp: lookup_range_pt_walk_not_incon)
    apply (erule disjE, blast)
    apply (erule disjE, clarsimp simp: lookup_range_pt_walk_not_incon, blast)
   apply (erule disjE, clarsimp)
    apply (drule union_incon_cases1 , clarsimp)
    apply (erule disjE, force)
    apply (erule disjE, clarsimp simp: asid_va_hit_incon_inter_def asid_va_hit_incon'_def asid_va_hit_incon''_def, force) 
    apply (erule disjE, clarsimp simp: lookup_range_pt_walk_not_incon)
    apply (erule disjE, blast)
    apply (erule disjE, clarsimp simp: lookup_range_pt_walk_not_incon, blast)
   apply (drule union_incon_cases1 , clarsimp)
   apply (erule disjE, force)
   apply (erule disjE, clarsimp)
    apply (subgoal_tac "the (pt_walk (ASID s) (MEM s) r xb) = the(pt_walk (ASID s) (MEM s) r b)", simp)
     apply (clarsimp simp: asid_va_hit_incon_inter_def asid_va_hit_incon'_def asid_va_hit_incon''_def) 
     apply force
    apply (frule lookup_range_fault_pt_walk)
    apply (drule_tac x = b in bspec, simp add: lookup_hit_entry_range, simp)
   apply (erule disjE, clarsimp simp: lookup_range_pt_walk_not_incon)
   apply (erule disjE, blast)
   apply (erule disjE, clarsimp simp: lookup_range_pt_walk_not_incon, blast)
  apply (rule conjI)
   apply (clarsimp simp:  saturated_def)
  apply (rule conjI)
   apply (clarsimp)
   apply (subgoal_tac "snapshot_of_tlb (tlb_sat_set s \<union> the `{e \<in> range (pt_walk (ASID s) (MEM s) r). \<not> is_fault e}) a v =
                             snapshot_of_tlb  (tlb_sat_set s) a v")
    apply clarsimp
   apply (rule lookup_miss_snapshot)
   apply (clarsimp simp: asid_unequal_miss'')
  apply clarsimp
  by blast




lemma update_ttbr0_sat_abs_refine'2:
  "\<lbrakk> update_TTBR0 r (s::tlb_incon_state') = ((), s') ;  update_TTBR0 r (t::tlb_incon_state) = ((), t'); 
             refine_rel (typ_incon' s) (typ_incon'2 t) \<rbrakk> \<Longrightarrow> 
                     refine_rel (typ_incon' s') (typ_incon'2 t')"
  apply (clarsimp simp: update_TTBR0_tlb_incon_state_ext_def update_TTBR0_tlb_incon_state'_ext_def refine_rel_def)
  apply (subgoal_tac "ASID s = ASID t \<and> TTBR0 s = TTBR0 t \<and> MEM s = MEM t")
   prefer 2
   apply (clarsimp simp: typ_incon'2_def typ_incon'_def state.defs) 
  apply (rule conjI)
   apply (clarsimp simp: typ_sat_tlb_def "state.defs")
  apply (rule conjI)
   apply clarsimp
   apply (drule_tac x = a in spec)
   apply (drule_tac x = a in spec)
   apply clarsimp
   apply (drule_tac x = v in spec)
   apply (drule_tac x = v in spec)
   apply rule  apply simp  
   apply (erule disjE)
    apply simp
   apply (subgoal_tac "(a, v) \<notin> ptable_comp (ASID t) (MEM t) (MEM t) (TTBR0 t) r", simp)
   apply (clarsimp simp: ptable_comp_def)
  apply (subgoal_tac  "{v. (ASID s, v) \<in> incon_set (tlb_incon_set' s) } \<subseteq> iset (tlb_incon_set t)")
   apply (subgoal_tac "{v. (ASID s, v) \<in> ptable_comp (ASID s) (MEM s) (MEM s) (TTBR0 s) r} \<subseteq> 
            ptable_comp' (ASID t) (MEM t) (MEM t) (TTBR0 t) r")
    apply blast
   prefer 2
   apply clarsimp
  by (clarsimp simp: ptable_comp_def ptable_comp'_def)

 
(* new refinement *)

lemma update_ttbr0_sat_abs2_refine':
  "\<lbrakk> update_TTBR0 r (s::tlb_sat_state) = ((), s') ;  update_TTBR0 r (t::tlb_incon_state) = ((), t'); 
             invar_rel (typ_sat_tlb s) (typ_incon'2 t) \<rbrakk> \<Longrightarrow> 
                     invar_rel (typ_sat_tlb s') (typ_incon'2 t')"
  apply (clarsimp simp: update_TTBR0_tlb_sat_state_ext_def update_TTBR0_tlb_incon_state_ext_def invar_rel_def)
  apply (subgoal_tac "ASID t = ASID s \<and> TTBR0 t = TTBR0 s \<and> MEM t = MEM s")
   prefer 2
   apply (clarsimp simp:  typ_sat_tlb_def state.defs)
  apply (rule conjI)
   apply (clarsimp simp: typ_sat_tlb_def "state.defs")
  apply (clarsimp simp: asid_va_incon_tlb_mem_n_def)
  apply (rule conjI)
   prefer 2
   apply (rule conjI)
    apply (clarsimp)
    apply (clarsimp simp: asid_va_hit_incon_n_def  ptable_comp'_def)
    apply (erule disjE)+
       apply (drule lookup_hit_union_cases')
       apply (erule disjE, clarsimp simp: lookup_miss_is_fault)
       apply (erule disjE, clarsimp simp: lookup_range_pt_walk_hit)
       apply (clarsimp simp: lookup_range_pt_walk_hit) 
      apply (drule lookup_hit_union_cases')
      apply (erule disjE, blast)
      apply (erule disjE, clarsimp simp: lookup_miss_is_fault_intro) 
      apply (clarsimp simp: lookup_miss_is_fault_intro)
     apply (erule disjE)+    
      apply (drule lookup_hit_union_cases')
      apply (erule disjE, blast)
      apply (erule disjE, clarsimp simp: lookup_range_pt_walk_hit) 
      apply (clarsimp simp: lookup_range_pt_walk_hit)
     apply (drule lookup_hit_union_cases')
     apply (erule disjE, blast)
     apply (erule disjE, clarsimp simp: lookup_range_pt_walk_hit) 
     apply (clarsimp simp: lookup_range_pt_walk_hit)
    apply (erule disjE)+  
       apply (drule lookup_hit_union_cases')
       apply (erule disjE, blast)
       apply (erule disjE, clarsimp simp: lookup_range_pt_walk_hit) 
       apply (clarsimp simp: lookup_range_pt_walk_hit)
      apply (drule lookup_hit_union_cases')
      apply (erule disjE, blast)
      apply (erule disjE, clarsimp simp: lookup_range_pt_walk_hit) 
      apply (clarsimp simp: lookup_range_pt_walk_hit)
     apply (drule lookup_hit_union_cases')
     apply (erule disjE, blast)
     apply (erule disjE, clarsimp simp: lookup_miss_is_fault_intro) 
     apply (clarsimp simp: lookup_miss_is_fault_intro)
    apply (erule disjE)+  
      apply (drule lookup_hit_union_cases')
      apply (erule disjE, blast)
      apply (erule disjE, clarsimp simp: lookup_miss_is_fault_intro) 
      apply (clarsimp simp: lookup_miss_is_fault_intro)
     apply (drule lookup_hit_union_cases')
     apply (erule disjE, force)
     apply (erule disjE, clarsimp simp: lookup_range_pt_walk_hit) 
     apply (clarsimp simp: lookup_range_pt_walk_hit)
    apply (erule disjE)+ 
     apply (drule lookup_hit_union_cases')
     apply (erule disjE, force)
     apply (erule disjE, clarsimp simp: lookup_range_pt_walk_hit) 
     apply (clarsimp simp: lookup_range_pt_walk_hit)
    apply (drule lookup_hit_union_cases')
    apply (erule disjE, force)
    apply (erule disjE, clarsimp simp: lookup_range_pt_walk_hit) 
    apply (clarsimp simp: lookup_range_pt_walk_hit)
   prefer 2
   apply (clarsimp)
   apply (clarsimp simp:  asid_va_incon_n_def ptable_comp'_def  asid_va_hit_incon_n_def)
   apply (erule disjE)+
     apply (drule union_incon_cases1)
     apply (erule disjE, blast)
     apply (erule disjE, blast)
     apply (erule disjE, blast)
     apply (erule disjE, blast)
     apply (erule disjE, clarsimp simp: lookup_range_pt_walk_not_incon)
     apply blast
    apply (drule union_incon_cases1)
    apply (erule disjE, blast)
    apply (erule disjE, blast)
    apply (erule disjE, blast)
    apply (erule disjE, blast)
    apply (erule disjE, clarsimp simp: lookup_range_pt_walk_not_incon)
    apply blast
   apply (erule disjE)+
     apply (drule union_incon_cases1)
     apply (erule disjE, blast)
     apply (erule disjE, blast)
     apply (erule disjE, blast)
     apply (erule disjE, blast)
     apply (erule disjE, clarsimp simp: lookup_range_pt_walk_not_incon)
     apply blast
    apply (drule union_incon_cases1)
    apply (erule disjE, blast)
    apply (erule disjE, blast)
    apply (erule disjE, blast)
    apply (erule disjE, blast)
    apply (erule disjE, clarsimp simp: lookup_range_pt_walk_not_incon)
    apply blast
   apply (erule disjE)+
    apply (drule union_incon_cases1)
    apply (erule disjE, blast)
    apply (erule disjE, blast)
    apply (erule disjE, blast)
    apply (erule disjE, blast)
    apply (erule disjE, clarsimp simp: lookup_range_pt_walk_not_incon)
    apply blast
   apply (drule union_incon_cases1)
   apply (erule disjE, blast)
   apply (erule disjE, clarsimp simp:) 
  using Un_subset_iff lookup_range_pt_walk_hit sat_state_tlb' subsetI tlb_mono tlb_sat_more typ_sat_prim_parameter apply force[1]   
   apply (erule disjE, clarsimp simp: lookup_range_pt_walk_not_incon')
   apply (erule disjE, blast)  
   apply (erule disjE, clarsimp simp: lookup_range_pt_walk_not_incon') 
   apply blast
  apply (rule conjI)
   apply (clarsimp simp:  saturated_def)
  apply (clarsimp)
  apply (subgoal_tac "snapshot_of_tlb (tlb_sat_set s \<union> the `{e \<in> range (pt_walk (ASID s) (MEM s) r). \<not> is_fault e}) a v =
                              snapshot_of_tlb  (tlb_sat_set s) a v")
   apply clarsimp
  apply (rule lookup_miss_snapshot)
  by (clarsimp simp: asid_unequal_miss'')




end