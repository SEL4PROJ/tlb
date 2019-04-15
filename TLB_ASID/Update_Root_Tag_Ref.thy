theory Update_Root_Tag_Ref

imports  Read_Write_Tag_Ref

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


lemma update_root_sat_incon_refine':
  "\<lbrakk> update_TTBR0 r (s::'a sat_tlb_state_scheme) = ((), s') ;  update_TTBR0 r (t::'b set_tlb_state_scheme) = ((), t'); 
             tlb_rel_abs (typ_sat_tlb s) (typ_set_tlb t) \<rbrakk> \<Longrightarrow> 
                     tlb_rel_abs (typ_sat_tlb s') (typ_set_tlb t')"
  apply (clarsimp simp: update_TTBR0_sat_tlb_state_ext_def update_TTBR0_set_tlb_state_ext_def tlb_rel_abs_def)
  apply (subgoal_tac "sat_asid s = set_asid t \<and>  TTBR0 t = TTBR0 s \<and> MEM t = MEM s")
   prefer 2
   apply (clarsimp simp:  typ_sat_tlb_def state.defs)
  apply (rule conjI)
   apply (clarsimp simp: typ_sat_tlb_def state.defs)
  apply (rule conjI)
   apply (clarsimp simp: saturated_def)
  apply (rule conjI)
   apply (clarsimp simp: incon_addrs_def)
   apply (rule conjI)
    apply (clarsimp simp: inconsistent_vaddrs_def incoherrent_vaddrs_def)
    apply (drule union_asid_tlb_incon_cases)
    apply (erule disjE, clarsimp simp: asid_tlb_lookup_range_pt_walk_not_incon)
    apply (erule disjE, clarsimp)
     apply (clarsimp simp: incon_comp_def ptable_comp_def Let_def)
     apply (erule disjE) 
      apply auto[1]
     apply (erule disjE)
      apply (subgoal_tac "the (pt_walk (sat_asid s) (MEM s) r xc) = the (pt_walk (sat_asid s) (MEM s) (TTBR0 s) x)")
       apply (case_tac "\<not>is_fault (pt_walk (sat_asid s) (MEM s) (TTBR0 s) x)")
        apply clarsimp
       using saturatd_lookup_hit_no_fault apply fastforce
      apply (subgoal_tac "the (pt_walk (sat_asid s)  (MEM s) r xc) = the (pt_walk (sat_asid s)  (MEM s) r x)")
       apply (force simp: is_fault_def) 
      apply (frule asid_tlb_lookup_range_fault_pt_walk)
      apply (drule_tac x = x in bspec; clarsimp simp: lookup_asid_tlb_hit_entry_range)
     apply (subgoal_tac "is_fault (pt_walk (set_asid t)(MEM s) (TTBR0 s) x)") 
       apply simp
     apply (erule disjE)
      apply (force simp: is_fault_def) 
     apply clarsimp
     apply (subgoal_tac "the (pt_walk (sat_asid s) (MEM s) r xc) = the (pt_walk (sat_asid s) (MEM s) r x)")
      prefer 2
  subgoal
  proof -
    fix x :: vaddr and xa :: "8 word option tlb_entry" and xc :: vaddr
    assume a1: "sat_asid s = set_asid t"
    assume a2: "MEM t = MEM s"
    assume a3: "\<not> is_fault (pt_walk (set_asid t) (MEM s) r xc)"
    assume "lookup'' (the ` {e \<in> range (pt_walk (set_asid t) (MEM s) r). \<not> is_fault e}) (set_asid t) x = Hit (the (pt_walk (set_asid t) (MEM s) r xc))"
    then have "x \<in> range_of (the (pt_walk (set_asid t) (MEM t) r xc))"
      using a2 lookup_asid_tlb_hit_entry_range by presburger
    then show "the (pt_walk (sat_asid s) (MEM s) r xc) = the (pt_walk (sat_asid s) (MEM s) r x)"
      using a3 a2 a1 by (metis (no_types) va_entry_set_pt_palk_same)
  qed
     apply clarsimp
     apply (metis (no_types, hide_lams) saturatd_lookup_hit_no_fault)
    apply (erule disjE)
  using asid_tlb_lookup_range_pt_walk_not_incon apply force
    apply (erule disjE, clarsimp)
     apply blast
    apply (erule disjE, clarsimp)
  using asid_tlb_lookup_range_pt_walk_not_incon apply force
    apply (clarsimp)
    apply blast
   apply clarsimp
   apply (clarsimp simp: incoherrent_vaddrs_def  inconsistent_vaddrs_def)
   apply (simp only: incon_comp_def ptable_comp_def)
   apply clarsimp
   apply (drule lookup_asid_tlb_hit_union_cases')
   apply (clarsimp simp: asid_tlb_lookup_miss_is_fault_intro  subset_eq)
  apply clarsimp
  apply (rule conjI)
   apply (simp only: global_entries_union)
   apply clarsimp
   apply blast
  apply (subgoal_tac "sat_tlb s \<union> the ` {e \<in> range (pt_walk (set_asid t) (MEM s) r). \<not> is_fault e} =
                       sat_tlb s \<union> non_global_entries (the ` {e \<in> range (pt_walk (set_asid t) (MEM s) r). \<not> is_fault e}) \<union> 
                                    global_entries (the ` {e \<in> range (pt_walk (set_asid t) (MEM s) r). \<not> is_fault e})")
   prefer 2
  apply (metis (no_types) sup_assoc tlb_global_non_global_union)
  apply clarsimp
  apply (thin_tac "sat_tlb s \<union> the ` {e \<in> range (pt_walk (set_asid t) (MEM s) r). \<not> is_fault e} =
                       sat_tlb s \<union> non_global_entries (the ` {e \<in> range (pt_walk (set_asid t) (MEM s) r). \<not> is_fault e}) \<union> 
                                    global_entries (the ` {e \<in> range (pt_walk (set_asid t) (MEM s) r). \<not> is_fault e})")

  apply (subgoal_tac "lookup'' (non_global_entries (the ` {e \<in> range (pt_walk (set_asid t) (MEM s) r). \<not> is_fault e})) a v = Miss")
   prefer 2
   apply (clarsimp simp: asid_unequal_lookup_pt_walk_miss)
  apply (drule_tac t = "sat_tlb s" and t''' = "global_entries (the ` {e \<in> range (pt_walk (set_asid t) (MEM s) r). \<not> is_fault e})" 
      and t'' = "global_entries (sat_tlb s \<union> non_global_entries (the ` {e \<in> range (pt_walk (set_asid t) (MEM s) r). \<not> is_fault e}) \<union> global_entries (the ` {e \<in> range (pt_walk (set_asid t) (MEM s) r). \<not> is_fault e}))" in  lookup_union_minus_equal)
  apply clarsimp
  apply (subgoal_tac " global_entries (sat_tlb s \<union> non_global_entries (the ` {e \<in> range (pt_walk (set_asid t) (MEM s) r). \<not> is_fault e}) \<union> global_entries (the ` {e \<in> range (pt_walk (set_asid t) (MEM s) r). \<not> is_fault e})) =
                          global_entries (sat_tlb s \<union> the ` {e \<in> range (pt_walk (set_asid t) (MEM s) r). \<not> is_fault e})")
   prefer 2
   apply (clarsimp simp: global_entries_def non_global_entries_def) apply blast
  apply (clarsimp)
  apply (clarsimp simp: global_entries_union)
  apply (clarsimp simp: Un_Diff)
  apply (simp only: set_double_minus [symmetric])
  apply clarsimp
  apply (drule_tac x = a in spec, clarsimp, drule_tac x = v in spec)
  by (clarsimp simp: lookup_minus_smaller_order)




lemma  update_asid_non_det_det_refine:
  "\<lbrakk> update_ASID a (s::'a non_det_tlb_state_scheme) = ((), s') ;  update_ASID a (t::'b det_tlb_state_scheme) = ((), t'); 
         tlb_rel_det (typ_non_det_tlb s) (typ_det_tlb t) \<rbrakk> \<Longrightarrow> 
                  tlb_rel_det (typ_non_det_tlb s') (typ_det_tlb t')"
  apply (clarsimp simp: update_ASID_non_det_tlb_state_ext_def update_ASID_det_tlb_state_ext_def)
  apply (clarsimp simp: tlb_rel_det_def  saturated_def)
  by (cases s, cases t , clarsimp simp: state.defs )



lemma  update_asid_det_sat_refine:
  "\<lbrakk>update_ASID a (s::'a det_tlb_state_scheme) = ((), s') ;  update_ASID a (t::'b sat_tlb_state_scheme) = ((), t'); 
         tlb_rel_sat (typ_det_tlb s) (typ_sat_tlb t) \<rbrakk> \<Longrightarrow> 
                  tlb_rel_sat (typ_det_tlb s') (typ_sat_tlb t')"
  apply (clarsimp simp: update_ASID_det_tlb_state_ext_def update_ASID_sat_tlb_state_ext_def)
  apply (clarsimp simp: tlb_rel_sat_def  saturated_def)
  apply (cases s, cases t , clarsimp simp: state.defs)
  by blast



lemma asid_unequal_snp_upd_equal' [simp]:
  "a \<noteq> a' \<Longrightarrow>   snp_upd_cur' snp ist m r a' a = snp a"
  by (clarsimp simp: snp_upd_cur'_def)
  

 
lemma  update_asid_sat_set'_refine:
  "\<lbrakk>update_ASID a (s::'a sat_tlb_state_scheme) = ((), s') ;  update_ASID a (t::'b set_tlb_state_scheme) = ((), t'); 
         tlb_rel_abs (typ_sat_tlb s) (typ_set_tlb t) \<rbrakk> \<Longrightarrow> 
                  tlb_rel_abs (typ_sat_tlb s') (typ_set_tlb t')"
  apply (clarsimp simp: update_ASID_sat_tlb_state_ext_def update_ASID_set_tlb_state_ext_def Let_def)
  apply (frule tlb_rel_absD')
  apply (case_tac "a = sat_asid s")
    (* when we update to the same ASID *)
   apply (subgoal_tac "sat_tlb s = sat_tlb s \<union> 
                                   the `  {e \<in> range (pt_walk (sat_asid s) (MEM s) (TTBR0 s)). \<not> is_fault e}")
    prefer 2
    apply (clarsimp simp:  saturated_def) 
    apply blast
   apply (clarsimp simp: tlb_rel_abs_def)
   apply (rule conjI)
    apply (clarsimp simp: state.defs)
   apply (rule conjI)
    apply (clarsimp simp:  saturated_def) 
   apply (rule conjI)
    apply clarsimp
    apply (clarsimp simp:  snp_upd_cur'_def snp_upd_cur_def )
    apply (cases t, cases s, clarsimp) apply force
   apply clarsimp
   apply (clarsimp simp: lookup_from'_def snap_conv'_def snp_upd_cur'_def snp_upd_cur_def)
    (* when we update to different asid *)
  apply (clarsimp simp: tlb_rel_abs_def)
  apply (rule conjI)
   apply (clarsimp simp: state.defs)
  apply (rule conjI)
   apply (clarsimp simp: saturated_def)
  apply (thin_tac " s' = s\<lparr>sat_asid := a, sat_tlb := sat_tlb s \<union> the ` {e \<in> range (pt_walk a (MEM s) (TTBR0 s)). \<not> is_fault e}\<rparr>")
  apply (thin_tac "t' = t \<lparr>set_asid := a, set_tlb := set_tlb t \<lparr>snapshot := snp_upd_cur' (snapshot (set_tlb t)) (iset (set_tlb t)) (MEM s) (TTBR0 s) (set_asid t),   iset :=      fst (snapshot (set_tlb t) a) \<union> iset (set_tlb t) \<inter> global_set (set_tlb t) \<union> ptable_comp (snd (snapshot (set_tlb t) a)) (pt_walk a (MEM s) (TTBR0 s))\<rparr>\<rparr>")
  apply (rule conjI)
   apply (clarsimp simp: incon_addrs_def)
   apply (rule conjI)
    apply (clarsimp simp: inconsistent_vaddrs_def)
    apply (rename_tac v)
    apply (subgoal_tac "sat_tlb s \<union> the ` {e \<in> range (pt_walk a (MEM s) (TTBR0 s)). \<not> is_fault e} =  (non_global_entries (sat_tlb s) \<union> non_global_entries (the ` {e \<in> range (pt_walk a (MEM s) (TTBR0 s)). \<not> is_fault e})) \<union>  
                          (global_entries (sat_tlb s) \<union> global_entries (the ` {e \<in> range (pt_walk a (MEM s) (TTBR0 s)). \<not> is_fault e}))")
     apply (simp only:)
     apply (thin_tac "sat_tlb s \<union> the ` {e \<in> range (pt_walk a (MEM s) (TTBR0 s)). \<not> is_fault e} = (non_global_entries (sat_tlb s) \<union> non_global_entries (the ` {e \<in> range (pt_walk a (MEM s) (TTBR0 s)). \<not> is_fault e})) \<union>  (global_entries (sat_tlb s) \<union>  global_entries (the ` {e \<in> range (pt_walk a (MEM s) (TTBR0 s)). \<not> is_fault e}))")
     apply (subgoal_tac "lookup''   (global_entries (sat_tlb s))  a v = lookup'' (global_entries (sat_tlb s) \<union>  global_entries (the ` {e \<in> range (pt_walk a (MEM s) (TTBR0 s)). \<not> is_fault e})) a v ")
      prefer 2
      apply (rule saturated_global_subset_lookup_un_eq[symmetric], simp)
     apply (drule_tac t = "non_global_entries (sat_tlb s) \<union> non_global_entries (the ` {e \<in> range (pt_walk a (MEM s) (TTBR0 s)). \<not> is_fault e})" in union_asid_tlb_incon_cases)
     apply (erule disjE, clarsimp)
      apply (thin_tac "lookup'' (global_entries (sat_tlb s) \<union> global_entries (the ` {e \<in> range (pt_walk a (MEM s) (TTBR0 s)). \<not> is_fault e}))
                       a v =  Incon")
      apply (subgoal_tac "v \<in> iset (set_tlb t)")
       apply (subgoal_tac "v \<in> global_set (set_tlb t)")
        apply blast
       apply (clarsimp simp: global_entries_def lookup_def tagged_entry_set_def entry_set_def split: if_split_asm option.splits)
       apply blast
      apply (drule_tac a' = "set_asid t" in lookup_global_incon_incon)
      apply blast
     apply (erule disjE, clarsimp)
      apply (thin_tac "lookup'' (global_entries (sat_tlb s) \<union> global_entries (the ` {e \<in> range (pt_walk a (MEM s) (TTBR0 s)). \<not> is_fault e})) a v = Hit xa") 
      apply (case_tac "v \<in> global_set (set_tlb t)")
       apply (case_tac "v \<in> iset (set_tlb t)")
        apply blast
       apply clarsimp
       apply (subgoal_tac "lookup''  (sat_tlb s) (set_asid t) v = Hit xa \<or> 
                           lookup''  (sat_tlb s) (set_asid t) v = Incon")
        apply (erule_tac P = "lookup''  (sat_tlb s) (set_asid t) v = Hit xa" in disjE)
         apply (case_tac "is_fault (pt_walk (set_asid t) (MEM s) (TTBR0 s) v)")
          apply (clarsimp simp: incoherrent_vaddrs_def)
          apply force
         apply (drule  lookup_asid_tlb_hit_union_cases')
         apply (erule disjE, clarsimp)
          apply (subgoal_tac "asid_of (the (pt_walk a (MEM s) (TTBR0 s) v)) = None")
           apply (drule_tac x = a in spec, simp, drule_tac x = v in spec)
           apply (clarsimp simp: non_global_to_global [symmetric])
           apply (case_tac "lookup_from' (snapshot (set_tlb t)) a v"; clarsimp?)
            apply (clarsimp simp: lookup_from'_def snap_conv'_def split: if_split_asm option.splits)
           apply (clarsimp simp: lookup_from'_def snap_conv'_def split: if_split_asm option.splits)
           apply (clarsimp simp: ptable_comp_def is_fault_def)
          apply (subgoal_tac "lookup'' (global_entries (the ` {e \<in> range (pt_walk a (MEM s) (TTBR0 s)). \<not> is_fault e})) a v = 
                                Hit (the (pt_walk a (MEM s) (TTBR0 s) v))")
           apply (drule lookup_global_hit_asid_of_none, simp)
          apply (subgoal_tac "\<not> is_fault (pt_walk a (MEM s) (TTBR0 s) v)")
           apply (drule lookup_non_global_miss_non_fault; simp)
          apply (drule_tac a' = a in no_fault_pt_walk_unequal_asid', simp)
         apply (erule disjE, clarsimp)
          apply (subgoal_tac "xa \<noteq> the (pt_walk (set_asid t) (MEM s) (TTBR0 s) v)")
           apply (drule_tac b = v and x = xa in saturatd_lookup_hit_no_fault; simp?)
          apply (subgoal_tac "asid_of xa = None")
           apply (subgoal_tac "asid_of (the (pt_walk (set_asid t) (MEM s) (TTBR0 s) v)) \<noteq> None")
            apply force
           apply (subgoal_tac "lookup'' (non_global_entries (the ` {e \<in> range (pt_walk (set_asid t) (MEM s) (TTBR0 s)). \<not> is_fault e})) (set_asid t) v = Hit 
                              (the (pt_walk (set_asid t) (MEM s) (TTBR0 s) v))")
            apply (rule lookup_non_global_hit_asid_of_not_none, simp)
           apply (rule_tac a = a in non_global_lookup_hit_asid, simp)
          apply (rule lookup_global_hit_asid_of_none, simp)
         apply (clarsimp)
         apply (subgoal_tac "xa \<noteq> the (pt_walk (set_asid t) (MEM s) (TTBR0 s) v)")
          apply (drule_tac b = v and x = xa in saturatd_lookup_hit_no_fault; simp?)
         apply (subgoal_tac "asid_of xa = None")
          apply (subgoal_tac "asid_of (the (pt_walk (set_asid t) (MEM s) (TTBR0 s) v)) \<noteq> None")
           apply force
          apply (subgoal_tac "lookup'' (non_global_entries (the ` {e \<in> range (pt_walk (set_asid t) (MEM s) (TTBR0 s)). \<not> is_fault e})) (set_asid t) v = Hit 
                              (the (pt_walk (set_asid t) (MEM s) (TTBR0 s) v))")
           apply (rule lookup_non_global_hit_asid_of_not_none, simp)
          apply (rule_tac a = a in non_global_lookup_hit_asid, simp)
         apply (rule lookup_global_hit_asid_of_none, simp)
        apply blast
       apply (metis (no_types, hide_lams) lookup_global_hit_order lookup_global_same_for_asids)
      apply (subgoal_tac "xa \<in> global_entries (sat_tlb s)")
       apply (subgoal_tac "v \<in> range_of xa")
        apply blast
       apply (simp add: lookup_asid_tlb_hit_entry_range)
  using lookup_in_asid_tlb apply auto[1]
     apply (erule disjE, clarsimp)
      apply (thin_tac "lookup'' (global_entries (sat_tlb s) \<union> global_entries (the ` {e \<in> range (pt_walk a (MEM s) (TTBR0 s)). \<not> is_fault e}))
                       a v =  Incon")
      apply (subgoal_tac "v \<in> iset (set_tlb t)")
       apply (subgoal_tac "v \<in> global_set (set_tlb t)")
        apply blast
       apply (clarsimp simp: global_entries_def lookup_def tagged_entry_set_def entry_set_def split: if_split_asm option.splits)
       apply blast
      apply (drule_tac a' = "set_asid t" in lookup_global_incon_incon)
      apply blast
     apply (erule disjE, clarsimp)
      apply (thin_tac "lookup'' (global_entries (sat_tlb s) \<union>  global_entries (the ` {e \<in> range (pt_walk a (MEM s) (TTBR0 s)). \<not> is_fault e}))a v = Hit x")
      apply (drule union_asid_tlb_incon_cases)
      apply (erule disjE, clarsimp simp: )
  using non_global_lookup_range_pt_walk_not_incon apply force
      apply (erule disjE, clarsimp simp: )
       apply (drule_tac x = a in spec, simp, drule_tac x = v in spec)
       apply (clarsimp simp: non_global_to_global [symmetric])
       apply (case_tac "lookup_from' (snapshot (set_tlb t)) a v"; clarsimp?)
        apply (clarsimp simp: lookup_from'_def snap_conv'_def split: if_split_asm option.splits)
       apply (subgoal_tac "\<not>is_fault (pt_walk a (MEM s) (TTBR0 s) v)")
        apply (subgoal_tac "xb = the (pt_walk a (MEM s) (TTBR0 s) v)")
         apply (clarsimp simp: lookup_from'_def snap_conv'_def split: if_split_asm option.splits)
         apply (clarsimp simp: ptable_comp_def is_fault_def) 
        apply (frule_tac a' = a in non_global_lookup_hit_asid, simp)
       apply (rule non_global_hit_no_fault, simp)
      apply (erule disjE, clarsimp simp: )
  using non_global_lookup_range_pt_walk_not_incon apply force
      apply (erule disjE, clarsimp simp: )
       apply (drule_tac x = a in spec, simp, drule_tac x = v in spec)
       apply (clarsimp simp: non_global_to_global [symmetric])
       apply (clarsimp simp: lookup_from'_def snap_conv'_def split: if_split_asm option.splits)
      apply (erule disjE, clarsimp simp: )
  using non_global_lookup_range_pt_walk_not_incon apply force
      apply (clarsimp simp: )
      apply (drule_tac x = a in spec, simp, drule_tac x = v in spec)
      apply (clarsimp simp: non_global_to_global [symmetric])
      apply (clarsimp simp: lookup_from'_def snap_conv'_def split: if_split_asm option.splits)
     apply (erule disjE, clarsimp)
      apply (thin_tac "lookup'' (global_entries (sat_tlb s) \<union> global_entries (the ` {e \<in> range (pt_walk a (MEM s) (TTBR0 s)). \<not> is_fault e}))
                       a v =  Incon")
      apply (subgoal_tac "v \<in> iset (set_tlb t)")
       apply (subgoal_tac "v \<in> global_set (set_tlb t)")
        apply blast
       apply (clarsimp simp: global_entries_def lookup_def tagged_entry_set_def entry_set_def split: if_split_asm option.splits)
       apply blast
      apply (drule_tac a' = "set_asid t" in lookup_global_incon_incon)
      apply blast
     apply (clarsimp)
     apply (thin_tac "lookup''  (global_entries (sat_tlb s) \<union> global_entries (the ` {e \<in> range (pt_walk a (MEM s) (TTBR0 s)). \<not> is_fault e})) a v = Miss")
     apply (drule union_asid_tlb_incon_cases)
     apply (erule disjE, clarsimp simp: )
  using non_global_lookup_range_pt_walk_not_incon apply force
     apply (erule disjE, clarsimp simp: )
      apply (drule_tac x = a in spec, simp, drule_tac x = v in spec)
      apply (clarsimp simp: non_global_to_global [symmetric])
      apply (case_tac "lookup_from' (snapshot (set_tlb t)) a v"; clarsimp?)
       apply (clarsimp simp: lookup_from'_def snap_conv'_def split: if_split_asm option.splits)
      apply (subgoal_tac "\<not>is_fault (pt_walk a (MEM s) (TTBR0 s) v)")
       apply (subgoal_tac "xa = the (pt_walk a (MEM s) (TTBR0 s) v)")
        apply (clarsimp simp: lookup_from'_def snap_conv'_def split: if_split_asm option.splits)
        apply (clarsimp simp: ptable_comp_def is_fault_def) 
       apply (frule_tac a' = a in non_global_lookup_hit_asid, simp)
      apply (rule non_global_hit_no_fault, simp)
     apply (erule disjE, clarsimp simp: )
  using non_global_lookup_range_pt_walk_not_incon apply force
     apply (erule disjE, clarsimp simp: )
      apply (drule_tac x = a in spec, simp, drule_tac x = v in spec)
      apply (clarsimp simp: non_global_to_global [symmetric])
      apply (clarsimp simp: lookup_from'_def snap_conv'_def split: if_split_asm option.splits)
     apply (erule disjE, clarsimp simp: )
  using non_global_lookup_range_pt_walk_not_incon apply force
     apply (clarsimp simp: )
     apply (drule_tac x = a in spec, simp, drule_tac x = v in spec)
     apply (clarsimp simp: non_global_to_global [symmetric])
     apply (clarsimp simp: lookup_from'_def snap_conv'_def split: if_split_asm option.splits)
  

    apply (rule tlb_nion_global_non_global)


   apply (clarsimp simp: incoherrent_vaddrs_def)
   apply (rename_tac v x)
   apply (subgoal_tac "sat_tlb s \<union> the ` {e \<in> range (pt_walk a (MEM s) (TTBR0 s)). \<not> is_fault e} = 
                                             (non_global_entries (sat_tlb s) \<union> non_global_entries (the ` {e \<in> range (pt_walk a (MEM s) (TTBR0 s)). \<not> is_fault e})) \<union>  (global_entries (sat_tlb s) \<union> global_entries (the ` {e \<in> range (pt_walk a (MEM s) (TTBR0 s)). \<not> is_fault e}))")
    apply (simp only:)
    apply (thin_tac "sat_tlb s \<union> the ` {e \<in> range (pt_walk a (MEM s) (TTBR0 s)). \<not> is_fault e} = 
                                                                               (non_global_entries (sat_tlb s) \<union> non_global_entries (the ` {e \<in> range (pt_walk a (MEM s) (TTBR0 s)). \<not> is_fault e})) \<union>  (global_entries (sat_tlb s) \<union>  global_entries (the ` {e \<in> range (pt_walk a (MEM s) (TTBR0 s)). \<not> is_fault e}))")
    apply (subgoal_tac "lookup''   (global_entries (sat_tlb s))  a v = lookup'' (global_entries (sat_tlb s) \<union>  global_entries (the ` {e \<in> range (pt_walk a (MEM s) (TTBR0 s)). \<not> is_fault e})) a v ")
      prefer 2
      apply (rule saturated_global_subset_lookup_un_eq[symmetric], simp)
    
    apply (drule_tac t = "non_global_entries (sat_tlb s) \<union> non_global_entries (the ` {e \<in> range (pt_walk a (MEM s) (TTBR0 s)). \<not> is_fault e})" in  lookup_asid_tlb_hit_union_cases')
    apply (erule disjE, clarsimp)

     apply (thin_tac "lookup''(global_entries (sat_tlb s) \<union> global_entries (the ` {e \<in> range (pt_walk a (MEM s) (TTBR0 s)). \<not> is_fault e})) a v = Miss")
     apply (subgoal_tac "lookup'' (non_global_entries (the ` {e \<in> range (pt_walk a (MEM s) (TTBR0 s)). \<not> is_fault e})) a v = Miss")
      apply (drule  lookup_asid_tlb_hit_union_cases')
      apply (erule disjE, clarsimp)
       apply (drule_tac x = a in spec, simp, drule_tac x = v in spec)
       apply (clarsimp simp: non_global_to_global [symmetric])
       apply (case_tac "lookup_from' (snapshot (set_tlb t)) a v"; clarsimp?)
        apply (clarsimp simp: lookup_from'_def snap_conv'_def split: if_split_asm option.splits)
       apply (clarsimp simp: lookup_from'_def snap_conv'_def split: if_split_asm option.splits)
       apply (clarsimp simp: ptable_comp_def is_fault_def) 
      apply (erule disjE, clarsimp)
      apply (clarsimp)
     apply (rule is_fault_non_global_entries_miss, simp)
    apply (erule disjE, clarsimp)
     apply (thin_tac "lookup''  (global_entries (sat_tlb s) \<union> global_entries (the ` {e \<in> range (pt_walk a (MEM s) (TTBR0 s)). \<not> is_fault e})) a v =  Hit x")
     apply (subgoal_tac "v \<in> global_set (set_tlb t)")
      apply (case_tac "v \<in> iset (set_tlb t)") 
       apply blast
      apply (subgoal_tac " lookup''  (sat_tlb s) (set_asid t) v = Hit x \<or>
                       lookup''  (sat_tlb s) (set_asid t) v = Incon")
       prefer 2
       apply (metis (no_types, hide_lams)  lookup_global_hit_order lookup_global_same_for_asids )
      apply (erule disjE)
  apply (clarsimp simp: ) 
  using no_fault_pt_walk_unequal_asid' apply fastforce
      apply (clarsimp simp: inconsistent_vaddrs_def) apply force
     apply (clarsimp simp: global_entries_def lookup_def tagged_entry_set_def entry_set_def split: if_split_asm option.splits)
     apply blast

  apply (clarsimp)
 apply (subgoal_tac "v \<in> global_set (set_tlb t)")
      apply (case_tac "v \<in> iset (set_tlb t)") 
       apply blast
      apply (subgoal_tac " lookup''  (sat_tlb s) (set_asid t) v = Hit x \<or>
                       lookup''  (sat_tlb s) (set_asid t) v = Incon")
       prefer 2
       apply (metis (no_types, hide_lams)  lookup_global_hit_order lookup_global_same_for_asids )
      apply (erule disjE)
  apply (clarsimp simp: ) 
  using no_fault_pt_walk_unequal_asid' apply fastforce
      apply (clarsimp simp: inconsistent_vaddrs_def) apply force
     apply (clarsimp simp: global_entries_def lookup_def tagged_entry_set_def entry_set_def split: if_split_asm option.splits)
     apply blast
 apply (rule tlb_nion_global_non_global)












  apply (rule conjI)
   apply (subgoal_tac " global_entries (sat_tlb s \<union> the ` {e \<in> range (pt_walk a (MEM s) (TTBR0 s)). \<not> is_fault e}) = 
                         global_entries (sat_tlb s)")
    apply (simp only:)
   apply (subgoal_tac "global_entries (the ` {e \<in> range (pt_walk a (MEM s) (TTBR0 s)). \<not> is_fault e}) \<subseteq> 
          global_entries (sat_tlb s)" )
    apply (clarsimp simp: global_entries_union)
    apply blast
   apply (subgoal_tac "global_entries (the ` {e \<in> range (pt_walk a (MEM s) (TTBR0 s)). \<not> is_fault e}) = 
                       global_entries (the ` {e \<in> range (pt_walk (sat_asid s) (MEM s) (TTBR0 s)). \<not> is_fault e})")
    apply (simp only:)
    apply (clarsimp simp: saturated_def global_entries_def) apply blast
   apply (rule global_entries_ptable_same)

  apply (clarsimp simp: )
  apply (subgoal_tac "(sat_tlb s \<union> the ` {e \<in> range (pt_walk a (MEM s) (TTBR0 s)). \<not> is_fault e} - global_entries (sat_tlb s \<union> the ` {e \<in> range (pt_walk a (MEM s) (TTBR0 s)). \<not> is_fault e})) =
                                                                                                non_global_entries (sat_tlb s \<union> the ` {e \<in> range (pt_walk a (MEM s) (TTBR0 s)). \<not> is_fault e})")
   apply (simp only:)
   apply (thin_tac "(sat_tlb s \<union> the ` {e \<in> range (pt_walk a (MEM s) (TTBR0 s)). \<not> is_fault e} - global_entries (sat_tlb s \<union> the ` {e \<in> range (pt_walk a (MEM s) (TTBR0 s)). \<not> is_fault e})) =
                                                                                                non_global_entries (sat_tlb s \<union> the ` {e \<in> range (pt_walk a (MEM s) (TTBR0 s)). \<not> is_fault e})")
   apply (case_tac "aa = set_asid t")
    apply (thin_tac "\<forall>a. a \<noteq> set_asid t \<longrightarrow> (\<forall>v. lookup'' (sat_tlb s - global_entries (sat_tlb s)) a v \<le> lookup_from' (snapshot (set_tlb t)) a v)")
    apply (clarsimp)
    apply (subgoal_tac "lookup'' (non_global_entries (sat_tlb s \<union> the ` {e \<in> range (pt_walk a (MEM s) (TTBR0 s)). \<not> is_fault e})) (set_asid t) v =
                                                              lookup'' (non_global_entries (sat_tlb s)) (set_asid t) v")
     apply (simp only:)
     apply (thin_tac "lookup'' (non_global_entries (sat_tlb s \<union> the ` {e \<in> range (pt_walk a (MEM s) (TTBR0 s)). \<not> is_fault e})) (set_asid t) v =
                                                              lookup'' (non_global_entries (sat_tlb s)) (set_asid t) v")
     apply (case_tac "lookup_from' (snp_upd_cur' (snapshot (set_tlb t)) (iset (set_tlb t)) (MEM s) (TTBR0 s) (set_asid t)) (set_asid t) v"; clarsimp)
      apply (clarsimp simp: lookup_from'_def snap_conv'_def split: if_split_asm option.splits)
       apply (clarsimp simp: snp_upd_cur'_def snp_upd_cur_def)
       apply (subgoal_tac "v \<notin> incon_addrs (typ_sat_tlb s)")
        apply (thin_tac "incon_addrs (typ_sat_tlb s) \<subseteq> iset (set_tlb t)")
        apply (clarsimp simp: incon_addrs_def inconsistent_vaddrs_def incoherrent_vaddrs_def is_fault_def)
        apply (metis lookup_asid_tlb_miss_union lookup_type.exhaust tlb_global_non_global_union)
       apply blast
      apply (clarsimp simp: snp_upd_cur'_def snp_upd_cur_def)
      apply (subgoal_tac "v \<notin> incon_addrs (typ_sat_tlb s)") prefer 2 apply blast
      apply (thin_tac "incon_addrs (typ_sat_tlb s) \<subseteq> iset (set_tlb t)")
      apply (clarsimp simp: incon_addrs_def inconsistent_vaddrs_def incoherrent_vaddrs_def is_fault_def)
      apply (case_tac "lookup'' (sat_tlb s) (set_asid t) v"; clarsimp)
       apply (metis lookup_asid_tlb_miss_union tlb_global_non_global_union)
      apply (subgoal_tac "lookup'' (sat_tlb s) (set_asid t) v = lookup'' (sat_tlb s \<union> the ` {e \<in> range (pt_walk (set_asid t) (MEM s) (TTBR0 s)). \<not> is_fault e}) (set_asid t) v")
       prefer 2
       apply (clarsimp simp: saturated_def)
       apply (simp add: sup.absorb1)  
      apply (simp only:)
      apply (drule lookup_asid_tlb_hit_union_cases')
      apply (erule disjE, clarsimp)
       apply (subgoal_tac "is_fault (pt_walk (set_asid t) (MEM s) (TTBR0 s) v)")
        apply (clarsimp simp: is_fault_def)
       apply (rule asid_tlb_lookup_miss_is_fault, simp)
      apply (erule disjE, clarsimp)
      apply (clarsimp)
      apply (subgoal_tac "x3 = x2") apply clarsimp
       apply (subgoal_tac "lookup'' (sat_tlb s) (set_asid t) v = lookup'' (global_entries (sat_tlb s) \<union> non_global_entries (sat_tlb s)) (set_asid t) v ")
        apply (simp only:)
        apply (thin_tac "  lookup'' (the ` {e \<in> range (pt_walk (set_asid t) (MEM s) (TTBR0 s)). \<not> is_fault e}) (set_asid t) v = Hit x2 ")
        apply (drule lookup_asid_tlb_hit_union_cases')   
        apply (erule disjE, clarsimp)   
        apply (erule disjE, clarsimp)  
         apply (drule lookup_non_global_hit_asid_of_not_none, simp)
        apply (clarsimp) 
        apply (drule lookup_non_global_hit_asid_of_not_none, simp)
       apply (clarsimp) apply (insert tlb_global_non_global_union [of "sat_tlb s"])
       apply (simp add: Un_commute)
      apply (frule asid_tlb_lookup_range_fault_pt_walk)
      apply (drule_tac x = v in bspec)
  using lookup_asid_tlb_hit_entry_range apply force
      apply simp
     apply (clarsimp simp: lookup_from'_def snap_conv'_def split: if_split_asm option.splits)
     apply (clarsimp simp: snp_upd_cur'_def snp_upd_cur_def)
     apply (subgoal_tac "v \<notin> incon_addrs (typ_sat_tlb s)") prefer 2 apply blast
     apply (thin_tac "incon_addrs (typ_sat_tlb s) \<subseteq> iset (set_tlb t)")
     apply (clarsimp simp: incon_addrs_def inconsistent_vaddrs_def incoherrent_vaddrs_def is_fault_def)
     apply (case_tac "lookup'' (sat_tlb s) (set_asid t) v"; clarsimp)
      apply (simp only: non_global_to_global)
      apply (subgoal_tac "lookup'' (sat_tlb s - global_entries (sat_tlb s)) (set_asid t) v = Miss") apply simp
      apply (rule lookup_miss_minus_miss, simp)
     apply (subgoal_tac "x3a = x3", simp)
      apply (simp only: non_global_to_global)
      apply (subgoal_tac "lookup'' (sat_tlb s - global_entries (sat_tlb s)) (set_asid t) v = Miss \<or> lookup'' (sat_tlb s - global_entries (sat_tlb s)) (set_asid t) v = Hit x3")
       apply force
      apply (rule lookup_miss_minus_miss_hit, simp)
     apply (frule_tac b = v and x = x3a in  saturatd_lookup_hit_no_fault, simp, 
      simp add: is_fault_def, simp)
    apply (rule lookup_non_global_union_asid_unequal, simp)
   apply (drule_tac x = aa in spec, simp, drule_tac x = v in spec)
   apply (subgoal_tac "lookup'' (non_global_entries (sat_tlb s \<union> the ` {e \<in> range (pt_walk a (MEM s) (TTBR0 s)). \<not> is_fault e})) aa v =
                                         lookup'' (non_global_entries (sat_tlb s)) aa v") 
    apply (simp only: non_global_to_global)
    apply (clarsimp simp: snp_upd_cur'_def snp_upd_cur_def)
    apply (clarsimp simp: lookup_from'_def snap_conv'_def split: if_split_asm option.splits)
   apply (rule lookup_non_global_union_asid_unequal', simp, simp, simp) 
  using non_global_to_global by auto 




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


lemma  flush_tlb_det_sat_refine:
  "\<lbrakk> flush FlushTLB (s::'a det_tlb_state_scheme) = ((), s') ;  flush FlushTLB (t::'b sat_tlb_state_scheme) = ((), t'); 
         tlb_rel_sat (typ_det_tlb s) (typ_sat_tlb t) \<rbrakk> \<Longrightarrow> 
                  tlb_rel_sat (typ_det_tlb s') (typ_sat_tlb t')"
  apply (clarsimp simp: flush_det_tlb_state_ext_def flush_sat_tlb_state_ext_def)
  apply (clarsimp simp: tlb_rel_sat_def saturated_def)
  apply (cases s, cases t , clarsimp simp: state.defs)
  done

lemma  flush_varange_det_sat_refine:
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
  by (cases f; clarsimp simp: flush_tlb_det_sat_refine   flush_varange_det_sat_refine ) 



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
  using asid_tlb_lookup_range_pt_walk_not_incon apply force
   apply (clarsimp simp: incoherrent_vaddrs_def)
  using asid_tlb_lookup_miss_is_fault_intro apply force
  apply (rule conjI)
   apply (cases s, cases t , clarsimp simp: state.defs)
  apply (clarsimp simp: non_global_to_global [symmetric])
  apply (subgoal_tac "lookup'' (non_global_entries (the ` {e \<in> range (pt_walk (set_asid t) (MEM s) (TTBR0 s)). \<not> is_fault e})) a v = Miss")
   apply force
  by (rule asid_unequal_lookup_pt_walk_miss, simp)


lemma lookup_minus_union_incon:
  "lookup'' (t - t' \<union> t'') a v = Incon \<Longrightarrow> lookup'' (t \<union> t'') a v = Incon"
  apply (subgoal_tac "t - t' \<union> t'' \<subseteq> t \<union> t''")
  using lookup_asid_tlb_incon_subset apply blast
  by blast
 

lemma addr_set_minus_lookup_miss:
  "v \<in> vset \<Longrightarrow> lookup'' (t - (\<Union>v\<in>vset. {e \<in> t. v \<in> range_of e})) a v = Miss"
  apply (subgoal_tac "tagged_entry_set (t - (\<Union>v\<in>vset. {e \<in> t. v \<in> range_of e})) a v = {}")
   apply (clarsimp simp: lookup_def)
  apply (clarsimp simp: tagged_entry_set_def entry_set_def) by force



lemma addr_set_minus_non_global_lookup_miss:
  "v \<in> vset \<Longrightarrow> lookup'' (non_global_entries (t - (\<Union>v\<in>vset. {e \<in> t. v \<in> range_of e}))) a v = Miss"
  apply (subgoal_tac "tagged_entry_set (non_global_entries (t - (\<Union>v\<in>vset. {e \<in> t. v \<in> range_of e}))) a v = {}")
   apply (clarsimp simp: lookup_def)
  by (clarsimp simp: non_global_entries_def tagged_entry_set_def entry_set_def) 





lemma non_global_entries_union:
  "non_global_entries (tlb \<union> tlb') = non_global_entries tlb \<union> non_global_entries tlb'"
  apply (clarsimp simp: non_global_entries_def)
  by blast

lemma non_global_entries_sub:
  "non_global_entries (tlb - tlb') = non_global_entries tlb - non_global_entries tlb'"
  apply (clarsimp simp: non_global_entries_def)
  by blast


lemma  flush_varange_sat_incon_refine:
  "\<lbrakk> flush (Flushvarange vset) (s::'a sat_tlb_state_scheme) = ((), s') ;  flush (Flushvarange vset) (t::'b set_tlb_state_scheme) = ((), t'); 
         tlb_rel_abs (typ_sat_tlb s) (typ_set_tlb t) \<rbrakk> \<Longrightarrow> 
                  tlb_rel_abs (typ_sat_tlb s') (typ_set_tlb t')"
  apply (clarsimp simp: flush_sat_tlb_state_ext_def flush_set_tlb_state_ext_def flush_tlb_vset_def  Let_def)
  apply (clarsimp simp: tlb_rel_abs_def)
  apply (rule conjI)
   apply (cases s, cases t , clarsimp simp: state.defs)
  apply (rule conjI)
   apply (clarsimp simp: saturated_def)
  apply (rule conjI)
   apply (clarsimp simp: incon_addrs_def)
   apply (rule conjI)
    apply (clarsimp simp: inconsistent_vaddrs_def)
    apply (rename_tac v)
    apply (rule conjI)
     apply (subgoal_tac "lookup'' (sat_tlb s  \<union> the ` {e \<in> range (pt_walk (set_asid t) (MEM s) (TTBR0 s)). \<not> is_fault e}) (set_asid t) v = Incon")
      apply (subgoal_tac "lookup'' (sat_tlb s) (set_asid t) v = Incon")
       apply blast
      apply (subgoal_tac "sat_tlb s \<union> the ` {e \<in> range (pt_walk (set_asid t) (MEM s) (TTBR0 s)). \<not> is_fault e} = sat_tlb s")
       apply force
      apply (force simp: saturated_def)
     apply (drule lookup_minus_union_incon, simp)
    apply (drule union_asid_tlb_incon_cases)
    apply (erule disjE, clarsimp simp: asid_tlb_lookup_range_pt_walk_not_incon)
    apply (erule disjE, clarsimp simp:)
  using lookup_asid_tlb_hit_entry_range apply force
    apply (erule disjE, clarsimp simp: asid_tlb_lookup_range_pt_walk_not_incon)
    apply (erule disjE, clarsimp simp: ) 
     apply (drule_tac t = "sat_tlb s" and a = "set_asid t" in  addr_set_minus_lookup_miss, force)
    apply (erule disjE, clarsimp simp: asid_tlb_lookup_range_pt_walk_not_incon)
    apply clarsimp
    apply (drule_tac t = "sat_tlb s" and a = "set_asid t" in  addr_set_minus_lookup_miss, force)
   apply (clarsimp simp: incoherrent_vaddrs_def)
   apply (rename_tac v x)
   apply (rule conjI)
    apply (drule lookup_asid_tlb_hit_union_cases')
    apply (erule disjE, clarsimp simp: ) 
     apply (subgoal_tac "lookup'' (sat_tlb s) (set_asid t) v = Hit x \<or> lookup'' (sat_tlb s) (set_asid t) v = Incon")
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
    apply (drule_tac t = "sat_tlb s" and a = "set_asid t" in  addr_set_minus_lookup_miss, force)
   apply (erule disjE, clarsimp simp: )   
    apply (drule asid_tlb_lookup_miss_is_fault_intro, simp)
   apply clarsimp
   apply (drule_tac t = "sat_tlb s" and a = "set_asid t" in  addr_set_minus_lookup_miss, force)
  apply (rule conjI)
   apply safe [1]
    apply (subgoal_tac " xa \<in> global_entries (sat_tlb s - (\<Union>v\<in>vset. {e \<in> sat_tlb s. v \<in> range_of e}))")
     apply (subgoal_tac " xa \<in> global_entries (sat_tlb s)")
      apply blast
     apply (clarsimp simp: global_entries_def) 
    apply (clarsimp simp: global_entries_union)    
    apply (cases s, cases t , clarsimp simp: state.defs)
   apply (subgoal_tac " xa \<in> global_entries (sat_tlb s - (\<Union>v\<in>vset. {e \<in> sat_tlb s. v \<in> range_of e}))")
    prefer 2
    apply (clarsimp simp: global_entries_union)    
    apply (cases s, cases t , clarsimp simp: state.defs)
   apply (clarsimp simp: entry_set_def global_entries_def)
  apply (clarsimp simp: non_global_to_global [symmetric])
  apply (case_tac "lookup''(non_global_entries  (sat_tlb s - (\<Union>v\<in>vset. {e \<in> sat_tlb s. v \<in> range_of e}) \<union>
                                the ` {e \<in> range (pt_walk (set_asid t) (MEM s) (TTBR0 s)). \<not> is_fault e})) a v"; clarsimp)
   apply (clarsimp simp: non_global_entries_union)
   apply (subgoal_tac "lookup''( non_global_entries  (the ` {e \<in> range (pt_walk (set_asid t) (MEM s) (TTBR0 s)). \<not> is_fault e})) a v = Miss")
    apply (subgoal_tac "lookup'' (non_global_entries (sat_tlb s - (\<Union>v\<in>vset. {e \<in> sat_tlb s. v \<in> range_of e}))) a v =  Incon")
     apply (subgoal_tac "lookup'' (non_global_entries (sat_tlb s)) a v = Incon")
      apply (case_tac "v \<in> vset")
       apply (drule_tac t = "sat_tlb s" and a = a in addr_set_minus_non_global_lookup_miss, clarsimp)
      apply (drule_tac x = a in spec, simp, drule_tac x = v in spec, simp)
      apply (clarsimp simp: lookup_from'_def snap_conv'_def split: if_split_asm option.splits)
     apply (clarsimp simp: non_global_entries_sub)
     apply (drule lookup_asid_tlb_incon_minus, simp)
    apply (meson lookup_asid_tlb_incon_not_miss)
   apply (rule asid_unequal_lookup_pt_walk_miss, simp)
  apply (clarsimp simp: non_global_entries_union)
  apply (subgoal_tac "lookup'' (non_global_entries (the ` {e \<in> range (pt_walk (set_asid t) (MEM s) (TTBR0 s)). \<not> is_fault e})) a v =  Miss")
   prefer 2
   apply (rule asid_unequal_lookup_pt_walk_miss, simp)
  apply (subgoal_tac "lookup'' (non_global_entries (sat_tlb s - (\<Union>v\<in>vset. {e \<in> sat_tlb s. v \<in> range_of e})))  a v = Hit x3")
   prefer 2
  apply(drule lookup_asid_tlb_hit_mis_hit; simp)
  apply (subgoal_tac "lookup'' (non_global_entries (sat_tlb s))  a v = Hit x3 \<or>
                         lookup'' (non_global_entries (sat_tlb s))  a v = Incon")
   prefer 2
   apply (clarsimp simp: non_global_entries_sub)
  apply (drule lookup_asid_tlb_hit_incon_minus; simp)
  apply (erule disjE)
   prefer 2
   apply (case_tac "v \<in> vset")
    apply (drule_tac t = "sat_tlb s" and a = a in addr_set_minus_non_global_lookup_miss, clarsimp)
   apply (drule_tac x = a in spec, simp, drule_tac x = v in spec, simp)
   apply (clarsimp simp: lookup_from'_def snap_conv'_def split: if_split_asm option.splits)
  apply (case_tac "v \<in> vset")
   apply (drule_tac t = "sat_tlb s" and a = a in addr_set_minus_non_global_lookup_miss, clarsimp)
  apply (drule_tac x = a in spec, simp, drule_tac x = v in spec, simp)
  by (clarsimp simp: lookup_from'_def snap_conv'_def entry_set_def split: if_split_asm option.splits) 


lemma  flush_sat_incon_refine:
  "\<lbrakk> flush f (s::'a sat_tlb_state_scheme) = ((), s') ;  flush f (t::'b set_tlb_state_scheme) = ((), t'); 
         tlb_rel_abs (typ_sat_tlb s) (typ_set_tlb t) \<rbrakk> \<Longrightarrow> 
                  tlb_rel_abs (typ_sat_tlb s') (typ_set_tlb t')"
  by (cases f; clarsimp simp: flush_tlb_sat_incon_refine   flush_varange_sat_incon_refine ) 



lemma  flush_with_asid_asid_non_det_det_refine:
  "\<lbrakk> flush_with_ASID (FlushASID a) (s::'a non_det_tlb_state_scheme) = ((), s') ;  flush_with_ASID (FlushASID a) (t::'b det_tlb_state_scheme) = ((), t'); 
         tlb_rel_det (typ_non_det_tlb s) (typ_det_tlb t) \<rbrakk> \<Longrightarrow> 
                  tlb_rel_det (typ_non_det_tlb s') (typ_det_tlb t')"
  apply (clarsimp simp: flush_with_ASID_non_det_tlb_state_ext_def flush_with_ASID_det_tlb_state_ext_def flush_tlb_asid_def)
  apply (clarsimp simp: tlb_rel_det_def)
  apply (cases s, cases t , clarsimp simp: state.defs)
  by blast

lemma  flush_with_asid_asid_varange_non_det_det_refine:
  "\<lbrakk>flush_with_ASID (FlushASIDvarange a vset) (s::'a non_det_tlb_state_scheme) = ((), s') ;  flush_with_ASID (FlushASIDvarange a vset) (t::'b det_tlb_state_scheme) = ((), t'); 
         tlb_rel_det (typ_non_det_tlb s) (typ_det_tlb t) \<rbrakk> \<Longrightarrow> 
                  tlb_rel_det (typ_non_det_tlb s') (typ_det_tlb t')"
  apply (clarsimp simp: flush_with_ASID_non_det_tlb_state_ext_def flush_with_ASID_det_tlb_state_ext_def  flush_tlb_a_vset_def)
  apply (clarsimp simp: tlb_rel_det_def)
  apply (cases s, cases t , clarsimp simp: state.defs) 
  by blast



lemma  flush_with_asid_non_det_det_refine:
  "\<lbrakk> flush_with_ASID f (s::'a non_det_tlb_state_scheme) = ((), s') ;  flush_with_ASID f (t::'b det_tlb_state_scheme) = ((), t'); 
         tlb_rel_det (typ_non_det_tlb s) (typ_det_tlb t) \<rbrakk> \<Longrightarrow> 
                  tlb_rel_det (typ_non_det_tlb s') (typ_det_tlb t')"
  by (cases f; clarsimp simp: flush_with_asid_asid_non_det_det_refine flush_with_asid_asid_varange_non_det_det_refine)



lemma  flush_with_asid_asid_det_sat_refine:
  "\<lbrakk> flush_with_ASID (FlushASID a) (s::'a det_tlb_state_scheme) = ((), s') ;  flush_with_ASID (FlushASID a) (t::'b sat_tlb_state_scheme) = ((), t'); 
         tlb_rel_sat (typ_det_tlb s) (typ_sat_tlb t) \<rbrakk> \<Longrightarrow> 
                  tlb_rel_sat (typ_det_tlb s') (typ_sat_tlb t')"
  apply (clarsimp simp: flush_with_ASID_det_tlb_state_ext_def flush_with_ASID_sat_tlb_state_ext_def flush_tlb_asid_def)
  apply (clarsimp simp: tlb_rel_sat_def)
  apply (cases s, cases t , clarsimp simp: state.defs saturated_def)
  by blast

lemma  flush_with_asid_asid_varange_det_sat_refine:
  "\<lbrakk>flush_with_ASID (FlushASIDvarange a vset) (s::'a det_tlb_state_scheme) = ((), s') ;  flush_with_ASID (FlushASIDvarange a vset) (t::'b sat_tlb_state_scheme) = ((), t'); 
         tlb_rel_sat (typ_det_tlb s) (typ_sat_tlb t) \<rbrakk> \<Longrightarrow> 
                  tlb_rel_sat (typ_det_tlb s') (typ_sat_tlb t')"
  apply (clarsimp simp: flush_with_ASID_det_tlb_state_ext_def flush_with_ASID_sat_tlb_state_ext_def  flush_tlb_a_vset_def)
  apply (clarsimp simp: tlb_rel_sat_def)
  apply (cases s, cases t , clarsimp simp: state.defs saturated_def)
  by blast


lemma  flush_with_asid_det_sat_refine:
  "\<lbrakk> flush_with_ASID f (s::'a det_tlb_state_scheme) = ((), s') ;  flush_with_ASID f (t::'b sat_tlb_state_scheme) = ((), t'); 
         tlb_rel_sat (typ_det_tlb s) (typ_sat_tlb t) \<rbrakk> \<Longrightarrow> 
                  tlb_rel_sat (typ_det_tlb s') (typ_sat_tlb t')"
  by (cases f; clarsimp simp: flush_with_asid_asid_det_sat_refine flush_with_asid_asid_varange_det_sat_refine)



lemma lookup_sub_asid_of_hit_global:
  "lookup'' (t - {e \<in> t. asid_of e = Some a}) a v = Hit e \<Longrightarrow>
        lookup'' (global_entries t) a v = Hit e"
  apply (clarsimp simp: global_entries_def lookup_def tagged_entry_set_def entry_set_def 
                  split: if_split_asm option.splits)
  by (safe; force)

lemma lookup_sub_asid_of_incon_global:
  "lookup'' (t - {e \<in> t. asid_of e = Some a}) a v = Incon \<Longrightarrow>
        lookup'' (global_entries t) a v = Incon"
  apply (clarsimp simp: global_entries_def lookup_def tagged_entry_set_def entry_set_def 
                  split: if_split_asm option.splits)
  by (safe; force)

                                                        
lemma lookup_minus_miss_sncd_miss:
  "\<lbrakk> lookup'' (t - t') a v = Miss; lookup'' t' a v = Miss \<rbrakk> \<Longrightarrow> lookup'' t  a v = Miss"
  apply (clarsimp simp: lookup_def tagged_entry_set_def entry_set_def split: if_split_asm)
  by (safe; force)


lemma lookup_union_miss_sncd_miss:
  "\<lbrakk> lookup'' (t \<union> t') a v = Miss; lookup'' t' a v = Miss \<rbrakk> \<Longrightarrow> lookup'' t  a v = Miss"
  apply (clarsimp simp: lookup_def tagged_entry_set_def entry_set_def split: if_split_asm)
  by (safe; force)


lemma asid_unequal_lookup_non_global_asid_flush_pt_walk:
  "a' \<noteq> a \<Longrightarrow>
       lookup'' (non_global_entries (t - {e \<in> t. asid_of e = Some a} \<union> the ` {e \<in> range (pt_walk a m r). \<not> is_fault e})) a' v =
           lookup'' (non_global_entries t) a' v"
  apply (clarsimp simp: non_global_entries_union)
  apply (subgoal_tac "lookup'' (non_global_entries (the ` {e \<in> range (pt_walk a m r). \<not> is_fault e})) a' v = Miss")
   prefer 2
   apply (rule asid_unequal_lookup_pt_walk_miss, simp)
  apply (cases "lookup'' (non_global_entries (t - {e \<in> t. asid_of e = Some a}) \<union> non_global_entries (the ` {e \<in> range (pt_walk a m r). \<not> is_fault e})) a' v"; clarsimp?)
    apply (subgoal_tac "lookup'' (non_global_entries (t - {e \<in> t. asid_of e = Some a})) a' v = Miss")
     apply (clarsimp simp: non_global_entries_sub)
     apply (subgoal_tac "lookup'' (non_global_entries {e \<in> t. asid_of e = Some a}) a' v = Miss")
      apply (drule lookup_minus_miss_sncd_miss, simp, simp)
     apply (clarsimp simp: non_global_entries_def lookup_def tagged_entry_set_def entry_set_def split: if_split_asm)
    apply (drule lookup_union_miss_sncd_miss, simp, simp)
   apply (drule lookup_asid_tlb_incon_not_miss, simp)
   apply (clarsimp simp: non_global_entries_sub)
  using lookup_asid_tlb_incon_minus apply force
  apply (drule lookup_asid_tlb_hit_mis_hit, simp)
  apply (clarsimp simp: non_global_entries_sub)
  apply (subgoal_tac "lookup'' (non_global_entries {e \<in> t. asid_of e = Some a}) a' v = Miss")
   apply (frule lookup_asid_tlb_minus_hit', simp, simp)
  by (clarsimp simp: non_global_entries_def lookup_def tagged_entry_set_def entry_set_def split: if_split_asm)

lemma asid_unequal_lookup_minus_non_global_hit_hit:
  "\<lbrakk>a \<noteq> a'; lookup'' (t - {e \<in> t. asid_of e = Some a}) a' v = Hit e\<rbrakk>
       \<Longrightarrow> lookup'' t a' v = Hit e"
  apply (subgoal_tac "lookup'' ({e \<in> t. asid_of e = Some a}) a' v = Miss")
   prefer 2
   apply (subgoal_tac "tagged_entry_set ({e \<in> t. asid_of e = Some a}) a' v = {}")
    apply (clarsimp simp: lookup_def split: if_split_asm)  
   apply (clarsimp simp:  tagged_entry_set_def entry_set_def split: if_split_asm)
  by (drule lookup_asid_tlb_minus_hit', simp, simp)


lemma lookup_non_global_entries_sub_miss :
  "lookup'' (non_global_entries (sat_tlb s - {e \<in> sat_tlb s. asid_of e = Some a})) a v = Miss"
  apply (subgoal_tac "tagged_entry_set (non_global_entries (sat_tlb s - {e \<in> sat_tlb s. asid_of e = Some a})) a v  = {}")
   apply (clarsimp simp: lookup_def )
  by (clarsimp simp: non_global_entries_def lookup_def tagged_entry_set_def entry_set_def split: if_split_asm)


lemma  flush_with_asid_asid_sat_incon_refine:
  "\<lbrakk> flush_with_ASID (FlushASID a) (s::'a sat_tlb_state_scheme) = ((), s') ;  flush_with_ASID (FlushASID a) (t::'b set_tlb_state_scheme) = ((), t'); 
         tlb_rel_abs (typ_sat_tlb s) (typ_set_tlb t) \<rbrakk> \<Longrightarrow> 
                  tlb_rel_abs (typ_sat_tlb s') (typ_set_tlb t')"
  apply (clarsimp simp: flush_with_ASID_sat_tlb_state_ext_def flush_with_ASID_set_tlb_state_ext_def 
      flush_tlb_asid_def split: if_split_asm)
   apply (clarsimp simp: tlb_rel_abs_def)
   apply (rule conjI)
    apply (cases s, cases t , clarsimp simp: state.defs)
   apply (rule conjI)
    apply (clarsimp simp: saturated_def)
   apply (rule conjI)
    apply (clarsimp simp: incon_addrs_def)
    apply (rule conjI)
     apply (clarsimp simp: inconsistent_vaddrs_def)
     apply (rename_tac v)
     apply (drule union_asid_tlb_incon_cases)
     apply (erule disjE, clarsimp simp: asid_tlb_lookup_range_pt_walk_not_incon)
     apply (erule disjE, clarsimp simp:)
      apply (subgoal_tac "lookup'' (sat_tlb s) (set_asid t) v = Hit x \<or> lookup'' (sat_tlb s) (set_asid t) v = Incon")
       prefer 2
  using lookup_asid_tlb_hit_incon_minus apply force
      apply (erule disjE)
       apply (subgoal_tac "the(pt_walk (set_asid t) (MEM s) (TTBR0 s) xb) = the(pt_walk (set_asid t) (MEM s) (TTBR0 s) v) \<and> 
                   \<not>is_fault (pt_walk (set_asid t) (MEM s) (TTBR0 s) v)")
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
      apply (subgoal_tac "lookup'' (sat_tlb s) (set_asid t) v = Incon")
       apply blast
  using lookup_asid_tlb_incon_minus apply force
     apply (erule disjE, clarsimp simp: asid_tlb_lookup_range_pt_walk_not_incon)
     apply (clarsimp simp:)
     apply (subgoal_tac "lookup'' (sat_tlb s) (set_asid t) v = Incon")
      apply blast
  using lookup_asid_tlb_incon_minus apply force
    apply (clarsimp simp: incoherrent_vaddrs_def)
    apply (rename_tac v x)
    apply (drule lookup_asid_tlb_hit_union_cases')
    apply (erule disjE, clarsimp)
     apply (subgoal_tac "lookup'' (sat_tlb s) (set_asid t) v = Hit x \<or> 
                                lookup'' (sat_tlb s) (set_asid t) v = Incon")
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
     apply (clarsimp simp: )
     apply (clarsimp simp: inconsistent_vaddrs_def)
     apply (rename_tac v)
     apply (drule union_asid_tlb_incon_cases)
     apply (erule disjE, clarsimp simp: asid_tlb_lookup_range_pt_walk_not_incon)
     apply (erule disjE, clarsimp simp: ) 
      apply (subgoal_tac "lookup'' (global_entries (sat_tlb s)) (set_asid t) v = Hit x")
       apply (subgoal_tac "x \<in> global_entries (sat_tlb s) \<and>  v \<in> range_of x")
        apply blast
  using lookup_asid_tlb_hit_entry_range lookup_in_asid_tlb apply force
  using lookup_sub_asid_of_hit_global apply force
     apply (erule disjE, clarsimp simp: asid_tlb_lookup_range_pt_walk_not_incon)
     apply (erule disjE, clarsimp simp: asid_tlb_lookup_range_pt_walk_not_incon)
      apply (subgoal_tac "lookup'' (global_entries (sat_tlb s)) (set_asid t) v = Incon")
       apply (clarsimp simp: lookup_def tagged_entry_set_def entry_set_def split: if_split_asm)
       apply blast
  using lookup_sub_asid_of_incon_global apply force
     apply (erule disjE, clarsimp simp: asid_tlb_lookup_range_pt_walk_not_incon)
     apply (clarsimp simp: )
     apply (subgoal_tac "lookup'' (global_entries (sat_tlb s)) (set_asid t) v = Incon")
      apply (clarsimp simp: lookup_def tagged_entry_set_def entry_set_def split: if_split_asm)
      apply blast
  using lookup_sub_asid_of_incon_global apply force
    apply (clarsimp simp: incoherrent_vaddrs_def)
    apply (rename_tac v x)
    apply (drule lookup_asid_tlb_hit_union_cases')
    apply (erule disjE, clarsimp)
     apply (subgoal_tac "lookup'' (global_entries (sat_tlb s)) (set_asid t) v = Hit x")
      apply (clarsimp simp: lookup_def tagged_entry_set_def entry_set_def split: if_split_asm)
      apply blast
  using lookup_sub_asid_of_hit_global apply force
    apply (erule disjE, clarsimp)
     apply (drule asid_tlb_lookup_miss_is_fault_intro, simp)
    apply (clarsimp)
    apply (subgoal_tac "lookup'' (global_entries (sat_tlb s)) (set_asid t) v = Hit x")
     apply (clarsimp simp: lookup_def tagged_entry_set_def entry_set_def split: if_split_asm)
     apply blast
  using lookup_sub_asid_of_hit_global apply force
   apply (rule conjI)
    apply (clarsimp simp: global_entries_union)
    apply (rule conjI)
     apply (clarsimp simp: global_entries_def) 
     apply blast
    apply (clarsimp simp: saturated_def global_entries_def) apply blast
   apply clarsimp
   apply (clarsimp simp: non_global_to_global [symmetric])
   apply (subgoal_tac "lookup'' (non_global_entries (sat_tlb s - {e \<in> sat_tlb s. asid_of e = Some (set_asid t)} \<union> the ` {e \<in> range (pt_walk (set_asid t) (MEM s) (TTBR0 s)). \<not> is_fault e})) aa v =
           lookup'' (non_global_entries (sat_tlb s)) aa v")
    apply clarsimp
   apply (rule asid_unequal_lookup_non_global_asid_flush_pt_walk, simp)
  apply (clarsimp simp: tlb_rel_abs_def)
  apply (rule conjI)
   apply (cases s, cases t , clarsimp simp: state.defs)
  apply (rule conjI)
   apply (clarsimp simp: saturated_def)
  apply (thin_tac "s' = s\<lparr>sat_tlb := sat_tlb s - {e \<in> sat_tlb s. asid_of e = Some a} \<union> the ` {e \<in> range (pt_walk (set_asid t) (MEM s) (TTBR0 s)). \<not> is_fault e}\<rparr>")
  apply (thin_tac "t' = t\<lparr>set_tlb := set_tlb t\<lparr>snapshot := (snapshot (set_tlb t))(a := ({}, Map.empty))\<rparr>\<rparr>")
  apply (rule conjI)
   apply (clarsimp simp: incon_addrs_def)
   apply (rule conjI)
    apply (clarsimp simp: inconsistent_vaddrs_def)
    apply (rename_tac v)
    apply (drule union_asid_tlb_incon_cases)
    apply (erule disjE, clarsimp simp: asid_tlb_lookup_range_pt_walk_not_incon)
    apply (erule disjE, clarsimp simp: )
     apply (subgoal_tac "lookup'' (sat_tlb s) (set_asid t) v = Hit x")
      prefer 2
      apply (rule_tac a = a  in asid_unequal_lookup_minus_non_global_hit_hit, simp, simp)
     apply (subgoal_tac "the (pt_walk (set_asid t) (MEM s) (TTBR0 s) xb) = the (pt_walk (set_asid t) (MEM s) (TTBR0 s) v) \<and> 
                      \<not>is_fault (pt_walk (set_asid t) (MEM s) (TTBR0 s) v)")
      apply (clarsimp)
      apply (frule saturatd_lookup_hit_no_fault, simp, simp, simp)
     apply (frule asid_tlb_lookup_range_fault_pt_walk')
     apply (drule_tac x = v in bspec) 
  using lookup_asid_tlb_hit_entry_range apply force
     apply clarsimp
    apply (erule disjE, clarsimp simp: asid_tlb_lookup_range_pt_walk_not_incon)
    apply (erule disjE, clarsimp simp:) 
     apply (subgoal_tac "lookup'' (sat_tlb s) (set_asid t) v = Incon")
      apply blast
  using lookup_asid_tlb_incon_minus apply force
    apply (erule disjE, clarsimp simp: asid_tlb_lookup_range_pt_walk_not_incon)
    apply clarsimp
    apply (subgoal_tac "lookup'' (sat_tlb s) (set_asid t) v = Incon")
     apply blast
  using lookup_asid_tlb_incon_minus apply force
   apply (clarsimp simp: incoherrent_vaddrs_def)
   apply (rename_tac v x)
   apply (drule lookup_asid_tlb_hit_union_cases')
   apply (erule disjE, clarsimp)
    apply (subgoal_tac "lookup'' (sat_tlb s) (set_asid t) v = Hit x")
     apply force
    apply (rule_tac a = a  in asid_unequal_lookup_minus_non_global_hit_hit, simp, simp)
   apply (erule disjE, clarsimp)
    apply (drule asid_tlb_lookup_miss_is_fault_intro, simp)
   apply clarsimp
   apply (drule asid_tlb_lookup_miss_is_fault_intro, simp)
  apply (rule conjI)
   apply (clarsimp simp: global_entries_union)
   apply (rule conjI)
    apply (clarsimp simp: global_entries_def) 
    apply blast
   apply (clarsimp simp: saturated_def global_entries_def) apply blast
  apply clarsimp
  apply (case_tac "aa = a"; clarsimp?)
   apply (clarsimp simp: non_global_to_global [symmetric])
   apply (subgoal_tac "lookup'' (non_global_entries (sat_tlb s - {e \<in> sat_tlb s. asid_of e = Some a} \<union> the ` {e \<in> range (pt_walk (set_asid t) (MEM s) (TTBR0 s)). \<not> is_fault e})) a v = Miss")
    apply clarsimp
   apply (clarsimp simp: non_global_entries_union)
   apply (subgoal_tac "lookup'' (non_global_entries (sat_tlb s - {e \<in> sat_tlb s. asid_of e = Some a})) a v = Miss")
    apply (subgoal_tac "lookup'' (non_global_entries (the ` {e \<in> range (pt_walk (set_asid t) (MEM s) (TTBR0 s)). \<not> is_fault e})) a v = Miss")
     apply (rule lookup_asid_tlb_miss_union_miss_miss, simp, simp)
    apply (rule asid_unequal_lookup_pt_walk_miss, simp)
   apply (rule lookup_non_global_entries_sub_miss)
  apply (clarsimp simp: non_global_to_global [symmetric])
  apply (subgoal_tac "lookup'' (non_global_entries (sat_tlb s - {e \<in> sat_tlb s. asid_of e = Some a} \<union> the ` {e \<in> range (pt_walk (set_asid t) (MEM s) (TTBR0 s)). \<not> is_fault e})) aa v =
                      lookup'' (non_global_entries (sat_tlb s)) aa v")
   apply (clarsimp simp: lookup_from'_def )
  apply (clarsimp simp: non_global_entries_union)
  apply (clarsimp simp: non_global_entries_sub)
  apply (subgoal_tac "lookup'' (non_global_entries {e \<in> sat_tlb s. asid_of e = Some a}) aa v = Miss")
   apply (subgoal_tac "lookup'' (non_global_entries (the ` {e \<in> range (pt_walk (set_asid t) (MEM s) (TTBR0 s)). \<not> is_fault e})) aa v = Miss")
    apply (rule lookup_asid_tlb_minus_union, simp, simp)
   apply (rule asid_unequal_lookup_pt_walk_miss, simp)
  apply (subgoal_tac "tagged_entry_set (non_global_entries {e \<in> sat_tlb s. asid_of e = Some a}) aa v = {}")
   apply (clarsimp simp: lookup_def)
  by (clarsimp simp: non_global_entries_def lookup_def tagged_entry_set_def entry_set_def split: if_split_asm)



lemma vaddr_elem_lookup_hit_global_entries_hit:
  "\<lbrakk> v \<in> vset ;  lookup'' (t - (\<Union>x\<in>vset. {e \<in> t. x \<in> range_of e \<and> asid_of e = Some a})) a v = Hit e\<rbrakk>  \<Longrightarrow>
     lookup' (global_entries t) v = Hit e"
  apply (case_tac " lookup' (global_entries t) v"; clarsimp?)
    apply (clarsimp simp: global_entries_def lookup_def tagged_entry_set_def entry_set_def split: if_split_asm option.splits)
    apply (safe ; force) [1]
   defer
   apply (clarsimp simp: global_entries_def lookup_def tagged_entry_set_def entry_set_def split: if_split_asm option.splits)
   apply (safe ; force) [1]
  apply (clarsimp simp: global_entries_def lookup_def tagged_entry_set_def entry_set_def split: if_split_asm option.splits)
  apply safe 
    apply force
   apply force
proof -
  fix x :: "8 word tlb_entry" and xa :: "8 word option tlb_entry"
  assume a1: "v \<in> vset"
  assume a2: "\<forall>x. {e \<in> t. asid_of e = None \<and> v \<in> range_of e} \<noteq> {x}"
  assume a3: "{e \<in> t. (e \<in> t \<longrightarrow> (\<forall>x\<in>vset. x \<notin> range_of e) \<or> asid_of e \<noteq> Some a) \<and> v \<in> range_of e \<and> (asid_of e = None \<or> asid_of e = Some a)} = {e}"
  assume "asid_of x \<noteq> Some a"
  assume "asid_of x = None"
  have "{ta \<in> t. (ta \<in> t \<longrightarrow> (\<forall>a. a \<in> vset \<longrightarrow> a \<notin> range_of ta) \<or> asid_of ta \<noteq> Some a) \<and> v \<in> range_of ta \<and> (asid_of ta = None \<or> asid_of ta = Some a)} \<noteq> {ta \<in> t. asid_of ta = None \<and> v \<in> range_of ta}"
    using a3 a2 by (metis (no_types))
  then show False
    using a1 by force
qed

  
  

lemma vaddr_elem_lookup_incon_global_entries_incon:
  "\<lbrakk> v \<in> vset ;  lookup'' (t - (\<Union>x\<in>vset. {e \<in> t. x \<in> range_of e \<and> asid_of e = Some a})) a v = Incon\<rbrakk>  \<Longrightarrow>
     lookup' (global_entries t) v = Incon"
  apply (case_tac " lookup' (global_entries t) v"; clarsimp?)
    apply (clarsimp simp: global_entries_def lookup_def tagged_entry_set_def entry_set_def split: if_split_asm option.splits)
    apply (safe ; force) [1]
   defer
   apply (clarsimp simp: global_entries_def lookup_def tagged_entry_set_def entry_set_def split: if_split_asm option.splits)
  by (safe ; force) [1]
 


lemma  flush_with_asid_asid_varange_sat_incon_refine:
  "\<lbrakk>flush_with_ASID (FlushASIDvarange a vset) (s::'a sat_tlb_state_scheme) = ((), s') ;  flush_with_ASID (FlushASIDvarange a vset) (t::'b set_tlb_state_scheme) = ((), t'); 
         tlb_rel_abs (typ_sat_tlb s) (typ_set_tlb t) \<rbrakk> \<Longrightarrow> 
                  tlb_rel_abs (typ_sat_tlb s') (typ_set_tlb t')"
  apply (clarsimp simp: flush_with_ASID_sat_tlb_state_ext_def flush_with_ASID_set_tlb_state_ext_def flush_tlb_a_vset_def Let_def split: if_split_asm)
   apply (clarsimp simp: tlb_rel_abs_def)
   apply (rule conjI)
    apply (cases s, cases t , clarsimp simp: state.defs)
   apply (rule conjI)
    apply (clarsimp simp: saturated_def)
   apply (rule conjI)
    apply (clarsimp simp: incon_addrs_def)
    apply (rule conjI)
     apply (clarsimp simp: inconsistent_vaddrs_def)
     apply (rename_tac v)
     apply (rule conjI)
      apply (drule union_asid_tlb_incon_cases)
      apply (erule disjE, clarsimp simp: asid_tlb_lookup_range_pt_walk_not_incon)
      apply (erule disjE, clarsimp simp: )
       apply (subgoal_tac " lookup'' (sat_tlb s ) (set_asid t) v = Hit x \<or> 
                        lookup'' (sat_tlb s ) (set_asid t) v = Incon")
        prefer 2
  using lookup_asid_tlb_hit_incon_minus apply force
       apply (erule_tac P = "lookup'' (sat_tlb s ) (set_asid t) v = Hit x " in disjE)
        prefer 2
        apply blast
       apply (subgoal_tac "the(pt_walk (set_asid t) (MEM s) (TTBR0 s) xb) = the(pt_walk (set_asid t) (MEM s) (TTBR0 s) v) \<and> 
                   \<not>is_fault (pt_walk (set_asid t) (MEM s) (TTBR0 s) v)")
        prefer 2
        apply (frule asid_tlb_lookup_range_fault_pt_walk')
        apply (drule_tac x = v in bspec) 
  using lookup_asid_tlb_hit_entry_range apply force
        apply clarsimp
       apply clarsimp
       apply (drule_tac b = v and x = x in saturatd_lookup_hit_no_fault; simp)
      apply (erule disjE, clarsimp simp: asid_tlb_lookup_range_pt_walk_not_incon)
      apply (erule disjE, clarsimp simp: )
       apply (subgoal_tac "lookup'' (sat_tlb s) (set_asid t) v = Incon")
        apply blast
  using lookup_asid_tlb_incon_minus apply force
      apply (erule disjE, clarsimp simp: asid_tlb_lookup_range_pt_walk_not_incon)
      apply (clarsimp simp: )
      apply (subgoal_tac "lookup'' (sat_tlb s) (set_asid t) v = Incon")
       apply blast
  using lookup_asid_tlb_incon_minus apply force
     apply clarsimp
     apply (drule union_asid_tlb_incon_cases)
     apply (erule disjE, clarsimp simp: asid_tlb_lookup_range_pt_walk_not_incon)
     apply (erule disjE, clarsimp simp: )
       apply (subgoal_tac "lookup' (global_entries (sat_tlb s))  v = Hit x")
         apply (clarsimp simp: lookup_def entry_set_def split: if_split_asm) apply force
      apply (rule_tac vset = vset in  vaddr_elem_lookup_hit_global_entries_hit, simp, simp)
     apply (erule disjE, clarsimp simp: asid_tlb_lookup_range_pt_walk_not_incon)
     apply (erule disjE, clarsimp simp:)
      apply (subgoal_tac "lookup' (global_entries (sat_tlb s))  v = Incon")
       apply (clarsimp simp: lookup_def entry_set_def split: if_split_asm)
       apply force
      apply (rule_tac vset = vset in  vaddr_elem_lookup_incon_global_entries_incon, simp, simp)
     apply (erule disjE, clarsimp simp: asid_tlb_lookup_range_pt_walk_not_incon)
     apply (clarsimp simp:)
     apply (subgoal_tac "lookup' (global_entries (sat_tlb s))  v = Incon")
      apply (clarsimp simp: lookup_def entry_set_def split: if_split_asm)
      apply force
     apply (rule_tac vset = vset in  vaddr_elem_lookup_incon_global_entries_incon, simp, simp)
    apply (clarsimp simp: incoherrent_vaddrs_def)
  apply (rename_tac v x)
    apply (rule conjI)
     apply (drule lookup_asid_tlb_hit_union_cases')
     apply (erule disjE, clarsimp)
      apply (case_tac "lookup'' (sat_tlb s) (set_asid t) v"; clarsimp?)
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
       apply (subgoal_tac "lookup' (global_entries (sat_tlb s))  v = Hit x")  
       apply (clarsimp simp: lookup_def entry_set_def split: if_split_asm) apply force
     apply (rule_tac vset = vset in  vaddr_elem_lookup_hit_global_entries_hit, simp, simp)
    apply (erule disjE, clarsimp)
     apply (drule asid_tlb_lookup_miss_is_fault_intro, clarsimp)
    apply (drule asid_tlb_lookup_miss_is_fault_intro, clarsimp)
   apply (rule conjI)
    apply (clarsimp simp: global_entries_union)
    apply (rule conjI)
     apply (clarsimp simp: global_entries_def) 
     apply blast
    apply (clarsimp simp: saturated_def global_entries_def) apply blast
   apply clarsimp
   apply (clarsimp simp: non_global_to_global [symmetric] non_global_entries_union)
   apply (subgoal_tac "lookup'' (non_global_entries (the ` {e \<in> range (pt_walk (set_asid t) (MEM s) (TTBR0 s)). \<not> is_fault e})) aa v = Miss")
  apply (subgoal_tac "lookup''
            (non_global_entries (sat_tlb s - (\<Union>x\<in>vset. {e \<in> sat_tlb s. x \<in> range_of e \<and> asid_of e = Some (set_asid t)})) \<union> non_global_entries (the ` {e \<in> range (pt_walk (set_asid t) (MEM s) (TTBR0 s)). \<not> is_fault e})) aa v =
   lookup''
            (non_global_entries (sat_tlb s - (\<Union>x\<in>vset. {e \<in> sat_tlb s. x \<in> range_of e \<and> asid_of e = Some (set_asid t)}))) aa v")
  prefer 2
  using lookup_asid_tlb_miss_union_equal 
      apply auto[1]
  apply clarsimp
  apply (subgoal_tac "lookup'' (non_global_entries (sat_tlb s - (\<Union>x\<in>vset. {e \<in> sat_tlb s. x \<in> range_of e \<and> asid_of e = Some (set_asid t)}))) aa v \<le> 
                       lookup'' (non_global_entries (sat_tlb s))  aa v")
  using order_trans apply force
    apply (rule asid_tlb_mono)
    apply (clarsimp simp: non_global_entries_def)
   apply (rule asid_unequal_lookup_pt_walk_miss, simp)
  apply (clarsimp simp: tlb_rel_abs_def)
  apply (rule conjI)
   apply (cases s, cases t , clarsimp simp: state.defs)
  apply (rule conjI)
   apply (clarsimp simp: saturated_def)
  apply (rule conjI)
    apply (thin_tac "s' = s\<lparr>sat_tlb := sat_tlb s - (\<Union>v\<in>vset. {e \<in> sat_tlb s. v \<in> range_of e \<and> asid_of e = Some a}) \<union> the ` {e \<in> range (pt_walk (set_asid t) (MEM s) (TTBR0 s)). \<not> is_fault e}\<rparr>")
    apply (thin_tac "t' = t\<lparr>set_tlb := set_tlb t\<lparr>snapshot := \<lambda>a'. if a' = a then (fst (snapshot (set_tlb t) a) - vset, \<lambda>v. if v \<in> vset then None else snd (snapshot (set_tlb t) a) v) else snapshot (set_tlb t) a'\<rparr>\<rparr>")
    apply (clarsimp simp: incon_addrs_def)
    apply (rule conjI)
     apply (clarsimp simp: inconsistent_vaddrs_def)
     apply (rename_tac v)
      apply (drule union_asid_tlb_incon_cases)
      apply (erule disjE, clarsimp simp: asid_tlb_lookup_range_pt_walk_not_incon)
      apply (erule disjE, clarsimp simp: )
     apply (subgoal_tac "lookup'' (sat_tlb s) (set_asid t) v = Hit x")
      prefer 2
      apply (subgoal_tac "lookup'' (\<Union>v\<in>vset. {e \<in> sat_tlb s. v \<in> range_of e \<and> asid_of e = Some a}) (set_asid t) v = Miss")
       apply (drule lookup_asid_tlb_minus_hit', simp, simp)
      apply (subgoal_tac "tagged_entry_set (\<Union>v\<in>vset. {e \<in> sat_tlb s. v \<in> range_of e \<and> asid_of e = Some a}) (set_asid t) v = {}")
       apply (clarsimp simp: lookup_def)
      apply (clarsimp simp: lookup_def tagged_entry_set_def entry_set_def split: if_split_asm option.splits)
     apply (subgoal_tac "the(pt_walk (set_asid t) (MEM s) (TTBR0 s) xb) = the(pt_walk (set_asid t) (MEM s) (TTBR0 s) v) \<and> 
                   \<not>is_fault (pt_walk (set_asid t) (MEM s) (TTBR0 s) v)")
      prefer 2
      apply (frule asid_tlb_lookup_range_fault_pt_walk')
      apply (drule_tac x = v in bspec) 
  using lookup_asid_tlb_hit_entry_range apply force
      apply clarsimp
     apply clarsimp
     apply (drule_tac b = v and x = x in saturatd_lookup_hit_no_fault; simp)
    apply (erule disjE, clarsimp simp: asid_tlb_lookup_range_pt_walk_not_incon)
    apply (erule disjE, clarsimp)
     apply (subgoal_tac "lookup'' (sat_tlb s) (set_asid t) v = Incon")
      apply blast
  using lookup_asid_tlb_incon_minus apply force
    apply (erule disjE, clarsimp simp: asid_tlb_lookup_range_pt_walk_not_incon)
    apply (subgoal_tac "lookup'' (sat_tlb s) (set_asid t) v = Incon")
     apply blast
  using lookup_asid_tlb_incon_minus apply force
   apply (clarsimp simp: incoherrent_vaddrs_def)
   apply (rename_tac v x)
   apply (drule lookup_asid_tlb_hit_union_cases')
   apply (erule disjE, clarsimp)
    apply (subgoal_tac "lookup'' (sat_tlb s) (set_asid t) v = Hit x")
     apply force
    apply (subgoal_tac "lookup'' (\<Union>v\<in>vset. {e \<in> sat_tlb s. v \<in> range_of e \<and> asid_of e = Some a}) (set_asid t) v = Miss")
     apply (drule lookup_asid_tlb_minus_hit', simp, simp)
    apply (subgoal_tac "tagged_entry_set (\<Union>v\<in>vset. {e \<in> sat_tlb s. v \<in> range_of e \<and> asid_of e = Some a}) (set_asid t) v = {}")
     apply (clarsimp simp: lookup_def)
    apply (clarsimp simp: lookup_def tagged_entry_set_def entry_set_def split: if_split_asm option.splits)
   apply (erule disjE, clarsimp)
    apply (drule asid_tlb_lookup_miss_is_fault_intro, simp)
   apply (drule asid_tlb_lookup_miss_is_fault_intro, simp)
  apply (rule conjI)
   apply (clarsimp simp: global_entries_union)
   apply (rule conjI)
    apply (clarsimp simp: global_entries_def) 
    apply blast
   apply (clarsimp simp: saturated_def global_entries_def) apply blast
  apply (clarsimp)
  apply (clarsimp simp: non_global_to_global [symmetric] non_global_entries_union)
  apply (case_tac "aa \<noteq> a"; clarsimp?)
   apply (subgoal_tac "lookup'' (non_global_entries (sat_tlb s - (\<Union>v\<in>vset. {e \<in> sat_tlb s. v \<in> range_of e \<and> asid_of e = Some a})) \<union> 
                          non_global_entries (the ` {e \<in> range (pt_walk (set_asid t) (MEM s) (TTBR0 s)). \<not> is_fault e})) aa v =
                       lookup'' (non_global_entries (sat_tlb s)) aa v")
    apply (clarsimp simp: lookup_from'_def)
   apply (clarsimp simp: non_global_entries_sub)
   apply (subgoal_tac "lookup'' (non_global_entries (\<Union>v\<in>vset. {e \<in> sat_tlb s. v \<in> range_of e \<and> asid_of e = Some a}))      aa v = Miss")
    apply (subgoal_tac "lookup'' (non_global_entries (the ` {e \<in> range (pt_walk (set_asid t) (MEM s) (TTBR0 s)). \<not> is_fault e}))      aa v = Miss")
  using lookup_asid_tlb_minus_union apply force
    apply (rule asid_unequal_lookup_pt_walk_miss, simp)
   apply (subgoal_tac "tagged_entry_set (non_global_entries (\<Union>v\<in>vset. {e \<in> sat_tlb s. v \<in> range_of e \<and> asid_of e = Some a})) aa v = {}")
    apply (clarsimp simp: lookup_def)
   apply (clarsimp simp: non_global_entries_def lookup_def tagged_entry_set_def entry_set_def split: if_split_asm option.splits)
  apply (subgoal_tac "lookup'' (non_global_entries (the ` {e \<in> range (pt_walk (set_asid t) (MEM s) (TTBR0 s)). \<not> is_fault e})) a v = Miss")
  prefer 2
 apply (rule asid_unequal_lookup_pt_walk_miss, simp)
  apply (subgoal_tac "lookup'' (non_global_entries (sat_tlb s - (\<Union>v\<in>vset. {e \<in> sat_tlb s. v \<in> range_of e \<and> asid_of e = Some a})) \<union> non_global_entries (the ` {e \<in> range (pt_walk (set_asid t) (MEM s) (TTBR0 s)). \<not> is_fault e})) a v =
   lookup'' (non_global_entries (sat_tlb s - (\<Union>v\<in>vset. {e \<in> sat_tlb s. v \<in> range_of e \<and> asid_of e = Some a}))) a v")
   prefer 2
  using lookup_asid_tlb_miss_union_equal apply force
  apply clarsimp
  apply (thin_tac "lookup'' (non_global_entries (sat_tlb s - (\<Union>v\<in>vset. {e \<in> sat_tlb s. v \<in> range_of e \<and> asid_of e = Some a})) \<union> non_global_entries (the ` {e \<in> range (pt_walk (set_asid t) (MEM s) (TTBR0 s)). \<not> is_fault e})) a v =
                   lookup'' (non_global_entries (sat_tlb s - (\<Union>v\<in>vset. {e \<in> sat_tlb s. v \<in> range_of e \<and> asid_of e = Some a}))) a v")

  apply (drule_tac x = a in spec, simp, drule_tac x = v in spec)
  apply (case_tac "lookup'' (non_global_entries (sat_tlb s)) a v"; clarsimp)
    apply (subgoal_tac "lookup'' (non_global_entries (sat_tlb s - (\<Union>v\<in>vset. {e \<in> sat_tlb s. v \<in> range_of e \<and> asid_of e = Some a}))) a v = Miss")
     apply force
    apply (clarsimp simp: non_global_entries_sub)
  using lookup_miss_minus_miss 
     apply blast
  apply (case_tac "v \<in> vset")
  apply (subgoal_tac "lookup_from' (\<lambda>a'. if a' = a then (fst (snapshot (set_tlb t) a) - vset, \<lambda>v. if v \<in> vset then None else snd (snapshot (set_tlb t) a) v) else snapshot (set_tlb t) a') a v = Miss")
  prefer 2
     apply (clarsimp simp:  lookup_from'_def snap_conv'_def split: if_split_asm option.splits)
    apply (clarsimp)
    apply (thin_tac "lookup_from' (\<lambda>a'. if a' = a then (fst (snapshot (set_tlb t) a) - vset, \<lambda>v. if v \<in> vset then None else snd (snapshot (set_tlb t) a) v) else snapshot (set_tlb t) a') a v = Miss")
    apply (subgoal_tac "tagged_entry_set (non_global_entries (sat_tlb s - (\<Union>v\<in>vset. {e \<in> sat_tlb s. v \<in> range_of e \<and> asid_of e = Some a}))) a v = {}")
     apply (clarsimp simp: lookup_def)
    apply (clarsimp simp: non_global_entries_def lookup_def tagged_entry_set_def entry_set_def split: if_split_asm option.splits)
   apply (subgoal_tac "lookup_from' (\<lambda>a'. if a' = a then (fst (snapshot (set_tlb t) a) - vset, \<lambda>v. if v \<in> vset then None else snd (snapshot (set_tlb t) a) v) else snapshot (set_tlb t) a') a v = Incon")
    apply force
   apply (clarsimp simp:  lookup_from'_def snap_conv'_def split: if_split_asm option.splits)
  apply (case_tac "v \<in> vset")
   apply (subgoal_tac "lookup'' (non_global_entries (sat_tlb s - (\<Union>v\<in>vset. {e \<in> sat_tlb s. v \<in> range_of e \<and> asid_of e = Some a}))) a v = Miss")
    apply force
   apply (subgoal_tac "tagged_entry_set (non_global_entries (sat_tlb s - (\<Union>v\<in>vset. {e \<in> sat_tlb s. v \<in> range_of e \<and> asid_of e = Some a}))) a v = {}")
    apply (clarsimp simp: lookup_def)
   apply (clarsimp simp: non_global_entries_def lookup_def tagged_entry_set_def entry_set_def split: if_split_asm option.splits)
  apply (subgoal_tac "lookup_from' (\<lambda>a'. if a' = a then (fst (snapshot (set_tlb t) a) - vset, \<lambda>v. if v \<in> vset then None else snd (snapshot (set_tlb t) a) v) else snapshot (set_tlb t) a') a v =
    lookup_from' (snapshot (set_tlb t)) a v")
  prefer 2
   apply (clarsimp simp:  lookup_from'_def snap_conv'_def split: if_split_asm option.splits)
  apply clarsimp
  apply (case_tac "lookup_from' (snapshot (set_tlb t)) a v"; clarsimp?)
  apply (clarsimp simp: non_global_entries_sub)
  apply (subgoal_tac "lookup'' (non_global_entries (sat_tlb s) - non_global_entries (\<Union>v\<in>vset. {e \<in> sat_tlb s. v \<in> range_of e \<and> asid_of e = Some a})) a v = Miss \<or> 
       lookup'' (non_global_entries (sat_tlb s) - non_global_entries (\<Union>v\<in>vset. {e \<in> sat_tlb s. v \<in> range_of e \<and> asid_of e = Some a})) a v =  Hit x3a ")
   apply (erule disjE)
    apply clarsimp
   apply clarsimp
  by (rule lookup_miss_minus_miss_hit, simp)


lemma  flush_with_asid_sat_incon_refine:
  "\<lbrakk> flush_with_ASID f (s::'a sat_tlb_state_scheme) = ((), s') ;  flush_with_ASID f (t::'b set_tlb_state_scheme) = ((), t'); 
         tlb_rel_abs (typ_sat_tlb s) (typ_set_tlb t) \<rbrakk> \<Longrightarrow> 
                  tlb_rel_abs (typ_sat_tlb s') (typ_set_tlb t')"
  by (cases f; clarsimp simp: flush_with_asid_asid_sat_incon_refine flush_with_asid_asid_varange_sat_incon_refine)


end