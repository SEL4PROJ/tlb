theory ARMv7A_Update_ASID_Ref


imports  ARMv7A_Update_TTBR0_Ref

begin  




lemma  update_asid_non_det_sat_refine:
  "\<lbrakk> update_ASID a (s::'a non_det_tlb_state_scheme) = ((), s') ;  update_ASID a (t::'b sat_tlb_state_scheme) = ((), t'); 
         tlb_rel_sat (typ_non_det_tlb s) (typ_sat_tlb t) \<rbrakk> \<Longrightarrow> 
                  tlb_rel_sat (typ_non_det_tlb s') (typ_sat_tlb t')"
  apply (clarsimp simp: update_ASID_non_det_tlb_state_ext_def update_ASID_sat_tlb_state_ext_def)
  apply (clarsimp simp: tlb_rel_sat_def saturated_def)
  apply (cases s, cases t , clarsimp simp: state.defs pairsub_def, force)
  done



lemma asid_unequal_snp_upd_equal' [simp]:
  "a \<noteq> a' \<Longrightarrow>   snp_upd_cur' snp ist m r a' a = snp a"
  by (clarsimp simp: snp_upd_cur'_def)



lemma saturated_global_subset_lookup_tlb_un_eq:
  "saturated (typ_sat_tlb s) \<Longrightarrow> 
        lookup''(global_entries (fst(sat_tlb s)) \<union> 
                 global_entries (the ` {e \<in> range (pt_walk a (MEM s) (TTBR0 s)). \<not> is_fault e}))  a v = 
                 lookup'' (global_entries (fst(sat_tlb s))) a v"
  apply (rule tlb_subset_lookup_un_eq)
  apply (subgoal_tac "global_entries (the ` {e \<in> range (pt_walk a (MEM s) (TTBR0 s)). \<not> is_fault e}) = 
                       global_entries (the ` {e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e})")
   apply (simp only:)
   apply (clarsimp simp: saturated_def global_entries_def) apply blast
  by (rule global_entries_ptable_same)



lemma saturated_global_subset_lookup_pdc_un_eq:
  "saturated (typ_sat_tlb s) \<Longrightarrow> 
        lookup_pdc (global_entries_pdc (snd(sat_tlb s)) \<union> 
                 global_entries_pdc (the ` {e \<in> range (pdc_walk a (MEM s) (TTBR0 s)). \<not> is_fault e}))  a v = 
                 lookup_pdc (global_entries_pdc (snd(sat_tlb s))) a v"
  apply (rule pdc_subset_lookup_un_eq)
  apply (subgoal_tac "global_entries_pdc (the ` {e \<in> range (pdc_walk a (MEM s) (TTBR0 s)). \<not> is_fault e}) = 
                       global_entries_pdc (the ` {e \<in> range (pdc_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e})")
   apply (simp only:)
   apply (clarsimp simp: saturated_def global_entries_pdc_def) apply blast
  by (rule global_entries_pdc_ptable_same)



lemma  update_asid_sat_incon_refine:
  "\<lbrakk> update_ASID a (s::'a sat_tlb_state_scheme) = ((), s') ;  update_ASID a (t::'b set_tlb_state_scheme) = ((), t'); 
         tlb_rel_abs (typ_sat_tlb s) (typ_set_tlb t) \<rbrakk> \<Longrightarrow> 
                  tlb_rel_abs (typ_sat_tlb s') (typ_set_tlb t')"
  apply (clarsimp simp: update_ASID_sat_tlb_state_ext_def update_ASID_set_tlb_state_ext_def Let_def)
  apply (frule tlb_rel_absD)
  apply (case_tac "a = ASID s")
    (* to the same ASID *)
   apply (subgoal_tac "sat_tlb s = pairunion (sat_tlb s)
           (the ` {e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e}, the ` {e \<in> range (pdc_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e})")
    prefer 2
    apply (clarsimp simp:  saturated_def) 
   apply (clarsimp simp: tlb_rel_abs_def)
   apply (rule conjI)
    apply (clarsimp simp: state.defs)
   apply (rule conjI)
    apply clarsimp
    apply (clarsimp simp:  snp_upd_cur'_def snp_upd_cur_def )
    apply (cases t, cases s, clarsimp) apply force
   apply clarsimp
   apply (clarsimp simp: lookup_from'_def snap_conv'_def snp_upd_cur'_def snp_upd_cur_def)
    (* to new asid *)
  apply (clarsimp simp: tlb_rel_abs_def)
  apply (rule conjI)
   apply (clarsimp simp: state.defs)
  apply (rule conjI)
   apply (clarsimp simp: saturated_def)
  apply (thin_tac "s' = s \<lparr>ASID := a,    sat_tlb :=  pairunion (sat_tlb s)
                  (the ` {e \<in> range (pt_walk a (MEM s) (TTBR0 s)). \<not> is_fault e}, the ` {e \<in> range (pdc_walk a (MEM s) (TTBR0 s)). \<not> is_fault e})\<rparr>")
  apply (thin_tac "t' = t
     \<lparr>ASID := a,
        set_tlb := set_tlb t
          \<lparr>snapshot := snp_upd_cur' (snapshot (set_tlb t)) (iset (set_tlb t)) (MEM s) (TTBR0 s) (ASID s),
             iset := fst (snapshot (set_tlb t) a) \<union> iset (set_tlb t) \<inter> global_set (set_tlb t) \<union> ptable_comp (snd (snapshot (set_tlb t) a)) (pt_walk_pair a (MEM s) (TTBR0 s))\<rparr>\<rparr>")
  apply (rule conjI)
   apply (clarsimp simp: incon_addrs_def)
   apply (rule conjI)
    apply (clarsimp simp: inconsistent_vaddrs_def)
    apply (rule conjI)
     apply (clarsimp)
     apply (rename_tac v)
     apply (subgoal_tac "fst(sat_tlb s) \<union> the ` {e \<in> range (pt_walk a (MEM s) (TTBR0 s)). \<not> is_fault e} =  (non_global_entries (fst(sat_tlb s)) \<union> non_global_entries (the ` {e \<in> range (pt_walk a (MEM s) (TTBR0 s)). \<not> is_fault e})) \<union>  
                          (global_entries (fst(sat_tlb s)) \<union> global_entries (the ` {e \<in> range (pt_walk a (MEM s) (TTBR0 s)). \<not> is_fault e}))")
      apply (simp only:)
      apply (thin_tac "fst(sat_tlb s) \<union> the ` {e \<in> range (pt_walk a (MEM s) (TTBR0 s)). \<not> is_fault e} =  (non_global_entries (fst(sat_tlb s)) \<union> non_global_entries (the ` {e \<in> range (pt_walk a (MEM s) (TTBR0 s)). \<not> is_fault e})) \<union>  
                          (global_entries (fst(sat_tlb s)) \<union> global_entries (the ` {e \<in> range (pt_walk a (MEM s) (TTBR0 s)). \<not> is_fault e}))")
      apply (subgoal_tac "lookup''   (global_entries (fst(sat_tlb s)))  a v = lookup'' (global_entries (fst(sat_tlb s)) \<union>  global_entries (the ` {e \<in> range (pt_walk a (MEM s) (TTBR0 s)). \<not> is_fault e})) a v ")
       prefer 2
       apply (rule saturated_global_subset_lookup_tlb_un_eq[symmetric], simp)
      apply (drule_tac t = "non_global_entries (fst(sat_tlb s)) \<union> non_global_entries (the ` {e \<in> range (pt_walk a (MEM s) (TTBR0 s)). \<not> is_fault e})" in union_asid_tlb_incon_cases)
      apply (erule disjE, clarsimp)
       apply (thin_tac "lookup'' (global_entries (fst(sat_tlb s)) \<union> global_entries (the ` {e \<in> range (pt_walk a (MEM s) (TTBR0 s)). \<not> is_fault e}))
                       a v =  Incon")
       apply (subgoal_tac "v \<in> iset (set_tlb t)")
        apply (subgoal_tac "v \<in> global_set (set_tlb t)")
         apply blast
        apply (clarsimp simp: global_entries_def lookup_def tagged_entry_set_def entry_set_def global_range_def split: if_split_asm option.splits)
        apply blast
       apply (drule_tac a' = "ASID s" in lookup_global_incon_incon)
       apply blast
      apply (erule disjE, clarsimp)
       apply (thin_tac "lookup'' (global_entries (fst(sat_tlb s)) \<union> global_entries (the ` {e \<in> range (pt_walk a (MEM s) (TTBR0 s)). \<not> is_fault e})) a v = Hit xa") 
       apply (case_tac "v \<in> global_set (set_tlb t)")
        apply (case_tac "v \<in> iset (set_tlb t)")
         apply blast
        apply clarsimp
        apply (subgoal_tac "lookup''  (fst(sat_tlb s)) (ASID s) v = Hit xa \<or> 
                           lookup''  (fst(sat_tlb s)) (ASID s) v = Incon")
         apply (erule_tac P = "lookup''  (fst(sat_tlb s)) (ASID s) v = Hit xa" in disjE)
          apply (case_tac "is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) v)")
           apply (clarsimp simp: incoherrent_vaddrs_def)
           apply force
          apply (drule  lookup_asid_tlb_hit_union_cases')
          apply (erule disjE, clarsimp)
           apply (subgoal_tac "asid_of (the (pt_walk a (MEM s) (TTBR0 s) v)) = None")
            apply (drule_tac x = a in spec, simp, drule_tac x = v in spec)
            apply (clarsimp simp: non_global_to_global [symmetric])
            apply (case_tac "fst(lookup_from' (snapshot (set_tlb t)) a v)"; clarsimp?)
             apply (clarsimp simp: lookup_from'_def snap_conv'_def split: pt_walk_typ.splits if_split_asm option.splits)
            apply (drule_tac a' = a in no_fault_pt_walk_unequal_asid')
            apply (frule non_fault_pt_walk_full_walk)
            apply (subgoal_tac "the (pt_walk a (MEM s) (TTBR0 s) v) \<noteq> x3")
             apply (clarsimp simp: lookup_from'_def snap_conv'_def split: pt_walk_typ.splits if_split_asm option.splits)
             apply (clarsimp simp: ptable_comp_def is_fault_def entry_leq_def)
            apply (subgoal_tac "asid_of x3 \<noteq> None")
             apply force
            apply (drule lookup_non_global_hit_asid_of_not_none, simp)
           apply (drule lookup_non_global_miss_non_fault)
            apply (frule_tac a' = a in no_fault_pt_walk_unequal_asid', simp)
           apply (rule_tac v = v and a = a and t = "(the ` {e \<in> range (pt_walk a (MEM s) (TTBR0 s)). \<not> is_fault e})" in lookup_global_hit_asid_of_none, simp)
          apply (erule disjE, clarsimp)
           apply (subgoal_tac "xa \<noteq> the (pt_walk (ASID t) (MEM s) (TTBR0 s) v)")
            apply (drule_tac b = v and x = xa in saturatd_lookup_hit_no_fault; simp?)
           apply (subgoal_tac "asid_of xa = None")
            apply (subgoal_tac "asid_of (the (pt_walk (ASID t) (MEM s) (TTBR0 s) v)) \<noteq> None")
             apply force
            apply (subgoal_tac "lookup'' (non_global_entries (the ` {e \<in> range (pt_walk (ASID t) (MEM s) (TTBR0 s)). \<not> is_fault e})) (ASID t) v = Hit 
                              (the (pt_walk (ASID t) (MEM s) (TTBR0 s) v))")
             apply (rule lookup_non_global_hit_asid_of_not_none, simp)
            apply (rule_tac a = a in non_global_lookup_hit_asid, simp)
           apply (rule lookup_global_hit_asid_of_none, simp)
          apply (clarsimp)
          apply (subgoal_tac "xa \<noteq> the (pt_walk (ASID t) (MEM s) (TTBR0 s) v)")
           apply (drule_tac b = v and x = xa in saturatd_lookup_hit_no_fault; simp?)
          apply (subgoal_tac "asid_of xa = None")
           apply (subgoal_tac "asid_of (the (pt_walk (ASID t) (MEM s) (TTBR0 s) v)) \<noteq> None")
            apply force
           apply (subgoal_tac "lookup'' (non_global_entries (the ` {e \<in> range (pt_walk (ASID t) (MEM s) (TTBR0 s)). \<not> is_fault e})) (ASID t) v = Hit 
                              (the (pt_walk (ASID t) (MEM s) (TTBR0 s) v))")
            apply (rule lookup_non_global_hit_asid_of_not_none, simp)
           apply (rule_tac a = a in non_global_lookup_hit_asid, simp)
          apply (rule lookup_global_hit_asid_of_none, simp)
         apply blast
        apply (metis (no_types, hide_lams) lookup_global_hit_order lookup_global_same_for_asids)
       apply (subgoal_tac "xa \<in> global_entries (fst(sat_tlb s))")
        apply (subgoal_tac "v \<in> range_of xa")
         apply (clarsimp simp: global_range_def)
         apply blast
        apply (simp add: lookup_asid_tlb_hit_entry_range)
  using lookup_in_asid_tlb apply auto[1]
      apply (erule disjE, clarsimp)
       apply (thin_tac "lookup'' (global_entries (fst(sat_tlb s)) \<union> global_entries (the ` {e \<in> range (pt_walk a (MEM s) (TTBR0 s)). \<not> is_fault e}))
                       a v =  Incon")
       apply (subgoal_tac "v \<in> iset (set_tlb t)")
        apply (subgoal_tac "v \<in> global_set (set_tlb t)")
         apply blast
        apply (clarsimp simp: global_entries_def lookup_def tagged_entry_set_def entry_set_def global_range_def split: if_split_asm option.splits)
        apply blast
       apply (drule_tac a' = "ASID s" in lookup_global_incon_incon)
       apply blast
      apply (erule disjE, clarsimp)
       apply (thin_tac "lookup'' (global_entries (fst(sat_tlb s)) \<union>  global_entries (the ` {e \<in> range (pt_walk a (MEM s) (TTBR0 s)). \<not> is_fault e}))a v = Hit x")
       apply (drule union_asid_tlb_incon_cases)
       apply (erule disjE, clarsimp simp: )
  using non_global_lookup_range_pt_walk_not_incon apply force
       apply (erule disjE, clarsimp simp: )
        apply (drule_tac x = a in spec, simp, drule_tac x = v in spec)
        apply (clarsimp simp: non_global_to_global [symmetric])
        apply (case_tac "fst(lookup_from' (snapshot (set_tlb t)) a v)"; clarsimp?)
         apply (clarsimp simp: lookup_from'_def snap_conv'_def split: pt_walk_typ.splits if_split_asm option.splits)
        apply (subgoal_tac "\<not>is_fault (pt_walk a (MEM s) (TTBR0 s) v)")
         apply (subgoal_tac "xb = the (pt_walk a (MEM s) (TTBR0 s) v)")
          apply (clarsimp simp: lookup_from'_def snap_conv'_def split: pt_walk_typ.splits if_split_asm option.splits)
          apply (clarsimp simp: ptable_comp_def is_fault_def entry_leq_def) 
          apply (metis pt_walk_new_no_fault_pt_walk' option.inject) 
         apply (frule_tac a' = a in non_global_lookup_hit_asid, simp)
        apply (rule non_global_hit_no_fault, simp)
       apply (erule disjE, clarsimp simp: )
  using non_global_lookup_range_pt_walk_not_incon apply force 
       apply (erule disjE, clarsimp simp: )
        apply (drule_tac x = a in spec, simp, drule_tac x = v in spec)
        apply (clarsimp simp: non_global_to_global [symmetric])
        apply (clarsimp simp: lookup_from'_def snap_conv'_def split: pt_walk_typ.splits if_split_asm option.splits)
       apply (erule disjE, clarsimp simp: )
  using non_global_lookup_range_pt_walk_not_incon apply force
       apply (clarsimp simp: )
       apply (drule_tac x = a in spec, simp, drule_tac x = v in spec)
       apply (clarsimp simp: non_global_to_global [symmetric])
       apply (clarsimp simp: lookup_from'_def snap_conv'_def split: pt_walk_typ.splits if_split_asm option.splits)
      apply (erule disjE, clarsimp)
       apply (thin_tac "lookup'' (global_entries (fst(sat_tlb s)) \<union> global_entries (the ` {e \<in> range (pt_walk a (MEM s) (TTBR0 s)). \<not> is_fault e}))
                       a v =  Incon")
       apply (subgoal_tac "v \<in> iset (set_tlb t)")
        apply (subgoal_tac "v \<in> global_set (set_tlb t)")
         apply blast
        apply (clarsimp simp: global_entries_def lookup_def tagged_entry_set_def entry_set_def global_range_def split: if_split_asm option.splits)
        apply blast
       apply (drule_tac a' = "ASID s" in lookup_global_incon_incon)
       apply blast
      apply (clarsimp)
      apply (thin_tac "lookup''  (global_entries (fst(sat_tlb s)) \<union> global_entries (the ` {e \<in> range (pt_walk a (MEM s) (TTBR0 s)). \<not> is_fault e})) a v = Miss")
      apply (drule union_asid_tlb_incon_cases)
      apply (erule disjE, clarsimp simp: )
  using non_global_lookup_range_pt_walk_not_incon apply force
      apply (erule disjE, clarsimp simp: )
       apply (drule_tac x = a in spec, simp, drule_tac x = v in spec)
       apply (clarsimp simp: non_global_to_global [symmetric])
       apply (case_tac "fst(lookup_from' (snapshot (set_tlb t)) a v)"; clarsimp?)
        apply (clarsimp simp: lookup_from'_def snap_conv'_def split: pt_walk_typ.splits if_split_asm option.splits)
       apply (subgoal_tac "\<not>is_fault (pt_walk a (MEM s) (TTBR0 s) v)")
        apply (subgoal_tac "xa = the (pt_walk a (MEM s) (TTBR0 s) v)")
         apply (clarsimp simp: lookup_from'_def snap_conv'_def split: pt_walk_typ.splits if_split_asm option.splits)
         apply (clarsimp simp: ptable_comp_def is_fault_def entry_leq_def) 
         apply (metis pt_walk_new_no_fault_pt_walk' option.inject) 
        apply (frule_tac a' = a in non_global_lookup_hit_asid, simp)
       apply (rule non_global_hit_no_fault, simp)
      apply (erule disjE, clarsimp simp: )
  using non_global_lookup_range_pt_walk_not_incon apply force
      apply (erule disjE, clarsimp simp: )
       apply (drule_tac x = a in spec, simp, drule_tac x = v in spec)
       apply (clarsimp simp: non_global_to_global [symmetric])
       apply (clarsimp simp: lookup_from'_def snap_conv'_def split:  pt_walk_typ.splits if_split_asm option.splits)
      apply (erule disjE, clarsimp simp: )
  using non_global_lookup_range_pt_walk_not_incon apply force
      apply (clarsimp simp: )
      apply (drule_tac x = a in spec, simp, drule_tac x = v in spec)
      apply (clarsimp simp: non_global_to_global [symmetric])
      apply (clarsimp simp: lookup_from'_def snap_conv'_def split:  pt_walk_typ.splits if_split_asm option.splits)
     apply (rule tlb_nion_global_non_global)
    apply (clarsimp)
    apply (rename_tac v)
    apply (subgoal_tac "snd(sat_tlb s) \<union> the ` {e \<in> range (pdc_walk a (MEM s) (TTBR0 s)). \<not> is_fault e} =  (non_global_entries_pdc (snd(sat_tlb s)) \<union> non_global_entries_pdc (the ` {e \<in> range (pdc_walk a (MEM s) (TTBR0 s)). \<not> is_fault e})) \<union>  
                          (global_entries_pdc (snd(sat_tlb s)) \<union> global_entries_pdc (the ` {e \<in> range (pdc_walk a (MEM s) (TTBR0 s)). \<not> is_fault e}))")
     apply (simp only:)
     apply (thin_tac "snd(sat_tlb s) \<union> the ` {e \<in> range (pdc_walk a (MEM s) (TTBR0 s)). \<not> is_fault e} =  (non_global_entries_pdc (snd(sat_tlb s)) \<union> non_global_entries_pdc (the ` {e \<in> range (pdc_walk a (MEM s) (TTBR0 s)). \<not> is_fault e})) \<union>  
                          (global_entries_pdc (snd(sat_tlb s)) \<union> global_entries_pdc (the ` {e \<in> range (pdc_walk a (MEM s) (TTBR0 s)). \<not> is_fault e}))")
     apply (subgoal_tac "lookup_pdc (global_entries_pdc (snd(sat_tlb s)))  a v = lookup_pdc (global_entries_pdc (snd(sat_tlb s)) \<union>  global_entries_pdc (the ` {e \<in> range (pdc_walk a (MEM s) (TTBR0 s)). \<not> is_fault e})) a v ")
      prefer 2
      apply (rule saturated_global_subset_lookup_pdc_un_eq[symmetric], simp)
     apply (drule_tac t = "non_global_entries_pdc (snd(sat_tlb s)) \<union> non_global_entries_pdc (the ` {e \<in> range (pdc_walk a (MEM s) (TTBR0 s)). \<not> is_fault e})" in union_asid_pdc_incon_cases)
     apply (erule disjE, clarsimp)
      apply (thin_tac "lookup_pdc (global_entries_pdc (snd(sat_tlb s)) \<union> global_entries_pdc (the ` {e \<in> range (pdc_walk a (MEM s) (TTBR0 s)). \<not> is_fault e}))
                       a v =  Incon")
      apply (subgoal_tac "v \<in> iset (set_tlb t)")
       apply (subgoal_tac "v \<in> global_set (set_tlb t)")
        apply blast
       apply (clarsimp simp: global_entries_pdc_def lookup_def asid_of_pdc_def tagged_pdc_entry_set_def entry_set_def global_range_def split: if_split_asm option.splits)
       apply blast
      apply (drule_tac a' = "ASID s" in lookup_global_incon_incon_pdc')
      apply blast
     apply (erule disjE, clarsimp)
      apply (thin_tac "lookup_pdc (global_entries_pdc (snd(sat_tlb s)) \<union> global_entries_pdc (the ` {e \<in> range (pdc_walk a (MEM s) (TTBR0 s)). \<not> is_fault e})) a v = Hit xa") 
      apply (case_tac "v \<in> global_set (set_tlb t)")
       apply (case_tac "v \<in> iset (set_tlb t)")
        apply blast
       apply clarsimp
       apply (subgoal_tac "lookup_pdc  (snd(sat_tlb s)) (ASID s) v = Hit xa \<or> 
                           lookup_pdc  (snd(sat_tlb s)) (ASID s) v = Incon")
        apply (erule_tac P = "lookup_pdc  (snd(sat_tlb s)) (ASID s) v = Hit xa" in disjE)
         apply (case_tac "is_fault (pdc_walk (ASID s) (MEM s) (TTBR0 s) v)")
          apply (clarsimp simp: incoherrent_vaddrs_def)
          apply force
         apply (drule  lookup_asid_pdc_hit_union_cases')
         apply (erule disjE, clarsimp)
          apply (subgoal_tac "asid_of_pdc (the (pdc_walk a (MEM s) (TTBR0 s) v)) = None")
           apply (drule_tac x = a in spec, simp, drule_tac x = v in spec)
           apply (clarsimp simp: non_global_to_global_pdc [symmetric])
           apply (case_tac "snd(lookup_from' (snapshot (set_tlb t)) a v)"; clarsimp?)
            apply (clarsimp simp: lookup_from'_def snap_conv'_def split: pt_walk_typ.splits if_split_asm option.splits)
           apply (clarsimp simp: lookup_from'_def snap_conv'_def split: pt_walk_typ.splits if_split_asm option.splits)
             apply (clarsimp simp: ptable_comp_def is_fault_def entry_leq_def) 
             apply (metis option.sel option.simps(3) pt_walk_new_no_fault_pdc_walk pt_walk_new_par_fault_pdc_walk)
            apply (clarsimp simp: ptable_comp_def is_fault_def entry_leq_def) 
            apply (metis option.sel option.simps(3) pt_walk_new_no_fault_pdc_walk )
           apply (clarsimp simp: ptable_comp_def is_fault_def entry_leq_def) 
           apply (metis lookup_non_global_hit_asid_of_not_none_pdc option.sel pt_walk_new_no_fault_pdc_walk)
          apply (rule_tac v = v and a = a and t = "(the ` {e \<in> range (pdc_walk a (MEM s) (TTBR0 s)). \<not> is_fault e})" in lookup_global_hit_asid_of_none_pdc)
          apply (subgoal_tac "\<not> is_fault (pdc_walk a (MEM s) (TTBR0 s) v)")
           apply (rule lookup_pdc_non_global_miss_non_fault, simp, simp)
  using no_fault_pdc_walk_unequal_asid' apply blast
         apply (erule disjE, clarsimp)
          apply (subgoal_tac "xa \<noteq> the (pdc_walk (ASID t) (MEM s) (TTBR0 s) v)")
           apply (drule_tac b = v and x = xa in saturatd_lookup_pdc_hit_no_fault; simp?)
          apply (subgoal_tac "asid_of_pdc xa = None")
           apply (subgoal_tac "asid_of_pdc (the (pdc_walk (ASID t) (MEM s) (TTBR0 s) v)) \<noteq> None")
            apply force
           apply (subgoal_tac "lookup_pdc (non_global_entries_pdc (the ` {e \<in> range (pdc_walk (ASID t) (MEM s) (TTBR0 s)). \<not> is_fault e})) (ASID t) v = Hit 
                              (the (pdc_walk (ASID t) (MEM s) (TTBR0 s) v))")
            apply (rule lookup_non_global_hit_asid_of_not_none_pdc, simp)
           apply (rule_tac a = a in non_global_lookup_pdc_hit_asid, simp)
          apply (rule lookup_global_hit_asid_of_none_pdc, simp)
         apply (clarsimp)
         apply (subgoal_tac "xa \<noteq> the (pdc_walk (ASID t) (MEM s) (TTBR0 s) v)")
          apply (drule_tac b = v and x = xa in saturatd_lookup_pdc_hit_no_fault; simp?)
         apply (subgoal_tac "asid_of_pdc xa = None")
          apply (subgoal_tac "asid_of_pdc (the (pdc_walk (ASID t) (MEM s) (TTBR0 s) v)) \<noteq> None")
           apply force
          apply (subgoal_tac "lookup_pdc (non_global_entries_pdc (the ` {e \<in> range (pdc_walk (ASID t) (MEM s) (TTBR0 s)). \<not> is_fault e})) (ASID t) v = Hit 
                              (the (pdc_walk (ASID t) (MEM s) (TTBR0 s) v))")
           apply (rule lookup_non_global_hit_asid_of_not_none_pdc, simp)
          apply (rule_tac a = a in non_global_lookup_pdc_hit_asid, simp)
         apply (rule lookup_global_hit_asid_of_none_pdc, simp)
        apply blast
       apply (metis lookup_global_same_for_asids_pdc lookup_pdc_global_hit_order)
      apply (subgoal_tac "xa \<in> global_entries_pdc (snd(sat_tlb s))")
       apply (subgoal_tac "v \<in> range_of xa")
        apply (clarsimp simp: global_range_def)
        apply blast
       apply (simp add: lookup_asid_pdc_hit_entry_range)
  using lookup_in_asid_pdc apply auto[1]
     apply (erule disjE, clarsimp)
      apply (thin_tac "lookup_pdc (global_entries_pdc (snd(sat_tlb s)) \<union> global_entries_pdc (the ` {e \<in> range (pdc_walk a (MEM s) (TTBR0 s)). \<not> is_fault e}))
                       a v =  Incon")
      apply (subgoal_tac "v \<in> iset (set_tlb t)")
       apply (subgoal_tac "v \<in> global_set (set_tlb t)")
        apply blast
       apply (clarsimp simp: global_entries_pdc_def lookup_def asid_of_pdc_def tagged_pdc_entry_set_def entry_set_def global_range_def split: if_split_asm option.splits)
       apply blast
      apply (drule_tac a' = "ASID s" in lookup_global_incon_incon_pdc')
      apply blast
     apply (erule disjE, clarsimp)
      apply (thin_tac "lookup_pdc (global_entries_pdc (snd(sat_tlb s)) \<union>  global_entries_pdc (the ` {e \<in> range (pdc_walk a (MEM s) (TTBR0 s)). \<not> is_fault e}))a v = Hit x")
      apply (drule union_asid_pdc_incon_cases)
      apply (erule disjE, clarsimp simp: )
  using non_global_lookup_range_pdc_walk_not_incon apply force
      apply (erule disjE, clarsimp simp: )
       apply (drule_tac x = a in spec, simp, drule_tac x = v in spec)
       apply (clarsimp simp: non_global_to_global_pdc [symmetric])
       apply (case_tac "snd(lookup_from' (snapshot (set_tlb t)) a v)"; clarsimp?)
        apply (clarsimp simp: lookup_from'_def snap_conv'_def split: pt_walk_typ.splits if_split_asm option.splits)
       apply (subgoal_tac "\<not>is_fault (pdc_walk a (MEM s) (TTBR0 s) v)")
        apply (subgoal_tac "xb = the (pdc_walk a (MEM s) (TTBR0 s) v)")
         apply (clarsimp simp: lookup_from'_def snap_conv'_def split: pt_walk_typ.splits if_split_asm option.splits)
           apply (clarsimp simp: ptable_comp_def is_fault_def entry_leq_def) 
           apply (metis option.inject pt_walk_new_no_fault_pdc_walk pt_walk_new_par_fault_pdc_walk) 
          apply (clarsimp simp: ptable_comp_def is_fault_def entry_leq_def) 
          apply (metis option.inject pt_walk_new_no_fault_pdc_walk pt_walk_new_par_fault_pdc_walk)
         apply (clarsimp simp: ptable_comp_def is_fault_def entry_leq_def) 
         apply (metis option.inject pt_walk_new_no_fault_pdc_walk pt_walk_new_par_fault_pdc_walk) 
        apply (frule_tac a' = a in non_global_lookup_pdc_hit_asid, simp)
       apply (rule non_global_hit_no_fault_pdc, simp)
      apply (erule disjE, clarsimp simp: )
  using non_global_lookup_range_pdc_walk_not_incon apply force 
      apply (erule disjE, clarsimp simp: )
       apply (drule_tac x = a in spec, simp, drule_tac x = v in spec)
       apply (clarsimp simp: non_global_to_global_pdc [symmetric])
       apply (clarsimp simp: lookup_from'_def snap_conv'_def split: pt_walk_typ.splits if_split_asm option.splits)
      apply (erule disjE, clarsimp simp: )
  using non_global_lookup_range_pdc_walk_not_incon apply force
      apply (clarsimp simp: )
      apply (drule_tac x = a in spec, simp, drule_tac x = v in spec)
      apply (clarsimp simp: non_global_to_global_pdc [symmetric])
      apply (clarsimp simp: lookup_from'_def snap_conv'_def split: pt_walk_typ.splits if_split_asm option.splits)
     apply (erule disjE, clarsimp)
      apply (thin_tac "lookup_pdc (global_entries_pdc (snd(sat_tlb s)) \<union> global_entries_pdc (the ` {e \<in> range (pdc_walk a (MEM s) (TTBR0 s)). \<not> is_fault e}))
                       a v =  Incon")
      apply (subgoal_tac "v \<in> iset (set_tlb t)")
       apply (subgoal_tac "v \<in> global_set (set_tlb t)")
        apply blast
       apply (clarsimp simp: global_entries_pdc_def lookup_def asid_of_pdc_def tagged_pdc_entry_set_def entry_set_def global_range_def split: if_split_asm option.splits)
       apply blast
      apply (drule_tac a' = "ASID s" in lookup_global_incon_incon_pdc')
      apply blast
     apply (clarsimp)
     apply (thin_tac "lookup_pdc (global_entries_pdc (snd(sat_tlb s)) \<union> global_entries_pdc (the ` {e \<in> range (pdc_walk a (MEM s) (TTBR0 s)). \<not> is_fault e})) a v = Miss")
     apply (drule union_asid_pdc_incon_cases)
     apply (erule disjE, clarsimp simp: )
  using non_global_lookup_range_pdc_walk_not_incon apply force
     apply (erule disjE, clarsimp simp: )
      apply (drule_tac x = a in spec, simp, drule_tac x = v in spec)
      apply (clarsimp simp: non_global_to_global_pdc [symmetric])
      apply (case_tac "snd(lookup_from' (snapshot (set_tlb t)) a v)"; clarsimp?)
       apply (clarsimp simp: lookup_from'_def snap_conv'_def split: pt_walk_typ.splits if_split_asm option.splits)
      apply (subgoal_tac "\<not>is_fault (pdc_walk a (MEM s) (TTBR0 s) v)")
       apply (subgoal_tac "xa = the (pdc_walk a (MEM s) (TTBR0 s) v)")
        apply (clarsimp simp: lookup_from'_def snap_conv'_def split: pt_walk_typ.splits if_split_asm option.splits)
          apply (clarsimp simp: ptable_comp_def is_fault_def entry_leq_def) 
          apply (metis (no_types, hide_lams) non_fault_pt_walk_pair_disjI option.inject
      option.sel pt_walk_full_no_pdc_fault pt_walk_new_par_fault_pdc_walk pt_walk_typ.inject(2) pt_walk_typ.simps(8))
         apply (clarsimp simp: ptable_comp_def is_fault_def entry_leq_def) 
         apply (metis option.inject pt_walk_new_no_fault_pdc_walk)   
        apply (clarsimp simp: ptable_comp_def is_fault_def entry_leq_def) 
        apply (metis option.inject pt_walk_new_no_fault_pdc_walk)
       apply (frule_tac a' = a in non_global_lookup_pdc_hit_asid, simp)
      apply (rule non_global_hit_no_fault_pdc, simp)
     apply (erule disjE, clarsimp simp: )
  using non_global_lookup_range_pdc_walk_not_incon apply force
     apply (erule disjE, clarsimp simp: )
      apply (drule_tac x = a in spec, simp, drule_tac x = v in spec)
      apply (clarsimp simp: non_global_to_global_pdc [symmetric])
      apply (clarsimp simp: lookup_from'_def snap_conv'_def split:  pt_walk_typ.splits if_split_asm option.splits)
     apply (erule disjE, clarsimp simp: )
  using non_global_lookup_range_pdc_walk_not_incon apply force
     apply (clarsimp simp: )
     apply (drule_tac x = a in spec, simp, drule_tac x = v in spec)
     apply (clarsimp simp: non_global_to_global_pdc [symmetric])
     apply (clarsimp simp: lookup_from'_def snap_conv'_def split:  pt_walk_typ.splits if_split_asm option.splits)
    apply (rule pdc_non_global_non_global)
   apply (clarsimp simp: incoherrent_vaddrs_def)
   apply (rule conjI)
    apply clarsimp
    apply (rename_tac v x)
    apply (subgoal_tac "fst(sat_tlb s) \<union> the ` {e \<in> range (pt_walk a (MEM s) (TTBR0 s)). \<not> is_fault e} = 
                                             (non_global_entries (fst(sat_tlb s)) \<union> non_global_entries (the ` {e \<in> range (pt_walk a (MEM s) (TTBR0 s)). \<not> is_fault e})) \<union>  (global_entries (fst(sat_tlb s)) \<union> global_entries (the ` {e \<in> range (pt_walk a (MEM s) (TTBR0 s)). \<not> is_fault e}))")
     apply (simp only:)
     apply (thin_tac "fst(sat_tlb s) \<union> the ` {e \<in> range (pt_walk a (MEM s) (TTBR0 s)). \<not> is_fault e} = 
                                             (non_global_entries (fst(sat_tlb s)) \<union> non_global_entries (the ` {e \<in> range (pt_walk a (MEM s) (TTBR0 s)). \<not> is_fault e})) \<union>  (global_entries (fst(sat_tlb s)) \<union> global_entries (the ` {e \<in> range (pt_walk a (MEM s) (TTBR0 s)). \<not> is_fault e}))")
     apply (subgoal_tac "lookup''   (global_entries (fst(sat_tlb s)))  a v = lookup'' (global_entries (fst(sat_tlb s)) \<union>  global_entries (the ` {e \<in> range (pt_walk a (MEM s) (TTBR0 s)). \<not> is_fault e})) a v ")
      prefer 2
      apply (rule saturated_global_subset_lookup_tlb_un_eq[symmetric], simp)
     apply (drule_tac t = "non_global_entries (fst(sat_tlb s)) \<union> non_global_entries (the ` {e \<in> range (pt_walk a (MEM s) (TTBR0 s)). \<not> is_fault e})" in  lookup_asid_tlb_hit_union_cases')
     apply (erule disjE, clarsimp)
      apply (thin_tac "lookup''(global_entries (fst(sat_tlb s)) \<union> global_entries (the ` {e \<in> range (pt_walk a (MEM s) (TTBR0 s)). \<not> is_fault e})) a v = Miss")
      apply (subgoal_tac "lookup'' (non_global_entries (the ` {e \<in> range (pt_walk a (MEM s) (TTBR0 s)). \<not> is_fault e})) a v = Miss")
       apply (drule  lookup_asid_tlb_hit_union_cases')
       apply (erule disjE, clarsimp)
        apply (drule_tac x = a in spec, simp, drule_tac x = v in spec)
        apply (clarsimp simp: non_global_to_global [symmetric])
        apply (case_tac "fst(lookup_from' (snapshot (set_tlb t)) a v)"; clarsimp?)
         apply (clarsimp simp: lookup_from'_def snap_conv'_def split: pt_walk_typ.splits if_split_asm option.splits)
        apply (clarsimp simp: lookup_from'_def snap_conv'_def split: pt_walk_typ.splits if_split_asm option.splits)
        apply (clarsimp simp: ptable_comp_def is_fault_def entry_leq_def) 
        apply (metis option.simps(3) pt_walk_new_no_fault_pt_walk') 
       apply (erule disjE, clarsimp)
       apply (clarsimp)
      apply (rule is_fault_non_global_entries_miss, simp)
     apply (erule disjE, clarsimp)
      apply (thin_tac "lookup''  (global_entries (fst(sat_tlb s)) \<union> global_entries (the ` {e \<in> range (pt_walk a (MEM s) (TTBR0 s)). \<not> is_fault e})) a v =  Hit x")
      apply (subgoal_tac "v \<in> global_set (set_tlb t)")
       apply (case_tac "v \<in> iset (set_tlb t)") 
        apply blast
       apply (subgoal_tac " lookup''  (fst(sat_tlb s)) (ASID t) v = Hit x \<or>
                       lookup''  (fst(sat_tlb s)) (ASID t) v = Incon")
        prefer 2
        apply (metis (no_types, hide_lams)  lookup_global_hit_order lookup_global_same_for_asids )
       apply (erule disjE)
        apply (clarsimp simp: ) 
  using no_fault_pt_walk_unequal_asid' apply fastforce
       apply (clarsimp simp: inconsistent_vaddrs_def) apply force
      apply (clarsimp simp: global_entries_def lookup_def tagged_entry_set_def entry_set_def global_range_def split: if_split_asm option.splits)
      apply blast
     apply (clarsimp)
     apply (subgoal_tac "v \<in> global_set (set_tlb t)")
      apply (case_tac "v \<in> iset (set_tlb t)") 
       apply blast
      apply (subgoal_tac " lookup''  (fst(sat_tlb s)) (ASID t) v = Hit x \<or>
                       lookup''  (fst(sat_tlb s)) (ASID t) v = Incon")
       prefer 2
       apply (metis (no_types, hide_lams)  lookup_global_hit_order lookup_global_same_for_asids )
      apply (erule disjE)
       apply (clarsimp simp: ) 
  using no_fault_pt_walk_unequal_asid' apply fastforce
      apply (clarsimp simp: inconsistent_vaddrs_def) apply force
     apply (clarsimp simp: global_entries_def lookup_def tagged_entry_set_def entry_set_def global_range_def split: if_split_asm option.splits)
     apply blast
    apply (rule tlb_nion_global_non_global)
   apply clarsimp
   apply (rename_tac v x)
   apply (subgoal_tac "snd(sat_tlb s) \<union> the ` {e \<in> range (pdc_walk a (MEM s) (TTBR0 s)). \<not> is_fault e} = 
                                             (non_global_entries_pdc (snd(sat_tlb s)) \<union> non_global_entries_pdc (the ` {e \<in> range (pdc_walk a (MEM s) (TTBR0 s)). \<not> is_fault e})) \<union>  (global_entries_pdc (snd(sat_tlb s)) \<union> global_entries_pdc (the ` {e \<in> range (pdc_walk a (MEM s) (TTBR0 s)). \<not> is_fault e}))")
    apply (simp only:)
    apply (thin_tac "snd(sat_tlb s) \<union> the ` {e \<in> range (pdc_walk a (MEM s) (TTBR0 s)). \<not> is_fault e} = 
                                             (non_global_entries_pdc (snd(sat_tlb s)) \<union> non_global_entries_pdc (the ` {e \<in> range (pdc_walk a (MEM s) (TTBR0 s)). \<not> is_fault e})) \<union>  (global_entries_pdc (snd(sat_tlb s)) \<union> global_entries_pdc (the ` {e \<in> range (pdc_walk a (MEM s) (TTBR0 s)). \<not> is_fault e}))")
    apply (subgoal_tac "lookup_pdc   (global_entries_pdc (snd(sat_tlb s)))  a v = lookup_pdc (global_entries_pdc (snd(sat_tlb s)) \<union>  global_entries_pdc (the ` {e \<in> range (pdc_walk a (MEM s) (TTBR0 s)). \<not> is_fault e})) a v ")
     prefer 2
     apply (rule saturated_global_subset_lookup_pdc_un_eq[symmetric], simp)
    apply (drule_tac t = "non_global_entries_pdc (snd(sat_tlb s)) \<union> non_global_entries_pdc (the ` {e \<in> range (pdc_walk a (MEM s) (TTBR0 s)). \<not> is_fault e})" in  lookup_asid_pdc_hit_union_cases')
    apply (erule disjE, clarsimp)
     apply (thin_tac "lookup_pdc (global_entries_pdc (snd(sat_tlb s)) \<union> global_entries_pdc (the ` {e \<in> range (pdc_walk a (MEM s) (TTBR0 s)). \<not> is_fault e})) a v = Miss")
     apply (subgoal_tac "lookup_pdc (non_global_entries_pdc (the ` {e \<in> range (pdc_walk a (MEM s) (TTBR0 s)). \<not> is_fault e})) a v = Miss")
      apply (drule  lookup_asid_pdc_hit_union_cases')
      apply (erule disjE, clarsimp)
       apply (drule_tac x = a in spec, simp, drule_tac x = v in spec)
       apply (clarsimp simp: non_global_to_global_pdc [symmetric])
       apply (case_tac "snd(lookup_from' (snapshot (set_tlb t)) a v)"; clarsimp?)
        apply (clarsimp simp: lookup_from'_def snap_conv'_def split: pt_walk_typ.splits if_split_asm option.splits)
       apply (clarsimp simp: lookup_from'_def snap_conv'_def split: pt_walk_typ.splits if_split_asm option.splits)
         apply (clarsimp simp: ptable_comp_def is_fault_def entry_leq_def)  
         apply (metis is_fault_def pt_walk_full_no_pdc_fault pt_walk_partial_no_pdc_fault)
        apply (clarsimp simp: ptable_comp_def is_fault_def entry_leq_def)  
        apply (metis is_fault_def pt_walk_full_no_pdc_fault)
       apply (clarsimp simp: ptable_comp_def is_fault_def entry_leq_def)  
       apply (metis is_fault_def pt_walk_full_no_pdc_fault)
      apply (erule disjE, clarsimp)
      apply (clarsimp)
     apply (rule is_fault_non_global_entries_pdc_miss,simp)
    apply (erule disjE, clarsimp)
     apply (thin_tac "lookup_pdc  (global_entries_pdc (snd(sat_tlb s)) \<union> global_entries_pdc (the ` {e \<in> range (pdc_walk a (MEM s) (TTBR0 s)). \<not> is_fault e})) a v =  Hit x")
     apply (subgoal_tac "v \<in> global_set (set_tlb t)")
      apply (case_tac "v \<in> iset (set_tlb t)") 
       apply blast
      apply (subgoal_tac " lookup_pdc  (snd(sat_tlb s)) (ASID t) v = Hit x \<or>
                       lookup_pdc  (snd(sat_tlb s)) (ASID t) v = Incon")
       prefer 2
       apply (metis (no_types, hide_lams)  lookup_pdc_global_hit_order lookup_global_same_for_asids_pdc )
      apply (erule disjE)
       apply (clarsimp simp: ) 
  using no_fault_pdc_walk_unequal_asid' apply fastforce
      apply (clarsimp simp: inconsistent_vaddrs_def) apply force
     apply (clarsimp simp: global_entries_pdc_def lookup_def asid_of_pdc_def tagged_pdc_entry_set_def entry_set_def global_range_def split: if_split_asm option.splits)
     apply blast
    apply (clarsimp)
    apply (subgoal_tac "v \<in> global_set (set_tlb t)")
     apply (case_tac "v \<in> iset (set_tlb t)") 
      apply blast
     apply (subgoal_tac " lookup_pdc  (snd(sat_tlb s)) (ASID t) v = Hit x \<or>
                       lookup_pdc  (snd(sat_tlb s)) (ASID t) v = Incon")
      prefer 2
      apply (metis (no_types, hide_lams)  lookup_pdc_global_hit_order lookup_global_same_for_asids_pdc )
     apply (erule disjE)
      apply (clarsimp simp: ) 
  using no_fault_pdc_walk_unequal_asid' apply fastforce
     apply (clarsimp simp: inconsistent_vaddrs_def) apply force
    apply (clarsimp simp: global_entries_pdc_def lookup_def asid_of_pdc_def tagged_pdc_entry_set_def entry_set_def global_range_def split: if_split_asm option.splits)
    apply blast
   apply (rule pdc_non_global_non_global)
  apply (rule conjI)
   apply (clarsimp simp: global_range_def)
   apply (rule conjI)

    apply (subgoal_tac "global_entries (fst(sat_tlb s) \<union> the ` {e \<in> range (pt_walk a (MEM s) (TTBR0 s)). \<not> is_fault e}) = 
                         global_entries (fst(sat_tlb s))")
     apply (simp only:)
    apply (subgoal_tac "global_entries (the ` {e \<in> range (pt_walk a (MEM s) (TTBR0 s)). \<not> is_fault e}) \<subseteq> 
          global_entries (fst(sat_tlb s))" )
     apply (clarsimp simp: global_entries_union)
     apply blast
    apply (subgoal_tac "global_entries (the ` {e \<in> range (pt_walk a (MEM s) (TTBR0 s)). \<not> is_fault e}) = 
                       global_entries (the ` {e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e})")
     apply (simp only:)
     apply (clarsimp simp: saturated_def global_entries_def) apply force
    apply (rule global_entries_ptable_same)
   apply (subgoal_tac "global_entries_pdc (snd(sat_tlb s) \<union> the ` {e \<in> range (pdc_walk a (MEM s) (TTBR0 s)). \<not> is_fault e}) = 
                         global_entries_pdc (snd(sat_tlb s))")
    apply (simp only:)
   apply (subgoal_tac "global_entries_pdc (the ` {e \<in> range (pdc_walk a (MEM s) (TTBR0 s)). \<not> is_fault e}) \<subseteq> 
          global_entries_pdc (snd(sat_tlb s))" )
    apply (clarsimp simp: global_entries_union_pdc)
    apply blast

   apply (subgoal_tac "global_entries_pdc (the ` {e \<in> range (pdc_walk a (MEM s) (TTBR0 s)). \<not> is_fault e}) = 
                       global_entries_pdc (the ` {e \<in> range (pdc_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e})")
    apply (simp only:)
    apply (clarsimp simp: saturated_def global_entries_pdc_def) apply force
   apply (rule global_entries_pdc_ptable_same)
  apply (clarsimp simp: )
  apply (rule conjI)
   apply (subgoal_tac "(fst(sat_tlb s) \<union> the ` {e \<in> range (pt_walk a (MEM s) (TTBR0 s)). \<not> is_fault e} - global_entries (fst(sat_tlb s) \<union> the ` {e \<in> range (pt_walk a (MEM s) (TTBR0 s)). \<not> is_fault e})) =
                                                                                                non_global_entries (fst(sat_tlb s)\<union> the ` {e \<in> range (pt_walk a (MEM s) (TTBR0 s)). \<not> is_fault e})")
    apply (simp only:)
    apply (thin_tac "(fst(sat_tlb s) \<union> the ` {e \<in> range (pt_walk a (MEM s) (TTBR0 s)). \<not> is_fault e} - global_entries (fst(sat_tlb s) \<union> the ` {e \<in> range (pt_walk a (MEM s) (TTBR0 s)). \<not> is_fault e})) =
                                                                                                non_global_entries (fst(sat_tlb s) \<union> the ` {e \<in> range (pt_walk a (MEM s) (TTBR0 s)). \<not> is_fault e})")
    apply (case_tac "aa = ASID t")
     apply (thin_tac " \<forall>a. a \<noteq> ASID s \<longrightarrow>
            (\<forall>v. lookup'' (fst (sat_tlb s) - global_entries (fst (sat_tlb s))) a v \<le> fst (lookup_from' (snapshot (set_tlb t)) a v) \<and>
                 lookup_pdc (snd (sat_tlb s) - global_entries_pdc (snd (sat_tlb s))) a v \<le> snd (lookup_from' (snapshot (set_tlb t)) a v))")
     apply (clarsimp)
     apply (subgoal_tac "lookup'' (non_global_entries (fst(sat_tlb s) \<union> the ` {e \<in> range (pt_walk a (MEM s) (TTBR0 s)). \<not> is_fault e})) (ASID t) v =
                                                              lookup'' (non_global_entries (fst(sat_tlb s))) (ASID t) v")
      apply (simp only:)
      apply (thin_tac "lookup'' (non_global_entries (fst(sat_tlb s) \<union> the ` {e \<in> range (pt_walk a (MEM s) (TTBR0 s)). \<not> is_fault e})) (ASID s) v =
                                                              lookup'' (non_global_entries (fst(sat_tlb s))) (ASID s) v")
      apply (case_tac "fst(lookup_from' (snp_upd_cur' (snapshot (set_tlb t)) (iset (set_tlb t)) (MEM s) (TTBR0 s) (ASID t)) (ASID t) v)"; clarsimp)
       apply (clarsimp simp: lookup_from'_def snap_conv'_def split: pt_walk_typ.splits if_split_asm option.splits)
          apply (clarsimp simp: snp_upd_cur'_def snp_upd_cur_def)
          apply (subgoal_tac "v \<notin> incon_addrs (typ_sat_tlb s)")
           apply (thin_tac "incon_addrs (typ_sat_tlb s) \<subseteq> iset (set_tlb t)")
           apply (clarsimp simp: incon_addrs_def inconsistent_vaddrs_def incoherrent_vaddrs_def is_fault_def)
           apply (metis lookup_asid_tlb_miss_union lookup_tlb_eq_union_global_non_global lookup_type.exhaust option.simps(3) pt_walk_new_fault_pt_walk_fault')
          apply blast
         apply (clarsimp simp: snp_upd_cur'_def snp_upd_cur_def)
         apply (subgoal_tac "v \<notin> incon_addrs (typ_sat_tlb s)")
          apply (thin_tac "incon_addrs (typ_sat_tlb s) \<subseteq> iset (set_tlb t)")
          apply (clarsimp simp: incon_addrs_def inconsistent_vaddrs_def incoherrent_vaddrs_def is_fault_def)
          apply (metis lookup_asid_tlb_miss_union not_miss_incon_hit_asid_tlb option.discI pt_walk_new_par_fault_pt_walk_fault' tlb_global_non_global_union)
         apply blast
        apply (clarsimp simp: snp_upd_cur'_def snp_upd_cur_def)
        apply (subgoal_tac "v \<notin> incon_addrs (typ_sat_tlb s)")
         apply (thin_tac "incon_addrs (typ_sat_tlb s) \<subseteq> iset (set_tlb t)")
         apply (clarsimp simp: incon_addrs_def inconsistent_vaddrs_def incoherrent_vaddrs_def is_fault_def)
         apply (metis lookup_asid_tlb_miss_union not_miss_incon_hit_asid_tlb option.discI pt_walk_new_par_fault_pt_walk_fault' tlb_global_non_global_union)
        apply blast       
       apply (clarsimp simp: snp_upd_cur'_def snp_upd_cur_def)
       apply (subgoal_tac "x31 = the (pt_walk (ASID t) (MEM s) (TTBR0 s) v)")
        prefer 2
        apply (simp add: pt_walk_new_no_fault_pt_walk')
       apply (subgoal_tac "v \<notin> incon_addrs (typ_sat_tlb s)") prefer 2 apply blast
       apply (thin_tac "incon_addrs (typ_sat_tlb s) \<subseteq> iset (set_tlb t)")
       apply (clarsimp simp: incon_addrs_def inconsistent_vaddrs_def incoherrent_vaddrs_def is_fault_def)
       apply (case_tac "lookup'' (fst(sat_tlb s)) (ASID s) v"; clarsimp)
        apply (metis lookup_asid_tlb_miss_union tlb_global_non_global_union)
       apply (subgoal_tac "lookup'' (fst(sat_tlb s)) (ASID s) v = lookup'' (fst(sat_tlb s) \<union> the ` {e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e}) (ASID t) v")
        prefer 2
        apply (clarsimp simp: saturated_def)
        apply (simp add: sup.absorb1)  
       apply (simp only:)
       apply (drule lookup_asid_tlb_hit_union_cases')
       apply (thin_tac "(\<forall>x. lookup_pdc (snd (sat_tlb s)) (ASID s) v \<noteq> Hit x) \<or> (\<exists>y. pdc_walk (ASID s) (MEM s) (TTBR0 s) v = Some y)")
       apply (erule disjE, clarsimp)
        apply (subgoal_tac "is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) v)")
         apply (clarsimp simp: is_fault_def)
        apply (rule asid_tlb_lookup_miss_is_fault, simp)
       apply (erule disjE, clarsimp)
       apply (clarsimp)
       apply (subgoal_tac "x3 = y") apply clarsimp
        apply (subgoal_tac "lookup'' (fst(sat_tlb s)) (ASID s) v = lookup'' (global_entries (fst(sat_tlb s)) \<union> non_global_entries (fst(sat_tlb s))) (ASID s) v ")
         apply (simp only:)
         apply (thin_tac "  lookup'' (the ` {e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e}) (ASID s) v = Hit y ")
         apply (drule lookup_asid_tlb_hit_union_cases')   
         apply (erule disjE, clarsimp)   
         apply (erule disjE, clarsimp)  
          apply (drule lookup_non_global_hit_asid_of_not_none, simp)
         apply (clarsimp) 
         apply (drule lookup_non_global_hit_asid_of_not_none, simp)
        apply (clarsimp) apply (insert tlb_global_non_global_union [of "fst(sat_tlb s)"])
        apply (simp add: Un_commute)
       apply (frule asid_tlb_lookup_range_fault_pt_walk)
       apply (drule_tac x = v in bspec)
  using lookup_asid_tlb_hit_entry_range apply force
       apply simp
      apply (clarsimp simp: lookup_from'_def snap_conv'_def split: pt_walk_typ.splits if_split_asm option.splits)
      apply (clarsimp simp: snp_upd_cur'_def snp_upd_cur_def)
      apply (subgoal_tac "v \<notin> incon_addrs (typ_sat_tlb s)") prefer 2 apply blast
      apply (thin_tac "incon_addrs (typ_sat_tlb s) \<subseteq> iset (set_tlb t)")
      apply (clarsimp simp: incon_addrs_def inconsistent_vaddrs_def incoherrent_vaddrs_def is_fault_def)
      apply (case_tac "lookup'' (fst(sat_tlb s)) (ASID t) v"; clarsimp)
       apply (simp only: non_global_to_global)
       apply (subgoal_tac "lookup'' (fst(sat_tlb s) - global_entries (fst(sat_tlb s))) (ASID t) v = Miss") apply simp
       apply (rule lookup_miss_minus_miss, simp)
      apply (subgoal_tac "x3a = x3", simp)
       apply (simp only: non_global_to_global)
       apply (subgoal_tac "lookup'' (fst(sat_tlb s) - global_entries (fst(sat_tlb s))) (ASID t) v = Miss \<or>
                 lookup'' (fst(sat_tlb s) - global_entries (fst(sat_tlb s))) (ASID t) v = Hit x3")
        apply force
       apply (rule lookup_miss_minus_miss_hit, simp)
      apply (frule_tac b = v and x = x3a in  saturatd_lookup_hit_no_fault, simp, 
      simp add: is_fault_def, simp)
  using pt_walk_new_no_fault_pt_walk' apply force
     apply (rule lookup_non_global_union_asid_unequal, simp)
    apply (drule_tac x = aa in spec, simp, drule_tac x = v in spec)
    apply (subgoal_tac "lookup'' (non_global_entries (fst(sat_tlb s) \<union> the ` {e \<in> range (pt_walk a (MEM s) (TTBR0 s)). \<not> is_fault e})) aa v =
                                         lookup'' (non_global_entries (fst(sat_tlb s))) aa v") 
     apply (simp only: non_global_to_global)
     apply (clarsimp simp: snp_upd_cur'_def snp_upd_cur_def)
     apply (clarsimp simp: lookup_from'_def snap_conv'_def split: if_split_asm option.splits)
    apply (rule lookup_non_global_union_asid_unequal', simp, simp, simp) 
  using non_global_to_global apply auto [1] 
  apply (subgoal_tac "(snd(sat_tlb s) \<union> the ` {e \<in> range (pdc_walk a (MEM s) (TTBR0 s)). \<not> is_fault e} - global_entries_pdc (snd(sat_tlb s) \<union> the ` {e \<in> range (pdc_walk a (MEM s) (TTBR0 s)). \<not> is_fault e})) =
                                                                                                non_global_entries_pdc (snd(sat_tlb s)\<union> the ` {e \<in> range (pdc_walk a (MEM s) (TTBR0 s)). \<not> is_fault e})")
   apply (simp only:)
   apply (thin_tac "(snd(sat_tlb s) \<union> the ` {e \<in> range (pdc_walk a (MEM s) (TTBR0 s)). \<not> is_fault e} - global_entries_pdc (snd(sat_tlb s) \<union> the ` {e \<in> range (pdc_walk a (MEM s) (TTBR0 s)). \<not> is_fault e})) =
                                                                                                non_global_entries_pdc (snd(sat_tlb s)\<union> the ` {e \<in> range (pdc_walk a (MEM s) (TTBR0 s)). \<not> is_fault e})")
   apply (case_tac "aa = ASID t")
    apply (thin_tac " \<forall>a. a \<noteq> ASID s \<longrightarrow>
            (\<forall>v. lookup'' (fst (sat_tlb s) - global_entries (fst (sat_tlb s))) a v \<le> fst (lookup_from' (snapshot (set_tlb t)) a v) \<and>
                 lookup_pdc (snd (sat_tlb s) - global_entries_pdc (snd (sat_tlb s))) a v \<le> snd (lookup_from' (snapshot (set_tlb t)) a v))")
    apply (clarsimp)
    apply (subgoal_tac "lookup_pdc (non_global_entries_pdc (snd(sat_tlb s) \<union> the ` {e \<in> range (pdc_walk a (MEM s) (TTBR0 s)). \<not> is_fault e})) (ASID s) v =
                                                              lookup_pdc (non_global_entries_pdc (snd(sat_tlb s))) (ASID s) v")
     apply (simp only:)
     apply (thin_tac  "lookup_pdc (non_global_entries_pdc (snd(sat_tlb s) \<union> the ` {e \<in> range (pdc_walk a (MEM s) (TTBR0 s)). \<not> is_fault e})) (ASID s) v =
                                                              lookup_pdc (non_global_entries_pdc (snd(sat_tlb s))) (ASID s) v")
     apply (case_tac "snd(lookup_from' (snp_upd_cur' (snapshot (set_tlb t)) (iset (set_tlb t)) (MEM s) (TTBR0 s) (ASID t)) (ASID t) v)"; clarsimp)
      apply (clarsimp simp: lookup_from'_def snap_conv'_def split: pt_walk_typ.splits if_split_asm option.splits)
        apply (clarsimp simp: snp_upd_cur'_def snp_upd_cur_def)
        apply (subgoal_tac "v \<notin> incon_addrs (typ_sat_tlb s)")
         apply (thin_tac "incon_addrs (typ_sat_tlb s) \<subseteq> iset (set_tlb t)")
         apply (clarsimp simp: incon_addrs_def inconsistent_vaddrs_def incoherrent_vaddrs_def is_fault_def)
         apply (metis (full_types) global_entries_pdc_def leq_Miss less_eq_lookup_type lookup_asid_pdc_miss_union lookup_eq_union_global_non_global_pdc lookup_type.exhaust lookup_type.simps(3) non_global_entries_pdc_def
      not_Some_eq pt_walk_new_fault_pdc_walk_fault' pt_walk_pair_def typ_sat_prim_parameter typ_sat_tlb_def)
        apply blast
       apply (clarsimp simp: snp_upd_cur'_def snp_upd_cur_def)
       apply (subgoal_tac "v \<notin> incon_addrs (typ_sat_tlb s)")
        apply (thin_tac "incon_addrs (typ_sat_tlb s) \<subseteq> iset (set_tlb t)")
        apply (clarsimp simp: incon_addrs_def inconsistent_vaddrs_def incoherrent_vaddrs_def is_fault_def)

  subgoal
  proof -
    fix v :: vaddr and x2 :: pdc_entry
    assume a1: "saturated (typ_sat_tlb s)"
    assume a2: "pt_walk_pair (ASID s) (MEM s) (TTBR0 s) v = Partial_Walk x2"
    assume a3: "asid_of_pdc x2 = None"
    assume a4: "lookup_pdc (snd (sat_tlb s)) (ASID s) v \<noteq> Incon"
    have "the (Some x2) = x2"
      by simp
    moreover
    { assume "lookup_pdc (snd (sat_tlb s)) (ASID s) v = Hit x2"
      then have "\<exists>P. lookup_pdc (P \<union> non_global_entries_pdc (snd (sat_tlb s))) (ASID s) v = Hit x2"
        by (metis (no_types) lookup_eq_union_global_non_global_pdc)
      then have "lookup_pdc (non_global_entries_pdc (snd (sat_tlb s))) (ASID s) v = Miss"
        using a3 lookup_asid_pdc_hit_union_cases' lookup_non_global_hit_asid_of_not_none_pdc by blast }
    ultimately show "lookup_pdc (non_global_entries_pdc (snd (sat_tlb s))) (ASID s) v = Miss"
      using a4 a2 a1 by (metis (no_types) lookup_asid_pdc_miss_union pdc_global_non_global_union pt_walk_new_par_fault_pdc_walk pt_walk_partial_no_pdc_fault saturate_no_icon_miss)
  qed
       apply blast
      apply (clarsimp simp: snp_upd_cur'_def snp_upd_cur_def)
      apply (subgoal_tac "x32 = the (pdc_walk (ASID s) (MEM s) (TTBR0 s) v)")
       prefer 2
       apply (simp add: pt_walk_new_no_fault_pdc_walk)
      apply (subgoal_tac "v \<notin> incon_addrs (typ_sat_tlb s)") prefer 2 apply blast
      apply (thin_tac "incon_addrs (typ_sat_tlb s) \<subseteq> iset (set_tlb t)")
      apply (clarsimp simp: incon_addrs_def inconsistent_vaddrs_def incoherrent_vaddrs_def is_fault_def)
      apply (case_tac "lookup_pdc (snd(sat_tlb s)) (ASID s) v"; clarsimp)
  using pt_walk_full_no_pdc_fault sat_miss_pdc_fault apply fastforce
      apply (subgoal_tac "lookup_pdc (snd(sat_tlb s)) (ASID s) v = lookup_pdc (snd(sat_tlb s) \<union> the ` {e \<in> range (pdc_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e}) (ASID t) v")
       prefer 2
       apply (clarsimp simp: saturated_def)
       apply (simp add: sup.absorb1)  
      apply (simp only:)
      apply (drule lookup_asid_pdc_hit_union_cases')
      apply (thin_tac "(\<forall>x. lookup'' (fst (sat_tlb s)) (ASID s) v \<noteq> Hit x) \<or> (\<exists>y. pt_walk (ASID s) (MEM s) (TTBR0 s) v = Some y)")
      apply (erule disjE, clarsimp)
       apply (subgoal_tac "is_fault (pdc_walk (ASID s) (MEM s) (TTBR0 s) v)")
        apply (clarsimp simp: is_fault_def) 
       apply (rule lookup_pdc_miss_is_fault, simp)
      apply (erule disjE, clarsimp)
      apply (clarsimp)
      apply (subgoal_tac "x3 = y") apply clarsimp
       apply (subgoal_tac "lookup_pdc (snd(sat_tlb s)) (ASID s) v = lookup_pdc (global_entries_pdc (snd(sat_tlb s)) \<union> non_global_entries_pdc (snd(sat_tlb s))) (ASID s) v ")
        apply (simp only:)
        apply (thin_tac "  lookup_pdc (the ` {e \<in> range (pdc_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e}) (ASID s) v = Hit y ")
        apply (drule lookup_asid_pdc_hit_union_cases')   
        apply (erule disjE, clarsimp)   
        apply (erule disjE, clarsimp)  
         apply (drule lookup_non_global_hit_asid_of_not_none_pdc, simp)
        apply (clarsimp) 
        apply (drule lookup_non_global_hit_asid_of_not_none_pdc, simp)
       apply (clarsimp) apply (insert pdc_global_non_global_union [of "snd(sat_tlb s)"])
       apply (simp add: Un_commute) 
      apply (frule lookup_pdc_range_fault_pt_walk)
      apply (drule_tac x = v in bspec)
  using lookup_asid_pdc_hit_entry_range apply blast
      apply simp
     apply (clarsimp simp: lookup_from'_def snap_conv'_def split: pt_walk_typ.splits if_split_asm option.splits)
       apply (clarsimp simp: snp_upd_cur'_def snp_upd_cur_def)
       apply (subgoal_tac "v \<notin> incon_addrs (typ_sat_tlb s)") prefer 2 apply blast
       apply (thin_tac "incon_addrs (typ_sat_tlb s) \<subseteq> iset (set_tlb t)")
       apply (clarsimp simp: incon_addrs_def inconsistent_vaddrs_def incoherrent_vaddrs_def is_fault_def)
       apply (case_tac "lookup_pdc (snd(sat_tlb s)) (ASID t) v"; clarsimp)
        apply (simp only: non_global_to_global_pdc)
        apply (subgoal_tac "lookup_pdc (snd(sat_tlb s) - global_entries_pdc (snd(sat_tlb s))) (ASID t) v = Miss") apply simp
        apply (rule lookup_miss_minus_miss_pdc, simp)
       apply (subgoal_tac "x3a = x3", simp)
        apply (simp only: non_global_to_global_pdc)
        apply (subgoal_tac "lookup_pdc (snd(sat_tlb s) - global_entries_pdc (snd(sat_tlb s))) (ASID t) v = Miss \<or>
                 lookup_pdc (snd(sat_tlb s) - global_entries_pdc (snd(sat_tlb s))) (ASID t) v = Hit x3")
         apply force
        apply (rule lookup_miss_minus_miss_hit_pdc, simp)
       apply (frule_tac b = v and x = x3a in  saturatd_lookup_pdc_hit_no_fault, simp, 
      simp add: is_fault_def, simp)
       apply (simp add: pt_walk_new_par_fault_pdc_walk)
      apply (clarsimp simp: snp_upd_cur'_def snp_upd_cur_def)
      apply (subgoal_tac "v \<notin> incon_addrs (typ_sat_tlb s)") prefer 2 apply blast
      apply (thin_tac "incon_addrs (typ_sat_tlb s) \<subseteq> iset (set_tlb t)")
      apply (clarsimp simp: incon_addrs_def inconsistent_vaddrs_def incoherrent_vaddrs_def is_fault_def)
      apply (case_tac "lookup_pdc (snd(sat_tlb s)) (ASID t) v"; clarsimp)
       apply (simp only: non_global_to_global_pdc)
       apply (subgoal_tac "lookup_pdc (snd(sat_tlb s) - global_entries_pdc (snd(sat_tlb s))) (ASID t) v = Miss") apply simp
       apply (rule lookup_miss_minus_miss_pdc, simp)
      apply (subgoal_tac "x3a = x3", simp)
       apply (simp only: non_global_to_global_pdc)
       apply (subgoal_tac "lookup_pdc (snd(sat_tlb s) - global_entries_pdc (snd(sat_tlb s))) (ASID t) v = Miss \<or>
                 lookup_pdc (snd(sat_tlb s) - global_entries_pdc (snd(sat_tlb s))) (ASID t) v = Hit x3")
        apply force
       apply (rule lookup_miss_minus_miss_hit_pdc, simp)
      apply (frule_tac b = v and x = x3a in  saturatd_lookup_pdc_hit_no_fault, simp, 
      simp add: is_fault_def, simp)
  using pt_walk_new_no_fault_pdc_walk apply force
     apply (clarsimp simp: snp_upd_cur'_def snp_upd_cur_def)
     apply (subgoal_tac "v \<notin> incon_addrs (typ_sat_tlb s)") prefer 2 apply blast
     apply (thin_tac "incon_addrs (typ_sat_tlb s) \<subseteq> iset (set_tlb t)")
     apply (clarsimp simp: incon_addrs_def inconsistent_vaddrs_def incoherrent_vaddrs_def is_fault_def)
     apply (case_tac "lookup_pdc (snd(sat_tlb s)) (ASID t) v"; clarsimp)
      apply (simp only: non_global_to_global_pdc)
      apply (subgoal_tac "lookup_pdc (snd(sat_tlb s) - global_entries_pdc (snd(sat_tlb s))) (ASID t) v = Miss") apply simp
      apply (rule lookup_miss_minus_miss_pdc, simp)
     apply (subgoal_tac "x3a = x3", simp)
      apply (simp only: non_global_to_global_pdc)
      apply (subgoal_tac "lookup_pdc (snd(sat_tlb s) - global_entries_pdc (snd(sat_tlb s))) (ASID t) v = Miss \<or>
                 lookup_pdc (snd(sat_tlb s) - global_entries_pdc (snd(sat_tlb s))) (ASID t) v = Hit x3")
       apply force
      apply (rule lookup_miss_minus_miss_hit_pdc, simp)
     apply (frule_tac b = v and x = x3a in  saturatd_lookup_pdc_hit_no_fault, simp, 
      simp add: is_fault_def, simp)
  using pt_walk_new_no_fault_pdc_walk apply force
    apply (rule lookup_non_global_union_asid_unequal_pdc, simp)
   apply (drule_tac x = aa in spec, simp, drule_tac x = v in spec)
   apply (subgoal_tac "lookup_pdc (non_global_entries_pdc (snd(sat_tlb s) \<union> the ` {e \<in> range (pdc_walk a (MEM s) (TTBR0 s)). \<not> is_fault e})) aa v =
                                         lookup_pdc (non_global_entries_pdc (snd(sat_tlb s))) aa v") 
    apply (simp only: non_global_to_global_pdc)
    apply (clarsimp simp: snp_upd_cur'_def snp_upd_cur_def)
    apply (clarsimp simp: lookup_from'_def snap_conv'_def split: if_split_asm option.splits) 
   apply (rule lookup_non_global_union_asid_unequal_pdc', simp, simp, simp) 
  using non_global_to_global_pdc by auto [1] 



end