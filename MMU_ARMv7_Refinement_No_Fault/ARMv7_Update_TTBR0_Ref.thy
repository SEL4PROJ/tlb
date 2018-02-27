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
  

 
(* new refinement *)

lemma update_ttbr0_sat_abs2_refine':
  "\<lbrakk> update_TTBR0 r (s::tlb_sat_state) = ((), s') ;  update_TTBR0 r (t::tlb_incon_state) = ((), t'); 
             tlb_rel_abs (typ_sat_tlb s) (typ_incon t) \<rbrakk> \<Longrightarrow> 
                     tlb_rel_abs (typ_sat_tlb s') (typ_incon t')"
  apply (clarsimp simp: update_TTBR0_tlb_sat_state_ext_def update_TTBR0_tlb_incon_state_ext_def tlb_rel_abs_def)
  apply (subgoal_tac "ASID t = ASID s \<and> TTBR0 t = TTBR0 s \<and> MEM t = MEM s")
   prefer 2
   apply (clarsimp simp:  typ_sat_tlb_def state.defs)
  apply (rule conjI)
   apply (clarsimp simp: typ_sat_tlb_def "state.defs")
  apply (clarsimp simp: incon_addrs_def)
  apply (rule conjI)
   prefer 2
   apply (rule conjI)
    apply (clarsimp)
    apply (clarsimp simp: ptable_tlb_va_incon_def  incon_va_set_def ptable_comp'_def)
    apply (drule lookup_hit_union_cases')
    apply (erule disjE, blast)
    apply (erule disjE, clarsimp simp:  lookup_miss_is_fault_intro) 
    apply (clarsimp simp:  lookup_miss_is_fault_intro) 
   prefer 2
   apply (clarsimp)
   apply (clarsimp simp:  incon_va_set_def ptable_comp'_def  ptable_tlb_va_incon_def)
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
  subgoal
  proof -
    fix x :: vaddr and xa :: tlb_entry and xc :: vaddr
    assume a1: "lookup (tlb_sat_set s) (ASID s) x = Hit xa"
    assume a2: "pt_walk (ASID s) (MEM s) (TTBR0 s) x = pt_walk (ASID s) (MEM s) r x"
    assume a3: "saturated (typ_sat_tlb s)"
    assume a4: "\<not> is_fault (pt_walk (ASID s) (MEM s) r x)"
    assume a5: "lookup (the ` {e \<in> range (pt_walk (ASID s) (MEM s) r). \<not> is_fault e}) (ASID s) x = Hit (the (pt_walk (ASID s) (MEM s) r xc))"
    assume a6: "xa \<noteq> the (pt_walk (ASID s) (MEM s) r xc)"
    have "Hit (the (pt_walk (ASID s) (MEM s) r xc)) = Hit (the (pt_walk (ASID s) (MEM s) r x))"
      using a5 a4 by (simp add: lookup_range_pt_walk_hit)
    then show "x \<in> iset (tlb_incon_set t)"
      using a6 a4 a3 a2 a1 by (metis (no_types) saturatd_lookup_hit_no_fault)
  qed
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