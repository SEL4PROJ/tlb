theory ARMv7_Update_ASID_Ref


imports  ARMv7_Update_TTBR0_Ref

begin  




lemma update_ASID_non_det_det_refine:
  "\<lbrakk> update_ASID a (s::tlb_state) = ((), s') ;  update_ASID a (t::tlb_det_state) = ((), t'); 
         tlb_rel (typ_tlb s) (typ_det_tlb t) \<rbrakk> \<Longrightarrow>  tlb_rel (typ_tlb s') (typ_det_tlb t') "
  apply (clarsimp simp: update_ASID_tlb_state_ext_def update_ASID_tlb_det_state_ext_def tlb_rel_def) 
  apply (rule conjI)
   apply (cases s, cases t , clarsimp simp: state.defs tlb_rel_def) 
  by blast

lemma  update_ASID_det_sat_refine:
  "\<lbrakk> update_ASID a (s::tlb_det_state) = ((), s') ;  update_ASID a (t::tlb_sat_state) = ((), t'); 
         tlb_rel_sat (typ_det_tlb s) (typ_sat_tlb t) \<rbrakk> \<Longrightarrow> 
                  tlb_rel_sat (typ_det_tlb s') (typ_sat_tlb t')"
  apply (clarsimp simp: update_ASID_tlb_det_state_ext_def update_ASID_tlb_sat_state_ext_def)
  apply (clarsimp simp: tlb_rel_sat_def saturated_def )
  apply (cases s, cases t , clarsimp simp: state.defs , force)
done

lemma  lookup_incon_not_miss:
   "\<lbrakk> lookup (t \<union> t') a v = Incon ; lookup t' a v = Miss\<rbrakk> \<Longrightarrow>
       lookup t a v = Incon"
  apply (clarsimp simp: lookup_def entry_set_def split: if_split_asm)
  apply safe
  by force+

lemma lookup_hit_diff_union_incon:
  "\<lbrakk>lookup t a v = Hit x ; lookup t' a v = Hit x' ; x \<noteq> x'\<rbrakk> \<Longrightarrow> lookup (t \<union> t') a v = Incon"
  apply (clarsimp simp: lookup_def entry_set_def entry_range_asid_tags_def split: if_split_asm)
  apply safe
     apply force
    apply (metis (no_types, lifting) mem_Collect_eq singletonD singletonI)
   apply (metis (no_types, lifting) mem_Collect_eq singletonD singletonI)
  apply force
  done


lemma lookup_miss_union_hit_intro:
  "\<lbrakk>lookup t a v = Miss;  lookup t' a v = Hit x\<rbrakk> \<Longrightarrow> 
           lookup (t \<union> t') a v = Hit x"
  apply (clarsimp simp: lookup_def entry_set_def entry_range_asid_tags_def split: if_split_asm)
  apply safe
       apply auto 
  by force


lemma lookup_miss_union_hit_intro':
  "\<lbrakk> lookup t a v = Hit x ; lookup t' a v = Miss\<rbrakk> \<Longrightarrow> 
           lookup (t \<union> t') a v = Hit x"
  apply (clarsimp simp: lookup_def entry_set_def entry_range_asid_tags_def split: if_split_asm)
  apply safe
       apply auto 
  by blast


lemma lookup_union_hit_hit:
  "\<lbrakk> lookup t a v = Hit x ; lookup t' a v = Hit x\<rbrakk> \<Longrightarrow> 
           lookup (t \<union> t') a v = Hit x"
  apply (clarsimp simp: lookup_def entry_set_def entry_range_asid_tags_def split: if_split_asm)
  apply safe
       apply auto 
  by blast+


lemma
  "\<lbrakk> lookup t a v \<noteq> Incon; lookup t a v \<noteq> Miss\<rbrakk>
         \<Longrightarrow> \<exists>x\<in>t. lookup t a v = Hit x"
  apply (clarsimp simp: lookup_def entry_set_def split: if_split_asm) 
  by blast



lemma not_miss_incon_hit':
  " lookup t a va = Incon \<or> (\<exists>x\<in>t. lookup t a va = Hit x) \<Longrightarrow> lookup t a va \<noteq> Miss "
 by (clarsimp simp: lookup_def entry_set_def split: if_split_asm)
 


lemma not_fault_range_not_miss:
  "\<not> is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) v) \<Longrightarrow> 
         lookup (tlb_sat_set s \<union> the ` {e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e}) (ASID s) v \<noteq> Miss"
  apply (clarsimp simp:)
  apply (clarsimp simp: lookup_def entry_set_va_set  a_va_set_def split: if_split_asm)
  apply (drule_tac x = "the (pt_walk (ASID s) (MEM s) (TTBR0 s) v)" in bspec)
   apply (drule_tac x = "pt_walk (ASID s) (MEM s) (TTBR0 s) v" in spec)
   apply clarsimp
   apply (insert asid_va_entry_range_pt_entry [of "ASID s" "MEM s" "TTBR0 s" "v"], clarsimp)
  apply clarsimp
  done



(* refinement between saturated and new abstracted model  *)

lemma update_ASID_sat_abs2_refine:
  "\<lbrakk> update_ASID a (s::tlb_sat_state) = ((), s') ;  update_ASID a (t::tlb_incon_state) = ((), t'); 
        tlb_rel_abs (typ_sat_tlb s) (typ_incon t) \<rbrakk> \<Longrightarrow> 
                       tlb_rel_abs (typ_sat_tlb s') (typ_incon t')"
  apply (clarsimp simp: update_ASID_tlb_sat_state_ext_def update_ASID_tlb_incon_state_ext_def Let_def)
  apply (frule tlb_rel_absD)
  apply (case_tac "a = ASID s")
    (* when we update to the same ASID *)
   apply (subgoal_tac "tlb_sat_set s = tlb_sat_set s \<union> 
         the `{e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e}")
    prefer 2
    apply (clarsimp simp:  saturated_def) 
    apply blast
   apply clarsimp
   apply (clarsimp simp: tlb_rel_abs_def)
   apply (rule conjI)
    apply (clarsimp simp: state.defs)
   apply (rule conjI)
    apply (clarsimp simp: snapshot_update_current'_def snapshot_update_current_def snapshot_update_current'2_def snapshot_update_current2_def 
      incon_load_incon_def incon_load2_def incon_load_def)
    apply force
   apply clarsimp
   apply (clarsimp simp: snapshot_of_tlb_def snapshot_update_current'_def snapshot_update_current_def
      snapshot_update_new'_def  snapshot_update_new_def)
   apply (clarsimp simp: snapshot_update_current'_def snapshot_update_current_def snapshot_update_current'2_def snapshot_update_current2_def 
      incon_load_incon_def incon_load2_def incon_load_def split: if_split_asm)
    (* when we update to the new ASID *)
  apply (clarsimp simp: tlb_rel_abs_def)
  apply (rule conjI)
   apply (clarsimp simp: state.defs)
  apply (rule conjI)
   apply (subgoal_tac "incon_load_incon (snapshot_update_current'2 (snapshot (tlb_incon_set t)) (iset (tlb_incon_set t)) (MEM s) (TTBR0 s) (ASID s)) a (MEM s) (TTBR0 s)  = 
                       incon_load_incon (snapshot (tlb_incon_set t)) a (MEM s) (TTBR0 s) ")
    prefer 2
    apply (clarsimp simp: incon_load_incon_def snapshot_update_current'2_def snapshot_update_current2_def split: if_split_asm)
   apply (subgoal_tac "incon_load2 (snapshot_update_current'2 (snapshot (tlb_incon_set t)) (iset (tlb_incon_set t)) (MEM s) (TTBR0 s) (ASID s)) a (MEM s) (TTBR0 s)  = 
                       incon_load2 (snapshot (tlb_incon_set t))  a (MEM s) (TTBR0 s) ")
    prefer 2
    apply (clarsimp simp: incon_load2_def snapshot_update_current'2_def snapshot_update_current2_def split: if_split_asm)
   apply (simp only:)
   apply (thin_tac "incon_load_incon (snapshot_update_current'2 (snapshot (tlb_incon_set t)) (iset (tlb_incon_set t)) (MEM s) (TTBR0 s) (ASID s)) a (MEM s) (TTBR0 s)  = 
                       incon_load_incon (snapshot (tlb_incon_set t)) a (MEM s) (TTBR0 s)")
   apply (thin_tac "incon_load2 (snapshot_update_current'2 (snapshot (tlb_incon_set t)) (iset (tlb_incon_set t)) (MEM s) (TTBR0 s) (ASID s)) a (MEM s) (TTBR0 s)  = 
                       incon_load2 (snapshot (tlb_incon_set t))  a (MEM s) (TTBR0 s)")
   apply (clarsimp)
   apply (drule_tac x = a in spec, simp add: snapshot_of_tlb_def)
   apply (clarsimp simp: incon_addrs_def incon_va_set_def ptable_tlb_va_incon_def)
   apply (drule_tac x = x in spec)
   apply (erule disjE)+
    apply (clarsimp simp: incon_load2_def incon_load_incon_def)
    apply (drule union_incon_cases1)
    apply (erule disjE , clarsimp)
    apply (erule disjE , clarsimp simp: less_eq_lookup_type lookup_range_pt_walk_hit)
    apply (erule disjE , clarsimp simp: lookup_range_pt_walk_not_incon)
    apply (erule disjE , clarsimp)
    apply (erule disjE , clarsimp simp: lookup_range_pt_walk_not_incon')
    apply (clarsimp)
   apply clarsimp
   apply (clarsimp simp: incon_load2_def incon_load_incon_def)
   apply (drule lookup_hit_union_cases')
   apply (erule disjE , clarsimp simp: less_eq_lookup_type) 
   apply (erule disjE , clarsimp simp:  lookup_miss_is_fault_intro) 
   apply (clarsimp simp: lookup_miss_is_fault_intro)
  apply (rule conjI)
   apply (clarsimp simp: saturated_def)
  apply (rule allI)
  apply (rule impI)
  apply (rule allI)
  apply (case_tac "aa \<noteq> ASID s")
   apply (subgoal_tac "snapshot_update_current'2 (snapshot (tlb_incon_set t)) (iset (tlb_incon_set t)) (MEM s) (TTBR0 s) (ASID s) aa v = 
                         (snapshot (tlb_incon_set t)) aa v")
    prefer 2
    apply (clarsimp simp: snapshot_update_current'2_def snapshot_update_current2_def split: if_split_asm)
   apply (simp only:)
   apply (thin_tac " snapshot_update_current'2 (snapshot (tlb_incon_set t)) (iset (tlb_incon_set t)) (MEM s) (TTBR0 s) (ASID s) aa v = snapshot (tlb_incon_set t) aa v")
   apply (simp only: snapshot_of_tlb_def)
   apply (subgoal_tac "lookup (tlb_sat_set s \<union> the ` {e \<in> range (pt_walk a (MEM s) (TTBR0 s)). \<not> is_fault e}) aa (  v) =
         lookup (tlb_sat_set s) aa (  v)")
    apply clarsimp
   apply (simp add: asid_unequal_miss'' lookup_miss_union_equal)
  apply clarsimp
  apply (simp only: snapshot_of_tlb_def)
  apply (subgoal_tac "lookup (tlb_sat_set s \<union> the ` {e \<in> range (pt_walk a (MEM s) (TTBR0 s)). \<not> is_fault e}) (ASID s) (  v) =
               lookup (tlb_sat_set s) (ASID s) (  v)")
   prefer 2
   apply (clarsimp simp: lookup_miss_union_equal asid_unequal_miss'')
  apply (clarsimp)
  apply (thin_tac "  lookup (tlb_sat_set s \<union> the ` {e \<in> range (pt_walk a (MEM s) (TTBR0 s)). \<not> is_fault e}) (ASID s) v = lookup (tlb_sat_set s) (ASID s) v")
  apply (clarsimp simp: snapshot_update_current'2_def snapshot_update_current2_def split: if_split_asm)
  apply (rule conjI)
   apply clarsimp
   apply (subgoal_tac "v \<notin>  incon_addrs (typ_sat_tlb s)")
    prefer 2
    apply blast
   apply (clarsimp simp: incon_addrs_def incon_va_set_def ptable_tlb_va_incon_def)  
   apply (metis (no_types, hide_lams)  less_eq_lookup_type lookup_def saturatd_lookup_hit_no_fault)
  apply clarsimp
  apply (subgoal_tac "v \<notin>  incon_addrs (typ_sat_tlb s)")
   prefer 2
   apply blast
  apply (clarsimp simp: incon_addrs_def incon_va_set_def ptable_tlb_va_incon_def)
  using not_miss_incon_hit by blast 


end