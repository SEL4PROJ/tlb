theory Update_ASID_TTBR0_Refine

imports  Update_ASID_Refine

begin               


(* the root register should also be updated in addition to the asid  *)

class update_asid_ttbr0 =
  fixes update_asid_ttbr0 :: "asid \<Rightarrow> paddr \<Rightarrow> 'a state_scheme \<Rightarrow>  unit \<times> 'a state_scheme" 


instantiation tlb_state_ext :: (type) update_asid_ttbr0  
begin
  definition   
  "(update_asid_ttbr0 a r :: ('a tlb_state_scheme \<Rightarrow> _))  = update_state (\<lambda>s. s\<lparr> ASID := a ,TTBR0 := r \<rparr>) "

thm update_asid_ttbr0_tlb_state_ext_def
(* print_context *)                      
  instance ..
end


instantiation tlb_det_state_ext :: (type) update_asid_ttbr0  
begin
  definition   
  "(update_asid_ttbr0 a r :: ('a tlb_det_state_scheme \<Rightarrow> _))  = update_state (\<lambda>s. s\<lparr> ASID := a , TTBR0 := r \<rparr>) "

thm update_asid_ttbr0_tlb_det_state_ext_def
(* print_context *)                      
  instance ..
end


instantiation tlb_sat_no_flt_state_ext :: (type) update_asid_ttbr0  
begin
  definition   
  "(update_asid_ttbr0 a r :: ('a tlb_sat_no_flt_state_scheme \<Rightarrow> _))  = do {
      update_state (\<lambda>s. s\<lparr> ASID := a , TTBR0 := r \<rparr>);
      mem   <- read_state MEM;
      let all_non_fault_entries = {e\<in>pt_walk a mem r ` UNIV. \<not>is_fault e};
      tlb0   <- read_state tlb_sat_no_flt_set;
      let tlb = tlb0 \<union> all_non_fault_entries; 
      update_state (\<lambda>s. s\<lparr> tlb_sat_no_flt_set := tlb \<rparr>)} "

thm update_asid_ttbr0_tlb_sat_no_flt_state_ext_def
(* print_context *)                      
  instance ..
end



instantiation tlb_incon_state'_ext :: (type) update_asid_ttbr0   
begin
  definition   
  "(update_asid_ttbr0 a r :: ('a tlb_incon_state'_scheme \<Rightarrow> _))  = do {
      update_state (\<lambda>s. s\<lparr> ASID := a , TTBR0 := r \<rparr>)} "
thm update_asid_ttbr0_tlb_incon_state'_ext_def
print_context                     
  instance ..
end





(* the goal is to have the final assumption of the incon set, that we are using in the logic, that
       should say that the intersection of updated asid and the iset is empty *)

lemma update_asid_non_det_det_refine:
  "\<lbrakk> update_asid_ttbr0 a r (s::tlb_state) = ((), s') ;  update_asid_ttbr0 a r (t::tlb_det_state) = ((), t'); 
         tlb_rel (typ_tlb s) (typ_det_tlb t); \<forall>va. consistent0 (MEM t) a r ( tlb_det_set t) va \<rbrakk> \<Longrightarrow> 
                  tlb_rel (typ_tlb s') (typ_det_tlb t') \<and> (\<forall>va. consistent0 (MEM t') a r (tlb_det_set t') va) "
  apply (clarsimp simp: update_asid_ttbr0_tlb_state_ext_def update_asid_ttbr0_tlb_det_state_ext_def tlb_rel_def) 
  by (cases s, cases t , clarsimp simp: state.defs)

thm entry_range_single_element



lemma  update_asid_det_sat_no_flt_refine:
  "\<lbrakk> update_asid_ttbr0 a r (s::tlb_det_state) = ((), s') ;  update_asid_ttbr0 a r (t::tlb_sat_no_flt_state) = ((), t'); 
         tlb_rel_sat_no_flt (typ_det_tlb s) (typ_sat_no_flt_tlb t); \<forall>va. consistent0 (MEM t) a r (tlb_sat_no_flt_set t) va \<rbrakk> \<Longrightarrow> 
                  tlb_rel_sat_no_flt (typ_det_tlb s') (typ_sat_no_flt_tlb t') \<and> (\<forall>va. consistent0 (MEM t') a r (tlb_sat_no_flt_set t') va)"
  apply (clarsimp simp: update_asid_ttbr0_tlb_det_state_ext_def update_asid_ttbr0_tlb_sat_no_flt_state_ext_def)
  apply (rule conjI)
   apply (clarsimp simp: tlb_rel_sat_no_flt_def saturated_no_flt_def no_faults_def)
   apply (cases s, cases t , clarsimp simp: state.defs , force)
  apply (clarsimp, drule_tac x = va in spec)
  apply (subst (asm) consistent0_def)
  apply (erule disjE)
   apply (simp add: consistent0_def)
   apply (rule disjI1)
   apply (clarsimp simp: tlb_rel_sat_no_flt_def)
   apply (rule lookup_hit_union_cases_rule)
   apply (rule disjI2)
   apply (rule disjI2)
   apply clarsimp
   apply (subgoal_tac "\<not>is_fault (pt_walk a (MEM t) r va)")
    apply (clarsimp simp: lookup_range_pt_walk_hit_no_flt)
   apply (subgoal_tac "pt_walk a (MEM t) r va \<in> tlb_sat_no_flt_set t")
    apply (clarsimp simp: no_faults_def)
   apply (clarsimp simp: lookup_in_tlb)
  apply (simp add: consistent0_def)
  apply (rule disjCI)
  apply (frule_tac t' = "{e \<in> range (pt_walk a (MEM t) r). \<not> is_fault e}" in lookup_union_miss_not_miss_cases)
   apply clarsimp
  apply (erule disjE)
   apply (rule lookup_hit_union_cases_rule)
   apply (rule disjI2)
   apply (rule disjI1)
   apply clarsimp
   apply (frule  lookup_range_fault_pt_walk)
   apply (drule_tac x = "addr_val va" in bspec)
    apply (clarsimp simp: lookup_hit_entry_range)
   apply clarsimp
  apply (clarsimp simp: lookup_no_flt_range_pt_walk_not_incon)
done



lemma update_asid_sat_no_flt_abs_refine:
  "\<lbrakk> update_asid_ttbr0 a r (s::tlb_sat_no_flt_state) = ((), s') ;  update_asid_ttbr0 a r (t::tlb_incon_state') = ((), t'); 
       saturated_no_flt (typ_sat_no_flt_tlb (s\<lparr>ASID := a , TTBR0 := r\<rparr>)) ; 
        (* coming from 'update_asid_det_sat_no_flt_refine' theorem i.e.
       tlb_rel_sat_no_flt (typ_det_tlb s') (typ_sat_no_flt_tlb t') states the saturated assumption with the updated asid  *) 
         tlb_rel_abs' (typ_sat_no_flt_tlb (s\<lparr>ASID := a, TTBR0 := r\<rparr>)) (typ_incon' t);   \<forall>va. (a, va) \<notin> (tlb_incon_set' t) \<rbrakk> \<Longrightarrow> 
                    tlb_rel_abs' (typ_sat_no_flt_tlb s') (typ_incon' t') \<and>  (\<forall>va. (a, va) \<notin> (tlb_incon_set' t'))"
  apply (subgoal_tac "tlb_sat_no_flt_set s = tlb_sat_no_flt_set s \<union> {e \<in> range (pt_walk a (MEM s) r). \<not> is_fault e} ")
   apply (clarsimp simp: update_asid_ttbr0_tlb_sat_no_flt_state_ext_def update_asid_ttbr0_tlb_incon_state'_ext_def tlb_rel_abs'_def)
   apply (cases s, cases t , clarsimp simp: state.defs)
  apply (clarsimp simp:  tlb_rel_abs'_def saturated_no_flt_def)  by force


end

