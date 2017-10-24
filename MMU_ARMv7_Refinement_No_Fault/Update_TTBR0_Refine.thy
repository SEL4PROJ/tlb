theory Update_TTBR0_Refine

imports 
  "MMU_ARMv7_Ref_No_Fault"

begin               


class update_TTBR0 =
  fixes update_TTBR0 :: "paddr \<Rightarrow> 'a state_scheme \<Rightarrow>  unit \<times> 'a state_scheme" 


instantiation tlb_state_ext :: (type) update_TTBR0   
begin
  definition   
  "(update_TTBR0 r :: ('a tlb_state_scheme \<Rightarrow> _))  = update_state (\<lambda>s. s\<lparr> TTBR0 := r \<rparr>) "

thm update_TTBR0_tlb_state_ext_def
(* print_context *)                      
  instance ..
end


instantiation tlb_det_state_ext :: (type) update_TTBR0  
begin
  definition   
  "(update_TTBR0 r :: ('a tlb_det_state_scheme \<Rightarrow> _))  = update_state (\<lambda>s. s\<lparr> TTBR0 := r \<rparr>) "

thm update_TTBR0_tlb_det_state_ext_def
(* print_context *)                      
  instance ..
end


instantiation tlb_sat_no_flt_state_ext :: (type) update_TTBR0   
begin
  definition   
  "(update_TTBR0 r :: ('a tlb_sat_no_flt_state_scheme \<Rightarrow> _))  = do {
      update_state (\<lambda>s. s\<lparr> TTBR0 := r \<rparr>);
      mem   <- read_state MEM;
      asid <- read_state ASID;
      let all_non_fault_entries = {e\<in>pt_walk asid mem r ` UNIV. \<not>is_fault e};
      tlb0   <- read_state tlb_sat_no_flt_set;
      let tlb = tlb0 \<union> all_non_fault_entries; 
      update_state (\<lambda>s. s\<lparr> tlb_sat_no_flt_set := tlb \<rparr>)} "

thm update_TTBR0_tlb_sat_no_flt_state_ext_def
(* print_context *)                      
  instance ..
end



instantiation tlb_incon_state'_ext :: (type) update_TTBR0   
begin
  definition   
  "(update_TTBR0 r :: ('a tlb_incon_state'_scheme \<Rightarrow> _))  = do {
      update_state (\<lambda>s. s\<lparr> TTBR0 := r \<rparr>);
      iset   <- read_state tlb_incon_set';
      asid   <- read_state ASID;
      update_state (\<lambda>s. s\<lparr> tlb_incon_set' := iset \<union> ({asid} \<times> UNIV) \<rparr>)
} "
thm update_TTBR0_tlb_incon_state'_ext_def
print_context                     
  instance ..
end



lemma update_asid_non_det_det_refine:
  "\<lbrakk> update_TTBR0 r (s::tlb_state) = ((), s') ;  update_TTBR0 r (t::tlb_det_state) = ((), t'); 
         tlb_rel (typ_tlb s) (typ_det_tlb t) \<rbrakk> \<Longrightarrow>  tlb_rel (typ_tlb s') (typ_det_tlb t') "
  apply (clarsimp simp: update_TTBR0_tlb_state_ext_def update_TTBR0_tlb_det_state_ext_def tlb_rel_def) 
  by (cases s, cases t , clarsimp simp: state.defs)


lemma  update_asid_det_sat_no_flt_refine:
  "\<lbrakk> update_TTBR0 r (s::tlb_det_state) = ((), s') ;  update_TTBR0 r (t::tlb_sat_no_flt_state) = ((), t'); 
         tlb_rel_sat_no_flt (typ_det_tlb s) (typ_sat_no_flt_tlb t) \<rbrakk> \<Longrightarrow> 
                  tlb_rel_sat_no_flt (typ_det_tlb s') (typ_sat_no_flt_tlb t')"
  apply (clarsimp simp: update_TTBR0_tlb_det_state_ext_def update_TTBR0_tlb_sat_no_flt_state_ext_def)
  apply (clarsimp simp: tlb_rel_sat_no_flt_def saturated_no_flt_def no_faults_def)
  apply (cases s, cases t , clarsimp simp: state.defs , force)
done


lemma lookup_no_flt_range_pt_walk_asid_miss:
  "a \<noteq> a1 \<Longrightarrow> lookup {e \<in> range (pt_walk a mem ttbr0). \<not> is_fault e} a1 va = Miss"
  apply (clarsimp simp: lookup_def entry_set_def entry_range_asid_tags_def)
  by force

lemma lookup_no_flt_range_pt_walk_not_incon':
  "lookup {e \<in> range (pt_walk asid mem ttbr0). \<not> is_fault e} asid1 va \<noteq> Incon"
  apply (case_tac "asid = asid1")
   apply (clarsimp simp: lookup_no_flt_range_pt_walk_not_incon)
  by (clarsimp simp: lookup_no_flt_range_pt_walk_asid_miss)
 
lemma update_asid_sat_no_flt_abs_refine':
  "\<lbrakk> update_TTBR0 r (s::tlb_sat_no_flt_state) = ((), s') ;  update_TTBR0 r (t::tlb_incon_state') = ((), t'); 
     (*  saturated_no_flt (typ_sat_no_flt_tlb s) ; *) tlb_rel_abs' (typ_sat_no_flt_tlb s) (typ_incon' t) \<rbrakk> \<Longrightarrow> 
                                 tlb_rel_abs' (typ_sat_no_flt_tlb s') (typ_incon' t')"
  apply (clarsimp simp: update_TTBR0_tlb_sat_no_flt_state_ext_def update_TTBR0_tlb_incon_state'_ext_def)
  apply (clarsimp simp:  tlb_rel_abs'_def)
  apply (rule conjI)
   apply (clarsimp simp: typ_sat_no_flt_tlb_def "state.defs")
  apply (clarsimp simp: asid_va_incon_tlb_mem_def)
  apply (subgoal_tac "ASID t = ASID s")
   prefer 2
   apply (clarsimp simp: tlb_rel'_absD typ_sat_no_flt_tlb_def state.defs)
  apply (rule conjI)
   prefer 2
   apply (clarsimp simp: asid_va_hit_incon_def)
  apply (clarsimp simp: asid_va_incon_def)
  apply (case_tac "a = ASID s")
   apply assumption
  apply (drule union_incon_cases1)
  using lookup_no_flt_range_pt_walk_asid_miss by auto


end