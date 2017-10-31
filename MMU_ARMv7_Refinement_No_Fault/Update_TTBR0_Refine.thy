theory Update_TTBR0_Refine

imports 
  MMU_ARMv7_Ref_No_Fault

begin               


class update_TTBR0 =
  fixes update_TTBR0 :: "paddr \<Rightarrow> 'a state_scheme \<Rightarrow>  unit \<times> 'a state_scheme" 


instantiation tlb_state_ext :: (type) update_TTBR0   
begin
  definition   
  "(update_TTBR0 r :: ('a tlb_state_scheme \<Rightarrow> _))  = 
do {
    update_state (\<lambda>s. s\<lparr> tlb_set := tlb_set s - tlb_evict (typ_tlb s) \<rparr>);
    update_state (\<lambda>s. s\<lparr> TTBR0 := r \<rparr>)
  } "

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
      ttbr0   <- read_state TTBR0;
      update_state (\<lambda>s. s\<lparr> TTBR0 := r \<rparr>);
      iset   <- read_state tlb_incon_set';
      asid   <- read_state ASID;
      mem   <- read_state MEM;
       let ptable_asid_va = ptable_comp asid mem mem ttbr0 r;
      update_state (\<lambda>s. s\<lparr> tlb_incon_set' := iset \<union> ptable_asid_va \<rparr>)
} "
thm update_TTBR0_tlb_incon_state'_ext_def
print_context                     
  instance ..
end



lemma update_asid_non_det_det_refine:
  "\<lbrakk> update_TTBR0 r (s::tlb_state) = ((), s') ;  update_TTBR0 r (t::tlb_det_state) = ((), t'); 
         tlb_rel (typ_tlb s) (typ_det_tlb t) \<rbrakk> \<Longrightarrow>  tlb_rel (typ_tlb s') (typ_det_tlb t') "
  apply (clarsimp simp: update_TTBR0_tlb_state_ext_def update_TTBR0_tlb_det_state_ext_def tlb_rel_def) 
  apply (rule conjI)
   apply (cases s, cases t , clarsimp simp: state.defs tlb_rel_def) 
  by blast

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



lemma  sat_no_fault_elem:
  "\<lbrakk>saturated_no_flt (typ_sat_no_flt_tlb s); no_faults (tlb_sat_no_flt_set s) ; x \<in>  tlb_sat_no_flt_set s\<rbrakk> \<Longrightarrow>
        \<not>is_fault x   "
  by (clarsimp simp: saturated_no_flt_def  no_faults_def)

lemma lookup_in_no_flt:
  " lookup {e \<in> range (pt_walk a m r). \<not> is_fault e} a (addr_val v) = Hit (pt_walk a m r v) \<Longrightarrow>
     \<not>is_fault (pt_walk a m r v)"
  apply (drule lookup_in_tlb)
  by blast


lemma saturated_no_flt_pt_walk:
  "\<lbrakk> saturated_no_flt (typ_sat_no_flt_tlb s) ;  no_faults (tlb_sat_no_flt_set s); lookup (tlb_sat_no_flt_set s) (ASID s) (addr_val b) = Hit x; 
    is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) b)\<rbrakk> \<Longrightarrow>  x \<noteq> pt_walk (ASID s) (MEM s) (TTBR0 s) b "
  apply (frule sat_state_tlb')
  apply clarsimp
  apply (subgoal_tac "   lookup ( tlb_sat_no_flt_set s \<union> {e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e}) (ASID s) (addr_val b) = Hit (pt_walk (ASID s) (MEM s) (TTBR0 s) b)")
   prefer 2
   apply simp
  apply (thin_tac " lookup (tlb_sat_no_flt_set s) (ASID s) (addr_val b) = Hit (pt_walk (ASID s) (MEM s) (TTBR0 s) b)")
  apply (thin_tac "tlb_sat_no_flt_set s = tlb_sat_no_flt_set s \<union> {e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e}")
  apply (drule lookup_hit_union_cases')
  apply (erule disjE)
   apply (clarsimp)
   apply (subgoal_tac "\<not>is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) b)")
    apply clarsimp
   apply (subgoal_tac "pt_walk (ASID s) (MEM s) (TTBR0 s) b \<in> tlb_sat_no_flt_set s")
    prefer 2
    apply (clarsimp simp: lookup_in_tlb)
   apply (clarsimp simp:  sat_no_fault_elem)
  apply (erule disjE)
  by (clarsimp simp: lookup_in_no_flt)+
 


lemma lookup_miss_union:
  " lookup (t1 \<union> t2) a va = Miss  \<Longrightarrow>
      (lookup t1 a va = Miss \<and> lookup t2 a va = Miss) "
  apply (clarsimp simp: lookup_def entry_set_def split: if_split_asm)
  by auto
       
lemma sat_no_flt_miss_fault:
  "\<lbrakk>saturated_no_flt (typ_sat_no_flt_tlb s); no_faults (tlb_sat_no_flt_set s); 
      lookup (tlb_sat_no_flt_set s) (ASID s) (addr_val b) = Miss\<rbrakk> \<Longrightarrow> is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) b)"
  apply (subgoal_tac " lookup (tlb_sat_no_flt_set s  \<union> {e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e}) (ASID s) (addr_val b) = Miss")
   apply (thin_tac " lookup (tlb_sat_no_flt_set s) (ASID s) (addr_val b) = Miss")
   apply (drule lookup_miss_union)
   apply clarsimp
   apply (drule lookup_miss_is_fault)
   apply clarsimp
  using sat_state_tlb' by force


lemma asid_unequal_miss'':
  " a \<noteq> a1 \<Longrightarrow>
   lookup {e \<in> range (pt_walk a1 m r). \<not> is_fault e} a bb = Miss"
  apply (clarsimp simp:  lookup_def entry_set_def entry_range_asid_tags_def) 
  by force



lemma update_asid_sat_no_flt_abs_refine':
  "\<lbrakk> update_TTBR0 r (s::tlb_sat_no_flt_state) = ((), s') ;  update_TTBR0 r (t::tlb_incon_state') = ((), t'); 
     saturated_no_flt  (typ_sat_no_flt_tlb s) ; no_faults (tlb_sat_no_flt_set s); 
             tlb_rel_abs' (typ_sat_no_flt_tlb s) (typ_incon' t) \<rbrakk> \<Longrightarrow> 
                     tlb_rel_abs' (typ_sat_no_flt_tlb s') (typ_incon' t')"
  apply (clarsimp simp: update_TTBR0_tlb_sat_no_flt_state_ext_def update_TTBR0_tlb_incon_state'_ext_def tlb_rel_abs'_def)
  apply (subgoal_tac "ASID t = ASID s \<and> TTBR0 t = TTBR0 s \<and> MEM t = MEM s")
   prefer 2
   apply (clarsimp simp: tlb_rel'_absD typ_sat_no_flt_tlb_def state.defs)
  apply (rule conjI)
   apply (clarsimp simp: typ_sat_no_flt_tlb_def "state.defs")
  apply (clarsimp simp: asid_va_incon_tlb_mem_def)
  apply (rule conjI)
   prefer 2
   apply (clarsimp simp: asid_va_hit_incon_def ptable_comp_def)
   apply (subgoal_tac "b \<notin>{va. \<not> is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) va) \<and>
                    \<not> is_fault (pt_walk (ASID s) (MEM s) r va) \<and>
                    pt_walk (ASID s) (MEM s) (TTBR0 s) va \<noteq> pt_walk (ASID s) (MEM s) r va \<or>
                    \<not> is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) va) \<and> is_fault (pt_walk (ASID s) (MEM s) r va)}")
    prefer 2
    apply blast
   apply (thin_tac "(ASID s, b)
            \<notin> Pair (ASID s) `
               {va. \<not> is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) va) \<and>
                    \<not> is_fault (pt_walk (ASID s) (MEM s) r va) \<and>
                    pt_walk (ASID s) (MEM s) (TTBR0 s) va \<noteq> pt_walk (ASID s) (MEM s) r va \<or>
                    \<not> is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) va) \<and> is_fault (pt_walk (ASID s) (MEM s) r va)}")
   apply clarsimp
   apply (erule disjE , clarsimp)
    apply (drule lookup_hit_union_cases')
    apply (erule disjE, clarsimp)
     apply (subgoal_tac "x \<noteq> pt_walk (ASID s) (MEM s) (TTBR0 s) b")
      apply blast
     apply (clarsimp simp: saturated_no_flt_pt_walk)
    apply (erule disjE, clarsimp)
     apply (frule lookup_range_fault_pt_walk)
     apply (drule_tac x = "addr_val b" in bspec)
      apply (clarsimp simp: lookup_hit_entry_range)
     apply clarsimp
    apply clarsimp
    apply (frule lookup_range_fault_pt_walk)
    apply (drule_tac x = "addr_val b" in bspec)
     apply (clarsimp simp: lookup_hit_entry_range)
    apply clarsimp
   apply (erule_tac P =  "is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) b)" in  disjE)
    apply (erule disjE)
     apply (drule lookup_hit_union_cases')
     apply (erule disjE)
      apply (clarsimp simp: asid_va_incon_def)
      apply (subgoal_tac "(ASID s, b) \<in> {(asid, va). asid = ASID s \<and> (\<exists>x. lookup (tlb_sat_no_flt_set s) asid (addr_val va) = Hit x \<and> x \<noteq> pt_walk (ASID s) (MEM s) (TTBR0 s) va)}")
       apply blast
      apply (subgoal_tac "x \<noteq> pt_walk (ASID s) (MEM s) (TTBR0 s) b")
       apply clarsimp
      apply (clarsimp simp: saturated_no_flt_pt_walk)
     apply (erule disjE)
      apply (clarsimp)
      apply (frule lookup_range_fault_pt_walk)
      apply (drule_tac x = "addr_val b" in bspec)
       apply (clarsimp simp: lookup_hit_entry_range)
      apply clarsimp
     apply (clarsimp)
     apply (frule lookup_range_fault_pt_walk)
     apply (drule_tac x = "addr_val b" in bspec)
      apply (clarsimp simp: lookup_hit_entry_range)
     apply clarsimp
    apply (clarsimp simp: asid_va_incon_def)
    apply (subgoal_tac "(ASID s, b) \<in> {(asid, va). asid = ASID s \<and> (\<exists>x. lookup (tlb_sat_no_flt_set s) asid (addr_val va) = Hit x \<and> x \<noteq> pt_walk (ASID s) (MEM s) (TTBR0 s) va)}")
     apply blast
    apply clarsimp
    apply (rule_tac x = x in exI)
    apply (drule lookup_hit_union_cases')
    apply (erule disjE)
     apply (clarsimp)
    apply (erule disjE)
     apply (clarsimp)
     apply (frule lookup_range_fault_pt_walk)
     apply (drule_tac x = "addr_val b" in bspec)
      apply (clarsimp simp: lookup_hit_entry_range)
     apply clarsimp
    apply (clarsimp)
   apply (erule disjE)
    apply (clarsimp)
   apply (drule lookup_hit_union_cases')
   apply (erule disjE)
    apply (clarsimp)
    apply (drule lookup_miss_is_fault)
    apply clarsimp
   apply (erule disjE)
    apply (clarsimp)
  using sat_no_flt_miss_fault apply fastforce
   apply clarsimp
   apply (frule lookup_range_fault_pt_walk)
   apply (drule_tac x = "addr_val b" in bspec)
    apply (clarsimp simp: lookup_hit_entry_range)
   apply clarsimp
  apply (clarsimp simp:  asid_va_incon_def ptable_comp_def  asid_va_hit_incon_def)
  apply (thin_tac " t' = t\<lparr>TTBR0 := r, tlb_incon_set' :=
                                 tlb_incon_set' t \<union>
                                 Pair (ASID s) `
                                 {va. \<not> is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) va) \<and> \<not> is_fault (pt_walk (ASID s) (MEM s) r va) \<and> pt_walk (ASID s) (MEM s) (TTBR0 s) va \<noteq> pt_walk (ASID s) (MEM s) r va \<or>
                                      \<not> is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) va) \<and> is_fault (pt_walk (ASID s) (MEM s) r va)}\<rparr>")
  apply (case_tac "a = ASID s" , clarsimp)
   prefer 2
   apply (drule union_incon_cases1)
   apply (erule disjE , force)
   apply (clarsimp simp: lookup_no_flt_range_pt_walk_not_incon')
   apply (erule disjE)
    apply (clarsimp simp: asid_unequal_miss'')
   apply (erule disjE)
    apply (clarsimp simp: asid_unequal_miss'')
   apply blast
  apply (drule union_incon_cases1 , clarsimp)
  apply (erule disjE)
   apply force
  apply (erule disjE)
   apply clarsimp
   apply (subgoal_tac "b \<notin>{va. \<not> is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) va) \<and>
                    \<not> is_fault (pt_walk (ASID s) (MEM s) r va) \<and>
                    pt_walk (ASID s) (MEM s) (TTBR0 s) va \<noteq> pt_walk (ASID s) (MEM s) r va \<or>
                    \<not> is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) va) \<and> is_fault (pt_walk (ASID s) (MEM s) r va)}")
    prefer 2
    apply blast
   apply (thin_tac "(ASID s, b)
            \<notin> Pair (ASID s) `
               {va. \<not> is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) va) \<and>
                    \<not> is_fault (pt_walk (ASID s) (MEM s) r va) \<and>
                    pt_walk (ASID s) (MEM s) (TTBR0 s) va \<noteq> pt_walk (ASID s) (MEM s) r va \<or>
                    \<not> is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) va) \<and> is_fault (pt_walk (ASID s) (MEM s) r va)}")
   apply clarsimp
   apply (erule_tac P = "is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) b)" in  disjE)
    apply (erule disjE)
     apply clarsimp
     apply (subgoal_tac " lookup (tlb_sat_no_flt_set s  \<union> {e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e}) (ASID s) (addr_val b) = Hit x")
      prefer 2
  using sat_state_tlb' apply force
     apply (thin_tac " lookup (tlb_sat_no_flt_set s) (ASID s) (addr_val b) =  Hit x")
     apply (drule lookup_hit_union_cases')
     apply (erule disjE)
      apply (clarsimp) 
      apply (subgoal_tac " x \<noteq> pt_walk (ASID s) (MEM s) (TTBR0 s) b ")
       apply force
      apply (clarsimp simp: saturated_no_flt_pt_walk)
     apply (erule disjE)
      apply (clarsimp)
      apply (thin_tac "lookup {e \<in> range (pt_walk (ASID s) (MEM s) r). \<not> is_fault e} (ASID s) (addr_val b) = Hit (pt_walk (ASID s) (MEM s) r xb)")
      apply (frule lookup_range_fault_pt_walk)
      apply (drule_tac x = "addr_val b" in bspec)
       apply (clarsimp simp: lookup_hit_entry_range)
      apply clarsimp
      apply (simp add: sat_no_fault_elem)
     apply clarsimp
     apply (thin_tac "lookup {e \<in> range (pt_walk (ASID s) (MEM s) r). \<not> is_fault e} (ASID s) (addr_val b) = Hit (pt_walk (ASID s) (MEM s) r xb)")
     apply (frule lookup_range_fault_pt_walk)
     apply (drule_tac x = "addr_val b" in bspec)
      apply (clarsimp simp: lookup_hit_entry_range)
     apply clarsimp
     apply (simp add: sat_no_fault_elem)
    apply (subgoal_tac "x \<noteq> pt_walk (ASID s) (MEM s) (TTBR0 s) b")
     apply blast
    apply (clarsimp simp: saturated_no_flt_pt_walk)
   apply (erule_tac P = "is_fault (pt_walk (ASID s) (MEM s) r b)" in disjE)
    apply (frule lookup_range_fault_pt_walk)
    apply (drule_tac x = "addr_val b" in bspec)
     apply (clarsimp simp: lookup_hit_entry_range)
    apply clarsimp
   apply (erule disjE)
    apply clarsimp
    apply (frule lookup_range_fault_pt_walk)
    apply (drule_tac x = "addr_val b" in bspec)
     apply (clarsimp simp: lookup_hit_entry_range)
    apply clarsimp
   apply (subgoal_tac "pt_walk (ASID s) (MEM s) r xb = pt_walk (ASID s) (MEM s) r b")
    apply force  
   apply (frule lookup_range_fault_pt_walk)
   apply (drule_tac x = "addr_val b" in bspec)
    apply (clarsimp simp: lookup_hit_entry_range)
   apply clarsimp
  apply (erule disjE)
   prefer 2
   apply (erule disjE)
    apply force
   apply (erule disjE)
    apply (clarsimp)
    apply (clarsimp simp: lookup_no_flt_range_pt_walk_not_incon)
   apply clarsimp
   apply blast
  apply clarsimp
  by (clarsimp simp: lookup_no_flt_range_pt_walk_not_incon)



end