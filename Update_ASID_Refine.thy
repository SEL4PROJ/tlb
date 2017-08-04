theory Update_ASID_Refine

imports MMU_ARM_Refine_No_Fault

begin               



class update_asid =
  fixes update_asid :: "asid \<Rightarrow> 'a state_scheme \<Rightarrow>  unit \<times> 'a state_scheme" 


instantiation tlb_state_ext :: (type) update_asid   
begin
  definition   
  "(update_asid a :: ('a tlb_state_scheme \<Rightarrow> _))  = update_state (\<lambda>s. s\<lparr> ASID := a \<rparr>) "

thm update_asid_tlb_state_ext_def
(* print_context *)                      
  instance ..
end


instantiation tlb_det_state_ext :: (type) update_asid   
begin
  definition   
  "(update_asid a :: ('a tlb_det_state_scheme \<Rightarrow> _))  = update_state (\<lambda>s. s\<lparr> ASID := a \<rparr>) "

thm update_asid_tlb_det_state_ext_def
(* print_context *)                      
  instance ..
end


instantiation tlb_sat_no_flt_state_ext :: (type) update_asid   
begin
  definition   
  "(update_asid a :: ('a tlb_sat_no_flt_state_scheme \<Rightarrow> _))  = do {
      update_state (\<lambda>s. s\<lparr> ASID := a \<rparr>);
      mem   <- read_state MEM;
      ttbr0 <- read_state TTBR0;
      let all_non_fault_entries = {e\<in>pt_walk a mem ttbr0 ` UNIV. \<not>is_fault e};
      tlb0   <- read_state tlb_sat_no_flt_set;
      let tlb = tlb0 \<union> all_non_fault_entries; 
      update_state (\<lambda>s. s\<lparr> tlb_sat_no_flt_set := tlb \<rparr>)} "

thm update_asid_tlb_sat_no_flt_state_ext_def
(* print_context *)                      
  instance ..
end



instantiation tlb_incon_state'_ext :: (type) update_asid   
begin
  definition   
  "(update_asid a :: ('a tlb_incon_state'_scheme \<Rightarrow> _))  = do {
      update_state (\<lambda>s. s\<lparr> ASID := a \<rparr>)} "
thm update_asid_tlb_incon_state'_ext_def
print_context                     
  instance ..
end





(* the goal is to have the final assumption of the incon set, that we are using in the logic, that
       should say that the intersection of updated asid and the iset is empty *)

lemma update_asid_non_det_det_refine:
  "\<lbrakk> update_asid a (s::tlb_state) = ((), s') ;  update_asid a (t::tlb_det_state) = ((), t'); 
         tlb_rel (typ_tlb s) (typ_det_tlb t); \<forall>va. consistent0 (MEM t) a (TTBR0 t) ( tlb_det_set t) va \<rbrakk> \<Longrightarrow> 
                  tlb_rel (typ_tlb s') (typ_det_tlb t') \<and> (\<forall>va. consistent0 (MEM t') a (TTBR0 t') (tlb_det_set t') va) "
  apply (clarsimp simp: update_asid_tlb_state_ext_def update_asid_tlb_det_state_ext_def tlb_rel_def) 
  by (cases s, cases t , clarsimp simp: state.defs)

thm entry_range_single_element


lemma lookup_hit_union_cases_rule:
  " (lookup t1 a va = Hit x \<and> lookup t2 a va = Miss)  \<or>
    (lookup t2 a va = Hit x \<and> lookup t1 a va = Miss)  \<or>
    (lookup t1 a va = Hit x \<and> lookup t2 a va = Hit x) \<Longrightarrow>  lookup (t1 \<union> t2) a va = Hit x"
  apply safe
    apply ((clarsimp simp: lookup_def entry_set_def split: split_if_asm,(safe ; force))+) [2]
  apply (clarsimp simp: lookup_def entry_set_def split: split_if_asm)
  apply rule
   by (clarsimp simp: entry_set_def, frule  entry_range_single_element, frule  entry_range_single_element, (safe ; force))+


lemma lookup_not_miss_hit_incon:
  "\<lbrakk>lookup t a v \<noteq> Miss\<rbrakk> \<Longrightarrow> (\<exists>x. lookup t a v = Hit x) \<or> lookup t a v = Incon"
  by (clarsimp simp: lookup_def split:split_if_asm)


lemma lookup_hit_mis_hit':
  "\<lbrakk>lookup (t1 \<union> t2) a va = Hit x ; lookup t1 a va = Miss\<rbrakk>  \<Longrightarrow> lookup t2 a va = Hit x   "
  apply (clarsimp simp: lookup_def entry_set_def split: split_if_asm)
  by (safe ; force)



lemma lookup_union_miss_not_miss_cases:
  "\<lbrakk>lookup t a v = Miss; lookup (t \<union> t') a v \<noteq> Miss\<rbrakk> \<Longrightarrow>  (\<exists>x. lookup t' a v = Hit x) \<or> lookup t' a v = Incon"
  apply (drule lookup_not_miss_hit_incon)
  apply (erule disjE)
   apply (rule disjI1 , clarsimp)
   apply (rule_tac x = x in exI)
   apply (drule lookup_hit_mis_hit' ; clarsimp)
  apply (rule disjI2)
  apply (clarsimp simp: lookup_def entry_set_def split: split_if_asm)
  by auto



lemma lookup_not_incon_hit_miss:
  "\<lbrakk>lookup t a v \<noteq> Incon\<rbrakk> \<Longrightarrow> (\<exists>x. lookup t a v = Hit x) \<or> lookup t a v = Miss"
  by (clarsimp simp: lookup_def split:split_if_asm)

lemma lookup_not_incon_hit_miss':
  "(\<exists>x. lookup t a v = Hit x) \<or> lookup t a v = Miss  \<Longrightarrow> lookup t a v \<noteq> Incon "
  by (clarsimp simp: lookup_def split:split_if_asm)



lemma  update_asid_det_sat_no_flt_refine:
  "\<lbrakk> update_asid a (s::tlb_det_state) = ((), s') ;  update_asid a (t::tlb_sat_no_flt_state) = ((), t'); 
         tlb_rel_sat_no_flt (typ_det_tlb s) (typ_sat_no_flt_tlb t); \<forall>va. consistent0 (MEM t) a (TTBR0 t) (tlb_sat_no_flt_set t) va \<rbrakk> \<Longrightarrow> 
                  tlb_rel_sat_no_flt (typ_det_tlb s') (typ_sat_no_flt_tlb t') \<and> (\<forall>va. consistent0 (MEM t') a (TTBR0 t') (tlb_sat_no_flt_set t') va)"
  apply (clarsimp simp: update_asid_tlb_det_state_ext_def update_asid_tlb_sat_no_flt_state_ext_def)
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
   apply (subgoal_tac "\<not>is_fault (pt_walk a (MEM t) (TTBR0 t) va)")
    apply (clarsimp simp: lookup_range_pt_walk_hit_no_flt)
   apply (subgoal_tac "pt_walk a (MEM t) (TTBR0 t) va \<in> tlb_sat_no_flt_set t")
    apply (clarsimp simp: no_faults_def)
   apply (clarsimp simp: lookup_in_tlb)
  apply (simp add: consistent0_def)
  apply (rule disjCI)
  apply (frule_tac t' = "{e \<in> range (pt_walk a (MEM t) (TTBR0 t)). \<not> is_fault e}" in lookup_union_miss_not_miss_cases)
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
  "\<lbrakk> update_asid a (s::tlb_sat_no_flt_state) = ((), s') ;  update_asid a (t::tlb_incon_state') = ((), t'); 
       saturated_no_flt (typ_sat_no_flt_tlb (s\<lparr>ASID := a\<rparr>)) ; 
        (* coming from 'update_asid_det_sat_no_flt_refine' theorem i.e.
       tlb_rel_sat_no_flt (typ_det_tlb s') (typ_sat_no_flt_tlb t') states the saturated assumption with the updated asid  *) 
         tlb_rel_abs' (typ_sat_no_flt_tlb (s\<lparr>ASID := a\<rparr>)) (typ_incon' t);   \<forall>va. (a, va) \<notin> (tlb_incon_set' t) \<rbrakk> \<Longrightarrow> 
                    tlb_rel_abs' (typ_sat_no_flt_tlb s') (typ_incon' t') \<and>  (\<forall>va. (a, va) \<notin> (tlb_incon_set' t'))"
  apply (subgoal_tac "tlb_sat_no_flt_set s = tlb_sat_no_flt_set s \<union> {e \<in> range (pt_walk a (MEM s) (TTBR0 s)). \<not> is_fault e} ")
   apply rule
    prefer 2
    apply (clarsimp simp: update_asid_tlb_sat_no_flt_state_ext_def update_asid_tlb_incon_state'_ext_def)
   apply (clarsimp simp: update_asid_tlb_sat_no_flt_state_ext_def update_asid_tlb_incon_state'_ext_def)
   apply (clarsimp simp: tlb_rel_abs'_def)
   apply (cases s, cases t , clarsimp simp: state.defs)
  apply (clarsimp simp:  tlb_rel_abs'_def saturated_no_flt_def) apply force
done
 

(*
lemma
  "\<lbrakk>tlb_sat_no_flt_set s = tlb_sat_no_flt_set s \<union> {e \<in> range (pt_walk a (MEM s) (TTBR0 s)). \<not> is_fault e}; saturated_no_flt (typ_sat_no_flt_tlb s); no_faults (tlb_sat_no_flt_set s);
              lookup (tlb_sat_no_flt_set s) a b = Hit x;  x \<noteq> pt_walk a (MEM s) (TTBR0 s) (Addr b)\<rbrakk>  \<Longrightarrow> False"
  apply (subgoal_tac "saturated_no_flt (typ_sat_no_flt_tlb s\<lparr>ASID := a\<rparr>)")
   prefer 2
   apply (clarsimp simp: saturated_no_flt_def)
   apply force
oops


lemma 
  "\<lbrakk> \<forall>va. (a , addr_val va) \<notin>  asid_va_incon_tlb_mem (typ_sat_no_flt_tlb s) \<rbrakk> \<Longrightarrow> 
           \<forall>va. consistent0 (MEM s) a (TTBR0 s) (tlb_sat_no_flt_set s) va "
  apply (clarsimp simp: asid_va_incon_tlb_mem_def asid_va_incon_def asid_va_hit_incon_def)
  apply (clarsimp simp: lookup_def consistent0_def split: split_if_asm)  apply auto
  done

lemma tlb_rel_abs_consistent':
  "\<lbrakk> \<forall>va. (a, va) \<notin> (tlb_incon_set' t) ;   tlb_sat_no_flt_set s = tlb_sat_no_flt_set s \<union> {e \<in> range (pt_walk a (MEM s) (TTBR0 s)). \<not> is_fault e} ;
                tlb_rel_abs' (typ_sat_no_flt_tlb s) (typ_incon' t) \<rbrakk>  \<Longrightarrow> 
             \<forall>va. consistent0 (MEM s) a (TTBR0 s) (tlb_sat_no_flt_set s) va  " 
  apply (rule not_member_incon_consistent' ; clarsimp)
  apply (clarsimp simp: tlb_rel_abs'_def)
  apply (subgoal_tac "ASID s = ASID t" , simp)
   apply blast
  apply (cases s , cases t , clarsimp simp: state.defs)
oops


lemma 
  "\<lbrakk> update_asid a (s::tlb_sat_no_flt_state) = ((), s') ;  update_asid a (t::tlb_incon_state') = ((), t'); 
            tlb_sat_no_flt_set s = tlb_sat_no_flt_set s \<union> {e \<in> range (pt_walk a (MEM s) (TTBR0 s)). \<not> is_fault e} ; 
       saturated_no_flt (typ_sat_no_flt_tlb s) ; no_faults (tlb_sat_no_flt_set s);
         tlb_rel_abs' (typ_sat_no_flt_tlb s) (typ_incon' t);   \<forall>va. (a, va) \<notin> (tlb_incon_set' t) \<rbrakk> \<Longrightarrow> 
                    tlb_rel_abs' (typ_sat_no_flt_tlb s') (typ_incon' t') \<and>  (\<forall>va. (a, va) \<notin> (tlb_incon_set' t'))"
  apply rule
   prefer 2
   apply (clarsimp simp: update_asid_tlb_sat_no_flt_state_ext_def update_asid_tlb_incon_state'_ext_def)
  apply (clarsimp simp: update_asid_tlb_sat_no_flt_state_ext_def update_asid_tlb_incon_state'_ext_def)
  apply (clarsimp simp: tlb_rel_abs'_def)
  apply rule
   apply (cases s, cases t , clarsimp simp: state.defs)
  apply (simp add: asid_va_incon_tlb_mem_def)
  apply (clarsimp simp: asid_va_hit_incon_def)
  apply (clarsimp simp: lookup_def split: split_if_asm)
oops
*)




end

