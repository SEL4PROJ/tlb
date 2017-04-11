theory Prog_Refine

imports Program_Logic

begin

  
definition 
  tlb_rel_prg :: "tlb_entry set state_scheme \<Rightarrow> (asid \<times> va) set state_scheme \<Rightarrow> bool"
where                                                                
  "tlb_rel_prg s t \<equiv> state.truncate s = state.truncate t \<and> asid_va_incon (state.more s) = state.more t"



lemma
  "\<lbrakk>(c, s) \<Rightarrow> s' ;  (c, t) \<Rightarrow> t' ; tlb_rel_prg (typ_tlb s) (typ_incon t)\<rbrakk> \<Longrightarrow> 
    tlb_rel_prg (typ_tlb (the s')) (typ_incon (the t'))" 
  apply (induction arbitrary:  t t' rule: big_step_induct )
             apply simp_all
             apply clarsimp
            apply (erule AssignE)
             apply clarsimp
       apply (clarsimp simp: tlb_rel_prg_def)
       apply (rule conjI)
        apply (clarsimp simp: state.defs the_def) 
oops


lemma
  "\<lbrakk>(c, s) \<Rightarrow> s' ;  (c, t) \<Rightarrow> t' ; tlb_rel_prg (typ_tlb s) (typ_incon t) ; s' \<noteq> None ; t' \<noteq> None\<rbrakk> \<Longrightarrow> 
   state.truncate (the s') = state.truncate (the t')" 
  apply (induct c arbitrary: s s' t t')
      apply (simp_all)
      apply (erule SkipE)
      apply (erule SkipE)
      apply (simp add: tlb_rel_prg_def)
     apply (erule AssignE)
      apply clarsimp
     apply (erule AssignE)
      apply clarsimp
     apply (clarsimp)

  apply (induction arbitrary:  t t' rule: big_step_induct )
             apply simp_all
           
             apply clarsimp
            apply (erule AssignE)
             apply clarsimp
       apply (clarsimp simp: tlb_rel_prg_def)
       apply (rule conjI)
        apply (clarsimp simp: state.defs the_def) 
       
 
             apply simp_all

  apply (induct c arbitrary: s s' t t')
      apply (erule SkipE)
      apply (erule SkipE)
      apply simp
     apply (erule AssignE)
     apply (erule AssignE)
  apply simp_all
  prefer 2

oops

(*tlb_rel_flt (typ_tlb s') (typ_det_tlb t') *)

end