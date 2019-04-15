theory  Refinement

imports 
  ARMv7A_Flush_Ref
 
begin    

datatype mem_op_typ = translate     vaddr 
                | memread       "vaddr \<times> nat" 
                | memwrite      "bool list \<times> vaddr \<times> nat"

datatype mmu_op_typ = root_update  paddr 
                    | asid_update  asid 
                    | flush_addr        flush_type

datatype res_typ = PA paddr
                 | BL "bool list"
                 | UT unit


fun 
  mem_op :: "mem_op_typ \<Rightarrow> 'a::mmu state_scheme \<Rightarrow> _"
  where 
  "mem_op (translate va) s             = (PA (fst (mmu_translate va s)),            snd (mmu_translate va s))"
| "mem_op (memread (va, sz)) s         = (BL (fst (mmu_read_size (va, sz) s)),      snd (mmu_read_size (va, sz) s))"
| "mem_op (memwrite (bl, va, sz)) s    = (UT (fst (mmu_write_size (bl, va, sz) s)), snd (mmu_write_size (bl, va, sz) s))"

fun 
  mmu_op :: "mmu_op_typ \<Rightarrow> 'a::mmu state_scheme \<Rightarrow> _"
  where 
  "mmu_op (root_update rt) s    = update_TTBR0 rt s"
| "mmu_op (asid_update a) s     = update_ASID a s"
| "mmu_op (flush_addr f) s      = flush f s"



fun
  consistent_sat :: "mem_op_typ \<Rightarrow> 'a::mmu sat_tlb_state_scheme \<Rightarrow> bool"
where
  "consistent_sat (translate va) s             =  consistent ( typ_sat_tlb s) va"
| "consistent_sat (memread (va, sz)) s         =  consistent ( typ_sat_tlb s) va"
| "consistent_sat (memwrite (bl, va, sz)) s    =  consistent ( typ_sat_tlb s) va"



lemma  addr_trans_sat:
  "\<lbrakk> mmu_translate va s = (pa, s');  mmu_translate va t = (pa', t'); 
consistent (typ_sat_tlb t) va; tlb_rel_sat (typ_non_det_tlb s) (typ_sat_tlb t)  \<rbrakk> \<Longrightarrow>
      pa' = pa \<and> tlb_rel_sat (typ_non_det_tlb s') (typ_sat_tlb t')"
  using mmu_translate_non_det_sat_refine [simplified split_def Let_def, rotated 2]  by force

lemma read_trans_sat:
  "\<lbrakk>mmu_read_size (va, sz) s = (val, s');  mmu_read_size (va, sz) t = (val', t'); consistent (typ_sat_tlb t) va;
              tlb_rel_sat (typ_non_det_tlb s) (typ_sat_tlb t)\<rbrakk> \<Longrightarrow>  
                     val' = val \<and> tlb_rel_sat (typ_non_det_tlb s') (typ_sat_tlb t') "
  using mmu_read_non_det_sat_refine by blast


lemma mem_refine_sat:
    "\<lbrakk> mem_op f s = (res, s') ; mem_op f t = (res', t'); 
          consistent_sat f t ; tlb_rel_sat (typ_non_det_tlb s) (typ_sat_tlb t) \<rbrakk> \<Longrightarrow> 
                 res' = res \<and> tlb_rel_sat (typ_non_det_tlb s') (typ_sat_tlb t')"
  apply (cases f; clarsimp)
    apply (rename_tac va)
    apply (rule_tac va = va and s = s and t = t in  addr_trans_sat; clarsimp?) 
   apply (rename_tac va sz)
   apply (rule_tac read_trans_sat; force?) 
  apply (rename_tac bl va sz)
  apply (rule_tac val = bl and va = va and sz = sz and s = s and t = t in mmu_write_non_det_sat_refine; force?) 
   apply (metis eq_snd_iff old.unit.exhaust)    
  by (metis eq_snd_iff old.unit.exhaust)


lemma mmu_refine_sat:
    "\<lbrakk> mmu_op f s = ((), s') ; mmu_op f t = ((), t'); 
           tlb_rel_sat (typ_non_det_tlb s) (typ_sat_tlb t) \<rbrakk> \<Longrightarrow> 
               tlb_rel_sat (typ_non_det_tlb s') (typ_sat_tlb t')"
  apply (cases f; clarsimp)
     apply (rename_tac rt)
     apply (rule_tac r = rt and s = s and t= t in update_root_non_det_sat_refine;  clarsimp simp: eq_snd_iff) 
    apply (rename_tac a)
    apply (rule_tac a = a and s = s and t= t in update_asid_non_det_sat_refine;  clarsimp simp: eq_snd_iff) 
   apply (rename_tac ft)
  by (rule_tac f = ft and s = s and t= t in flush_det_sat_refine;  clarsimp simp: eq_snd_iff) 


fun
  consistent_set :: "mem_op_typ \<Rightarrow> _"
where
  "consistent_set (translate va) s             =  (va \<notin> iset(set_tlb s))"
| "consistent_set (memread (va, sz)) s         =  (va \<notin> iset(set_tlb s))"
| "consistent_set (memwrite (bl, va, sz)) s    =  (va \<notin> iset(set_tlb s))"



lemma  addr_trans_set:
  "\<lbrakk> mmu_translate va s = (pa, s');  mmu_translate va t = (pa', t'); 
    va \<notin> iset(set_tlb t); tlb_rel_abs (typ_sat_tlb s) (typ_set_tlb t)  \<rbrakk> \<Longrightarrow>
      pa' = pa \<and> tlb_rel_abs (typ_sat_tlb s') (typ_set_tlb t')"
  using mmu_translate_sat_incon_refine [simplified split_def Let_def, rotated 2]  apply auto by blast+


lemma read_trans_set:
  "\<lbrakk>mmu_read_size (va, sz) s = (val, s');  mmu_read_size (va, sz) t = (val', t'); va \<notin> iset(set_tlb t);
              tlb_rel_abs (typ_sat_tlb s) (typ_set_tlb t)\<rbrakk> \<Longrightarrow>  
                     val' = val \<and> tlb_rel_abs (typ_sat_tlb s') (typ_set_tlb t') "
  using mmu_read_sat_incon_refine by blast


lemma mem_refine_set:
    "\<lbrakk> mem_op f s = (res, s') ; mem_op f t = (res', t'); 
          consistent_set f t ; tlb_rel_abs (typ_sat_tlb s) (typ_set_tlb t) \<rbrakk> \<Longrightarrow> 
                 res' = res \<and> tlb_rel_abs (typ_sat_tlb s') (typ_set_tlb t')"
  apply (cases f; clarsimp)
    apply (rename_tac va)
    apply (rule_tac va = va and s = s and t = t in  addr_trans_set; clarsimp?) 
   apply (rename_tac va sz)
   apply (rule_tac read_trans_set; force?) 
  apply (rename_tac bl va sz)
  apply (rule_tac val = bl and va = va and sz = sz and s = s and t = t in mmu_write_sat_incon_refine; force?) 
   apply (metis eq_snd_iff old.unit.exhaust)    
  by (metis eq_snd_iff old.unit.exhaust)


lemma mmu_refine_set:
    "\<lbrakk> mmu_op f s = ((), s') ; mmu_op f t = ((), t'); 
           tlb_rel_abs (typ_sat_tlb s) (typ_set_tlb t) \<rbrakk> \<Longrightarrow> 
               tlb_rel_abs (typ_sat_tlb s') (typ_set_tlb t')"
  apply (cases f; clarsimp)
     apply (rename_tac rt)
     apply (rule_tac r = rt and s = s and t= t in update_root_sat_incon_refine;  clarsimp simp: eq_snd_iff) 
    apply (rename_tac a)
    apply (rule_tac a = a and s = s and t= t in update_asid_sat_incon_refine;  clarsimp simp: eq_snd_iff) 
   apply (rename_tac ft)
  by (rule_tac f = ft and s = s and t= t in flush_sat_incon_refine;  clarsimp simp: eq_snd_iff) 
 



definition 
  tlb_rel :: "_"
where                                                                
  "tlb_rel r t \<equiv> \<exists>(s:: unit sat_tlb_state_scheme).  
                    tlb_rel_sat r (typ_sat_tlb s) \<and> 
                           tlb_rel_abs (typ_sat_tlb s) t"


lemmas  abc =  mmu_translate_non_det_sat_refine [simplified split_def Let_def, rotated 2]   


lemma address_refinement:
  "\<lbrakk> mmu_translate va r = (pa, r');  mmu_translate va t = (pa', t') ;
           va \<notin> iset(set_tlb t) ; tlb_rel (typ_non_det_tlb r) (typ_set_tlb t) \<rbrakk> \<Longrightarrow> 
                               pa = pa' \<and>   tlb_rel  (typ_non_det_tlb r') (typ_set_tlb t') " 
  apply (clarsimp simp: tlb_rel_def)
  apply (frule_tac s = s and pa = "fst(mmu_translate va s)" and s' = "snd(mmu_translate va s)" in 
      mmu_translate_sat_incon_refine [rotated]; clarsimp?)
  apply (frule_tac va = va and pa =  "fst(mmu_translate va r)" and s' = "snd(mmu_translate va r)"in  abc; clarsimp?)
  using tlb_rel_abs_consistent apply force
  by force
  
  


lemma read_refinement:
  "\<lbrakk> mmu_read_size (va, sz) r = (val, r');  mmu_read_size (va, sz) t = (val', t');
           va \<notin> iset(set_tlb t) ; tlb_rel (typ_non_det_tlb r) (typ_set_tlb t) \<rbrakk> \<Longrightarrow> 
                               val = val' \<and>  tlb_rel  (typ_non_det_tlb r') (typ_set_tlb t') " 
  apply (clarsimp simp: tlb_rel_def)
  apply (frule_tac s = s and val = "fst(mmu_read_size (va, sz) s)" and s' = "snd(mmu_read_size (va, sz) s)" in 
      mmu_read_sat_incon_refine [rotated]; clarsimp?)
  apply (frule_tac va = va and sz= sz and val =  "fst(mmu_read_size (va, sz)r)" and s' = "snd(mmu_read_size (va, sz) r)" and 
      val' =  "fst(mmu_read_size (va, sz)s)"  and t' = "snd(mmu_read_size (va, sz) s)" in  mmu_read_non_det_sat_refine [rotated 2]; clarsimp?)
  using tlb_rel_abs_consistent apply force
  using  tlb_rel_sat_consistent by fastforce
   

lemma write_refinement:
  "\<lbrakk> mmu_write_size (val,va, sz) r = ((), r');  mmu_write_size (val,va, sz)  t = ((), t');
            va \<notin> iset(set_tlb t) ; tlb_rel (typ_non_det_tlb r) (typ_set_tlb t) \<rbrakk> \<Longrightarrow> 
                              tlb_rel  (typ_non_det_tlb r') (typ_set_tlb t') " 
  apply (clarsimp simp: tlb_rel_def)
  apply (frule_tac s = s and s' = "snd(mmu_write_size (val,va, sz) s)" in 
      mmu_write_sat_incon_refine [rotated]; clarsimp?)
   apply (metis eq_snd_iff old.unit.exhaust)
  apply (frule_tac va = va and sz= sz  and s' = "snd(mmu_write_size (val,va, sz)  r)" and t' = "snd(mmu_write_size (val,va, sz)  s)" and val = val in  
      mmu_write_non_det_sat_refine [rotated]; clarsimp?)
  using tlb_rel_abs_consistent apply force 
    apply (metis eq_snd_iff old.unit.exhaust)
  by (metis eq_snd_iff old.unit.exhaust)
 



lemma mem_refine:
    "\<lbrakk> mem_op f r = (res, r') ; mem_op f t = (res', t'); 
          consistent_set f t ; tlb_rel (typ_non_det_tlb r) (typ_set_tlb t) \<rbrakk> \<Longrightarrow> 
                 res = res' \<and> tlb_rel (typ_non_det_tlb r') (typ_set_tlb t')"
  apply (cases f; clarsimp)
    apply (rename_tac va)
    apply (rule_tac  va = va and  r = r and t = t in address_refinement; force?) 
   apply (rename_tac va sz)
   apply (rule_tac read_refinement; force?) 
  apply (rename_tac bl va sz)
  apply (rule_tac val = bl and va = va and sz = sz and r = r and t = t in write_refinement; force?) 
   apply (metis eq_snd_iff old.unit.exhaust)    
  by (metis eq_snd_iff old.unit.exhaust)



lemma root_refinement:
  "\<lbrakk> update_TTBR0 rt r = ((), r');  update_TTBR0 rt t = ((), t') ; tlb_rel (typ_non_det_tlb r) (typ_set_tlb t) \<rbrakk> \<Longrightarrow> 
                               tlb_rel  (typ_non_det_tlb r') (typ_set_tlb t') " 
  apply (clarsimp simp: tlb_rel_def)
  apply (frule_tac s = s  and s' = "snd (update_TTBR0 rt s)"  in update_root_sat_incon_refine [rotated]; clarsimp?)
   apply (metis eq_snd_iff old.unit.exhaust)  
  apply (frule_tac  r = rt and s' ="snd ( update_TTBR0 rt r) " and t' = "snd (update_TTBR0 rt s)" in update_root_non_det_sat_refine [rotated 2]; clarsimp?)
    apply (metis eq_snd_iff old.unit.exhaust)     
  by (metis eq_snd_iff old.unit.exhaust)  


lemma asid_refinement:
  "\<lbrakk> update_ASID a r = ((), r');  update_ASID a t = ((), t') ; tlb_rel (typ_non_det_tlb r) (typ_set_tlb t) \<rbrakk> \<Longrightarrow> 
                               tlb_rel  (typ_non_det_tlb r') (typ_set_tlb t') " 
  apply (clarsimp simp: tlb_rel_def)
  apply (frule_tac s = s  and s' = "snd (update_ASID a s)"  in update_asid_sat_incon_refine [rotated]; clarsimp?)
   apply (metis eq_snd_iff old.unit.exhaust)  
  apply (frule_tac  a = a and s' ="snd ( update_ASID a r) " and t' = "snd (update_ASID a s)" in update_asid_non_det_sat_refine [rotated 2]; clarsimp?)
    apply (metis eq_snd_iff old.unit.exhaust)     
   by (metis eq_snd_iff old.unit.exhaust)  
 


lemma flush_refinement:
  "\<lbrakk> flush f r = ((), r');  flush f t = ((), t') ; tlb_rel (typ_non_det_tlb r) (typ_set_tlb t) \<rbrakk> \<Longrightarrow> 
                               tlb_rel  (typ_non_det_tlb r') (typ_set_tlb t') " 
  apply (clarsimp simp: tlb_rel_def)
  apply (frule_tac s = s  and s' = "snd (flush f s)"  in flush_sat_incon_refine [rotated]; clarsimp?)
   apply (metis eq_snd_iff old.unit.exhaust)  
  apply (frule_tac f= f and s' ="snd ( flush f r) " and t' = "snd (flush f s)" in flush_det_sat_refine [rotated 2]; clarsimp?)
    apply (metis eq_snd_iff old.unit.exhaust)     
  by (metis eq_snd_iff old.unit.exhaust)  
 

  
lemma mmu_refine:
    "\<lbrakk> mmu_op f r = ((), r') ; mmu_op f t = ((), t'); 
         tlb_rel (typ_non_det_tlb r) (typ_set_tlb t) \<rbrakk> \<Longrightarrow> 
                  tlb_rel (typ_non_det_tlb r') (typ_set_tlb t')"
  apply (cases f; clarsimp)
     apply (rename_tac rt)
     apply (rule_tac  rt = rt and  r = r and t = t in root_refinement; force?) 
    apply (simp add: asid_refinement)
  using flush_refinement by blast
  


end