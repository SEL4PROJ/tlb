theory Refinement_MMU_No_ASIDs

imports  Update_Root_Ref

begin    


definition 
  tlb_rel :: "(unit tlb_entry set)  state_scheme  \<Rightarrow> (vaddr set) state_scheme \<Rightarrow> bool"
where                                                                
  "tlb_rel r t \<equiv> \<exists>(s:: unit det_tlb_state_scheme) (s':: unit sat_tlb_state_scheme).  
                    tlb_rel_det r (typ_det_tlb s) \<and> tlb_rel_sat (typ_det_tlb s) (typ_sat_tlb s') \<and> 
                           tlb_rel_abs (typ_sat_tlb s') t"


lemmas  abc =  mmu_translate_det_sat_refine [simplified split_def Let_def, rotated 2]   
lemmas  abc' =  mmu_translate_non_det_det_refine [simplified split_def Let_def, rotated 2]


lemma address_refinement:
  "\<lbrakk> mmu_translate va r = (pa, r');  mmu_translate va t = (pa', t') ;
           va \<notin> set_tlb t ; tlb_rel (typ_non_det_tlb r) (typ_set_tlb t) \<rbrakk> \<Longrightarrow> 
                               pa = pa' \<and>   tlb_rel  (typ_non_det_tlb r') (typ_set_tlb t') " 
  apply (clarsimp simp: tlb_rel_def)
  apply (frule_tac s = s' and pa = "fst(mmu_translate va s')" and s' = "snd(mmu_translate va s')" in 
      mmu_translate_sat_incon_refine [rotated]; clarsimp?)
  apply (frule_tac va = va and pa =  "fst(mmu_translate va s)" and s' = "snd(mmu_translate va s)"in  abc; clarsimp?)
  using tlb_rel_abs_consistent apply force
  apply (frule_tac va = va and pa =  "fst(mmu_translate va r)" and s' = "snd(mmu_translate va r)"in  abc'; clarsimp?)
   apply (smt det_tlb_more mmu_incon_eq_asid_root_mem mmu_translate_sat_const_tlb sat_tlb_more tlb_rel_absD tlb_rel_sat_consistent typ_det_prim_parameter typ_sat_prim_parameter typ_set_prim_parameter)
  by force


lemma read_refinement:
  "\<lbrakk> mmu_read_size (va, sz) r = (val, r');  mmu_read_size (va, sz) t = (val', t');
           va \<notin> set_tlb t ; tlb_rel (typ_non_det_tlb r) (typ_set_tlb t) \<rbrakk> \<Longrightarrow> 
                               val = val' \<and>  tlb_rel  (typ_non_det_tlb r') (typ_set_tlb t') " 
  apply (clarsimp simp: tlb_rel_def)
  apply (frule_tac s = s' and val = "fst(mmu_read_size (va, sz) s')" and s' = "snd(mmu_read_size (va, sz) s')" in 
      mmu_read_sat_incon_refine [rotated]; clarsimp?)
  apply (frule_tac va = va and sz= sz and val =  "fst(mmu_read_size (va, sz)s)" and s' = "snd(mmu_read_size (va, sz) s)" and 
      val' =  "fst(mmu_read_size (va, sz)s')"  and t' = "snd(mmu_read_size (va, sz) s')" in  mmu_read_non_det_sat_refine [rotated 2]; clarsimp?)
  using tlb_rel_abs_consistent apply force

  apply (frule_tac va = va and sz= sz and val =  "fst(mmu_read_size (va, sz)r)" and s' = "snd(mmu_read_size (va, sz) r)" and 
      val' =  "fst(mmu_read_size (va, sz)s)"  and t' = "snd(mmu_read_size (va, sz) s)" in  mmu_read_non_det_det_refine [rotated 2]; clarsimp?)
  using tlb_rel_abs_consistent tlb_rel_sat_consistent apply fastforce
   apply (metis (no_types) prod.collapse)
  by force

lemma write_refinement:
  "\<lbrakk> mmu_write_size (val,va, sz) r = ((), r');  mmu_write_size (val,va, sz)  t = ((), t');
           va \<notin> set_tlb t ; tlb_rel (typ_non_det_tlb r) (typ_set_tlb t) \<rbrakk> \<Longrightarrow> 
                              tlb_rel  (typ_non_det_tlb r') (typ_set_tlb t') " 
  apply (clarsimp simp: tlb_rel_def)
  apply (frule_tac s = s' and s' = "snd(mmu_write_size (val,va, sz) s')" in 
      mmu_write_sat_incon_refine [rotated]; clarsimp?)
   apply (metis eq_snd_iff old.unit.exhaust)
  apply (frule_tac va = va and sz= sz  and s' = "snd(mmu_write_size (val,va, sz)  s)" and t' = "snd(mmu_write_size (val,va, sz)  s')" and val = val in  
      mmu_write_det_sat_refine [rotated]; clarsimp?)
  using tlb_rel_abs_consistent apply force 
    apply (metis eq_snd_iff old.unit.exhaust)
   apply (metis eq_snd_iff old.unit.exhaust)
  apply (frule_tac va = va and sz= sz and val =  val and s' = "snd(mmu_write_size (val,va, sz) r)" and 
      t' = "snd(mmu_write_size (val,va, sz) s)" in  mmu_write_non_det_det_refine [rotated]; clarsimp?)
  using tlb_rel_abs_consistent tlb_rel_sat_consistent apply fastforce
   apply (metis eq_snd_iff old.unit.exhaust)
  by force



datatype op_typ = translate     vaddr 
                | memread       "vaddr \<times> nat" 
                | memwrite      "bool list \<times> vaddr \<times> nat"


datatype res_typ = PA paddr
                 | BL "bool list"
                 | UT unit

fun 
  mem_op :: "op_typ \<Rightarrow> 'a::mmu state_scheme \<Rightarrow> _"
  where 
  "mem_op (translate va) s             = (PA (fst (mmu_translate va s)),            snd (mmu_translate va s))"
| "mem_op (memread (va, sz)) s         = (BL (fst (mmu_read_size (va, sz) s)),      snd (mmu_read_size (va, sz) s))"
| "mem_op (memwrite (bl, va, sz)) s    = (UT (fst (mmu_write_size (bl, va, sz) s)), snd (mmu_write_size (bl, va, sz) s))"


fun
  consistent_f :: "op_typ \<Rightarrow> 'a::mmu set_tlb_state_scheme \<Rightarrow> bool"
where
  "consistent_f (translate va) s             =  (va \<notin> set_tlb s)"
| "consistent_f (memread (va, sz)) s         =  (va \<notin> set_tlb s)"
| "consistent_f (memwrite (bl, va, sz)) s    =  (va \<notin> set_tlb s)"


lemma mem_refine:
    "\<lbrakk> mem_op f r = (res, r') ; mem_op f t = (res', t'); 
          consistent_f f t ; tlb_rel (typ_non_det_tlb r) (typ_set_tlb t) \<rbrakk> \<Longrightarrow> 
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



datatype op_typ' = root_update  paddr 
                 | flush_op        flush_type


lemma root_refinement:
  "\<lbrakk> update_TTBR0 rt r = ((), r');  update_TTBR0 rt t = ((), t') ; tlb_rel (typ_non_det_tlb r) (typ_set_tlb t) \<rbrakk> \<Longrightarrow> 
                               tlb_rel  (typ_non_det_tlb r') (typ_set_tlb t') " 
  apply (clarsimp simp: tlb_rel_def)
  apply (frule_tac s = s'  and s' = "snd (update_TTBR0 rt s')"  in update_root_sat_incon_refine [rotated]; clarsimp?)
   apply (metis eq_snd_iff old.unit.exhaust)  
  apply (frule_tac  r = rt and s' ="snd ( update_TTBR0 rt s) " and t' = "snd (update_TTBR0 rt s')" in update_root_det_sat_refine [rotated 2]; clarsimp?)
    apply (metis eq_snd_iff old.unit.exhaust)     
   apply (metis eq_snd_iff old.unit.exhaust)  
  apply (frule_tac  r = rt and s' ="snd ( update_TTBR0 rt r) " and t' = "snd (update_TTBR0 rt s)" in update_root_non_det_det_refine [rotated 2]; clarsimp?)
   apply (metis eq_snd_iff old.unit.exhaust)  
  by force
  
lemma flush_refinement:
  "\<lbrakk> flush f r = ((), r');  flush f t = ((), t') ; tlb_rel (typ_non_det_tlb r) (typ_set_tlb t) \<rbrakk> \<Longrightarrow> 
                               tlb_rel  (typ_non_det_tlb r') (typ_set_tlb t') " 
  apply (clarsimp simp: tlb_rel_def)
  apply (frule_tac s = s'  and s' = "snd (flush f s')"  in flush_sat_incon_refine [rotated]; clarsimp?)
   apply (metis eq_snd_iff old.unit.exhaust)  
  apply (frule_tac f= f and s' ="snd ( flush f s) " and t' = "snd (flush f s')" in flush_det_sat_refine [rotated 2]; clarsimp?)
    apply (metis eq_snd_iff old.unit.exhaust)     
   apply (metis eq_snd_iff old.unit.exhaust)  
  apply (frule_tac  f = f and s' ="snd ( flush f r) " and t' = "snd (flush f s)" in flush_non_det_det_refine [rotated 2]; clarsimp?)
   apply (metis eq_snd_iff old.unit.exhaust)  
  by force
  
fun 
  main_op :: "op_typ' \<Rightarrow> 'a::mmu state_scheme \<Rightarrow> _"
  where 
  "main_op (root_update rt) s     = ((),  snd (update_TTBR0 rt s))"
| "main_op (flush_op f) s         = ((), snd (flush f s))"

lemma main_refine:
    "\<lbrakk> main_op f r = ((), r') ; main_op f t = ((), t'); 
         tlb_rel (typ_non_det_tlb r) (typ_set_tlb t) \<rbrakk> \<Longrightarrow> 
                  tlb_rel (typ_non_det_tlb r') (typ_set_tlb t')"
  apply (cases f; clarsimp)
   apply (rename_tac rt)
   apply (rule_tac  rt = rt and  r = r and t = t in root_refinement; force?) 
    apply (metis eq_snd_iff old.unit.exhaust)    
   apply (metis eq_snd_iff old.unit.exhaust)    
  apply (rule_tac f = x2 in flush_refinement; force?) 
   apply (metis eq_snd_iff old.unit.exhaust)    
  by (metis eq_snd_iff old.unit.exhaust)    
 


end