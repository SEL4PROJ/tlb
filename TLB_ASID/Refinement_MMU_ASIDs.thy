theory Refinement_MMU_ASIDs

imports  Update_Root_Tag_Ref

begin    

datatype mem_op_typ = translate     vaddr 
                | memread       "vaddr \<times> nat" 
                | memwrite      "bool list \<times> vaddr \<times> nat"

datatype mmu_op_typ = root_update  paddr 
                    | asid_update  asid 
                    | flush_addr        flush_type
                    | flush_asid        asid_flush_type

datatype res_typ = PA paddr
                 | BL "bool list"
                 | UT unit


fun 
  mem_op :: "mem_op_typ \<Rightarrow> 'a::mmu_extended state_scheme \<Rightarrow> _"
  where 
  "mem_op (translate va) s             = (PA (fst (mmu_translate va s)),            snd (mmu_translate va s))"
| "mem_op (memread (va, sz)) s         = (BL (fst (mmu_read_size (va, sz) s)),      snd (mmu_read_size (va, sz) s))"
| "mem_op (memwrite (bl, va, sz)) s    = (UT (fst (mmu_write_size (bl, va, sz) s)), snd (mmu_write_size (bl, va, sz) s))"

fun 
  mmu_op :: "mmu_op_typ \<Rightarrow> 'a::mmu_extended state_scheme \<Rightarrow> _"
  where 
  "mmu_op (root_update rt) s    = ((), snd (update_TTBR0 rt s))"
| "mmu_op (asid_update a) s     = ((), snd (update_ASID a s))"
| "mmu_op (flush_addr f) s      = ((), snd (flush f s))"
| "mmu_op (flush_asid f) s      = ((), snd (flush_with_ASID f s))"




thm mmu_write_non_det_det_refine
thm mmu_read_non_det_det_refine


fun
  consistent_det :: "mem_op_typ \<Rightarrow> 'a::mmu_extended det_tlb_state_scheme \<Rightarrow> bool"
where
  "consistent_det (translate va) s             =  consistent (typ_det_tlb s) va"
| "consistent_det (memread (va, sz)) s         =  consistent ( typ_det_tlb s) va"
| "consistent_det (memwrite (bl, va, sz)) s    =  consistent ( typ_det_tlb s) va"


lemma  addr_trans_det:
  "\<lbrakk> mmu_translate va s = (pa, s');  mmu_translate va t = (pa', t'); 
consistent (typ_det_tlb t) va; tlb_rel_det (typ_non_det_tlb s) (typ_det_tlb t)  \<rbrakk> \<Longrightarrow>
      pa' = pa \<and> tlb_rel_det (typ_non_det_tlb s') (typ_det_tlb t')"
  using mmu_translate_non_det_det_refine [simplified split_def Let_def, rotated 2]  by force

lemma read_trans_det:
  "\<lbrakk>mmu_read_size (va, sz) s = (val, s');  mmu_read_size (va, sz) t = (val', t'); consistent (typ_det_tlb t) va;
              tlb_rel_det (typ_non_det_tlb s) (typ_det_tlb t)\<rbrakk> \<Longrightarrow>  
                     val' = val \<and> tlb_rel_det (typ_non_det_tlb s') (typ_det_tlb t') "
  using mmu_read_non_det_det_refine by blast


lemma mem_refine_det:
    "\<lbrakk> mem_op f s = (res, s') ; mem_op f t = (res', t'); 
          consistent_det f t ; tlb_rel_det (typ_non_det_tlb s) (typ_det_tlb t) \<rbrakk> \<Longrightarrow> 
                 res' = res \<and> tlb_rel_det (typ_non_det_tlb s') (typ_det_tlb t')"
  apply (cases f; clarsimp)
    apply (rename_tac va)
    apply (rule_tac va = va and s = s and t = t in  addr_trans_det; clarsimp?) 
   apply (rename_tac va sz)
   apply (rule_tac read_trans_det; force?) 
  apply (rename_tac bl va sz)
  apply (rule_tac val = bl and va = va and sz = sz and s = s and t = t in mmu_write_non_det_det_refine; force?) 
   apply (metis eq_snd_iff old.unit.exhaust)    
  by (metis eq_snd_iff old.unit.exhaust)


lemma mmu_refine_det:
    "\<lbrakk> mmu_op f s = ((), s') ; mmu_op f t = ((), t'); 
           tlb_rel_det (typ_non_det_tlb s) (typ_det_tlb t) \<rbrakk> \<Longrightarrow> 
               tlb_rel_det (typ_non_det_tlb s') (typ_det_tlb t')"
  apply (cases f; clarsimp)
     apply (rename_tac rt)
     apply (rule_tac r = rt and s = s and t= t in update_root_non_det_det_refine;  clarsimp simp: eq_snd_iff) 
    apply (rename_tac a)
    apply (rule_tac a = a and s = s and t= t in update_asid_non_det_det_refine;  clarsimp simp: eq_snd_iff) 
   apply (rename_tac ft)
   apply (rule_tac f = ft and s = s and t= t in flush_non_det_det_refine;  clarsimp simp: eq_snd_iff) 
  apply (rename_tac ft)
  by (rule_tac f = ft and s = s and t= t in flush_with_asid_non_det_det_refine;  clarsimp simp: eq_snd_iff) 



fun
  consistent_sat :: "mem_op_typ \<Rightarrow> 'a::mmu_extended sat_tlb_state_scheme \<Rightarrow> bool"
where
  "consistent_sat (translate va) s             =  consistent ( typ_sat_tlb s) va"
| "consistent_sat (memread (va, sz)) s         =  consistent ( typ_sat_tlb s) va"
| "consistent_sat (memwrite (bl, va, sz)) s    =  consistent ( typ_sat_tlb s) va"



lemma  addr_trans_sat:
  "\<lbrakk> mmu_translate va s = (pa, s');  mmu_translate va t = (pa', t'); 
consistent (typ_sat_tlb t) va; tlb_rel_sat (typ_det_tlb s) (typ_sat_tlb t)  \<rbrakk> \<Longrightarrow>
      pa' = pa \<and> tlb_rel_sat (typ_det_tlb s') (typ_sat_tlb t')"
  using mmu_translate_det_sat_refine [simplified split_def Let_def, rotated 2]  by force

lemma read_trans_sat:
  "\<lbrakk>mmu_read_size (va, sz) s = (val, s');  mmu_read_size (va, sz) t = (val', t'); consistent (typ_sat_tlb t) va;
              tlb_rel_sat (typ_det_tlb s) (typ_sat_tlb t)\<rbrakk> \<Longrightarrow>  
                     val' = val \<and> tlb_rel_sat (typ_det_tlb s') (typ_sat_tlb t') "
  using mmu_read_non_det_sat_refine by blast


lemma mem_refine_sat:
    "\<lbrakk> mem_op f s = (res, s') ; mem_op f t = (res', t'); 
          consistent_sat f t ; tlb_rel_sat (typ_det_tlb s) (typ_sat_tlb t) \<rbrakk> \<Longrightarrow> 
                 res' = res \<and> tlb_rel_sat (typ_det_tlb s') (typ_sat_tlb t')"
  apply (cases f; clarsimp)
    apply (rename_tac va)
    apply (rule_tac va = va and s = s and t = t in  addr_trans_sat; clarsimp?) 
   apply (rename_tac va sz)
   apply (rule_tac read_trans_sat; force?) 
  apply (rename_tac bl va sz)
  apply (rule_tac val = bl and va = va and sz = sz and s = s and t = t in mmu_write_det_sat_refine; force?) 
   apply (metis eq_snd_iff old.unit.exhaust)    
  by (metis eq_snd_iff old.unit.exhaust)


lemma mmu_refine_sat:
    "\<lbrakk> mmu_op f s = ((), s') ; mmu_op f t = ((), t'); 
           tlb_rel_sat (typ_det_tlb s) (typ_sat_tlb t) \<rbrakk> \<Longrightarrow> 
               tlb_rel_sat (typ_det_tlb s') (typ_sat_tlb t')"
  apply (cases f; clarsimp)
     apply (rename_tac rt)
     apply (rule_tac r = rt and s = s and t= t in update_root_det_sat_refine;  clarsimp simp: eq_snd_iff) 
    apply (rename_tac a)
    apply (rule_tac a = a and s = s and t= t in update_asid_det_sat_refine;  clarsimp simp: eq_snd_iff) 
   apply (rename_tac ft)
   apply (rule_tac f = ft and s = s and t= t in flush_det_sat_refine;  clarsimp simp: eq_snd_iff) 
  apply (rename_tac ft)
  by (rule_tac f = ft and s = s and t= t in flush_with_asid_det_sat_refine;  clarsimp simp: eq_snd_iff) 


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
     apply (rule_tac r = rt and s = s and t= t in update_root_sat_incon_refine';  clarsimp simp: eq_snd_iff) 
    apply (rename_tac a)
    apply (rule_tac a = a and s = s and t= t in update_asid_sat_set'_refine;  clarsimp simp: eq_snd_iff) 
   apply (rename_tac ft)
   apply (rule_tac f = ft and s = s and t= t in flush_sat_incon_refine;  clarsimp simp: eq_snd_iff) 
  apply (rename_tac ft)
  by (rule_tac f = ft and s = s and t= t in flush_with_asid_sat_incon_refine;  clarsimp simp: eq_snd_iff) 




definition 
  tlb_rel :: "(asid \<times> asid tlb_entry set)  state_scheme  \<Rightarrow>  (asid \<times> set_tlb) state_scheme  \<Rightarrow> bool"
where                                                                
  "tlb_rel r t \<equiv> \<exists>(s:: unit det_tlb_state_scheme) (s':: unit sat_tlb_state_scheme).  
                    tlb_rel_det r (typ_det_tlb s) \<and> tlb_rel_sat (typ_det_tlb s) (typ_sat_tlb s') \<and> 
                           tlb_rel_abs (typ_sat_tlb s') t"


lemmas  abc =  mmu_translate_det_sat_refine [simplified split_def Let_def, rotated 2]   
lemmas  abc' =  mmu_translate_non_det_det_refine [simplified split_def Let_def, rotated 2]


lemma address_refinement:
  "\<lbrakk> mmu_translate va r = (pa, r');  mmu_translate va t = (pa', t') ;
           va \<notin> iset(set_tlb t) ; tlb_rel (typ_non_det_tlb r) (typ_set_tlb t) \<rbrakk> \<Longrightarrow> 
                               pa = pa' \<and>   tlb_rel  (typ_non_det_tlb r') (typ_set_tlb t') " 
  apply (clarsimp simp: tlb_rel_def)
  apply (frule_tac s = s' and pa = "fst(mmu_translate va s')" and s' = "snd(mmu_translate va s')" in 
      mmu_translate_sat_incon_refine [rotated]; clarsimp?)
  apply (frule_tac va = va and pa =  "fst(mmu_translate va s)" and s' = "snd(mmu_translate va s)"in  abc; clarsimp?)
  using tlb_rel_abs_consistent' apply force
  apply (frule_tac va = va and pa =  "fst(mmu_translate va r)" and s' = "snd(mmu_translate va r)"in  abc'; clarsimp?)
  prefer 2
  apply force
  apply (clarsimp simp: fst_def snd_def)
  apply (case_tac "mmu_translate va s'", simp)
  apply (case_tac " mmu_translate va s", simp)
  apply (clarsimp simp:   det_tlb_more det_tlb_truncate fst_conv mmu_det_eq_asid_root_mem mmu_sat_eq_asid_root_mem sat_tlb_more sat_tlb_truncate snd_conv tlb_rel_abs_consistent'  
   tlb_rel_sat_consistent tlb_rel_sat_def typ_det_prim_parameter typ_det_tlb_def typ_sat_prim_parameter typ_sat_tlb_def)
(* update this later *)
proof -
  fix s :: det_tlb_state and s' :: sat_tlb_state and b :: sat_tlb_state and ba :: det_tlb_state
  assume "tlb_rel_det (typ_non_det_tlb r) (state.extend (state.truncate s) (det_asid ba, det_tlb s))"
  assume a1: "consistent0 (lookup'' (sat_tlb b) (sat_asid b)) (pt_walk (sat_asid b) (MEM b) (TTBR0 b)) va"
assume a2: "mmu_translate va s' = (pa', b)"
assume a3: "mmu_translate va s = (pa', ba)"
  assume a4: "state.truncate (state.extend (state.truncate s) (det_asid ba, det_tlb s)) = state.truncate (state.extend (state.truncate s') (sat_asid b, sat_tlb s'))"
  assume a5: "fst (state.more (state.extend (state.truncate s) (det_asid ba, det_tlb s))) = fst (state.more (state.extend (state.truncate s') (sat_asid b, sat_tlb s')))"
  assume a6: "fst (state.more (state.extend (state.truncate ba) (det_asid ba, det_tlb ba))) = fst (state.more (state.extend (state.truncate b) (sat_asid b, sat_tlb b)))"
  assume a7: "snd (state.more (state.extend (state.truncate s) (det_asid ba, det_tlb s))) \<subseteq> snd (state.more (state.extend (state.truncate s') (sat_asid b, sat_tlb s')))"
  assume a8: "saturated (state.extend (state.truncate s') (sat_asid b, sat_tlb s'))"
  have f9: "fst (state.more (typ_det_tlb ba)) = fst (state.more (typ_sat_tlb b))"
    using a6 by (simp add: typ_det_tlb_def typ_sat_tlb_def)
  have f10: "sat_asid b = sat_asid s'"
    using a2 by (simp add: mmu_sat_eq_asid_root_mem)
  have f11: "det_asid ba = det_asid s"
using a3 by (simp add: mmu_det_eq_asid_root_mem)
  have f12: "TTBR0 ba = TTBR0 s"
    using a3 by (simp add: mmu_det_eq_asid_root_mem)
  have f13: "MEM ba = MEM s"
    using a3 by (metis (no_types) mmu_det_eq_asid_root_mem)
  have f14: "state.more (typ_sat_tlb s') = (sat_asid b, sat_tlb s')"
using f10 by simp
  then have f15: "state.extend (state.truncate s') (state.more (typ_sat_tlb s')) = typ_sat_tlb s'"
    using f10 by (simp add: typ_sat_tlb_def)
  then have f16: "state.more (typ_sat_tlb b) = state.more (typ_sat_tlb s')"
    using f14 a8 a2 by (metis (no_types) mmu_translate_saturated_tlb_unchange sat_tlb_more)
  have f17: "fst (state.more (typ_det_tlb ba)) = fst (state.more (typ_det_tlb s))"
    using f15 f14 f11 f9 a5 by simp
  have f18: "det_asid ba = fst (state.more (typ_det_tlb s))"
    using f11 by simp
  then have f19: "det_asid ba = fst (state.more (typ_det_tlb ba))"
    using f17 by presburger
  then have "tlb_rel_det (typ_det_tlb s) (typ_sat_tlb s')"
    using f18 f15 f14 f11 f9 a7 a4 by (simp add: tlb_rel_det_def typ_det_tlb_def)
  then show "consistent0 (lookup'' (det_tlb s) (det_asid ba)) (pt_walk (det_asid ba) (MEM ba) (TTBR0 ba)) va"
    using f19 f16 f13 f12 f11 a2 a1 by (metis det_tlb_more mmu_sat_eq_asid_root_mem old.prod.inject prod.exhaust_sel sat_tlb_more tlb_rel_det_consistent typ_det_prim_parameter typ_sat_prim_parameter)
qed
 
  


lemma read_refinement:
  "\<lbrakk> mmu_read_size (va, sz) r = (val, r');  mmu_read_size (va, sz) t = (val', t');
           va \<notin> iset(set_tlb t) ; tlb_rel (typ_non_det_tlb r) (typ_set_tlb t) \<rbrakk> \<Longrightarrow> 
                               val = val' \<and>  tlb_rel  (typ_non_det_tlb r') (typ_set_tlb t') " 
  apply (clarsimp simp: tlb_rel_def)
  apply (frule_tac s = s' and val = "fst(mmu_read_size (va, sz) s')" and s' = "snd(mmu_read_size (va, sz) s')" in 
      mmu_read_sat_incon_refine [rotated]; clarsimp?)
  apply (frule_tac va = va and sz= sz and val =  "fst(mmu_read_size (va, sz)s)" and s' = "snd(mmu_read_size (va, sz) s)" and 
      val' =  "fst(mmu_read_size (va, sz)s')"  and t' = "snd(mmu_read_size (va, sz) s')" in  mmu_read_non_det_sat_refine [rotated 2]; clarsimp?)
  using tlb_rel_abs_consistent' apply force

  apply (frule_tac va = va and sz= sz and val =  "fst(mmu_read_size (va, sz)r)" and s' = "snd(mmu_read_size (va, sz) r)" and 
      val' =  "fst(mmu_read_size (va, sz)s)"  and t' = "snd(mmu_read_size (va, sz) s)" in  mmu_read_non_det_det_refine [rotated 2]; clarsimp?)
  using tlb_rel_abs_consistent' tlb_rel_sat_consistent apply fastforce
   apply (metis (no_types) prod.collapse)
  by force

lemma write_refinement:
  "\<lbrakk> mmu_write_size (val,va, sz) r = ((), r');  mmu_write_size (val,va, sz)  t = ((), t');
            va \<notin> iset(set_tlb t) ; tlb_rel (typ_non_det_tlb r) (typ_set_tlb t) \<rbrakk> \<Longrightarrow> 
                              tlb_rel  (typ_non_det_tlb r') (typ_set_tlb t') " 
  apply (clarsimp simp: tlb_rel_def)
  apply (frule_tac s = s' and s' = "snd(mmu_write_size (val,va, sz) s')" in 
      mmu_write_sat_incon_refine [rotated]; clarsimp?)
   apply (metis eq_snd_iff old.unit.exhaust)
  apply (frule_tac va = va and sz= sz  and s' = "snd(mmu_write_size (val,va, sz)  s)" and t' = "snd(mmu_write_size (val,va, sz)  s')" and val = val in  
      mmu_write_det_sat_refine [rotated]; clarsimp?)
  using tlb_rel_abs_consistent' apply force 
    apply (metis eq_snd_iff old.unit.exhaust)
   apply (metis eq_snd_iff old.unit.exhaust)
  apply (frule_tac va = va and sz= sz and val =  val and s' = "snd(mmu_write_size (val,va, sz) r)" and 
      t' = "snd(mmu_write_size (val,va, sz) s)" in  mmu_write_non_det_det_refine [rotated]; clarsimp?)
  using tlb_rel_abs_consistent' tlb_rel_sat_consistent apply fastforce
   apply (metis eq_snd_iff old.unit.exhaust)
  by force



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
  apply (frule_tac s = s'  and s' = "snd (update_TTBR0 rt s')"  in update_root_sat_incon_refine' [rotated]; clarsimp?)
   apply (metis eq_snd_iff old.unit.exhaust)  
  apply (frule_tac  r = rt and s' ="snd ( update_TTBR0 rt s) " and t' = "snd (update_TTBR0 rt s')" in update_root_det_sat_refine [rotated 2]; clarsimp?)
    apply (metis eq_snd_iff old.unit.exhaust)     
   apply (metis eq_snd_iff old.unit.exhaust)  
  apply (frule_tac  r = rt and s' ="snd ( update_TTBR0 rt r) " and t' = "snd (update_TTBR0 rt s)" in update_root_non_det_det_refine [rotated 2]; clarsimp?)
   apply (metis eq_snd_iff old.unit.exhaust)  
  by force


lemma asid_refinement:
  "\<lbrakk> update_ASID a r = ((), r');  update_ASID a t = ((), t') ; tlb_rel (typ_non_det_tlb r) (typ_set_tlb t) \<rbrakk> \<Longrightarrow> 
                               tlb_rel  (typ_non_det_tlb r') (typ_set_tlb t') " 
  apply (clarsimp simp: tlb_rel_def)
  apply (frule_tac s = s'  and s' = "snd (update_ASID a s')"  in update_asid_sat_set'_refine [rotated]; clarsimp?)
   apply (metis eq_snd_iff old.unit.exhaust)  
  apply (frule_tac  a = a and s' ="snd ( update_ASID a s) " and t' = "snd (update_ASID a s')" in update_asid_det_sat_refine [rotated 2]; clarsimp?)
    apply (metis eq_snd_iff old.unit.exhaust)     
   apply (metis eq_snd_iff old.unit.exhaust)  
  apply (frule_tac  a = a and s' ="snd ( update_ASID a r) " and t' = "snd (update_ASID a s)" in update_asid_non_det_det_refine [rotated 2]; clarsimp?)
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

lemma flush_asid_refinement:
  "\<lbrakk> flush_with_ASID f r = ((), r');  flush_with_ASID f t = ((), t') ; tlb_rel (typ_non_det_tlb r) (typ_set_tlb t) \<rbrakk> \<Longrightarrow> 
                               tlb_rel  (typ_non_det_tlb r') (typ_set_tlb t') " 
  apply (clarsimp simp: tlb_rel_def)
  apply (frule_tac s = s'  and s' = "snd (flush_with_ASID f s')"  in flush_with_asid_sat_incon_refine [rotated]; clarsimp?)
   apply (metis eq_snd_iff old.unit.exhaust)  
  apply (frule_tac f= f and s' ="snd ( flush_with_ASID f s) " and t' = "snd (flush_with_ASID f s')" in flush_with_asid_det_sat_refine [rotated 2]; clarsimp?)
    apply (metis eq_snd_iff old.unit.exhaust)     
   apply (metis eq_snd_iff old.unit.exhaust)  
  apply (frule_tac  f = f and s' ="snd ( flush_with_ASID f r) " and t' = "snd (flush_with_ASID f s)" in flush_with_asid_non_det_det_refine [rotated 2]; clarsimp?)
   apply (metis eq_snd_iff old.unit.exhaust)  
  by force
  

lemma mmu_refine:
    "\<lbrakk> mmu_op f r = ((), r') ; mmu_op f t = ((), t'); 
         tlb_rel (typ_non_det_tlb r) (typ_set_tlb t) \<rbrakk> \<Longrightarrow> 
                  tlb_rel (typ_non_det_tlb r') (typ_set_tlb t')"
  apply (cases f; clarsimp)
     apply (rename_tac rt)
     apply (rule_tac  rt = rt and  r = r and t = t in root_refinement; force?) 
      apply (metis eq_snd_iff old.unit.exhaust)    
     apply (metis eq_snd_iff old.unit.exhaust)    
    apply (rename_tac a)
    apply (rule_tac  a = a and  r = r and t = t in asid_refinement; force?) 
     apply (metis eq_snd_iff old.unit.exhaust)    
    apply (metis eq_snd_iff old.unit.exhaust) 
   apply (rename_tac ft)
   apply (rule_tac f = ft in flush_refinement; force?) 
    apply (metis eq_snd_iff old.unit.exhaust)    
   apply (metis eq_snd_iff old.unit.exhaust)  
  apply (rename_tac ft)
  apply (rule_tac f = ft in flush_asid_refinement; force?) 
   apply (metis eq_snd_iff old.unit.exhaust)    
  by (metis eq_snd_iff old.unit.exhaust)  



end