theory Read_Write_Tag_Ref

imports  Address_Translate_Tag_Ref

begin    

lemma  mmu_write_rel:
  "\<lbrakk>mmu_write_size (val,va, sz) s = ((), s')\<rbrakk>   \<Longrightarrow>  s' = s \<lparr> non_det_tlb := non_det_tlb s' , MEM:= MEM s' , exception:= exception s' \<rparr>"
  apply (clarsimp simp:  mmu_write_size_non_det_tlb_state_ext_def Let_def, cases "mmu_translate va s", clarsimp split: if_split_asm)
   apply (drule write_mem_rel, cases "mmu_translate va s" , clarsimp)
   apply (drule mmu_rel, cases s, cases s', case_tac b, clarsimp)
  apply (clarsimp simp: mmu_translate_non_det_tlb_state_ext_def Let_def split: lookup_type.splits)
  by (clarsimp simp: Let_def raise'exception_def split:if_split_asm)+


lemma mmu_write_tlb_disj:
  "\<lbrakk> mmu_write_size (val,va, sz) s = ((), s') \<rbrakk> \<Longrightarrow>
     non_det_tlb s' = non_det_tlb s - tlb_evict (typ_non_det_tlb s) \<or> 
           non_det_tlb s' = non_det_tlb s - tlb_evict (typ_non_det_tlb s) \<union> {the (pt_walk (non_det_asid s) (MEM s) (TTBR0 s) va)}"
  apply (clarsimp simp:  mmu_write_size_non_det_tlb_state_ext_def mmu_translate_non_det_tlb_state_ext_def split_def Let_def write_mem_eq_TLB raise'exception_def 
                  split: lookup_type.splits split: if_split_asm)
    apply (drule write_mem_eq_TLB state.defs)
    apply (cases s , cases s' ; clarsimp)
   apply (drule write_mem_eq_TLB state.defs)
  by(cases s , cases s' ; clarsimp)

 
lemma  mmu_write_det_rel:
  "\<lbrakk>mmu_write_size (val,va, sz) s = ((), s')\<rbrakk>   \<Longrightarrow>  s' = s \<lparr> det_tlb := det_tlb s' , MEM:= MEM s' , exception:= exception s' \<rparr>"
  apply (clarsimp simp:  mmu_write_size_det_tlb_state_ext_def Let_def, cases "mmu_translate va s", clarsimp split: if_split_asm)
   apply (drule write_mem_rel, cases "mmu_translate va s" , clarsimp)
   apply (drule mmu_det_rel, cases s, cases s', case_tac b, clarsimp)
  apply (clarsimp simp: mmu_translate_det_tlb_state_ext_def Let_def split: lookup_type.splits)
  by (clarsimp simp: Let_def raise'exception_def split:if_split_asm)+


lemma mmu_write_tlb_disj_det:
  "\<lbrakk> mmu_write_size (val,va, sz) s = ((), s') \<rbrakk> \<Longrightarrow>
     det_tlb s' = det_tlb s  \<or>  det_tlb s' = det_tlb s  \<union> {the (pt_walk (det_asid s)  (MEM s) (TTBR0 s) va)}"
  apply (clarsimp simp:  mmu_write_size_det_tlb_state_ext_def mmu_translate_det_tlb_state_ext_def split_def Let_def write_mem_eq_TLB raise'exception_def 
                  split: lookup_type.splits split: if_split_asm)
    apply (drule write_mem_eq_TLB state.defs)
    apply (cases s , cases s' ; clarsimp)
   apply (drule write_mem_eq_TLB state.defs)
  by(cases s , cases s' ; clarsimp)

(**************************************************************)


lemma mmu_write_tlb_subset_non_det_det:
  "\<lbrakk> mmu_write_size (val,va, sz) s = ((), s'); tlb_rel_det (typ_non_det_tlb s) (typ_det_tlb t); consistent (typ_det_tlb t) va; 
       mmu_write_size (val,va, sz) t = ((), t') \<rbrakk> \<Longrightarrow> non_det_tlb s' \<subseteq> det_tlb t'"
  apply (frule tlb_rel_detD)
  apply (subgoal_tac "lookup'' (non_det_tlb s - tlb_evict (typ_non_det_tlb s)) (non_det_asid s) va \<le> lookup'' (det_tlb t) (det_asid t) va")
   prefer 2
   apply (simp add:  sup.absorb1 asid_tlb_mono tlb_rel_det_def)
   apply (meson Diff_subset order_trans asid_tlb_mono)
  apply (frule mmu_write_tlb_disj)
  apply (frule mmu_write_tlb_disj_det)
  apply (erule disjE)
   apply (clarsimp simp: )
   apply blast
  apply (erule disjE)
   apply clarsimp
   apply (rule conjI)
    prefer 2
    apply blast
   apply (clarsimp simp:  mmu_write_size_det_tlb_state_ext_def , cases "mmu_translate va t" , clarsimp split: if_split_asm)
    apply (clarsimp simp:  mmu_translate_det_tlb_state_ext_def)
    apply (case_tac "lookup'' (det_tlb t) (det_asid t) va"; clarsimp simp: Let_def consistent0_def)
     apply (clarsimp simp: raise'exception_def  split: if_split_asm)
     apply (clarsimp simp: write'mem1_def split: if_split_asm)
         apply (cases t, cases t', clarsimp simp: state.defs) apply force
        apply (cases t, cases t', clarsimp simp: state.defs) apply force
       apply (cases t, cases t', clarsimp simp: state.defs) apply force
      apply (cases t, cases t', clarsimp simp: state.defs) apply force
     apply (clarsimp simp: raise'exception_def  split: if_split_asm)
     apply (cases t, cases t', clarsimp simp: state.defs) apply force
  using lookup_in_asid_tlb apply blast
   apply (clarsimp simp:  mmu_translate_det_tlb_state_ext_def)
   apply (case_tac "lookup'' (det_tlb t) (det_asid t) va")
     apply (subgoal_tac "lookup'' (non_det_tlb s - tlb_evict (typ_non_det_tlb s)) (det_asid t) va = Miss")
      prefer 2
      apply force
     apply (clarsimp simp:  mmu_write_size_non_det_tlb_state_ext_def)
     apply (case_tac "mmu_translate va s", clarsimp)
     apply (clarsimp simp: mmu_translate_non_det_tlb_state_ext_def)
     apply (clarsimp simp: Let_def split: if_split_asm)
       apply (case_tac "exception s = NoException")
        apply (clarsimp simp: raise'exception_def  split: if_split_asm)
       apply (thin_tac "raise'exception (PAGE_FAULT ''more info'') t = (a, t')")
       apply (clarsimp simp: raise'exception_def  split: if_split_asm)
      apply (thin_tac "raise'exception (PAGE_FAULT ''more info'') t = (a, t')")
      apply (clarsimp simp: raise'exception_def  split: if_split_asm)
       apply force
      apply force
     apply force
    apply (clarsimp simp: consistent0_def)
   apply (simp only: consistent0_def)
   apply (metis lookup_in_asid_tlb lookup_type.simps(5))
  apply clarsimp
  by blast



lemma write_mem_non_det_det_MEM:
  "\<lbrakk> mmu_write_size (val,va, sz) s = ((), s');  tlb_rel_det (typ_non_det_tlb s) (typ_det_tlb t) ; consistent (typ_det_tlb t) va; 
                   mmu_write_size (val,va, sz) t = ((), t') \<rbrakk> \<Longrightarrow> MEM s' = MEM t'"
  apply (frule tlb_rel_detD)
  apply (clarsimp simp:  mmu_write_size_non_det_tlb_state_ext_def , cases "mmu_translate va s" , clarsimp)
  apply (clarsimp simp:  mmu_write_size_det_tlb_state_ext_def , cases "mmu_translate va t" , clarsimp)
  apply (clarsimp split: if_split_asm)
     apply (case_tac "write'mem1 (val, aa, sz) ba" , clarsimp)
     apply (subgoal_tac "MEM b = MEM ba \<and> aa = a")
  using write_same_mem apply blast
     apply (rule conjI)
      apply (clarsimp simp:  mmu_eq_asid_root_mem mmu_det_eq_asid_root_mem)
     apply (frule_tac s= "(typ_non_det_tlb s)" and va= "va" in tlb_rel_det_consistent, clarsimp)
     apply (subgoal_tac "non_det_tlb s - tlb_evict (typ_non_det_tlb s) \<subseteq> non_det_tlb s")
      prefer 2
      apply blast
     apply (subgoal_tac "lookup'' (non_det_tlb s - tlb_evict (typ_non_det_tlb s)) (non_det_asid s) va \<le> lookup'' (det_tlb t) (det_asid t) va")
      prefer 2
      apply (simp add:  sup.absorb1 asid_tlb_mono tlb_rel_det_def)
     apply (clarsimp simp:  mmu_translate_non_det_tlb_state_ext_def  mmu_translate_det_tlb_state_ext_def split_def Let_def)
     apply (cases "lookup'' (det_tlb t) (det_asid t) va"; clarsimp)
       apply (clarsimp simp: tlb_rel_det_def Let_def raise'exception_def  state.defs split: if_split_asm)
      apply (clarsimp simp: consistent0_def)
     apply (subgoal_tac "x3 = the (pt_walk (non_det_asid s) (MEM s) (TTBR0 s) va)")
      prefer 2
      apply (clarsimp simp: consistent0_def)
     apply (cases "lookup'' (non_det_tlb s - tlb_evict (typ_non_det_tlb s)) (non_det_asid s) va"; clarsimp)
     apply (clarsimp simp: Let_def)
     apply (cases "\<not>is_fault (pt_walk () (MEM s) (TTBR0 s) va)")
      apply (clarsimp simp: tlb_rel_det_def typ_det_tlb_def typ_non_det_tlb_def state.defs lookup_in_asid_tlb raise'exception_def split: if_split_asm)
     apply (clarsimp simp: tlb_rel_det_def typ_det_tlb_def typ_non_det_tlb_def state.defs lookup_in_asid_tlb raise'exception_def split: if_split_asm)
  using mmu_translate_non_det_det_excp mmu_translate_non_det_det_pa apply fastforce
  using mmu_translate_non_det_det_excp mmu_translate_non_det_det_pa apply fastforce
  by (simp add: mmu_det_eq_asid_root_mem mmu_eq_asid_root_mem)

 
lemma mmu_write_size_det_non_det_state_trun:
  "\<lbrakk>mmu_write_size (val,va, sz) s = ((), s'); tlb_rel_det(typ_non_det_tlb s) (typ_det_tlb t)  ; consistent (typ_det_tlb t) va;
     mmu_write_size (val,va, sz) t = ((), t')\<rbrakk> \<Longrightarrow> state.truncate t' = state.truncate s' \<and> det_asid t' = non_det_asid s'"
  apply (frule (3)  write_mem_non_det_det_MEM)
  apply (frule tlb_rel_detD, clarsimp)
  apply (frule mmu_write_rel)
  apply (rotate_tac)
  apply (frule mmu_write_det_rel)
  apply (clarsimp simp: tlb_rel_det_def)
  apply (subgoal_tac "exception s' = exception t'")
   apply (cases s, cases t, cases s' , cases t')
   apply (clarsimp simp: state.defs det_tlb_state.defs)
  apply (clarsimp simp: mmu_write_size_non_det_tlb_state_ext_def mmu_write_size_det_tlb_state_ext_def Let_def)
  apply (case_tac "mmu_translate va t" , case_tac "write'mem1 (val, a, sz) b" , clarsimp)
  apply (case_tac "mmu_translate va s" , clarsimp)
  apply (subgoal_tac "exception b = exception bb \<and> a = aa")
   apply (clarsimp split: if_split_asm)
   apply (subgoal_tac "MEM b = MEM bb ")
    apply (frule_tac s="bb" and s'="s'" and t = b and t' = t' in write_same_mem_excep ; clarsimp)
   apply (frule_tac s="s" and s'="bb" and t = t and t' = b and p' = aa in mmu_translate_non_det_det_mem_excp ; clarsimp simp: consistent0_def tlb_rel_det_def)
  apply (rule conjI)
   apply (frule_tac t= t and pa' = a and t' = b in mmu_translate_non_det_det_pa)
      apply (clarsimp simp: tlb_rel_det_def)
     apply (clarsimp simp: consistent0_def)
    apply (clarsimp simp: tlb_rel_det_def)
   apply (frule_tac s = "s" and s' = "bb" and t = "t" and t' = "b" in   mmu_translate_non_det_det_excp ; clarsimp simp: tlb_rel_det_def)
  apply (subgoal_tac "non_det_tlb s - tlb_evict (typ_non_det_tlb s) \<subseteq> non_det_tlb s")
   prefer 2
   apply blast
  apply (subgoal_tac "lookup'' (non_det_tlb s - tlb_evict (typ_non_det_tlb s))  (non_det_asid s) va \<le> lookup'' (det_tlb t) (det_asid t) va")
   prefer 2
   apply (simp add: sup.absorb1 asid_tlb_mono tlb_rel_det_def)
  apply (clarsimp simp: mmu_translate_non_det_tlb_state_ext_def mmu_translate_det_tlb_state_ext_def split_def Let_def)
  apply (cases "lookup'' (det_tlb t) (det_asid t) va")
    apply clarsimp
    prefer 2
    apply (clarsimp simp: consistent0_def)
   apply (clarsimp simp: tlb_rel_det_def Let_def)
   apply (cases "(is_fault (pt_walk (non_det_asid s)  (MEM s) (TTBR0 s) va))")
    apply (clarsimp simp: raise'exception_def  state.defs split: if_split_asm)
   apply (clarsimp simp: lookup_def entry_set_def  split: if_split_asm)
  apply clarsimp
  apply (subgoal_tac "x3 = the (pt_walk (non_det_asid s) (MEM s) (TTBR0 s) va)")
   prefer 2
   apply (clarsimp simp: consistent0_def)
  apply (cases "lookup''  (non_det_tlb s - tlb_evict (typ_non_det_tlb s)) (non_det_asid s)  va"; clarsimp)
  by (clarsimp simp: Let_def consistent0_def)



lemma mmu_write_non_det_det_refine:
  "\<lbrakk> mmu_write_size (val,va, sz) s = ((), s'); tlb_rel_det (typ_non_det_tlb s) (typ_det_tlb t)  ; consistent (typ_det_tlb t) va;
        mmu_write_size (val,va, sz) t = ((), t') \<rbrakk> \<Longrightarrow>  tlb_rel_det (typ_non_det_tlb s') (typ_det_tlb t') "
  apply (clarsimp simp: tlb_rel_det_def)
  apply (rule conjI)
   prefer 2                                                               
   apply (frule_tac s = s and s' = s' and t = t and t' = t' in mmu_write_tlb_subset_non_det_det; clarsimp simp: tlb_rel_det_def)
   apply (frule_tac s = s and s' = s' and t = t and t' = t' in mmu_write_size_det_non_det_state_trun; clarsimp simp: tlb_rel_det_def)+
  done



lemma mmu_write_saturated_state:
  "\<lbrakk>mmu_write_size (val,va,sz) s = ((), t)  \<rbrakk>  \<Longrightarrow> saturated (typ_sat_tlb t)"
  apply (clarsimp simp: mmu_write_size_sat_tlb_state_ext_def Let_def)
  apply (case_tac "mmu_translate va s" , clarsimp)
  apply (clarsimp split: if_split_asm)
   apply (case_tac "write'mem1 (val, a, sz) b" , clarsimp)
   apply (subgoal_tac "sat_asid s = sat_asid ba \<and>  TTBR0 s = TTBR0 ba ")
    apply (clarsimp simp: saturated_def)
   apply (subgoal_tac " sat_asid s = sat_asid b \<and> TTBR0 s = TTBR0 b")
    apply clarsimp
    apply (clarsimp simp:  write'mem1_def Let_def)
    apply (clarsimp split: if_split_asm)
    apply (clarsimp simp:  raise'exception_def)
   apply (clarsimp simp: mmu_translate_sat_tlb_state_ext_def Let_def raise'exception_def split:lookup_type.splits if_split_asm)
  using mmu_translate_saturated_state surjective_pairing by blast



lemma mmu_wrtie_sat_rel:
  "\<lbrakk>mmu_write_size (val,va, sz) s = ((), s')\<rbrakk>   \<Longrightarrow> 
      s' = s \<lparr> sat_tlb := sat_tlb s' , MEM:= MEM s' , exception:= exception s' \<rparr>"
  apply (clarsimp simp: mmu_write_size_sat_tlb_state_ext_def Let_def)
  apply (cases "mmu_translate va s" , clarsimp)
  apply (clarsimp split: if_split_asm)
   apply (case_tac " write'mem1 (val, a, sz) b", clarsimp)
   apply (drule write_mem_rel)
   apply (drule mmu_sat_rel)
   apply (cases s, cases s', case_tac a, case_tac b, case_tac ba)
   apply clarsimp
  apply (clarsimp simp: mmu_translate_sat_tlb_state_ext_def Let_def split: lookup_type.splits)
   apply (clarsimp simp: raise'exception_def  split:if_split_asm) 
  by (clarsimp simp: raise'exception_def split:if_split_asm)



lemma wrtie_mem_sat_tlbs:
  "\<lbrakk>mmu_write_size (val,va, sz) s = ((), s') \<rbrakk> \<Longrightarrow>
     sat_tlb s' = sat_tlb s \<union> the `{e\<in>pt_walk (sat_asid s)   (MEM s) (TTBR0 s) ` UNIV. \<not> is_fault e} \<or>
     sat_tlb s' = sat_tlb s \<union> the `{e\<in>pt_walk (sat_asid s)   (MEM s) (TTBR0 s) ` UNIV. \<not> is_fault e} \<union> the `{e\<in>pt_walk (sat_asid s)   (MEM s') (TTBR0 s') ` UNIV. \<not> is_fault e}"
  apply (cases "exception (snd (mmu_translate va s)) \<noteq> NoException")
   apply (rule disjI1)
   apply (clarsimp simp: mmu_write_size_sat_tlb_state_ext_def Let_def)
   apply (case_tac "mmu_translate va s" , clarsimp)
   apply (clarsimp simp: mmu_translate_sat_tlb_union)
  apply (clarsimp simp: mmu_write_size_sat_tlb_state_ext_def Let_def)
  apply (case_tac "mmu_translate va s " , clarsimp)
  apply (case_tac "write'mem1 (val, a, sz) b" , clarsimp)
  apply (subgoal_tac "sat_tlb ba = sat_tlb b")
   apply (subgoal_tac "sat_tlb b  = sat_tlb s \<union> the `{e\<in>pt_walk (sat_asid s)   (MEM s) (TTBR0 s) ` UNIV. \<not> is_fault e}")
    apply (subgoal_tac "  TTBR0 ba = TTBR0 s")
     apply clarsimp
    apply (subgoal_tac "  TTBR0 b = TTBR0 s") 
     apply (simp add: write_mem1_eq_ASID_TTBR0)
  apply (simp add: mmu_sat_eq_asid_root_mem)
   apply (clarsimp simp: mmu_translate_sat_tlb_union) 
  apply (drule write_mem_eq_TLB)
  apply (case_tac ba , case_tac b ; clarsimp)
  done


lemma mmu_write_tlb_subset:
  "\<lbrakk> mmu_write_size (val,va, sz) s = ((), s'); tlb_rel_sat (typ_det_tlb s) (typ_sat_tlb t) ; consistent (typ_sat_tlb t) va ;
        mmu_write_size (val,va, sz) t = ((), t') \<rbrakk> \<Longrightarrow> 
          det_tlb s' \<subseteq> sat_tlb t'"
  apply (frule tlb_rel_satD)
  apply (clarsimp simp:  mmu_write_size_det_tlb_state_ext_def , cases "mmu_translate va s" , clarsimp)
  apply (clarsimp simp:  mmu_write_size_sat_tlb_state_ext_def , cases "mmu_translate va t" , clarsimp)
  apply (frule_tac t' = ba and s' = b and t = t and s = s and pa' = aa in mmu_translate_det_sat_subset_rel; simp?)
  apply (subgoal_tac "det_tlb b = det_tlb s'", clarsimp split: if_split_asm)
    apply (case_tac "write'mem1 (val, aa, sz) ba", clarsimp simp:)
    apply (subgoal_tac "state.more bb = state.more ba")
     apply force
    apply (drule write_mem_eq_TLB)  
    apply (drule write_mem_eq_TLB)
    apply (clarsimp simp: typ_sat_tlb_def) apply force 
   apply (case_tac "write'mem1 (val, aa, sz) ba", simp)
   apply (subgoal_tac "state.more ba = state.more b")
    apply force
   apply (drule write_mem_eq_TLB)  
    apply (clarsimp simp: typ_sat_tlb_def)
   apply (clarsimp simp: typ_sat_tlb_def) apply force
  apply (clarsimp split: if_split_asm)
   apply (drule write_mem_eq_TLB)
   apply (cases s' , case_tac b, clarsimp simp:)
  apply (drule write_mem_eq_TLB)
  by (cases s' , case_tac b, clarsimp simp:)


lemma mmu_write_det_sat_mem:
  "\<lbrakk> mmu_write_size (val,va, sz) s = ((), s');  tlb_rel_sat (typ_det_tlb s) (typ_sat_tlb t) ; consistent (typ_sat_tlb t) va; 
                   mmu_write_size (val,va, sz) t = ((), t') \<rbrakk> \<Longrightarrow> MEM s' = MEM t'"
  apply (frule tlb_rel_satD)
  apply (clarsimp simp:  mmu_write_size_det_tlb_state_ext_def , cases "mmu_translate va s" , clarsimp)
  apply (clarsimp simp:  mmu_write_size_sat_tlb_state_ext_def , cases "mmu_translate va t" , clarsimp)
  apply (subgoal_tac "MEM ba = MEM b \<and>  exception ba = exception b")
   prefer 2
   apply (frule_tac t = t and t' = ba in mmu_translate_non_det_sat_mem_excp; simp?)
  apply (subgoal_tac "a = aa")
   prefer 2
   apply (frule  mmu_translate_non_det_sat_pa; simp)
  apply simp
  apply (clarsimp split: if_split_asm)
  apply (case_tac "write'mem1 (val, aa, sz) ba", simp)
  apply (frule_tac t = ba and t' = bb in  write_same_mem, simp, simp)
  by (case_tac bb, cases t', simp)

 

lemma mmu_write_size_det_sat_state_trunc:
  "\<lbrakk>mmu_write_size (val,va, sz) s = ((), s'); tlb_rel_sat (typ_det_tlb s) (typ_sat_tlb t)  ; consistent (typ_sat_tlb t) va;
     mmu_write_size (val,va, sz) t = ((), t')\<rbrakk> \<Longrightarrow> state.truncate t' = state.truncate s' \<and> det_asid s' = sat_asid t'"
  apply (frule (3)  mmu_write_det_sat_mem)
  apply (frule tlb_rel_satD, clarsimp)
  apply (frule mmu_write_det_rel)
  apply (rotate_tac)
  apply (frule mmu_wrtie_sat_rel)
  apply (clarsimp simp: tlb_rel_sat_def)
  apply (subgoal_tac "exception s' = exception t'")
   apply (cases s, cases t, cases s' , cases t')
   apply (clarsimp simp: state.defs)
  apply (clarsimp simp: mmu_write_size_sat_tlb_state_ext_def mmu_write_size_det_tlb_state_ext_def Let_def)
  apply (case_tac "mmu_translate va t" , case_tac "write'mem1 (val, a, sz) b" , clarsimp)
  apply (case_tac "mmu_translate va s" , clarsimp?)
  apply (subgoal_tac "exception b = exception bb \<and> a = aa")
   apply (clarsimp split: if_split_asm)
   apply (subgoal_tac "MEM b = MEM bb ")
    apply (frule_tac s="bb" and s'="s'" and t = b and t' = ba in write_same_mem_excep ; clarsimp?)
   apply (frule_tac s="s" and s'="bb" and t = t and t' = b and p' = aa in mmu_translate_non_det_sat_mem_excp ; clarsimp simp: consistent0_def tlb_rel_sat_def)
  apply (rule conjI)
   apply (frule_tac s = "s" and s' = "bb" and t = "t" and t' = "b" in   mmu_translate_non_det_sat_excp ; clarsimp simp: tlb_rel_sat_def)
  by (frule_tac t= t and pa' = a and t' = b in mmu_translate_non_det_sat_pa ; clarsimp simp: tlb_rel_sat_def) +



lemma mmu_write_det_sat_refine:
  "\<lbrakk> mmu_write_size (val,va, sz) s = ((), s'); tlb_rel_sat (typ_det_tlb s) (typ_sat_tlb t)  ; consistent (typ_sat_tlb t) va;
        mmu_write_size (val,va, sz) t = ((), t') \<rbrakk> \<Longrightarrow>  tlb_rel_sat (typ_det_tlb s') (typ_sat_tlb t') "
  apply (clarsimp simp: tlb_rel_sat_def)
  apply (clarsimp simp: mmu_write_saturated_state )
  apply (rule conjI)
   prefer 2                                                               
   apply (frule_tac s="s" and s'="s'" and t="t" and t'="t'" in mmu_write_tlb_subset; clarsimp simp: tlb_rel_sat_def)
  by (frule_tac s="s" and s'="s'" and t="t" and t'="t'" in mmu_write_size_det_sat_state_trunc; clarsimp simp: tlb_rel_sat_def)+


(*

lemma mmu_write_incon_set_rel:
  "\<lbrakk> saturated (typ_sat_tlb s) ; 
       inconsistent_vaddrs (typ_sat_tlb s) \<subseteq> iset (set_tlb t);  incoherrent_vaddrs (typ_sat_tlb s) \<subseteq> iset (set_tlb t); 
      sat_asid s = sat_asid r; TTBR0 s = TTBR0 r\<rbrakk> \<Longrightarrow>
     inconsistent_vaddrs (typ_sat_tlb (r\<lparr>sat_tlb := sat_tlb s \<union> the ` {e \<in> range (pt_walk (sat_asid r) (MEM q) (TTBR0 r)). \<not> is_fault e}\<rparr>))
           \<subseteq> iset(set_tlb t) \<union> incon_comp  (sat_asid r) (sat_asid r) (MEM s) (MEM q) (TTBR0 r) (TTBR0 r)"
  apply (clarsimp)
  apply (clarsimp simp: inconsistent_vaddrs_def incon_comp_def ptable_comp_def  incoherrent_vaddrs_def)
  apply (erule disjE)
   apply (drule union_asid_tlb_incon_cases)
   apply (erule disjE, clarsimp simp: saturated_def asid_tlb_lookup_range_pt_walk_not_incon) apply blast
   apply (erule disjE, clarsimp simp: asid_tlb_lookup_range_pt_walk_not_incon)
   apply (erule disjE)   apply blast
   apply (erule disjE, clarsimp simp: asid_tlb_lookup_range_pt_walk_not_incon)
   apply (erule disjE) apply blast
   apply (erule disjE, clarsimp simp: asid_tlb_lookup_range_pt_walk_not_incon)
   apply clarsimp
   apply (subgoal_tac "is_fault (pt_walk (sat_asid r) (MEM s) (TTBR0 r) x)")
    apply blast
   apply (clarsimp simp:)
  apply (erule disjE) 
   apply (erule disjE) 
    apply (drule union_asid_tlb_incon_cases)
    apply (erule disjE, clarsimp simp: saturated_def asid_tlb_lookup_range_pt_walk_not_incon)
    apply (erule disjE, clarsimp simp: asid_tlb_lookup_range_pt_walk_not_incon)
     apply (subgoal_tac "is_fault (pt_walk (sat_asid r) (MEM s) (TTBR0 r) x)")
      apply blast
     apply (clarsimp simp:)
    apply (erule disjE)   apply blast
    apply (erule disjE, clarsimp simp: asid_tlb_lookup_range_pt_walk_not_incon) apply blast
    apply (erule disjE, clarsimp simp: asid_tlb_lookup_range_pt_walk_not_incon)
    apply clarsimp
    apply (subgoal_tac "is_fault (pt_walk (sat_asid r) (MEM s) (TTBR0 r) x)")
     apply blast
    apply (clarsimp simp:)
   apply (drule union_asid_tlb_incon_cases)
   apply (erule disjE, clarsimp simp: saturated_def asid_tlb_lookup_range_pt_walk_not_incon)
   apply (erule disjE, clarsimp simp: asid_tlb_lookup_range_pt_walk_not_incon)
    apply (subgoal_tac "is_fault (pt_walk (sat_asid r) (MEM s) (TTBR0 r) x)")
     apply blast
    apply (clarsimp simp:)
   apply (erule disjE)   apply blast
   apply (erule disjE, clarsimp simp: asid_tlb_lookup_range_pt_walk_not_incon) apply blast
   apply (erule disjE, clarsimp simp: asid_tlb_lookup_range_pt_walk_not_incon)
   apply clarsimp
   apply (subgoal_tac "is_fault (pt_walk (sat_asid r) (MEM s) (TTBR0 r) x)")
    apply blast
   apply (clarsimp simp:)
  apply (erule disjE) 
   apply (drule union_asid_tlb_incon_cases)
   apply (erule disjE, clarsimp simp: saturated_def asid_tlb_lookup_range_pt_walk_not_incon)
   apply (erule disjE, clarsimp simp: asid_tlb_lookup_range_pt_walk_not_incon)
   apply (subgoal_tac "is_fault (pt_walk (sat_asid r) (MEM s) (TTBR0 r) x)")
    apply blast
   apply (clarsimp simp:)
  apply (drule union_asid_tlb_incon_cases)
  apply (erule disjE, clarsimp simp: saturated_def asid_tlb_lookup_range_pt_walk_not_incon)
  apply (erule disjE, clarsimp)
   apply (subgoal_tac "the (pt_walk (sat_asid r) (MEM q) (TTBR0 r) xc) = the (pt_walk (sat_asid r) (MEM q) (TTBR0 r) x)")
    apply clarsimp
  using saturatd_lookup_hit_no_fault apply fastforce
   apply (frule asid_tlb_lookup_range_fault_pt_walk)
   apply (drule_tac x = x in bspec)
  using lookup_asid_tlb_hit_entry_range apply blast
   apply clarsimp
  apply (erule disjE, clarsimp simp: asid_tlb_lookup_range_pt_walk_not_incon)
  apply (erule disjE, clarsimp simp:)
   apply blast
  apply (clarsimp simp: saturated_def asid_tlb_lookup_range_pt_walk_not_incon) by blast
  *)


(*
lemma  mmu_write_asid_ptcomp_rel:
  "\<lbrakk>saturated (typ_sat_tlb s) ;   sat_asid t = set_asid r; set_asid r = sat_asid s; MEM t = MEM r; TTBR0 t = TTBR0 s ;
       inconsistent_vaddrs (typ_sat_tlb s) \<subseteq> iset (set_tlb q) ;  incoherrent_vaddrs (typ_sat_tlb s) \<subseteq> iset(set_tlb q)\<rbrakk> \<Longrightarrow>
      incoherrent_vaddrs  (typ_sat_tlb (t\<lparr>sat_tlb := sat_tlb s \<union> the ` {e \<in> range (pt_walk (sat_asid t) (MEM r) (TTBR0 t)). \<not> is_fault e}\<rparr>)) \<subseteq> iset (set_tlb q) \<union> 
                                            incon_comp  (sat_asid t) (sat_asid t) (MEM s) (MEM r) (TTBR0 t) (TTBR0 t)"
  apply rule
  apply (clarsimp simp: incoherrent_vaddrs_def  inconsistent_vaddrs_def )
  apply (drule lookup_asid_tlb_hit_union_cases')
  apply (erule disjE)
   apply (clarsimp simp: incon_comp_def ptable_comp_def Let_def) 
   apply blast
  by  (clarsimp simp: asid_tlb_lookup_miss_is_fault_intro)
*)


lemma mmu_write_incon_set_rel:
  "\<lbrakk> saturated (typ_sat_tlb s) ; 
       inconsistent_vaddrs (typ_sat_tlb s) \<subseteq> iset (set_tlb t);  incoherrent_vaddrs (typ_sat_tlb s) \<subseteq> iset (set_tlb t); 
      sat_asid s = sat_asid r; TTBR0 s = TTBR0 r\<rbrakk> \<Longrightarrow>
     inconsistent_vaddrs (typ_sat_tlb (r\<lparr>sat_tlb := sat_tlb s \<union> the ` {e \<in> range (pt_walk (sat_asid r) (MEM q) (TTBR0 r)). \<not> is_fault e}\<rparr>))
           \<subseteq> iset(set_tlb t) \<union> incon_comp  (sat_asid r) (sat_asid r) (MEM s) (MEM q) (TTBR0 r) (TTBR0 r)"
  apply (clarsimp)
  apply (clarsimp simp: inconsistent_vaddrs_def incon_comp_def ptable_comp_def  incoherrent_vaddrs_def)
  apply (erule disjE)
   apply (drule union_asid_tlb_incon_cases)
   apply (erule disjE, clarsimp simp: saturated_def asid_tlb_lookup_range_pt_walk_not_incon) apply blast
   apply (erule disjE, clarsimp simp: asid_tlb_lookup_range_pt_walk_not_incon)
   apply (erule disjE)   apply blast
   apply (erule disjE, clarsimp simp: asid_tlb_lookup_range_pt_walk_not_incon)
   apply (erule disjE) apply blast
   apply (erule disjE, clarsimp simp: asid_tlb_lookup_range_pt_walk_not_incon)
   apply clarsimp
   apply (subgoal_tac "is_fault (pt_walk (sat_asid r) (MEM s) (TTBR0 r) x)")
    apply blast
   apply (clarsimp simp:)
  apply (erule disjE) 
   apply (erule disjE) 
    apply (drule union_asid_tlb_incon_cases)
    apply (erule disjE, clarsimp simp: saturated_def asid_tlb_lookup_range_pt_walk_not_incon)
    apply (erule disjE, clarsimp simp: asid_tlb_lookup_range_pt_walk_not_incon)
     apply (subgoal_tac "is_fault (pt_walk (sat_asid r) (MEM s) (TTBR0 r) x)")
      apply blast
     apply (clarsimp simp:)
    apply (erule disjE)   apply blast
    apply (erule disjE, clarsimp simp: asid_tlb_lookup_range_pt_walk_not_incon) apply blast
    apply (erule disjE, clarsimp simp: asid_tlb_lookup_range_pt_walk_not_incon)
    apply clarsimp
    apply (subgoal_tac "is_fault (pt_walk (sat_asid r) (MEM s) (TTBR0 r) x)")
     apply blast
    apply (clarsimp simp:)
   apply (drule union_asid_tlb_incon_cases)
   apply (erule disjE, clarsimp simp: saturated_def asid_tlb_lookup_range_pt_walk_not_incon)
   apply (erule disjE, clarsimp simp: asid_tlb_lookup_range_pt_walk_not_incon)
    apply (subgoal_tac "is_fault (pt_walk (sat_asid r) (MEM s) (TTBR0 r) x)")
     apply blast
    apply (clarsimp simp:)
   apply (erule disjE)   apply blast
   apply (erule disjE, clarsimp simp: asid_tlb_lookup_range_pt_walk_not_incon) apply blast
   apply (erule disjE, clarsimp simp: asid_tlb_lookup_range_pt_walk_not_incon)
   apply clarsimp
   apply (subgoal_tac "is_fault (pt_walk (sat_asid r) (MEM s) (TTBR0 r) x)")
    apply blast
   apply (clarsimp simp:)
  apply (erule disjE) 
   apply (drule union_asid_tlb_incon_cases)
   apply (erule disjE, clarsimp simp: saturated_def asid_tlb_lookup_range_pt_walk_not_incon)
   apply (erule disjE, clarsimp simp: asid_tlb_lookup_range_pt_walk_not_incon)
   apply (subgoal_tac "is_fault (pt_walk (sat_asid r) (MEM s) (TTBR0 r) x)")
    apply blast
   apply (clarsimp simp:)
  apply (drule union_asid_tlb_incon_cases)
  apply (erule disjE, clarsimp simp: saturated_def asid_tlb_lookup_range_pt_walk_not_incon)
  apply (erule disjE, clarsimp)
   apply (subgoal_tac "the (pt_walk (sat_asid r) (MEM q) (TTBR0 r) xc) = the (pt_walk (sat_asid r) (MEM q) (TTBR0 r) x)")
    apply clarsimp
  using saturatd_lookup_hit_no_fault apply fastforce
   apply (frule asid_tlb_lookup_range_fault_pt_walk)
   apply (drule_tac x = x in bspec)
  using lookup_asid_tlb_hit_entry_range apply blast
   apply clarsimp
  apply (erule disjE, clarsimp simp: asid_tlb_lookup_range_pt_walk_not_incon)
  apply (erule disjE, clarsimp simp:)
   apply blast
  apply (clarsimp simp: saturated_def asid_tlb_lookup_range_pt_walk_not_incon) by blast

  
lemma  mmu_write_asid_ptcomp_rel:
  "\<lbrakk>saturated (typ_sat_tlb s) ;   sat_asid t = set_asid r; set_asid r = sat_asid s; MEM t = MEM r; TTBR0 t = TTBR0 s ;
       inconsistent_vaddrs (typ_sat_tlb s) \<subseteq> iset (set_tlb q) ;  incoherrent_vaddrs (typ_sat_tlb s) \<subseteq> iset(set_tlb q)\<rbrakk> \<Longrightarrow>
      incoherrent_vaddrs  (typ_sat_tlb (t\<lparr>sat_tlb := sat_tlb s \<union> the ` {e \<in> range (pt_walk (sat_asid t) (MEM r) (TTBR0 t)). \<not> is_fault e}\<rparr>)) \<subseteq> iset (set_tlb q) \<union> 
                                            incon_comp  (sat_asid t) (sat_asid t) (MEM s) (MEM r) (TTBR0 t) (TTBR0 t)"
  apply rule
  apply (clarsimp simp: incoherrent_vaddrs_def  inconsistent_vaddrs_def )
  apply (drule lookup_asid_tlb_hit_union_cases')
  apply (erule disjE)
   apply (clarsimp simp: incon_comp_def ptable_comp_def Let_def) 
   apply blast
  by  (clarsimp simp: asid_tlb_lookup_miss_is_fault_intro)



lemma mmu_write_sat_incon_refine:        
  "\<lbrakk> mmu_write_size (val,va, sz) s = ((), s');  mmu_write_size (val,va, sz) t = ((), t'); va \<notin> iset(set_tlb t);
            tlb_rel_abs (typ_sat_tlb s) (typ_set_tlb t)  \<rbrakk> \<Longrightarrow> 
                                  tlb_rel_abs (typ_sat_tlb s') (typ_set_tlb t')"  
  apply (frule_tac s = s in tlb_rel_abs_consistent' ; clarsimp )
  apply (frule tlb_rel_absD' , clarsimp)
  apply (clarsimp simp: mmu_write_size_sat_tlb_state_ext_def  mmu_write_size_set_tlb_state_ext_def)
  apply (cases "mmu_translate va s", cases "mmu_translate va t" , clarsimp)
  apply (frule_tac t=t and pa'= aa and t' = ba in mmu_translate_sat_incon_refine; clarsimp) 
  apply (clarsimp simp: tlb_rel_abs_def)
  apply (subgoal_tac "exception b = exception ba")
   prefer 2 apply (case_tac b , case_tac ba , clarsimp simp: state.defs)
  apply (clarsimp split: if_split_asm)
  apply (case_tac "write'mem1 (val, aa, sz) b " , case_tac "write'mem1 (val, aa, sz) ba" , clarsimp simp: Let_def)
  apply (subgoal_tac "state.truncate bb = state.truncate bc")
   prefer 2 
   apply (meson write_mem_state_trun_equal)
  apply (rule conjI , clarsimp simp: state.defs)
  apply (subgoal_tac "MEM bb = MEM bc  \<and> MEM s = MEM b" , simp)
   apply (subgoal_tac "sat_asid s =  sat_asid b \<and> TTBR0 s = TTBR0 b" , simp)
    apply (subgoal_tac "saturated (typ_sat_tlb b)")
     prefer 2 apply blast
    prefer 2 apply (drule mmu_sat_eq_asid_root_mem) apply simp 
   prefer 2
   apply (rule conjI)
    apply (clarsimp simp: state.defs)
   apply (drule mmu_sat_eq_asid_root_mem) apply simp  
  apply (subgoal_tac "set_asid t = set_asid bc \<and> sat_asid b = sat_asid bb \<and> TTBR0 b = TTBR0 bb")
   prefer 2
   apply (rule conjI)
    apply (subgoal_tac "set_asid t = set_asid ba \<and> set_asid ba = set_asid bc") 
     apply presburger
    apply (rule conjI, drule mmu_incon_eq_asid_root_mem') 
     apply presburger
    apply (clarsimp simp: write'mem1_def raise'exception_def split: if_split_asm)
   apply (clarsimp simp: write'mem1_def raise'exception_def split: if_split_asm)
  apply (simp only: incon_addrs_def)
  apply simp
  apply (rule conjI)
   apply (clarsimp simp: saturated_def)
  apply (rule conjI)
   apply (drule_tac s = b and t = ba and q = bc and r = bb in mmu_write_incon_set_rel; clarsimp simp:) 
  apply (rule conjI)
   apply (frule_tac t = bb and r = bc and q = ba and s = b in  mmu_write_asid_ptcomp_rel ; clarsimp simp:)
  apply (rule conjI) 
   apply (simp only: global_entries_union)
   apply clarsimp
   apply blast
  apply (clarsimp simp: )
  apply (subgoal_tac "sat_tlb b \<union> the ` {e \<in> range (pt_walk (set_asid bc) (MEM bc) (TTBR0 bb)). \<not> is_fault e} =
                       sat_tlb b \<union> non_global_entries (the ` {e \<in> range (pt_walk (set_asid bc) (MEM bc) (TTBR0 bb)). \<not> is_fault e}) \<union> 
                                    global_entries (the ` {e \<in> range (pt_walk (set_asid bc) (MEM bc) (TTBR0 bb)). \<not> is_fault e})")
   prefer 2
   apply (metis (no_types) sup_assoc tlb_global_non_global_union)
  apply clarsimp
  apply (thin_tac "sat_tlb b \<union> the ` {e \<in> range (pt_walk (set_asid bc) (MEM bc) (TTBR0 bb)). \<not> is_fault e} =
                       sat_tlb b \<union> non_global_entries (the ` {e \<in> range (pt_walk (set_asid bc) (MEM bc) (TTBR0 bb)). \<not> is_fault e}) \<union> 
                                    global_entries (the ` {e \<in> range (pt_walk (set_asid bc) (MEM bc) (TTBR0 bb)). \<not> is_fault e})")
  apply (subgoal_tac "lookup'' (non_global_entries (the ` {e \<in> range (pt_walk (set_asid bc) (MEM bc) (TTBR0 bb)). \<not> is_fault e})) a v = Miss")
   prefer 2
   apply (clarsimp simp: asid_unequal_lookup_pt_walk_miss)
  apply (drule_tac t = "sat_tlb b" and t''' = "global_entries (the ` {e \<in> range (pt_walk (set_asid bc) (MEM bc) (TTBR0 bb)). \<not> is_fault e})" 
      and t'' = "global_entries (sat_tlb b \<union> non_global_entries (the ` {e \<in> range (pt_walk (set_asid bc) (MEM bc) (TTBR0 bb)). \<not> is_fault e}) \<union> 
       global_entries (the ` {e \<in> range (pt_walk (set_asid bc) (MEM bc) (TTBR0 bb)). \<not> is_fault e}))" in  lookup_union_minus_equal)
  apply clarsimp
  apply (subgoal_tac " global_entries (sat_tlb b \<union> non_global_entries (the ` {e \<in> range (pt_walk (set_asid bc) (MEM bc) (TTBR0 bb)). \<not> is_fault e}) \<union> 
                     global_entries (the ` {e \<in> range (pt_walk (set_asid bc) (MEM bc) (TTBR0 bb)). \<not> is_fault e})) =
                          global_entries (sat_tlb b \<union> the ` {e \<in> range (pt_walk (set_asid bc) (MEM bc) (TTBR0 bb)). \<not> is_fault e})")
   prefer 2
   apply (clarsimp simp: global_entries_def non_global_entries_def) apply blast
  apply (clarsimp)
  apply (subgoal_tac "sat_tlb b = sat_tlb s  \<and> set_tlb ba = set_tlb t")
   prefer 2
   apply (clarsimp simp: mmu_translate_saturated_tlb_unchange mmu_translate_incon_unchange)
  apply clarsimp
  apply (clarsimp simp: global_entries_union)
  apply (clarsimp simp: Un_Diff)
  apply (simp only: set_double_minus [symmetric])
  apply clarsimp
  apply (drule_tac x = a in spec, clarsimp, drule_tac x = v in spec)
  apply (clarsimp simp: lookup_minus_smaller_order)
  done


(* refinement for read theroems *)

lemma  mem_read1_consistent_tlb_rel_non_det_det:
  " \<lbrakk>mem_read1 (a, sz) s = (val, s');   mem_read1 (a, sz) t = (val', t'); 
               consistent0 (lookup'' (det_tlb t) (det_asid t)) (pt_walk (det_asid t)  (MEM t) (TTBR0 t))   va; tlb_rel_det (typ_non_det_tlb s) (typ_det_tlb t)\<rbrakk>
              \<Longrightarrow> consistent0 (lookup'' (det_tlb t')  (det_asid t')) (pt_walk (det_asid t') (MEM t') (TTBR0 t')) va \<and> tlb_rel_det (typ_non_det_tlb s') (typ_det_tlb t')"
   apply (rule conjI)
   apply (subgoal_tac "MEM t = MEM t' \<and>   TTBR0 t = TTBR0 t' \<and> det_asid t = det_asid t' \<and> det_tlb t = det_tlb t'")
    apply (clarsimp simp: consistent0_def)
   prefer 2
   apply (subgoal_tac " exception s' =  exception t'")
    apply (drule mem1_read_exception)
    apply (drule mem1_read_exception)
    apply (clarsimp simp: tlb_rel_det_def)
    apply (clarsimp simp: saturated_def  state.truncate_def)
    apply (cases s', cases t')
    apply clarsimp
   apply (subgoal_tac "MEM s = MEM t \<and> exception s = exception t")
    apply (thin_tac "tlb_rel_det (typ_non_det_tlb s) (typ_det_tlb t)")
    apply (clarsimp simp: mem_read1_def)
    apply (clarsimp split: if_split_asm)
        apply (clarsimp simp: mem1_def raise'exception_def split: option.splits if_split_asm)
       apply (clarsimp simp: mem1_def raise'exception_def split: option.splits if_split_asm)
      apply (clarsimp simp: mem1_def raise'exception_def split: option.splits if_split_asm)
     subgoal
     by (clarsimp simp: mem1_def raise'exception_def split: option.splits if_split_asm)
    apply (clarsimp simp: raise'exception_def split: option.splits if_split_asm)
   apply (clarsimp simp: tlb_rel_det_def state.defs)
  apply (drule mem1_read_exception)
  apply (drule mem1_read_exception)
  apply (cases t, cases t' , clarsimp)
   done




lemma  mem_read1_consistent_tlb_rel_det_sat:
  " \<lbrakk>mem_read1 (a, sz) s = (val, s');   mem_read1 (a, sz) t = (val', t'); 
                consistent0 (lookup'' (sat_tlb t) (sat_asid t)) (pt_walk (sat_asid t) (MEM t) (TTBR0 t)) va; tlb_rel_sat (typ_det_tlb s) (typ_sat_tlb t)\<rbrakk>
              \<Longrightarrow>  consistent0 (lookup'' (sat_tlb t') (sat_asid t')) (pt_walk (sat_asid t') (MEM t') (TTBR0 t')) va \<and> tlb_rel_sat (typ_det_tlb s') (typ_sat_tlb t')"
   apply (rule conjI)
   apply (subgoal_tac "MEM t = MEM t' \<and>   TTBR0 t = TTBR0 t' \<and> sat_asid t = sat_asid t' \<and> sat_tlb t = sat_tlb t'")
    apply (clarsimp simp: consistent0_def)
   prefer 2
   apply (subgoal_tac " exception s' =  exception t'")
    apply (drule mem1_read_exception)
    apply (drule mem1_read_exception)
    apply (clarsimp simp: tlb_rel_sat_def)
    apply (clarsimp simp: saturated_def  state.truncate_def)
    apply (cases s', cases t')
    apply clarsimp
   apply (subgoal_tac "MEM s = MEM t \<and> exception s = exception t")   
    apply (thin_tac "tlb_rel_sat (typ_det_tlb s) (typ_sat_tlb t)")
    apply (clarsimp simp: mem_read1_def)
    apply (clarsimp split: if_split_asm)
        apply (clarsimp simp: mem1_def raise'exception_def split: option.splits if_split_asm)
       apply (clarsimp simp: mem1_def raise'exception_def split: option.splits if_split_asm)
      apply (clarsimp simp: mem1_def raise'exception_def split: option.splits if_split_asm)
     subgoal
     by (clarsimp simp: mem1_def raise'exception_def split: option.splits if_split_asm)
    apply (clarsimp simp: raise'exception_def split: option.splits if_split_asm)
   apply (clarsimp simp: tlb_rel_sat_def state.defs)
  apply (drule mem1_read_exception)
  apply (drule mem1_read_exception)
  apply (cases t, cases t' , clarsimp)
   done


lemma mmu_read_non_det_det_rel_cons:
  "\<lbrakk> mmu_read_size (va, sz) s = (val, s'); tlb_rel_det (typ_non_det_tlb s) (typ_det_tlb t);
         consistent (typ_det_tlb t) va; mmu_read_size (va, sz) t = (val', t') \<rbrakk> \<Longrightarrow>  
                     consistent (typ_det_tlb t') va \<and>  tlb_rel_det (typ_non_det_tlb s') (typ_det_tlb t') "
  apply (clarsimp simp: mmu_read_size_det_tlb_state_ext_def   mmu_read_size_non_det_tlb_state_ext_def Let_def)
  apply (cases "mmu_translate va s", cases "mmu_translate va t", clarsimp)
  apply (drule_tac t = t in mmu_translate_non_det_det_refine ; clarsimp simp: Let_def mem_read1_consistent_tlb_rel_non_det_det)
  done


lemma mmu_read_det_sat_rel_cons:
  "\<lbrakk> mmu_read_size (va, sz) s = (val, s'); tlb_rel_sat (typ_det_tlb s) (typ_sat_tlb t);
         consistent (typ_sat_tlb t) va; mmu_read_size (va, sz) t = (val', t') \<rbrakk> \<Longrightarrow>  
                     consistent (typ_sat_tlb t') va \<and>  tlb_rel_sat (typ_det_tlb s') (typ_sat_tlb t') "
  apply (clarsimp simp: mmu_read_size_sat_tlb_state_ext_def   mmu_read_size_det_tlb_state_ext_def Let_def)
  apply (cases "mmu_translate va s", cases "mmu_translate va t", clarsimp)
  apply (drule_tac t = t in mmu_translate_det_sat_refine ; clarsimp simp: Let_def mem_read1_consistent_tlb_rel_det_sat)
  done

lemma same_mem_read_equal:
  "\<lbrakk>MEM s = MEM t; mem_read1 (pa, sz) s = (val, s'); mem_read1 (pa, sz) t = (val', t')  \<rbrakk> \<Longrightarrow> val = val'"
  apply (clarsimp simp: mem_read1_def)
  apply (clarsimp split: if_split_asm)
      apply (clarsimp simp: mem1_def raise'exception_def split: option.splits if_split_asm)
     apply (clarsimp simp: mem1_def raise'exception_def split: option.splits if_split_asm)
    apply (clarsimp simp: mem1_def raise'exception_def split: option.splits if_split_asm)
  subgoal
    by (clarsimp simp: mem1_def raise'exception_def split: option.splits if_split_asm)
  apply (clarsimp simp: raise'exception_def split: option.splits if_split_asm)
    done


lemma mmu_read_non_det_det_refine:
  "\<lbrakk>mmu_read_size (va, sz) s = (val, s');  mmu_read_size (va, sz) t = (val', t'); 
              tlb_rel_det (typ_non_det_tlb s) (typ_det_tlb t); consistent (typ_det_tlb t) va\<rbrakk> \<Longrightarrow>  
                     val = val' \<and> tlb_rel_det (typ_non_det_tlb s') (typ_det_tlb t') \<and> consistent (typ_det_tlb t') va  "
  apply (rule conjI)
   apply (clarsimp simp: mmu_read_size_det_tlb_state_ext_def   mmu_read_size_non_det_tlb_state_ext_def Let_def)
   apply (cases "mmu_translate va s", cases "mmu_translate va t", clarsimp)
   apply (rename_tac pa s'' pa' t'')
   apply (subgoal_tac "pa = pa'", clarsimp)
    apply (subgoal_tac "MEM s'' = MEM t''")
     apply (clarsimp simp: same_mem_read_equal)
  using mmu_det_eq_asid_root_mem mmu_eq_asid_root_mem tlb_rel_detD apply fastforce 
  using det_tlb_more mmu_translate_non_det_det_pa apply fastforce
  by (frule_tac t = t and t' =t' in  mmu_read_non_det_det_rel_cons; simp?)


lemma mmu_read_non_det_sat_refine:
  "\<lbrakk>mmu_read_size (va, sz) s = (val, s');  mmu_read_size (va, sz) t = (val', t'); 
              tlb_rel_sat (typ_det_tlb s) (typ_sat_tlb t); consistent (typ_sat_tlb t) va\<rbrakk> \<Longrightarrow>  
                     val = val' \<and> tlb_rel_sat (typ_det_tlb s') (typ_sat_tlb t') \<and> consistent (typ_sat_tlb t') va  "
  apply (rule conjI)
   apply (clarsimp simp: mmu_read_size_det_tlb_state_ext_def   mmu_read_size_sat_tlb_state_ext_def Let_def)
   apply (cases "mmu_translate va s", cases "mmu_translate va t", clarsimp)
   apply (rename_tac pa s'' pa' t'')
   apply (subgoal_tac "pa = pa'", clarsimp)
    apply (subgoal_tac "MEM s'' = MEM t''") 
     apply (clarsimp simp: same_mem_read_equal) 
  using mmu_det_eq_asid_root_mem mmu_sat_eq_asid_root_mem tlb_rel_satD apply fastforce
  apply (simp add: mmu_translate_non_det_sat_pa)
  apply (frule_tac t = t and t' =t' in  mmu_read_det_sat_rel_cons; simp?)
  done


lemma mmu_read_sat_const_inter [simp]:
  "saturated (typ_sat_tlb s) \<Longrightarrow> sat_tlb (snd (mmu_read_size v s)) = sat_tlb s "
   by (clarsimp simp: mmu_read_size_sat_tlb_state_ext_def split_def Let_def
                      mem_read1_def raise'exception_def  split: if_split_asm)
  

lemma  mem_read1_consistent_tlb_rel_incon:
  "\<lbrakk>mem_read1 (a, sz) s = (val, s'); mem_read1 (a, sz) t = (val', t'); 
             va \<notin> iset (set_tlb t); tlb_rel_abs (typ_sat_tlb s) (typ_set_tlb t)\<rbrakk>
              \<Longrightarrow>  va \<notin> iset(set_tlb t') \<and>  tlb_rel_abs (typ_sat_tlb s') (typ_set_tlb t')"
  apply (rule conjI)
   apply (subgoal_tac "set_tlb t = set_tlb t'")
    apply clarsimp
   apply (drule mem1_read_exception)
   apply (drule mem1_read_exception)
   apply (cases t, cases t')
   apply clarsimp
  apply (subgoal_tac "exception s' =  exception t'")
   apply (drule mem1_read_exception)
   apply (drule mem1_read_exception)
   apply (clarsimp simp: tlb_rel_abs_def)
   apply (rule conjI)
    apply (clarsimp simp: state.defs)
    apply (cases s', cases t')
    apply clarsimp
   apply (rule conjI)
    apply (clarsimp simp: state.defs)
    apply (cases s', cases t')
    apply clarsimp
   apply (rule conjI)
    apply (clarsimp simp:  saturated_def)
  apply (rule conjI)
    apply (clarsimp simp: incon_addrs_def inconsistent_vaddrs_def incoherrent_vaddrs_def)
    apply (cases s', cases t')
    apply clarsimp 
   apply (rule conjI)
    apply (cases t, cases t')
    apply (clarsimp)
   apply clarsimp
   apply (subgoal_tac "set_tlb t' = set_tlb t")
    apply clarsimp
   apply (cases t, cases t')
   apply clarsimp
  apply (subgoal_tac "MEM s = MEM t \<and> exception s = exception t")
   apply (thin_tac " va \<notin> iset(set_tlb t)")    
   apply (thin_tac " tlb_rel_abs (typ_sat_tlb s) (typ_set_tlb t)")
   apply (clarsimp simp: mem_read1_def)
   apply (clarsimp split: if_split_asm)
       apply (clarsimp simp: mem1_def raise'exception_def split: option.splits if_split_asm)
      apply (clarsimp simp: mem1_def raise'exception_def split: option.splits if_split_asm)
     apply (clarsimp simp: mem1_def raise'exception_def split: option.splits if_split_asm)
    subgoal
    by (clarsimp simp: mem1_def raise'exception_def split: option.splits if_split_asm)
   apply (clarsimp simp: raise'exception_def split: option.splits if_split_asm)
  apply (clarsimp simp: tlb_rel_abs_def state.defs)
  done


lemma mmu_read_sat_incon_rel_con:
  "\<lbrakk> mmu_read_size (va, sz) s = (val, s'); tlb_rel_abs (typ_sat_tlb s) (typ_set_tlb t);
         va \<notin> iset (set_tlb t); mmu_read_size (va, sz) t = (val', t') \<rbrakk> \<Longrightarrow>  
                     va \<notin> iset(set_tlb t') \<and>  tlb_rel_abs (typ_sat_tlb s') (typ_set_tlb t') "
  apply (clarsimp simp: mmu_read_size_sat_tlb_state_ext_def  mmu_read_size_set_tlb_state_ext_def Let_def)
  apply (cases "mmu_translate va s", cases "mmu_translate va t", clarsimp)
  apply (drule_tac t = t and pa' = aa  and t' = ba in mmu_translate_sat_incon_refine ; clarsimp simp: Let_def mem_read1_consistent_tlb_rel_incon)
  done


lemma mmu_read_sat_incon_refine:
  "\<lbrakk> mmu_read_size (va, sz) s = (val, s'); mmu_read_size (va, sz) t = (val', t');
        tlb_rel_abs (typ_sat_tlb s) (typ_set_tlb t); va \<notin> iset (set_tlb t)  \<rbrakk> \<Longrightarrow>  
                    val = val' \<and> tlb_rel_abs (typ_sat_tlb s') (typ_set_tlb t') \<and> va \<notin> iset(set_tlb t')"
  apply (rule conjI)
   apply (clarsimp simp: mmu_read_size_sat_tlb_state_ext_def  mmu_read_size_set_tlb_state_ext_def Let_def)
   apply (cases "mmu_translate va s", cases "mmu_translate va t", clarsimp)
   apply (rename_tac pa s'' pa' t'')
   apply (subgoal_tac "pa = pa'", clarsimp)
    apply (subgoal_tac "MEM s'' = MEM t''")
     apply (clarsimp simp: same_mem_read_equal)
    using mmu_translate_sat_incon_mem_excp apply force
   using mmu_translate_sat_incon_refine apply force
   by (frule_tac t = t and t' = t' in  mmu_read_sat_incon_rel_con; simp)


end