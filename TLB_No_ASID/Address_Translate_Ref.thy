theory Address_Translate_Ref

imports  MMU_Instants_TLB

begin    



lemma mmu_rel:
  "\<lbrakk> mmu_translate va s = (p, s') \<rbrakk>  \<Longrightarrow> s' = s \<lparr> non_det_tlb := non_det_tlb s' , exception:= exception s' \<rparr>"
   by (clarsimp simp: mmu_translate_non_det_tlb_state_ext_def Let_def  raise'exception_def split:lookup_type.splits if_split_asm)


lemma mmu_det_rel:
  "\<lbrakk> mmu_translate va s = (p, s') \<rbrakk>  \<Longrightarrow> s' = s \<lparr>det_tlb := det_tlb s' , exception:= exception s' \<rparr>"
   by (clarsimp simp: mmu_translate_det_tlb_state_ext_def Let_def  raise'exception_def split:lookup_type.splits if_split_asm)


lemma mmu_sat_rel:
  "\<lbrakk> mmu_translate va s = (p, s') \<rbrakk>  \<Longrightarrow> s' = s \<lparr> sat_tlb := sat_tlb s' , exception:= exception s' \<rparr>"
  by (clarsimp simp: mmu_translate_sat_tlb_state_ext_def Let_def  raise'exception_def split:lookup_type.splits if_split_asm)


lemma mmu_incon_rel:
  "\<lbrakk>  mmu_translate va t = (pa', t')\<rbrakk>  \<Longrightarrow> (t'::'a set_tlb_state_scheme) = t\<lparr>exception := exception t'\<rparr>"
  by (clarsimp simp: mmu_translate_set_tlb_state_ext_def Let_def raise'exception_def split: if_split_asm)


lemma mmu_eq_asid_root_mem:
  "\<lbrakk> mmu_translate va (s::'a non_det_tlb_state_scheme) = (pa , s') \<rbrakk>  \<Longrightarrow> TTBR0 s = TTBR0 s' \<and>  MEM s = MEM s'"
  by (clarsimp simp: mmu_translate_non_det_tlb_state_ext_def Let_def raise'exception_def  split: lookup_type.splits if_split_asm)

lemma mmu_det_eq_asid_root_mem:
  "\<lbrakk> mmu_translate va (s::'a det_tlb_state_scheme) = (pa , s') \<rbrakk>  \<Longrightarrow> TTBR0 s = TTBR0 s' \<and>  MEM s = MEM s'"
  by (clarsimp simp: mmu_translate_det_tlb_state_ext_def Let_def raise'exception_def  split: lookup_type.splits if_split_asm)
 
lemma mmu_sat_eq_asid_root_mem:
  "\<lbrakk> mmu_translate va (s::'a sat_tlb_state_scheme) = (pa , s') \<rbrakk>  \<Longrightarrow>  TTBR0 s = TTBR0 s' \<and> MEM s = MEM s'"
  by (clarsimp simp: mmu_translate_sat_tlb_state_ext_def Let_def  raise'exception_def split:lookup_type.splits if_split_asm)

lemma mmu_incon_eq_asid_root_mem:
  "\<lbrakk> mmu_translate va (s::'a set_tlb_state_scheme) = (pa , s') \<rbrakk>  \<Longrightarrow> TTBR0 s = TTBR0 s' \<and> MEM s = MEM s'"
  by (clarsimp simp: mmu_translate_set_tlb_state_ext_def Let_def  raise'exception_def split:lookup_type.splits if_split_asm)


lemma mmu_translate_sat_tlb_union:
  "mmu_translate v s = (p,t) \<Longrightarrow> 
      sat_tlb t = sat_tlb s \<union> the ` {e\<in>pt_walk ()  (MEM s) (TTBR0 s) ` UNIV. \<not>is_fault e}"
  by (clarsimp simp:  mmu_translate_sat_tlb_state_ext_def Let_def raise'exception_def split:lookup_type.splits if_split_asm)


lemma mmu_translate_saturated_tlb_unchange:
  "\<lbrakk> mmu_translate va s = (pa, s'); saturated (typ_sat_tlb s) \<rbrakk> \<Longrightarrow> sat_tlb s' = sat_tlb s"
  apply (clarsimp simp:  mmu_translate_sat_tlb_state_ext_def Let_def saturated_def  raise'exception_def
                  split: lookup_type.splits if_split_asm)
  by blast+
 

lemma mmu_translate_saturated_tlb_unchange_pair:
  "\<lbrakk> mmu_translate va s = (pa, s'); saturated (typ_sat_tlb s) \<rbrakk>
       \<Longrightarrow> sat_tlb s' = sat_tlb s"
  apply (clarsimp simp:  mmu_translate_sat_tlb_state_ext_def Let_def saturated_def  raise'exception_def
                  split: lookup_type.splits if_split_asm)
  by blast+

lemma mmu_translate_incon_unchange:
  "\<lbrakk> mmu_translate va t = (aa, ba)\<rbrakk>  \<Longrightarrow> set_tlb ba = set_tlb t"
  by (clarsimp simp: mmu_translate_set_tlb_state_ext_def Let_def raise'exception_def split: if_split_asm)


lemma mmu_translate_saturated_state:
  "mmu_translate v s = (p,t) \<Longrightarrow>   saturated (typ_sat_tlb t)"
  apply (clarsimp simp: mmu_translate_sat_tlb_state_ext_def Let_def split: lookup_type.splits)
    by (clarsimp simp: saturated_def raise'exception_def split:if_split_asm)+


lemma mmu_translate_sat_const_tlb [simp]:
  "saturated (typ_sat_tlb s) \<Longrightarrow> sat_tlb (snd (mmu_translate va s)) = sat_tlb s"
  apply (simp add: mmu_translate_sat_tlb_state_ext_def Let_def raise'exception_def fst_def split: lookup_type.splits)
  using sat_state_tlb by fastforce



(* Refinement *)


lemma  mmu_translate_non_det_det_refine:
  "\<lbrakk> mmu_translate va s = (pa, s');  consistent (typ_det_tlb t) va; tlb_rel_det (typ_non_det_tlb s) (typ_det_tlb t)  \<rbrakk> \<Longrightarrow>
    let (pa', t') = mmu_translate va t
     in pa' = pa  \<and> consistent (typ_det_tlb t') va \<and> tlb_rel_det (typ_non_det_tlb s') (typ_det_tlb t')"
  apply (frule (1) tlb_rel_det_consistent , clarsimp)
  apply (frule tlb_rel_detD , clarsimp)
  apply (subgoal_tac "non_det_tlb s - tlb_evict (typ_non_det_tlb s) \<subseteq> non_det_tlb s")
   prefer 2 apply blast
  apply (subgoal_tac "lookup' (non_det_tlb s - tlb_evict (typ_non_det_tlb s)) va \<le> lookup' (det_tlb t) va")
   prefer 2 apply (simp add: tlb_mono)
  apply (clarsimp simp: mmu_translate_non_det_tlb_state_ext_def mmu_translate_det_tlb_state_ext_def split_def Let_def split: if_split_asm)
  apply (cases "lookup' (det_tlb t) va" ; clarsimp simp: Let_def)
    apply (simp add: raise'exception_def typ_det_tlb_def typ_non_det_tlb_def tlb_rel_det_def split: if_split_asm)
      apply (cases s, cases t, clarsimp simp: state.defs)
      apply fastforce
     apply (cases s, cases t ,clarsimp simp: state.defs)
     apply fastforce
    apply (rule conjI) 
     apply (cases s, cases t ,clarsimp simp: consistent0_def state.defs ) 
     apply (simp add: is_fault_def lookup_refill)
    apply (cases s, cases t ,clarsimp simp: state.defs)
    apply fastforce
   apply (simp add: consistent0_def )
  apply (cases "lookup' (non_det_tlb s - tlb_evict (typ_non_det_tlb s))   va"; clarsimp)
   apply (clarsimp simp : consistent0_def Let_def tlb_rel_det_def 
      lookup_in_tlb split: if_split_asm)
   apply (drule lookup_in_tlb)
   apply (simp add: typ_det_tlb_def state.defs)
  apply (clarsimp split: if_split_asm simp: tlb_rel_det_def typ_non_det_tlb_def typ_det_tlb_def state.defs )
  using lookup_in_tlb by blast


lemma mmu_translate_det_sat_refine:
  "\<lbrakk> mmu_translate va s = (pa, s'); consistent (typ_sat_tlb t) va; tlb_rel_sat (typ_det_tlb s) (typ_sat_tlb t)  \<rbrakk> \<Longrightarrow>
         let (pa', t') = mmu_translate va t
         in pa' = pa \<and> consistent (typ_sat_tlb t') va \<and> tlb_rel_sat (typ_det_tlb s') (typ_sat_tlb t')"
  apply (frule (1) tlb_rel_sat_consistent , clarsimp)
  apply (frule tlb_rel_satD , clarsimp)
  apply (subgoal_tac "lookup' (det_tlb s) va \<le> lookup' (sat_tlb t \<union> the `{e\<in>pt_walk ()  (MEM s) (TTBR0 s) ` UNIV. \<not> is_fault e}) va")
   prefer 2
   apply (simp add: saturated_def sup.absorb1 tlb_mono tlb_rel_sat_def)
  apply (subgoal_tac "sat_tlb t = sat_tlb t \<union> the `{e\<in>pt_walk ()  (MEM s) (TTBR0 s) ` UNIV. \<not> is_fault e}")
   prefer 2
   apply (fastforce simp: tlb_rel_sat_def saturated_def)
  apply (clarsimp simp: mmu_translate_det_tlb_state_ext_def  mmu_translate_sat_tlb_state_ext_def split_def Let_def)  
  apply (cases "lookup' (sat_tlb t \<union> the `{e \<in> range (pt_walk ()  (MEM s) (TTBR0 s)). \<not> is_fault e}) va"; clarsimp simp: Let_def)
    apply (clarsimp simp: tlb_rel_sat_def Let_def)
    apply (subgoal_tac "is_fault (pt_walk ()  (MEM s) (TTBR0 s) va)")
     apply (clarsimp simp: raise'exception_def  saturated_def state.defs  split: if_split_asm) 
    apply (clarsimp simp: lookup_def entry_set_def is_fault_def split: if_split_asm)
    apply force
   apply (clarsimp simp: consistent0_def)
  apply (subgoal_tac "x3 = the (pt_walk ()  (MEM s) (TTBR0 s) va)")
   prefer 2
   apply (clarsimp simp: consistent0_def)
  apply (cases "lookup' (det_tlb s) va"; clarsimp simp: Let_def)
  apply (subgoal_tac "\<not>is_fault (pt_walk ()  (MEM s) (TTBR0 s) va)")
   prefer 2
   apply (clarsimp simp: tlb_rel_sat_def is_fault_def lookup_in_tlb) 

   apply (subgoal_tac "\<not>is_fault (pt_walk ()  (MEM s) (TTBR0 s) va)")
    apply (clarsimp simp: tlb_rel_sat_def is_fault_def lookup_in_tlb)
   apply (simp add: consistent_not_Incon_imp is_fault_def)
  by (clarsimp simp: tlb_rel_sat_def typ_sat_tlb_def typ_det_tlb_def state.defs lookup_in_tlb raise'exception_def split: if_split_asm)



lemma mmu_translate_sat_incon_refine_pa:
  "\<lbrakk> mmu_translate va s = (pa, s');  mmu_translate va t = (pa', t') ;
           va \<notin> set_tlb t ; tlb_rel_abs (typ_sat_tlb s) (typ_set_tlb t) \<rbrakk> \<Longrightarrow> 
                                          pa = pa'"
  apply (frule_tac s = s in tlb_rel_abs_consistent ; clarsimp )
  apply (frule tlb_rel_absD , clarsimp)
  apply (clarsimp simp: mmu_translate_set_tlb_state_ext_def mmu_translate_sat_tlb_state_ext_def split_def Let_def)
  apply (subgoal_tac "sat_tlb s = sat_tlb s \<union> the ` {e\<in>pt_walk () (MEM s) (TTBR0 s) ` UNIV. \<not>is_fault e}")
   prefer 2
   apply (fastforce simp: saturated_def)
  apply (cases "lookup' (sat_tlb s \<union> the ` {e\<in>pt_walk () (MEM s) (TTBR0 s) ` UNIV. \<not>is_fault e})   va")
    apply clarsimp
    apply (frule_tac va = va in  sat_miss_fault, simp) 
    apply (clarsimp simp: raise'exception_def is_fault_def split:if_split_asm)
   apply (clarsimp simp: consistent0_def)
  apply (subgoal_tac "x3 = the (pt_walk () (MEM s) (TTBR0 s) va)")
   prefer 2
   apply (clarsimp simp: consistent0_def)
  apply (subgoal_tac "\<not>is_fault (pt_walk () (MEM s) (TTBR0 s) va)", clarsimp)
  by (clarsimp simp: is_fault_def lookup_in_tlb consistent0_def)


lemma mmu_translate_sat_consistent:
  "\<lbrakk> mmu_translate va s = (pa, s');  consistent (typ_sat_tlb s) va ; saturated (typ_sat_tlb s)\<rbrakk>  \<Longrightarrow>  
                   consistent (typ_sat_tlb s') va"
  apply (subgoal_tac "sat_tlb s = sat_tlb s \<union> the ` {e\<in>pt_walk ()   (MEM s) (TTBR0 s) ` UNIV. \<not>is_fault e}")
   prefer 2
   apply (fastforce simp: saturated_def)
  apply (clarsimp simp: mmu_translate_sat_tlb_state_ext_def Let_def  split: lookup_type.splits)
   apply (clarsimp simp: raise'exception_def split:if_split_asm)+
  done


lemma mmu_translate_sat_incon_refine_tlb_rel:
  "\<lbrakk> mmu_translate va s = (pa, s');  mmu_translate va t = (pa', t') ;
           va \<notin> set_tlb t ; tlb_rel_abs (typ_sat_tlb s) (typ_set_tlb t) \<rbrakk> \<Longrightarrow> 
                                          tlb_rel_abs  (typ_sat_tlb s') (typ_set_tlb t')"
  apply (frule_tac s = s in tlb_rel_abs_consistent ; clarsimp )
  apply (frule tlb_rel_absD , clarsimp)
  apply (frule_tac mmu_translate_sat_consistent ; clarsimp simp: tlb_rel_abs_def incon_addrs_def inconsistent_vaddrs_def incoherrent_vaddrs_def)
    (* TLB is not changing as s is already saturated *)
  apply (subgoal_tac "s' = s\<lparr>exception := exception s'\<rparr> \<and> t' = t\<lparr>exception := exception t'\<rparr>")
   apply (subgoal_tac "exception t' = exception s'")
    apply (cases t, cases t, cases s, cases s', clarsimp simp: state.defs saturated_def)
   prefer 2
   apply (frule mmu_incon_rel, clarsimp)
   apply (subgoal_tac "sat_tlb s' = sat_tlb s")
    apply (drule mmu_sat_rel, clarsimp)
   apply (metis (no_types, lifting) Un_def fst_def mmu_translate_sat_tlb_union prod_eqI saturated_tlb_pde)
  apply (subgoal_tac "sat_tlb s' = sat_tlb s \<union> the ` {e\<in>pt_walk () (MEM s) (TTBR0 s) ` UNIV. \<not>is_fault e}  \<and> 
                        MEM s' = MEM s \<and> TTBR0 s' = TTBR0 s")
   apply (clarsimp simp: mmu_translate_sat_tlb_state_ext_def split_def Let_def)
   apply (cases "lookup' (sat_tlb s \<union> the ` {e\<in>pt_walk ()   (MEM s) (TTBR0 s) ` UNIV. \<not>is_fault e}) va")
     apply clarsimp
     apply (frule_tac va = va in sat_miss_fault, simp add: saturated_def)
      apply (meson lookup_miss_union)
     apply (clarsimp simp: mmu_translate_set_tlb_state_ext_def raise'exception_def is_fault_def)
     apply (cases"exception s = NoException", simp)  apply (cases t, cases s, cases t', cases s', clarsimp) apply (cases t, cases s, cases t', cases s', clarsimp)
    apply (clarsimp simp: consistent0_def)
   apply (subgoal_tac "x3 = the (pt_walk ()   (MEM s) (TTBR0 s) va)")
    prefer 2
    apply (clarsimp simp: consistent0_def)
   apply (subgoal_tac "\<not>is_fault (pt_walk ()   (MEM s) (TTBR0 s) va)")
    prefer 2
    apply (clarsimp simp: consistent0_def is_fault_def lookup_in_tlb)
   apply (simp only: mmu_translate_set_tlb_state_ext_def Let_def is_fault_def)  apply (cases t, cases s, cases t', cases s', clarsimp)
  apply (simp only: mmu_translate_sat_tlb_union mmu_sat_eq_asid_root_mem is_fault_def) 
  done

lemma mmu_translate_sat_incon_refine_consistent:
  "\<lbrakk> mmu_translate va s = (pa, s');  mmu_translate va t = (pa', t') ;
           va \<notin> set_tlb t ; tlb_rel_abs (typ_sat_tlb s) (typ_set_tlb t) \<rbrakk> \<Longrightarrow> 
                                          va \<notin> set_tlb t'"
  apply (frule_tac s = s in tlb_rel_abs_consistent ; clarsimp )
  apply (frule tlb_rel_absD , clarsimp)
  apply (clarsimp simp: mmu_translate_set_tlb_state_ext_def  Let_def mmu_translate_sat_tlb_state_ext_def split_def)
  apply (subgoal_tac "sat_tlb s = sat_tlb s \<union> the ` {e\<in>pt_walk ()   (MEM s) (TTBR0 s) ` UNIV. \<not>is_fault e}")
   prefer 2
   apply (fastforce simp: saturated_def)
  apply (cases "lookup' (sat_tlb s \<union> the ` {e\<in>pt_walk ()   (MEM s) (TTBR0 s) ` UNIV. \<not>is_fault e}) va")
    apply clarsimp
    apply (frule_tac va = va in  sat_miss_fault, simp) 
    apply (clarsimp simp: raise'exception_def is_fault_def split:if_split_asm)
   apply (clarsimp simp: consistent0_def)
  apply (subgoal_tac "x3 = the (pt_walk () (MEM s) (TTBR0 s) va)")
   prefer 2
   apply (clarsimp simp: consistent0_def)
  apply (subgoal_tac "\<not>is_fault (pt_walk () (MEM s) (TTBR0 s) va)")
   prefer 2
   apply (clarsimp simp: is_fault_def lookup_in_tlb consistent0_def)
  apply clarsimp
  done


lemma mmu_translate_sat_incon_refine:
  "\<lbrakk> mmu_translate va s = (pa, s');  mmu_translate va t = (pa', t') ;
           va \<notin> set_tlb t ; tlb_rel_abs (typ_sat_tlb s) (typ_set_tlb t) \<rbrakk> \<Longrightarrow> 
                  pa = pa' \<and>  tlb_rel_abs  (typ_sat_tlb s') (typ_set_tlb t')  \<and>  va \<notin> set_tlb t'"
  by (clarsimp simp: mmu_translate_sat_incon_refine_pa mmu_translate_sat_incon_refine_tlb_rel
      mmu_translate_sat_incon_refine_consistent)





lemma mmu_translate_det_sat_subset_rel:
  "\<lbrakk> mmu_translate va s = (pa, s'); consistent (typ_sat_tlb t) va; 
       tlb_rel_sat (typ_det_tlb s) (typ_sat_tlb t) ; mmu_translate va t = (pa', t')  \<rbrakk> \<Longrightarrow> det_tlb s' \<subseteq> sat_tlb t'"
  by (drule_tac t = t in  mmu_translate_det_sat_refine [unfolded tlb_rel_sat_def];
           simp add: tlb_rel_sat_def)


lemma mmu_translate_non_det_sat_excp:
  "\<lbrakk> mmu_translate va s = (p, s') ; mmu_translate va t = (p, t') ;
     consistent (typ_sat_tlb t) va; tlb_rel_sat (typ_det_tlb s) (typ_sat_tlb t)\<rbrakk>  \<Longrightarrow>  exception s' = exception t'"
  apply (subgoal_tac "tlb_rel_sat (typ_det_tlb s') (typ_sat_tlb t')")
   apply (clarsimp simp: tlb_rel_sat_def state.defs)
  apply (drule (2)  mmu_translate_det_sat_refine, clarsimp simp: Let_def)
 done

lemma mmu_translate_sat_state_param:
  "\<lbrakk> mmu_translate va t = (pa', t') ; saturated (typ_sat_tlb t) \<rbrakk> \<Longrightarrow>
      state.more t' = state.more t  \<and> MEM t' = MEM t \<and> TTBR0 t' = TTBR0 t \<and>  saturated (typ_sat_tlb t')"
  apply (frule sat_state_tlb)
  by (clarsimp simp: mmu_translate_sat_tlb_state_ext_def Let_def raise'exception_def
      state.defs saturated_def split: lookup_type.splits if_split_asm) 
  

lemma mmu_translate_non_det_sat_mem_excp:
  "\<lbrakk> mmu_translate va s = (p, s') ; mmu_translate va t = (p', t') ;
     consistent (typ_sat_tlb t) va; tlb_rel_sat (typ_det_tlb s) (typ_sat_tlb t)\<rbrakk>  \<Longrightarrow> MEM s' = MEM t' \<and> exception s' = exception t'"
  apply (subgoal_tac "tlb_rel_sat (typ_det_tlb s') (typ_sat_tlb t')")
   apply (clarsimp simp: tlb_rel_sat_def state.defs)
  apply (drule (2)  mmu_translate_det_sat_refine, clarsimp simp: Let_def)
  done


lemma  mmu_translate_non_det_sat_pa:
  "\<lbrakk> mmu_translate va s = (pa, s'); tlb_rel_sat (typ_det_tlb s) (typ_sat_tlb t)  ; consistent (typ_sat_tlb t) va;
         mmu_translate va t = (pa', t')  \<rbrakk> \<Longrightarrow> pa = pa'"
  using mmu_translate_det_sat_refine by fastforce

lemma mmu_translate_sat_incon_mem_excp:
  "\<lbrakk> mmu_translate va s = (p, s') ; mmu_translate va t = (p', t') ;
     va \<notin> set_tlb t; tlb_rel_abs (typ_sat_tlb s) (typ_set_tlb t)\<rbrakk>  \<Longrightarrow> MEM s' = MEM t' \<and> exception s' = exception t'"
  apply (subgoal_tac "tlb_rel_abs (typ_sat_tlb s') (typ_set_tlb t')")
   apply (clarsimp simp: tlb_rel_abs_def state.defs)
  by (drule (2)  mmu_translate_sat_incon_refine; clarsimp simp: Let_def)

lemma mmu_translate_non_det_det_mem_excp:
  "\<lbrakk> mmu_translate va s = (p, s') ; mmu_translate va t = (p', t') ;
     consistent (typ_det_tlb t) va; tlb_rel_det (typ_non_det_tlb s) (typ_det_tlb t)\<rbrakk>  \<Longrightarrow> MEM s' = MEM t' \<and> exception s' = exception t'"
  apply (subgoal_tac "tlb_rel_det (typ_non_det_tlb s') (typ_det_tlb t')")
   apply (clarsimp simp: tlb_rel_det_def state.defs)
  apply (drule (2)  mmu_translate_non_det_det_refine, clarsimp simp: Let_def)
  done


lemma  mmu_translate_non_det_det_pa:
  "\<lbrakk> mmu_translate va s = (pa, s'); tlb_rel_det (typ_non_det_tlb s) (typ_det_tlb t)  ; consistent (typ_det_tlb t) va;
         mmu_translate va t = (pa', t')  \<rbrakk> \<Longrightarrow> pa = pa'"
  using mmu_translate_non_det_det_refine by fastforce

lemma mmu_translate_non_det_det_excp:
  "\<lbrakk> mmu_translate va s = (p, s') ; mmu_translate va t = (p, t') ;
     consistent (typ_det_tlb t) va; tlb_rel_det (typ_non_det_tlb s) (typ_det_tlb t)\<rbrakk>  \<Longrightarrow>  exception s' = exception t'"
  apply (subgoal_tac "tlb_rel_det (typ_non_det_tlb s') (typ_det_tlb t')")
   apply (clarsimp simp: tlb_rel_det_def state.defs)
  apply (drule (2)  mmu_translate_non_det_det_refine, clarsimp simp: Let_def)
 done

end