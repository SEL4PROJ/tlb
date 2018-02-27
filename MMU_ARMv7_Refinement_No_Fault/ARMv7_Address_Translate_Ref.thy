theory ARMv7_Address_Translate_Ref

imports  ARMv7_TLB_Ref_Func

begin               



instantiation tlb_state_ext :: (type) mmu   
begin
  definition   
  "(mmu_translate v :: ('a tlb_state_scheme \<Rightarrow> _))
  = do {
  update_state (\<lambda>s. s\<lparr> tlb_set := tlb_set s - tlb_evict (typ_tlb s) \<rparr>);
     mem   <- read_state MEM;
     asid  <- read_state ASID;
     ttbr0 <- read_state TTBR0;
     tlb   <- read_state tlb_set;
          case lookup tlb asid v of
            Hit entry \<Rightarrow> return (va_to_pa v  entry)
          | Miss \<Rightarrow> let entry = pt_walk asid mem ttbr0 v in
              if is_fault entry
                then raise'exception (PAGE_FAULT ''more info'')
                  else do {
                    update_state (\<lambda>s. s\<lparr> tlb_set := tlb \<union> {the entry} \<rparr>);
                    return (va_to_pa v (the entry))
                  }
          | Incon \<Rightarrow> raise'exception (IMPLEMENTATION_DEFINED ''set on fire'')
   }"

thm mmu_translate_tlb_state_ext_def
(* print_context *)                      
  instance ..
end


instantiation tlb_det_state_ext :: (type) mmu    
begin
definition   
 "(mmu_translate v :: ('a tlb_det_state_scheme \<Rightarrow> _))
  = do {
     mem   <- read_state MEM;
     asid  <- read_state ASID;
     ttbr0 <- read_state TTBR0;
     tlb   <- read_state tlb_det_set;
          case lookup tlb asid v of
            Hit entry \<Rightarrow> return (va_to_pa v entry)
          | Miss \<Rightarrow> let entry = pt_walk asid mem ttbr0 v in
              if is_fault entry
                then raise'exception (PAGE_FAULT ''more info'')
                  else do {
                    update_state (\<lambda>s. s\<lparr> tlb_det_set := tlb \<union> {the entry} \<rparr>);
                    return (va_to_pa v (the entry))
                  }
          | Incon \<Rightarrow> raise'exception (IMPLEMENTATION_DEFINED ''set on fire'')
   }"

  instance ..
end



instantiation tlb_sat_state_ext :: (type) mmu    
begin
definition   
 "(mmu_translate v :: ('a tlb_sat_state_scheme \<Rightarrow> _))
 = do {
     mem   <- read_state MEM;
     asid  <- read_state ASID;
     ttbr0 <- read_state TTBR0;
     let all_non_fault_entries = the ` {e\<in>pt_walk asid mem ttbr0 ` UNIV. \<not>is_fault e};
     tlb0   <- read_state tlb_sat_set;
     let tlb = tlb0 \<union> all_non_fault_entries; 
     update_state (\<lambda>s. s\<lparr> tlb_sat_set := tlb \<rparr>);
          case lookup tlb asid v of
            Hit entry \<Rightarrow> return (va_to_pa v entry)
          | Miss \<Rightarrow> raise'exception (PAGE_FAULT ''more info'')
          | Incon \<Rightarrow> raise'exception (IMPLEMENTATION_DEFINED ''set on fire'')
   }" 
   
  instance ..
end





instantiation tlb_incon_state_ext :: (type) mmu    
begin
definition   
 "(mmu_translate v :: ('a tlb_incon_state_scheme \<Rightarrow> _))
  = do {
     mem   <- read_state MEM;
     asid  <- read_state ASID;
     ttbr0 <- read_state TTBR0;
     tlb_incon_set <- read_state tlb_incon_set;
     if  v \<in> iset tlb_incon_set
       then raise'exception (IMPLEMENTATION_DEFINED ''set on fire'')
       else let entry = pt_walk asid mem ttbr0 v in 
             if is_fault entry
              then raise'exception (PAGE_FAULT ''more info'')
              else return (va_to_pa v (the entry))
    }"

  instance ..
end



lemma lookup_miss_tlb_subset1:
  "\<lbrakk>lookup (tlb_det_set s) (ASID s) va = Miss ; 
    \<not>is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) va) ;
     mmu_translate va s = (pa, s') \<rbrakk> \<Longrightarrow> 
              tlb_det_set s' = tlb_det_set s \<union> {the (pt_walk (ASID s) (MEM s) (TTBR0 s) va)} "
  by (clarsimp simp add: mmu_translate_tlb_det_state_ext_def Let_def)
  

lemma  lookup_miss_tlb_subset2:
  "\<lbrakk>lookup (tlb_det_set s) (ASID s) va = Miss ; is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) va) ;
     mmu_translate va s = (pa, s') \<rbrakk> \<Longrightarrow> 
              tlb_det_set s' = tlb_det_set s "
  apply (clarsimp simp add: mmu_translate_tlb_det_state_ext_def Let_def)
  apply (clarsimp simp:raise'exception_def split: if_split_asm)
done
  
lemma lookup_miss_tlb_subset:
  "\<lbrakk>lookup (tlb_det_set s) (ASID s) va = Miss ; mmu_translate va s = (pa, s')\<rbrakk> \<Longrightarrow> 
           tlb_det_set s' = tlb_det_set s  \<or> tlb_det_set s' = tlb_det_set s \<union> {the (pt_walk (ASID s) (MEM s) (TTBR0 s) va)} "
  apply (cases "is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) va)" )
   apply (drule (2) lookup_miss_tlb_subset2 , clarsimp)
  apply (drule (2) lookup_miss_tlb_subset1 , clarsimp)
done 

lemma lookup_incon_tlb_equal:
  "\<lbrakk>lookup (tlb_det_set s) (ASID s) va = Incon ; mmu_translate va s = (pa, s')  \<rbrakk> \<Longrightarrow> 
        tlb_det_set s' = tlb_det_set s"
  by (clarsimp simp add: mmu_translate_tlb_det_state_ext_def Let_def raise'exception_def split:if_split_asm)
 

lemma lookup_hit_tlb_equal:
  "\<lbrakk>lookup (tlb_det_set s) (ASID s) va = Hit x ; mmu_translate va s = (pa, s') \<rbrakk> \<Longrightarrow>  tlb_det_set s' = tlb_det_set s "
  by (clarsimp simp add: mmu_translate_tlb_det_state_ext_def Let_def raise'exception_def split:if_split_asm)

(* important *)
lemma mmu_translate_tlbs_rel:
  "\<lbrakk> mmu_translate va s = (pa, s') \<rbrakk> \<Longrightarrow>
       tlb_det_set s' = tlb_det_set s \<or>  tlb_det_set s' = tlb_det_set s \<union> 
        {the (pt_walk (ASID s) (MEM s) (TTBR0 s) va)} "
  apply (cases "lookup (tlb_det_set s) (ASID s) va")
    apply (drule (2)lookup_miss_tlb_subset)
   apply (rule disjI1)
   apply (drule (2) lookup_incon_tlb_equal)
  apply (rule disjI1)
  apply (drule (2) lookup_hit_tlb_equal)
done  


lemma mmu_det_rel:
  "\<lbrakk> mmu_translate va s = (p, s') \<rbrakk>  \<Longrightarrow> 
    s' = s \<lparr> tlb_det_set := tlb_det_set s' , exception:= exception s' \<rparr>"
  apply (clarsimp simp: mmu_translate_tlb_det_state_ext_def Let_def  split:lookup_type.splits)
    apply (clarsimp simp: raise'exception_def split:if_split_asm)+
done


lemma mmu_rel:
  "\<lbrakk> mmu_translate va s = (p, s') \<rbrakk>  \<Longrightarrow> s' = s \<lparr> tlb_set := tlb_set s' , exception:= exception s' \<rparr>"
  apply (clarsimp simp: mmu_translate_tlb_state_ext_def Let_def  split:lookup_type.splits)
    apply (clarsimp simp: raise'exception_def split:if_split_asm)+
done


lemma mmu_det_eq_ASID_TTBR0_MEM:
  "\<lbrakk> mmu_translate va (s::'a tlb_det_state_scheme) = (pa , s') \<rbrakk>  \<Longrightarrow> 
      ASID s = ASID s' \<and> TTBR0 s = TTBR0 s' \<and>
                      MEM s = MEM s'"
   apply (clarsimp simp: mmu_translate_tlb_det_state_ext_def Let_def)
   apply (cases "lookup (tlb_det_set s) (ASID s) va")
   by (clarsimp simp:Let_def raise'exception_def split: if_split_asm)+
  


lemma mmu_eq_ASID_TTBR0_MEM:
  "\<lbrakk> mmu_translate va (s::'a tlb_state_scheme) = (pa , s') \<rbrakk>  \<Longrightarrow> 
     ASID s = ASID s' \<and> TTBR0 s = TTBR0 s' \<and>
                      MEM s = MEM s'"
   apply (clarsimp simp: mmu_translate_tlb_state_ext_def Let_def)
   apply (cases "lookup (tlb_set s - tlb_evict (typ_tlb s)) (ASID s) va ")
   by (clarsimp simp:Let_def raise'exception_def split: if_split_asm)+
  

(* add the mmu_translate refinements here *)

lemma consistent_insert' [simp, intro!]:
  "\<lbrakk> lookup tlb asid va = Miss ; pt_walk asid m ttbr va \<noteq> None \<rbrakk> \<Longrightarrow>
  consistent0 m asid ttbr (insert (the(pt_walk asid m ttbr va)) tlb) va"
     by (simp add: )


lemma  mmu_translate_det_refine:
  "\<lbrakk> mmu_translate va s = (pa, s'); consistent (typ_det_tlb t) va;  tlb_rel (typ_det_tlb s) (typ_det_tlb t)\<rbrakk> \<Longrightarrow>
     let (pa', t') = mmu_translate va t
         in pa' = pa \<and> consistent (typ_det_tlb t') va \<and> tlb_rel (typ_det_tlb s') (typ_det_tlb t')"
  apply (frule (1) tlb_rel_consistent , clarsimp)
  apply (frule tlb_relD , clarsimp)
  apply (subgoal_tac "lookup (tlb_det_set s) (ASID s) va \<le> lookup (tlb_det_set t) (ASID s) va")
   prefer 2
   apply (simp add: tlb_mono)
  apply (clarsimp simp: mmu_translate_tlb_det_state_ext_def split_def Let_def split: if_split_asm)
  apply (cases "lookup (tlb_det_set t) (ASID s) va")
    apply clarsimp
    apply (simp add: Let_def raise'exception_def typ_det_tlb_def state.defs tlb_rel_def split: if_split_asm)
     apply (cases s, cases t, clarsimp)
    apply (clarsimp simp: is_fault_def)
    apply (drule_tac  asid = "ASID s" and ttbr0 = "TTBR0 s" and m = "MEM s" and tlb = "tlb_det_set t" in
                       consistent_insert'; clarsimp)
    apply (cases s, cases t, force)
   apply (simp add: consistent0_def )
  apply clarsimp
  apply (cases "lookup (tlb_det_set s) (ASID s) va"; clarsimp)
   apply (simp add: consistent0_def Let_def tlb_rel_def is_fault_def
                    lookup_in_tlb split: if_split_asm)
   apply clarsimp
   apply (drule lookup_in_tlb)
   by (simp add: typ_det_tlb_def state.defs)



(* refinement between eviction and deterministic TLB lookups *)
lemma  mmu_translate_non_det_det_refine:
  "\<lbrakk> mmu_translate va s = (pa, s');  consistent (typ_det_tlb t) va; tlb_rel (typ_tlb s) (typ_det_tlb t)  \<rbrakk> \<Longrightarrow>
    let (pa', t') = mmu_translate va t
     in pa' = pa  \<and> consistent (typ_det_tlb t') va \<and> tlb_rel (typ_tlb s') (typ_det_tlb t')"
  apply (frule (1) tlb_rel_consistent , clarsimp)
  apply (frule tlb_relD , clarsimp)
  apply (subgoal_tac "tlb_set s - tlb_evict (typ_tlb s) \<subseteq> tlb_set s")
   prefer 2
   apply blast
  apply (subgoal_tac "lookup (tlb_set s - tlb_evict (typ_tlb s)) (ASID s) va \<le> lookup (tlb_det_set t) (ASID s) va")
   prefer 2
   apply (simp add: tlb_mono)
  apply (clarsimp simp: mmu_translate_tlb_state_ext_def mmu_translate_tlb_det_state_ext_def split_def Let_def split: if_split_asm)
  apply (cases "lookup (tlb_det_set t) (ASID s) va")
    apply clarsimp
    apply (simp add: Let_def raise'exception_def typ_det_tlb_def typ_tlb_def state.defs tlb_rel_def split: if_split_asm)
      apply (cases s, cases t, clarsimp simp: is_fault_def)
      apply fastforce
     apply (cases s, cases t ,clarsimp simp: is_fault_def)
     apply fastforce
    apply (clarsimp simp: is_fault_def)
    apply (drule_tac  asid = "ASID s" and ttbr0 = "TTBR0 s" and m = "MEM s" and tlb = "tlb_det_set t" in
      consistent_insert'; clarsimp)
    apply (cases s, cases t, force)
   apply (simp add: consistent0_def )
  apply clarsimp
  apply (cases "lookup (tlb_set s - tlb_evict (typ_tlb s)) (ASID s) va"; clarsimp)
   apply (simp add: consistent0_def Let_def tlb_rel_def is_fault_def
      lookup_in_tlb split: if_split_asm)
   apply clarsimp
   apply (drule lookup_in_tlb)
   apply (simp add: typ_det_tlb_def state.defs)
  apply (clarsimp split: if_split_asm simp: tlb_rel_def typ_tlb_def typ_det_tlb_def state.defs is_fault_def)
  using lookup_in_tlb by blast


lemma mmu_translate_det_sat_refine:
  "\<lbrakk> mmu_translate va s = (pa, s'); consistent (typ_sat_tlb t) va; tlb_rel_sat (typ_det_tlb s) (typ_sat_tlb t)  \<rbrakk> \<Longrightarrow>
         let (pa', t') = mmu_translate va t
         in pa' = pa \<and> consistent (typ_sat_tlb t') va \<and> tlb_rel_sat (typ_det_tlb s') (typ_sat_tlb t')"
  apply (frule (1) tlb_rel_sat_consistent , clarsimp)
  apply (frule tlb_rel_satD , clarsimp)
  apply (subgoal_tac "lookup (tlb_det_set s) (ASID s) va \<le> lookup (tlb_sat_set t \<union> the ` {e\<in>pt_walk (ASID s) (MEM s) (TTBR0 s) ` UNIV. \<not>is_fault e}) (ASID s) va")
   prefer 2
   apply (simp add: saturated_def sup.absorb1 tlb_mono tlb_rel_sat_def)
  apply (clarsimp simp: mmu_translate_tlb_det_state_ext_def  mmu_translate_tlb_sat_state_ext_def split_def Let_def)
  apply (subgoal_tac "tlb_sat_set t = tlb_sat_set t \<union> the ` {e\<in>pt_walk (ASID s) (MEM s) (TTBR0 s) ` UNIV. \<not>is_fault e}")
   prefer 2
   apply (fastforce simp: tlb_rel_sat_def saturated_def)
  apply (cases "lookup (tlb_sat_set t \<union> the ` {e\<in>pt_walk (ASID s) (MEM s) (TTBR0 s) ` UNIV. \<not>is_fault e}) (ASID s) va")
    apply (clarsimp simp: tlb_rel_sat_def Let_def)
    apply (subgoal_tac "is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) va)")
     apply (clarsimp simp: raise'exception_def saturated_def state.defs  is_fault_def  split: if_split_asm)
    apply (clarsimp simp: lookup_def entry_set_def entry_range_asid_tags_def is_fault_def  split: if_split_asm)
    apply (subgoal_tac "the ( pt_walk (ASID s) (MEM s) (TTBR0 s) va) \<in> tlb_sat_set t") 
     apply (drule_tac x = "the (pt_walk (ASID s) (MEM s) (TTBR0 s) va)" in spec)
     apply (drule_tac x = "the (pt_walk (ASID s) (MEM s) (TTBR0 s) va)" in spec)
     apply clarsimp 
     apply (subgoal_tac "asid_entry y = ASID s")
      apply (clarsimp simp: image_def)
  using asid_entry_range apply fastforce
  using asid_entry_pt_walk apply fastforce
    apply blast
    (*    apply (clarsimp simp: is_fault_def split: if_split_asm) 
     apply blast  
    apply (subgoal_tac "y \<in> the ` {e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<exists>y. e = Some y}")
     apply blast
    apply (clarsimp simp: image_iff) 
    apply (rule_tac x = "pt_walk (ASID s) (MEM s) (TTBR0 s) va " in exI, rule, rule_tac x = va in exI, simp, rule, simp, simp) *)
   apply (clarsimp simp: consistent0_def)
  apply clarsimp
  apply (subgoal_tac "x3 = the (pt_walk (ASID s) (MEM s) (TTBR0 s) va)")
   prefer 2
   apply (clarsimp simp: consistent0_def)
  apply (cases "lookup (tlb_det_set s) (ASID s) va"; clarsimp)
  apply (clarsimp simp: Let_def)
  apply (subgoal_tac "\<not>is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) va)")
   apply (clarsimp simp: tlb_rel_sat_def typ_sat_tlb_def typ_det_tlb_def state.defs lookup_in_tlb raise'exception_def split: if_split_asm)
  by (clarsimp simp: tlb_rel_sat_def is_fault_def lookup_in_tlb consistent0_def)





lemma mmu_translate_sat_refine:
  "\<lbrakk> mmu_translate va s = (pa, s'); consistent (typ_sat_tlb t) va; tlb_rel_sat (typ_tlb s) (typ_sat_tlb t)  \<rbrakk> \<Longrightarrow>
         let (pa', t') = mmu_translate va t
         in pa' = pa \<and> consistent (typ_sat_tlb t') va \<and> tlb_rel_sat (typ_tlb s') (typ_sat_tlb t')"
  apply (frule (1) tlb_rel_sat_consistent , clarsimp)
  apply (frule tlb_rel_satD , clarsimp)
  apply (subgoal_tac "tlb_set s - tlb_evict (typ_tlb s) \<subseteq> tlb_set s")
   prefer 2
   apply blast
  apply (subgoal_tac "lookup (tlb_set s - tlb_evict (typ_tlb s)) (ASID s) va \<le> lookup (tlb_sat_set t \<union> the ` {e\<in>pt_walk (ASID s) (MEM s) (TTBR0 s) ` UNIV. \<not>is_fault e}) (ASID s) va")
   prefer 2
   apply (simp add: saturated_def sup.absorb1 tlb_mono tlb_rel_sat_def)
  apply (clarsimp simp: mmu_translate_tlb_state_ext_def  mmu_translate_tlb_sat_state_ext_def split_def Let_def)
  apply (subgoal_tac "tlb_sat_set t = tlb_sat_set t \<union>  the ` {e\<in>pt_walk (ASID s) (MEM s) (TTBR0 s) ` UNIV. \<not>is_fault e}")
   prefer 2
   apply (force simp: tlb_rel_sat_def saturated_def)
  apply (cases "lookup (tlb_sat_set t \<union> the ` {e\<in>pt_walk (ASID s) (MEM s) (TTBR0 s) ` UNIV. \<not>is_fault e}) (ASID s) va")
    apply (clarsimp simp: tlb_rel_sat_def Let_def)
    apply (subgoal_tac "is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) va)")
     apply (clarsimp simp: raise'exception_def  saturated_def state.defs split: if_split_asm ; force)
    apply (clarsimp simp: lookup_def entry_set_def entry_range_asid_tags_def is_fault_def split: if_split_asm)
    apply (subgoal_tac "the ( pt_walk (ASID s) (MEM s) (TTBR0 s) va) \<in> tlb_sat_set t") 
     apply (drule_tac x = "the (pt_walk (ASID s) (MEM s) (TTBR0 s) va)" in spec)
     apply (drule_tac x = "the (pt_walk (ASID s) (MEM s) (TTBR0 s) va)" in spec)
     apply clarsimp 
     apply (subgoal_tac "asid_entry y = ASID s")
      apply (clarsimp simp: image_def)
  using asid_entry_range apply fastforce
  using asid_entry_pt_walk apply fastforce
    apply blast
    (*  apply (clarsimp simp:  split: if_split_asm) 
     apply blast  
    apply (subgoal_tac "y \<in> the ` {e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<exists>y. e = Some y}")
     apply blast
    apply (clarsimp simp: image_iff) 
    apply (rule_tac x = "pt_walk (ASID s) (MEM s) (TTBR0 s) va " in exI, rule, rule_tac x = va in exI, simp, rule, simp, simp) *)
   apply (clarsimp simp: consistent0_def)
  apply clarsimp
  apply (subgoal_tac "x3 = the (pt_walk (ASID s) (MEM s) (TTBR0 s) va)")
   prefer 2
   apply (clarsimp simp: consistent0_def)
  apply (cases " lookup (tlb_set s - tlb_evict (typ_tlb s)) (ASID s) va"; clarsimp)
   apply (clarsimp simp: Let_def)
   apply (subgoal_tac "\<not>is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) va)")
    prefer 2
    apply (clarsimp simp: tlb_rel_sat_def is_fault_def lookup_in_tlb consistent0_def) 
   apply (clarsimp simp: tlb_rel_sat_def typ_sat_tlb_def typ_tlb_def is_fault_def state.defs lookup_in_tlb raise'exception_def split: if_split_asm , force)
  apply (subgoal_tac "\<not>is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) va)")
   apply (clarsimp simp:  tlb_rel_sat_def  typ_tlb_def state.defs , force)
  apply (clarsimp simp: tlb_rel_sat_def is_fault_def lookup_in_tlb consistent0_def) 
  done



(* have refinement between flt and incon *)


lemma mmu_translate_sa_consistent':
  "\<lbrakk> mmu_translate va s = (pa, s');  consistent (typ_sat_tlb s) va ; saturated (typ_sat_tlb s)\<rbrakk>  \<Longrightarrow>  
                   consistent (typ_sat_tlb s') va"
  apply (subgoal_tac "tlb_sat_set s = tlb_sat_set s \<union> the `  {e\<in>pt_walk (ASID s) (MEM s) (TTBR0 s) ` UNIV. \<not>is_fault e}")
   prefer 2
   apply (fastforce simp: saturated_def)
  apply (clarsimp simp: mmu_translate_tlb_sat_state_ext_def Let_def  split:lookup_type.splits)
    apply (clarsimp simp: raise'exception_def split:if_split_asm)+
done


lemma mmu_sat_rel':
  "\<lbrakk> mmu_translate va s = (p, s') \<rbrakk>  \<Longrightarrow> s' = s \<lparr> tlb_sat_set := tlb_sat_set s' , exception:= exception s' \<rparr>"
  apply (clarsimp simp: mmu_translate_tlb_sat_state_ext_def Let_def  split:lookup_type.splits)
    apply (clarsimp simp: raise'exception_def split:if_split_asm)+
done



lemma mmu_translate_sat_TLB_union':
  "mmu_translate v s = (p,t) \<Longrightarrow> 
      tlb_sat_set t = tlb_sat_set s \<union> the ` {e\<in>pt_walk (ASID s) (MEM s) (TTBR0 s) ` UNIV. \<not>is_fault e}"
  apply (clarsimp simp:  mmu_translate_tlb_sat_state_ext_def Let_def)
  apply (cases "lookup (tlb_sat_set s \<union> the ` {e\<in>pt_walk (ASID s) (MEM s) (TTBR0 s) ` UNIV. \<not>is_fault e}) (ASID s) v")
    apply (clarsimp simp:raise'exception_def split:if_split_asm) +
done


lemma mmu_sat_eq_ASID_TTBR0_MEM:
  "\<lbrakk> mmu_translate va (s::'a tlb_sat_state_scheme) = (pa , s') \<rbrakk>  \<Longrightarrow> ASID s = ASID s' \<and> TTBR0 s = TTBR0 s' \<and>
                     MEM s = MEM s'"
  apply (clarsimp simp: mmu_translate_tlb_sat_state_ext_def Let_def)
  apply (cases "lookup (tlb_sat_set s \<union> the ` {e\<in>pt_walk (ASID s) (MEM s) (TTBR0 s) ` UNIV. \<not>is_fault e}) (ASID s) va ")
    by (clarsimp simp:raise'exception_def split: if_split_asm)+



lemma tlb_snapshot_sat_same  [simp]:
  "\<lbrakk> mmu_translate va s = (pa, s');  saturated  (typ_sat_tlb s) \<rbrakk> \<Longrightarrow> 
                  snapshot_of_tlb (tlb_sat_set s') =  snapshot_of_tlb (tlb_sat_set s)"
  apply (subgoal_tac "tlb_sat_set s' = tlb_sat_set s")
    apply (clarsimp simp: snapshot_of_tlb_def)
   using mmu_translate_sat_TLB_union' sat_state_tlb' by fastforce
  


(* refinement between two abstracted levels  *)


 
lemma mmu_translate_abs_rel'2:
  "\<lbrakk>  mmu_translate va t = (pa', t')\<rbrakk>  \<Longrightarrow> (t'::'a tlb_incon_state_scheme) = t\<lparr>exception := exception t'\<rparr>"
  by (clarsimp simp: mmu_translate_tlb_incon_state_ext_def Let_def raise'exception_def split: if_split_asm)




(* refinement between saturated and second abstracted model *)


theorem entry_range_single_element':
  " {E \<in> the ` {e \<in> t. \<not> is_fault e}. (a, v) \<in> entry_range_asid_tags E} = {x} \<Longrightarrow> 
       (a, v) \<in> entry_range_asid_tags x \<and> \<not> is_fault (Some x) 
         \<and> (\<forall>y\<in>the ` {e \<in> t. \<not> is_fault e}. y\<noteq>x \<and> 
               \<not> is_fault (Some y) \<longrightarrow> (a, v) \<notin> entry_range_asid_tags y)" 
  apply safe
    apply force
   apply (clarsimp simp: is_fault_def)
  by force


theorem entry_range_single_elementI':
  "\<lbrakk>x\<in> the ` {e \<in> range (pt_walk asid mem ttbr0). \<not> is_fault e} ; \<not> is_fault (Some x) ; (a, v) \<in> entry_range_asid_tags x ; 
    (\<forall>y\<in>the ` {e \<in> range (pt_walk asid mem ttbr0). \<not> is_fault e}. y\<noteq>x \<longrightarrow> (a, v) \<notin> entry_range_asid_tags y) \<rbrakk> \<Longrightarrow> 
           {E \<in> the ` {e \<in> range (pt_walk asid mem ttbr0). \<not> is_fault e}. (a, v) \<in> entry_range_asid_tags E} = {x}" 
   by force



lemma asid_va_entry_range_pt_entry:
  "\<not>is_fault(pt_walk  asid mem ttbr0 va) \<Longrightarrow> 
      (asid, va) \<in> entry_range_asid_tags (the(pt_walk asid mem ttbr0 va))"
  by (clarsimp simp: entry_range_asid_tags_def is_fault_def)
 




lemma va_offset_add:
  " (va::32 word) : {ucast (ucast ((x:: 32 word) >> 12):: 20 word) << 12  .. 
    (ucast (ucast (x >> 12):: 20 word) << 12) + mask 12 } \<Longrightarrow>
      \<exists>a.  (0 \<le> a \<and> a \<le> mask 12) \<and>
  va = (ucast (ucast ((x:: 32 word) >> 12):: 20 word) << 12)  + a"
  apply (rule_tac x = "va - (ucast (ucast ((x:: 32 word) >> 12):: 20 word) << 12) " in exI)
  apply (clarsimp simp: mask_def)
  apply uint_arith
done
  

lemma va_offset_add_1:
  " (va::32 word) : {ucast (ucast ((x:: 32 word) >> 20):: 12 word) << 20  .. 
    (ucast (ucast (x >> 20):: 12 word) << 20) + mask 20 } \<Longrightarrow>
      \<exists>a.  (0 \<le> a \<and> a \<le> mask 20) \<and>
      va = (ucast (ucast ((x:: 32 word) >> 20):: 12 word) << 20)  + a"
  apply (rule_tac x = "va - (ucast (ucast ((x:: 32 word) >> 20):: 12 word) << 20) " in exI)
  apply (clarsimp simp: mask_def)
  apply uint_arith
done

lemma shift_to_mask:
  "x AND NOT mask 12 = (ucast (ucast ((x::32 word) >> 12):: 20 word)::32 word) << 12"
  apply (rule word_eqI)
  apply (simp add : word_ops_nth_size word_size)
  apply (simp add : nth_shiftr nth_shiftl nth_ucast)
  apply auto
done


lemma shift_to_mask_1:
  "x AND NOT mask 20 = (ucast (ucast ((x::32 word) >> 20):: 12 word)::32 word) << 20"
  apply (rule word_eqI)
  apply (simp add : word_ops_nth_size word_size)
  apply (simp add : nth_shiftr nth_shiftl nth_ucast)
  apply auto
done




lemma nth_bits_false:
  "\<lbrakk>(n::nat) < 20; (a::32 word) \<le> 0xFFF\<rbrakk> \<Longrightarrow> \<not>(a !! (n + 12))"
  apply word_bitwise
  apply clarsimp
  apply (case_tac "n = 0")
   apply clarsimp
  apply (case_tac "n = 1")
   apply clarsimp
  apply (case_tac "n = 2")
   apply clarsimp
  apply (case_tac "n = 3")
   apply clarsimp
  apply (case_tac "n = 4")
   apply clarsimp
  apply (case_tac "n = 5")
   apply clarsimp
  apply (case_tac "n = 6")
   apply clarsimp
  apply (case_tac "n = 7")
   apply clarsimp
  apply (case_tac "n = 8")
   apply clarsimp
  apply (case_tac "n = 9")
   apply clarsimp
  apply (case_tac "n = 10")
   apply clarsimp
  apply (case_tac "n = 11")
   apply clarsimp
  apply (case_tac "n = 12")
   apply clarsimp
  apply (case_tac "n = 13")
   apply clarsimp
  apply (case_tac "n = 14")
   apply clarsimp
  apply (case_tac "n = 15")
   apply clarsimp
  apply (case_tac "n = 16")
   apply clarsimp
  apply (case_tac "n = 17")
   apply clarsimp
  apply (case_tac "n = 18")
   apply clarsimp
  apply (case_tac "n = 19")
   apply clarsimp
  apply (thin_tac "\<not> a !! P" for P)+
  apply arith
done



lemma nth_bits_false_1:
  "\<lbrakk>(n::nat) < 12; (a::32 word) \<le> 0xFFFFF\<rbrakk> \<Longrightarrow> \<not>(a !! (n + 20))"
  apply word_bitwise
  apply clarsimp
  apply (case_tac "n = 0")
   apply clarsimp
  apply (case_tac "n = 1")
   apply clarsimp
  apply (case_tac "n = 2")
   apply clarsimp
  apply (case_tac "n = 3")
   apply clarsimp
  apply (case_tac "n = 4")
   apply clarsimp
  apply (case_tac "n = 5")
   apply clarsimp
  apply (case_tac "n = 6")
   apply clarsimp
  apply (case_tac "n = 7")
   apply clarsimp
  apply (case_tac "n = 8")
   apply clarsimp
  apply (case_tac "n = 9")
   apply clarsimp
  apply (case_tac "n = 10")
   apply clarsimp
  apply (case_tac "n = 11")
   apply clarsimp
  apply (thin_tac "\<not> a !! P" for P)+
  apply arith
done



lemma nth_bits_offset_equal: "\<lbrakk>n < 20 ; (a::32 word) \<le> 0x00000FFF \<rbrakk> \<Longrightarrow> 
        (((x::32 word) && 0xFFFFF000) || a) !!  (n + 12) = x !! (n + 12)"
  apply clarsimp
  apply (rule iffI)
   apply (erule disjE)
    apply clarsimp
   apply (clarsimp simp: nth_bits_false)
  apply clarsimp
  apply (simp only: test_bit_int_def [symmetric])
  apply (case_tac "n = 0")
   apply clarsimp
  apply (case_tac "n = 1")
   apply clarsimp
  apply (case_tac "n = 2")
   apply clarsimp
  apply (case_tac "n = 3")
   apply clarsimp
  apply (case_tac "n = 4")
   apply clarsimp
  apply (case_tac "n = 5")
   apply clarsimp
  apply (case_tac "n = 6")
   apply clarsimp
  apply (case_tac "n = 7")
   apply clarsimp
  apply (case_tac "n = 8")
   apply clarsimp
  apply (case_tac "n = 9")
   apply clarsimp
  apply (case_tac "n = 10")
   apply clarsimp
  apply (case_tac "n = 11")
   apply clarsimp
  apply (case_tac "n = 12")
   apply clarsimp
  apply (case_tac "n = 13")
   apply clarsimp
  apply (case_tac "n = 14")
   apply clarsimp
  apply (case_tac "n = 15")
   apply clarsimp
  apply (case_tac "n = 16")
   apply clarsimp
  apply (case_tac "n = 17")
   apply clarsimp
  apply (case_tac "n = 18")
   apply clarsimp
  apply (case_tac "n = 19")
   apply clarsimp
  by presburger

   


lemma nth_bits_offset_equal_1: "\<lbrakk>n < 12 ; (a::32 word) \<le> 0x000FFFFF \<rbrakk> \<Longrightarrow> 
        (((x::32 word) && 0xFFF00000) || a) !!  (n + 20) = x !! (n + 20)"
  apply clarsimp
  apply (rule iffI)
   apply (erule disjE)
    apply clarsimp
   apply (clarsimp simp: nth_bits_false_1)
  apply clarsimp
  apply (simp only: test_bit_int_def [symmetric])
  apply (case_tac "n = 0")
   apply clarsimp
  apply (case_tac "n = 1")
   apply clarsimp
  apply (case_tac "n = 2")
   apply clarsimp
  apply (case_tac "n = 3")
   apply clarsimp
  apply (case_tac "n = 4")
   apply clarsimp
  apply (case_tac "n = 5")
   apply clarsimp
  apply (case_tac "n = 6")
   apply clarsimp
  apply (case_tac "n = 7")
   apply clarsimp
  apply (case_tac "n = 8")
   apply clarsimp
  apply (case_tac "n = 9")
   apply clarsimp
  apply (case_tac "n = 10")
   apply clarsimp
  apply (case_tac "n = 11")
   apply clarsimp
  by presburger

   
lemma add_to_or:
  "(a::32 word) \<le> 0xFFF \<Longrightarrow>
     ((x::32 word) && 0xFFFFF000) + a =  (x && 0xFFFFF000) || a"
  apply word_bitwise
  apply clarsimp
  using xor3_simps carry_simps apply auto
 done


lemma add_to_or_1:
  "(a::32 word) \<le> 0xFFFFF \<Longrightarrow>
     ((x::32 word) && 0xFFF00000) + a =  (x && 0xFFF00000) || a"
  apply word_bitwise
  apply clarsimp
  using xor3_simps carry_simps apply auto
done


lemma va_offset_higher_bits: 
   " \<lbrakk>ucast (ucast ((x:: 32 word) >> 12):: 20 word) << 12 \<le> va ; 
      va \<le> (ucast (ucast (x >> 12):: 20 word) << 12) + 0x00000FFF \<rbrakk> \<Longrightarrow>
        (ucast (x >> 12)::20 word) = (ucast ((va:: 32 word) >> 12)::20 word)"
  apply (subgoal_tac "(va::32 word) : {ucast (ucast ((x:: 32 word) >> 12):: 20 word) << 12  ..
   (ucast (ucast (x >> 12):: 20 word) << 12) + mask 12 }")
   prefer 2
   apply (clarsimp simp: mask_def)
  apply (frule va_offset_add)
  apply simp
  apply (erule exE)
  apply (erule conjE)
  apply (simp add: mask_def)
  apply (subgoal_tac "(ucast ((((ucast (ucast ((x:: 32 word) >> 12):: 20 word) << 12)::32 word)  + a) >> 12):: 20 word) =
                       (ucast (((ucast (ucast ((x:: 32 word) >> 12):: 20 word) << 12)::32 word)   >> 12):: 20 word) ")
   apply clarsimp
   apply (word_bitwise) [1]
  apply (subgoal_tac "ucast ((ucast (ucast ((x::32 word) >> 12):: 20 word)::32 word) << 12 >> 12) =
                      (ucast (x >> 12) :: 20 word)")
   prefer 2
   apply (word_bitwise) [1]
  apply simp
  apply (clarsimp simp: shift_to_mask [symmetric])
  apply (rule word_eqI)
  apply (simp only: nth_ucast)
  apply clarsimp
  apply (subgoal_tac "n < 20")
   prefer 2
   apply word_bitwise [1]
  apply clarsimp
  apply (clarsimp simp: nth_shiftr)
  apply (clarsimp simp: mask_def)
  apply (frule_tac a = a in nth_bits_offset_equal) apply clarsimp
  apply (drule_tac x= x in add_to_or)
  apply (simp only: )
 done



lemma va_offset_higher_bits_1: 
   " \<lbrakk>ucast (ucast ((x:: 32 word) >> 20):: 12 word) << 20 \<le> va ; 
      va \<le> (ucast (ucast (x >> 20):: 12 word) << 20) + 0x000FFFFF \<rbrakk> \<Longrightarrow>
        (ucast (x >> 20):: 12 word) = (ucast ((va:: 32 word) >> 20)::12 word)"
  apply (subgoal_tac "(va::32 word) : {ucast (ucast ((x:: 32 word) >> 20):: 12 word) << 20 ..
                      (ucast (ucast (x >> 20):: 12 word) << 20) + mask 20 }")
   prefer 2
   apply (clarsimp simp: mask_def)
  apply (frule va_offset_add_1)
  apply simp
  apply (erule exE)
  apply (erule conjE)
  apply (simp add: mask_def)
  apply (subgoal_tac "(ucast ((((ucast (ucast ((x:: 32 word) >> 20):: 12 word) << 20)::32 word)  + a) >> 20):: 12 word) =
                      (ucast (((ucast (ucast ((x:: 32 word) >> 20):: 12 word) << 20)::32 word)   >> 20):: 12 word) ")
   apply clarsimp
   apply (word_bitwise) [1]
  apply (subgoal_tac "ucast ((ucast (ucast ((x::32 word) >> 20):: 12 word)::32 word) << 20 >> 20) =
   (ucast (x >> 20) :: 12 word)")
   prefer 2
   apply (word_bitwise) [1]
  apply simp
  apply (clarsimp simp: shift_to_mask_1 [symmetric])
  apply (rule word_eqI)
  apply (simp only: nth_ucast)
  apply clarsimp
  apply (subgoal_tac "n < 12")
   prefer 2
   apply word_bitwise [1]
  apply clarsimp
  apply (clarsimp simp: nth_shiftr)
  apply (clarsimp simp: mask_def)
  apply (frule_tac a = a in nth_bits_offset_equal_1) apply clarsimp
  apply (drule_tac x= x in add_to_or_1)
  apply (simp only: )
 done




lemma nth_bits_offset: "\<lbrakk> n \<in> {12..31} ; (a::32 word) \<le> 0x00000FFF \<rbrakk> \<Longrightarrow> 
        (x::32 word) !! n = (x && 0xFFFFF000 || a) !! n"
  apply (rule iffI)
   apply (case_tac "n = 12")
    apply clarsimp
   apply (case_tac "n = 13")
    apply clarsimp
   apply (case_tac "n = 14")
    apply clarsimp
   apply (case_tac "n = 15")
    apply clarsimp
   apply (case_tac "n = 16")
    apply clarsimp
   apply (case_tac "n = 17")
    apply clarsimp
   apply (case_tac "n = 18")
    apply clarsimp
   apply (case_tac "n = 19")
    apply clarsimp
   apply (case_tac "n = 20")
    apply clarsimp
   apply (case_tac "n = 21")
    apply clarsimp
   apply (case_tac "n = 22")
    apply clarsimp
   apply (case_tac "n = 23")
    apply clarsimp
   apply (case_tac "n = 24")
    apply clarsimp
   apply (case_tac "n = 25")
    apply clarsimp
   apply (case_tac "n = 26")
    apply clarsimp
   apply (case_tac "n = 27")
    apply clarsimp
   apply (case_tac "n = 28")
    apply clarsimp
   apply (case_tac "n = 29")
    apply clarsimp
   apply (case_tac "n = 30")
    apply clarsimp
   apply (case_tac "n = 31")
    apply clarsimp
   prefer 2
   apply (case_tac "n = 12")
    apply word_bitwise [1] apply clarsimp
   apply (case_tac "n = 13")
    apply word_bitwise [1] apply clarsimp
   apply (case_tac "n = 14")
    apply word_bitwise [1]  apply clarsimp
   apply (case_tac "n = 15")
    apply word_bitwise [1]  apply clarsimp
   apply (case_tac "n = 16")
    apply word_bitwise [1] apply clarsimp
   apply (case_tac "n = 17")
    apply word_bitwise [1] apply clarsimp
   apply (case_tac "n = 18")
    apply word_bitwise [1] apply clarsimp
   apply (case_tac "n = 19")
    apply word_bitwise [1] apply clarsimp
   apply (case_tac "n = 20")
    apply word_bitwise [1] apply clarsimp
   apply (case_tac "n = 21")
    apply word_bitwise [1] apply clarsimp
   apply (case_tac "n = 22")
    apply word_bitwise [1] apply clarsimp
   apply (case_tac "n = 23")
    apply word_bitwise [1] apply clarsimp
   apply (case_tac "n = 24")
    apply word_bitwise [1] apply clarsimp
   apply (case_tac "n = 25")
    apply word_bitwise [1] apply clarsimp
   apply (case_tac "n = 26")
    apply word_bitwise [1]  apply clarsimp
   apply (case_tac "n = 27")
    apply word_bitwise [1] apply clarsimp
   apply (case_tac "n = 28")
    apply word_bitwise [1] apply clarsimp
   apply (case_tac "n = 29")
    apply word_bitwise [1] apply clarsimp
   apply (case_tac "n = 30")
    apply word_bitwise [1] apply clarsimp
   apply (case_tac "n = 31")
    apply word_bitwise [1] apply clarsimp
   apply clarsimp
   apply arith
  apply clarsimp
  apply arith
done




lemma n_bit_shift:
  "\<lbrakk> \<forall>n::nat. n \<in> {12 .. 31} \<longrightarrow>(a::32 word) !! n = (b::32 word) !! n  \<rbrakk>  \<Longrightarrow>  a >> 12 = b >> 12"
  apply word_bitwise
  by auto
 


lemma n_bit_shift_1:
  "\<lbrakk> \<forall>n::nat. n \<in> {12 .. 31} \<longrightarrow>(a::32 word) !! n = (b::32 word) !! n  \<rbrakk>  \<Longrightarrow>  a >> 20 = b >> 20"
  apply word_bitwise
  by auto


lemma n_bit_shift_2:
  "\<lbrakk> \<forall>n::nat. n \<in> {20 .. 31} \<longrightarrow>(a::32 word) !! n = (b::32 word) !! n  \<rbrakk>  \<Longrightarrow>  a >> 20 = b >> 20"
  apply word_bitwise
  by auto
 

lemma offset_mask_eq:
 "\<lbrakk>ucast (ucast ((x:: 32 word) >> 12):: 20 word) << 12 \<le> va ; 
      va \<le> (ucast (ucast (x >> 12):: 20 word) << 12) + 0x00000FFF\<rbrakk>
          \<Longrightarrow> (( x >> 12) && mask 8 << 2) = 
         ((va >> 12) && mask 8 << 2)"
  apply (subgoal_tac "(va::32 word) : {ucast (ucast ((x:: 32 word) >> 12):: 20 word) << 12  ..
                      (ucast (ucast (x >> 12):: 20 word) << 12) + mask 12 }")
   prefer 2
   apply (clarsimp simp: mask_def)
  apply (frule va_offset_add)
  apply simp
  apply (erule exE)
  apply (erule conjE)
  apply (simp add: mask_def)
  apply (rule_tac f = "(\<lambda>x. x && 0xFF << 2)" in  arg_cong)
  apply (clarsimp simp: shift_to_mask [symmetric])
  apply (simp add: mask_def)
  apply (rule n_bit_shift)
  apply (rule allI)
  apply (rule impI)
  apply (frule_tac x= x in add_to_or)
  apply (frule_tac x= x in nth_bits_offset)
   apply (simp only:)+
done
 



lemma offset_mask_eq_1:
  "\<lbrakk>ucast (ucast ((x:: 32 word) >> 12):: 20 word) << 12 \<le> va ; 
      va \<le> (ucast (ucast (x >> 12):: 20 word) << 12) + 0x00000FFF\<rbrakk>
          \<Longrightarrow>((x >> 20) && mask 12 << 2) =
                          ((va >> 20) && mask 12 << 2)"
  apply (subgoal_tac "(va::32 word) : {ucast (ucast ((x:: 32 word) >> 12):: 20 word) << 12  ..
   (ucast (ucast (x >> 12):: 20 word) << 12) + mask 12 }")
   prefer 2
   apply (clarsimp simp: mask_def)
  apply (frule va_offset_add)
  apply simp
  apply (erule exE)
  apply (erule conjE)
  apply (simp add: mask_def)
  apply (rule_tac f = "(\<lambda>x. x && 0xFFF << 2)" in  arg_cong)
  apply (clarsimp simp: shift_to_mask [symmetric])
  apply (simp add: mask_def)
  apply (rule n_bit_shift_1)
  apply (rule allI)
  apply (rule impI)
  apply (frule_tac x= x in add_to_or)
  apply (frule_tac x= x in nth_bits_offset)
   apply (simp only:)+
done

lemma nth_bits_offset_1: "\<lbrakk> n \<in> {20..31} ; (a::32 word) \<le> 0x000FFFFF \<rbrakk> \<Longrightarrow> 
        (x::32 word) !! n = (x && 0xFFF00000 || a) !! n"
  apply (rule iffI)
   apply (case_tac "n = 20")
    apply clarsimp
   apply (case_tac "n = 21")
    apply clarsimp
   apply (case_tac "n = 22")
    apply clarsimp
   apply (case_tac "n = 23")
    apply clarsimp
   apply (case_tac "n = 24")
    apply clarsimp
   apply (case_tac "n = 25")
    apply clarsimp
   apply (case_tac "n = 26")
    apply clarsimp
   apply (case_tac "n = 27")
    apply clarsimp
   apply (case_tac "n = 28")
    apply clarsimp
   apply (case_tac "n = 29")
    apply clarsimp
   apply (case_tac "n = 30")
    apply clarsimp
   apply (case_tac "n = 31")
    apply clarsimp
   prefer 2
   apply (case_tac "n = 20")
    apply word_bitwise [1] apply clarsimp
   apply (case_tac "n = 21")
    apply word_bitwise [1] apply clarsimp
   apply (case_tac "n = 22")
    apply word_bitwise [1] apply clarsimp
   apply (case_tac "n = 23")
    apply word_bitwise [1] apply clarsimp
   apply (case_tac "n = 24")
    apply word_bitwise [1] apply clarsimp
   apply (case_tac "n = 25")
    apply word_bitwise [1] apply clarsimp
   apply (case_tac "n = 26")
    apply word_bitwise [1]  apply clarsimp
   apply (case_tac "n = 27")
    apply word_bitwise [1] apply clarsimp
   apply (case_tac "n = 28")
    apply word_bitwise [1] apply clarsimp
   apply (case_tac "n = 29")
    apply word_bitwise [1] apply clarsimp
   apply (case_tac "n = 30")
    apply word_bitwise [1] apply clarsimp
   apply (case_tac "n = 31")
    apply word_bitwise [1] apply clarsimp
   apply clarsimp
   apply arith
  apply clarsimp
  apply arith
done



lemma  shfit_mask_eq:
  "\<lbrakk>ucast (ucast ((x:: 32 word) >> 20):: 12 word) << 20 \<le> va ; 
      va \<le> (ucast (ucast (x >> 20):: 12 word) << 20) + 0x000FFFFF \<rbrakk>
    \<Longrightarrow>   ((x >> 20) && mask 12 << 2) = ((va >> 20) && mask 12 << 2)"
  apply (subgoal_tac "(va::32 word) : {ucast (ucast ((x:: 32 word) >> 20):: 12 word) << 20 ..
   (ucast (ucast (x >> 20):: 12 word) << 20) + mask 20 }")
   prefer 2
   apply (clarsimp simp: mask_def)
  apply (frule va_offset_add_1)
  apply simp
  apply (erule exE)
  apply (erule conjE)
  apply (simp add: mask_def)
  apply (rule_tac f = "(\<lambda>x. x && 0xFFF << 2)" in  arg_cong)
  apply (clarsimp simp: shift_to_mask_1 [symmetric])
  apply (simp add: mask_def)
  apply (rule n_bit_shift_2)
  apply (rule allI)
  apply (rule impI)
  apply (frule_tac x= x in add_to_or_1)
  apply (frule_tac x= x and a = a in nth_bits_offset_1)
   apply (simp only:)+
done



lemma  va_entry_set_pt_palk_same:
  "\<lbrakk>\<not>is_fault (pt_walk asid mem ttbr0 x) ;
           (asid, va) \<in> entry_range_asid_tags (the (pt_walk asid mem ttbr0 x))\<rbrakk> \<Longrightarrow>
              the(pt_walk asid mem ttbr0 x) = the(pt_walk asid mem ttbr0 va)"
  apply (subgoal_tac "(asid, x) \<in> entry_range_asid_tags (the(pt_walk asid mem ttbr0 x))")
   prefer 2
   apply (clarsimp simp: asid_va_entry_range_pt_entry)
  apply (cases "the (pt_walk asid mem ttbr0 x)")
   apply (clarsimp simp: entry_range_asid_tags_def entry_range_def pt_walk_def is_fault_def)
   apply (cases "get_pde mem ttbr0 x" ; clarsimp)
   apply (case_tac a ; clarsimp)
   apply (case_tac "get_pte mem x3 x " ; clarsimp)
   apply (subgoal_tac "get_pde mem ttbr0 (Addr xaa) = get_pde mem ttbr0  (Addr xa)" ; clarsimp)
    apply (subgoal_tac "get_pte mem x3 (Addr xaa) = get_pte mem x3  (Addr xa)" ; clarsimp)
     apply (case_tac a ; clarsimp)
  using va_offset_higher_bits apply blast
    apply (case_tac a ; clarsimp)
    apply (clarsimp simp:  get_pte_def vaddr_pt_index_def)
    apply (subgoal_tac "(( xaa >> 12) && mask 8 << 2) =
                          (( xa >> 12) && mask 8 << 2) ")
     prefer 2
  using offset_mask_eq apply blast
    apply force
   apply (case_tac a ; clarsimp)
   apply (clarsimp simp: get_pde_def vaddr_pd_index_def)
   apply (subgoal_tac "((xaa >> 20) && mask 12 << 2) =
                         ((xa >> 20) && mask 12 << 2) ")
    prefer 2
  using offset_mask_eq_1 apply blast
   apply force
  apply (clarsimp simp: entry_range_asid_tags_def entry_range_def pt_walk_def is_fault_def)
  apply (cases "get_pde mem ttbr0 x" ; clarsimp)
  apply (case_tac a ; clarsimp)
   apply (case_tac "get_pte mem x3 x" ; clarsimp)
   apply (subgoal_tac "get_pde mem ttbr0 (Addr xaa) = get_pde mem ttbr0 (Addr xa)" ; clarsimp)
    apply (subgoal_tac "get_pte mem x3 (Addr xaa) = get_pte mem x3 (Addr xa)" ; clarsimp)
     apply (case_tac a ; clarsimp)
    apply (case_tac a ; clarsimp simp: get_pte_def vaddr_pt_index_def)
   apply (case_tac a ; clarsimp simp: get_pde_def vaddr_pd_index_def)
  apply (cases "get_pde mem ttbr0 x" ; clarsimp)
  apply (subgoal_tac "get_pde mem ttbr0 (Addr xaa) = get_pde mem ttbr0 (Addr xa)" ; clarsimp)
  using va_offset_higher_bits_1 apply blast
  apply (clarsimp simp: get_pde_def vaddr_pd_index_def)
  apply (subgoal_tac "((xaa >> 20) && mask 12 << 2) = ((xa >> 20) && mask 12 << 2)")
   apply force
  using shfit_mask_eq by blast


lemma lookup_range_pt_walk_hit:
  "\<not> is_fault (pt_walk asid mem ttbr0  va) \<Longrightarrow> 
        lookup (the ` {e \<in> range (pt_walk asid mem ttbr0). \<not> is_fault e}) asid va = Hit (the (pt_walk asid mem ttbr0  va)) "
  apply (clarsimp simp: lookup_def)
  apply safe
    apply simp
   apply (subgoal_tac "x = the (pt_walk asid mem ttbr0 va)" , force)
   apply (clarsimp simp: entry_set_def)
   apply (drule entry_range_single_element')
   apply safe
   apply (unfold Ball_def) [1]
   apply (erule_tac x = "the (pt_walk asid mem ttbr0  va)" in allE)
   apply (clarsimp simp: asid_va_entry_range_pt_entry is_fault_def)
  apply (rule_tac x = "the (pt_walk asid mem ttbr0 va)" in exI)
  apply (clarsimp simp: entry_set_def)
  apply (rule entry_range_single_elementI')
     apply force
    apply (clarsimp simp: asid_va_entry_range_pt_entry is_fault_def)
   apply (clarsimp simp: asid_va_entry_range_pt_entry)
  apply safe
  apply (drule_tac x = xa in va_entry_set_pt_palk_same , simp)
  by (clarsimp simp: is_fault_def)


lemma lookup_hit_miss_or_hit' :
  " lookup (t1 \<union> t2) a va = Hit x  \<Longrightarrow> 
              lookup t2 a va = Miss \<or> (lookup t2 a va = Hit x)"
  apply (clarsimp simp: lookup_def entry_set_def split: if_split_asm)
  by force+


lemma lookup_range_fault_pt_walk:
  "\<lbrakk>lookup (the ` {e \<in> range (pt_walk a m r). \<not> is_fault e}) a v = Hit x\<rbrakk>  \<Longrightarrow> 
          \<forall>va\<in> entry_range x. x = the (pt_walk a m r va)"
  apply (subgoal_tac "x \<in> the ` {e \<in> range (pt_walk a m r). \<not> is_fault e}")
   prefer 2
   using  lookup_in_tlb apply force
  apply clarsimp
  apply (rule va_entry_set_pt_palk_same, simp)
  by (clarsimp simp: entry_range_asid_tags_def)


lemma  lookup_hit_entry_range:
  "lookup t a va = Hit x \<Longrightarrow> va \<in> entry_range x"
  apply (clarsimp simp: lookup_def  entry_set_def entry_range_asid_tags_def  split:if_split_asm)
  by force


lemma saturatd_lookup_hit_no_fault:
  "\<lbrakk>saturated (typ_sat_tlb s);
          lookup (tlb_sat_set s) (ASID s) b = Hit x; \<not> is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) b)\<rbrakk>
                \<Longrightarrow> x = the (pt_walk (ASID s) (MEM s) (TTBR0 s) b)"
  apply (subgoal_tac "lookup (tlb_sat_set s \<union> 
                              the ` {e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e}) (ASID s) (  b) = Hit x")
   prefer 2
   apply (drule sat_state_tlb', clarsimp simp: state.defs)
  apply (drule lookup_hit_miss_or_hit')
  apply (erule disjE)
   apply (clarsimp simp: lookup_range_pt_walk_hit)
  apply (frule lookup_range_fault_pt_walk)
  apply (drule_tac x = "  b" in bspec; clarsimp simp: lookup_hit_entry_range)
  done




lemma not_member_incon2_consistent':
  "\<lbrakk>va \<notin>  incon_addrs (typ_sat_tlb s) ; saturated (typ_sat_tlb s) \<rbrakk> \<Longrightarrow> 
                                       consistent (typ_sat_tlb s) va"
  apply (clarsimp simp: incon_addrs_def incon_va_set_def ptable_tlb_va_incon_def consistent0_def)
  apply (erule disjE)
   apply (meson lookup_type.exhaust)
  apply clarsimp
  apply (subgoal_tac "\<exists>x\<in>tlb_sat_set s.  lookup (tlb_sat_set s) (ASID s) va = Hit x")
   prefer 2
   apply (meson lookup_def lookup_in_tlb)
  by (clarsimp simp: saturatd_lookup_hit_no_fault)
  

lemma tlb_rel_abs2_consistent' [simp]:
  "\<lbrakk>va \<notin> iset (tlb_incon_set t) ;   tlb_rel_abs  (typ_sat_tlb s) (typ_incon t)  \<rbrakk>  \<Longrightarrow> 
           consistent (typ_sat_tlb s) va " 
  apply (rule not_member_incon2_consistent' ; clarsimp simp: tlb_rel_abs_def) 
  by blast
  

lemma mmu_translate_sat_abs2_refine_pa':
  "\<lbrakk> mmu_translate va s = (pa, s');  mmu_translate va t = (pa', t') ;
           va \<notin> iset (tlb_incon_set t) ; tlb_rel_abs  (typ_sat_tlb s) (typ_incon t) \<rbrakk> \<Longrightarrow> 
                                          pa = pa'"
 apply (frule_tac s = s in tlb_rel_abs2_consistent' ; clarsimp )
  apply (frule tlb_rel_absD , clarsimp)
  apply (clarsimp simp: mmu_translate_tlb_incon_state_ext_def  Let_def)
  apply (clarsimp simp: mmu_translate_tlb_sat_state_ext_def split_def Let_def)
  apply (cases "lookup (tlb_sat_set s \<union> the ` {e\<in>pt_walk (ASID s) (MEM s) (TTBR0 s) ` UNIV. \<not>is_fault e}) (ASID s) va")
    apply clarsimp
    apply (frule lookup_saturated_miss_is_fault)
    apply (clarsimp simp: raise'exception_def is_fault_def split:if_split_asm)
   apply (subgoal_tac "tlb_sat_set s = tlb_sat_set s \<union> the ` {e\<in>pt_walk (ASID s) (MEM s) (TTBR0 s) ` UNIV. \<not>is_fault e}")
    prefer 2
    apply (fastforce simp: saturated_def)
   apply clarsimp
   apply (clarsimp simp: consistent0_def)
  apply clarsimp
  apply (subgoal_tac "x3 = the (pt_walk (ASID s) (MEM s) (TTBR0 s) va)")
   prefer 2
   apply (subgoal_tac "tlb_sat_set s = tlb_sat_set s \<union> the ` {e\<in>pt_walk (ASID s) (MEM s) (TTBR0 s) ` UNIV. \<not>is_fault e}")
    prefer 2
    apply (fastforce simp: saturated_def)
   apply (clarsimp simp: consistent0_def)
  apply clarsimp
  apply (subgoal_tac "\<not>is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) va)")
   prefer 2
   apply (subgoal_tac "tlb_sat_set s = tlb_sat_set s \<union> the ` {e\<in>pt_walk (ASID s) (MEM s) (TTBR0 s) ` UNIV. \<not>is_fault e}")
    prefer 2
    apply (fastforce simp: saturated_def)
   apply clarsimp
   apply (clarsimp simp: is_fault_def lookup_in_tlb consistent0_def)
  apply clarsimp
 done


lemma mmu_translate_sat_abs2_refine':
   "\<lbrakk> mmu_translate va s = (pa, s');  mmu_translate va t = (pa', t') ;
           va \<notin> iset (tlb_incon_set t) ;  tlb_rel_abs (typ_sat_tlb s) (typ_incon t) \<rbrakk> \<Longrightarrow> 
             tlb_rel_abs (typ_sat_tlb s') (typ_incon t')"
 apply (frule_tac s = s in tlb_rel_abs2_consistent' ; clarsimp )
  apply (frule tlb_rel_absD , clarsimp)
  apply (frule_tac mmu_translate_sa_consistent' ; clarsimp simp: tlb_rel_abs_def incon_addrs_def incon_va_set_def ptable_tlb_va_incon_def)
    (* TLB is not changing as s is already saturated *)
  apply (subgoal_tac "s' = s\<lparr>exception := exception s'\<rparr> \<and> t' = t\<lparr>exception := exception t'\<rparr>")
   apply (subgoal_tac "exception t' = exception s'")
    apply (cases t, cases t, cases s, cases s', clarsimp simp: state.defs saturated_def)
   prefer 2
   apply (frule mmu_translate_abs_rel'2, clarsimp)
   apply (subgoal_tac "tlb_sat_set s' = tlb_sat_set s")
    apply (drule mmu_sat_rel', clarsimp)
  using mmu_translate_sat_TLB_union' sat_state_tlb' apply fastforce
  apply (subgoal_tac "tlb_sat_set s' = tlb_sat_set s \<union> the ` {e\<in>pt_walk (ASID s) (MEM s) (TTBR0 s) ` UNIV. \<not>is_fault e} \<and> ASID s' = ASID s  \<and> 
                                              MEM s' = MEM s \<and> TTBR0 s' = TTBR0 s")
   apply (clarsimp simp: mmu_translate_tlb_sat_state_ext_def split_def Let_def)
   apply (cases "lookup (tlb_sat_set s \<union> the ` {e\<in>pt_walk (ASID s) (MEM s) (TTBR0 s) ` UNIV. \<not>is_fault e}) (ASID s) va")
     apply clarsimp
     apply (frule lookup_saturated_miss_is_fault)
     apply (clarsimp simp: mmu_translate_tlb_incon_state_ext_def raise'exception_def is_fault_def split:if_split_asm)
    apply (clarsimp simp: consistent0_def)
   apply clarsimp
   apply (subgoal_tac "x3 = the (pt_walk (ASID s) (MEM s) (TTBR0 s) va)")
    prefer 2
    apply (clarsimp simp: consistent0_def)
   apply clarsimp
   apply (subgoal_tac "\<not>is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) va)")
    prefer 2
    apply (subgoal_tac "tlb_sat_set s = tlb_sat_set s \<union> the ` {e\<in>pt_walk (ASID s) (MEM s) (TTBR0 s) ` UNIV. \<not>is_fault e}")
     prefer 2
     apply (fastforce simp: saturated_def)
    apply clarsimp
    apply (clarsimp simp: consistent0_def is_fault_def lookup_in_tlb)
   apply (clarsimp simp: mmu_translate_tlb_incon_state_ext_def Let_def is_fault_def)
  apply (clarsimp simp: mmu_translate_sat_TLB_union' mmu_sat_eq_ASID_TTBR0_MEM is_fault_def) 
done



lemma mmu_translate_sat_abs_refine2_consistency:
   "\<lbrakk> mmu_translate va s = (pa, s');  mmu_translate va t = (pa', t') ;
           va \<notin> iset (tlb_incon_set t) ; tlb_rel_abs (typ_sat_tlb s) (typ_incon t) \<rbrakk> \<Longrightarrow> 
                                  va \<notin> iset (tlb_incon_set t')"
 apply (frule_tac s = s in tlb_rel_abs2_consistent' ; clarsimp )
  apply (frule tlb_rel_absD , clarsimp)
  apply (clarsimp simp: mmu_translate_tlb_incon_state_ext_def  Let_def)
  apply (clarsimp simp: mmu_translate_tlb_sat_state_ext_def split_def Let_def)
  apply (cases "lookup (tlb_sat_set s \<union> the ` {e\<in>pt_walk (ASID s) (MEM s) (TTBR0 s) ` UNIV. \<not>is_fault e}) (ASID s) va")
    apply clarsimp
    apply (frule lookup_saturated_miss_is_fault)
    apply (clarsimp simp: raise'exception_def split:if_split_asm)
   apply (subgoal_tac "tlb_sat_set s = tlb_sat_set s \<union> the ` {e\<in>pt_walk (ASID s) (MEM s) (TTBR0 s) ` UNIV. \<not>is_fault e}")
    prefer 2
    apply (fastforce simp: saturated_def)
   apply clarsimp
   apply (clarsimp simp: consistent0_def)
  apply clarsimp
  apply (subgoal_tac "x3 = the (pt_walk (ASID s) (MEM s) (TTBR0 s) va)")
   prefer 2
   apply (subgoal_tac "tlb_sat_set s = tlb_sat_set s \<union> the ` {e\<in>pt_walk (ASID s) (MEM s) (TTBR0 s) ` UNIV. \<not>is_fault e}")
    prefer 2
    apply (fastforce simp: saturated_def)
   apply (clarsimp simp: consistent0_def)
  apply clarsimp
  apply (subgoal_tac "\<not>is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) va)")
   prefer 2
   apply (subgoal_tac "tlb_sat_set s = tlb_sat_set s \<union> the ` {e\<in>pt_walk (ASID s) (MEM s) (TTBR0 s) ` UNIV. \<not>is_fault e}")
    prefer 2
    apply (fastforce simp: saturated_def)
   apply clarsimp
   apply (clarsimp simp: is_fault_def lookup_in_tlb consistent0_def)
  apply clarsimp
 done


lemma mmu_translate_sat_abs2_refine:
  "\<lbrakk> mmu_translate va s = (pa, s');  mmu_translate va t = (pa', t') ;
           va \<notin> iset (tlb_incon_set t) ; tlb_rel_abs (typ_sat_tlb s) (typ_incon t) \<rbrakk> \<Longrightarrow> 
                              pa = pa' \<and>  tlb_rel_abs  (typ_sat_tlb s') (typ_incon t')  \<and> 
                              va \<notin> iset (tlb_incon_set t')"
  by (clarsimp simp: mmu_translate_sat_abs2_refine_pa' mmu_translate_sat_abs2_refine'
      mmu_translate_sat_abs_refine2_consistency)



end