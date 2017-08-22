theory MMU_ARM_Refine_No_Fault

imports MMU_ARM_No_Fault

begin               





(**************************************************************)



lemma  mmu_translate_det_refine:
  "\<lbrakk> mmu_translate va s = (pa, s'); consistent (typ_det_tlb t) va;  tlb_rel (typ_det_tlb s) (typ_det_tlb t)\<rbrakk> \<Longrightarrow>
     let (pa', t') = mmu_translate va t
         in pa' = pa \<and> consistent (typ_det_tlb t') va \<and> tlb_rel (typ_det_tlb s') (typ_det_tlb t')"
  apply (frule (1) tlb_rel_consistent , clarsimp)
  apply (frule tlb_relD , clarsimp)
  apply (subgoal_tac "lookup (tlb_det_set s) (ASID s) (addr_val va) \<le> lookup (tlb_det_set t) (ASID s) (addr_val va)")
   prefer 2
   apply (simp add: tlb_mono)
  apply (clarsimp simp: mmu_translate_tlb_det_state_ext_def split_def Let_def split: split_if_asm)
  apply (cases "lookup (tlb_det_set t) (ASID s) (addr_val va)")
    apply clarsimp
    apply (simp add: Let_def raise'exception_def typ_det_tlb_def state.defs tlb_rel_def split: split_if_asm)
     apply (cases s, cases t, clarsimp)
    apply (cases s, cases t)
    apply (clarsimp simp: no_faults_def)
    apply fastforce
   apply (simp add: consistent0_def )
  apply clarsimp
  apply (cases "lookup (tlb_det_set s) (ASID s) (addr_val va)"; clarsimp)
   apply (simp add: consistent0_def Let_def tlb_rel_def no_faults_def
                    lookup_in_tlb split: split_if_asm)
   apply clarsimp
   apply (drule lookup_in_tlb)
   apply (simp add: typ_det_tlb_def state.defs)
  apply (clarsimp split: split_if_asm simp: tlb_rel_def no_faults_def)
  using lookup_in_tlb apply blast
done


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
  apply (subgoal_tac "lookup (tlb_set s - tlb_evict (typ_tlb s)) (ASID s) (addr_val va) \<le> lookup (tlb_det_set t) (ASID s) (addr_val va)")
   prefer 2
   apply (simp add: tlb_mono)
  apply (clarsimp simp: mmu_translate_tlb_state_ext_def mmu_translate_tlb_det_state_ext_def split_def Let_def split: split_if_asm)
  apply (cases "lookup (tlb_det_set t) (ASID s) (addr_val va)")
    apply clarsimp
    apply (simp add: Let_def raise'exception_def typ_det_tlb_def typ_tlb_def state.defs tlb_rel_def split: split_if_asm)
      apply (cases s, cases t, clarsimp simp: no_faults_def)
      apply fastforce
     apply (cases s, cases t ,clarsimp simp: no_faults_def)
     apply fastforce
    apply (cases s, cases t, clarsimp simp: no_faults_def)
    apply fastforce
   apply (simp add: consistent0_def )
  apply clarsimp
  apply (cases "lookup (tlb_set s - tlb_evict (typ_tlb s)) (ASID s) (addr_val va)"; clarsimp)
   apply (simp add: consistent0_def Let_def tlb_rel_def no_faults_def
                     lookup_in_tlb split: split_if_asm)
   apply clarsimp
   apply (drule lookup_in_tlb)
   apply (simp add: typ_det_tlb_def state.defs)
  apply (clarsimp split: split_if_asm simp: tlb_rel_def typ_tlb_def typ_det_tlb_def state.defs no_faults_def)
   using lookup_in_tlb apply blast
  using lookup_in_tlb apply blast
done


instantiation tlb_sat_no_flt_state_ext :: (type) mmu    
begin
definition   
 "(mmu_translate v :: ('a tlb_sat_no_flt_state_scheme \<Rightarrow> _))
 = do {
     mem   <- read_state MEM;
     asid  <- read_state ASID;
     ttbr0 <- read_state TTBR0;
     let all_non_fault_entries = {e\<in>pt_walk asid mem ttbr0 ` UNIV. \<not>is_fault e};
     tlb0   <- read_state tlb_sat_no_flt_set;
     let tlb = tlb0 \<union> all_non_fault_entries;  (* there can be fault entries in the tlb0, and of there are , they should not be 
                                                  in the all non fault entries *)
     update_state (\<lambda>s. s\<lparr> tlb_sat_no_flt_set := tlb \<rparr>);
          case lookup tlb asid (addr_val v) of
            Hit entry \<Rightarrow> if is_fault entry 
              then raise'exception (PAGE_FAULT ''more info'')    (* it can be possible because there can be a fault entry in the tlb0 already *)
                else return (Addr (va_to_pa (addr_val v) entry))
          | Miss \<Rightarrow> raise'exception (PAGE_FAULT ''more info'')
          | Incon \<Rightarrow> raise'exception (IMPLEMENTATION_DEFINED ''set on fire'')
   }" 
   
  instance ..
end

thm  mmu_translate_tlb_sat_no_flt_state_ext_def

lemma mmu_translate_det_sat_no_flt_refine:
  "\<lbrakk> mmu_translate va s = (pa, s'); consistent (typ_sat_no_flt_tlb t) va; tlb_rel_sat_no_flt (typ_det_tlb s) (typ_sat_no_flt_tlb t)  \<rbrakk> \<Longrightarrow>
         let (pa', t') = mmu_translate va t
         in pa' = pa \<and> consistent (typ_sat_no_flt_tlb t') va \<and> tlb_rel_sat_no_flt (typ_det_tlb s') (typ_sat_no_flt_tlb t')"
  apply (frule (1) tlb_rel_sat_no_flt_consistent , clarsimp)
  apply (frule tlb_rel_no_flt_satD , clarsimp)
  apply (subgoal_tac "lookup (tlb_det_set s) (ASID s) (addr_val va) \<le> lookup (tlb_sat_no_flt_set t \<union> {e\<in>pt_walk (ASID s) (MEM s) (TTBR0 s) ` UNIV. \<not> is_fault e}) (ASID s) (addr_val va)")
   prefer 2
   apply (simp add: saturated_no_flt_def sup.absorb1 tlb_mono tlb_rel_sat_no_flt_def)
  apply (clarsimp simp: mmu_translate_tlb_det_state_ext_def  mmu_translate_tlb_sat_no_flt_state_ext_def split_def Let_def)
  apply (subgoal_tac "tlb_sat_no_flt_set t = tlb_sat_no_flt_set t \<union> {e\<in>pt_walk (ASID s) (MEM s) (TTBR0 s) ` UNIV. \<not> is_fault e}")
   prefer 2
   apply (fastforce simp: tlb_rel_sat_no_flt_def saturated_no_flt_def)
  apply (cases "lookup (tlb_sat_no_flt_set t \<union> {e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e}) (ASID s) (addr_val va)")
    apply (clarsimp simp: tlb_rel_sat_no_flt_def Let_def)
    apply (subgoal_tac "is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) va)")
     apply (clarsimp simp: raise'exception_def  saturated_no_flt_def state.defs split: split_if_asm)
    apply (clarsimp simp: lookup_def entry_set_def entry_range_asid_tags_def split: split_if_asm)
    apply force
   apply (clarsimp simp: consistent0_def)
  apply clarsimp
  apply (subgoal_tac "x3 = pt_walk (ASID s) (MEM s) (TTBR0 s) va")
   prefer 2
   apply (clarsimp simp: consistent0_def)
  apply (cases "lookup (tlb_det_set s) (ASID s) (addr_val va)"; clarsimp)
   apply (clarsimp simp: Let_def)
   apply (subgoal_tac "\<not>is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) va)")
    prefer 2
    apply (clarsimp simp: tlb_rel_sat_no_flt_def no_faults_def lookup_in_tlb)
   apply (clarsimp simp: tlb_rel_sat_no_flt_def typ_sat_no_flt_tlb_def typ_det_tlb_def state.defs lookup_in_tlb raise'exception_def split: split_if_asm)
  apply (subgoal_tac "\<not>is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) va)")
   apply clarsimp
  apply (clarsimp simp: tlb_rel_sat_no_flt_def no_faults_def lookup_in_tlb)
done




lemma mmu_translate_sat_no_flt_refine:
  "\<lbrakk> mmu_translate va s = (pa, s'); consistent (typ_sat_no_flt_tlb t) va; tlb_rel_sat_no_flt (typ_tlb s) (typ_sat_no_flt_tlb t)  \<rbrakk> \<Longrightarrow>
         let (pa', t') = mmu_translate va t
         in pa' = pa \<and> consistent (typ_sat_no_flt_tlb t') va \<and> tlb_rel_sat_no_flt (typ_tlb s') (typ_sat_no_flt_tlb t')"
  apply (frule (1) tlb_rel_sat_no_flt_consistent , clarsimp)
  apply (frule tlb_rel_no_flt_satD , clarsimp)
  apply (subgoal_tac "tlb_set s - tlb_evict (typ_tlb s) \<subseteq> tlb_set s")
   prefer 2
   apply blast
  apply (subgoal_tac "lookup (tlb_set s - tlb_evict (typ_tlb s)) (ASID s) (addr_val va) \<le> lookup (tlb_sat_no_flt_set t \<union> {e\<in>pt_walk (ASID s) (MEM s) (TTBR0 s) ` UNIV. \<not> is_fault e}) (ASID s) (addr_val va)")
   prefer 2
   apply (simp add: saturated_no_flt_def sup.absorb1 tlb_mono tlb_rel_sat_no_flt_def)
  apply (clarsimp simp: mmu_translate_tlb_state_ext_def  mmu_translate_tlb_sat_no_flt_state_ext_def split_def Let_def)
  apply (subgoal_tac "tlb_sat_no_flt_set t = tlb_sat_no_flt_set t \<union> {e\<in>pt_walk (ASID s) (MEM s) (TTBR0 s) ` UNIV. \<not> is_fault e}")
   prefer 2
   apply (fastforce simp: tlb_rel_sat_no_flt_def saturated_no_flt_def)
  apply (cases "lookup (tlb_sat_no_flt_set t \<union> {e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e}) (ASID s) (addr_val va)")
    apply (clarsimp simp: tlb_rel_sat_no_flt_def Let_def)
    apply (subgoal_tac "is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) va)")
     apply (clarsimp simp: raise'exception_def  saturated_no_flt_def state.defs split: split_if_asm ; force)
    apply (clarsimp simp: lookup_def entry_set_def entry_range_asid_tags_def split: split_if_asm)
    apply force
   apply (clarsimp simp: consistent0_def)
  apply clarsimp
  apply (subgoal_tac "x3 = pt_walk (ASID s) (MEM s) (TTBR0 s) va")
   prefer 2
   apply (clarsimp simp: consistent0_def)
  apply (cases " lookup (tlb_set s - tlb_evict (typ_tlb s)) (ASID s) (addr_val va)"; clarsimp)
   apply (clarsimp simp: Let_def)
   apply (subgoal_tac "\<not>is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) va)")
    prefer 2
    apply (clarsimp simp: tlb_rel_sat_no_flt_def no_faults_def lookup_in_tlb)
   apply (clarsimp simp: tlb_rel_sat_no_flt_def typ_sat_no_flt_tlb_def typ_tlb_def state.defs lookup_in_tlb raise'exception_def split: split_if_asm , force)
  apply (subgoal_tac "\<not>is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) va)")
   apply (clarsimp simp:  tlb_rel_sat_no_flt_def typ_sat_tlb_def typ_tlb_def state.defs , force)
  apply (clarsimp simp: tlb_rel_sat_no_flt_def no_faults_def lookup_in_tlb)
done





instantiation tlb_incon_state'_ext :: (type) mmu    
begin
definition   
 "(mmu_translate v :: ('a tlb_incon_state'_scheme \<Rightarrow> _))
  = do {
     mem   <- read_state MEM;
     asid  <- read_state ASID;
     ttbr0 <- read_state TTBR0;
     incon_set <- read_state tlb_incon_set';
     if (asid , addr_val v) \<in> incon_set
       then raise'exception (IMPLEMENTATION_DEFINED ''set on fire'')
       else let entry = pt_walk asid mem ttbr0 v in 
             if is_fault entry
              then raise'exception (PAGE_FAULT ''more info'')
              else return (Addr (va_to_pa (addr_val v) entry))
    }"

  instance ..
end

thm mmu_translate_tlb_incon_state_ext_def



(* have refinement between flt and incon *)


lemma sat_state_tlb':
  "\<lbrakk> saturated_no_flt s \<rbrakk> \<Longrightarrow> 
     state.more s = state.more s \<union> {e\<in>pt_walk (ASID s) (MEM s) (TTBR0 s) ` UNIV. \<not> is_fault e}"
  by (fastforce simp: saturated_no_flt_def)



lemma mmu_translate_sa_consistent':
  "\<lbrakk> mmu_translate va s = (pa, s');  consistent (typ_sat_no_flt_tlb s) va ; saturated_no_flt (typ_sat_no_flt_tlb s) ; 
                no_faults (tlb_sat_no_flt_set s)\<rbrakk>  \<Longrightarrow>  
                   consistent (typ_sat_no_flt_tlb s') va"
  apply (subgoal_tac "tlb_sat_no_flt_set s = tlb_sat_no_flt_set s \<union> {e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e}")
   prefer 2
   apply (fastforce simp: saturated_no_flt_def)
  apply (clarsimp simp: mmu_translate_tlb_sat_no_flt_state_ext_def Let_def  split:lookup_type.splits)
    apply (clarsimp simp: raise'exception_def split:split_if_asm)+
done


lemma mmu_sat_rel':
  "\<lbrakk> mmu_translate va s = (p, s') \<rbrakk>  \<Longrightarrow> s' = s \<lparr> tlb_sat_no_flt_set := tlb_sat_no_flt_set s' , exception:= exception s' \<rparr>"
  apply (clarsimp simp: mmu_translate_tlb_sat_no_flt_state_ext_def Let_def  split:lookup_type.splits)
    apply (clarsimp simp: raise'exception_def split:split_if_asm)+
done


lemma mmu_translate_abs_rel':
  "\<lbrakk>  mmu_translate va t = (pa', t')\<rbrakk>  \<Longrightarrow> (t'::'a tlb_incon_state'_scheme) = t\<lparr>exception := exception t'\<rparr>"
  by (clarsimp simp: mmu_translate_tlb_incon_state'_ext_def Let_def raise'exception_def split: split_if_asm)


lemma mmu_translate_sat_TLB_union':
  "mmu_translate v s = (p,t) \<Longrightarrow> 
      tlb_sat_no_flt_set t = tlb_sat_no_flt_set s \<union> {e\<in>pt_walk (ASID s) (MEM s) (TTBR0 s) ` UNIV. \<not> is_fault e}"
  apply (clarsimp simp:  mmu_translate_tlb_sat_no_flt_state_ext_def Let_def)
  apply (cases "lookup (tlb_sat_no_flt_set s \<union> {e\<in>pt_walk (ASID s) (MEM s) (TTBR0 s) ` UNIV. \<not> is_fault e}) (ASID s) (addr_val v)")
    apply (clarsimp simp:raise'exception_def split:split_if_asm) +
done


lemma mmu_sat_no_flt_eq_ASID_TTBR0_MEM:
  "\<lbrakk> mmu_translate va (s::'a tlb_sat_no_flt_state_scheme) = (pa , s') \<rbrakk>  \<Longrightarrow> ASID s = ASID s' \<and> TTBR0 s = TTBR0 s' \<and>
                     MEM s = MEM s'"
  apply (clarsimp simp: mmu_translate_tlb_sat_no_flt_state_ext_def Let_def)
  apply (cases "lookup (tlb_sat_no_flt_set s \<union> {e\<in>pt_walk (ASID s) (MEM s) (TTBR0 s) ` UNIV. \<not> is_fault e}) (ASID s) (addr_val va) ")
    by (clarsimp simp:raise'exception_def split: split_if_asm)+

thm tlb_rel_abs_def
thm asid_va_incon_def

(* for current state's asid and root only *)

definition                              
   asid_va_hit_incon :: "tlb_entry set state_scheme \<Rightarrow> (asid \<times> va) set"
where                                                         
  "asid_va_hit_incon s  \<equiv>  {(asid, va). asid = ASID s \<and>  
                            (\<exists>x. lookup (state.more s) asid va = Hit x \<and> x \<noteq> pt_walk (ASID s) (MEM s) (TTBR0 s) (Addr va) ) }"

(*  should we here reload for all the assigned asid? ,
    might be not, as we are reloading only for the current asid later *)       

definition                              
   asid_va_incon_tlb_mem :: "tlb_entry set state_scheme \<Rightarrow> (asid \<times> va) set"
where                                                         
  "asid_va_incon_tlb_mem s  \<equiv>  asid_va_incon (state.more s) \<union> asid_va_hit_incon s "
       

      
definition 
  tlb_rel_abs' :: "tlb_entry set state_scheme \<Rightarrow> (asid \<times> va) set state_scheme \<Rightarrow> bool"
where                                                                
  "tlb_rel_abs' s t \<equiv> state.truncate s = state.truncate t \<and>  asid_va_incon_tlb_mem s \<subseteq> state.more t"


lemma tlb_rel'_absD:
  "tlb_rel_abs' s t \<Longrightarrow>
     ASID t = ASID s \<and> MEM t = MEM s \<and> TTBR0 t = TTBR0 s \<and>  asid_va_incon_tlb_mem s  \<subseteq> state.more t \<and> exception t = exception s"
   by (clarsimp simp: tlb_rel_abs'_def state.defs)



thm pt_walk_def
thm lookup_pde_def


lemma not_member_incon_consistent':
  "\<lbrakk>(ASID s , addr_val va) \<notin>  asid_va_incon_tlb_mem (typ_sat_no_flt_tlb s) \<rbrakk> \<Longrightarrow> 
         consistent (typ_sat_no_flt_tlb s) va"
  apply (clarsimp simp: asid_va_incon_tlb_mem_def asid_va_incon_def asid_va_hit_incon_def)
  apply (clarsimp simp: lookup_def consistent0_def split: split_if_asm)
  done


lemma tlb_rel_abs_consistent':
  "\<lbrakk>(ASID t, addr_val va) \<notin> (tlb_incon_set' t) ;   tlb_rel_abs' (typ_sat_no_flt_tlb s) (typ_incon' t) \<rbrakk>  \<Longrightarrow> 
           consistent (typ_sat_no_flt_tlb s) va " 
  apply (rule not_member_incon_consistent' ; clarsimp)
  apply (clarsimp simp: tlb_rel_abs'_def)
  apply (subgoal_tac "ASID s = ASID t" , simp)
   apply blast
  apply (cases s , cases t , clarsimp simp: state.defs)
done


lemma mmu_translate_sat_abs_refine':
  "\<lbrakk> mmu_translate va s = (pa, s');  mmu_translate va t = (pa', t') ;
       saturated_no_flt  (typ_sat_no_flt_tlb s) ; no_faults (tlb_sat_no_flt_set s); 
          (ASID t, addr_val va) \<notin> (tlb_incon_set' t) ; tlb_rel_abs' (typ_sat_no_flt_tlb s) (typ_incon' t) \<rbrakk> \<Longrightarrow> 
            tlb_rel_abs'  (typ_sat_no_flt_tlb s') (typ_incon' t')"
  apply (frule_tac s = s in tlb_rel_abs_consistent' ; clarsimp )
   apply (frule tlb_rel'_absD , clarsimp)
  apply (frule_tac mmu_translate_sa_consistent' ; clarsimp simp: tlb_rel_abs'_def asid_va_incon_tlb_mem_def asid_va_hit_incon_def)
  (* TLB is not changing as s is already saturated *)
  apply (subgoal_tac "s' = s\<lparr>exception := exception s'\<rparr> \<and> t' = t\<lparr>exception := exception t'\<rparr>")
   apply (subgoal_tac "exception t' = exception s'")
    apply (cases t, cases t, cases s, cases s', clarsimp simp: state.defs)
   prefer 2
   apply (frule mmu_translate_abs_rel', clarsimp)
   apply (subgoal_tac "tlb_sat_no_flt_set s' = tlb_sat_no_flt_set s")
    apply (drule mmu_sat_rel', clarsimp)
   using mmu_translate_sat_TLB_union' sat_state_tlb' apply fastforce
  apply (subgoal_tac "tlb_sat_no_flt_set s' = tlb_sat_no_flt_set s \<union> {e\<in>pt_walk (ASID s) (MEM s) (TTBR0 s) ` UNIV. \<not> is_fault e} \<and> ASID s' = ASID s  \<and> 
                                              MEM s' = MEM s \<and> TTBR0 s' = TTBR0 s")
   apply (clarsimp simp: mmu_translate_tlb_sat_no_flt_state_ext_def split_def Let_def)
   apply (cases "lookup (tlb_sat_no_flt_set s \<union> {e\<in>pt_walk (ASID s) (MEM s) (TTBR0 s) ` UNIV. \<not> is_fault e}) (ASID s) (addr_val va)")
     apply clarsimp
     apply (frule lookup_saturated_no_flt_miss_is_fault)
     apply (clarsimp simp: mmu_translate_tlb_incon_state'_ext_def raise'exception_def split:split_if_asm)
    apply (clarsimp simp: consistent0_def)
   apply clarsimp
   apply (subgoal_tac "x3 = pt_walk (ASID s) (MEM s) (TTBR0 s) va")
    prefer 2
    apply (clarsimp simp: consistent0_def)
   apply clarsimp
   apply (subgoal_tac "\<not>is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) va)")
    prefer 2
    apply (subgoal_tac "tlb_sat_no_flt_set s = tlb_sat_no_flt_set s \<union> {e\<in>pt_walk (ASID s) (MEM s) (TTBR0 s) ` UNIV. \<not> is_fault e}")
     prefer 2
     apply (fastforce simp: saturated_no_flt_def)
    apply clarsimp
    apply (simp only: no_faults_def lookup_in_tlb)
   apply clarsimp
  apply (clarsimp simp: mmu_translate_tlb_incon_state'_ext_def Let_def)
  apply (clarsimp simp: mmu_translate_sat_TLB_union' mmu_sat_no_flt_eq_ASID_TTBR0_MEM)
done


lemma mmu_translate_sat_abs_refine_pa':
  "\<lbrakk> mmu_translate va s = (pa, s');  mmu_translate va t = (pa', t') ;
       saturated_no_flt  (typ_sat_no_flt_tlb s) ; no_faults (tlb_sat_no_flt_set s); 
          (ASID t, addr_val va) \<notin> (tlb_incon_set' t) ; tlb_rel_abs' (typ_sat_no_flt_tlb s) (typ_incon' t) \<rbrakk> \<Longrightarrow> 
                                          pa = pa'"
  apply (frule_tac s = s in tlb_rel_abs_consistent' ; clarsimp )
  apply (frule tlb_rel'_absD , clarsimp)
  apply (clarsimp simp: mmu_translate_tlb_incon_state'_ext_def  Let_def)
  apply (clarsimp simp: mmu_translate_tlb_sat_no_flt_state_ext_def split_def Let_def)
  apply (cases "lookup (tlb_sat_no_flt_set s \<union> {e\<in>pt_walk (ASID s) (MEM s) (TTBR0 s) ` UNIV. \<not> is_fault e}) (ASID s) (addr_val va)")
    apply clarsimp
    apply (frule lookup_saturated_no_flt_miss_is_fault)
    apply (clarsimp simp: raise'exception_def split:split_if_asm)
   apply (subgoal_tac "tlb_sat_no_flt_set s = tlb_sat_no_flt_set s \<union> {e\<in>pt_walk (ASID s) (MEM s) (TTBR0 s) ` UNIV. \<not> is_fault e}")
    prefer 2
    apply (fastforce simp: saturated_no_flt_def)
   apply clarsimp
   apply (clarsimp simp: consistent0_def)
  apply clarsimp
  apply (subgoal_tac "x3 = pt_walk (ASID s) (MEM s) (TTBR0 s) va")
   prefer 2
   apply (subgoal_tac "tlb_sat_no_flt_set s = tlb_sat_no_flt_set s \<union> {e\<in>pt_walk (ASID s) (MEM s) (TTBR0 s) ` UNIV. \<not> is_fault e}")
    prefer 2
    apply (fastforce simp: saturated_no_flt_def)
   apply (clarsimp simp: consistent0_def)
  apply clarsimp
  apply (subgoal_tac "\<not>is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) va)")
   prefer 2
   apply (subgoal_tac "tlb_sat_no_flt_set s = tlb_sat_no_flt_set s \<union> {e\<in>pt_walk (ASID s) (MEM s) (TTBR0 s) ` UNIV. \<not> is_fault e}")
    prefer 2
    apply (fastforce simp: saturated_no_flt_def)
   apply clarsimp
   apply (simp only: no_faults_def lookup_in_tlb)
  apply clarsimp
 done




lemma mmu_translate_sat_no_flt_abs_refine:
  "\<lbrakk> mmu_translate va s = (pa, s');  mmu_translate va t = (pa', t') ;
       saturated_no_flt  (typ_sat_no_flt_tlb s) ; no_faults (tlb_sat_no_flt_set s);
          (ASID t, addr_val va) \<notin> (tlb_incon_set' t) ; tlb_rel_abs' (typ_sat_no_flt_tlb s) (typ_incon' t) \<rbrakk> \<Longrightarrow> 
                              pa = pa' \<and> tlb_rel_abs'  (typ_sat_no_flt_tlb s') (typ_incon' t')"
  by (clarsimp simp: mmu_translate_sat_abs_refine_pa' mmu_translate_sat_abs_refine')



instantiation tlb_sat_no_flt_state_ext :: (type) mem_op    
begin

definition   
  "(mmu_read  :: (vaddr  \<Rightarrow>  'a tlb_sat_no_flt_state_scheme \<Rightarrow> bool list \<times>  'a tlb_sat_no_flt_state_scheme))
   \<equiv>  \<lambda>va. do {
                     pa  \<leftarrow> mmu_translate va;
                     mem1 pa
  }"

definition
 "(mmu_read_size  :: (vaddr \<times> nat \<Rightarrow>  'a tlb_sat_no_flt_state_scheme \<Rightarrow> bool list \<times>  'a tlb_sat_no_flt_state_scheme))
  \<equiv> \<lambda>(va,size). do {
                     pa  \<leftarrow> mmu_translate va;
                     mem_read1 (pa , size)
  }"

definition   
  "(mmu_write_size  :: (bool list \<times> vaddr \<times> nat \<Rightarrow> 'a tlb_sat_no_flt_state_scheme \<Rightarrow> unit \<times> 'a tlb_sat_no_flt_state_scheme))
   \<equiv> \<lambda>(value, vaddr, size).  do {
     ttbr0 <- read_state TTBR0;
     asid <- read_state ASID;
     pa <- mmu_translate vaddr;
     tlb0  <- read_state tlb_sat_no_flt_set;
     exception <- read_state exception;
     if exception = NoException 
      then do { 
           write'mem1 (value, pa, size); 
           mem1  <- read_state MEM;
           let all_non_fault_entries = {e\<in>pt_walk asid mem1 ttbr0 ` UNIV. \<not>is_fault e};
           let tlb = tlb0 \<union> all_non_fault_entries;  (* what about inconsistency here ? *)
           update_state (\<lambda>s. s\<lparr> tlb_sat_no_flt_set := tlb \<rparr>)
          } 
      else return () 
    }"
  instance ..
end


thm mmu_translate_det_sat_refine

thm write'mem'det1_sat_refine1

thm mmu_translate_det_sat_no_flt_refine

lemma  mmu_translate_asid_ttbr0 :
  "mmu_translate va (s::tlb_sat_no_flt_state) = (a, b) \<Longrightarrow> ASID s = ASID b \<and> TTBR0 s = TTBR0 b"
 by (clarsimp simp: mmu_translate_tlb_sat_no_flt_state_ext_def Let_def raise'exception_def split:lookup_type.splits split_if_asm) 
 


lemma mmu_translate_sat_sat_no_fault:
  "mmu_translate v s = (p,t) \<Longrightarrow>   saturated_no_flt (typ_sat_no_flt_tlb t)"
  apply (clarsimp simp: mmu_translate_tlb_sat_no_flt_state_ext_def Let_def split: lookup_type.splits)
    by (clarsimp simp: saturated_no_flt_def raise'exception_def split:split_if_asm)+

lemma mmu_translate_sat_sat_no_fault':
  "\<lbrakk> mmu_translate v s = (p,t) ; no_faults (tlb_sat_no_flt_set s) \<rbrakk>  \<Longrightarrow> 
           no_faults (tlb_sat_no_flt_set t)"
  apply (clarsimp simp: mmu_translate_tlb_sat_no_flt_state_ext_def Let_def split: lookup_type.splits)
    by (clarsimp simp: no_faults_def raise'exception_def split:split_if_asm)+



find_theorems "saturated_no_flt" "mmu_translate"

lemma write_mmu_sat_no_flt_saturated:
  "\<lbrakk>mmu_write_size (val,va,sz) s = ((), t)  \<rbrakk>  \<Longrightarrow> saturated_no_flt (typ_sat_no_flt_tlb t)"
  apply (clarsimp simp: mmu_write_size_tlb_sat_no_flt_state_ext_def Let_def)
  apply (case_tac "mmu_translate va s" , clarsimp)
  apply (clarsimp split: split_if_asm)
   apply (case_tac "write'mem1 (val, a, sz) b" , clarsimp)
   apply (subgoal_tac "ASID s = ASID ba \<and> TTBR0 s = TTBR0 ba ")
    apply (clarsimp simp: saturated_no_flt_def)
   apply (subgoal_tac "ASID s = ASID b \<and> TTBR0 s = TTBR0 b")
    apply clarsimp
    apply (clarsimp simp:  write'mem1_def Let_def)
    apply (clarsimp split: split_if_asm)
    apply (clarsimp simp:  raise'exception_def)
   apply (clarsimp simp: mmu_translate_tlb_sat_no_flt_state_ext_def Let_def raise'exception_def split:lookup_type.splits  split_if_asm)
  using mmu_translate_sat_sat_no_fault surjective_pairing by blast


lemma write_mmu_sat_no_flt_no_flts:
  "\<lbrakk>mmu_write_size (val,va,sz) s = ((), t) ; no_faults (tlb_sat_no_flt_set s)  \<rbrakk>  \<Longrightarrow> no_faults (tlb_sat_no_flt_set t)"
  apply (clarsimp simp: mmu_write_size_tlb_sat_no_flt_state_ext_def Let_def)
  apply (case_tac "mmu_translate va s" , clarsimp)
  apply (clarsimp split: split_if_asm)
   prefer 2
   apply (clarsimp simp: mmu_translate_tlb_sat_no_flt_state_ext_def Let_def raise'exception_def
                no_faults_def split:lookup_type.splits split_if_asm)
  apply (case_tac "write'mem1 (val, a, sz) b" , clarsimp)
  apply (subgoal_tac " no_faults (tlb_sat_no_flt_set b)")
   prefer 2
   apply (clarsimp simp: mmu_translate_tlb_sat_no_flt_state_ext_def Let_def raise'exception_def
                    no_faults_def split:lookup_type.splits split_if_asm)
  apply (subgoal_tac "ASID s = ASID ba \<and> TTBR0 s = TTBR0 ba")
   apply (clarsimp simp: no_faults_def)
  apply (subgoal_tac "ASID s = ASID b \<and> TTBR0 s = TTBR0 b")
   prefer 2
   apply (clarsimp simp: mmu_translate_tlb_sat_no_flt_state_ext_def Let_def split: lookup_type.splits)
     apply (clarsimp simp: raise'exception_def split:split_if_asm)+
  apply (clarsimp simp: write'mem1_eq_ASID_TTBR0)
 done


thm mmu_translate_sat_TLB_union'

lemma wrtie_mem_sat_tlbs:
  "\<lbrakk>mmu_write_size (val,va, sz) s = ((), s') \<rbrakk> \<Longrightarrow>
     tlb_sat_no_flt_set s' = tlb_sat_no_flt_set s \<union> {e\<in>pt_walk (ASID s) (MEM s) (TTBR0 s) ` UNIV. \<not> is_fault e} \<or>
     tlb_sat_no_flt_set s' = tlb_sat_no_flt_set s \<union> {e\<in>pt_walk (ASID s) (MEM s) (TTBR0 s) ` UNIV. \<not> is_fault e} \<union> {e\<in>pt_walk (ASID s') (MEM s') (TTBR0 s') ` UNIV. \<not> is_fault e}"
  apply (cases "exception (snd (mmu_translate va s)) \<noteq> NoException")
   apply (rule disjI1)
   apply (clarsimp simp: mmu_write_size_tlb_sat_no_flt_state_ext_def Let_def)
   apply (case_tac "mmu_translate va s" , clarsimp)
   apply (clarsimp simp: mmu_translate_sat_TLB_union')
  apply (clarsimp simp: mmu_write_size_tlb_sat_no_flt_state_ext_def Let_def)
  apply (case_tac "mmu_translate va s " , clarsimp)
  apply (case_tac "write'mem1 (val, a, sz) b" , clarsimp)
  apply (subgoal_tac "tlb_sat_no_flt_set ba = tlb_sat_no_flt_set b")
   apply (subgoal_tac "tlb_sat_no_flt_set b  = tlb_sat_no_flt_set s \<union> {e\<in>pt_walk (ASID s) (MEM s) (TTBR0 s) ` UNIV. \<not> is_fault e}")
    apply (subgoal_tac "ASID ba = ASID s \<and>  TTBR0 ba = TTBR0 s")
     apply clarsimp
    apply (subgoal_tac "ASID b = ASID s \<and> TTBR0 b = TTBR0 s")
     apply (clarsimp simp: write'mem1_eq_ASID_TTBR0)
    apply (clarsimp simp: mmu_sat_no_flt_eq_ASID_TTBR0_MEM)
   apply (clarsimp simp: mmu_translate_sat_TLB_union')
  apply (drule write'mem1_eq_TLB)
  apply (case_tac ba , case_tac b ; clarsimp)
done



lemma mmu_write_tlb_subset:
  "\<lbrakk> mmu_write_size (val,va, sz) s = ((), s'); tlb_rel_sat_no_flt (typ_det_tlb s) (typ_sat_no_flt_tlb t);
       mmu_write_size (val,va, sz) t = ((), t') \<rbrakk> \<Longrightarrow> tlb_det_set s' \<subseteq> tlb_sat_no_flt_set t'"
  apply (frule tlb_rel_no_flt_satD)
  apply (subgoal_tac "lookup (tlb_det_set s) (ASID s) (addr_val va) \<le> lookup (tlb_sat_no_flt_set t \<union> {e\<in>pt_walk (ASID s) (MEM s) (TTBR0 s) ` UNIV. \<not> is_fault e}) (ASID s) (addr_val va)")
   prefer 2
   apply (simp add: saturated_no_flt_def sup.absorb1 tlb_mono tlb_rel_sat_no_flt_def)
  apply (frule write'mem'det1_TLBs1)
  apply (frule wrtie_mem_sat_tlbs)
  apply (erule disjE)
   apply (clarsimp simp: typ_det_tlb_def typ_sat_no_flt_tlb_def state.defs)
   apply blast
  apply (subgoal_tac "\<not>is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) va)")
   apply (subgoal_tac "pt_walk (ASID s) (MEM s) (TTBR0 s) va \<in> {e\<in>pt_walk (ASID t) (MEM t) (TTBR0 t) ` UNIV. \<not> is_fault e}")
    apply (clarsimp simp: typ_det_tlb_def typ_sat_tlb_def state.defs)
    apply blast
   apply simp
  apply (case_tac "pt_walk (ASID s) (MEM s) (TTBR0 s) va \<in> tlb_det_set s")
   apply (clarsimp simp: tlb_rel_sat_no_flt_def no_faults_def)
   apply fastforce
  apply (clarsimp simp: mmu_write_size_tlb_det_state_ext_def)
  apply (case_tac "mmu_translate va s" , clarsimp)
  apply (clarsimp split: split_if_asm)
   prefer 2
   apply (clarsimp simp: mmu_translate_tlb_det_state_ext_def split: lookup_type.splits)
     apply (clarsimp simp: raise'exception_def split: split_if_asm)
      apply (subgoal_tac "pt_walk (ASID s) (MEM s) (TTBR0 s) va \<notin> tlb_det_set s")
       apply force
      apply (frule_tac m = "MEM s" and ttbr = "TTBR0 s" in lookup_refill)
      apply force
     apply (subgoal_tac "pt_walk (ASID s) (MEM s) (TTBR0 s) va \<notin> tlb_det_set s")
      apply force
     apply (frule_tac m = "MEM s" and ttbr = "TTBR0 s" in lookup_refill)
     apply force
    apply (clarsimp simp: raise'exception_def split:split_if_asm)
     apply force
    apply force
   apply (clarsimp split: split_if_asm)
    apply (drule lookup_in_tlb)
    apply (clarsimp simp: tlb_rel_sat_no_flt_def no_faults_def)
    apply force
   apply force
  apply (subgoal_tac "tlb_det_set s'  = tlb_det_set b")
   apply clarsimp
   apply (thin_tac "tlb_det_set s' = insert (pt_walk (ASID s) (MEM s) (TTBR0 s) va) (tlb_det_set s)")
   apply (clarsimp simp: mmu_translate_tlb_det_state_ext_def split: lookup_type.splits)
     apply (clarsimp simp: raise'exception_def split: split_if_asm)
    apply (clarsimp simp: raise'exception_def split: split_if_asm)
   apply (clarsimp simp: raise'exception_def split: split_if_asm)
   apply force
  apply (thin_tac " tlb_det_set s' = insert (pt_walk (ASID s) (MEM s) (TTBR0 s) va) (tlb_det_set s)")
  apply (clarsimp simp: write'mem1_def raise'exception_def split: split_if_asm)
   done
 

lemma mmu_translate_no_flt_excep:
  "\<lbrakk> mmu_translate va s = (p, s') ; mmu_translate va t = (p, t') ;
     consistent (typ_sat_no_flt_tlb t) va; tlb_rel_sat_no_flt (typ_det_tlb s) (typ_sat_no_flt_tlb t)\<rbrakk>  \<Longrightarrow>  exception s' = exception t'"
  apply (subgoal_tac "tlb_rel_sat_no_flt (typ_det_tlb s') (typ_sat_no_flt_tlb t')")
   apply (clarsimp simp: tlb_rel_sat_no_flt_def state.defs)
  apply (drule (2)  mmu_translate_det_sat_no_flt_refine, clarsimp simp: Let_def)
 done




lemma mmu_translate_no_flt_excep':
  "\<lbrakk> mmu_translate va s = (p, s') ; mmu_translate va t = (p, t') ;
     consistent (typ_sat_no_flt_tlb t) va; tlb_rel_sat_no_flt (typ_tlb s) (typ_sat_no_flt_tlb t)\<rbrakk>  \<Longrightarrow>  exception s' = exception t'"
  apply (subgoal_tac "tlb_rel_sat_no_flt (typ_tlb s') (typ_sat_no_flt_tlb t')")
   apply (clarsimp simp: tlb_rel_sat_no_flt_def state.defs)
  apply (drule (2)  mmu_translate_sat_no_flt_refine, clarsimp simp: Let_def)
 done



lemma sat_no_flt_states_parameters:
  "\<lbrakk> mmu_translate va t = (pa', t') ; saturated_no_flt (typ_sat_no_flt_tlb t) \<rbrakk> \<Longrightarrow>
      state.more t' = state.more t \<and> ASID t' = ASID t \<and> MEM t' = MEM t \<and> TTBR0 t' = TTBR0 t \<and>  saturated_no_flt (typ_sat_no_flt_tlb t')"
  apply (frule sat_state_tlb')
  apply (clarsimp simp: mmu_translate_tlb_sat_no_flt_state_ext_def Let_def saturated_no_flt_def)
  apply (cases "lookup (tlb_sat_no_flt_set t) (ASID t) (addr_val va)" )
    apply (clarsimp simp: raise'exception_def split:split_if_asm)+
  done


lemma write_mem_det_sat_no_flt_MEM:
  "\<lbrakk> mmu_write_size (val,va, sz) s = ((), s');  tlb_rel_sat_no_flt (typ_det_tlb s) (typ_sat_no_flt_tlb t) ; consistent (typ_sat_no_flt_tlb t) va; 
                   mmu_write_size (val,va, sz) t = ((), t') \<rbrakk> \<Longrightarrow> MEM s' = MEM t'"
  apply (frule tlb_rel_no_flt_satD)
  apply (clarsimp simp:  mmu_write_size_tlb_det_state_ext_def , cases "mmu_translate va s" , clarsimp)
  apply (clarsimp simp:  mmu_write_size_tlb_sat_no_flt_state_ext_def , cases "mmu_translate va t" , clarsimp)
  apply (clarsimp split: split_if_asm)
     apply (case_tac "write'mem1 (val, aa, sz) ba" , clarsimp)
     apply (subgoal_tac "MEM b = MEM ba \<and> aa = a")
      using write_same_mem apply blast
     apply (rule conjI)
      apply (clarsimp simp: mmu_sat_no_flt_eq_ASID_TTBR0_MEM  mmu_det_eq_ASID_TTBR0_MEM)
     apply (frule_tac s= "(typ_det_tlb s)" and va= "va" in tlb_rel_sat_no_flt_consistent, clarsimp)
     apply (subgoal_tac "lookup (tlb_det_set s) (ASID s) (addr_val va) \<le> lookup (tlb_sat_no_flt_set t \<union> {e\<in>pt_walk (ASID s) (MEM s) (TTBR0 s) ` UNIV. \<not> is_fault e}) (ASID s) (addr_val va)")
      prefer 2
      apply (simp add: saturated_no_flt_def sup.absorb1 tlb_mono tlb_rel_sat_no_flt_def)
     apply (clarsimp simp:  mmu_translate_tlb_det_state_ext_def  mmu_translate_tlb_sat_no_flt_state_ext_def split_def Let_def)
     apply (subgoal_tac "tlb_sat_no_flt_set t = tlb_sat_no_flt_set t \<union> {e\<in>pt_walk (ASID s) (MEM s) (TTBR0 s) ` UNIV. \<not> is_fault e}")
      prefer 2
      apply (fastforce simp: tlb_rel_sat_no_flt_def saturated_no_flt_def)
     apply (cases "lookup (tlb_sat_no_flt_set t \<union> {e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e}) (ASID s) (addr_val va)")
       apply (clarsimp simp: tlb_rel_sat_no_flt_def)
       apply (subgoal_tac "is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) va)")
        apply (clarsimp simp: raise'exception_def  saturated_no_flt_def state.defs split: split_if_asm)
       apply (clarsimp simp: lookup_def entry_set_def entry_range_asid_tags_def split: split_if_asm)
       apply force
      apply (clarsimp simp: consistent0_def)
     apply clarsimp
     apply (subgoal_tac "x3 = pt_walk (ASID s) (MEM s) (TTBR0 s) va")
      prefer 2
      apply (clarsimp simp: consistent0_def)
     apply (cases "lookup (tlb_det_set s) (ASID s) (addr_val va)"; clarsimp)
      apply (clarsimp simp: Let_def)
      apply (subgoal_tac "\<not>is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) va)")
       prefer 2
       apply (clarsimp simp: tlb_rel_sat_no_flt_def no_faults_def lookup_in_tlb)
      apply (clarsimp simp: tlb_rel_sat_no_flt_def typ_sat_no_flt_tlb_def typ_det_tlb_def state.defs lookup_in_tlb raise'exception_def split: split_if_asm)
     apply (subgoal_tac "\<not>is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) va)")
      apply clarsimp
     apply (clarsimp simp: tlb_rel_sat_no_flt_def no_faults_def lookup_in_tlb)
    apply (metis (mono_tags, lifting) MMU_ARM_No_Fault.typ_det_prim_parameter mmu_translate_det_sat_no_flt_refine mmu_translate_no_flt_excep prod.simps(2) tlb_rel_no_flt_satD tlb_sat_no_flt_more)
   apply (metis (mono_tags, lifting) MMU_ARM_No_Fault.typ_det_prim_parameter mmu_translate_det_sat_no_flt_refine mmu_translate_no_flt_excep prod.simps(2) tlb_rel_no_flt_satD tlb_sat_no_flt_more)
  apply (simp add: mmu_det_eq_ASID_TTBR0_MEM sat_no_flt_states_parameters tlb_rel_sat_no_flt_def)
 done


lemma mmu_wrtie_sat_no_flt_rel:
  "\<lbrakk>mmu_write_size (val,va, sz) s = ((), s')\<rbrakk>   \<Longrightarrow> 
      s' = s \<lparr> tlb_sat_no_flt_set:= tlb_sat_no_flt_set s' , MEM:= MEM s' , exception:= exception s' \<rparr>"
  apply (clarsimp simp: mmu_write_size_tlb_sat_no_flt_state_ext_def Let_def)
  apply (cases "mmu_translate va s" , clarsimp)
  apply (clarsimp split: split_if_asm)
   apply (case_tac " write'mem1 (val, a, sz) b", clarsimp)
   apply (drule write'mem1_rel)
   apply (drule mmu_sat_rel')
   apply (cases s, cases s', case_tac a, case_tac b, case_tac ba)
   apply clarsimp
  apply (clarsimp simp: mmu_translate_tlb_sat_no_flt_state_ext_def Let_def)
  apply (cases "lookup (tlb_sat_no_flt_set s \<union> {e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e}) (ASID s) (addr_val va) ")
    apply (clarsimp simp: raise'exception_def saturated_not_miss split:split_if_asm) (* this has to do *)
   apply (clarsimp simp: raise'exception_def split:split_if_asm)
  apply (clarsimp simp: raise'exception_def split:split_if_asm)
done



lemma mmu_translate_sat_no_flt_mem_excep:
  "\<lbrakk> mmu_translate va s = (p, s') ; mmu_translate va t = (p, t') ;
     consistent (typ_sat_no_flt_tlb t) va; tlb_rel_sat_no_flt (typ_det_tlb s) (typ_sat_no_flt_tlb t)\<rbrakk>  \<Longrightarrow> MEM s' = MEM t' \<and> exception s' = exception t'"
  apply (subgoal_tac "tlb_rel_sat_no_flt (typ_det_tlb s') (typ_sat_no_flt_tlb t')")
   apply (clarsimp simp: tlb_rel_sat_no_flt_def state.defs)
  apply (drule (2)  mmu_translate_det_sat_no_flt_refine, clarsimp simp: Let_def)
 done


lemma mmu_translate_sat_no_flt_mem_excep':
  "\<lbrakk> mmu_translate va s = (p, s') ; mmu_translate va t = (p, t') ;
     consistent (typ_sat_no_flt_tlb t) va; tlb_rel_sat_no_flt (typ_tlb s) (typ_sat_no_flt_tlb t)\<rbrakk>  \<Longrightarrow> MEM s' = MEM t' \<and> exception s' = exception t'"
  apply (subgoal_tac "tlb_rel_sat_no_flt (typ_tlb s') (typ_sat_no_flt_tlb t')")
   apply (clarsimp simp: tlb_rel_sat_no_flt_def state.defs)
  apply (drule (2)  mmu_translate_sat_no_flt_refine, clarsimp simp: Let_def)
 done

lemma  mmu_translate_det_no_flt_sat_pa:
  "\<lbrakk> mmu_translate va s = (pa, s'); tlb_rel_sat_no_flt (typ_det_tlb s) (typ_sat_no_flt_tlb t)  ; consistent (typ_sat_no_flt_tlb t) va;
         mmu_translate va t = (pa', t')  \<rbrakk> \<Longrightarrow> pa = pa'"
  using mmu_translate_det_sat_no_flt_refine by fastforce




lemma  mmu_translate_no_flt_sat_pa:
  "\<lbrakk> mmu_translate va s = (pa, s'); tlb_rel_sat_no_flt (typ_tlb s) (typ_sat_no_flt_tlb t)  ; consistent (typ_sat_no_flt_tlb t) va;
         mmu_translate va t = (pa', t')  \<rbrakk> \<Longrightarrow> pa = pa'"
  using mmu_translate_sat_no_flt_refine by fastforce




lemma mmu_write_size_det_sat_no_flt_state_trun:
  "\<lbrakk>mmu_write_size (val,va, sz) s = ((), s'); tlb_rel_sat_no_flt (typ_det_tlb s) (typ_sat_no_flt_tlb t)  ; consistent (typ_sat_no_flt_tlb t) va;
     mmu_write_size (val,va, sz) t = ((), t')\<rbrakk> \<Longrightarrow> state.truncate t' = state.truncate s'"
  apply (frule (3)  write_mem_det_sat_no_flt_MEM)
  apply (frule tlb_rel_no_flt_satD, clarsimp)
  apply (frule write'mem'det1_rel1)
  apply (rotate_tac)
  apply (frule mmu_wrtie_sat_no_flt_rel)
  apply (clarsimp simp: tlb_rel_sat_no_flt_def)
  apply (subgoal_tac "exception s' = exception t'")
   apply (cases s, cases t, cases s' , cases t')
   apply (clarsimp simp: state.defs tlb_sat_no_flt_state.defs)
  apply (clarsimp simp: mmu_write_size_tlb_sat_no_flt_state_ext_def mmu_write_size_tlb_det_state_ext_def Let_def)
  apply (case_tac "mmu_translate va t" , case_tac "write'mem1 (val, a, sz) b" , clarsimp)
  apply (case_tac "mmu_translate va s" , clarsimp)
  apply (subgoal_tac "exception b = exception bb \<and> a = aa")
   apply (clarsimp split: split_if_asm)
   apply (subgoal_tac "MEM b = MEM bb ")
    apply (frule_tac s="bb" and s'="s'" and t = b and t' = ba in write_same_mem_excep ; clarsimp)
   apply (frule_tac s="s" and s'="bb" and t = t and t' = b in mmu_translate_sat_no_flt_mem_excep ; clarsimp simp: consistent0_def tlb_rel_sat_no_flt_def)
  apply (rule conjI)
   apply (frule_tac t= t and pa' = a and t' = b in mmu_translate_det_no_flt_sat_pa)
      apply (clarsimp simp: tlb_rel_sat_no_flt_def)
     apply (clarsimp simp: consistent0_def)
    apply (clarsimp simp: tlb_rel_sat_no_flt_def)
   apply (frule_tac s = "s" and s' = "bb" and t = "t" and t' = "b" in   mmu_translate_no_flt_excep ; clarsimp simp: tlb_rel_sat_no_flt_def)
  apply (subgoal_tac "lookup (tlb_det_set s) (ASID s) (addr_val va) \<le> lookup (tlb_sat_no_flt_set t \<union> {e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e}) (ASID s) (addr_val va)")
   prefer 2
   apply (simp add: saturated_no_flt_def sup.absorb1 tlb_mono tlb_rel_sat_no_flt_def)
  apply (clarsimp simp: mmu_translate_tlb_det_state_ext_def mmu_translate_tlb_sat_no_flt_state_ext_def split_def Let_def)
  apply (subgoal_tac "tlb_sat_no_flt_set t = tlb_sat_no_flt_set t \<union>  {e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e}")
   prefer 2
   apply (fastforce simp: tlb_rel_sat_no_flt_def saturated_no_flt_def)
  apply (cases "lookup (tlb_sat_no_flt_set t \<union> {e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e}) (ASID s) (addr_val va)")
    apply clarsimp
    prefer 2
    apply (clarsimp simp: consistent0_def)
   prefer 2
   apply clarsimp
   apply (subgoal_tac "x3 = pt_walk (ASID s) (MEM s) (TTBR0 s) va")
    prefer 2
    apply (clarsimp simp: consistent0_def)
   apply (cases "lookup (tlb_det_set s) (ASID s) (addr_val va)"; clarsimp)
    apply (clarsimp simp: Let_def)
    apply (subgoal_tac "\<not>is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) va)")
     prefer 2
     apply (clarsimp simp: tlb_rel_sat_no_flt_def no_faults_def lookup_in_tlb)
    apply (clarsimp simp: tlb_rel_sat_no_flt_def typ_sat_no_flt_tlb_def typ_det_tlb_def state.defs lookup_in_tlb raise'exception_def split: split_if_asm)
   apply (subgoal_tac "\<not>is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) va)")
    apply clarsimp
   apply (clarsimp simp: tlb_rel_sat_no_flt_def no_faults_def lookup_in_tlb)
  apply (clarsimp simp: tlb_rel_sat_no_flt_def Let_def)
    apply (subgoal_tac "is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) va)")
     apply (clarsimp simp: raise'exception_def  saturated_no_flt_def state.defs split: split_if_asm)
    apply (clarsimp simp: lookup_def entry_set_def entry_range_asid_tags_def split: split_if_asm)
    by force+
  

lemma mmu_write_det_sat_refine:
  "\<lbrakk> mmu_write_size (val,va, sz) s = ((), s'); tlb_rel_sat_no_flt (typ_det_tlb s) (typ_sat_no_flt_tlb t)  ; consistent (typ_sat_no_flt_tlb t) va;
        mmu_write_size (val,va, sz) t = ((), t') \<rbrakk> \<Longrightarrow>  tlb_rel_sat_no_flt (typ_det_tlb s') (typ_sat_no_flt_tlb t') "
  apply (clarsimp simp: tlb_rel_sat_no_flt_def)
  apply (clarsimp simp: write_mmu_sat_no_flt_saturated write_mmu_sat_no_flt_no_flts)
  apply (rule conjI)
   prefer 2                                                               
   apply (frule_tac s="s" and s'="s'" and t="t" and t'="t'" in mmu_write_tlb_subset; clarsimp simp: tlb_rel_sat_no_flt_def)
  apply (frule_tac s="s" and s'="s'" and t="t" and t'="t'" in mmu_write_size_det_sat_no_flt_state_trun; clarsimp simp: tlb_rel_sat_no_flt_def)
  done


lemma mmu_write_tlb_subset':
  "\<lbrakk> mmu_write_size (val,va, sz) s = ((), s'); tlb_rel_sat_no_flt (typ_tlb s) (typ_sat_no_flt_tlb t);
       mmu_write_size (val,va, sz) t = ((), t') \<rbrakk> \<Longrightarrow> tlb_set s' \<subseteq> tlb_sat_no_flt_set t'"
  apply (frule tlb_rel_no_flt_satD)
  apply (subgoal_tac "lookup (tlb_set s) (ASID s) (addr_val va) \<le> lookup (tlb_sat_no_flt_set t \<union> {e\<in>pt_walk (ASID s) (MEM s) (TTBR0 s) ` UNIV. \<not> is_fault e}) (ASID s) (addr_val va)")
   prefer 2
   apply (simp add: saturated_no_flt_def sup.absorb1 tlb_mono tlb_rel_sat_no_flt_def)
  apply (frule write'mem'_TLBs1)
  apply (frule wrtie_mem_sat_tlbs)
  apply (erule disjE)
   apply (clarsimp simp: )
   apply blast
  apply (subgoal_tac "\<not>is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) va)")
   apply (subgoal_tac "pt_walk (ASID s) (MEM s) (TTBR0 s) va \<in> {e\<in>pt_walk (ASID t) (MEM t) (TTBR0 t) ` UNIV. \<not> is_fault e}")
    apply (clarsimp simp: )
    apply blast
   apply simp
  apply (case_tac "pt_walk (ASID s) (MEM s) (TTBR0 s) va \<in> tlb_set s - tlb_evict (typ_tlb s)")
   apply (clarsimp simp: tlb_rel_sat_no_flt_def no_faults_def)
   apply fastforce
  apply (clarsimp simp: mmu_write_size_tlb_state_ext_def)
  apply (case_tac "mmu_translate va s" , clarsimp)
  apply (clarsimp split: split_if_asm)
   prefer 2
   apply (clarsimp simp: mmu_translate_tlb_state_ext_def split: lookup_type.splits)
     apply (clarsimp simp: raise'exception_def split: split_if_asm)
      apply (subgoal_tac "pt_walk (ASID s) (MEM s) (TTBR0 s) va \<notin> tlb_set s - tlb_evict (typ_tlb s)")
       apply force
      apply (frule_tac m = "MEM s" and ttbr = "TTBR0 s" in lookup_refill)
      apply force
     apply (subgoal_tac "pt_walk (ASID s) (MEM s) (TTBR0 s) va \<notin> tlb_set s - tlb_evict (typ_tlb s)")
      apply force
     apply (frule_tac m = "MEM s" and ttbr = "TTBR0 s" in lookup_refill)
     apply force
    apply (clarsimp simp: raise'exception_def split:split_if_asm)
     apply force
    apply force
   apply (clarsimp split: split_if_asm)
    apply (drule lookup_in_tlb)
    apply (clarsimp simp: tlb_rel_sat_no_flt_def no_faults_def)
    apply force
   apply force
  apply (subgoal_tac "tlb_set s'  = tlb_set b")
   apply clarsimp
   apply (thin_tac "tlb_set s' =  insert (pt_walk (ASID s) (MEM s) (TTBR0 s) va) (tlb_set s - tlb_evict (typ_tlb s))")
   apply (clarsimp simp: mmu_translate_tlb_state_ext_def split: lookup_type.splits)
     apply (clarsimp simp: raise'exception_def split: split_if_asm)
    apply (clarsimp simp: raise'exception_def split: split_if_asm)
   apply (clarsimp simp: raise'exception_def split: split_if_asm)
   apply force
  apply (thin_tac " tlb_set s' = insert (pt_walk (ASID s) (MEM s) (TTBR0 s) va) (tlb_set s - tlb_evict (typ_tlb s))")
  apply (clarsimp simp: write'mem1_def raise'exception_def split: split_if_asm)
  done
 

thm  write_mem_det_sat_no_flt_MEM

lemma write_mem_sat_no_flt_MEM:
  "\<lbrakk> mmu_write_size (val,va, sz) s = ((), s');  tlb_rel_sat_no_flt (typ_tlb s) (typ_sat_no_flt_tlb t) ; consistent (typ_sat_no_flt_tlb t) va; 
                   mmu_write_size (val,va, sz) t = ((), t') \<rbrakk> \<Longrightarrow> MEM s' = MEM t'"
  apply (frule tlb_rel_no_flt_satD)
  apply (clarsimp simp:  mmu_write_size_tlb_state_ext_def , cases "mmu_translate va s" , clarsimp)
  apply (clarsimp simp:  mmu_write_size_tlb_sat_no_flt_state_ext_def , cases "mmu_translate va t" , clarsimp)
  apply (clarsimp split: split_if_asm)
     apply (case_tac "write'mem1 (val, aa, sz) ba" , clarsimp)
     apply (subgoal_tac "MEM b = MEM ba \<and> aa = a")
      using write_same_mem apply blast
     apply (rule conjI)
      apply (clarsimp simp: mmu_sat_no_flt_eq_ASID_TTBR0_MEM  mmu_eq_ASID_TTBR0_MEM)
     apply (frule_tac s= "(typ_tlb s)" and va= "va" in tlb_rel_sat_no_flt_consistent, clarsimp)
     apply (subgoal_tac "tlb_set s - tlb_evict (typ_tlb s) \<subseteq> tlb_set s")
      prefer 2
      apply blast
     apply (subgoal_tac "lookup (tlb_set s - tlb_evict (typ_tlb s)) (ASID s) (addr_val va) \<le> lookup (tlb_sat_no_flt_set t \<union> {e\<in>pt_walk (ASID s) (MEM s) (TTBR0 s) ` UNIV. \<not> is_fault e}) (ASID s) (addr_val va)")
      prefer 2
      apply (simp add: saturated_no_flt_def sup.absorb1 tlb_mono tlb_rel_sat_no_flt_def)
     apply (clarsimp simp:  mmu_translate_tlb_state_ext_def  mmu_translate_tlb_sat_no_flt_state_ext_def split_def Let_def)
     apply (subgoal_tac "tlb_sat_no_flt_set t = tlb_sat_no_flt_set t \<union> {e\<in>pt_walk (ASID s) (MEM s) (TTBR0 s) ` UNIV. \<not> is_fault e}")
      prefer 2
      apply (fastforce simp: tlb_rel_sat_no_flt_def saturated_no_flt_def)
     apply (cases "lookup (tlb_sat_no_flt_set t \<union> {e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e}) (ASID s) (addr_val va)")
       apply (clarsimp simp: tlb_rel_sat_no_flt_def)
       apply (subgoal_tac "is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) va)")
        apply (clarsimp simp: raise'exception_def  saturated_no_flt_def state.defs split: split_if_asm)
       apply (clarsimp simp: lookup_def entry_set_def entry_range_asid_tags_def split: split_if_asm)
       apply fastforce
      apply (clarsimp simp: consistent0_def)
     apply clarsimp
     apply (subgoal_tac "x3 = pt_walk (ASID s) (MEM s) (TTBR0 s) va")
      prefer 2
      apply (clarsimp simp: consistent0_def)
     apply (cases "lookup (tlb_set s - tlb_evict (typ_tlb s)) (ASID s) (addr_val va)"; clarsimp)
      apply (clarsimp simp: Let_def)
      apply (subgoal_tac "\<not>is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) va)")
       prefer 2
       apply (clarsimp simp: tlb_rel_sat_no_flt_def no_faults_def lookup_in_tlb)
      apply (clarsimp simp: tlb_rel_sat_no_flt_def typ_sat_no_flt_tlb_def typ_tlb_def state.defs lookup_in_tlb raise'exception_def split: split_if_asm)
     apply (subgoal_tac "\<not>is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) va)")
      apply clarsimp
     apply (clarsimp simp: tlb_rel_sat_no_flt_def no_faults_def lookup_in_tlb)
    using mmu_translate_no_flt_excep' mmu_translate_no_flt_sat_pa apply fastforce
   using mmu_translate_no_flt_excep' mmu_translate_no_flt_sat_pa apply fastforce
  apply (simp add: mmu_eq_ASID_TTBR0_MEM sat_no_flt_states_parameters tlb_rel_sat_no_flt_def)
 done

thm mmu_write_size_det_sat_no_flt_state_trun
lemma mmu_write_size_det_sat_no_flt_state_trun':
  "\<lbrakk>mmu_write_size (val,va, sz) s = ((), s'); tlb_rel_sat_no_flt (typ_tlb s) (typ_sat_no_flt_tlb t)  ; consistent (typ_sat_no_flt_tlb t) va;
     mmu_write_size (val,va, sz) t = ((), t')\<rbrakk> \<Longrightarrow> state.truncate t' = state.truncate s'"
  apply (frule (3)  write_mem_sat_no_flt_MEM)
  apply (frule tlb_rel_no_flt_satD, clarsimp)
  apply (frule write'mem'_rel1)
  apply (rotate_tac)
  apply (frule mmu_wrtie_sat_no_flt_rel)
  apply (clarsimp simp: tlb_rel_sat_no_flt_def)
  apply (subgoal_tac "exception s' = exception t'")
   apply (cases s, cases t, cases s' , cases t')
   apply (clarsimp simp: state.defs tlb_sat_no_flt_state.defs)
  apply (clarsimp simp: mmu_write_size_tlb_sat_no_flt_state_ext_def mmu_write_size_tlb_state_ext_def Let_def)
  apply (case_tac "mmu_translate va t" , case_tac "write'mem1 (val, a, sz) b" , clarsimp)
  apply (case_tac "mmu_translate va s" , clarsimp)
  apply (subgoal_tac "exception b = exception bb \<and> a = aa")
   apply (clarsimp split: split_if_asm)
   apply (subgoal_tac "MEM b = MEM bb ")
    apply (frule_tac s="bb" and s'="s'" and t = b and t' = ba in write_same_mem_excep ; clarsimp)
   apply (frule_tac s="s" and s'="bb" and t = t and t' = b in mmu_translate_sat_no_flt_mem_excep' ; clarsimp simp: consistent0_def tlb_rel_sat_no_flt_def)
  apply (rule conjI)
   apply (frule_tac t= t and pa' = a and t' = b in mmu_translate_no_flt_sat_pa)
      apply (clarsimp simp: tlb_rel_sat_no_flt_def)
     apply (clarsimp simp: consistent0_def)
    apply (clarsimp simp: tlb_rel_sat_no_flt_def)
   apply (frule_tac s = "s" and s' = "bb" and t = "t" and t' = "b" in   mmu_translate_no_flt_excep' ; clarsimp simp: tlb_rel_sat_no_flt_def)
  apply (subgoal_tac "tlb_set s - tlb_evict (typ_tlb s) \<subseteq> tlb_set s")
   prefer 2
   apply blast
  apply (subgoal_tac "lookup (tlb_set s - tlb_evict (typ_tlb s)) (ASID s) (addr_val va) \<le> lookup (tlb_sat_no_flt_set t \<union> {e\<in>pt_walk (ASID s) (MEM s) (TTBR0 s) ` UNIV. \<not> is_fault e}) (ASID s) (addr_val va)")
   prefer 2
   apply (simp add: saturated_no_flt_def sup.absorb1 tlb_mono tlb_rel_sat_no_flt_def)
  apply (clarsimp simp: mmu_translate_tlb_state_ext_def mmu_translate_tlb_sat_no_flt_state_ext_def split_def Let_def)
  apply (subgoal_tac "tlb_sat_no_flt_set t = tlb_sat_no_flt_set t \<union>  {e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e}")
   prefer 2
   apply (fastforce simp: tlb_rel_sat_no_flt_def saturated_no_flt_def)
  apply (cases "lookup (tlb_sat_no_flt_set t \<union> {e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e}) (ASID s) (addr_val va)")
    apply clarsimp
    prefer 2
    apply (clarsimp simp: consistent0_def)
   prefer 2
   apply clarsimp
   apply (subgoal_tac "x3 = pt_walk (ASID s) (MEM s) (TTBR0 s) va")
    prefer 2
    apply (clarsimp simp: consistent0_def)
   apply (cases "lookup  (tlb_set s - tlb_evict (typ_tlb s)) (ASID s) (addr_val va)"; clarsimp)
    apply (clarsimp simp: Let_def)
    apply (subgoal_tac "\<not>is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) va)")
     prefer 2
     apply (clarsimp simp: tlb_rel_sat_no_flt_def no_faults_def lookup_in_tlb)
    apply (clarsimp simp: tlb_rel_sat_no_flt_def typ_sat_no_flt_tlb_def typ_tlb_def state.defs lookup_in_tlb raise'exception_def split: split_if_asm)
   apply (subgoal_tac "\<not>is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) va)")
    apply clarsimp
   apply (clarsimp simp: tlb_rel_sat_no_flt_def no_faults_def lookup_in_tlb)
  apply (clarsimp simp: tlb_rel_sat_no_flt_def Let_def)
  apply (subgoal_tac "is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) va)")
   apply (clarsimp simp: raise'exception_def  saturated_no_flt_def state.defs split: split_if_asm)
  apply (clarsimp simp: lookup_def entry_set_def entry_range_asid_tags_def split: split_if_asm)
     by force+




lemma mmu_write_non_det_sat_refine:
  "\<lbrakk> mmu_write_size (val,va, sz) s = ((), s'); tlb_rel_sat_no_flt (typ_tlb s) (typ_sat_no_flt_tlb t)  ; consistent (typ_sat_no_flt_tlb t) va;
        mmu_write_size (val,va, sz) t = ((), t') \<rbrakk> \<Longrightarrow>  tlb_rel_sat_no_flt (typ_tlb s') (typ_sat_no_flt_tlb t') "
  apply (clarsimp simp: tlb_rel_sat_no_flt_def)
  apply (clarsimp simp: write_mmu_sat_no_flt_saturated write_mmu_sat_no_flt_no_flts)
  apply (rule conjI)
   prefer 2                                                               
   apply (frule_tac s = s and s' = s' and t = t and t' = t' in mmu_write_tlb_subset'; clarsimp simp: tlb_rel_sat_no_flt_def)
  apply (frule_tac s="s" and s'="s'" and t="t" and t'="t'" in mmu_write_size_det_sat_no_flt_state_trun'; clarsimp simp: tlb_rel_sat_no_flt_def)
done


(*definition 
  pde_comp :: "asid \<Rightarrow> heap \<Rightarrow> heap \<Rightarrow> paddr \<Rightarrow> (asid \<times> 32 word) set"
where
  "pde_comp a hp1 hp2 rt \<equiv> 
         (\<lambda>x. (a, addr_val x)) ` {va. (\<exists>p1 p2. ptable_lift' hp1 rt va = Some p1 \<and> ptable_lift' hp2 rt va = Some p2 \<and> p1 \<noteq> p2 )  \<or> 
                                      (\<exists>p. ptable_lift' hp1 rt va = Some p \<and> ptable_lift' hp2 rt va = None )}" *)


definition 
  pde_comp :: "asid \<Rightarrow> heap \<Rightarrow> heap \<Rightarrow> paddr \<Rightarrow> (asid \<times> 32 word) set"
where
  "pde_comp a hp1 hp2 rt \<equiv> 
         (\<lambda>x. (a, addr_val x)) ` {va. (\<exists>p1 p2. ptable_lift hp1 rt va = Some p1 \<and> ptable_lift hp2 rt va = Some p2 \<and> p1 \<noteq> p2 )  \<or> 
                                      (\<exists>p.     ptable_lift hp1 rt va = Some p \<and> ptable_lift hp2 rt va = None) }"


definition 
  pde_comp' :: "asid \<Rightarrow> heap \<Rightarrow> heap \<Rightarrow> paddr \<Rightarrow> (asid \<times> 32 word) set"
where
  "pde_comp' a hp1 hp2 rt \<equiv> 
         (\<lambda>x. (a, addr_val x)) ` {va. (\<exists>e1 e2. pt_walk a hp1 rt va = e1 \<and> pt_walk a hp2 rt va = e2  \<and> \<not>is_fault e1 \<and> \<not>is_fault e2 \<and> e1 \<noteq> e2 )  \<or> 
                                      (\<exists>e1 e2. pt_walk a hp1 rt va = e1 \<and> pt_walk a hp2 rt va = e2  \<and> \<not>is_fault e1 \<and> is_fault e2 )}"

find_theorems "is_fault"  "ptable_lift"


lemma not_fault_ptable_defined:
  "\<not>is_fault (pt_walk a hp1 rt va) \<Longrightarrow> ptable_lift hp1 rt va \<noteq> None"
  apply (clarsimp simp: pt_walk_def is_fault_def ptable_lift_def lookup_pde_def lookup_pte_def split:option.splits pde.splits pte.splits) 
  by force
 

lemma
  "\<not> is_fault (pt_walk a hp1 rt va) \<Longrightarrow> \<exists>p1. ptable_lift hp1 rt va = Some p1"
  apply (clarsimp simp: pt_walk_def is_fault_def ptable_lift_def lookup_pde_def lookup_pte_def split:option.splits pde.splits pte.splits)
  by force

lemma
  "\<lbrakk>\<not> is_fault (pt_walk a hp1 rt x); \<not> is_fault (pt_walk a hp2 rt x); pt_walk a hp1 rt x \<noteq> pt_walk a hp2 rt x\<rbrakk> \<Longrightarrow>
      ptable_lift hp1 rt x \<noteq> ptable_lift hp2 rt x"
  apply (clarsimp simp: pt_walk_def is_fault_def ptable_lift_def lookup_pde_def)
  apply (clarsimp  split:option.splits)
  apply (case_tac x2 ; clarsimp)
   apply (case_tac x2a ; clarsimp)
   apply (clarsimp split: option.splits)
   apply (case_tac x2 ; clarsimp)
   apply (case_tac x2a ; clarsimp)
    apply (clarsimp simp: lookup_pte_def)
    apply (subgoal_tac "x21a = x21")  apply clarsimp 
    apply (clarsimp simp: vaddr_offset_def mask_def) 
   apply word_bitwise  

oops
 
lemma  pde_comp'_pde_comp:
(* not true *)
  "\<forall>av\<in>pde_comp' a hp1 hp2 rt. av \<in> pde_comp a hp1 hp2 rt"
  apply safe
  apply (clarsimp simp: pde_comp'_def)
  apply (clarsimp simp: pde_comp_def)
  apply (erule disjE ; clarsimp)  
oops


instantiation tlb_incon_state'_ext :: (type) mem_op    
begin

definition   
  "(mmu_read  :: (vaddr  \<Rightarrow>  'a tlb_incon_state'_scheme\<Rightarrow> bool list \<times>  'a tlb_incon_state'_scheme))
   \<equiv>  \<lambda>va. do {
                     pa  \<leftarrow> mmu_translate va;
                     mem1 pa
  }"

definition
 "(mmu_read_size  :: (vaddr \<times> nat \<Rightarrow>  'a tlb_incon_state'_scheme \<Rightarrow> bool list \<times>  'a tlb_incon_state'_scheme))
  \<equiv> \<lambda>(va,size). do {
                     pa  \<leftarrow> mmu_translate va;
                     mem_read1 (pa , size)
  }"


definition   
  "(mmu_write_size  :: (bool list \<times> vaddr \<times> nat \<Rightarrow> 'a tlb_incon_state'_scheme \<Rightarrow> unit \<times> 'a tlb_incon_state'_scheme))
  \<equiv> \<lambda>(value, vaddr, size). do {
      ttbr0 <- read_state TTBR0;
      asid  <- read_state ASID;
      mem   <- read_state MEM; 
      paddr <- mmu_translate vaddr;
      incon_set <- read_state tlb_incon_set'; 
      exception <- read_state exception;
      if exception = NoException 
        then  do {
                   write'mem1 (value, paddr, size);
                   mem' <- read_state MEM;
                   ptable_asid_va <- return (pde_comp' asid mem mem' ttbr0);
                   update_state (\<lambda>s. s\<lparr> tlb_incon_set' :=  incon_set \<union> ptable_asid_va \<rparr>)
            }
        else return ()
   }"
  instance ..
end


find_theorems "consistent" "saturated_no_flt"

thm write_asid_incon_set_rel



lemma asid_unequal_miss':
  " a \<noteq> ASID b \<Longrightarrow>
   lookup {e \<in> range (pt_walk (ASID b) (MEM bc) (TTBR0 b)). \<not> is_fault e} a bb = Miss"
  apply (clarsimp simp:  lookup_def entry_set_def entry_range_asid_tags_def) 
  by force


lemma
  "(\<exists>x\<in>(t1 \<union> t2). lookup (t1 \<union> t2) a va = Hit x \<and> lookup t2 a va = Miss)  \<Longrightarrow>
      (\<exists>x\<in>t1. lookup t1 a va = Hit x)    "
  apply (clarsimp simp: lookup_def entry_set_def split: split_if_asm)
  apply auto
  done



lemma lookup_hit_mis_hit:
  " lookup (t1 \<union> t2) a va = Hit x \<and> lookup t2 a va = Miss \<Longrightarrow> lookup t1 a va = Hit x   "
  apply (clarsimp simp: lookup_def entry_set_def split: split_if_asm)
  apply auto
  apply force
  done


lemma lookup_union_hit_miss_hit :
  "\<lbrakk>lookup (t \<union> t') a va = Hit x ; lookup t' a va \<noteq> Miss \<rbrakk> \<Longrightarrow> lookup t' a va = Hit x   "
  apply (clarsimp simp: lookup_def entry_set_def split: split_if_asm)  
  by force+
  

lemma lookup_union_hit_miss_hit' :
  "\<lbrakk>lookup (t \<union> t') a va = Hit x ; lookup t a va \<noteq> Miss \<rbrakk> \<Longrightarrow> lookup t a va = Hit x   "
  apply (clarsimp simp: lookup_def entry_set_def split: split_if_asm)
   by force+

lemma   lookup_union_hit_hit_miss :
  "\<lbrakk>lookup (t \<union> t') a va = Hit x ;  \<forall>x\<in>t. lookup t a va \<noteq> Hit x\<rbrakk> \<Longrightarrow> lookup t a va = Miss   "
 apply (clarsimp simp: lookup_def entry_set_def split: split_if_asm)
   by force+


lemma
  "lookup (t1 \<union> t2) a va = Hit x \<and> lookup t1 a va = Miss \<Longrightarrow> lookup t2 a va = Hit x   "
  apply (clarsimp simp: lookup_def entry_set_def split: split_if_asm)
  apply safe
         by force+
  

lemma lookup_hit_miss_or_hit :
  " lookup (t1 \<union> t2) a va = Hit x \<and> x \<in> t1  \<Longrightarrow> 
              lookup t2 a va = Miss \<or> (lookup t2 a va = Hit x)"
  apply (clarsimp simp: lookup_def entry_set_def split: split_if_asm)
  by force+


lemma lookup_hit_miss_or_hit' :
  " lookup (t1 \<union> t2) a va = Hit x  \<Longrightarrow> 
              lookup t2 a va = Miss \<or> (lookup t2 a va = Hit x)"
  apply (clarsimp simp: lookup_def entry_set_def split: split_if_asm)
  by force+


lemma not_miss_incon_hit:
  "lookup t a va \<noteq> Miss \<Longrightarrow> lookup t a va = Incon \<or> (\<exists>x\<in>t. lookup t a va = Hit x)"
 apply (clarsimp simp: lookup_def entry_set_def split: split_if_asm)
  by auto

lemma  entry_set_rewrite :
  "{E. (E \<in> t1 \<or> E \<in> t2) \<and> (asid_entry xa, va) \<in> Pair (asid_entry E) ` entry_range E} = {x} \<Longrightarrow>
        x \<in> t1 \<or> x \<in> t2 \<or> (x\<in>t1 \<and> x\<in>t2)"
  by blast


lemma  lookup_not_hit_false:
  "\<lbrakk>lookup (t1 \<union> t2) a va = Hit x; lookup t1 a va \<noteq> Hit x; lookup t2 a va \<noteq> Hit x\<rbrakk> \<Longrightarrow> False"
  apply (clarsimp simp: lookup_def entry_set_def split: split_if_asm)
          apply safe by force+



lemma  lookup_not_hit_miss:
  "\<lbrakk>lookup (t1 \<union> t2) a va = Hit x ;   lookup t1 a va \<noteq> Hit x\<rbrakk> \<Longrightarrow> lookup t1 a va = Miss   "
  apply (clarsimp simp: lookup_def entry_set_def split: split_if_asm)
   apply safe
       by force+


lemma  lookup_hit_union_cases:
  "(\<exists>x\<in>(t1 \<union> t2). lookup (t1 \<union> t2) a va = Hit x)  \<Longrightarrow>
      ((\<exists>x\<in>t1. lookup t1 a va = Hit x) \<and> lookup t2 a va = Miss)       \<or>
      ((\<exists>x\<in>t2. lookup t2 a va = Hit x)  \<and> lookup t1 a va = Miss)      \<or>
      ((\<exists>x\<in>t1. \<exists>x1\<in>t2.  lookup t1 a va = Hit x  \<and> lookup t2 a va = Hit x1 \<and>  x = x1)) "
  apply (safe ; clarsimp)
         apply (clarsimp simp: lookup_def entry_set_def split: split_if_asm ,force , force, ((safe ; force) [1]))
        apply (clarsimp simp: lookup_def entry_set_def split: split_if_asm , force, force)
       apply (drule_tac x = "x" in bspec , clarsimp)
       apply (drule_tac not_miss_incon_hit , erule disjE ; clarsimp )
       using lookup_hit_miss_or_hit apply force
      apply (frule lookup_union_hit_miss_hit , clarsimp)
      apply (drule_tac x = "x" in bspec ,clarsimp)
      apply (subgoal_tac "x \<in> t2" , clarsimp)
       apply (clarsimp simp: lookup_def entry_set_def split: split_if_asm ; force)
      using lookup_in_tlb apply force
     apply (clarsimp simp: lookup_def entry_set_def split: split_if_asm ;  (safe ; force))
    using lookup_union_hit_hit_miss apply clarsimp
   apply (clarsimp simp: lookup_def entry_set_def split: split_if_asm ; (safe ; force))
  apply (cases " lookup t1 a va = Miss" ; clarsimp)
  apply (frule_tac lookup_union_hit_miss_hit ; clarsimp)
  apply (frule_tac lookup_union_hit_miss_hit' ; clarsimp)
  apply (subgoal_tac "x\<in>t1")
   apply (drule_tac x = "x" in bspec ; clarsimp)
  using lookup_in_tlb by force

   



lemma lookup_hit_union_cases':
  " lookup (t1 \<union> t2) a va = Hit x  \<Longrightarrow>
      (lookup t1 a va = Hit x \<and> lookup t2 a va = Miss)  \<or>
      (lookup t2 a va = Hit x \<and> lookup t1 a va = Miss)  \<or>
      (lookup t1 a va = Hit x  \<and> lookup t2 a va = Hit x) "
  apply (safe , clarsimp)
         apply (clarsimp simp: lookup_def entry_set_def split: split_if_asm , (safe ; force) , force)
         apply auto [1]
         apply (rule_tac x = x in exI)
         apply (safe ; force)
        apply (clarsimp simp: lookup_def entry_set_def split: split_if_asm ; force)
       apply ((drule lookup_not_hit_false ; clarsimp) +) [2]
     apply (drule lookup_union_hit_miss_hit ; clarsimp)
    apply (drule lookup_not_hit_miss ; clarsimp)
   apply (drule lookup_union_hit_miss_hit ; clarsimp)
  by (drule lookup_hit_miss_or_hit' ; clarsimp)




lemma  not_elem_rewrite:
  "(ASID b, bb)
                \<notin> (\<lambda>x. (ASID b, addr_val x)) `
                   {va. \<not> is_fault (pt_walk (ASID b) (MEM b) (TTBR0 b) va) \<and> \<not> is_fault (pt_walk (ASID b) (MEM bc) (TTBR0 b) va) \<and> pt_walk (ASID b) (MEM b) (TTBR0 b) va \<noteq> pt_walk (ASID b) (MEM bc) (TTBR0 b) va \<or>
                        \<not> is_fault (pt_walk (ASID b) (MEM b) (TTBR0 b) va) \<and> is_fault (pt_walk (ASID b) (MEM bc) (TTBR0 b) va)} \<Longrightarrow>
   (is_fault (pt_walk (ASID b) (MEM b) (TTBR0 b) (Addr bb)) \<or> is_fault (pt_walk (ASID b) (MEM bc) (TTBR0 b) (Addr bb)) \<or> pt_walk (ASID b) (MEM b) (TTBR0 b) (Addr bb) = pt_walk (ASID b) (MEM bc) (TTBR0 b) (Addr bb)) \<and>
            (is_fault (pt_walk (ASID b) (MEM b) (TTBR0 b) (Addr bb)) \<or> \<not> is_fault (pt_walk (ASID b) (MEM bc) (TTBR0 b) (Addr bb)))  "
  by force



theorem entry_range_single_element':
  "{E \<in> t. \<not> is_fault E \<and> (a, v) \<in> entry_range_asid_tags E} = {x} \<Longrightarrow> (a, v) \<in> entry_range_asid_tags x \<and> \<not> is_fault x 
         \<and> (\<forall>y\<in>t. y\<noteq>x \<and> \<not> is_fault y \<longrightarrow> (a, v) \<notin> entry_range_asid_tags y)" 
   by force


theorem entry_range_single_elementI':
  "\<lbrakk>x\<in> t ; \<not> is_fault x ; (a, v) \<in> entry_range_asid_tags x ; (\<forall>y\<in>t. y\<noteq>x \<longrightarrow> (a, v) \<notin> entry_range_asid_tags y) \<rbrakk> \<Longrightarrow> 
         {E \<in> t. \<not> is_fault E \<and> (a, v) \<in> entry_range_asid_tags E} = {x}" 
   by force


lemma lookup_range_pt_walk_hit_no_flt:
  "\<not> is_fault (pt_walk asid mem ttbr0 (Addr va)) \<Longrightarrow> 
        lookup {e \<in> range (pt_walk asid mem ttbr0). \<not> is_fault e} asid va = Hit (pt_walk asid mem ttbr0 (Addr va)) "
  apply (clarsimp simp: lookup_def)
  apply safe
    apply simp
   apply (subgoal_tac "x = pt_walk asid mem ttbr0 (Addr va)" , force)
   apply (clarsimp simp: entry_set_def)
   apply (drule entry_range_single_element')
   apply safe
   apply (unfold Ball_def) [1]
   apply (erule_tac x = "pt_walk asid mem ttbr0 (Addr va)" in allE)
   apply (clarsimp simp: asid_va_entry_range_pt_entry)
  apply (rule_tac x = "pt_walk asid mem ttbr0 (Addr va)" in exI)
  apply (clarsimp simp: entry_set_def)
  apply (rule entry_range_single_elementI')
     apply force
    apply (clarsimp simp: asid_va_entry_range_pt_entry)
   apply (clarsimp simp: asid_va_entry_range_pt_entry)
  apply safe
  apply (drule va_entry_set_pt_palk_same , simp)
done

lemma lookup_no_flt_range_pt_walk_not_incon:
  "lookup {e \<in> range (pt_walk asid mem ttbr0). \<not> is_fault e} asid va \<noteq> Incon"
  apply (case_tac "\<not>is_fault (pt_walk asid mem ttbr0 (Addr va))" )
   apply (clarsimp simp: lookup_range_pt_walk_hit_no_flt)
  apply clarsimp
  apply (clarsimp simp: lookup_def entry_set_def split: split_if_asm)
  using va_entry_set_pt_palk_same apply force
 done

lemma write_asid_incon_set_rel_no_flt:
  "\<lbrakk> saturated_no_flt (typ_sat_no_flt_tlb b) ;  no_faults (tlb_sat_no_flt_set b) ; 
       asid_va_incon (tlb_sat_no_flt_set b) \<subseteq> tlb_incon_set' ba ;  asid_va_hit_incon (typ_sat_no_flt_tlb b) \<subseteq> tlb_incon_set' ba\<rbrakk> \<Longrightarrow>
      asid_va_incon (tlb_sat_no_flt_set b \<union> {e \<in> range (pt_walk (ASID b) (MEM bc) (TTBR0 b)). \<not> is_fault e}) \<subseteq>
              tlb_incon_set' ba \<union> pde_comp' (ASID b) (MEM b) (MEM bc) (TTBR0 b)"
  apply (clarsimp simp: asid_va_incon_def pde_comp'_def  asid_va_hit_incon_def)
  apply (case_tac "a = ASID b" , clarsimp)
   prefer 2
   apply (drule union_incon_cases1)
   apply (erule disjE , force)
   apply (erule disjE)
    apply (drule_tac bb = bb and bc = bc in asid_unequal_miss' , clarsimp)
   apply (erule disjE)
    apply (drule_tac bb = bb and bc = bc in asid_unequal_miss' , clarsimp)
   apply (erule disjE , force)
   apply (erule disjE)
    apply (drule_tac bb = bb and bc = bc in asid_unequal_miss' , clarsimp)
   apply force
  apply (drule union_incon_cases1 , clarsimp)
  apply (erule disjE)
   apply force
  apply (erule disjE)
   apply clarsimp
   apply (drule not_elem_rewrite)
   apply clarsimp
   apply (case_tac "x = pt_walk (ASID b) (MEM b) (TTBR0 b) (Addr bb)")
    prefer 2
    apply force
   apply (clarsimp simp:)
   apply (erule disjE)
    apply (clarsimp simp: no_faults_def)
   apply (erule disjE)
    apply (clarsimp simp: no_faults_def)
   apply clarsimp
   apply (clarsimp simp: lookup_def split:split_if_asm)
   apply (subgoal_tac "(ASID b , bb) \<in> entry_range_asid_tags (pt_walk (ASID b) (MEM bc) (TTBR0 b) xb)")
    prefer 2
    apply (clarsimp simp: entry_set_hit_entry_range)
   apply (drule va_entry_set_pt_palk_same , clarsimp)
  apply (erule disjE , clarsimp simp: lookup_no_flt_range_pt_walk_not_incon)
  apply (erule disjE , force)
  apply (erule disjE)
   apply (clarsimp simp: lookup_no_flt_range_pt_walk_not_incon)
  apply force
done



lemma  lookup_miss_is_fault:
  "lookup {e \<in> range (pt_walk a m r). \<not> is_fault e} a v = Miss \<Longrightarrow> is_fault (pt_walk a m r (Addr v))"
  apply (clarsimp simp: lookup_def entry_set_def split: split_if_asm)
  by (drule_tac x = "pt_walk a m r (Addr v)" in spec, clarsimp simp: asid_va_entry_range_pt_entry)



lemma lookup_range_fault_pt_walk:
  "\<lbrakk>lookup {e \<in> range (pt_walk a m r). \<not> is_fault e} a v = Hit x\<rbrakk>  \<Longrightarrow>  \<forall>va\<in> entry_range x. x = pt_walk a m r (Addr va)"
  apply (subgoal_tac "x \<in> {e \<in> range (pt_walk a m r). \<not> is_fault e}")
   prefer 2
   using  lookup_in_tlb apply force
  apply clarsimp
  apply (rule va_entry_set_pt_palk_same)
  by (clarsimp simp: entry_range_asid_tags_def)



lemma  lookup_hit_entry_range:
  "lookup t a va = Hit x \<Longrightarrow> va \<in> entry_range x"
  apply (clarsimp simp: lookup_def  entry_set_def entry_range_asid_tags_def  split:split_if_asm)
  by force

lemma  write_asid_incon_set_rel_no_flt':
  "\<lbrakk> saturated_no_flt (typ_sat_no_flt_tlb b) ;  no_faults (tlb_sat_no_flt_set b) ; ASID bb = ASID b; MEM bb = MEM bc; TTBR0 bb = TTBR0 b ;
       asid_va_incon (tlb_sat_no_flt_set b) \<subseteq> tlb_incon_set' ba ;  asid_va_hit_incon (typ_sat_no_flt_tlb b) \<subseteq> tlb_incon_set' ba\<rbrakk> \<Longrightarrow>
      asid_va_hit_incon (typ_sat_no_flt_tlb (bb\<lparr>tlb_sat_no_flt_set := tlb_sat_no_flt_set b \<union> {e \<in> range (pt_walk (ASID b) (MEM bc) (TTBR0 b)). \<not> is_fault e}\<rparr>)) \<subseteq> 
             tlb_incon_set' ba \<union> pde_comp' (ASID b) (MEM b) (MEM bc) (TTBR0 b)"
  apply (clarsimp simp: asid_va_hit_incon_def pde_comp'_def  asid_va_incon_def)
  apply (drule not_elem_rewrite)
  apply clarsimp
  apply (drule lookup_hit_union_cases')
  apply (erule_tac P = " lookup (tlb_sat_no_flt_set b) (ASID b) bd = Hit x \<and> lookup {e \<in> range (pt_walk (ASID b) (MEM bc) (TTBR0 b)). \<not> is_fault e} (ASID b) bd = Miss " in  disjE)
   apply clarsimp
   apply (case_tac "x = pt_walk (ASID b) (MEM b) (TTBR0 b) (Addr bd)")
    prefer 2
    apply force
   apply (clarsimp simp:)
   apply (subgoal_tac "\<not>is_fault (pt_walk (ASID b) (MEM b) (TTBR0 b) (Addr bd))")
    prefer 2
    apply (subgoal_tac "pt_walk (ASID b) (MEM b) (TTBR0 b) (Addr bd) \<in> tlb_sat_no_flt_set b")
     prefer 2
     apply (clarsimp simp: lookup_in_tlb)
    apply (clarsimp simp: saturated_no_flt_def no_faults_def)
   apply (erule disjE)
    apply clarsimp
   apply (erule_tac P = " is_fault (pt_walk (ASID b) (MEM b) (TTBR0 b) (Addr bd)) " in disjE)
    apply clarsimp
   apply (subgoal_tac "is_fault (pt_walk (ASID b) (MEM bc) (TTBR0 b) (Addr bd))")
    apply clarsimp
   apply (clarsimp simp: lookup_miss_is_fault)
  apply (erule_tac P = "lookup {e \<in> range (pt_walk (ASID b) (MEM bc) (TTBR0 b)). \<not> is_fault e} (ASID b) bd = Hit x \<and> lookup (tlb_sat_no_flt_set b) (ASID b) bd = Miss" in  disjE)
   apply (clarsimp)
   apply (subgoal_tac " x = pt_walk (ASID b) (MEM bc) (TTBR0 b) (Addr bd)")
    apply clarsimp
    apply (frule lookup_range_fault_pt_walk)
    apply (drule_tac x = "bd" in bspec)
    apply (clarsimp simp: lookup_hit_entry_range)
    apply clarsimp
  apply (clarsimp simp:)
  apply (case_tac "x = pt_walk (ASID b) (MEM b) (TTBR0 b) (Addr bd)")
   prefer 2
   apply force
  apply (clarsimp simp:)
  apply (subgoal_tac "\<not>is_fault (pt_walk (ASID b) (MEM b) (TTBR0 b) (Addr bd))")
   prefer 2
   apply (subgoal_tac "pt_walk (ASID b) (MEM b) (TTBR0 b) (Addr bd) \<in> tlb_sat_no_flt_set b")
    prefer 2
    apply (clarsimp simp: lookup_in_tlb)
   apply (clarsimp simp: saturated_no_flt_def no_faults_def)
  apply (erule disjE)
   apply clarsimp
  apply (erule_tac P = " is_fault (pt_walk (ASID b) (MEM b) (TTBR0 b) (Addr bd)) " in disjE)
   apply clarsimp
  apply (subgoal_tac "is_fault (pt_walk (ASID b) (MEM bc) (TTBR0 b) (Addr bd))")
   apply clarsimp
  apply (clarsimp simp: lookup_miss_is_fault)
done



lemma write_refinement_saturated_incon_only:        
  "\<lbrakk> mmu_write_size (val,va, sz) s = ((), s'); (ASID t, addr_val va) \<notin> (tlb_incon_set' t); saturated_no_flt (typ_sat_no_flt_tlb s);
           no_faults (tlb_sat_no_flt_set s); tlb_rel_abs' (typ_sat_no_flt_tlb s) (typ_incon' t) ;  mmu_write_size (val,va, sz) t = ((), t') \<rbrakk> \<Longrightarrow> 
                                 tlb_rel_abs' (typ_sat_no_flt_tlb s') (typ_incon' t')"  
  apply (frule_tac s = s in tlb_rel_abs_consistent' ; clarsimp )
  apply (frule_tac tlb_rel'_absD , clarsimp)
  apply (clarsimp simp:  mmu_write_size_tlb_sat_no_flt_state_ext_def  mmu_write_size_tlb_incon_state'_ext_def)
  apply (cases "mmu_translate va s" ,cases "mmu_translate va t" , clarsimp)
  apply (frule_tac t=t and pa'= aa and t' = ba in   mmu_translate_sat_no_flt_abs_refine)  apply clarsimp+
  apply (clarsimp simp: tlb_rel_abs'_def)
  apply (subgoal_tac "exception b = exception ba")
   prefer 2 apply (case_tac b , case_tac ba , clarsimp simp: state.defs)
  apply (clarsimp split: split_if_asm)
  apply (case_tac "write'mem1 (val, aa, sz) b " , case_tac "write'mem1 (val, aa, sz) ba" , clarsimp)
  apply (subgoal_tac "state.truncate bb = state.truncate bc")
   prefer 2 using write_mem_state_trun_equal apply blast
  apply (rule conjI , clarsimp simp: state.defs)
  apply (subgoal_tac "MEM bb = MEM bc  \<and> MEM s = MEM b" , simp)
   apply (subgoal_tac "ASID s = ASID b \<and> TTBR0 s = TTBR0 b" , simp)
    apply (subgoal_tac "saturated_no_flt (typ_sat_no_flt_tlb b)")
     prefer 2
     using mmu_translate_sat_sat_no_fault apply blast
    apply (subgoal_tac "no_faults (tlb_sat_no_flt_set b)")
     prefer 2
     using mmu_translate_sat_sat_no_fault' apply blast
    prefer 2
    using mmu_sat_no_flt_eq_ASID_TTBR0_MEM apply blast
   prefer 2
   apply (rule conjI)
    apply (clarsimp simp: state.defs)
   using mmu_sat_no_flt_eq_ASID_TTBR0_MEM
   apply blast
  apply (simp only: asid_va_incon_tlb_mem_def)
  apply simp
  apply (rule conjI)
   apply (drule_tac b = b and ba = ba and bc = bc in write_asid_incon_set_rel_no_flt ; clarsimp)
  apply (frule_tac bb = bb and bc = bc and ba = ba and b = b in  write_asid_incon_set_rel_no_flt' ; clarsimp simp: write'mem1_eq_ASID_TTBR0)
done



end