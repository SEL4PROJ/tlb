theory MMU_ARMv7_Ref

imports MMU_ARM.ARM_Monadic

begin               


record tlb_state = state + 
           tlb_set :: "tlb_entry set "


record tlb_det_state = state + 
           tlb_det_set :: "tlb_entry set"

record tlb_sat_state = state + 
           tlb_sat_set :: "tlb_entry set"


record tlb_incon_state = state + 
           tlb_incon_set :: "(asid \<times> va) set"

                 
definition 
  typ_tlb :: "'a tlb_state_scheme \<Rightarrow> tlb_entry set state_scheme"
where
  "typ_tlb s =  state.extend (state.truncate s) (tlb_set s)"


definition 
  typ_det_tlb :: "'a tlb_det_state_scheme \<Rightarrow> tlb_entry set state_scheme"
where
  "typ_det_tlb s =  state.extend (state.truncate s) (tlb_det_set s)"


definition 
  typ_sat_tlb :: "'a tlb_sat_state_scheme \<Rightarrow> tlb_entry set state_scheme"
where
  "typ_sat_tlb s =  state.extend (state.truncate s) (tlb_sat_set s)"


definition 
  typ_incon :: "'a tlb_incon_state_scheme \<Rightarrow> (asid \<times> va) set state_scheme"
where
  "typ_incon s =  state.extend (state.truncate s) (tlb_incon_set s)"


lemma tlb_more [simp]:
  "state.more (typ_tlb s) = tlb_set s"
  by (clarsimp simp: typ_tlb_def state.defs)


lemma tlb_det_more [simp]:
  "state.more (typ_det_tlb s) = tlb_det_set s"
  by (clarsimp simp: typ_det_tlb_def state.defs)


lemma tlb_sat_more [simp]:
  "state.more (typ_sat_tlb s) = tlb_sat_set s"
  by (clarsimp simp: typ_sat_tlb_def state.defs)

lemma tlb_incon_more [simp]:
  "state.more (typ_incon s) = tlb_incon_set s"
  by (clarsimp simp: typ_incon_def state.defs)

lemma tlb_truncate [simp]:
  "state.truncate (typ_tlb s') = state.truncate s'"
  by (clarsimp simp: typ_tlb_def state.defs)

lemma tlb_det_truncate [simp]:
  "state.truncate (typ_det_tlb s') = state.truncate s'"
  by (clarsimp simp: typ_det_tlb_def state.defs)

lemma tlb_sat_truncate [simp]:
  "state.truncate (typ_sat_tlb s') = state.truncate s'"
  by (clarsimp simp: typ_sat_tlb_def state.defs)

lemma tlb_incon_truncate [simp]:
  "state.truncate (typ_incon s') = state.truncate s'"
  by (clarsimp simp: typ_incon_def state.defs)


lemma typ_prim_parameter [simp]:
  "ASID (typ_tlb s) = ASID s \<and> TTBR0 (typ_tlb s) =  TTBR0 s \<and> MEM (typ_tlb s) = MEM s \<and>
      exception (typ_tlb s) = exception s"
  by (clarsimp simp: typ_tlb_def  state.defs)


lemma typ_det_prim_parameter [simp]:
  "ASID (typ_det_tlb s) = ASID s \<and> TTBR0 (typ_det_tlb s) =  TTBR0 s \<and> MEM (typ_det_tlb s) = MEM s \<and>
      exception (typ_det_tlb s) = exception s"
  by (clarsimp simp: typ_det_tlb_def state.defs)


lemma typ_sat_prim_parameter [simp]:
  "ASID (typ_sat_tlb s) = ASID s \<and> TTBR0 (typ_sat_tlb s) =  TTBR0 s \<and> MEM (typ_sat_tlb s) = MEM s \<and>
      exception (typ_sat_tlb s) = exception s"
  by (clarsimp simp: typ_sat_tlb_def state.defs)


lemma typ_incon_prim_parameter [simp]:
  "ASID (typ_incon s) = ASID s \<and> TTBR0 (typ_incon s) =  TTBR0 s \<and> MEM (typ_incon s) = MEM s \<and>
      exception (typ_incon s) = exception s"
  by (clarsimp simp: typ_incon_def state.defs)


definition
  "consistent0 m asid ttbr0 tlb va \<equiv>
     lookup tlb asid (addr_val va) = Hit (pt_walk asid m ttbr0 va) \<or>
     lookup tlb asid (addr_val va) = Miss"


abbreviation
  "consistent (s::tlb_entry set state_scheme) \<equiv>
               consistent0 (MEM s) (ASID s) (TTBR0 s) (state.more s)"

(* TLB doesn't store page faults in this level of the model *)
definition
  "no_faults tlb = (\<forall>e \<in> tlb. \<not>is_fault e)"


definition 
   asid_va_incon :: "tlb \<Rightarrow> (asid \<times> va) set"
where                                                         
  "asid_va_incon tlb  \<equiv>  {(asid, va). lookup tlb asid va = Incon}"
       
definition
  saturated :: "tlb_entry set state_scheme \<Rightarrow> bool"
where
  "saturated s  \<equiv> pt_walk (ASID s) (MEM s) (TTBR0 s) ` UNIV \<subseteq> state.more s"

definition
  tlb_rel :: "tlb_entry set state_scheme \<Rightarrow> tlb_entry set state_scheme \<Rightarrow> bool"
where
  "tlb_rel s t \<equiv> state.truncate s = state.truncate t \<and> state.more s \<subseteq> state.more t \<and> no_faults (state.more t)"

definition
  tlb_rel_flt :: "tlb_entry set state_scheme \<Rightarrow> tlb_entry set state_scheme \<Rightarrow> bool"
where
  "tlb_rel_flt s t \<equiv> state.truncate s = state.truncate t \<and> state.more s \<subseteq> state.more t"


definition 
  tlb_rel_sat :: "tlb_entry set state_scheme \<Rightarrow> tlb_entry set state_scheme \<Rightarrow> bool"
where                                                                
  "tlb_rel_sat s t \<equiv> state.truncate s = state.truncate t \<and> state.more s \<subseteq> state.more t \<and> saturated t"
      
      
definition 
  tlb_rel_abs :: "tlb_entry set state_scheme \<Rightarrow> (asid \<times> va) set state_scheme \<Rightarrow> bool"
where                                                                
  "tlb_rel_abs s t \<equiv> state.truncate s = state.truncate t \<and> asid_va_incon (state.more s) \<subseteq> state.more t"


consts tlb_evict :: "tlb_entry set state_scheme \<Rightarrow> tlb_entry set"



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
          case lookup tlb asid (addr_val v) of
            Hit entry \<Rightarrow> if is_fault entry
              then raise'exception(PAGE_FAULT ''more info'') 
                else return (Addr (va_to_pa (addr_val v) entry))
          | Miss \<Rightarrow> let entry = pt_walk asid mem ttbr0 v in
              if is_fault entry
                then raise'exception (PAGE_FAULT ''more info'')
                  else do {
                    update_state (\<lambda>s. s\<lparr> tlb_set := tlb \<union> {entry} \<rparr>);
                    return (Addr (va_to_pa (addr_val v) entry))
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
          case lookup tlb asid (addr_val v) of
            Hit entry \<Rightarrow> if is_fault entry
              then raise'exception(PAGE_FAULT ''more info'') 
                else return (Addr (va_to_pa (addr_val v) entry))
          | Miss \<Rightarrow> let entry = pt_walk asid mem ttbr0 v in
              if is_fault entry
                then raise'exception (PAGE_FAULT ''more info'')
                  else do {
                    update_state (\<lambda>s. s\<lparr> tlb_det_set := tlb \<union> {entry} \<rparr>);
                    return (Addr (va_to_pa (addr_val v) entry))
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
     let all_entries = pt_walk asid mem ttbr0 ` UNIV;
     tlb0   <- read_state tlb_sat_set;
     let tlb = tlb0 \<union> all_entries;
     update_state (\<lambda>s. s\<lparr> tlb_sat_set := tlb \<rparr>);
          case lookup tlb asid (addr_val v) of
            Hit entry \<Rightarrow> if is_fault entry 
              then raise'exception (PAGE_FAULT ''more info'')
                else return (Addr (va_to_pa (addr_val v) entry))
          | Miss \<Rightarrow> raise'exception (ASSERT ''impossible'')
          | Incon \<Rightarrow> raise'exception (IMPLEMENTATION_DEFINED ''set on fire'')
   }" 
   
  instance ..
end

thm  mmu_translate_tlb_sat_state_ext_def

instantiation tlb_incon_state_ext :: (type) mmu    
begin
definition   
 "(mmu_translate v :: ('a tlb_incon_state_scheme \<Rightarrow> _))
  = do {
     mem   <- read_state MEM;
     asid  <- read_state ASID;
     ttbr0 <- read_state TTBR0;
     incon_set <- read_state tlb_incon_set;
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

(* thm arg_cong
thm state.cases_scheme  *)


(* TLB consistency for an address va: if we look up va, the result is not Incon, 
   and if it is Hit, then it agrees with the page table *)

lemma consistent_not_Incon:
  "consistent0 m asid ttbr0 tlb va = 
  (lookup tlb asid (addr_val va) \<noteq> Incon \<and> (\<forall>e. lookup tlb asid (addr_val va) = Hit e \<longrightarrow> e = pt_walk asid m ttbr0 va))"
  by (cases "lookup tlb asid (addr_val va)"; simp add: consistent0_def)


lemma tlb_relD:
  "tlb_rel s t \<Longrightarrow> ASID t = ASID s \<and> MEM t = MEM s \<and> TTBR0 t = TTBR0 s \<and>
      state.more s \<subseteq> state.more t \<and> exception t = exception s"
  by (clarsimp simp: tlb_rel_def state.defs)

lemma tlb_rel_consistent:
  "\<lbrakk> tlb_rel s t; consistent t va \<rbrakk> \<Longrightarrow> 
          consistent s va"
  apply (drule tlb_relD)
  apply clarsimp
  apply (drule tlb_mono [of _ _ "ASID s" "(addr_val va)"])
  by (auto simp: consistent0_def less_eq_lookup_type typ_det_tlb_def state.defs)


lemma tlb_rel_fltD:
  "tlb_rel_flt s t \<Longrightarrow>
     ASID t = ASID s \<and> MEM t = MEM s \<and> TTBR0 t = TTBR0 s \<and>  state.more s \<subseteq> state.more t \<and> exception t = exception s"
   by (clarsimp simp: tlb_rel_flt_def state.defs)

lemma tlb_rel_flt_consistent:
  "\<lbrakk> tlb_rel_flt s t; consistent t va \<rbrakk> \<Longrightarrow> consistent s va"
  apply (drule tlb_rel_fltD)
  apply clarsimp
  apply (drule tlb_mono [of _ _ "ASID s" "addr_val va"])
  apply (auto simp: consistent0_def less_eq_lookup_type)
done


lemma tlb_rel_satD:
  "tlb_rel_sat s t \<Longrightarrow>
      ASID t = ASID s \<and> MEM t = MEM s \<and> TTBR0 t = TTBR0 s \<and>  state.more s \<subseteq>  state.more t \<and> exception t = exception s"
  by (clarsimp simp: tlb_rel_sat_def state.defs)

lemma sat_state_tlb:
  "\<lbrakk>saturated s \<rbrakk> \<Longrightarrow> 
     state.more s = state.more s \<union> pt_walk (ASID s) (MEM s) (TTBR0 s) ` UNIV"
  by (fastforce simp: saturated_def)


lemma tlb_rel_sat_consistent:
  "\<lbrakk> tlb_rel_sat s t; consistent t va \<rbrakk> \<Longrightarrow> consistent s va"
  apply (drule tlb_rel_satD)
  apply clarsimp
  apply (drule tlb_mono [of _ _ "ASID s" "(addr_val va)"])
  apply (auto simp: consistent0_def less_eq_lookup_type)
  done



(*find_theorems consistent
  thm consistent_tlb_state_ext_def
  help*)

lemma lookup_in_tlb:
  "lookup tlb asid va = Hit e \<Longrightarrow> e \<in> tlb"
  by (auto simp: lookup_def entry_set_def split: if_split_asm)

lemma entry_set_insert:
  "\<lbrakk> entry_set tlb asid va = {}; asid_entry e = asid; va \<in> entry_range e \<rbrakk> \<Longrightarrow> 
  entry_set (insert e tlb) asid va = {e}"
  by (auto simp add: entry_set_def entry_range_asid_tags_def)

lemma asid_entry_pt_walk [simp]:
  "asid_entry (pt_walk asid m ttbr0 va) = asid"
  apply (simp add: pt_walk_def Let_def)
  apply ((((cases "get_pde m ttbr0 va" ; clarsimp) , case_tac a ; clarsimp) , 
      case_tac "get_pte m x3 va" ; clarsimp) , case_tac a ; clarsimp)
  done

lemma va_20_left [simp]:
  fixes va :: "32 word"
  shows "ucast (ucast (va >> 20) :: 12 word) << 20 \<le> va"
  by word_bitwise

lemma va_12_left [simp]:
  fixes va :: "32 word"
  shows "ucast (ucast (va >> 12) :: 20 word) << 12 \<le> va"
  by word_bitwise

lemma va_20_right [simp]:
  fixes va :: "32 word"
  shows "va \<le> (ucast (ucast (va >> 20) :: 12 word) << 20) + 0x000FFFFF"
  by word_bitwise

lemma va_12_right [simp]:
  fixes va :: "32 word"
  shows "va \<le> (ucast (ucast (va >> 12) :: 20 word) << 12) + 0x00000FFF"
  by word_bitwise

lemma asid_entry_range [simp, intro!]:
  "addr_val va \<in> entry_range (pt_walk asid m ttbr0 va)"
  apply (clarsimp simp: entry_range_def pt_walk_def Let_def)
  by ((((cases "get_pde m ttbr0 va" ; clarsimp) , case_tac a ; clarsimp) , 
      case_tac "get_pte m x3 va" ; clarsimp) , case_tac a ; clarsimp)

lemma asid_entry_range1 [simp, intro!]:
  "va \<in> entry_range (pt_walk asid m ttbr0 (Addr va))"
  apply (clarsimp simp: entry_range_def pt_walk_def Let_def)
  by ((((cases "get_pde m ttbr0 (Addr va)" ; clarsimp) , case_tac a ; clarsimp) , 
      case_tac "get_pte m x3 (Addr va)" ; clarsimp) , case_tac a ; clarsimp)


lemma lookup_refill:
  "lookup tlb asid (addr_val va) = Miss \<Longrightarrow>
   lookup (insert (pt_walk asid m ttrb0 va) tlb) asid (addr_val va) = Hit (pt_walk asid m ttrb0 va)"
   by (clarsimp simp: lookup_def entry_set_insert [where e="pt_walk asid m ttrb0 va"] split: if_split_asm)


lemma consistent_insert [simp, intro!]:
  "lookup tlb asid (addr_val va) = Miss \<Longrightarrow>
  consistent0 m asid ttrb0 (insert (pt_walk asid m ttrb0 va) tlb) va"
  by (simp add: consistent0_def lookup_refill)



lemma sat_state_lookup_not_miss:
  "\<lbrakk>saturated s\<rbrakk> \<Longrightarrow> \<forall>va. lookup (state.more s) (ASID s) va \<noteq> Miss"
  apply (clarsimp simp: saturated_def)
  apply (clarsimp simp: lookup_def split:if_split_asm)
  apply (subgoal_tac "pt_walk (ASID s) (MEM s) (TTBR0 s) (Addr va) \<in>  range (pt_walk (ASID s) (MEM s) (TTBR0 s))")
   prefer 2
   apply simp
  apply (subgoal_tac "pt_walk (ASID s) (MEM s) (TTBR0 s) (Addr va) \<in> state.more s")
   prefer 2
   apply fastforce
  apply (subgoal_tac "va \<in> entry_range (pt_walk (ASID s) (MEM s) (TTBR0 s) (Addr va) )")
   prefer 2
   apply (clarsimp)
  apply (subgoal_tac "entry_set (state.more s) (ASID s) va \<noteq> {}")
   apply simp
  apply (clarsimp simp: entry_set_def entry_range_asid_tags_def)
  apply force
   done

lemma sat_con_not_miss_incon:
  "\<lbrakk>saturated s ; consistent s va\<rbrakk> \<Longrightarrow> 
    (lookup (state.more s) (ASID s) (addr_val va) \<noteq> Incon \<and> lookup (state.more s) (ASID s) (addr_val va) \<noteq> Miss \<and>
       (\<forall>e. lookup (state.more s) (ASID s) (addr_val va) = Hit e \<longrightarrow> e = pt_walk (ASID s) (MEM s) (TTBR0 s) va))"
  apply (frule sat_state_lookup_not_miss)
  apply (clarsimp simp:consistent_not_Incon)
  done


find_theorems mmu_translate

thm state.defs [simp]



declare return_def [simp add]
declare bind_def [simp add]
declare read_state_def [simp add]
declare update_state_def [simp add]
declare extend_state_def [simp add]
declare trim_state_def [simp add]


(* refinement between two deterministic TLB lookups, tlb_rel states that TLBs don't store page faults  *)
lemma  mmu_translate_det_refine:
  "\<lbrakk> mmu_translate va s = (pa, s'); consistent (typ_det_tlb t) va;  tlb_rel (typ_det_tlb s) (typ_det_tlb t) \<rbrakk> \<Longrightarrow>
     let (pa', t') = mmu_translate va t
         in pa' = pa \<and> consistent (typ_det_tlb t') va \<and> tlb_rel (typ_det_tlb s') (typ_det_tlb t')"
  apply (frule (1) tlb_rel_consistent , clarsimp)
  apply (frule tlb_relD , clarsimp)
  apply (subgoal_tac "lookup (tlb_det_set s) (ASID s) (addr_val va) \<le> lookup (tlb_det_set t) (ASID s) (addr_val va)")
   prefer 2
   apply (simp add: tlb_mono)
  apply (clarsimp simp: mmu_translate_tlb_det_state_ext_def split_def Let_def  split: if_split_asm )
  apply (cases "lookup (tlb_det_set t) (ASID s) (addr_val va)")
    apply clarsimp
    apply (simp add: Let_def raise'exception_def typ_det_tlb_def state.defs tlb_rel_def split: if_split_asm )
     apply (cases s, cases t, clarsimp)
    apply (cases s, cases t)
    apply (clarsimp simp: no_faults_def)
    apply fastforce
   apply (simp add: consistent0_def )
  apply clarsimp
  apply (cases "lookup (tlb_det_set s) (ASID s) (addr_val va)"; clarsimp)
   apply (simp add: consistent0_def Let_def tlb_rel_def no_faults_def
                    lookup_in_tlb split: if_split_asm)
   apply clarsimp
   apply (drule lookup_in_tlb)
   apply (simp add: typ_det_tlb_def state.defs)
  apply (clarsimp split: if_split_asm simp: tlb_rel_def no_faults_def)
  using lookup_in_tlb apply blast
done


(* refinement between eviction and deterministic TLB lookups *)
lemma 
  "\<lbrakk> mmu_translate va s = (pa, s');  consistent (typ_det_tlb t) va; tlb_rel (typ_tlb s) (typ_det_tlb t) \<rbrakk> \<Longrightarrow>
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
  apply (clarsimp simp: mmu_translate_tlb_state_ext_def mmu_translate_tlb_det_state_ext_def split_def Let_def split: if_split_asm)
  apply (cases "lookup (tlb_det_set t) (ASID s) (addr_val va)")
    apply clarsimp
    apply (simp add: Let_def raise'exception_def typ_det_tlb_def typ_tlb_def state.defs tlb_rel_def split: if_split_asm)
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
                     lookup_in_tlb split: if_split_asm)
   apply clarsimp
   apply (drule lookup_in_tlb)
   apply (simp add: typ_det_tlb_def state.defs)
  apply (clarsimp split: if_split_asm simp: tlb_rel_def typ_tlb_def typ_det_tlb_def state.defs no_faults_def)
   using lookup_in_tlb apply blast
  using lookup_in_tlb apply blast
done


(* refinement between two deterministic TLB lookups, tlb_rel_flt states that TLBs store page faults  *)
lemma mmu_translate_det_flt_refine:
  "\<lbrakk> mmu_translate va s = (pa, s'); consistent (typ_det_tlb t) va; tlb_rel_flt (typ_det_tlb s) (typ_det_tlb t) \<rbrakk> \<Longrightarrow>
    let (pa', t') = mmu_translate va t
      in pa' = pa \<and> consistent (typ_det_tlb t') va \<and> tlb_rel_flt (typ_det_tlb s') (typ_det_tlb t')"
  apply (frule (1) tlb_rel_flt_consistent)
  apply (frule tlb_rel_fltD)
  apply (subgoal_tac "lookup (tlb_det_set s) (ASID s) (addr_val va) \<le> lookup (tlb_det_set t) (ASID s) (addr_val va)")
   prefer 2
   apply (simp add: tlb_mono)
  apply (clarsimp simp: mmu_translate_tlb_det_state_ext_def split_def Let_def)
  apply (cases "lookup (tlb_det_set t) (ASID s) (addr_val va)")
    apply clarsimp
    apply (simp add: Let_def raise'exception_def typ_det_tlb_def state.defs tlb_rel_flt_def split: if_split_asm)
     apply (clarsimp simp: tlb_rel_flt_def)
    apply (cases s, cases t, clarsimp) apply blast
   apply (clarsimp simp: consistent0_def)
  apply (clarsimp)
  apply (cases "lookup (tlb_det_set s) (ASID s) (addr_val va)"; clarsimp)
   apply (clarsimp simp: consistent0_def Let_def tlb_rel_flt_def
                         lookup_in_tlb raise'exception_def split: if_split_asm)
    apply (cases s, cases t, clarsimp simp: state.defs)
   apply (cases s, cases t, clarsimp simp: state.defs)
  apply (clarsimp split: if_split_asm simp:raise'exception_def tlb_rel_flt_def)
  apply (cases s, cases t, clarsimp simp: state.defs)
done

(* refinement between eviction and deterministic TLB lookups *)
lemma mmu_translate_flt_refine_det:
  "\<lbrakk> mmu_translate va s = (pa, s');  consistent (typ_det_tlb t) va; tlb_rel_flt (typ_tlb s) (typ_det_tlb t) \<rbrakk> \<Longrightarrow>
    let (pa', t') = mmu_translate va t
     in pa' = pa  \<and> consistent (typ_det_tlb t') va \<and> tlb_rel_flt (typ_tlb s') (typ_det_tlb t')"
  apply (frule (1) tlb_rel_flt_consistent , clarsimp)
  apply (frule tlb_rel_fltD , clarsimp)
  apply (subgoal_tac "tlb_set s - tlb_evict (typ_tlb s) \<subseteq> tlb_set s")
   prefer 2
   apply blast
  apply (subgoal_tac "lookup (tlb_set s - tlb_evict (typ_tlb s)) (ASID s) (addr_val va) \<le> lookup (tlb_det_set t) (ASID s) (addr_val va)")
   prefer 2
   apply (simp add: tlb_mono)
  apply (clarsimp simp: mmu_translate_tlb_state_ext_def mmu_translate_tlb_det_state_ext_def split_def Let_def)
  apply (cases "lookup (tlb_det_set t) (ASID s) (addr_val va)")
    apply clarsimp
    apply (simp add: Let_def raise'exception_def typ_det_tlb_def typ_tlb_def state.defs tlb_rel_flt_def split: if_split_asm)
      apply (cases s, cases t, clarsimp simp: no_faults_def)
      apply fastforce
     apply (cases s, cases t ,clarsimp simp: no_faults_def)
     apply fastforce
    apply (cases s, cases t, clarsimp simp: no_faults_def)
    apply fastforce
   apply (clarsimp simp: consistent0_def)
  apply (clarsimp)
  apply (cases "lookup (tlb_set s - tlb_evict (typ_tlb s)) (ASID s) (addr_val va)"; clarsimp)
   apply (clarsimp simp: consistent0_def Let_def tlb_rel_flt_def
                         lookup_in_tlb raise'exception_def split: if_split_asm)
     apply (cases s, cases t, clarsimp simp: state.defs) apply blast
    apply (cases s, cases t, clarsimp simp: state.defs) apply blast
   apply (cases s, cases t, clarsimp simp: state.defs) apply blast
  apply (clarsimp split:if_split_asm)
   apply (clarsimp simp: raise'exception_def tlb_rel_flt_def typ_tlb_def typ_det_tlb_def state.defs split: if_split_asm)
    using lookup_in_tlb apply blast
   using lookup_in_tlb apply blast
  apply (clarsimp simp: tlb_rel_flt_def typ_tlb_def typ_det_tlb_def state.defs)
  using lookup_in_tlb apply blast
done


lemma sat_states_parameters:
  "\<lbrakk> mmu_translate va t = (pa', t') ; saturated (typ_sat_tlb t) \<rbrakk> \<Longrightarrow>
      state.more t' = state.more t \<and> ASID t' = ASID t \<and> MEM t' = MEM t \<and> TTBR0 t' = TTBR0 t \<and> saturated (typ_sat_tlb t')"
  apply (frule sat_state_tlb)
  apply (clarsimp simp: mmu_translate_tlb_sat_state_ext_def Let_def saturated_def)
  apply (cases "lookup (tlb_sat_set t) (ASID t) (addr_val va)" )
    apply (clarsimp simp: raise'exception_def split:if_split_asm)+
  done

(* state doesn't change in reading a non_page_fault entry through a saturated state *)
lemma const_sat_state:
  "\<lbrakk>saturated (typ_sat_tlb s) ; consistent (typ_sat_tlb s) va ; \<not>is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) va) ;
      mmu_translate va s = (pa , s') \<rbrakk> \<Longrightarrow>   s = s' "
  apply (frule sat_con_not_miss_incon , simp)
  apply (clarsimp simp: mmu_translate_tlb_sat_state_ext_def split_def Let_def)
  apply (frule sat_state_tlb ; clarsimp)
  apply (cases "lookup (tlb_sat_set s) (ASID s) (addr_val va)")
    apply clarsimp 
   apply clarsimp
  apply (clarsimp split:if_split_asm simp:raise'exception_def)
  done


lemma saturated_no_excpetion:
  "\<lbrakk>saturated (typ_sat_tlb s) ; consistent (typ_sat_tlb s) va; mmu_translate va s = (pa , s');
     is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) va) ; exception s = NoException\<rbrakk> \<Longrightarrow> 
       s' = s\<lparr>exception := PAGE_FAULT ''more info'' \<rparr> "
  apply (frule sat_con_not_miss_incon , simp)
  apply (clarsimp simp: mmu_translate_tlb_sat_state_ext_def split_def Let_def)
   apply (frule sat_state_tlb ; clarsimp) 
   apply (cases "lookup (tlb_sat_set s) (ASID s) (addr_val va)")
    apply clarsimp
   apply clarsimp
  apply clarsimp
  apply (simp add: Let_def raise'exception_def)
  done



lemma lookup_miss_sat_hit:
  "\<lbrakk> lookup (tlb_det_set s) (ASID s) (addr_val va) = Miss ; tlb_rel_sat (typ_det_tlb s) (typ_sat_tlb t) ; consistent (typ_sat_tlb t) va\<rbrakk> \<Longrightarrow>
        lookup (tlb_sat_set t) (ASID t) (addr_val va)= Hit (pt_walk (ASID s) (MEM s) (TTBR0 s) va)"
   apply (frule tlb_rel_satD)
   apply (clarsimp simp: tlb_rel_sat_def)
   apply (drule sat_state_lookup_not_miss)
   apply (clarsimp simp: consistent0_def)
   done


lemma det1_miss_sat_pa:
  "\<lbrakk>lookup (tlb_det_set s) (ASID s) (addr_val va) = Miss ;  mmu_translate va s = (pa, s') ; tlb_rel_sat (typ_det_tlb s) (typ_sat_tlb t) ;
       consistent (typ_sat_tlb t) va ; mmu_translate va t = (pa', t') \<rbrakk> \<Longrightarrow>  pa' = pa"
  apply (frule (2) lookup_miss_sat_hit)
  apply (frule tlb_rel_satD)
  apply (simp add: tlb_rel_sat_def , clarsimp)
  apply (frule sat_state_tlb , clarsimp)
  apply (clarsimp simp: mmu_translate_tlb_det_state_ext_def
                        mmu_translate_tlb_sat_state_ext_def Let_def raise'exception_def split: if_split_asm)
done


lemma state_change_is_fault_sat:
  "\<lbrakk>saturated (typ_sat_tlb s) ; consistent (typ_sat_tlb s) va ; is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) va) ;
      mmu_translate va s = (pa , s') \<rbrakk> \<Longrightarrow> 
          raise'exception (PAGE_FAULT ''more info'') s = (pa, s') "
  apply (frule sat_con_not_miss_incon , simp)
  apply (clarsimp simp:  mmu_translate_tlb_sat_state_ext_def split_def Let_def)
  apply (frule sat_state_tlb ; clarsimp)
  apply (cases "lookup (tlb_sat_set s) (ASID s) (addr_val va)")
    apply clarsimp
   apply clarsimp
  apply (clarsimp split: if_split_asm simp:raise'exception_def)
  done


lemma lookup_hit_sat_hit:
  "\<lbrakk> lookup (tlb_det_set s) (ASID s) (addr_val va) = Hit x ; tlb_rel_sat (typ_det_tlb s) (typ_sat_tlb t) ; consistent (typ_sat_tlb t) va\<rbrakk> \<Longrightarrow>
        lookup (tlb_sat_set t) (ASID t) (addr_val va) = Hit (pt_walk (ASID s) (MEM s) (TTBR0 s) va)"
  apply (frule tlb_rel_satD , safe)
  apply (clarsimp simp: tlb_rel_sat_def)
  apply (frule sat_con_not_miss_incon , simp)
  apply (clarsimp simp: consistent0_def)
  done

lemma lookup_hit_sat_unsat_equal:
  "\<lbrakk> lookup (tlb_det_set s) (ASID s) (addr_val va) = Hit x ; tlb_rel_sat (typ_det_tlb s) (typ_sat_tlb t) ; consistent (typ_sat_tlb t) va\<rbrakk> \<Longrightarrow>
        x = pt_walk (ASID s) (MEM s) (TTBR0 s) va"
  apply (frule (2) lookup_hit_sat_hit)
  apply (frule tlb_rel_satD)
  apply (clarsimp simp: tlb_rel_sat_def)
  apply (frule tlb_mono [of _ _ "ASID s" "(addr_val va)"])
  apply clarsimp
  done


lemma det1_hit_sat_pa:
  "\<lbrakk>lookup (tlb_det_set s) (ASID s) (addr_val va) = Hit (pt_walk (ASID s) (MEM s) (TTBR0 s) va) ;  
      mmu_translate va s = (pa, s') ;  tlb_rel_sat (typ_det_tlb s) (typ_sat_tlb t) ; consistent (typ_sat_tlb t) va ; 
        mmu_translate va t = (pa', t') \<rbrakk> \<Longrightarrow> pa' = pa"
  apply (frule (2) lookup_hit_sat_hit)
  apply (frule tlb_rel_satD)
  apply (simp add: tlb_rel_sat_def , clarsimp)
  apply (frule sat_state_tlb , clarsimp)
  apply (clarsimp simp: mmu_translate_tlb_det_state_ext_def
                        mmu_translate_tlb_sat_state_ext_def Let_def raise'exception_def split: if_split_asm)
done

lemma lookup_incon_subset [simp]:
  "\<lbrakk> s \<subseteq> t ; lookup s a va = Incon \<rbrakk> \<Longrightarrow> 
       lookup t a va = Incon"
  by (metis less_eq_lookup_type lookup_type.simps(3) tlb_mono)


lemma lookup_incon_saturated :
  "\<lbrakk>lookup (tlb_det_set s) (ASID s) va = Incon ; tlb_rel_sat (typ_det_tlb s) (typ_sat_tlb t) \<rbrakk> \<Longrightarrow> 
       lookup (tlb_sat_set t) (ASID t) va = Incon"
   by (frule tlb_rel_satD , clarsimp)


lemma
  "\<lbrakk>lookup (tlb_det_set s) (ASID s) (addr_val va) = Incon ;  
      mmu_translate va s = (pa, s') ;  tlb_rel_sat (typ_det_tlb s) (typ_sat_tlb t); 
        mmu_translate va t = (pa', t') \<rbrakk> \<Longrightarrow> exception s' = exception t'"
  apply (frule lookup_incon_saturated , simp)
  apply (frule tlb_rel_satD)
  apply (simp add: tlb_rel_sat_def , clarsimp)
  apply (frule sat_state_tlb)
  apply (clarsimp simp: mmu_translate_tlb_det_state_ext_def
                        mmu_translate_tlb_sat_state_ext_def Let_def  
                  split: if_split_asm simp add:raise'exception_def)
done


lemma lookup_miss_tlb_subset1:
  "\<lbrakk>lookup (tlb_det_set s) (ASID s) (addr_val va) = Miss ; \<not>is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) va) ;
     mmu_translate va s = (pa, s') \<rbrakk> \<Longrightarrow> 
              tlb_det_set s' = tlb_det_set s \<union> {pt_walk (ASID s) (MEM s) (TTBR0 s) va} "
  by (clarsimp simp add: mmu_translate_tlb_det_state_ext_def Let_def)
  

lemma  lookup_miss_tlb_subset2:
  "\<lbrakk>lookup (tlb_det_set s) (ASID s) (addr_val va) = Miss ; is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) va) ;
     mmu_translate va s = (pa, s') \<rbrakk> \<Longrightarrow> 
              tlb_det_set s' = tlb_det_set s "
  apply (clarsimp simp add: mmu_translate_tlb_det_state_ext_def Let_def)
  apply (clarsimp simp:raise'exception_def split: if_split_asm)
done
  
lemma lookup_miss_tlb_subset:
  "\<lbrakk>lookup (tlb_det_set s) (ASID s) (addr_val va) = Miss ; mmu_translate va s = (pa, s')\<rbrakk> \<Longrightarrow> 
           tlb_det_set s' = tlb_det_set s  \<or> tlb_det_set s' = tlb_det_set s \<union> {pt_walk (ASID s) (MEM s) (TTBR0 s) va} "
  apply (cases "is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) va)" )
   apply (drule (2) lookup_miss_tlb_subset2 , clarsimp)
  apply (drule (2) lookup_miss_tlb_subset1 , clarsimp)
done 

lemma lookup_incon_tlb_equal:
  "\<lbrakk>lookup (tlb_det_set s) (ASID s) (addr_val va) = Incon ; mmu_translate va s = (pa, s')  \<rbrakk> \<Longrightarrow> 
        tlb_det_set s' = tlb_det_set s"
  by (clarsimp simp add: mmu_translate_tlb_det_state_ext_def Let_def raise'exception_def split:if_split_asm)
 

lemma lookup_hit_tlb_equal:
  "\<lbrakk>lookup (tlb_det_set s) (ASID s) (addr_val va) = Hit x ; mmu_translate va s = (pa, s') \<rbrakk> \<Longrightarrow>  tlb_det_set s' = tlb_det_set s "
  by (clarsimp simp add: mmu_translate_tlb_det_state_ext_def Let_def raise'exception_def split:if_split_asm)

(* important *)
lemma mmu_translate_tlbs_rel:
  "\<lbrakk> mmu_translate va s = (pa, s') \<rbrakk> \<Longrightarrow>
       tlb_det_set s' = tlb_det_set s \<or>  tlb_det_set s' = tlb_det_set s \<union> {pt_walk (ASID s) (MEM s) (TTBR0 s) va} "
  apply (cases "lookup (tlb_det_set s) (ASID s) (addr_val va)")
    apply (drule (2)lookup_miss_tlb_subset)
   apply (rule disjI1)
   apply (drule (2) lookup_incon_tlb_equal)
  apply (rule disjI1)
  apply (drule (2) lookup_hit_tlb_equal)
done  

(* important *)
lemma mmu_translate_det_sat_refine:
  "\<lbrakk> mmu_translate va s = (pa, s'); consistent (typ_sat_tlb t) va; tlb_rel_sat (typ_det_tlb s) (typ_sat_tlb t)  \<rbrakk> \<Longrightarrow>
  let (pa', t') = mmu_translate va t
  in pa' = pa \<and> consistent (typ_sat_tlb t') va \<and> tlb_rel_sat (typ_det_tlb s') (typ_sat_tlb t')"
  apply (frule (1) tlb_rel_sat_consistent , clarsimp)
  apply (frule tlb_rel_satD , clarsimp)
  apply (subgoal_tac "lookup (tlb_det_set s) (ASID s) (addr_val va) \<le> lookup (tlb_sat_set t \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s))) (ASID s) (addr_val va)")
   prefer 2
   apply (simp add: saturated_def sup.absorb1 tlb_mono tlb_rel_sat_def)
  apply (clarsimp simp: mmu_translate_tlb_det_state_ext_def
                        mmu_translate_tlb_sat_state_ext_def split_def Let_def)
  apply (subgoal_tac "tlb_sat_set t = tlb_sat_set t \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s))")
   prefer 2
   apply (fastforce simp: tlb_rel_sat_def saturated_def)
  apply (cases "lookup (tlb_sat_set t \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s))) (ASID s) (addr_val va)")
    apply (clarsimp simp: tlb_rel_sat_def)
    apply (frule sat_state_lookup_not_miss , clarsimp)
   apply (clarsimp simp:consistent0_def)
  apply (clarsimp)
  apply (cases "lookup (tlb_det_set s) (ASID s) (addr_val va)"; clarsimp)
   apply (clarsimp simp: consistent0_def Let_def tlb_rel_sat_def typ_sat_tlb_def typ_det_tlb_def state.defs
                         lookup_in_tlb raise'exception_def split: if_split_asm)
   apply (cases s, cases t, clarsimp simp:saturated_def)
  apply (clarsimp split: if_split_asm simp:raise'exception_def tlb_rel_sat_def  typ_sat_tlb_def typ_det_tlb_def state.defs)
  apply (cases s, cases t, clarsimp simp:saturated_def)
done

(* important *)
lemma  mmu_translate_sat_refine_non_det:        
  "\<lbrakk> mmu_translate va s = (pa, s'); consistent (typ_sat_tlb t) va; tlb_rel_sat (typ_tlb s) (typ_sat_tlb t) \<rbrakk> \<Longrightarrow>
       let (pa', t') = mmu_translate va t
                 in pa' = pa  \<and> consistent (typ_sat_tlb t') va \<and> tlb_rel_sat (typ_tlb s') (typ_sat_tlb t')"
  apply (frule (1) tlb_rel_sat_consistent , clarsimp)
  apply (frule tlb_rel_satD , clarsimp)
  apply (subgoal_tac "tlb_set s - tlb_evict (typ_tlb s) \<subseteq> tlb_set s")
   prefer 2
   apply blast
  apply (subgoal_tac "lookup (tlb_set s - tlb_evict (typ_tlb s)) (ASID s) (addr_val va) \<le> lookup (tlb_sat_set t \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s))) (ASID s) (addr_val va)")
   prefer 2
   apply (simp add: saturated_def sup.absorb1 tlb_mono tlb_rel_sat_def)
  apply (clarsimp simp: mmu_translate_tlb_state_ext_def
                        mmu_translate_tlb_sat_state_ext_def split_def Let_def)
  apply (subgoal_tac "tlb_sat_set t = tlb_sat_set t \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s))")
   prefer 2
   apply (fastforce simp: tlb_rel_sat_def saturated_def)
  apply (cases "lookup (tlb_sat_set t \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s))) (ASID s) (addr_val va)")
    apply (clarsimp simp: tlb_rel_sat_def)
    apply (frule sat_state_lookup_not_miss , clarsimp)
   apply (clarsimp simp:consistent0_def)
  apply (clarsimp)
  apply (cases "lookup (tlb_set s - tlb_evict (typ_tlb s)) (ASID s) (addr_val va)"; clarsimp)
   apply (clarsimp simp: consistent0_def Let_def tlb_rel_sat_def typ_sat_tlb_def typ_tlb_def state.defs
                         lookup_in_tlb raise'exception_def split: if_split_asm)
     apply (cases s, cases t, clarsimp simp:saturated_def) apply blast
    apply (cases s, cases t, clarsimp simp:saturated_def) apply blast
   apply (cases s, cases t, clarsimp simp:saturated_def) apply blast
  apply (clarsimp split: if_split_asm simp:raise'exception_def tlb_rel_sat_def typ_sat_tlb_def typ_tlb_def state.defs)
    apply (cases s, cases t, clarsimp simp:saturated_def)
    using lookup_in_tlb apply blast+
done



lemma mmu_translate_det_sat_pa:
  "\<lbrakk> mmu_translate va s = (pa, s'); consistent (typ_sat_tlb t) va; tlb_rel_sat (typ_det_tlb s) (typ_sat_tlb t) ;
         mmu_translate va t = (pa', t')  \<rbrakk> \<Longrightarrow> pa = pa'"
  apply (frule (1) tlb_rel_sat_consistent , clarsimp)
  apply (frule tlb_rel_satD , clarsimp)
  apply (subgoal_tac "lookup (tlb_det_set s) (ASID s) (addr_val va) \<le> lookup (tlb_sat_set t \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s))) (ASID s) (addr_val va)")
   prefer 2
   apply (simp add: saturated_def sup.absorb1 tlb_mono tlb_rel_sat_def)
  apply (clarsimp simp: mmu_translate_tlb_det_state_ext_def
                        mmu_translate_tlb_sat_state_ext_def split_def Let_def)
  apply (subgoal_tac "tlb_sat_set t = tlb_sat_set t \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s))")
   prefer 2
   apply (fastforce simp: tlb_rel_sat_def saturated_def)
  apply (cases "lookup (tlb_sat_set t \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s))) (ASID s) (addr_val va)")
    apply (clarsimp simp: tlb_rel_sat_def)
    apply (frule sat_state_lookup_not_miss , clarsimp)
   apply (clarsimp simp:consistent0_def)
  apply (clarsimp)
  apply (cases "lookup (tlb_det_set s) (ASID s) (addr_val va)"; clarsimp)
   apply (clarsimp simp: consistent0_def Let_def tlb_rel_sat_def
                         lookup_in_tlb raise'exception_def split: if_split_asm)
   apply (cases s, cases t, clarsimp simp:saturated_def)
  apply (clarsimp split: if_split_asm simp:raise'exception_def tlb_rel_sat_def)
done


lemma mmu_translate_sat_TLB_union:
  "mmu_translate v s = (p,t) \<Longrightarrow> 
      tlb_sat_set t = tlb_sat_set s \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s))"
  apply (clarsimp simp:  mmu_translate_tlb_sat_state_ext_def Let_def)
  apply (cases "lookup (tlb_sat_set s \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s))) (ASID s) (addr_val v)")
    apply (clarsimp simp:raise'exception_def split:if_split_asm) +
done

lemma mmu_translate_sat_sat:
  "saturated (typ_sat_tlb (snd (mmu_translate va s)))"
 apply (clarsimp simp: mmu_translate_tlb_sat_state_ext_def Let_def split:lookup_type.splits; safe)
  by (clarsimp simp: saturated_def raise'exception_def split:if_split_asm)+
    

lemma mmu_translate_sat_sat':
  "mmu_translate v s = (p,t) \<Longrightarrow>  saturated (typ_sat_tlb t)"
  apply (clarsimp simp: mmu_translate_tlb_sat_state_ext_def Let_def)
  apply (cases "lookup (tlb_sat_set s \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s))) (ASID s) (addr_val v)")
    apply (clarsimp simp: saturated_def raise'exception_def split:if_split_asm)+
done


lemma saturated_not_miss:
  "lookup (state.more s \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s))) (ASID s) (addr_val (v::vaddr)) \<noteq> Miss"
  apply clarsimp
  apply (clarsimp simp: lookup_def split:if_split_asm)
  apply (subgoal_tac "entry_set (range (pt_walk (ASID s) (MEM s) (TTBR0 s))) (ASID s) (addr_val v) \<noteq> {}")
   using entry_set_def apply fastforce[1]
  apply (clarsimp simp: entry_set_def)
  apply (rule_tac x = "pt_walk (ASID s) (MEM s) (TTBR0 s) v" in exI)
  apply (clarsimp simp: entry_range_asid_tags_def)
done



definition
  ptable_walk' :: "vaddr \<Rightarrow> 'a state_scheme\<Rightarrow> paddr \<times> 'a state_scheme" 
where
  "ptable_walk' v  \<equiv> do {
    mem   <- read_state MEM;
    ttbr0 <- read_state TTBR0;
    asid  <- read_state ASID;
    let entry = pt_walk asid mem ttbr0 v in
              if is_fault entry
                then raise'exception (PAGE_FAULT ''more info'')
                  else return (Addr (va_to_pa (addr_val v) entry))
     }"



(* IMPORTANT *)

lemma  mmu_translate_sat_implies_pt_walk:
  "\<lbrakk>mmu_translate v s = (p, t) ; ptable_walk' v s = (p', t') ;
           consistent (typ_sat_tlb t) v \<rbrakk>  \<Longrightarrow> p = p'"
  apply (clarsimp simp:consistent_not_Incon)
  apply (frule mmu_translate_sat_TLB_union)
  apply (subgoal_tac "ASID s = ASID t \<and> TTBR0 s = TTBR0 t \<and> MEM s = MEM t")
   prefer 2
   apply (clarsimp simp: mmu_translate_tlb_sat_state_ext_def Let_def)
   apply (cases "lookup (tlb_sat_set s \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s))) (ASID s) (addr_val v)";
            clarsimp simp : raise'exception_def split: if_split_asm)
  apply (subgoal_tac "lookup (tlb_sat_set s) (ASID s) (addr_val v) \<le>
            lookup (tlb_sat_set s \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s))) (ASID s) (addr_val v)")
   prefer 2
   apply (simp add: tlb_mono)
  apply (subgoal_tac "lookup (tlb_sat_set s) (ASID s) (addr_val v) \<noteq> Incon")
   prefer 2
   using less_eq_lookup_type apply force
  apply (subgoal_tac "consistent (typ_sat_tlb s) v")
   prefer 2
   apply (clarsimp simp: consistent0_def)
   apply (clarsimp simp: lookup_def Let_def split:if_split_asm)
  apply (clarsimp simp: mmu_translate_tlb_sat_state_ext_def Let_def)
  apply (cases "lookup (tlb_sat_set s \<union> range (pt_walk (ASID t) (MEM t) (TTBR0 t))) (ASID t) (addr_val v)")
    apply (metis (no_types, lifting) saturated_not_miss tlb_sat_more typ_sat_prim_parameter)
   apply simp
  apply (clarsimp simp: ptable_walk'_def Let_def raise'exception_def split: if_split_asm)
  done



lemma write'mem1_eq_TLB:
  "\<lbrakk> write'mem1 (val, va, sz) s = ((), s') \<rbrakk>  \<Longrightarrow> state.more s' = state.more s"
   by (clarsimp simp: write'mem1_def raise'exception_def split: if_split_asm)

lemma mmu_sat_rel:
  "\<lbrakk> mmu_translate va s = (p, s') \<rbrakk>  \<Longrightarrow> s' = s \<lparr> tlb_sat_set := tlb_sat_set s' , exception:= exception s' \<rparr>"
  apply (clarsimp simp: mmu_translate_tlb_sat_state_ext_def Let_def  split:lookup_type.splits)
    apply (clarsimp simp: raise'exception_def split:if_split_asm)+
done


lemma mmu_det_rel:
  "\<lbrakk> mmu_translate va s = (p, s') \<rbrakk>  \<Longrightarrow> s' = s \<lparr> tlb_det_set := tlb_det_set s' , exception:= exception s' \<rparr>"
  apply (clarsimp simp: mmu_translate_tlb_det_state_ext_def Let_def  split:lookup_type.splits)
    apply (clarsimp simp: raise'exception_def split:if_split_asm)+
done


lemma mmu_rel:
  "\<lbrakk> mmu_translate va s = (p, s') \<rbrakk>  \<Longrightarrow> s' = s \<lparr> tlb_set := tlb_set s' , exception:= exception s' \<rparr>"
  apply (clarsimp simp: mmu_translate_tlb_state_ext_def Let_def  split:lookup_type.splits)
    apply (clarsimp simp: raise'exception_def split:if_split_asm)+
done


lemma write'mem1_eq_ASID_TTBR0:
  "\<lbrakk> write'mem1 (val, va, sz) s = ((), s') \<rbrakk>  \<Longrightarrow> ASID s' = ASID s \<and> TTBR0 s' = TTBR0 s"
   by (clarsimp simp: write'mem1_def raise'exception_def split: if_split_asm)
  
lemma mmu_incon_eq_ASID_TTBR0_MEM:
  "\<lbrakk> mmu_translate va (s::'a tlb_incon_state_scheme) = (pa , s') \<rbrakk>  \<Longrightarrow> ASID s = ASID s' \<and> TTBR0 s = TTBR0 s' \<and>
                      MEM s = MEM s'"
   apply (clarsimp simp: mmu_translate_tlb_incon_state_ext_def Let_def split: if_split_asm)
   by (clarsimp simp:raise'exception_def split: if_split_asm)+


lemma mmu_sat_eq_ASID_TTBR0_MEM:
  "\<lbrakk> mmu_translate va (s::'a tlb_sat_state_scheme) = (pa , s') \<rbrakk>  \<Longrightarrow> ASID s = ASID s' \<and> TTBR0 s = TTBR0 s' \<and>
                      MEM s = MEM s'"
   apply (clarsimp simp: mmu_translate_tlb_sat_state_ext_def Let_def)
   apply (cases "lookup (tlb_sat_set s \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s))) (ASID s) (addr_val va) ")
   by (clarsimp simp:raise'exception_def split: if_split_asm)+

lemma mmu_det_eq_ASID_TTBR0_MEM:
  "\<lbrakk> mmu_translate va (s::'a tlb_det_state_scheme) = (pa , s') \<rbrakk>  \<Longrightarrow> ASID s = ASID s' \<and> TTBR0 s = TTBR0 s' \<and>
                      MEM s = MEM s'"
   apply (clarsimp simp: mmu_translate_tlb_det_state_ext_def Let_def)
   apply (cases "lookup (tlb_det_set s) (ASID s) (addr_val va) ")
   by (clarsimp simp:Let_def raise'exception_def split: if_split_asm)+
  


lemma mmu_eq_ASID_TTBR0_MEM:
  "\<lbrakk> mmu_translate va (s::'a tlb_state_scheme) = (pa , s') \<rbrakk>  \<Longrightarrow> ASID s = ASID s' \<and> TTBR0 s = TTBR0 s' \<and>
                      MEM s = MEM s'"
   apply (clarsimp simp: mmu_translate_tlb_state_ext_def Let_def)
   apply (cases "lookup (tlb_set s - tlb_evict (typ_tlb s)) (ASID s) (addr_val va) ")
   by (clarsimp simp:Let_def raise'exception_def split: if_split_asm)+
  
lemma write_same_mem:
  "\<lbrakk> write'mem1 (val, va, sz) s = ((), s') ; write'mem1 (val, va, sz) t = ((), t') ;
      MEM s = MEM t\<rbrakk>  \<Longrightarrow>  MEM s' = MEM t'"
  by (clarsimp simp: write'mem1_def raise'exception_def split:if_split_asm)

lemma write_same_mem_excep:
  "\<lbrakk> write'mem1 (val, pa, sz) s = ((), s') ; write'mem1 (val, pa, sz) t = ((), t') ;
      MEM s = MEM t ; exception s = exception t \<rbrakk>  \<Longrightarrow> exception s' = exception t'"
   apply (clarsimp simp: write'mem1_def raise'exception_def split:if_split_asm)
done

 
lemma mmu_translate_mem_excep:
  "\<lbrakk> mmu_translate va s = (p, s') ; mmu_translate va t = (p, t') ;
     consistent (typ_sat_tlb t) va; tlb_rel_sat (typ_det_tlb s) (typ_sat_tlb t)\<rbrakk>  \<Longrightarrow> MEM s' = MEM t' \<and> exception s' = exception t'"
  apply (subgoal_tac "tlb_rel_sat (typ_det_tlb s') (typ_sat_tlb t')")
   apply (clarsimp simp: tlb_rel_sat_def state.defs)
  apply (drule (2) mmu_translate_det_sat_refine, clarsimp simp: Let_def)
 done

lemma mmu_translate_mem_excep1:
  "\<lbrakk> mmu_translate va s = (p, s') ; mmu_translate va t = (p, t') ;
     consistent (typ_sat_tlb t) va; tlb_rel_sat (typ_tlb s) (typ_sat_tlb t)\<rbrakk>  \<Longrightarrow> MEM s' = MEM t' \<and> exception s' = exception t'"
  apply (subgoal_tac "tlb_rel_sat (typ_tlb s') (typ_sat_tlb t')")
   apply (clarsimp simp: tlb_rel_sat_def state.defs)
  apply (drule (2)  mmu_translate_sat_refine_non_det, clarsimp simp: Let_def)
 done

 
lemma mmu_translate_excep:
  "\<lbrakk> mmu_translate va s = (p, s') ; mmu_translate va t = (p, t') ;
     consistent (typ_sat_tlb t) va; tlb_rel_sat (typ_det_tlb s) (typ_sat_tlb t)\<rbrakk>  \<Longrightarrow>  exception s' = exception t'"
  apply (subgoal_tac "tlb_rel_sat (typ_det_tlb s') (typ_sat_tlb t')")
   apply (clarsimp simp: tlb_rel_sat_def state.defs)
  apply (drule (2) mmu_translate_det_sat_refine, clarsimp simp: Let_def)
 done



lemma mmu_translate_excep1:
  "\<lbrakk> mmu_translate va s = (p, s') ; mmu_translate va t = (p, t') ;
     consistent (typ_sat_tlb t) va; tlb_rel_sat (typ_tlb s) (typ_sat_tlb t)\<rbrakk>  \<Longrightarrow>  exception s' = exception t'"
  apply (subgoal_tac "tlb_rel_sat (typ_tlb s') (typ_sat_tlb t')")
   apply (clarsimp simp: tlb_rel_sat_def state.defs)
  apply (drule (2) mmu_translate_sat_refine_non_det, clarsimp simp: Let_def)
 done

lemma write'mem1_rel:
  "\<lbrakk> write'mem1 (val, va, sz) s = ((), s') \<rbrakk>  \<Longrightarrow> s' = s \<lparr> MEM:= MEM s' , exception:= exception s' \<rparr>"
   by (clarsimp simp: write'mem1_def raise'exception_def split: if_split_asm)

thm mem_read1_def

(*  mem instants *)

instantiation tlb_state_ext :: (type) mem_op 
begin

definition   
  "(mmu_read  :: (vaddr  \<Rightarrow>  'a tlb_state_scheme \<Rightarrow> bool list \<times>  'a tlb_state_scheme))
   \<equiv>  \<lambda>va. do {
                     pa  \<leftarrow> mmu_translate va;
                     mem1 pa
  }"

definition
 "(mmu_read_size  :: (vaddr \<times> nat \<Rightarrow>  'a tlb_state_scheme \<Rightarrow> bool list \<times>  'a tlb_state_scheme))
  \<equiv> \<lambda>(va,size). do {
                     pa  \<leftarrow> mmu_translate va;
                     mem_read1 (pa , size)
  }"

thm  mmu_read_size_tlb_state_ext_def

definition   
  "(mmu_write_size  :: (bool list \<times> vaddr \<times> nat \<Rightarrow> 'a tlb_state_scheme \<Rightarrow> unit \<times> 'a tlb_state_scheme))
   \<equiv> \<lambda>(value, vaddr, size). do {
     paddr <- mmu_translate vaddr;
     exception <- read_state exception;
     if exception = NoException 
       then  write'mem1 (value, paddr, size)
       else return ()
  }"
(* print_context *)                      
  instance ..
end

thm  mmu_write_size_tlb_state_ext_def

instantiation tlb_det_state_ext :: (type) mem_op   
begin


definition   
  "(mmu_read  :: (vaddr  \<Rightarrow>  'a tlb_det_state_scheme \<Rightarrow> bool list \<times>  'a tlb_det_state_scheme))
   \<equiv>  \<lambda>va. do {
                     pa  \<leftarrow> mmu_translate va;
                     mem1 pa
  }"

definition
 "(mmu_read_size  :: (vaddr \<times> nat \<Rightarrow>  'a tlb_det_state_scheme \<Rightarrow> bool list \<times>  'a tlb_det_state_scheme))
  \<equiv> \<lambda>(va,size). do {
                     pa  \<leftarrow> mmu_translate va;
                     mem_read1 (pa , size)
  }"

definition   
  "(mmu_write_size  :: (bool list \<times> vaddr \<times> nat \<Rightarrow> 'a tlb_det_state_scheme \<Rightarrow> unit \<times> 'a tlb_det_state_scheme))
   \<equiv> \<lambda>(value, vaddr, size). do {
     paddr <- mmu_translate vaddr;
     exception <- read_state exception;
     if exception = NoException 
       then  write'mem1 (value, paddr, size)
       else return ()
  }"
  instance ..
end

instantiation tlb_sat_state_ext :: (type) mem_op    
begin

definition   
  "(mmu_read  :: (vaddr  \<Rightarrow>  'a tlb_sat_state_scheme \<Rightarrow> bool list \<times>  'a tlb_sat_state_scheme))
   \<equiv>  \<lambda>va. do {
                     pa  \<leftarrow> mmu_translate va;
                     mem1 pa
  }"

definition
 "(mmu_read_size  :: (vaddr \<times> nat \<Rightarrow>  'a tlb_sat_state_scheme \<Rightarrow> bool list \<times>  'a tlb_sat_state_scheme))
  \<equiv> \<lambda>(va,size). do {
                     pa  \<leftarrow> mmu_translate va;
                     mem_read1 (pa , size)
  }"

definition   
  "(mmu_write_size  :: (bool list \<times> vaddr \<times> nat \<Rightarrow> 'a tlb_sat_state_scheme \<Rightarrow> unit \<times> 'a tlb_sat_state_scheme))
   \<equiv> \<lambda>(value, vaddr, size).  do {
     ttbr0 <- read_state TTBR0;
     asid <- read_state ASID;
     pa <- mmu_translate vaddr;
     tlb0  <- read_state tlb_sat_set;
     exception <- read_state exception;
     if exception = NoException 
      then do { 
           write'mem1 (value, pa, size); 
           mem1  <- read_state MEM;
           let all_entries = pt_walk asid mem1 ttbr0 ` UNIV;
           let tlb = tlb0 \<union> all_entries;  (* what about inconsistency here ? *)
           update_state (\<lambda>s. s\<lparr> tlb_sat_set := tlb \<rparr>)
          } 
      else return () 
    }"
  instance ..
end


definition 
  ptable_asid_va :: "asid \<Rightarrow> heap \<Rightarrow> ttbr0 \<Rightarrow> (asid \<times> va) set"
where
  "ptable_asid_va  asid heap ttbr0 \<equiv> \<Union>(entry_range_asid_tags `(pt_walk asid heap ttbr0 ` UNIV))"


definition 
  ptable_comp :: "asid \<Rightarrow> heap \<Rightarrow> heap \<Rightarrow> ttbr0 \<Rightarrow> (asid \<times> va) set"
where
  "ptable_comp  asid hp1 hp2 ttbr0 \<equiv> 
         (\<lambda>x. (asid, addr_val x)) ` {va. pt_walk asid hp1 ttbr0 va \<noteq> pt_walk asid hp2 ttbr0 va }"


instantiation tlb_incon_state_ext :: (type) mem_op     
begin

definition   
  "(mmu_read  :: (vaddr  \<Rightarrow>  'a tlb_incon_state_scheme \<Rightarrow> bool list \<times>  'a tlb_incon_state_scheme))
   \<equiv>  \<lambda>va. do {
                     pa  \<leftarrow> mmu_translate va;
                     mem1 pa
  }"

definition
 "(mmu_read_size  :: (vaddr \<times> nat \<Rightarrow>  'a tlb_incon_state_scheme \<Rightarrow> bool list \<times>  'a tlb_incon_state_scheme))
  \<equiv> \<lambda>(va,size). do {
                     pa  \<leftarrow> mmu_translate va;
                     mem_read1 (pa , size)
  }"


definition   
  "(mmu_write_size  :: (bool list \<times> vaddr \<times> nat \<Rightarrow> 'a tlb_incon_state_scheme \<Rightarrow> unit \<times> 'a tlb_incon_state_scheme))
   \<equiv> \<lambda>(value, vaddr, size). do {
      ttbr0 <- read_state TTBR0;
      asid  <- read_state ASID;
      mem   <- read_state MEM; 
      paddr <- mmu_translate vaddr;
      incon_set <- read_state tlb_incon_set; 
      exception <- read_state exception;
      if exception = NoException 
        then  do {
                   write'mem1 (value, paddr, size);
                   mem' <- read_state MEM;
                   ptable_asid_va <- return (ptable_comp asid mem mem' ttbr0);
                   update_state (\<lambda>s. s\<lparr> tlb_incon_set :=  incon_set \<union> ptable_asid_va \<rparr>)
            }
        else return ()
   }"

  instance ..
end


lemma write'_not_in_translation_tables_saturated11:
  "\<lbrakk>mmu_write_size (val,va,sz) s = ((), t)  \<rbrakk>  \<Longrightarrow> saturated (typ_sat_tlb t)"
  apply (clarsimp simp: mmu_write_size_tlb_sat_state_ext_def split_def Let_def)
  apply (clarsimp split: if_split_asm)
   apply (clarsimp simp: split_def)
   apply (subgoal_tac "ASID s = ASID (snd (write'mem1 (val, fst (mmu_translate va s), sz) (snd (mmu_translate va s)))) \<and>
                        TTBR0 s = TTBR0 (snd (write'mem1 (val, fst (mmu_translate va s), sz) (snd (mmu_translate va s)))) ")
    apply (clarsimp simp: saturated_def)
   apply (subgoal_tac "ASID s = ASID (snd(mmu_translate va s)) \<and> TTBR0 s = TTBR0 (snd(mmu_translate va s))")
    apply (clarsimp simp:  write'mem1_def Let_def raise'exception_def)
   apply (clarsimp simp: mmu_translate_tlb_sat_state_ext_def Let_def raise'exception_def split:lookup_type.splits)
  using mmu_translate_sat_sat' surjective_pairing by blast
  

lemma mem1_exception:
  "mem1 p b = (val, r) \<Longrightarrow>  r = b\<lparr>exception := exception r\<rparr>"
  apply (clarsimp simp: mem1_def)
  apply (cases "MEM b p")
   apply (clarsimp simp: raise'exception_def split: if_split_asm)
  apply clarsimp
done


lemma mem1_read_exception:
  "mem_read1 (a, sz) b = (val, r) \<Longrightarrow> r = b \<lparr>exception := exception r\<rparr>"
  apply (clarsimp simp: mem_read1_def)
  apply (clarsimp split: if_split_asm)
      apply (case_tac "mem1 (a r+ 0) b" , clarsimp)
      apply (clarsimp simp: mem1_exception)
     apply (case_tac "mem1 (a r+ 1) b" , clarsimp)
     apply (case_tac "mem1 (a r+ 0) ba", clarsimp)
     apply (drule mem1_exception)
     apply (drule mem1_exception)
     apply (cases b, case_tac ba, cases r ,clarsimp)
    apply (case_tac "mem1 (a r+ 3) b" , clarsimp)
    apply (case_tac "mem1 (a r+ 2) ba", clarsimp)
    apply (case_tac "mem1 (a r+ 1) baa", clarsimp)
    apply (case_tac "mem1 (a r+ 0) bb", clarsimp)
    apply (drule mem1_exception)
    apply (drule mem1_exception)
    apply (drule mem1_exception)
    apply (drule mem1_exception)
    apply (cases b, case_tac ba, case_tac baa, case_tac bb , cases r ,clarsimp)
   apply (case_tac "mem1 (a r+ 7) b" , clarsimp)
   apply (case_tac "mem1 (a r+ 6) ba", clarsimp)
   apply (case_tac "mem1 (a r+ 5) baa", clarsimp)
   apply (case_tac "mem1 (a r+ 4) bb", clarsimp)
   apply (case_tac "mem1 (a r+ 3) bc", clarsimp)
   apply (case_tac "mem1 (a r+ 2) bd", clarsimp)
   apply (case_tac "mem1 (a r+ 1) be", clarsimp)
   apply (case_tac "mem1 (a r+ 0) bf", clarsimp)
   apply (drule mem1_exception)
   apply (drule mem1_exception)
   apply (drule mem1_exception)
   apply (drule mem1_exception)
   apply (drule mem1_exception)
   apply (drule mem1_exception)
   apply (drule mem1_exception)
   apply (drule mem1_exception)
   apply (cases b, case_tac ba, case_tac baa, case_tac bb ,case_tac bc ,
                   case_tac bd ,  case_tac be ,  case_tac bf , cases r ,clarsimp)
  apply (clarsimp simp: raise'exception_def split:if_split_asm)
done


lemma pt_walk_range:
  "\<forall>va. pt_walk (ASID s) (MEM s) (TTBR0 s) va =  pt_walk (ASID s') (MEM s') (TTBR0 s') va  \<Longrightarrow> 
     pt_walk (ASID s) (MEM s) (TTBR0 s) ` UNIV = pt_walk (ASID s') (MEM s') (TTBR0 s') ` UNIV"
  by auto

lemma write_not_ptable_tlb_same:
  "\<lbrakk> mmu_write_size (val,va,sz) s = ((), s');
  \<forall>va. pt_walk (ASID s) (MEM s) (TTBR0 s) va = pt_walk (ASID s') (MEM s') (TTBR0 s') va;
  consistent (typ_sat_tlb s) v; saturated (typ_sat_tlb s) \<rbrakk> \<Longrightarrow>
    tlb_sat_set s' = tlb_sat_set s  \<and> consistent (typ_sat_tlb s') v \<and> saturated (typ_sat_tlb s')"
  apply (subgoal_tac "saturated (typ_sat_tlb s')")
   prefer 2
   apply (clarsimp simp: write'_not_in_translation_tables_saturated11)
  apply (frule pt_walk_range)
  apply (clarsimp simp: mmu_write_size_tlb_sat_state_ext_def Let_def)
  apply (cases "mmu_translate va s") apply (clarsimp split: if_split_asm)
   apply (case_tac "write'mem1 (val, a, sz) b") apply clarsimp
   apply (subgoal_tac "tlb_sat_set b = tlb_sat_set s")
    apply (subgoal_tac "ASID ba = ASID s \<and> TTBR0 ba = TTBR0 s")
     apply (clarsimp simp: saturated_def)
     apply (rule conjI)
      apply blast
     apply (clarsimp simp: consistent0_def)
     apply (subgoal_tac "tlb_sat_set s \<union> range (pt_walk (ASID s) (MEM ba) (TTBR0 s)) =
                         tlb_sat_set s")
      apply clarsimp
     apply blast
    apply (simp add: mmu_sat_eq_ASID_TTBR0_MEM write'mem1_eq_ASID_TTBR0)
   apply (simp add: mmu_translate_sat_TLB_union saturated_def sup.absorb1)
  apply (rule conjI)
   apply (metis mmu_translate_sat_TLB_union saturated_def sup.orderE tlb_sat_more typ_sat_prim_parameter)
  by (metis Un_absorb1 inf_sup_aci(5) mmu_translate_sat_TLB_union sat_states_parameters saturated_def tlb_sat_more typ_sat_prim_parameter)




lemma write_read_saturated_tlb:
  "\<lbrakk> mmu_write_size (val,va,sz) s = ((), t); mmu_read_size (va, sz) t = (val, r) \<rbrakk>  \<Longrightarrow> tlb_sat_set t = tlb_sat_set r"
  apply (cases "\<not> ptable_trace (MEM s) (TTBR0 s) va \<subseteq> \<Union>(ptable_trace (MEM s) (TTBR0 s) ` UNIV)" )
   apply (subgoal_tac "saturated (typ_sat_tlb t)")
    prefer 2
    apply (clarsimp simp: write'_not_in_translation_tables_saturated11)
   apply (clarsimp simp: mmu_read_size_tlb_sat_state_ext_def)
   apply (cases "mmu_translate va t" , clarsimp)
   apply (clarsimp simp:  mmu_translate_tlb_sat_state_ext_def Let_def)
   apply (cases "lookup (tlb_sat_set t \<union> range (pt_walk (ASID t) (MEM t) (TTBR0 t))) (ASID t) (addr_val va)")
     apply (simp only: if_split_asm raise'exception_def saturated_def, force)+
  apply simp
  apply (subgoal_tac "saturated (typ_sat_tlb t)")
   prefer 2
   apply (clarsimp simp: write'_not_in_translation_tables_saturated11)
  apply (clarsimp simp: mmu_read_size_tlb_sat_state_ext_def)
  apply (cases "mmu_translate va t" , clarsimp)
  apply (subgoal_tac "saturated (typ_sat_tlb b)")
   prefer 2
   apply (clarsimp simp: sat_states_parameters)
  apply (subgoal_tac "tlb_sat_set t = tlb_sat_set b")
   apply clarsimp
   apply (drule mem1_read_exception)
   apply (case_tac b , cases r , clarsimp)
  apply (subgoal_tac "ASID t = ASID b \<and> MEM t = MEM b \<and> TTBR0 t = TTBR0 b")
   apply (clarsimp simp: saturated_def)
   apply (subgoal_tac "tlb_sat_set b = tlb_sat_set t \<union> range (pt_walk (ASID b) (MEM b) (TTBR0 b))")
    apply (subgoal_tac "range (pt_walk (ASID b) (MEM b) (TTBR0 b)) \<subseteq> tlb_sat_set t")
     apply blast
    apply blast
   apply (clarsimp simp: mmu_translate_sat_TLB_union)
  apply (clarsimp simp: mmu_translate_tlb_sat_state_ext_def Let_def)
  apply (cases "lookup (tlb_sat_set t \<union> range (pt_walk (ASID t) (MEM t) (TTBR0 t))) (ASID t) (addr_val va)";
                clarsimp simp : raise'exception_def split: if_split_asm)
done

(* Refinement between write functions *)
(* writing to memory using saturated TLB *)


lemma write'mem'det1_TLBs1:
  "\<lbrakk> mmu_write_size (val,va, sz) s = ((), s') \<rbrakk> \<Longrightarrow>
     tlb_det_set s' = tlb_det_set s \<or>  tlb_det_set s' = tlb_det_set s \<union> {pt_walk (ASID s) (MEM s) (TTBR0 s) va}"
  apply (cases "lookup (tlb_det_set s) (ASID s) (addr_val va)")
    apply (cases " is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) va)")
     apply (rule disjI1)
     apply (clarsimp simp: mmu_write_size_tlb_det_state_ext_def mmu_translate_tlb_det_state_ext_def split_def Let_def
                           raise'exception_def write'mem1_eq_TLB split:if_split_asm)
    apply (rule disjI2)
    apply (clarsimp simp: mmu_write_size_tlb_det_state_ext_def mmu_translate_tlb_det_state_ext_def split_def Let_def raise'exception_def
                          split:if_split_asm)
    apply (drule write'mem1_eq_TLB state.defs)
    apply (cases s , cases s' ; clarsimp)
   apply (rule disjI1)
   apply (clarsimp simp:  mmu_write_size_tlb_det_state_ext_def mmu_translate_tlb_det_state_ext_def split_def Let_def raise'exception_def write'mem1_eq_TLB
                          split:if_split_asm)+
  apply (drule write'mem1_eq_TLB state.defs)
  apply (cases s , cases s' ; clarsimp)
done


lemma write'mem'sat_TLBs1:
  "\<lbrakk>mmu_write_size (val,va, sz) s = ((), s') \<rbrakk> \<Longrightarrow>
     tlb_sat_set s' = tlb_sat_set s \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s)) \<or>
     tlb_sat_set s' = tlb_sat_set s \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s)) \<union> range (pt_walk (ASID s') (MEM s') (TTBR0 s'))"
  apply (cases "exception (snd (mmu_translate va s)) \<noteq> NoException")
   apply (rule disjI1)
   apply (clarsimp simp: mmu_write_size_tlb_sat_state_ext_def Let_def split_def)
   apply (metis mmu_translate_sat_TLB_union prod.collapse)
  apply (clarsimp simp: mmu_write_size_tlb_sat_state_ext_def Let_def split_def)
  apply (subgoal_tac "tlb_sat_set (snd (write'mem1 (val, fst (mmu_translate va s), sz) (snd (mmu_translate va s)))) = tlb_sat_set (snd (mmu_translate va s))")
   apply (subgoal_tac "tlb_sat_set (snd (mmu_translate va s)) = tlb_sat_set s \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s))")
    apply (subgoal_tac "ASID (snd (write'mem1 (val, fst (mmu_translate va s), sz) (snd (mmu_translate va s)))) = ASID s \<and>
                        TTBR0 (snd (write'mem1 (val, fst (mmu_translate va s), sz) (snd (mmu_translate va s)))) = TTBR0 s")
     apply clarsimp
    apply (clarsimp simp: snd_def fst_def)
    apply (case_tac " mmu_translate va s" , clarsimp)
    apply (case_tac "write'mem1 (val, a, sz) b" , clarsimp)
    apply (subgoal_tac "ASID b = ASID s \<and> TTBR0 b = TTBR0 s")
     apply (clarsimp simp: write'mem1_eq_ASID_TTBR0)
    apply (clarsimp simp: mmu_sat_eq_ASID_TTBR0_MEM)
   apply (clarsimp simp: snd_def)
   apply (case_tac " mmu_translate va s" , clarsimp)
   apply (clarsimp simp: mmu_translate_sat_TLB_union)
  apply (clarsimp simp: snd_def fst_def)
  apply (cases "mmu_translate va s" , clarsimp)
  apply (case_tac "write'mem1 (val, a, sz) b" , clarsimp)
  apply (drule write'mem1_eq_TLB)
  apply (case_tac ba , case_tac b ; clarsimp)
done


lemma tlb_rel_write1:
  "\<lbrakk> mmu_write_size (val,va, sz) s = ((), s'); tlb_rel_sat (typ_det_tlb s) (typ_sat_tlb t) ;
       mmu_write_size (val,va, sz) t = ((), t') \<rbrakk> \<Longrightarrow> tlb_det_set s' \<subseteq> tlb_sat_set t'"
  apply (frule tlb_rel_satD)
  apply (subgoal_tac "lookup (tlb_det_set s) (ASID s) (addr_val va) \<le> lookup (tlb_sat_set t \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s))) (ASID s) (addr_val va)")
   prefer 2
   apply (simp add: saturated_def sup.absorb1 tlb_mono tlb_rel_sat_def)
  apply (frule write'mem'det1_TLBs1)
  apply (frule write'mem'sat_TLBs1)
  apply (erule disjE)
   apply (clarsimp simp: typ_det_tlb_def typ_sat_tlb_def state.defs)
   apply blast
  apply (subgoal_tac "pt_walk (ASID s) (MEM s) (TTBR0 s) va \<in> range (pt_walk (ASID t) (MEM t) (TTBR0 t))")
   apply (clarsimp simp: typ_det_tlb_def typ_sat_tlb_def state.defs)
   apply blast
  apply simp
done



lemma write_mem_det_sat_MEM11:
  "\<lbrakk> mmu_write_size (val,va, sz) s = ((), s');  tlb_rel_sat (typ_det_tlb s) (typ_sat_tlb t) ; consistent (typ_sat_tlb t) va; 
       mmu_write_size (val,va, sz) t = ((), t') \<rbrakk> \<Longrightarrow> MEM s' = MEM t'"
  apply (frule tlb_rel_satD)
  apply (clarsimp simp:  mmu_write_size_tlb_det_state_ext_def , cases "mmu_translate va s" , clarsimp)
  apply (clarsimp simp:  mmu_write_size_tlb_sat_state_ext_def , cases "mmu_translate va t" , clarsimp)
  apply (clarsimp split: if_split_asm)
     apply (case_tac "write'mem1 (val, aa, sz) ba" , clarsimp)
     apply (subgoal_tac "MEM b = MEM ba \<and> aa = a")
      apply (metis write_same_mem)
     apply (rule conjI)
      apply (clarsimp simp: mmu_sat_eq_ASID_TTBR0_MEM mmu_det_eq_ASID_TTBR0_MEM)
     apply (frule_tac s= "(typ_det_tlb s)" and va= "va" in tlb_rel_sat_consistent, clarsimp)
     apply (subgoal_tac "lookup (tlb_det_set s) (ASID s) (addr_val va) \<le> lookup (tlb_sat_set t \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s))) (ASID s) (addr_val va)")
      prefer 2
      apply (simp add: saturated_def sup.absorb1 tlb_mono tlb_rel_sat_def)
     apply (clarsimp simp:  mmu_translate_tlb_det_state_ext_def  mmu_translate_tlb_sat_state_ext_def split_def Let_def)
     apply (subgoal_tac "tlb_sat_set t = tlb_sat_set t \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s))")
      prefer 2
      apply (fastforce simp: tlb_rel_sat_def saturated_def)
     apply (cases "lookup (tlb_sat_set t \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s))) (ASID s) (addr_val va)")
       apply (clarsimp simp: tlb_rel_sat_def)
       apply (frule sat_state_lookup_not_miss , clarsimp)
      apply (clarsimp simp:consistent0_def)
     apply (clarsimp)
     apply (cases "lookup (tlb_det_set s) (ASID s) (addr_val va)"; clarsimp)
      apply (clarsimp simp: consistent0_def Let_def tlb_rel_sat_def
                            lookup_in_tlb raise'exception_def split: if_split_asm)
     apply (cases s, cases t, clarsimp simp:saturated_def)
     apply (clarsimp split: if_split_asm simp:raise'exception_def tlb_rel_sat_def)
    apply (metis mmu_translate_det_sat_pa mmu_translate_excep tlb_sat_more typ_sat_prim_parameter)
   apply (metis (mono_tags, lifting) mmu_translate_det_sat_pa mmu_translate_excep tlb_sat_more typ_sat_prim_parameter)
  by (simp add: mmu_det_eq_ASID_TTBR0_MEM sat_states_parameters tlb_rel_sat_def)
 


lemma  write'mem'det1_rel1:
  "\<lbrakk>mmu_write_size (val,va, sz) s = ((), s')\<rbrakk>   \<Longrightarrow> 
      s' = s \<lparr> tlb_det_set := tlb_det_set s' , MEM:= MEM s' , exception:= exception s' \<rparr>"
  apply (clarsimp simp:  mmu_write_size_tlb_det_state_ext_def split_def Let_def)
  apply (clarsimp split: if_split_asm)
   apply (drule write'mem1_rel)
   apply (cases "mmu_translate va s" , clarsimp)
   apply (drule mmu_det_rel)
   apply (cases s, cases s', case_tac b)
   apply clarsimp
  apply (clarsimp simp:  mmu_translate_tlb_det_state_ext_def Let_def split_def)
  apply (cases "lookup (tlb_det_set s) (ASID s) (addr_val va)")
    apply (clarsimp simp: Let_def raise'exception_def)
    apply (clarsimp simp: Let_def raise'exception_def)
   apply (clarsimp simp: Let_def raise'exception_def)
done


lemma write'mem'sat_rel1:
  "\<lbrakk>mmu_write_size (val,va, sz) s = ((), s')\<rbrakk>   \<Longrightarrow> 
      s' = s \<lparr> tlb_sat_set:= tlb_sat_set s' , MEM:= MEM s' , exception:= exception s' \<rparr>"
  apply (clarsimp simp: mmu_write_size_tlb_sat_state_ext_def Let_def)
  apply (cases "mmu_translate va s" , clarsimp)
  apply (clarsimp split: if_split_asm)
   apply (case_tac " write'mem1 (val, a, sz) b", clarsimp)
   apply (drule write'mem1_rel)
   apply (drule mmu_sat_rel)
   apply (cases s, cases s', case_tac a, case_tac b, case_tac ba)
   apply clarsimp
  apply (clarsimp simp: mmu_translate_tlb_sat_state_ext_def Let_def)
  apply (cases "lookup (tlb_sat_set s \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s))) (ASID s) (addr_val va) ")
    apply (clarsimp simp: raise'exception_def saturated_not_miss split:if_split_asm) (* this has to do *)
   apply (clarsimp simp: raise'exception_def split:if_split_asm)
  apply (clarsimp simp: raise'exception_def split:if_split_asm)
done


lemma  write'mem'_rel1:
  "\<lbrakk>mmu_write_size (val,va, sz) s = ((), s')\<rbrakk>   \<Longrightarrow> 
      s' = s \<lparr> tlb_set := tlb_set s' , MEM:= MEM s' , exception:= exception s' \<rparr>"
  apply (clarsimp simp:  mmu_write_size_tlb_state_ext_def split_def Let_def)
  apply (clarsimp split: if_split_asm)
   apply (drule write'mem1_rel)
   apply (cases "mmu_translate va s" , clarsimp)
   apply (drule mmu_rel)
   apply (cases s, cases s', case_tac b)
   apply clarsimp
  apply (clarsimp simp:  mmu_translate_tlb_state_ext_def Let_def split_def)
  apply (cases "lookup (tlb_set s - tlb_evict (typ_tlb s)) (ASID s) (addr_val va)")
    by (clarsimp simp: Let_def raise'exception_def)+
   


lemma tlb_rel_2'1:
  "\<lbrakk>mmu_write_size (val,va, sz) s = ((), s'); tlb_rel_sat (typ_det_tlb s) (typ_sat_tlb t) ; consistent (typ_sat_tlb t) va;
     mmu_write_size (val,va, sz) t = ((), t')\<rbrakk> \<Longrightarrow> state.truncate t' = state.truncate s'"
  apply (frule (3) write_mem_det_sat_MEM11)
  apply (frule tlb_rel_satD, clarsimp)
  apply (frule write'mem'det1_rel1)
  apply (rotate_tac)
  apply (frule write'mem'sat_rel1)
  apply (clarsimp simp: tlb_rel_sat_def)
  apply (subgoal_tac "exception s' = exception t'")
   apply (cases s, cases t, cases s' , cases t')
   apply (clarsimp simp: state.defs tlb_sat_state.defs)
  apply (clarsimp simp: mmu_write_size_tlb_sat_state_ext_def mmu_write_size_tlb_det_state_ext_def Let_def)
  apply (case_tac "mmu_translate va t" , case_tac "write'mem1 (val, a, sz) b" , clarsimp)
  apply (case_tac "mmu_translate va s" , clarsimp)
  apply (subgoal_tac "exception b = exception bb \<and> a = aa")
   apply (clarsimp split: if_split_asm)
   apply (subgoal_tac "MEM b = MEM bb ")
    apply (frule_tac s="bb" and s'="s'" and t = b and t' = ba in write_same_mem_excep ; clarsimp)
   apply (frule_tac s="s" and s'="bb" and t = t and t' = b in mmu_translate_mem_excep ; clarsimp simp: consistent0_def tlb_rel_sat_def)
  apply (rule conjI)
   prefer 2
   apply (subgoal_tac "lookup (tlb_det_set s) (ASID s) (addr_val va) \<le> lookup (tlb_sat_set t \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s))) (ASID s) (addr_val va)")
    prefer 2
    apply (simp add: saturated_def sup.absorb1 tlb_mono tlb_rel_sat_def)
   apply (clarsimp simp: mmu_translate_tlb_det_state_ext_def mmu_translate_tlb_sat_state_ext_def split_def Let_def)
   apply (subgoal_tac "tlb_sat_set t = tlb_sat_set t \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s))")
    prefer 2
    apply (fastforce simp: tlb_rel_sat_def saturated_def)
   apply (cases "lookup (tlb_sat_set t \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s))) (ASID s) (addr_val va)")
     apply (clarsimp simp: tlb_rel_sat_def)
     apply (frule sat_state_lookup_not_miss , clarsimp)
    apply (clarsimp simp:consistent0_def)
   apply (clarsimp)
   apply (cases "lookup (tlb_det_set s) (ASID s) (addr_val va)"; clarsimp)
    apply (clarsimp simp: consistent0_def Let_def tlb_rel_sat_def
                           lookup_in_tlb raise'exception_def split: if_split_asm)
   apply (cases s, cases t, clarsimp simp:saturated_def)
   apply (clarsimp split: if_split_asm simp:raise'exception_def tlb_rel_sat_def)
  apply (frule_tac t= "t" in mmu_translate_det_sat_pa)
     apply (clarsimp simp: consistent0_def)
    apply (clarsimp simp: tlb_rel_sat_def)
   apply auto [1]
  apply (frule_tac s = "s" and s' = "bb" and t = "t" and t' = "b" in   mmu_translate_excep ;
              clarsimp simp: tlb_rel_sat_def)
done



lemma write'mem'det1_sat_refine1:
  "\<lbrakk> mmu_write_size (val,va, sz) s = ((), s'); tlb_rel_sat (typ_det_tlb s) (typ_sat_tlb t) ; consistent (typ_sat_tlb t) va;
        mmu_write_size (val,va, sz) t = ((), t') \<rbrakk> \<Longrightarrow> tlb_rel_sat (typ_det_tlb s') (typ_sat_tlb t')"
  apply (clarsimp simp: tlb_rel_sat_def)
  apply (clarsimp simp:  write'_not_in_translation_tables_saturated11)
  apply (rule conjI)
   prefer 2                                                               
   apply (frule_tac s="s" and s'="s'" and t="t" and t'="t'" in tlb_rel_write1; clarsimp simp: tlb_rel_sat_def)
  apply (frule_tac s="s" and s'="s'" and t="t" and t'="t'" in tlb_rel_2'1; clarsimp simp: tlb_rel_sat_def)
  done



lemma write'mem'_TLBs1:
  "\<lbrakk> mmu_write_size (val,va, sz) s = ((), s') \<rbrakk> \<Longrightarrow>
     tlb_set s' = tlb_set s - tlb_evict (typ_tlb s) \<or>  tlb_set s' = tlb_set s - tlb_evict (typ_tlb s) \<union> {pt_walk (ASID s) (MEM s) (TTBR0 s) va}"
  apply (cases "lookup (tlb_set s - tlb_evict (typ_tlb s)) (ASID s) (addr_val va)")
    apply (cases " is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) va)")
     apply (rule disjI1)
     apply (clarsimp simp: mmu_write_size_tlb_state_ext_def mmu_translate_tlb_state_ext_def split_def Let_def
                           raise'exception_def write'mem1_eq_TLB split:if_split_asm)
    apply (rule disjI2)
    apply (clarsimp simp: mmu_write_size_tlb_state_ext_def mmu_translate_tlb_state_ext_def split_def Let_def raise'exception_def
                          split:if_split_asm)
    apply (drule write'mem1_eq_TLB state.defs)
    apply (cases s , cases s' ; clarsimp)
   apply (rule disjI1)
   apply (clarsimp simp:  mmu_write_size_tlb_state_ext_def mmu_translate_tlb_state_ext_def split_def Let_def raise'exception_def write'mem1_eq_TLB
                          split:if_split_asm)+
  apply (drule write'mem1_eq_TLB state.defs)
  apply (cases s , cases s' ; clarsimp)
done


lemma tlb_rel_write11:
  "\<lbrakk> mmu_write_size (val,va, sz) s = ((), s'); tlb_rel_sat (typ_tlb s) (typ_sat_tlb t) ;
       mmu_write_size (val,va, sz) t = ((), t') \<rbrakk> \<Longrightarrow> tlb_set s' \<subseteq> tlb_sat_set t'"
  apply (frule tlb_rel_satD)
  apply (subgoal_tac "lookup (tlb_set s) (ASID s) (addr_val va) \<le> lookup (tlb_sat_set t \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s))) (ASID s) (addr_val va)")
   prefer 2
   apply (simp add: saturated_def sup.absorb1 tlb_mono tlb_rel_sat_def)
  apply (frule write'mem'_TLBs1)
  apply (frule write'mem'sat_TLBs1)
  apply (erule disjE)
   apply (clarsimp simp: typ_det_tlb_def typ_sat_tlb_def state.defs)
   apply blast
  apply (subgoal_tac "pt_walk (ASID s) (MEM s) (TTBR0 s) va \<in> range (pt_walk (ASID t) (MEM t) (TTBR0 t))")
   apply (clarsimp simp: typ_det_tlb_def typ_sat_tlb_def state.defs)
   apply blast
  apply simp
done


lemma mmu_translate_sat_pa:
  "\<lbrakk> mmu_translate va s = (pa, s'); consistent (typ_sat_tlb t) va; tlb_rel_sat (typ_tlb s) (typ_sat_tlb t) ;
         mmu_translate va t = (pa', t')  \<rbrakk> \<Longrightarrow> pa = pa'"
  apply (frule (1) tlb_rel_sat_consistent , clarsimp)
  apply (frule tlb_rel_satD , clarsimp)
  apply (subgoal_tac "tlb_set s - tlb_evict (typ_tlb s) \<subseteq> tlb_set s")
   prefer 2
   apply blast
  apply (subgoal_tac "lookup (tlb_set s - tlb_evict (typ_tlb s))(ASID s) (addr_val va) \<le> lookup (tlb_sat_set t \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s))) (ASID s) (addr_val va)")
   prefer 2
   apply (simp add: saturated_def sup.absorb1 tlb_mono tlb_rel_sat_def)
  apply (clarsimp simp: mmu_translate_tlb_state_ext_def
                        mmu_translate_tlb_sat_state_ext_def split_def Let_def)
  apply (subgoal_tac "tlb_sat_set t = tlb_sat_set t \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s))")
   prefer 2
   apply (fastforce simp: tlb_rel_sat_def saturated_def)
  apply (cases "lookup (tlb_sat_set t \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s))) (ASID s) (addr_val va)")
    apply (clarsimp simp: tlb_rel_sat_def)
    apply (frule sat_state_lookup_not_miss , clarsimp)
   apply (clarsimp simp:consistent0_def)
  apply (clarsimp)
  apply (cases "lookup (tlb_set s - tlb_evict (typ_tlb s)) (ASID s) (addr_val va)"; clarsimp)
   apply (clarsimp simp: consistent0_def Let_def tlb_rel_sat_def
                         lookup_in_tlb raise'exception_def split: if_split_asm)
   apply (cases s, cases t, clarsimp simp:saturated_def)
  apply (clarsimp split: if_split_asm simp:raise'exception_def tlb_rel_sat_def)
done

lemma write_mem_sat_MEM11:
  "\<lbrakk> mmu_write_size (val,va, sz) s = ((), s');  tlb_rel_sat (typ_tlb s) (typ_sat_tlb t) ; consistent (typ_sat_tlb t) va; 
       mmu_write_size (val,va, sz) t = ((), t') \<rbrakk> \<Longrightarrow> MEM s' = MEM t'"
  apply (frule tlb_rel_satD , clarsimp)
  apply (clarsimp simp: mmu_write_size_tlb_state_ext_def , cases "mmu_translate va s" , clarsimp)
  apply (clarsimp simp: mmu_write_size_tlb_sat_state_ext_def , cases "mmu_translate va t" , clarsimp)
  apply (clarsimp split: if_split_asm)
     apply (case_tac "write'mem1 (val, aa, sz) ba" , clarsimp)
     apply (subgoal_tac "MEM b = MEM ba \<and> aa = a")
      apply (metis write_same_mem)
     apply (rule conjI)
      apply (clarsimp simp: mmu_sat_eq_ASID_TTBR0_MEM mmu_eq_ASID_TTBR0_MEM)
     apply (frule_tac s = "(typ_tlb s)" and va= "va" in tlb_rel_sat_consistent, clarsimp)
     apply (subgoal_tac "tlb_set s - tlb_evict (typ_tlb s) \<subseteq> tlb_set s")
      prefer 2
      apply blast
     apply (subgoal_tac "lookup (tlb_set s - tlb_evict (typ_tlb s))  (ASID s) (addr_val va) \<le> lookup (tlb_sat_set t \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s))) (ASID s) (addr_val va)")
      prefer 2
      apply (simp add: saturated_def sup.absorb1 tlb_mono tlb_rel_sat_def typ_tlb_def state.defs)
     apply (clarsimp simp:  mmu_translate_tlb_state_ext_def  mmu_translate_tlb_sat_state_ext_def split_def Let_def)
     apply (subgoal_tac "tlb_sat_set t = tlb_sat_set t \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s))")
      prefer 2
      apply (auto simp: tlb_rel_sat_def saturated_def state.defs) [1]
     apply (cases "lookup (tlb_sat_set t \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s))) (ASID s) (addr_val va)")
       apply (clarsimp simp: tlb_rel_sat_def)
       apply (frule sat_state_lookup_not_miss , clarsimp simp: state.defs)
      apply (clarsimp simp:consistent0_def)
     apply (clarsimp)
     apply (cases "lookup (tlb_set s - tlb_evict (typ_tlb s)) (ASID s) (addr_val va)"; clarsimp)
      apply (clarsimp simp: consistent0_def Let_def tlb_rel_sat_def
                            lookup_in_tlb raise'exception_def split: if_split_asm)
     apply (cases s, cases t, clarsimp simp:saturated_def)
     apply (clarsimp split: if_split_asm simp:raise'exception_def tlb_rel_sat_def state.defs)
    apply (metis mmu_translate_sat_pa mmu_translate_excep1 tlb_sat_more typ_sat_prim_parameter)
   apply (metis (mono_tags, lifting) mmu_translate_sat_pa mmu_translate_excep1 tlb_sat_more typ_sat_prim_parameter)
  by (simp add: mmu_eq_ASID_TTBR0_MEM sat_states_parameters tlb_rel_sat_def)
      



lemma tlb_rel_2'11:
  "\<lbrakk>mmu_write_size (val,va, sz) s = ((), s'); tlb_rel_sat (typ_tlb s) (typ_sat_tlb t) ; consistent (typ_sat_tlb t) va;
     mmu_write_size (val,va, sz) t = ((), t')\<rbrakk> \<Longrightarrow> state.truncate t' = state.truncate s'"
  apply (frule (3) write_mem_sat_MEM11)
  apply (frule tlb_rel_satD, clarsimp)
  apply (frule write'mem'_rel1)
  apply (rotate_tac)
  apply (frule write'mem'sat_rel1)
  apply (clarsimp simp: tlb_rel_sat_def)
  apply (subgoal_tac "exception s' = exception t'")
   apply (cases s, cases t, cases s' , cases t')
   apply (clarsimp simp: state.defs tlb_sat_state.defs)
  apply (clarsimp simp: mmu_write_size_tlb_sat_state_ext_def mmu_write_size_tlb_state_ext_def Let_def)
  apply (case_tac "mmu_translate va t" , case_tac "write'mem1 (val, a, sz) b" , clarsimp)
  apply (case_tac "mmu_translate va s" , clarsimp)
  apply (subgoal_tac "exception b = exception bb \<and> a = aa")
   apply (clarsimp split: if_split_asm)
   apply (subgoal_tac "MEM b = MEM bb ")
    apply (frule_tac s="bb" and s'="s'" and t = b and t' = ba in write_same_mem_excep ; clarsimp)
   apply (frule_tac s="s" and s'="bb" and t = t and t' = b in mmu_translate_mem_excep1 ; clarsimp simp: consistent0_def tlb_rel_sat_def)
  apply (rule conjI)
   prefer 2
   apply (subgoal_tac "tlb_set s - tlb_evict (typ_tlb s) \<subseteq> tlb_set s")
    prefer 2
    apply blast
   apply (subgoal_tac "lookup (tlb_set s - tlb_evict (typ_tlb s)) (ASID s) (addr_val va) \<le> lookup (tlb_sat_set t \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s))) (ASID s) (addr_val va)")
    prefer 2
    apply (simp add: saturated_def sup.absorb1 tlb_mono tlb_rel_sat_def)
   apply (clarsimp simp: mmu_translate_tlb_state_ext_def mmu_translate_tlb_sat_state_ext_def split_def Let_def)
   apply (subgoal_tac "tlb_sat_set t = tlb_sat_set t \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s))")
    prefer 2
    apply (auto simp: tlb_rel_sat_def saturated_def state.defs) [1]
   apply (cases "lookup (tlb_sat_set t \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s))) (ASID s) (addr_val va)")
     apply (clarsimp simp: tlb_rel_sat_def)
     apply (frule sat_state_lookup_not_miss , clarsimp)
    apply (clarsimp simp:consistent0_def)
   apply (clarsimp)
   apply (cases "lookup (tlb_set s - tlb_evict (typ_tlb s)) (ASID s) (addr_val va)"; clarsimp)
    apply (clarsimp simp: consistent0_def Let_def tlb_rel_sat_def
                           lookup_in_tlb raise'exception_def split: if_split_asm)
   apply (cases s, cases t, clarsimp simp:saturated_def)
   apply (clarsimp split: if_split_asm simp:raise'exception_def tlb_rel_sat_def)
  apply (frule_tac t= "t" in mmu_translate_sat_pa)
     apply (clarsimp simp: consistent0_def)
    apply (clarsimp simp: tlb_rel_sat_def)
   apply auto [1]
  apply (frule_tac s = "s" and s' = "bb" and t = "t" and t' = "b" in   mmu_translate_excep1 ;
              clarsimp simp: tlb_rel_sat_def)
done

(* important *)
lemma write'mem_sat_refine1:
  "\<lbrakk>  mmu_write_size (val,va, sz) s = ((), s'); tlb_rel_sat (typ_tlb s) (typ_sat_tlb t) ; consistent (typ_sat_tlb t) va;
         mmu_write_size (val,va, sz) t = ((), t') \<rbrakk> \<Longrightarrow> tlb_rel_sat (typ_tlb s') (typ_sat_tlb t')"
   apply (clarsimp simp: tlb_rel_sat_def)
  apply (clarsimp simp:  write'_not_in_translation_tables_saturated11)
  apply (rule conjI)
   prefer 2
   apply (frule_tac s="s" and s'="s'" and t="t" and t'="t'" in tlb_rel_write11; clarsimp simp: tlb_rel_sat_def)
  apply (frule_tac s="s" and s'="s'" and t="t" and t'="t'" in tlb_rel_2'11; clarsimp simp: tlb_rel_sat_def)
  done

thm write'mem_sat_refine1

lemma  mmu_translate_implies_pt_walk1:
  "\<lbrakk>mmu_translate v s = (p, t) ; ptable_walk' v s = (p', t') ;
           consistent (typ_sat_tlb t) v \<rbrakk>  \<Longrightarrow> p = p'"
  apply (clarsimp simp:consistent_not_Incon)
  apply (frule mmu_translate_sat_TLB_union)
  apply (subgoal_tac "ASID s = ASID t \<and> TTBR0 s = TTBR0 t \<and> MEM s = MEM t")
   prefer 2
   apply (clarsimp simp: mmu_translate_tlb_sat_state_ext_def Let_def)
   apply (cases "lookup (tlb_sat_set s \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s))) (ASID s) (addr_val v)";
            clarsimp simp : raise'exception_def split: if_split_asm)
  apply (subgoal_tac "lookup (tlb_sat_set s) (ASID s) (addr_val v) \<le>
            lookup (tlb_sat_set s \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s))) (ASID s) (addr_val v)")
   prefer 2
   apply (simp add: tlb_mono)
  apply (subgoal_tac "lookup (tlb_sat_set s) (ASID s) (addr_val v) \<noteq> Incon")
   prefer 2
   using less_eq_lookup_type apply force
  apply (subgoal_tac "consistent (typ_sat_tlb s) v")
   prefer 2
   apply (clarsimp simp: consistent0_def)
   apply (clarsimp simp: lookup_def Let_def split:if_split_asm)
  apply (clarsimp simp: mmu_translate_tlb_sat_state_ext_def Let_def)
  apply (cases "lookup (tlb_sat_set s \<union> range (pt_walk (ASID t) (MEM t) (TTBR0 t))) (ASID t) (addr_val v)")
    apply (metis (no_types, lifting) saturated_not_miss tlb_sat_more typ_sat_prim_parameter)
   apply simp
  apply (clarsimp simp: ptable_walk'_def Let_def raise'exception_def split: if_split_asm)
  done




lemma mmu_translate_abs_rel:
  "\<lbrakk>  mmu_translate va t = (pa', t')\<rbrakk>  \<Longrightarrow> (t'::'a tlb_incon_state_scheme) = t\<lparr>exception := exception t'\<rparr>"
  by (clarsimp simp: mmu_translate_tlb_incon_state_ext_def Let_def raise'exception_def split: if_split_asm)



lemma mmu_abs_rel:
  "consistent s va \<Longrightarrow> (ASID s, addr_val va) \<notin> asid_va_incon (state.more s)"
  by (clarsimp simp: consistent0_def  asid_va_incon_def state.defs)


lemma entry_set_hit_pt_walk:
  "\<lbrakk>entry_set (tlb_sat_set s) (ASID s) (addr_val va) = {x} ; saturated (typ_sat_tlb s)\<rbrakk> \<Longrightarrow>
       x = pt_walk (ASID s) (MEM s) (TTBR0 s) va"
  apply (clarsimp simp: saturated_def)
  apply (subgoal_tac "(ASID s, (addr_val va)) \<in> entry_range_asid_tags  (pt_walk (ASID s) (MEM s) (TTBR0 s) va )")
   apply (subgoal_tac "\<forall>y\<in>(tlb_sat_set s). y \<noteq> x \<longrightarrow> (ASID s, addr_val va) \<notin> entry_range_asid_tags y")
    apply (drule_tac x = "pt_walk (ASID s) (MEM s) (TTBR0 s) va" in bspec)
     apply blast
    apply clarsimp
   apply (clarsimp simp: entry_set_def ; blast)
  apply (cases "pt_walk (ASID s) (MEM s) (TTBR0 s) va")
   apply (subgoal_tac "x11 = ASID s \<and> x12 = (ucast (addr_val va >> 12)) \<and> x14 = 0")
    prefer 2
    apply (clarsimp simp:pt_walk_def)
    apply (cases "get_pde (MEM s) (TTBR0 s) va"; clarsimp)
    apply (case_tac a ; clarsimp)
    apply (case_tac "get_pte (MEM s) x3 va" ; clarsimp)
    apply (case_tac a ; clarsimp)
   apply (case_tac x13)
    apply (clarsimp simp: pt_walk_def split:option.splits)
    apply (case_tac x2 ; clarsimp)
    apply (case_tac "get_pte (MEM s) x3 va")
     apply (clarsimp simp: entry_range_asid_tags_def entry_range_def)
    apply (case_tac a ; clarsimp simp: entry_range_asid_tags_def entry_range_def)
   apply (clarsimp simp: pt_walk_def)
   apply (cases "get_pde (MEM s) (TTBR0 s) va" ; clarsimp)
   apply (case_tac aa ; clarsimp)
   apply (case_tac "get_pte (MEM s) x3 va" ; clarsimp)
   apply (case_tac aa ; clarsimp simp: entry_range_asid_tags_def entry_range_def)
  apply (case_tac x23)
   apply (clarsimp simp: pt_walk_def)
   apply (cases "get_pde (MEM s) (TTBR0 s) va")
    apply (clarsimp simp: entry_range_asid_tags_def entry_range_def)
   apply (case_tac a ; clarsimp simp: entry_range_asid_tags_def entry_range_def)
   apply (case_tac "get_pte (MEM s) x3 va" ; clarsimp)
   apply (case_tac a ; clarsimp)
  apply (clarsimp simp: pt_walk_def)
  apply (cases "get_pde (MEM s) (TTBR0 s) va" ; clarsimp)
  apply (case_tac aa ; clarsimp)
   apply (case_tac "get_pte (MEM s) x3 va" ; clarsimp)
   apply (case_tac aa ; clarsimp)
  apply (clarsimp simp: entry_range_asid_tags_def entry_range_def)
done

lemma entry_set_hit_pt_walk1:
  "\<lbrakk>entry_set (tlb_sat_set s) (ASID s) va = {x} ; saturated (typ_sat_tlb s)\<rbrakk> \<Longrightarrow>
       x = pt_walk (ASID s) (MEM s) (TTBR0 s) (Addr va)"
  apply (clarsimp simp: saturated_def)
  apply (subgoal_tac "(ASID s, va) \<in> entry_range_asid_tags  (pt_walk (ASID s) (MEM s) (TTBR0 s) (Addr va) )")
   apply (subgoal_tac "\<forall>y\<in>(tlb_sat_set s). y \<noteq> x \<longrightarrow> (ASID s, va) \<notin> entry_range_asid_tags y")
    apply (drule_tac x = "pt_walk (ASID s) (MEM s) (TTBR0 s) (Addr va)" in bspec)
     apply blast
    apply clarsimp
   apply (clarsimp simp: entry_set_def ; blast)
  apply (cases "pt_walk (ASID s) (MEM s) (TTBR0 s) (Addr va)")
   apply (subgoal_tac "x11 = ASID s \<and> x12 = (ucast (va >> 12)) \<and> x14 = 0")
    prefer 2
    apply (clarsimp simp:pt_walk_def)
    apply (cases "get_pde (MEM s) (TTBR0 s) (Addr va)"; clarsimp)
    apply (case_tac a ; clarsimp)
    apply (case_tac "get_pte (MEM s) x3 (Addr va)" ; clarsimp)
    apply (case_tac a ; clarsimp)
   apply (case_tac x13)
    apply (clarsimp simp: pt_walk_def split:option.splits)
    apply (case_tac x2 ; clarsimp)
    apply (case_tac "get_pte (MEM s) x3 (Addr va)")
     apply (clarsimp simp: entry_range_asid_tags_def entry_range_def)
    apply (case_tac a ; clarsimp simp: entry_range_asid_tags_def entry_range_def)
   apply (clarsimp simp: pt_walk_def)
   apply (cases "get_pde (MEM s) (TTBR0 s) (Addr va)" ; clarsimp)
   apply (case_tac aa ; clarsimp)
   apply (case_tac "get_pte (MEM s) x3 (Addr va)" ; clarsimp)
   apply (case_tac aa ; clarsimp simp: entry_range_asid_tags_def entry_range_def)
  apply (case_tac x23)
   apply (clarsimp simp: pt_walk_def)
   apply (cases "get_pde (MEM s) (TTBR0 s) (Addr va)")
    apply (clarsimp simp: entry_range_asid_tags_def entry_range_def)
   apply (case_tac a ; clarsimp simp: entry_range_asid_tags_def entry_range_def)
   apply (case_tac "get_pte (MEM s) x3 (Addr va)" ; clarsimp)
   apply (case_tac a ; clarsimp)
  apply (clarsimp simp: pt_walk_def)
  apply (cases "get_pde (MEM s) (TTBR0 s) (Addr va)" ; clarsimp)
  apply (case_tac aa ; clarsimp)
   apply (case_tac "get_pte (MEM s) x3 (Addr va)" ; clarsimp)
   apply (case_tac aa ; clarsimp)
  apply (clarsimp simp: entry_range_asid_tags_def entry_range_def)
done


lemma not_member_incon_consistent:
  "\<lbrakk>(ASID s , addr_val va) \<notin> asid_va_incon (tlb_sat_set s);  saturated (typ_sat_tlb s) \<rbrakk> \<Longrightarrow> consistent (typ_sat_tlb s) va"
  by (clarsimp simp: asid_va_incon_def consistent0_def lookup_def entry_set_hit_pt_walk 
                  split:if_split_asm)


lemma tlb_rel_absD:
  "tlb_rel_abs s t \<Longrightarrow>
     ASID t = ASID s \<and> MEM t = MEM s \<and> TTBR0 t = TTBR0 s \<and>  asid_va_incon (state.more s) \<subseteq> state.more t \<and> exception t = exception s"
   by (clarsimp simp: tlb_rel_abs_def state.defs)


lemma tlb_rel_abs_consistent:
  "\<lbrakk>(ASID t, addr_val va) \<notin> (tlb_incon_set t) ;  tlb_rel_abs (typ_sat_tlb s) (typ_incon t) ;  saturated (typ_sat_tlb s) \<rbrakk>
            \<Longrightarrow> consistent (typ_sat_tlb s) va" 
  apply (rule not_member_incon_consistent ; clarsimp)
  apply (clarsimp simp: tlb_rel_abs_def)
  apply (subgoal_tac "ASID s = ASID t")
   apply simp
   apply blast
  apply (cases s , cases t , clarsimp simp: state.defs)
done


lemma mmu_translate_sa_consistent:
  "\<lbrakk> mmu_translate va s = (pa, s'); consistent (typ_sat_tlb s) va ; saturated (typ_sat_tlb s)\<rbrakk>  \<Longrightarrow>  consistent (typ_sat_tlb s') va"
  apply (subgoal_tac " tlb_sat_set s = tlb_sat_set s' \<and> ASID s = ASID s' \<and> MEM s = MEM s'  \<and> TTBR0 s = TTBR0 s'")
   apply (clarsimp simp: consistent0_def)
  apply (clarsimp simp: mmu_sat_eq_ASID_TTBR0_MEM)
  apply (subgoal_tac "tlb_sat_set s = tlb_sat_set s \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s))")
   apply (subgoal_tac "tlb_sat_set s' = tlb_sat_set s \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s))")
    apply clarsimp
   apply (simp add: mmu_translate_sat_TLB_union)
  by (simp add: saturated_def sup.absorb1)



lemma mmu_translate_sat_abs_refine:
  "\<lbrakk> mmu_translate va s = (pa, s');  mmu_translate va t = (pa', t') ;
      saturated (typ_sat_tlb s); (ASID t, addr_val va) \<notin> (tlb_incon_set t) ; tlb_rel_abs (typ_sat_tlb s) (typ_incon t) \<rbrakk> \<Longrightarrow> 
            tlb_rel_abs  (typ_sat_tlb s') (typ_incon t')"
  apply (frule_tac s = s in tlb_rel_abs_consistent ; clarsimp )
  apply (frule tlb_rel_absD , clarsimp)
  apply (frule_tac mmu_translate_sa_consistent ; clarsimp simp: tlb_rel_abs_def)
  (* TLB is not changing as s is already saturated *)
  apply (subgoal_tac "s' = s\<lparr>exception := exception s'\<rparr> \<and> t' = t\<lparr>exception := exception t'\<rparr>")
   apply (subgoal_tac "exception t' = exception s'")
    apply (cases t, cases t, cases s, cases s', clarsimp simp: state.defs)
   prefer 2
   apply (frule mmu_translate_abs_rel, clarsimp)
   apply (subgoal_tac "tlb_sat_set s' = tlb_sat_set s")
    apply (drule mmu_sat_rel, clarsimp)
   using mmu_translate_sat_TLB_union sat_state_tlb apply fastforce
  apply (subgoal_tac "tlb_sat_set s' = tlb_sat_set s \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s)) \<and> ASID s' = ASID s
                      \<and> MEM s' = MEM s \<and> TTBR0 s' = TTBR0 s")
   apply (clarsimp simp: mmu_translate_tlb_sat_state_ext_def split_def Let_def)
   apply (cases "lookup (tlb_sat_set s \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s))) (ASID s) (addr_val va)")
     apply (metis (no_types, lifting) saturated_not_miss tlb_sat_more typ_sat_prim_parameter)
    apply (clarsimp simp: consistent0_def)
   apply clarsimp
   apply (clarsimp simp: mmu_translate_tlb_incon_state_ext_def Let_def)
   apply (subgoal_tac "x3 = pt_walk (ASID s) (MEM s) (TTBR0 s) va")
    apply (clarsimp simp: raise'exception_def split:if_split_asm)
   apply (clarsimp simp: consistent0_def)
  apply (clarsimp simp: mmu_translate_sat_TLB_union mmu_sat_eq_ASID_TTBR0_MEM)
done

lemma mmu_translate_sat_abs_refine_pa:
  "\<lbrakk>mmu_translate va s = (pa, s');  mmu_translate va t = (pa', t') ;
      saturated (typ_sat_tlb s); (ASID t, addr_val va) \<notin> (tlb_incon_set t) ; tlb_rel_abs (typ_sat_tlb s) (typ_incon t) \<rbrakk> \<Longrightarrow>  pa = pa'"
  apply (frule_tac s = s in tlb_rel_abs_consistent ; clarsimp )
  apply (frule tlb_rel_absD , clarsimp)
  apply (frule_tac mmu_translate_sa_consistent ; clarsimp simp: tlb_rel_abs_def)
  apply (subgoal_tac "tlb_sat_set s' = tlb_sat_set s \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s)) \<and> ASID s' = ASID s
                      \<and> MEM s' = MEM s \<and> TTBR0 s' = TTBR0 s")
   apply (clarsimp simp: mmu_translate_tlb_sat_state_ext_def split_def Let_def)
   apply (cases "lookup (tlb_sat_set s \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s))) (ASID s) (addr_val va)")
     apply (metis (no_types, lifting) saturated_not_miss tlb_sat_more typ_sat_prim_parameter)
    apply (clarsimp simp: consistent0_def)
   apply clarsimp
   apply (clarsimp simp: mmu_translate_tlb_incon_state_ext_def Let_def)
   apply (subgoal_tac "x3 = pt_walk (ASID s) (MEM s) (TTBR0 s) va")
    apply (clarsimp simp: raise'exception_def split:if_split_asm)
   apply (clarsimp simp: consistent0_def)
  apply (clarsimp simp: mmu_translate_sat_TLB_union mmu_sat_eq_ASID_TTBR0_MEM)
done



lemma mmu_translate_sat_abs_refine_states:
  "\<lbrakk> mmu_translate va s = (pa, s');  mmu_translate va t = (pa', t') ;
     saturated (typ_sat_tlb s); (ASID t, addr_val va) \<notin> (tlb_incon_set t) ; tlb_rel_abs (typ_sat_tlb s) (typ_incon t) \<rbrakk> \<Longrightarrow> 
         state.truncate t' = state.truncate s'"
  apply (frule_tac s = s and t = t in tlb_rel_abs_consistent , clarsimp) apply clarsimp
  apply (frule_tac s = s and s' = s' in mmu_translate_sa_consistent , clarsimp)
   apply (clarsimp simp: tlb_rel_abs_def)
  apply (frule tlb_rel_absD)
  apply (subgoal_tac "state.truncate t = state.truncate s")
   (* TLB is not changing as s is already saturated *)
   apply (subgoal_tac "s' = s\<lparr>exception := exception s'\<rparr>")
    apply (subgoal_tac "t' = t\<lparr>exception := exception t'\<rparr>")
     apply (subgoal_tac "exception t' = exception s'")
      apply (cases t, cases t, cases s, cases s', clarsimp simp: state.defs)
     prefer 2
     apply (drule mmu_translate_abs_rel, clarsimp)
    prefer 2
    apply (subgoal_tac "tlb_sat_set s' = tlb_sat_set s")
     apply (drule mmu_sat_rel, clarsimp)
    using mmu_translate_sat_TLB_union sat_state_tlb apply force
   prefer 2
   apply (clarsimp simp: tlb_rel_abs_def)
  apply (subgoal_tac "tlb_sat_set s' = tlb_sat_set s \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s)) \<and> ASID s' = ASID s
        \<and> MEM s' = MEM s \<and> TTBR0 s' = TTBR0 s")
   apply (clarsimp simp: mmu_translate_tlb_sat_state_ext_def split_def Let_def)
   apply (cases "lookup (tlb_sat_set s \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s))) (ASID s) (addr_val va)")
     apply (metis (no_types, lifting) saturated_not_miss tlb_sat_more typ_sat_prim_parameter)
    apply (clarsimp simp: consistent0_def)
   apply clarsimp
   apply (clarsimp simp: mmu_translate_tlb_incon_state_ext_def Let_def)
   apply (subgoal_tac "x3 = pt_walk (ASID s) (MEM s) (TTBR0 s) va")
    apply (clarsimp simp: raise'exception_def split:if_split_asm)
   apply (clarsimp simp: consistent0_def)
  apply (clarsimp simp: mmu_translate_sat_TLB_union mmu_sat_eq_ASID_TTBR0_MEM)    
done

lemma write_mem_state_trun_equal:
  "\<lbrakk>  write'mem1 (val, pa, sz) s = ((), s'); write'mem1 (val, pa, sz) t = ((), t'); 
     state.truncate s = state.truncate t \<rbrakk>  \<Longrightarrow> state.truncate s' = state.truncate t'"
  apply (frule write'mem1_rel)
  apply rotate_tac
  apply (frule write'mem1_rel)
  apply (subgoal_tac "MEM s' = MEM t' \<and> exception s' = exception t'")
   apply clarsimp
   apply (cases s, cases t, cases s', cases t', clarsimp simp: state.defs)
  apply (cases s, cases t, cases s', cases t', clarsimp simp: state.defs)
  apply (clarsimp simp: write'mem1_def Let_def state.defs raise'exception_def split:if_split_asm)
done

lemma  union_incon_cases:
  "lookup (t1 \<union> t2) a va = Incon \<Longrightarrow> 
      (lookup t1 a va = Incon \<and> lookup t2 a va = Incon)                       \<or>
      ((\<exists>x\<in>t1. lookup t1 a va = Hit x)  \<and> (\<exists>x\<in>t2. lookup t2 a va = Hit x))    \<or>
      (lookup t2 a va = Incon \<and> (\<exists>x\<in>t1. lookup t1 a va = Hit x) )             \<or>
      ((\<exists>x\<in>t2. lookup t2 a va = Hit x)  \<and> lookup t1 a va = Incon)             \<or>
      (lookup t1 a va = Miss \<and> lookup t2 a va = Incon)                        \<or>
      (lookup t1 a va = Incon \<and> lookup t2 a va = Miss) "
  apply (clarsimp simp: lookup_def entry_set_def split: if_split_asm) 
  by auto

lemma  union_incon_cases1:
  "lookup (t1 \<union> t2) a va = Incon \<Longrightarrow> 
      (lookup t1 a va = Incon \<and> lookup t2 a va = Incon)                       \<or>
      ((\<exists>x\<in>t1. lookup t1 a va = Hit x)  \<and> (\<exists>x\<in>t2. lookup t2 a va = Hit x) \<and>  lookup t1 a va \<noteq>  lookup t2 a va)    \<or>
      (lookup t2 a va = Incon \<and> (\<exists>x\<in>t1. lookup t1 a va = Hit x) )             \<or>
      ((\<exists>x\<in>t2. lookup t2 a va = Hit x)  \<and> lookup t1 a va = Incon)             \<or>
      (lookup t1 a va = Miss \<and> lookup t2 a va = Incon)                        \<or>
      (lookup t1 a va = Incon \<and> lookup t2 a va = Miss) "
  apply (clarsimp simp: lookup_def entry_set_def split: if_split_asm)
  apply auto
   apply force+
done

lemma entry_set_hit_entry_range:
  "entry_set t a va = {x} \<Longrightarrow> (a , va) \<in> entry_range_asid_tags x"
  apply (clarsimp simp: entry_set_def split:if_split_asm)
   apply force
done

lemma asid_pt_walk:
  "(a, va) \<in> entry_range_asid_tags (pt_walk asid mem ttbr0 x) \<Longrightarrow> a = asid"
  apply (clarsimp simp: pt_walk_def)
  apply (cases "get_pde mem ttbr0 x")
   apply (clarsimp simp: entry_range_asid_tags_def)
  apply (case_tac "aa" ; clarsimp simp: entry_range_asid_tags_def)
  apply (case_tac "get_pte mem x3 x" ,clarsimp simp: entry_range_asid_tags_def)
  apply (case_tac "aa" ; clarsimp simp: entry_range_asid_tags_def)
done



lemma asid_va_entry_range_pt_entry:
  "(asid, va) \<in> entry_range_asid_tags (pt_walk asid mem ttbr0 (Addr va))"
  apply (clarsimp simp: pt_walk_def)
  apply (cases "get_pde mem ttbr0 (Addr va)" ; clarsimp simp: entry_range_asid_tags_def entry_range_def)
  apply (case_tac a ; clarsimp simp: entry_range_asid_tags_def entry_range_def)
  apply (case_tac "get_pte mem x3 (Addr va)" ; clarsimp simp: entry_range_asid_tags_def entry_range_def)
  apply (case_tac a ; clarsimp simp: entry_range_asid_tags_def entry_range_def)
done

lemma asid_va_entry_range_pt_entry1:
  "(asid, addr_val va) \<in> entry_range_asid_tags (pt_walk asid mem ttbr0 va)"
  apply (clarsimp simp: pt_walk_def)
  apply (cases "get_pde mem ttbr0 va" ,  clarsimp simp: entry_range_asid_tags_def entry_range_def)
  apply (case_tac a ; clarsimp simp: entry_range_asid_tags_def entry_range_def)
  apply (case_tac "get_pte mem x3 va" , clarsimp simp: entry_range_asid_tags_def entry_range_def)
  apply (case_tac a ; clarsimp simp: entry_range_asid_tags_def entry_range_def)
done


theorem entry_range_single_elementI:
  "\<lbrakk>x\<in> t ; (a, v) \<in> entry_range_asid_tags x ; (\<forall>y\<in>t. y\<noteq>x \<longrightarrow> (a, v) \<notin> entry_range_asid_tags y) \<rbrakk> \<Longrightarrow> 
         {E \<in> t. (a, v) \<in> entry_range_asid_tags E} = {x}" 
   by force




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
  "(asid, va) \<in> entry_range_asid_tags (pt_walk asid mem ttbr0 x) \<Longrightarrow>
       pt_walk asid mem ttbr0 x = pt_walk asid mem ttbr0 (Addr va)"
  apply (subgoal_tac "(asid, addr_val x) \<in> entry_range_asid_tags (pt_walk asid mem ttbr0 x)")
   prefer 2
   apply (clarsimp simp: asid_va_entry_range_pt_entry1)
  apply (cases "pt_walk asid mem ttbr0 x")
   apply (case_tac "x13" ; simp)
    apply (clarsimp simp: entry_range_asid_tags_def entry_range_def pt_walk_def)
    apply (cases "get_pde mem ttbr0 x" ; clarsimp)
    apply (case_tac a ; clarsimp)
    apply (case_tac " get_pte mem x3 x " ; clarsimp)
     apply (subgoal_tac "get_pde mem ttbr0 x = get_pde mem ttbr0 (Addr va)" ; clarsimp)
      apply (subgoal_tac "get_pte mem x3 x = get_pte mem x3 (Addr va)" ; clarsimp)
       using va_offset_higher_bits apply blast
      apply (clarsimp simp:  get_pte_def vaddr_pt_index_def)
      apply (subgoal_tac "((addr_val x >> 12) && mask 8 << 2) =
                          ((va >> 12) && mask 8 << 2) ")
       prefer 2
       using offset_mask_eq apply blast
      apply force
     apply (clarsimp simp: get_pde_def vaddr_pd_index_def)
     apply (subgoal_tac "((addr_val x >> 20) && mask 12 << 2) =
                         ((va >> 20) && mask 12 << 2) ")
      prefer 2
      using offset_mask_eq_1 apply blast
     apply force
    apply (case_tac a ; clarsimp)
    apply (subgoal_tac "get_pde mem ttbr0 x = get_pde mem ttbr0 (Addr va)" ; clarsimp)
     apply (subgoal_tac "get_pte mem x3 x = get_pte mem x3 (Addr va)" ; clarsimp)
      using va_offset_higher_bits apply blast
     apply (clarsimp simp: get_pte_def vaddr_pt_index_def)
     apply (case_tac "get_pde mem ttbr0 (Addr va)" ; clarsimp)
     apply (subgoal_tac "((addr_val x >> 12) && mask 8 << 2) =
                         ((va >> 12) && mask 8 << 2) ")
      prefer 2
      using offset_mask_eq apply blast
     apply force
    apply (clarsimp simp: get_pde_def vaddr_pd_index_def)
    apply (subgoal_tac "((addr_val x >> 20) && mask 12 << 2) =
                        ((va >> 20) && mask 12 << 2) ")
     prefer 2
     using offset_mask_eq_1 apply blast
    apply force
   apply clarsimp
   apply (clarsimp simp: entry_range_asid_tags_def entry_range_def pt_walk_def)
   apply (cases "get_pde mem ttbr0 x" ; clarsimp)
   apply (case_tac aa ; clarsimp)
   apply (case_tac "get_pte mem x3 x" ; clarsimp)
   apply (subgoal_tac "get_pde mem ttbr0 x = get_pde mem ttbr0 (Addr va)" ; clarsimp)
    apply (subgoal_tac "get_pte mem x3 x = get_pte mem x3 (Addr va)" ; clarsimp)
     apply (case_tac aa ; clarsimp)
     using va_offset_higher_bits apply blast
    apply (case_tac aa ; clarsimp simp: get_pte_def vaddr_pt_index_def)
    apply (subgoal_tac "((addr_val x >> 12) && mask 8 << 2) =
                        ((va >> 12) && mask 8 << 2) ")
     prefer 2
     using offset_mask_eq apply blast
    apply force
   apply (case_tac aa ; clarsimp simp: get_pde_def vaddr_pd_index_def)
   apply (subgoal_tac "((addr_val x >> 20) && mask 12 << 2) =
                       ((va >> 20) && mask 12 << 2) ")
    prefer 2
    using offset_mask_eq_1 apply blast
   apply force
  apply (clarsimp)
  apply (case_tac "x23" ; clarsimp simp: entry_range_asid_tags_def entry_range_def pt_walk_def)
   apply (cases "get_pde mem ttbr0 x" ; clarsimp)
    apply (subgoal_tac "get_pde mem ttbr0 (Addr va) = get_pde mem ttbr0 x" ; clarsimp)
     using va_offset_higher_bits_1 apply blast
    apply (clarsimp simp: get_pde_def vaddr_pd_index_def)
    apply (subgoal_tac "((addr_val x >> 20) && mask 12 << 2) = ((va >> 20) && mask 12 << 2)")
     apply force
    using shfit_mask_eq apply blast
   apply (case_tac a , clarsimp)
      apply (subgoal_tac "get_pde mem ttbr0 (Addr va) = get_pde mem ttbr0 x" ; clarsimp)
       using va_offset_higher_bits_1 apply blast
      apply (clarsimp simp: get_pde_def vaddr_pd_index_def)
      apply (subgoal_tac "((addr_val x >> 20) && mask 12 << 2) = ((va >> 20) && mask 12 << 2)")
       apply force
      using shfit_mask_eq apply blast
     apply clarsimp
     apply (subgoal_tac "get_pde mem ttbr0 (Addr va) = get_pde mem ttbr0 x" ; clarsimp)
      using va_offset_higher_bits_1 apply blast
     apply (clarsimp simp: get_pde_def vaddr_pd_index_def)
     apply (subgoal_tac "((addr_val x >> 20) && mask 12 << 2) = ((va >> 20) && mask 12 << 2)")
      apply force
     using shfit_mask_eq apply blast
    apply clarsimp
    apply (case_tac "get_pte mem x3 x" ; clarsimp)
    apply (case_tac a , clarsimp)
    apply clarsimp
   apply (case_tac a ; clarsimp)
  apply (cases "get_pde mem ttbr0 x" ; clarsimp)
  apply (case_tac aa ; clarsimp)
   apply (case_tac "get_pte mem x3 x" ; clarsimp)
   apply (case_tac aa ; clarsimp)
  apply (subgoal_tac "get_pde mem ttbr0 (Addr va) = get_pde mem ttbr0 x" ; clarsimp)
   using va_offset_higher_bits_1 apply blast
  apply (clarsimp simp: get_pde_def vaddr_pd_index_def)
  apply (subgoal_tac "((addr_val x >> 20) && mask 12 << 2) = ((va >> 20) && mask 12 << 2)")
   apply force
  using shfit_mask_eq apply blast
 done


lemma lookup_range_pt_walk_hit:
  "lookup (range (pt_walk asid mem ttbr0)) asid va = Hit (pt_walk asid mem ttbr0 (Addr va))"
  apply (clarsimp simp: lookup_def)
  apply safe
    apply simp
   apply (subgoal_tac "x = pt_walk asid mem ttbr0 (Addr va)" , force)
   apply (clarsimp simp: entry_set_def)
   apply (drule entry_range_single_element)
   apply safe
   apply (unfold Ball_def) [1]
   apply (erule_tac x = "pt_walk asid mem ttbr0 (Addr va)" in allE)
   apply (clarsimp simp: asid_va_entry_range_pt_entry)
  apply (rule_tac x = "pt_walk asid mem ttbr0 (Addr va)" in exI)
  apply (clarsimp simp: entry_set_def)
  apply (rule entry_range_single_elementI)
    apply force
   apply (clarsimp simp: asid_va_entry_range_pt_entry)
  apply safe
  apply (drule va_entry_set_pt_palk_same , simp)
done
 

lemma lookup_range_pt_walk_not_incon:
  "lookup (range (pt_walk asid mem ttbr0)) asid va \<noteq> Incon"
  by (clarsimp simp: lookup_range_pt_walk_hit)


lemma sat_state_lookup_not_miss1:
  "saturated (typ_sat_tlb s) \<Longrightarrow>   \<forall>va. lookup (tlb_sat_set s) (ASID s) va \<noteq> Miss"
  apply (clarsimp simp: saturated_def)
  apply (clarsimp simp: lookup_def split:if_split_asm)
  apply (subgoal_tac "pt_walk (ASID s) (MEM s) (TTBR0 s) (Addr va) \<in>  range (pt_walk (ASID s) (MEM s) (TTBR0 s))")
   prefer 2
   apply simp
  apply (subgoal_tac "pt_walk (ASID s) (MEM s) (TTBR0 s) (Addr va) \<in> tlb_sat_set s")
   prefer 2
   apply fastforce
  apply (subgoal_tac "va \<in> entry_range (pt_walk (ASID s) (MEM s) (TTBR0 s) (Addr va) )")
   prefer 2
   apply (clarsimp)
  apply (subgoal_tac "entry_set (tlb_sat_set s) (ASID s) va \<noteq> {}" , simp)
  using entry_set_def entry_range_asid_tags_def apply force
done


lemma asid_entry_set_pt_walk1 [simp]:
  "asid_entry ` (pt_walk asid m ttbr0 `UNIV) = {asid}"
  by force

 

lemma asid_lookup_miss:
  "\<lbrakk>asid_entry ` tlb = aset ; a \<notin> aset \<rbrakk> \<Longrightarrow> lookup tlb a va = Miss "
  using lookup_def entry_set_def entry_range_asid_tags_def by fastforce

  

lemma asid_unequal_miss:
  " a \<noteq> ASID b \<Longrightarrow>
   lookup (range (pt_walk (ASID b) (MEM bc) (TTBR0 b))) a bb = Miss"
  apply (subgoal_tac "asid_entry ` ((pt_walk (ASID b) (MEM bc) (TTBR0 b)) `UNIV) = {ASID b}")
   prefer 2
   apply fastforce
   using asid_lookup_miss by force


lemma write_asid_incon_set_rel:
  "\<lbrakk> saturated (typ_sat_tlb b) ; asid_va_incon (tlb_sat_set b) \<subseteq> tlb_incon_set ba \<rbrakk> \<Longrightarrow>
    asid_va_incon (tlb_sat_set b \<union> range (pt_walk (ASID b) (MEM bc) (TTBR0 b)))
           \<subseteq> tlb_incon_set ba \<union> ptable_comp (ASID b) (MEM b) (MEM bc) (TTBR0 b)"
  apply (clarsimp simp: asid_va_incon_def ptable_comp_def)
  apply (case_tac "a = ASID b" , clarsimp)
   apply (subgoal_tac "pt_walk (ASID b) (MEM b) (TTBR0 b) (Addr bb) =
                       pt_walk (ASID b) (MEM bc) (TTBR0 b) (Addr bb)")
    prefer 2
    apply force
   apply (subgoal_tac "(ASID b, bb) \<in> {(asid, va). lookup (tlb_sat_set b) asid va = Incon}")
    apply blast
   apply (subgoal_tac "lookup (tlb_sat_set b) (ASID b) bb = Incon" , clarsimp)
   apply (drule union_incon_cases1 , clarsimp)
   apply (erule disjE , clarsimp)
   apply (erule disjE , clarsimp)
    apply (clarsimp simp: lookup_def split:if_split_asm)
    apply (drule_tac s = b and va = bb and x = x in entry_set_hit_pt_walk1 , clarsimp)
    apply (subgoal_tac "(ASID b , bb) \<in> entry_range_asid_tags (pt_walk (ASID b) (MEM bc) (TTBR0 b) xa)")
     prefer 2
     apply (clarsimp simp: entry_set_hit_entry_range)
    apply (drule va_entry_set_pt_palk_same , clarsimp)
   apply (erule disjE , clarsimp simp: lookup_range_pt_walk_not_incon )
   apply (erule disjE , force)
   apply (erule disjE)
    apply (drule_tac sat_state_lookup_not_miss1 , clarsimp)
   apply force
  apply (drule union_incon_cases1)
  apply (erule disjE , force)
  apply (erule disjE)
   apply (drule_tac bb = bb and bc = bc in asid_unequal_miss , clarsimp)
  apply (erule disjE)
   apply (drule_tac bb = bb and bc = bc in asid_unequal_miss , clarsimp)
  apply (erule disjE , force)
  apply (erule disjE)
   apply (drule_tac bb = bb and bc = bc in asid_unequal_miss , clarsimp)
  apply force
done

lemma write_refinement_saturated_incon_only:        
  "\<lbrakk> mmu_write_size (val,va, sz) s = ((), s'); (ASID t, addr_val va) \<notin> (tlb_incon_set t); saturated (typ_sat_tlb s);
         tlb_rel_abs (typ_sat_tlb s) (typ_incon t) ;  mmu_write_size (val,va, sz) t = ((), t') \<rbrakk> \<Longrightarrow> 
         tlb_rel_abs (typ_sat_tlb s') (typ_incon t')"
  apply (frule_tac s = s in tlb_rel_abs_consistent ; clarsimp)
  apply (frule_tac tlb_rel_absD , clarsimp)
  apply (clarsimp simp:  mmu_write_size_tlb_sat_state_ext_def  mmu_write_size_tlb_incon_state_ext_def)
  apply (cases "mmu_translate va s" ,cases "mmu_translate va t" , clarsimp)
  apply (frule_tac t=t and pa'= aa and t' = ba in  mmu_translate_sat_abs_refine) apply clarsimp+
  apply (frule_tac t=t and pa'= aa and t' = ba in  mmu_translate_sat_abs_refine_pa) apply clarsimp+
  apply (clarsimp simp: tlb_rel_abs_def)
  apply (subgoal_tac "exception b = exception ba")
   prefer 2 apply (case_tac b , case_tac ba , clarsimp simp: state.defs)
  apply (clarsimp split: if_split_asm)
  apply (case_tac "write'mem1 (val, aa, sz) b " , case_tac "write'mem1 (val, aa, sz) ba" , clarsimp)
  apply (subgoal_tac "state.truncate bb = state.truncate bc")
   prefer 2 using write_mem_state_trun_equal apply blast
  apply (rule conjI , clarsimp simp: state.defs)
  apply (subgoal_tac "MEM bb = MEM bc  \<and> MEM s = MEM b" , simp)
   apply (subgoal_tac "ASID s = ASID b \<and> TTBR0 s = TTBR0 b" , simp)
    apply (subgoal_tac "saturated (typ_sat_tlb b)")
     prefer 2
     using mmu_translate_sat_sat' apply blast
    apply (drule_tac b = b and ba = ba and bc = bc in write_asid_incon_set_rel) apply clarsimp+
   using mmu_sat_eq_ASID_TTBR0_MEM apply blast
  apply (rule conjI)
   apply (clarsimp simp: state.defs)
  using mmu_sat_eq_ASID_TTBR0_MEM by blast




lemma mmu_translate_sat_abs_refine':
  "\<lbrakk>mmu_translate va s = (pa, s'); mmu_translate va t = (pa', t'); saturated (typ_sat_tlb s);
    (ASID t, addr_val va) \<notin> tlb_incon_set t; tlb_rel_abs (typ_sat_tlb s) (typ_incon t)\<rbrakk>
   \<Longrightarrow> pa = pa' \<and> tlb_rel_abs (typ_sat_tlb s') (typ_incon t')"
   by (simp add: mmu_translate_sat_abs_refine mmu_translate_sat_abs_refine_pa)


lemma saturated_tlb_const [simp]:
  "saturated (typ_sat_tlb s) \<Longrightarrow>
  tlb_sat_set s \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s)) = tlb_sat_set s"
  by (auto simp add: saturated_def)


lemma mmu_translate_sat_const_tlb [simp]:
  "saturated (typ_sat_tlb s) \<Longrightarrow> tlb_sat_set (snd (mmu_translate va s)) = tlb_sat_set s"
  by (simp add: mmu_translate_tlb_sat_state_ext_def Let_def raise'exception_def
         split: lookup_type.splits)


lemma tlb_sat_set_mem1 [simp]:
  "tlb_sat_set (snd (mem1 ps s)) = tlb_sat_set s"
  by (simp add: mem1_def raise'exception_def split: option.splits)


lemma mmu_read_sat_const [simp]:
  "saturated (typ_sat_tlb s) \<Longrightarrow> tlb_sat_set (snd (mmu_read_size v s)) = tlb_sat_set s"
   by (clarsimp simp: mmu_read_size_tlb_sat_state_ext_def split_def Let_def
                      mem_read1_def raise'exception_def
               split: if_split_asm)



lemma addr_val_eqD [dest!]:
  "addr_val a = addr_val b \<Longrightarrow> a = b"
  apply (cases a, cases b)
  by simp


(* A set of addresses SA is consistent, if it is not TLB-inconsistent and will
   not page fault. Such addresses are safe to write to without losing consistency,
   if their page mappings are not changed by the write operation *)

definition
  consistent_set :: "vaddr set \<Rightarrow> tlb_incon_state \<Rightarrow> bool"
where
  "consistent_set SA s \<equiv>
     \<forall>va \<in> SA. (ASID s, addr_val va) \<notin> tlb_incon_set s \<and>
               \<not> is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) va)"

lemma consistent_set_translate:
  "\<lbrakk> consistent_set SA s; va \<in> SA \<rbrakk> \<Longrightarrow>
  mmu_translate va s = (Addr (va_to_pa (addr_val va) (pt_walk (ASID s) (MEM s) (TTBR0 s) va)), s)"
  by (simp add: mmu_translate_tlb_incon_state_ext_def consistent_set_def Let_def)

lemma incon_safe_writes:
  "\<lbrakk> mmu_write_size (val, va, sz) s = ((), s');
     va \<in> SA; consistent_set SA s;
     \<forall>v \<in> SA. pt_walk (ASID s) (MEM s) (TTBR0 s) v = pt_walk (ASID s') (MEM s') (TTBR0 s') v \<rbrakk>
    \<Longrightarrow> consistent_set SA s'"
  apply (simp add: mmu_write_size_tlb_incon_state_ext_def)
  apply (cases "mmu_translate va s")
  apply (clarsimp simp: consistent_set_translate split: if_splits)
  apply (clarsimp split: prod.splits)
  apply (simp add: consistent_set_def write'mem1_eq_ASID_TTBR0)
  apply (auto simp: ptable_comp_def)
  done


end