(*
 * Copyright 2016, Data61, CSIRO
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *)

theory TLB_Refine
imports ARM_Monadic "~~/src/HOL/Word/WordBitwise"
begin


(* "Deterministic" mmu_translate: without entry eviction and with page_faults entries *)
definition 
  mmu_translate_det ::"32 word  \<Rightarrow> state \<Rightarrow> 32 word \<times> state"
where
  "mmu_translate_det va \<equiv> do {
     mem   <- read_state MEM;
     asid  <- read_state ASID;
     ttbr0 <- read_state TTBR0;
     tlb   <- read_state TLB;
      case lookup tlb asid va of
            Hit entry \<Rightarrow> if is_fault entry
              then raise'exception (PAGE_FAULT ''more info'')
                else return (va_to_pa va entry)
          | Miss \<Rightarrow> let entry = pt_walk asid mem ttbr0 va in
              if is_fault entry
                then raise'exception (PAGE_FAULT ''more info'')
                  else do {
                    update_state (\<lambda>s. s\<lparr> TLB := tlb \<union> {entry} \<rparr>);
                    return (va_to_pa va entry)
                  }
          | Incon \<Rightarrow> raise'exception (IMPLEMENTATION_DEFINED ''set on fire'')
   }" 


lemma mmu_translate_def2:
  "mmu_translate va = do {
     update_state (\<lambda>s. s\<lparr> TLB := TLB s - tlb_evict s \<rparr>);
     mmu_translate_det va
  }"
  by (simp add: mmu_translate_def mmu_translate_det_def)


(* TLB doesn't store page faults in this level of the model *)
definition
  "no_faults tlb = (\<forall>e \<in> tlb. \<not>is_fault e)"

(* relate a concrete and abstract state, where the abstract state has a TLB with more entries *)
definition
  "tlb_rel s s' \<equiv> s' = s \<lparr>TLB := TLB s'\<rparr> \<and> TLB s \<subseteq> TLB s' \<and> no_faults (TLB s')"

(* TLB consistency for an address va: if we look up va, the result is not Incon, 
   and if it is Hit, then it agrees with the page table *)
definition
  "consistent0 m asid ttbr0 tlb va \<equiv>
     lookup tlb asid va = Hit (pt_walk asid m ttbr0 va) \<or>
     lookup tlb asid va = Miss"

lemma consistent_not_Incon:
  "consistent0 m asid ttbr0 tlb va = 
  (lookup tlb asid va \<noteq> Incon \<and> (\<forall>e. lookup tlb asid va = Hit e \<longrightarrow> e = pt_walk asid m ttbr0 va))"
  by (cases "lookup tlb asid va"; simp add: consistent0_def)

(* abbreviation for machine states *)
abbreviation
  "consistent s \<equiv> consistent0 (MEM s) (ASID s) (TTBR0 s) (TLB s)"

lemma tlb_relD:
  "tlb_rel s t \<Longrightarrow>
  ASID t = ASID s \<and> MEM t = MEM s \<and> TTBR0 t = TTBR0 s \<and> TLB s \<subseteq> TLB t \<and> exception t = exception s"
  by (cases s, cases t) (simp add: tlb_rel_def)

lemma tlb_rel_consistent:
  "\<lbrakk> tlb_rel s t; consistent t va \<rbrakk> \<Longrightarrow> consistent s va"
  apply (drule tlb_relD)
  apply clarsimp
  apply (drule tlb_mono [of _ _ "ASID s" va])
  apply (auto simp: consistent0_def less_eq_lookup_type)
done

lemma lookup_in_tlb:
  "lookup tlb asid va = Hit e \<Longrightarrow> e \<in> tlb"
  by (auto simp: lookup_def entry_set_def split: split_if_asm)

lemma entry_set_insert:
  "\<lbrakk> entry_set tlb asid va = {}; asid_entry e = asid; va \<in> entry_range e \<rbrakk> \<Longrightarrow> 
  entry_set (insert e tlb) asid va = {e}"
  by (auto simp add: entry_set_def entry_range_asid_tags_def)

lemma asid_entry_pt_walk [simp]:
  "asid_entry (pt_walk asid m ttbr0 va) = asid"
  by (simp add: pt_walk_def Let_def)

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
  "va \<in> entry_range (pt_walk asid m ttrb0 va)"
  by (auto simp add: entry_range_def pt_walk_def Let_def)

lemma lookup_refill:
  "lookup tlb asid va = Miss \<Longrightarrow>
   lookup (insert (pt_walk asid m ttrb0 va) tlb) asid va = Hit (pt_walk asid m ttrb0 va)"
   by (clarsimp simp: lookup_def entry_set_insert [where e="pt_walk asid m ttrb0 va"] split: split_if_asm)

lemma consistent_insert [simp, intro!]:
  "lookup tlb asid va = Miss \<Longrightarrow>
  consistent0 m asid ttrb0 (insert (pt_walk asid m ttrb0 va) tlb) va"
  by (simp add: consistent0_def lookup_refill)


(* refinement between two deterministic TLB lookups, tlb_rel states that TLBs don't store page faults  *)
lemma mmu_translate_det_refine:
  "\<lbrakk> mmu_translate_det va s = (pa, s'); consistent t va; tlb_rel s t \<rbrakk> \<Longrightarrow>
  let (pa', t') = mmu_translate_det va t
  in pa' = pa \<and> consistent t' va \<and> tlb_rel s' t'"
  apply (frule (1) tlb_rel_consistent)
  apply (frule tlb_relD)
  apply (subgoal_tac "lookup (TLB s) (ASID s) va \<le> lookup (TLB t) (ASID s) va")
   prefer 2
   apply (simp add: tlb_mono)
  apply (clarsimp simp: mmu_translate_det_def split_def Let_def split: split_if_asm)
  apply (cases "lookup (TLB t) (ASID s) va")
    apply clarsimp
    apply (simp add: Let_def raise'exception_def tlb_rel_def split: split_if_asm)
     apply (cases s, cases t, clarsimp)
    apply (cases s, cases t)
    apply (clarsimp simp: no_faults_def)
    apply fastforce
   apply (simp add: raise'exception_def consistent0_def split_def split: split_if_asm)
  apply clarsimp
  apply (cases "lookup (TLB s) (ASID s) va"; clarsimp)
   apply (simp add: consistent0_def Let_def tlb_rel_def no_faults_def lookup_in_tlb split: split_if_asm)
   apply clarsimp
   apply (drule lookup_in_tlb)
   apply simp
  apply (clarsimp split: split_if_asm simp: tlb_rel_def no_faults_def)
  using lookup_in_tlb apply blast
done


(* refinement between eviction and deterministic TLB lookups *)
lemma mmu_translate_refine_det:
  "\<lbrakk> mmu_translate va s = (pa, s'); consistent t va; tlb_rel s t \<rbrakk> \<Longrightarrow>
    let (pa', t') = mmu_translate_det va t
     in pa' = pa  \<and> consistent t' va \<and> tlb_rel s' t'"
  apply (simp add: mmu_translate_def2)
  apply (drule (1) mmu_translate_det_refine; fastforce simp: tlb_rel_def)
done

(* relate a concrete and abstract state, where the abstract state has a TLB with more entries
    and it stores entries with faults*)
definition
  "tlb_rel_flt s s' \<equiv> s' = s \<lparr>TLB := TLB s'\<rparr> \<and> TLB s \<subseteq> TLB s'"

lemma tlb_rel_fltD:
  "tlb_rel_flt s t \<Longrightarrow>
     ASID t = ASID s \<and> MEM t = MEM s \<and> TTBR0 t = TTBR0 s \<and> TLB s \<subseteq> TLB t \<and> exception t = exception s"
  by (cases s, cases t) (simp add: tlb_rel_flt_def)

lemma tlb_rel_flt_consistent:
  "\<lbrakk> tlb_rel_flt s t; consistent t va \<rbrakk> \<Longrightarrow> consistent s va"
  apply (drule tlb_rel_fltD)
  apply clarsimp
  apply (drule tlb_mono [of _ _ "ASID s" va])
  apply (auto simp: consistent0_def less_eq_lookup_type)
done

(* refinement between two deterministic TLB lookups, tlb_rel_flt states that TLBs store page faults  *)
lemma mmu_translate_det_flt_refine:
  "\<lbrakk> mmu_translate_det va s = (pa, s'); consistent t va; tlb_rel_flt s t \<rbrakk> \<Longrightarrow>
    let (pa', t') = mmu_translate_det va t
      in pa' = pa \<and> consistent t' va \<and> tlb_rel_flt s' t'"
  apply (frule (1) tlb_rel_flt_consistent)
  apply (frule tlb_rel_fltD)
  apply (subgoal_tac "lookup (TLB s) (ASID s) va \<le> lookup (TLB t) (ASID s) va")
   prefer 2
   apply (simp add: tlb_mono)
  apply (clarsimp simp: mmu_translate_det_def split_def Let_def)
  apply (cases "lookup (TLB t) (ASID s) va")
    apply clarsimp
    apply (simp add: Let_def raise'exception_def tlb_rel_flt_def split: split_if_asm)
     apply (clarsimp simp: tlb_rel_flt_def)
     apply (cases s, cases t, clarsimp)
    apply (clarsimp simp: tlb_rel_flt_def)
    apply (clarsimp simp: subset_insertI2)
    apply (cases s, cases t, clarsimp)
   apply (clarsimp simp: consistent0_def)
  apply (clarsimp)
  apply (cases "lookup (TLB s) (ASID s) va"; clarsimp)
   apply (clarsimp simp: consistent0_def Let_def tlb_rel_flt_def
                   lookup_in_tlb raise'exception_def split: split_if_asm)
   apply (cases s, cases t, clarsimp)
  apply (clarsimp split: split_if_asm simp:raise'exception_def tlb_rel_flt_def)
  apply (cases s, cases t, clarsimp)
done

(* refinement between eviction and deterministic TLB lookups *)
lemma mmu_translate_flt_refine_det:
  "\<lbrakk> mmu_translate va s = (pa, s'); consistent t va; tlb_rel_flt s t \<rbrakk> \<Longrightarrow>
    let (pa', t') = mmu_translate_det va t
     in pa' = pa  \<and> consistent t' va \<and> tlb_rel_flt s' t'"
  apply (simp add: mmu_translate_def2)
  apply (drule (1) mmu_translate_det_flt_refine; fastforce simp: tlb_rel_flt_def)
done


(* Saturated TLB; always read all entries from the current page table, including all faults *)
definition
  mmu_translate_sat ::"32 word  \<Rightarrow> state \<Rightarrow> 32 word \<times> state"
where
  "mmu_translate_sat va \<equiv> do {
     mem   <- read_state MEM;
     asid  <- read_state ASID;
     ttbr0 <- read_state TTBR0;
     let all_entries = pt_walk asid mem ttbr0 ` UNIV;
     tlb0   <- read_state TLB;
     let tlb = tlb0 \<union> all_entries;
     update_state (\<lambda>s. s\<lparr> TLB := tlb \<rparr>);
          case lookup tlb asid va of
            Hit entry \<Rightarrow> if is_fault entry 
              then raise'exception (PAGE_FAULT ''more info'')
                else return (va_to_pa va entry)
          | Miss \<Rightarrow> raise'exception (ASSERT ''impossible'')
          | Incon \<Rightarrow> raise'exception (IMPLEMENTATION_DEFINED ''set on fire'')
   }" 


(*saturated state, TLB contains all the page table entries for current TTBR0 *)
definition
  saturated :: "state  \<Rightarrow> bool"
where
  "saturated s  \<equiv> pt_walk (ASID s) (MEM s) (TTBR0 s) ` UNIV \<subseteq> TLB s"

(* relate a concrete and abstract state, where the abstract state is saturated w.r.t. current TTBR0*)
definition 
  tlb_rel_sat :: " state \<Rightarrow> state \<Rightarrow> bool"
where                                                                
  "tlb_rel_sat s s' \<equiv> s' = s \<lparr>TLB := TLB s'\<rparr> \<and> TLB s \<subseteq> TLB s' \<and> saturated s'"


lemma tlb_rel_satD:
  "tlb_rel_sat s t \<Longrightarrow>
      ASID t = ASID s \<and> MEM t = MEM s \<and> TTBR0 t = TTBR0 s \<and> TLB s \<subseteq> TLB t \<and> exception t = exception s"
  by (cases s, cases t) (simp add: tlb_rel_sat_def)

lemma sat_state_tlb:
  "\<lbrakk>saturated s \<rbrakk> \<Longrightarrow> 
      TLB s = TLB s \<union> pt_walk (ASID s) (MEM s) (TTBR0 s) ` UNIV"
  by (fastforce simp: saturated_def)

lemma tlb_rel_sat_consistent:
  "\<lbrakk> tlb_rel_sat s t; consistent t va \<rbrakk> \<Longrightarrow> consistent s va"
  apply (drule tlb_rel_satD)
  apply clarsimp
  apply (drule tlb_mono [of _ _ "ASID s" va])
  apply (auto simp: consistent0_def less_eq_lookup_type)
  done

lemma saturated_states_tlbs_equal:
  "\<lbrakk> mmu_translate_sat va t = (pa', t') ; saturated t \<rbrakk> \<Longrightarrow>
      TLB t' = TLB t \<and> ASID t' = ASID t \<and> MEM t' = MEM t \<and> TTBR0 t' = TTBR0 t \<and> saturated t'"
  apply (frule sat_state_tlb)
  apply (clarsimp simp: mmu_translate_sat_def Let_def saturated_def)
  apply (cases "lookup (TLB t) (ASID t) va" )
    apply (clarsimp simp: raise'exception_def split:split_if_asm)+
  done


lemma saturated_lookup_not_miss:
  "\<lbrakk>saturated s\<rbrakk> \<Longrightarrow> \<forall>va. lookup (TLB s) (ASID s) va \<noteq> Miss"
  apply (clarsimp simp: saturated_def)
  apply (clarsimp simp: lookup_def split:split_if_asm)
  apply (subgoal_tac "pt_walk (ASID s) (MEM s) (TTBR0 s) va \<in>  range (pt_walk (ASID s) (MEM s) (TTBR0 s))")
   prefer 2
   apply simp
  apply (subgoal_tac "pt_walk (ASID s) (MEM s) (TTBR0 s) va \<in> TLB s")
   prefer 2
   apply fastforce
  apply (subgoal_tac "va \<in> entry_range (pt_walk (ASID s) (MEM s) (TTBR0 s) va )")
   prefer 2
   apply (clarsimp)
  apply (subgoal_tac "entry_set (TLB s) (ASID s) va \<noteq> {}")
   apply simp
  apply (clarsimp simp: entry_set_def entry_range_asid_tags_def)
  apply force
   done

lemma sat_con_not_miss_incon:
  "\<lbrakk>saturated s ; consistent s va\<rbrakk> \<Longrightarrow> 
    (lookup (TLB s) (ASID s)va \<noteq> Incon \<and> lookup (TLB s) (ASID s) va \<noteq> Miss \<and>
       (\<forall>e. lookup (TLB s) (ASID s) va = Hit e \<longrightarrow> e = pt_walk (ASID s) (MEM s) (TTBR0 s) va))"
  apply (frule saturated_lookup_not_miss)
  apply (clarsimp simp:consistent_not_Incon)
  done


(* state doesn't change in reading a non_page_fault entry through a saturated state *)
lemma const_sat_state:
  "\<lbrakk>saturated s ; consistent s va ; \<not>is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) va) ;
      mmu_translate_sat va s = (pa , s') \<rbrakk> \<Longrightarrow> 
              s = s' "
  apply (frule sat_con_not_miss_incon , simp)
  apply (clarsimp simp: mmu_translate_sat_def split_def Let_def)
  apply (frule sat_state_tlb ; clarsimp)
  apply (cases "lookup (TLB s) (ASID s) va")
    apply clarsimp 
   apply clarsimp
  apply (clarsimp split:split_if_asm simp:raise'exception_def)
  done


lemma saturated_no_excpetion:
  "\<lbrakk>saturated s ; consistent s va ; mmu_translate_sat va s = (pa , s');
     is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) va) ; exception s = NoException\<rbrakk> \<Longrightarrow> 
       s' = s\<lparr>exception := PAGE_FAULT ''more info'' \<rparr> "
  apply (frule sat_con_not_miss_incon , simp)
  apply (clarsimp simp: mmu_translate_sat_def split_def Let_def)
   apply (frule sat_state_tlb ; clarsimp) 
   apply (cases "lookup (TLB s) (ASID s) va")
    apply clarsimp
   apply clarsimp
  apply clarsimp
  apply (simp add: Let_def raise'exception_def)
  done

lemma 
  "\<lbrakk> lookup (TLB s) (ASID s) va = Miss ; tlb_rel_sat s t\<rbrakk> \<Longrightarrow>
       lookup (TLB t) (ASID s) va \<noteq> Miss"
  apply (frule tlb_rel_satD)
  apply (simp add: tlb_rel_sat_def saturated_def , clarsimp)
  apply (simp add: lookup_def split:split_if_asm)
  apply (subgoal_tac "pt_walk (ASID s) (MEM s) (TTBR0 s) va \<in>  range (pt_walk (ASID s) (MEM s) (TTBR0 s))")
   prefer 2
   apply simp
  apply (subgoal_tac "pt_walk (ASID s) (MEM s) (TTBR0 s) va \<in> TLB t")
   prefer 2
   apply fastforce
  apply (subgoal_tac "va \<in> entry_range (pt_walk (ASID s) (MEM s) (TTBR0 s) va )")
   prefer 2
   apply (clarsimp)
  apply (subgoal_tac "entry_set (TLB t) (ASID s) va \<noteq> {}")
   apply simp
  apply (clarsimp simp: entry_set_def entry_range_asid_tags_def)
  apply force
   done

lemma lookup_miss_sat_hit:
  "\<lbrakk> lookup (TLB s) (ASID s) va = Miss ; tlb_rel_sat s t ; consistent t va\<rbrakk> \<Longrightarrow>
        lookup (TLB t) (ASID t) va = Hit (pt_walk (ASID s) (MEM s) (TTBR0 s) va)"
   apply (frule tlb_rel_satD)
   apply (clarsimp simp: tlb_rel_sat_def)
   apply (drule saturated_lookup_not_miss)
   apply (clarsimp simp: consistent0_def)
   done


lemma det1_miss_sat_pa:
  "\<lbrakk>lookup (TLB s) (ASID s) va = Miss ;  mmu_translate_det va s = (pa, s') ; tlb_rel_sat s t ;
       consistent t va ; mmu_translate_sat va t = (pa', t') \<rbrakk> \<Longrightarrow>  pa' = pa"
  apply (frule (2) lookup_miss_sat_hit)
  apply (frule tlb_rel_satD)
  apply (simp add: tlb_rel_sat_def , clarsimp)
  apply (frule sat_state_tlb , clarsimp)
  apply (clarsimp simp: mmu_translate_det_def
                        mmu_translate_sat_def Let_def raise'exception_def split: split_if_asm)
done


lemma state_change_is_fault_sat:
  "\<lbrakk>saturated s ; consistent s va ; is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) va) ;
      mmu_translate_sat va s = (pa , s') \<rbrakk> \<Longrightarrow> 
          raise'exception (PAGE_FAULT ''more info'') s = (pa, s') "
  apply (frule sat_con_not_miss_incon , simp)
  apply (clarsimp simp: mmu_translate_sat_def split_def Let_def)
  apply (frule sat_state_tlb ; clarsimp)
  apply (cases "lookup (TLB s) (ASID s) va")
    apply clarsimp
   apply clarsimp
  apply (clarsimp split: split_if_asm simp:raise'exception_def)
  done


lemma lookup_hit_sat_hit:
  "\<lbrakk> lookup (TLB s) (ASID s) va = Hit x ; tlb_rel_sat s t ; consistent t va\<rbrakk> \<Longrightarrow>
        lookup (TLB t) (ASID t) va = Hit (pt_walk (ASID s) (MEM s) (TTBR0 s) va)"
  apply (frule tlb_rel_satD , safe)
  apply (clarsimp simp: tlb_rel_sat_def)
  apply (frule sat_con_not_miss_incon , simp)
  apply (clarsimp simp: consistent0_def)
  done

lemma lookup_hit_sat_unsat_equal:
  "\<lbrakk> lookup (TLB s) (ASID s) va = Hit x ; tlb_rel_sat s t ; consistent t va\<rbrakk> \<Longrightarrow>
        x = pt_walk (ASID s) (MEM s) (TTBR0 s) va"
  apply (frule (2) lookup_hit_sat_hit)
  apply (frule tlb_rel_satD)
  apply (clarsimp simp: tlb_rel_sat_def)
  apply (frule tlb_mono [of _ _ "ASID s" va])
  apply clarsimp
  done


lemma det1_hit_sat_pa:
  "\<lbrakk>lookup (TLB s) (ASID s) va = Hit (pt_walk (ASID s) (MEM s) (TTBR0 s) va) ;  
      mmu_translate_det va s = (pa, s') ; tlb_rel_sat s t ; consistent t va ; 
        mmu_translate_sat va t = (pa', t') \<rbrakk> \<Longrightarrow> pa' = pa"
  apply (frule (2) lookup_hit_sat_hit)
  apply (frule tlb_rel_satD)
  apply (simp add: tlb_rel_sat_def , clarsimp)
  apply (frule sat_state_tlb , clarsimp)
  apply (clarsimp simp: mmu_translate_det_def
                        mmu_translate_sat_def Let_def raise'exception_def split: split_if_asm)
done

lemma lookup_incon_subset [simp]:
  "\<lbrakk> s \<subseteq> t ; lookup s a va = Incon \<rbrakk> \<Longrightarrow> 
       lookup t a va = Incon"
  by (metis less_eq_lookup_type lookup_type.simps(3) tlb_mono)


lemma lookup_incon_saturated :
  "\<lbrakk>lookup (TLB s) (ASID s) va = Incon ;  tlb_rel_sat s t\<rbrakk> \<Longrightarrow> 
       lookup (TLB t) (ASID t) va = Incon"
   by (frule tlb_rel_satD , clarsimp)


lemma
  "\<lbrakk>lookup (TLB s) (ASID s) va = Incon ;  
      mmu_translate_det va s = (pa, s') ; tlb_rel_sat s t ; 
        mmu_translate_sat va t = (pa', t') \<rbrakk> \<Longrightarrow> exception s' = exception t'"
  apply (frule lookup_incon_saturated , simp)
  apply (frule tlb_rel_satD)
  apply (simp add: tlb_rel_sat_def , clarsimp)
  apply (frule sat_state_tlb)
  apply (clarsimp simp: mmu_translate_det_def mmu_translate_sat_def Let_def  
                  split: split_if_asm simp add:raise'exception_def)
done


lemma lookup_miss_tlb_subset1:
  "\<lbrakk>lookup (TLB s) (ASID s) va = Miss ; \<not>is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) va) ;
     mmu_translate_det va s = (pa, s') \<rbrakk> \<Longrightarrow> 
              TLB s' = TLB s \<union> {pt_walk (ASID s) (MEM s) (TTBR0 s) va} "
  by (clarsimp simp add: mmu_translate_det_def Let_def)
  

lemma  lookup_miss_tlb_subset2:
  "\<lbrakk>lookup (TLB s) (ASID s) va = Miss ; is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) va) ;
     mmu_translate_det va s = (pa, s') \<rbrakk> \<Longrightarrow> 
              TLB s' = TLB s "
  apply (clarsimp simp add: mmu_translate_det_def Let_def)
  apply (clarsimp simp:raise'exception_def split: split_if_asm)
done
  
lemma lookup_miss_tlb_subset:
  "\<lbrakk>lookup (TLB s) (ASID s) va = Miss ; mmu_translate_det va s = (pa, s')\<rbrakk> \<Longrightarrow> 
           TLB s' = TLB s  \<or> TLB s' = TLB s \<union> {pt_walk (ASID s) (MEM s) (TTBR0 s) va} "
  apply (cases "is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) va)" )
   apply (drule (2) lookup_miss_tlb_subset2 , clarsimp)
  apply (drule (2) lookup_miss_tlb_subset1 , clarsimp)
done 

lemma lookup_incon_tlb_equal:
  "\<lbrakk>lookup (TLB s) (ASID s) va = Incon ; mmu_translate_det va s = (pa, s')  \<rbrakk> \<Longrightarrow> 
        TLB s' = TLB s"
  by (clarsimp simp add: mmu_translate_det_def Let_def raise'exception_def split:split_if_asm)
 

lemma lookup_hit_tlb_equal:
  "\<lbrakk>lookup (TLB s) (ASID s) va = Hit x ; mmu_translate_det va s = (pa, s') \<rbrakk> \<Longrightarrow>  TLB s' = TLB s "
  by (clarsimp simp add: mmu_translate_det_def Let_def raise'exception_def split:split_if_asm)

(* important *)
lemma mmu_translate_tlbs_rel:
  "\<lbrakk> mmu_translate_det va s = (pa, s') \<rbrakk> \<Longrightarrow>
  TLB s' = TLB s \<or>  TLB s' = TLB s \<union> {pt_walk (ASID s) (MEM s) (TTBR0 s) va} "
  apply (cases "lookup (TLB s) (ASID s) va")
    apply (drule (2)lookup_miss_tlb_subset)
   apply (rule disjI1)
   apply (drule (2) lookup_incon_tlb_equal)
  apply (rule disjI1)
  apply (drule (2) lookup_hit_tlb_equal)
done  


(* important *)
lemma mmu_translate_det_sat_refine:
  "\<lbrakk> mmu_translate_det va s = (pa, s'); consistent t va; tlb_rel_sat s t  \<rbrakk> \<Longrightarrow>
  let (pa', t') = mmu_translate_sat va t
  in pa' = pa \<and> consistent t' va \<and> tlb_rel_sat s' t'"
  apply (frule (1) tlb_rel_sat_consistent)
  apply (frule tlb_rel_satD)
  apply (subgoal_tac "lookup (TLB s) (ASID s) va \<le> lookup (TLB t \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s))) (ASID s) va")
   prefer 2
   apply (simp add: saturated_def sup.absorb1 tlb_mono tlb_rel_sat_def)
  apply (clarsimp simp: mmu_translate_det_def mmu_translate_sat_def split_def Let_def)
  apply (subgoal_tac "TLB t = TLB t \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s))")
   prefer 2
   apply (fastforce simp: tlb_rel_sat_def saturated_def)
  apply (cases "lookup (TLB t \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s))) (ASID s) va")
    apply (clarsimp simp: tlb_rel_sat_def)
    apply (frule saturated_lookup_not_miss , clarsimp)
   apply (clarsimp simp:consistent0_def)
  apply (clarsimp)
  apply (cases "lookup (TLB s) (ASID s) va"; clarsimp)
   apply (clarsimp simp: consistent0_def Let_def tlb_rel_sat_def
                         lookup_in_tlb raise'exception_def split: split_if_asm)
   apply (cases s, cases t, clarsimp simp:saturated_def)
  apply (clarsimp split: split_if_asm simp:raise'exception_def tlb_rel_sat_def)
  apply (cases s, cases t, clarsimp simp:saturated_def)
done

(* important *)
lemma  mmu_translate_sat_refine_non_det:        
  "\<lbrakk> mmu_translate va s = (pa, s'); consistent t va; tlb_rel_sat s t \<rbrakk> \<Longrightarrow>
       let (pa', t') = mmu_translate_sat va t
                 in pa' = pa  \<and> consistent t' va \<and> tlb_rel_sat s' t'"
  apply (simp add: mmu_translate_def2)
  by (drule (1)mmu_translate_det_sat_refine ; fastforce simp: tlb_rel_sat_def)


lemma mmu_translate_sat_TLB_union:
  "mmu_translate_sat v s = (p,t) \<Longrightarrow> 
      TLB t = TLB s \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s))"
  apply (clarsimp simp: mmu_translate_sat_def Let_def)
  apply (cases "lookup (TLB s \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s))) (ASID s) v")
    apply (clarsimp simp:raise'exception_def split:split_if_asm) +
done


lemma mmu_translate_sat_sat:
  "mmu_translate_sat v s = (p,t) \<Longrightarrow> 
      saturated t"
  apply (clarsimp simp: mmu_translate_sat_def Let_def)
  apply (cases "lookup (TLB s \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s))) (ASID s) v")
    apply (unfold saturated_def) [1]
    apply (clarsimp simp:raise'exception_def split:split_if_asm)
   apply (unfold saturated_def) [1]
   apply (clarsimp simp:raise'exception_def split:split_if_asm)
  apply (unfold saturated_def) [1]
  apply (clarsimp simp:raise'exception_def split:split_if_asm)
done


find_theorems "Store _ "

find_theorems "StoreByte _ "

(* mem1s is reading memory using saturated TLB *)
(* Here pa can be undefined either because of PAGE_FAULT or IMPLEMENTATION_DEFINED (incon) *)
(* state can be changed either because of TLB update, or raise'exception *)
definition
  mem1s :: "32 word \<Rightarrow> state \<Rightarrow> bool list \<times> state"
where
  "mem1s \<equiv> \<lambda>va. do {
     mem \<leftarrow> read_state MEM;  
     pa \<leftarrow> mmu_translate_sat va;
     let v = mem pa;  (*arent these two *)
     v \<leftarrow> return (mem pa);  (* same? *) 
     return (nat_to_bitstring (nat (uint v)))
  }"                           



(* writing to memory using saturated TLB *)
definition
  "write'mem'sat" :: "bool list \<times> 32 word \<times> nat \<Rightarrow> state \<Rightarrow> unit \<times> state"
where
  "write'mem'sat \<equiv> \<lambda>(value, vaddr, size). do {
     (* original TLB before memory translation *)
     tlb0  <- read_state TLB;
     paddr <- mmu_translate_sat vaddr;
     asid  <- read_state ASID;
     ttbr0 <- read_state TTBR0;
     (* size is in {1, 2, 4, 8} and will be aligned, so will not cross page boundaries *)
     write'mem1 (value, paddr, size);
     mem   <- read_state MEM; (*mem is updated after write'mem1 *) 
     let all_entries = pt_walk asid mem ttbr0 ` UNIV;
     let tlb = tlb0 \<union> all_entries;
     update_state (\<lambda>s. s\<lparr> TLB := tlb \<rparr>)
  }"

lemma write'mem'sat_tlb_TLB_sat:
  "write'mem'sat (v,va,sz) s = ((), t) \<Longrightarrow>
                TLB t = TLB s \<union> pt_walk (ASID s) (MEM t) (TTBR0 s)` UNIV  "
  apply (clarsimp simp: write'mem'sat_def)
  apply (cases "mmu_translate_sat va s", clarsimp)
  apply (case_tac "write'mem1 (v, a, sz) b", clarsimp)
  apply (subgoal_tac "ASID s = ASID b \<and> TTBR0 s = TTBR0 b" , clarsimp)
  apply (clarsimp simp: mmu_translate_sat_def Let_def,
                  cases "lookup (TLB s \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s))) (ASID s) va")
    apply (clarsimp simp: raise'exception_def split: split_if_asm) +
done

lemma mem'write'asid_ttbr0:
  "write'mem'sat (v, va, sz) s = ((), t) \<Longrightarrow>
         ASID s = ASID t \<and> TTBR0 s = TTBR0 t"
  apply (clarsimp simp: write'mem'sat_def)
  apply (cases "mmu_translate_sat va s" , clarsimp)
  apply (subgoal_tac "ASID s = ASID b \<and> TTBR0 s = TTBR0 b")
   apply (subgoal_tac "ASID b = ASID t \<and> TTBR0 b = TTBR0 t", clarsimp)
   apply (clarsimp simp: write'mem1_def raise'exception_def split:split_if_asm)
  apply (clarsimp simp: mmu_translate_sat_def Let_def)
  apply (cases "lookup (TLB s \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s))) (ASID s) va ")
    apply (clarsimp simp: raise'exception_def split:split_if_asm)+
done

(* IMPORTANT *)
lemma write'mem'sat_saturated:
  "write'mem'sat (v,va,sz) s = ((), t) \<Longrightarrow> saturated t"
  apply (clarsimp simp: write'mem'sat_def) 
  apply (cases "mmu_translate_sat va s" , clarsimp)
  apply (case_tac "write'mem1 (v, a, sz) b" , clarsimp)
  apply (subgoal_tac "ASID b = ASID ba \<and> TTBR0 b = TTBR0 ba") 
   apply (clarsimp simp: saturated_def)
  apply (clarsimp simp: write'mem1_def raise'exception_def split:split_if_asm)
done
 


lemma mem1s_TLB_sat:
  "mem1s va s = (v, t) \<Longrightarrow> 
      TLB t = TLB s \<union> pt_walk (ASID s) (MEM s) (TTBR0 s)` UNIV "
  apply (clarsimp simp: mem1s_def)
  apply (cases "mmu_translate_sat va s")
  apply (frule mmu_translate_sat_TLB_union , clarsimp)
done




(* Here mem1s is saturated *)
lemma write_read_sat_tlb:
  "\<lbrakk>write'mem'sat (v,va,sz) s = ((), t) ; mem1s va t = (v, r)\<rbrakk> \<Longrightarrow> TLB t = TLB r"
  apply (subgoal_tac "saturated t")
   apply (clarsimp simp: mem1s_def)
   apply (cases "mmu_translate_sat va t")
   apply (clarsimp simp: mmu_translate_sat_def Let_def)
   apply (cases "lookup (TLB t \<union> range (pt_walk (ASID t) (MEM t) (TTBR0 t))) (ASID t) va")
     apply (frule saturated_lookup_not_miss)
     apply (frule sat_state_tlb ; clarsimp)
    apply (clarsimp simp:raise'exception_def split:split_if_asm)
     using saturated_def apply force
    using saturated_def apply force
   apply (clarsimp split:split_if_asm simp:raise'exception_def saturated_def, force)
    using saturated_def apply force
   using saturated_def apply force
  apply (frule write'mem'sat_tlb_TLB_sat)
  apply (frule mem'write'asid_ttbr0 ; erule conjE ; clarsimp)
  using saturated_def apply simp
done


definition
  translation_table1 ::"state \<Rightarrow> 32 word set \<times> state"
where
  "translation_table1 \<equiv> do {
     mem   <- read_state MEM;
     ttbr0 <- read_state TTBR0;
     let ttbr0_mask = ttbr0 AND 0xFFFFC000;
     (* Physical addresses of first level translation table *)
     let pa_l1 = {x. ttbr0_mask \<le> x \<and> x \<le> (ttbr0_mask + (16384-1))};
     (* set of physical addresses of first level descriptors *)
     let pa_l1_des = {x. x \<in> pa_l1 \<and> (ucast(x OR 0xFFFFFFFC):: 2 word) = 0x0};
     (* set of first level descriptor *)
     (* word_fetch is the function for memory read using physical address *)
     let l1_des = word_fetch mem ` pa_l1_des;
     (* set of base addresses of second level translation-tables (page-table) *)
     let l2_ba = (\<lambda>x. x AND 0xFFFFFC00) ` {x. x \<in> l1_des \<and> x AND 0x3 = 0x1}; 
     (* set of physical addresses of second-level translation tables (1KB each) *)  
     let pa_l2 = \<Union>( (\<lambda>x. {y. x \<le> y \<and> y \<le> x + (1024 -1)}) ` l2_ba ); 
     (* second level page tables are not fixed *)
     return (pa_l1 \<union> pa_l2)
   }"


(* set of all 8 word physical addresses of translation table *)
definition
  translation_table_pa ::"mem_type \<Rightarrow> ttbr0 \<Rightarrow> 32 word set"
where
  "translation_table_pa memory ttbr0 \<equiv> 
   let ttbr0_mask = ttbr0 AND 0xFFFFC000;
       (* Physical addresses of first level translation table *)
       pa_l1 = {x. ttbr0_mask \<le> x \<and> x \<le> (ttbr0_mask + (16384 -1))};
       (* set of physical addresses of first level descriptors *)
       pa_l1_des = {x. x \<in> pa_l1 \<and> (ucast(x OR 0xFFFFFFFC):: 2 word) = 0x0};
       (* set of first level descriptor *)
       (* word_fetch is the function for memory read using physical address *)
       l1_des = word_fetch memory ` pa_l1_des;
       (* set of base addresses of second level translation-tables (page-table) *)
       l2_ba = (\<lambda>x. x AND 0xFFFFFC00) ` {x. x \<in> l1_des \<and> x AND 0x3 = 0x1}; 
       (* set of physical addresses of second-level translation tables (1KB each) *)  
       pa_l2 = \<Union>( (\<lambda>x. {y. x \<le> y \<and> y \<le> x + (1024-1)}) ` l2_ba )
       (* second level page tables are not fixed *)
   in pa_l1 \<union> pa_l2" 


(* set of all the descriptors of translation table *)
definition
  translation_table_des::"mem_type \<Rightarrow> ttbr0 \<Rightarrow> 32 word set"
where
  "translation_table_des memory ttbr0 \<equiv> 
   let ttbr0_mask = ttbr0 AND 0xFFFFC000;
       (* Physical addresses of first level translation table *)
       pa_l1 = {x. ttbr0_mask \<le> x \<and> x \<le> (ttbr0_mask + (16384-1))};
       (* set of physical addresses of first level descriptors *)
       pa_l1_des = {x. x \<in> pa_l1 \<and> (ucast(x OR 0xFFFFFFFC):: 2 word) = 0x0};
       (* set of first level descriptor *)
       (* word_fetch is the function for memory read using physical address *)
       l1_des = word_fetch memory ` pa_l1_des;
       (* set of base addresses of second level translation-tables (page-table) *)
       l2_ba = (\<lambda>x. x AND 0xFFFFFC00) ` {x. x \<in> l1_des \<and> x AND 0x3 = 0x1}; 
       (* set of physical addresses of second-level translation tables (1KB each) *)  
       pa_l2 = \<Union>( (\<lambda>x. {y. x \<le> y \<and> y \<le> x + (1024-1)}) ` l2_ba );
       (* second level page tables are not fixed *)
       (* set of physical addresses of second level descriptors *)
       pa_l2_des = {x. x \<in> pa_l2 \<and> (ucast(x OR 0xFFFFFFFC):: 2 word) = 0x0};
       (* set of second level descriptor *)
       l2_des = word_fetch memory ` pa_l2_des
   in l1_des \<union> l2_des" 

definition
  translation_table_des1::"mem_type \<Rightarrow> ttbr0 \<Rightarrow> 32 word set"
where
  "translation_table_des1 memory ttbr0 \<equiv> 
   let ttbr0_mask = ttbr0 AND 0xFFFFC000;
       (* Physical addresses of first level translation table *)
       pa_l1 = {x. ttbr0_mask \<le> x \<and> x \<le> (ttbr0_mask + (16384-1))};
       (* set of physical addresses of first level descriptors *)
       pa_l1_des = {x. x \<in> pa_l1 \<and> (ucast(x OR 0xFFFFFFFC):: 2 word) = 0x0}
       (* set of first level descriptor *)
       (* word_fetch is the function for memory read using physical address *)
    in  (word_fetch memory ` pa_l1_des)" 


definition
  translation_table_des2::"mem_type \<Rightarrow> ttbr0 \<Rightarrow> 32 word set"
where
  "translation_table_des2 memory ttbr0 \<equiv> 
   let ttbr0_mask = ttbr0 AND 0xFFFFC000;
       (* Physical addresses of first level translation table *)
       pa_l1 = {x. ttbr0_mask \<le> x \<and> x \<le> (ttbr0_mask + (16384-1))};
       (* set of physical addresses of first level descriptors *)
       pa_l1_des = {x. x \<in> pa_l1 \<and> (ucast(x OR 0xFFFFFFFC):: 2 word) = 0x0};
       (* set of first level descriptor *)
       (* word_fetch is the function for memory read using physical address *)
       l1_des = word_fetch memory ` pa_l1_des;
       (* set of base addresses of second level translation-tables (page-table) *)
       l2_ba = (\<lambda>x. x AND 0xFFFFFC00) ` {x. x \<in> l1_des \<and> x AND 0x3 = 0x1}; 
       (* set of physical addresses of second-level translation tables (1KB each) *)  
       pa_l2 = \<Union>( (\<lambda>x. {y. x \<le> y \<and> y \<le> x + (1024-1)}) ` l2_ba );
       (* second level page tables are not fixed *)
       (* set of physical addresses of second level descriptors *)
       pa_l2_des = {x. x \<in> pa_l2 \<and> (ucast(x OR 0xFFFFFFFC):: 2 word) = 0x0}
       (* set of second level descriptor *)
       in  word_fetch memory ` pa_l2_des" 

definition
  translation_table_pa_des1::"mem_type \<Rightarrow> ttbr0 \<Rightarrow> (32 word \<times>32 word) set"
where
  "translation_table_pa_des1 memory ttbr0 \<equiv> 
   let ttbr0_mask = ttbr0 AND 0xFFFFC000;
       (* Physical addresses of first level translation table *)
       pa_l1 = {x. ttbr0_mask \<le> x \<and> x \<le> (ttbr0_mask + (16384-1))};
       (* set of physical addresses of first level descriptors *)
       pa_l1_des = {x. x \<in> pa_l1 \<and> (ucast(x OR 0xFFFFFFFC):: 2 word) = 0x0}
       (* set of first level descriptor *)
       (* word_fetch is the function for memory read using physical address *)
    in (\<lambda>x. (x , word_fetch memory x)) ` pa_l1_des" 

definition
  translation_table_pa_des2::"mem_type \<Rightarrow> ttbr0 \<Rightarrow> (32 word \<times> 32 word) set"
where
  "translation_table_pa_des2 memory ttbr0 \<equiv> 
   let ttbr0_mask = ttbr0 AND 0xFFFFC000;
       (* Physical addresses of first level translation table *)
       pa_l1 = {x. ttbr0_mask \<le> x \<and> x \<le> (ttbr0_mask + (16384-1))};
       (* set of physical addresses of first level descriptors *)
       pa_l1_des = {x. x \<in> pa_l1 \<and> (ucast(x OR 0xFFFFFFFC):: 2 word) = 0x0};
       (* set of first level descriptor *)
       (* word_fetch is the function for memory read using physical address *)
       l1_des = word_fetch memory ` pa_l1_des;
       (* set of base addresses of second level translation-tables (page-table) *)
       l2_ba = (\<lambda>x. x AND 0xFFFFFC00) ` {x. x \<in> l1_des \<and> x AND 0x3 = 0x1}; 
       (* set of physical addresses of second-level translation tables (1KB each) *)  
       pa_l2 = \<Union>( (\<lambda>x. {y. x \<le> y \<and> y \<le> x + (1024-1)}) ` l2_ba );
       (* second level page tables are not fixed *)
       (* set of physical addresses of second level descriptors *)
       pa_l2_des = {x. x \<in> pa_l2 \<and> (ucast(x OR 0xFFFFFFFC):: 2 word) = 0x0}
       (* set of second level descriptor *)
    in (\<lambda>x. (x , word_fetch memory x)) ` pa_l2_des" 


definition
  translation_table_pa_des::"mem_type \<Rightarrow> ttbr0 \<Rightarrow> (32 word \<times> 32 word) set"
where
  "translation_table_pa_des memory ttbr0 \<equiv> 
   let ttbr0_mask = ttbr0 AND 0xFFFFC000;
       (* Physical addresses of first level translation table *)
       pa_l1 = {x. ttbr0_mask \<le> x \<and> x \<le> (ttbr0_mask + (16384-1))};
       (* set of physical addresses of first level descriptors *)
       pa_l1_des = {x. x \<in> pa_l1 \<and> (ucast(x OR 0xFFFFFFFC):: 2 word) = 0x0};
       (* set of first level descriptor *)
       (* word_fetch is the function for memory read using physical address *)
       l1_des = word_fetch memory ` pa_l1_des;
       l1_pa_des = (\<lambda>x. (x , word_fetch memory x)) ` pa_l1_des;
       (* set of base addresses of second level translation-tables (page-table) *)
       l2_ba = (\<lambda>x. x AND 0xFFFFFC00) ` {x. x \<in> l1_des \<and> x AND 0x3 = 0x1}; 
       (* set of physical addresses of second-level translation tables (1KB each) *)  
       pa_l2 = \<Union>( (\<lambda>x. {y. x \<le> y \<and> y \<le> x + (1024-1)}) ` l2_ba );
       (* second level page tables are not fixed *)
       (* set of physical addresses of second level descriptors *)
       pa_l2_des = {x. x \<in> pa_l2 \<and> (ucast(x OR 0xFFFFFFFC):: 2 word) = 0x0};
       (* set of second level descriptor *)
       l2_des = word_fetch memory ` pa_l2_des;
       l2_pa_des = (\<lambda>x. (x , word_fetch memory x)) ` pa_l2_des
   in l1_pa_des \<union> l2_pa_des" 




lemma tt_pa_des_first_level:
  "\<lbrakk>ttbr01 = ttbr02 ; translation_table_pa_des1 memory1 ttbr01 = translation_table_pa_des1 memory2 ttbr02  \<rbrakk> \<Longrightarrow>
    (\<lambda>x. (x, word_fetch memory1 x)) ` {x. x \<in> {x. ttbr01 AND 0xFFFFC000 \<le> x \<and> x \<le> ((ttbr01 AND 0xFFFFC000) + (16384-1))} \<and> (ucast(x OR 0xFFFFFFFC):: 2 word) = 0x0} =
    (\<lambda>x. (x, word_fetch memory2 x)) ` {x. x \<in> {x. ttbr02 AND 0xFFFFC000 \<le> x \<and> x \<le> ((ttbr02 AND 0xFFFFC000) + (16384-1))} \<and> (ucast(x OR 0xFFFFFFFC):: 2 word) = 0x0}"
    by (clarsimp simp: translation_table_pa_des1_def Let_def)


lemma tt_first_level_image:
  "translation_table_pa_des1 memory ttbr0 =
   (\<lambda>x. (x, word_fetch memory x)) ` {x. x \<in> {x. ttbr0 AND 0xFFFFC000 \<le> x \<and> x \<le> ((ttbr0 AND 0xFFFFC000) + (16384-1))} \<and> (ucast(x OR 0xFFFFFFFC):: 2 word) = 0x0} "
  by (clarsimp simp: translation_table_pa_des1_def Let_def)


lemma tt_second_level_image:
  "translation_table_pa_des2 memory ttbr0 = 
  (\<lambda>x. (x, word_fetch memory x)) ` {x. x \<in>  \<Union>( (\<lambda>x. {y. x \<le> y \<and> y \<le> x + (1024-1)}) `(\<lambda>x. x AND 0xFFFFFC00) `  {x. x \<in> word_fetch memory ` {x. x \<in> {x. ttbr0 AND 0xFFFFC000 \<le> x \<and> x \<le> ((ttbr0 AND 0xFFFFC000) + (16384-1))} \<and> (ucast(x OR 0xFFFFFFFC):: 2 word) = 0x0} \<and> x AND 0x3 = 0x1} ) \<and> (ucast(x OR 0xFFFFFFFC):: 2 word) = 0x0} "
  by (clarsimp simp: translation_table_pa_des2_def Let_def)
  
lemma abcd5_n:
  "\<lbrakk>ttbr01 = ttbr02 ;
     translation_table_pa_des2 memory1 ttbr01 = translation_table_pa_des2 memory2 ttbr02  \<rbrakk> \<Longrightarrow>
  (\<lambda>x. (x, word_fetch memory1 x)) `  {x. x \<in>  \<Union>( (\<lambda>x. {y. x \<le> y \<and> y \<le> x + (1024-1)}) `(\<lambda>x. x AND 0xFFFFFC00) `  {x. x \<in> word_fetch memory1 ` {x. x \<in> {x. ttbr01 AND 0xFFFFC000 \<le> x \<and> x \<le> ((ttbr01 AND 0xFFFFC000) + (16384-1))} \<and> (ucast(x OR 0xFFFFFFFC):: 2 word) = 0x0} \<and> x AND 0x3= 0x1} ) \<and> (ucast(x OR 0xFFFFFFFC):: 2 word) = 0x0} = 
  (\<lambda>x. (x, word_fetch memory2 x)) `  {x. x \<in> \<Union>( (\<lambda>x. {y. x \<le> y \<and> y \<le> x + (1024-1)}) ` (\<lambda>x. x AND 0xFFFFFC00) `  {x. x \<in> word_fetch memory2 ` {x. x \<in> {x. ttbr02 AND 0xFFFFC000 \<le> x \<and> x \<le> ((ttbr02 AND 0xFFFFC000) + (16384-1))} \<and> (ucast(x OR 0xFFFFFFFC):: 2 word) = 0x0} \<and> x AND 0x3 = 0x1}) \<and> (ucast(x OR 0xFFFFFFFC):: 2 word) = 0x0}"
  apply (clarsimp simp : tt_second_level_image)
done

lemma tt_levels:
  "\<lbrakk>ttbr01 = ttbr02 ; translation_table_pa_des1 memory1 ttbr01 = translation_table_pa_des1 memory2 ttbr02 ;
     translation_table_pa_des2 memory1 ttbr01 = translation_table_pa_des2 memory2 ttbr02  \<rbrakk> \<Longrightarrow>
    translation_table_pa_des memory1 ttbr01 = translation_table_pa_des memory2 ttbr02"
  apply (frule (1)tt_pa_des_first_level)
  apply (frule_tac ?memory1.0 = "memory1" and ?memory2.0 = "memory2" in abcd5_n) thm abcd5_n
   apply clarsimp
  apply (clarsimp simp: translation_table_pa_des_def)
  done

lemma tt_pa_des_union_level:
  "translation_table_pa_des memory ttbr0 = 
    (\<lambda>x. (x, word_fetch memory x)) ` {x. x \<in> {x. ttbr0 AND 0xFFFFC000 \<le> x \<and> x \<le> ((ttbr0 AND 0xFFFFC000) + (16384-1))} \<and> (ucast(x OR 0xFFFFFFFC):: 2 word) = 0x0} \<union>
    (\<lambda>x. (x, word_fetch memory x)) `  {x. x \<in>  \<Union>( (\<lambda>x. {y. x \<le> y \<and> y \<le> x + (1024-1)}) `(\<lambda>x. x AND 0xFFFFFC00) `  {x. x \<in> word_fetch memory ` {x. x \<in> {x. ttbr0 AND 0xFFFFC000 \<le> x \<and> x \<le> ((ttbr0 AND 0xFFFFC000) + (16384-1))} \<and> (ucast(x OR 0xFFFFFFFC):: 2 word) = 0x0} \<and> x AND 0x3 = 0x1} ) \<and> (ucast(x OR 0xFFFFFFFC):: 2 word) = 0x0}"
  apply (clarsimp simp : tt_first_level_image [symmetric] tt_second_level_image [symmetric])
  apply (clarsimp simp: translation_table_pa_des_def Let_def)
  done

lemma tt_rewrite:
  "\<lbrakk>ttbr01 = ttbr02 ; translation_table_pa_des memory1 ttbr01 = translation_table_pa_des memory2 ttbr02  \<rbrakk> \<Longrightarrow>
    (\<lambda>x. (x, word_fetch memory1 x)) ` {x. x \<in> {x. ttbr01 AND 0xFFFFC000 \<le> x \<and> x \<le> ((ttbr01 AND 0xFFFFC000) + (16384-1))} \<and> (ucast(x OR 0xFFFFFFFC):: 2 word) = 0x0} \<union>
    (\<lambda>x. (x, word_fetch memory1 x)) `  {x. x \<in>  \<Union>( (\<lambda>x. {y. x \<le> y \<and> y \<le> x + (1024-1)}) `(\<lambda>x. x AND 0xFFFFFC00) `  {x. x \<in> word_fetch memory1 ` {x. x \<in> {x. ttbr01 AND 0xFFFFC000 \<le> x \<and> x \<le> ((ttbr01 AND 0xFFFFC000) + (16384-1))} \<and> (ucast(x OR 0xFFFFFFFC):: 2 word) = 0x0} \<and> x AND 0x3= 0x1} ) \<and> (ucast(x OR 0xFFFFFFFC):: 2 word) = 0x0} =
   (\<lambda>x. (x, word_fetch memory2 x)) ` {x. x \<in> {x. ttbr02 AND 0xFFFFC000 \<le> x \<and> x \<le> ((ttbr02 AND 0xFFFFC000) + (16384-1))} \<and> (ucast(x OR 0xFFFFFFFC):: 2 word) = 0x0} \<union>
   (\<lambda>x. (x, word_fetch memory2 x)) `  {x. x \<in>  \<Union>( (\<lambda>x. {y. x \<le> y \<and> y \<le> x + (1024-1)}) `(\<lambda>x. x AND 0xFFFFFC00) `  {x. x \<in> word_fetch memory2 ` {x. x \<in> {x. ttbr02 AND 0xFFFFC000 \<le> x \<and> x \<le> ((ttbr02 AND 0xFFFFC000) + (16384-1))} \<and> (ucast(x OR 0xFFFFFFFC):: 2 word) = 0x0} \<and> x AND 0x3 = 0x1} ) \<and> (ucast(x OR 0xFFFFFFFC):: 2 word) = 0x0}"
  apply clarify
   apply (clarsimp simp: tt_pa_des_union_level)
  done





lemma first_level_des_equal:
  "\<lbrakk>ttbr01 = ttbr02 ; translation_table_pa_des memory1 ttbr01 = translation_table_pa_des memory2 ttbr02  \<rbrakk> \<Longrightarrow>
    (\<lambda>x. x AND 0xFFFFFC00) ` {x. x \<in> word_fetch memory1 ` {x. x \<in> {x. ttbr01 AND 0xFFFFC000 \<le> x \<and> x \<le> ((ttbr01 AND 0xFFFFC000) + (16384-1))} \<and> (ucast(x OR 0xFFFFFFFC):: 2 word) = 0x0}
      \<and> x AND 3 = 1}
      =  (\<lambda>x. x AND 0xFFFFFC00) ` {x. x \<in>  word_fetch memory2 ` {x. x \<in> {x. ttbr02 AND 0xFFFFC000 \<le> x \<and> x \<le> ((ttbr02 AND 0xFFFFC000) + (16384-1))} \<and> (ucast(x OR 0xFFFFFFFC):: 2 word) = 0x0}
           \<and> x AND 3 = 1}"
  apply (frule (1) tt_rewrite)
  apply blast
done


lemma good:
  "\<lbrakk>ttbr01 = ttbr02 ; translation_table_pa_des memory1 ttbr01 = translation_table_pa_des memory2 ttbr02  \<rbrakk> \<Longrightarrow>
   {x. x \<in> \<Union>( (\<lambda>x. {y. x \<le> y \<and> y \<le> x + (1024-1)}) ` (\<lambda>x. x AND 0xFFFFFC00) ` {x. x \<in> word_fetch memory1 ` {x. x \<in> {x. ttbr01 AND 0xFFFFC000 \<le> x \<and> x \<le> ((ttbr01 AND 0xFFFFC000) + (16384-1))} \<and> (ucast(x OR 0xFFFFFFFC):: 2 word) = 0x0}
      \<and> x AND 3 = 1}) \<and> (ucast(x OR 0xFFFFFFFC):: 2 word) = 0x0} =   
     {x. x \<in> \<Union>( (\<lambda>x. {y. x \<le> y \<and> y \<le> x + (1024-1)}) ` (\<lambda>x. x AND 0xFFFFFC00) ` {x. x \<in>  word_fetch memory2 ` {x. x \<in> {x. ttbr02 AND 0xFFFFC000 \<le> x \<and> x \<le> ((ttbr02 AND 0xFFFFC000) + (16384-1))} \<and> (ucast(x OR 0xFFFFFFFC):: 2 word) = 0x0}
           \<and> x AND 3 = 1} ) \<and> (ucast(x OR 0xFFFFFFFC):: 2 word) = 0x0}  "
  apply (frule (1) first_level_des_equal)
   by auto

(*this is good *)


lemma func_map:
  "\<lbrakk>a \<in> X ; b \<in> Y ; (\<lambda>x. (x, f x)) ` (XX \<union> X) = (\<lambda>x. (x, g x)) ` (YY \<union> Y) ; a = b \<rbrakk> \<Longrightarrow> f a = g b"
  by auto

lemma uff1:
  "\<lbrakk>a \<in> XX ; b \<in> YY ; (\<lambda>x. (x, f x)) ` (XX \<union> X) = (\<lambda>x. (x, g x)) ` (YY \<union> Y) ; a = b \<rbrakk> \<Longrightarrow> f a = g b"
  by auto

lemma uff2: 
  "\<lbrakk>a \<in> XX ; b \<in> YY ; (\<lambda>x. (x, f x)) ` (XX \<union> X) = (\<lambda>x. (x, g x)) ` (YY \<union> Y) ; a = b;
   f a \<in> X  ; g b \<in> Y\<rbrakk> \<Longrightarrow> f (f a) = g (g b)"
   by blast

lemma uff3: (* for table 1 *)
  "\<lbrakk>(\<lambda>x. (x, f x)) ` (XX \<union> X) = (\<lambda>x. (x, g x)) ` (YY \<union> Y) ; XX = YY  \<rbrakk> \<Longrightarrow>
   (\<lambda>x. (x, f x)) ` XX = (\<lambda>x. (x, g x)) ` YY "
   by blast

lemma uff4: (* for table 2 *)
  "\<lbrakk>(\<lambda>x. (x, f x)) ` (XX \<union> X) = (\<lambda>x. (x, g x)) ` (YY \<union> Y) ; XX = YY ;
       X = Y  \<rbrakk> \<Longrightarrow>
   (\<lambda>x. (x, f x)) ` X = (\<lambda>x. (x, g x)) ` Y "
   by blast


lemma pt_walk_eq:
  "\<lbrakk>ttbr01 = ttbr02 ; translation_table_pa_des memory1 ttbr01 = translation_table_pa_des memory2 ttbr02 \<rbrakk> \<Longrightarrow>
        pt_walk asid memory1 ttbr01 v = pt_walk asid memory2 ttbr02 v"
  (* pa_l1 in pt_walk is equal *)
  apply (subgoal_tac "ttbr01 AND 0xFFFFC000 OR (v AND 0xFFF00000 >> 18) =
           ttbr02 AND 0xFFFFC000 OR (v AND 0xFFF00000 >> 18)")
   prefer 2
   apply simp
  apply (subgoal_tac "ttbr01 AND 0xFFFFC000 OR (v AND 0xFFF00000 >> 18) \<in>
           {x. x \<in> {x. ttbr01 AND 0xFFFFC000 \<le> x \<and> x \<le> ((ttbr01 AND 0xFFFFC000) + (16384-1))} \<and> (ucast(x OR 0xFFFFFFFC):: 2 word) = 0x0}")
   prefer 2
   apply clarsimp
   apply word_bitwise
  apply (subgoal_tac "word_fetch memory1 (ttbr01 AND 0xFFFFC000 OR (v AND 0xFFF00000 >> 18)) =
             word_fetch memory2 (ttbr02 AND 0xFFFFC000 OR (v AND 0xFFF00000 >> 18))")
   prefer 2
   apply (frule (1) tt_rewrite)
   apply blast
  (* pde1 *)
  (* new logic *)
  apply (cases "word_fetch memory1 (ttbr01 AND 0xFFFFC000 OR (v AND 0xFFF00000 >> 18)) AND 3 = 2")
   apply (cases "\<not> word_fetch memory1 (ttbr01 AND 0xFFFFC000 OR (v AND 0xFFF00000 >> 18)) !! 18")
    apply (clarsimp simp: pt_walk_def Let_def)
   apply (clarsimp simp: pt_walk_def Let_def)
  apply (cases "word_fetch memory1 (ttbr01 AND 0xFFFFC000 OR ((v AND 0xFFF00000) >> 18)) AND 3 = 1")
   prefer 2
   apply (clarsimp simp: pt_walk_def Let_def)
  apply (subgoal_tac "word_fetch memory2 (ttbr02 AND 4294950912 OR (v AND 4293918720 >> 18)) AND 3 = 1")
   prefer 2
   apply clarsimp
  (* apply (cases "pde2 !! 1") *)
  (* pa_l2 *)
  apply (subgoal_tac "word_fetch memory1 (ttbr02 AND 4294950912 OR (v AND 4293918720 >> 18)) AND 4294966272 OR (v AND 1044480 >> 10) =
           word_fetch memory2 (ttbr02 AND 4294950912 OR (v AND 4293918720 >> 18)) AND 4294966272 OR (v AND 1044480 >> 10)")
   prefer 2
   apply clarsimp
  (* pde 2 *)
  (* element of l2_ba *)
  apply (subgoal_tac "word_fetch memory1 (ttbr01 AND 0xFFFFC000 OR ((v AND 0xFFF00000) >> 18)) \<in>
           word_fetch memory1 `  {x. x \<in> {x. ttbr01 AND 0xFFFFC000 \<le> x \<and> x \<le> ((ttbr01 AND 0xFFFFC000) + (16384-1))} \<and> (ucast(x OR 0xFFFFFFFC):: 2 word) = 0x0}")
   prefer 2
   apply blast
  apply (subgoal_tac "word_fetch memory1 (ttbr01 AND 4294950912 OR (v AND 4293918720 >> 18)) AND 4294966272 \<in>
           (\<lambda>x. x AND 0xFFFFFC00) `word_fetch memory1 ` {x. x \<in> {x. ttbr01 AND 0xFFFFC000 \<le> x \<and> x \<le> ((ttbr01 AND 0xFFFFC000) + (16384-1))} \<and> (ucast(x OR 0xFFFFFFFC):: 2 word) = 0x0}")
   prefer 2
   apply blast
  (* set of base address *)
  apply (subgoal_tac "(word_fetch memory1 (ttbr01 AND 4294950912 OR (v AND 4293918720 >> 18))  AND 4294966272 OR ((v AND 0x000FF000) >> 10)) \<in>
           \<Union>( (\<lambda>x. {y. x \<le> y \<and> y \<le> x + (1024-1)}) ` ((\<lambda>x. x AND 0xFFFFFC00) `word_fetch memory1 ` {x. x \<in> {x. ttbr01 AND 0xFFFFC000 \<le> x \<and> x \<le> ((ttbr01 AND 0xFFFFC000) + (16384-1))} \<and> (ucast(x OR 0xFFFFFFFC):: 2 word) = 0x0}) )")
   prefer 2
   apply (rule UnionI)
    apply blast
   apply clarsimp
   apply word_bitwise
  apply (subgoal_tac "(word_fetch memory1 (ttbr01 AND 4294950912 OR (v AND 4293918720 >> 18)) AND 4294966272 OR ((v AND 0x000FF000) >> 10)) \<in>
           {x. x \<in> \<Union>( (\<lambda>x. {y. x \<le> y \<and> y \<le> x + (1024-1)}) ` ((\<lambda>x. x AND 0xFFFFFC00) `word_fetch memory1 ` {x. x \<in> {x. ttbr01 AND 0xFFFFC000 \<le> x \<and> x \<le> ((ttbr01 AND 0xFFFFC000) + (16384-1))}
               \<and> (ucast(x OR 0xFFFFFFFC):: 2 word) = 0x0})) \<and> (ucast(x OR 0xFFFFFFFC):: 2 word) = 0x0} ")
   prefer 2
   apply clarsimp
   apply word_bitwise
  apply (subgoal_tac
   " (word_fetch memory1 (ttbr01 AND 4294950912 OR (v AND 4293918720 >> 18)) AND 4294966272 OR ((v AND 0x000FF000) >> 10)) \<in>
       {x \<in> \<Union>((\<lambda>x. {y. x \<le> y \<and> y \<le> x + (1024 - 1)}) ` (\<lambda>x. x AND 4294966272) ` {x \<in> word_fetch memory1 ` {x \<in> {x. ttbr01 AND 4294950912 \<le> x \<and> x \<le> (ttbr01 AND 4294950912) + (16384 - 1)}. ucast (x OR 4294967292) = 0}.x AND 3 = 1}).  ucast (x OR 4294967292) = 0}")
   prefer 2
   apply auto [1]
   apply (rule_tac x = "word_fetch memory1 x" in exI)
   apply clarsimp
   apply (rule conjI)
    apply blast
   apply (rule conjI)
    apply word_bitwise
   apply word_bitwise
  apply (subgoal_tac "word_fetch memory2 (ttbr02 AND 0xFFFFC000 OR ((v AND 0xFFF00000) >> 18)) \<in>
           word_fetch memory2 `  {x. x \<in> {x. ttbr02 AND 0xFFFFC000 \<le> x \<and> x \<le> ((ttbr02 AND 0xFFFFC000) + (16384-1))} \<and> (ucast(x OR 0xFFFFFFFC):: 2 word) = 0x0} ")
   prefer 2
   apply blast
  apply (subgoal_tac "word_fetch memory2 (ttbr02 AND 4294950912 OR (v AND 4293918720 >> 18)) AND 4294966272 \<in>
           (\<lambda>x. x AND 0xFFFFFC00) `word_fetch memory2 ` {x. x \<in> {x. ttbr02 AND 0xFFFFC000 \<le> x \<and> x \<le> ((ttbr02 AND 0xFFFFC000) + (16384-1))} \<and> (ucast(x OR 0xFFFFFFFC):: 2 word) = 0x0}")
   prefer 2
   apply blast
  (* set of base address *)
  apply (subgoal_tac "(word_fetch memory2 (ttbr02 AND 4294950912 OR (v AND 4293918720 >> 18)) AND 4294966272 OR ((v AND 0x000FF000) >> 10)) \<in>
   \<Union>( (\<lambda>x. {y. x \<le> y \<and> y \<le> x + (1024-1)}) ` ((\<lambda>x. x AND 0xFFFFFC00) `word_fetch memory2 ` {x. x \<in> {x. ttbr02 AND 0xFFFFC000 \<le> x \<and> x \<le> ((ttbr02 AND 0xFFFFC000) + (16384-1))} \<and> (ucast(x OR 0xFFFFFFFC):: 2 word) = 0x0}))")
   prefer 2
   apply (rule UnionI)
    apply blast
   apply clarsimp
   apply word_bitwise
  apply (subgoal_tac "(word_fetch memory2 (ttbr02 AND 4294950912 OR (v AND 4293918720 >> 18)) AND 4294966272 OR ((v AND 0x000FF000) >> 10)) \<in>
           {x. x \<in>   \<Union>( (\<lambda>x. {y. x \<le> y \<and> y \<le> x + (1024-1)}) ` ((\<lambda>x. x AND 0xFFFFFC00) `
             word_fetch memory2 `{x. x \<in> {x. ttbr02 AND 0xFFFFC000 \<le> x \<and> x \<le> ((ttbr02 AND 0xFFFFC000) + (16384-1))} \<and> (ucast(x OR 0xFFFFFFFC):: 2 word) = 0x0}) ) \<and> (ucast(x OR 0xFFFFFFFC):: 2 word) = 0x0} ")
   prefer 2
   apply clarsimp
  apply (subgoal_tac "(word_fetch memory2 (ttbr01 AND 4294950912 OR (v AND 4293918720 >> 18)) AND 4294966272 OR ((v AND 0x000FF000) >> 10)) \<in>
           {x \<in> \<Union>((\<lambda>x. {y. x \<le> y \<and> y \<le> x + (1024 - 1)}) ` (\<lambda>x. x AND 4294966272) ` {x \<in> word_fetch memory2 ` {x \<in> {x. ttbr02 AND 4294950912 \<le> x \<and> x \<le> (ttbr02 AND 4294950912) + (16384 - 1)}. ucast (x OR 4294967292) = 0}. x AND 3 = 1}). ucast (x OR 4294967292) = 0}")
   prefer 2
   apply auto [1]
   apply (rule_tac x = "word_fetch memory1 x" in exI)
   apply clarsimp
   apply (rule conjI)
    prefer 2
    apply word_bitwise
   thm subst
   apply (erule_tac s="word_fetch memory2 (ttbr02 AND 4294950912 OR (v AND 4293918720 >> 18))"  in  subst)
   apply blast
  (* I am here finally *)
  apply (subgoal_tac " word_fetch memory1 (word_fetch memory1 (ttbr01 AND 4294950912 OR (v AND 4293918720 >> 18)) AND 4294966272 OR (v AND 1044480 >> 10)) =
           word_fetch memory2 (word_fetch memory2 (ttbr02 AND 4294950912 OR (v AND 4293918720 >> 18)) AND 4294966272 OR (v AND 1044480 >> 10))")
   prefer 2
   apply (frule (1) tt_rewrite)
   apply (rule_tac a  = "(word_fetch memory1 (ttbr01 AND 4294950912 OR (v AND 4293918720 >> 18)) AND 4294966272 OR (v AND 1044480 >> 10))" and
                   b  = "(word_fetch memory2 (ttbr02 AND 4294950912 OR (v AND 4293918720 >> 18)) AND 4294966272 OR (v AND 1044480 >> 10))" and
                   X  = "{x \<in> \<Union>((\<lambda>x. {y. x \<le> y \<and> y \<le> x + (1024 - 1)}) ` (\<lambda>x. x AND 4294966272) ` {x \<in> word_fetch memory1 ` {x \<in> {x. ttbr01 AND 4294950912 \<le> x \<and> x \<le> (ttbr01 AND 4294950912) + (16384 - 1)}. ucast (x OR 4294967292) = 0}.x AND 3 = 1}).ucast (x OR 4294967292) = 0}"  and
                   Y  = "{x \<in> \<Union>((\<lambda>x. {y. x \<le> y \<and> y \<le> x + (1024 - 1)}) `(\<lambda>x. x AND 4294966272) ` {x \<in> word_fetch memory2 ` {x \<in> {x. ttbr02 AND 4294950912 \<le> x \<and> x \<le> (ttbr02 AND 4294950912) + (16384 - 1)}. ucast (x OR 4294967292) = 0}. x AND 3 = 1}).ucast (x OR 4294967292) = 0}" and
                   XX = "{x \<in> {x. ttbr01 AND 4294950912 \<le> x \<and> x \<le> (ttbr01 AND 4294950912) + (16384 - 1)}. ucast (x OR 4294967292) = 0}" and
                   YY = "{x \<in> {x. ttbr02 AND 4294950912 \<le> x \<and> x \<le> (ttbr02 AND 4294950912) + (16384 - 1)}. ucast (x OR 4294967292) = 0}" in  func_map)
      apply assumption
     apply simp
    apply (simp only: image_Un)
   apply simp
  apply (clarsimp simp: pt_walk_def Let_def)
done
  


lemma pt_walk_eq_mem:
  "\<lbrakk>TTBR0 s = TTBR0 t ; translation_table_pa_des (MEM s) (TTBR0 s) = translation_table_pa_des (MEM t) (TTBR0 t) ;
      MEM s ` UNIV \<noteq> MEM t ` UNIV \<rbrakk> \<Longrightarrow> 
          pt_walk asid (MEM s) (TTBR0 s) v = pt_walk asid (MEM t) (TTBR0 t) v"            
  by (rule pt_walk_eq ; clarsimp)

lemma pt_walk_eq_UNIV:
  "\<lbrakk>TTBR0 s = TTBR0 t ; translation_table_pa_des (MEM s) (TTBR0 s) = translation_table_pa_des (MEM t) (TTBR0 t) \<rbrakk> \<Longrightarrow> 
          pt_walk asid (MEM s) (TTBR0 s) ` UNIV = pt_walk asid (MEM t) (TTBR0 t) ` UNIV"            
by (metis image_cong pt_walk_eq)




(* new definition of write'mem  *)

 
definition
  "write'mem'sat1" :: "bool list \<times> 32 word \<times> nat \<Rightarrow> state \<Rightarrow> unit \<times> state"
where
  "write'mem'sat1 \<equiv> \<lambda>(value, vaddr, size). do {
     (* original TLB before memory translation *)
     tlb0  <- read_state TLB;
     paddr <- mmu_translate_sat vaddr;
     asid  <- read_state ASID;
     ttbr0 <- read_state TTBR0;
     mem1  <-  read_state MEM;
     let tt1 = translation_table_pa_des mem1 ttbr0;
     (* size is in {1, 2, 4, 8} and will be aligned, so will not cross page boundaries *)
     write'mem1 (value, paddr, size);
     mem2  <- read_state MEM; (*mem is updated after write'mem1 *) 
     let tt2 = translation_table_pa_des mem2 ttbr0;
     if tt1 = tt2 
       then return ()
       else
         do {let all_entries = pt_walk asid mem2 ttbr0 ` UNIV;
             let tlb = tlb0 \<union> all_entries;
             update_state (\<lambda>s. s\<lparr> TLB := tlb \<rparr>) 
         }
  }"



(* do it for changes to ttbr0 as well *)

lemma
  "\<lbrakk>TTBR0 s = TTBR0 t ; ASID s = ASID t ; saturated s;
    (*pt_walk (ASID s) (MEM s) (TTBR0 s) ` UNIV \<subseteq> TLB s; *) 
     translation_table_pa_des (MEM s) (TTBR0 s) = translation_table_pa_des (MEM t) (TTBR0 t)\<rbrakk>
           \<Longrightarrow> saturated t"
  apply (subgoal_tac "pt_walk (ASID s) (MEM s) (TTBR0 s) ` UNIV =
                pt_walk (ASID t) (MEM s) (TTBR0 s) ` UNIV")
thm pt_walk_eq
  prefer 2
  apply (clarsimp simp: pt_walk_eq)
  unfolding saturated_def
  oops


(* HAPPY PROVING *)
lemma write'mem'sat1_saturated:
  "write'mem'sat1 (v,va,sz) s = ((), t) \<Longrightarrow> saturated t"
  apply (clarsimp simp: write'mem'sat1_def)
  apply (cases "mmu_translate_sat va s" , clarsimp)
  apply (case_tac "write'mem1 (v, a, sz) b" , clarsimp)
  apply (clarsimp split:split_if_asm)
   prefer 2
   apply (subgoal_tac "ASID b = ASID ba \<and> TTBR0 b = TTBR0 ba")
    apply (clarsimp simp: saturated_def)
   apply (clarsimp simp: write'mem1_def raise'exception_def split:split_if_asm)
  apply (subgoal_tac "saturated b \<and> 
           TLB b = TLB t \<and> 
           range (pt_walk (ASID b) (MEM b) (TTBR0 b)) = range (pt_walk (ASID t) (MEM t) (TTBR0 t))")
   using saturated_def apply blast
  apply (rule conjI)
   apply (clarsimp simp:mmu_translate_sat_sat)
  apply (rule conjI)
   apply (clarsimp simp: write'mem1_def raise'exception_def split:split_if_asm)
  apply (subgoal_tac "TTBR0 b = TTBR0 t \<and> ASID b = ASID t")
   apply (metis pt_walk_eq_UNIV)
  apply (clarsimp simp: write'mem1_def raise'exception_def split:split_if_asm)
done



(* Next Step: Refinement theorem for write'mem and write'mem'sat (write'mem'sat1) *)




end
