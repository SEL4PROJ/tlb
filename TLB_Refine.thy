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

(* "Deterministic" mmu_translate: without entry eviction *)
definition
  mmu_translate_det ::"32 word  \<Rightarrow> state \<Rightarrow> 32 word \<times> state"
where
  "mmu_translate_det va \<equiv> do {
     mem   <- read_state MEM;
     asid  <- read_state ASID;
     ttbr0 <- read_state TTBR0;
     tlb   <- read_state TLB;
     case lookup tlb asid va of
       Hit entry \<Rightarrow> return (va_to_pa va entry)
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

(* refinement between two deterministic TLB lookups *)
lemma mmu_translate_refine:
  "\<lbrakk> mmu_translate_det va s = (pa, s'); consistent t va; tlb_rel s t \<rbrakk> \<Longrightarrow>
  let (pa', t') = mmu_translate_det va t
  in pa' = pa \<and> consistent t' va \<and> tlb_rel s' t'"
  apply (frule (1) tlb_rel_consistent)
  apply (frule tlb_relD)
  apply (subgoal_tac "lookup (TLB s) (ASID s) va \<le> lookup (TLB t) (ASID s) va")
   prefer 2
   apply (simp add: tlb_mono) 
  apply (clarsimp simp: mmu_translate_det_def split_def Let_def)
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
  done

(* refinement between eviction and deterministic TLB lookups *)
lemma mmu_translate_refine_det:
  "\<lbrakk> mmu_translate va s = (pa, s'); consistent t va; tlb_rel s t \<rbrakk> \<Longrightarrow>
  let (pa', t') = mmu_translate_det va t
  in pa' = pa  \<and> consistent t' va \<and> tlb_rel s' t'"
  apply (simp add: mmu_translate_def2)
  apply (drule (1) mmu_translate_refine; fastforce simp: tlb_rel_def)
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

definition
  saturated :: "state \<Rightarrow> tlb \<Rightarrow> bool"
where
  "saturated s tlb \<equiv> pt_walk (ASID s) (MEM s) (TTBR0 s) ` UNIV \<subseteq> TLB s"


end
