(*
 * Copyright 2016, Data61, CSIRO
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *)

theory TLB
imports
  "HOL-Word.Word"
  PTABLE.PageTable_seL4
  L3_LIB.L3_Lib
begin

type_synonym vSm = "20 word"
type_synonym pSm = "20 word"

type_synonym vSe = "12 word"
type_synonym pSe = "12 word"

type_synonym asid  = "8 word"
type_synonym fl     = "8 word"



datatype tlb_entry =
    EntrySmall   asid vSm pSm fl
  | EntrySection asid vSe pSe fl

type_synonym tlb = "tlb_entry set"

datatype lookup_type  =  Miss  | Incon  |  Hit "tlb_entry"


(* Address Range of an Entry *)
definition
  entry_range :: "tlb_entry \<Rightarrow> vaddr set"
where
  "entry_range E \<equiv> case E of EntrySmall   a va pa f   \<Rightarrow> Addr ` {(ucast va::32 word) << 12 ..
                                                            ((ucast va::32 word) << 12) + (2^12 - 1)} |
                             EntrySection a va pa f    \<Rightarrow> Addr ` {(ucast va::32 word) << 20 ..
                                                            ((ucast va::32 word) << 20) + (2^20 - 1)}"

(* ASID tag of an Entry *)
fun
  asid_entry :: "tlb_entry \<Rightarrow> asid"
where
  "asid_entry (EntrySmall   a x y z) = a"
| "asid_entry (EntrySection a x y z) = a"


(* Address Range of an entry with ASID tag *)
definition
  entry_range_asid_tags :: "tlb_entry \<Rightarrow> (asid \<times> vaddr) set"
where
  "entry_range_asid_tags E \<equiv> image (\<lambda>v. (asid_entry E , v)) (entry_range E)"


(* Set of all the entries covering a virtual address and an ASID *)
definition
  entry_set :: "tlb \<Rightarrow> asid \<Rightarrow> vaddr \<Rightarrow> (tlb_entry set)"
where
  "entry_set t a v \<equiv> {E\<in>t. (a,v) : entry_range_asid_tags E } "


(* Lookup for a virtual address along with an ASID *)
definition
  lookup :: "tlb \<Rightarrow> asid \<Rightarrow> vaddr \<Rightarrow> lookup_type"
where
  "lookup t a va \<equiv> if entry_set t a va = {} then Miss
                   else if \<exists>x. entry_set t a va = {x} then Hit (the_elem (entry_set t a va))
                        else Incon"


(* set of all the virtual addresses with ASID tags covered by TLB *)
definition
  a_va_set :: "tlb \<Rightarrow> (asid \<times> vaddr) set"
where
  "a_va_set t \<equiv> \<Union> (entry_range_asid_tags ` t)"


(* Is a virtual address and an ASID covered by TLB *)
definition
  is_a_va_present :: "tlb \<Rightarrow> asid \<Rightarrow> vaddr \<Rightarrow> bool"
where
  "is_a_va_present t a v \<equiv> (a,v) : a_va_set t"



definition
  Flush_TLB :: "tlb \<Rightarrow> tlb"
where
  "Flush_TLB t  \<equiv> {}"


definition
  Flush_ASID :: "tlb \<Rightarrow> asid  \<Rightarrow> tlb"
where
  "Flush_ASID t a \<equiv> t - {e\<in>t. asid_entry e = a}"

definition
  Flush_varange :: "tlb \<Rightarrow> vaddr set  \<Rightarrow> tlb"
where
  "Flush_varange t V \<equiv>   t - (\<Union>v\<in>V. {e \<in> t. v \<in> entry_range e})"


definition
  Flush_ASIDvarange :: "tlb \<Rightarrow> asid \<Rightarrow> vaddr set  \<Rightarrow> tlb"
where
  "Flush_ASIDvarange t a V \<equiv>  t - (\<Union>v\<in>V. {e \<in> t. (a, v) \<in> entry_range_asid_tags e})"


definition
  a_va_sel_invalidate :: "tlb \<Rightarrow> asid \<Rightarrow> vaddr \<Rightarrow> tlb"
where
  "a_va_sel_invalidate t a v \<equiv> case lookup t a v of Hit x \<Rightarrow> t - {x}
                                                          | Miss  \<Rightarrow> t
                                                          | Incon \<Rightarrow> t - entry_set t a v"

theorem is_present_selective:
  "\<not>(is_a_va_present (a_va_sel_invalidate t a v) a v)"
  unfolding a_va_sel_invalidate_def
            lookup_def is_a_va_present_def entry_set_def a_va_set_def
  by (fastforce split: if_split_asm)


(* Block invalidation of a set of virtual addresses for an ASID *)

definition
  a_va_block_invalidation :: "tlb \<Rightarrow> asid \<Rightarrow> vaddr set \<Rightarrow> tlb"
where
  "a_va_block_invalidation t a V \<equiv> \<Inter>x\<in>V. a_va_sel_invalidate t a x"


definition
  is_a_vset_present :: "tlb \<Rightarrow> asid \<Rightarrow> vaddr set \<Rightarrow> bool"
where
  "is_a_vset_present t a V \<equiv> \<exists>v\<in>V. is_a_va_present t a v"

theorem lookup_miss_case:
  "lookup t a v = Miss \<Longrightarrow> \<not>is_a_va_present t a v"
  unfolding is_a_va_present_def lookup_def entry_set_def a_va_set_def
  by (simp split: if_split_asm)


(* Theorems for Block Invalidation *)
theorem  lookup_incon_case:
  "lookup t a v = Incon \<Longrightarrow> \<not>is_a_va_present (t - entry_set t a v) a v"
  unfolding is_a_va_present_def lookup_def entry_set_def a_va_set_def
  by (simp split: if_split_asm)


theorem lookup_hit_case:
  "lookup t a v = Hit x \<Longrightarrow> \<not>is_a_va_present (t - {x}) a v"
  unfolding lookup_def is_a_va_present_def entry_set_def a_va_set_def
  by (force split: if_split_asm)

theorem member_selective_invalidation:
  "x \<in> a_va_sel_invalidate t a v \<Longrightarrow> (a,v) \<notin>  entry_range_asid_tags x"
  unfolding a_va_sel_invalidate_def
  apply (simp split: lookup_type.splits)
  apply (drule lookup_miss_case)
  unfolding is_a_va_present_def a_va_set_def
  apply (simp)
  apply (drule lookup_incon_case)
  unfolding is_a_va_present_def a_va_set_def
  apply (simp)
  apply (drule lookup_hit_case)
  unfolding is_a_va_present_def a_va_set_def
  by (simp)



theorem is_present_block:
  "\<not>(is_a_vset_present (a_va_block_invalidation t a V) a V)"
  unfolding is_a_vset_present_def
  apply (safe)
  unfolding is_a_va_present_def
  apply (subgoal_tac "entry_set (a_va_block_invalidation t a V) a v \<noteq> {}")
  unfolding entry_set_def a_va_block_invalidation_def
  apply clarsimp
  apply (drule_tac x="v" in bspec, assumption , simp add: member_selective_invalidation)
  unfolding a_va_set_def entry_set_def
  by force


(* is_TLB_okay *)

definition
  overlapping_entries :: "tlb \<Rightarrow> tlb"
where
  "overlapping_entries t \<equiv>
     {x\<in>t. (entry_range_asid_tags x \<inter> a_va_set (t - {x}) ) \<noteq> {} }"


definition
  is_okay :: "tlb \<Rightarrow> bool"
where
  "is_okay t \<equiv> (overlapping_entries t = {})"

theorem member_va_set:
  "(a,v) \<in> a_va_set t \<Longrightarrow> entry_set t a v \<noteq> {}"
  unfolding a_va_set_def entry_set_def
  apply clarsimp
  unfolding  entry_range_asid_tags_def
  by force

theorem  inter_entry_va_set:
  "entry_range_asid_tags x \<inter> a_va_set (t - {x}) = {} \<Longrightarrow>
     \<forall>y\<in>t. \<forall>av\<in>entry_range_asid_tags x. y \<noteq> x \<longrightarrow> av \<notin> entry_range_asid_tags y"
  unfolding a_va_set_def
  by force

theorem  invalidating_corrupt_entries:
  "is_okay (t - overlapping_entries t)"
  unfolding is_okay_def overlapping_entries_def
  apply safe
  apply (drule member_va_set)
  unfolding entry_set_def
  apply clarsimp
  apply (drule inter_entry_va_set , drule_tac x="xa" in bspec , assumption ,
               drule_tac x="(a,b)" in bspec , assumption )
   by simp


(* Physical Address Retrieval *)

datatype bpa = Bpsm "20 word" | Bpse "12 word"

fun
  bpa_entry :: "tlb_entry \<Rightarrow> bpa"
where
  "bpa_entry (EntrySmall _ _ p _)   =  Bpsm p"
| "bpa_entry (EntrySection _ _ p _) =  Bpse p"

fun
  bpa_to_pa :: "vaddr \<Rightarrow> bpa \<Rightarrow> paddr"
where
  "bpa_to_pa va (Bpsm bpa) = Addr ((ucast bpa << 12) OR (addr_val va AND mask 12))"
| "bpa_to_pa va (Bpse bpa) = Addr ((ucast bpa << 20) OR (addr_val va AND mask 20))"

definition
  va_to_pa :: "vaddr \<Rightarrow> tlb_entry \<Rightarrow> paddr"
where
  "va_to_pa v t \<equiv> bpa_to_pa v (bpa_entry t)"

(* Uniqueness *)

theorem lookup_miss_not_present_implies:
  "lookup t a v = Miss \<Longrightarrow> \<not>is_a_va_present t a v"
  unfolding is_a_va_present_def lookup_def entry_set_def a_va_set_def
  by (simp split: if_split_asm)

theorem not_present_lookup_miss_implies:
  "\<not>is_a_va_present t a v \<Longrightarrow> lookup t a v = Miss"
  unfolding is_a_va_present_def lookup_def entry_set_def a_va_set_def
  by (simp split: if_split_asm)

theorem lookup_miss_not_present:
  "(lookup t a v = Miss) = (\<not>is_a_va_present t a v)"
  apply (rule iffI)
  unfolding is_a_va_present_def lookup_def entry_set_def a_va_set_def
  by (simp split: if_split_asm)+

(* ---------------------------------------------------------------------*)

theorem is_present_look_up_not_miss_implies:
  "is_a_va_present t a v \<Longrightarrow> lookup t a v \<noteq> Miss "
  unfolding is_a_va_present_def lookup_def entry_set_def a_va_set_def
  apply (safe)
  by (simp split: if_split_asm)

theorem look_up_not_miss_is_present_imples:
  "lookup t a v \<noteq> Miss \<Longrightarrow> is_a_va_present t a v"
  unfolding is_a_va_present_def lookup_def entry_set_def a_va_set_def
  apply (simp split: if_split_asm)
  by force+

theorem is_present_look_up_not_miss:
  "(is_a_va_present t a v) = (lookup t a v \<noteq> Miss)"
  apply (rule iffI)
  unfolding is_a_va_present_def lookup_def entry_set_def a_va_set_def
  apply (safe)
  by (simp split: if_split_asm ; force)+

(* ---------------------------------------------------------------------*)

theorem is_okay_not_empty_exist:
  "\<lbrakk>is_okay t ; entry_set t a v \<noteq> {} \<rbrakk> \<Longrightarrow> \<exists>x. entry_set t a v = {x}"
  unfolding entry_set_def
  unfolding is_okay_def overlapping_entries_def
  unfolding a_va_set_def
  apply clarsimp
  apply (drule_tac x="x" in spec)
  apply clarsimp
  apply (rule_tac x="x" in exI)
  by auto


theorem is_okay_not_miss_exist:
  "\<lbrakk>is_okay t ; lookup t a v \<noteq> Miss  \<rbrakk> \<Longrightarrow>
               \<exists>x\<in>t. lookup t a v = Hit x"
  unfolding lookup_def
  apply (simp split: if_split_asm)
  apply (unfold entry_set_def) [1]
  apply force
  apply (drule(1) is_okay_not_empty_exist)
  by simp
(* ---------------------------------------------------------------------*)

theorem is_okay_is_present_not_incon:
  "\<lbrakk>is_okay t ; is_a_va_present t a v \<rbrakk> \<Longrightarrow> lookup t a v \<noteq> Incon"
  apply safe
  apply (drule is_present_look_up_not_miss_implies)
  unfolding lookup_def
  apply (simp split: if_split_asm)
  unfolding is_okay_def overlapping_entries_def a_va_set_def entry_set_def
  apply clarsimp
  apply (drule_tac x="x" in spec)
  apply simp
  apply (drule_tac x="x" in spec)
  by force


theorem is_okay_not_incon:
  "is_okay t \<Longrightarrow>  \<forall>v a. lookup t a v \<noteq> Incon"
  apply safe
  unfolding lookup_def
  apply (simp split: if_split_asm)
  unfolding is_okay_def overlapping_entries_def a_va_set_def entry_set_def
  apply clarsimp
  apply (drule_tac x="x" in spec)
  apply simp
  apply (drule_tac x="x" in spec)
  by force


theorem  entry_set_empty:
  "entry_set t a v  = {} \<Longrightarrow> (a, v) \<notin> a_va_set t"
  unfolding entry_set_def a_va_set_def
  by simp


theorem is_okay_intro1:
  "\<forall>x \<in> t. entry_range_asid_tags x \<inter> a_va_set (t - {x}) = {} \<Longrightarrow> is_okay t"
  unfolding is_okay_def overlapping_entries_def
  by simp

theorem  is_okay_intro2:
  " \<lbrakk>x \<in> t;  \<forall>(a,v)\<in> entry_range_asid_tags x. \<forall>y\<in>t. y \<noteq> x \<longrightarrow> (a,v) \<notin> entry_range_asid_tags y \<rbrakk>
     \<Longrightarrow> entry_range_asid_tags x \<inter> a_va_set (t - {x}) = {}"
   unfolding a_va_set_def
   by force

theorem bounded_forall_v_a:
  "\<forall>v a. lookup t a v \<noteq> Incon \<Longrightarrow>
      \<forall>x\<in>t. \<forall>v a. (a, v) \<in> a_va_set t \<longrightarrow> lookup t a v \<noteq> Incon"
  by clarsimp


theorem entry_range_single_element:
  "{E \<in> t. (a, v) \<in> entry_range_asid_tags E} = {x} \<Longrightarrow> (a, v) \<in> entry_range_asid_tags x
         \<and> (\<forall>y\<in>t. y\<noteq>x \<longrightarrow> (a, v) \<notin> entry_range_asid_tags y)"
   by force


theorem entry_range_memeber_va_set:
  "\<lbrakk>x \<in> t;  (a, b) \<in> entry_range_asid_tags x\<rbrakk> \<Longrightarrow> (a, b) \<in> a_va_set t"
   unfolding a_va_set_def
   by force

theorem not_incon_is_okay:
  "\<forall>v a. lookup t a v \<noteq> Incon \<Longrightarrow> is_okay t"
  apply (rule is_okay_intro1)
  unfolding Ball_def
  apply (rule allI)
  apply (rule impI)
  apply (rule is_okay_intro2)
  apply simp
  apply safe
  unfolding is_okay_def overlapping_entries_def
  apply (drule bounded_forall_v_a)
  apply (drule_tac x="x" in bspec, assumption)
  apply (drule_tac x="b" in spec)
  apply (drule_tac x="a" in spec)
  apply (frule entry_range_memeber_va_set)
  apply simp
  unfolding lookup_def
  apply (simp split: if_split_asm)
  apply (drule entry_set_empty)
  apply (unfold a_va_set_def) [1]
  apply simp
  apply (unfold a_va_set_def) [1]
  apply (unfold entry_set_def) [1]
  apply clarsimp
  apply (drule entry_range_single_element)
  apply (case_tac "x=xa")
  by simp+

theorem
  "is_okay t = (\<forall>v a. lookup t a v \<noteq> Incon)"
  apply (rule iffI)
  by (clarsimp simp:is_okay_not_incon not_incon_is_okay)+

(* ---------------------------------------------------------------------*)

theorem is_okay_not_hit_miss:
  "\<lbrakk>is_okay t ; (\<forall>x\<in>t. lookup t a v \<noteq> Hit x) \<rbrakk> \<Longrightarrow>
          lookup t a v = Miss "
  unfolding lookup_def
  apply (simp split: if_split_asm)
  apply (unfold entry_set_def) [1]
  apply force
  apply (drule(1) is_okay_not_empty_exist)
  by simp



theorem overlapping_entries_non_singleton:
  "\<lbrakk>entry_range_asid_tags x \<inter> a_va_set (t - {x}) \<noteq> {} \<rbrakk> \<Longrightarrow>
    \<exists>y\<in>t. \<exists>(a,v)\<in>entry_range_asid_tags x. y\<noteq>x \<and> (a,v)\<in>entry_range_asid_tags y"
  unfolding a_va_set_def
  by force


theorem not_okay_lookup_incon:
  "\<not>is_okay t \<Longrightarrow>\<exists>(a,v)\<in>a_va_set t. lookup t a v = Incon"
  unfolding is_okay_def overlapping_entries_def
  apply clarsimp
  apply (drule overlapping_entries_non_singleton)
  apply clarsimp
  unfolding Bex_def
  apply (rule_tac x="(a , b)" in exI)
  apply (clarsimp simp: entry_range_memeber_va_set)

  unfolding lookup_def
  apply (simp split:if_split)
  apply (rule conjI)
  apply safe
  unfolding entry_set_def
  apply (drule entry_range_single_element)
  apply metis
  by simp

(* ---------------------------------------------------------------------*)


(*          ASID INVALIDATION CASE       *)

(* set of all the entries for a particular ASID *)
definition
  asid_entry_set :: "tlb \<Rightarrow> asid \<Rightarrow> (tlb_entry set)"
where
  "asid_entry_set t a \<equiv> {E\<in>t. asid_entry E = a} "

definition
  asid_set :: "tlb \<Rightarrow> asid set"
where
  "asid_set t \<equiv> asid_entry ` t"

(* is ASID entries present in TLB *)

definition
  is_asid_present :: "tlb \<Rightarrow> asid \<Rightarrow> bool"
where
  "is_asid_present t a \<equiv>  a : asid_set t"



(* ASID Invalidation *)

definition
  asid_invalidation :: "tlb \<Rightarrow> asid \<Rightarrow> tlb"
where
  "asid_invalidation t a \<equiv> t - asid_entry_set t a "


theorem is_present_asid_invalidation:
  "\<not>(is_asid_present (asid_invalidation t a) a)"
  unfolding is_asid_present_def asid_invalidation_def asid_entry_set_def asid_set_def
  by force

theorem lookup_asid_inv_miss:
  "\<lbrakk> a1 \<noteq> a2 ; lookup t a2 v = Miss \<rbrakk> \<Longrightarrow>
         lookup (asid_invalidation t a1) a2 v = Miss"
  apply (clarsimp simp:lookup_miss_not_present)
  unfolding asid_invalidation_def is_a_va_present_def
    asid_entry_set_def a_va_set_def
   by simp


theorem lookup_hit_is_present:
  "lookup t a v = Hit x \<Longrightarrow> is_a_va_present t a v"
  unfolding lookup_def is_a_va_present_def entry_set_def a_va_set_def
  by (force split: if_split_asm)

theorem entry_ranhe_asid_entry:
  "(a2, v) \<in> entry_range_asid_tags x \<Longrightarrow> a2 = asid_entry x"
  unfolding entry_range_asid_tags_def
  by force

theorem lookup_asid_inv_hit:
  "\<lbrakk> a1 \<noteq> a2 ; lookup t a2 v = Hit x \<rbrakk> \<Longrightarrow>
         lookup (asid_invalidation t a1) a2 v = Hit x"
  apply (frule lookup_hit_is_present)
  unfolding asid_invalidation_def lookup_def
  apply (simp split: if_split_asm)
  apply safe
    unfolding entry_set_def asid_entry_set_def a_va_set_def
    apply simp
   apply force
  apply simp
  apply (rule_tac x="x" in exI)
  apply safe
     apply force
    apply force
   prefer 2
   apply force
  apply simp
  apply (drule entry_range_single_element)
  apply safe
  apply (drule entry_ranhe_asid_entry)
  by simp

theorem for_incon:
  "\<lbrakk> a1 \<noteq> a2 ; \<forall>x. entry_set t a2 v \<noteq> {x}\<rbrakk> \<Longrightarrow>
         \<forall>x. entry_set (t- asid_entry_set t a1) a2 v \<noteq> {x}"
  unfolding entry_set_def asid_entry_set_def entry_range_asid_tags_def
  by auto


theorem   entry_set_comp:
  "\<lbrakk>a1 \<noteq> a2 ; entry_set t a2 v \<noteq> {} \<rbrakk> \<Longrightarrow>
    entry_set (t - asid_entry_set t a1) a2 v \<noteq> {}"
  unfolding entry_set_def asid_entry_set_def entry_range_asid_tags_def
  by auto

theorem  lookup_asid_inv_incon:
  "\<lbrakk> a1 \<noteq> a2 ; lookup t a2 v = Incon \<rbrakk> \<Longrightarrow>
         lookup (asid_invalidation t a1) a2 v = Incon"
  unfolding asid_invalidation_def lookup_def
  apply (simp split: if_split_asm)
  apply safe
  apply (clarsimp simp:for_incon)
  apply (subgoal_tac "entry_set t a2 v \<noteq> {}")
  apply (clarsimp simp:entry_set_comp)
  by auto


theorem
  "\<lbrakk> a1 \<noteq> a2 ; lookup t a2 v = S \<rbrakk> \<Longrightarrow>
         lookup (asid_invalidation t a1) a2 v = S"
  apply (case_tac "S")
  by (clarsimp simp: lookup_asid_inv_miss lookup_asid_inv_incon lookup_asid_inv_hit)+


(* Virtual Address Invalidation for all ASID *)

(* set of entries having v in their range *)
definition
  va_entry_set :: "tlb  \<Rightarrow> vaddr \<Rightarrow> (tlb_entry set)"
where
  "va_entry_set t v \<equiv> {E\<in>t. v : entry_range E} "


(* set of all the virtual addresses covered by TLB *)
definition
  va_set :: "tlb \<Rightarrow> (vaddr set)"
where
  "va_set t \<equiv> \<Union> (entry_range ` t)"


(* is Virtual Address covered by TLB *)
definition
  is_va_present :: "tlb  \<Rightarrow> vaddr \<Rightarrow> bool"
where
  "is_va_present t v \<equiv> v : va_set t"


(*  -------- selective invalidation -------- *)

definition
  va_sel_invalidation :: "tlb \<Rightarrow> vaddr \<Rightarrow> tlb"
where
  "va_sel_invalidation t v \<equiv> t - va_entry_set t v"



theorem is_presect_va_invlaidation:
  "\<not>is_va_present (va_sel_invalidation t v) v"
  unfolding is_va_present_def va_sel_invalidation_def
    va_entry_set_def va_set_def
    by simp

theorem  entry_set_va_set:
  "(entry_set t a v = {}) = ((a, v) \<notin> a_va_set t)"
  apply (unfold a_va_set_def entry_set_def)[1]
  by auto

theorem entry_set_empty_va_inv:
  "entry_set (va_sel_invalidation t v) a v = {}"
  apply (simp add: entry_set_va_set)
  apply safe
  apply (unfold va_sel_invalidation_def a_va_set_def)[1]
  apply clarsimp
  apply (subgoal_tac "x \<in> entry_set t a v" )
  prefer 2
  apply (unfold entry_set_def)[1]
  apply simp
  apply (subgoal_tac "x \<in> va_entry_set t v" )
  apply simp
  apply (unfold entry_set_def va_entry_set_def entry_range_asid_tags_def)[1]
  by auto



theorem lookup_va_invalid:
  "lookup (va_sel_invalidation t v) a v = Miss"
  apply (unfold lookup_def)
  apply (simp split: if_split)
  by (clarsimp simp: entry_set_empty_va_inv)


lemma entry_set_def2:
  "entry_set t a v = {e\<in>t. v \<in> entry_range e \<and> a = asid_entry e}"
  by (auto simp: entry_set_def entry_range_asid_tags_def)


(*---------------------------------------------------*)

instantiation lookup_type :: order
begin
  definition
    less_eq_lookup_type: "e \<le> e' \<equiv> e' = Incon \<or> e' = e \<or> e = Miss"

  definition
    less_lookup_type: "e < (e'::lookup_type) \<equiv> e \<le> e' \<and> e \<noteq> e'"

  instance
     by intro_classes (auto simp add: less_lookup_type less_eq_lookup_type)
end


lemma Incon_top [iff]: "e \<le> Incon"
  by (simp add: less_eq_lookup_type)

lemma Incon_leq [simp]: "(Incon \<le> e) = (e = Incon)"
  by (auto simp add: less_eq_lookup_type)

lemma Miss_bottom [iff]: "Miss \<le> e"
  by (simp add: less_eq_lookup_type)

lemma leq_Miss [simp]: "(e \<le> Miss) = (e = Miss)"
  by (auto simp add: less_eq_lookup_type)

lemma Hits_le [simp]:
  "(Hit h \<le> Hit h') = (h = h')"
  by (auto simp add: less_eq_lookup_type)

lemma tlb_mono_entry_set:
  "t \<subseteq> t' \<Longrightarrow> entry_set t a v \<subseteq> entry_set t' a v"
  by (simp add: entry_set_def) blast

lemma tlb_mono:
  "t \<subseteq> t' \<Longrightarrow> lookup t a v \<le> lookup t' a v"
  by (drule tlb_mono_entry_set) (fastforce simp: lookup_def)


(*   Page Tables   *)

type_synonym mem_type = "32 word \<Rightarrow> 8 word option"

type_synonym ttbr0 = paddr


(* works well only for descriptors *)

definition
  word_fetch :: "mem_type \<Rightarrow> 32 word \<Rightarrow> 32 word option"
where
  "word_fetch  mem pa \<equiv>
      case mem pa of
            None   \<Rightarrow> None
          | Some _ \<Rightarrow>
            Some (((ucast (the (mem pa))       ::32 word) << 24)  OR
                  ((ucast (the (mem (pa + 1))) ::32 word) << 16)  OR
                  ((ucast (the (mem (pa + 2))) ::32 word) << 8)   OR
                  (ucast  (the (mem (pa + 3))) ::32 word)) "



definition
 pt_walk :: "asid \<Rightarrow> heap \<Rightarrow> ttbr0 \<Rightarrow> vaddr \<Rightarrow> tlb_entry option"
where
  "pt_walk asid heap ttbr0 v \<equiv>
      case get_pde heap ttbr0 v
       of None                 \<Rightarrow> None
       | Some InvalidPDE       \<Rightarrow> None
       | Some ReservedPDE      \<Rightarrow> None
       | Some (SectionPDE p a) \<Rightarrow> Some (EntrySection asid (ucast (addr_val v >> 20) :: 12 word)
                                       ((word_extract 31 20 (addr_val p)):: 12 word)  (0::8 word))
       | Some (PageTablePDE p) \<Rightarrow>
               (case get_pte heap p v
                 of None                     \<Rightarrow> None
                 |  Some InvalidPTE          \<Rightarrow> None
                 |  Some (SmallPagePTE p1 a) \<Rightarrow> Some(EntrySmall asid (ucast (addr_val v >> 12) :: 20 word)
                                                    ((word_extract 31 12 (addr_val p1):: 20 word)) 0))"

definition
  "is_fault (e::tlb_entry option) \<equiv> (e = None)"



end
