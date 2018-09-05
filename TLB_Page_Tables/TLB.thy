(*
 * Copyright 2016, Data61, CSIRO
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *)

theory TLB
imports
  PTABLE.PageTable_seL4

begin

type_synonym vSm = "20 word"
type_synonym pSm = "20 word"

type_synonym vLr = "16 word"
type_synonym pLr = "16 word"

type_synonym vSe = "12 word"
type_synonym pSe = "12 word"

type_synonym vSp = "8 word"
type_synonym pSp = "8 word"

type_synonym asid  = "8 word"

type_synonym va    = "32 word"


datatype memtyp_t = MemNormal |  MemDevice |  MemStronglyOrdered


record memattribs_t = 
   memtyp           :: memtyp_t
   innerattrs		    :: "2 word"
   outerattrs		    :: "2 word"
   innerhints		    :: "2 word"
   outerhints		    :: "2 word"
   innertransient   :: bool
   outertransient   :: bool
   shareable        :: bool
   outershareable   :: bool


record permissions_t =
   accessperm   :: "3 word"
   executenever	  :: "1 word"
   pexecutenever  :: "1 word"


record flags_t =                 
   memattribs  :: memattribs_t
   permissions :: permissions_t
   domain  ::  "4 word"
   level   :: int


(*  can also make a datatype for base addresses *)

datatype tlb_entry =
    Entrysmall   (tag : "asid option") vSm pSm (flags : flags_t)
  | Entrylarge   (tag : "asid option") vLr pLr (flags : flags_t)
  | Entrysection (tag : "asid option") vSe pSe (flags : flags_t)
  | Entrysuper   (tag : "asid option") vSp pSp (flags : flags_t)

type_synonym tlb = "tlb_entry set"

datatype lookup_type  =  Miss  | Incon  |  Hit "tlb_entry"


(* Address Range of an Entry *)
definition
  entry_range :: "tlb_entry \<Rightarrow> va set"
where
  "entry_range E \<equiv> case E of Entrysmall   a va pa f   \<Rightarrow> {(ucast va::32 word) << 12 ..
                                                            ((ucast va::32 word) << 12) + (2^12 - 1)}

                      |      Entrylarge   a va pa f    \<Rightarrow> {(ucast va::32 word) << 16 ..
                                                            ((ucast va::32 word) << 16) + (2^16 - 1)}

                      |      Entrysection a va pa f    \<Rightarrow> {(ucast va::32 word) << 20 ..
                                                            ((ucast va::32 word) << 20) + (2^20 - 1)}

                      |      Entrysuper   a va pa f    \<Rightarrow> {(ucast va::32 word) << 24 ..
                                                            ((ucast va::32 word) << 24) + (2^24 - 1)}"


definition
  entry_range_tags :: "tlb_entry \<Rightarrow> (asid option \<times> va) set"
where
  "entry_range_tags E \<equiv> image (\<lambda>v. (tag E , v)) (entry_range E)"

(*
definition 
  tlb_asid :: "tlb_entry set \<Rightarrow> tlb_entry set"
where
  "tlb_asid t = {E\<in>t. tag_entry E \<noteq> Global}"

lemma tlb_asid_check:
  "\<forall>tag\<in>(tag_entry ` tlb_asid t). \<exists>a. tag = Asid a"
  apply (clarsimp simp: tlb_asid_def)
  using tag.exhaust by auto

definition 
  tlb_global :: "tlb_entry set \<Rightarrow> tlb_entry set"
where
  "tlb_global t = {E\<in>t. tag_entry E = Global}"


lemma tlb_asid_global_check:
  "t = tlb_global t  \<union> tlb_asid t"
  apply (clarsimp simp: tlb_asid_def tlb_global_def)
  by blast



definition
  entry_set :: "tlb \<Rightarrow> asid \<Rightarrow> va \<Rightarrow> (tlb_entry set)"
where
  "entry_set t a v \<equiv> {E\<in>tlb_asid t. (Asid a,v) : entry_range_tags E } \<union>
                      {E\<in>tlb_global t. (Global,v) : entry_range_tags E } "
*)

definition
  entry_set :: "tlb \<Rightarrow> asid \<Rightarrow> va \<Rightarrow> (tlb_entry set)"
where
  "entry_set t a v \<equiv> {E\<in> t. \<exists>a'. (a',v) : entry_range_tags E \<and> (a' = None \<or> a' = Some a)}"

(* another version *)

definition
  entry_set' :: "tlb \<Rightarrow> asid \<Rightarrow> va \<Rightarrow> (tlb_entry set)"
where
  "entry_set' t a v \<equiv> {E\<in> t. v : entry_range E \<and> (tag E = None \<or> tag E = Some a)}"


(*
definition
  entry_set' :: "tlb \<Rightarrow> asid \<Rightarrow> va \<Rightarrow> (tlb_entry set)"
where
  "entry_set' t a v \<equiv> {E\<in>tlb_asid t. (Asid a,v) : entry_range_tags E } \<union>
                      {E\<in>tlb_global t. v : entry_range E } "
*)


(* Lookup for a virtual address along with an ASID *)
definition
  lookup :: "tlb \<Rightarrow> asid \<Rightarrow> va \<Rightarrow> lookup_type"
where
  "lookup t a va \<equiv> if entry_set t a va = {} then Miss
                   else if \<exists>x. entry_set t a va = {x} then Hit (the_elem (entry_set t a va))
                        else Incon"

(* commenting out for the time being *)
(*
(* set of all the virtual addresses with ASID tags covered by TLB *)
definition
  tag_va_set :: "tlb \<Rightarrow> (tag \<times> va) set"
where
  "tag_va_set t \<equiv> \<Union> (entry_range_tags ` t)"


(* Is a virtual address and an ASID covered by TLB *)
definition
  is_a_va_present :: "tlb \<Rightarrow> asid \<Rightarrow> va \<Rightarrow> bool"
where
  "is_a_va_present t a v \<equiv> (Asid a, v) : tag_va_set (tlb_asid t)"


definition
  is_global_va_present :: "tlb \<Rightarrow> va \<Rightarrow> bool"
where
  "is_global_va_present t v \<equiv> (Global, v) : tag_va_set (tlb_global t)"


(* Selective invalidation of a virtual address for an ASID *)

definition
  a_va_sel_invalidate :: "tlb \<Rightarrow> asid \<Rightarrow> va \<Rightarrow> tlb"
where
  "a_va_sel_invalidate t a v \<equiv> t -{E\<in>tlb_asid t. (Asid a,v) : entry_range_tags E } "

definition
  global_va_sel_invalidate :: "tlb \<Rightarrow> va \<Rightarrow> tlb"
where
  "global_va_sel_invalidate t v \<equiv> t - {E\<in>tlb_global t. (Global,v) : entry_range_tags E }"


theorem is_present_selective:
  "\<not>(is_a_va_present (a_va_sel_invalidate t a v) a v)"
  unfolding a_va_sel_invalidate_def
            lookup_def is_a_va_present_def entry_set_def tag_va_set_def tlb_asid_def
  by (fastforce split: if_split_asm)


(* Block invalidation of a set of virtual addresses for an ASID *)

definition
  a_va_block_invalidation :: "tlb \<Rightarrow> asid \<Rightarrow> va set \<Rightarrow> tlb"
where
  "a_va_block_invalidation t a V \<equiv> \<Inter>x\<in>V. a_va_sel_invalidate t a x"


definition
  is_a_vset_present :: "tlb \<Rightarrow> asid \<Rightarrow> va set \<Rightarrow> bool"
where
  "is_a_vset_present t a V \<equiv> \<exists>v\<in>V. is_a_va_present t a v"

theorem lookup_miss_case:
  "lookup t a v = Miss \<Longrightarrow> \<not>is_a_va_present t a v"
  unfolding is_a_va_present_def lookup_def entry_set_def tag_va_set_def tlb_asid_def
  by (simp split: if_split_asm)


(* Theorems for Block Invalidation *)
theorem  lookup_incon_case:
  "lookup t a v = Incon \<Longrightarrow> \<not>is_a_va_present (t - entry_set t a v) a v"
  unfolding is_a_va_present_def lookup_def entry_set_def tag_va_set_def tlb_asid_def tlb_global_def
  by (simp split: if_split_asm, blast)


theorem lookup_hit_case:
  "lookup t a v = Hit x \<Longrightarrow> \<not>is_a_va_present (t - {x}) a v"
  unfolding is_a_va_present_def lookup_def entry_set_def tag_va_set_def tlb_asid_def tlb_global_def
  by (simp split: if_split_asm, blast)

theorem member_selective_invalidation:
  "x \<in> a_va_sel_invalidate t a v \<Longrightarrow> (Asid a,v) \<notin>  entry_range_tags x"
  by (clarsimp simp: a_va_sel_invalidate_def tlb_asid_def entry_range_tags_def)
 

theorem is_present_block:
  "\<not>(is_a_vset_present (a_va_block_invalidation t a V) a V)"
  apply (clarsimp simp: is_a_vset_present_def a_va_block_invalidation_def is_a_va_present_def 
                        a_va_sel_invalidate_def tag_va_set_def tlb_asid_def entry_range_tags_def)
  by blast

(* is_TLB_okay *)

definition
  overlapping_entries :: "tlb \<Rightarrow> tlb"
where
  "overlapping_entries t \<equiv>
     {x\<in>t. (entry_range_tags x \<inter> tag_va_set (t - {x}) ) \<noteq> {} }"


definition
  is_okay :: "tlb \<Rightarrow> bool"
where
  "is_okay t \<equiv> (overlapping_entries t = {})"

theorem member_va_set:
  "(Asid a,v) \<in> tag_va_set t \<Longrightarrow> entry_set t a v \<noteq> {}"
  unfolding tag_va_set_def entry_set_def tlb_asid_def
  apply clarsimp
  unfolding  entry_range_tags_def
  by force

theorem  inter_entry_va_set:
  "entry_range_tags x \<inter> tag_va_set (t - {x}) = {} \<Longrightarrow>
     \<forall>y\<in>t. \<forall>av\<in>entry_range_tags x. y \<noteq> x \<longrightarrow> av \<notin> entry_range_tags y"
  unfolding tag_va_set_def
  by force

theorem  invalidating_corrupt_entries:
  "is_okay (t - overlapping_entries t)"
  apply (clarsimp simp: is_okay_def overlapping_entries_def tag_va_set_def)
  by blast

*)

(* Physical Address Retrieval *)

datatype bpa = Bpsm "20 word" | Bplr "16 word" | Bpse "12 word" | Bpsp "8 word"


fun
  bpa_entry :: "tlb_entry \<Rightarrow> bpa "
where
  "bpa_entry (Entrysmall _ _ p _)   =  Bpsm p"
| "bpa_entry (Entrylarge _ _ p _)   =  Bplr p"
| "bpa_entry (Entrysection _ _ p _) =  Bpse p"
| "bpa_entry (Entrysuper _ _ p _)   =  Bpsp p"


fun
  bpa_to_pa :: "va \<Rightarrow> bpa \<Rightarrow> 32 word"
where
  "bpa_to_pa va (Bpsm bpa) = (ucast bpa << 12) OR (va AND mask 12)"
| "bpa_to_pa va (Bplr bpa) = (ucast bpa << 16) OR (va AND mask 16)"
| "bpa_to_pa va (Bpse bpa) = (ucast bpa << 20) OR (va AND mask 20)"
| "bpa_to_pa va (Bpsp bpa) = (ucast bpa << 24) OR (va AND mask 24)"


definition
  va_to_pa :: "va \<Rightarrow> tlb_entry \<Rightarrow> 32 word"
where
  "va_to_pa v t \<equiv> bpa_to_pa v ( bpa_entry t)"


(*
(* Uniqueness *)

theorem lookup_miss_not_present_implies:
  "lookup t a v = Miss \<Longrightarrow> \<not>is_a_va_present t a v"
  by (simp add: lookup_miss_case)

theorem not_present_lookup_miss_implies:
  "\<not>is_a_va_present t a v \<Longrightarrow> lookup t a v = Miss"
  (* not true anymore *)
  oops

(* not true anymore *)
theorem lookup_miss_not_present:
  "(lookup t a v = Miss) = (\<not>is_a_va_present t a v)"
  (*apply (rule iffI)
  unfolding is_a_va_present_def lookup_def entry_set_def  tag_va_set_def tlb_asid_def tlb_global_def
  apply (simp split: if_split_asm)+ *)
  oops


(* ---------------------------------------------------------------------*)

theorem is_present_look_up_not_miss_implies:
  "is_a_va_present t a v \<Longrightarrow> lookup t a v \<noteq> Miss "
  unfolding is_a_va_present_def lookup_def entry_set_def tag_va_set_def
  apply (safe)
  by (simp split: if_split_asm)

(* not true anymore *)
theorem look_up_not_miss_is_present_imples:
  "lookup t a v \<noteq> Miss \<Longrightarrow> is_a_va_present t a v"
  (*unfolding is_a_va_present_def lookup_def entry_set_def tag_va_set_def
  apply (simp split: if_split_asm)
  by force+ *)
  oops

(* have to see *)
theorem is_present_look_up_not_miss:
  "(is_a_va_present t a v) = (lookup t a v \<noteq> Miss)"
  (*apply (rule iffI)
  unfolding is_a_va_present_def lookup_def entry_set_def tag_va_set_def
  apply (safe)
  by (simp split: if_split_asm ; force)+
*)
oops

(* ---------------------------------------------------------------------*)
 (* have to see *)
theorem is_okay_not_empty_exist:
  "\<lbrakk>is_okay t ; entry_set t a v \<noteq> {} \<rbrakk> \<Longrightarrow> \<exists>x. entry_set t a v = {x}"
 (* apply (clarsimp simp: is_okay_def overlapping_entries_def entry_set_def tag_va_set_def entry_range_tags_def tlb_asid_def tlb_global_def)

  unfolding entry_set_def
  unfolding is_okay_def overlapping_entries_def
  unfolding tag_va_set_def
  apply clarsimp
  apply (drule_tac x="x" in spec)
  apply clarsimp
  apply (rule_tac x="x" in exI)
  by auto
*)

oops

theorem is_okay_not_miss_exist:
  "\<lbrakk>is_okay t ; lookup t a v \<noteq> Miss  \<rbrakk> \<Longrightarrow>
               \<exists>x\<in>t. lookup t a v = Hit x"
(*  unfolding lookup_def
  apply (simp split: if_split_asm)
  apply (unfold entry_set_def) [1]
  apply force
  apply (drule(1) is_okay_not_empty_exist)
  by simp *)
oops

(* ---------------------------------------------------------------------*)

theorem is_okay_is_present_not_incon:
  "\<lbrakk>is_okay t ; is_a_va_present t a v \<rbrakk> \<Longrightarrow> lookup t a v \<noteq> Incon"
(*  apply safe
  apply (drule is_present_look_up_not_miss_implies)
  unfolding lookup_def
  apply (simp split: if_split_asm)
  unfolding is_okay_def overlapping_entries_def a_va_set_def entry_set_def
  apply clarsimp
  apply (drule_tac x="x" in spec)
  apply simp
  apply (drule_tac x="x" in spec)
  by force
*)
oops

theorem is_okay_not_incon:
  "is_okay t \<Longrightarrow>  \<forall>v a. lookup t a v \<noteq> Incon"
(*  apply safe
  unfolding lookup_def
  apply (simp split: if_split_asm)
  unfolding is_okay_def overlapping_entries_def a_va_set_def entry_set_def
  apply clarsimp
  apply (drule_tac x="x" in spec)
  apply simp
  apply (drule_tac x="x" in spec)
  by force
*)
oops


(*
theorem  entry_set_empty:
  "entry_set t a v  = {} \<Longrightarrow> (Asid a, v) \<notin> tag_va_set t"
   unfolding entry_set_def tag_va_set_def tlb_global_def tlb_asid_def entry_range_tags_def
 oops

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
      \<forall>x\<in>t. \<forall>v a. (a, v) \<in> tag_va_set t \<longrightarrow> lookup t a v \<noteq> Incon"
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

*)
(* ---------------------------------------------------------------------*)


(*          ASID INVALIDATION CASE       *)

(* set of all the entries for a particular ASID *)
(*
definition
  asid_entry_set :: "tlb \<Rightarrow> Asid \<Rightarrow> (tlb_entry set)"
where
  "asid_entry_set t a \<equiv> {E\<in>t. asid_entry E = a} "

definition
  asid_set :: "tlb \<Rightarrow> Asid set"
where
  "asid_set t \<equiv> asid_entry ` t"

(* is ASID entries present in TLB *)

definition
  is_asid_present :: "tlb \<Rightarrow> Asid \<Rightarrow> bool"
where
  "is_asid_present t a \<equiv>  a : asid_set t"



(* ASID Invalidation *)

definition
  asid_invalidation :: "tlb \<Rightarrow> Asid \<Rightarrow> tlb"
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
  va_entry_set :: "tlb  \<Rightarrow> va \<Rightarrow> (tlb_entry set)"
where
  "va_entry_set t v \<equiv> {E\<in>t. v : entry_range E} "


(* set of all the virtual addresses covered by TLB *)
definition
  va_set :: "tlb \<Rightarrow> (va set)"
where
  "va_set t \<equiv> \<Union> (entry_range ` t)"


(* is Virtual Address covered by TLB *)
definition
  is_va_present :: "tlb  \<Rightarrow> va \<Rightarrow> bool"
where
  "is_va_present t v \<equiv> v : va_set t"


(*  -------- selective invalidation -------- *)

definition
  va_sel_invalidation :: "tlb \<Rightarrow> va \<Rightarrow> tlb"
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
*)

*)

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
  by (simp add: entry_set_def ) blast

lemma tlb_mono:
  "t \<subseteq> t' \<Longrightarrow> lookup t a v \<le> lookup t' a v"
  by (drule tlb_mono_entry_set) (fastforce simp: lookup_def)


(*   Page Tables   *)

type_synonym mem_type = "32 word \<Rightarrow> 8 word option"

(* works well only for descriptors *)

definition
  word_fetch :: "mem_type \<Rightarrow> 32 word \<Rightarrow> 32 word option"
where
  "word_fetch  mem pa \<equiv>
      case mem pa of
            None   \<Rightarrow> None
          | Some _ \<Rightarrow>
            Some  (((ucast (the (mem pa))       ::32 word) << 24)  OR
                  ((ucast (the (mem (pa + 1))) ::32 word) << 16)  OR
                  ((ucast (the (mem (pa + 2))) ::32 word) << 8)   OR
	                (ucast  (the (mem (pa + 3))) ::32 word)) "


end
