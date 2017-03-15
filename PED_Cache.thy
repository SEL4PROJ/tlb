theory PED_Cache
imports 
 TLB
begin



datatype bpa_pde_type = bpa_sec "32 word" 
                 |      bpa_sm  "32 word"

datatype pde_entry =  EntryPDE asid vSe "bpa_pde_type option" fl

type_synonym pde_cache = "pde_entry set"


datatype lookup_pde_type  =  Miss_pde  | Incon_pde  |  Hit_pde "pde_entry" 



fun 
  pde_entry_asid :: "pde_entry \<Rightarrow> asid"
where
  "pde_entry_asid (EntryPDE a va pa f)= a" 



(* Address Range of an Entry *)
fun 
  pde_entry_range :: "pde_entry \<Rightarrow> va set"
where
  "pde_entry_range (EntryPDE a va pa f) =  {(ucast va::32 word) << 20 ..
                                                            ((ucast va::32 word) << 20) + (2^20 - 1)}" 


(* Address Range of an entry with ASID tag *)
definition 
  pde_entry_range_asid_tags :: "pde_entry \<Rightarrow> (asid \<times> va) set"
where
  "pde_entry_range_asid_tags E \<equiv> image (\<lambda>v. (pde_entry_asid E , v)) (pde_entry_range E)"
 



(* Set of all the entries covering a virtual address and an ASID *)
definition 
  pde_entry_set :: "pde_cache \<Rightarrow> asid \<Rightarrow> va \<Rightarrow> (pde_entry set)"
where
  "pde_entry_set t a v \<equiv> {E\<in>t. (a,v) : pde_entry_range_asid_tags E } "



(* Lookup for a virtual address along with an ASID *)
definition 
  lookup_pde :: "pde_cache \<Rightarrow> asid \<Rightarrow> va \<Rightarrow> lookup_pde_type" 
where  
  "lookup_pde t a va \<equiv> if pde_entry_set t a va = {} then Miss_pde
                   else if \<exists>x. pde_entry_set t a va = {x} then Hit_pde (the_elem (pde_entry_set t a va)) 
                        else Incon_pde"



definition 
 pt_walk_pde :: "asid \<Rightarrow> heap \<Rightarrow> ttbr0 \<Rightarrow> vaddr \<Rightarrow> pde_entry"
where
  "pt_walk_pde asid heap ttbr0 v \<equiv>
      case get_pde heap ttbr0 v
       of None                 \<Rightarrow> EntryPDE asid (ucast (addr_val v >> 20) :: 12 word) None 0
       | Some InvalidPDE       \<Rightarrow> EntryPDE asid (ucast (addr_val v >> 20) :: 12 word) None 0
       | Some ReservedPDE      \<Rightarrow> EntryPDE asid (ucast (addr_val v >> 20) :: 12 word) None 0
       | Some (SectionPDE p a) \<Rightarrow> 
          EntryPDE asid (ucast (addr_val v >> 20) :: 12 word) (Some (bpa_sec (addr_val p)))  0 
       | Some (PageTablePDE p) \<Rightarrow> 
            EntryPDE asid (ucast (addr_val v >> 20) :: 12 word)  (Some (bpa_sm (addr_val p))) 0" 



fun 
  bpa_pde_entry :: "pde_entry \<Rightarrow>  bpa_pde_type option"
where                                    
  "bpa_pde_entry (EntryPDE _ _ p _) =  p"


definition
  "is_fault_pde e = (bpa_pde_entry e = None)"


instantiation lookup_pde_type :: order
begin
  definition 
    less_eq_lookup_pde_type: "e \<le> e' \<equiv> e' = Incon_pde \<or> e' = e \<or> e = Miss_pde"

  definition 
    less_lookup_pde_type: "e < (e'::lookup_pde_type) \<equiv> e \<le> e' \<and> e \<noteq> e'"

  instance
     by intro_classes (auto simp add: less_lookup_pde_type less_eq_lookup_pde_type)
end


lemma Incon_pde_top [iff]: "e \<le> Incon_pde"
  by (simp add: less_eq_lookup_pde_type)

lemma Incon_pde_leq [simp]: "(Incon_pde \<le> e) = (e = Incon_pde)"
  by (auto simp add: less_eq_lookup_pde_type)

lemma Miss_pde_bottom [iff]: "Miss_pde \<le> e"
  by (simp add: less_eq_lookup_pde_type)

lemma leq_pde_Miss [simp]: "(e \<le> Miss_pde) = (e = Miss_pde)"
  by (auto simp add: less_eq_lookup_pde_type)

lemma Hits_pde_le [simp]:
  "(Hit_pde h \<le> Hit_pde h') = (h = h')"
  by (auto simp add: less_eq_lookup_pde_type)

lemma tlb_mono_pde_entry_set:
  "t \<subseteq> t' \<Longrightarrow> pde_entry_set t a v \<subseteq> pde_entry_set t' a v"
  by (simp add: pde_entry_set_def) blast

lemma tlb_pde_mono:
  "t \<subseteq> t' \<Longrightarrow> lookup_pde t a v \<le> lookup_pde t' a v"
  by (drule tlb_mono_pde_entry_set) (fastforce simp: lookup_pde_def)

(*
(* set of all the virtual addresses with ASID tags covered by TLB *)
definition 
  a_va_set_pde :: "pde_cache \<Rightarrow> (asid \<times> va) set"
where
  "a_va_set_pde t \<equiv> \<Union> (pde_entry_range_asid_tags ` t)"


(* Is a virtual address and an ASID covered by TLB *)
definition 
  is_a_va_present_pde :: "pde_cache \<Rightarrow> asid \<Rightarrow> va \<Rightarrow> bool" 
where
  "is_a_va_present_pde t a v \<equiv> (a,v) : a_va_set_pde t"


(* Selective invalidation of a virtual address for an ASID *)

definition 
  a_va_sel_invalidate_pde :: "pde_cache \<Rightarrow> asid \<Rightarrow> va \<Rightarrow> pde_cache" 
where 
  "a_va_sel_invalidate_pde t a v \<equiv> case lookup_pde t a v of Hit_pde x \<Rightarrow> t - {x}
                                                          | Miss_pde  \<Rightarrow> t 
                                                          | Incon_pde \<Rightarrow> t - pde_entry_set t a v"

theorem is_present_selective:
  "\<not>(is_a_va_present_pde (a_va_sel_invalidate_pde t a v) a v)"
  unfolding a_va_sel_invalidate_pde_def
            lookup_pde_def is_a_va_present_pde_def pde_entry_set_def a_va_set_pde_def
  by (fastforce split: split_if_asm)


(* Block invalidation of a set of virtual addresses for an ASID *)

definition 
  a_va_block_invalidation_pde :: "pde_cache \<Rightarrow> asid \<Rightarrow> va set \<Rightarrow> pde_cache" 
where 
  "a_va_block_invalidation_pde t a V \<equiv> \<Inter>x\<in>V. a_va_sel_invalidate_pde t a x"


definition 
  is_a_vset_present_pde :: "pde_cache \<Rightarrow> asid \<Rightarrow> va set \<Rightarrow> bool"
where
  "is_a_vset_present_pde t a V \<equiv> \<exists>v\<in>V. is_a_va_present_pde t a v"

theorem lookup_miss_case:
  "lookup_pde t a v = Miss_pde \<Longrightarrow> \<not>is_a_va_present_pde t a v"
  unfolding is_a_va_present_pde_def lookup_pde_def pde_entry_set_def a_va_set_pde_def
  by (simp split: split_if_asm)
  
 
(* Theorems for Block Invalidation *)
theorem  lookup_incon_case:
  "lookup_pde t a v = Incon_pde \<Longrightarrow> \<not>is_a_va_present_pde (t - pde_entry_set t a v) a v"
  unfolding is_a_va_present_pde_def lookup_pde_def pde_entry_set_def a_va_set_pde_def
  by (simp split: split_if_asm)


theorem lookup_hit_case:
  "lookup_pde t a v = Hit_pde x \<Longrightarrow> \<not>is_a_va_present_pde (t - {x}) a v"
  unfolding lookup_pde_def is_a_va_present_pde_def pde_entry_set_def a_va_set_pde_def
  by (force split: split_if_asm)

theorem member_selective_invalidation:  
  "x \<in> a_va_sel_invalidate_pde t a v \<Longrightarrow> (a,v) \<notin>  pde_entry_range_asid_tags x"
  unfolding a_va_sel_invalidate_pde_def
  apply (simp split: lookup_pde_type.splits)
  apply (drule lookup_miss_case)
  unfolding is_a_va_present_pde_def a_va_set_pde_def
  apply (simp)
  apply (drule lookup_incon_case)
  unfolding is_a_va_present_pde_def a_va_set_pde_def
  apply (simp)
  apply (drule lookup_hit_case)
  unfolding is_a_va_present_pde_def a_va_set_pde_def
  by (simp)



theorem is_present_block:
  "\<not>(is_a_vset_present_pde (a_va_block_invalidation_pde t a V) a V)"
  unfolding is_a_vset_present_pde_def 
  apply (safe)
  unfolding is_a_va_present_pde_def  
  apply (subgoal_tac "pde_entry_set (a_va_block_invalidation_pde t a V) a v \<noteq> {}")
  unfolding pde_entry_set_def a_va_block_invalidation_pde_def
  apply clarsimp
  apply (drule_tac x="v" in bspec, assumption , simp add: member_selective_invalidation)
  unfolding a_va_set_pde_def pde_entry_set_def
  by force
 

(* is_TLB_okay *)

definition 
  overlapping_entries :: "pde_cache \<Rightarrow> pde_cache"
where
  "overlapping_entries t \<equiv> 
     {x\<in>t. (pde_entry_range_asid_tags x \<inter> a_va_set_pde (t - {x}) ) \<noteq> {} }"


definition
  is_okay :: "pde_cache \<Rightarrow> bool"
where
  "is_okay t \<equiv> (overlapping_entries t = {})"

theorem member_va_set:
  "(a,v) \<in> a_va_set_pde t \<Longrightarrow> pde_entry_set t a v \<noteq> {}"
  unfolding a_va_set_pde_def pde_entry_set_def 
  apply clarsimp
  unfolding  pde_entry_range_asid_tags_def
  by force 

theorem  inter_entry_va_set:
  "pde_entry_range_asid_tags x \<inter> a_va_set_pde (t - {x}) = {} \<Longrightarrow>
     \<forall>y\<in>t. \<forall>av\<in>pde_entry_range_asid_tags x. y \<noteq> x \<longrightarrow> av \<notin> pde_entry_range_asid_tags y"
  unfolding a_va_set_pde_def
  by force

theorem  invalidating_corrupt_entries:
  "is_okay (t - overlapping_entries t)"
  unfolding is_okay_def overlapping_entries_def  
  apply safe
  apply (drule member_va_set)
  unfolding pde_entry_set_def
  apply clarsimp
  apply (drule inter_entry_va_set , drule_tac x="xa" in bspec , assumption ,
               drule_tac x="(a,b)" in bspec , assumption )
   by simp


(* Physical Address Retrieval *)

fun 
  bpa_pde_entry :: "pde_entry \<Rightarrow> bpa option"
where                                    
  "bpa_pde_entry (EntryPDE _ _ p _) =  p"


definition
  "is_fault' e = (bpa_pde_entry e = None)"




(* Uniqueness *)

theorem lookup_miss_not_present_implies:
  "lookup_pde t a v = Miss_pde \<Longrightarrow> \<not>is_a_va_present_pde t a v"
  unfolding is_a_va_present_pde_def lookup_pde_def pde_entry_set_def a_va_set_pde_def
  by (simp split: split_if_asm)

theorem not_present_lookup_miss_implies:
  "\<not>is_a_va_present_pde t a v \<Longrightarrow> lookup_pde t a v = Miss_pde"
  unfolding is_a_va_present_pde_def lookup_pde_def pde_entry_set_def a_va_set_pde_def
  by (simp split: split_if_asm)

theorem lookup_miss_not_present:
  "(lookup_pde t a v = Miss_pde) = (\<not>is_a_va_present_pde t a v)"
  apply (rule iffI)
  unfolding is_a_va_present_pde_def lookup_pde_def pde_entry_set_def a_va_set_pde_def
  by (simp split: split_if_asm)+
  
(* ---------------------------------------------------------------------*)

theorem is_present_look_up_not_miss_implies:
  "is_a_va_present_pde t a v \<Longrightarrow> lookup_pde t a v \<noteq> Miss_pde "
  unfolding is_a_va_present_pde_def lookup_pde_def pde_entry_set_def a_va_set_pde_def
  apply (safe)
  by (simp split: split_if_asm)

theorem look_up_not_miss_is_present_imples:
  "lookup_pde t a v \<noteq> Miss_pde \<Longrightarrow> is_a_va_present_pde t a v"
  unfolding is_a_va_present_pde_def lookup_pde_def pde_entry_set_def a_va_set_pde_def
  apply (simp split: split_if_asm)
  by force+

theorem is_present_look_up_not_miss:
  "(is_a_va_present_pde t a v) = (lookup_pde t a v \<noteq> Miss_pde)"
  apply (rule iffI)
  unfolding is_a_va_present_pde_def lookup_pde_def pde_entry_set_def a_va_set_pde_def
  apply (safe)
  by (simp split: split_if_asm ; force)+

(* ---------------------------------------------------------------------*)

theorem is_okay_not_empty_exist:
  "\<lbrakk>is_okay t ; pde_entry_set t a v \<noteq> {} \<rbrakk> \<Longrightarrow> \<exists>x. pde_entry_set t a v = {x}"
  unfolding pde_entry_set_def
  unfolding is_okay_def overlapping_entries_def
  unfolding a_va_set_pde_def
  apply clarsimp
  apply (drule_tac x="x" in spec)
  apply clarsimp
  apply (rule_tac x="x" in exI)
  by auto


theorem is_okay_not_miss_exist:
  "\<lbrakk>is_okay t ; lookup_pde t a v \<noteq> Miss_pde  \<rbrakk> \<Longrightarrow> 
               \<exists>x\<in>t. lookup_pde t a v = Hit_pde x"
  unfolding lookup_pde_def
  apply (simp split: split_if_asm)
  apply (unfold pde_entry_set_def) [1]
  apply force
  apply (drule(1) is_okay_not_empty_exist)
  by simp
(* ---------------------------------------------------------------------*)

theorem is_okay_is_present_not_incon:
  "\<lbrakk>is_okay t ; is_a_va_present_pde t a v \<rbrakk> \<Longrightarrow> lookup_pde t a v \<noteq> Incon_pde"
  apply safe
  apply (drule is_present_look_up_not_miss_implies)
  unfolding lookup_pde_def
  apply (simp split: split_if_asm)
  unfolding is_okay_def overlapping_entries_def a_va_set_pde_def pde_entry_set_def
  apply clarsimp
  apply (drule_tac x="x" in spec)
  apply simp
  apply (drule_tac x="x" in spec)
  by force


theorem is_okay_not_incon:
  "is_okay t \<Longrightarrow>  \<forall>v a. lookup_pde t a v \<noteq> Incon_pde"
  apply safe
  unfolding lookup_pde_def
  apply (simp split: split_if_asm)
  unfolding is_okay_def overlapping_entries_def a_va_set_pde_def pde_entry_set_def
  apply clarsimp
  apply (drule_tac x="x" in spec)
  apply simp
  apply (drule_tac x="x" in spec)
  by force


theorem  entry_set_empty:
  "pde_entry_set t a v  = {} \<Longrightarrow> (a, v) \<notin> a_va_set_pde t"
  unfolding pde_entry_set_def a_va_set_pde_def
  by simp


theorem is_okay_intro1:
  "\<forall>x \<in> t. pde_entry_range_asid_tags x \<inter> a_va_set_pde (t - {x}) = {} \<Longrightarrow> is_okay t"
  unfolding is_okay_def overlapping_entries_def
  by simp

theorem  is_okay_intro2:
  " \<lbrakk>x \<in> t;  \<forall>(a,v)\<in> pde_entry_range_asid_tags x. \<forall>y\<in>t. y \<noteq> x \<longrightarrow> (a,v) \<notin> pde_entry_range_asid_tags y \<rbrakk> 
     \<Longrightarrow> pde_entry_range_asid_tags x \<inter> a_va_set_pde (t - {x}) = {}"
   unfolding a_va_set_pde_def
   by force

theorem bounded_forall_v_a:
  "\<forall>v a. lookup_pde t a v \<noteq> Incon_pde \<Longrightarrow> 
      \<forall>x\<in>t. \<forall>v a. (a, v) \<in> a_va_set_pde t \<longrightarrow> lookup_pde t a v \<noteq> Incon_pde"
  by clarsimp


theorem entry_range_single_element:
  "{E \<in> t. (a, v) \<in> pde_entry_range_asid_tags E} = {x} \<Longrightarrow> (a, v) \<in> pde_entry_range_asid_tags x
         \<and> (\<forall>y\<in>t. y\<noteq>x \<longrightarrow> (a, v) \<notin> pde_entry_range_asid_tags y)" 
   by force


theorem entry_range_memeber_va_set:
  "\<lbrakk>x \<in> t;  (a, b) \<in> pde_entry_range_asid_tags x\<rbrakk> \<Longrightarrow> (a, b) \<in> a_va_set_pde t"
   unfolding a_va_set_pde_def
   by force

theorem not_incon_is_okay:
  "\<forall>v a. lookup_pde t a v \<noteq> Incon_pde \<Longrightarrow> is_okay t"
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
  unfolding lookup_pde_def
  apply (simp split: split_if_asm)
  apply (drule entry_set_empty)
  apply (unfold a_va_set_pde_def) [1]
  apply simp
  apply (unfold a_va_set_pde_def) [1]
  apply (unfold pde_entry_set_def) [1]
  apply clarsimp
  apply (drule entry_range_single_element)
  apply (case_tac "x=xa")
  by simp+

theorem
  "is_okay t = (\<forall>v a. lookup_pde t a v \<noteq> Incon_pde)"
  apply (rule iffI)
  by (clarsimp simp:is_okay_not_incon not_incon_is_okay)+

(* ---------------------------------------------------------------------*)

theorem is_okay_not_hit_miss:
  "\<lbrakk>is_okay t ; (\<forall>x\<in>t. lookup_pde t a v \<noteq> Hit_pde x) \<rbrakk> \<Longrightarrow>
          lookup_pde t a v = Miss_pde "
  unfolding lookup_pde_def
  apply (simp split: split_if_asm)
  apply (unfold pde_entry_set_def) [1]
  apply force
  apply (drule(1) is_okay_not_empty_exist)
  by simp



theorem overlapping_entries_non_singleton:
  "\<lbrakk>pde_entry_range_asid_tags x \<inter> a_va_set_pde (t - {x}) \<noteq> {} \<rbrakk> \<Longrightarrow>
    \<exists>y\<in>t. \<exists>(a,v)\<in>pde_entry_range_asid_tags x. y\<noteq>x \<and> (a,v)\<in>pde_entry_range_asid_tags y"
  unfolding a_va_set_pde_def
  by force


theorem not_okay_lookup_incon:
  "\<not>is_okay t \<Longrightarrow>\<exists>(a,v)\<in>a_va_set_pde t. lookup_pde t a v = Incon_pde"
  unfolding is_okay_def overlapping_entries_def
  apply clarsimp
  apply (drule overlapping_entries_non_singleton)
  apply clarsimp
  unfolding Bex_def
  apply (rule_tac x="(a , b)" in exI)
  apply (clarsimp simp: entry_range_memeber_va_set)

  unfolding lookup_pde_def
  apply (simp split:split_if)
  apply (rule conjI)
  apply safe 
  unfolding pde_entry_set_def
  apply (drule entry_range_single_element)
  apply metis
  by simp

(* ---------------------------------------------------------------------*)


(*          ASID INVALIDATION CASE       *)

(* set of all the entries for a particular ASID *)
definition 
  asid_entry_set :: "pde_cache \<Rightarrow> asid \<Rightarrow> (pde_entry set)"
where
  "asid_entry_set t a \<equiv> {E\<in>t. pde_entry_asid E = a} "

definition 
  asid_set :: "pde_cache \<Rightarrow> asid set"
where
  "asid_set t \<equiv> pde_entry_asid ` t"

(* is ASID entries present in TLB *)

definition 
  is_asid_present :: "pde_cache \<Rightarrow> asid \<Rightarrow> bool" 
where
  "is_asid_present t a \<equiv>  a : asid_set t"



(* ASID Invalidation *)

definition 
  asid_invalidation :: "pde_cache \<Rightarrow> asid \<Rightarrow> pde_cache" 
where 
  "asid_invalidation t a \<equiv> t - asid_entry_set t a "


theorem is_present_asid_invalidation:
  "\<not>(is_asid_present (asid_invalidation t a) a)"
  unfolding is_asid_present_def asid_invalidation_def asid_entry_set_def asid_set_def
  by force

theorem lookup_asid_inv_miss:
  "\<lbrakk> a1 \<noteq> a2 ; lookup_pde t a2 v = Miss_pde \<rbrakk> \<Longrightarrow> 
         lookup_pde (asid_invalidation t a1) a2 v = Miss_pde"
  apply (clarsimp simp:lookup_miss_not_present)
  unfolding asid_invalidation_def is_a_va_present_pde_def
    asid_entry_set_def a_va_set_pde_def
   by simp


theorem lookup_hit_is_present:
  "lookup_pde t a v = Hit_pde x \<Longrightarrow> is_a_va_present_pde t a v"
  unfolding lookup_pde_def is_a_va_present_pde_def pde_entry_set_def a_va_set_pde_def
  by (force split: split_if_asm)

theorem entry_ranhe_asid_entry:
  "(a2, v) \<in> pde_entry_range_asid_tags x \<Longrightarrow> a2 = pde_entry_asid x"
  unfolding pde_entry_range_asid_tags_def
  by force

theorem lookup_asid_inv_hit:
  "\<lbrakk> a1 \<noteq> a2 ; lookup_pde t a2 v = Hit_pde x \<rbrakk> \<Longrightarrow> 
         lookup_pde (asid_invalidation t a1) a2 v = Hit_pde x"
  apply (frule lookup_hit_is_present)
  unfolding asid_invalidation_def lookup_pde_def
  apply (simp split: split_if_asm)
  apply safe
    unfolding pde_entry_set_def asid_entry_set_def a_va_set_pde_def
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
  "\<lbrakk> a1 \<noteq> a2 ; \<forall>x. pde_entry_set t a2 v \<noteq> {x}\<rbrakk> \<Longrightarrow> 
         \<forall>x. pde_entry_set (t- asid_entry_set t a1) a2 v \<noteq> {x}"
  unfolding pde_entry_set_def asid_entry_set_def pde_entry_range_asid_tags_def
  by auto 


theorem   entry_set_comp:
  "\<lbrakk>a1 \<noteq> a2 ; pde_entry_set t a2 v \<noteq> {} \<rbrakk> \<Longrightarrow> 
    pde_entry_set (t - asid_entry_set t a1) a2 v \<noteq> {}"
  unfolding pde_entry_set_def asid_entry_set_def pde_entry_range_asid_tags_def
  by auto 
    
theorem  lookup_asid_inv_incon:
  "\<lbrakk> a1 \<noteq> a2 ; lookup_pde t a2 v = Incon_pde \<rbrakk> \<Longrightarrow> 
         lookup_pde (asid_invalidation t a1) a2 v = Incon_pde"
  unfolding asid_invalidation_def lookup_pde_def
  apply (simp split: split_if_asm)
  apply safe
  apply (clarsimp simp:for_incon)
  apply (subgoal_tac "pde_entry_set t a2 v \<noteq> {}")
  apply (clarsimp simp:entry_set_comp)
  by auto


theorem  
  "\<lbrakk> a1 \<noteq> a2 ; lookup_pde t a2 v = S \<rbrakk> \<Longrightarrow> 
         lookup_pde (asid_invalidation t a1) a2 v = S"
  apply (case_tac "S")
  by (clarsimp simp: lookup_asid_inv_miss lookup_asid_inv_incon lookup_asid_inv_hit)+


(* Virtual Address Invalidation for all ASID *)

(* set of entries having v in their range *)
definition 
  va_pde_entry_set :: "pde_cache  \<Rightarrow> va \<Rightarrow> (pde_entry set)"
where
  "va_pde_entry_set t v \<equiv> {E\<in>t. v : pde_entry_range E} "


(* set of all the virtual addresses covered by TLB *)
definition 
  va_set_pde :: "pde_cache \<Rightarrow> (va set)"
where
  "va_set_pde t \<equiv> \<Union> (pde_entry_range ` t)"


(* is Virtual Address covered by TLB *)
definition 
  is_va_present_pde :: "pde_cache  \<Rightarrow> va \<Rightarrow> bool" 
where
  "is_va_present_pde t v \<equiv> v : va_set_pde t"


(*  -------- selective invalidation -------- *)

definition 
  va_sel_invalidation_pde :: "pde_cache \<Rightarrow> va \<Rightarrow> pde_cache" 
where 
  "va_sel_invalidation_pde t v \<equiv> t - va_pde_entry_set t v"



theorem is_presect_va_invlaidation:
  "\<not>is_va_present_pde (va_sel_invalidation_pde t v) v"
  unfolding is_va_present_pde_def va_sel_invalidation_pde_def
    va_pde_entry_set_def va_set_pde_def
    by simp

theorem  entry_set_va_set:
  "(pde_entry_set t a v = {}) = ((a, v) \<notin> a_va_set_pde t)"
  apply (unfold a_va_set_pde_def pde_entry_set_def)[1]
  by auto

theorem entry_set_empty_va_inv:
  "pde_entry_set (va_sel_invalidation_pde t v) a v = {}"
  apply (simp add: entry_set_va_set)
  apply safe
  apply (unfold va_sel_invalidation_pde_def a_va_set_pde_def)[1]
  apply clarsimp
  apply (subgoal_tac "x \<in> pde_entry_set t a v" )
  prefer 2
  apply (unfold pde_entry_set_def)[1]
  apply simp
  apply (subgoal_tac "x \<in> va_pde_entry_set t v" )
  apply simp
  apply (unfold pde_entry_set_def va_pde_entry_set_def pde_entry_range_asid_tags_def)[1]
  by auto



theorem lookup_va_invalid:
  "lookup_pde (va_sel_invalidation_pde t v) a v = Miss_pde"
  apply (unfold lookup_pde_def)
  apply (simp split: split_if)
  by (clarsimp simp: entry_set_empty_va_inv)


lemma entry_set_def2:
  "pde_entry_set t a v = {e\<in>t. v \<in> pde_entry_range e \<and> a = pde_entry_asid e}"
  by (auto simp: pde_entry_set_def pde_entry_range_asid_tags_def)


(*---------------------------------------------------*)

instantiation lookup_pde_type :: order
begin
  definition 
    less_eq_lookup_pde_type: "e \<le> e' \<equiv> e' = Incon_pde \<or> e' = e \<or> e = Miss_pde"

  definition 
    less_lookup_pde_type: "e < (e'::lookup_pde_type) \<equiv> e \<le> e' \<and> e \<noteq> e'"

  instance
     by intro_classes (auto simp add: less_lookup_pde_type less_eq_lookup_pde_type)
end


lemma Incon_top [iff]: "e \<le> Incon_pde"
  by (simp add: less_eq_lookup_pde_type)

lemma Incon_leq [simp]: "(Incon_pde \<le> e) = (e = Incon_pde)"
  by (auto simp add: less_eq_lookup_pde_type)

lemma Miss_bottom [iff]: "Miss_pde \<le> e"
  by (simp add: less_eq_lookup_pde_type)

lemma leq_Miss [simp]: "(e \<le> Miss_pde) = (e = Miss_pde)"
  by (auto simp add: less_eq_lookup_pde_type)

lemma Hits_le [simp]:
  "(Hit_pde h \<le> Hit_pde h') = (h = h')"
  by (auto simp add: less_eq_lookup_pde_type)

lemma tlb_mono_entry_set:
  "t \<subseteq> t' \<Longrightarrow> pde_entry_set t a v \<subseteq> pde_entry_set t' a v"
  by (simp add: pde_entry_set_def) blast

lemma tlb_mono:
  "t \<subseteq> t' \<Longrightarrow> lookup_pde t a v \<le> lookup_pde t' a v"
  by (drule tlb_mono_entry_set) (fastforce simp: lookup_pde_def)




thm pt_walk_def
(*definition 
  pt_walk :: "asid \<Rightarrow> heap \<Rightarrow> ttbr0 \<Rightarrow> vaddr \<Rightarrow> pde_entry"
where
  "pt_walk asid heap ttbr0 v \<equiv>
      case get_pde heap ttbr0 v
       of None                 \<Rightarrow> EntryPDE asid (ucast (addr_val v >> 20) :: 12 word) None 0
       | Some InvalidPDE       \<Rightarrow> EntryPDE asid (ucast (addr_val v >> 20) :: 12 word) None 0
       | Some ReservedPDE      \<Rightarrow> EntryPDE asid (ucast (addr_val v >> 20) :: 12 word) None 0
       | Some (SectionPDE p a) \<Rightarrow> 
          EntryPDE asid (ucast (addr_val v >> 20) :: 12 word) 
                            (Some (ucast (addr_val p >> 20) :: 12 word))  0
       | Some (PageTablePDE p) \<Rightarrow> 
               (case get_pte heap p v 
                 of None                     \<Rightarrow> EntrySmall asid (ucast (addr_val v >> 12) :: 20 word) None 0
                 |  Some InvalidPTE          \<Rightarrow> EntrySmall asid (ucast (addr_val v >> 12) :: 20 word) None 0
                 |  Some (SmallPagePTE p1 a) \<Rightarrow> EntrySmall asid (ucast (addr_val v >> 12) :: 20 word) 
                                            (Some (ucast (addr_val p1 >> 12) :: 20 word)) 0)"
*)

(* nice definition but it looses information about the entrysmall none case
    incomplete too (may be) *)
definition 
  pt_walk1 :: "asid \<Rightarrow> heap \<Rightarrow> ttbr0 \<Rightarrow> vaddr \<Rightarrow> pde_entry"
where
  "pt_walk1 asid heap ttbr0 v \<equiv>
      case lookup_pde heap ttbr0 v
       of None            \<Rightarrow> EntryPDE asid (ucast (addr_val v >> 20) :: 12 word) None 0
       | Some (p, pt, a)  \<Rightarrow> if pt = ArmSection 
                              then EntryPDE asid (ucast (addr_val v >> 20) :: 12 word) (Some (ucast (addr_val p >> 20) :: 12 word))  0 
                                else EntrySmall asid (ucast (addr_val v >> 12) :: 20 word) (Some (ucast (addr_val p >> 12) :: 20 word)) 0"
         

(*definition 
  pt_lookup :: "8 word \<Rightarrow> mem_type \<Rightarrow> ttbr0 \<Rightarrow> va \<Rightarrow> 32 word option"
where
  "pt_lookup asid mem ttbr0 v \<equiv>
    let entry = pt_walk asid mem ttbr0 v
      in if is_fault' entry then None else Some (va_to_pa v entry)"
*)

*)

end













