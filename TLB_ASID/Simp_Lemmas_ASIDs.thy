theory Simp_Lemmas_ASIDs
  imports  TLB_ASIDs
           TLBJ.Simp_Lemmas
          
begin


(* lookup'' Lemmas *)


abbreviation "lookup'' t a \<equiv> lookup (tagged_entry_set t a)" 


lemma asid_tlb_mono_entry_set:
  "t \<subseteq> t' \<Longrightarrow> tagged_entry_set t a v \<subseteq> tagged_entry_set t' a v"
  apply (clarsimp simp: tagged_entry_set_def entry_set_def)
  by (meson subset_eq tlb_mono_entry_set) 


lemma asid_tlb_mono:
  "t \<subseteq> t' \<Longrightarrow> lookup'' t a v \<le> lookup'' t' a v"
  by (drule asid_tlb_mono_entry_set) (fastforce simp: lookup_def)


lemma lookup_in_asid_tlb:
  "lookup'' t a v = Hit e \<Longrightarrow> e \<in> t"
  by (auto simp: lookup_def tagged_entry_set_def entry_set_def   split: if_split_asm)

lemma lookup_asid_tlb_incon_subset [simp]:
  "\<lbrakk> s \<subseteq> t ; lookup'' s a v = Incon \<rbrakk> \<Longrightarrow>  lookup'' t a v = Incon"
  by (metis less_eq_lookup_type lookup_type.simps(3) asid_tlb_mono)


lemma tagged_entry_set_insert:
  "\<lbrakk> tagged_entry_set t a v = {}; asid_of e = Some a \<or> asid_of e = None; v \<in> range_of e \<rbrakk> \<Longrightarrow> 
               tagged_entry_set (insert e t) a v = {e}"
  apply (clarsimp simp: tagged_entry_set_def  entry_set_def )
  by force    



lemma lookup_asid_tlb_miss_union:
  " lookup'' (t \<union> t') a v = Miss  \<Longrightarrow>
      (lookup'' t a v = Miss \<and> lookup'' t' a v = Miss)"
  apply rule
   apply (clarsimp simp: lookup_def tagged_entry_set_def entry_set_def   split: if_split_asm)
   apply safe
      apply blast+
  apply (clarsimp simp: lookup_def tagged_entry_set_def entry_set_def   split: if_split_asm)
  apply safe
  by blast+


lemma lookup_asid_tlb_hit_miss_or_hit' :
  " lookup'' (t \<union> t') a v = Hit e  \<Longrightarrow> 
              lookup'' t' a v = Miss \<or> (lookup'' t' a v = Hit e)"
  by (metis Un_upper2 asid_tlb_mono less_eq_lookup_type lookup_type.simps(7))
 
lemma  lookup_asid_tlb_hit_entry_range:
  "lookup'' t a v = Hit e \<Longrightarrow> v \<in> range_of e"
  apply (clarsimp simp: lookup_def  tagged_entry_set_def entry_set_def  split:if_split_asm)
  by force

lemma lookup_asid_tlb_union_hit_miss_hit :
  "\<lbrakk>lookup'' (t \<union> t') a v = Hit e ; lookup'' t' a v \<noteq> Miss \<rbrakk> \<Longrightarrow> lookup'' t' a v = Hit e"
  using lookup_asid_tlb_hit_miss_or_hit' by blast
 
lemma  lookup_asid_tlb_not_hit_miss:
  "\<lbrakk>lookup'' (t \<union> t') a v = Hit e;   lookup'' t a v \<noteq> Hit e\<rbrakk> \<Longrightarrow> lookup'' t a v = Miss"
  by (metis lookup_asid_tlb_union_hit_miss_hit sup_commute)
  

lemma lookup_asid_tlb_union_hit_miss_hit' :
  "\<lbrakk>lookup'' (t \<union> t') a v = Hit e; lookup'' t a v \<noteq> Miss \<rbrakk> \<Longrightarrow> lookup'' t a v = Hit e"
  using lookup_asid_tlb_not_hit_miss by blast
  
lemma  lookup_asid_tlb_not_hit_false:
  "\<lbrakk>lookup'' (t \<union> t') a v = Hit e; lookup'' t a v \<noteq> Hit e; lookup'' t' a v \<noteq> Hit e\<rbrakk> \<Longrightarrow> False"
  apply (cases "lookup'' t a v"; clarsimp)
    defer
    apply (metis Un_upper1 lookup_asid_tlb_incon_subset lookup_type.simps(7))
   apply (metis Hits_le asid_tlb_mono inf_sup_ord(3))
  apply (simp only: lookup_def  tagged_entry_set_def entry_set_def   split:if_split_asm cong: Collect_cong)
     by blast+ 

  

lemma lookup_asid_tlb_not_hit_hit:
  "\<lbrakk>lookup'' (t \<union> t') a v = Hit e; lookup'' t a v \<noteq> Hit e\<rbrakk> \<Longrightarrow> lookup'' t' a v = Hit e"
  using lookup_asid_tlb_not_hit_false by blast


lemma lookup_asid_tlb_hit_union_cases':
  " lookup'' (t \<union> t') a v = Hit e  \<Longrightarrow>
      (lookup'' t a v  = Hit e \<and> lookup'' t' a v = Miss)  \<or>
      (lookup'' t' a v = Hit e \<and> lookup'' t a v  = Miss)  \<or>
      (lookup'' t a v  = Hit e \<and> lookup'' t' a v = Hit e)"
  apply (safe , clarsimp)
         apply (drule lookup_asid_tlb_not_hit_hit; clarsimp)
        apply (drule lookup_asid_tlb_not_hit_miss; clarsimp)
       apply (drule lookup_asid_tlb_not_hit_false ; clarsimp) 
      apply (drule lookup_asid_tlb_not_hit_false ; clarsimp)
     apply (drule lookup_asid_tlb_union_hit_miss_hit ; clarsimp)
    apply (drule lookup_asid_tlb_not_hit_miss ; clarsimp)
   apply (drule lookup_asid_tlb_union_hit_miss_hit ; clarsimp)
  by (drule lookup_asid_tlb_hit_miss_or_hit' ; clarsimp)

lemma lookup_asid_tlb_miss_implies_union_miss:
  "\<lbrakk>lookup'' t a v = Miss ; lookup'' t' a v = Miss \<rbrakk> \<Longrightarrow> lookup'' (t \<union> t') a v = Miss "
  apply (clarsimp simp: lookup_def tagged_entry_set_def entry_set_def   split: if_split_asm)
  apply safe
  by blast+

lemma lookup_asid_tlb_miss_hit_implies_union_hit:
  "\<lbrakk>lookup'' t a v = Miss; lookup'' t' a v = Hit e\<rbrakk> \<Longrightarrow> lookup'' (t \<union> t') a v = Hit e"
  apply (case_tac "lookup'' (t \<union> t') a v = Hit e"; clarsimp)
  apply (clarsimp simp: lookup_def tagged_entry_set_def entry_set_def   split: if_split_asm)
  by (safe; force)+
 
 

lemma  union_asid_tlb_incon_cases:
  "lookup'' (t \<union> t') a v = Incon \<Longrightarrow> 
      (lookup'' t a v = Incon \<and> lookup'' t' a v = Incon)  \<or>
      ((\<exists>x\<in>t. lookup'' t a v = Hit x)  \<and> (\<exists>x\<in>t'. lookup'' t' a v = Hit x) \<and>  lookup'' t a v \<noteq>  lookup'' t' a v)  \<or>
      (lookup'' t' a v = Incon \<and> (\<exists>x\<in>t. lookup'' t a v = Hit x) ) \<or>
      ((\<exists>x\<in>t'. lookup'' t' a v = Hit x)  \<and> lookup'' t a v = Incon)\<or>
      (lookup'' t a v = Miss \<and> lookup'' t' a v = Incon)  \<or>
      (lookup'' t a v = Incon \<and> lookup'' t' a v = Miss)"
  apply (cases "lookup'' t a v"; cases "lookup'' t' a v"; clarsimp)
       apply (drule_tac t' = t' in lookup_asid_tlb_miss_implies_union_miss; simp)
      apply (drule_tac t' = t' in lookup_asid_tlb_miss_hit_implies_union_hit; simp)
  using lookup_in_asid_tlb apply blast
    apply (drule_tac t' = t and e = x3 in lookup_asid_tlb_miss_hit_implies_union_hit, simp)
    apply (simp add: sup_commute)
  using lookup_in_asid_tlb apply blast
  apply (rule)
  using lookup_in_asid_tlb apply blast
  apply (rule)
  using lookup_in_asid_tlb apply blast
  apply (clarsimp simp: lookup_def tagged_entry_set_def entry_set_def split:if_split_asm)
  by (safe; force)


lemma tagged_entry_set_hit_entry_range:
  "tagged_entry_set t a v = {e} \<Longrightarrow> (Some a, v) \<in> asid_range_of e \<or> (None, v) \<in> asid_range_of e"
  apply (clarsimp simp: tagged_entry_set_def entry_set_def asid_range_of_def   split:if_split_asm)
 by force  




theorem asid_entry_range_single_elementI:
  "\<lbrakk>x\<in> t ; (Some a, v) \<in> asid_range_of x ; (\<forall>y\<in>t. y\<noteq>x \<longrightarrow> (Some a, v) \<notin> asid_range_of y) \<rbrakk> \<Longrightarrow> 
         {E \<in> t. (Some a, v) \<in> asid_range_of E} = {x}" 
   by force


lemma lookup_asid_tlb_hit_mis_hit:
  "\<lbrakk>lookup'' (t \<union> t') a v = Hit e ; lookup'' t' a v = Miss \<rbrakk> \<Longrightarrow> lookup'' t a v = Hit e"
  using lookup_asid_tlb_hit_union_cases' by force
 

lemma   lookup_asid_tlb_union_hit_hit_miss :
  "\<lbrakk>lookup'' (t \<union> t') a v = Hit e ;  \<forall>x\<in>t. lookup'' t a v \<noteq> Hit x\<rbrakk> \<Longrightarrow> lookup'' t a v = Miss"
  using lookup_asid_tlb_not_hit_miss lookup_in_asid_tlb by blast

lemma lookup_asid_tlb_hit_miss_or_hit :
  " lookup'' (t \<union> t') a v = Hit e \<and> e \<in> t  \<Longrightarrow> 
              lookup'' t' a v = Miss \<or> (lookup'' t' a v = Hit e)"
  using lookup_asid_tlb_union_hit_miss_hit by blast

lemma not_miss_incon_hit_asid_tlb:
  "lookup'' t a v \<noteq> Miss \<Longrightarrow> lookup'' t a v = Incon \<or> (\<exists>x\<in>t. lookup'' t a v = Hit x)"
  by (meson lookup_in_asid_tlb lookup_type.exhaust)
  


lemma  lookup_asid_tlb_hit_union_cases:
  "(\<exists>x\<in>(t \<union> t'). lookup'' (t \<union> t') a va = Hit x)  \<Longrightarrow>
      ((\<exists>x\<in>t. lookup'' t a va = Hit x) \<and> lookup'' t' a va = Miss)       \<or>
      ((\<exists>x\<in>t'. lookup'' t' a va = Hit x)  \<and> lookup'' t a va = Miss)      \<or>
      ((\<exists>x\<in>t. \<exists>x'\<in>t'.  lookup'' t a va = Hit x  \<and> lookup'' t' a va = Hit x' \<and>  x = x')) "
  by (metis lookup_asid_tlb_hit_union_cases' lookup_asid_tlb_not_hit_hit lookup_asid_tlb_union_hit_hit_miss lookup_in_asid_tlb lookup_type.distinct(3))


lemma lookup_asid_tlb_miss_union_equal:
  "lookup'' t' a v = Miss \<Longrightarrow> lookup'' (t \<union> t') a v = lookup'' t a v"
  apply (cases "lookup'' (t \<union> t') a v"; clarsimp)
    apply (drule lookup_asid_tlb_miss_union, simp)
   apply (drule union_asid_tlb_incon_cases, clarsimp)
  by (drule lookup_asid_tlb_hit_union_cases', clarsimp)

 

lemma lookup_asid_tlb_miss_union_miss_miss:
  "\<lbrakk>lookup'' t a v = Miss;  lookup'' t' a v = Miss\<rbrakk> \<Longrightarrow> 
           lookup'' (t \<union> t') a v = Miss"
  by (simp add: lookup_asid_tlb_miss_union_equal)


lemma  lookup_asid_tlb_incon_not_miss:
   "\<lbrakk> lookup'' (t \<union> t') a v = Incon ; lookup'' t' a v = Miss\<rbrakk> \<Longrightarrow> lookup'' t a v = Incon"
  by (simp add: lookup_asid_tlb_miss_union_equal)
  

lemma lookup_asid_tlb_hit_diff_union_incon:
  "\<lbrakk>lookup'' t a v = Hit e ; lookup'' t' a v = Hit e' ; e \<noteq> e'\<rbrakk> \<Longrightarrow> lookup'' (t \<union> t') a v = Incon"
  apply (clarsimp simp: lookup_def tagged_entry_set_def entry_set_def asid_range_of_def  split: if_split_asm)
 by (metis (no_types, lifting) mem_Collect_eq singletonD singletonI)
 

lemma lookup_asid_tlb_miss_union_hit_intro:
  "\<lbrakk>lookup'' t a v = Miss;  lookup'' t' a v = Hit e\<rbrakk> \<Longrightarrow> 
           lookup'' (t \<union> t') a v = Hit e"
  by (metis lookup_asid_tlb_miss_union_equal sup.commute)

lemma lookup_asid_tlb_miss_union_hit_intro':
  "\<lbrakk> lookup'' t a v = Hit e ; lookup'' t' a v = Miss\<rbrakk> \<Longrightarrow> 
           lookup'' (t \<union> t') a v = Hit e"
  by (metis inf_sup_aci(5) lookup_asid_tlb_miss_union_hit_intro)
 

lemma lookup_asid_tlb_union_hit_hit:
  "\<lbrakk> lookup'' t a v = Hit e ; lookup'' t' a v = Hit e\<rbrakk> \<Longrightarrow> 
           lookup'' (t \<union> t') a v = Hit e"
  apply (cases "lookup'' (t \<union> t') a v"; clarsimp)
  apply (drule lookup_asid_tlb_miss_union, simp)
   apply (drule union_asid_tlb_incon_cases, clarsimp)
  by (drule lookup_asid_tlb_hit_union_cases', clarsimp)
  



lemma asid_tlb_not_miss_incon_hit':
  "lookup'' t a v = Incon \<or> (\<exists>e\<in>t. lookup'' t a v = Hit e) \<Longrightarrow> lookup'' t a v \<noteq> Miss "
  by (clarsimp simp: lookup_def tagged_entry_set_def entry_set_def split: if_split_asm)


lemma lookup_asid_tlb_incon_minus:
  "lookup'' (t - t') a v  = Incon  \<Longrightarrow> lookup'' t a v = Incon"
  apply (subgoal_tac "t - t' \<subseteq> t")
   apply (frule_tac a = a and v = v in asid_tlb_mono)
   apply clarsimp
  by blast


lemma  lookup_asid_tlb_hit_entry_range_asid_tags:
  "lookup'' t a v = Hit e \<Longrightarrow> (Some a, v) \<in> asid_range_of e \<or> (None, v) \<in> asid_range_of e"
  apply (clarsimp simp: lookup_def  tagged_entry_set_def entry_set_def    asid_range_of_def  split:if_split_asm)
  by force



lemma  lookup_asid_tlb_hit_asid:
  "lookup'' t a v = Hit e \<Longrightarrow> Some a = asid_of e \<or> None =  asid_of e"
  apply (clarsimp simp: lookup_def  tagged_entry_set_def entry_set_def asid_range_of_def  split:if_split_asm)
  by force


lemma  lookup_asid_tlb_hit_incon_minus:
  "\<lbrakk>lookup'' (t - t') a v = Hit e\<rbrakk>
                \<Longrightarrow> lookup'' t a v = Hit e \<or> lookup'' t a v = Incon"
  apply (clarsimp simp: lookup_def  tagged_entry_set_def entry_set_def asid_range_of_def  split:if_split_asm)
  by force


lemma  lookup_asid_tlb_not_miss_varange:
  "lookup'' (t - (\<Union>v\<in>vset. {e \<in> t. v \<in> range_of e})) a v \<noteq> Miss \<Longrightarrow>
      v \<notin> vset"
  by (clarsimp simp: lookup_def tagged_entry_set_def entry_set_def asid_range_of_def split:if_split_asm)


lemma  lookup_asid_tlb_minus_union:
  "\<lbrakk>lookup'' t' a v = Miss; lookup''  t'' a v = Miss \<rbrakk> \<Longrightarrow>
      lookup'' (t - t' \<union> t'') a v = lookup'' t a v"
  by (metis Un_Diff_cancel2 lookup_asid_tlb_miss_union_equal sup_commute)
 


lemma  lookup_asid_tlb_minus_same:
  "\<lbrakk>lookup'' t' a v = Miss \<rbrakk> \<Longrightarrow> lookup'' (t - t') a v = lookup'' t a v"
  by (metis Un_Diff_cancel2 lookup_asid_tlb_miss_union_equal)

lemma  lookup_asid_tlb_minus_hit':
  "\<lbrakk>lookup'' (t - t') a v = Hit e ; lookup'' t' a v = Miss \<rbrakk> \<Longrightarrow> lookup'' t a v = Hit e"
  by (metis Un_Diff_cancel2 lookup_asid_tlb_hit_mis_hit lookup_asid_tlb_miss_union_hit_intro')


lemma  lookup_minus_union':
  "\<lbrakk>lookup'' t' a v = Miss \<rbrakk> \<Longrightarrow>
      lookup'' (t - t' \<union> t'') a v = lookup'' (t \<union> t'') a v"
proof -
  assume "lookup'' t' a v = Miss"
  then have "\<forall>T Ta. lookup'' (Ta \<union> T) a v = lookup'' (Ta \<union> (T \<union> t')) a v"
    by (metis Un_assoc lookup_asid_tlb_miss_union_equal)
  then show ?thesis
    by (metis (no_types) Un_Diff_cancel2 Un_commute)
qed
  


lemma lookup_asid_tlb_asid_entry_miss:
  "a \<noteq> a' \<Longrightarrow> lookup'' {e \<in> t. asid_of e = Some a} a' v = Miss"
  by (clarsimp simp: lookup_def tagged_entry_set_def entry_set_def asid_range_of_def split: if_split_asm)
 

lemma lookup_minus_smaller_order:
  "lookup'' (t - t') a v \<le> lk \<Longrightarrow> lookup'' (t - t'' - t') a v \<le> lk"
  apply (cases lk; clarsimp)
  apply (metis Diff_mono asid_tlb_mono inf_sup_ord(3) leq_Miss set_double_minus subset_refl)
  by (metis (no_types, hide_lams) Diff_mono asid_tlb_mono order.trans set_double_minus subset_refl sup_ge1)


lemma lookup_union_minus_equal':
  "lookup'' b a v = Miss \<Longrightarrow>
     lookup'' (a' \<union> b \<union> c - d) a v = lookup'' (a' \<union> c - d) a v"
  apply (case_tac "lookup'' (a' \<union> b \<union> c - d) a v"; clarsimp)
  subgoal
  proof -
    assume "lookup'' (a' \<union> b \<union> c - d) a v = Miss"
    then have "\<exists>T. lookup'' (a' \<union> (c \<union> T) - d) a v = Miss"
      by (metis (no_types) Un_left_commute sup_commute)
    then show "Miss = lookup'' (a' \<union> c - d) a v"
      by (metis (no_types) Un_Diff lookup_asid_tlb_miss_union sup_assoc)
  qed
  subgoal
  proof -
    assume a1: "lookup'' b a v = Miss"
    assume a2: "lookup'' (a' \<union> b \<union> c - d) a v = Incon"
    have f3: "\<forall>T Ta Tb. (T::tlb_entry set) \<union> Ta - Tb = T \<union> (Ta - Tb) - Tb"
      by (simp add: Un_Diff)
    have "lookup'' (b \<union> (a' \<union> c) - d) a v = Incon"
      using a2 by (metis (no_types) Un_commute sup_assoc)
    then show "Incon = lookup'' (a' \<union> c - d) a v"
      using f3 a1 by (metis (full_types) Un_commute lookup_asid_tlb_incon_minus lookup_asid_tlb_incon_not_miss)
  qed
  apply (case_tac " lookup'' d a v")
  subgoal
  proof -
    fix x3 :: "tlb_entry"
    assume a1: "lookup'' b a v = Miss"
    assume a2: "lookup'' (a' \<union> b \<union> c - d) a v = Hit x3"
    assume a3: "lookup'' d a v = Miss"
    have "lookup'' (a' \<union> (c \<union> b) - d) a v = Hit x3"
      using a2 by (simp add: inf_sup_aci(5) sup.left_commute)
    then have "lookup'' (a' \<union> (b \<union> c) - d \<union> d) a v = Hit x3"
      using a3 by (metis inf_sup_aci(5) lookup_asid_tlb_miss_union_hit_intro')
    then have "lookup'' (b \<union> (a' \<union> (c \<union> d))) a v = Hit x3"
      by (simp add: inf_sup_aci(5) sup.left_commute)
    then have "lookup'' (a' \<union> (c \<union> d)) a v = Hit x3"
      using a1 by (metis (no_types) inf_sup_aci(5) lookup_asid_tlb_hit_mis_hit)
    then have "lookup'' (d \<union> (a' \<union> c)) a v = Hit x3"
      by (simp add: inf_sup_aci(5) sup.left_commute)
    then show "Hit x3 = lookup'' (a' \<union> c - d) a v"
      using a3 by (metis (no_types) Un_Diff_cancel inf_sup_aci(5) lookup_asid_tlb_hit_mis_hit)
  qed
   apply (case_tac "lookup'' (a' \<union> c - d) a v"; clarsimp)
     apply (case_tac "lookup'' (a' \<union> c) a v")
  subgoal
  proof -
    fix x3 :: "tlb_entry"
    assume a1: "lookup'' b a v = Miss"
    assume a2: "lookup'' (a' \<union> b \<union> c - d) a v = Hit x3"
    assume a3: "lookup'' (a' \<union> c) a v = Miss"
    have f4: "lookup'' (a' \<union> (c \<union> b) - d) a v = Hit x3"
      using a2 by (simp add: sup_commute sup_left_commute)
    have "lookup'' (b \<union> (a' \<union> c)) a v = Miss"
      using a3 a1 by (meson lookup_asid_tlb_miss_union_miss_miss)
    then have "lookup'' (a' \<union> (b \<union> c)) a v = Miss"
      by (simp add: sup_left_commute)
    then show False
      using f4 by (metis lookup_asid_tlb_hit_incon_minus lookup_type.distinct(1) lookup_type.simps(5) sup_commute)
  qed
      apply (clarsimp simp: lookup_def tagged_entry_set_def entry_set_def split:if_split_asm)
      apply (safe ; force) [1]                                    
     apply (clarsimp simp: lookup_def tagged_entry_set_def entry_set_def split:if_split_asm)
     apply (safe ; force) [1]
  subgoal
  proof -
    fix x3 :: "tlb_entry"
    assume a1: "lookup'' (a' \<union> c - d) a v = Incon"
    assume "lookup'' (a' \<union> b \<union> c - d) a v = Hit x3"
    then have "lookup'' (b \<union> (a' \<union> c) - d) a v = Hit x3"
      by (simp add: sup_commute sup_left_commute)
    then show False
      using a1 by (metis (no_types) Un_Diff lookup_asid_tlb_incon_subset lookup_type.distinct(5) sup_commute sup_ge1)
  qed
  subgoal
  proof -
    fix x3 :: "tlb_entry" and x3a :: "tlb_entry"
    assume a1: "lookup'' (a' \<union> c - d) a v = Hit x3a"
    assume "lookup'' (a' \<union> b \<union> c - d) a v = Hit x3"
    then have "Hit x3a \<le> Hit x3"
      using a1 by (metis (no_types) Un_Diff Un_upper2 asid_tlb_mono sup_commute sup_left_commute)
    then show "x3 = x3a"
      by (meson less_eq_lookup_type lookup_type.inject lookup_type.simps(5) lookup_type.simps(7))
  qed
  apply (case_tac "lookup'' (a' \<union> c) a v")
    apply (cases "lookup'' (a' \<union> c - d) a v"; clarsimp)
      apply (clarsimp simp: lookup_def tagged_entry_set_def entry_set_def split:if_split_asm)
      apply (safe ; force) [1]         
     apply (clarsimp simp: lookup_def tagged_entry_set_def entry_set_def split:if_split_asm)
     apply (safe ; force) [1]         
    apply (clarsimp simp: lookup_def tagged_entry_set_def entry_set_def split:if_split_asm)
    apply (safe ; force) [1]     
   apply (cases "lookup'' (a' \<union> c - d) a v"; clarsimp)
     apply (clarsimp simp: lookup_def tagged_entry_set_def entry_set_def split:if_split_asm)
     apply (safe ; force) [1]
    apply (metis (no_types) Un_Diff lookup_asid_tlb_incon_subset lookup_type.distinct(5) sup_assoc sup_commute sup_ge1)
  subgoal
  proof -
    fix x3 :: "tlb_entry" and x3a :: "tlb_entry" and x3b :: "tlb_entry"
    assume a1: "lookup'' (a' \<union> c - d) a v = Hit x3b"
    assume a2: "lookup'' (a' \<union> b \<union> c - d) a v = Hit x3"
    have "\<forall>T Ta. (Ta::tlb_entry set) \<union> (T \<union> Ta) = T \<union> Ta"
      by blast
    then show "x3 = x3b"
      using a2 a1 by (metis (no_types) Un_Diff lookup_asid_tlb_hit_diff_union_incon lookup_type.distinct(5) sup_assoc)
  qed
proof -
  fix x3 :: "tlb_entry" and x3a :: "tlb_entry" and x3b :: "tlb_entry"
  assume a1: "lookup'' (a' \<union> b \<union> c - d) a v = Hit x3"
  assume a2: "lookup'' b a v = Miss"
  have f3: "lookup'' (b - d \<union> (a' - d \<union> (c - d))) a v = Hit x3"
    using a1 by (simp add: Un_Diff sup_commute sup_left_commute)
  then have "lookup'' (b - d) a v = Miss"
    using a2 by (metis (no_types) lookup_asid_tlb_hit_incon_minus lookup_asid_tlb_hit_union_cases' lookup_type.simps(3))
  then have "lookup'' (a' - d \<union> (c - d)) a v = Hit x3"
    using f3 by (metis lookup_asid_tlb_miss_union_equal sup_commute)
  then show "Hit x3 = lookup'' (a' \<union> c - d) a v"
    by (simp add: Un_Diff)
qed


(* lookup_union_minus_equal' is being used with these variables later *)
lemma lookup_union_minus_equal:
  " lookup'' t' a v = Miss \<Longrightarrow>
     lookup'' (t \<union> t' \<union> t''' - t'') a v = lookup'' (t \<union> t''' - t'') a v"
  by (clarsimp simp: lookup_union_minus_equal')



theorem asid_entry_range_single_element_n:
  " {E \<in> the ` {e \<in> t. \<not> is_fault e}. v \<in> range_of E \<and> (asid_of E = None \<or> asid_of E = Some a)} = {x} \<Longrightarrow> 
       v \<in> range_of x \<and> (asid_of x = None \<or> asid_of x = Some a) \<and> \<not> is_fault (Some x) 
         \<and> (\<forall>y\<in>the ` {e \<in> t. \<not> is_fault e}. y\<noteq>x \<and> 
               \<not> is_fault (Some y) \<longrightarrow> ((Some a, v) \<notin> asid_range_of y \<and> (None, v) \<notin> asid_range_of y))" 
  apply safe
     apply force
    apply (clarsimp simp: is_fault_def)
    apply force
   apply (simp add: is_fault_def)
  apply (clarsimp simp: asid_range_of_def)
   apply force
 apply (clarsimp simp: asid_range_of_def)
  by force



theorem asid_entry_range_single_elementI':
  "\<lbrakk>x\<in> t ; (Some a, v) \<in> asid_range_of x \<or> (None, v) \<in> asid_range_of x ; (\<forall>y\<in>t. y\<noteq>x \<longrightarrow> (Some a, v) \<notin> asid_range_of y \<and> (None, v) \<notin> asid_range_of y) \<rbrakk> \<Longrightarrow> 
         {E \<in> t.  v \<in> range_of E \<and> (asid_of E = None \<or> asid_of E = Some a)} = {x}" 
   apply (clarsimp simp: asid_range_of_def) by force


theorem asid_entry_range_single_element':
  " {E \<in> the ` {e \<in> t. \<not> is_fault e}. (a, v) \<in> asid_range_of E} = {x} \<Longrightarrow> 
       (a, v) \<in> asid_range_of x \<and> \<not> is_fault (Some x) 
         \<and> (\<forall>y\<in>the ` {e \<in> t. \<not> is_fault e}. y\<noteq>x \<and> 
               \<not> is_fault (Some y) \<longrightarrow> (a, v) \<notin> asid_range_of y)" 
  apply safe
    apply force
   apply (clarsimp simp: is_fault_def)
  by force


lemma asid_entry_range_asid_entry:
  "(Some a, v) \<in> asid_range_of e \<Longrightarrow> asid_of e = Some a"
  by (clarsimp simp: asid_range_of_def)



theorem  entry_set_va_set:
  "(tagged_entry_set t a v = {}) = ((Some a, v) \<notin> asid_vadr_tlb t \<and> (None, v) \<notin> asid_vadr_tlb t)"
  apply (clarsimp simp: asid_vadr_tlb_def tagged_entry_set_def asid_range_of_def entry_set_def)
  apply safe
  by force+



lemma lookup_asid_tlb_hit_mis_hit':
  "\<lbrakk>lookup'' (t \<union> t') a v = Hit e ; lookup'' t a v = Miss \<rbrakk> \<Longrightarrow> lookup'' t' a v = Hit e"
  using lookup_asid_tlb_hit_union_cases' by force




(* global and non_global entries *)


lemma tlb_global_non_global_union:
  "t = non_global_entries t \<union> global_entries t"
  apply (clarsimp simp:  non_global_entries_def global_entries_def)
  using UnI1 by auto


lemma glb_tlb_subset:
  "global_entries t \<subseteq> t"
  by (clarsimp simp: global_entries_def)  

lemma non_glb_tlb_subset:
  "non_global_entries t \<subseteq> t"
  by (clarsimp simp: non_global_entries_def)


lemma global_entries_union:
  "global_entries (tlb \<union> tlb') = global_entries tlb \<union> global_entries tlb'"
  apply (clarsimp simp: global_entries_def)
  by blast


lemma non_global_to_global:
  "non_global_entries t = t - global_entries t"
  apply (clarsimp simp: non_global_entries_def global_entries_def)
  apply safe
  by simp

lemma lookup_global_incon_for_asids:
  "lookup'' (global_entries t) a v = Incon \<Longrightarrow> lookup'' (global_entries t) a' v = Incon"
  apply (case_tac "a = a'"; clarsimp?)
  apply (case_tac "lookup'' (global_entries t) a' v"; clarsimp?)
   apply (clarsimp simp: global_entries_def lookup_def tagged_entry_set_def entry_set_def split: if_split_asm)
   apply force
 apply (clarsimp simp: global_entries_def lookup_def tagged_entry_set_def entry_set_def split: if_split_asm)
  by force


lemma lookup_global_same_for_asids:
  "lookup'' (global_entries t) a v = lookup'' (global_entries t) a' v"
  apply (case_tac "a = a'"; clarsimp?)
  apply (case_tac "lookup'' (global_entries t) a' v"; clarsimp?)
   apply (clarsimp simp: global_entries_def lookup_def tagged_entry_set_def entry_set_def split: if_split_asm)
   apply force
 apply (clarsimp simp: global_entries_def lookup_def tagged_entry_set_def entry_set_def split: if_split_asm)
   apply (safe; force) [1]
 apply (clarsimp simp: global_entries_def lookup_def tagged_entry_set_def entry_set_def split: if_split_asm)
  by (safe; force) [1]


lemma lookup_global_incon_tlb_incon:
  " lookup'' (global_entries t) a v = Incon \<Longrightarrow> lookup'' t a v = Incon"
  using glb_tlb_subset lookup_asid_tlb_incon_subset by blast


lemma lookup_global_incon_incon:
  "lookup'' (global_entries t) a v = Incon \<Longrightarrow>  lookup'' t a' v = Incon"
  apply (case_tac "a = a'"; (clarsimp simp: lookup_global_incon_tlb_incon)?)
  apply (subgoal_tac "lookup'' (global_entries t) a' v = Incon")
   prefer 2
   apply (clarsimp simp: lookup_global_incon_for_asids)
  by (clarsimp simp: lookup_global_incon_tlb_incon)
  



lemma  lookup_incon_global_vset_elem:
   "\<lbrakk> {v. lookup'' t a v = Incon} \<subseteq> vset;
               lookup'' (global_entries t) a' v = Incon  \<rbrakk> \<Longrightarrow>  v \<in> vset"
  apply (subgoal_tac " lookup'' t a v = Incon ")
   apply blast
  using lookup_global_incon_incon by blast


lemma lookup_global_hit_asid_of_none:
  "lookup'' (global_entries t) a v = Hit e \<Longrightarrow> asid_of e = None"
  apply (clarsimp simp: global_entries_def lookup_def tagged_entry_set_def entry_set_def split: if_split_asm)
  by force



lemma lookup_tlb_eq_union_global_non_global:
  "lookup'' t a v = lookup'' (global_entries t \<union> non_global_entries t) a v"
  apply (case_tac "lookup'' (global_entries t \<union> non_global_entries t) a v"; clarsimp)
    apply (clarsimp simp: global_entries_def non_global_entries_def lookup_def tagged_entry_set_def entry_set_def split: if_split_asm)
    apply  (safe; force) [1]
   apply (clarsimp simp: global_entries_def non_global_entries_def lookup_def tagged_entry_set_def entry_set_def split: if_split_asm)
   apply  (safe; force) [1]
  apply (clarsimp simp: global_entries_def non_global_entries_def lookup_def tagged_entry_set_def entry_set_def split: if_split_asm)
  by  (safe; force) [1]      

lemma lookup_global_hit_lookup':
  "lookup'' (global_entries t) a v = Hit e
       \<Longrightarrow> lookup' (global_entries t) v = Hit e"
  apply (clarsimp simp: global_entries_def lookup_def tagged_entry_set_def entry_set_def split: if_split_asm)
  apply safe
  by force+

lemma lookup''_global_incon_lookup':
  "lookup'' (global_entries t) a v = Incon
       \<Longrightarrow> lookup' (global_entries t) v = Incon"
  apply (clarsimp simp: global_entries_def lookup_def tagged_entry_set_def entry_set_def split: if_split_asm)
  apply safe
  by force+

lemma interesting_lemma:
  "\<lbrakk>lookup'' (non_global_entries t) a v = Hit x; lookup' (global_entries t')  v = Hit x' \<rbrakk> \<Longrightarrow>
    x' \<noteq> x"
  apply (subgoal_tac "asid_of x' \<noteq> asid_of x")
  apply clarsimp
  apply (clarsimp simp: global_entries_def non_global_entries_def 
                   lookup_def tagged_entry_set_def entry_set_def split: if_split_asm)
proof -
fix xa :: "tlb_entry" and xaa :: "tlb_entry"
  assume a1: "{e \<in> t. (\<exists>a. asid_of e = Some a) \<and> v \<in> range_of e \<and> (asid_of e = None \<or> asid_of e = Some a)} = {x}"
  assume a2: "{e \<in> t'. asid_of e = None \<and> v \<in> range_of e} = {x'}"
  assume a3: "asid_of x' = asid_of x"
have "x \<in> t \<and> (\<exists>w. asid_of x = Some w) \<and> v \<in> range_of x \<and> (asid_of x = None \<or> asid_of x = Some a)"
  using a1 by blast
then show False
using a3 a2 by force
qed

lemma lookup_global_asid_of_none:
  "lookup' (global_entries t) v = Hit e \<Longrightarrow> asid_of e = None"
  apply (clarsimp simp: global_entries_def lookup_def tagged_entry_set_def entry_set_def split: if_split_asm)
  by force
  
lemma lookup_non_global_hit_asid_of_not_none:
  "lookup'' (non_global_entries t) a v = Hit e \<Longrightarrow> asid_of e \<noteq> None"
  apply (clarsimp simp: non_global_entries_def lookup_def tagged_entry_set_def entry_set_def split: if_split_asm)
  by force


                                                          
lemma lookup_miss_minus_miss:
  "lookup'' t a v = Miss \<Longrightarrow> lookup'' (t - t') a v = Miss"
  by (clarsimp simp: lookup_def tagged_entry_set_def entry_set_def split: if_split_asm)
  

lemma lookup_miss_minus_miss_hit:
  "lookup'' t a v = Hit e \<Longrightarrow> lookup'' (t - t') a v = Miss \<or> lookup'' (t - t') a v = Hit e"
  by (metis Diff_subset asid_tlb_mono less_eq_lookup_type lookup_type.simps(7))

lemma tlb_nion_global_non_global:
  " a \<union> b = non_global_entries a \<union> non_global_entries b \<union> (global_entries a \<union> global_entries b)"
  apply (clarsimp simp: non_global_entries_def global_entries_def)
  apply safe [1]
  by force+

lemma tagged_entry_set_to_entry_set:
  "tagged_entry_set (global_entries t) a v = entry_set (global_entries t) v"
  apply (clarsimp simp: global_entries_def tagged_entry_set_def entry_set_def)
  by blast

lemma lookup_global_miss_entry_set_empty:
  "lookup'' (global_entries t) a v = Miss \<Longrightarrow>
    entry_set (global_entries t) v = {}"
  apply (subgoal_tac "lookup' (global_entries t)  v = Miss")
   apply (clarsimp simp: lookup_def split: if_split_asm)
  apply (clarsimp simp: global_entries_def lookup_def tagged_entry_set_def entry_set_def split: if_split_asm)
  apply safe
  by force+


(* page table walk simplification lemmas *)

lemma asid_entry_pt_walk [simp]:
  "pt_walk (a:: 8 word) m r v \<noteq> None \<Longrightarrow> asid_of (the (pt_walk (a:: 8 word) m r v)) = Some a \<or> 
    asid_of (the (pt_walk (a:: 8 word) m r v)) = None"
  apply (clarsimp simp: pt_walk_def Let_def tag_conv_def split: option.splits pde.splits pte.splits if_split_asm)
  by force+


lemma asid_entry_pt_walk_no_fault [simp]:
  "\<not>is_fault(pt_walk (a:: 8 word) m r v) \<Longrightarrow> asid_of (the (pt_walk (a:: 8 word) m r v)) = Some a \<or> 
    asid_of (the (pt_walk (a:: 8 word) m r v)) = None"
  apply (clarsimp simp: pt_walk_def Let_def tag_conv_def is_fault_def split: option.splits pde.splits pte.splits if_split_asm)
  by force+

lemma asid_entry_pt_walk_some [simp, intro!]:
  "pt_walk (a:: 8 word) m r v = Some e \<Longrightarrow> asid_of (the (pt_walk a m r v)) = Some a \<or> asid_of (the (pt_walk a m r v)) = None"
  by (clarsimp simp: pt_walk_def Let_def tag_conv_def split: option.splits pde.splits pte.splits if_split_asm)


lemma asid_tlb_lookup_refill:
  "\<lbrakk> lookup'' t a v = Miss; pt_walk (a:: 8 word) m r v \<noteq> None\<rbrakk> \<Longrightarrow>
   lookup'' (insert (the(pt_walk a m r v)) t) a v = Hit (the(pt_walk a m r v))"
  apply (clarsimp simp: lookup_def split: if_split_asm)
  apply (frule_tac e = "the(pt_walk a m r v)" in tagged_entry_set_insert)
    apply blast
   apply blast
  by simp


lemma asid_va_entry_range_pt_entry':
  "\<not>is_fault(pt_walk (a:: 8 word) m r v) \<Longrightarrow> 
      (Some a, v) \<in> asid_range_of (the(pt_walk a m r v)) \<or> (None, v) \<in> asid_range_of (the(pt_walk a m r v))"
  apply (clarsimp simp: asid_range_of_def is_fault_def) 
  by (metis Option.is_none_def asid_entry_pt_walk_no_fault handy_if_lemma is_fault_def option.discI option.sel option.simps(3)) 
  


lemma  asid_tlb_lookup_miss_is_fault:
  "lookup'' (the ` {e \<in> range (pt_walk a m r). \<not> is_fault e}) a v = Miss \<Longrightarrow> is_fault (pt_walk a m r v)"
  apply (clarsimp simp: lookup_def tagged_entry_set_def entry_set_def image_iff split: if_split_asm)
  apply (drule_tac x = "the (pt_walk a m r v)" in spec)
  apply (cases " v \<in> range_of (the (pt_walk a m r v))"; clarsimp simp: image_iff)
  apply (metis (no_types, hide_lams) asid_entry_pt_walk_no_fault domIff dom_iff)
  by (simp add: is_fault_def)



lemma  asid_va_entry_set_pt_palk_same:
  "\<lbrakk>\<not>is_fault (pt_walk (a:: 8 word) m r x) ;
           (Some a, va) \<in> asid_range_of (the (pt_walk a m r x))\<rbrakk> \<Longrightarrow>
              the(pt_walk a m r x) = the(pt_walk a m r va)"
  apply (clarsimp simp: asid_range_of_def)
  using va_entry_set_pt_palk_same by blast



lemma  asid_va_entry_set_pt_palk_same':
  "\<lbrakk>\<not>is_fault (pt_walk (a:: 8 word) m r x) ;
           (Some a, va) \<in> asid_range_of (the (pt_walk (a:: 8 word) m r x))\<rbrakk> \<Longrightarrow>
              pt_walk (a:: 8 word) m r x = pt_walk (a:: 8 word) m r va"
 apply (clarsimp simp: asid_range_of_def)
  using va_entry_set_pt_palk_same' by blast


 
lemma asid_tlb_lookup_range_pt_walk_hit:
  "\<not> is_fault (pt_walk (asid :: 8 word ) mem ttbr0  va) \<Longrightarrow> 
        lookup'' (the ` {e \<in> range (pt_walk asid mem ttbr0). \<not> is_fault e}) asid va = Hit (the (pt_walk asid mem ttbr0  va)) "
  apply (clarsimp simp: lookup_def)
  apply safe
    apply simp apply clarsimp
   apply (subgoal_tac "x = the (pt_walk asid mem ttbr0 va)" , force)
   apply (clarsimp simp: tagged_entry_set_def entry_set_def)
   apply (drule asid_entry_range_single_element_n)
   apply safe
    apply (unfold Ball_def) [1]
    apply (erule_tac x = "the (pt_walk asid mem ttbr0  va)" in allE)
    apply (clarsimp simp: asid_va_entry_range_pt_entry is_fault_def asid_range_of_def)
    apply (metis asid_entry_pt_walk_no_fault bot.extremum handy_if_lemma is_fault_def option.discI option.distinct(1) option.sel)
   apply (unfold Ball_def) [1]
   apply (erule_tac x = "the (pt_walk asid mem ttbr0  va)" in allE)
   apply (clarsimp simp: asid_va_entry_range_pt_entry is_fault_def asid_range_of_def)
   apply (metis asid_entry_pt_walk_no_fault bot.extremum handy_if_lemma is_fault_def option.discI option.distinct(1) option.sel)
  apply (rule_tac x = "the (pt_walk asid mem ttbr0 va)" in exI)
  apply (clarsimp simp: tagged_entry_set_def entry_set_def)
  apply (rule asid_entry_range_single_elementI')
    apply force
   apply (clarsimp simp: asid_va_entry_range_pt_entry is_fault_def asid_range_of_def) 
   apply (metis Option.is_none_def asid_entry_pt_walk_no_fault handy_if_lemma is_fault_def option.discI option.sel option.simps(3)) 
  apply (clarsimp simp: asid_va_entry_range_pt_entry is_fault_def asid_range_of_def)
  by (metis is_fault_def option.sel option.simps(3) va_entry_set_pt_palk_same') 


lemma asid_tlb_lookup_range_fault_pt_walk:
  "\<lbrakk>lookup'' (the ` {e \<in> range (pt_walk a m r). \<not> is_fault e}) a v = Hit x\<rbrakk>  \<Longrightarrow> 
          \<forall>va\<in> range_of x. x = the (pt_walk a m r va)"
  apply (subgoal_tac "x \<in> the ` {e \<in> range (pt_walk a m r). \<not> is_fault e}")
   prefer 2
   using  lookup_in_asid_tlb apply force
  apply clarsimp
  apply (rule va_entry_set_pt_palk_same, simp)
   by (clarsimp simp: asid_range_of_def)



lemma asid_pt_walk:
  "\<lbrakk> \<not>is_fault (pt_walk a' m r v'); 
      (Some a, v) \<in> asid_range_of (the (pt_walk a' m r v'))\<rbrakk> \<Longrightarrow> a = a'"
 by (clarsimp simp: pt_walk_def Let_def tag_conv_def is_fault_def asid_range_of_def split: option.splits pde.splits pte.splits if_split_asm)


 
lemma pt_walk_some_asid_entry:
  "pt_walk (a:: 8 word) m r v = Some e \<Longrightarrow> asid_of e = Some a \<or> asid_of e = None"
 by (clarsimp simp: pt_walk_def Let_def tag_conv_def split: option.splits pde.splits pte.splits if_split_asm)


lemma asid_tlb_lookup_range_fault_pt_walk':
  "\<lbrakk>lookup'' (the ` {e \<in> range (pt_walk a m r). \<not> is_fault e}) a v = Hit x\<rbrakk>  \<Longrightarrow> 
          \<forall>va\<in> range_of x. x = the (pt_walk a m r va) \<and> \<not>is_fault (pt_walk a m r va)"
  apply (subgoal_tac "x \<in> the ` {e \<in> range (pt_walk a m r). \<not> is_fault e}")
   prefer 2
   using  lookup_in_asid_tlb apply force
   apply clarsimp
   apply (rule conjI)
  apply (rule va_entry_set_pt_palk_same, simp)
   apply (clarsimp simp: asid_range_of_def)
   by (metis (no_types, hide_lams) lookup_asid_tlb_hit_entry_range va_entry_set_pt_palk_same')



lemma  asid_tlb_lookup_miss_is_fault_intro:
  "is_fault (pt_walk (a:: 8 word) m r v) \<Longrightarrow> lookup'' (the ` {e \<in> range (pt_walk (a:: 8 word) m r). \<not> is_fault e}) a v = Miss"
 apply (subgoal_tac  "tagged_entry_set (the ` {e \<in> range (pt_walk (a:: 8 word) m r). \<not> is_fault e}) a v = {}")
   apply (clarsimp simp: lookup_def)
  apply (clarsimp simp: tagged_entry_set_def entry_set_def)
  apply (subgoal_tac "pt_walk (a:: 8 word) m r xb = pt_walk (a:: 8 word) m r v", simp)
  using va_entry_set_pt_palk_same' by blast


lemma asid_tlb_lookup_range_pt_walk_not_incon:
  "lookup'' (the ` {e \<in> range (pt_walk (asid :: 8 word) mem ttbr0). \<not> is_fault e}) asid va \<noteq> Incon"
  apply (case_tac "\<not>is_fault (pt_walk asid mem ttbr0 va)")
   apply (clarsimp simp: asid_tlb_lookup_range_pt_walk_hit ) 
  apply clarsimp
  apply (subgoal_tac " lookup'' (the ` {e \<in> pt_walk asid mem ttbr0 ` top. \<not> is_fault e}) asid va = Miss")
   apply (clarsimp simp: lookup_def tagged_entry_set_def entry_set_def split: if_split_asm)
  by (clarsimp simp: asid_tlb_lookup_miss_is_fault_intro)




lemma is_fault_pt_walk_unequal_asid:
   "is_fault (pt_walk a m r v) \<Longrightarrow> is_fault (pt_walk a' m r v)"
  apply (clarsimp simp: is_fault_def)
  by (clarsimp simp: pt_walk_def Let_def tag_conv_def split: option.splits pde.splits pte.splits if_split_asm)




lemma no_fault_pt_walk_unequal_asid':
   "\<not>is_fault (pt_walk (a::8 word) m r v) \<Longrightarrow> \<not>is_fault (pt_walk a' m r v)"
  apply (clarsimp simp: is_fault_def)
  apply (clarsimp simp: pt_walk_def Let_def tag_conv_def split: option.splits pde.splits pte.splits if_split_asm)
  by force+

lemma  asid_tlb_lookup_miss_is_fault_intro_unequal_asid:
  "is_fault (pt_walk (a:: 8 word) m r v) \<Longrightarrow> lookup'' (the ` {e \<in> range (pt_walk (a:: 8 word) m r). \<not> is_fault e}) a' v = Miss"
 apply (subgoal_tac  "tagged_entry_set (the ` {e \<in> range (pt_walk (a:: 8 word) m r). \<not> is_fault e}) a' v = {}")
   apply (clarsimp simp: lookup_def)
  apply (clarsimp simp: tagged_entry_set_def entry_set_def)
  apply (subgoal_tac "pt_walk (a:: 8 word) m r xb = pt_walk (a:: 8 word) m r v", simp)
  using va_entry_set_pt_palk_same' by blast




lemma asid_unequal_lookup_pt_walk_miss:
  "a \<noteq> a' \<Longrightarrow> lookup'' (non_global_entries (the ` {e \<in> range (pt_walk (a':: 8 word) m r). \<not> is_fault e})) a v = Miss"
  apply (subgoal_tac "tagged_entry_set (non_global_entries (the ` {e \<in> range (pt_walk a' m r). \<not> is_fault e})) a v = {}")
   apply (clarsimp simp:  lookup_def) 
  apply (clarsimp simp: entry_set_va_set asid_vadr_tlb_def is_fault_def non_global_entries_def asid_range_of_def) 
  apply safe
  by (clarsimp simp: pt_walk_def Let_def tag_conv_def split: option.splits pde.splits pte.splits if_split_asm)





lemma global_lookup_range_pt_walk_not_incon:
  "lookup'' (global_entries (the ` {e \<in> range (pt_walk (asid :: 8 word) mem ttbr0). \<not> is_fault e})) asid va \<noteq> Incon"
  apply (subgoal_tac "lookup''  (the ` {e \<in> range (pt_walk asid mem ttbr0). \<not> is_fault e}) asid va \<noteq> Incon")
   prefer 2
   apply (rule asid_tlb_lookup_range_pt_walk_not_incon)
  apply (subgoal_tac "global_entries (the ` {e \<in> range (pt_walk asid mem ttbr0). \<not> is_fault e}) \<subseteq> 
                          the ` {e \<in> range (pt_walk asid mem ttbr0). \<not> is_fault e}")
  using lookup_asid_tlb_incon_subset apply blast
  by (rule glb_tlb_subset)
  


lemma non_global_lookup_range_pt_walk_not_incon:
  "lookup'' (non_global_entries (the ` {e \<in> range (pt_walk (asid :: 8 word) mem ttbr0). \<not> is_fault e})) asid va \<noteq> Incon"
  apply (subgoal_tac "lookup''  (the ` {e \<in> range (pt_walk asid mem ttbr0). \<not> is_fault e}) asid va \<noteq> Incon")
   prefer 2
   apply (rule asid_tlb_lookup_range_pt_walk_not_incon)
  apply (subgoal_tac "non_global_entries (the ` {e \<in> range (pt_walk asid mem ttbr0). \<not> is_fault e}) \<subseteq> 
                          the ` {e \<in> range (pt_walk asid mem ttbr0). \<not> is_fault e}")
  using lookup_asid_tlb_incon_subset apply blast
  by (rule non_glb_tlb_subset)


lemma global_entries_rewrite:
  "global_entries (the ` {e \<in> range (pt_walk a m r). \<not> is_fault e}) = 
     the ` {e \<in> range (pt_walk a m r). \<exists>e'. e = Some e' \<and> asid_of e' = None}"
  apply (clarsimp simp: global_entries_def is_fault_def)
  apply safe
  using image_iff apply fastforce
   apply blast
  by force




lemma  global_entries_ptable_same:
  "global_entries (the ` {e \<in> range (pt_walk a m r). \<not> is_fault e}) = 
        global_entries (the ` {e \<in> range (pt_walk a' m r). \<not> is_fault e})"
  apply rule
   apply (clarsimp simp: global_entries_def is_fault_def)
   apply (clarsimp simp: image_iff)
   apply (rule_tac x = "pt_walk a m r xb" in exI)
   apply (rule conjI)
    apply (rule_tac x = xb in exI)
    apply (clarsimp simp: is_fault_def pt_walk_def Let_def 
                           tag_conv_def split: option.splits pde.splits pte.splits if_split_asm)
    apply force
   apply force
  apply (clarsimp simp: global_entries_def is_fault_def)
  apply (clarsimp simp: image_iff)
  apply (rule_tac x = "pt_walk a' m r xb" in exI)
  apply (rule conjI)
   apply (rule_tac x = xb in exI)
   apply (clarsimp simp: is_fault_def pt_walk_def Let_def 
      tag_conv_def split: option.splits pde.splits pte.splits if_split_asm)
   apply force
  by force





lemma non_global_lookup_range_fault_pt_walk:
  "\<lbrakk>lookup'' (non_global_entries (the ` {e \<in> range (pt_walk a m r). \<not> is_fault e})) a v = Hit x\<rbrakk>  \<Longrightarrow> 
          \<forall>va\<in> range_of x. x = the (pt_walk a m r va)"
  apply (subgoal_tac "lookup''  (the ` {e \<in> range (pt_walk a m r). \<not> is_fault e}) a v = Hit x")
   apply (rule asid_tlb_lookup_range_fault_pt_walk, simp)
  apply (subgoal_tac "lookup'' (the ` {e \<in> range (pt_walk a m r). \<not> is_fault e}) a v \<noteq> Incon")
   apply (subgoal_tac "non_global_entries (the ` {e \<in> range (pt_walk a m r). \<not> is_fault e}) \<subseteq>
                      the ` {e \<in> range (pt_walk a m r). \<not> is_fault e} ")
    apply (drule_tac a = a and v = v in asid_tlb_mono)
    apply (simp add: less_eq_lookup_type)
   apply (clarsimp simp: non_global_entries_def)
  by (rule asid_tlb_lookup_range_pt_walk_not_incon)


lemma global_lookup_range_fault_pt_walk:
  "\<lbrakk>lookup'' (global_entries (the ` {e \<in> range (pt_walk a m r). \<not> is_fault e})) a v = Hit x\<rbrakk>  \<Longrightarrow> 
          \<forall>va\<in> range_of x. x = the (pt_walk a m r va)"
  apply (subgoal_tac "lookup''  (the ` {e \<in> range (pt_walk a m r). \<not> is_fault e}) a v = Hit x")
   apply (rule asid_tlb_lookup_range_fault_pt_walk, simp)
  apply (subgoal_tac "lookup'' (the ` {e \<in> range (pt_walk a m r). \<not> is_fault e}) a v \<noteq> Incon")
   apply (subgoal_tac "global_entries (the ` {e \<in> range (pt_walk a m r). \<not> is_fault e}) \<subseteq>
                      the ` {e \<in> range (pt_walk a m r). \<not> is_fault e} ")
    apply (drule_tac a = a and v = v in asid_tlb_mono)
    apply (simp add: less_eq_lookup_type)
   apply (clarsimp simp: global_entries_def)
  by (rule asid_tlb_lookup_range_pt_walk_not_incon)


        


lemma lookup_non_global_miss_non_fault:
  "\<lbrakk> lookup'' (non_global_entries (the ` {e \<in> range (pt_walk a m r). \<not> is_fault e}) ) a v = Miss;  
        \<not> is_fault (pt_walk a m r v)\<rbrakk> \<Longrightarrow> 
    lookup'' (global_entries (the ` {e \<in> range (pt_walk a m r). \<not> is_fault e})) a v = 
           Hit (the (pt_walk a m r v))"
  apply (frule asid_tlb_lookup_range_pt_walk_hit)
  apply (subgoal_tac "lookup'' (the ` {e \<in> range (pt_walk a m r). \<not> is_fault e}) a v =
                lookup'' (global_entries (the ` {e \<in> range (pt_walk a m r). \<not> is_fault e}) \<union>
                 non_global_entries (the ` {e \<in> range (pt_walk a m r). \<not> is_fault e})) a v")
   apply (simp only:)
   apply (drule lookup_asid_tlb_hit_mis_hit; simp)
  by (rule lookup_tlb_eq_union_global_non_global)


lemma lookup_global_miss_non_fault:
  "\<lbrakk> lookup'' (global_entries (the ` {e \<in> range (pt_walk a m r). \<not> is_fault e}) ) a v = Miss;  
        \<not> is_fault (pt_walk a m r v)\<rbrakk> \<Longrightarrow> 
    lookup'' (non_global_entries (the ` {e \<in> range (pt_walk a m r). \<not> is_fault e})) a v = 
           Hit (the (pt_walk a m r v))"
  apply (frule asid_tlb_lookup_range_pt_walk_hit)
  apply (subgoal_tac "lookup'' (the ` {e \<in> range (pt_walk a m r). \<not> is_fault e}) a v =
                lookup'' (global_entries (the ` {e \<in> range (pt_walk a m r). \<not> is_fault e}) \<union>
                 non_global_entries (the ` {e \<in> range (pt_walk a m r). \<not> is_fault e})) a v")
   apply (simp only:)
   apply (drule lookup_asid_tlb_hit_mis_hit'; simp)
  by (rule lookup_tlb_eq_union_global_non_global)

 
lemma non_global_global_disjoint:
  "lookup'' (non_global_entries (the ` {e \<in> range (pt_walk a m r). \<not> is_fault e})) a v = Hit x \<Longrightarrow>
   lookup'' (global_entries (the ` {e \<in> range (pt_walk a m r). \<not> is_fault e})) a v = Miss"
  apply (cases "lookup'' (the ` {e \<in> range (pt_walk a m r). \<not> is_fault e}) a v")
    apply (metis (no_types) lookup_asid_tlb_miss_union lookup_tlb_eq_union_global_non_global)
   apply (clarsimp simp: asid_tlb_lookup_range_pt_walk_not_incon)
  apply (case_tac "lookup'' (global_entries (the ` {e \<in> range (pt_walk a m r). \<not> is_fault e})) a v")
    apply simp
   apply (simp add: lookup_global_incon_incon)
  apply clarsimp
proof -
fix x3 :: "tlb_entry" and x3a :: "tlb_entry"
assume a1: "lookup'' (non_global_entries (the ` {e \<in> range (pt_walk a m r). \<not> is_fault e})) a v = Hit x"
  assume a2: "lookup'' (the ` {e \<in> range (pt_walk a m r). \<not> is_fault e}) a v = Hit x3"
  assume a3: "lookup'' (global_entries (the ` {e \<in> range (pt_walk a m r). \<not> is_fault e})) a v = Hit x3a"
  have f4: "x \<in> non_global_entries (the ` {z \<in> range (pt_walk a m r). \<not> is_fault z})"
using a1 by (meson lookup_in_asid_tlb)
  have f5: "lookup'' (non_global_entries (the ` {z \<in> range (pt_walk a m r). \<not> is_fault z})) a v \<le> Hit x3"
using a2 by (metis (no_types) asid_tlb_mono non_glb_tlb_subset)
  have "lookup'' (global_entries (the ` {z \<in> range (pt_walk a m r). \<not> is_fault z})) a v \<le> Hit x3"
    using a2 by (metis (no_types) asid_tlb_mono glb_tlb_subset)
  then show False
  using f5 f4 a3 a1 by (simp add: lookup_in_asid_tlb non_global_to_global)
qed

 

lemma lookup_global_non_global_miss_fault:
  "\<lbrakk>lookup'' (non_global_entries (the ` {e \<in> range (pt_walk a m r). \<not> is_fault e})) a v = Miss;
         lookup'' (global_entries (the ` {e \<in> range (pt_walk a m r). \<not> is_fault e})) a v = Miss\<rbrakk>
                 \<Longrightarrow> is_fault (pt_walk a m r v)"
  apply (subgoal_tac " lookup''  (the ` {e \<in> range (pt_walk a m r). \<not> is_fault e}) a v = Miss")
  using asid_tlb_lookup_range_pt_walk_hit apply fastforce
  apply (subgoal_tac "lookup'' (global_entries (the ` {e \<in> range (pt_walk a m r). \<not> is_fault e}) \<union>
                     non_global_entries (the ` {e \<in> range (pt_walk a m r). \<not> is_fault e})) a v = Miss")
  using lookup_tlb_eq_union_global_non_global apply fastforce
  by (rule lookup_asid_tlb_miss_union_miss_miss; simp)



lemma non_global_hit_no_fault:
  "lookup'' (non_global_entries (the ` {e \<in> range (pt_walk a m r). \<not> is_fault e})) a v = Hit x \<Longrightarrow>
             \<not> is_fault (pt_walk a m r v)"
  apply (subgoal_tac "lookup'' (the ` {e \<in> range (pt_walk a m r). \<not> is_fault e}) a v = Hit x")
   apply (simp add: asid_tlb_lookup_range_fault_pt_walk' lookup_asid_tlb_hit_entry_range)
  apply (subgoal_tac "non_global_entries (the ` {e \<in> range (pt_walk a m r). \<not> is_fault e}) \<subseteq>
                       the ` {e \<in> range (pt_walk a m r). \<not> is_fault e}")
   prefer 2 apply (rule non_glb_tlb_subset)
  apply (case_tac "lookup'' (the ` {e \<in> range (pt_walk a m r). \<not> is_fault e}) a v"; clarsimp)
    apply (drule_tac a = a and v= v in asid_tlb_mono, simp)
   apply (clarsimp simp: asid_tlb_lookup_range_pt_walk_not_incon)
  by (drule_tac a = a and v= v in asid_tlb_mono, simp)


lemma global_hit_no_fault:
  "lookup'' (global_entries (the ` {e \<in> range (pt_walk a m r). \<not> is_fault e})) a v = Hit x \<Longrightarrow>
             \<not> is_fault (pt_walk a m r v)"
  apply (subgoal_tac "lookup'' (the ` {e \<in> range (pt_walk a m r). \<not> is_fault e}) a v = Hit x")
   apply (simp add: asid_tlb_lookup_range_fault_pt_walk' lookup_asid_tlb_hit_entry_range)
  apply (subgoal_tac "global_entries (the ` {e \<in> range (pt_walk a m r). \<not> is_fault e}) \<subseteq>
                       the ` {e \<in> range (pt_walk a m r). \<not> is_fault e}")
   prefer 2 apply (rule glb_tlb_subset)
  apply (case_tac "lookup'' (the ` {e \<in> range (pt_walk a m r). \<not> is_fault e}) a v"; clarsimp)
    apply (drule_tac a = a and v= v in asid_tlb_mono, simp)
   apply (clarsimp simp: asid_tlb_lookup_range_pt_walk_not_incon)
  by (drule_tac a = a and v= v in asid_tlb_mono, simp)



lemma lookup_global_entry_hit_diff_asid:
  "lookup'' (global_entries (the ` {e \<in> range (pt_walk a m r). \<not> is_fault e})) a v = Hit e \<Longrightarrow>
     e =  the (pt_walk a' m r v)"
  apply (subgoal_tac "e = the (pt_walk a m r v)")
   apply (subgoal_tac "\<not>is_fault (pt_walk a m r v)")
    apply (subgoal_tac "asid_of e = None")
     apply (clarsimp)
     apply (clarsimp simp: is_fault_def)
     apply (clarsimp simp: pt_walk_def Let_def tag_conv_def split: option.splits pde.splits pte.splits if_split_asm)
     apply force
    apply (simp add: lookup_global_hit_asid_of_none)
   apply clarsimp
   apply (clarsimp simp: global_hit_no_fault)
  apply (frule_tac global_lookup_range_fault_pt_walk)
  apply (drule_tac x = v in bspec)
  using lookup_global_hit_lookup' lookup_hit_entry_range_asid_tags apply blast
  by simp




lemma global_entries_range_unequal_asid_equal:
  "global_entries (the ` {e \<in> range (pt_walk a m r). \<not> is_fault e}) =
           global_entries (the ` {e \<in> range (pt_walk a' m r). \<not> is_fault e})"
  apply safe
   apply (clarsimp simp: global_entries_def)
   apply (clarsimp simp: image_iff)
   apply (rule_tac x = "pt_walk a m r xb" in exI)
   apply (rule conjI)
    apply (rule_tac x = xb in exI)
    apply (case_tac " pt_walk a m r xb ")
     apply (clarsimp simp: is_fault_def)
    apply (clarsimp simp: is_fault_def pt_walk_def Let_def tag_conv_def split: option.splits pde.splits pte.splits if_split_asm)
    apply (safe ; force)[1]
   apply force
  apply (clarsimp simp: global_entries_def)
  apply (clarsimp simp: image_iff)
  apply (rule_tac x = "pt_walk a' m r xb" in exI)
  apply (rule conjI)
   apply (rule_tac x = xb in exI)
   apply (case_tac " pt_walk a' m r xb ")
    apply (clarsimp simp: is_fault_def)
   apply (clarsimp simp: is_fault_def pt_walk_def Let_def tag_conv_def split: option.splits pde.splits pte.splits if_split_asm)
   apply (safe ; force)[1]
  by force
   


lemma is_fault_global_entries_miss:
 "is_fault (pt_walk a m r v) \<Longrightarrow> lookup'' (global_entries (the ` {e \<in> range (pt_walk a m r). \<not> is_fault e})) a v = Miss"
  apply (subgoal_tac "lookup'' (the ` {e \<in> range (pt_walk a m r). \<not> is_fault e}) a v = Miss")
  apply (subgoal_tac "lookup'' (global_entries (the ` {e \<in> range (pt_walk a m r). \<not> is_fault e}) \<union>
                  non_global_entries (the ` {e \<in> range (pt_walk a m r). \<not> is_fault e})) a v = Miss")
  prefer 2
  using lookup_tlb_eq_union_global_non_global apply auto[1]
   apply (drule lookup_asid_tlb_miss_union, simp)
  using asid_tlb_lookup_miss_is_fault_intro by auto 

lemma is_fault_non_global_entries_miss:
 "is_fault (pt_walk a m r v) \<Longrightarrow> lookup'' (non_global_entries (the ` {e \<in> range (pt_walk a m r). \<not> is_fault e})) a v = Miss"
  apply (subgoal_tac "lookup'' (the ` {e \<in> range (pt_walk a m r). \<not> is_fault e}) a v = Miss")
  apply (subgoal_tac "lookup'' (global_entries (the ` {e \<in> range (pt_walk a m r). \<not> is_fault e}) \<union>
                  non_global_entries (the ` {e \<in> range (pt_walk a m r). \<not> is_fault e})) a v = Miss")
  prefer 2
  using lookup_tlb_eq_union_global_non_global apply auto[1]
   apply (drule lookup_asid_tlb_miss_union, simp)
  using asid_tlb_lookup_miss_is_fault_intro by auto 


lemma is_fault_global_non_global_entries_miss:
 "is_fault (pt_walk a m r v) \<Longrightarrow> 
   lookup'' (global_entries (the ` {e \<in> range (pt_walk a m r). \<not> is_fault e})) a v = Miss \<and> 
   lookup'' (non_global_entries (the ` {e \<in> range (pt_walk a m r). \<not> is_fault e})) a v = Miss"
  using is_fault_non_global_entries_miss is_fault_global_entries_miss by force



lemma lookup_global_miss_asid_unequal:
  "\<lbrakk>lookup'' (global_entries (the ` {e \<in> range (pt_walk a m r). \<not> is_fault e})) a v = Miss\<rbrakk>
    \<Longrightarrow> lookup'' (global_entries (the ` {e \<in> range (pt_walk a' m r). \<not> is_fault e})) a' v = Miss"  
  apply (subgoal_tac "tagged_entry_set (global_entries (the ` {e \<in> range (pt_walk a' m r). \<not> is_fault e})) a' v = {}")
  apply (clarsimp simp:  lookup_def)
  apply (clarsimp simp: tagged_entry_set_to_entry_set)
  apply (rule_tac a = a in lookup_global_miss_entry_set_empty)
  apply (insert global_entries_ptable_same [of a m r a'])
  by force


lemma non_global_lookup_hit_asid:
  "lookup'' (non_global_entries (the ` {e \<in> range (pt_walk a m r). \<not> is_fault e})) a v = Hit e \<Longrightarrow>
   lookup'' (non_global_entries (the ` {e \<in> range (pt_walk a' m r). \<not> is_fault e})) a' v =  
            Hit (the (pt_walk a' m r v))"
  apply (case_tac " lookup'' (non_global_entries (the ` {e \<in> range (pt_walk a' m r). \<not> is_fault e})) a' v"; clarsimp)
    defer
    apply (clarsimp simp: non_global_lookup_range_pt_walk_not_incon)
   apply (frule_tac a = a' in non_global_lookup_range_fault_pt_walk, 
               drule_tac x = v in bspec, clarsimp simp: lookup_asid_tlb_hit_entry_range, simp) 
  apply (subgoal_tac "lookup'' (global_entries (the ` {e \<in> range (pt_walk a m r). \<not> is_fault e})) a v = Miss")
  prefer 2
  using non_global_global_disjoint apply auto[1]
 apply (subgoal_tac "lookup'' (global_entries (the ` {e \<in> range (pt_walk a' m r). \<not> is_fault e})) a' v = Miss")
   apply (subgoal_tac "\<not>is_fault (pt_walk a' m r v)")
  using lookup_global_miss_non_fault apply auto [1]
  apply (subgoal_tac "\<not> is_fault (pt_walk a m r v)")
    apply (rule_tac a = a in no_fault_pt_walk_unequal_asid', simp)
   apply (clarsimp simp: non_global_hit_no_fault)
  by (rule_tac a = a in lookup_global_miss_asid_unequal, simp)
  
lemma lookup_non_global_union_asid_unequal:
 "a \<noteq> a' \<Longrightarrow> lookup'' (non_global_entries (t \<union> the ` {e \<in> range (pt_walk a m r). \<not> is_fault e}))  a' v =
                 lookup'' (non_global_entries t) a' v"
  apply (subgoal_tac "non_global_entries (t \<union> the ` {e \<in> range (pt_walk a m r). \<not> is_fault e}) =
       non_global_entries t \<union> non_global_entries (the ` {e \<in> range (pt_walk  a m r). \<not> is_fault e})")
   prefer 2
   apply (clarsimp simp: non_global_entries_def) apply blast
  apply clarsimp
  apply (subgoal_tac " lookup'' (non_global_entries (the ` {e \<in> range (pt_walk  a m r). \<not> is_fault e}))  a' v  = Miss")
  using lookup_asid_tlb_miss_union_equal apply blast
  using asid_unequal_lookup_pt_walk_miss by auto
                                      
lemma lookup_non_global_union_asid_unequal':
 "\<lbrakk>a \<noteq> a''; a' \<noteq> a''; a' \<noteq> a \<rbrakk> \<Longrightarrow>
     lookup'' (non_global_entries (t \<union> the ` {e \<in> range (pt_walk a m r). \<not> is_fault e}))
              a' v =
             lookup'' (non_global_entries t) a' v"
  apply (subgoal_tac "non_global_entries (t \<union> the ` {e \<in> range (pt_walk a m r). \<not> is_fault e}) =
       non_global_entries t \<union> non_global_entries (the ` {e \<in> range (pt_walk a m r). \<not> is_fault e})")
   prefer 2
   apply (clarsimp simp: non_global_entries_def) apply blast
  apply clarsimp
  apply (subgoal_tac " lookup'' (non_global_entries (the ` {e \<in> range (pt_walk a m r). \<not> is_fault e})) a' v  = Miss")
  using lookup_asid_tlb_miss_union_equal apply blast
  using asid_unequal_lookup_pt_walk_miss by auto

lemma lookup_global_hit_order:
  "lookup'' (global_entries t) a v = Hit e  \<Longrightarrow>
        lookup'' t a v = Hit e \<or> lookup'' t a v = Incon"
  apply safe
  by (metis (mono_tags, hide_lams) asid_tlb_mono glb_tlb_subset 
                less_eq_lookup_type lookup_type.simps(5))

lemma lookup_range_pt_hit_no_fault:
  "lookup''  (the ` {e \<in> range (pt_walk a m r). \<not> is_fault e}) a v = Hit x \<Longrightarrow>
             \<not> is_fault (pt_walk a m r v)"
  by (simp add: asid_tlb_lookup_range_fault_pt_walk' lookup_asid_tlb_hit_entry_range)



lemma tlb_subset_lookup_un_eq:
  "t \<subseteq> t' \<Longrightarrow> lookup''(t' \<union> t) a v =  lookup'' t' a v"
  apply (subgoal_tac "t' = t \<union> t'")
   apply (simp add: sup.commute)
  by blast
 



end