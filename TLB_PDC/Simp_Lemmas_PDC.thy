theory Simp_Lemmas_PDC

imports TLB_PDC
         TLB_ASID_REFJ.Simp_Lemmas_ASIDs
        
begin


lemma [simp]:
  "fst (pairunion t (a, b)) =  fst t \<union> a "
  apply (cases t)
  by clarsimp


lemma [simp]:
  "snd (pairunion t(a, b)) = snd t \<union> b" 
  apply (cases t)
  by clarsimp


lemma [simp]:
 "fst (pairunion (pairunion t ({}, {a})) ({b}, {})) = insert b (fst t)"
 apply (cases t)
  by clarsimp

lemma [simp]:
 "snd (pairunion (pairunion t ({}, {a})) (b, {})) = insert a (snd t)"
 apply (cases t)
  by clarsimp

lemma [simp]:
  "fst (pairunion t (a, {})) = fst t \<union> a"
  apply (cases t)
  by (clarsimp)

lemma [simp]:
  "snd (pairunion t (a, {})) = snd t "
  apply (cases t)
  by (clarsimp)

lemma subset_pairunion [simp]:
   "\<lbrakk>a \<subseteq> fst s; b \<subseteq> snd s\<rbrakk>  \<Longrightarrow> s = pairunion s (a, b)"
  by (metis (no_types, hide_lams)  le_sup_iff  pairunion.simps prod.exhaust_sel subset_antisym subset_refl)


lemma [simp]:
  "\<lbrakk>a \<preceq> b; a \<noteq> Fault\<rbrakk> \<Longrightarrow> b \<noteq> Fault"
  by (force simp: entry_leq_def)

(* lookup_pdc Lemmas *)

abbreviation "lookup_pdc p a \<equiv> lookup (tagged_pdc_entry_set p a)" 



lemma asid_pdc_mono_entry_set:
  "t \<subseteq> t' \<Longrightarrow> tagged_pdc_entry_set t a v \<subseteq> tagged_pdc_entry_set t' a v"
  apply (clarsimp simp: tagged_pdc_entry_set_def entry_set_def asid_of_pdc_def)
  by (meson subset_eq tlb_mono_entry_set) 

lemma asid_pdc_mono:
  "t \<subseteq> t' \<Longrightarrow> lookup_pdc t a v \<le> lookup_pdc t' a v"
  by (drule asid_pdc_mono_entry_set) (fastforce simp: lookup_def)

lemma lookup_in_asid_pdc:
  "lookup_pdc t a v = Hit e \<Longrightarrow> e \<in> t"
  by (auto simp: lookup_def tagged_pdc_entry_set_def entry_set_def asid_of_pdc_def   split: if_split_asm)


lemma lookup_asid_pdc_incon_subset [simp]:
  "\<lbrakk> s \<subseteq> t ; lookup_pdc s a v = Incon \<rbrakk> \<Longrightarrow>  lookup_pdc t a v = Incon"
  by (metis less_eq_lookup_type lookup_type.simps(3) asid_pdc_mono)


lemma tagged_pdc_entry_set_insert:
  "\<lbrakk> tagged_pdc_entry_set t a v = {}; asid_of_pdc e = Some a \<or> asid_of_pdc e = None; v \<in> range_of e \<rbrakk> \<Longrightarrow> 
               tagged_pdc_entry_set (insert e t) a v = {e}"
  apply (clarsimp simp: tagged_pdc_entry_set_def entry_set_def asid_of_pdc_def )
  by force    



lemma pdc_subset_lookup_un_eq:
  "t \<subseteq> t' \<Longrightarrow> lookup_pdc(t' \<union> t) a v =  lookup_pdc t' a v"
  apply (subgoal_tac "t' = t \<union> t'")
   apply (simp add: sup.commute)
  by blast


lemma lookup_minus_union_incon:
  "lookup'' (t - t' \<union> t'') a v = Incon \<Longrightarrow> lookup'' (t \<union> t'') a v = Incon"
  apply (subgoal_tac "t - t' \<union> t'' \<subseteq> t \<union> t''")
  using lookup_asid_tlb_incon_subset apply blast
  by blast

lemma lookup_minus_union_incon_pdc:
  "lookup_pdc (t - t' \<union> t'') a v = Incon \<Longrightarrow> lookup_pdc (t \<union> t'') a v = Incon"
  apply (subgoal_tac "t - t' \<union> t'' \<subseteq> t \<union> t''")
  using lookup_asid_pdc_incon_subset apply blast
  by blast
 

lemma addr_set_minus_lookup_miss:
  "v \<in> vset \<Longrightarrow> lookup'' (t - (\<Union>v\<in>vset. {e \<in> t. v \<in> range_of e})) a v = Miss"
  apply (subgoal_tac "tagged_entry_set (t - (\<Union>v\<in>vset. {e \<in> t. v \<in> range_of e})) a v = {}")
   apply (clarsimp simp: lookup_def)
  apply (clarsimp simp: tagged_entry_set_def entry_set_def) by force

lemma addr_set_minus_lookup_miss_pdc:
  "v \<in> vset \<Longrightarrow> lookup_pdc (t - (\<Union>v\<in>vset. {e \<in> t. v \<in> range_of e})) a v = Miss"
  apply (subgoal_tac "tagged_pdc_entry_set (t - (\<Union>v\<in>vset. {e \<in> t. v \<in> range_of e})) a v = {}")
   apply (clarsimp simp: lookup_def)
  apply (clarsimp simp: tagged_pdc_entry_set_def entry_set_def) by force


lemma lookup_asid_pdc_miss_union:
  " lookup_pdc (t \<union> t') a v = Miss  \<Longrightarrow>
      (lookup_pdc t a v = Miss \<and> lookup_pdc t' a v = Miss)"
  apply rule
   apply (clarsimp simp: lookup_def tagged_pdc_entry_set_def entry_set_def asid_of_pdc_def   split: if_split_asm)
   apply safe
      apply blast+
  apply (clarsimp simp: lookup_def tagged_pdc_entry_set_def entry_set_def asid_of_pdc_def   split: if_split_asm)
  apply safe
  by blast+


lemma lookup_asid_pdc_hit_miss_or_hit' :
  " lookup_pdc (t \<union> t') a v = Hit e  \<Longrightarrow> 
              lookup_pdc t' a v = Miss \<or> (lookup_pdc t' a v = Hit e)"
  by (metis Un_upper2 asid_pdc_mono less_eq_lookup_type lookup_type.simps(7))
 
lemma  lookup_asid_pdc_hit_entry_range:
  "lookup_pdc t a v = Hit e \<Longrightarrow> v \<in> range_of e"
  apply (clarsimp simp: lookup_def  tagged_pdc_entry_set_def entry_set_def asid_of_pdc_def  split:if_split_asm)
  by force

lemma lookup_asid_pdc_union_hit_miss_hit :
  "\<lbrakk>lookup_pdc (t \<union> t') a v = Hit e ; lookup_pdc t' a v \<noteq> Miss \<rbrakk> \<Longrightarrow> lookup_pdc t' a v = Hit e"
  using lookup_asid_pdc_hit_miss_or_hit' by blast
 
lemma  lookup_asid_pdc_not_hit_miss:
  "\<lbrakk>lookup_pdc (t \<union> t') a v = Hit e;   lookup_pdc t a v \<noteq> Hit e\<rbrakk> \<Longrightarrow> lookup_pdc t a v = Miss"
  by (metis lookup_asid_pdc_union_hit_miss_hit sup_commute)
  

lemma lookup_asid_pdc_union_hit_miss_hit' :
  "\<lbrakk>lookup_pdc (t \<union> t') a v = Hit e; lookup_pdc t a v \<noteq> Miss \<rbrakk> \<Longrightarrow> lookup_pdc t a v = Hit e"
  using lookup_asid_pdc_not_hit_miss by blast
  
lemma  lookup_asid_pdc_not_hit_false:
  "\<lbrakk>lookup_pdc (t \<union> t') a v = Hit e; lookup_pdc t a v \<noteq> Hit e; lookup_pdc t' a v \<noteq> Hit e\<rbrakk> \<Longrightarrow> False"
  apply (cases "lookup_pdc t a v"; clarsimp)
    defer
    apply (metis Un_upper1 lookup_asid_pdc_incon_subset lookup_type.simps(7))
   apply (metis Hits_le asid_pdc_mono inf_sup_ord(3))
  apply (simp only: lookup_def  tagged_pdc_entry_set_def entry_set_def asid_of_pdc_def   split:if_split_asm cong: Collect_cong)
     by blast+ 

  

lemma lookup_asid_pdc_not_hit_hit:
  "\<lbrakk>lookup_pdc (t \<union> t') a v = Hit e; lookup_pdc t a v \<noteq> Hit e\<rbrakk> \<Longrightarrow> lookup_pdc t' a v = Hit e"
  using lookup_asid_pdc_not_hit_false by blast


lemma lookup_asid_pdc_hit_union_cases':
  " lookup_pdc (t \<union> t') a v = Hit e  \<Longrightarrow>
      (lookup_pdc t a v  = Hit e \<and> lookup_pdc t' a v = Miss)  \<or>
      (lookup_pdc t' a v = Hit e \<and> lookup_pdc t a v  = Miss)  \<or>
      (lookup_pdc t a v  = Hit e \<and> lookup_pdc t' a v = Hit e)"
  apply (safe , clarsimp)
         apply (drule lookup_asid_pdc_not_hit_hit; clarsimp)
        apply (drule lookup_asid_pdc_not_hit_miss; clarsimp)
       apply (drule lookup_asid_pdc_not_hit_false ; clarsimp) 
      apply (drule lookup_asid_pdc_not_hit_false ; clarsimp)
     apply (drule lookup_asid_pdc_union_hit_miss_hit ; clarsimp)
    apply (drule lookup_asid_pdc_not_hit_miss ; clarsimp)
   apply (drule lookup_asid_pdc_union_hit_miss_hit ; clarsimp)
  by (drule lookup_asid_pdc_hit_miss_or_hit' ; clarsimp)

lemma lookup_asid_pdc_miss_implies_union_miss:
  "\<lbrakk>lookup_pdc t a v = Miss ; lookup_pdc t' a v = Miss \<rbrakk> \<Longrightarrow> lookup_pdc (t \<union> t') a v = Miss "
  apply (clarsimp simp: lookup_def tagged_pdc_entry_set_def entry_set_def asid_of_pdc_def   split: if_split_asm)
  apply safe
  by blast+

lemma lookup_asid_pdc_miss_hit_implies_union_hit:
  "\<lbrakk>lookup_pdc t a v = Miss; lookup_pdc t' a v = Hit e\<rbrakk> \<Longrightarrow> lookup_pdc (t \<union> t') a v = Hit e"
  apply (case_tac "lookup_pdc (t \<union> t') a v"; clarsimp)
    apply (clarsimp simp: lookup_def tagged_pdc_entry_set_def entry_set_def   split: if_split_asm)
    apply (safe; force) [1] 
   apply (clarsimp simp: lookup_def tagged_pdc_entry_set_def entry_set_def   split: if_split_asm)
   apply (safe; force) [1]
  apply (clarsimp simp: lookup_def tagged_pdc_entry_set_def entry_set_def   split: if_split_asm)
  by (safe; force) [1]

 

lemma  union_asid_pdc_incon_cases:
  "lookup_pdc (t \<union> t') a v = Incon \<Longrightarrow> 
      (lookup_pdc t a v = Incon \<and> lookup_pdc t' a v = Incon)  \<or>
      ((\<exists>x\<in>t. lookup_pdc t a v = Hit x)  \<and> (\<exists>x\<in>t'. lookup_pdc t' a v = Hit x) \<and>  lookup_pdc t a v \<noteq>  lookup_pdc t' a v)  \<or>
      (lookup_pdc t' a v = Incon \<and> (\<exists>x\<in>t. lookup_pdc t a v = Hit x) ) \<or>
      ((\<exists>x\<in>t'. lookup_pdc t' a v = Hit x)  \<and> lookup_pdc t a v = Incon)\<or>
      (lookup_pdc t a v = Miss \<and> lookup_pdc t' a v = Incon)  \<or>
      (lookup_pdc t a v = Incon \<and> lookup_pdc t' a v = Miss)"
  apply (cases "lookup_pdc t a v"; cases "lookup_pdc t' a v"; clarsimp)
       apply (drule_tac t' = t' in lookup_asid_pdc_miss_implies_union_miss; simp)
      apply (drule_tac t' = t' in lookup_asid_pdc_miss_hit_implies_union_hit; simp)
  using lookup_in_asid_pdc apply blast
    apply (drule_tac t' = t and e = x3 in lookup_asid_pdc_miss_hit_implies_union_hit, simp)
    apply (simp add: sup_commute)
  using lookup_in_asid_pdc apply blast
  apply (rule)
  using lookup_in_asid_pdc apply blast
  apply (rule)
  using lookup_in_asid_pdc apply blast
  apply (clarsimp simp: lookup_def tagged_pdc_entry_set_def entry_set_def asid_of_pdc_def split:if_split_asm)
  by (safe; force)


lemma tagged_pdc_entry_set_hit_entry_range:
  "tagged_pdc_entry_set t a v = {e} \<Longrightarrow> (Some a, v) \<in> asid_range_of_pdc e \<or> (None, v) \<in> asid_range_of_pdc e"
  apply (clarsimp simp: tagged_pdc_entry_set_def entry_set_def asid_of_pdc_def asid_range_of_pdc_def   split:if_split_asm)
 by force  



lemma lookup_asid_pdc_hit_mis_hit:
  "\<lbrakk>lookup_pdc (t \<union> t') a v = Hit e ; lookup_pdc t' a v = Miss \<rbrakk> \<Longrightarrow> lookup_pdc t a v = Hit e"
  using lookup_asid_pdc_hit_union_cases' by force
 

lemma   lookup_asid_pdc_union_hit_hit_miss :
  "\<lbrakk>lookup_pdc (t \<union> t') a v = Hit e ;  \<forall>x\<in>t. lookup_pdc t a v \<noteq> Hit x\<rbrakk> \<Longrightarrow> lookup_pdc t a v = Miss"
  using lookup_asid_pdc_not_hit_miss lookup_in_asid_pdc by blast

lemma lookup_asid_pdc_hit_miss_or_hit :
  " lookup_pdc (t \<union> t') a v = Hit e \<and> e \<in> t  \<Longrightarrow> 
              lookup_pdc t' a v = Miss \<or> (lookup_pdc t' a v = Hit e)"
  using lookup_asid_pdc_union_hit_miss_hit by blast

lemma not_miss_incon_hit_asid_pdc:
  "lookup_pdc t a v \<noteq> Miss \<Longrightarrow> lookup_pdc t a v = Incon \<or> (\<exists>x\<in>t. lookup_pdc t a v = Hit x)"
  by (meson lookup_in_asid_pdc lookup_type.exhaust)
  


lemma  lookup_asid_pdc_hit_union_cases:
  "(\<exists>x\<in>(t \<union> t'). lookup_pdc (t \<union> t') a va = Hit x)  \<Longrightarrow>
      ((\<exists>x\<in>t. lookup_pdc t a va = Hit x) \<and> lookup_pdc t' a va = Miss)       \<or>
      ((\<exists>x\<in>t'. lookup_pdc t' a va = Hit x)  \<and> lookup_pdc t a va = Miss)      \<or>
      ((\<exists>x\<in>t. \<exists>x'\<in>t'.  lookup_pdc t a va = Hit x  \<and> lookup_pdc t' a va = Hit x' \<and>  x = x')) "
  by (metis lookup_asid_pdc_hit_union_cases' lookup_asid_pdc_not_hit_hit lookup_asid_pdc_union_hit_hit_miss lookup_in_asid_pdc lookup_type.distinct(3))


lemma lookup_asid_pdc_miss_union_equal:
  "lookup_pdc t' a v = Miss \<Longrightarrow> lookup_pdc (t \<union> t') a v = lookup_pdc t a v"
  apply (cases "lookup_pdc (t \<union> t') a v"; clarsimp)
    apply (drule lookup_asid_pdc_miss_union, simp)
   apply (drule union_asid_pdc_incon_cases, clarsimp)
  by (drule lookup_asid_pdc_hit_union_cases', clarsimp)

 

lemma lookup_asid_pdc_miss_union_miss_miss:
  "\<lbrakk>lookup_pdc t a v = Miss;  lookup_pdc t' a v = Miss\<rbrakk> \<Longrightarrow> 
           lookup_pdc (t \<union> t') a v = Miss"
  by (simp add: lookup_asid_pdc_miss_union_equal)


lemma  lookup_asid_pdc_incon_not_miss:
   "\<lbrakk> lookup_pdc (t \<union> t') a v = Incon ; lookup_pdc t' a v = Miss\<rbrakk> \<Longrightarrow> lookup_pdc t a v = Incon"
  by (simp add: lookup_asid_pdc_miss_union_equal)
  

lemma lookup_asid_pdc_hit_diff_union_incon:
  "\<lbrakk>lookup_pdc t a v = Hit e ; lookup_pdc t' a v = Hit e' ; e \<noteq> e'\<rbrakk> \<Longrightarrow> lookup_pdc (t \<union> t') a v = Incon"
  apply (clarsimp simp: lookup_def tagged_pdc_entry_set_def entry_set_def asid_of_pdc_def asid_range_of_pdc_def  split: if_split_asm)
 by (metis (no_types, lifting) mem_Collect_eq singletonD singletonI)
 

lemma lookup_asid_pdc_miss_union_hit_intro:
  "\<lbrakk>lookup_pdc t a v = Miss;  lookup_pdc t' a v = Hit e\<rbrakk> \<Longrightarrow> 
           lookup_pdc (t \<union> t') a v = Hit e"
  by (metis lookup_asid_pdc_miss_union_equal sup.commute)

lemma lookup_asid_pdc_miss_union_hit_intro':
  "\<lbrakk> lookup_pdc t a v = Hit e ; lookup_pdc t' a v = Miss\<rbrakk> \<Longrightarrow> 
           lookup_pdc (t \<union> t') a v = Hit e"
  by (metis inf_sup_aci(5) lookup_asid_pdc_miss_union_hit_intro)
 

lemma lookup_asid_pdc_union_hit_hit:
  "\<lbrakk> lookup_pdc t a v = Hit e ; lookup_pdc t' a v = Hit e\<rbrakk> \<Longrightarrow> 
           lookup_pdc (t \<union> t') a v = Hit e"
  apply (cases "lookup_pdc (t \<union> t') a v"; clarsimp)
  apply (drule lookup_asid_pdc_miss_union, simp)
   apply (drule union_asid_pdc_incon_cases, clarsimp)
  by (drule lookup_asid_pdc_hit_union_cases', clarsimp)
  


lemma asid_pdc_not_miss_incon_hit':
  "lookup_pdc t a v = Incon \<or> (\<exists>e\<in>t. lookup_pdc t a v = Hit e) \<Longrightarrow> lookup_pdc t a v \<noteq> Miss "
  by (clarsimp simp: lookup_def tagged_pdc_entry_set_def entry_set_def asid_of_pdc_def split: if_split_asm)


lemma lookup_asid_pdc_incon_minus:
  "lookup_pdc (t - t') a v  = Incon  \<Longrightarrow> lookup_pdc t a v = Incon"
  apply (subgoal_tac "t - t' \<subseteq> t")
   apply (frule_tac a = a and v = v in asid_pdc_mono)
   apply clarsimp
  by blast



lemma  lookup_asid_pdc_hit_entry_range_asid_tags:
  "lookup_pdc t a v = Hit e \<Longrightarrow> (Some a, v) \<in> asid_range_of_pdc e \<or> (None, v) \<in> asid_range_of_pdc e"
  apply (clarsimp simp: lookup_def  tagged_pdc_entry_set_def entry_set_def asid_of_pdc_def  asid_range_of_pdc_def  split:if_split_asm)
  by force



lemma  lookup_asid_pdc_hit_asid:
  "lookup_pdc t a v = Hit e \<Longrightarrow> Some a = asid_of_pdc e \<or> None =  asid_of_pdc e"
  apply (clarsimp simp: lookup_def  tagged_pdc_entry_set_def entry_set_def asid_of_pdc_def asid_range_of_pdc_def  split:if_split_asm)
  by force


lemma  lookup_asid_pdc_hit_incon_minus:
  "\<lbrakk>lookup_pdc (t - t') a v = Hit e\<rbrakk>
                \<Longrightarrow> lookup_pdc t a v = Hit e \<or> lookup_pdc t a v = Incon"
  apply (clarsimp simp: lookup_def  tagged_pdc_entry_set_def entry_set_def asid_of_pdc_def asid_range_of_pdc_def  split:if_split_asm)
  by force


lemma  lookup_asid_pdc_not_miss_varange:
  "lookup_pdc (t - (\<Union>v\<in>vset. {e \<in> t. v \<in> range_of e})) a v \<noteq> Miss \<Longrightarrow>
      v \<notin> vset"
  by (clarsimp simp: lookup_def tagged_pdc_entry_set_def entry_set_def asid_of_pdc_def asid_range_of_pdc_def split:if_split_asm)


lemma  lookup_asid_pdc_minus_union:
  "\<lbrakk>lookup_pdc t' a v = Miss; lookup_pdc  t'' a v = Miss \<rbrakk> \<Longrightarrow>
      lookup_pdc (t - t' \<union> t'') a v = lookup_pdc t a v"
  by (metis Un_Diff_cancel2 lookup_asid_pdc_miss_union_equal sup_commute)
 


lemma  lookup_asid_pdc_minus_same:
  "\<lbrakk>lookup_pdc t' a v = Miss \<rbrakk> \<Longrightarrow> lookup_pdc (t - t') a v = lookup_pdc t a v"
  by (metis Un_Diff_cancel2 lookup_asid_pdc_miss_union_equal)

lemma  lookup_asid_pdc_minus_hit':
  "\<lbrakk>lookup_pdc (t - t') a v = Hit e ; lookup_pdc t' a v = Miss \<rbrakk> \<Longrightarrow> lookup_pdc t a v = Hit e"
  by (metis Un_Diff_cancel2 lookup_asid_pdc_hit_mis_hit lookup_asid_pdc_miss_union_hit_intro')


 
lemma  lookup_pdc_minus_union':
  "\<lbrakk>lookup_pdc t' a v = Miss \<rbrakk> \<Longrightarrow>
      lookup_pdc (t - t' \<union> t'') a v = lookup_pdc (t \<union> t'') a v"
proof -
  assume "lookup_pdc t' a v = Miss"
  then have "\<forall>T Ta. lookup_pdc (Ta \<union> T) a v = lookup_pdc (Ta \<union> (T \<union> t')) a v"
    by (metis Un_assoc lookup_asid_pdc_miss_union_equal)
  then show ?thesis
    by (metis (no_types) Un_Diff_cancel2 Un_commute)
qed
  


lemma lookup_asid_pdc_asid_entry_miss:
  "a \<noteq> a' \<Longrightarrow> lookup_pdc {e \<in> t. asid_of_pdc e = Some a} a' v = Miss"
  by (clarsimp simp: lookup_def tagged_pdc_entry_set_def entry_set_def asid_of_pdc_def asid_range_of_pdc_def split: if_split_asm)
 

lemma lookup_pdc_minus_smaller_order:
  "lookup_pdc (t - t') a v \<le> lk \<Longrightarrow> lookup_pdc (t - t'' - t') a v \<le> lk"
  apply (cases lk; clarsimp)
  apply (metis Diff_mono asid_pdc_mono inf_sup_ord(3) leq_Miss set_double_minus subset_refl)
  by (metis (no_types, hide_lams) Diff_mono asid_pdc_mono order.trans set_double_minus subset_refl sup_ge1)


lemma lookup_pdc_union_minus_equal:
  "lookup_pdc b a v = Miss \<Longrightarrow>
     lookup_pdc (a' \<union> b \<union> c - d) a v = lookup_pdc (a' \<union> c - d) a v"
  apply (case_tac "lookup_pdc (a' \<union> b \<union> c - d) a v"; clarsimp)
  subgoal
  proof -
    assume "lookup_pdc (a' \<union> b \<union> c - d) a v = Miss"
    then have "\<exists>T. lookup_pdc (a' \<union> (c \<union> T) - d) a v = Miss"
      by (metis (no_types) Un_left_commute sup_commute)
    then show "Miss = lookup_pdc (a' \<union> c - d) a v"
      by (metis (no_types) Un_Diff lookup_asid_pdc_miss_union sup_assoc)
  qed
  subgoal
proof -
  assume a1: "lookup_pdc b a v = Miss"
  assume a2: "lookup_pdc (a' \<union> b \<union> c - d) a v = Incon"
  have f3: "\<forall>P Pa Pb. (P::pdc_entry set) \<union> Pa - Pb = P \<union> (Pa - Pb) - Pb"
    by (simp add: Un_Diff)
  have "lookup_pdc (b \<union> (a' \<union> c) - d) a v = Incon"
    using a2 by (metis Un_commute sup_assoc)
  then show "Incon = lookup_pdc (a' \<union> c - d) a v"
    using f3 a1 by (metis (no_types) Un_commute lookup_asid_pdc_incon_minus lookup_asid_pdc_incon_not_miss)
qed
  apply (case_tac " lookup_pdc d a v")
  subgoal
proof -
  fix x3 :: pdc_entry
  assume a1: "lookup_pdc b a v = Miss"
  assume a2: "lookup_pdc (a' \<union> b \<union> c - d) a v = Hit x3"
  assume a3: "lookup_pdc d a v = Miss"
  then have "lookup_pdc (a' \<union> (b \<union> c) - d \<union> d) a v = Hit x3"
    using a2 by (metis lookup_asid_pdc_miss_union_hit_intro' sup_commute sup_left_commute)
  then have "lookup_pdc (b \<union> (a' \<union> (c \<union> d))) a v = Hit x3"
    by (simp add: sup_commute sup_left_commute)
  then have "lookup_pdc (a' \<union> (c \<union> d)) a v = Hit x3"
    using a1 by (metis (no_types) lookup_asid_pdc_hit_mis_hit sup_commute)
  then have "lookup_pdc (d \<union> (a' \<union> c)) a v = Hit x3"
    by (simp add: sup_commute sup_left_commute)
  then show "Hit x3 = lookup_pdc (a' \<union> c - d) a v"
    using a3 by (metis (no_types) Un_Diff_cancel lookup_asid_pdc_hit_mis_hit sup_commute)
qed
   apply (case_tac "lookup_pdc (a' \<union> c - d) a v"; clarsimp)
   apply (case_tac "lookup_pdc (a' \<union> c) a v")
     apply (metis less_eq_lookup_type lookup_asid_pdc_hit_incon_minus 
   lookup_asid_pdc_miss_implies_union_miss lookup_type.distinct(5) lookup_type.simps(3) lookup_type.simps(5) sup.commute sup.left_commute)
      apply (clarsimp simp: lookup_def tagged_pdc_entry_set_def entry_set_def  split:if_split_asm)
      apply (safe ; force) [1]                                    
     apply (clarsimp simp: lookup_def tagged_pdc_entry_set_def entry_set_def  split:if_split_asm)
  apply (safe ; force) [1]
  apply (metis Un_Diff Un_upper2 lookup_asid_pdc_incon_subset lookup_type.distinct(5) sup_commute sup_left_commute)
  apply (metis Hits_le Un_Diff Un_upper2 asid_pdc_mono sup_commute sup_left_commute)

  apply (case_tac "lookup_pdc (a' \<union> c) a v")
    apply (cases "lookup_pdc (a' \<union> c - d) a v"; clarsimp)
      apply (clarsimp simp: lookup_def tagged_pdc_entry_set_def entry_set_def  split:if_split_asm)
      apply (safe ; force) [1]         
     apply (clarsimp simp: lookup_def tagged_pdc_entry_set_def entry_set_def  split:if_split_asm)
     apply (safe ; force) [1]         
    apply (clarsimp simp: lookup_def tagged_pdc_entry_set_def entry_set_def  split:if_split_asm)
    apply (safe ; force) [1]     
   apply (cases "lookup_pdc (a' \<union> c - d) a v"; clarsimp)
     apply (clarsimp simp: lookup_def tagged_pdc_entry_set_def entry_set_def  split:if_split_asm)
     apply (safe ; force) [1]
  apply (metis (no_types) Un_Diff lookup_asid_pdc_incon_subset lookup_type.distinct(5) sup_assoc sup_commute sup_ge1)
  apply (metis Hits_le Un_Diff Un_upper2 asid_pdc_mono sup_commute sup_left_commute)
proof -
  fix x3 :: pdc_entry and x3a :: pdc_entry and x3b :: pdc_entry
  assume a1: "lookup_pdc (a' \<union> b \<union> c - d) a v = Hit x3"
  assume a2: "lookup_pdc b a v = Miss"
  have f3: "\<forall>P w Pa a Pb. lookup_pdc (P \<union> Pb - Pa) w a = lookup_pdc (P - Pa) w a \<or> lookup_pdc (Pb - Pa) w a \<noteq> Miss"
    by (metis (full_types) Un_Diff lookup_asid_pdc_miss_union_equal)
  have f4: "\<forall>P. lookup_pdc (b - P) a v \<le> Miss"
    using a2 by (metis (full_types) Diff_subset asid_pdc_mono)
  have "lookup_pdc (a' \<union> (c \<union> b) - d) a v = Hit x3"
    using a1 by (metis sup_assoc sup_commute)
  then show "Hit x3 = lookup_pdc (a' \<union> c - d) a v"
    using f4 f3 by (metis (no_types) less_eq_lookup_type lookup_type.simps(3) sup_assoc)
qed


(* lookup_pdc_union_minus_equal' is being used with these variables later *)
lemma lookup_pdc_union_minus_equal':
  " lookup_pdc t' a v = Miss \<Longrightarrow>
     lookup_pdc (t \<union> t' \<union> t''' - t'') a v = lookup_pdc (t \<union> t''' - t'') a v"
  by (clarsimp simp: lookup_pdc_union_minus_equal)




theorem asid_pdc_entry_range_single_element':
  " {E \<in> the ` {e \<in> t. \<not> is_fault e}. (a, v) \<in> asid_range_of_pdc E} = {x} \<Longrightarrow> 
       (a, v) \<in> asid_range_of_pdc x \<and> \<not> is_fault (Some x) 
         \<and> (\<forall>y\<in>the ` {e \<in> t. \<not> is_fault e}. y\<noteq>x \<and> 
               \<not> is_fault (Some y) \<longrightarrow> (a, v) \<notin> asid_range_of_pdc y)" 
  apply safe
    apply force
   apply (clarsimp simp: is_fault_def)
  by force


lemma asid_pdc_entry_range_asid_entry:
  "(Some a, v) \<in> asid_range_of_pdc e \<Longrightarrow> asid_of_pdc e = Some a"
  by (clarsimp simp: asid_range_of_pdc_def)



theorem  entry_pdc_set_va_set:
  "(tagged_pdc_entry_set t a v = {}) = ((Some a, v) \<notin> tag_vadr_pdc t \<and> (None, v) \<notin> tag_vadr_pdc t)"
  apply (clarsimp simp: tag_vadr_pdc_def tagged_pdc_entry_set_def asid_range_of_pdc_def entry_set_def asid_of_pdc_def)
  apply safe
  by force+



lemma lookup_asid_pdc_hit_mis_hit':
  "\<lbrakk>lookup_pdc (t \<union> t') a v = Hit e ; lookup_pdc t a v = Miss \<rbrakk> \<Longrightarrow> lookup_pdc t' a v = Hit e"
  using lookup_asid_pdc_hit_union_cases' by force




(* global and non_global entries *)


definition
  non_global_entries_pdc :: "pdc \<Rightarrow> pdc"
where
  "non_global_entries_pdc t =  {e\<in>t. \<exists>a. asid_of_pdc e = Some a}"


definition
  global_entries_pdc :: "pdc \<Rightarrow> pdc"
where
  "global_entries_pdc t =  {e\<in>t. asid_of_pdc e = None}"





lemma pdc_global_non_global_union:
  "t = non_global_entries_pdc t \<union> global_entries_pdc t"
  apply (clarsimp simp:  non_global_entries_pdc_def global_entries_pdc_def)
  using UnI1 by auto


lemma glb_pdc_subset:
  "global_entries_pdc t \<subseteq> t"
  by (clarsimp simp: global_entries_pdc_def)  

lemma non_glb_pdc_subset:
  "non_global_entries_pdc t \<subseteq> t"
  by (clarsimp simp: non_global_entries_pdc_def)


lemma global_entries_union_pdc:
  "global_entries_pdc (tlb \<union> tlb') = global_entries_pdc tlb \<union> global_entries_pdc tlb'"
  apply (clarsimp simp: global_entries_pdc_def)
  by blast


lemma non_global_to_global_pdc:
  "non_global_entries_pdc t = t - global_entries_pdc t"
  apply (clarsimp simp: non_global_entries_pdc_def global_entries_pdc_def)
  apply safe
  by simp

lemma lookup_global_incon_for_asids_pdc:
  "lookup_pdc (global_entries_pdc t) a v = Incon \<Longrightarrow> lookup_pdc (global_entries_pdc t) a' v = Incon"
  apply (case_tac "a = a'"; clarsimp?)
  apply (case_tac "lookup_pdc (global_entries_pdc t) a' v"; clarsimp?)
   apply (clarsimp simp: global_entries_pdc_def lookup_def tagged_pdc_entry_set_def entry_set_def asid_of_pdc_def split: if_split_asm)
   apply force
 apply (clarsimp simp: global_entries_pdc_def lookup_def tagged_pdc_entry_set_def entry_set_def asid_of_pdc_def split: if_split_asm)
  by force


lemma lookup_global_same_for_asids_pdc:
  "lookup_pdc (global_entries_pdc t) a v = lookup_pdc (global_entries_pdc t) a' v"
  apply (case_tac "a = a'"; clarsimp?)
  apply (case_tac "lookup_pdc (global_entries_pdc t) a' v"; clarsimp?)
   apply (clarsimp simp: global_entries_pdc_def lookup_def tagged_pdc_entry_set_def entry_set_def asid_of_pdc_def split: if_split_asm)
   apply force
 apply (clarsimp simp: global_entries_pdc_def lookup_def tagged_pdc_entry_set_def entry_set_def asid_of_pdc_def split: if_split_asm)
   apply (safe; force) [1]
 apply (clarsimp simp: global_entries_pdc_def lookup_def tagged_pdc_entry_set_def entry_set_def asid_of_pdc_def split: if_split_asm)
  by (safe; force) [1]


lemma lookup_global_incon_incon_pdc:
  " lookup_pdc (global_entries_pdc t) a v = Incon \<Longrightarrow> lookup_pdc t a v = Incon"
  using glb_pdc_subset lookup_asid_pdc_incon_subset by blast


lemma lookup_global_incon_incon_pdc':
  "lookup_pdc (global_entries_pdc t) a v = Incon \<Longrightarrow>  lookup_pdc t a' v = Incon"
  apply (case_tac "a = a'"; (clarsimp simp: lookup_global_incon_incon_pdc)?)
  apply (subgoal_tac "lookup_pdc (global_entries_pdc t) a' v = Incon")
   prefer 2
   apply (clarsimp simp: lookup_global_incon_for_asids_pdc)
  by (clarsimp simp: lookup_global_incon_incon_pdc)
  



lemma  lookup_incon_global_vset_elem:
   "\<lbrakk> {v. lookup_pdc t a v = Incon} \<subseteq> vset;
               lookup_pdc (global_entries_pdc t) a' v = Incon  \<rbrakk> \<Longrightarrow>  v \<in> vset"
  apply (subgoal_tac " lookup_pdc t a v = Incon ")
   apply blast
  using lookup_global_incon_incon_pdc' by blast


lemma lookup_global_hit_asid_of_none_pdc:
  "lookup_pdc (global_entries_pdc t) a v = Hit e \<Longrightarrow> asid_of_pdc e = None"
  apply (clarsimp simp: global_entries_pdc_def lookup_def tagged_pdc_entry_set_def entry_set_def asid_of_pdc_def split: if_split_asm)
  by force



lemma lookup_eq_union_global_non_global_pdc:
  "lookup_pdc t a v = lookup_pdc (global_entries_pdc t \<union> non_global_entries_pdc t) a v"
  apply (case_tac "lookup_pdc (global_entries_pdc t \<union> non_global_entries_pdc t) a v"; clarsimp)
    apply (clarsimp simp: global_entries_pdc_def non_global_entries_pdc_def lookup_def tagged_pdc_entry_set_def entry_set_def asid_of_pdc_def split: if_split_asm)
    apply  (safe; force) [1]
   apply (clarsimp simp: global_entries_pdc_def non_global_entries_pdc_def lookup_def tagged_pdc_entry_set_def entry_set_def asid_of_pdc_def split: if_split_asm)
   apply  (safe; force) [1]
  apply (clarsimp simp: global_entries_pdc_def non_global_entries_pdc_def lookup_def tagged_pdc_entry_set_def entry_set_def asid_of_pdc_def split: if_split_asm)
  by  (safe; force) [1]      

lemma lookup_global_hit_lookup'_pdc:
  "lookup_pdc (global_entries_pdc t) a v = Hit e
       \<Longrightarrow> lookup' (global_entries_pdc t) v = Hit e"
  apply (clarsimp simp: global_entries_pdc_def lookup_def tagged_pdc_entry_set_def entry_set_def asid_of_pdc_def split: if_split_asm)
  apply safe
  by force+

lemma lookup''_global_incon_lookup'_pdc:
  "lookup_pdc (global_entries_pdc t) a v = Incon
       \<Longrightarrow> lookup' (global_entries_pdc t) v = Incon"
  apply (clarsimp simp: global_entries_pdc_def lookup_def tagged_pdc_entry_set_def entry_set_def asid_of_pdc_def split: if_split_asm)
  apply safe
  by force+

lemma interesting_lemma_pdc:
  "\<lbrakk>lookup_pdc (non_global_entries_pdc t) a v = Hit x; lookup' (global_entries_pdc t')  v = Hit x' \<rbrakk> \<Longrightarrow>
    x' \<noteq> x"
  apply (subgoal_tac "asid_of_pdc x' \<noteq> asid_of_pdc x")
  apply clarsimp
  apply (clarsimp simp: global_entries_pdc_def non_global_entries_pdc_def 
                   lookup_def tagged_pdc_entry_set_def entry_set_def asid_of_pdc_def split: if_split_asm)
  by (metis (mono_tags, lifting) asid_of_pdc_def emptyE insert_iff mem_Collect_eq option.distinct(1))


lemma lookup_global_asid_of_none_pdc:
  "lookup' (global_entries_pdc t) v = Hit e \<Longrightarrow> asid_of_pdc e = None"
  apply (clarsimp simp: global_entries_pdc_def lookup_def tagged_pdc_entry_set_def entry_set_def asid_of_pdc_def split: if_split_asm)
  by force
  
lemma lookup_non_global_hit_asid_of_not_none_pdc:
  "lookup_pdc (non_global_entries_pdc t) a v = Hit e \<Longrightarrow> asid_of_pdc e \<noteq> None"
  apply (clarsimp simp: non_global_entries_pdc_def lookup_def tagged_pdc_entry_set_def entry_set_def asid_of_pdc_def split: if_split_asm)
  by force


                                                          
lemma lookup_miss_minus_miss_pdc:
  "lookup_pdc t a v = Miss \<Longrightarrow> lookup_pdc (t - t') a v = Miss"
  by (clarsimp simp: lookup_def tagged_pdc_entry_set_def entry_set_def asid_of_pdc_def split: if_split_asm)
  

lemma lookup_miss_minus_miss_hit_pdc:
  "lookup_pdc t a v = Hit e \<Longrightarrow> lookup_pdc (t - t') a v = Miss \<or> lookup_pdc (t - t') a v = Hit e"
  by (metis Diff_subset asid_pdc_mono less_eq_lookup_type lookup_type.simps(7))

lemma pdc_non_global_non_global:
  " a \<union> b = non_global_entries_pdc a \<union> non_global_entries_pdc b \<union> (global_entries_pdc a \<union> global_entries_pdc b)"
  apply (clarsimp simp: non_global_entries_pdc_def global_entries_pdc_def)
  apply safe [1]
  by force+

lemma tagged_entry_set_to_entry_set_pdc:
  "tagged_pdc_entry_set (global_entries_pdc t) a v = entry_set (global_entries_pdc t) v"
  apply (clarsimp simp: global_entries_pdc_def tagged_pdc_entry_set_def entry_set_def asid_of_pdc_def)
  by blast

lemma lookup_global_miss_entry_set_empty_pdc:
  "lookup_pdc (global_entries_pdc t) a v = Miss \<Longrightarrow>
    entry_set (global_entries_pdc t) v = {}"
  apply (subgoal_tac "lookup' (global_entries_pdc t)  v = Miss")
   apply (clarsimp simp: lookup_def split: if_split_asm)
  apply (clarsimp simp: global_entries_pdc_def lookup_def tagged_pdc_entry_set_def entry_set_def asid_of_pdc_def split: if_split_asm)
  apply safe
  by force+



lemma addr_set_minus_non_global_lookup_miss:
  "v \<in> vset \<Longrightarrow> lookup'' (non_global_entries (t - (\<Union>v\<in>vset. {e \<in> t. v \<in> range_of e}))) a v = Miss"
  apply (subgoal_tac "tagged_entry_set (non_global_entries (t - (\<Union>v\<in>vset. {e \<in> t. v \<in> range_of e}))) a v = {}")
   apply (clarsimp simp: lookup_def)
  by (clarsimp simp: non_global_entries_def tagged_entry_set_def entry_set_def) 



lemma non_global_entries_union:
  "non_global_entries (tlb \<union> tlb') = non_global_entries tlb \<union> non_global_entries tlb'"
  apply (clarsimp simp: non_global_entries_def)
  by blast

lemma non_global_entries_sub:
  "non_global_entries (tlb - tlb') = non_global_entries tlb - non_global_entries tlb'"
  apply (clarsimp simp: non_global_entries_def)
  by blast

lemma non_global_entries_union_pdc:
  "non_global_entries_pdc (tlb \<union> tlb') = non_global_entries_pdc tlb \<union> non_global_entries_pdc tlb'"
  apply (clarsimp simp: non_global_entries_pdc_def)
  by blast

lemma non_global_entries_sub_pdc:
  "non_global_entries_pdc (tlb - tlb') = non_global_entries_pdc tlb - non_global_entries_pdc tlb'"
  apply (clarsimp simp: non_global_entries_pdc_def)
  by blast

lemma addr_set_minus_non_global_lookup_miss_pdc:
  "v \<in> vset \<Longrightarrow> lookup_pdc (non_global_entries_pdc (t - (\<Union>v\<in>vset. {e \<in> t. v \<in> range_of e}))) a v = Miss"
  apply (subgoal_tac "tagged_pdc_entry_set (non_global_entries_pdc (t - (\<Union>v\<in>vset. {e \<in> t. v \<in> range_of e}))) a v = {}")
   apply (clarsimp simp: lookup_def)
  by (clarsimp simp: non_global_entries_pdc_def tagged_pdc_entry_set_def entry_set_def) 




lemma lookup_sub_asid_of_hit_global:
  "lookup'' (t - {e \<in> t. asid_of e = Some a}) a v = Hit e \<Longrightarrow>
        lookup'' (global_entries t) a v = Hit e"
  apply (clarsimp simp: global_entries_def lookup_def tagged_entry_set_def entry_set_def 
                  split: if_split_asm option.splits)
  by (safe; force)

lemma lookup_sub_asid_of_incon_global:
  "lookup'' (t - {e \<in> t. asid_of e = Some a}) a v = Incon \<Longrightarrow>
        lookup'' (global_entries t) a v = Incon"
  apply (clarsimp simp: global_entries_def lookup_def tagged_entry_set_def entry_set_def 
                  split: if_split_asm option.splits)
  by (safe; force)

                                                        
lemma lookup_minus_miss_sncd_miss:
  "\<lbrakk> lookup'' (t - t') a v = Miss; lookup'' t' a v = Miss \<rbrakk> \<Longrightarrow> lookup'' t  a v = Miss"
  apply (clarsimp simp: lookup_def tagged_entry_set_def entry_set_def split: if_split_asm)
  by (safe; force)


lemma lookup_union_miss_sncd_miss:
  "\<lbrakk> lookup'' (t \<union> t') a v = Miss; lookup'' t' a v = Miss \<rbrakk> \<Longrightarrow> lookup'' t  a v = Miss"
  apply (clarsimp simp: lookup_def tagged_entry_set_def entry_set_def split: if_split_asm)
  by (safe; force)


lemma asid_unequal_lookup_non_global_asid_flush_pt_walk:
  "a' \<noteq> a \<Longrightarrow>
       lookup'' (non_global_entries (t - {e \<in> t. asid_of e = Some a} \<union> the ` {e \<in> range (pt_walk a m r). \<not> is_fault e})) a' v =
           lookup'' (non_global_entries t) a' v"
  apply (clarsimp simp: non_global_entries_union)
  apply (subgoal_tac "lookup'' (non_global_entries (the ` {e \<in> range (pt_walk a m r). \<not> is_fault e})) a' v = Miss")
   prefer 2
   apply (rule asid_unequal_lookup_pt_walk_miss, simp)
  apply (cases "lookup'' (non_global_entries (t - {e \<in> t. asid_of e = Some a}) \<union> non_global_entries (the ` {e \<in> range (pt_walk a m r). \<not> is_fault e})) a' v"; clarsimp?)
    apply (subgoal_tac "lookup'' (non_global_entries (t - {e \<in> t. asid_of e = Some a})) a' v = Miss")
     apply (clarsimp simp: non_global_entries_sub)
     apply (subgoal_tac "lookup'' (non_global_entries {e \<in> t. asid_of e = Some a}) a' v = Miss")
      apply (drule lookup_minus_miss_sncd_miss, simp, simp)
     apply (clarsimp simp: non_global_entries_def lookup_def tagged_entry_set_def entry_set_def split: if_split_asm)
    apply (drule lookup_union_miss_sncd_miss, simp, simp)
   apply (drule lookup_asid_tlb_incon_not_miss, simp)
   apply (clarsimp simp: non_global_entries_sub)
  using lookup_asid_tlb_incon_minus apply force
  apply (drule lookup_asid_tlb_hit_mis_hit, simp)
  apply (clarsimp simp: non_global_entries_sub)
  apply (subgoal_tac "lookup'' (non_global_entries {e \<in> t. asid_of e = Some a}) a' v = Miss")
   apply (frule lookup_asid_tlb_minus_hit', simp, simp)
  by (clarsimp simp: non_global_entries_def lookup_def tagged_entry_set_def entry_set_def split: if_split_asm)

lemma asid_unequal_lookup_minus_non_global_hit_hit:
  "\<lbrakk>a \<noteq> a'; lookup'' (t - {e \<in> t. asid_of e = Some a}) a' v = Hit e\<rbrakk>
       \<Longrightarrow> lookup'' t a' v = Hit e"
  apply (subgoal_tac "lookup'' ({e \<in> t. asid_of e = Some a}) a' v = Miss")
   prefer 2
   apply (subgoal_tac "tagged_entry_set ({e \<in> t. asid_of e = Some a}) a' v = {}")
    apply (clarsimp simp: lookup_def split: if_split_asm)  
   apply (clarsimp simp:  tagged_entry_set_def entry_set_def split: if_split_asm)
  by (drule lookup_asid_tlb_minus_hit', simp, simp)


lemma lookup_non_global_entries_sub_miss :
  "lookup'' (non_global_entries (fst(sat_tlb s) - {e \<in> fst(sat_tlb s). asid_of e = Some a})) a v = Miss"
  apply (subgoal_tac "tagged_entry_set (non_global_entries (fst(sat_tlb s) - {e \<in> fst(sat_tlb s). asid_of e = Some a})) a v  = {}")
   apply (clarsimp simp: lookup_def )
  by (clarsimp simp: non_global_entries_def lookup_def tagged_entry_set_def entry_set_def split: if_split_asm)



lemma lookup_sub_asid_of_hit_global_pdc:
  "lookup_pdc (t - {e \<in> t. asid_of_pdc e = Some a}) a v = Hit e \<Longrightarrow>
        lookup_pdc (global_entries_pdc t) a v = Hit e"
  apply (clarsimp simp: global_entries_pdc_def lookup_def tagged_pdc_entry_set_def entry_set_def 
                  split: if_split_asm option.splits)
  by (safe; force)


lemma lookup_sub_asid_of_incon_global_pdc:
  "lookup_pdc (t - {e \<in> t. asid_of_pdc e = Some a}) a v = Incon \<Longrightarrow>
        lookup_pdc (global_entries_pdc t) a v = Incon"
  apply (clarsimp simp: global_entries_pdc_def lookup_def tagged_pdc_entry_set_def entry_set_def 
                  split: if_split_asm option.splits)
  by (safe; force)


lemma lookup_minus_miss_sncd_miss_pdc:
  "\<lbrakk> lookup_pdc (t - t') a v = Miss; lookup_pdc t' a v = Miss \<rbrakk> \<Longrightarrow> lookup_pdc t  a v = Miss"
  apply (clarsimp simp: lookup_def tagged_pdc_entry_set_def entry_set_def split: if_split_asm)
  by (safe; force)


lemma lookup_union_miss_sncd_miss_pdc:
  "\<lbrakk> lookup_pdc (t \<union> t') a v = Miss; lookup_pdc t' a v = Miss \<rbrakk> \<Longrightarrow> lookup_pdc t  a v = Miss"
  apply (clarsimp simp: lookup_def tagged_pdc_entry_set_def entry_set_def split: if_split_asm)
  by (safe; force)




lemma asid_unequal_lookup_minus_non_global_hit_hit_pdc:
  "\<lbrakk>a \<noteq> a'; lookup_pdc (t - {e \<in> t. asid_of_pdc e = Some a}) a' v = Hit e\<rbrakk>
       \<Longrightarrow> lookup_pdc t a' v = Hit e"
  apply (subgoal_tac "lookup_pdc ({e \<in> t. asid_of_pdc e = Some a}) a' v = Miss")
   prefer 2
   apply (subgoal_tac "tagged_pdc_entry_set ({e \<in> t. asid_of_pdc e = Some a}) a' v = {}")
    apply (clarsimp simp: lookup_def split: if_split_asm)  
   apply (clarsimp simp:  tagged_pdc_entry_set_def entry_set_def split: if_split_asm)
  by (drule lookup_asid_pdc_minus_hit', simp, simp)



lemma lookup_non_global_entries_sub_miss_pdc:
  "lookup_pdc (non_global_entries_pdc (snd(sat_tlb s) - {e \<in> snd(sat_tlb s). asid_of_pdc e = Some a})) a v = Miss"
  apply (subgoal_tac "tagged_pdc_entry_set (non_global_entries_pdc (snd(sat_tlb s) - {e \<in> snd(sat_tlb s). asid_of_pdc e = Some a})) a v  = {}")
   apply (clarsimp simp: lookup_def )
  by (clarsimp simp: non_global_entries_pdc_def lookup_def tagged_pdc_entry_set_def entry_set_def split: if_split_asm)



lemma vaddr_elem_lookup_hit_global_entries_hit:
  "\<lbrakk> v \<in> vset ;  lookup'' (t - (\<Union>x\<in>vset. {e \<in> t. x \<in> range_of e \<and> asid_of e = Some a})) a v = Hit e\<rbrakk>  \<Longrightarrow>
     lookup' (global_entries t) v = Hit e"
  apply (case_tac " lookup' (global_entries t) v"; clarsimp?)
    apply (clarsimp simp: global_entries_def lookup_def tagged_entry_set_def entry_set_def split: if_split_asm option.splits)
    apply (safe ; force) [1]
   defer
   apply (clarsimp simp: global_entries_def lookup_def tagged_entry_set_def entry_set_def split: if_split_asm option.splits)
   apply (safe ; force) [1]
  apply (clarsimp simp: global_entries_def lookup_def tagged_entry_set_def entry_set_def split: if_split_asm option.splits)
  apply safe 
    apply force
   apply force
proof -
  fix x :: "tlb_entry" and xa :: "tlb_entry"
  assume a1: "v \<in> vset"
  assume a2: "\<forall>x. {e \<in> t. asid_of e = None \<and> v \<in> range_of e} \<noteq> {x}"
  assume a3: "{e \<in> t. (e \<in> t \<longrightarrow> (\<forall>x\<in>vset. x \<notin> range_of e) \<or> asid_of e \<noteq> Some a) \<and> v \<in> range_of e \<and> (asid_of e = None \<or> asid_of e = Some a)} = {e}"
  assume "asid_of x \<noteq> Some a"
  assume "asid_of x = None"
  have "{ta \<in> t. (ta \<in> t \<longrightarrow> (\<forall>a. a \<in> vset \<longrightarrow> a \<notin> range_of ta) \<or> asid_of ta \<noteq> Some a) \<and> v \<in> range_of ta \<and> (asid_of ta = None \<or> asid_of ta = Some a)} \<noteq> {ta \<in> t. asid_of ta = None \<and> v \<in> range_of ta}"
    using a3 a2 by (metis (no_types))
  then show False
    using a1 by force
qed

  
  

lemma vaddr_elem_lookup_incon_global_entries_incon:
  "\<lbrakk> v \<in> vset ;  lookup'' (t - (\<Union>x\<in>vset. {e \<in> t. x \<in> range_of e \<and> asid_of e = Some a})) a v = Incon\<rbrakk>  \<Longrightarrow>
     lookup' (global_entries t) v = Incon"
  apply (case_tac " lookup' (global_entries t) v"; clarsimp?)
    apply (clarsimp simp: global_entries_def lookup_def tagged_entry_set_def entry_set_def split: if_split_asm option.splits)
    apply (safe ; force) [1]
   defer
   apply (clarsimp simp: global_entries_def lookup_def tagged_entry_set_def entry_set_def split: if_split_asm option.splits)
  by (safe ; force) [1]
 

lemma vaddr_elem_lookup_hit_global_entries_hit_pdc:
  "\<lbrakk> v \<in> vset ;  lookup_pdc (t - (\<Union>x\<in>vset. {e \<in> t. x \<in> range_of e \<and> asid_of_pdc e = Some a})) a v = Hit e\<rbrakk>  \<Longrightarrow>
     lookup' (global_entries_pdc t) v = Hit e"
  apply (case_tac " lookup' (global_entries_pdc t) v"; clarsimp?)
    apply (clarsimp simp: global_entries_pdc_def lookup_def tagged_pdc_entry_set_def entry_set_def split: if_split_asm option.splits)
    apply (safe ; force) [1]
   defer
   apply (clarsimp simp: global_entries_pdc_def lookup_def tagged_pdc_entry_set_def entry_set_def split: if_split_asm option.splits)
   apply (safe ; force) [1]
  apply (clarsimp simp: global_entries_pdc_def lookup_def tagged_pdc_entry_set_def entry_set_def split: if_split_asm option.splits)
  apply safe 
    apply force
   apply force
proof -
  fix x :: "pdc_entry" and xa :: "pdc_entry"
  assume a1: "v \<in> vset"
  assume a2: "\<forall>x. {e \<in> t. asid_of_pdc e = None \<and> v \<in> range_of e} \<noteq> {x}"
  assume a3: "{e \<in> t. (e \<in> t \<longrightarrow> (\<forall>x\<in>vset. x \<notin> range_of e) \<or> asid_of_pdc e \<noteq> Some a) \<and> v \<in> range_of e \<and> (asid_of_pdc e = None \<or> asid_of_pdc e = Some a)} = {e}"
  assume "asid_of_pdc x \<noteq> Some a"
  assume "asid_of_pdc x = None"
  have "{ta \<in> t. (ta \<in> t \<longrightarrow> (\<forall>a. a \<in> vset \<longrightarrow> a \<notin> range_of ta) \<or> asid_of_pdc ta \<noteq> Some a) \<and> v \<in> range_of ta \<and> (asid_of_pdc ta = None \<or> asid_of_pdc ta = Some a)} \<noteq> {ta \<in> t. asid_of_pdc ta = None \<and> v \<in> range_of ta}"
    using a3 a2 by (metis (no_types))
  then show False
    using a1 by force
qed

lemma vaddr_elem_lookup_incon_global_entries_incon_pdc:
  "\<lbrakk> v \<in> vset ;  lookup_pdc (t - (\<Union>x\<in>vset. {e \<in> t. x \<in> range_of e \<and> asid_of_pdc e = Some a})) a v = Incon\<rbrakk>  \<Longrightarrow>
     lookup' (global_entries_pdc t) v = Incon"
  apply (case_tac " lookup' (global_entries_pdc t) v"; clarsimp?)
    apply (clarsimp simp: global_entries_pdc_def lookup_def tagged_pdc_entry_set_def entry_set_def split: if_split_asm option.splits)
    apply (safe ; force) [1]
   defer
   apply (clarsimp simp: global_entries_pdc_def lookup_def tagged_pdc_entry_set_def entry_set_def split: if_split_asm option.splits)
  by (safe ; force) [1]







(* page table walk simplification lemmas *)

lemma asid_entry_pdc_walk [simp]:
  "pdc_walk a m r v \<noteq> None \<Longrightarrow> asid_of_pdc (the (pdc_walk a m r v)) = Some a \<or> asid_of_pdc (the (pdc_walk a m r v)) = None"
  by (clarsimp simp: pdc_walk_def Let_def asid_of_pdc_def tag_conv_def split: option.splits pde.splits)


lemma asid_entry_pdc_walk_tlb_entry [simp]:
  "\<lbrakk>pdc_walk a m r v = Some pe; pde_tlb_entry pe m v = Some te\<rbrakk> \<Longrightarrow> asid_of te = Some a \<or> asid_of te = None"
  by (clarsimp simp: pdc_walk_def pte_tlb_entry_def asid_of_pdc_def tag_conv_def
                 split: option.splits pde.splits pte.splits if_split_asm)



lemma pdc_walk_asid [simp, intro!]:
  "pdc_walk a m r v = Some e \<Longrightarrow> asid_of_pdc (the (pdc_walk a m r v)) = Some a \<or> asid_of_pdc (the (pdc_walk a m r v)) = None"
  by (clarsimp simp: pdc_walk_def is_fault_def asid_of_pdc_def tag_conv_def split: option.splits pde.splits if_split_asm)


lemma pdc_asid_entry_range [simp, intro!]:
  "pdc_walk a m r v \<noteq> None \<Longrightarrow> v \<in> range_of (the (pdc_walk a m r v))"
  apply (clarsimp simp: pdc_walk_def Let_def range_of_pdc_entry_def split: option.splits pde.splits ) 
   apply (metis (no_types, hide_lams) Addr_addr_val atLeastAtMost_iff image_iff va_20_left va_20_right)
  by (metis (no_types, hide_lams) Addr_addr_val atLeastAtMost_iff image_iff va_20_left va_20_right)



lemma lookup_pdc_miss_inser_no_fault:
  "\<lbrakk>lookup_pdc p a v = Miss ;  pdc_walk a m r v \<noteq> None \<rbrakk> \<Longrightarrow>
    lookup_pdc (insert (the(pdc_walk a m r v)) p) a v = Hit (the (pdc_walk a m r v)) "
  apply (clarsimp simp: lookup_def  split: if_split_asm) 
  by (metis (no_types, hide_lams) asid_entry_pdc_walk insert_not_empty is_singleton_def is_singleton_the_elem 
            not_Some_eq option.sel pdc_asid_entry_range pdc_walk_def tagged_pdc_entry_set_insert the_elem_eq)
 

lemma pt_walk'_pt_walk:
  "pt_walk asid heap ttbr0 v = pt_walk' asid heap ttbr0 v"
  apply (clarsimp simp: pt_walk'_def pt_walk_def pdc_walk_def pte_tlb_entry_def  map_opt_def
                        word_extract_def word_bits_def  mask_def split:option.splits pde.splits pte.splits )
  by word_bitwise


lemma pdc_walk_pt_walk_is_fault:
  "\<lbrakk> pdc_walk a m r v = Some pde; is_fault (pde_tlb_entry pde m v) \<rbrakk> \<Longrightarrow>
      is_fault (pt_walk a m r v)"
  apply (simp only: pt_walk'_pt_walk)
  by (clarsimp simp: is_fault_def pt_walk'_def map_opt_def split: option.splits)

lemma pdc_walk_pt_walk_not_is_fault:
  "\<lbrakk> pdc_walk a m r v = Some pde; \<not>is_fault (pde_tlb_entry pde m v) \<rbrakk> \<Longrightarrow>
      \<not>is_fault (pt_walk a m r v)"
  apply (simp only: pt_walk'_pt_walk)
  by (clarsimp simp: is_fault_def pt_walk'_def map_opt_def split: option.splits)

lemma pdc_entry_pt_walk:
   "pdc_walk a m r v = Some pde \<Longrightarrow>
    pde_tlb_entry pde m v = pt_walk a m r v"
  apply (simp only: pt_walk'_pt_walk)
  by (clarsimp simp:  pt_walk'_def map_opt_def split: option.splits)


lemma pdc_entry_pt_walk'':
   "\<not>is_fault (pdc_walk a m r v) \<Longrightarrow>
    pde_tlb_entry (the (pdc_walk a m r v)) m v = pt_walk a m r v"
  apply (simp only: pt_walk'_pt_walk)
  by (clarsimp simp: is_fault_def pt_walk'_def map_opt_def split: option.splits)


lemma asid_va_entry_range_pt_entry_pde:
  "\<not>is_fault(pdc_walk a m r v) \<Longrightarrow> 
      (Some a, v) \<in> asid_range_of_pdc (the(pdc_walk a m r v)) \<or> (None, v) \<in> asid_range_of_pdc (the(pdc_walk a m r v))"
  apply (clarsimp simp: asid_range_of_pdc_def is_fault_def)
  by (metis asid_entry_pdc_walk domIff dom_iff handy_if_lemma is_some_simps(2) option.sel option.simps(3))


lemma no_fault_pt_no_fault_pde:
  "\<not>is_fault (pt_walk a m r va) \<Longrightarrow> \<not>is_fault (pdc_walk a m r va)"
  apply (simp only: pt_walk'_pt_walk)
  by (clarsimp simp: is_fault_def pt_walk'_def map_opt_def split: option.splits)

lemma is_fault_pde_is_fault_pt :
  "is_fault (pdc_walk a m r va) \<Longrightarrow> is_fault (pt_walk a m r va)"
  apply (simp only: pt_walk'_pt_walk)
  by (clarsimp simp: is_fault_def pt_walk'_def map_opt_def split: option.splits)


lemma  va_pdc_entry_set_pt_palk_same:
  "\<lbrakk>\<not>is_fault (pdc_walk a m r x) ;  (Some a, va) \<in> asid_range_of_pdc (the (pdc_walk a m r x)) \<or> (None , va) \<in> asid_range_of_pdc (the (pdc_walk a m r x))\<rbrakk> \<Longrightarrow>
              the(pdc_walk a m r x) = the(pdc_walk a m r va)"
  apply (subgoal_tac "(Some a, x) \<in> asid_range_of_pdc (the(pdc_walk a m r x)) \<or> (None , x) \<in> asid_range_of_pdc (the (pdc_walk a m r x))")
   prefer 2
   apply (clarsimp simp: asid_va_entry_range_pt_entry_pde split: pdc_entry.splits)
  apply (subgoal_tac "get_pde m r x = get_pde m r va" )
   apply (clarsimp simp: range_of_pdc_entry_def asid_range_of_pdc_def asid_of_pdc_def pdc_walk_def is_fault_def tag_conv_def va_offset_higher_bits_1 split: option.splits pde.splits if_split_asm)
  apply (clarsimp simp: range_of_pdc_entry_def asid_range_of_pdc_def asid_of_pdc_def pdc_walk_def is_fault_def tag_conv_def  split: option.splits pde.splits if_split_asm)
    apply (clarsimp simp: get_pde_def vaddr_pd_index_def)
    apply (subgoal_tac "((addr_val x >> 20) && mask 12 << 2) =  ((addr_val va >> 20) && mask 12 << 2) ")
     prefer 2 
  using shfit_mask_eq apply force
    apply force
   apply (clarsimp simp: get_pde_def vaddr_pd_index_def)
   apply (subgoal_tac "((addr_val x >> 20) && mask 12 << 2) =  ((addr_val va >> 20) && mask 12 << 2) ")
    prefer 2 
  using shfit_mask_eq apply force
   apply force
  apply (clarsimp simp: get_pde_def vaddr_pd_index_def)
  apply (subgoal_tac "((addr_val x >> 20) && mask 12 << 2) =  ((addr_val va >> 20) && mask 12 << 2) ")
   prefer 2 
  using shfit_mask_eq apply force
  by force
 

lemma  va_pdc_entry_set_pt_palk_same':
  "\<lbrakk>\<not>is_fault (pdc_walk a m r x) ;  (Some a, va) \<in> asid_range_of_pdc (the (pdc_walk a m r x))  \<or> (None , va) \<in> asid_range_of_pdc (the (pdc_walk a m r x))\<rbrakk> \<Longrightarrow>
              pdc_walk a m r x = pdc_walk a m r va"
  apply (subgoal_tac "(Some a, x) \<in> asid_range_of_pdc (the(pdc_walk a m r x)) \<or> (None , x) \<in> asid_range_of_pdc (the (pdc_walk a m r x))")
   prefer 2
   apply (clarsimp simp:  asid_va_entry_range_pt_entry_pde split: pdc_entry.splits)
  apply (subgoal_tac "get_pde m r x = get_pde m r va" )
   apply (clarsimp simp: range_of_pdc_entry_def asid_range_of_pdc_def asid_of_pdc_def pdc_walk_def is_fault_def tag_conv_def va_offset_higher_bits_1 split: option.splits pde.splits if_split_asm)
  apply (clarsimp simp: range_of_pdc_entry_def asid_range_of_pdc_def asid_of_pdc_def pdc_walk_def is_fault_def tag_conv_def  split: option.splits pde.splits if_split_asm)
    apply (clarsimp simp: get_pde_def vaddr_pd_index_def)
    apply (subgoal_tac "((addr_val x >> 20) && mask 12 << 2) =  ((addr_val va >> 20) && mask 12 << 2) ")
     prefer 2 
  using shfit_mask_eq apply force
    apply force
   apply (clarsimp simp: get_pde_def vaddr_pd_index_def)
   apply (subgoal_tac "((addr_val x >> 20) && mask 12 << 2) =  ((addr_val va >> 20) && mask 12 << 2) ")
    prefer 2 
  using shfit_mask_eq apply force
   apply force
  apply (clarsimp simp: get_pde_def vaddr_pd_index_def)
  apply (subgoal_tac "((addr_val x >> 20) && mask 12 << 2) =  ((addr_val va >> 20) && mask 12 << 2) ")
   prefer 2 
  using shfit_mask_eq apply force
  by force


theorem entry_range_single_element':
  " {E \<in> the ` {e \<in> t. \<not> is_fault e}. (a, v) \<in> asid_range_of E} = {x} \<Longrightarrow> 
       (a, v) \<in> asid_range_of x \<and> \<not> is_fault (Some x) 
         \<and> (\<forall>y\<in>the ` {e \<in> t. \<not> is_fault e}. y\<noteq>x \<and> 
               \<not> is_fault (Some y) \<longrightarrow> (a, v) \<notin> asid_range_of y)" 
  apply safe
    apply force
   apply (clarsimp simp: is_fault_def)
  by force




lemma lookup_pdc_range_fault_pt_walk:
  "\<lbrakk>lookup_pdc (the ` {e \<in> range (pdc_walk a m r). \<not> is_fault e}) a v = Hit x\<rbrakk>  \<Longrightarrow> 
          \<forall>va\<in> range_of x. x = the (pdc_walk a m r va)"
  apply (subgoal_tac "x \<in> the ` {e \<in> range (pdc_walk a m r). \<not> is_fault e}")
   prefer 2
  using lookup_in_asid_pdc apply blast
  apply clarsimp
  apply (rule va_pdc_entry_set_pt_palk_same, simp)
  apply (clarsimp simp: asid_range_of_pdc_def is_fault_def)
  using pdc_walk_asid by force


theorem pdc_entry_range_single_elementI':
  "\<lbrakk>x\<in> the ` {e \<in> range (pdc_walk asid mem ttbr0). \<not> is_fault e} ; \<not> is_fault (Some x) ; (a, v) \<in> asid_range_of_pdc x ; 
    (\<forall>y\<in>the ` {e \<in> range (pdc_walk asid mem ttbr0). \<not> is_fault e}. y\<noteq>x \<longrightarrow> (a, v) \<notin> asid_range_of_pdc y) \<rbrakk> \<Longrightarrow> 
           {E \<in> the ` {e \<in> range (pdc_walk asid mem ttbr0). \<not> is_fault e}. (a, v) \<in> asid_range_of_pdc E} = {x}" 
  by force


theorem asid_entry_range_single_element_pdc:
  " {E \<in> the ` {e \<in> t. \<not> is_fault e}. v \<in> range_of E \<and> (asid_of_pdc E = None \<or> asid_of_pdc E = Some a)} = {x} \<Longrightarrow> 
       v \<in> range_of x \<and> (asid_of_pdc x = None \<or> asid_of_pdc x = Some a) \<and> \<not> is_fault (Some x) 
         \<and> (\<forall>y\<in>the ` {e \<in> t. \<not> is_fault e}. y\<noteq>x \<and> 
               \<not> is_fault (Some y) \<longrightarrow> ((Some a, v) \<notin> asid_range_of_pdc y \<and> (None, v) \<notin> asid_range_of_pdc y))" 
  apply safe
     apply force
    apply (clarsimp simp: is_fault_def)
    apply force
   apply (simp add: is_fault_def)
  apply (clarsimp simp: asid_range_of_pdc_def)
   apply force
 apply (clarsimp simp: asid_range_of_pdc_def)
  by force


theorem asid_pdc_range_single_elementI':
  "\<lbrakk>x\<in> t ; (Some a, v) \<in> asid_range_of_pdc x \<or> (None, v) \<in> asid_range_of_pdc x ;
     (\<forall>y\<in>t. y\<noteq>x \<longrightarrow> (Some a, v) \<notin> asid_range_of_pdc y \<and> (None, v) \<notin> asid_range_of_pdc y) \<rbrakk> \<Longrightarrow> 
         {E \<in> t.  v \<in> range_of E \<and> (asid_of_pdc E = None \<or> asid_of_pdc E = Some a)} = {x}" 
   apply (clarsimp simp: asid_range_of_pdc_def) by force


 lemma  va_entry_set_pdc_walk_same':
  "\<lbrakk>\<not>is_fault (pdc_walk asid m r x) ;
           va \<in> range_of (the (pdc_walk asid m r x))\<rbrakk> \<Longrightarrow>
              pdc_walk asid m r x = pdc_walk asid m r va"
   apply (subgoal_tac "x \<in> range_of (the(pdc_walk asid m r x))")
    prefer 2
    apply (clarsimp simp:  is_fault_def)
   apply (cases "the (pdc_walk asid m r x)")
    apply (simp only: )
    apply (clarsimp simp:   range_of_pdc_entry_def  is_fault_def)
    apply (cases "get_pde m r x" ; clarsimp simp: pdc_walk_def)
    apply (case_tac a ; clarsimp)
    apply (subgoal_tac "get_pde m r (Addr xaa) = get_pde m r (Addr xa)" ; clarsimp)
     apply (cases "get_pde m r x" ; clarsimp)
     apply (subgoal_tac "get_pde m r (Addr xaa) = get_pde m r (Addr xa)" ; clarsimp)
   using va_offset_higher_bits_1 apply blast
    apply (clarsimp simp: get_pde_def vaddr_pd_index_def)
    apply (subgoal_tac "((xaa >> 20) && mask 12 << 2) = ((xa >> 20) && mask 12 << 2)")
     apply force
   using shfit_mask_eq apply force
   apply (simp only: )
   apply (clarsimp simp:   range_of_pdc_entry_def  is_fault_def)
   apply (cases "get_pde m r x" ; clarsimp simp: pdc_walk_def)
   apply (case_tac a ; clarsimp)
   apply (subgoal_tac "get_pde m r (Addr xaa) = get_pde m r (Addr xa)" ; clarsimp)
    apply (cases "get_pde m r x" ; clarsimp)
    apply (subgoal_tac "get_pde m r (Addr xaa) = get_pde m r (Addr xa)" ; clarsimp)
   using va_offset_higher_bits_1 apply blast
   apply (clarsimp simp: get_pde_def vaddr_pd_index_def)
   apply (subgoal_tac "((xaa >> 20) && mask 12 << 2) = ((xa >> 20) && mask 12 << 2)")
    apply force
   using shfit_mask_eq by force



lemma lookup_pdc_range_pt_walk_hit:
  "\<not> is_fault (pdc_walk asid mem ttbr0  va) \<Longrightarrow> 
        lookup_pdc (the ` {e \<in> range (pdc_walk asid mem ttbr0). \<not> is_fault e}) asid va = Hit (the (pdc_walk asid mem ttbr0  va))"
 apply (clarsimp simp: lookup_def)
  apply safe
    apply simp apply clarsimp
   apply (subgoal_tac "x = the (pdc_walk asid mem ttbr0 va)" , force)
   apply (clarsimp simp: tagged_pdc_entry_set_def entry_set_def)
   apply (drule asid_entry_range_single_element_pdc)
   apply safe
    apply (unfold Ball_def) [1]
    apply (erule_tac x = "the (pdc_walk asid mem ttbr0  va)" in allE)
    apply (clarsimp simp:  is_fault_def asid_range_of_pdc_def)
    apply (metis  asid_entry_pdc_walk option.distinct(1) option.sel)
   apply (unfold Ball_def) [1]
   apply (erule_tac x = "the (pdc_walk asid mem ttbr0  va)" in allE)
   apply (clarsimp simp:  is_fault_def asid_range_of_pdc_def)
  apply (metis asid_entry_pdc_walk  handy_if_lemma  option.sel option.simps(3))
  apply (rule_tac x = "the (pdc_walk asid mem ttbr0 va)" in exI)
  apply (clarsimp simp: tagged_pdc_entry_set_def entry_set_def)
  apply (rule asid_pdc_range_single_elementI')
    apply force
   apply (clarsimp simp:  is_fault_def asid_range_of_pdc_def) 
  apply (metis asid_entry_pdc_walk domIff dom_iff handy_if_lemma is_some_simps(2) option.distinct(1) option.sel)
  apply (clarsimp simp:  is_fault_def asid_range_of_pdc_def)
  by (metis is_fault_def option.discI  option.sel  va_entry_set_pdc_walk_same')
  

lemma  lookup_pdc_walk_not_incon:
  "lookup_pdc (the ` {e \<in> range (pdc_walk asid mem ttbr0). \<not> is_fault e}) asid va \<noteq> Incon"
 apply (case_tac "\<not>is_fault (pdc_walk asid mem ttbr0 va)")
   apply (clarsimp simp: lookup_pdc_range_pt_walk_hit)
  apply clarsimp
  apply (subgoal_tac " lookup_pdc (the ` {e \<in> pdc_walk asid mem ttbr0 ` top. \<not> is_fault e}) asid va = Miss")
   apply (clarsimp simp: lookup_def tagged_pdc_entry_set_def entry_set_def asid_of_pdc_def  split: if_split_asm)
  apply (thin_tac "lookup_pdc (the ` {e \<in> range (pdc_walk asid mem ttbr0). \<not> is_fault e}) asid va = Incon")
  apply (subgoal_tac "tagged_pdc_entry_set (the ` {e \<in> range (pdc_walk asid mem ttbr0). \<not> is_fault e}) asid va = {}")
   apply (clarsimp simp: lookup_def tagged_pdc_entry_set_def entry_set_def  split: if_split_asm)
  apply (clarsimp simp: entry_pdc_set_va_set tag_vadr_pdc_def)
  apply safe 
   apply (subgoal_tac "pdc_walk asid mem ttbr0 xa = pdc_walk asid mem ttbr0 va", simp)
   apply (thin_tac "is_fault (pdc_walk asid mem ttbr0 va)") 
   apply (frule_tac va = va in va_pdc_entry_set_pt_palk_same'; clarsimp)
  apply (subgoal_tac "pdc_walk asid mem ttbr0  xa = pdc_walk asid mem ttbr0 va", simp)
  apply (thin_tac "is_fault (pdc_walk asid mem ttbr0 va)") 
  by (frule_tac va = va in va_pdc_entry_set_pt_palk_same'; clarsimp)
 

lemma lookup_pdc_hit_range_pdes:
  "lookup_pdc (the ` {e \<in> range (pdc_walk a mem ttbr0). \<not> is_fault e}) a va = Hit pde \<Longrightarrow>
     pde = the (pdc_walk a mem ttbr0 va) "
  apply (frule lookup_pdc_range_fault_pt_walk)
  apply (drule_tac x = va in bspec)
  using lookup_asid_pdc_hit_entry_range apply blast
  by blast
  

lemma pdc_walk_set_simp:
  "{e. (\<exists>x. e = pdc_walk a mem ttbr0 x) \<and> \<not> is_fault e} =
   {e \<in> range (pdc_walk a mem ttbr0). \<not> is_fault e}"
  by blast
 


lemma pdc_entry_set_empty_lookup_pdc:
  "tagged_pdc_entry_set (the ` {e \<in> range (pdc_walk a mem ttbr0). \<not> is_fault e}) a xa = {} \<Longrightarrow>
         lookup_pdc (the ` {e \<in> range (pdc_walk a mem ttbr0). \<not> is_fault e}) a xa = Miss"
  by (clarsimp simp: lookup_def)


lemma lookup_pdc_miss_is_fault_intro:
  "is_fault (pdc_walk a m r v) \<Longrightarrow>
     lookup_pdc (the ` {e \<in> range (pdc_walk a m r). \<not> is_fault e}) a v = Miss"
 apply (rule pdc_entry_set_empty_lookup_pdc)
  apply (clarsimp simp: entry_pdc_set_va_set)
  apply (clarsimp simp: tag_vadr_pdc_def)
  apply safe
  apply (subgoal_tac "pdc_walk a m r xa = pdc_walk a m r v", simp)
  apply (thin_tac "is_fault (pdc_walk a m r v)") 
   apply (frule_tac va = v in va_pdc_entry_set_pt_palk_same'; clarsimp)
 apply (subgoal_tac "pdc_walk a m r xa = pdc_walk a m r v", simp)
  apply (thin_tac "is_fault (pdc_walk a m r v)") 
  by (frule_tac va = v in va_pdc_entry_set_pt_palk_same'; clarsimp)
 
  

lemma  tlb_pde_union_walk [simp]:
  "{e. (\<exists>x. e \<in> tlb_pdc_walk a (the ` {e \<in> range (pdc_walk a mem ttbr0). \<not> is_fault e}) mem ttbr0 x) \<and> \<not> is_fault e} = 
         {e\<in>pt_walk a mem ttbr0 ` UNIV. \<not>is_fault e}"
  apply safe
   apply (clarsimp simp: tlb_pdc_walk_def lookup_pdc_walk_not_incon split: lookup_type.splits)
   apply (subgoal_tac "x3 = the (pdc_walk a mem ttbr0 xa)")
    prefer 2
    apply (rule lookup_pdc_hit_range_pdes, simp add: pdc_walk_set_simp)
   apply clarsimp
   apply (case_tac "\<not> is_fault (pdc_walk a mem ttbr0 xa)")
    prefer 2 
    apply (clarsimp simp: lookup_pdc_miss_is_fault_intro)
   apply (clarsimp simp: image_iff)
   apply (case_tac "the (pdc_walk a mem ttbr0 xa)"; clarsimp)
    apply (rule_tac x = xa in exI)
    apply (simp only: pt_walk'_pt_walk)
    apply (clarsimp simp: pt_walk'_def map_opt_def is_fault_def split: option.splits)
   apply (rule_tac x = xa in exI)
   apply (simp only: pt_walk'_pt_walk)
   apply (clarsimp simp: pdc_walk_def pt_walk'_def map_opt_def is_fault_def split:option.splits)
  apply (rename_tac va)
  apply (rule_tac x = va in exI)
  apply (clarsimp simp:  tlb_pdc_walk_def split: lookup_type.splits)
  apply (rule conjI)
   apply (clarsimp simp: lookup_pdc_walk_not_incon)
  apply (clarsimp)
  apply (subgoal_tac "x3 = the (pdc_walk a mem ttbr0 va)")
   prefer 2
   apply (clarsimp simp: lookup_pdc_hit_range_pdes)
  apply (simp only: pt_walk'_pt_walk)
  by (case_tac x3; clarsimp simp:  pt_walk'_def pdc_walk_def map_opt_def  is_fault_def split:option.splits pde.splits)
   


lemma lookup_pdc_miss_is_fault:
  "lookup_pdc (the ` {e \<in> range (pdc_walk a m r). \<not> is_fault e}) a v = Miss \<Longrightarrow>
       is_fault (pdc_walk a m r v)"
   apply (clarsimp simp: lookup_def tagged_pdc_entry_set_def entry_set_def asid_of_pdc_def  split: if_split_asm)
  apply (drule_tac x = "the (pdc_walk a m r v)" in spec)
  by (metis (no_types, lifting) UNIV_I asid_entry_pdc_walk asid_of_pdc_def 
     image_eqI is_fault_def mem_Collect_eq option.simps(3) pdc_asid_entry_range)





(* asid_unequal_miss' *)




lemma pt_walk_new_fault_pt_walk_fault:
  "pt_walk_pair a m r v = Fault \<Longrightarrow> is_fault (pt_walk a m r v)"
  apply (simp only: pt_walk'_pt_walk)
  by (clarsimp simp: pt_walk_pair_def is_fault_def pt_walk'_def map_opt_def split: option.splits pde.splits) 
  

lemma pt_walk_new_fault_pde_walk_fault:
  "pt_walk_pair a m r v = Fault \<Longrightarrow> is_fault (pdc_walk a m r v)"
  by (clarsimp simp: pt_walk_pair_def is_fault_def pdc_walk_def split: option.splits pde.splits pte.splits)

lemma  pt_walk_new_fault_pt_walk_fault':
  "\<lbrakk>pt_walk_pair a m rt v = Fault\<rbrakk> \<Longrightarrow> pt_walk a m rt v = None"
  apply (simp only: pt_walk'_pt_walk)
  by (clarsimp simp: pt_walk_pair_def is_fault_def pt_walk'_def map_opt_def split: option.splits pde.splits)


lemma  pt_walk_new_fault_pdc_walk_fault':
  "\<lbrakk>pt_walk_pair a m rt v = Fault\<rbrakk> \<Longrightarrow> pdc_walk a m rt v = None"
  by (clarsimp simp: pt_walk_pair_def pdc_walk_def split: option.splits pde.splits pte.splits)


lemma pt_walk_new_par_fault_pt_walk_fault:
  "\<lbrakk>pt_walk_pair a m r v = Partial_Walk y\<rbrakk> \<Longrightarrow> is_fault (pt_walk a m r v)"
  apply (simp only: pt_walk'_pt_walk)
   by (clarsimp simp: pt_walk_pair_def is_fault_def pt_walk'_def map_opt_def split: option.splits pde.splits)


lemma pt_walk_new_par_fault_pt_walk_fault':
  "\<lbrakk>pt_walk_pair a m r v = Partial_Walk y\<rbrakk> \<Longrightarrow> pt_walk a m r v = None"
  apply (simp only: pt_walk'_pt_walk)
   by (clarsimp simp: pt_walk_pair_def is_fault_def pt_walk'_def map_opt_def split: option.splits pde.splits)


lemma pt_walk_new_par_fault_pdc_walk:
  "\<lbrakk>pt_walk_pair a m r v = Partial_Walk y\<rbrakk> \<Longrightarrow> pdc_walk a m r v = Some y"
  by (clarsimp simp: pt_walk_pair_def is_fault_def pdc_walk_def split: option.splits pde.splits pte.splits)


lemma pt_walk_new_no_fault_pt_walk':
  "\<lbrakk>pt_walk_pair a m rt v = Full_Walk entry entry'\<rbrakk> \<Longrightarrow> pt_walk a m rt v = Some entry"
  apply (simp only: pt_walk'_pt_walk)
  by (clarsimp simp: pt_walk_pair_def pt_walk'_def map_opt_def split: option.splits pde.splits pte.splits)
 

lemma pt_walk_new_no_fault_pdc_walk:
  "\<lbrakk>pt_walk_pair a m rt v = Full_Walk entry entry'\<rbrakk> \<Longrightarrow> pdc_walk a m rt v = Some entry'"
  by (clarsimp simp: pt_walk_pair_def pdc_walk_def split: option.splits pde.splits pte.splits)
 

 
lemma pt_walk_new_equal_pt_walk:
  "pt_walk_pair a m rt v = pt_walk_pair a' m' rt' v \<Longrightarrow> pt_walk a m rt v = pt_walk a' m' rt' v"
  by (cases "pt_walk_pair a m rt v"; cases "pt_walk_pair a' m' rt' v";
               clarsimp simp: pt_walk_new_fault_pt_walk_fault' pt_walk_new_par_fault_pt_walk_fault'
                              pt_walk_new_no_fault_pt_walk')


lemma pt_walk_new_equal_pdc_walk:
  "pt_walk_pair a m rt v = pt_walk_pair a' m' rt' v \<Longrightarrow> pdc_walk a m rt v = pdc_walk a' m' rt' v"
  by (cases "pt_walk_pair a m rt v"; cases "pt_walk_pair a' m' rt' v";
               clarsimp simp: pt_walk_new_fault_pdc_walk_fault' pt_walk_new_par_fault_pdc_walk
                              pt_walk_new_no_fault_pdc_walk)

lemma pt_walk_partial_full_pdc_walk_eq:
  "\<lbrakk>pt_walk_pair a m r v = Partial_Walk y; pt_walk_pair a' m' r' v = Full_Walk x y \<rbrakk> \<Longrightarrow>
                     pdc_walk a m r v = pdc_walk a' m' r' v"
  by (cases "pt_walk_pair a m r v"; cases "pt_walk_pair a' m' r' v"; clarsimp simp: pt_walk_new_par_fault_pdc_walk
                      pt_walk_new_no_fault_pdc_walk)


lemma pdc_entry_range_asid_entry:
  "(a, v) \<in> asid_range_of_pdc (e::pdc_entry) \<Longrightarrow> asid_of_pdc e = a"
  by (clarsimp simp: asid_range_of_pdc_def)



definition
  "consistent0' m asid ttbr0 tlb pdc va \<equiv>
     ((lookup'' tlb asid va = Hit (the (pt_walk asid m ttbr0 va)) \<and> \<not>is_fault (pt_walk asid m ttbr0 va)) \<or> 
       lookup'' tlb asid va = Miss) \<and>
     ((lookup_pdc pdc asid va = Hit (the (pdc_walk asid m ttbr0 va)) \<and> \<not>is_fault (pdc_walk asid m ttbr0 va)) \<or>
        lookup_pdc pdc asid va = Miss )"

lemma consistent_not_Incon_imp':
  "consistent0' m asid ttbr0 tlb pde_set va \<Longrightarrow>
  (lookup'' tlb asid va \<noteq> Incon \<and> (\<forall>e. lookup'' tlb asid va = Hit e \<longrightarrow> e = the (pt_walk asid m ttbr0 va) \<and> pt_walk asid m ttbr0 va \<noteq> None) \<and>
  lookup_pdc pde_set asid va \<noteq> Incon \<and> (\<forall>e. lookup_pdc pde_set asid va = Hit e \<longrightarrow> e = the (pdc_walk asid m ttbr0 va) \<and> pdc_walk asid m ttbr0 va \<noteq> None))"
  apply (clarsimp simp: consistent0'_def is_fault_def) 
  by force

lemma consistent_not_Incon'':
  "consistent0' m asid ttbr0 tlb pde_set va =
  (lookup'' tlb asid va \<noteq> Incon \<and> (\<forall>e. lookup'' tlb asid va = Hit e \<longrightarrow> e = the (pt_walk asid m ttbr0 va) \<and> pt_walk asid m ttbr0 va \<noteq> None) \<and>
  lookup_pdc pde_set asid va \<noteq> Incon \<and> (\<forall>e. lookup_pdc pde_set asid va = Hit e \<longrightarrow> e = the (pdc_walk asid m ttbr0 va) \<and> pdc_walk asid m ttbr0 va \<noteq> None))"
  apply ((cases "lookup'' tlb asid va", cases "lookup_pdc pde_set asid va"); simp add: consistent0'_def is_fault_def)
  by (metis lookup_type.distinct(1) lookup_type.distinct(3) lookup_type.distinct(5) lookup_type.exhaust lookup_type.inject option.distinct(1) option.expand option.sel)



lemma non_fault_pt_walk_pair_disjI:
  "\<not> is_fault (pdc_walk a m r v) \<Longrightarrow>
          pt_walk_pair a m r v = Partial_Walk (the (pdc_walk a m r v)) \<or>
          pt_walk_pair a m r v = Full_Walk (the (pt_walk a m r v)) (the (pdc_walk a m r v))"
  apply (simp only: pt_walk'_pt_walk)
  apply (case_tac "is_fault (pt_walk' a m r v) ")
   apply (rule disjI1)
   apply (clarsimp simp: is_fault_def pt_walk_pair_def split: option.split)
   apply (case_tac y; clarsimp simp: pt_walk'_def map_opt_def)
  apply (rule disjI2)
  apply (clarsimp simp: is_fault_def pt_walk_pair_def split: option.split)
  apply (case_tac x2, clarsimp simp: pt_walk'_def map_opt_def)
  apply (clarsimp simp: pte_tlb_entry_def pdc_walk_def pt_walk'_def map_opt_def 
                  split: option.splits pde.splits pte.splits)
  by force
 

lemma non_fault_pt_walk_full_walk:
  "\<not> is_fault (pt_walk a m r v) \<Longrightarrow> 
       pt_walk_pair a m r v = Full_Walk (the (pt_walk a m r v)) (the (pdc_walk a m r v)) "
  apply (subgoal_tac "\<not> is_fault (pdc_walk a m r v)")
  using non_fault_pt_walk_pair_disjI pt_walk_new_par_fault_pt_walk_fault apply blast
  using is_fault_pde_is_fault_pt by blast


lemma pt_walk_new_no_fault_pt_walk_new:
  "pt_walk_pair a m r v = Full_Walk te pe \<Longrightarrow> \<not>is_fault (pt_walk a m r v)"
  by (simp add: is_fault_def pt_walk_new_no_fault_pt_walk')


lemma pt_walk_full_no_pdc_fault:
  "pt_walk_pair a m r v = Full_Walk te pe \<Longrightarrow> \<not>is_fault (pdc_walk a m r v)"
  using no_fault_pt_no_fault_pde pt_walk_new_no_fault_pt_walk_new by auto

lemma pt_walk_partial_no_pdc_fault:
  "pt_walk_pair a m r v = Partial_Walk pe \<Longrightarrow> \<not>is_fault (pdc_walk a m r v)"
  by (simp add: is_fault_def pt_walk_new_par_fault_pdc_walk)


lemma  global_entries_pdc_ptable_same:
  "global_entries_pdc (the ` {e \<in> range (pdc_walk a m r). \<not> is_fault e}) = 
        global_entries_pdc (the ` {e \<in> range (pdc_walk a' m r). \<not> is_fault e})"
  apply rule
   apply (clarsimp simp: global_entries_pdc_def is_fault_def)
   apply (clarsimp simp: image_iff)
   apply (rule_tac x = "pdc_walk a m r xb" in exI)
   apply (rule conjI)
    apply (rule_tac x = xb in exI)
    apply (clarsimp simp: is_fault_def pdc_walk_def Let_def  asid_of_pdc_def
      tag_conv_def split: option.splits pde.splits pte.splits if_split_asm)
   apply force
  apply (clarsimp simp: global_entries_pdc_def is_fault_def)
  apply (clarsimp simp: image_iff)
  apply (rule_tac x = "pdc_walk a' m r xb" in exI)
  apply (rule conjI)
   apply (rule_tac x = xb in exI)
   apply (clarsimp simp: is_fault_def pdc_walk_def Let_def  asid_of_pdc_def
      tag_conv_def split: option.splits pde.splits pte.splits if_split_asm)
  by force



lemma is_fault_non_global_entries_pdc_miss:
 "is_fault (pdc_walk a m r v) \<Longrightarrow> lookup_pdc (non_global_entries_pdc (the ` {e \<in> range (pdc_walk a m r). \<not> is_fault e})) a v = Miss"
  apply (subgoal_tac "lookup_pdc (the ` {e \<in> range (pdc_walk a m r). \<not> is_fault e}) a v = Miss")
  apply (subgoal_tac "lookup_pdc (global_entries_pdc (the ` {e \<in> range (pdc_walk a m r). \<not> is_fault e}) \<union>
                  non_global_entries_pdc (the ` {e \<in> range (pdc_walk a m r). \<not> is_fault e})) a v = Miss")
  prefer 2
  using lookup_eq_union_global_non_global_pdc apply auto[1]
   apply (drule lookup_asid_pdc_miss_union, simp)
  using lookup_pdc_miss_is_fault_intro by auto


lemma lookup_pdc_global_hit_order:
  "lookup_pdc (global_entries_pdc t) a v = Hit e  \<Longrightarrow>
        lookup_pdc t a v = Hit e \<or> lookup_pdc t a v = Incon"
  apply safe
  by (metis asid_pdc_mono glb_pdc_subset global_entries_pdc_def less_eq_lookup_type lookup_type.simps(5))


lemma no_fault_pdc_walk_unequal_asid':
   "\<not>is_fault (pdc_walk (a::8 word) m r v) \<Longrightarrow> \<not>is_fault (pdc_walk a' m r v)"
  apply (clarsimp simp: is_fault_def)
  by (clarsimp simp: pdc_walk_def Let_def tag_conv_def split: option.splits pde.splits pte.splits if_split_asm)


lemma lookup_pdc_non_global_miss_non_fault:
  "\<lbrakk> lookup_pdc (non_global_entries_pdc (the ` {e \<in> range (pdc_walk a m r). \<not> is_fault e}) ) a v = Miss;  
        \<not> is_fault (pdc_walk a m r v)\<rbrakk> \<Longrightarrow> 
    lookup_pdc (global_entries_pdc (the ` {e \<in> range (pdc_walk a m r). \<not> is_fault e})) a v = 
           Hit (the (pdc_walk a m r v))"
  apply (frule lookup_pdc_range_pt_walk_hit)
  apply (subgoal_tac "lookup_pdc  (the ` {e \<in> range (pdc_walk a m r). \<not> is_fault e}) a v =
                lookup_pdc (global_entries_pdc (the ` {e \<in> range (pdc_walk a m r). \<not> is_fault e}) \<union>
                 non_global_entries_pdc (the ` {e \<in> range (pdc_walk a m r). \<not> is_fault e})) a v")
   apply (simp only:)
   apply (drule lookup_asid_pdc_hit_mis_hit; simp)
  by (rule lookup_eq_union_global_non_global_pdc)



lemma non_global_lookup_range_fault_pt_walk_pdc:
  "\<lbrakk>lookup_pdc (non_global_entries_pdc (the ` {e \<in> range (pdc_walk a m r). \<not> is_fault e})) a v = Hit x\<rbrakk>  \<Longrightarrow> 
          \<forall>va\<in> range_of x. x = the (pdc_walk a m r va)"
  apply (subgoal_tac "lookup_pdc  (the ` {e \<in> range (pdc_walk a m r). \<not> is_fault e}) a v = Hit x")
   apply (rule lookup_pdc_range_fault_pt_walk, simp)
  apply (subgoal_tac "lookup_pdc (the ` {e \<in> range (pdc_walk a m r). \<not> is_fault e}) a v \<noteq> Incon")
   apply (subgoal_tac "non_global_entries_pdc (the ` {e \<in> range (pdc_walk a m r). \<not> is_fault e}) \<subseteq>
                      the ` {e \<in> range (pdc_walk a m r). \<not> is_fault e} ")
    apply (drule_tac a = a and v = v in asid_pdc_mono)
    apply (simp add: less_eq_lookup_type)
   apply (clarsimp simp: non_global_entries_pdc_def)
  by (rule lookup_pdc_walk_not_incon)

  

lemma non_global_global_disjoint_pdc:
  "lookup_pdc (non_global_entries_pdc (the ` {e \<in> range (pdc_walk a m r). \<not> is_fault e})) a v = Hit x \<Longrightarrow>
   lookup_pdc (global_entries_pdc (the ` {e \<in> range (pdc_walk a m r). \<not> is_fault e})) a v = Miss"
  apply (cases "lookup_pdc (the ` {e \<in> range (pdc_walk a m r). \<not> is_fault e}) a v")
  apply (metis (full_types) lookup_asid_pdc_miss_union lookup_eq_union_global_non_global_pdc)
   apply (clarsimp simp: lookup_pdc_walk_not_incon)
  apply (case_tac "lookup_pdc (global_entries_pdc (the ` {e \<in> range (pdc_walk a m r). \<not> is_fault e})) a v")
    apply simp
   apply (simp add: lookup_global_incon_incon_pdc)
  apply clarsimp
proof -
fix x3 :: pdc_entry and x3a :: pdc_entry
  assume a1: "lookup_pdc (non_global_entries_pdc (the ` {e \<in> range (pdc_walk a m r). \<not> is_fault e})) a v = Hit x"
assume a2: "lookup_pdc (the ` {e \<in> range (pdc_walk a m r). \<not> is_fault e}) a v = Hit x3"
assume a3: "lookup_pdc (global_entries_pdc (the ` {e \<in> range (pdc_walk a m r). \<not> is_fault e})) a v = Hit x3a"
  have f4: "Hit x = lookup_pdc {p \<in> the ` {z \<in> range (pdc_walk a m r). \<not> is_fault z}. \<exists>w. asid_of_pdc p = Some w} a v"
    using a1 by (simp add: non_global_entries_pdc_def)
  have f5: "\<forall>a P p w. Hit p \<noteq> lookup_pdc {p \<in> P. asid_of_pdc p = None} w a \<or> Hit p = lookup' {p \<in> P. asid_of_pdc p = None} a"
    by (metis global_entries_pdc_def lookup_global_hit_lookup'_pdc)
  have f6: "\<forall>P. lookup_pdc P a v \<le> Hit x3 \<or> \<not> P \<subseteq> the ` {z \<in> range (pdc_walk a m r). \<not> is_fault z}"
  using a2 by (metis (no_types) asid_pdc_mono)
  have f7: "\<forall>p P. Hit p \<noteq> lookup' {p \<in> P. asid_of_pdc p = None} v \<or> Hit x \<noteq> Hit p"
    using f4 by (metis (no_types) global_entries_pdc_def interesting_lemma_pdc non_global_entries_pdc_def)
  have f8: "Hit x3a \<le> Hit x3"
    using f6 a3 by (metis (no_types) glb_pdc_subset)
  have f9: "Hit x \<le> Hit x3"
    using f6 f4 by auto
  have f10: "x3 = x3a"
  using f8 by auto
have "x = x3"
using f9 by auto
  then show False
    using f10 f7 f5 a3 by (metis (no_types) global_entries_pdc_def)
qed



lemma lookup_global_miss_non_fault_pdc:
  "\<lbrakk> lookup_pdc (global_entries_pdc (the ` {e \<in> range (pdc_walk a m r). \<not> is_fault e}) ) a v = Miss;  
        \<not> is_fault (pdc_walk a m r v)\<rbrakk> \<Longrightarrow> 
    lookup_pdc (non_global_entries_pdc (the ` {e \<in> range (pdc_walk a m r). \<not> is_fault e})) a v = 
           Hit (the (pdc_walk a m r v))"
  apply (frule lookup_pdc_range_pt_walk_hit)
  apply (subgoal_tac "lookup_pdc (the ` {e \<in> range (pdc_walk a m r). \<not> is_fault e}) a v =
                lookup_pdc (global_entries_pdc (the ` {e \<in> range (pdc_walk a m r). \<not> is_fault e}) \<union>
                 non_global_entries_pdc (the ` {e \<in> range (pdc_walk a m r). \<not> is_fault e})) a v")
   apply (simp only:)
   apply (drule lookup_asid_pdc_hit_mis_hit'; simp)
  by (rule lookup_eq_union_global_non_global_pdc)



lemma non_global_lookup_range_pdc_walk_not_incon:
  "lookup_pdc (non_global_entries_pdc (the ` {e \<in> range (pdc_walk (asid :: 8 word) mem ttbr0). \<not> is_fault e})) asid va \<noteq> Incon"
  apply (subgoal_tac "lookup_pdc  (the ` {e \<in> range (pdc_walk asid mem ttbr0). \<not> is_fault e}) asid va \<noteq> Incon")
   prefer 2
   apply (rule lookup_pdc_walk_not_incon)
  apply (subgoal_tac "non_global_entries_pdc (the ` {e \<in> range (pdc_walk asid mem ttbr0). \<not> is_fault e}) \<subseteq> 
                          the ` {e \<in> range (pdc_walk asid mem ttbr0). \<not> is_fault e}")
  using lookup_asid_pdc_incon_subset apply blast
  by (rule non_glb_pdc_subset)




lemma lookup_global_miss_asid_unequal_pdc:
  "\<lbrakk>lookup_pdc (global_entries_pdc (the ` {e \<in> range (pdc_walk a m r). \<not> is_fault e})) a v = Miss\<rbrakk>
    \<Longrightarrow> lookup_pdc (global_entries_pdc (the ` {e \<in> range (pdc_walk a' m r). \<not> is_fault e})) a' v = Miss"  
  apply (subgoal_tac "tagged_pdc_entry_set (global_entries_pdc (the ` {e \<in> range (pdc_walk a' m r). \<not> is_fault e})) a' v = {}")
  apply (clarsimp simp:  lookup_def)
  apply (clarsimp simp: tagged_entry_set_to_entry_set_pdc)
  apply (rule_tac a = a in lookup_global_miss_entry_set_empty_pdc)
  apply (insert global_entries_pdc_ptable_same [of a m r a'])
  by force




lemma asid_pdc_lookup_range_fault_pt_walk':
  "\<lbrakk>lookup_pdc (the ` {e \<in> range (pdc_walk a m r). \<not> is_fault e}) a v = Hit x\<rbrakk>  \<Longrightarrow> 
          \<forall>va\<in> range_of x. x = the (pdc_walk a m r va) \<and> \<not>is_fault (pdc_walk a m r va)"
  apply (subgoal_tac "x \<in> the ` {e \<in> range (pdc_walk a m r). \<not> is_fault e}")
   prefer 2
  using lookup_in_asid_pdc apply blast
   apply clarsimp
   apply (rule conjI)
  using lookup_pdc_range_fault_pt_walk apply blast
  apply (clarsimp simp: asid_range_of_def)
  apply (frule_tac va = v in  va_pdc_entry_set_pt_palk_same')
   apply (drule lookup_asid_pdc_hit_entry_range_asid_tags, simp)
  by (metis (no_types, hide_lams)  va_entry_set_pdc_walk_same') 

lemma non_global_hit_no_fault_pdc:
  "lookup_pdc (non_global_entries_pdc (the ` {e \<in> range (pdc_walk a m r). \<not> is_fault e})) a v = Hit x \<Longrightarrow>
             \<not> is_fault (pdc_walk a m r v)"
  apply (subgoal_tac "lookup_pdc (the ` {e \<in> range (pdc_walk a m r). \<not> is_fault e}) a v = Hit x")
   defer
  apply (subgoal_tac "non_global_entries_pdc (the ` {e \<in> range (pdc_walk a m r). \<not> is_fault e}) \<subseteq>
                       the ` {e \<in> range (pdc_walk a m r). \<not> is_fault e}")
   prefer 2 apply (rule non_glb_pdc_subset)
  apply (case_tac "lookup_pdc (the ` {e \<in> range (pdc_walk a m r). \<not> is_fault e}) a v"; clarsimp)
    apply (drule_tac a = a and v= v in asid_pdc_mono, simp)
   apply (clarsimp simp: lookup_pdc_walk_not_incon)
  apply (drule_tac a = a and v= v in asid_pdc_mono, simp)
  by (simp add: asid_pdc_lookup_range_fault_pt_walk' lookup_asid_pdc_hit_entry_range) 


lemma non_global_lookup_pdc_hit_asid:
  "lookup_pdc (non_global_entries_pdc (the ` {e \<in> range (pdc_walk a m r). \<not> is_fault e})) a v = Hit e \<Longrightarrow>
   lookup_pdc (non_global_entries_pdc (the ` {e \<in> range (pdc_walk a' m r). \<not> is_fault e})) a' v =  
            Hit (the (pdc_walk a' m r v))"
  apply (case_tac " lookup_pdc (non_global_entries_pdc (the ` {e \<in> range (pdc_walk a' m r). \<not> is_fault e})) a' v"; clarsimp)
    defer 
    apply (clarsimp simp: non_global_lookup_range_pdc_walk_not_incon)
   apply (frule_tac a = a' in non_global_lookup_range_fault_pt_walk_pdc, 
               drule_tac x = v in bspec, clarsimp simp: lookup_asid_pdc_hit_entry_range, simp) 
  apply (subgoal_tac "lookup_pdc (global_entries_pdc (the ` {e \<in> range (pdc_walk a m r). \<not> is_fault e})) a v = Miss")
  prefer 2
  using non_global_global_disjoint_pdc apply auto[1]
 apply (subgoal_tac "lookup_pdc (global_entries_pdc (the ` {e \<in> range (pdc_walk a' m r). \<not> is_fault e})) a' v = Miss")
   apply (subgoal_tac "\<not>is_fault (pdc_walk a' m r v)")
  using lookup_global_miss_non_fault_pdc apply auto [1]
  apply (subgoal_tac "\<not> is_fault (pdc_walk a m r v)")
    apply (rule_tac a = a in no_fault_pdc_walk_unequal_asid', simp)
   apply (clarsimp simp: non_global_hit_no_fault_pdc)
  by (rule_tac a = a in lookup_global_miss_asid_unequal_pdc, simp)


lemma global_entr_pdc_subset_global_entries:
  "(\<Union>x\<in>global_entries_pdc (the ` {e \<in> range (pdc_walk a m r). \<not> is_fault e}). range_of x)
           \<subseteq>  (\<Union>x\<in>global_entries (the ` {e \<in> range (pt_walk a m r). \<not> is_fault e}). range_of x)"
  apply safe
  apply (clarsimp simp: global_entries_pdc_def is_fault_def pdc_walk_def asid_of_pdc_def split: option.splits pde.splits)
  apply (rename_tac v vba pba fl)
  apply (rule_tac x = "EntrySection None (UCAST(32 \<rightarrow> 12) (addr_val vba >> 20)) (UCAST(32 \<rightarrow> 12) (addr_val pba >> 20)) (to_tlb_flags fl)" in bexI)
   apply (clarsimp simp: range_of_tlb_entry_def range_of_pdc_entry_def)
  apply (clarsimp simp: global_entries_def)
  apply (rule_tac x = "Some (EntrySection None (UCAST(32 \<rightarrow> 12) (addr_val vba >> 20)) (UCAST(32 \<rightarrow> 12) (addr_val pba >> 20)) (to_tlb_flags fl))" in image_eqI)
   apply force
  apply safe
   prefer 2
   apply force
  apply (rule_tac x = vba in range_eqI)
  apply (clarsimp simp:  pt_walk'_pt_walk)
  by (clarsimp simp: pt_walk'_def map_opt_def pdc_walk_def)


lemma asid_unequal_lookup_pdc_walk_miss:
  "a \<noteq> a' \<Longrightarrow> lookup_pdc (non_global_entries_pdc (the ` {e \<in> range (pdc_walk a' m r). \<not> is_fault e})) a v = Miss"
  apply (subgoal_tac "tagged_pdc_entry_set (non_global_entries_pdc (the ` {e \<in> range (pdc_walk a' m r). \<not> is_fault e})) a v = {}")
   apply (clarsimp simp:  lookup_def) 
  apply (clarsimp simp: entry_pdc_set_va_set tag_vadr_pdc_def asid_range_of_pdc_def is_fault_def non_global_entries_pdc_def asid_of_pdc_def) 
  apply safe
  by (clarsimp simp: pdc_walk_def Let_def tag_conv_def split: option.splits pde.splits pte.splits if_split_asm)


lemma lookup_non_global_union_asid_unequal_pdc:
 "a \<noteq> a' \<Longrightarrow> lookup_pdc (non_global_entries_pdc (t \<union> the ` {e \<in> range (pdc_walk a m r). \<not> is_fault e}))  a' v =
                 lookup_pdc (non_global_entries_pdc t) a' v"
  apply (subgoal_tac "non_global_entries_pdc (t \<union> the ` {e \<in> range (pdc_walk a m r). \<not> is_fault e}) =
       non_global_entries_pdc t \<union> non_global_entries_pdc (the ` {e \<in> range (pdc_walk  a m r). \<not> is_fault e})")
   prefer 2
   apply (clarsimp simp: non_global_entries_pdc_def) apply blast
  apply clarsimp
  apply (subgoal_tac " lookup_pdc (non_global_entries_pdc (the ` {e \<in> range (pdc_walk  a m r). \<not> is_fault e}))  a' v  = Miss")
  using lookup_asid_pdc_miss_union_equal apply blast
  using asid_unequal_lookup_pdc_walk_miss by auto



lemma lookup_non_global_union_asid_unequal_pdc':
 "\<lbrakk>a \<noteq> a''; a' \<noteq> a''; a' \<noteq> a \<rbrakk> \<Longrightarrow>
     lookup_pdc (non_global_entries_pdc (t \<union> the ` {e \<in> range (pdc_walk a m r). \<not> is_fault e}))
              a' v =
             lookup_pdc (non_global_entries_pdc t) a' v"
  apply (subgoal_tac "non_global_entries_pdc (t \<union> the ` {e \<in> range (pdc_walk a m r). \<not> is_fault e}) =
       non_global_entries_pdc t \<union> non_global_entries_pdc (the ` {e \<in> range (pdc_walk a m r). \<not> is_fault e})")
   prefer 2
   apply (clarsimp simp: non_global_entries_pdc_def) apply blast
  apply clarsimp
  apply (subgoal_tac " lookup_pdc (non_global_entries_pdc (the ` {e \<in> range (pdc_walk a m r). \<not> is_fault e})) a' v  = Miss")
  using lookup_asid_pdc_miss_union_equal apply blast
  using asid_unequal_lookup_pdc_walk_miss by auto 



lemma asid_unequal_lookup_non_global_asid_flush_pt_walk_pdc:
  "a' \<noteq> a \<Longrightarrow>
       lookup_pdc (non_global_entries_pdc (t - {e \<in> t. asid_of_pdc e = Some a} \<union> the ` {e \<in> range (pdc_walk a m r). \<not> is_fault e})) a' v =
           lookup_pdc (non_global_entries_pdc t) a' v"
  apply (clarsimp simp: non_global_entries_union_pdc)
  apply (subgoal_tac "lookup_pdc (non_global_entries_pdc (the ` {e \<in> range (pdc_walk a m r). \<not> is_fault e})) a' v = Miss")
   prefer 2
   apply (rule asid_unequal_lookup_pdc_walk_miss, simp)
  apply (cases "lookup_pdc (non_global_entries_pdc (t - {e \<in> t. asid_of_pdc e = Some a}) \<union> non_global_entries_pdc (the ` {e \<in> range (pdc_walk a m r). \<not> is_fault e})) a' v"; clarsimp?)
    apply (subgoal_tac "lookup_pdc (non_global_entries_pdc (t - {e \<in> t. asid_of_pdc e = Some a})) a' v = Miss")
     apply (clarsimp simp: non_global_entries_sub_pdc)
     apply (subgoal_tac "lookup_pdc (non_global_entries_pdc {e \<in> t. asid_of_pdc e = Some a}) a' v = Miss")
      apply (drule lookup_minus_miss_sncd_miss_pdc, simp, simp)
     apply (clarsimp simp: non_global_entries_pdc_def lookup_def tagged_pdc_entry_set_def entry_set_def split: if_split_asm)
    apply (drule lookup_union_miss_sncd_miss_pdc, simp, simp)
   apply (drule lookup_asid_pdc_incon_not_miss, simp)
   apply (clarsimp simp: non_global_entries_sub_pdc)
  using lookup_asid_pdc_incon_minus apply force
  apply (drule lookup_asid_pdc_hit_mis_hit, simp)
  apply (clarsimp simp: non_global_entries_sub_pdc)
  apply (subgoal_tac "lookup_pdc (non_global_entries_pdc {e \<in> t. asid_of_pdc e = Some a}) a' v = Miss")
   apply (frule lookup_asid_pdc_minus_hit', simp, simp)
  by (clarsimp simp: non_global_entries_pdc_def lookup_def tagged_pdc_entry_set_def entry_set_def split: if_split_asm)




end