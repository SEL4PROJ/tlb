theory Simp_Lemmas
  imports  TLB
        
begin


(* lookup' Lemmas *)

lemma Incon_top [iff]: "e \<le> Incon"
  by (simp add: less_eq_lookup_type)

lemma Incon_leq [simp]: "(Incon \<le> e) = (e = Incon)"
  by (auto simp add: less_eq_lookup_type)

lemma Miss_bottom [iff]: "Miss \<le> e"
  by (simp add: less_eq_lookup_type)

lemma leq_Miss [simp]: "(e \<le> Miss) = (e = Miss)"
  by (auto simp add: less_eq_lookup_type)

lemma Hits_le [simp]:
  "(Hit e \<le> Hit e') = (e = e')"
  by (auto simp add: less_eq_lookup_type)

lemma tlb_mono_entry_set:
  "t \<subseteq> t' \<Longrightarrow> entry_set t v \<subseteq> entry_set t' v"
  by (simp add: entry_set_def) blast


abbreviation "lookup' t \<equiv> lookup (entry_set t)" 

lemma tlb_mono:
  "t \<subseteq> t' \<Longrightarrow> lookup' t v \<le> lookup' t' v"
  by (drule tlb_mono_entry_set) (fastforce simp: lookup_def)


lemma lookup_in_tlb:
  "lookup' t v = Hit e \<Longrightarrow> e \<in> t"
  by (auto simp: lookup_def entry_set_def split: if_split_asm)

lemma lookup_incon_subset [simp]:
  "\<lbrakk> s \<subseteq> t ;  lookup' s v = Incon \<rbrakk> \<Longrightarrow>  lookup' t v = Incon"
  by (metis less_eq_lookup_type lookup_type.simps(3) tlb_mono)


lemma entry_set_insert:
  "\<lbrakk> entry_set t v = {}; v \<in> range_of e \<rbrakk> \<Longrightarrow> 
               entry_set (insert e t) v = {e}"
  by (auto simp add: entry_set_def)


lemma lookup_miss_union:
  " lookup'  (t \<union> t') v = Miss  \<Longrightarrow>
      (lookup' t v = Miss \<and> lookup' t' v = Miss)"
  by (auto simp: lookup_def entry_set_def split: if_split_asm)
  

lemma lookup_hit_miss_or_hit' :
  " lookup' (t \<union> t') v = Hit e  \<Longrightarrow> 
              lookup' t' v = Miss \<or> (lookup' t' v = Hit e)"
  apply (clarsimp simp: lookup_def entry_set_def split: if_split_asm)
  by force+

lemma  lookup_hit_entry_range:
  "lookup' t v = Hit e \<Longrightarrow> v \<in> range_of e"
  apply (clarsimp simp: lookup_def  entry_set_def  split:if_split_asm)
  by force

lemma lookup_union_hit_miss_hit :
  "\<lbrakk>lookup' (t \<union> t') v = Hit e ; lookup' t' v \<noteq> Miss \<rbrakk> \<Longrightarrow> lookup' t' v = Hit e"
  apply (clarsimp simp: lookup_def entry_set_def split: if_split_asm)  
  by force+

lemma  lookup_not_hit_miss:
  "\<lbrakk>lookup' (t \<union> t') v = Hit e;   lookup' t v \<noteq> Hit e\<rbrakk> \<Longrightarrow> lookup' t v = Miss   "
  apply (clarsimp simp: lookup_def entry_set_def split: if_split_asm)
   apply safe
  by force+

lemma lookup_union_hit_miss_hit' :
  "\<lbrakk>lookup' (t \<union> t') v = Hit e; lookup' t v \<noteq> Miss \<rbrakk> \<Longrightarrow> lookup' t v = Hit e"
  apply (clarsimp simp: lookup_def entry_set_def split: if_split_asm)
   by force+

lemma  lookup_not_hit_false:
  "\<lbrakk>lookup' (t \<union> t') v = Hit e; lookup' t v \<noteq> Hit e; lookup' t' v \<noteq> Hit e\<rbrakk> \<Longrightarrow> False"
  apply (clarsimp simp: lookup_def entry_set_def split: if_split_asm)
  apply safe by blast+

lemma lookup_not_hit_hit:
  "\<lbrakk>lookup' (t \<union> t') v = Hit e; lookup' t v \<noteq> Hit e\<rbrakk> \<Longrightarrow> lookup' t' v = Hit e"
  apply (clarsimp simp: lookup_def entry_set_def split: if_split_asm , (safe ; force) , force)
  apply auto [1]
  apply (rule_tac x = e in exI)
  by (safe ; force)


lemma lookup_hit_union_cases':
  " lookup' (t \<union> t') v = Hit e  \<Longrightarrow>
      (lookup' t v  = Hit e \<and> lookup' t' v = Miss)  \<or>
      (lookup' t' v = Hit e \<and> lookup' t v  = Miss)  \<or>
      (lookup' t v  = Hit e \<and> lookup' t' v = Hit e)"
  apply (safe , clarsimp)
         apply (drule lookup_not_hit_hit; clarsimp)
        apply (drule lookup_not_hit_miss; clarsimp)
       apply (drule lookup_not_hit_false ; clarsimp) 
      apply (drule lookup_not_hit_false ; clarsimp)
     apply (drule lookup_union_hit_miss_hit ; clarsimp)
    apply (drule lookup_not_hit_miss ; clarsimp)
   apply (drule lookup_union_hit_miss_hit ; clarsimp)
  by (drule lookup_hit_miss_or_hit' ; clarsimp)


lemma  union_incon_cases:
  "lookup' (t \<union> t') v = Incon \<Longrightarrow> 
      (lookup' t v = Incon \<and> lookup' t' v = Incon)  \<or>
      ((\<exists>x\<in>t. lookup' t v = Hit x)  \<and> (\<exists>x\<in>t'. lookup' t' v = Hit x) \<and>  lookup' t v \<noteq>  lookup' t' v)  \<or>
      (lookup' t' v = Incon \<and> (\<exists>x\<in>t. lookup' t v = Hit x) ) \<or>
      ((\<exists>x\<in>t'. lookup' t' v = Hit x)  \<and> lookup' t v = Incon)\<or>
      (lookup' t v = Miss \<and> lookup' t' v = Incon)  \<or>
      (lookup' t v = Incon \<and> lookup' t' v = Miss) "
  apply (clarsimp simp: lookup_def entry_set_def split: if_split_asm)
  apply auto
   by force+


lemma entry_set_hit_entry_range:
  "entry_set t v = {e} \<Longrightarrow> v \<in> range_of e"
  apply (clarsimp simp: entry_set_def split:if_split_asm)
   apply force
done


lemma addr_val_eqD [dest!]:
  "addr_val a = addr_val b \<Longrightarrow> a = b"
  apply (cases a, cases b)
  by simp


theorem entry_range_single_elementI:
  "\<lbrakk>x\<in> t ; v \<in> range_of x ; (\<forall>y\<in>t. y\<noteq>x \<longrightarrow> v \<notin> range_of y) \<rbrakk> \<Longrightarrow> 
         {E \<in> t. v \<in> range_of E} = {x}" 
   by force

lemma lookup_hit_mis_hit:
  "\<lbrakk>lookup' (t \<union> t') v = Hit e ; lookup' t' v = Miss \<rbrakk> \<Longrightarrow> lookup' t v = Hit e"
  apply (clarsimp simp: lookup_def entry_set_def split: if_split_asm)
  apply auto
  by force


lemma   lookup_union_hit_hit_miss :
  "\<lbrakk>lookup' (t \<union> t') v = Hit e ;  \<forall>x\<in>t. lookup' t v \<noteq> Hit x\<rbrakk> \<Longrightarrow> lookup' t v = Miss"
 apply (clarsimp simp: lookup_def entry_set_def split: if_split_asm)
  by force+


lemma lookup_hit_miss_or_hit :
  " lookup' (t \<union> t') v = Hit e \<and> e \<in> t  \<Longrightarrow> 
              lookup' t' v = Miss \<or> (lookup' t' v = Hit e)"
  apply (clarsimp simp: lookup_def entry_set_def split: if_split_asm)
  by force+

lemma not_miss_incon_hit:
  "lookup' t v \<noteq> Miss \<Longrightarrow> lookup' t v = Incon \<or> (\<exists>x\<in>t. lookup' t v = Hit x)"
 apply (clarsimp simp: lookup_def entry_set_def split: if_split_asm)
  by auto



lemma  lookup_hit_union_cases:
  "(\<exists>x\<in>(t \<union> t'). lookup' (t \<union> t') va = Hit x)  \<Longrightarrow>
      ((\<exists>x\<in>t. lookup' t va = Hit x) \<and> lookup' t' va = Miss)       \<or>
      ((\<exists>x\<in>t'. lookup' t' va = Hit x)  \<and> lookup' t va = Miss)      \<or>
      ((\<exists>x\<in>t. \<exists>x'\<in>t'.  lookup' t va = Hit x  \<and> lookup' t' va = Hit x' \<and>  x = x')) "
  apply (safe ; clarsimp)
         apply (clarsimp simp: lookup_def entry_set_def split: if_split_asm ,force , force, ((safe ; force) [1]))
        apply (clarsimp simp: lookup_def entry_set_def split: if_split_asm , force, force)
       apply (drule_tac x = "x" in bspec , clarsimp)
       apply (drule_tac not_miss_incon_hit , erule disjE ; clarsimp )
       using lookup_hit_miss_or_hit apply force
      apply (frule lookup_union_hit_miss_hit , clarsimp)
      apply (drule_tac x = "x" in bspec ,clarsimp)
      apply (subgoal_tac "x \<in> t'" , clarsimp)
       apply (clarsimp simp: lookup_def entry_set_def split: if_split_asm ; force)
      using lookup_in_tlb apply force
     apply (clarsimp simp: lookup_def entry_set_def split: if_split_asm ;  (safe ; force))
    using lookup_union_hit_hit_miss apply blast
   apply (clarsimp simp: lookup_def entry_set_def split: if_split_asm ; (safe ; force))
  apply (cases " lookup' t va = Miss" ; clarsimp)
  apply (frule_tac lookup_union_hit_miss_hit ; clarsimp)
  apply (frule_tac lookup_union_hit_miss_hit' ; clarsimp)
  apply (subgoal_tac "x\<in>t")
   apply (drule_tac x = "x" in bspec ; clarsimp)
  using lookup_in_tlb by force


lemma lookup_miss_union_equal:
  " lookup' t' v = Miss \<Longrightarrow> lookup' (t \<union> t') v = lookup' t v "
  apply (clarsimp simp: lookup_def entry_set_def split: if_split_asm)
  apply safe
  by force+



lemma lookup_miss_union_miss_miss:
  "\<lbrakk>lookup' t v = Miss;  lookup' t' v = Miss\<rbrakk> \<Longrightarrow> 
           lookup' (t \<union> t') v = Miss"
  apply (clarsimp simp: lookup_def entry_set_def  split: if_split_asm)
  apply safe
     by auto




lemma  lookup_incon_not_miss:
   "\<lbrakk> lookup' (t \<union> t') v = Incon ; lookup' t' v = Miss\<rbrakk> \<Longrightarrow> lookup' t v = Incon"
  apply (clarsimp simp: lookup_def entry_set_def split: if_split_asm)
  apply safe
  by force+

lemma lookup_hit_diff_union_incon:
  "\<lbrakk>lookup' t v = Hit e ; lookup' t' v = Hit e' ; e \<noteq> e'\<rbrakk> \<Longrightarrow> lookup' (t \<union> t') v = Incon"
  apply (clarsimp simp: lookup_def entry_set_def   split: if_split_asm)
  apply safe
     apply force
    apply (metis (no_types, lifting) mem_Collect_eq singletonD)
   apply (metis (no_types, lifting) mem_Collect_eq singletonD)
  apply force
  done

lemma lookup_miss_union_hit_intro:
  "\<lbrakk>lookup' t v = Miss;  lookup' t' v = Hit e\<rbrakk> \<Longrightarrow> 
           lookup' (t \<union> t') v = Hit e"
  apply (clarsimp simp: lookup_def entry_set_def   split: if_split_asm)
  apply safe
  by (auto, force)

lemma lookup_miss_union_hit_intro':
  "\<lbrakk> lookup' t v = Hit e ; lookup' t' v = Miss\<rbrakk> \<Longrightarrow> 
           lookup' (t \<union> t') v = Hit e"
  apply (clarsimp simp: lookup_def entry_set_def   split: if_split_asm)
  apply safe
  apply auto
  by blast
 
lemma lookup_union_hit_hit:
  "\<lbrakk> lookup' t v = Hit e ; lookup' t' v = Hit e\<rbrakk> \<Longrightarrow> 
           lookup' (t \<union> t') v = Hit e"
  apply (clarsimp simp: lookup_def entry_set_def   split: if_split_asm)
  apply safe
  apply auto
  by blast+

lemma
  "\<lbrakk> lookup' t v \<noteq> Incon; lookup' t v \<noteq> Miss\<rbrakk>
         \<Longrightarrow> \<exists>e\<in>t. lookup' t v = Hit e"
  apply (clarsimp simp: lookup_def entry_set_def split: if_split_asm) 
  by blast

lemma not_miss_incon_hit':
  "lookup' t v = Incon \<or> (\<exists>e\<in>t. lookup' t v = Hit e) \<Longrightarrow> lookup' t v \<noteq> Miss "
  by (clarsimp simp: lookup_def entry_set_def split: if_split_asm)


lemma lookup_incon_minus:
  "lookup' (t - t') v  = Incon  \<Longrightarrow> lookup' t v = Incon"
  apply (subgoal_tac "t - t' \<subseteq> t")
   apply (frule_tac v = v in tlb_mono)
   apply clarsimp
  by blast


lemma  lookup_hit_entry_range_asid_tags:
  "lookup' t v = Hit e \<Longrightarrow> v \<in> range_of e"
  apply (clarsimp simp: lookup_def  entry_set_def    split:if_split_asm)
  by force


lemma  lookup_hit_incon_minus:
  "\<lbrakk>lookup' (t - t') v = Hit e\<rbrakk>
                \<Longrightarrow> lookup' t v = Hit e \<or> lookup' t v = Incon"
  apply (clarsimp simp: lookup_def  entry_set_def    split:if_split_asm)
  by force


lemma  lookup_not_miss_varange:
  "lookup' (t - (\<Union>v\<in>vset. {e \<in> t. v \<in> range_of e})) v \<noteq> Miss \<Longrightarrow>
      v \<notin> vset"
  by (clarsimp simp: lookup_def entry_set_def   split:if_split_asm)


lemma  lookup_minus_union:
  "\<lbrakk>lookup' t' v = Miss; lookup'  t'' v = Miss \<rbrakk> \<Longrightarrow>
      lookup' (t - t' \<union> t'') v = lookup' t v"
  apply (clarsimp simp: lookup_def entry_set_def   the_elem_def image_iff split: lookup_type.splits if_split_asm cong: Collect_cong)
  apply safe
                   apply blast 
                  apply blast
                 apply blast
                apply (clarsimp simp: the_elem_def) by blast+
          
lemma  lookup_minus_same:
  "\<lbrakk>lookup' t' v = Miss \<rbrakk> \<Longrightarrow> lookup' (t - t') v = lookup' t v"
  apply (clarsimp simp: lookup_def  entry_set_def    split: lookup_type.splits if_split_asm)
    by (auto; blast+)


lemma  lookup_minus_hit':
  "\<lbrakk>lookup' (t - t') v = Hit e ; lookup' t' v = Miss \<rbrakk> \<Longrightarrow> lookup' t v = Hit e"
  apply (clarsimp simp: lookup_def  entry_set_def    split:if_split_asm)
   by (auto; blast+) 


lemma  lookup_not_miss_asidvarange:
  "lookup' (t - (\<Union>v\<in>vset. {e \<in> t. v \<in> range_of e})) v \<noteq> Miss \<Longrightarrow> v \<notin> vset"
  by (clarsimp simp: lookup_def entry_set_def   split:if_split_asm) 

lemma  lookup_minus_union':
  "\<lbrakk>lookup' t' v = Miss \<rbrakk> \<Longrightarrow>
      lookup' (t - t' \<union> t'') v = lookup' (t \<union> t'') v"
  apply (case_tac "lookup' (t \<union> t'') v" ; clarsimp simp: lookup_def  entry_set_def    split:if_split_asm)
    apply auto
  by blast+
 

(* bit lemmas *)

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

lemma va_offset_add:
  " (va::32 word) : {ucast (ucast ((x:: 32 word) >> 12):: 20 word) << 12  .. 
    (ucast (ucast (x >> 12):: 20 word) << 12) + mask 12 } \<Longrightarrow>
      \<exists>a.  (0 \<le> a \<and> a \<le> mask 12) \<and>
  va = (ucast (ucast ((x:: 32 word) >> 12):: 20 word) << 12)  + a"
  apply (rule_tac x = "va - (ucast (ucast ((x:: 32 word) >> 12):: 20 word) << 12) " in exI)
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

lemma add_to_or:
  "(a::32 word) \<le> 0xFFF \<Longrightarrow>
     ((x::32 word) && 0xFFFFF000) + a =  (x && 0xFFFFF000) || a"
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

lemma n_bit_shift:
  "\<lbrakk> \<forall>n::nat. n \<in> {12 .. 31} \<longrightarrow>(a::32 word) !! n = (b::32 word) !! n  \<rbrakk>  \<Longrightarrow> a >> 12 = b >> 12"
  apply word_bitwise
  by auto
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

lemma offset_mask_eq:
 "\<lbrakk>ucast (ucast ((x:: 32 word) >> 12):: 20 word) << 12 \<le> va ; 
      va \<le> (ucast (ucast (x >> 12):: 20 word) << 12) + 0x00000FFF\<rbrakk>
          \<Longrightarrow> (( x >> 12) && mask 8 << 2) =  ((va >> 12) && mask 8 << 2)"
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

lemma n_bit_shift_1:
  "\<lbrakk> \<forall>n::nat. n \<in> {12 .. 31} \<longrightarrow>(a::32 word) !! n = (b::32 word) !! n  \<rbrakk>  \<Longrightarrow>  a >> 20 = b >> 20"
  apply word_bitwise
  by auto

lemma offset_mask_eq_1:
  "\<lbrakk>ucast (ucast ((x:: 32 word) >> 12):: 20 word) << 12 \<le> va ; 
      va \<le> (ucast (ucast (x >> 12):: 20 word) << 12) + 0x00000FFF\<rbrakk>
          \<Longrightarrow>((x >> 20) && mask 12 << 2) =  ((va >> 20) && mask 12 << 2)"
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

lemma va_offset_add_1:
  " (va::32 word) : {ucast (ucast ((x:: 32 word) >> 20):: 12 word) << 20  .. 
    (ucast (ucast (x >> 20):: 12 word) << 20) + mask 20 } \<Longrightarrow>
      \<exists>a.  (0 \<le> a \<and> a \<le> mask 20) \<and>
      va = (ucast (ucast ((x:: 32 word) >> 20):: 12 word) << 20)  + a"
  apply (rule_tac x = "va - (ucast (ucast ((x:: 32 word) >> 20):: 12 word) << 20) " in exI)
  apply (clarsimp simp: mask_def)
  apply uint_arith
done

lemma shift_to_mask_1:
  "x AND NOT mask 20 = (ucast (ucast ((x::32 word) >> 20):: 12 word)::32 word) << 20"
  apply (rule word_eqI)
  apply (simp add : word_ops_nth_size word_size)
  apply (simp add : nth_shiftr nth_shiftl nth_ucast)
  apply auto
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

lemma add_to_or_1:
  "(a::32 word) \<le> 0xFFFFF \<Longrightarrow>
     ((x::32 word) && 0xFFF00000) + a =  (x && 0xFFF00000) || a"
  apply word_bitwise
  apply clarsimp
  using xor3_simps carry_simps apply auto
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

lemma n_bit_shift_2:
  "\<lbrakk> \<forall>n::nat. n \<in> {20 .. 31} \<longrightarrow>(a::32 word) !! n = (b::32 word) !! n  \<rbrakk>  \<Longrightarrow>  a >> 20 = b >> 20"
  apply word_bitwise
  by auto


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



(* page table walk simplification lemmas *)

lemma asid_entry_range [simp, intro!]:
  "pt_walk a m r v \<noteq> None \<Longrightarrow> v \<in> range_of (the (pt_walk a m r v))"
  apply (clarsimp simp: range_of_tlb_entry_def pt_walk_def Let_def  split: option.splits ) 
  apply (case_tac x2; clarsimp split:  option.splits)
  apply (case_tac x2a; clarsimp split:  option.splits)
  apply (metis (no_types, hide_lams) Addr_addr_val atLeastAtMost_iff image_iff va_12_left va_12_right)
  by (metis (no_types, hide_lams) Addr_addr_val atLeastAtMost_iff image_iff va_20_left va_20_right)

  



lemma asid_va_entry_range_pt_entry:
  "\<not>is_fault(pt_walk a m r v) \<Longrightarrow> 
      v \<in> range_of (the(pt_walk a m r v))"
  by (clarsimp simp:   is_fault_def)




lemma  va_entry_set_pt_palk_same:
  "\<lbrakk>\<not>is_fault (pt_walk asid m r x) ;
           va \<in> range_of (the (pt_walk asid m r x))\<rbrakk> \<Longrightarrow>
              the(pt_walk asid m r x) = the(pt_walk asid m r va)"
  apply (subgoal_tac "x \<in> range_of (the(pt_walk asid m r x))")
   prefer 2
   apply (clarsimp simp: asid_va_entry_range_pt_entry is_fault_def) 
  apply (cases "the (pt_walk asid m r x)")
   apply (clarsimp simp:   range_of_tlb_entry_def  is_fault_def image_iff)
   apply (cases "get_pde m r x" ; clarsimp)
    apply (clarsimp simp: pt_walk_def)
   apply (case_tac a ; clarsimp simp: pt_walk_def)
   apply (case_tac "get_pte m x3 x " ; clarsimp)
   apply (subgoal_tac "get_pde m r (Addr xaa) = get_pde m r  (Addr xa)" ; clarsimp)
    apply (subgoal_tac "get_pte m x3 (Addr xaa) = get_pte m x3  (Addr xa)" ; clarsimp)
     apply (case_tac a ; clarsimp)
  using va_offset_higher_bits apply blast
    apply (case_tac a ; clarsimp)
    apply (clarsimp simp:  get_pte_def vaddr_pt_index_def)
    apply (subgoal_tac "(( xaa >> 12) && mask 8 << 2) =
                          (( xa >> 12) && mask 8 << 2) ")
     prefer 2
  using offset_mask_eq apply force
    apply force
   apply (case_tac a ; clarsimp)
   apply (clarsimp simp: get_pde_def vaddr_pd_index_def)
   apply (subgoal_tac "((xaa >> 20) && mask 12 << 2) =
                         ((xa >> 20) && mask 12 << 2) ")
    prefer 2
  using offset_mask_eq_1 apply force
   apply force
  apply (simp only: )
  apply (clarsimp simp:   range_of_tlb_entry_def  is_fault_def)
  apply (cases "get_pde m r x" ; clarsimp simp: pt_walk_def)
  apply (case_tac a ; clarsimp)
   apply (case_tac "get_pte m x3 x" ; clarsimp)
   apply (subgoal_tac "get_pde m r (Addr xaa) = get_pde m r (Addr xa)" ; clarsimp)
    apply (subgoal_tac "get_pte m x3 (Addr xaa) = get_pte m x3 (Addr xa)" ; clarsimp)
     apply (case_tac a ; clarsimp)
    apply (case_tac a ; clarsimp simp: get_pte_def vaddr_pt_index_def)
   apply (case_tac a ; clarsimp simp: get_pde_def vaddr_pd_index_def)
  apply (cases "get_pde m r x" ; clarsimp)
  apply (subgoal_tac "get_pde m r (Addr xaa) = get_pde m r (Addr xa)" ; clarsimp)
  using va_offset_higher_bits_1 apply blast
  apply (clarsimp simp: get_pde_def vaddr_pd_index_def)
  apply (subgoal_tac "((xaa >> 20) && mask 12 << 2) = ((xa >> 20) && mask 12 << 2)")
   apply force
  using shfit_mask_eq by force



lemma  va_entry_set_pt_palk_same':
  "\<lbrakk>\<not>is_fault (pt_walk asid m r x) ;
           va \<in> range_of (the (pt_walk asid m r x))\<rbrakk> \<Longrightarrow>
              pt_walk asid m r x = pt_walk asid m r va"
 apply (subgoal_tac "x \<in> range_of (the(pt_walk asid m r x))")
   prefer 2
   apply (clarsimp simp: asid_va_entry_range_pt_entry is_fault_def)
  apply (cases "the (pt_walk asid m r x)")
     apply (simp only: )
   apply (clarsimp simp:   range_of_tlb_entry_def  is_fault_def)
   apply (cases "get_pde m r x" ; clarsimp simp: pt_walk_def)
   apply (case_tac a ; clarsimp)
   apply (case_tac "get_pte m x3 x " ; clarsimp)
   apply (subgoal_tac "get_pde m r (Addr xaa) = get_pde m r  (Addr xa)" ; clarsimp)
    apply (subgoal_tac "get_pte m x3 (Addr xaa) = get_pte m x3  (Addr xa)" ; clarsimp)
     apply (case_tac a ; clarsimp)
  using va_offset_higher_bits apply blast
    apply (case_tac a ; clarsimp)
    apply (clarsimp simp:  get_pte_def vaddr_pt_index_def)
    apply (subgoal_tac "(( xaa >> 12) && mask 8 << 2) =
                          (( xa >> 12) && mask 8 << 2) ")
     prefer 2
  using offset_mask_eq apply force
    apply force
   apply (case_tac a ; clarsimp)
   apply (clarsimp simp: get_pde_def vaddr_pd_index_def)
   apply (subgoal_tac "((xaa >> 20) && mask 12 << 2) =
                         ((xa >> 20) && mask 12 << 2) ")
    prefer 2
  using offset_mask_eq_1 apply force
   apply force
  apply (simp only: )
  apply (clarsimp simp:   range_of_tlb_entry_def  is_fault_def)
  apply (cases "get_pde m r x" ; clarsimp simp: pt_walk_def)
  apply (case_tac a ; clarsimp)
   apply (case_tac "get_pte m x3 x" ; clarsimp)
   apply (subgoal_tac "get_pde m r (Addr xaa) = get_pde m r (Addr xa)" ; clarsimp)
    apply (subgoal_tac "get_pte m x3 (Addr xaa) = get_pte m x3 (Addr xa)" ; clarsimp)
     apply (case_tac a ; clarsimp)
    apply (case_tac a ; clarsimp simp: get_pte_def vaddr_pt_index_def)
   apply (case_tac a ; clarsimp simp: get_pde_def vaddr_pd_index_def)
  apply (cases "get_pde m r x" ; clarsimp)
  apply (subgoal_tac "get_pde m r (Addr xaa) = get_pde m r (Addr xa)" ; clarsimp)
  using va_offset_higher_bits_1 apply blast
  apply (clarsimp simp: get_pde_def vaddr_pd_index_def)
  apply (subgoal_tac "((xaa >> 20) && mask 12 << 2) = ((xa >> 20) && mask 12 << 2)")
   apply force
  using shfit_mask_eq by force


theorem entry_range_single_element':
  " {E \<in> the ` {e \<in> t. \<not> is_fault e}. v \<in> range_of E} = {x} \<Longrightarrow> 
       v \<in> range_of x \<and> \<not> is_fault (Some x) 
         \<and> (\<forall>y\<in>the ` {e \<in> t. \<not> is_fault e}. y\<noteq>x \<and> 
               \<not> is_fault (Some y) \<longrightarrow> v \<notin> range_of y)" 
  apply safe
    apply force
   apply (clarsimp simp: is_fault_def)
  by force


lemma lookup_range_pt_walk_hit:
  "\<not> is_fault (pt_walk a mem ttbr0  va) \<Longrightarrow> 
        lookup' (the ` {e \<in> range (pt_walk a mem ttbr0). \<not> is_fault e}) va = Hit (the (pt_walk a mem ttbr0  va)) "
  apply (clarsimp simp: lookup_def)
  apply safe
    apply simp
   apply (subgoal_tac "x = the (pt_walk a mem ttbr0 va)" , force)
   apply (clarsimp simp: entry_set_def)
   apply (drule entry_range_single_element')
   apply safe
   apply (unfold Ball_def) [1]
   apply (erule_tac x = "the (pt_walk a mem ttbr0  va)" in allE)
   apply (clarsimp simp: asid_va_entry_range_pt_entry is_fault_def)
  apply (rule_tac x = "the (pt_walk a mem ttbr0 va)" in exI)
  apply (clarsimp simp: entry_set_def)
  apply (rule entry_range_single_elementI)
     apply force
    apply (clarsimp simp: asid_va_entry_range_pt_entry is_fault_def)
  apply (clarsimp simp: asid_va_entry_range_pt_entry is_fault_def)
  by (metis is_fault_def option.sel option.simps(3) va_entry_set_pt_palk_same') 

lemma lookup_range_fault_pt_walk:
  "\<lbrakk>lookup' (the ` {e \<in> range (pt_walk a m r). \<not> is_fault e}) v = Hit x\<rbrakk>  \<Longrightarrow> 
          \<forall>va\<in> range_of x. x = the (pt_walk a m r va)"
  apply (subgoal_tac "x \<in> the ` {e \<in> range (pt_walk a m r). \<not> is_fault e}")
   prefer 2
   using  lookup_in_tlb apply force
  apply clarsimp
  apply (rule va_entry_set_pt_palk_same, simp)
   by (clarsimp simp:  )



lemma  lookup_miss_is_fault_intro:
  "is_fault (pt_walk a m r v) \<Longrightarrow> lookup' (the ` {e \<in> range (pt_walk a m r). \<not> is_fault e}) v = Miss"
  apply (subgoal_tac  "entry_set (the ` {e \<in> range (pt_walk a m r). \<not> is_fault e}) v = {}")
   apply (clarsimp simp: lookup_def)
  apply (clarsimp simp: entry_set_def)
  apply (subgoal_tac "pt_walk a m r xb = pt_walk a m r v", simp)
  using va_entry_set_pt_palk_same' by blast


lemma lookup_range_pt_walk_not_incon:
  "lookup' (the ` {e \<in> range (pt_walk a mem ttbr0). \<not> is_fault e}) va \<noteq> Incon"
  apply (case_tac "\<not>is_fault (pt_walk a mem ttbr0 va)")
   apply (clarsimp simp: lookup_range_pt_walk_hit)
  apply clarsimp
  apply (subgoal_tac " lookup' (the ` {e \<in> pt_walk a mem ttbr0 ` top. \<not> is_fault e}) va = Miss")
   apply (clarsimp simp: lookup_def entry_set_def split: if_split_asm)
  by (clarsimp simp: lookup_miss_is_fault_intro)
 

end