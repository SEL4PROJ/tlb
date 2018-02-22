theory  ARMv7_Flush_Ref

imports 
   ARMv7_Update_ASID_Ref

begin               


(* flushing complete TLB *)




lemma flush_tlb_non_det_det_refine:
  "\<lbrakk> Flush_TLB (s::tlb_state) = ((), s') ;   Flush_TLB (t::tlb_det_state) = ((), t'); 
         tlb_rel (typ_tlb s) (typ_det_tlb t) \<rbrakk> \<Longrightarrow>  tlb_rel (typ_tlb s') (typ_det_tlb t') "
  apply (clarsimp simp:  Flush_TLB_tlb_state_ext_def  Flush_TLB_tlb_det_state_ext_def tlb_rel_def) 
  by (cases s, cases t , clarsimp simp: state.defs tlb_rel_def) 


lemma  flush_tlb_det_sat_refine:
  "\<lbrakk> Flush_TLB (s::tlb_det_state) = ((), s') ;  Flush_TLB(t::tlb_sat_state) = ((), t'); 
         tlb_rel_sat (typ_det_tlb s) (typ_sat_tlb t) \<rbrakk> \<Longrightarrow> 
                  tlb_rel_sat (typ_det_tlb s') (typ_sat_tlb t')"
  apply (clarsimp simp: Flush_TLB_tlb_det_state_ext_def Flush_TLB_tlb_sat_state_ext_def)
  apply (clarsimp simp: tlb_rel_sat_def saturated_def)
  apply (cases s, cases t , clarsimp simp: state.defs)
  done


lemma flush_tlb_sat_abs_refine':
  "\<lbrakk>Flush_TLB (s::tlb_sat_state) = ((), s') ;  Flush_TLB (t::tlb_incon_state') = ((), t'); 
             tlb_rel_abs' (typ_sat_tlb s) (typ_incon' t) \<rbrakk> \<Longrightarrow> 
                     tlb_rel_abs' (typ_sat_tlb s') (typ_incon' t')"
  apply (clarsimp simp: Flush_TLB_tlb_sat_state_ext_def
      Flush_TLB_tlb_incon_state'_ext_def tlb_rel_abs'_def)
  apply (rule conjI)
   apply (cases s, cases t, clarsimp simp: state.defs)
  apply (rule conjI)
   apply (clarsimp simp: asid_va_incon_tlb_mem_def)
   apply (rule conjI)
    apply (clarsimp simp: asid_va_incon_def lookup_range_pt_walk_not_incon')
   apply (clarsimp simp: asid_va_hit_incon_inter_def)
   apply (rule conjI)
    apply (clarsimp simp: asid_va_hit_incon'_def)
    apply (frule lookup_range_fault_pt_walk)
    apply (drule_tac x = b in bspec)
     apply (clarsimp simp: lookup_hit_entry_range)
    apply clarsimp
   apply (clarsimp simp: asid_va_hit_incon''_def lookup_miss_is_fault_intro)
  apply (rule conjI)
   apply (clarsimp simp: saturated_def)
  apply (clarsimp simp: snapshot_of_tlb_def asid_unequal_miss'')
  done




lemma flush_tlb_abs_abs_refine':
  "\<lbrakk>Flush_TLB (s::tlb_incon_state') = ((), s') ;  Flush_TLB (t::tlb_incon_state) = ((), t'); 
             refine_rel (typ_incon' s) (typ_incon'2 t) \<rbrakk> \<Longrightarrow> 
                     refine_rel (typ_incon' s') (typ_incon'2 t')"
  apply (clarsimp simp: Flush_TLB_tlb_incon_state'_ext_def
                        Flush_TLB_tlb_incon_state_ext_def refine_rel_def)
  by (cases s, cases t, clarsimp simp: state.defs)
 



lemma flush_asid_non_det_det_refine:
  "\<lbrakk> Flush_ASID a (s::tlb_state) = ((), s') ; Flush_ASID a (t::tlb_det_state) = ((), t'); 
         tlb_rel (typ_tlb s) (typ_det_tlb t) \<rbrakk> \<Longrightarrow>  tlb_rel (typ_tlb s') (typ_det_tlb t') "
  apply (clarsimp simp:  Flush_ASID_tlb_state_ext_def  Flush_ASID_tlb_det_state_ext_def  tlb_rel_def) 
  apply (cases s, cases t , clarsimp simp: state.defs tlb_rel_def) 
  by blast

lemma  flush_asid_det_sat_refine:
  "\<lbrakk> Flush_ASID a (s::tlb_det_state) = ((), s') ;  Flush_ASID a (t::tlb_sat_state) = ((), t'); 
         tlb_rel_sat (typ_det_tlb s) (typ_sat_tlb t) \<rbrakk> \<Longrightarrow> 
                  tlb_rel_sat (typ_det_tlb s') (typ_sat_tlb t')"
  apply (clarsimp simp: Flush_ASID_tlb_det_state_ext_def Flush_ASID_tlb_sat_state_ext_def)
  apply (clarsimp simp: tlb_rel_sat_def saturated_def)
  apply (cases s, cases t , clarsimp simp: state.defs)
  by blast

lemma lookup_incon_minus:
  "lookup (t - t') a v  = Incon  \<Longrightarrow> lookup t a v = Incon"
  apply (subgoal_tac "t - t' \<subseteq> t")
   apply (frule_tac a = a and v = v in tlb_mono)
   apply clarsimp
  by blast


lemma  lookup_asid_incon_diff:
  "lookup (t - {e \<in> t . asid_entry e = a}) a' v = Incon \<Longrightarrow>
        a' \<noteq> a"
  by (clarsimp simp: lookup_def entry_set_def entry_range_asid_tags_def split: if_split_asm)


lemma  lookup_asid_hit_diff:
  "lookup (t - {e \<in> t . asid_entry e = a}) a' v = Hit x \<Longrightarrow>
        a' \<noteq> a"
  by (clarsimp simp: lookup_def entry_set_def entry_range_asid_tags_def split: if_split_asm)


 
lemma  lookup_minus_hit_asid_hit:
  "\<lbrakk>lookup (tlb_sat_set s - {e \<in> tlb_sat_set s. asid_entry e = a}) a' va = Hit x; a \<noteq> a'\<rbrakk> \<Longrightarrow> 
                         lookup (tlb_sat_set s) a' va = Hit x"
  apply (clarsimp simp: lookup_def entry_set_def entry_range_asid_tags_def split: if_split_asm)
  apply safe
  by auto


lemma lookup_tlb_minus_asid_miss:
  "lookup (tlb - {e \<in> tlb. asid_entry e = a}) a va = Miss"
  apply (clarsimp simp: lookup_def entry_set_def entry_range_asid_tags_def split: if_split_asm)
  by auto


lemma diff_asid_lookup_union:
  "\<lbrakk> a' \<noteq> a; a' \<noteq> a'';
       asid_entry ` the ` {e \<in> range (pt_walk a'' m r). \<not> is_fault e} = {a''}  \<or>
            asid_entry ` the ` {e \<in> range (pt_walk a'' m r). \<not> is_fault e} = {}\<rbrakk>  \<Longrightarrow> 
                 lookup (tlb_sat_set s - {e \<in> tlb_sat_set s. asid_entry e = a} \<union>
                        the ` {e \<in> range (pt_walk a'' m r). \<not> is_fault e}) a' va =
                                lookup (tlb_sat_set s) a' va"
  apply (erule disjE)
   apply (cases "lookup (tlb_sat_set s - {e \<in> tlb_sat_set s. asid_entry e = a} \<union>
                 the ` {e \<in> range (pt_walk a'' m r). \<not> is_fault e}) a' va" ; 
      (clarsimp simp: lookup_def entry_set_def entry_range_asid_tags_def split: if_split_asm , fastforce))
  by (cases "lookup (tlb_sat_set s - {e \<in> tlb_sat_set s. asid_entry e = a} \<union>
                 the ` {e \<in> range (pt_walk a'' m r). \<not> is_fault e})  a' va"; 
      (clarsimp simp: lookup_def entry_set_def entry_range_asid_tags_def split: if_split_asm , fastforce))

lemma  asid_entry_set_inter:
  "a \<noteq> ASID s  \<Longrightarrow>   
     {e \<in> tlb_sat_set s. asid_entry e = a} \<inter> the ` {e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e} = {}"
  apply (case_tac "{e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e} = {}")
   apply simp
   apply blast
  apply (subgoal_tac "asid_entry ` the ` {e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e} = {ASID s}")
   apply (subgoal_tac "\<forall>e1 e2. asid_entry e1 = a \<and> asid_entry e2 = ASID s \<longrightarrow> e1 \<noteq> e2")
    apply clarsimp
    apply blast
   apply blast
  apply (subgoal_tac "asid_entry ` the ` {e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e} \<noteq> {}")
   prefer 2
   apply blast
  by (insert asid_entry_set_pt_walk1 [of "ASID s" "MEM s" "TTBR0 s"], clarsimp)



lemma flush_asid_sat_abs_refine':
  "\<lbrakk>Flush_ASID a (s::tlb_sat_state) = ((), s') ;  Flush_ASID a (t::tlb_incon_state') = ((), t'); 
             tlb_rel_abs' (typ_sat_tlb s) (typ_incon' t) \<rbrakk> \<Longrightarrow> tlb_rel_abs' (typ_sat_tlb s') (typ_incon' t')"
  apply (clarsimp simp: Flush_ASID_tlb_sat_state_ext_def Flush_ASID_tlb_incon_state'_ext_def tlb_rel_abs'_def)
  apply (rule conjI)
   apply (cases s, cases t, clarsimp simp: state.defs)
  apply (subgoal_tac "tlb_sat_set s = tlb_sat_set s \<union> 
                              the ` {e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e}")
   prefer 2
   apply (drule sat_state_tlb', clarsimp simp: state.defs)
  apply (rule conjI)
   apply (clarsimp simp: asid_va_incon_tlb_mem_def)
   apply (rule conjI)
    apply (clarsimp simp: asid_va_incon_def)
    apply (case_tac "a \<noteq> ASID s")
     apply (subgoal_tac "{e \<in> tlb_sat_set s. asid_entry e = a} \<inter> the ` {e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e} = {}")
      apply (subgoal_tac "tlb_sat_set s - {e \<in> tlb_sat_set s. asid_entry e = a} \<union> the ` {e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e} = 
                     tlb_sat_set s - {e \<in> tlb_sat_set s. asid_entry e = a}")
       prefer 2
       apply blast
      apply clarsimp
      apply (rule conjI)
       apply (drule lookup_incon_minus)
       apply blast
      apply (drule lookup_asid_incon_diff, clarsimp)
     apply (clarsimp simp: asid_entry_set_inter)
    apply clarsimp
    apply (drule union_incon_cases1)
    apply (erule disjE)
     apply (clarsimp simp: lookup_range_pt_walk_not_incon')
    apply (erule disjE)
     apply clarsimp
     apply (subgoal_tac "aa \<noteq> ASID s")
      apply (clarsimp simp: asid_unequal_miss'')
     apply (drule lookup_asid_hit_diff , clarsimp)
    apply (erule disjE)
     apply clarsimp
     apply (subgoal_tac "aa \<noteq> ASID s")
      apply (clarsimp simp: asid_unequal_miss'')
     apply (drule lookup_asid_hit_diff , clarsimp)
    apply (erule disjE)
     apply clarsimp
     apply (rule conjI)
      prefer 2
      apply (drule lookup_asid_incon_diff , clarsimp)
     apply (drule lookup_incon_minus)
     apply blast
    apply (erule disjE)
     apply (clarsimp simp: lookup_range_pt_walk_not_incon')
    apply clarsimp
    apply (rule conjI)
     prefer 2
     apply (drule lookup_asid_incon_diff , clarsimp)
    apply (drule lookup_incon_minus)
    apply blast
   apply (clarsimp simp: asid_va_hit_incon_inter_def asid_va_hit_incon'_def)
   apply (rule conjI)
   apply (case_tac "a \<noteq> ASID s")
    apply (subgoal_tac "{e \<in> tlb_sat_set s. asid_entry e = a} \<inter> the ` {e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e} = {}")
     apply (subgoal_tac "tlb_sat_set s - {e \<in> tlb_sat_set s. asid_entry e = a} \<union> the ` {e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e} = 
            tlb_sat_set s - {e \<in> tlb_sat_set s. asid_entry e = a}")
      prefer 2
      apply blast
     apply clarsimp
     apply (subgoal_tac " lookup (tlb_sat_set s) (ASID s) (  b) = Hit x")
      apply blast
     apply (clarsimp simp: lookup_minus_hit_asid_hit)
    apply (clarsimp simp: asid_entry_set_inter)
   apply clarsimp
   apply (drule lookup_hit_union_cases')
   apply (erule disjE)
    apply (clarsimp simp: lookup_tlb_minus_asid_miss)
   apply (erule disjE)
    apply clarsimp
    apply (frule lookup_range_fault_pt_walk)
    apply (drule_tac x = "  b" in bspec)
     apply (clarsimp simp:lookup_hit_entry_range)
    apply (clarsimp)
   apply (clarsimp simp: lookup_tlb_minus_asid_miss)
   apply (clarsimp simp: asid_va_hit_incon''_def)
  apply (rule conjI)
   prefer 2
   using lookup_miss_is_fault_intro lookup_miss_union_equal lookup_tlb_minus_asid_miss apply force
   apply (subgoal_tac " lookup (tlb_sat_set s) (ASID s) b = Hit x")
     apply force
   apply (subgoal_tac "ASID s \<noteq> a")
   apply (simp add: lookup_minus_hit_asid_hit lookup_miss_is_fault_intro lookup_miss_union_equal)
  using lookup_miss_is_fault_intro lookup_miss_union_equal lookup_tlb_minus_asid_miss apply force
  apply (rule conjI)
   apply (clarsimp simp: saturated_def)
  apply (rule conjI)
   apply clarsimp
   apply (rule conjI)
    apply (clarsimp simp: snapshot_of_tlb_def)
     using asid_unequal_miss'' lookup_miss_union_equal lookup_tlb_minus_asid_miss apply force
   apply (clarsimp simp: snapshot_of_tlb_def)
   apply (subgoal_tac "lookup (tlb_sat_set s - {e \<in> tlb_sat_set s. asid_entry e = a} \<union> 
          the ` {e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e}) aa v = lookup (tlb_sat_set s) aa  v")
    apply clarsimp
   apply (subgoal_tac "asid_entry ` the ` {e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e} = {ASID s} \<or>
        asid_entry ` the ` {e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e} = {}")
    prefer 2
    apply (simp only: asid_entry_set_pt_walk1)
   apply (clarsimp simp: diff_asid_lookup_union)
  apply (clarsimp split: if_split_asm)
  apply blast 
  done


lemma flush_asid_abs_abs_refine':
  "\<lbrakk>Flush_ASID a (s::tlb_incon_state') = ((), s') ;  Flush_ASID a (t::tlb_incon_state) = ((), t'); 
             refine_rel (typ_incon' s) (typ_incon'2 t) \<rbrakk> \<Longrightarrow> refine_rel (typ_incon' s') (typ_incon'2 t')"
  apply (clarsimp simp: Flush_ASID_tlb_incon_state_ext_def Flush_ASID_tlb_incon_state'_ext_def refine_rel_def 
      split: if_split_asm)
  by (cases s, cases t, clarsimp simp: state.defs)+



lemma flush_varange_non_det_det_refine:
  "\<lbrakk> Flush_varange vset (s::tlb_state) = ((), s') ; Flush_varange vset (t::tlb_det_state) = ((), t'); 
         tlb_rel (typ_tlb s) (typ_det_tlb t) \<rbrakk> \<Longrightarrow>  tlb_rel (typ_tlb s') (typ_det_tlb t') "
  apply (clarsimp simp:  Flush_varange_tlb_state_ext_def  Flush_varange_tlb_det_state_ext_def 
          tlb_rel_def  ) 
  apply (cases s, cases t , clarsimp simp: state.defs tlb_rel_def) 
  by blast

lemma  flush_varange_det_sat_refine:
  "\<lbrakk> Flush_varange vset (s::tlb_det_state) = ((), s') ;  Flush_varange vset (t::tlb_sat_state) = ((), t'); 
         tlb_rel_sat (typ_det_tlb s) (typ_sat_tlb t) \<rbrakk> \<Longrightarrow> 
                  tlb_rel_sat (typ_det_tlb s') (typ_sat_tlb t')"
  apply (clarsimp simp: Flush_varange_tlb_det_state_ext_def Flush_varange_tlb_sat_state_ext_def)
  apply (clarsimp simp: tlb_rel_sat_def saturated_def )
  apply (cases s, cases t , clarsimp simp: state.defs)
  by blast

lemma saturatd_lookup_hit_no_fault:
  "\<lbrakk>saturated (typ_sat_tlb s);
          lookup (tlb_sat_set s) (ASID s) b = Hit x; \<not> is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) b)\<rbrakk>
                \<Longrightarrow> x = the (pt_walk (ASID s) (MEM s) (TTBR0 s) b)"
  apply (subgoal_tac "lookup (tlb_sat_set s \<union> 
                              the ` {e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e}) (ASID s) (  b) = Hit x")
   prefer 2
   apply (drule sat_state_tlb', clarsimp simp: state.defs)
  apply (drule lookup_hit_miss_or_hit')
  apply (erule disjE)
   apply (clarsimp simp: lookup_range_pt_walk_hit)
  apply (frule lookup_range_fault_pt_walk)
  apply (drule_tac x = "  b" in bspec; clarsimp simp: lookup_hit_entry_range)
  done


lemma  lookup_hit_entry_range_asid_tags:
  "lookup t a va = Hit x \<Longrightarrow> (a, va) \<in> entry_range_asid_tags x"
  apply (clarsimp simp: lookup_def  entry_set_def entry_range_asid_tags_def  split:if_split_asm)
  by force

lemma  lookup_hit_asid:
  "lookup t a va = Hit x \<Longrightarrow> a  = asid_entry x"
  apply (clarsimp simp: lookup_def  entry_set_def entry_range_asid_tags_def  split:if_split_asm)
  by force



lemma  lookup_hit_incon_minus:
  "\<lbrakk>lookup (t- t') a va = Hit x\<rbrakk>
                \<Longrightarrow> lookup t a va = Hit x \<or> lookup t a va = Incon"
  apply (clarsimp simp: lookup_def  entry_set_def entry_range_asid_tags_def  split:if_split_asm)
  by force

lemma  lookup_not_miss_varange:
  "lookup (tlb - (\<Union>v\<in>vset. {e \<in> tlb.   v \<in> entry_range e})) a (  b) \<noteq> Miss \<Longrightarrow>
      b \<notin> vset"
  by (clarsimp simp: lookup_def entry_set_def entry_range_asid_tags_def split:if_split_asm)

lemma lookup_not_miss_varange':
  "v \<in> vset\<Longrightarrow> 
   lookup (tlb_sat_set s - (\<Union>v\<in>vset. {e \<in> tlb_sat_set s.   v \<in> entry_range e})) a (  v) =
               Miss"
  apply (subgoal_tac "entry_set (tlb_sat_set s - 
              (\<Union>v\<in>vset. {e \<in> tlb_sat_set s.   v \<in> entry_range e})) a (  v) = {}")
   apply (clarsimp simp: lookup_def)
  by (clarsimp simp: entry_set_va_set a_va_set_def entry_range_asid_tags_def)


lemma  lookup_minus_union:
  "\<lbrakk>lookup t' a v = Miss; lookup  t'' a v = Miss \<rbrakk> \<Longrightarrow>
      lookup (t - t' \<union> t'') a v = lookup t a v"
  apply (case_tac "lookup t a v" ; clarsimp)
    apply (clarsimp simp: lookup_def  entry_set_def entry_range_asid_tags_def  split:if_split_asm)
    apply force
   apply (clarsimp simp: lookup_def  entry_set_def entry_range_asid_tags_def  split:if_split_asm)
   apply auto [1] apply blast
  apply (clarsimp simp: lookup_def  entry_set_def entry_range_asid_tags_def  split:if_split_asm)
  apply auto
  by blast+



lemma  lookup_minus_same:
  "\<lbrakk>lookup t' a v = Miss \<rbrakk> \<Longrightarrow> lookup (t - t') a v = lookup t a v"
  apply (case_tac "lookup t a v" ; clarsimp)
    apply (clarsimp simp: lookup_def  entry_set_def entry_range_asid_tags_def  split:if_split_asm)
   apply (clarsimp simp: lookup_def  entry_set_def entry_range_asid_tags_def  split:if_split_asm)
   apply auto [1] apply blast
  apply (clarsimp simp: lookup_def  entry_set_def entry_range_asid_tags_def  split:if_split_asm)
  apply auto
  by blast+



lemma  lookup_minus_hit':
  "\<lbrakk>lookup (t - t') a v = Hit x ; lookup t' a v = Miss \<rbrakk> \<Longrightarrow> lookup t a v = Hit x"
  apply (clarsimp simp: lookup_def  entry_set_def entry_range_asid_tags_def  split:if_split_asm)
  apply auto 
  by blast+




lemma flush_varange_sat_abs_refine':
  "\<lbrakk>Flush_varange vset (s::tlb_sat_state) = ((), s') ;  Flush_varange vset (t::tlb_incon_state') = ((), t'); 
             tlb_rel_abs' (typ_sat_tlb s) (typ_incon' t) \<rbrakk> \<Longrightarrow> tlb_rel_abs' (typ_sat_tlb s') (typ_incon' t')"
  apply (clarsimp simp: Flush_varange_tlb_sat_state_ext_def 
      Flush_varange_tlb_incon_state'_ext_def tlb_rel_abs'_def)
  apply (rule conjI)
   apply (cases s, cases t, clarsimp simp: state.defs)
  apply (subgoal_tac "tlb_sat_set s = tlb_sat_set s \<union> 
                              the ` {e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e}")
   prefer 2
   apply (drule sat_state_tlb', clarsimp simp: state.defs)
  apply (rule conjI)
   apply (clarsimp simp: asid_va_incon_tlb_mem_def)
   apply (rule conjI)
    apply (clarsimp simp: asid_va_incon_def)
    apply (drule union_incon_cases1)
    apply (erule disjE)
     apply (clarsimp simp: lookup_range_pt_walk_not_incon')
    apply (erule disjE)
     apply clarsimp
     apply (subgoal_tac "a = ASID s")
      apply clarsimp
      apply (rule conjI)
       prefer 2
       apply (subgoal_tac "  b \<in> entry_range x")
        apply blast
       apply (clarsimp simp:lookup_hit_entry_range)
      apply (subgoal_tac "lookup (tlb_sat_set s) (ASID s) (  b) = Hit x  \<or> 
                     lookup (tlb_sat_set s ) (ASID s) (  b) = Incon")
       apply (erule disjE)
        apply (subgoal_tac "x = the (pt_walk (ASID s) (MEM s) (TTBR0 s) xb)")
         apply clarsimp
        prefer 2
        apply (subgoal_tac " (ASID s, b) \<in> incon_set (tlb_incon_set' t)")
         prefer 2
         apply blast
        apply clarsimp
       prefer 2
       apply (drule lookup_hit_incon_minus, clarsimp)
      prefer 2 
      apply (drule_tac t = "the ` {e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e}" in  lookup_hit_asid)
      apply clarsimp
     prefer 2
     apply (erule disjE)
      apply clarsimp
      apply (clarsimp simp: lookup_range_pt_walk_not_incon')
     apply (erule disjE)
      apply clarsimp
      apply (subgoal_tac " lookup (tlb_sat_set s) a (  b) = Incon")
       apply (rule conjI)
        apply blast
       apply (rule_tac tlb = "tlb_sat_set s" and a = a in lookup_not_miss_varange, clarsimp)
      apply (drule lookup_incon_minus, clarsimp)
     apply (erule disjE)
      apply (clarsimp simp: lookup_range_pt_walk_not_incon')
     apply clarsimp
     apply (subgoal_tac " lookup (tlb_sat_set s) a (  b) = Incon")
      apply (rule conjI)
       apply blast
      apply (rule_tac tlb = "tlb_sat_set s" and a = a in lookup_not_miss_varange, clarsimp)
     apply (drule lookup_incon_minus, clarsimp)
    prefer 2
    apply (clarsimp simp: asid_va_hit_incon_inter_def)
    apply (rule conjI)
     apply (clarsimp simp: asid_va_hit_incon'_def asid_va_hit_incon''_def)
     apply (drule lookup_hit_union_cases')
     apply (erule disjE)
      apply clarsimp
      apply (rule conjI)
       apply (subgoal_tac "lookup (tlb_sat_set s) (ASID s) (  b) = Hit x  \<or> 
                     lookup (tlb_sat_set s ) (ASID s) (  b) = Incon")
        apply (erule disjE)
         prefer 2
         apply (clarsimp simp: asid_va_incon_def , blast)
        apply (subgoal_tac "x \<noteq> the (pt_walk (ASID s) (MEM s) (TTBR0 s) b)")
         apply blast
        apply blast
       apply (drule lookup_hit_incon_minus, clarsimp) 
      apply (rule_tac tlb = "tlb_sat_set s" and a = "ASID s" in lookup_not_miss_varange, clarsimp)
     apply (erule disjE)
      apply clarsimp
      apply (frule lookup_range_fault_pt_walk)
      apply (drule_tac x = b in bspec; clarsimp simp: lookup_hit_entry_range)
     apply clarsimp
     apply (frule lookup_range_fault_pt_walk)
     apply (drule_tac x = b in bspec; clarsimp simp: lookup_hit_entry_range)
    apply (clarsimp simp: asid_va_hit_incon'_def asid_va_hit_incon''_def)
    apply (rule conjI)
     apply (drule lookup_hit_union_cases')
     apply (erule disjE)
      apply clarsimp
      apply (subgoal_tac "lookup (tlb_sat_set s) (ASID s) (  b) = Hit x  \<or> 
                     lookup (tlb_sat_set s ) (ASID s) (  b) = Incon")
       apply (erule disjE)
        prefer 2
        apply (clarsimp simp: asid_va_incon_def , blast)
       apply force
      apply (drule lookup_hit_incon_minus, clarsimp) 
     apply (erule disjE)
      apply (clarsimp simp: lookup_miss_is_fault_intro)
     apply (clarsimp simp: lookup_miss_is_fault_intro)
    prefer 3
    apply (rule conjI)
     apply (clarsimp simp: saturated_def)
    apply (rule conjI)
     apply clarsimp
     apply (rule conjI)
      apply (clarsimp simp: snapshot_of_tlb_def)
      apply (subgoal_tac "lookup (tlb_sat_set s - 
                              (\<Union>v\<in>vset. {e \<in> tlb_sat_set s.   v \<in> entry_range e}))  a (  v) =  Miss")
       apply (subgoal_tac "lookup ( the ` {e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e}) a (  v) = Miss")
        apply (rule lookup_miss_union_miss_miss; clarsimp)
       apply (clarsimp simp: lookup_range_pt_walk_asid_miss)
      apply (clarsimp simp: lookup_not_miss_varange')
     apply (clarsimp simp: snapshot_of_tlb_def)
     apply (subgoal_tac "lookup (tlb_sat_set s - (\<Union>v\<in>vset. {e \<in> tlb_sat_set s.   v \<in> entry_range e}) \<union>
                       the ` {e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e}) a (  v) = 
             lookup (tlb_sat_set s - (\<Union>v\<in>vset. {e \<in> tlb_sat_set s.   v \<in> entry_range e}))  a (  v)")
      apply (clarsimp)
      apply (subgoal_tac " lookup (tlb_sat_set s - (\<Union>v\<in>vset. {e \<in> tlb_sat_set s.   v \<in> entry_range e})) a (  v) \<le>
                                lookup (tlb_sat_set s) a (  v)")
       apply (force simp add: less_eq_lookup_type)
      apply (rule tlb_mono)
      apply blast
     apply (rule lookup_miss_union_equal)
     apply (clarsimp simp: lookup_range_pt_walk_asid_miss)
    apply clarsimp
    apply blast
proof -
  fix b :: vaddr and x :: tlb_entry
  assume a1: "is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) b)"
  assume "lookup (tlb_sat_set s - (\<Union>v\<in>vset. {e \<in> tlb_sat_set s. v \<in> entry_range e}) \<union> the ` {e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e}) (ASID s) b = Hit x"
  then have f2: "lookup (the ` {z \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault z}) (ASID s) b = Hit x \<or> lookup (tlb_sat_set s - (\<Union>a\<in>vset. {t \<in> tlb_sat_set s. a \<in> entry_range t})) (ASID s) b = Hit x"
    using lookup_not_hit_false by blast
  have "lookup (the ` {z \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault z}) (ASID s) b \<noteq> Hit x"
    using a1 by (simp add: lookup_miss_is_fault_intro)
  then have "\<exists>T w. lookup (T - (\<Union>a\<in>vset. {t \<in> T. a \<in> entry_range t})) w b \<noteq> Miss"
    using f2 by (metis lookup_type.simps(5))
  then show "b \<notin> vset"
    using lookup_not_miss_varange by blast
next
  fix b :: vaddr and x :: tlb_entry and xb :: vaddr
  assume a1: "lookup (the ` {e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e}) (ASID s) b = Hit (the (pt_walk (ASID s) (MEM s) (TTBR0 s) xb))"
  assume a2: "lookup (tlb_sat_set s) (ASID s) b = Hit x"
  assume a3: "saturated (typ_sat_tlb s)"
  assume "x \<noteq> the (pt_walk (ASID s) (MEM s) (TTBR0 s) xb)"
  have "\<not> is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) b)"
    using a1 lookup_miss_is_fault_intro by force
  then show "x = the (pt_walk (ASID s) (MEM s) (TTBR0 s) xb)"
    using a3 a2 a1 lookup_range_pt_walk_hit saturatd_lookup_hit_no_fault by fastforce
qed



lemma flush_varange_abs_abs_refine':
  "\<lbrakk>Flush_varange vset (s::tlb_incon_state') = ((), s') ;  Flush_varange vset (t::tlb_incon_state) = ((), t'); 
             refine_rel (typ_incon' s) (typ_incon'2 t) \<rbrakk> \<Longrightarrow> refine_rel (typ_incon' s') (typ_incon'2 t')"
  apply (clarsimp simp: Flush_varange_tlb_incon_state_ext_def 
      Flush_varange_tlb_incon_state'_ext_def refine_rel_def split: if_split_asm)
  apply (rule conjI)
   apply (cases s, cases t, clarsimp simp: state.defs)
  by force
 

lemma flush_ASIDvarange_non_det_det_refine:
  "\<lbrakk> Flush_ASIDvarange a vset (s::tlb_state) = ((), s') ; Flush_ASIDvarange a vset (t::tlb_det_state) = ((), t'); 
         tlb_rel (typ_tlb s) (typ_det_tlb t) \<rbrakk> \<Longrightarrow>  tlb_rel (typ_tlb s') (typ_det_tlb t') "
  apply (clarsimp simp:  Flush_ASIDvarange_tlb_state_ext_def  Flush_ASIDvarange_tlb_det_state_ext_def 
          tlb_rel_def) 
  apply (cases s, cases t , clarsimp simp: state.defs tlb_rel_def) 
  by blast

lemma  flush_ASIDvarange_det_sat_refine:
  "\<lbrakk> Flush_ASIDvarange a vset (s::tlb_det_state) = ((), s') ;  Flush_ASIDvarange a vset (t::tlb_sat_state) = ((), t'); 
         tlb_rel_sat (typ_det_tlb s) (typ_sat_tlb t) \<rbrakk> \<Longrightarrow> 
                  tlb_rel_sat (typ_det_tlb s') (typ_sat_tlb t')"
  apply (clarsimp simp: Flush_ASIDvarange_tlb_det_state_ext_def Flush_ASIDvarange_tlb_sat_state_ext_def)
  apply (clarsimp simp: tlb_rel_sat_def saturated_def)
  apply (cases s, cases t , clarsimp simp: state.defs)
  by blast



lemma lookup_miss_diff_asid_varange:
  " a \<noteq> ASID s
              \<Longrightarrow> lookup (\<Union>x\<in>{a} \<times> vset. case x of (a, v) \<Rightarrow> {e \<in> tlb_sat_set s. (a,   v) \<in> entry_range_asid_tags e})
                   (ASID s) (  b) =
                  Miss"
 apply (subgoal_tac "entry_set (\<Union>x\<in>{a} \<times> vset. case x of (a, v) \<Rightarrow> {e \<in> tlb_sat_set s. (a,   v) \<in> entry_range_asid_tags e})
                   (ASID s) (  b) = {}")
   apply (clarsimp simp: lookup_def)
  by (clarsimp simp: entry_set_va_set a_va_set_def entry_range_asid_tags_def)


lemma lookup_asid_va_range_elem:
  "lookup (\<Union>x\<in>{ASID s} \<times> vset. case x of (a, v) \<Rightarrow> {e \<in> tlb_sat_set s. (a,   v) \<in> entry_range_asid_tags e}) (ASID s) (  b) = Hit x \<Longrightarrow>
        b \<in> \<Union>(entry_range ` (\<Union>x\<in>{ASID s} \<times> vset. case x of (a, v) \<Rightarrow> {e \<in> tlb_sat_set s. (a,   v) \<in> entry_range_asid_tags e}))"
  apply (clarsimp simp: lookup_def  entry_set_def entry_range_asid_tags_def  split:if_split_asm)
  by force


lemma  asidvset_elem_lookup_miss:
  "b \<in> vset \<Longrightarrow>  lookup (tlb_sat_set s - (\<Union>v\<in>vset. {e \<in> tlb_sat_set s. (ASID s,   v) \<in> entry_range_asid_tags e}))
                (ASID s) (  b) = Miss"
  apply (clarsimp simp: lookup_def entry_set_def entry_range_asid_tags_def)
  apply safe
  by auto


lemma   asidvset_elem_lookup_miss':
  "b \<in> vset \<Longrightarrow>  lookup (tlb_sat_set s - (\<Union>v\<in>vset. {e \<in> tlb_sat_set s. (a,   v) \<in> entry_range_asid_tags e}))
                a (  b) = Miss"
  apply (clarsimp simp: lookup_def entry_set_def entry_range_asid_tags_def)
  apply safe
  by auto

lemma  lookup_not_miss_asidvarange:
  "lookup (tlb - (\<Union>v\<in>vset. {e \<in> tlb. (a,   v) \<in> entry_range_asid_tags e})) a (  va) \<noteq> Miss \<Longrightarrow> va \<notin> vset"
  apply (clarsimp simp: lookup_def entry_set_def entry_range_asid_tags_def split:if_split_asm) 
   by auto

lemma flush_ASIDvarange_sat_abs_refine':
  "\<lbrakk>Flush_ASIDvarange a vset (s::tlb_sat_state) = ((), s') ; Flush_ASIDvarange a vset (t::tlb_incon_state') = ((), t'); 
             tlb_rel_abs' (typ_sat_tlb s) (typ_incon' t) \<rbrakk> \<Longrightarrow> tlb_rel_abs' (typ_sat_tlb s') (typ_incon' t')"
  apply (clarsimp simp: Flush_ASIDvarange_tlb_sat_state_ext_def 
      Flush_ASIDvarange_tlb_incon_state'_ext_def tlb_rel_abs'_def)
  apply (rule conjI)
   apply (cases s, cases t, clarsimp simp: state.defs)
  apply (subgoal_tac "tlb_sat_set s = tlb_sat_set s \<union> 
                              the ` {e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e}")
   prefer 2
   apply (drule sat_state_tlb', clarsimp simp: state.defs)
  apply (rule conjI)
   apply (clarsimp simp: asid_va_incon_tlb_mem_def)
   apply (rule conjI)
    apply (clarsimp simp: asid_va_incon_def)
    apply (drule union_incon_cases1)
    apply (erule disjE)
     apply (clarsimp simp: lookup_range_pt_walk_not_incon')
    apply (erule disjE)
     apply clarsimp
     apply (subgoal_tac "aa = ASID s")
      apply clarsimp
      apply (rule conjI)
       apply (subgoal_tac "lookup (tlb_sat_set s) (ASID s) (  b) = Hit x  \<or> 
                     lookup (tlb_sat_set s ) (ASID s) (  b) = Incon")
        apply (erule disjE)
         prefer 2
         apply blast
        apply (subgoal_tac "\<not> is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) b)")
         prefer 2
  using lookup_miss_is_fault_intro apply force
  using lookup_range_pt_walk_hit saturatd_lookup_hit_no_fault apply fastforce
       apply (drule lookup_hit_incon_minus, clarsimp)
      apply (clarsimp simp: asidvset_elem_lookup_miss)
     apply (drule_tac t = "the ` {e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e}" in  lookup_hit_asid , clarsimp)
    apply (erule disjE)
     apply clarsimp
     apply (clarsimp simp: lookup_range_pt_walk_not_incon')
    apply (erule disjE)
     apply clarsimp
     apply (subgoal_tac " lookup (tlb_sat_set s) aa (  b) = Incon")
      apply (rule conjI)
       apply blast
      apply (rule impI)
      apply (rule_tac tlb = "tlb_sat_set s" and a = a in lookup_not_miss_asidvarange, clarsimp)
     apply (drule lookup_incon_minus, clarsimp)
    apply (erule disjE)
     apply (clarsimp simp: lookup_range_pt_walk_not_incon')
    apply clarsimp
    apply (subgoal_tac " lookup (tlb_sat_set s) aa (  b) = Incon")
     apply (rule conjI)
      apply blast
     apply (rule impI)
     apply (rule_tac tlb = "tlb_sat_set s" and a = a in lookup_not_miss_asidvarange, clarsimp)
    apply (drule lookup_incon_minus, clarsimp)
   apply (clarsimp simp: asid_va_hit_incon_inter_def)
   apply (rule conjI)
    apply (clarsimp simp: asid_va_hit_incon'_def)
    apply (drule lookup_hit_union_cases')
    apply (erule disjE)
     apply clarsimp
     apply (rule conjI)
      apply (subgoal_tac "lookup (tlb_sat_set s) (ASID s) (  b) = Hit x  \<or> 
                     lookup (tlb_sat_set s ) (ASID s) (  b) = Incon")
       apply (erule disjE)
        prefer 2
        apply (clarsimp simp: asid_va_incon_def , blast)
       apply force
      apply (drule lookup_hit_incon_minus, clarsimp)
     apply (rule impI)
     apply (rule_tac tlb = "tlb_sat_set s" and a = "ASID s" in lookup_not_miss_asidvarange, clarsimp)
    apply (erule disjE)
     apply clarsimp
     apply (frule lookup_range_fault_pt_walk)
     apply (drule_tac x = "  b" in bspec; clarsimp simp: lookup_hit_entry_range)
    apply clarsimp
    apply (frule lookup_range_fault_pt_walk)
    apply (drule_tac x = "  b" in bspec; clarsimp simp: lookup_hit_entry_range)
   apply (clarsimp simp: asid_va_hit_incon''_def)
   apply (rule conjI)
    apply (drule lookup_hit_union_cases')
    apply (erule disjE)
     apply clarsimp
     apply (subgoal_tac "lookup (tlb_sat_set s) (ASID s) (  b) = Hit x  \<or> 
                     lookup (tlb_sat_set s ) (ASID s) (  b) = Incon")
      apply (erule disjE)
       prefer 2
       apply (clarsimp simp: asid_va_incon_def , blast)
      apply force
     apply (drule lookup_hit_incon_minus, clarsimp)
    apply (erule disjE)
     apply (clarsimp simp: lookup_miss_is_fault_intro)
    apply (clarsimp simp: lookup_miss_is_fault_intro)
   prefer 2
   apply (rule conjI)
    apply (clarsimp simp: saturated_def)
   apply (rule conjI)
    apply clarsimp
    apply (rule conjI)
     apply (clarsimp simp: snapshot_of_tlb_def)
     apply (subgoal_tac "lookup (tlb_sat_set s - 
        (\<Union>v\<in>vset. {e \<in> tlb_sat_set s. (a,   v) \<in> entry_range_asid_tags e}))  a (  v) =  Miss")
      apply (subgoal_tac "lookup ( the `{e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e}) a (  v) = Miss")
       apply (rule lookup_miss_union_miss_miss ; clarsimp)
      apply (clarsimp simp: lookup_range_pt_walk_asid_miss)
     apply (clarsimp simp: asidvset_elem_lookup_miss')
    apply (clarsimp simp: snapshot_of_tlb_def)
    apply (subgoal_tac "lookup (tlb_sat_set s - (\<Union>v\<in>vset. {e \<in> tlb_sat_set s. (a,   v) \<in> entry_range_asid_tags e}) \<union>
                        the ` {e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e}) aa (  v) = 
             lookup (tlb_sat_set s - (\<Union>v\<in>vset. {e \<in> tlb_sat_set s. (a,   v) \<in> entry_range_asid_tags e}))  aa (  v)")
     apply (clarsimp)
     apply (subgoal_tac " lookup (tlb_sat_set s - (\<Union>v\<in>vset. {e \<in> tlb_sat_set s. (a,   v) \<in> entry_range_asid_tags e})) aa (  v) \<le>
                                lookup (tlb_sat_set s) aa (  v)")
      apply (force simp add: less_eq_lookup_type)
     apply (rule tlb_mono)
     apply blast
    apply (rule lookup_miss_union_equal)
    apply (clarsimp simp: lookup_range_pt_walk_asid_miss)
   apply clarsimp
   apply blast
proof -
  fix b :: vaddr and x :: tlb_entry
  assume a1: "lookup (tlb_sat_set s - (\<Union>v\<in>vset. {e \<in> tlb_sat_set s. (a, v) \<in> entry_range_asid_tags e}) \<union> the ` {e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e}) (ASID s) b = Hit x"
  assume "is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) b)"
  moreover
  { assume "lookup (the ` {z \<in> range (pt_walk a (MEM s) (TTBR0 s)). \<not> is_fault z}) a b = Miss"
    then have "(ASID s = a \<longrightarrow> b \<notin> vset) \<or> lookup (tlb_sat_set s - (\<Union>aa\<in>vset. {t \<in> tlb_sat_set s. (a, aa) \<in> entry_range_asid_tags t})) a b = Miss \<and> lookup (the ` {z \<in> range (pt_walk a (MEM s) (TTBR0 s)). \<not> is_fault z}) a b = Miss"
      using lookup_not_miss_asidvarange by blast
    then have "ASID s = a \<longrightarrow> b \<notin> vset"
      using a1 lookup_miss_union_miss_miss by force }
  ultimately show "ASID s = a \<longrightarrow> b \<notin> vset"
    using lookup_miss_is_fault_intro by blast
qed




lemma flush_ASIDvarange_abs_abs_refine':
  "\<lbrakk>Flush_ASIDvarange a vset (s::tlb_incon_state') = ((), s') ; Flush_ASIDvarange a vset (t::tlb_incon_state) = ((), t'); 
             refine_rel (typ_incon' s) (typ_incon'2 t) \<rbrakk> \<Longrightarrow> refine_rel (typ_incon' s') (typ_incon'2 t')"
  apply (clarsimp simp: Flush_ASIDvarange_tlb_incon_state_ext_def 
      Flush_ASIDvarange_tlb_incon_state'_ext_def refine_rel_def split: if_split_asm)
   apply (rule conjI)
    apply (cases s, cases t, clarsimp simp: state.defs)
   prefer 2
   apply (cases s, cases t, clarsimp simp: state.defs)
  apply (cases s, cases t, clarsimp simp: state.defs)
  by blast



end