theory ARMv7_Update_ASID_Ref


imports  ARMv7_Update_TTBR0_Ref

begin  




lemma update_ASID_non_det_det_refine:
  "\<lbrakk> update_ASID a (s::tlb_state) = ((), s') ;  update_ASID a (t::tlb_det_state) = ((), t'); 
         tlb_rel (typ_tlb s) (typ_det_tlb t) \<rbrakk> \<Longrightarrow>  tlb_rel (typ_tlb s') (typ_det_tlb t') "
  apply (clarsimp simp: update_ASID_tlb_state_ext_def update_ASID_tlb_det_state_ext_def tlb_rel_def) 
  apply (rule conjI)
   apply (cases s, cases t , clarsimp simp: state.defs tlb_rel_def) 
  by blast

lemma  update_ASID_det_sat_no_flt_refine:
  "\<lbrakk> update_ASID a (s::tlb_det_state) = ((), s') ;  update_ASID a (t::tlb_sat_no_flt_state) = ((), t'); 
         tlb_rel_sat_no_flt (typ_det_tlb s) (typ_sat_no_flt_tlb t) \<rbrakk> \<Longrightarrow> 
                  tlb_rel_sat_no_flt (typ_det_tlb s') (typ_sat_no_flt_tlb t')"
  apply (clarsimp simp: update_ASID_tlb_det_state_ext_def update_ASID_tlb_sat_no_flt_state_ext_def)
  apply (clarsimp simp: tlb_rel_sat_no_flt_def saturated_no_flt_def no_faults_def)
  apply (cases s, cases t , clarsimp simp: state.defs , force)
done

lemma  lookup_incon_not_miss:
   "\<lbrakk> lookup (t \<union> t') a v = Incon ; lookup t' a v = Miss\<rbrakk> \<Longrightarrow>
       lookup t a v = Incon"
  apply (clarsimp simp: lookup_def entry_set_def split: if_split_asm)
  apply safe
  by force+

lemma lookup_hit_diff_union_incon:
  "\<lbrakk>lookup t a v = Hit x ; lookup t' a v = Hit x' ; x \<noteq> x'\<rbrakk> \<Longrightarrow> lookup (t \<union> t') a v = Incon"
  apply (clarsimp simp: lookup_def entry_set_def entry_range_asid_tags_def split: if_split_asm)
  apply safe
     apply force
    apply (metis (no_types, lifting) mem_Collect_eq singletonD singletonI)
   apply (metis (no_types, lifting) mem_Collect_eq singletonD singletonI)
  apply force
  done


lemma asid_va_incon_rewrite:
  "\<lbrakk> a \<noteq> ASID s\<rbrakk> \<Longrightarrow> 
   asid_va_incon (tlb_sat_no_flt_set s \<union> {e \<in> range (pt_walk a (MEM s) (TTBR0 s)). \<not> is_fault e}) =
     asid_va_incon (tlb_sat_no_flt_set s) \<union> 
            ((\<lambda>v. (a, v) ) ` {v. \<exists>x. lookup (tlb_sat_no_flt_set s) a (addr_val v) = Hit x \<and>
                                       x \<noteq> pt_walk a (MEM s) (TTBR0 s) v \<and> \<not> is_fault (pt_walk a (MEM s) (TTBR0 s) v)})"
  apply (clarsimp simp: asid_va_incon_def)
  apply safe
    apply (case_tac "aa \<noteq> a")
     apply (drule union_incon_cases1)
     apply( clarsimp simp: lookup_no_flt_range_pt_walk_not_incon' asid_unequal_miss'')
    apply clarsimp
    apply (drule union_incon_cases1)
    apply (erule disjE)
     apply( clarsimp simp :lookup_no_flt_range_pt_walk_not_incon')
    apply (erule disjE)
     apply clarsimp
     apply (subgoal_tac "pt_walk a (MEM s) (TTBR0 s) xb = pt_walk a (MEM s) (TTBR0 s) (Addr (addr_val b))")
      apply clarsimp
     apply (rule va_entry_set_pt_palk_same)
     apply (clarsimp simp: lookup_def entry_set_hit_entry_range split: if_split_asm)
    apply (clarsimp simp :lookup_no_flt_range_pt_walk_not_incon')
    apply (erule disjE)
     apply (clarsimp simp :lookup_no_flt_range_pt_walk_not_incon')
    apply (clarsimp simp:)
   apply (subgoal_tac "tlb_sat_no_flt_set s \<subseteq> tlb_sat_no_flt_set s \<union> {e \<in> range (pt_walk a (MEM s) (TTBR0 s)). \<not> is_fault e}")
    apply (drule_tac a = aa and v = "addr_val b" in tlb_mono)
    apply force
   apply blast
  apply (subgoal_tac "lookup {e \<in> range (pt_walk a (MEM s) (TTBR0 s)). \<not> is_fault e} a (addr_val x) = Hit (pt_walk a (MEM s) (TTBR0 s) x)")
   apply (clarsimp simp: lookup_hit_diff_union_incon)
  using lookup_range_pt_walk_hit_no_flt apply force
  done



lemma tlb_snapshot_rewrite:
  "(a, b) \<notin> Pair a ` {v. \<exists>x. tlb_snapshot (tlb_incon_set' t) a v = Hit x \<and> x \<noteq> pt_walk a (MEM s) (TTBR0 s) v} \<Longrightarrow>
     (a, b) \<in> Pair a ` {v.  tlb_snapshot (tlb_incon_set' t) a v = Miss} \<or> 
       (a, b) \<in> Pair a ` {v.  tlb_snapshot (tlb_incon_set' t) a v = Incon} \<or> 
         (a, b) \<in> Pair a ` {v. \<exists>x. tlb_snapshot (tlb_incon_set' t) a v = Hit x \<and> x = pt_walk a (MEM s) (TTBR0 s) v}"
  apply (clarsimp simp: image_iff)
  using lookup_type.exhaust by auto

lemma tlb_snapshot_rewrite':
  "(a, v) \<notin> Pair a ` {v. tlb_snapshot (tlb_incon_set' t) a v = Miss \<and> \<not> is_fault (pt_walk a (MEM s) (TTBR0 s) v)} \<Longrightarrow>
       tlb_snapshot (tlb_incon_set' t) a v \<noteq> Miss \<or> (tlb_snapshot (tlb_incon_set' t) a v = Miss \<and> is_fault (pt_walk a (MEM s) (TTBR0 s) v))"
  by (clarsimp simp: image_iff)

lemma lookup_miss_union_hit_intro:
  "\<lbrakk>lookup t a v = Miss;  lookup t' a v = Hit x\<rbrakk> \<Longrightarrow> 
           lookup (t \<union> t') a v = Hit x"
  apply (clarsimp simp: lookup_def entry_set_def entry_range_asid_tags_def split: if_split_asm)
  apply safe
       apply auto 
  by force


lemma lookup_miss_union_hit_intro':
  "\<lbrakk> lookup t a v = Hit x ; lookup t' a v = Miss\<rbrakk> \<Longrightarrow> 
           lookup (t \<union> t') a v = Hit x"
  apply (clarsimp simp: lookup_def entry_set_def entry_range_asid_tags_def split: if_split_asm)
  apply safe
       apply auto 
  by blast


lemma lookup_union_hit_hit:
  "\<lbrakk> lookup t a v = Hit x ; lookup t' a v = Hit x\<rbrakk> \<Longrightarrow> 
           lookup (t \<union> t') a v = Hit x"
  apply (clarsimp simp: lookup_def entry_set_def entry_range_asid_tags_def split: if_split_asm)
  apply safe
       apply auto 
  by blast+


lemma
  "\<lbrakk> lookup t a v \<noteq> Incon; lookup t a v \<noteq> Miss\<rbrakk>
         \<Longrightarrow> \<exists>x\<in>t. lookup t a v = Hit x"
  apply (clarsimp simp: lookup_def entry_set_def split: if_split_asm) 
  by blast



lemma not_miss_incon_hit':
  " lookup t a va = Incon \<or> (\<exists>x\<in>t. lookup t a va = Hit x) \<Longrightarrow> lookup t a va \<noteq> Miss "
 by (clarsimp simp: lookup_def entry_set_def split: if_split_asm)
 


lemma not_fault_range_not_miss:
  "\<not> is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) v) \<Longrightarrow> lookup (tlb_sat_no_flt_set s \<union> {e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e}) (ASID s) (addr_val v) \<noteq> Miss"
  apply (clarsimp simp:)
  apply (clarsimp simp: lookup_def entry_set_va_set  a_va_set_def split: if_split_asm)
  apply (drule_tac x = "pt_walk (ASID s) (MEM s) (TTBR0 s) v" in bspec)
   apply (drule_tac x = "pt_walk (ASID s) (MEM s) (TTBR0 s) v" in spec)
   apply clarsimp
   apply (insert asid_va_entry_range_pt_entry [of "ASID s" "addr_val v" "MEM s" "TTBR0 s" ] , clarsimp)
  apply clarsimp
  done



lemma update_ASID_sat_no_flt_abs_refine':
  "\<lbrakk> update_ASID a (s::tlb_sat_no_flt_state) = ((), s') ;  update_ASID a (t::tlb_incon_state') = ((), t'); 
        tlb_rel_abs' (typ_sat_no_flt_tlb s) (typ_incon' t) \<rbrakk> \<Longrightarrow> 
                       tlb_rel_abs' (typ_sat_no_flt_tlb s') (typ_incon' t')"
  apply (clarsimp simp: update_ASID_tlb_sat_no_flt_state_ext_def update_ASID_tlb_incon_state'_ext_def Let_def)
  apply (frule tlb_rel'_absD)
  apply (case_tac "a = ASID s")
    (* when we update to the same ASID *)
   apply (subgoal_tac "tlb_sat_no_flt_set s = tlb_sat_no_flt_set s \<union> 
         {e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e}")
    prefer 2
    apply (clarsimp simp:  saturated_no_flt_def) 
    apply blast
   apply clarsimp
   apply (clarsimp simp: tlb_rel_abs'_def)
   apply (rule conjI)
    apply (clarsimp simp: state.defs)
   apply (rule conjI)
    apply force
   apply (rule conjI)
    apply clarsimp
    apply (clarsimp simp: snapshot_of_tlb_def snapshot_update_current'_def snapshot_update_current_def
                        snapshot_update_new'_def  snapshot_update_new_def)
   apply (clarsimp simp: snapshot_of_tlb_def snapshot_update_current'_def snapshot_update_current_def
                        snapshot_update_new'_def  snapshot_update_new_def incon_load_def)
   apply force



(* when we update to the new ASID *)
  apply (clarsimp simp: tlb_rel_abs'_def)
  apply (rule conjI)
   apply (clarsimp simp: state.defs)
  apply (rule conjI)
   apply (clarsimp simp: asid_va_incon_tlb_mem_def)
   apply (rule conjI)
    apply (subgoal_tac "asid_va_incon (tlb_sat_no_flt_set s \<union> {e \<in> range (pt_walk a (MEM s) (TTBR0 s)). \<not> is_fault e}) =
     asid_va_incon (tlb_sat_no_flt_set s) \<union> 
            ((\<lambda>v. (a, v) ) ` {v. \<exists>x. lookup (tlb_sat_no_flt_set s) a (addr_val v) = Hit x \<and>
                                       x \<noteq> pt_walk a (MEM s) (TTBR0 s) v \<and> \<not> is_fault (pt_walk a (MEM s) (TTBR0 s) v)})")
     prefer 2
     apply (clarsimp simp: asid_va_incon_rewrite)
    apply (simp only:)
    apply (thin_tac "asid_va_incon (tlb_sat_no_flt_set s \<union> {e \<in> range (pt_walk a (MEM s) (TTBR0 s)). \<not> is_fault e}) =
     asid_va_incon (tlb_sat_no_flt_set s) \<union>
     Pair a `
     {v. \<exists>x. lookup (tlb_sat_no_flt_set s) a (addr_val v) = Hit x \<and> x \<noteq> pt_walk a (MEM s) (TTBR0 s) v \<and> \<not> is_fault (pt_walk a (MEM s) (TTBR0 s) v)}")
    apply (simp only: incon_load_def snapshot_update_current'_def snapshot_update_current_def)
    apply (subgoal_tac " Pair a `
        {v. \<exists>x. lookup (tlb_sat_no_flt_set s) a (addr_val v) = Hit x \<and> x \<noteq> pt_walk a (MEM s) (TTBR0 s) v \<and> \<not> is_fault (pt_walk a (MEM s) (TTBR0 s) v)}
        \<subseteq> incon_set (tlb_incon_set' t) \<union>
           Pair a `
           {v. \<exists>x. ((tlb_snapshot (tlb_incon_set' t))
                    (ASID s :=
                       \<lambda>y. if (ASID s, y) \<in> {ASID s} \<times> UNIV \<inter> incon_set (tlb_incon_set' t) then Incon
                           else if \<not> is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) y) then Hit (pt_walk (ASID s) (MEM s) (TTBR0 s) y)
                                else Miss))
                    a v =
                   Hit x \<and>
                   x \<noteq> pt_walk a (MEM s) (TTBR0 s) v}")
     apply blast
    apply rule
    apply (clarsimp simp: snapshot_of_tlb_def)
    apply (subgoal_tac " tlb_snapshot (tlb_incon_set' t) a x = Hit xa \<or>  tlb_snapshot (tlb_incon_set' t) a x = Incon")
     apply (erule disjE)
      apply force
     (* last assumption of tlb_rel_abs' is needed here , in the case of update asid, only equality is required*)
     apply force
    apply (rule disjCI)
    apply (force simp: less_eq_lookup_type)
   apply (clarsimp simp: asid_va_hit_incon_def)
   apply (clarsimp simp: incon_load_def snapshot_of_tlb_def  snapshot_update_current'_def snapshot_update_current_def)
   apply (drule tlb_snapshot_rewrite)
   apply (erule disjE)
    apply (subgoal_tac "lookup (tlb_sat_no_flt_set s) a (addr_val b) = Miss")
     prefer 2
     apply (clarsimp simp: image_iff)
     apply (drule_tac x = a in spec, clarsimp)
     apply (drule_tac x = b in spec)
     apply force
    apply (drule lookup_hit_union_cases')
    apply (erule disjE , clarsimp)
    apply (erule disjE)
     apply clarsimp
     apply (frule lookup_range_fault_pt_walk)
     apply (subgoal_tac "(addr_val xa) \<in> entry_range x")
      apply force
     apply (clarsimp simp: lookup_def lookup_hit_entry_range split: if_split_asm)
    apply clarsimp
   apply (erule disjE)
    apply force
   apply (drule lookup_hit_union_cases')
   apply (erule disjE)
    apply clarsimp
    apply (subgoal_tac " x = pt_walk a (MEM s) (TTBR0 s) xa")
     apply clarsimp
    apply (drule_tac x = a in spec, clarsimp)
    apply (drule_tac x = xa in spec)
    apply (force simp: less_eq_lookup_type)
   apply (erule disjE , clarsimp)
    apply (frule lookup_range_fault_pt_walk)
    apply (subgoal_tac "(addr_val xa) \<in> entry_range x")
     apply force
    apply (clarsimp simp: lookup_def lookup_hit_entry_range split: if_split_asm)
   apply clarsimp    
   apply (frule lookup_range_fault_pt_walk)
   apply (subgoal_tac "(addr_val xa) \<in> entry_range x")
    apply force
   apply (clarsimp simp: lookup_def lookup_hit_entry_range split: if_split_asm)

  apply (rule conjI)
   apply (clarsimp simp: saturated_no_flt_def)
  apply (rule conjI)
   apply (clarsimp simp: no_faults_def)

  apply (thin_tac " t' = t\<lparr>ASID := a, tlb_incon_set' := tlb_incon_set' t
                         \<lparr>incon_set := incon_set (tlb_incon_set' t) \<union> incon_load (snapshot_update_current' (tlb_snapshot (tlb_incon_set' t)) ({ASID s} \<times> UNIV \<inter> incon_set (tlb_incon_set' t)) (MEM s) (TTBR0 s) (ASID s)) a (MEM s) (TTBR0 s),
                            tlb_snapshot :=
                              snapshot_update_new' (snapshot_update_current' (tlb_snapshot (tlb_incon_set' t)) ({ASID s} \<times> UNIV \<inter> incon_set (tlb_incon_set' t)) (MEM s) (TTBR0 s) (ASID s))
                               ({a} \<times> UNIV \<inter> incon_set (tlb_incon_set' t) \<union> incon_load (snapshot_update_current' (tlb_snapshot (tlb_incon_set' t)) ({ASID s} \<times> UNIV \<inter> incon_set (tlb_incon_set' t)) (MEM s) (TTBR0 s) (ASID s)) a (MEM s) (TTBR0 s))
                               (miss_to_hit (snapshot_update_current' (tlb_snapshot (tlb_incon_set' t)) ({ASID s} \<times> UNIV \<inter> incon_set (tlb_incon_set' t)) (MEM s) (TTBR0 s) (ASID s)) a (MEM s) (TTBR0 s))
                               (consistent_hit (snapshot_update_current' (tlb_snapshot (tlb_incon_set' t)) ({ASID s} \<times> UNIV \<inter> incon_set (tlb_incon_set' t)) (MEM s) (TTBR0 s) (ASID s)) a (MEM s) (TTBR0 s)) (MEM s) (TTBR0 s) a\<rparr>\<rparr>")

(* relationship between snapshot_of_tlb and tlb_snapshot *)

  apply (rule conjI)
   apply (rule allI)
   apply (rule impI)
   apply (rule allI)
   apply (case_tac "aa \<noteq> ASID s")
    apply (simp only: snapshot_of_tlb_def snapshot_update_new'_def snapshot_update_new_def snapshot_update_current'_def snapshot_update_current_def)
    apply clarsimp
    apply (subgoal_tac "lookup (tlb_sat_no_flt_set s \<union> {e \<in> range (pt_walk a (MEM s) (TTBR0 s)). \<not> is_fault e}) aa (addr_val v) =
         lookup (tlb_sat_no_flt_set s) aa (addr_val v)")
     apply clarsimp
    apply (rule lookup_miss_union_equal)
    apply (clarsimp simp: asid_unequal_miss'')
   apply clarsimp
   apply (simp only: snapshot_of_tlb_def snapshot_update_new'_def snapshot_update_new_def snapshot_update_current'_def snapshot_update_current_def)
   apply clarsimp
   apply (rule conjI)
    apply clarsimp
    apply (subgoal_tac "lookup (tlb_sat_no_flt_set s \<union> {e \<in> range (pt_walk a (MEM s) (TTBR0 s)). \<not> is_fault e}) (ASID s) (addr_val v) =
               lookup (tlb_sat_no_flt_set s) (ASID s) (addr_val v)")
     prefer 2
     apply (rule lookup_miss_union_equal)
     apply (clarsimp simp: asid_unequal_miss'')
    apply clarsimp
    apply (subgoal_tac " lookup (tlb_sat_no_flt_set s) (ASID s) (addr_val v) \<noteq> Incon")
     prefer 2
     apply (clarsimp simp:  asid_va_incon_tlb_mem_def asid_va_incon_def)
     apply force
    apply (subgoal_tac "lookup (tlb_sat_no_flt_set s) (ASID s) (addr_val v) = Miss \<or> lookup (tlb_sat_no_flt_set s) (ASID s) (addr_val v) = Hit (pt_walk (ASID s) (MEM s) (TTBR0 s) v)")
     apply force
    apply (rule disjI2)
    apply (clarsimp simp:  asid_va_incon_tlb_mem_def asid_va_hit_incon_def)
    apply (subgoal_tac "lookup (tlb_sat_no_flt_set s) (ASID s) (addr_val v) \<noteq> Miss")
     apply (subgoal_tac "\<exists>x\<in>tlb_sat_no_flt_set s. lookup (tlb_sat_no_flt_set s) (ASID s) (addr_val v) = Hit x")
      apply force
     apply (clarsimp simp: lookup_def entry_set_def split: if_split_asm) 
     apply blast
    apply (subgoal_tac "lookup (tlb_sat_no_flt_set s \<union> 
         {e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e}) (ASID s) (addr_val v) \<noteq> Miss")
     apply (subgoal_tac "tlb_sat_no_flt_set s = tlb_sat_no_flt_set s \<union> 
         {e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e}")
      prefer 2
      apply (clarsimp simp:  saturated_no_flt_def) 
      apply blast
     apply clarsimp
    apply (clarsimp simp:  not_fault_range_not_miss)
   apply clarsimp
   apply (subgoal_tac "lookup (tlb_sat_no_flt_set s \<union> {e \<in> range (pt_walk a (MEM s) (TTBR0 s)). \<not> is_fault e}) (ASID s) (addr_val v) =
               lookup (tlb_sat_no_flt_set s) (ASID s) (addr_val v)")
    prefer 2
    apply (rule lookup_miss_union_equal)
    apply (clarsimp simp: asid_unequal_miss'')
   apply clarsimp
   apply (subgoal_tac " lookup (tlb_sat_no_flt_set s) (ASID s) (addr_val v) \<noteq> Incon")
    prefer 2
    apply (clarsimp simp:  asid_va_incon_tlb_mem_def asid_va_incon_def)
    apply force
   apply (subgoal_tac "lookup (tlb_sat_no_flt_set s) (ASID s) (addr_val v) = Miss \<or> 
                    (\<exists>x\<in>tlb_sat_no_flt_set s. lookup (tlb_sat_no_flt_set s) (ASID s) (addr_val v) = Hit x)")
    prefer 2
    apply (clarsimp simp: lookup_def entry_set_def split: if_split_asm) 
    apply blast
   apply (erule disjE)
    apply clarsimp
:  
  "{v. (ASID b, v) \<in>   ptable_comp (ASID b) (MEM b) (MEM bc) (TTBR0 b) (TTBR0 b)}
           \<subseteq> snd ` ptable_comp (ASID b) (MEM b) (MEM bc) (TTBR0 b) (TTBR0 b)"
  apply (clarsimp simp: subset_image_iff)
  apply (rule_tac x = "ptable_comp (ASID b) (MEM b) (MEM bc) (TTBR0 b) (TTBR0 b)" in exI)
  apply (rule conjI)
   apply simp
  apply (clarsimp simp: ptable_comp_def)
  apply (clarsimp simp: snd_eq_Range)
  by auto   apply clarsimp
   apply (clarsimp simp:  asid_va_incon_tlb_mem_def asid_va_hit_incon_def)
   apply (case_tac "x \<noteq> pt_walk (ASID s) (MEM s) (TTBR0 s) v")
    apply blast
   apply (clarsimp simp: no_faults_def)
  apply (clarsimp simp: snapshot_of_tlb_def snapshot_update_new'_def snapshot_update_new_def snapshot_update_current'_def snapshot_update_current_def incon_load_def miss_to_hit_def consistent_hit_def
      split: if_split_asm)
  by force


end