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

lemma  update_ASID_det_sat_refine:
  "\<lbrakk> update_ASID a (s::tlb_det_state) = ((), s') ;  update_ASID a (t::tlb_sat_state) = ((), t'); 
         tlb_rel_sat (typ_det_tlb s) (typ_sat_tlb t) \<rbrakk> \<Longrightarrow> 
                  tlb_rel_sat (typ_det_tlb s') (typ_sat_tlb t')"
  apply (clarsimp simp: update_ASID_tlb_det_state_ext_def update_ASID_tlb_sat_state_ext_def)
  apply (clarsimp simp: tlb_rel_sat_def saturated_def )
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
   asid_va_incon (tlb_sat_set s \<union> the ` {e \<in> range (pt_walk a (MEM s) (TTBR0 s)). \<not> is_fault e}) =
     asid_va_incon (tlb_sat_set s) \<union> 
            ((\<lambda>v. (a, v) ) ` {v. \<exists>x. lookup (tlb_sat_set s) a v = Hit x \<and>
                                       x \<noteq> the (pt_walk a (MEM s) (TTBR0 s) v) \<and> \<not> is_fault (pt_walk a (MEM s) (TTBR0 s) v)})"
  apply (clarsimp simp: asid_va_incon_def)
  apply safe
    apply (case_tac "aa \<noteq> a")
     apply (drule union_incon_cases1)
     apply( clarsimp simp: lookup_range_pt_walk_not_incon' asid_unequal_miss'')
    apply clarsimp
    apply (drule union_incon_cases1)
    apply (erule disjE)
     apply( clarsimp simp :lookup_range_pt_walk_not_incon')
    apply (erule disjE)
     apply clarsimp
     apply (subgoal_tac "pt_walk a (MEM s) (TTBR0 s) xb = pt_walk a (MEM s) (TTBR0 s) b")
      apply clarsimp
     prefer 2
     apply (erule disjE)
      apply (clarsimp simp :lookup_range_pt_walk_not_incon')
     apply (erule disjE)
      apply (clarsimp simp:)
     apply (erule disjE) 
      apply (clarsimp simp :lookup_range_pt_walk_not_incon')
     apply blast
    prefer 2
    apply (subgoal_tac "tlb_sat_set s \<subseteq> tlb_sat_set s \<union> the ` {e \<in> range (pt_walk a (MEM s) (TTBR0 s)). \<not> is_fault e}")
     apply (drule_tac a = aa and v = "  b" in tlb_mono)
     apply force
    apply blast
   prefer 2
   apply (subgoal_tac "lookup (the `{e \<in> range (pt_walk a (MEM s) (TTBR0 s)). \<not> is_fault e}) a (  x) = Hit (the (pt_walk a (MEM s) (TTBR0 s) x))")
    apply (clarsimp simp: lookup_hit_diff_union_incon)
  using lookup_range_pt_walk_hit apply force
proof -
  fix b :: vaddr and x :: tlb_entry and xb :: vaddr
  assume a1: "lookup (the ` {e \<in> range (pt_walk a (MEM s) (TTBR0 s)). \<not> is_fault e}) a b = Hit (the (pt_walk a (MEM s) (TTBR0 s) xb))"
  assume a2: "\<not> is_fault (pt_walk a (MEM s) (TTBR0 s) xb)"
  have "\<not> is_fault (pt_walk a (MEM s) (TTBR0 s) b)"
    using a1 lookup_miss_is_fault_intro by force
  then show "pt_walk a (MEM s) (TTBR0 s) xb = pt_walk a (MEM s) (TTBR0 s) b"
    using a2 a1 is_fault_def lookup_range_pt_walk_hit by force
qed

lemma tlb_snapshot_rewrite:
  "(a, b) \<notin> Pair a ` {v. \<exists>x. tlb_snapshot (tlb_incon_set' t) a v = Hit x \<and>
                                       (x \<noteq> the (pt_walk a (MEM s) (TTBR0 s) v) \<and> \<not> is_fault (pt_walk a (MEM s) (TTBR0 s) v) \<or> is_fault (pt_walk a (MEM s) (TTBR0 s) v))} \<Longrightarrow>
     (a, b) \<in> Pair a ` {v.  tlb_snapshot (tlb_incon_set' t) a v = Miss} \<or> 
       (a, b) \<in> Pair a ` {v.  tlb_snapshot (tlb_incon_set' t) a v = Incon} \<or> 
         (a, b) \<in> Pair a ` {v. \<exists>x. tlb_snapshot (tlb_incon_set' t) a v = Hit x \<and> x = the(pt_walk a (MEM s) (TTBR0 s) v)}"
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
  "\<not> is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) v) \<Longrightarrow> 
         lookup (tlb_sat_set s \<union> the ` {e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e}) (ASID s) v \<noteq> Miss"
  apply (clarsimp simp:)
  apply (clarsimp simp: lookup_def entry_set_va_set  a_va_set_def split: if_split_asm)
  apply (drule_tac x = "the (pt_walk (ASID s) (MEM s) (TTBR0 s) v)" in bspec)
   apply (drule_tac x = "pt_walk (ASID s) (MEM s) (TTBR0 s) v" in spec)
   apply clarsimp
   apply (insert asid_va_entry_range_pt_entry [of "ASID s" "MEM s" "TTBR0 s" "v"], clarsimp)
  apply clarsimp
  done


lemma update_ASID_sat_abs_refine':
  "\<lbrakk> update_ASID a (s::tlb_sat_state) = ((), s') ;  update_ASID a (t::tlb_incon_state') = ((), t'); 
        tlb_rel_abs' (typ_sat_tlb s) (typ_incon' t) \<rbrakk> \<Longrightarrow> 
                       tlb_rel_abs' (typ_sat_tlb s') (typ_incon' t')"
  apply (clarsimp simp: update_ASID_tlb_sat_state_ext_def update_ASID_tlb_incon_state'_ext_def Let_def)
  apply (frule tlb_rel'_absD)
  apply (case_tac "a = ASID s")
    (* when we update to the same ASID *)
   apply (subgoal_tac "tlb_sat_set s = tlb_sat_set s \<union> 
         the `{e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e}")
    prefer 2
    apply (clarsimp simp:  saturated_def) 
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
   apply (simp split: if_split_asm)
   apply force  
    (* when we update to the new ASID *)
  apply (clarsimp simp: tlb_rel_abs'_def)
  apply (rule conjI)
   apply (clarsimp simp: state.defs)
  apply (rule conjI)
   apply (clarsimp simp: asid_va_incon_tlb_mem_def)
   apply (rule conjI)
    apply (subgoal_tac "asid_va_incon (tlb_sat_set s \<union> the `{e \<in> range (pt_walk a (MEM s) (TTBR0 s)). \<not> is_fault e}) =
     asid_va_incon (tlb_sat_set s) \<union> 
            ((\<lambda>v. (a, v) ) ` {v. \<exists>x. lookup (tlb_sat_set s) a v = Hit x \<and>
                                       x \<noteq> the (pt_walk a (MEM s) (TTBR0 s) v) \<and> \<not> is_fault (pt_walk a (MEM s) (TTBR0 s) v)})")
     prefer 2
     apply (clarsimp simp: asid_va_incon_rewrite)
    apply (simp only:)
    apply (thin_tac "asid_va_incon (tlb_sat_set s \<union> the ` {e \<in> range (pt_walk a (MEM s) (TTBR0 s)). \<not> is_fault e}) =
                   asid_va_incon (tlb_sat_set s) \<union>
              Pair a `
              {v. \<exists>x. lookup (tlb_sat_set s) a v = Hit x \<and> x \<noteq> the (pt_walk a (MEM s) (TTBR0 s) v) \<and> \<not> is_fault (pt_walk a (MEM s) (TTBR0 s) v)}")
    apply (simp only: incon_load_def snapshot_update_current'_def snapshot_update_current_def)
    apply (subgoal_tac " Pair a `
        {v. \<exists>x. lookup (tlb_sat_set s) a (  v) = Hit x \<and> x \<noteq> the (pt_walk a (MEM s) (TTBR0 s) v) \<and> \<not> is_fault (pt_walk a (MEM s) (TTBR0 s) v)}
        \<subseteq> incon_set (tlb_incon_set' t) \<union>
           Pair a `
           {v. \<exists>x. ((tlb_snapshot (tlb_incon_set' t))
                    (ASID s :=
                       \<lambda>y. if (ASID s, y) \<in> {ASID s} \<times> UNIV \<inter> incon_set (tlb_incon_set' t) then Incon
                           else if \<not> is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) y) then Hit (the (pt_walk (ASID s) (MEM s) (TTBR0 s) y))
                                else Miss))
                    a v =
                   Hit x \<and>
                   x \<noteq> the (pt_walk a (MEM s) (TTBR0 s) v)}")
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
   apply (clarsimp simp: asid_va_hit_incon_inter_def asid_va_hit_incon'_def asid_va_hit_incon''_def)
   apply (rule conjI)
    apply (clarsimp simp: incon_load_def snapshot_of_tlb_def  snapshot_update_current'_def snapshot_update_current_def)
    apply (drule tlb_snapshot_rewrite)
    apply (erule disjE)
     apply (subgoal_tac "lookup (tlb_sat_set s) a (  b) = Miss")
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
      apply (subgoal_tac "(  xa) \<in> entry_range x")
       apply force
      apply (clarsimp simp: lookup_def lookup_hit_entry_range split: if_split_asm)
     apply clarsimp
    apply (erule disjE)
     apply force
    apply (drule lookup_hit_union_cases')
    apply (erule disjE)
     apply clarsimp
     apply (subgoal_tac " x = the (pt_walk a (MEM s) (TTBR0 s) xa)")
      apply clarsimp
     apply (drule_tac x = a in spec, clarsimp)
     apply (drule_tac x = xa in spec)
     apply (force simp: less_eq_lookup_type)
    apply (erule disjE , clarsimp)
     apply (frule lookup_range_fault_pt_walk)
     apply (subgoal_tac "(  xa) \<in> entry_range x")
      apply force
     apply (clarsimp simp: lookup_def lookup_hit_entry_range split: if_split_asm)
    apply clarsimp    
    apply (frule lookup_range_fault_pt_walk)
    apply (subgoal_tac "(  xa) \<in> entry_range x")
     apply force
    apply (clarsimp simp: lookup_def lookup_hit_entry_range split: if_split_asm)
    (* from here *)
   apply (subgoal_tac "
            incon_load (snapshot_update_current' (tlb_snapshot (tlb_incon_set' t)) ({ASID s} \<times> UNIV \<inter> incon_set (tlb_incon_set' t)) (MEM s) (TTBR0 s) (ASID s)) a (MEM s) (TTBR0 s) =
            incon_load (tlb_snapshot (tlb_incon_set' t)) a (MEM s) (TTBR0 s)")
    apply simp
    apply (thin_tac "incon_load (snapshot_update_current' (tlb_snapshot (tlb_incon_set' t)) ({ASID s} \<times> UNIV \<inter> incon_set (tlb_incon_set' t)) (MEM s) (TTBR0 s) (ASID s)) a (MEM s) (TTBR0 s) =
            incon_load (tlb_snapshot (tlb_incon_set' t)) a (MEM s) (TTBR0 s)")
    apply (simp only: incon_load_def snapshot_of_tlb_def)
    apply clarsimp
    apply (case_tac "tlb_snapshot (tlb_incon_set' t) a b")
      prefer 3
      apply clarsimp 
     apply (subgoal_tac " lookup (tlb_sat_set s) a b = Hit x")
      apply (drule_tac x = a in spec, clarsimp, drule_tac x = b in spec, force)
     apply (drule lookup_hit_union_cases')
     apply (erule disjE , clarsimp)
     apply (erule disjE, clarsimp) 
      apply (frule lookup_range_fault_pt_walk)
      apply (drule_tac x = b in bspec)
       apply (clarsimp simp: lookup_hit_entry_range)
      apply (clarsimp simp: lookup_miss_is_fault_intro)
     apply (clarsimp simp: lookup_miss_is_fault_intro)
    apply blast
   apply (clarsimp simp: snapshot_update_current'_def snapshot_update_current_def incon_load_def)
  apply (rule conjI)
   apply (clarsimp simp: saturated_def)
  apply (rule conjI)
   apply (rule allI)
   apply (rule impI)
   apply (rule allI)
   apply (case_tac "aa \<noteq> ASID s")
    apply (simp only: snapshot_of_tlb_def snapshot_update_new'_def snapshot_update_new_def snapshot_update_current'_def snapshot_update_current_def)
    apply clarsimp
    apply (subgoal_tac "lookup (tlb_sat_set s \<union> the ` {e \<in> range (pt_walk a (MEM s) (TTBR0 s)). \<not> is_fault e}) aa (  v) =
         lookup (tlb_sat_set s) aa (  v)")
     apply clarsimp
    apply (rule lookup_miss_union_equal)
    apply (clarsimp simp: asid_unequal_miss'')
   apply clarsimp
   apply (simp only: snapshot_of_tlb_def snapshot_update_new'_def snapshot_update_new_def snapshot_update_current'_def snapshot_update_current_def)
   apply clarsimp
   apply (rule conjI)
    apply clarsimp
    apply (subgoal_tac "lookup (tlb_sat_set s \<union> the ` {e \<in> range (pt_walk a (MEM s) (TTBR0 s)). \<not> is_fault e}) (ASID s) (  v) =
               lookup (tlb_sat_set s) (ASID s) (  v)")
     prefer 2
     apply (rule lookup_miss_union_equal)
     apply (clarsimp simp: asid_unequal_miss'')
    apply clarsimp
    apply (subgoal_tac " lookup (tlb_sat_set s) (ASID s) (  v) \<noteq> Incon")
     prefer 2
     apply (clarsimp simp:  asid_va_incon_tlb_mem_def asid_va_incon_def)
     apply force
    apply (subgoal_tac "lookup (tlb_sat_set s) (ASID s) (  v) = Miss \<or> lookup (tlb_sat_set s) (ASID s) (  v) = Hit (the(pt_walk (ASID s) (MEM s) (TTBR0 s) v))")
     apply force
    apply (rule disjI2)
    apply (clarsimp simp:  asid_va_incon_tlb_mem_def asid_va_hit_incon_inter_def asid_va_hit_incon'_def asid_va_hit_incon''_def)
    apply (subgoal_tac "lookup (tlb_sat_set s) (ASID s) (  v) \<noteq> Miss")
     apply (subgoal_tac "\<exists>x\<in>tlb_sat_set s. lookup (tlb_sat_set s) (ASID s) (  v) = Hit x")
      apply fastforce
     apply (clarsimp simp: lookup_def entry_set_def split: if_split_asm) 
     apply blast
    apply (subgoal_tac "lookup (tlb_sat_set s \<union> 
         the ` {e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e}) (ASID s) (  v) \<noteq> Miss")
     apply (subgoal_tac "tlb_sat_set s = tlb_sat_set s \<union> 
         the ` {e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e}")
      prefer 2
      apply (clarsimp simp:  saturated_def) 
      apply blast
     apply clarsimp
    apply (clarsimp simp:  not_fault_range_not_miss)
   apply clarsimp
   apply (subgoal_tac "lookup (tlb_sat_set s \<union> the ` {e \<in> range (pt_walk a (MEM s) (TTBR0 s)). \<not> is_fault e}) (ASID s) (  v) =
               lookup (tlb_sat_set s) (ASID s) (  v)")
    prefer 2
    apply (rule lookup_miss_union_equal)
    apply (clarsimp simp: asid_unequal_miss'')
   apply clarsimp
   apply (subgoal_tac " lookup (tlb_sat_set s) (ASID s) (  v) \<noteq> Incon")
    prefer 2
    apply (clarsimp simp:  asid_va_incon_tlb_mem_def asid_va_incon_def)
    apply force
   apply (subgoal_tac "lookup (tlb_sat_set s) (ASID s) (  v) = Miss \<or> 
                    (\<exists>x\<in>tlb_sat_set s. lookup (tlb_sat_set s) (ASID s) (  v) = Hit x)")
    prefer 2
    apply (clarsimp simp: lookup_def entry_set_def split: if_split_asm) 
    apply blast
   apply (erule disjE)
    apply clarsimp
   apply clarsimp
   apply (clarsimp simp:  asid_va_incon_tlb_mem_def asid_va_hit_incon_inter_def asid_va_hit_incon'_def asid_va_hit_incon''_def )
   apply (case_tac "x \<noteq> the (pt_walk (ASID s) (MEM s) (TTBR0 s) v)")
    apply blast
   apply (clarsimp simp: snapshot_of_tlb_def snapshot_update_new'_def snapshot_update_new_def snapshot_update_current'_def snapshot_update_current_def incon_load_def miss_to_hit_def consistent_hit_def
      split: if_split_asm)
   apply fastforce
  apply (clarsimp simp: snapshot_of_tlb_def snapshot_update_new'_def snapshot_update_new_def snapshot_update_current'_def snapshot_update_current_def incon_load_def miss_to_hit_def consistent_hit_def
      split: if_split_asm)
  apply fastforce
  done


lemma update_ASID_sat_abs_refine'2:
  "\<lbrakk> update_ASID a (s::tlb_incon_state') = ((), s') ;  update_ASID a (t::tlb_incon_state) = ((), t'); 
        refine_rel (typ_incon' s) (typ_incon'2 t) \<rbrakk> \<Longrightarrow> 
                       refine_rel (typ_incon' s') (typ_incon'2 t')"
  apply (clarsimp simp: update_ASID_tlb_incon_state_ext_def update_ASID_tlb_incon_state'_ext_def Let_def)
  apply (frule refine_relD)
  apply (case_tac "a = ASID s")
    (* when we update to the same ASID *)
   apply clarsimp
   apply (clarsimp simp: refine_rel_def)
   apply (rule conjI)
    apply (clarsimp simp: state.defs)
   apply (rule conjI)
    prefer 2
    apply (rule conjI)
     apply (clarsimp)
     apply (clarsimp simp: snapshot_update_current'_def snapshot_update_current_def snapshot_update_current'2_def snapshot_update_current2_def 
      incon_load_incon_def incon_load2_def)
    apply (clarsimp simp: snapshot_update_current'_def snapshot_update_current_def snapshot_update_current'2_def snapshot_update_current2_def 
      incon_load_incon_def incon_load2_def incon_load_def)
    apply force
   apply (clarsimp simp: snapshot_update_current'_def snapshot_update_current_def snapshot_update_current'2_def snapshot_update_current2_def 
      incon_load_incon_def incon_load2_def incon_load_def split: if_split_asm)
  apply (clarsimp simp: refine_rel_def)
  apply (rule conjI)
   apply (clarsimp simp: state.defs)
  apply (rule conjI)
   apply (clarsimp simp: snapshot_update_current'_def snapshot_update_current_def snapshot_update_current'2_def snapshot_update_current2_def 
      incon_load_incon_def incon_load2_def incon_load_def split: if_split_asm)
   apply force
  apply (rule conjI)
   apply (clarsimp simp: snapshot_update_current'_def snapshot_update_current_def snapshot_update_current'2_def snapshot_update_current2_def 
      incon_load_incon_def incon_load2_def)
   apply force
  apply (clarsimp simp: snapshot_update_current'_def snapshot_update_current_def snapshot_update_current'2_def snapshot_update_current2_def 
      incon_load_incon_def incon_load2_def incon_load_def)
  apply (erule disjE)
   apply (drule_tac x = a in spec , simp)
   apply (drule_tac x = x in spec, simp)
   apply (drule_tac x = a in spec , simp)
   apply (drule_tac x = x in spec, simp)
  apply clarsimp
  apply (drule_tac x = a in spec , simp)
  apply (drule_tac x = v in spec, simp)
  apply (drule_tac x = a in spec , simp)
  apply (drule_tac x = v in spec, simp)
  apply (case_tac "snapshot (tlb_incon_set t) a v")
    apply (clarsimp simp: less_eq_lookup_type)
   apply clarsimp
  apply (clarsimp simp: less_eq_lookup_type)
  done


(* refinement between saturated and new abstracted model  *)

lemma update_ASID_sat_abs2_refine:
  "\<lbrakk> update_ASID a (s::tlb_sat_state) = ((), s') ;  update_ASID a (t::tlb_incon_state) = ((), t'); 
        invar_rel (typ_sat_tlb s) (typ_incon'2 t) \<rbrakk> \<Longrightarrow> 
                       invar_rel (typ_sat_tlb s') (typ_incon'2 t')"
  apply (clarsimp simp: update_ASID_tlb_sat_state_ext_def update_ASID_tlb_incon_state_ext_def Let_def)
  apply (frule invar_relD)
  apply (case_tac "a = ASID s")
    (* when we update to the same ASID *)
   apply (subgoal_tac "tlb_sat_set s = tlb_sat_set s \<union> 
         the `{e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e}")
    prefer 2
    apply (clarsimp simp:  saturated_def) 
    apply blast
   apply clarsimp
   apply (clarsimp simp: invar_rel_def)
   apply (rule conjI)
    apply (clarsimp simp: state.defs)
   apply (rule conjI)
    apply (clarsimp simp: snapshot_update_current'_def snapshot_update_current_def snapshot_update_current'2_def snapshot_update_current2_def 
      incon_load_incon_def incon_load2_def incon_load_def)
    apply force
   apply clarsimp
   apply (clarsimp simp: snapshot_of_tlb_def snapshot_update_current'_def snapshot_update_current_def
      snapshot_update_new'_def  snapshot_update_new_def)
   apply (clarsimp simp: snapshot_update_current'_def snapshot_update_current_def snapshot_update_current'2_def snapshot_update_current2_def 
      incon_load_incon_def incon_load2_def incon_load_def split: if_split_asm)
    (* when we update to the new ASID *)
  apply (clarsimp simp: invar_rel_def)
  apply (rule conjI)
   apply (clarsimp simp: state.defs)
  apply (rule conjI)
   apply (subgoal_tac "incon_load_incon (snapshot_update_current'2 (snapshot (tlb_incon_set t)) (iset (tlb_incon_set t)) (MEM s) (TTBR0 s) (ASID s)) a (MEM s) (TTBR0 s)  = 
                       incon_load_incon (snapshot (tlb_incon_set t)) a (MEM s) (TTBR0 s) ")
    prefer 2
    apply (clarsimp simp: incon_load_incon_def snapshot_update_current'2_def snapshot_update_current2_def split: if_split_asm)
   apply (subgoal_tac "incon_load2 (snapshot_update_current'2 (snapshot (tlb_incon_set t)) (iset (tlb_incon_set t)) (MEM s) (TTBR0 s) (ASID s)) a (MEM s) (TTBR0 s)  = 
                       incon_load2 (snapshot (tlb_incon_set t))  a (MEM s) (TTBR0 s) ")
    prefer 2
    apply (clarsimp simp: incon_load2_def snapshot_update_current'2_def snapshot_update_current2_def split: if_split_asm)
   apply (simp only:)
   apply (thin_tac "incon_load_incon (snapshot_update_current'2 (snapshot (tlb_incon_set t)) (iset (tlb_incon_set t)) (MEM s) (TTBR0 s) (ASID s)) a (MEM s) (TTBR0 s)  = 
                       incon_load_incon (snapshot (tlb_incon_set t)) a (MEM s) (TTBR0 s)")
   apply (thin_tac "incon_load2 (snapshot_update_current'2 (snapshot (tlb_incon_set t)) (iset (tlb_incon_set t)) (MEM s) (TTBR0 s) (ASID s)) a (MEM s) (TTBR0 s)  = 
                       incon_load2 (snapshot (tlb_incon_set t))  a (MEM s) (TTBR0 s)")
   apply (clarsimp)
   apply (drule_tac x = a in spec, simp add: snapshot_of_tlb_def)
   apply (clarsimp simp: asid_va_incon_tlb_mem_n_def asid_va_incon_n_def asid_va_hit_incon_n_def)
   apply (drule_tac x = x in spec)
   apply (erule disjE)+
    apply (clarsimp simp: incon_load2_def incon_load_incon_def)
    apply (drule union_incon_cases1)
    apply (erule disjE , clarsimp)
    apply (erule disjE , clarsimp simp: less_eq_lookup_type lookup_range_pt_walk_hit)
    apply (erule disjE , clarsimp simp: lookup_range_pt_walk_not_incon)
    apply (erule disjE , clarsimp)
    apply (erule disjE , clarsimp simp: lookup_range_pt_walk_not_incon')
    apply (clarsimp)
   apply clarsimp
   apply (erule disjE)+
    apply (clarsimp simp: incon_load2_def incon_load_incon_def)
    apply (drule lookup_hit_union_cases')
    apply (erule disjE , clarsimp simp: less_eq_lookup_type) 
    apply (erule disjE , clarsimp simp:  lookup_range_pt_walk_hit)
    apply (clarsimp simp: lookup_range_pt_walk_hit)
   apply (clarsimp simp: incon_load2_def incon_load_incon_def)
   apply (drule lookup_hit_union_cases')
   apply (erule disjE , clarsimp simp: less_eq_lookup_type) 
   apply (erule disjE , clarsimp simp:  lookup_miss_is_fault_intro) 
   apply (clarsimp simp: lookup_miss_is_fault_intro)
  apply (rule conjI)
   apply (clarsimp simp: saturated_def)
  apply (rule allI)
  apply (rule impI)
  apply (rule allI)
  apply (case_tac "aa \<noteq> ASID s")
   apply (subgoal_tac "snapshot_update_current'2 (snapshot (tlb_incon_set t)) (iset (tlb_incon_set t)) (MEM s) (TTBR0 s) (ASID s) aa v = 
                         (snapshot (tlb_incon_set t)) aa v")
    prefer 2
    apply (clarsimp simp: snapshot_update_current'2_def snapshot_update_current2_def split: if_split_asm)
   apply (simp only:)
   apply (thin_tac " snapshot_update_current'2 (snapshot (tlb_incon_set t)) (iset (tlb_incon_set t)) (MEM s) (TTBR0 s) (ASID s) aa v = snapshot (tlb_incon_set t) aa v")
   apply (simp only: snapshot_of_tlb_def)
   apply (subgoal_tac "lookup (tlb_sat_set s \<union> the ` {e \<in> range (pt_walk a (MEM s) (TTBR0 s)). \<not> is_fault e}) aa (  v) =
         lookup (tlb_sat_set s) aa (  v)")
    apply clarsimp
   apply (simp add: asid_unequal_miss'' lookup_miss_union_equal)
  apply clarsimp
  apply (simp only: snapshot_of_tlb_def)
  apply (subgoal_tac "lookup (tlb_sat_set s \<union> the ` {e \<in> range (pt_walk a (MEM s) (TTBR0 s)). \<not> is_fault e}) (ASID s) (  v) =
               lookup (tlb_sat_set s) (ASID s) (  v)")
   prefer 2
   apply (clarsimp simp: lookup_miss_union_equal asid_unequal_miss'')
  apply (clarsimp)
  apply (thin_tac "  lookup (tlb_sat_set s \<union> the ` {e \<in> range (pt_walk a (MEM s) (TTBR0 s)). \<not> is_fault e}) (ASID s) v = lookup (tlb_sat_set s) (ASID s) v")
  apply (clarsimp simp: snapshot_update_current'2_def snapshot_update_current2_def split: if_split_asm)
  apply (rule conjI)
   apply clarsimp
   apply (subgoal_tac "v \<notin>  asid_va_incon_tlb_mem_n (typ_sat_tlb s)")
    prefer 2
    apply blast
   apply (clarsimp simp: asid_va_incon_tlb_mem_n_def asid_va_incon_n_def asid_va_hit_incon_n_def) 
   apply (metis (no_types, hide_lams) less_eq_lookup_type lookup_type.exhaust)
  apply clarsimp
  apply (subgoal_tac "v \<notin>  asid_va_incon_tlb_mem_n (typ_sat_tlb s)")
   prefer 2
   apply blast
  apply (clarsimp simp: asid_va_incon_tlb_mem_n_def asid_va_incon_n_def asid_va_hit_incon_n_def)
  using not_miss_incon_hit by blast 


end