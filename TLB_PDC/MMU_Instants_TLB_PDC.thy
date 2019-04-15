theory MMU_Instants_TLB_PDC

imports  Simp_Lemmas_PDC
         TLBJ.ARM_Monadic


begin       




record non_det_tlb_state = state + 
           non_det_tlb  :: "tlb \<times> pdc"


record sat_tlb_state = state +
           sat_tlb  :: "tlb \<times> pdc"



record set_tlb =
  iset       :: "vaddr set"
  global_set :: "vaddr set" 
  snapshot   :: "asid \<Rightarrow> (vaddr set \<times> (vaddr \<Rightarrow> pt_walk_typ))"


record set_tlb_state  = state + 
            set_tlb  :: set_tlb



definition 
  typ_non_det_tlb :: "'a non_det_tlb_state_scheme \<Rightarrow> (tlb \<times> pdc) state_scheme"
where
  "typ_non_det_tlb s =  state.extend (state.truncate s) (non_det_tlb s)"

definition 
  typ_sat_tlb :: "'a sat_tlb_state_scheme \<Rightarrow> (tlb \<times> pdc) state_scheme"
where
  "typ_sat_tlb s =  state.extend (state.truncate s) (sat_tlb s)"


definition 
  typ_set_tlb :: "'a set_tlb_state_scheme \<Rightarrow> (set_tlb) state_scheme"
where
  "typ_set_tlb s =  state.extend (state.truncate s) (set_tlb s)"


lemma non_det_tlb_more [simp]:
  "state.more (typ_non_det_tlb s) = (non_det_tlb s)"
  by (clarsimp simp: typ_non_det_tlb_def state.defs)



lemma sat_tlb_more [simp]:
  "state.more (typ_sat_tlb s) = (sat_tlb s)"
  by (clarsimp simp: typ_sat_tlb_def state.defs)



lemma set_tlb_more' [simp]:
  "state.more (typ_set_tlb s) = (set_tlb s)"
  by (clarsimp simp: typ_set_tlb_def state.defs)


lemma non_det_tlb_truncate [simp]:
  "state.truncate (typ_non_det_tlb s') = state.truncate s'"
  by (clarsimp simp: typ_non_det_tlb_def state.defs)


lemma sat_tlb_truncate [simp]:
  "state.truncate (typ_sat_tlb s') = state.truncate s'"
  by (clarsimp simp: typ_sat_tlb_def state.defs)

lemma set_tlb_truncate [simp]:
  "state.truncate (typ_set_tlb s') = state.truncate s'"
  by (clarsimp simp: typ_set_tlb_def state.defs)

lemma typ_non_det_prim_parameter [simp]:
  " TTBR0 (typ_non_det_tlb s) =  TTBR0 s \<and> ASID (typ_non_det_tlb s) = ASID s \<and>
           MEM (typ_non_det_tlb s) = MEM s \<and> exception (typ_non_det_tlb s) = exception s"
  by (clarsimp simp: typ_non_det_tlb_def  state.defs)


lemma typ_sat_prim_parameter [simp]:
  "TTBR0 (typ_sat_tlb s) =  TTBR0 s \<and> ASID (typ_sat_tlb s) =  ASID s  \<and> MEM (typ_sat_tlb s) = MEM s \<and> exception (typ_sat_tlb s) = exception s"
  by (clarsimp simp: typ_sat_tlb_def  state.defs)

lemma typ_set_prim_parameter [simp]:
  "TTBR0 (typ_set_tlb s) =  TTBR0 s \<and> ASID (typ_set_tlb s) =  ASID s \<and> MEM (typ_set_tlb s) = MEM s \<and> exception (typ_set_tlb s) = exception s"
  by (clarsimp simp: typ_set_tlb_def  state.defs)






abbreviation
  "consistent (s:: (tlb \<times> pdc) state_scheme) \<equiv>
               consistent0' (MEM s) (ASID s)  (TTBR0 s) (fst (state.more s)) (snd (state.more s))"



definition
  saturated :: "(tlb \<times> pdc)  state_scheme \<Rightarrow> bool"
where
  "saturated s  \<equiv> the ` {e\<in>pt_walk (ASID s) (MEM s) (TTBR0 s) ` UNIV. \<not>is_fault e} \<subseteq>  (fst  (state.more s)) \<and>
                   the ` {e\<in>pdc_walk(ASID s) (MEM s) (TTBR0 s) ` UNIV. \<not>is_fault e} \<subseteq> (snd  (state.more s))"


definition 
  tlb_rel_sat :: "(tlb \<times> pdc) state_scheme \<Rightarrow> (tlb \<times> pdc) state_scheme \<Rightarrow> bool"
where                                                                
  "tlb_rel_sat s t \<equiv> state.truncate s = state.truncate t \<and> 
                     fst (state.more s) \<subseteq> fst (state.more t) \<and> 
                     snd (state.more s) \<subseteq> snd (state.more t)  \<and>  saturated t"

definition 
   inconsistent_vaddrs :: "(tlb \<times> pdc) state_scheme \<Rightarrow>  vaddr set"
where                                                        
  "inconsistent_vaddrs s  \<equiv>  {va. lookup'' (fst (state.more s)) (ASID s) va = Incon} \<union> {va. lookup_pdc (snd (state.more s)) (ASID s) va = Incon}"



definition                              
   incoherrent_vaddrs :: "(tlb \<times> pdc) state_scheme \<Rightarrow>  vaddr set"
where                                                         
  "incoherrent_vaddrs s  \<equiv> {va. \<exists>x. lookup'' (fst ((state.more s))) (ASID s) va = Hit x     \<and> is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) va)} \<union> 
                            {va. \<exists>x. lookup_pdc ( (snd(state.more s))) (ASID s) va = Hit x \<and> is_fault (pdc_walk (ASID s) (MEM s) (TTBR0 s) va)} "


definition                              
   incon_addrs :: "(tlb \<times> pdc) state_scheme \<Rightarrow>  vaddr set"
where                                                         
  "incon_addrs s  \<equiv>  inconsistent_vaddrs s \<union> incoherrent_vaddrs s"


definition                              
   global_range :: "(tlb \<times> pdc) state_scheme \<Rightarrow>  vaddr set"
where                                                         
  "global_range s  \<equiv>   \<Union>(range_of `  global_entries     (fst( state.more s))) \<union>
                       \<Union>(range_of `  global_entries_pdc (snd(state.more s))) "


definition
  snap_conv' :: "(vaddr set \<times> (vaddr \<Rightarrow> pt_walk_typ)) \<Rightarrow> (vaddr \<Rightarrow> tlb_entry lookup_type \<times> pdc_entry lookup_type)"
  where 
  "snap_conv' snp  \<equiv> \<lambda>v. if v \<in> (fst snp) then (Incon, Incon) else  
                          case (snd snp) v of Fault              \<Rightarrow> (Miss, Miss)
                                           |  Partial_Walk pe    \<Rightarrow> if asid_of_pdc pe = None then (Miss, Miss) else (Miss, Hit pe)
                                           |  Full_Walk te pe    \<Rightarrow> if asid_of te = None 
                                                                      then (Miss, if asid_of_pdc pe = None then Miss else Hit pe) 
                                                                       else (Hit te, Hit pe )"


definition 
   "lookup_from' snp a v \<equiv> snap_conv' (snp a) v"


definition 
  tlb_rel_abs :: "(tlb \<times> pdc) state_scheme  \<Rightarrow> (set_tlb) state_scheme \<Rightarrow> bool"
where                                                                
"tlb_rel_abs s t \<equiv>   state.truncate s = state.truncate t \<and> 
                     saturated s \<and>
                     incon_addrs s \<subseteq>  iset (state.more t) \<and> 
                     global_range s \<subseteq>  global_set (state.more t) \<and>  
                     (\<forall>a v. a \<noteq> ASID s \<longrightarrow>  lookup''   (fst ((state.more s)) - global_entries (fst ((state.more s)))) a v \<le> fst (lookup_from' (snapshot  (state.more t)) a v) \<and>
                                                        lookup_pdc (snd ((state.more s)) - global_entries_pdc (snd ((state.more s)))) a v \<le> snd (lookup_from' (snapshot  (state.more t)) a v))" 

declare return_def [simp add]
declare bind_def [simp add]
declare read_state_def [simp add]
declare update_state_def [simp add]
declare extend_state_def [simp add]
declare trim_state_def [simp add]

lemma tlb_rel_satD:
  "tlb_rel_sat s t \<Longrightarrow> MEM t = MEM s \<and> TTBR0 t = TTBR0 s \<and> ASID t = ASID s  \<and>
          fst(state.more s) \<subseteq> fst(state.more t) \<and>  snd(state.more s) \<subseteq> snd(state.more t) \<and> exception t = exception s  \<and> saturated t"
  by (clarsimp simp: tlb_rel_sat_def state.defs)


lemma tlb_rel_absD:
  "tlb_rel_abs s t \<Longrightarrow> MEM t = MEM s \<and> TTBR0 t = TTBR0 s  \<and> ASID t = ASID s  \<and> saturated s \<and> 
                         incon_addrs s \<subseteq> iset ((state.more t)) \<and>  global_range s \<subseteq> global_set ((state.more t)) \<and>
                          exception t = exception s"
  by (clarsimp simp: tlb_rel_abs_def state.defs)

lemma tlb_rel_sat_consistent:
  "\<lbrakk> tlb_rel_sat s t; consistent t va \<rbrakk> \<Longrightarrow> consistent s va"
  apply (insert tlb_rel_satD [of s t])
  apply ( clarsimp )
  apply (drule asid_tlb_mono)
  by (drule asid_pdc_mono [of _ _ "ASID s" va], auto simp: consistent0'_def less_eq_lookup_type)


lemma sat_state_tlb:
  "\<lbrakk> saturated s \<rbrakk> \<Longrightarrow> 
     fst((state.more s)) = fst((state.more s)) \<union> the ` {e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e} \<and>   
     snd((state.more s)) = snd((state.more s)) \<union> the ` {e \<in> range (pdc_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e}"
  by (fastforce simp: saturated_def)


lemma saturated_tlb_pde:
  "saturated (typ_sat_tlb s) \<Longrightarrow> fst (sat_tlb s) = fst (sat_tlb s) \<union> the ` {e\<in>pt_walk (ASID s) (MEM s) (TTBR0 s) ` UNIV. \<not>is_fault e} \<and>
     snd (sat_tlb s) = snd (sat_tlb s) \<union>  the ` {e\<in>pdc_walk (ASID s) (MEM s) (TTBR0 s) ` UNIV. \<not>is_fault e}"
 apply (clarsimp simp:  saturated_def fst_def) apply (cases "sat_tlb s" ; clarsimp)  by blast


lemma sat_miss_fault:
  "\<lbrakk> saturated (typ_sat_tlb s); lookup'' (fst (sat_tlb s)) (ASID s) va = Miss \<rbrakk> \<Longrightarrow> 
           is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) va)"
  apply (subgoal_tac " lookup'' (fst (sat_tlb s)  \<union> the ` {e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e}) (ASID s) va = Miss")
   apply (thin_tac "lookup'' (fst (sat_tlb s)) (ASID s) va = Miss")
   apply (drule lookup_asid_tlb_miss_union)
   apply clarsimp
  using asid_tlb_lookup_miss_is_fault apply force
  using  sat_state_tlb by force



lemma saturatd_lookup_hit_no_fault:
  "\<lbrakk>saturated (typ_sat_tlb s); 
    lookup'' (fst(sat_tlb s)) (ASID s) b = Hit x; \<not> is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) b)\<rbrakk> \<Longrightarrow>
                       x = the (pt_walk (ASID s) (MEM s) (TTBR0 s) b)"
  apply (subgoal_tac "lookup'' (fst(sat_tlb s) \<union> 
                              the ` {e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e}) (ASID s) (  b) = Hit x")
   prefer 2
   apply (drule sat_state_tlb, clarsimp simp: state.defs)
  apply (drule lookup_asid_tlb_hit_miss_or_hit')
  apply (erule disjE)
   apply (clarsimp simp: asid_tlb_lookup_range_pt_walk_hit)
  apply (frule asid_tlb_lookup_range_fault_pt_walk)
  apply (drule_tac x = b in bspec; clarsimp simp: lookup_asid_tlb_hit_entry_range)
  done

  
lemma saturated_tlb:
  "saturated (typ_sat_tlb s) \<Longrightarrow> fst (sat_tlb s) = fst (sat_tlb s) \<union> the ` {e\<in>pt_walk (ASID s) (MEM s) (TTBR0 s) ` UNIV. \<not>is_fault e} "
 apply (clarsimp simp:  saturated_def fst_def) apply (cases "sat_tlb s" ; clarsimp)  by blast


lemma sat_miss_pdc_fault: 
  "\<lbrakk> saturated (typ_sat_tlb s); lookup_pdc (snd (sat_tlb s)) (ASID s) va = Miss \<rbrakk> \<Longrightarrow> 
           is_fault (pdc_walk (ASID s) (MEM s) (TTBR0 s) va)"
  apply (subgoal_tac "lookup_pdc (snd (sat_tlb s)  \<union> the ` {e \<in> range (pdc_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e}) (ASID s) va = Miss")
   apply (thin_tac "lookup_pdc (snd (sat_tlb s)) (ASID s) va = Miss")
   apply (drule lookup_asid_pdc_miss_union)
   apply clarsimp
   apply (drule lookup_pdc_miss_is_fault)
   apply clarsimp
  using saturated_tlb_pde by fastforce

  

lemma saturatd_lookup_pdc_hit_no_fault:
  "\<lbrakk>saturated (typ_sat_tlb s); 
    lookup_pdc (snd(sat_tlb s)) (ASID s) b = Hit x; \<not> is_fault (pdc_walk (ASID s) (MEM s) (TTBR0 s) b)\<rbrakk> \<Longrightarrow>
                       x = the (pdc_walk (ASID s) (MEM s) (TTBR0 s) b)"
  apply (subgoal_tac "lookup_pdc (snd(sat_tlb s) \<union> 
                              the ` {e \<in> range (pdc_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e}) (ASID s) b = Hit x")
   prefer 2
   apply (drule sat_state_tlb, clarsimp simp: state.defs)
  apply (drule lookup_asid_pdc_hit_miss_or_hit')
  apply (erule disjE)
   apply (clarsimp simp: lookup_pdc_range_pt_walk_hit)
  apply (frule lookup_pdc_range_fault_pt_walk)
  apply (drule_tac x = b in bspec; clarsimp simp: lookup_asid_pdc_hit_entry_range)
  done


lemma saturate_no_icon_miss:
  "\<lbrakk>saturated (typ_sat_tlb s); lookup_pdc (snd (sat_tlb s)) (ASID s) va \<noteq> Incon;
     lookup_pdc (snd (sat_tlb s)) (ASID s) va \<noteq> Miss; \<not> is_fault (pdc_walk (ASID s) (MEM s) (TTBR0 s) va)\<rbrakk>
    \<Longrightarrow> lookup_pdc (snd (sat_tlb s)) (ASID s) va = Hit (the (pdc_walk (ASID s) (MEM s) (TTBR0 s) va))"
  apply (subgoal_tac "\<exists>x\<in>snd(sat_tlb s). lookup_pdc (snd(sat_tlb s)) (ASID s) va = Hit x")
   prefer 2 
  apply (meson lookup_in_asid_pdc lookup_type.exhaust) 
  by (clarsimp simp: saturatd_lookup_pdc_hit_no_fault)



lemma write_mem_eq_TLB:
  "\<lbrakk> write'mem1 (val, va, sz) s = ((), s') \<rbrakk>  \<Longrightarrow> state.more s' = state.more s"
   by (clarsimp simp: write'mem1_def raise'exception_def split: if_split_asm)


lemma write_same_mem:
  "\<lbrakk> write'mem1 (val, va, sz) s = ((), s') ; write'mem1 (val, va, sz) t = ((), t') ;
      MEM s = MEM t\<rbrakk>  \<Longrightarrow>  MEM s' = MEM t'"
  by (clarsimp simp: write'mem1_def raise'exception_def split:if_split_asm)

lemma write_same_mem_excep:
  "\<lbrakk> write'mem1 (val, pa, sz) s = ((), s') ; write'mem1 (val, pa, sz) t = ((), t') ;
      MEM s = MEM t ; exception s = exception t \<rbrakk>  \<Longrightarrow> exception s' = exception t'"
   by (clarsimp simp: write'mem1_def raise'exception_def split:if_split_asm)


lemma write_mem_rel:
  "\<lbrakk> write'mem1 (val, va, sz) s = ((), s') \<rbrakk>  \<Longrightarrow> s' = s \<lparr> MEM:= MEM s' , exception:= exception s' \<rparr>"
   by (clarsimp simp: write'mem1_def raise'exception_def split: if_split_asm)

lemma not_member_incon_consistent:
  "\<lbrakk>va \<notin>  incon_addrs (typ_sat_tlb s) ; saturated (typ_sat_tlb s) \<rbrakk> \<Longrightarrow> 
                                       consistent (typ_sat_tlb s) va"
  apply (clarsimp simp: incon_addrs_def inconsistent_vaddrs_def incoherrent_vaddrs_def consistent0'_def)
  apply (erule disjE)
   apply (rule conjI)
    apply (meson lookup_type.exhaust)
  using not_miss_incon_hit_asid_pdc saturate_no_icon_miss apply blast
  apply clarsimp
  apply (rule conjI)
   apply (subgoal_tac "\<exists>x\<in>fst(sat_tlb s). lookup'' (fst(sat_tlb s)) (ASID s) va = Hit x")
    prefer 2
    apply (meson lookup_in_asid_tlb lookup_type.exhaust sat_miss_fault)
  using saturatd_lookup_hit_no_fault apply blast
  apply (subgoal_tac "\<exists>x\<in>snd(sat_tlb s). lookup_pdc (snd(sat_tlb s)) (ASID s) va = Hit x")
   prefer 2
   apply (meson is_fault_pde_is_fault_pt lookup_type.exhaust lookup_in_asid_pdc sat_miss_pdc_fault)
  using saturate_no_icon_miss by blast


lemma tlb_rel_abs_consistent [simp]:
  "\<lbrakk>va \<notin> iset (set_tlb t) ;   tlb_rel_abs  (typ_sat_tlb s) (typ_set_tlb t)  \<rbrakk>  \<Longrightarrow> 
           consistent (typ_sat_tlb s) va " 
  apply (rule not_member_incon_consistent ; clarsimp simp: tlb_rel_abs_def) 
  by blast



(*      ARM Monadic Simplification Lemmas     *)

lemma mem1_exception:
  "mem1 p s = (val, t) \<Longrightarrow>  t = s\<lparr>exception := exception t\<rparr>"
  apply (clarsimp simp: mem1_def)
  apply (cases "MEM s p")
   apply (clarsimp simp: raise'exception_def split: if_split_asm)
  apply clarsimp
done


lemma mem1_read_exception:
  "mem_read1 (a, sz) b = (val, r) \<Longrightarrow> r = b \<lparr>exception := exception r\<rparr>"
  apply (clarsimp simp: mem_read1_def)
  apply (clarsimp split: if_split_asm)
      apply (case_tac "mem1 (a r+ 0) b" , clarsimp)
      apply (clarsimp simp: mem1_exception)
     apply (case_tac "mem1 (a r+ 1) b" , clarsimp)
     apply (case_tac "mem1 (a r+ 0) ba", clarsimp)
     apply (drule mem1_exception)
     apply (drule mem1_exception)
     apply (cases b, case_tac ba, cases r ,clarsimp)
    apply (case_tac "mem1 (a r+ 3) b" , clarsimp)
    apply (case_tac "mem1 (a r+ 2) ba", clarsimp)
    apply (case_tac "mem1 (a r+ 1) baa", clarsimp)
    apply (case_tac "mem1 (a r+ 0) bb", clarsimp)
    apply (drule mem1_exception)
    apply (drule mem1_exception)
    apply (drule mem1_exception)
    apply (drule mem1_exception)
    apply (cases b, case_tac ba, case_tac baa, case_tac bb , cases r ,clarsimp)
   apply (case_tac "mem1 (a r+ 7) b" , clarsimp)
   apply (case_tac "mem1 (a r+ 6) ba", clarsimp)
   apply (case_tac "mem1 (a r+ 5) baa", clarsimp)
   apply (case_tac "mem1 (a r+ 4) bb", clarsimp)
   apply (case_tac "mem1 (a r+ 3) bc", clarsimp)
   apply (case_tac "mem1 (a r+ 2) bd", clarsimp)
   apply (case_tac "mem1 (a r+ 1) be", clarsimp)
   apply (case_tac "mem1 (a r+ 0) bf", clarsimp)
   apply (drule mem1_exception)
   apply (drule mem1_exception)
   apply (drule mem1_exception)
   apply (drule mem1_exception)
   apply (drule mem1_exception)
   apply (drule mem1_exception)
   apply (drule mem1_exception)
   apply (drule mem1_exception)
   apply (cases b, case_tac ba, case_tac baa, case_tac bb ,case_tac bc ,
                   case_tac bd ,  case_tac be ,  case_tac bf , cases r ,clarsimp)
  apply (clarsimp simp: raise'exception_def split:if_split_asm)
done

lemma write_mem_state_trun_equal:
  "\<lbrakk>  write'mem1 (val, pa, sz) s = ((), s'); write'mem1 (val, pa, sz) t = ((), t'); 
     state.truncate s = state.truncate t \<rbrakk>  \<Longrightarrow> state.truncate s' = state.truncate t'"
  apply (frule write_mem_rel)
  apply rotate_tac
  apply (frule write_mem_rel)
  apply (subgoal_tac "MEM s' = MEM t' \<and> exception s' = exception t'")
   apply clarsimp
   apply (cases s, cases t, cases s', cases t', clarsimp simp: state.defs)
  apply (cases s, cases t, cases s', cases t', clarsimp simp: state.defs)
  apply (clarsimp simp: write'mem1_def Let_def state.defs raise'exception_def split:if_split_asm)
  done
lemma write_mem1_eq_ASID_TTBR0:
  "\<lbrakk> write'mem1 (val, va, sz) s = ((), s') \<rbrakk>  \<Longrightarrow> fst (state.more s') = fst (state.more s) \<and> TTBR0 s' = TTBR0 s"
   by (clarsimp simp: write'mem1_def raise'exception_def split: if_split_asm)

lemma tlb_sat_set_mem1 [simp]:
  "fst(sat_tlb (snd (mem1 ps s))) = fst(sat_tlb s) \<and>
     snd(sat_tlb (snd (mem1 ps s))) = snd(sat_tlb s)"
  by (simp add: mem1_def raise'exception_def split: option.splits)


definition
  flush_tlb_pdc_vset :: " (tlb \<times> pdc) \<Rightarrow> vaddr set \<Rightarrow> (tlb \<times> pdc)"
where
  "flush_tlb_pdc_vset t vset = (fst t - \<Union>((\<lambda> v. {e\<in>(fst t). v \<in> range_of e}) ` vset), snd t - \<Union>((\<lambda> v. {e\<in>(snd t). v \<in> range_of e}) ` vset))"


definition
  flush_tlb_pdc_asid :: " (tlb \<times> pdc) \<Rightarrow> asid \<Rightarrow> (tlb \<times> pdc)"
where
  "flush_tlb_pdc_asid t a = (fst t - {e\<in>(fst t). asid_of e = Some a}, snd t - {e\<in>(snd t). asid_of_pdc e = Some a})"


definition
  flush_tlb_pdc_a_vset :: " (tlb \<times> pdc) \<Rightarrow> asid \<Rightarrow> vaddr set \<Rightarrow> (tlb \<times> pdc)"
where
  "flush_tlb_pdc_a_vset t a vset = (fst t - (\<Union>v\<in>vset. {e\<in>(fst t). v \<in> range_of e \<and> asid_of e = Some a}),
                                    snd t - (\<Union>v\<in>vset. {e\<in>(snd t). v \<in> range_of e \<and> asid_of_pdc e = Some a}))"

consts tlb_evict :: "(tlb_entry set \<times> pdc) state_scheme \<Rightarrow> tlb_entry set \<times> pdc"

instantiation non_det_tlb_state_ext :: (type) mmu
begin
  definition                          
  "(mmu_translate v :: ('a non_det_tlb_state_scheme \<Rightarrow> _))
 = do {
     update_state (\<lambda>s. s\<lparr> non_det_tlb := pairsub (non_det_tlb s)  (tlb_evict (typ_non_det_tlb s)) \<rparr>);
     mem   <- read_state MEM;
     asid  <- read_state ASID;
     ttbr0 <- read_state TTBR0;
     tlb_pde   <- read_state non_det_tlb;
     let tlb = fst tlb_pde;
     let pdc  = snd tlb_pde;
          case lookup'' tlb asid v of 
               Hit entry \<Rightarrow> return (va_to_pa v  entry)
          |    Miss \<Rightarrow> 
                   (case lookup_pdc pdc asid v of
                         Hit pdc_entry \<Rightarrow> do { 
                                        let entry = pde_tlb_entry pdc_entry mem v;
                                        if is_fault entry 
                                        then raise'exception (PAGE_FAULT ''more info'')
                                        else do {
                                        update_state (\<lambda>s. s\<lparr> non_det_tlb := pairunion (non_det_tlb s)  ({the entry} , {}) \<rparr>);
                                        return  (va_to_pa v (the entry)) 
                                           } }
                     |   Miss \<Rightarrow> do { 
                                    let pde  = pdc_walk asid mem ttbr0 v;
                                    if is_fault pde
                                    then raise'exception (PAGE_FAULT ''more info'')
                                    else do {
                                         update_state (\<lambda>s. s\<lparr> non_det_tlb := pairunion (non_det_tlb s)  ({} , {the pde}) \<rparr>);
                                         let entry = pt_walk asid mem ttbr0 v;
                                         if is_fault entry 
                                         then raise'exception (PAGE_FAULT ''more info'')
                                         else do {
                                              update_state (\<lambda>s. s\<lparr> non_det_tlb := pairunion (non_det_tlb s)  ({the entry} , {}) \<rparr>);
                                              return (va_to_pa v (the entry)) }
                                              } 
                                           }
                      |   Incon  \<Rightarrow> raise'exception (IMPLEMENTATION_DEFINED ''set on fire''))
         | Incon \<Rightarrow> raise'exception (IMPLEMENTATION_DEFINED ''set on fire'') 
   }"


definition
 "(mmu_read_size  :: (vaddr \<times> nat \<Rightarrow>  'a non_det_tlb_state_scheme \<Rightarrow> bool list \<times>  'a non_det_tlb_state_scheme))
  \<equiv> \<lambda>(va,size). do {
                     pa  \<leftarrow> mmu_translate va :: ('a non_det_tlb_state_scheme \<Rightarrow> _);
                     mem_read1 (pa , size)
  }"


definition   
  "(mmu_write_size  :: (bool list \<times> vaddr \<times> nat \<Rightarrow> 'a non_det_tlb_state_scheme \<Rightarrow> unit \<times> 'a non_det_tlb_state_scheme))
   \<equiv> \<lambda>(value, vaddr, size). do {
     paddr <- mmu_translate vaddr :: ('a non_det_tlb_state_scheme \<Rightarrow> _);
     exception <- read_state exception;
     if exception = NoException 
       then  write'mem1 (value, paddr, size)
       else return ()
  }"               

definition
  "(update_TTBR0 r :: ('a non_det_tlb_state_scheme \<Rightarrow> _))  = 
do {
    update_state (\<lambda>s. s\<lparr> TTBR0 := r \<rparr>)
  } "

definition   
  "(update_ASID a :: ('a non_det_tlb_state_scheme \<Rightarrow> _))  = 
    do {  update_state (\<lambda>s. s\<lparr> ASID := a \<rparr>) }"

definition   
  "(flush f :: ('a non_det_tlb_state_scheme \<Rightarrow> _))  \<equiv> 
           case f of FlushTLB \<Rightarrow> update_state (\<lambda>s. s\<lparr> non_det_tlb := ({}, {}) \<rparr>)
                  | Flushvarange vset \<Rightarrow> do {                            
                             update_state (\<lambda>s. s\<lparr> non_det_tlb := flush_tlb_pdc_vset (non_det_tlb s) vset \<rparr>)}
                  | FlushASID a \<Rightarrow> do { update_state (\<lambda>s. s\<lparr> non_det_tlb := flush_tlb_pdc_asid (non_det_tlb s) a \<rparr>)}
                  |  FlushASIDvarange a vset \<Rightarrow> do {
                                         update_state (\<lambda>s. s\<lparr> non_det_tlb := flush_tlb_pdc_a_vset (non_det_tlb s) a vset \<rparr>)}"

  instance ..
end




instantiation sat_tlb_state_ext :: (type) mmu   
begin
definition   
 "(mmu_translate v :: ('a sat_tlb_state_scheme \<Rightarrow> _))
 = do {
     mem   <- read_state MEM;
     asid  <- read_state ASID;
     ttbr0 <- read_state TTBR0;
     let all_pdes = the ` {e\<in>pdc_walk asid mem ttbr0 ` UNIV. \<not>is_fault e};
     let all_tlbes = the ` {e\<in>\<Union>(tlb_pdc_walk asid all_pdes mem ttbr0 ` UNIV). \<not>is_fault e};
     tlb_pde0   <- read_state sat_tlb;
     let tlb0 = fst tlb_pde0;
     let pdc0  = snd tlb_pde0;
     let tlb_pde = pairunion tlb_pde0 (all_tlbes , all_pdes) ;
     update_state (\<lambda>s. s\<lparr> sat_tlb := tlb_pde \<rparr>);
          case lookup'' (fst tlb_pde) asid  v of
            Hit entry \<Rightarrow> return (va_to_pa v entry)
          | Miss \<Rightarrow> raise'exception (PAGE_FAULT ''more info'')
          | Incon \<Rightarrow> raise'exception (IMPLEMENTATION_DEFINED ''set on fire'')
   }" 

definition
 "(mmu_read_size  :: (vaddr \<times> nat \<Rightarrow>  'a sat_tlb_state_scheme \<Rightarrow> bool list \<times>  'a sat_tlb_state_scheme))
  \<equiv> \<lambda>(va,size). do {
                     pa  \<leftarrow> mmu_translate va :: ('a sat_tlb_state_scheme \<Rightarrow> _);
                     mem_read1 (pa , size)
  }"

definition
  "Somes S' \<equiv> the ` (S' \<inter> {x. x \<noteq> None})"


definition   
  "(mmu_write_size  :: (bool list \<times> vaddr \<times> nat \<Rightarrow> 'a sat_tlb_state_scheme \<Rightarrow> unit \<times> 'a sat_tlb_state_scheme))
   \<equiv> \<lambda>(value, vaddr, size). do {
     ttbr0 <- read_state TTBR0;
     asid <- read_state ASID;
     pa <- mmu_translate vaddr :: ('a sat_tlb_state_scheme \<Rightarrow> _);
     tlb_pde0   <- read_state sat_tlb;
     exception <- read_state exception;
     if exception = NoException 
      then do { 
           write'mem1 (value, pa, size); 
           mem1  <- read_state MEM;
           let all_pdes = the ` {e\<in>pdc_walk asid mem1 ttbr0 ` UNIV. \<not>is_fault e};
           let all_tlbes =  the ` {e\<in>\<Union>(tlb_pdc_walk asid all_pdes mem1 ttbr0 ` UNIV). \<not>is_fault e};
           let tlb_pde = pairunion tlb_pde0 (all_tlbes , all_pdes) ;
           update_state (\<lambda>s. s\<lparr> sat_tlb := tlb_pde \<rparr>)
          } 
      else return () 
    }" 




definition   
  "(update_TTBR0  r :: ('a sat_tlb_state_scheme \<Rightarrow> _)) \<equiv> do {
     update_state (\<lambda>s. s\<lparr> TTBR0 := r \<rparr>);
     asid <- read_state ASID;
     mem  <- read_state MEM;
     let all_pdes = the ` {e\<in>pdc_walk asid mem r ` UNIV. \<not>is_fault e};
     let all_tlbes = the ` {e\<in>\<Union>(tlb_pdc_walk asid all_pdes mem r ` UNIV). \<not>is_fault e};
     tlb_pde0   <- read_state sat_tlb;
     let tlb0 = fst tlb_pde0;
     let pdc0  = snd tlb_pde0;
     let tlb_pde = pairunion tlb_pde0 (all_tlbes , all_pdes) ;
     update_state (\<lambda>s. s\<lparr> sat_tlb := tlb_pde \<rparr>)} "

definition   
  "(update_ASID a :: ('a sat_tlb_state_scheme \<Rightarrow> _))  = do {
      update_state (\<lambda>s. s\<lparr> ASID := a \<rparr>);
      mem   <- read_state MEM;
      ttbr0 <- read_state TTBR0;
      let all_pdes = the ` {e\<in>pdc_walk a mem ttbr0 ` UNIV. \<not>is_fault e};
      let all_tlbes = the ` {e\<in>\<Union>(tlb_pdc_walk a all_pdes mem ttbr0 ` UNIV). \<not>is_fault e};
      tlb_pde0   <- read_state sat_tlb;
      let tlb0 = fst tlb_pde0;
      let pdc0  = snd tlb_pde0;
      let tlb_pde = pairunion tlb_pde0 (all_tlbes , all_pdes) ;
      update_state (\<lambda>s. s\<lparr> sat_tlb := tlb_pde \<rparr>)} "

definition   
  "(flush f :: ('a sat_tlb_state_scheme \<Rightarrow> _))  \<equiv>  do {
      mem   <- read_state MEM;
      ttbr0 <- read_state TTBR0;
      asid <- read_state ASID;
     tlb0 <- read_state sat_tlb;
     let all_pdes  = the ` {e\<in>pdc_walk asid mem ttbr0 ` UNIV. \<not>is_fault e};
     let all_tlbes = the ` {e\<in>\<Union>(tlb_pdc_walk asid all_pdes mem ttbr0 ` UNIV). \<not>is_fault e};
     case f of FlushTLB \<Rightarrow>  update_state (\<lambda>s. s\<lparr> sat_tlb := (all_tlbes , all_pdes) \<rparr>)
            |  Flushvarange vset \<Rightarrow>  do {
                                  let tlb_pde = pairunion (flush_tlb_pdc_vset tlb0 vset) (all_tlbes , all_pdes) ;
                                  update_state (\<lambda>s. s\<lparr> sat_tlb := tlb_pde \<rparr>) } 
            | FlushASID a \<Rightarrow>  update_state (\<lambda>s. s\<lparr> sat_tlb := pairunion (flush_tlb_pdc_asid tlb0 a) (all_tlbes,all_pdes) \<rparr>)
            | FlushASIDvarange a vset \<Rightarrow>  
                                update_state (\<lambda>s. s\<lparr> sat_tlb := pairunion (flush_tlb_pdc_a_vset tlb0 a vset) (all_tlbes,all_pdes) \<rparr>)}"



  instance ..
end

definition
  ptable_comp :: "(vaddr \<Rightarrow> pt_walk_typ) \<Rightarrow> (vaddr \<Rightarrow> pt_walk_typ) \<Rightarrow> vaddr set"
where
  "ptable_comp walk walk'  \<equiv> {va. \<not>(walk va \<preceq> walk' va)}"

definition
  incon_comp :: "asid \<Rightarrow> asid \<Rightarrow> heap \<Rightarrow> heap \<Rightarrow> paddr \<Rightarrow> paddr \<Rightarrow> vaddr set"
where
  "incon_comp a a' hp hp' rt rt' \<equiv> ptable_comp (pt_walk_pair a hp rt) (pt_walk_pair a' hp' rt')"



definition 
  snp_upd_cur :: "vaddr set \<Rightarrow> heap \<Rightarrow> ttbr0  \<Rightarrow> asid \<Rightarrow> (vaddr set \<times> (vaddr \<Rightarrow> pt_walk_typ))"
where
  "snp_upd_cur ist m r  \<equiv> \<lambda>a. (ist, \<lambda>v. pt_walk_pair a m r v)"


definition 
  snp_upd_cur' :: "(asid \<Rightarrow> (vaddr set \<times> (vaddr \<Rightarrow> pt_walk_typ))) \<Rightarrow> vaddr set \<Rightarrow> 
                                 heap \<Rightarrow> ttbr0 \<Rightarrow> asid \<Rightarrow> (asid \<Rightarrow> (vaddr set \<times> (vaddr \<Rightarrow> pt_walk_typ)))"
where
  "snp_upd_cur' snp ist mem ttbr0 a \<equiv> snp (a := snp_upd_cur ist mem ttbr0 a)"


instantiation set_tlb_state_ext :: (type) mmu   
begin
definition   
 "(mmu_translate v :: ('a set_tlb_state_scheme \<Rightarrow> _))
  = do {
     mem   <- read_state MEM;
     asid  <- read_state ASID;
     ttbr0 <- read_state TTBR0;
     set_tlb <- read_state set_tlb;
     if  v \<in> iset set_tlb
       then raise'exception (IMPLEMENTATION_DEFINED ''set on fire'')
       else let entry = pt_walk asid mem ttbr0 v in 
             if is_fault entry
              then raise'exception (PAGE_FAULT ''more info'')
              else return (va_to_pa v (the entry))
    }"

definition
 "(mmu_read_size  :: (vaddr \<times> nat \<Rightarrow>  'a set_tlb_state_scheme \<Rightarrow> bool list \<times>  'a set_tlb_state_scheme))
  \<equiv> \<lambda>(va,size). do {
                     pa  \<leftarrow> mmu_translate va :: ('a set_tlb_state_scheme \<Rightarrow> _);
                     mem_read1 (pa , size)
  }"

definition   
  "(mmu_write_size  :: (bool list \<times> vaddr \<times> nat \<Rightarrow> 'a set_tlb_state_scheme \<Rightarrow> unit \<times> 'a set_tlb_state_scheme))
  \<equiv> \<lambda>(value, vaddr, size). do {
      ttbr0 <- read_state TTBR0;
      mem   <- read_state MEM; 
      asid  <- read_state ASID;
      paddr <- mmu_translate vaddr :: ('a set_tlb_state_scheme \<Rightarrow> _);
      iset_snapshot <- read_state set_tlb;
      let incon_vaddrs = iset (iset_snapshot);
      let global_set = global_set (iset_snapshot);
      exception <- read_state exception;
      if exception = NoException 
        then  do {
                   write'mem1 (value, paddr, size);
                   mem' <- read_state MEM; 
                   let ptable_comp = incon_comp asid asid mem mem' ttbr0 ttbr0;
                   let incon_vaddrs_new    = incon_vaddrs \<union>  ptable_comp;
                    \<comment> \<open> pdc_walk are always asid specific, only using pt_walk for global_entries\<close>
                   let global_set_up = global_set \<union>  \<Union> (range_of ` global_entries (the ` {e\<in>pt_walk asid mem' ttbr0 ` UNIV. \<not>is_fault e}));
                   let iset_snapshot = iset_snapshot \<lparr>iset := incon_vaddrs_new , global_set := global_set_up \<rparr>;
                   update_state (\<lambda>s. s\<lparr> set_tlb :=  iset_snapshot \<rparr>)
            }
        else return ()
   }"

definition   
  "(update_TTBR0 r :: ('a set_tlb_state_scheme \<Rightarrow> _))  = do {
      ttbr0   <- read_state TTBR0;
      update_state (\<lambda>s. s\<lparr> TTBR0 := r \<rparr>);
      iset_snapshot   <- read_state set_tlb;
      let global_set = global_set (iset_snapshot);
      asid   <- read_state ASID;
      mem    <- read_state MEM;
       let ptable_asid_va = incon_comp asid asid mem mem ttbr0 r; 
       let incon_set_n = iset iset_snapshot \<union>  ptable_asid_va;
       let global_set_up = global_set \<union>  \<Union> (range_of `global_entries (the ` {e\<in>pt_walk asid mem r ` UNIV. \<not>is_fault e}));
       let iset_snapshot = iset_snapshot \<lparr>iset := incon_set_n , global_set := global_set_up \<rparr>;
      update_state (\<lambda>s. s\<lparr> set_tlb := iset_snapshot \<rparr>)
}"


definition
   "(update_ASID a :: ('a set_tlb_state_scheme \<Rightarrow> _))  = do {
      mem   <- read_state MEM;
      ttbr0 <- read_state TTBR0;
      asid  <- read_state ASID;
      iset_snapshot   <- read_state set_tlb;
      let iset = iset iset_snapshot;  \<comment> \<open>current iset\<close>
      let global_set = global_set (iset_snapshot);
      let snapshot = snapshot iset_snapshot;

      \<comment> \<open>incon vaddrs that are global\<close>
      \<comment> \<open>let iset_global = iset \<inter> \<Union> (range_of ` global_set);\<close>
      let iset_global = iset \<inter> global_set;
 
      \<comment> \<open>snapshot update\<close>
      let snapshot_current = snp_upd_cur' snapshot iset mem ttbr0 asid;
      let set_tlb = iset_snapshot \<lparr>snapshot := snapshot_current \<rparr>;
      update_state (\<lambda>s. s\<lparr> set_tlb := set_tlb \<rparr>);

      \<comment> \<open>new ASID\<close>
      update_state (\<lambda>s. s\<lparr> ASID := a \<rparr>);

     \<comment> \<open>for the new iset\<close>
     let iset_snp_incon = fst (snapshot_current a);
     let iset_snp = ptable_comp (snd(snapshot_current a)) (pt_walk_pair a mem ttbr0); 
     let set_tlb = set_tlb\<lparr> iset := iset_snp_incon \<union> iset_global \<union> iset_snp  \<rparr>;
     update_state (\<lambda>s. s\<lparr> set_tlb := set_tlb \<rparr>)
}"



definition   
  "(flush f :: ('a set_tlb_state_scheme \<Rightarrow> _))  \<equiv> do  {
                       asid      <- read_state ASID;
                       mem       <- read_state MEM;
                       ttbr0     <- read_state TTBR0;
                       set_tlb   <- read_state set_tlb;
                       let iset = iset set_tlb;
                       let global_set = global_set set_tlb;
                       let snapshot   = snapshot set_tlb;
                       case f of FlushTLB \<Rightarrow> do {
                                            let empty_set_tlb = set_tlb \<lparr>iset := {}, 
                                                    global_set :=  \<Union>(range_of ` global_entries (the ` {e \<in> range (pt_walk asid mem ttbr0). \<not> is_fault e})), 
                                                    snapshot := \<lambda> a. ({}, \<lambda>v. Fault) \<rparr>;
                                                    update_state (\<lambda>s. s\<lparr> set_tlb := empty_set_tlb \<rparr>) }
                               | Flushvarange vset \<Rightarrow>  do {
                                             let upd_set_tlb = set_tlb \<lparr>iset := iset - vset , 
                                                          global_set := (global_set  - vset)  \<union>
                                                         \<Union>(range_of ` global_entries (the ` {e \<in> range (pt_walk asid mem ttbr0). \<not> is_fault e})),
                                                    snapshot := \<lambda> a. (fst(snapshot a) - vset,  \<lambda>v. if v \<in> vset then Fault else snd(snapshot a) v) \<rparr>;
                                                    update_state (\<lambda>s. s\<lparr> set_tlb := upd_set_tlb \<rparr>) }
               | FlushASID a \<Rightarrow> 
                           if a = asid then 
                                update_state (\<lambda>s. s\<lparr> set_tlb := set_tlb \<lparr> iset := iset \<inter> global_set \<rparr> \<rparr> )
                           else do {
                               let upd_set_tlb = set_tlb \<lparr> snapshot := snapshot (a := ({}, \<lambda>v. Fault)) \<rparr>;
                                   update_state (\<lambda>s. s\<lparr> set_tlb := upd_set_tlb \<rparr>)
                             } 
                  | FlushASIDvarange a vset \<Rightarrow> 
                       
                          if a = asid then 
                               update_state (\<lambda>s. s\<lparr> set_tlb := set_tlb \<lparr> iset := iset - (vset - global_set)  \<rparr> \<rparr> )
                          else 
                               update_state (\<lambda>s. s\<lparr> set_tlb := set_tlb \<lparr> snapshot := \<lambda>a'. if a' = a then (fst (snapshot a) - vset, 
                                 \<lambda>v. if v \<in> vset then Fault else (snd (snapshot a)) v)  else snapshot a'  \<rparr> \<rparr> )
                         }"
 
  instance ..
end



end