theory MMU_Instants_TLB_Tag
imports
  Simp_Lemmas_ASIDs
  TLBJ.ARM_Monadic

begin


datatype asid_flush_type = FlushASID asid 
                         | FlushASIDvarange  asid "vaddr set" 


class  mmu_extended = mmu +
  fixes update_ASID      :: "asid \<Rightarrow> 'a state_scheme \<Rightarrow>  unit \<times> 'a state_scheme" 
  fixes flush_with_ASID  :: "asid_flush_type \<Rightarrow>'a state_scheme \<Rightarrow>  unit \<times> 'a state_scheme" 


definition
  flush_tlb_asid :: "tlb_with_asids \<Rightarrow> asid \<Rightarrow> tlb_with_asids"
where
  "flush_tlb_asid t a =  t - {e\<in>t. asid_of e = Some a}"


definition
  flush_tlb_a_vset :: "tlb_with_asids \<Rightarrow> asid \<Rightarrow> vaddr set \<Rightarrow> tlb_with_asids"
where
  "flush_tlb_a_vset t a vset = t - (\<Union>v\<in>vset. {e\<in>t. v \<in> range_of e \<and> asid_of e = Some a})"


record non_det_tlb_state = state + 
           non_det_asid :: asid 
           non_det_tlb  :: "asid tlb"

record det_tlb_state = state + 
           det_asid :: asid 
           det_tlb  :: "asid tlb"

record sat_tlb_state = state +
           sat_asid :: asid 
           sat_tlb  :: "asid tlb"


record set_tlb =
  iset       :: "vaddr set"
  global_set :: "vaddr set" (* "(asid tlb_entry) set" *)
  snapshot   :: "asid \<Rightarrow> (vaddr set \<times> (vaddr \<Rightarrow> asid tlb_entry option))"

record set_tlb_state  = state + 
            set_asid :: asid 
            set_tlb  :: set_tlb

definition 
  typ_non_det_tlb :: "'a non_det_tlb_state_scheme \<Rightarrow> (asid \<times> asid tlb_entry set) state_scheme"
where
  "typ_non_det_tlb s =  state.extend (state.truncate s) (non_det_asid s, non_det_tlb s)"

definition 
  typ_det_tlb :: "'a det_tlb_state_scheme \<Rightarrow> (asid \<times> asid tlb_entry set) state_scheme"
where
  "typ_det_tlb s =  state.extend (state.truncate s) (det_asid  s, det_tlb s)"

definition 
  typ_sat_tlb :: "'a sat_tlb_state_scheme \<Rightarrow> (asid \<times> asid tlb_entry set) state_scheme"
where
  "typ_sat_tlb s =  state.extend (state.truncate s) (sat_asid s, sat_tlb s)"


definition 
  typ_set_tlb :: "'a set_tlb_state_scheme \<Rightarrow> (asid \<times> set_tlb) state_scheme"
where
  "typ_set_tlb s =  state.extend (state.truncate s) (set_asid s, set_tlb s)"


lemma non_det_tlb_more [simp]:
  "state.more (typ_non_det_tlb s) = (non_det_asid s, non_det_tlb s)"
  by (clarsimp simp: typ_non_det_tlb_def state.defs)


lemma det_tlb_more [simp]:
  "state.more (typ_det_tlb s) = (det_asid  s, det_tlb s)"
  by (clarsimp simp: typ_det_tlb_def state.defs)


lemma sat_tlb_more [simp]:
  "state.more (typ_sat_tlb s) = (sat_asid s, sat_tlb s)"
  by (clarsimp simp: typ_sat_tlb_def state.defs)



lemma set_tlb_more' [simp]:
  "state.more (typ_set_tlb s) = (set_asid s, set_tlb s)"
  by (clarsimp simp: typ_set_tlb_def state.defs)


lemma non_det_tlb_truncate [simp]:
  "state.truncate (typ_non_det_tlb s') = state.truncate s'"
  by (clarsimp simp: typ_non_det_tlb_def state.defs)

lemma det_tlb_truncate [simp]:
  "state.truncate (typ_det_tlb s') = state.truncate s'"
  by (clarsimp simp: typ_det_tlb_def state.defs)

lemma sat_tlb_truncate [simp]:
  "state.truncate (typ_sat_tlb s') = state.truncate s'"
  by (clarsimp simp: typ_sat_tlb_def state.defs)

lemma set_tlb_truncate [simp]:
  "state.truncate (typ_set_tlb s') = state.truncate s'"
  by (clarsimp simp: typ_set_tlb_def state.defs)

lemma typ_non_det_prim_parameter [simp]:
  " TTBR0 (typ_non_det_tlb s) =  TTBR0 s \<and>
           MEM (typ_non_det_tlb s) = MEM s \<and> exception (typ_non_det_tlb s) = exception s"
  by (clarsimp simp: typ_non_det_tlb_def  state.defs)


lemma typ_det_prim_parameter [simp]:
  "TTBR0 (typ_det_tlb s) =  TTBR0 s \<and> MEM (typ_det_tlb s) = MEM s \<and> exception (typ_det_tlb s) = exception s"
  by (clarsimp simp: typ_det_tlb_def  state.defs)


lemma typ_sat_prim_parameter [simp]:
  "TTBR0 (typ_sat_tlb s) =  TTBR0 s \<and> MEM (typ_sat_tlb s) = MEM s \<and> exception (typ_sat_tlb s) = exception s"
  by (clarsimp simp: typ_sat_tlb_def  state.defs)


lemma typ_set_prim_parameter [simp]:
  "TTBR0 (typ_set_tlb s) =  TTBR0 s \<and> MEM (typ_set_tlb s) = MEM s \<and> exception (typ_set_tlb s) = exception s"
  by (clarsimp simp: typ_set_tlb_def  state.defs)


abbreviation
  "consistent (s:: (asid \<times> asid tlb_entry set) state_scheme) \<equiv>
               consistent0  (lookup'' (snd (state.more s)) (fst (state.more s))) (pt_walk (fst (state.more s)) (MEM s) (TTBR0 s))"


definition
  saturated :: "(asid \<times> asid tlb_entry set) state_scheme \<Rightarrow> bool"
where
  "saturated s  \<equiv> the ` {e\<in>pt_walk (fst (state.more s)) (MEM s) (TTBR0 s) ` UNIV. \<not>is_fault e} \<subseteq> snd (state.more s)"


definition 
  tlb_rel_det :: "(asid \<times> asid tlb_entry set)  state_scheme \<Rightarrow>(asid \<times> asid tlb_entry set)  state_scheme \<Rightarrow> bool"
where                                                                
  "tlb_rel_det s t \<equiv> state.truncate s = state.truncate t \<and>  fst(state.more s) = fst(state.more t) \<and>  snd(state.more s) \<subseteq> snd(state.more t)"

definition 
  tlb_rel_sat :: "(asid \<times> asid tlb_entry set) state_scheme \<Rightarrow> (asid \<times> asid tlb_entry set) state_scheme \<Rightarrow> bool"
where                                                                
  "tlb_rel_sat s t \<equiv> state.truncate s = state.truncate t \<and> fst(state.more s) = fst(state.more t) \<and>  snd(state.more s) \<subseteq> snd(state.more t)  \<and>  saturated t"



definition 
   inconsistent_vaddrs :: "(asid \<times> asid tlb_entry set) state_scheme \<Rightarrow>  vaddr set"
where                                                        
  "inconsistent_vaddrs s  \<equiv>  {va. lookup'' (snd(state.more s)) (fst(state.more s)) va = Incon}"


definition                              
   incoherrent_vaddrs :: "(asid \<times> asid tlb_entry set) state_scheme \<Rightarrow>  vaddr set"
where                                                         
  "incoherrent_vaddrs s  \<equiv> {va. \<exists>x. lookup'' (snd(state.more s)) (fst(state.more s)) va = Hit x \<and> 
                               is_fault (pt_walk  (fst(state.more s)) (MEM s) (TTBR0 s) va)} "


definition                              
   incon_addrs :: "(asid \<times> asid tlb_entry set) state_scheme \<Rightarrow>  vaddr set"
where                                                         
  "incon_addrs s  \<equiv>  inconsistent_vaddrs s \<union> incoherrent_vaddrs s"


definition
  snap_conv' :: "(vaddr set \<times> (vaddr \<Rightarrow> asid tlb_entry option)) \<Rightarrow> (vaddr \<Rightarrow> asid tlb_entry lookup_type)"
  where 
  "snap_conv' snp  \<equiv> \<lambda>v. if v \<in> (fst snp) then Incon else  
                          case (snd snp) v of None         \<Rightarrow> Miss
                                           |  Some entry   \<Rightarrow> if asid_of entry = None then Miss else Hit entry"

definition 
   "lookup_from' snp a v \<equiv> snap_conv' (snp a) v"


definition 
  tlb_rel_abs :: "(asid \<times> asid tlb_entry set) state_scheme  \<Rightarrow> (asid \<times> set_tlb) state_scheme \<Rightarrow> bool"
where                                                                
"tlb_rel_abs s t \<equiv>  state.truncate s = state.truncate t \<and> fst(state.more s) = fst(state.more t) \<and> 
                     saturated s \<and>
                     incon_addrs s \<subseteq>  iset (snd(state.more t)) \<and> 
                      \<Union>(range_of `  global_entries (snd(state.more s))) \<subseteq>  global_set (snd(state.more t)) \<and> 
                     (\<forall>a v. a \<noteq> fst (state.more s) \<longrightarrow>  lookup'' (snd (state.more s) - global_entries (snd (state.more s))) a v \<le> 
                                                          lookup_from' (snapshot (snd (state.more t))) a v)" 
(*
definition 
  tlb_rel_abs :: "(asid \<times> asid tlb_entry set) state_scheme  \<Rightarrow> (asid \<times> set_tlb) state_scheme \<Rightarrow> bool"
where                                                                
"tlb_rel_abs s t \<equiv>  state.truncate s = state.truncate t \<and> fst(state.more s) = fst(state.more t) \<and> 
                     saturated s \<and>
                     incon_addrs s \<subseteq>  iset (snd(state.more t)) \<and> 
                     global_entries (snd(state.more s)) \<subseteq>  global_set (snd(state.more t)) \<and> 
                     (\<forall>a v. a \<noteq> fst (state.more s) \<longrightarrow>  lookup'' (snd (state.more s) - global_entries (snd (state.more s))) a v \<le> 
                                                          lookup_from' (snapshot (snd (state.more t))) a v)" 
*)
                                                        
thm tlb_rel_abs_def

declare return_def [simp add]
declare bind_def [simp add]
declare read_state_def [simp add]
declare update_state_def [simp add]
declare extend_state_def [simp add]
declare trim_state_def [simp add]

lemma tlb_rel_detD:
  "tlb_rel_det s t \<Longrightarrow>  MEM t = MEM s \<and> TTBR0 t = TTBR0 s \<and> fst(state.more s) = fst (state.more t) \<and> 
                                          snd(state.more s) \<subseteq> snd(state.more t)  \<and>  exception t = exception s"
  by (clarsimp simp: tlb_rel_det_def state.defs)

lemma tlb_rel_satD:
  "tlb_rel_sat s t \<Longrightarrow> MEM t = MEM s \<and> TTBR0 t = TTBR0 s \<and> fst(state.more s) = fst (state.more t) \<and> snd(state.more s) \<subseteq> snd(state.more t) \<and> exception t = exception s  \<and> saturated t"
  by (clarsimp simp: tlb_rel_sat_def state.defs)


lemma tlb_rel_absD':
  "tlb_rel_abs s t \<Longrightarrow> MEM t = MEM s \<and> TTBR0 t = TTBR0 s  \<and> fst(state.more s) = fst (state.more t) \<and> saturated s \<and> 
                         incon_addrs s \<subseteq> iset (snd(state.more t)) \<and>   \<Union>(range_of `  global_entries (snd(state.more s))) \<subseteq> global_set (snd(state.more t)) \<and>
                          exception t = exception s"
  by (clarsimp simp: tlb_rel_abs_def state.defs)

lemma tlb_rel_det_consistent:
  "\<lbrakk> tlb_rel_det s t; consistent t va \<rbrakk> \<Longrightarrow> consistent s va" 
   by (insert tlb_rel_detD [of s t] , clarsimp ,drule asid_tlb_mono [of _ _ "fst (state.more s)" "va"] ,auto simp: consistent0_def less_eq_lookup_type)


lemma tlb_rel_sat_consistent:
  "\<lbrakk> tlb_rel_sat s t; consistent t va \<rbrakk> \<Longrightarrow> consistent s va"
   by (insert tlb_rel_satD [of s t] , clarsimp ,drule asid_tlb_mono [of _ _ "fst (state.more s)" "va"] ,auto simp: consistent0_def less_eq_lookup_type)


lemma sat_state_tlb:
  "saturated s  \<Longrightarrow> snd(state.more s) = 
         snd(state.more s) \<union> the ` {e \<in> range (pt_walk (fst(state.more s)) (MEM s) (TTBR0 s)). \<not> is_fault e}"
  by (fastforce simp: saturated_def)


lemma saturated_tlb:
  "saturated (typ_sat_tlb s) \<Longrightarrow> (sat_tlb s) = 
            sat_tlb s \<union> the ` {e\<in>pt_walk (sat_asid s) (MEM s) (TTBR0 s) ` UNIV. \<not>is_fault e}"
 apply (clarsimp simp:  saturated_def) apply (cases s ; clarsimp)  by blast 


lemma sat_miss_fault:
  "\<lbrakk> saturated (typ_sat_tlb s); lookup'' (sat_tlb s) (sat_asid s)  va = Miss \<rbrakk> \<Longrightarrow> 
           is_fault (pt_walk (sat_asid s) (MEM s) (TTBR0 s) va)"
  apply (subgoal_tac " lookup'' ((sat_tlb s)  \<union> the ` {e \<in> range (pt_walk(sat_asid s)  (MEM s) (TTBR0 s)). \<not> is_fault e}) (sat_asid s) va = Miss")
   apply (thin_tac "lookup'' ((sat_tlb s)) (sat_asid s) va = Miss")
   apply (drule lookup_asid_tlb_miss_union)
   apply clarsimp
   apply (drule asid_tlb_lookup_miss_is_fault)
   apply clarsimp
  using saturated_tlb by fastforce


lemma saturatd_lookup_hit_no_fault:
  "\<lbrakk>saturated (typ_sat_tlb s); 
    lookup'' (sat_tlb s) (sat_asid s)  b = Hit x; \<not> is_fault (pt_walk (sat_asid s)  (MEM s) (TTBR0 s) b)\<rbrakk> \<Longrightarrow>
                       x = the (pt_walk (sat_asid s) (MEM s) (TTBR0 s) b)"
  apply (subgoal_tac "lookup''(sat_tlb s \<union> 
                              the ` {e \<in> range (pt_walk (sat_asid s)  (MEM s) (TTBR0 s)). \<not> is_fault e}) (sat_asid s) b = Hit x")
   prefer 2
   apply (drule sat_state_tlb, clarsimp simp: state.defs)  defer
  apply (drule lookup_asid_tlb_hit_miss_or_hit')
  apply (erule disjE)
   apply (clarsimp simp: asid_tlb_lookup_range_pt_walk_hit)
  apply (frule asid_tlb_lookup_range_fault_pt_walk)
  by (drule_tac x = b in bspec; clarsimp simp: lookup_asid_tlb_hit_entry_range)



lemma saturated_global_entries_subset:
  " saturated (typ_sat_tlb s) \<Longrightarrow> 
      global_entries (the ` {e \<in> range (pt_walk (sat_asid s) (MEM s) (TTBR0 s)). \<not> is_fault e}) \<subseteq> 
          global_entries (sat_tlb s)"
  apply (subgoal_tac "global_entries (the ` {e \<in> range (pt_walk (sat_asid s) (MEM s) (TTBR0 s)). \<not> is_fault e})  \<subseteq>
                       the ` {e \<in> range (pt_walk (sat_asid s) (MEM s) (TTBR0 s)). \<not> is_fault e} ")
   apply (subgoal_tac "global_entries (sat_tlb s)  \<subseteq> sat_tlb s")
    apply (subgoal_tac "the ` {e \<in> range (pt_walk (sat_asid s) (MEM s) (TTBR0 s)). \<not> is_fault e}  \<subseteq> sat_tlb s ")
     apply (smt Un_absorb2 global_entries_union subset_Un_eq)
    apply (clarsimp simp: saturated_def)
  by (simp add: glb_tlb_subset)+

lemma saturated_global_subset_lookup_un_eq:
  "saturated (typ_sat_tlb s) \<Longrightarrow> 
        lookup''(global_entries (sat_tlb s) \<union> 
                 global_entries (the ` {e \<in> range (pt_walk a (MEM s) (TTBR0 s)). \<not> is_fault e}))  a v = 
                 lookup'' (global_entries (sat_tlb s)) a v"
  apply (rule tlb_subset_lookup_un_eq)
  apply (subgoal_tac "global_entries (the ` {e \<in> range (pt_walk a (MEM s) (TTBR0 s)). \<not> is_fault e}) = 
                       global_entries (the ` {e \<in> range (pt_walk (sat_asid s) (MEM s) (TTBR0 s)). \<not> is_fault e})")
   apply (simp only:)
   apply (clarsimp simp: saturated_def global_entries_def) apply blast
  by (rule global_entries_ptable_same)


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
  apply (clarsimp simp: incon_addrs_def inconsistent_vaddrs_def incoherrent_vaddrs_def consistent0_def)
  apply (erule disjE)
   apply (rule conjI)
    apply (meson lookup_type.exhaust )
   apply (meson lookup_type.exhaust) 
  using not_miss_incon_hit_asid_tlb saturatd_lookup_hit_no_fault by blast 



lemma tlb_rel_abs_consistent' [simp]:
  "\<lbrakk>va \<notin> iset(set_tlb t) ;   tlb_rel_abs  (typ_sat_tlb s) (typ_set_tlb t)  \<rbrakk>  \<Longrightarrow> 
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
  "\<lbrakk> write'mem1 (val, va, sz) s = ((), s') \<rbrakk>  \<Longrightarrow> TTBR0 s' = TTBR0 s"
   by (clarsimp simp: write'mem1_def raise'exception_def split: if_split_asm)

lemma tlb_sat_set_mem1 [simp]:
  "sat_tlb (snd (mem1 ps s)) = sat_tlb s"
  by (simp add: mem1_def raise'exception_def split: option.splits)


consts tlb_evict :: "('a \<times> 'b) state_scheme \<Rightarrow> 'b"


instantiation non_det_tlb_state_ext :: (type) mmu_extended       
begin
  definition                          
  "(mmu_translate va :: ('a non_det_tlb_state_scheme \<Rightarrow> _))
 = do {
     update_state (\<lambda>s. s\<lparr> non_det_tlb := non_det_tlb s - tlb_evict (typ_non_det_tlb s) \<rparr>);
     mem   <- read_state MEM;
     ttbr0 <- read_state TTBR0;
     asid <- read_state non_det_asid;
     tlb   <- read_state non_det_tlb;
          case lookup'' tlb asid va of 
               Hit entry \<Rightarrow> return (va_to_pa va entry)
          |    Miss \<Rightarrow> 
                   do { 
                       let entry = pt_walk asid mem ttbr0 va;
                       if is_fault entry 
                       then raise'exception (PAGE_FAULT ''more info'')
                       else do {
                                   update_state (\<lambda>s. s\<lparr> non_det_tlb := non_det_tlb s \<union>  {the entry} \<rparr>);
                                   return (va_to_pa va (the entry)) } }
          |    Incon \<Rightarrow> raise'exception (IMPLEMENTATION_DEFINED ''set on fire'') 
   }"

  
thm mmu_translate_non_det_tlb_state_ext_def                    

definition
 "(mmu_read_size  :: (vaddr \<times> nat \<Rightarrow>  'a non_det_tlb_state_scheme \<Rightarrow> bool list \<times>  'a non_det_tlb_state_scheme))
  \<equiv> \<lambda>(va,size). do {
                     pa  \<leftarrow> mmu_translate va :: ('a non_det_tlb_state_scheme \<Rightarrow> _);
                     mem_read1 (pa , size)
  }"

definition   
  "(mmu_write_size  :: (bool list \<times> vaddr \<times> nat \<Rightarrow> 'a non_det_tlb_state_scheme \<Rightarrow> unit \<times> 'a non_det_tlb_state_scheme))
   \<equiv> \<lambda>(value, va, size). do {
     pa <- mmu_translate va :: ('a non_det_tlb_state_scheme \<Rightarrow> _);
     exception <- read_state exception;
     if exception = NoException 
       then  write'mem1 (value, pa, size)
       else return ()
  }"
(* print_context *)                      


definition
  "(update_TTBR0 r :: ('a non_det_tlb_state_scheme \<Rightarrow> _))  = 
do {
    update_state (\<lambda>s. s\<lparr> TTBR0 := r \<rparr>)
  } "


definition   
  "(update_ASID a :: ('a non_det_tlb_state_scheme \<Rightarrow> _))  = 
    do {  update_state (\<lambda>s. s\<lparr> non_det_asid := a \<rparr>) }"

definition   
  "(flush f :: ('a non_det_tlb_state_scheme \<Rightarrow> _))  \<equiv> 
           case f of FlushTLB \<Rightarrow> update_state (\<lambda>s. s\<lparr> non_det_tlb := {} \<rparr>)
                  | Flushvarange vset \<Rightarrow> do {
                                         update_state (\<lambda>s. s\<lparr> non_det_tlb := flush_tlb_vset (non_det_tlb s) vset \<rparr>)}"

definition   
  "(flush_with_ASID f :: ('a non_det_tlb_state_scheme \<Rightarrow> _))  \<equiv> 
           case f of FlushASID a \<Rightarrow> do { update_state (\<lambda>s. s\<lparr> non_det_tlb := flush_tlb_asid (non_det_tlb s) a \<rparr>)}
                  |  FlushASIDvarange a vset \<Rightarrow> do {
                                         update_state (\<lambda>s. s\<lparr> non_det_tlb := flush_tlb_a_vset (non_det_tlb s) a vset \<rparr>)}"

 
  instance ..
end


               
instantiation det_tlb_state_ext :: (_) mmu_extended       
begin
  definition                          
  "(mmu_translate va :: ('a det_tlb_state_scheme \<Rightarrow> _))
 = do {
     mem   <- read_state MEM;
     ttbr0 <- read_state TTBR0;
     asid <- read_state det_asid;
     tlb   <- read_state det_tlb;
          case lookup'' tlb asid va of 
               Hit entry \<Rightarrow> return (va_to_pa va entry)
          |    Miss \<Rightarrow> 
                   do { 
                       let entry = pt_walk asid mem ttbr0 va;
                       if is_fault entry 
                       then raise'exception (PAGE_FAULT ''more info'')
                       else do {
                                   update_state (\<lambda>s. s\<lparr> det_tlb := det_tlb s \<union>  {the entry} \<rparr>);
                                   return (va_to_pa va (the entry)) } }
          |    Incon \<Rightarrow> raise'exception (IMPLEMENTATION_DEFINED ''set on fire'') 
   }"

thm mmu_translate_non_det_tlb_state_ext_def                    

definition
 "(mmu_read_size  :: (vaddr \<times> nat \<Rightarrow>  'a det_tlb_state_scheme \<Rightarrow> bool list \<times>  'a det_tlb_state_scheme))
  \<equiv> \<lambda>(va,size). do {
                     pa  \<leftarrow> mmu_translate va :: ('a det_tlb_state_scheme \<Rightarrow> _);
                     mem_read1 (pa , size)
  }"

definition   
  "(mmu_write_size  :: (bool list \<times> vaddr \<times> nat \<Rightarrow> 'a det_tlb_state_scheme \<Rightarrow> unit \<times> 'a det_tlb_state_scheme))
   \<equiv> \<lambda>(value, va, size). do {
     pa <- mmu_translate va :: ('a det_tlb_state_scheme \<Rightarrow> _);
     exception <- read_state exception;
     if exception = NoException 
       then  write'mem1 (value, pa, size)
       else return ()
  }"
(* print_context *)                      


definition
  "(update_TTBR0 r :: ('a det_tlb_state_scheme \<Rightarrow> _))  = 
do {
    update_state (\<lambda>s. s\<lparr> TTBR0 := r \<rparr>)
  } "


definition   
  "(update_ASID a :: ('a det_tlb_state_scheme \<Rightarrow> _))  = 
    do {  update_state (\<lambda>s. s\<lparr> det_asid := a \<rparr>) }"


definition   
  "(flush f :: ('a det_tlb_state_scheme \<Rightarrow> _))  \<equiv> 
           case f of FlushTLB \<Rightarrow> update_state (\<lambda>s. s\<lparr> det_tlb := {} \<rparr>)
                  | Flushvarange vset \<Rightarrow> do {
                                         update_state (\<lambda>s. s\<lparr> det_tlb := flush_tlb_vset (det_tlb s) vset \<rparr>)}"


definition   
  "(flush_with_ASID f :: ('a det_tlb_state_scheme \<Rightarrow> _))  \<equiv> 
           case f of FlushASID a \<Rightarrow> do { update_state (\<lambda>s. s\<lparr> det_tlb := flush_tlb_asid (det_tlb s) a \<rparr>)}
                  |  FlushASIDvarange a vset \<Rightarrow> do {
                                         update_state (\<lambda>s. s\<lparr> det_tlb := flush_tlb_a_vset (det_tlb s) a vset \<rparr>)}"

 
  instance ..
end



instantiation sat_tlb_state_ext :: (_) mmu_extended       
begin
  definition                          
  "(mmu_translate va :: ('a sat_tlb_state_scheme \<Rightarrow> _))
 = do {
     mem   <- read_state MEM;
     ttbr0 <- read_state TTBR0;
     asid <- read_state sat_asid;
     let tlb_new = the ` {e\<in>pt_walk asid mem ttbr0 ` UNIV. \<not>is_fault e};
     tlb   <- read_state sat_tlb;
     let sat_tlb' = tlb \<union> tlb_new;
     update_state (\<lambda>s. s\<lparr> sat_tlb := sat_tlb' \<rparr>);
          case lookup'' sat_tlb' asid va of 
               Hit entry \<Rightarrow> return (va_to_pa va entry)
          |    Miss \<Rightarrow> raise'exception (PAGE_FAULT ''more info'') 
          |    Incon \<Rightarrow> raise'exception (IMPLEMENTATION_DEFINED ''set on fire'') 
   }"

thm mmu_translate_non_det_tlb_state_ext_def                    
 


definition
 "(mmu_read_size  :: (vaddr \<times> nat \<Rightarrow>  'a sat_tlb_state_scheme \<Rightarrow> bool list \<times>  'a sat_tlb_state_scheme))
  \<equiv> \<lambda>(va,size). do {
                     pa  \<leftarrow> mmu_translate va :: ('a sat_tlb_state_scheme \<Rightarrow> _);
                     mem_read1 (pa , size)
  }"

definition   
  "(mmu_write_size  :: (bool list \<times> vaddr \<times> nat \<Rightarrow> 'a sat_tlb_state_scheme \<Rightarrow> unit \<times> 'a sat_tlb_state_scheme))
   \<equiv> \<lambda>(value, va, size). do {
      ttbr0 <- read_state TTBR0;
      asid <- read_state sat_asid;
      pa <- mmu_translate va :: ('a sat_tlb_state_scheme \<Rightarrow> _);
      tlb   <- read_state sat_tlb;
      exception <- read_state exception;
      if exception = NoException 
       then  do {
                 write'mem1 (value, pa, size);
                 mem'  <- read_state MEM;
                 let tlb_new = the ` {e\<in>pt_walk asid mem' ttbr0 ` UNIV. \<not>is_fault e};
                 update_state (\<lambda>s. s\<lparr> sat_tlb := tlb \<union> tlb_new \<rparr>) }
       else return ()
  }"
(* print_context *)                      


definition
  "(update_TTBR0 r :: ('a sat_tlb_state_scheme \<Rightarrow> _))  = 
do {
      update_state (\<lambda>s. s\<lparr> TTBR0 := r \<rparr>);
      mem   <- read_state MEM;
      asid <- read_state sat_asid;
      let all_entries = the ` {e\<in>pt_walk asid mem r ` UNIV. \<not>is_fault e};
      tlb   <- read_state sat_tlb;
      update_state (\<lambda>s. s\<lparr> sat_tlb := tlb \<union> all_entries \<rparr>)}"


definition   
  "(update_ASID a :: ('a sat_tlb_state_scheme \<Rightarrow> _))  = do {
      update_state (\<lambda>s. s\<lparr> sat_asid := a \<rparr>);
      mem   <- read_state MEM;
      ttbr0 <- read_state TTBR0;
      let tlb_new = the `{e\<in>pt_walk a mem ttbr0 ` UNIV. \<not>is_fault e};
      tlb0   <- read_state sat_tlb;
      let tlb = tlb0 \<union> tlb_new; 
      update_state (\<lambda>s. s\<lparr> sat_tlb := tlb \<rparr>)} "


definition   
  "(flush f :: ('a sat_tlb_state_scheme \<Rightarrow> _))  \<equiv>  do {
      mem   <- read_state MEM;
      ttbr0 <- read_state TTBR0;
      asid <- read_state sat_asid;
      let tlb_new = the ` {e\<in>pt_walk asid mem ttbr0 ` UNIV. \<not>is_fault e};
      case f of FlushTLB \<Rightarrow>  update_state (\<lambda>s. s\<lparr> sat_tlb := tlb_new \<rparr>)
             | Flushvarange vset \<Rightarrow>  do {
                                  tlb0 <- read_state sat_tlb;
                                  update_state (\<lambda>s. s\<lparr> sat_tlb := flush_tlb_vset tlb0 vset \<union> tlb_new \<rparr>)}}"


definition   
  "(flush_with_ASID f :: ('a sat_tlb_state_scheme \<Rightarrow> _))  \<equiv>  do {
      mem   <- read_state MEM;
      ttbr0 <- read_state TTBR0;
      asid <- read_state sat_asid;
      tlb0 <- read_state sat_tlb;
      let tlb_new = the ` {e\<in>pt_walk asid mem ttbr0 ` UNIV. \<not>is_fault e};
      case f of FlushASID a \<Rightarrow>  update_state (\<lambda>s. s\<lparr> sat_tlb := flush_tlb_asid tlb0 a \<union>  tlb_new \<rparr>)
             | FlushASIDvarange a vset \<Rightarrow>  
                        
                                  update_state (\<lambda>s. s\<lparr> sat_tlb := flush_tlb_a_vset tlb0 a vset \<union> tlb_new \<rparr>)}"


  instance ..
end


definition
  ptable_comp :: "(vaddr \<Rightarrow> asid tlb_entry option) \<Rightarrow> (vaddr \<Rightarrow> asid tlb_entry option) \<Rightarrow> vaddr set"
where
  "ptable_comp wlk wlk'  \<equiv> {va. \<not> is_fault (wlk va) \<and> \<not> is_fault (wlk' va) \<and> wlk va \<noteq> wlk' va \<or> 
                                 \<not> is_fault (wlk va) \<and> is_fault (wlk' va)}"


definition
  incon_comp :: "asid \<Rightarrow> asid \<Rightarrow> heap \<Rightarrow> heap \<Rightarrow> paddr \<Rightarrow> paddr \<Rightarrow> vaddr set"
where
  "incon_comp  a a' hp hp' rt rt' \<equiv> ptable_comp (pt_walk a hp rt) (pt_walk a' hp' rt')"



definition 
  snp_upd_cur :: "vaddr set \<Rightarrow> heap \<Rightarrow> ttbr0  \<Rightarrow> asid \<Rightarrow> (vaddr set \<times> (vaddr \<Rightarrow> asid tlb_entry option))"
where
  "snp_upd_cur ist m r  \<equiv> \<lambda>a. (ist, \<lambda>v. pt_walk a m r v)"


definition 
  snp_upd_cur' :: "(asid \<Rightarrow> (vaddr set \<times> (vaddr \<Rightarrow> asid tlb_entry option))) \<Rightarrow> vaddr set \<Rightarrow> 
                                 heap \<Rightarrow> ttbr0 \<Rightarrow> asid \<Rightarrow> (asid \<Rightarrow> (vaddr set \<times> (vaddr \<Rightarrow> asid tlb_entry option)))"
where
  "snp_upd_cur' snp ist mem ttbr0 a \<equiv> snp (a := snp_upd_cur ist mem ttbr0 a)"


instantiation set_tlb_state_ext :: (_) mmu_extended      
begin
  definition                          
  "(mmu_translate va :: ('a set_tlb_state_scheme \<Rightarrow> _))
 = do {
     mem   <- read_state MEM;
     ttbr0 <- read_state TTBR0;
     asid <- read_state set_asid;
     iset_snapshot <- read_state set_tlb;
     let incon_vaddrs = iset (iset_snapshot);
     if  va \<in> incon_vaddrs 
       then raise'exception (IMPLEMENTATION_DEFINED ''set on fire'')
       else let entry = pt_walk asid mem ttbr0 va in 
             if is_fault entry
              then raise'exception (PAGE_FAULT ''more info'')
              else return (va_to_pa va (the entry))
    }"


definition
 "(mmu_read_size  :: (vaddr \<times> nat \<Rightarrow>  'a set_tlb_state_scheme \<Rightarrow> bool list \<times>  'a set_tlb_state_scheme))
  \<equiv> \<lambda>(va,size). do {
                     pa  \<leftarrow> mmu_translate va :: ('a set_tlb_state_scheme \<Rightarrow> _);
                     mem_read1 (pa , size)
  }"

definition   
  "(mmu_write_size  :: (bool list \<times> vaddr \<times> nat \<Rightarrow> 'a set_tlb_state_scheme \<Rightarrow> unit \<times> 'a set_tlb_state_scheme))
   \<equiv> \<lambda>(value, va, size). do {
      ttbr0 <- read_state TTBR0;
      mem   <- read_state MEM; 
      asid <- read_state set_asid;
      paddr <- mmu_translate va :: ('a set_tlb_state_scheme \<Rightarrow> _);
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
               \<comment> \<open>let global_set_up = global_set \<union>  global_entries (the ` {e\<in>pt_walk asid mem' ttbr0 ` UNIV. \<not>is_fault e});\<close>
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
      asid <- read_state set_asid;
      mem  <- read_state MEM;
       let incon_vaddrs_new = incon_comp asid asid mem mem ttbr0 r; 
       let incon_set_n = iset iset_snapshot \<union>  incon_vaddrs_new;
   \<comment> \<open>let global_set_up = global_set \<union>  global_entries (the ` {e\<in>pt_walk asid mem r ` UNIV. \<not>is_fault e});\<close>
       let global_set_up = global_set \<union>  \<Union> (range_of `global_entries (the ` {e\<in>pt_walk asid mem r ` UNIV. \<not>is_fault e}));
       let iset_snapshot = iset_snapshot \<lparr>iset := incon_set_n , global_set := global_set_up \<rparr>;
      update_state (\<lambda>s. s\<lparr> set_tlb := iset_snapshot \<rparr>)
}"


definition
   "(update_ASID a :: ('a set_tlb_state_scheme \<Rightarrow> _))  = do {
      mem   <- read_state MEM;
      ttbr0 <- read_state TTBR0;
      asid  <- read_state set_asid;
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
      update_state (\<lambda>s. s\<lparr> set_asid := a \<rparr>);

     \<comment> \<open>for the new iset\<close>
     let iset_snp_incon = fst (snapshot_current a);
     let iset_snp = ptable_comp (snd(snapshot_current a)) (pt_walk a mem ttbr0); 
     let set_tlb = set_tlb\<lparr> iset := iset_snp_incon \<union> iset_global \<union> iset_snp  \<rparr>;
     update_state (\<lambda>s. s\<lparr> set_tlb := set_tlb \<rparr>)
}"




definition   
  "(flush f :: ('a set_tlb_state_scheme \<Rightarrow> _))  \<equiv> do  {
                       asid    <- read_state set_asid;
                       mem     <- read_state MEM;
                       ttbr0   <- read_state TTBR0;
                       set_tlb   <- read_state set_tlb;
                       let iset = iset set_tlb;
                       let global_set = global_set set_tlb;
                       let snapshot = snapshot set_tlb;
                       case f of FlushTLB \<Rightarrow> do {
                                            let empty_set_tlb = set_tlb \<lparr>iset := {}, 
                                                    global_set :=  \<Union>(range_of ` global_entries (the ` {e \<in> range (pt_walk asid mem ttbr0). \<not> is_fault e})), 
                                                    snapshot := \<lambda> a. ({}, Map.empty) \<rparr>;
                                                    update_state (\<lambda>s. s\<lparr> set_tlb := empty_set_tlb \<rparr>) }
                               | Flushvarange vset \<Rightarrow>  do {
                                             let upd_set_tlb = set_tlb \<lparr>iset := iset - vset , 
                                                  \<comment> \<open>  global_set := (global_set  - \<Union>(entry_set global_set ` vset))  \<union>
                                                          global_entries (the ` {e \<in> range (pt_walk asid mem ttbr0). \<not> is_fault e}), \<close> 
                                                          global_set := (global_set  - vset)  \<union>
                                                         \<Union>(range_of ` global_entries (the ` {e \<in> range (pt_walk asid mem ttbr0). \<not> is_fault e})),
                                                    snapshot := \<lambda> a. (fst(snapshot a) - vset,  \<lambda>v. if v \<in> vset then None else snd(snapshot a) v) \<rparr>;
                                                    update_state (\<lambda>s. s\<lparr> set_tlb := upd_set_tlb \<rparr>) }}"


definition   
  "(flush_with_ASID f :: ('a set_tlb_state_scheme \<Rightarrow> _))  \<equiv> do {
                       asid    <- read_state set_asid;
                       mem     <- read_state MEM;
                       ttbr0   <- read_state TTBR0;
                       set_tlb   <- read_state set_tlb;
                       let iset = iset set_tlb;
                       let global_set = global_set set_tlb;
                       let snapshot = snapshot set_tlb;
                        case f of FlushASID a \<Rightarrow> 
                           if a = asid then 
                                update_state (\<lambda>s. s\<lparr> set_tlb := set_tlb \<lparr> iset := iset \<inter> global_set \<rparr> \<rparr> )
                           else do {
                               let upd_set_tlb = set_tlb \<lparr> snapshot := snapshot (a := ({}, \<lambda>v. None)) \<rparr>;
                                   update_state (\<lambda>s. s\<lparr> set_tlb := upd_set_tlb \<rparr>)
                             } 
                  | FlushASIDvarange a vset \<Rightarrow> 
                       
                          if a = asid then 
                               update_state (\<lambda>s. s\<lparr> set_tlb := set_tlb \<lparr> iset := iset - (vset - global_set)  \<rparr> \<rparr> )
                          else 
                               update_state (\<lambda>s. s\<lparr> set_tlb := set_tlb \<lparr> snapshot := \<lambda>a'. if a' = a then (fst (snapshot a) - vset, 
                                 \<lambda>v. if v \<in> vset then None else (snd (snapshot a)) v)  else snapshot a'  \<rparr> \<rparr> )
                         }"
 
  instance ..
end


end
