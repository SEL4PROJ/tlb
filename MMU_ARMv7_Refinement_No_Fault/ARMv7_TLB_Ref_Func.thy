theory ARMv7_TLB_Ref_Func

imports  MMU_ARM.ARM_Monadic

begin               



record tlb_state = state + 
           tlb_set :: "tlb_entry set"


record tlb_det_state = state + 
           tlb_det_set :: "tlb_entry set"


record tlb_sat_state = state + 
           tlb_sat_set :: "tlb_entry set"


record tlb_incon_set' =
  incon_set    :: "(asid \<times> vaddr) set"
  tlb_snapshot :: "asid \<Rightarrow> vaddr \<Rightarrow> lookup_type"


record tlb_incon_state' = state + 
           tlb_incon_set' :: tlb_incon_set'


record tlb_incon_set =
  iset     :: "vaddr set"
  snapshot :: "asid \<Rightarrow> vaddr \<Rightarrow> lookup_type"


record tlb_incon_state = state + 
           tlb_incon_set :: tlb_incon_set



definition 
  typ_tlb :: "'a tlb_state_scheme \<Rightarrow> tlb_entry set state_scheme"
where
  "typ_tlb s =  state.extend (state.truncate s) (tlb_set s)"


definition 
  typ_det_tlb :: "'a tlb_det_state_scheme \<Rightarrow> tlb_entry set state_scheme"
where
  "typ_det_tlb s =  state.extend (state.truncate s) (tlb_det_set s)"



definition 
  typ_sat_tlb :: "'a tlb_sat_state_scheme \<Rightarrow> tlb_entry set state_scheme"
where
  "typ_sat_tlb s =  state.extend (state.truncate s) (tlb_sat_set s)"



definition 
  typ_incon' :: "'a tlb_incon_state'_scheme \<Rightarrow> tlb_incon_set' state_scheme"
where
  "typ_incon' s =  state.extend (state.truncate s) (tlb_incon_set' s)"


definition 
  typ_incon'2 :: "'a tlb_incon_state_scheme \<Rightarrow> tlb_incon_set state_scheme"
where
  "typ_incon'2 s =  state.extend (state.truncate s) (tlb_incon_set s)"


lemma tlb_more [simp]:
  "state.more (typ_tlb s) = tlb_set s"
  by (clarsimp simp: typ_tlb_def state.defs)


lemma tlb_det_more [simp]:
  "state.more (typ_det_tlb s) = tlb_det_set s"
  by (clarsimp simp: typ_det_tlb_def state.defs)


lemma tlb_sat_more [simp]:
  "state.more (typ_sat_tlb s) = tlb_sat_set s"
  by (clarsimp simp: typ_sat_tlb_def state.defs)

lemma tlb_incon_more' [simp]:
  "state.more (typ_incon' s) = tlb_incon_set' s"
  by (clarsimp simp: typ_incon'_def state.defs)

lemma tlb_incon_more'2 [simp]:
  "state.more (typ_incon'2 s) = tlb_incon_set s"
  by (clarsimp simp: typ_incon'2_def state.defs)


lemma tlb_truncate [simp]:
  "state.truncate (typ_tlb s') = state.truncate s'"
  by (clarsimp simp: typ_tlb_def state.defs)

lemma tlb_det_truncate [simp]:
  "state.truncate (typ_det_tlb s') = state.truncate s'"
  by (clarsimp simp: typ_det_tlb_def state.defs)

lemma tlb_sat_truncate [simp]:
  "state.truncate (typ_sat_tlb s') = state.truncate s'"
  by (clarsimp simp: typ_sat_tlb_def state.defs)

lemma tlb_incon_truncate' [simp]:
  "state.truncate (typ_incon' s') = state.truncate s'"
  by (clarsimp simp: typ_incon'_def state.defs)


lemma tlb_incon_truncate'2 [simp]:
  "state.truncate (typ_incon'2 s') = state.truncate s'"
  by (clarsimp simp: typ_incon'2_def state.defs)


lemma typ_prim_parameter [simp]:
  "ASID (typ_tlb s) = ASID s \<and> TTBR0 (typ_tlb s) =  TTBR0 s \<and> MEM (typ_tlb s) = MEM s \<and>
      exception (typ_tlb s) = exception s"
  by (clarsimp simp: typ_tlb_def  state.defs)


lemma typ_det_prim_parameter [simp]:
  "ASID (typ_det_tlb s) = ASID s \<and> TTBR0 (typ_det_tlb s) =  TTBR0 s \<and> MEM (typ_det_tlb s) = MEM s \<and>
      exception (typ_det_tlb s) = exception s"
  by (clarsimp simp: typ_det_tlb_def state.defs)


lemma typ_sat_prim_parameter [simp]:
  "ASID (typ_sat_tlb s) = ASID s \<and> TTBR0 (typ_sat_tlb s) =  TTBR0 s \<and> MEM (typ_sat_tlb s) = MEM s \<and>
      exception (typ_sat_tlb s) = exception s"
  by (clarsimp simp: typ_sat_tlb_def state.defs)


lemma typ_incon_prim_parameter' [simp]:
  "ASID (typ_incon' s) = ASID s \<and> TTBR0 (typ_incon' s) =  TTBR0 s \<and> MEM (typ_incon' s) = MEM s \<and>
      exception (typ_incon' s) = exception s"
  by (clarsimp simp: typ_incon'_def state.defs)

lemma typ_incon_prim_parameter'2 [simp]:
  "ASID (typ_incon'2 s) = ASID s \<and> TTBR0 (typ_incon'2 s) =  TTBR0 s \<and> MEM (typ_incon'2 s) = MEM s \<and>
      exception (typ_incon'2 s) = exception s"
  by (clarsimp simp: typ_incon'2_def state.defs)


definition
  "consistent0 m asid ttbr0 tlb va \<equiv>
     (lookup tlb asid va = Hit (the (pt_walk asid m ttbr0 va)) \<and> \<not>is_fault (pt_walk asid m ttbr0 va)) \<or>
     lookup tlb asid va = Miss"


abbreviation
  "consistent (s::tlb_entry set state_scheme) \<equiv>
               consistent0 (MEM s) (ASID s) (TTBR0 s) (state.more s)"


definition 
   asid_va_incon :: "tlb \<Rightarrow> (asid \<times> vaddr) set"
where                                                        
  "asid_va_incon tlb  \<equiv>  {(asid, va). lookup tlb asid va = Incon}"


definition
  saturated :: "tlb_entry set state_scheme \<Rightarrow> bool"
where
  "saturated s  \<equiv> 
       the ` {e\<in>pt_walk (ASID s) (MEM s) (TTBR0 s) ` UNIV. \<not>is_fault e} \<subseteq> state.more s"


definition
  tlb_rel :: "tlb_entry set state_scheme \<Rightarrow> tlb_entry set state_scheme \<Rightarrow> bool"
where
  "tlb_rel s t \<equiv> state.truncate s = state.truncate t \<and> state.more s \<subseteq> state.more t "


definition 
  tlb_rel_sat :: "tlb_entry set state_scheme \<Rightarrow> tlb_entry set state_scheme \<Rightarrow> bool"
where                                                                
  "tlb_rel_sat s t \<equiv> state.truncate s = state.truncate t \<and> state.more s \<subseteq> state.more t \<and> saturated t"

(*
definition                              
   asid_va_hit_incon :: "tlb_entry set state_scheme \<Rightarrow> (asid \<times> vaddr) set"
where                                                         
  "asid_va_hit_incon s  \<equiv>  {(asid, va). asid = ASID s \<and>  
                            (\<exists>x. lookup (state.more s) asid va = Hit x \<and> x \<noteq> the (pt_walk (ASID s) (MEM s) (TTBR0 s) va )) }"
*)


definition                              
   asid_va_hit_incon' :: "tlb_entry set state_scheme \<Rightarrow> (asid \<times> vaddr) set"
where                                                         
  "asid_va_hit_incon' s  \<equiv> 
                  {(asid, va). asid = ASID s \<and>  
                   (\<exists>x. lookup (state.more s) asid va = Hit x \<and> x \<noteq> the (pt_walk (ASID s) (MEM s) (TTBR0 s) va) \<and>
                         \<not>is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) va ) ) }"

definition                              
   asid_va_hit_incon'' :: "tlb_entry set state_scheme \<Rightarrow> (asid \<times> vaddr) set"
where                                                         
  "asid_va_hit_incon'' s  \<equiv> 
                  {(asid, va). asid = ASID s \<and>  (\<exists>x. lookup (state.more s) asid va = Hit x) \<and>
                   is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) va ) }"


definition                              
   asid_va_hit_incon_inter :: "tlb_entry set state_scheme \<Rightarrow> (asid \<times> vaddr) set"
where                                                         
  "asid_va_hit_incon_inter s  \<equiv>  asid_va_hit_incon' s \<union> asid_va_hit_incon'' s"


definition                              
   asid_va_hit_incon :: "tlb_entry set state_scheme \<Rightarrow> (asid \<times> vaddr) set"
where                                                         
  "asid_va_hit_incon s  \<equiv>  (\<lambda>va. (ASID s , va)) ` {va. \<exists>x. lookup (state.more s) (ASID s) va = Hit x \<and>
                                                         ((x \<noteq> the (pt_walk (ASID s) (MEM s) (TTBR0 s) va) \<and>
                                                               \<not>is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) va ) ) \<or>
                                                         is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) va ))}"




lemma asid_calib_thm [simp]:
  "asid_va_hit_incon s = asid_va_hit_incon_inter s"
  apply (clarsimp simp: asid_va_hit_incon_def asid_va_hit_incon'_def asid_va_hit_incon''_def asid_va_hit_incon_inter_def)
    by blast
    

definition                              
   asid_va_incon_tlb_mem :: "tlb_entry set state_scheme \<Rightarrow> (asid \<times> vaddr) set"
where                                                         
  "asid_va_incon_tlb_mem s  \<equiv>  asid_va_incon (state.more s) \<union> asid_va_hit_incon s "



definition 
  snapshot_of_tlb :: "tlb \<Rightarrow>  asid \<Rightarrow> vaddr \<Rightarrow> lookup_type"
where                                                                
  "snapshot_of_tlb t \<equiv> (\<lambda> a v. lookup t a v)"


definition 
  tlb_rel_abs' :: "tlb_entry set state_scheme \<Rightarrow> tlb_incon_set' state_scheme \<Rightarrow> bool"
where                                                                
  "tlb_rel_abs' s t \<equiv> state.truncate s = state.truncate t \<and> asid_va_incon_tlb_mem s \<subseteq> incon_set (state.more t) \<and> 
                       saturated s \<and> 
                         (\<forall>a v. a \<noteq> ASID s \<longrightarrow> snapshot_of_tlb (state.more s) a v \<le> tlb_snapshot (state.more t) a v) \<and>
                          {(a,v). tlb_snapshot (state.more t) a  v = Incon }  \<subseteq>  incon_set (state.more t)" 


(* refinement relation for the last abstraction *)

definition 
  refine_rel :: "tlb_incon_set' state_scheme \<Rightarrow> tlb_incon_set state_scheme \<Rightarrow> bool"
where  
"refine_rel s t \<equiv> state.truncate s = state.truncate t \<and> 
                   (\<forall>a v. a \<noteq> ASID s \<longrightarrow> ((tlb_snapshot (state.more s) a  v = Incon) = ((a,v) \<in> incon_set (state.more s)))) \<and> 
                 (*done *)  (\<forall>a v. a \<noteq> ASID s \<longrightarrow> tlb_snapshot (state.more s) a  v \<le> snapshot (state.more t) a  v) \<and> 
                   {v. (ASID s,v) \<in> incon_set (state.more s)}  \<subseteq>  iset (state.more t)" 



definition 
   asid_va_incon_n :: "tlb_entry set state_scheme \<Rightarrow>  vaddr set"
where                                                        
  "asid_va_incon_n s  \<equiv>  {va. lookup (state.more s) (ASID s) va = Incon}"


definition                              
   asid_va_hit_incon_n :: "tlb_entry set state_scheme \<Rightarrow>  vaddr set"
where                                                         
  "asid_va_hit_incon_n s  \<equiv>   {va. \<exists>x. lookup (state.more s) (ASID s) va = Hit x \<and>
                                   ((x \<noteq> the (pt_walk (ASID s) (MEM s) (TTBR0 s) va) \<and>
                                     \<not>is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) va ) ) \<or>
                                      is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) va ))}"


definition                              
   asid_va_incon_tlb_mem_n :: "tlb_entry set state_scheme \<Rightarrow>  vaddr set"
where                                                         
  "asid_va_incon_tlb_mem_n s  \<equiv>  asid_va_incon_n s \<union> asid_va_hit_incon_n s "



definition 
  invar_rel :: "tlb_entry set state_scheme  \<Rightarrow> tlb_incon_set state_scheme \<Rightarrow> bool"
where                                                                
"invar_rel s t \<equiv>  state.truncate s = state.truncate t \<and> asid_va_incon_tlb_mem_n s \<subseteq>  iset (state.more t) \<and> 
                       saturated s 
    \<and> (\<forall>a v. a \<noteq> ASID s \<longrightarrow> snapshot_of_tlb (state.more s) a v \<le> snapshot (state.more t) a v)" 
                       (* may have to add the incon equality here, or may be not*)

consts tlb_evict :: "tlb_entry set state_scheme \<Rightarrow> tlb_entry set"


declare return_def [simp add]
declare bind_def [simp add]
declare read_state_def [simp add]
declare update_state_def [simp add]
declare extend_state_def [simp add]
declare trim_state_def [simp add]


lemma consistent_not_Incon:
  "consistent0 m asid ttbr0 tlb va = 
  (lookup tlb asid va \<noteq> Incon \<and> (\<forall>e. lookup tlb asid va = Hit e \<longrightarrow> e = the (pt_walk asid m ttbr0 va) 
             \<and> pt_walk asid m ttbr0 va \<noteq> None))"
  by (cases "lookup tlb asid va"; simp add: consistent0_def is_fault_def)


lemma tlb_relD:
  "tlb_rel s t \<Longrightarrow> ASID t = ASID s \<and> MEM t = MEM s \<and> TTBR0 t = TTBR0 s \<and>
      state.more s \<subseteq> state.more t \<and> exception t = exception s"
  by (clarsimp simp: tlb_rel_def state.defs)

lemma tlb_rel_consistent:
  "\<lbrakk> tlb_rel s t; consistent t va \<rbrakk> \<Longrightarrow> 
          consistent s va"
  apply (drule tlb_relD)
  apply clarsimp
  apply (drule tlb_mono [of _ _ "ASID s" "va"])
  by (auto simp: consistent0_def less_eq_lookup_type typ_det_tlb_def state.defs)



lemma tlb_rel_satD:
  "tlb_rel_sat s t \<Longrightarrow>
      ASID t = ASID s \<and> MEM t = MEM s \<and> TTBR0 t = TTBR0 s \<and>  state.more s \<subseteq>  state.more t \<and> exception t = exception s"
  by (clarsimp simp: tlb_rel_sat_def state.defs)


lemma tlb_rel_sat_consistent:
  "\<lbrakk> tlb_rel_sat s t; consistent t va \<rbrakk> \<Longrightarrow> consistent s va"
  apply (drule  tlb_rel_satD)
  apply clarsimp
  apply (drule tlb_mono [of _ _ "ASID s" va])
  apply (auto simp: consistent0_def less_eq_lookup_type)
  done


(*find_theorems consistent
  thm consistent_tlb_state_ext_def
  help*)

lemma lookup_in_tlb:
  "lookup tlb asid va = Hit e \<Longrightarrow> e \<in> tlb"
  by (auto simp: lookup_def entry_set_def split: if_split_asm)

lemma entry_set_insert:
  "\<lbrakk> entry_set tlb asid va = {}; asid_entry e = asid; va \<in> entry_range e \<rbrakk> \<Longrightarrow> 
  entry_set (insert e tlb) asid va = {e}"
  by (auto simp add: entry_set_def entry_range_asid_tags_def)

lemma asid_entry_pt_walk [simp]:
  "pt_walk asid m ttbr0 va \<noteq> None \<Longrightarrow> asid_entry (the (pt_walk asid m ttbr0 va)) = asid"
  apply (simp add: pt_walk_def Let_def)
  apply ((((cases "get_pde m ttbr0 va" ; clarsimp) , case_tac a ; clarsimp) , 
      case_tac "get_pte m x3 va" ; clarsimp) , case_tac a ; clarsimp)
  done


lemma asid_entry_pt_walk''' [simp]:
  "\<not>is_fault(pt_walk asid m ttbr0 va) \<Longrightarrow> asid_entry (the (pt_walk asid m ttbr0 va)) = asid"
  apply (simp add: pt_walk_def Let_def is_fault_def)
  apply ((((cases "get_pde m ttbr0 va" ; clarsimp) , case_tac a ; clarsimp) , 
      case_tac "get_pte m x3 va" ; clarsimp) , case_tac a ; clarsimp)
  done

lemma asid_entry_pt_walk' [simp]:
  "pt_walk asid m ttbr0 va = Some x \<Longrightarrow> asid_entry (the (pt_walk asid m ttbr0 va)) = asid"
  apply (simp add: pt_walk_def Let_def)
  apply ((((cases "get_pde m ttbr0 va" ; clarsimp) , case_tac a ; clarsimp) , 
      case_tac "get_pte m x3 va" ; clarsimp) , case_tac a ; clarsimp)
  done

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

lemma asid_entry_range [simp, intro!]:
  "pt_walk asid m ttbr0 va \<noteq> None \<Longrightarrow> va \<in> entry_range (the (pt_walk asid m ttbr0 va))"
  apply (clarsimp simp: entry_range_def pt_walk_def Let_def)
  apply (cases "get_pde m ttbr0 va" ; clarsimp simp: image_iff)
  apply (case_tac a; clarsimp simp: image_iff)
   apply (case_tac "get_pte m x3 va"; clarsimp simp: image_iff )
   apply (case_tac a; clarsimp simp: image_iff)
  by (rule_tac x = "addr_val va" in bexI; clarsimp)+



lemma lookup_refill:
  "pt_walk asid m ttbr va \<noteq> None \<and> lookup tlb asid va = Miss \<Longrightarrow>
   lookup (insert (the(pt_walk asid m ttbr va)) tlb) asid va = Hit (the(pt_walk asid m ttbr va))"
   by (clarsimp simp: lookup_def entry_set_insert [where e="the (pt_walk asid m ttbr va)"] split: if_split_asm)


lemma consistent_insert [simp, intro!]:
  "pt_walk asid m ttbr va \<noteq> None \<and> lookup tlb asid va = Miss \<Longrightarrow>
  consistent0 m asid ttbr (insert (the(pt_walk asid m ttbr va)) tlb) va"
  by (simp add: consistent0_def lookup_refill is_fault_def)



(******************************)


lemma lookup_incon_subset [simp]:
  "\<lbrakk> s \<subseteq> t ; lookup s a va = Incon \<rbrakk> \<Longrightarrow> 
       lookup t a va = Incon"
  by (metis less_eq_lookup_type lookup_type.simps(3) tlb_mono)

lemma  pt_walk_some_asid_entry [simp, intro!]:
  "pt_walk (ASID s) (MEM s) (TTBR0 s) va = Some a \<Longrightarrow> 
    asid_entry (the (pt_walk (ASID s) (MEM s) (TTBR0 s) va)) = ASID s"
  by (clarsimp simp: pt_walk_def split: option.splits pde.splits pte.splits)





lemma  lookup_saturated_miss_is_fault:
  "lookup (tlb_sat_set s \<union>  
        the ` {e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e}) (ASID s) va = Miss \<Longrightarrow>
     pt_walk (ASID s) (MEM s) (TTBR0 s) va = None  "
  apply (clarsimp simp: lookup_def entry_set_def entry_range_asid_tags_def is_fault_def split: if_split_asm)
  apply (erule_tac x = "the (pt_walk (ASID s) (MEM s) (TTBR0 s) va)" in allE)
  apply (erule disjE)
   apply force
  apply (cases "pt_walk (ASID s) (MEM s) (TTBR0 s) va ", simp)  
  apply (drule pt_walk_some_asid_entry)
  by force
 

lemma 
  "\<lbrakk>lookup (t1 \<union> t2) a va = Hit x ; t2 \<subseteq> t1 \<rbrakk>  \<Longrightarrow>  entry_set t1 a va = {x} "
  apply (clarsimp simp: lookup_def split:if_split_asm)
  apply (clarsimp simp: entry_set_def)
  by auto 



lemma
  "\<lbrakk>consistent (typ_sat_tlb s) va ;  lookup (tlb_sat_set s) (ASID s) va = Hit x3 \<rbrakk> \<Longrightarrow> 
     x3 = the (pt_walk (ASID s) (MEM s) (TTBR0 s) va)"
  apply (clarsimp simp: consistent0_def )
done




(* IMPORTANT *)


lemma write'mem1_eq_TLB:
  "\<lbrakk> write'mem1 (val, va, sz) s = ((), s') \<rbrakk>  \<Longrightarrow> state.more s' = state.more s"
   by (clarsimp simp: write'mem1_def raise'exception_def split: if_split_asm)


lemma write_same_mem:
  "\<lbrakk> write'mem1 (val, va, sz) s = ((), s') ; write'mem1 (val, va, sz) t = ((), t') ;
      MEM s = MEM t\<rbrakk>  \<Longrightarrow>  MEM s' = MEM t'"
  by (clarsimp simp: write'mem1_def raise'exception_def split:if_split_asm)

lemma write_same_mem_excep:
  "\<lbrakk> write'mem1 (val, pa, sz) s = ((), s') ; write'mem1 (val, pa, sz) t = ((), t') ;
      MEM s = MEM t ; exception s = exception t \<rbrakk>  \<Longrightarrow> exception s' = exception t'"
   apply (clarsimp simp: write'mem1_def raise'exception_def split:if_split_asm)
done

 

lemma write'mem1_rel:
  "\<lbrakk> write'mem1 (val, va, sz) s = ((), s') \<rbrakk>  \<Longrightarrow> s' = s \<lparr> MEM:= MEM s' , exception:= exception s' \<rparr>"
   by (clarsimp simp: write'mem1_def raise'exception_def split: if_split_asm)


lemma sat_state_tlb':
  "\<lbrakk> saturated s \<rbrakk> \<Longrightarrow> 
     state.more s = state.more s \<union> the ` {e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e}"
  by (fastforce simp: saturated_def)


lemma tlb_rel'_absD:
  "tlb_rel_abs' s t \<Longrightarrow>
     ASID t = ASID s \<and> MEM t = MEM s \<and> TTBR0 t = TTBR0 s \<and>  saturated s \<and> 
                asid_va_incon_tlb_mem s  \<subseteq> incon_set (state.more t) \<and> exception t = exception s"
  by (clarsimp simp: tlb_rel_abs'_def state.defs)


lemma refine_relD:
  "refine_rel s t \<Longrightarrow>
     ASID t = ASID s \<and> MEM t = MEM s \<and> TTBR0 t = TTBR0 s  \<and> exception t = exception s"
  apply (clarsimp simp: refine_rel_def)
  by (clarsimp simp:  state.defs)

lemma invar_relD:
  "invar_rel s t \<Longrightarrow>
     ASID t = ASID s \<and> MEM t = MEM s \<and> TTBR0 t = TTBR0 s   \<and>  saturated s \<and> 
                asid_va_incon_tlb_mem_n s  \<subseteq> iset (state.more t) \<and> exception t = exception s"
  apply (clarsimp simp: invar_rel_def)
  by (clarsimp simp:  state.defs)

end