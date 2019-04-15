theory MMU_Instants_TLB
imports
  TLBJ.Simp_Lemmas
  TLBJ.ARM_Monadic
                            
begin

record non_det_tlb_state = state + 
           non_det_tlb :: "unit tlb"

record det_tlb_state = state + 
           det_tlb :: "unit tlb"

record sat_tlb_state = state + 
           sat_tlb :: "unit tlb"

record set_tlb_state = state + 
           set_tlb :: "vaddr set"


definition 
  typ_non_det_tlb :: "'a non_det_tlb_state_scheme \<Rightarrow> unit tlb state_scheme"
where
  "typ_non_det_tlb s =  state.extend (state.truncate s) (non_det_tlb s)"

definition 
  typ_det_tlb :: "'a det_tlb_state_scheme \<Rightarrow> unit tlb state_scheme"
where
  "typ_det_tlb s =  state.extend (state.truncate s) (det_tlb s)"

definition 
  typ_sat_tlb :: "'a sat_tlb_state_scheme \<Rightarrow> unit tlb state_scheme"
where
  "typ_sat_tlb s =  state.extend (state.truncate s) (sat_tlb s)"

definition 
  typ_set_tlb :: "'a set_tlb_state_scheme \<Rightarrow> vaddr set state_scheme"
where
  "typ_set_tlb s =  state.extend (state.truncate s) (set_tlb s)"


lemma non_det_tlb_more [simp]:
  "state.more (typ_non_det_tlb s) = non_det_tlb s"
  by (clarsimp simp: typ_non_det_tlb_def state.defs)


lemma det_tlb_more [simp]:
  "state.more (typ_det_tlb s) = det_tlb s"
  by (clarsimp simp: typ_det_tlb_def state.defs)


lemma sat_tlb_more [simp]:
  "state.more (typ_sat_tlb s) = sat_tlb s"
  by (clarsimp simp: typ_sat_tlb_def state.defs)


lemma set_tlb_more [simp]:
  "state.more (typ_set_tlb s) = set_tlb s"
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
  "TTBR0 (typ_non_det_tlb s) =  TTBR0 s \<and> MEM (typ_non_det_tlb s) = MEM s \<and> exception (typ_non_det_tlb s) = exception s"
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
  "consistent (s:: unit tlb_entry set state_scheme) \<equiv>
               consistent0  (lookup' (state.more s)) (pt_walk () (MEM s) (TTBR0 s))"


definition
  saturated :: "unit tlb_entry set state_scheme \<Rightarrow> bool"
where
  "saturated s  \<equiv> the ` {e\<in>pt_walk () (MEM s) (TTBR0 s) ` UNIV. \<not>is_fault e} \<subseteq> state.more s"


definition 
  tlb_rel_det :: "unit tlb_entry set state_scheme \<Rightarrow> unit tlb_entry set state_scheme \<Rightarrow> bool"
where                                                                
  "tlb_rel_det s t \<equiv> state.truncate s = state.truncate t \<and>  state.more s \<subseteq> state.more t"

definition 
  tlb_rel_sat :: "unit tlb_entry set state_scheme \<Rightarrow> unit tlb_entry set state_scheme \<Rightarrow> bool"
where                                                                
  "tlb_rel_sat s t \<equiv> state.truncate s = state.truncate t \<and>  state.more s \<subseteq> state.more t  \<and>  saturated t"


definition 
   inconsistent_vaddrs :: "unit tlb_entry set state_scheme \<Rightarrow>  vaddr set"
where                                                        
  "inconsistent_vaddrs s  \<equiv>  {va. lookup' (state.more s) va = Incon}"



definition                              
   incoherrent_vaddrs :: "unit tlb_entry set state_scheme \<Rightarrow>  vaddr set"
where                                                         
  "incoherrent_vaddrs s  \<equiv> {va. \<exists>x. lookup' (state.more s) va = Hit x \<and> is_fault (pt_walk () (MEM s) (TTBR0 s) va)} "


definition                              
   incon_addrs :: "unit tlb_entry set state_scheme \<Rightarrow>  vaddr set"
where                                                         
  "incon_addrs s  \<equiv>  inconsistent_vaddrs s \<union> incoherrent_vaddrs s"


definition 
  tlb_rel_abs :: "unit tlb_entry set state_scheme  \<Rightarrow> vaddr set state_scheme \<Rightarrow> bool"
where                                                                
"tlb_rel_abs s t \<equiv>  state.truncate s = state.truncate t \<and> incon_addrs s \<subseteq> state.more t \<and> saturated s" 


declare return_def [simp add]
declare bind_def [simp add]
declare read_state_def [simp add]
declare update_state_def [simp add]
declare extend_state_def [simp add]
declare trim_state_def [simp add]

lemma tlb_rel_detD:
  "tlb_rel_det s t \<Longrightarrow>  MEM t = MEM s \<and> TTBR0 t = TTBR0 s \<and> state.more s \<subseteq> state.more t  \<and>  exception t = exception s"
  by (clarsimp simp: tlb_rel_det_def state.defs)

lemma tlb_rel_satD:
  "tlb_rel_sat s t \<Longrightarrow> MEM t = MEM s \<and> TTBR0 t = TTBR0 s \<and> state.more s \<subseteq> state.more t \<and> exception t = exception s  \<and> saturated t"
  by (clarsimp simp: tlb_rel_sat_def state.defs)

lemma tlb_rel_det_consistent:
  "\<lbrakk> tlb_rel_det s t; consistent t va \<rbrakk> \<Longrightarrow> consistent s va"
   by (insert tlb_rel_detD [of s t] , clarsimp ,drule tlb_mono [of _ _ "va"] ,auto simp: consistent0_def less_eq_lookup_type)


lemma tlb_rel_sat_consistent:
  "\<lbrakk> tlb_rel_sat s t; consistent t va \<rbrakk> \<Longrightarrow> consistent s va"
   by (insert tlb_rel_satD [of s t] , clarsimp ,drule tlb_mono [of _ _ "va"] ,auto simp: consistent0_def less_eq_lookup_type)

lemma sat_state_tlb:
  "saturated s  \<Longrightarrow> state.more s = state.more s \<union> the ` {e \<in> range (pt_walk () (MEM s) (TTBR0 s)). \<not> is_fault e}"
  by (fastforce simp: saturated_def)


lemma saturated_tlb_pde:
  "saturated (typ_sat_tlb s) \<Longrightarrow> (sat_tlb s) = sat_tlb s \<union> the ` {e\<in>pt_walk ()  (MEM s) (TTBR0 s) ` UNIV. \<not>is_fault e}"
 apply (clarsimp simp:  saturated_def fst_def) apply (cases s ; clarsimp)  by blast


lemma sat_miss_fault:
  "\<lbrakk> saturated (typ_sat_tlb s); lookup' (sat_tlb s)   va = Miss \<rbrakk> \<Longrightarrow> 
           is_fault (pt_walk () (MEM s) (TTBR0 s) va)"
  apply (subgoal_tac " lookup' ((sat_tlb s)  \<union> the ` {e \<in> range (pt_walk ()   (MEM s) (TTBR0 s)). \<not> is_fault e})   va = Miss")
   apply (thin_tac "lookup' ((sat_tlb s))   va = Miss")
   apply (drule lookup_miss_union)
   apply clarsimp
   apply (drule lookup_miss_is_fault)
   apply clarsimp
  using  sat_state_tlb by force


lemma saturatd_lookup_hit_no_fault:
  "\<lbrakk>saturated (typ_sat_tlb s); 
    lookup' (sat_tlb s)   b = Hit x; \<not> is_fault (pt_walk ()  (MEM s) (TTBR0 s) b)\<rbrakk> \<Longrightarrow>
                       x = the (pt_walk ()   (MEM s) (TTBR0 s) b)"
  apply (subgoal_tac "lookup'(sat_tlb s \<union> 
                              the ` {e \<in> range (pt_walk ()   (MEM s) (TTBR0 s)). \<not> is_fault e})   (  b) = Hit x")
   prefer 2
   apply (drule sat_state_tlb, clarsimp simp: state.defs)
  apply (drule lookup_hit_miss_or_hit')
  apply (erule disjE)
   apply (clarsimp simp: lookup_range_pt_walk_hit)
  apply (frule lookup_range_fault_pt_walk)
  apply (drule_tac x = b in bspec; clarsimp simp: lookup_hit_entry_range)
  done

lemma saturated_tlb:
  "saturated (typ_sat_tlb s) \<Longrightarrow> sat_tlb s = sat_tlb s \<union> the ` {e\<in>pt_walk ()   (MEM s) (TTBR0 s) ` UNIV. \<not>is_fault e} "
 apply (clarsimp simp:  saturated_def fst_def) apply (cases s ; clarsimp)  by blast


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
  using not_miss_incon_hit saturatd_lookup_hit_no_fault by blast
  

lemma tlb_rel_abs_consistent [simp]:
  "\<lbrakk>va \<notin> set_tlb t ;   tlb_rel_abs  (typ_sat_tlb s) (typ_set_tlb t)  \<rbrakk>  \<Longrightarrow> 
           consistent (typ_sat_tlb s) va " 
  apply (rule not_member_incon_consistent ; clarsimp simp: tlb_rel_abs_def) 
  by blast


lemma tlb_rel_absD:
  "tlb_rel_abs s t \<Longrightarrow> MEM t = MEM s \<and> TTBR0 t = TTBR0 s  \<and>  saturated s \<and> 
                        incon_addrs s  \<subseteq> state.more t \<and> exception t = exception s"
  by (clarsimp simp: tlb_rel_abs_def state.defs)


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



consts tlb_evict :: "'a state_scheme \<Rightarrow> 'a"


instantiation non_det_tlb_state_ext :: (type) mmu       
begin
  definition                          
  "(mmu_translate va :: ('a non_det_tlb_state_scheme \<Rightarrow> _))
 = do {
     update_state (\<lambda>s. s\<lparr> non_det_tlb := non_det_tlb s - tlb_evict (typ_non_det_tlb s) \<rparr>);
     mem   <- read_state MEM;
     ttbr0 <- read_state TTBR0;
     tlb   <- read_state non_det_tlb;
          case lookup' tlb va of 
               Hit entry \<Rightarrow> return (va_to_pa va entry)
          |    Miss \<Rightarrow> 
                   do { 
                       let entry = pt_walk () mem ttbr0 va;
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
  "(flush f :: ('a non_det_tlb_state_scheme \<Rightarrow> _))  \<equiv> 
           case f of FlushTLB \<Rightarrow> update_state (\<lambda>s. s\<lparr> non_det_tlb := {} \<rparr>)
                  | Flushvarange vset \<Rightarrow> do {
                                         update_state (\<lambda>s. s\<lparr> non_det_tlb := flush_tlb_vset (non_det_tlb s) vset \<rparr>)}"
 
  instance ..
end

               
instantiation det_tlb_state_ext :: (_) mmu       
begin
  definition                          
  "(mmu_translate va :: ('a det_tlb_state_scheme \<Rightarrow> _))
 = do {
     mem   <- read_state MEM;
     ttbr0 <- read_state TTBR0;
     tlb   <- read_state det_tlb;
          case lookup' tlb va of 
               Hit entry \<Rightarrow> return (va_to_pa va entry)
          |    Miss \<Rightarrow> 
                   do { 
                       let entry = pt_walk () mem ttbr0 va;
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
  "(flush f :: ('a det_tlb_state_scheme \<Rightarrow> _))  \<equiv> 
           case f of FlushTLB \<Rightarrow> update_state (\<lambda>s. s\<lparr> det_tlb := {} \<rparr>)
                  | Flushvarange vset \<Rightarrow> do {
                                         update_state (\<lambda>s. s\<lparr> det_tlb := flush_tlb_vset (det_tlb s) vset \<rparr>)}"
 
  instance ..
end



instantiation sat_tlb_state_ext :: (_) mmu       
begin
  definition                          
  "(mmu_translate va :: ('a sat_tlb_state_scheme \<Rightarrow> _))
 = do {
     mem   <- read_state MEM;
     ttbr0 <- read_state TTBR0;
     let tlb_new = the ` {e\<in>pt_walk () mem ttbr0 ` UNIV. \<not>is_fault e};
     tlb   <- read_state sat_tlb;
     let sat_tlb' = tlb \<union> tlb_new;
     update_state (\<lambda>s. s\<lparr> sat_tlb := sat_tlb' \<rparr>);
          case lookup' sat_tlb' va of 
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
      pa <- mmu_translate va :: ('a sat_tlb_state_scheme \<Rightarrow> _);
      tlb   <- read_state sat_tlb;
      exception <- read_state exception;
      if exception = NoException 
       then  do {
                 write'mem1 (value, pa, size);
                 mem'  <- read_state MEM;
                 let tlb_new = the ` {e\<in>pt_walk () mem' ttbr0 ` UNIV. \<not>is_fault e};
                 update_state (\<lambda>s. s\<lparr> sat_tlb := tlb \<union> tlb_new \<rparr>) }
       else return ()
  }"
(* print_context *)                      


definition
  "(update_TTBR0 r :: ('a sat_tlb_state_scheme \<Rightarrow> _))  = 
do {
      update_state (\<lambda>s. s\<lparr> TTBR0 := r \<rparr>);
      mem   <- read_state MEM;
      let all_entries = the ` {e\<in>pt_walk () mem r ` UNIV. \<not>is_fault e};
      tlb   <- read_state sat_tlb;
      update_state (\<lambda>s. s\<lparr> sat_tlb := tlb \<union> all_entries \<rparr>)}"

definition   
  "(flush f :: ('a sat_tlb_state_scheme \<Rightarrow> _))  \<equiv> 
           case f of FlushTLB \<Rightarrow> do {update_state (\<lambda>s. s\<lparr> sat_tlb := {} \<rparr>);
                                     mem   <- read_state MEM;
                                     ttbr0 <- read_state TTBR0;
                                     let tlb_new = the ` {e\<in>pt_walk () mem ttbr0 ` UNIV. \<not>is_fault e};
                                     update_state (\<lambda>s. s\<lparr> sat_tlb := tlb_new \<rparr>)}
                  | Flushvarange vset \<Rightarrow>  do {
                                     mem   <- read_state MEM;
                                     ttbr0 <- read_state TTBR0;
                                     let tlb_new = the ` {e\<in>pt_walk () mem ttbr0 ` UNIV. \<not>is_fault e};
                                     tlb_pde     <- read_state sat_tlb;
                                     update_state (\<lambda>s. s\<lparr> sat_tlb := flush_tlb_vset tlb_pde vset \<union> tlb_new \<rparr>)}"

  instance ..
end

(*definition
  ptable_comp :: "(vaddr \<Rightarrow> pt_walk_typ) \<Rightarrow> (vaddr \<Rightarrow> pt_walk_typ) \<Rightarrow> vaddr set"
where
  "ptable_comp walk walk'  \<equiv> {va. \<not>(walk va \<preceq> walk' va)}"
*)

definition
  ptable_comp :: "(vaddr \<Rightarrow> unit tlb_entry option) \<Rightarrow> (vaddr \<Rightarrow> unit tlb_entry option) \<Rightarrow> vaddr set"
where
  "ptable_comp wlk wlk'  \<equiv> {va. \<not> is_fault (wlk va) \<and> \<not> is_fault (wlk' va) \<and> wlk va \<noteq> wlk' va \<or> 
                                 \<not> is_fault (wlk va) \<and> is_fault (wlk' va)}"


definition
  incon_comp :: " heap \<Rightarrow> heap \<Rightarrow> paddr \<Rightarrow> paddr \<Rightarrow> vaddr set"
where
  "incon_comp  hp hp' rt rt' \<equiv> ptable_comp (pt_walk () hp rt) (pt_walk () hp' rt')"


instantiation set_tlb_state_ext :: (_) mmu       
begin
  definition                          
  "(mmu_translate va :: ('a set_tlb_state_scheme \<Rightarrow> _))
 = do {
     mem   <- read_state MEM;
     ttbr0 <- read_state TTBR0;
     incon_vaddrs <- read_state set_tlb;
     if  va \<in> incon_vaddrs
       then raise'exception (IMPLEMENTATION_DEFINED ''set on fire'')
       else let entry = pt_walk () mem ttbr0 va in 
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
      paddr <- mmu_translate va :: ('a set_tlb_state_scheme \<Rightarrow> _);
      incon_vaddrs <- read_state set_tlb; 
      exception <- read_state exception;
      if exception = NoException 
        then  do {
                   write'mem1 (value, paddr, size);
                   mem' <- read_state MEM; 
                   let ptable_comp = incon_comp mem mem' ttbr0 ttbr0;
                   let incon_vaddrs_new    = incon_vaddrs \<union>  ptable_comp;
                   update_state (\<lambda>s. s\<lparr> set_tlb :=  incon_vaddrs_new \<rparr>)
            }
        else return ()
   }"
                     

definition
  "(update_TTBR0 r :: ('a set_tlb_state_scheme \<Rightarrow> _))  = 
do {
      ttbr0   <- read_state TTBR0;
      update_state (\<lambda>s. s\<lparr> TTBR0 := r \<rparr>);
      incon_vaddrs   <- read_state set_tlb;
      mem    <- read_state MEM;
       let ptable_comp = incon_comp mem mem ttbr0 r; 
       let incon_vaddrs_new = incon_vaddrs \<union>  ptable_comp;
      update_state (\<lambda>s. s\<lparr> set_tlb := incon_vaddrs_new \<rparr>)
}"


definition   
  "(flush f :: ('a set_tlb_state_scheme \<Rightarrow> _))  \<equiv> 
           case f of FlushTLB \<Rightarrow> update_state (\<lambda>s. s\<lparr> set_tlb := {} \<rparr>)
                  | Flushvarange vset \<Rightarrow> do {
                       incon_vaddrs   <- read_state set_tlb;
                        update_state (\<lambda>s. s\<lparr> set_tlb := incon_vaddrs -vset\<rparr>)}"

  instance ..
end

end
