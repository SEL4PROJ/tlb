theory  ARMv7_Flush_Ref

imports 
   ARMv7_Update_ASID_Ref

begin               


(* flushing complete TLB *)

class Flush_TLB =
  fixes Flush_TLB :: "'a state_scheme \<Rightarrow>  unit \<times> 'a state_scheme" 


instantiation tlb_state_ext :: (type) Flush_TLB   
begin
  definition   
  "(Flush_TLB :: ('a tlb_state_scheme \<Rightarrow> _))  = update_state (\<lambda>s. s\<lparr> tlb_set := {} \<rparr>)"
  instance ..
end


instantiation tlb_det_state_ext :: (type) Flush_TLB  
begin
  definition   
  "(Flush_TLB  :: ('a tlb_det_state_scheme \<Rightarrow> _))  = update_state (\<lambda>s. s\<lparr> tlb_det_set := {} \<rparr>)"
 print_context                    
  instance ..
end


instantiation tlb_sat_no_flt_state_ext :: (type) Flush_TLB  
begin
  definition   
  "(Flush_TLB :: ('a tlb_sat_no_flt_state_scheme \<Rightarrow> _))  = do {
       update_state (\<lambda>s. s\<lparr> tlb_sat_no_flt_set := {} \<rparr>);
      mem   <- read_state MEM;
      ttbr0 <- read_state TTBR0;
      asid <- read_state ASID;
      let all_non_fault_entries = {e\<in>pt_walk asid mem ttbr0 ` UNIV. \<not>is_fault e};
      update_state (\<lambda>s. s\<lparr> tlb_sat_no_flt_set := all_non_fault_entries \<rparr>)} "
  instance ..
end



instantiation tlb_incon_state'_ext :: (type) Flush_TLB   
begin
  definition   
  "(Flush_TLB  :: ('a tlb_incon_state'_scheme \<Rightarrow> _))  = do {
      iset   <- read_state tlb_incon_set';
      let iset = iset \<lparr>incon_set := {} , tlb_snapshot := \<lambda> a v . Miss \<rparr>;
      update_state (\<lambda>s. s\<lparr> tlb_incon_set' := iset \<rparr>)
} "                
  instance ..
end

lemma flush_tlb_non_det_det_refine:
  "\<lbrakk> Flush_TLB (s::tlb_state) = ((), s') ;   Flush_TLB (t::tlb_det_state) = ((), t'); 
         tlb_rel (typ_tlb s) (typ_det_tlb t) \<rbrakk> \<Longrightarrow>  tlb_rel (typ_tlb s') (typ_det_tlb t') "
  apply (clarsimp simp:  Flush_TLB_tlb_state_ext_def  Flush_TLB_tlb_det_state_ext_def tlb_rel_def  no_faults_def) 
  by (cases s, cases t , clarsimp simp: state.defs tlb_rel_def) 


lemma  flush_tlb_det_sat_no_flt_refine:
  "\<lbrakk> Flush_TLB (s::tlb_det_state) = ((), s') ;  Flush_TLB(t::tlb_sat_no_flt_state) = ((), t'); 
         tlb_rel_sat_no_flt (typ_det_tlb s) (typ_sat_no_flt_tlb t) \<rbrakk> \<Longrightarrow> 
                  tlb_rel_sat_no_flt (typ_det_tlb s') (typ_sat_no_flt_tlb t')"
  apply (clarsimp simp: Flush_TLB_tlb_det_state_ext_def Flush_TLB_tlb_sat_no_flt_state_ext_def)
  apply (clarsimp simp: tlb_rel_sat_no_flt_def saturated_no_flt_def no_faults_def)
  apply (cases s, cases t , clarsimp simp: state.defs)
  done


lemma flush_tlb_sat_no_flt_abs_refine':
  "\<lbrakk>Flush_TLB (s::tlb_sat_no_flt_state) = ((), s') ;  Flush_TLB (t::tlb_incon_state') = ((), t'); 
             tlb_rel_abs' (typ_sat_no_flt_tlb s) (typ_incon' t) \<rbrakk> \<Longrightarrow> 
                     tlb_rel_abs' (typ_sat_no_flt_tlb s') (typ_incon' t')"
  apply (clarsimp simp: Flush_TLB_tlb_sat_no_flt_state_ext_def
                        Flush_TLB_tlb_incon_state'_ext_def tlb_rel_abs'_def)
  apply (rule conjI)
   apply (cases s, cases t, clarsimp simp: state.defs)
  apply (rule conjI)
   apply (clarsimp simp: asid_va_incon_tlb_mem_def)
   apply (rule conjI)
    apply (clarsimp simp: asid_va_incon_def lookup_no_flt_range_pt_walk_not_incon')
   apply (clarsimp simp: asid_va_hit_incon_def)
   apply (frule lookup_range_fault_pt_walk)
   apply (drule_tac x = "addr_val b" in bspec)
    apply (clarsimp simp: lookup_hit_entry_range)
   apply clarsimp
  apply (rule conjI)
   apply (clarsimp simp: saturated_no_flt_def)
  apply (rule conjI)
   apply (clarsimp simp: no_faults_def)
  apply (clarsimp simp: snapshot_of_tlb_def asid_unequal_miss'')
  done




class Flush_ASID =
  fixes Flush_ASID :: "asid \<Rightarrow> 'a state_scheme \<Rightarrow>  unit \<times> 'a state_scheme" 


instantiation tlb_state_ext :: (type) Flush_ASID   
begin
  definition   
  "(Flush_ASID a :: ('a tlb_state_scheme \<Rightarrow> _))  = do {
      tlb   <- read_state tlb_set;
      update_state (\<lambda>s. s\<lparr> tlb_set := tlb - {e\<in>tlb. asid_entry e = a} - tlb_evict (typ_tlb s) \<rparr>)}"
  instance ..
end


instantiation tlb_det_state_ext :: (type) Flush_ASID  
begin
  definition   
  "(Flush_ASID a :: ('a tlb_det_state_scheme \<Rightarrow> _))  = do {
      tlb   <- read_state tlb_det_set;
      update_state (\<lambda>s. s\<lparr> tlb_det_set := tlb - {e\<in>tlb. asid_entry e = a} \<rparr>)}"
 print_context                    
  instance ..
end


instantiation tlb_sat_no_flt_state_ext :: (type) Flush_ASID  
begin
  definition   
  "(Flush_ASID a :: ('a tlb_sat_no_flt_state_scheme \<Rightarrow> _))  = do {
      tlb   <- read_state tlb_sat_no_flt_set;
      mem   <- read_state MEM;
      ttbr0 <- read_state TTBR0;
      asid <- read_state ASID;
      let all_non_fault_entries = {e\<in>pt_walk asid mem ttbr0 ` UNIV. \<not>is_fault e};
      update_state (\<lambda>s. s\<lparr> tlb_sat_no_flt_set := (tlb - {e\<in>tlb. asid_entry e = a}) \<union> 
                                                       all_non_fault_entries \<rparr>)} "
  instance ..
end



instantiation tlb_incon_state'_ext :: (type) Flush_ASID   
begin
  definition   
  "(Flush_ASID  a :: ('a tlb_incon_state'_scheme \<Rightarrow> _))  = do {
      iset   <- read_state tlb_incon_set';
      let iset = iset \<lparr>incon_set := incon_set(iset) - {a} \<times> UNIV, 
                       tlb_snapshot := (tlb_snapshot iset)(a := \<lambda>v. Miss) \<rparr>;
      update_state (\<lambda>s. s\<lparr> tlb_incon_set' := iset\<rparr>)
} "
                  
  instance ..
end

lemma flush_asid_non_det_det_refine:
  "\<lbrakk> Flush_ASID a (s::tlb_state) = ((), s') ; Flush_ASID a (t::tlb_det_state) = ((), t'); 
         tlb_rel (typ_tlb s) (typ_det_tlb t) \<rbrakk> \<Longrightarrow>  tlb_rel (typ_tlb s') (typ_det_tlb t') "
  apply (clarsimp simp:  Flush_ASID_tlb_state_ext_def  Flush_ASID_tlb_det_state_ext_def 
          tlb_rel_def  no_faults_def) 
  apply (cases s, cases t , clarsimp simp: state.defs tlb_rel_def) 
  by blast

lemma  flush_asid_det_sat_no_flt_refine:
  "\<lbrakk> Flush_ASID a (s::tlb_det_state) = ((), s') ;  Flush_ASID a (t::tlb_sat_no_flt_state) = ((), t'); 
         tlb_rel_sat_no_flt (typ_det_tlb s) (typ_sat_no_flt_tlb t) \<rbrakk> \<Longrightarrow> 
                  tlb_rel_sat_no_flt (typ_det_tlb s') (typ_sat_no_flt_tlb t')"
  apply (clarsimp simp: Flush_ASID_tlb_det_state_ext_def Flush_ASID_tlb_sat_no_flt_state_ext_def)
  apply (clarsimp simp: tlb_rel_sat_no_flt_def saturated_no_flt_def no_faults_def)
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


lemma  asid_entry_set_pt_walk_is_fault:
  "asid_entry ` {e \<in> range (pt_walk a m rt). \<not> is_fault e} = {a} \<or> 
   asid_entry ` {e \<in> range (pt_walk a m rt). \<not> is_fault e} = {}"
  by(case_tac "{e \<in> range (pt_walk a m rt). \<not> is_fault e} \<noteq> {}", rule disjI1, force, rule disjI2, force)

  
 
lemma  lookup_minus_hit_asid_hit:
  "\<lbrakk>lookup (tlb_sat_no_flt_set s - {e \<in> tlb_sat_no_flt_set s. asid_entry e = a}) a' va = Hit x; a \<noteq> a'\<rbrakk> \<Longrightarrow> 
                         lookup (tlb_sat_no_flt_set s) a' va = Hit x"
  apply (clarsimp simp: lookup_def entry_set_def entry_range_asid_tags_def split: if_split_asm)
  apply safe
  by auto


lemma lookup_tlb_minus_asid_miss:
  "lookup (tlb - {e \<in> tlb. asid_entry e = a}) a va = Miss"
  apply (clarsimp simp: lookup_def entry_set_def entry_range_asid_tags_def split: if_split_asm)
  by auto


lemma diff_asid_lookup_union:
  "\<lbrakk> a' \<noteq> a; a' \<noteq> a'';
       asid_entry ` {e \<in> range (pt_walk a'' m r). \<not> is_fault e} = {a''}  \<or>
            asid_entry ` {e \<in> range (pt_walk a'' m r). \<not> is_fault e} = {}\<rbrakk>  \<Longrightarrow> 
                 lookup (tlb_sat_no_flt_set s - {e \<in> tlb_sat_no_flt_set s. asid_entry e = a} \<union>
                        {e \<in> range (pt_walk a'' m r). \<not> is_fault e}) a' va =
                                lookup (tlb_sat_no_flt_set s) a' va"
  apply (erule disjE)
   apply (cases "lookup (tlb_sat_no_flt_set s - {e \<in> tlb_sat_no_flt_set s. asid_entry e = a} \<union>
                {e \<in> range (pt_walk a'' m r). \<not> is_fault e})a' va" ; 
      (clarsimp simp: lookup_def entry_set_def entry_range_asid_tags_def split: if_split_asm , fastforce))
  by (cases "lookup (tlb_sat_no_flt_set s - {e \<in> tlb_sat_no_flt_set s. asid_entry e = a} \<union>
                {e \<in> range (pt_walk a'' m r). \<not> is_fault e})  a' va"; 
      (clarsimp simp: lookup_def entry_set_def entry_range_asid_tags_def split: if_split_asm , fastforce))

   
lemma flush_asid_sat_no_flt_abs_refine':
  "\<lbrakk>Flush_ASID a (s::tlb_sat_no_flt_state) = ((), s') ;  Flush_ASID a (t::tlb_incon_state') = ((), t'); 
             tlb_rel_abs' (typ_sat_no_flt_tlb s) (typ_incon' t) \<rbrakk> \<Longrightarrow> tlb_rel_abs' (typ_sat_no_flt_tlb s') (typ_incon' t')"
  apply (clarsimp simp: Flush_ASID_tlb_sat_no_flt_state_ext_def Flush_ASID_tlb_incon_state'_ext_def tlb_rel_abs'_def)
  apply (rule conjI)
   apply (cases s, cases t, clarsimp simp: state.defs)
  apply (subgoal_tac "tlb_sat_no_flt_set s = tlb_sat_no_flt_set s \<union> 
                              {e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e}")
   prefer 2
   apply (drule sat_state_tlb', clarsimp simp: state.defs)
  apply (rule conjI)
   apply (clarsimp simp: asid_va_incon_tlb_mem_def)
   apply (rule conjI)
    apply (clarsimp simp: asid_va_incon_def)
    apply (case_tac "a \<noteq> ASID s")
     apply (subgoal_tac "{e \<in> tlb_sat_no_flt_set s. asid_entry e = a} \<inter> {e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e} = {}")
      apply (subgoal_tac "tlb_sat_no_flt_set s - {e \<in> tlb_sat_no_flt_set s. asid_entry e = a} \<union> {e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e} = 
            tlb_sat_no_flt_set s - {e \<in> tlb_sat_no_flt_set s. asid_entry e = a}")
       prefer 2
       apply blast
      apply clarsimp
      apply (rule conjI)
       apply (drule lookup_incon_minus)
       apply blast
      apply (drule lookup_asid_incon_diff, clarsimp)
     apply (subgoal_tac "asid_entry ` {e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e} = {ASID s} \<or>
        asid_entry ` {e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e} = {}")
      apply blast
     apply (simp only: asid_entry_set_pt_walk_is_fault)
    apply clarsimp
    apply (drule union_incon_cases1)
    apply (erule disjE)
     apply (clarsimp simp: lookup_no_flt_range_pt_walk_not_incon')
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
     apply (clarsimp simp: lookup_no_flt_range_pt_walk_not_incon')
    apply clarsimp
    apply (rule conjI)
     prefer 2
     apply (drule lookup_asid_incon_diff , clarsimp)
    apply (drule lookup_incon_minus)
    apply blast
   apply (clarsimp simp: asid_va_hit_incon_def)
   apply (case_tac "a \<noteq> ASID s")
    apply (subgoal_tac "{e \<in> tlb_sat_no_flt_set s. asid_entry e = a} \<inter> {e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e} = {}")
     apply (subgoal_tac "tlb_sat_no_flt_set s - {e \<in> tlb_sat_no_flt_set s. asid_entry e = a} \<union> {e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e} = 
            tlb_sat_no_flt_set s - {e \<in> tlb_sat_no_flt_set s. asid_entry e = a}")
      prefer 2
      apply blast
     apply clarsimp
     apply (subgoal_tac " lookup (tlb_sat_no_flt_set s) (ASID s) (addr_val b) = Hit x")
      apply blast
     apply (clarsimp simp: lookup_minus_hit_asid_hit)
    apply (subgoal_tac "asid_entry ` {e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e} = {ASID s} \<or>
        asid_entry ` {e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e} = {}")
     apply force
    apply (simp only: asid_entry_set_pt_walk_is_fault)
   apply clarsimp
   apply (drule lookup_hit_union_cases')
   apply (erule disjE)
    apply (clarsimp simp: lookup_tlb_minus_asid_miss)
   apply (erule disjE)
    apply clarsimp
    apply (frule lookup_range_fault_pt_walk)
    apply (drule_tac x = "addr_val b" in bspec)
     apply (clarsimp simp:lookup_hit_entry_range)
    apply (clarsimp)
   apply (clarsimp simp: lookup_tlb_minus_asid_miss)
  apply (rule conjI)
   apply (clarsimp simp: saturated_no_flt_def)
  apply (rule conjI)
   apply (clarsimp simp:  no_faults_def)
  apply (rule conjI)
   apply clarsimp
   apply (rule conjI)
    apply (clarsimp simp:snapshot_of_tlb_def )
    apply (subgoal_tac "asid_entry ` {e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e} = {ASID s} \<or>
        asid_entry ` {e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e} = {}")
     prefer 2
     apply (simp only: asid_entry_set_pt_walk_is_fault)
    apply (clarsimp simp: lookup_def entry_set_def entry_range_asid_tags_def split: if_split_asm)
    apply force
   apply (clarsimp simp: snapshot_of_tlb_def)
   apply (subgoal_tac "lookup (tlb_sat_no_flt_set s - {e \<in> tlb_sat_no_flt_set s. asid_entry e = a} \<union> {e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e}) aa (addr_val v) =
    lookup (tlb_sat_no_flt_set s) aa (addr_val v)")
    apply clarsimp
   apply (subgoal_tac "asid_entry ` {e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e} = {ASID s} \<or>
        asid_entry ` {e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e} = {}")
    prefer 2
    apply (simp only: asid_entry_set_pt_walk_is_fault)
   apply (clarsimp simp: diff_asid_lookup_union)
  apply (clarsimp split: if_split_asm)
  apply blast 
  done




class Flush_varange =
  fixes Flush_varange :: "vaddr set \<Rightarrow> 'a state_scheme \<Rightarrow>  unit \<times> 'a state_scheme" 


instantiation tlb_state_ext :: (type) Flush_varange  
begin
  definition   
  "(Flush_varange vset :: ('a tlb_state_scheme \<Rightarrow> _))  = do {
      tlb   <- read_state tlb_set;
      update_state (\<lambda>s. s\<lparr> tlb_set := tlb - \<Union>((\<lambda> v. {e\<in>tlb. addr_val v \<in> entry_range e}) ` vset) - 
                                             tlb_evict (typ_tlb s) \<rparr>)}"
  instance ..
end


instantiation tlb_det_state_ext :: (type) Flush_varange  
begin
  definition   
  "(Flush_varange vset :: ('a tlb_det_state_scheme \<Rightarrow> _))  = do {
      tlb   <- read_state tlb_det_set;
      update_state (\<lambda>s. s\<lparr> tlb_det_set := tlb - \<Union>((\<lambda> v. {e\<in>tlb. addr_val v \<in> entry_range e}) ` vset)\<rparr>)}"
 print_context                    
  instance ..
end


instantiation tlb_sat_no_flt_state_ext :: (type) Flush_varange 
begin
  definition   
  "(Flush_varange vset :: ('a tlb_sat_no_flt_state_scheme \<Rightarrow> _))  = do {
      tlb   <- read_state tlb_sat_no_flt_set;
      mem   <- read_state MEM;
      ttbr0 <- read_state TTBR0;
      asid <- read_state ASID;
      let all_non_fault_entries = {e\<in>pt_walk asid mem ttbr0 ` UNIV. \<not>is_fault e};
      update_state (\<lambda>s. s\<lparr> tlb_sat_no_flt_set := 
              (tlb - (\<Union>v\<in>vset. {e \<in> tlb. addr_val v \<in> entry_range e})) \<union> all_non_fault_entries \<rparr>)} "
  instance ..
end

instantiation tlb_incon_state'_ext :: (type) Flush_varange  
begin
  definition   
  "(Flush_varange  vset :: ('a tlb_incon_state'_scheme \<Rightarrow> _))  = do {
      iset   <- read_state tlb_incon_set';
      let iset = iset \<lparr>incon_set := incon_set(iset) - UNIV \<times> vset , 
                 tlb_snapshot := \<lambda>x y. if (x, y) \<in> UNIV \<times> vset then Miss else tlb_snapshot iset x y \<rparr>;
      update_state (\<lambda>s. s\<lparr> tlb_incon_set' := iset\<rparr>)
} "
                  
  instance ..
end

lemma flush_varange_non_det_det_refine:
  "\<lbrakk> Flush_varange vset (s::tlb_state) = ((), s') ; Flush_varange vset (t::tlb_det_state) = ((), t'); 
         tlb_rel (typ_tlb s) (typ_det_tlb t) \<rbrakk> \<Longrightarrow>  tlb_rel (typ_tlb s') (typ_det_tlb t') "
  apply (clarsimp simp:  Flush_varange_tlb_state_ext_def  Flush_varange_tlb_det_state_ext_def 
          tlb_rel_def  no_faults_def) 
  apply (cases s, cases t , clarsimp simp: state.defs tlb_rel_def) 
  by blast

lemma  flush_varange_det_sat_no_flt_refine:
  "\<lbrakk> Flush_varange vset (s::tlb_det_state) = ((), s') ;  Flush_varange vset (t::tlb_sat_no_flt_state) = ((), t'); 
         tlb_rel_sat_no_flt (typ_det_tlb s) (typ_sat_no_flt_tlb t) \<rbrakk> \<Longrightarrow> 
                  tlb_rel_sat_no_flt (typ_det_tlb s') (typ_sat_no_flt_tlb t')"
  apply (clarsimp simp: Flush_varange_tlb_det_state_ext_def Flush_varange_tlb_sat_no_flt_state_ext_def)
  apply (clarsimp simp: tlb_rel_sat_no_flt_def saturated_no_flt_def no_faults_def)
  apply (cases s, cases t , clarsimp simp: state.defs)
  by blast

lemma saturatd_lookup_hit_no_fault:
  "\<lbrakk>saturated_no_flt (typ_sat_no_flt_tlb s); no_faults (tlb_sat_no_flt_set s);
          lookup (tlb_sat_no_flt_set s) (ASID s) (addr_val b) = Hit x; \<not> is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) b)\<rbrakk>
                \<Longrightarrow> x = pt_walk (ASID s) (MEM s) (TTBR0 s) b"
  apply (subgoal_tac "lookup (tlb_sat_no_flt_set s \<union> 
                              {e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e}) (ASID s) (addr_val b) = Hit x")
   prefer 2
   apply (drule sat_state_tlb', clarsimp simp: state.defs)
  apply (drule lookup_hit_miss_or_hit')
  apply (erule disjE)
   apply (clarsimp simp: lookup_range_pt_walk_hit_no_flt)
  apply (frule lookup_range_fault_pt_walk)
  apply (drule_tac x = "addr_val b" in bspec; clarsimp simp: lookup_hit_entry_range)
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
  "lookup (tlb - (\<Union>v\<in>vset. {e \<in> tlb. addr_val v \<in> entry_range e})) a (addr_val b) \<noteq> Miss \<Longrightarrow>
      b \<notin> vset"
  by (clarsimp simp: lookup_def entry_set_def entry_range_asid_tags_def split:if_split_asm)

lemma lookup_not_miss_varange':
  "v \<in> vset\<Longrightarrow> 
   lookup (tlb_sat_no_flt_set s - (\<Union>v\<in>vset. {e \<in> tlb_sat_no_flt_set s. addr_val v \<in> entry_range e})) a (addr_val v) =
               Miss"
  apply (subgoal_tac "entry_set (tlb_sat_no_flt_set s - 
              (\<Union>v\<in>vset. {e \<in> tlb_sat_no_flt_set s. addr_val v \<in> entry_range e})) a (addr_val v) = {}")
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




lemma flush_varange_sat_no_flt_abs_refine':
  "\<lbrakk>Flush_varange vset (s::tlb_sat_no_flt_state) = ((), s') ;  Flush_varange vset (t::tlb_incon_state') = ((), t'); 
             tlb_rel_abs' (typ_sat_no_flt_tlb s) (typ_incon' t) \<rbrakk> \<Longrightarrow> tlb_rel_abs' (typ_sat_no_flt_tlb s') (typ_incon' t')"
  apply (clarsimp simp: Flush_varange_tlb_sat_no_flt_state_ext_def 
      Flush_varange_tlb_incon_state'_ext_def tlb_rel_abs'_def)
  apply (rule conjI)
   apply (cases s, cases t, clarsimp simp: state.defs)
  apply (subgoal_tac "tlb_sat_no_flt_set s = tlb_sat_no_flt_set s \<union> 
                              {e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e}")
   prefer 2
   apply (drule sat_state_tlb', clarsimp simp: state.defs)
  apply (rule conjI)
   apply (clarsimp simp: asid_va_incon_tlb_mem_def)
   apply (rule conjI)
    apply (clarsimp simp: asid_va_incon_def)
    apply (drule union_incon_cases1)
    apply (erule disjE)
     apply (clarsimp simp: lookup_no_flt_range_pt_walk_not_incon')
    apply (erule disjE)
     apply clarsimp
     apply (subgoal_tac "a = ASID s")
      apply clarsimp
      apply (rule conjI)
       prefer 2
       apply (subgoal_tac "addr_val b \<in> entry_range x")
        apply blast
       apply (clarsimp simp:lookup_hit_entry_range)
      apply (subgoal_tac "lookup (tlb_sat_no_flt_set s) (ASID s) (addr_val b) = Hit x  \<or> 
                     lookup (tlb_sat_no_flt_set s ) (ASID s) (addr_val b) = Incon")
       apply (erule disjE)
        apply (subgoal_tac "x = pt_walk (ASID s) (MEM s) (TTBR0 s) xb")
         apply clarsimp
        apply (subgoal_tac "pt_walk (ASID s) (MEM s) (TTBR0 s) xb =  pt_walk (ASID s) (MEM s) (TTBR0 s) b")
         apply (clarsimp simp: saturatd_lookup_hit_no_fault) 
        apply (subgoal_tac " (ASID s, addr_val b) \<in> entry_range_asid_tags (pt_walk (ASID s) (MEM s) (TTBR0 s) xb)")
         apply (drule va_entry_set_pt_palk_same , clarsimp)
        apply (clarsimp simp: lookup_hit_entry_range_asid_tags)
       apply (subgoal_tac " (ASID s, b) \<in> incon_set (tlb_incon_set' t)")
        prefer 2
        apply blast
       apply clarsimp
      apply (drule lookup_hit_incon_minus, clarsimp) 
     apply (drule_tac t = "{e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e}" in  lookup_hit_asid)
     apply clarsimp
    apply (erule disjE)
     apply clarsimp
     apply (clarsimp simp: lookup_no_flt_range_pt_walk_not_incon')
    apply (erule disjE)
     apply clarsimp
     apply (subgoal_tac " lookup (tlb_sat_no_flt_set s) a (addr_val b) = Incon")
      apply (rule conjI)
       apply blast
      apply (rule_tac tlb = "tlb_sat_no_flt_set s" and a = a in lookup_not_miss_varange, clarsimp)
     apply (drule lookup_incon_minus, clarsimp)
    apply (erule disjE)
     apply (clarsimp simp: lookup_no_flt_range_pt_walk_not_incon')
    apply clarsimp
    apply (subgoal_tac " lookup (tlb_sat_no_flt_set s) a (addr_val b) = Incon")
     apply (rule conjI)
      apply blast
     apply (rule_tac tlb = "tlb_sat_no_flt_set s" and a = a in lookup_not_miss_varange, clarsimp)
    apply (drule lookup_incon_minus, clarsimp)
   apply (clarsimp simp: asid_va_hit_incon_def)
   apply (drule lookup_hit_union_cases')
   apply (erule disjE)
    apply clarsimp
    apply (rule conjI)
     apply (subgoal_tac "lookup (tlb_sat_no_flt_set s) (ASID s) (addr_val b) = Hit x  \<or> 
                     lookup (tlb_sat_no_flt_set s ) (ASID s) (addr_val b) = Incon")
      apply (erule disjE)
       prefer 2
       apply (clarsimp simp: asid_va_incon_def , blast)
      apply (subgoal_tac "x \<noteq> pt_walk (ASID s) (MEM s) (TTBR0 s) b")
       apply blast
      apply (drule_tac b = b and x = x in saturated_no_flt_pt_walk ; clarsimp simp: lookup_miss_is_fault')
     apply (drule lookup_hit_incon_minus, clarsimp) 
    apply (rule_tac tlb = "tlb_sat_no_flt_set s" and a = "ASID s" in lookup_not_miss_varange, clarsimp)
   apply (erule disjE)
    apply clarsimp
    apply (frule lookup_range_fault_pt_walk)
    apply (drule_tac x = "addr_val b" in bspec; clarsimp simp: lookup_hit_entry_range)
   apply clarsimp
   apply (frule lookup_range_fault_pt_walk)
   apply (drule_tac x = "addr_val b" in bspec; clarsimp simp: lookup_hit_entry_range)
  apply (rule conjI)
   apply (clarsimp simp: saturated_no_flt_def)
  apply (rule conjI)
   apply (clarsimp simp:  no_faults_def)
  apply (rule conjI)
   apply clarsimp
   apply (rule conjI)
    apply (clarsimp simp: snapshot_of_tlb_def)
    apply (subgoal_tac "lookup (tlb_sat_no_flt_set s - 
        (\<Union>v\<in>vset. {e \<in> tlb_sat_no_flt_set s. addr_val v \<in> entry_range e}))  a (addr_val v) =  Miss")
     apply (subgoal_tac "lookup ( {e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e}) a (addr_val v) = Miss")
      apply (rule lookup_miss_union_miss_miss; clarsimp)
     apply (clarsimp simp: lookup_no_flt_range_pt_walk_asid_miss)
    apply (clarsimp simp: lookup_not_miss_varange')
   apply (clarsimp simp: snapshot_of_tlb_def)
   apply (subgoal_tac "lookup (tlb_sat_no_flt_set s - (\<Union>v\<in>vset. {e \<in> tlb_sat_no_flt_set s. addr_val v \<in> entry_range e}) \<union>
                       {e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e}) a (addr_val v) = 
             lookup (tlb_sat_no_flt_set s - (\<Union>v\<in>vset. {e \<in> tlb_sat_no_flt_set s. addr_val v \<in> entry_range e}))  a (addr_val v)")
    apply (clarsimp)
    apply (subgoal_tac " lookup (tlb_sat_no_flt_set s - (\<Union>v\<in>vset. {e \<in> tlb_sat_no_flt_set s. addr_val v \<in> entry_range e})) a (addr_val v) \<le>
                                lookup (tlb_sat_no_flt_set s) a (addr_val v)")
     apply (force simp add: less_eq_lookup_type)
    apply (rule tlb_mono)
    apply blast
   apply (rule lookup_miss_union_equal)
   apply (clarsimp simp: lookup_no_flt_range_pt_walk_asid_miss)
  apply clarsimp
  apply blast
  done



class Flush_ASIDvarange =
  fixes Flush_ASIDvarange :: "asid \<Rightarrow> vaddr set \<Rightarrow> 'a state_scheme \<Rightarrow>  unit \<times> 'a state_scheme" 


instantiation tlb_state_ext :: (type) Flush_ASIDvarange  
begin
  definition   
  "(Flush_ASIDvarange a vset :: ('a tlb_state_scheme \<Rightarrow> _))  = do {
      tlb   <- read_state tlb_set;
      update_state (\<lambda>s. s\<lparr> tlb_set := tlb -
                   (\<Union>v\<in> vset. {e \<in> tlb. (a, addr_val v) \<in> entry_range_asid_tags e}) - 
                                             tlb_evict (typ_tlb s) \<rparr>)}"
instance ..
end


instantiation tlb_det_state_ext :: (type) Flush_ASIDvarange  
begin
  definition   
  "(Flush_ASIDvarange a vset :: ('a tlb_det_state_scheme \<Rightarrow> _))  = do {
      tlb   <- read_state tlb_det_set;
      update_state (\<lambda>s. s\<lparr> tlb_det_set := tlb - 
          (\<Union>v\<in>vset. {e \<in> tlb. (a, addr_val v) \<in> entry_range_asid_tags e})\<rparr>)}"                  
  instance ..
end


instantiation tlb_sat_no_flt_state_ext :: (type) Flush_ASIDvarange 
begin
  definition   
  "(Flush_ASIDvarange a vset :: ('a tlb_sat_no_flt_state_scheme \<Rightarrow> _))  = do {
      tlb   <- read_state tlb_sat_no_flt_set;
      mem   <- read_state MEM;
      ttbr0 <- read_state TTBR0;
      asid <- read_state ASID;
      let all_non_fault_entries = {e\<in>pt_walk asid mem ttbr0 ` UNIV. \<not>is_fault e};
      update_state (\<lambda>s. s\<lparr> tlb_sat_no_flt_set := 
              (tlb - (\<Union>v\<in>vset. {e \<in> tlb. (a, addr_val v) \<in> entry_range_asid_tags e}))
                                  \<union> all_non_fault_entries \<rparr>)} "
  instance ..
end



instantiation tlb_incon_state'_ext :: (type) Flush_ASIDvarange  
begin
  definition   
  "(Flush_ASIDvarange  a vset :: ('a tlb_incon_state'_scheme \<Rightarrow> _))  = do {
      iset   <- read_state tlb_incon_set';
      let iset = iset \<lparr>incon_set := incon_set(iset) - {a} \<times> vset, 
                 tlb_snapshot := \<lambda>x y. if (x, y) \<in> {a} \<times> vset then Miss else tlb_snapshot iset x y \<rparr>;
      update_state (\<lambda>s. s\<lparr> tlb_incon_set' := iset\<rparr>) } "
                  
  instance ..
end

lemma flush_ASIDvarange_non_det_det_refine:
  "\<lbrakk> Flush_ASIDvarange a vset (s::tlb_state) = ((), s') ; Flush_ASIDvarange a vset (t::tlb_det_state) = ((), t'); 
         tlb_rel (typ_tlb s) (typ_det_tlb t) \<rbrakk> \<Longrightarrow>  tlb_rel (typ_tlb s') (typ_det_tlb t') "
  apply (clarsimp simp:  Flush_ASIDvarange_tlb_state_ext_def  Flush_ASIDvarange_tlb_det_state_ext_def 
          tlb_rel_def  no_faults_def) 
  apply (cases s, cases t , clarsimp simp: state.defs tlb_rel_def) 
  by blast

lemma  flush_ASIDvarange_det_sat_no_flt_refine:
  "\<lbrakk> Flush_ASIDvarange a vset (s::tlb_det_state) = ((), s') ;  Flush_ASIDvarange a vset (t::tlb_sat_no_flt_state) = ((), t'); 
         tlb_rel_sat_no_flt (typ_det_tlb s) (typ_sat_no_flt_tlb t) \<rbrakk> \<Longrightarrow> 
                  tlb_rel_sat_no_flt (typ_det_tlb s') (typ_sat_no_flt_tlb t')"
  apply (clarsimp simp: Flush_ASIDvarange_tlb_det_state_ext_def Flush_ASIDvarange_tlb_sat_no_flt_state_ext_def)
  apply (clarsimp simp: tlb_rel_sat_no_flt_def saturated_no_flt_def no_faults_def)
  apply (cases s, cases t , clarsimp simp: state.defs)
  by blast



lemma lookup_miss_diff_asid_varange:
  " a \<noteq> ASID s
              \<Longrightarrow> lookup (\<Union>x\<in>{a} \<times> vset. case x of (a, v) \<Rightarrow> {e \<in> tlb_sat_no_flt_set s. (a, addr_val v) \<in> entry_range_asid_tags e})
                   (ASID s) (addr_val b) =
                  Miss"
 apply (subgoal_tac "entry_set (\<Union>x\<in>{a} \<times> vset. case x of (a, v) \<Rightarrow> {e \<in> tlb_sat_no_flt_set s. (a, addr_val v) \<in> entry_range_asid_tags e})
                   (ASID s) (addr_val b) = {}")
   apply (clarsimp simp: lookup_def)
  by (clarsimp simp: entry_set_va_set a_va_set_def entry_range_asid_tags_def)


lemma lookup_asid_va_range_elem:
  "lookup (\<Union>x\<in>{ASID s} \<times> vset. case x of (a, v) \<Rightarrow> {e \<in> tlb_sat_no_flt_set s. (a, addr_val v) \<in> entry_range_asid_tags e}) (ASID s) (addr_val b) = Hit x \<Longrightarrow>
      addr_val b \<in> \<Union>(entry_range ` (\<Union>x\<in>{ASID s} \<times> vset. case x of (a, v) \<Rightarrow> {e \<in> tlb_sat_no_flt_set s. (a, addr_val v) \<in> entry_range_asid_tags e}))"
  apply (clarsimp simp: lookup_def  entry_set_def entry_range_asid_tags_def  split:if_split_asm)
  by force


lemma  va_entry_set_pt_palk_same':
  "(asid, addr_val va) \<in> entry_range_asid_tags (pt_walk asid mem ttbr0 x) \<Longrightarrow>
       pt_walk asid mem ttbr0 x = pt_walk asid mem ttbr0 va"
  apply (subgoal_tac "(asid, addr_val x) \<in> entry_range_asid_tags (pt_walk asid mem ttbr0 x)")
   prefer 2
   apply (clarsimp simp: asid_va_entry_range_pt_entry1)
  apply (cases "pt_walk asid mem ttbr0 x")
   apply (case_tac "x13" ; simp)
    apply (clarsimp simp: entry_range_asid_tags_def entry_range_def pt_walk_def)
    apply (cases "get_pde mem ttbr0 x" ; clarsimp)
    apply (case_tac a ; clarsimp)
    apply (case_tac " get_pte mem x3 x " ; clarsimp)
     apply (subgoal_tac "get_pde mem ttbr0 x = get_pde mem ttbr0 va" ; clarsimp)
      apply (subgoal_tac "get_pte mem x3 x = get_pte mem x3 va" ; clarsimp)
       using va_offset_higher_bits apply blast
      apply (clarsimp simp:  get_pte_def vaddr_pt_index_def)
      apply (subgoal_tac "((addr_val x >> 12) && mask 8 << 2) =
                          ((addr_val va >> 12) && mask 8 << 2) ")
       prefer 2
       using offset_mask_eq apply blast
      apply force
     apply (clarsimp simp: get_pde_def vaddr_pd_index_def)
     apply (subgoal_tac "((addr_val x >> 20) && mask 12 << 2) =
                         ((addr_val va >> 20) && mask 12 << 2) ")
      prefer 2
      using offset_mask_eq_1 apply blast
     apply force
    apply (case_tac a ; clarsimp)
    apply (subgoal_tac "get_pde mem ttbr0 x = get_pde mem ttbr0 va" ; clarsimp)
     apply (subgoal_tac "get_pte mem x3 x = get_pte mem x3 va" ; clarsimp)
      using va_offset_higher_bits apply blast
     apply (clarsimp simp: get_pte_def vaddr_pt_index_def)
     apply (case_tac "get_pde mem ttbr0 va" ; clarsimp)
     apply (subgoal_tac "((addr_val x >> 12) && mask 8 << 2) =
                         ((addr_val va >> 12) && mask 8 << 2) ")
      prefer 2
      using offset_mask_eq apply blast
     apply force
    apply (clarsimp simp: get_pde_def vaddr_pd_index_def)
    apply (subgoal_tac "((addr_val x >> 20) && mask 12 << 2) =
                        ((addr_val va >> 20) && mask 12 << 2) ")
     prefer 2
     using offset_mask_eq_1 apply blast
    apply force
   apply clarsimp
   apply (clarsimp simp: entry_range_asid_tags_def entry_range_def pt_walk_def)
   apply (cases "get_pde mem ttbr0 x" ; clarsimp)
   apply (case_tac aa ; clarsimp)
   apply (case_tac "get_pte mem x3 x" ; clarsimp)
   apply (subgoal_tac "get_pde mem ttbr0 x = get_pde mem ttbr0 va" ; clarsimp)
    apply (subgoal_tac "get_pte mem x3 x = get_pte mem x3 va" ; clarsimp)
     apply (case_tac aa ; clarsimp)
     using va_offset_higher_bits apply blast
    apply (case_tac aa ; clarsimp simp: get_pte_def vaddr_pt_index_def)
    apply (subgoal_tac "((addr_val x >> 12) && mask 8 << 2) =
                        ((addr_val va >> 12) && mask 8 << 2) ")
     prefer 2
     using offset_mask_eq apply blast
    apply force
   apply (case_tac aa ; clarsimp simp: get_pde_def vaddr_pd_index_def)
   apply (subgoal_tac "((addr_val x >> 20) && mask 12 << 2) =
                       ((addr_val va >> 20) && mask 12 << 2) ")
    prefer 2
    using offset_mask_eq_1 apply blast
   apply force
  apply (clarsimp)
  apply (case_tac "x23" ; clarsimp simp: entry_range_asid_tags_def entry_range_def pt_walk_def)
   apply (cases "get_pde mem ttbr0 x" ; clarsimp)
    apply (subgoal_tac "get_pde mem ttbr0 va = get_pde mem ttbr0 x" ; clarsimp)
     using va_offset_higher_bits_1 apply blast
    apply (clarsimp simp: get_pde_def vaddr_pd_index_def)
    apply (subgoal_tac "((addr_val x >> 20) && mask 12 << 2) = ((addr_val va >> 20) && mask 12 << 2)")
     apply force
    using shfit_mask_eq apply blast
   apply (case_tac a , clarsimp)
      apply (subgoal_tac "get_pde mem ttbr0 va = get_pde mem ttbr0 x" ; clarsimp)
       using va_offset_higher_bits_1 apply blast
      apply (clarsimp simp: get_pde_def vaddr_pd_index_def)
      apply (subgoal_tac "((addr_val x >> 20) && mask 12 << 2) = ((addr_val va >> 20) && mask 12 << 2)")
       apply force
      using shfit_mask_eq apply blast
     apply clarsimp
     apply (subgoal_tac "get_pde mem ttbr0 va = get_pde mem ttbr0 x" ; clarsimp)
      using va_offset_higher_bits_1 apply blast
     apply (clarsimp simp: get_pde_def vaddr_pd_index_def)
     apply (subgoal_tac "((addr_val x >> 20) && mask 12 << 2) = ((addr_val va >> 20) && mask 12 << 2)")
      apply force
     using shfit_mask_eq apply blast
    apply clarsimp
    apply (case_tac "get_pte mem x3 x" ; clarsimp)
    apply (case_tac a , clarsimp)
    apply clarsimp
   apply (case_tac a ; clarsimp)
  apply (cases "get_pde mem ttbr0 x" ; clarsimp)
  apply (case_tac aa ; clarsimp)
   apply (case_tac "get_pte mem x3 x" ; clarsimp)
   apply (case_tac aa ; clarsimp)
  apply (subgoal_tac "get_pde mem ttbr0 va= get_pde mem ttbr0 x" ; clarsimp)
   using va_offset_higher_bits_1 apply blast
  apply (clarsimp simp: get_pde_def vaddr_pd_index_def)
  apply (subgoal_tac "((addr_val x >> 20) && mask 12 << 2) = ((addr_val va >> 20) && mask 12 << 2)")
   apply force
  using shfit_mask_eq apply blast
 done

lemma  asidvset_elem_lookup_miss:
  "b \<in> vset \<Longrightarrow>  lookup (tlb_sat_no_flt_set s - (\<Union>v\<in>vset. {e \<in> tlb_sat_no_flt_set s. (ASID s, addr_val v) \<in> entry_range_asid_tags e}))
                (ASID s) (addr_val b) = Miss"
  apply (clarsimp simp: lookup_def entry_set_def entry_range_asid_tags_def)
  apply safe
  by auto


lemma   asidvset_elem_lookup_miss':
  "b \<in> vset \<Longrightarrow>  lookup (tlb_sat_no_flt_set s - (\<Union>v\<in>vset. {e \<in> tlb_sat_no_flt_set s. (a, addr_val v) \<in> entry_range_asid_tags e}))
                a (addr_val b) = Miss"
  apply (clarsimp simp: lookup_def entry_set_def entry_range_asid_tags_def)
  apply safe
  by auto

lemma  lookup_not_miss_asidvarange:
  "lookup (tlb - (\<Union>v\<in>vset. {e \<in> tlb. (a, addr_val v) \<in> entry_range_asid_tags e})) a (addr_val va) \<noteq> Miss \<Longrightarrow> va \<notin> vset"
  apply (clarsimp simp: lookup_def entry_set_def entry_range_asid_tags_def split:if_split_asm) 
   by auto

lemma flush_ASIDvarange_sat_no_flt_abs_refine':
  "\<lbrakk>Flush_ASIDvarange a vset (s::tlb_sat_no_flt_state) = ((), s') ; Flush_ASIDvarange a vset (t::tlb_incon_state') = ((), t'); 
             tlb_rel_abs' (typ_sat_no_flt_tlb s) (typ_incon' t) \<rbrakk> \<Longrightarrow> tlb_rel_abs' (typ_sat_no_flt_tlb s') (typ_incon' t')"
  apply (clarsimp simp: Flush_ASIDvarange_tlb_sat_no_flt_state_ext_def 
      Flush_ASIDvarange_tlb_incon_state'_ext_def tlb_rel_abs'_def)
  apply (rule conjI)
   apply (cases s, cases t, clarsimp simp: state.defs)
  apply (subgoal_tac "tlb_sat_no_flt_set s = tlb_sat_no_flt_set s \<union> 
                              {e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e}")
   prefer 2
   apply (drule sat_state_tlb', clarsimp simp: state.defs)
  apply (rule conjI)
   apply (clarsimp simp: asid_va_incon_tlb_mem_def)
   apply (rule conjI)
    apply (clarsimp simp: asid_va_incon_def)
    apply (drule union_incon_cases1)
    apply (erule disjE)
     apply (clarsimp simp: lookup_no_flt_range_pt_walk_not_incon')
    apply (erule disjE)
     apply clarsimp
     apply (subgoal_tac "aa = ASID s")
      apply clarsimp
      apply (rule conjI)
       apply (subgoal_tac "lookup (tlb_sat_no_flt_set s) (ASID s) (addr_val b) = Hit x  \<or> 
                     lookup (tlb_sat_no_flt_set s ) (ASID s) (addr_val b) = Incon")
        apply (erule disjE)
         prefer 2
         apply blast
        apply (subgoal_tac "pt_walk (ASID s) (MEM s) (TTBR0 s) xb = pt_walk (ASID s) (MEM s) (TTBR0 s) b")
         apply (subgoal_tac "x = pt_walk (ASID s) (MEM s) (TTBR0 s) b")
          apply clarsimp
         apply (rule  saturatd_lookup_hit_no_fault ; clarsimp)
        apply (subgoal_tac "(ASID s, addr_val b) \<in>
                   entry_range_asid_tags (pt_walk (ASID s) (MEM s) (TTBR0 s) xb)")
         apply (drule va_entry_set_pt_palk_same, clarsimp)
        apply (clarsimp simp: lookup_hit_entry_range_asid_tags)
       apply (drule lookup_hit_incon_minus, clarsimp)
      apply (clarsimp simp: asidvset_elem_lookup_miss)
     apply (drule_tac t = "{e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e}" in  lookup_hit_asid , clarsimp)
    apply (erule disjE)
     apply clarsimp
     apply (clarsimp simp: lookup_no_flt_range_pt_walk_not_incon')
    apply (erule disjE)
     apply clarsimp
     apply (subgoal_tac " lookup (tlb_sat_no_flt_set s) aa (addr_val b) = Incon")
      apply (rule conjI)
       apply blast
      apply (rule impI)
      apply (rule_tac tlb = "tlb_sat_no_flt_set s" and a = a in lookup_not_miss_asidvarange, clarsimp)
     apply (drule lookup_incon_minus, clarsimp)
    apply (erule disjE)
     apply (clarsimp simp: lookup_no_flt_range_pt_walk_not_incon')
    apply clarsimp
    apply (subgoal_tac " lookup (tlb_sat_no_flt_set s) aa (addr_val b) = Incon")
     apply (rule conjI)
      apply blast
     apply (rule impI)
     apply (rule_tac tlb = "tlb_sat_no_flt_set s" and a = a in lookup_not_miss_asidvarange, clarsimp)
    apply (drule lookup_incon_minus, clarsimp)
   apply (clarsimp simp: asid_va_hit_incon_def)
   apply (drule lookup_hit_union_cases')
   apply (erule disjE)
    apply clarsimp
    apply (rule conjI)
     apply (subgoal_tac "lookup (tlb_sat_no_flt_set s) (ASID s) (addr_val b) = Hit x  \<or> 
                     lookup (tlb_sat_no_flt_set s ) (ASID s) (addr_val b) = Incon")
      apply (erule disjE)
       prefer 2
       apply (clarsimp simp: asid_va_incon_def , blast)
      apply (subgoal_tac "x \<noteq> pt_walk (ASID s) (MEM s) (TTBR0 s) b")
       apply blast
      apply (drule_tac b = b and x = x in saturated_no_flt_pt_walk ; clarsimp simp: lookup_miss_is_fault')
     apply (drule lookup_hit_incon_minus, clarsimp)
    apply (rule impI)
    apply (rule_tac tlb = "tlb_sat_no_flt_set s" and a = "ASID s" in lookup_not_miss_asidvarange, clarsimp)
   apply (erule disjE)
    apply clarsimp
    apply (frule lookup_range_fault_pt_walk)
    apply (drule_tac x = "addr_val b" in bspec; clarsimp simp: lookup_hit_entry_range)
   apply clarsimp
   apply (frule lookup_range_fault_pt_walk)
   apply (drule_tac x = "addr_val b" in bspec; clarsimp simp: lookup_hit_entry_range)
  apply (rule conjI)
   apply (clarsimp simp: saturated_no_flt_def)
  apply (rule conjI)
   apply (clarsimp simp:  no_faults_def)
  apply (rule conjI)
   apply clarsimp
   apply (rule conjI)
    apply (clarsimp simp: snapshot_of_tlb_def)
    apply (subgoal_tac "lookup (tlb_sat_no_flt_set s - 
        (\<Union>v\<in>vset. {e \<in> tlb_sat_no_flt_set s. (a, addr_val v) \<in> entry_range_asid_tags e}))  a (addr_val v) =  Miss")
     apply (subgoal_tac "lookup ( {e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e}) a (addr_val v) = Miss")
      apply (rule lookup_miss_union_miss_miss ; clarsimp)
     apply (clarsimp simp: lookup_no_flt_range_pt_walk_asid_miss)
    apply (clarsimp simp: asidvset_elem_lookup_miss')
   apply (clarsimp simp: snapshot_of_tlb_def)
   apply (subgoal_tac "lookup (tlb_sat_no_flt_set s - (\<Union>v\<in>vset. {e \<in> tlb_sat_no_flt_set s. (a, addr_val v) \<in> entry_range_asid_tags e}) \<union>
                       {e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e}) aa (addr_val v) = 
             lookup (tlb_sat_no_flt_set s - (\<Union>v\<in>vset. {e \<in> tlb_sat_no_flt_set s. (a, addr_val v) \<in> entry_range_asid_tags e}))  aa (addr_val v)")
    apply (clarsimp)
    apply (subgoal_tac " lookup (tlb_sat_no_flt_set s - (\<Union>v\<in>vset. {e \<in> tlb_sat_no_flt_set s. (a, addr_val v) \<in> entry_range_asid_tags e})) aa (addr_val v) \<le>
                                lookup (tlb_sat_no_flt_set s) aa (addr_val v)")
     apply (force simp add: less_eq_lookup_type)
    apply (rule tlb_mono)
    apply blast
   apply (rule lookup_miss_union_equal)
   apply (clarsimp simp: lookup_no_flt_range_pt_walk_asid_miss)
  apply clarsimp
  apply blast
  done
 


end