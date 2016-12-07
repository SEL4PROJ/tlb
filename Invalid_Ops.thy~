theory Invalid_Ops

imports MMU_ARM

begin               





(* ----------- Invalidation Operations and theorems  --------  *)


definition 
  asid_va_invlaidate :: "vaddr \<Rightarrow> tlb_entry set state_scheme \<Rightarrow> unit \<times> tlb_entry set state_scheme"
where
  "asid_va_invlaidate va \<equiv> do {
     asid  <- read_state ASID;
     tlb   <- read_state (state.more);
     update_state (\<lambda>s. s\<lparr> state.more := a_va_sel_invalidate (state.more s) asid (addr_val va) \<rparr>)
   }"


lemma lookup_incon_invalid_case:
  "\<lbrakk> lookup t a v = Incon  \<rbrakk> \<Longrightarrow> 
     lookup (a_va_sel_invalidate t a v) a v = Miss "
  by (clarsimp simp: lookup_def a_va_sel_invalidate_def entry_set_def
                  split:split_if_asm)


lemma hit_invlaidate_miss:
  "lookup (state.more s) (ASID s) (addr_val va) = Hit x3 \<Longrightarrow>
           lookup (state.more s - {x3}) (ASID s) (addr_val va) = Miss"
  apply (clarsimp simp: lookup_def split: split_if_asm)
  unfolding entry_set_def apply blast 
done


lemma inavlidate_implies_consistent:
  "\<lbrakk> asid_va_invlaidate va s = ((), s')  \<rbrakk>  \<Longrightarrow> consistent s' va"
  apply (clarsimp simp: asid_va_invlaidate_def a_va_sel_invalidate_def)
  apply (cases "lookup (state.more s) (ASID s) (addr_val va)")
    apply (clarsimp simp: consistent0_def)
   apply (frule lookup_incon_invalid_case)
   apply (clarsimp simp: a_va_sel_invalidate_def) 
   unfolding consistent0_def apply simp
  apply (clarsimp simp: hit_invlaidate_miss)
done


definition 
  asid_va_block_invlaidate :: "vaddr set \<Rightarrow> tlb_entry set state_scheme \<Rightarrow> unit \<times> tlb_entry set state_scheme"
where
  "asid_va_block_invlaidate va \<equiv> do {
     asid  <- read_state ASID;
     tlb   <- read_state state.more;
     update_state (\<lambda>s. s\<lparr> state.more := a_va_block_invalidation tlb asid (addr_val `va) \<rparr>)
   }"

lemma  not_block_present_miss:
  "\<not> is_a_vset_present t a va  \<Longrightarrow> \<forall>v\<in>va. (lookup t a v = Miss)"
  apply (clarsimp simp: is_a_vset_present_def is_a_va_present_def a_va_set_def image_def
    lookup_def entry_set_def)
  by blast
 
   
lemma block_inavlidate_implies_consistent:
  "\<lbrakk> asid_va_block_invlaidate va s = ((), s')  \<rbrakk>  \<Longrightarrow> \<forall>v\<in>va. consistent s' v"
  apply (simp add: asid_va_block_invlaidate_def )
  apply (subgoal_tac "state.more s' = a_va_block_invalidation (state.more s) (ASID s) (addr_val ` va)")
   prefer 2 
   apply clarsimp
   apply (insert is_present_block [of "state.more s" "ASID s" "(addr_val ` va)"])
   apply (frule not_block_present_miss)
   unfolding consistent0_def 
   apply (rule ballI)
   by auto
 



definition 
  asid_invlaidate :: "tlb_entry set state_scheme \<Rightarrow> unit \<times> tlb_entry set state_scheme"
where
  "asid_invlaidate \<equiv> do {
     asid  <- read_state ASID;
     tlb   <- read_state state.more;
     update_state (\<lambda>s. s\<lparr> state.more := asid_invalidation tlb asid \<rparr>)
   }"

lemma  not_asid_present_miss:
  "\<not>is_asid_present t a  \<Longrightarrow> \<forall>v. (lookup t a v = Miss)"
  apply (clarsimp simp: is_asid_present_def asid_set_def lookup_def)
  apply (subgoal_tac "entry_set t a v = {}")
   apply (clarsimp simp: lookup_def)
  by (clarsimp simp: entry_set_def entry_range_asid_tags_def)
 
   
lemma asid_inavlidate_implies_consistent:
  "\<lbrakk> asid_invlaidate  s = ((), s')  \<rbrakk>  \<Longrightarrow> consistent s' v"
  apply (simp add: asid_invlaidate_def )
  apply (subgoal_tac "state.more s' = asid_invalidation (state.more s) (ASID s)")
   prefer 2 
   apply clarsimp
   apply (insert is_present_asid_invalidation [of "state.more s" "ASID s" ])
   apply (frule not_asid_present_miss)
   unfolding consistent0_def 
   by auto
 

definition 
  va_sel_invlaidate :: "vaddr \<Rightarrow> tlb_entry set state_scheme \<Rightarrow> unit \<times> tlb_entry set state_scheme"
where
  "va_sel_invlaidate va \<equiv> do {
     tlb   <- read_state state.more;
     update_state (\<lambda>s. s\<lparr> state.more := va_sel_invalidation tlb (addr_val va) \<rparr>)
   }"

lemma not_va_present_miss:
  "\<not>is_va_present t v  \<Longrightarrow> \<forall>a. (lookup t a v = Miss)"
  apply (clarsimp simp: is_va_present_def va_entry_set_def va_set_def lookup_def)
  apply (subgoal_tac "entry_set t a v = {}")
   apply (clarsimp simp: lookup_def)
  by (clarsimp simp: entry_set_def entry_range_asid_tags_def)

lemma va_inavlidate_implies_consistent:
  "\<lbrakk> va_sel_invlaidate v s = ((), s')  \<rbrakk>  \<Longrightarrow> consistent s' v"
  apply (simp add: va_sel_invlaidate_def )
  apply (subgoal_tac "state.more s' = va_sel_invalidation (state.more s) (addr_val v)")
   prefer 2 
   apply clarsimp
   apply (insert is_presect_va_invlaidation [of "state.more s" "addr_val v" ])
   apply (frule not_va_present_miss)
   unfolding consistent0_def 
   by auto



end