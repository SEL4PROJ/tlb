theory User_Execution
                  
imports Context_Switch
        

begin               



definition
  ptable_lift_user :: "vaddr  \<Rightarrow> p_state  \<Rightarrow> paddr \<Rightarrow> bool"    ("(_/ \<hookrightarrow>\<^sub>_/ \<^sub>u\<^sub>s\<^sub>e\<^sub>r / _)")
where
  "ptable_lift_user va s p \<equiv> (ptable_lift_m (heap s) (root s) User va  = Some p)"



definition                   
  user_safe :: "p_state \<Rightarrow> vaddr set"
where
  "user_safe s = {va. \<exists>p. va \<hookrightarrow>\<^sub>s  \<^sub>u\<^sub>s\<^sub>e\<^sub>r  p } "




lemma mmu_layout_no_phy:
  "\<lbrakk> mmu_layout s; mode s = User;  ptable_lift_m (heap s) (root s) (mode s) (Addr vp) = Some p \<rbrakk> 
           \<Longrightarrow> p \<notin> kernel_phy_mem"
  by (clarsimp simp: mmu_layout_def user_mappings_def dest!: root_map_rootsD)




lemma user_safe_assignment:
  "\<Turnstile> \<lbrace> \<lambda>s. mmu_layout s \<and> mode s = User \<and> \<I>\<C> s = {} \<and>
           aval lval s = Some vp \<and> aval rval s = Some v \<and> 
         ptable_lift_m (heap s) (root s) (mode s) (Addr vp) = Some p \<rbrace>
                  lval ::= rval
           \<lbrace>\<lambda>s. mmu_layout s \<and> mode s = User \<and> \<I>\<C> s = {} \<and> heap s p = Some v\<rbrace>"
  apply vcgm
  apply (rule conjI)
   apply (clarsimp simp: \<I>\<C>_def)
  apply (frule_tac vp = vp and p = p in  mmu_layout_no_phy , clarsimp , clarsimp)
  apply (simp add: mmu_layout_ptable_comp mmu_layout_upd)
  apply (simp add: \<I>\<C>_def)
  done


end
