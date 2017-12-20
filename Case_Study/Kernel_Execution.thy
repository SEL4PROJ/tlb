theory Kernel_Execution
                  
imports Memory_Model
        

begin  

lemma [simp]:
  "safe_memory S (s\<lparr>incon_set := IS\<rparr>) =  safe_memory S s "
  by (clarsimp simp: safe_memory_def ptrace_set_def)


lemma [simp]:
  "con_set S (s\<lparr>heap := hp ,  incon_set := IS\<rparr>) =  con_set S (s\<lparr>incon_set := IS\<rparr>) "
  by (clarsimp simp: con_set_def)



lemma kerenl_region_offset':
  " mmu_layout s \<and> mode s = Kernel   \<Longrightarrow>
        \<forall>va\<in>kernel_safe s.  ptable_lift' (heap s) (root s) va = 
      Some (Addr (addr_val va) r- global_offset)"
  by (clarsimp simp: mmu_layout_def)




lemma mmu_layout_pt_walk':
  "\<lbrakk> mmu_layout s; p \<notin> kernel_data_area s; rt \<in> root_log s \<rbrakk> \<Longrightarrow>
  pt_walk a (heap s(p \<mapsto> v)) rt = pt_walk a (heap s) rt"
  apply (rule ext)
  apply (subst pt_walk_pt_trace_upd')
   apply (clarsimp simp: mmu_layout_def kernel_data_def ptable_footprint_def)
  by fastforce 



lemma mmu_layout_ptable_comp':
  "\<lbrakk> mmu_layout s; p \<notin> kernel_data_area s \<rbrakk> \<Longrightarrow> 
        ptable_comp (asid s) (heap s) (heap s(p \<mapsto> v)) (root s) (root s) = {}"
  apply (simp add: ptable_comp_def)
  apply (subgoal_tac "root s \<in> root_log s")
   apply (simp add: mmu_layout_pt_walk')
  by (simp add: mmu_layout_def)




lemma mmu_layout_upd':
  "\<lbrakk> mmu_layout s; p \<notin> kernel_data_area s \<rbrakk> \<Longrightarrow> mmu_layout (s\<lparr>p_state.heap := heap s(p \<mapsto> v)\<rparr>)"
  apply (clarsimp simp: mmu_layout_def)
  apply (subgoal_tac "p \<notin> kernel_data_area s")
   prefer 2
   apply blast
  apply (simp add: kernel_data_upd kernel_mapping_upd)
  apply (rule conjI)
   apply (clarsimp simp: non_overlapping_tables_def)
   apply (simp add: kernel_data_def ptable_footprint_upd)
  apply (clarsimp simp: user_mappings_def)
  apply (subst (asm) pt_table_lift_trace_upd)
   apply (simp add: kernel_data_def ptable_footprint_def)
  apply simp
  done


lemma global_mappings_decode_mmu:
  "\<lbrakk>mmu_layout s ; mode s = Kernel  ; va \<in> kernel_safe s\<rbrakk> \<Longrightarrow> 
         \<exists>p perm. decode_pde (the ((heap s) 
          (root s r+ (vaddr_pd_index (addr_val va) << 2)))) =  SectionPDE p perm"
  apply (clarsimp simp: kernel_safe_def vas_mapped_by_global_mappings_def
  global_mappings_of_all_processes_def global_mappings_def  mmu_layout_def )
  apply (drule_tac x = "root s" in bspec)
   apply clarsimp
  apply (drule_tac x = "x" in spec)
  by (clarsimp simp: get_pde'_def decode_heap_pde'_def)
   

lemma global_high_ptable:
  "\<lbrakk> mmu_layout s ; mode s = Kernel ; Addr vp \<in> (kernel_safe s) ;
        x \<in> ptable_trace' (heap s) (root s) (Addr vp)\<rbrakk>
           \<Longrightarrow> x \<in> high_ptable (root s)"
  apply (frule_tac va = "Addr vp" in global_mappings_decode_mmu ; clarsimp )
  apply (clarsimp simp: ptable_trace'_def Let_def)
  apply (clarsimp simp: mmu_layout_def kernel_safe_def vas_mapped_by_global_mappings_def
  vas_of_current_state_mapped_to_global_mappings_of_all_processes_def)
  apply (subgoal_tac "xa = root s r+ (vaddr_pd_index vp << 2)")
   apply (rule_tac x = "root s" in bexI)
    apply (clarsimp simp: pd_idx_offset_def)
   apply clarsimp
  by (clarsimp simp: ptable_trace'_def)


lemma global_high_ptable':
  "\<lbrakk> mmu_layout s ; mode s = Kernel ; Addr vp \<in> (kernel_safe s) \<rbrakk> \<Longrightarrow>
        \<forall>x\<in>ptable_trace' (heap s) (root s) (Addr vp).
           x \<in> high_ptable (root s)"
   by (clarsimp simp: global_high_ptable)
   
  

lemma pt_table_lift_trace_upd':
  "p \<notin> ptable_trace' h r x \<Longrightarrow>  ptable_lift' h r  x = ptable_lift' (h(p \<mapsto> v)) r  x"
  apply (clarsimp simp: ptable_trace'_def Let_def ptable_lift'_def
  lookup_pde_perm_def lookup_pde'_def get_pde'_def)
  apply (subgoal_tac "decode_heap_pde' (h(p \<mapsto> v)) (r r+ (vaddr_pd_index (addr_val x) << 2)) =
   decode_heap_pde' h (r r+ (vaddr_pd_index (addr_val x) << 2))")
   apply clarsimp
   apply (clarsimp simp: decode_heap_pde'_def)
   apply (clarsimp split: option.splits)
   apply (clarsimp split: pde.splits)
   apply (clarsimp simp: lookup_pte'_def get_pte'_def)
   apply (subgoal_tac "decode_heap_pte' (h(p \<mapsto> v)) (x3 r+ (vaddr_pt_index (addr_val x) << 2)) =
    decode_heap_pte' h (x3 r+ (vaddr_pt_index (addr_val x) << 2))")
    apply (clarsimp)
   apply (clarsimp simp: decode_heap_pte'_def)
  by (clarsimp simp: decode_heap_pde'_def decode_pde_def Let_def split: pde.splits)



lemma  kernel_safe_region_ptable_trace'' [simp]:
  " \<lbrakk> mmu_layout s ; mode s = Kernel ; Addr vp' \<in> kernel_safe s; 
     vp \<in> kernel_safe s\<rbrakk> \<Longrightarrow>
     Addr (vp' - global_offset) \<notin> ptable_trace' (heap s) (root s) vp"
  apply (frule_tac va = vp in  global_mappings_decode_mmu)
    apply (clarsimp simp: mmu_layout_def)
   apply clarsimp
  apply (clarsimp simp:  mmu_layout_def ptable_trace'_def kernel_safe_def Let_def
      vas_mapped_by_global_mappings_def 
        vas_of_current_state_mapped_to_global_mappings_of_all_processes_def 
        pd_idx_offset_def)   
done



lemma kernel_exec2:
  "\<Turnstile> \<lbrace>\<lambda>s. mmu_layout s \<and> mode s = Kernel \<and> safe_set (kernel_safe s) s \<and>
           asids_consistent {} s \<and>
           aval lval s = Some vp \<and> aval rval s = Some v \<and> 
           Addr vp \<in> (kernel_safe s) \<and> k_phy_ad vp \<notin> kernel_data_area s \<rbrace>
        lval ::= rval
      \<lbrace>\<lambda>s. mmu_layout s \<and> mode s = Kernel \<and> safe_set (kernel_safe s) s \<and> 
           asids_consistent {} s \<and> heap s (k_phy_ad vp) = Some v\<rbrace>"
  apply (vcgm vcg: weak_pre_write')
  apply (rule conjI)
   apply (clarsimp simp: asids_consistent_def safe_set_def con_set_def)
  apply (subgoal_tac " ptable_lift' (heap s) (root s) (Addr vp) = Some (Addr vp r-  global_offset)")
   prefer 2
   apply (clarsimp simp: kerenl_region_offset')
  apply clarsimp
  apply (clarsimp simp: k_phy_ad_def)
  apply (clarsimp simp: mmu_layout_ptable_comp')
  apply (clarsimp simp: mmu_layout_upd')
  apply (rule conjI)
   apply (subgoal_tac  "kernel_safe (s\<lparr> heap := heap s(Addr (vp - global_offset) \<mapsto> v)\<rparr>) =
                        kernel_safe s")
    apply clarsimp
    apply (clarsimp simp: safe_set_def)
    apply (rule conjI)
     prefer 2
     apply (clarsimp simp: con_set_def)
    apply (clarsimp simp: safe_memory_def)
    apply (drule_tac x = va in bspec) apply clarsimp
    apply (clarsimp)
    apply (rule_tac x = "p" in exI)
    apply (subgoal_tac "ptable_lift' (heap s) (root s) va = ptable_lift' (heap s(Addr (vp -
     global_offset) \<mapsto> v)) (root s) va")
     apply (rule conjI)
      apply clarsimp
     apply (subgoal_tac  "ptrace_set (kernel_safe s) (s\<lparr> heap := heap s(Addr (vp - global_offset) \<mapsto> v)\<rparr>) =
      ptrace_set (kernel_safe s) s")
      apply (clarsimp simp: )
     prefer 4
     apply (clarsimp simp: asids_consistent_def)
    prefer 3
    apply (frule_tac vp = vp in global_high_ptable' , clarsimp , clarsimp)
    apply (clarsimp simp: kernel_safe_def
    vas_of_current_state_mapped_to_global_mappings_of_all_processes_def)
    apply (rule_tac x = "root s" in bexI)
     apply force
    apply (clarsimp simp: mmu_layout_def)
   prefer 2
   apply (rule pt_table_lift_trace_upd')
   apply clarsimp
  apply (clarsimp simp: ptrace_set_def)
  apply safe
   apply (rule_tac a = xa in UN_I , clarsimp)
   prefer 2
   apply (rule_tac a = xa in UN_I  , clarsimp)
   apply (subgoal_tac "ptable_trace' (heap s(Addr (vp - global_offset) \<mapsto> v)) (root s) xa =
                       ptable_trace' (heap s) (root s) xa")
    apply clarsimp
   prefer 2
   apply (subgoal_tac "ptable_trace' (heap s(Addr (vp - global_offset) \<mapsto> v)) (root s) xa =
                       ptable_trace' (heap s) (root s) xa")
    apply clarsimp
   apply (rule pt_trace_upd)
   apply clarsimp
  apply (subgoal_tac "ptable_trace' (heap s(Addr (vp - global_offset) \<mapsto> v)) (root s) xa =
                      ptable_trace' (heap s) (root s) xa")
   apply clarsimp
  apply (rule pt_trace_upd)
  apply clarsimp
done



end



