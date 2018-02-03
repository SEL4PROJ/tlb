theory Page_Table_Ops
                  
imports User_Execution


begin               



lemma remap_section_current_asid:
  "\<Turnstile> \<lbrace>\<lambda>s. mmu_layout s \<and> mode s = Kernel \<and> safe_set (kernel_safe s) s \<and> 
      Addr vp \<in> SM \<and>
      SM = kernel_safe s \<and>
      asids_consistent {} s \<and>
      k_phy_ad vp \<in> ptable_footprint s (root s) \<and>
      heap s (k_phy_ad vp) = Some pde \<and>
      (\<exists>p perms. decode_pde pde = SectionPDE p perms) \<and> 
      decode_pde pde' = SectionPDE base' perms' \<rbrace>
      Const vp ::= Const pde'
   \<lbrace>\<lambda>s. asids_consistent {asid s} s\<rbrace>"
  apply (vcgm vcg: weak_pre_write')
  apply (rule conjI)
   apply (clarsimp simp: asids_consistent_def safe_set_def con_set_def)
  apply (subgoal_tac " ptable_lift' (heap s) (root s) (Addr vp) = Some (Addr vp r-  global_offset)" , clarsimp)
   prefer 2
   apply (clarsimp simp: kerenl_region_offset')
  apply (subgoal_tac "Addr (vp - global_offset) \<notin> root_map_area")
   prefer 2
   apply (subgoal_tac "root s \<in> set (root_log s)")
    apply (clarsimp simp: mmu_layout_def kernel_data_def k_phy_ad_def, blast) 
   apply (clarsimp simp: mmu_layout_def root_log_def)
   apply (rule_tac x = "addr_val (root s)" in image_eqI, simp, force)
  apply (clarsimp simp:asids_consistent_def)
  apply (subgoal_tac "root_map (s\<lparr> heap := heap s(Addr (vp - global_offset) \<mapsto> pde')\<rparr>) = root_map s")
   apply clarsimp
   apply (drule_tac x = r in spec, drule_tac x = a in spec, simp)
   apply (drule_tac x = v in spec)
   apply (erule disjE, simp)
   apply (subgoal_tac "pt_walk a (heap s(Addr (vp - global_offset) \<mapsto> pde')) r v =
                          pt_walk a (heap s) r v", simp)
   apply (rule pt_walk_pt_trace_upd')
   apply simp
   prefer 2
   apply (clarsimp simp: root_map_area_def)
  apply (subgoal_tac "r \<noteq> root s")
   prefer 2
   apply (clarsimp simp: mmu_layout_def)
  apply (clarsimp simp: k_phy_ad_def ptable_footprint_def)
  apply (subgoal_tac "non_overlapping_tables s")
   prefer 2
   apply (clarsimp simp: mmu_layout_def non_overlapping_tables_from_kernel_data )
  apply (clarsimp simp: non_overlapping_tables_def)
  apply (drule_tac x = r in spec, drule_tac x = "root s" in spec)
  apply (subgoal_tac "r \<in> roots s \<and> root s \<in> roots s")
   apply (clarsimp simp: ptable_footprint_def) apply blast
  apply rule
   prefer 2
   apply (clarsimp simp: roots_def mmu_layout_def root_log_def)
   apply (rule_tac x = "addr_val (root s)" in image_eqI, simp, force)
  apply (clarsimp simp: roots_def mmu_layout_def root_log_def)
  apply (rule_tac x = "addr_val r" in image_eqI, simp, force)
  done
 



lemma kernel_safe_incon_upd[simp]:
  "kernel_safe (incon_set_update f s) = kernel_safe s"
  by (simp add: kernel_safe_def vas_of_current_state_mapped_to_global_mappings_of_all_processes_def
    roots_def)


lemma kernel_safe_ptable_snapshot_upd[simp]:
  "kernel_safe (ptable_snapshot_update f s) = kernel_safe s"
  by (simp add: kernel_safe_def vas_of_current_state_mapped_to_global_mappings_of_all_processes_def roots_def)


lemma flush_one_asid:
  "\<Turnstile> \<lbrace>\<lambda>s. asids_consistent {a} s \<and> mode s = Kernel\<rbrace>
       Flush (flushASID a)
   \<lbrace>\<lambda>s. asids_consistent {} s\<rbrace>"
   apply vcgm
   by (simp add: asids_consistent_def Times_Diff_distrib1 Diff_Int_distrib2)



lemma flush_one_asid_rest:
  "\<Turnstile> \<lbrace>\<lambda>s. mmu_layout s \<and> mode s = Kernel \<and> safe_set (kernel_safe s) s\<rbrace>
       Flush (flushASID a)
   \<lbrace>\<lambda>s. mmu_layout s \<and> mode s = Kernel \<and> safe_set (kernel_safe s) s\<rbrace>"
  apply vcgm
  by (simp add: mmu_layout_def safe_set_def safe_memory_def con_set_def ptrace_set_def kernel_data_def)
  


end
