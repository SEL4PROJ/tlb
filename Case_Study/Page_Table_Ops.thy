theory Page_Table_Ops
                  
imports User_Execution


begin               



lemma remap_section_current_asid:
  "\<Turnstile> \<lbrace>\<lambda>s. mmu_layout s \<and> mode s = Kernel \<and>
      Addr vp \<in> SM \<and>
      SM = kernel_safe s \<and>
      asids_consistent {} s \<and>
      k_phy_ad vp \<in> ptable_footprint s (root s) \<and>
      heap s (k_phy_ad vp) = Some pde \<and>
      (\<exists>p perms. decode_pde pde = SectionPDE p perms) \<and> 
      decode_pde pde' = SectionPDE base' perms' \<rbrace>
      Const vp ::= Const pde'
   \<lbrace>\<lambda>s. asids_consistent {asid s} s\<rbrace>"
  apply (vcgm vcg:  assign_sound)
  apply (rule conjI)
   apply (clarsimp simp: asids_consistent_def mmu_layout_def ran_def)
   apply blast
  apply (clarsimp simp: kernel_safe_def mmu_layout_def)
  apply (clarsimp simp: asids_consistent_def)
  apply (subgoal_tac "root_map (s\<lparr> heap := heap s(Addr (vp - global_offset) \<mapsto> pde')\<rparr>) = root_map s")
   apply clarsimp
   apply (clarsimp simp: ptable_comp_def)
   apply (clarsimp simp: ran_def)
   apply blast
  apply (clarsimp simp: kernel_data_def )
  apply (clarsimp simp: ptable_footprint_def k_phy_ad_def)
  apply (subgoal_tac "Addr (vp - global_offset) \<notin> root_map_area")
   prefer 2
   apply blast
  by clarsimp
 
  




lemma remap_section_current_strong:
  "\<Turnstile> \<lbrace>\<lambda>s. mmu_layout s \<and> mode s = Kernel \<and>
      Addr vp \<in> SM \<and>
      SM = kernel_safe s \<and>
      asids_consistent {} s \<and>
      k_phy_ad vp \<in> ptable_footprint s (root s) \<and>
      heap s (k_phy_ad vp) = Some pde \<and>
      (\<exists>p pbits. decode_pde pde = SectionPDE p pbits) \<and> 
      decode_pde pde' = SectionPDE base permissions \<and>
      {base .. base r+ section_size} \<inter> kernel_phy_mem = {} \<rbrace>
      Const vp ::= Const pde'
   \<lbrace>\<lambda>s. mmu_layout s \<and> asids_consistent {asid s} s \<and> mode s = Kernel \<and> safe_set (kernel_safe s) s\<rbrace>"
   oops (* would be nicer, but we probably don't have enough time, probably needs stronger preconds *)

lemma kernel_safe_incon_upd[simp]:
  "kernel_safe (incon_set_update f s) = kernel_safe s"
  by (simp add: kernel_safe_def vas_of_current_state_mapped_to_global_mappings_of_all_processes_def)

lemma flush_one_asid:
  "\<Turnstile> \<lbrace>\<lambda>s. asids_consistent {a} s \<and> mode s = Kernel\<rbrace>
       Flush (flushASID a)
   \<lbrace>\<lambda>s. asids_consistent {} s\<rbrace>"
   apply vcgm
   apply (simp add: asids_consistent_def Times_Diff_distrib1 Diff_Int_distrib2)
   apply fastforce
   done

lemma flush_one_asid_rest:
  "\<Turnstile> \<lbrace>\<lambda>s. mmu_layout s \<and> mode s = Kernel \<and> safe_set (kernel_safe s) s\<rbrace>
       Flush (flushASID a)
   \<lbrace>\<lambda>s. mmu_layout s \<and> mode s = Kernel \<and> safe_set (kernel_safe s) s\<rbrace>"
   apply vcgm
   apply (simp add: mmu_layout_def)
   apply (simp add: safe_set_def safe_memory_def con_set_def ptrace_set_def)
  sorry



end
