theory Memory_Model
                  
imports RT_Log
        

begin               


consts kernel_window_lower_bound   :: "32 word"
consts  kernel_window_upper_bound  :: "32 word"
consts global_offset               :: "32 word"
consts ker_phy_lower_bound         :: "paddr"
consts ker_phy_upper_bound         :: "paddr"


definition
  high_ptable :: "paddr \<Rightarrow> paddr set"
where
  "high_ptable rt  = {rt r+  kernel_window_lower_bound .. rt r+  kernel_window_upper_bound}"


definition
  "kernel_phy_mem  = {ker_phy_lower_bound .. ker_phy_upper_bound}"


definition 
   pd_idx_offset :: "32 word \<Rightarrow> machine_word"
where      
  "pd_idx_offset vp = ((vaddr_pd_index vp) << 2)"

definition
  va_to_pid_offset :: "vaddr set \<Rightarrow> 32 word set"
where
  "va_to_pid_offset V = pd_idx_offset ` addr_val ` V"



definition
  "pointer_to_high_ptable  rt va \<equiv> rt r+ pd_idx_offset va \<in> high_ptable rt"



definition
  global_mappings :: "heap \<Rightarrow> paddr  \<Rightarrow> bool"
where
  "global_mappings h r  \<equiv>
      \<forall>va. r r+ pd_idx_offset va \<in> high_ptable r \<longrightarrow>                                      
                         (\<exists>p perms. get_pde' h r (Addr va) = Some (SectionPDE p perms) \<and> 
                             \<not>user_perms perms ) \<and>
        ptable_lift_m h r Kernel (Addr va)  =  Some (Addr va r- global_offset) \<and> (Addr va r- global_offset) \<in> kernel_phy_mem"



definition
  vas_mapped_by_global_mappings :: "paddr \<Rightarrow> vaddr set"
where
  "vas_mapped_by_global_mappings r \<equiv> Addr ` {va. r r+ pd_idx_offset va \<in>
          high_ptable r }"



definition
  global_mappings_of_all_processes :: "p_state  \<Rightarrow> bool"
where
  "global_mappings_of_all_processes s  \<equiv> \<forall>rt\<in>root_log s. global_mappings (heap s) rt"



definition
  vas_of_current_state_mapped_to_global_mappings_of_all_processes :: "p_state \<Rightarrow> vaddr set"
where
  "vas_of_current_state_mapped_to_global_mappings_of_all_processes s = 
         {va\<in>vas_mapped_by_global_mappings (root s). 
    ptable_trace' (heap s) (root s)va \<subseteq> \<Union>(high_ptable ` root_log s)}"


definition                   
  kernel_safe :: "p_state \<Rightarrow> vaddr set"
where
  "kernel_safe s = vas_mapped_by_global_mappings (root s) -
 vas_of_current_state_mapped_to_global_mappings_of_all_processes s"


lemma global_mappings_ptable_lift' [simp]:
  "\<exists>rt. root s = rt \<and> mode s = Kernel \<and>  rt \<in> root_log s \<and>   global_mappings_of_all_processes s  \<Longrightarrow>
        \<forall>va\<in>kernel_safe s.  ptable_lift' (heap s) (root s) va = Some (Addr (addr_val va) r- global_offset)"
  by (clarsimp simp:  global_mappings_of_all_processes_def kernel_safe_def vas_mapped_by_global_mappings_def global_mappings_def
    vas_of_current_state_mapped_to_global_mappings_of_all_processes_def ) 

lemma global_mappings_ptable_lift_m:
  "\<lbrakk>\<exists>rt. root s = rt \<and> rt  \<in> root_log s ;
                        global_mappings_of_all_processes s;  va \<in> kernel_safe s\<rbrakk> \<Longrightarrow>
      ptable_lift_m (heap s) (root s) Kernel va = Some (Addr (addr_val va) r- global_offset) "
  by (clarsimp simp:  global_mappings_of_all_processes_def kernel_safe_def vas_mapped_by_global_mappings_def global_mappings_def)


lemma global_mappings_ptable_decode_heap_pde:
  "\<lbrakk>root s \<in> root_log s ;
                        global_mappings_of_all_processes s ; va \<in> kernel_safe s\<rbrakk> \<Longrightarrow> 
         \<exists>p perm. decode_heap_pde' (heap s) (root s r+ (vaddr_pd_index (addr_val va) << 2)) =  Some (SectionPDE p perm)"
  apply (clarsimp simp: kernel_safe_def vas_mapped_by_global_mappings_def global_mappings_of_all_processes_def pd_idx_offset_def get_pde'_def global_mappings_def)
  apply force
done


(* Page Tables *)

definition
  "ptable_footprint s rt \<equiv> \<Union>(ptable_trace' (heap s) rt ` UNIV)"

definition
  "page_tables_in_high_memory s \<equiv> ptable_footprint s (root s) \<subseteq> kernel_phy_mem"

abbreviation
  "non_overlapping_tables \<equiv> non_overlapping_defined_page_tables"

lemma non_overlapping_tables_def:
  "non_overlapping_tables s \<equiv> 
  \<forall>rt rt'. rt \<in> root_log s \<and> rt' \<in> root_log s \<and> rt \<noteq> rt' \<longrightarrow>
      ptable_footprint s rt \<inter> ptable_footprint s rt' = {}"
  by (auto simp: non_overlapping_defined_page_tables_def ptable_footprint_def)

definition
  "root_log_area = {root_log_low .. root_log_high}"

definition
  "kernel_data s \<equiv> [\<Union>(ptable_footprint s ` root_log s), root_log_area, root_map_area]"

abbreviation
  "kernel_data_area s \<equiv> \<Union> set (kernel_data s)"

definition
  "user_mappings s \<equiv> \<forall>rt \<in> root_log s. \<forall>va pa. ptable_lift_m (heap s) rt User va = Some pa \<longrightarrow> pa \<notin> kernel_phy_mem"

primrec non_overlapping where
  "non_overlapping [] = True" |
  "non_overlapping (x#xs) = ((x \<inter> \<Union>set xs = {}) \<and> non_overlapping xs)"

definition 
 "page_tables s  \<equiv> non_overlapping (kernel_data s) \<and> user_mappings s \<and> kernel_data_area s \<subseteq> kernel_phy_mem"


(* MMU *)

definition
  mmu_layout :: "p_state \<Rightarrow> bool"
where
  "mmu_layout s \<equiv>  
  kernel_data_area s \<subseteq> kernel_phy_mem \<and>
  non_overlapping_tables s \<and> non_overlapping (kernel_data s) \<and>
  root s \<in> root_log s \<and>
  root_map s (root s) = Some (asid s) \<and>
  global_mappings_of_all_processes s \<and> 
  user_mappings s \<and>
  partial_inj (root_map s)"



(*  kernel_safe_region preservation *)
definition
  "k_phy_ad vp = Addr vp r- global_offset"

lemma kernel_safe_region'_upd:
  "Addr vp \<in> kernel_safe s \<Longrightarrow> 
  kernel_safe (s \<lparr>p_state.heap := heap s (k_phy_ad vp \<mapsto> v)\<rparr>) = kernel_safe s"  
  oops (* something like this one would be nice to have and show in the paper, but not strictly necessary *)



lemma mmu_layout_pt_walk:
  "\<lbrakk> mmu_layout s; p \<notin> kernel_phy_mem; rt \<in> root_log s \<rbrakk> \<Longrightarrow>
  pt_walk a (heap s(p \<mapsto> v)) rt = pt_walk a (heap s) rt"
  apply (rule ext)
  apply (subst pt_walk_pt_trace_upd')
   apply (clarsimp simp: mmu_layout_def kernel_data_def ptable_footprint_def)
   apply fastforce
  apply simp
  done

lemma mmu_layout_ptable_comp:
  "\<lbrakk> mmu_layout s; p \<notin> kernel_phy_mem \<rbrakk> \<Longrightarrow> pde_comp' (asid s) (heap s) (heap s(p \<mapsto> v)) (root s) (root s) = {}"
  apply (simp add: pde_comp'_def)
  apply (subgoal_tac "root s \<in> root_log s")
   apply (simp add: mmu_layout_pt_walk)
  apply (simp add: mmu_layout_def)
  done

lemma ptable_footprint_upd:
  "p \<notin> ptable_footprint s rt \<Longrightarrow> 
   ptable_footprint (s\<lparr>p_state.heap := p_state.heap s(p \<mapsto> v)\<rparr>) rt = ptable_footprint s rt"
  by (simp add: ptable_footprint_def pt_trace_upd)

lemma ptable_footprint_upd_roots[simp]:
  "p \<notin> kernel_data_area s \<Longrightarrow> 
   ptable_footprint (s\<lparr>p_state.heap := p_state.heap s(p \<mapsto> v)\<rparr>) ` (root_log s) = ptable_footprint s ` (root_log s)"
  by (rule set_eqI) (clarsimp simp: kernel_data_def image_iff ptable_footprint_upd)

lemma root_log_upd[simp]:
  "p \<notin> kernel_data_area s \<Longrightarrow> root_log (s\<lparr>p_state.heap := heap s(p \<mapsto> v)\<rparr>) = root_log s"
  by (clarsimp simp: kernel_data_def root_log_def root_log_area_def)

lemma root_set_upd'[simp]:
  "p \<notin> root_map_area \<Longrightarrow> root_set (s\<lparr>p_state.heap := heap s(p \<mapsto> v)\<rparr>) = root_set s"
  using root_set_not_elem by auto

lemma root_set_upd[simp]:
  "p \<notin> kernel_data_area s \<Longrightarrow> root_set (s\<lparr>p_state.heap := heap s(p \<mapsto> v)\<rparr>) = root_set s"  
  by (clarsimp simp: kernel_data_def)

lemma root_map_upd[simp]:
  "p \<notin> kernel_data_area s \<Longrightarrow> root_map (s\<lparr>p_state.heap := heap s(p \<mapsto> v)\<rparr>) = root_map s"
  by (clarsimp simp: kernel_data_def root_map_def)


lemma root_map_upd'[simp]:
  "p \<notin> root_map_area \<Longrightarrow> root_map (s\<lparr>p_state.heap := heap s(p \<mapsto> v)\<rparr>) = root_map s"
  by (clarsimp simp: kernel_data_def root_map_def)

lemma kernel_data_upd:
  "p \<notin> kernel_data_area s \<Longrightarrow> kernel_data (s\<lparr>p_state.heap := heap s(p \<mapsto> v)\<rparr>) = kernel_data s"
  by (clarsimp simp: kernel_data_def)



lemma kernel_mapping_upd:
  "p \<notin> kernel_data_area s \<Longrightarrow> 
  global_mappings_of_all_processes (s\<lparr>p_state.heap := heap s(p \<mapsto> v)\<rparr>) =
      global_mappings_of_all_processes s"
  apply (clarsimp simp: kernel_data_def global_mappings_of_all_processes_def)
  apply safe
   apply (clarsimp simp: ptable_footprint_def)
   apply (clarsimp simp:global_mappings_def)
   apply (rule conjI)
    apply (rotate_tac) apply (rotate_tac)
    apply (drule_tac x = rt in bspec)
     apply clarsimp
    apply (drule_tac x = va in spec)
    apply clarsimp
    apply (rule_tac x = pa in exI)
    apply (rule_tac x = perms in exI)
    apply (frule ptable_trace_get_pde')
     apply force
    apply clarsimp
   apply (rotate_tac) apply (rotate_tac)
   apply (drule_tac x = rt in bspec)
    apply clarsimp
   apply (drule_tac x = va in spec)
   apply clarsimp
   apply (subgoal_tac "p \<notin> ptable_trace' (heap s) rt (Addr va)")
    apply (frule_tac v = v in pt_table_lift_trace_upd'')
    apply clarsimp
   apply force
  apply (clarsimp simp: ptable_footprint_def)
  apply (clarsimp simp:global_mappings_def)
  apply (rule conjI)
   apply (rotate_tac) apply (rotate_tac)
   apply (drule_tac x = rt in bspec)
    apply clarsimp
   apply (drule_tac x = va in spec)
   apply clarsimp
   apply (rule_tac x = pa in exI)
   apply (rule_tac x = perms in exI)
   apply clarsimp
   apply (rule ptable_trace_get_pde)
    apply force
   apply clarsimp
  apply (rotate_tac) apply (rotate_tac)
  apply (drule_tac x = rt in bspec)
   apply clarsimp
  apply (drule_tac x = va in spec)
  apply clarsimp
  apply (subgoal_tac "p \<notin> ptable_trace' (heap s) rt (Addr va)")
   apply (frule_tac v = v in pt_table_lift_trace_upd'')
   apply clarsimp
  by force



lemma mmu_layout_upd:
  "\<lbrakk> mmu_layout s; p \<notin> kernel_phy_mem \<rbrakk> \<Longrightarrow> mmu_layout (s\<lparr>p_state.heap := heap s(p \<mapsto> v)\<rparr>)"
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




(* to sort here *)


lemma pde_comp_asid_incon:
  "{av. (av \<in> incon_set s \<or> av \<in> pde_comp' (asid s) (heap s) (heap s(Addr (vp - global_offset) \<mapsto> v)) (root s) 
      (root s)) \<and> fst av \<noteq> asid s} =
   {av. av \<in> incon_set s  \<and> fst av \<noteq> asid s}"
  apply (clarsimp simp: pde_comp'_def)
  apply force
done

end