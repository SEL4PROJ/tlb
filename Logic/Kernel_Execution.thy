theory Kernel_Execution
                  
imports Memory_Model
        

begin  

lemma [simp]:
  "safe_memory S (s\<lparr>incon_set := IS, global_set := GS\<rparr>) =  safe_memory S s "
  by (clarsimp simp: safe_memory_def ptrace_set_def)


lemma [simp]:
  "con_set S (s\<lparr>heap := hp ,  incon_set := IS, global_set := GS\<rparr>) =  con_set S (s\<lparr>incon_set := IS\<rparr>) "
  by (clarsimp simp: con_set_def)

lemma [simp]:
  "kernel_data_area (s\<lparr>heap := hp', global_set := GS\<rparr>) = kernel_data_area (s\<lparr>heap := hp'\<rparr>)"
  by (clarsimp simp: kernel_data_area_def kernel_data_def ptable_footprint_def)
  

lemma [simp]:
  "kernel_data (s\<lparr>heap := hp', global_set := GS\<rparr>)  = kernel_data (s\<lparr>heap := hp'\<rparr>) "
  by (clarsimp simp: kernel_data_def ptable_footprint_def)
  

lemma [simp]:
  "kernel_mappings (s\<lparr>heap := hp', global_set := GS\<rparr>)  = kernel_mappings (s\<lparr>heap := hp'\<rparr>) "
  by (clarsimp simp: kernel_mappings_def global_mappings_def global_mappings'_def hptable_eq_def)
  


 lemma [simp]:
  "kernel_safe (s\<lparr>heap := hp',  global_set := GS \<rparr>) =
         kernel_safe (s\<lparr>heap := hp' \<rparr>) "
   by (clarsimp simp: kernel_safe_def vas_of_current_state_mapped_to_global_mappings_of_all_processes_def)


 lemma [simp]:
  "ptrace_set V (s\<lparr>heap := hp',  global_set := GS \<rparr>) =
         ptrace_set V (s\<lparr>heap := hp' \<rparr>) "
   by (clarsimp simp: ptrace_set_def)

 lemma [simp]:
  "root_map  (s\<lparr>heap := hp',  global_set := GS \<rparr>) =
         root_map  (s\<lparr>heap := hp' \<rparr>) "
 by (clarsimp simp: root_map_def  map_of_set_def  root_set_def)


lemma root_map_rootsD:
  "root_map s r = Some a \<Longrightarrow> r \<in> roots s"
  by (simp add: roots_def')

lemma kernel_region_offset':
  " mmu_layout s \<and> mode s = Kernel   \<Longrightarrow>
        \<forall>va\<in>kernel_safe s.  ptable_lift' (heap s) (root s) va = 
      Some (Addr (addr_val va) r- global_offset)"
  by (clarsimp simp: mmu_layout_def dest!: root_map_rootsD)



lemma mmu_layout_ptable_comp':
  "\<lbrakk> mmu_layout s; p \<notin> kernel_data_area s \<rbrakk> \<Longrightarrow> 
        incon_comp (asid s) (asid s) (heap s) (heap s(p \<mapsto> v)) (root s) (root s) = {}"
  apply (simp add: incon_comp_def ptable_comp_def)
  apply (subgoal_tac "root s \<in> roots s")
   apply (simp add: mmu_layout_pt_walk_pair')
  by (clarsimp simp: mmu_layout_def rootsI)


lemma global_mappings_decode_mmu:
  "\<lbrakk>mmu_layout s ; mode s = Kernel  ; va \<in> kernel_safe s\<rbrakk> \<Longrightarrow> 
         \<exists>p perm. decode_pde (the ((heap s) 
          (root s r+ (vaddr_pd_index (addr_val va) << 2)))) =  SectionPDE p perm"
  apply (clarsimp simp: kernel_safe_def vas_mapped_by_global_mappings_def
                         kernel_mappings_def global_mappings_def global_mappings'_def  mmu_layout_def dest!: root_map_rootsD)
  apply (drule_tac x = "root s" in bspec)
   apply clarsimp
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
  vas_of_current_state_mapped_to_global_mappings_of_all_processes_def dest!: root_map_rootsD)
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
        pd_idx_offset_def dest!: root_map_rootsD)
  done


lemma mmu_layout_pt_comp_heap_same[simp]:
  "\<lbrakk> mmu_layout s; p \<notin> kernel_data_area s ; r \<in> roots s\<rbrakk>
       \<Longrightarrow> ptable_comp (snd (ptable_snapshot s a)) (pt_walk_pair a (heap s) r) = 
         ptable_comp (snd (ptable_snapshot s a)) (pt_walk_pair a (heap s(p \<mapsto> v)) r)"
  apply (subgoal_tac "pt_walk_pair a (heap s(p \<mapsto> v)) r = pt_walk_pair a (heap s) r")
   apply clarsimp
  by (rule mmu_layout_pt_walk_pair'; simp)


lemma mmu_layout_global_heap_upd:
  "\<lbrakk>mmu_layout s; p \<notin> kernel_data_area s\<rbrakk>
         \<Longrightarrow> global_entries (ran (pt_walk (asid s) (heap s(p \<mapsto> v)) (root s))) = global_entries (ran (pt_walk (asid s) (heap s) (root s)))"
  apply (subgoal_tac "pt_walk (asid s) (heap s(p \<mapsto> v)) (root s) = pt_walk (asid s)  (heap s) (root s)")
   apply (clarsimp)
  apply (subst mmu_layout_pt_walk'; simp?)
  apply (clarsimp simp: mmu_layout_def roots_def)
  using rootsI roots_def by blast


lemma mmu_layout_global_set_subset':
  "\<lbrakk>mmu_layout s ; rt \<in> roots s \<rbrakk> \<Longrightarrow>   (\<Union>x\<in>global_entries (ran (pt_walk a (heap s) rt)). range_of x) = 
           {va::vaddr. rt r+ pd_idx_offset (addr_val va) \<in> high_ptable rt}"
  apply safe
   apply (rename_tac va e)
   apply (subgoal_tac "global (heap s) rt va \<and> (\<exists>e. pt_walk a (heap s) rt va = Some e)")
    apply (clarsimp simp: mmu_layout_def kernel_mappings_def global_mappings_def global_mappings'_def)
    apply (drule_tac x = rt in bspec, simp, clarsimp)
    apply (drule_tac x = "addr_val va" in spec, drule_tac x = "addr_val va" in spec)
    apply (case_tac " rt r+ pd_idx_offset (addr_val va) \<in> high_ptable rt"; clarsimp)
    apply (clarsimp simp: global_def non_global_def is_fault_def pt_walk_def map_opt_def pdc_walk_def  pte_tlb_entry_def
      split: option.splits pde.splits pte.splits)
   apply (subgoal_tac "\<exists>v'. e = the (pt_walk a (heap s) rt v') \<and>(\<exists>e. pt_walk a (heap s) rt v' = Some e)")
    prefer 2
    apply (clarsimp simp:  global_entries_def ran_def is_fault_def)
    apply force
   apply clarsimp
   apply (subgoal_tac "(\<exists>e. pt_walk a (heap s) rt v' = Some e)")
    prefer 2
    apply (clarsimp simp: global_entries_def  ran_def) 
   apply (subgoal_tac "pt_walk a (heap s) rt v' = pt_walk a (heap s) rt va")
    apply clarsimp
    apply (subgoal_tac "asid_of (the (pt_walk a (heap s) rt va)) = None")
     prefer 2
     apply (clarsimp simp: global_entries_def)
    apply (clarsimp simp: mmu_layout_def kernel_mappings_def global_mappings_def global_mappings'_def)
    apply (drule_tac x = rt in bspec, simp, clarsimp)
    apply (drule_tac x = "addr_val va" in spec, drule_tac x = "addr_val va" in spec)
    apply (case_tac " rt r+ pd_idx_offset (addr_val va) \<in> high_ptable rt"; clarsimp)
     apply (clarsimp simp: global_def non_global_def is_fault_def pt_walk_def map_opt_def pdc_walk_def  pte_tlb_entry_def
      split: option.splits pde.splits pte.splits)
    apply (clarsimp simp: global_def non_global_def is_fault_def pt_walk_def map_opt_def pdc_walk_def  global_entries_def tag_conv_def 
      pte_tlb_entry_def to_tlb_flags_def split: option.splits pde.splits pte.splits)
   apply (rule va_entry_set_pt_palk_same', simp add: is_fault_def, simp)
  apply clarsimp
  apply (rename_tac va)
  apply (subgoal_tac "global (heap s) rt va \<and> \<not>is_fault (pt_walk a (heap s) rt va)")
   apply (rule_tac x = "the (pt_walk a (heap s) rt va)" in bexI, clarsimp)
    apply (simp add: pt_walk'_pt_walk [symmetric])
    apply (frule asid_va_entry_range_pt_entry, simp)
   apply (subgoal_tac "asid_of (the (pt_walk a (heap s) rt va)) = None")
    apply (clarsimp simp: global_entries_def is_fault_def ran_def) apply force
   apply (clarsimp simp: global_def  is_fault_def pt_walk_def map_opt_def pdc_walk_def  pte_tlb_entry_def tag_conv_def to_tlb_flags_def
      split: option.splits pde.splits pte.splits)
  apply (clarsimp simp: mmu_layout_def kernel_mappings_def global_mappings_def global_mappings'_def)
  apply (drule_tac x = rt in bspec, simp, clarsimp)
  apply (drule_tac x = "addr_val va" in spec, drule_tac x = "addr_val va" in spec)
  by (clarsimp simp: global_def non_global_def is_fault_def pt_walk_def map_opt_def pdc_walk_def  pte_tlb_entry_def
      split: option.splits pde.splits pte.splits)


lemma mmu_layout_global_set_subset:
  "mmu_layout s \<Longrightarrow>   (\<Union>x\<in>global_entries (ran (pt_walk (asid s) (heap s) (root s))). range_of x) = global_set s "
  apply (frule_tac rt = "root s"  and a = "asid s" in mmu_layout_global_set_subset') 
  using mmu_layout_def rootsI apply force
  by (clarsimp simp: mmu_layout_def  global_set_eq_def)
  



lemma kernel_safe_assignment:
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
   apply (clarsimp simp: kernel_region_offset')
  apply (clarsimp simp: k_phy_ad_def mmu_layout_ptable_comp' mmu_layout_upd')
  apply (rule conjI)
   apply (clarsimp simp: mmu_layout_global_heap_upd)
   apply (frule_tac mmu_layout_global_set_subset, simp)
   apply (clarsimp simp: k_phy_ad_def mmu_layout_ptable_comp' mmu_layout_upd') 
  apply (rule conjI)
   apply (subgoal_tac  "kernel_safe (s\<lparr> heap := heap s(Addr (vp - global_offset) \<mapsto> v)\<rparr>) =
                        kernel_safe s")
    apply (clarsimp simp: safe_set_def safe_memory_def con_set_def)
    apply (drule_tac x = va in bspec; clarsimp)
    apply (rule_tac x = p in exI)
    apply (subgoal_tac "ptable_lift' (heap s) (root s) va = 
                      ptable_lift' (heap s(Addr (vp -  global_offset) \<mapsto> v)) (root s) va")
     apply (rule conjI, clarsimp)
     apply (subgoal_tac  "ptrace_set (kernel_safe s) (s\<lparr> heap := heap s(Addr (vp - global_offset) \<mapsto> v)\<rparr>) =
                           ptrace_set (kernel_safe s) s", clarsimp)
     prefer 3
     apply (frule_tac vp = vp in global_high_ptable', clarsimp, clarsimp)
     apply (clarsimp simp: kernel_safe_def  vas_of_current_state_mapped_to_global_mappings_of_all_processes_def)
     apply (rule_tac x = "root s" in bexI, force)
     apply (clarsimp simp: mmu_layout_def dest!: root_map_rootsD)
    prefer 2 apply (rule pt_table_lift_trace_upd', clarsimp)
   apply (clarsimp simp: ptrace_set_def)
   apply safe
    apply (rule_tac a = xa in UN_I, clarsimp)
    prefer 2 apply (rule_tac a = xa in UN_I, clarsimp)
    apply (subgoal_tac "ptable_trace' (heap s(Addr (vp - global_offset) \<mapsto> v)) (root s) xa =
                       ptable_trace' (heap s) (root s) xa", clarsimp)
    prefer 2
    apply (subgoal_tac "ptable_trace' (heap s(Addr (vp - global_offset) \<mapsto> v)) (root s) xa =
                       ptable_trace' (heap s) (root s) xa" , clarsimp)
    apply (rule pt_trace_upd, clarsimp)
   apply (subgoal_tac "ptable_trace' (heap s(Addr (vp - global_offset) \<mapsto> v)) (root s) xa =
                      ptable_trace' (heap s) (root s) xa" , clarsimp)
   apply (rule pt_trace_upd, clarsimp)
  apply (frule_tac mmu_layout_global_set_subset)
  apply (subgoal_tac "(s\<lparr>heap := heap s(Addr (vp - global_offset) \<mapsto> v),
                   global_set := global_set s \<union> (\<Union>x\<in>global_entries (ran (pt_walk (asid s) (heap s(Addr (vp - global_offset) \<mapsto> v)) (root s))). range_of x)\<rparr>) =
   s\<lparr>heap := heap s(Addr (vp - global_offset) \<mapsto> v)\<rparr>")
   apply simp
   apply (clarsimp simp: asids_consistent_def)
   apply (rule)
    apply clarsimp
    apply (subgoal_tac "pt_walk_pair a (heap s(Addr (vp - global_offset) \<mapsto> v)) r = pt_walk_pair a (heap s) r")
     apply force
    apply (rule mmu_layout_pt_walk_pair', simp, simp, simp add: roots_def) 
  using root_map_rootsD roots_def apply force
   apply clarsimp
   apply (subgoal_tac "pt_walk_pair a (heap s(Addr (vp - global_offset) \<mapsto> v)) r = pt_walk_pair a (heap s) r")
    apply force
   apply (rule mmu_layout_pt_walk_pair'; simp add: roots_def) 
  apply (subgoal_tac "pt_walk (asid s) (heap s(Addr (vp - global_offset) \<mapsto> v)) (root s) = pt_walk (asid s) (heap s) (root s)")
   apply clarsimp
  apply (rule mmu_layout_pt_walk'; simp add: roots_def)
  using mmu_layout_def rootsI roots_def by auto


end

