theory Memory_Model
imports Word_Lib.Word_Lemmas_32 RT_Log
begin               

consts kernel_window_lower_bound :: "32 word"
consts kernel_window_upper_bound :: "32 word"
consts global_offset             :: "32 word"
consts ker_phy_lower_bound       :: "paddr"
consts ker_phy_upper_bound       :: "paddr"


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


(*making nG bit zero  *)

definition
  "global hp rt va \<equiv>  (\<forall> bpa perms. get_pde' hp rt va = Some (SectionPDE bpa perms) \<longrightarrow> arm_p_nG perms = 0) \<and>
                   (\<forall>p bpa perms. (get_pde' hp rt va = Some (PageTablePDE p) \<and> get_pte' hp p va =  Some (SmallPagePTE bpa perms)) \<longrightarrow> arm_p_nG perms = 0)"



definition
  vas_mapped_by_global_mappings :: "paddr \<Rightarrow> vaddr set"
where
  "vas_mapped_by_global_mappings r \<equiv> Addr ` {va. r r+ pd_idx_offset va \<in>
          high_ptable r }"


definition
  "non_global hp rt va \<equiv>  (\<forall> bpa perms. get_pde' hp rt va = Some (SectionPDE bpa perms) \<longrightarrow> arm_p_nG perms = 1) \<and>
                   (\<forall>p bpa perms. (get_pde' hp rt va = Some (PageTablePDE p) \<and> get_pte' hp p va =  Some (SmallPagePTE bpa perms)) \<longrightarrow> arm_p_nG perms = 1)"

definition
  global_mappings' :: "heap \<Rightarrow> paddr  \<Rightarrow> bool"
where
  "global_mappings' h r  \<equiv>
     (\<forall>va. r r+ pd_idx_offset va \<in> high_ptable r \<longrightarrow>                                      
                (\<exists>p perms. get_pde' h r (Addr va) = Some (SectionPDE p perms) \<and> arm_p_nG perms = 0 \<and>  \<not>user_perms perms ) \<and>
                 ptable_lift_m h r Kernel (Addr va)  =  Some (Addr va r- global_offset) \<and> 
                       (Addr va r- global_offset) \<in> kernel_phy_mem)

    \<and> ( \<forall>va. r r+ pd_idx_offset va \<notin> high_ptable r \<longrightarrow> non_global h r (Addr va))"


definition
  global_mappings :: _
where
  "global_mappings s  \<equiv> (\<forall>rt\<in>roots s. global_mappings' (heap s) rt)"


definition
  hptable_eq :: "p_state  \<Rightarrow> bool"
where
  "hptable_eq s  \<equiv> \<forall>rt rt'. rt\<in>roots s \<and>rt'\<in>roots s \<longrightarrow>  
        (\<forall>va. rt r+ pd_idx_offset va \<in> high_ptable rt \<longrightarrow>  
            get_pde' (heap s) rt (Addr va) = get_pde' (heap s) rt' (Addr va))"


definition "pd_bits = (14 :: nat)"

definition "kwindow_bound  \<equiv> kernel_window_lower_bound < 2 ^ pd_bits \<and> kernel_window_upper_bound < 2 ^ pd_bits"



definition
  kernel_mappings :: "p_state  \<Rightarrow> bool"
where
  "kernel_mappings s  \<equiv> kwindow_bound \<and> hptable_eq s  \<and> global_mappings s"



definition
  vas_of_current_state_mapped_to_global_mappings_of_all_processes :: "p_state \<Rightarrow> vaddr set"
where
  "vas_of_current_state_mapped_to_global_mappings_of_all_processes s = 
         {va\<in>vas_mapped_by_global_mappings (root s). 
    ptable_trace' (heap s) (root s) va \<subseteq> \<Union>(high_ptable ` roots s)}"


definition                   
  kernel_safe :: "p_state \<Rightarrow> vaddr set"
where
  "kernel_safe s = vas_mapped_by_global_mappings (root s) -
 vas_of_current_state_mapped_to_global_mappings_of_all_processes s"


lemma global_mappings_ptable_lift' [simp]:
  "\<exists>rt. root s = rt \<and> mode s = Kernel \<and>  rt \<in> roots s \<and>   kernel_mappings s  \<Longrightarrow>
        \<forall>va\<in>kernel_safe s.  ptable_lift' (heap s) (root s) va = Some (Addr (addr_val va) r- global_offset)"
  by (clarsimp simp:  kernel_mappings_def kernel_safe_def vas_mapped_by_global_mappings_def 
         kernel_mappings_def global_mappings_def global_mappings'_def
    vas_of_current_state_mapped_to_global_mappings_of_all_processes_def ) 

lemma global_mappings_ptable_lift_m:
  "\<lbrakk>\<exists>rt. root s = rt \<and> rt  \<in> roots s;
                        kernel_mappings s;  va \<in> kernel_safe s\<rbrakk> \<Longrightarrow>
      ptable_lift_m (heap s) (root s) Kernel va = Some (Addr (addr_val va) r- global_offset) "
  by (clarsimp simp:  kernel_mappings_def kernel_safe_def vas_mapped_by_global_mappings_def kernel_mappings_def 
    global_mappings_def global_mappings'_def)


lemma global_mappings_ptable_decode_heap_pde:
  "\<lbrakk>root s \<in> roots s; kernel_mappings s ; va \<in> kernel_safe s\<rbrakk> \<Longrightarrow> 
         \<exists>p perm. decode_heap_pde' (heap s) (root s r+ (vaddr_pd_index (addr_val va) << 2)) =  Some (SectionPDE p perm)"
  apply (clarsimp simp: kernel_safe_def vas_mapped_by_global_mappings_def 
       kernel_mappings_def global_mappings_def global_mappings'_def pd_idx_offset_def get_pde'_def global_mappings_def)
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
  \<forall>rt rt'. rt \<in> roots s \<and> rt' \<in> roots s \<and> rt \<noteq> rt' \<longrightarrow>
      ptable_footprint s rt \<inter> ptable_footprint s rt' = {}"
  by (auto simp: non_overlapping_defined_page_tables_def ptable_footprint_def)

(*
definition
  "root_log_area = set root_log_fp"
*)

definition
  "kernel_data s \<equiv> map (ptable_footprint s) (root_log s) @ [root_map_area]"

definition
  "kernel_data_area s \<equiv> \<Union> (set (kernel_data s))"



definition
  "user_mappings s \<equiv> \<forall>rt \<in> roots s. \<forall>va pa. ptable_lift_m (heap s) rt User va = Some pa \<longrightarrow> 
                       (pa \<notin> kernel_phy_mem \<and> non_global (heap s) rt va)"

definition "global_set_eq' s \<equiv>  
             (\<Union>x\<in>global_entries (the ` {e \<in> range (pt_walk (asid s) (heap s) (root s)). \<not> is_fault e}). range_of x) =
                global_set s"


lemma
  " \<lbrakk>user_mappings s ;  rt \<in> roots s\<rbrakk>  \<Longrightarrow> \<forall>va. 
         ptable_lift_m (heap s) rt User va = Some pa \<longrightarrow> non_global (heap s) rt va"
  by (clarsimp simp: user_mappings_def )



fun non_overlapping where
  "non_overlapping [] = True" |
  "non_overlapping (x#xs) = ((x \<inter> \<Union> (set xs) = {}) \<and> non_overlapping xs)"

definition 
 "page_tables s  \<equiv> non_overlapping (kernel_data s) \<and> user_mappings s \<and> kernel_data_area s \<subseteq> kernel_phy_mem"


lemma non_overlapping_append[simp]:
  "non_overlapping (xs @ ys) = (non_overlapping xs \<and> non_overlapping ys \<and> \<Union>(set xs) \<inter> \<Union>(set ys) = {})"
  by (induct xs) auto

lemma non_overlapping_map:
  "\<lbrakk> non_overlapping (map f xs); x \<in> set xs; y \<in> set xs; x \<noteq> y\<rbrakk> \<Longrightarrow> f x \<inter> f y = {}"
  by (induct xs) auto

lemma non_overlapping_tables_from_kernel_data:
  "non_overlapping (kernel_data s) \<Longrightarrow> non_overlapping_tables s"
  by (clarsimp simp: non_overlapping_tables_def kernel_data_def non_overlapping_map roots_def)


(*
find_consts "('a \<Rightarrow> 'b option) \<Rightarrow> ('b \<Rightarrow> 'c option)"
thm map_comp_def
*)

definition "global_set_eq s \<equiv>  {va. root s r+ pd_idx_offset (addr_val va) \<in> high_ptable (root s)} = global_set s "

(* MMU *)


definition
  "aligned (rts :: paddr set) \<equiv> \<forall>rt\<in>rts. is_aligned (addr_val rt) pd_bits"


definition
  mmu_layout :: "p_state \<Rightarrow> bool"
where
  "mmu_layout s \<equiv>  
  kernel_data_area s \<subseteq> kernel_phy_mem \<and>
  non_overlapping (kernel_data s) \<and>
  aligned (roots s) \<and>
  root_map s (root s) = Some (asid s) \<and>
  kernel_mappings s \<and> 
  user_mappings s \<and>
  partial_inj (root_map s) \<and>
  global_set_eq s"

(*  kernel_safe_region preservation *)
definition
  "k_phy_ad vp = Addr vp r- global_offset"


lemma mmu_layout_pt_walk':
  "\<lbrakk> mmu_layout s; p \<notin> kernel_data_area s; rt \<in> roots s \<rbrakk> \<Longrightarrow>
  pt_walk a (heap s(p \<mapsto> v)) rt = pt_walk a (heap s) rt"
  apply (rule ext)
  apply (subst pt_walk_pt_trace_upd')
   apply (clarsimp simp: mmu_layout_def kernel_data_def kernel_data_area_def ptable_footprint_def roots_def)
  apply simp
  done

lemma mmu_layout_pt_walk:
  "\<lbrakk> mmu_layout s; p \<notin> kernel_phy_mem; rt \<in> roots s \<rbrakk> \<Longrightarrow>
  pt_walk a (heap s(p \<mapsto> v)) rt = pt_walk a (heap s) rt"
  apply (rule mmu_layout_pt_walk'; assumption?)
  apply (auto simp: mmu_layout_def)
  done


lemma mmu_layout_pt_walk_pair':
  "\<lbrakk> mmu_layout s; p \<notin> kernel_data_area s; rt \<in> roots s \<rbrakk> \<Longrightarrow>
  pt_walk_pair a (heap s(p \<mapsto> v)) rt = pt_walk_pair a (heap s) rt"
  apply (rule ext)
  apply (subst pt_walk_pair_pt_trace_upd')
   apply (clarsimp simp: mmu_layout_def kernel_data_def kernel_data_area_def ptable_footprint_def roots_def)
  apply simp
  done


lemma mmu_layout_pt_walk_pair:
  "\<lbrakk> mmu_layout s; p \<notin> kernel_phy_mem; rt \<in> roots s \<rbrakk> \<Longrightarrow>
  pt_walk_pair a (heap s(p \<mapsto> v)) rt = pt_walk_pair a (heap s) rt"
  apply (rule mmu_layout_pt_walk_pair'; assumption?)
  apply (auto simp: mmu_layout_def)
  done

lemma rootsI:
  "root_map s r \<noteq> None \<Longrightarrow> r \<in> roots s"
  by (simp add: roots_def')

lemma mmu_layout_ptable_comp:
  "\<lbrakk> mmu_layout s; p \<notin> kernel_phy_mem \<rbrakk> \<Longrightarrow> incon_comp (asid s) (asid s)(heap s) (heap s(p \<mapsto> v)) (root s) (root s) = {}"
  apply (simp add: incon_comp_def)
  apply (subgoal_tac "root s \<in> roots s")
   apply (simp add: mmu_layout_pt_walk_pair ptable_comp_def)
  apply (clarsimp simp: mmu_layout_def intro!: rootsI)
  done

lemma ptable_footprint_upd:
  "p \<notin> ptable_footprint s rt \<Longrightarrow> 
   ptable_footprint (s\<lparr>p_state.heap := p_state.heap s(p \<mapsto> v)\<rparr>) rt = ptable_footprint s rt"
  by (simp add: ptable_footprint_def pt_trace_upd)

lemma root_set_upd[simp]:
  "p \<notin> kernel_data_area s \<Longrightarrow> root_set (s\<lparr>p_state.heap := heap s(p \<mapsto> v)\<rparr>) = root_set s"  
  by (clarsimp simp: kernel_data_area_def kernel_data_def root_set_not_elem[symmetric])

lemma root_set_upd'[simp]:
  "p \<notin> root_map_area \<Longrightarrow> root_set (s\<lparr>p_state.heap := heap s(p \<mapsto> v)\<rparr>) = root_set s"
  using root_set_not_elem by auto

lemma root_map_upd[simp]:
  "p \<notin> kernel_data_area s \<Longrightarrow> root_map (s\<lparr>p_state.heap := heap s(p \<mapsto> v)\<rparr>) = root_map s"
  by (clarsimp simp: kernel_data_area_def root_map_def)

lemma root_map_upd'[simp]:
  "p \<notin> root_map_area \<Longrightarrow> root_map (s\<lparr>p_state.heap := heap s(p \<mapsto> v)\<rparr>) = root_map s"
  by (clarsimp simp: kernel_data_area_def root_map_def)

lemma roots_upd[simp]:
  "p \<notin> kernel_data_area s \<Longrightarrow> roots (s\<lparr>p_state.heap := heap s(p \<mapsto> v)\<rparr>) = roots s"
  by (clarsimp simp: kernel_data_area_def roots_def')

lemma roots_upd'[simp]:
  "p \<notin> root_map_area \<Longrightarrow> roots (s\<lparr>p_state.heap := heap s(p \<mapsto> v)\<rparr>) = roots s"
  by (clarsimp simp: kernel_data_area_def roots_def')

lemma ptable_footprint_upd_roots[simp]:
  "p \<notin> kernel_data_area s \<Longrightarrow> 
   ptable_footprint (s\<lparr>p_state.heap := p_state.heap s(p \<mapsto> v)\<rparr>) ` (roots s) = ptable_footprint s ` (roots s)"
  by (rule set_eqI) (clarsimp simp: kernel_data_def kernel_data_area_def image_iff ptable_footprint_upd roots_def)

lemma root_log_upd[simp]:
  "p \<notin> kernel_data_area s \<Longrightarrow> root_log (s\<lparr>p_state.heap := heap s(p \<mapsto> v)\<rparr>) = root_log s"
  by (clarsimp simp: kernel_data_area_def root_log_def)
 
lemma kernel_data_upd:
  "p \<notin> kernel_data_area s \<Longrightarrow> kernel_data (s\<lparr>p_state.heap := heap s(p \<mapsto> v)\<rparr>) = kernel_data s"
  by (clarsimp simp: kernel_data_def kernel_data_area_def ptable_footprint_upd) 

lemma kernel_data_area_upd:
  "p \<notin> kernel_data_area s \<Longrightarrow> kernel_data_area (s\<lparr>p_state.heap := heap s(p \<mapsto> v)\<rparr>) = kernel_data_area s"
  by (clarsimp simp: kernel_data_area_def kernel_data_upd) 


lemma  kernel_data_area_ptrace:
 "\<lbrakk>p \<notin> kernel_data_area s; rt \<in> roots s\<rbrakk>
       \<Longrightarrow> p \<notin> ptable_trace' (heap s) rt va "
  by (clarsimp simp: kernel_data_area_def kernel_data_def ptable_footprint_def roots_def)
 
lemma  kernel_data_area_ptrace':
 "\<lbrakk>p \<notin> kernel_data_area s; rt \<in> roots s\<rbrakk>
       \<Longrightarrow> p \<notin> ptable_trace' (heap s (p \<mapsto> v)) rt va "
  apply (clarsimp simp: kernel_data_area_def kernel_data_def ptable_footprint_def roots_def)
  using pt_trace_upd by blast


lemma kernel_data_global_map_update [simp]:
  "p \<notin> kernel_data_area s \<Longrightarrow>  
   global_mappings s = global_mappings (s\<lparr>heap := heap s(p \<mapsto> v)\<rparr>)"
  apply safe
   apply (clarsimp simp: global_mappings_def global_mappings'_def)
   apply (drule_tac x = rt in bspec, simp)
   apply (clarsimp)
   apply (rule conjI)
    apply clarsimp
    apply (subgoal_tac "p \<notin> ptable_trace' (heap s) rt (Addr va)")
  using pt_table_lift_trace_upd'' ptable_trace_get_pde apply auto[1]
    apply (rule kernel_data_area_ptrace; simp)
   apply clarsimp
   apply (subgoal_tac "p \<notin> ptable_trace' (heap s) rt (Addr va)")
    apply (clarsimp simp: non_global_def)
    apply (rule conjI)
  using ptable_trace_get_pde' apply blast
    apply (clarsimp)
    apply (thin_tac " \<forall>va. rt r+ pd_idx_offset va \<in> high_ptable rt \<longrightarrow>
             (\<exists>p perms. get_pde' (heap s) rt (Addr va) = Some (SectionPDE p perms) \<and> arm_p_nG perms = 0 \<and> \<not> user_perms perms) \<and>
             ptable_lift' (heap s) rt (Addr va) = Some (Addr (va - global_offset)) \<and> Addr (va - global_offset) \<in> kernel_phy_mem")
    apply (drule_tac x = "va" in spec, clarsimp)
    apply (subgoal_tac " get_pde' (heap s(p \<mapsto> v)) rt (Addr va) =  get_pde' (heap s) rt (Addr va)")
     apply clarsimp
     apply (subgoal_tac "get_pte' (heap s) pa (Addr va) = get_pte' (heap s(p \<mapsto> v)) pa (Addr va)")
      apply clarsimp
     apply (subgoal_tac " p \<notin> ptable_trace' (heap s) rt (Addr va)")
      apply (clarsimp simp: get_pte'_def get_pde'_def decode_heap_pde'_def ptable_trace'_def Let_def
      decode_heap_pte'_def)
     apply (rule kernel_data_area_ptrace, simp, simp)
    apply (metis ptable_trace_get_pde')
   apply (rule kernel_data_area_ptrace, simp, simp)
   apply (clarsimp simp: global_mappings_def global_mappings'_def)
   apply (drule_tac x = rt in bspec, simp)
   apply (clarsimp)
   apply (rule conjI)
    apply clarsimp
    apply (subgoal_tac "p \<notin> ptable_trace' (heap s(p \<mapsto> v)) rt (Addr va)")
  apply (metis kernel_data_area_ptrace pt_table_lift_trace_upd' ptable_trace_get_pde')
    apply (rule kernel_data_area_ptrace'; simp)
   apply clarsimp
   apply (subgoal_tac "p \<notin> ptable_trace' (heap s(p \<mapsto> v)) rt (Addr va)")
    apply (clarsimp simp: non_global_def)
   apply (rule conjI)
  apply (simp add: kernel_data_area_ptrace ptable_trace_get_pde)
    apply (clarsimp)
    apply (thin_tac "  \<forall>va. rt r+ pd_idx_offset va \<in> high_ptable rt \<longrightarrow>
             (\<exists>pa perms. get_pde' (heap s(p \<mapsto> v)) rt (Addr va) = Some (SectionPDE pa perms) \<and> arm_p_nG perms = 0 \<and> \<not> user_perms perms) \<and>
             ptable_lift' (heap s(p \<mapsto> v)) rt (Addr va) = Some (Addr (va - global_offset)) \<and> Addr (va - global_offset) \<in> kernel_phy_mem")
    apply (drule_tac x = "va" in spec, clarsimp)
    apply (subgoal_tac " get_pde' (heap s(p \<mapsto> v)) rt (Addr va) =  get_pde' (heap s) rt (Addr va)")
     apply clarsimp
     apply (subgoal_tac "get_pte' (heap s) pa (Addr va) = get_pte' (heap s(p \<mapsto> v)) pa (Addr va)")
      apply clarsimp
     apply (subgoal_tac " p \<notin> ptable_trace' (heap s(p \<mapsto> v)) rt (Addr va)")
      apply (clarsimp simp: get_pte'_def get_pde'_def decode_heap_pde'_def ptable_trace'_def Let_def
      decode_heap_pte'_def)
     apply (rule kernel_data_area_ptrace', simp, simp)
  apply (simp add: kernel_data_area_ptrace ptable_trace_get_pde)
  by (rule kernel_data_area_ptrace', simp, simp)
                        

 

lemma kerenl_data_global_mappings [simp]:
  "p \<notin> kernel_data_area s \<Longrightarrow>  
   hptable_eq s = hptable_eq (s\<lparr>heap := heap s(p \<mapsto> v)\<rparr>)"
  apply (safe)
   apply (clarsimp simp: hptable_eq_def)
   apply (subgoal_tac "get_pde' (heap s(p \<mapsto> v)) rt (Addr va) = get_pde' (heap s) rt (Addr va)")
    apply (subgoal_tac "get_pde' (heap s(p \<mapsto> v)) rt' (Addr va) = get_pde' (heap s) rt' (Addr va)")
     apply presburger
    apply (thin_tac "\<forall>rt rt'. rt \<in> roots s \<and> rt' \<in> roots s \<longrightarrow> (\<forall>va. rt r+ pd_idx_offset va \<in> high_ptable rt \<longrightarrow> get_pde' (heap s) rt (Addr va) = get_pde' (heap s) rt' (Addr va))")
    apply (subgoal_tac " p \<notin> ptable_trace' (heap s) rt' (Addr va)")
     apply (clarsimp simp: ptable_trace'_def get_pde'_def Let_def decode_heap_pde'_def split: pde.splits)
    apply (rule kernel_data_area_ptrace, simp, simp)
   apply (thin_tac "\<forall>rt rt'. rt \<in> roots s \<and> rt' \<in> roots s \<longrightarrow> (\<forall>va. rt r+ pd_idx_offset va \<in> high_ptable rt \<longrightarrow> get_pde' (heap s) rt (Addr va) = get_pde' (heap s) rt' (Addr va))")
   apply (subgoal_tac " p \<notin> ptable_trace' (heap s) rt (Addr va)")
    apply (clarsimp simp: ptable_trace'_def get_pde'_def Let_def decode_heap_pde'_def split: pde.splits)
   apply (rule kernel_data_area_ptrace, simp, simp)
  apply (clarsimp simp: hptable_eq_def)
  apply (subgoal_tac "get_pde' (heap s(p \<mapsto> v)) rt (Addr va) = get_pde' (heap s) rt (Addr va)")
   apply (subgoal_tac "get_pde' (heap s(p \<mapsto> v)) rt' (Addr va) = get_pde' (heap s) rt' (Addr va)")
    apply presburger
   apply (thin_tac "\<forall>rt rt'.
           rt \<in> roots s \<and> rt' \<in> roots s \<longrightarrow> (\<forall>va. rt r+ pd_idx_offset va \<in> high_ptable rt \<longrightarrow> get_pde' (heap s(p \<mapsto> v)) rt (Addr va) = get_pde' (heap s(p \<mapsto> v)) rt' (Addr va))")
   apply (subgoal_tac " p \<notin> ptable_trace' (heap s) rt' (Addr va)")
    apply (clarsimp simp: ptable_trace'_def get_pde'_def Let_def decode_heap_pde'_def split: pde.splits)
   apply (rule kernel_data_area_ptrace, simp, simp)
  apply (thin_tac "\<forall>rt rt'.
           rt \<in> roots s \<and> rt' \<in> roots s \<longrightarrow> (\<forall>va. rt r+ pd_idx_offset va \<in> high_ptable rt \<longrightarrow> get_pde' (heap s(p \<mapsto> v)) rt (Addr va) = get_pde' (heap s(p \<mapsto> v)) rt' (Addr va))")
  apply (subgoal_tac " p \<notin> ptable_trace' (heap s) rt (Addr va)")
   apply (clarsimp simp: ptable_trace'_def get_pde'_def Let_def decode_heap_pde'_def split: pde.splits)
  by (rule kernel_data_area_ptrace, simp, simp)
  


lemma kernel_data_area_non_global[simp]:
  "\<lbrakk>p \<notin> kernel_data_area s ; rt \<in> roots s\<rbrakk> \<Longrightarrow>
            non_global (heap (s\<lparr>p_state.heap := heap s(p \<mapsto> v)\<rparr>)) rt va = non_global (heap s) rt va"
  apply (subgoal_tac "get_pde' (heap s) rt va = get_pde' (heap s(p \<mapsto> v)) rt va")
   apply safe
    apply (clarsimp simp: non_global_def)
    apply (subgoal_tac "get_pte' (heap s) pa va = get_pte' (heap s(p \<mapsto> v)) pa va")
     apply clarsimp
    apply (subgoal_tac " p \<notin> ptable_trace' (heap s(p \<mapsto> v)) rt va")
     apply (clarsimp simp: get_pte'_def get_pde'_def decode_heap_pde'_def ptable_trace'_def Let_def
      decode_heap_pte'_def)
    apply (rule kernel_data_area_ptrace', simp, simp)
   apply (clarsimp simp: non_global_def)
   apply (subgoal_tac "get_pte' (heap s) pa va = get_pte' (heap s(p \<mapsto> v)) pa va")
    apply clarsimp
   apply (subgoal_tac " p \<notin> ptable_trace' (heap s(p \<mapsto> v)) rt va")
    apply (clarsimp simp: get_pte'_def get_pde'_def decode_heap_pde'_def ptable_trace'_def Let_def
      decode_heap_pte'_def)
   apply (rule kernel_data_area_ptrace', simp, simp)
  apply (subgoal_tac " p \<notin> ptable_trace' (heap s(p \<mapsto> v)) rt va")
   apply (clarsimp simp: ptable_trace'_def get_pde'_def Let_def decode_heap_pde'_def split: pde.splits)
  by (simp add: kernel_data_area_ptrace')





lemma kernel_mapping_upd:
  "p \<notin> kernel_data_area s \<Longrightarrow> 
  kernel_mappings (s\<lparr>p_state.heap := heap s(p \<mapsto> v)\<rparr>) =
      kernel_mappings s"
  apply (clarsimp simp: kernel_mappings_def)
  apply (subgoal_tac "hptable_eq (s\<lparr>heap := heap s(p \<mapsto> v)\<rparr>)  = hptable_eq s  ")
   apply (subgoal_tac "global_mappings (s\<lparr>heap := heap s(p \<mapsto> v)\<rparr>) =  global_mappings s ")
    apply simp
   apply (frule kernel_data_global_map_update)
  apply blast
  apply (frule_tac v = v in  kerenl_data_global_mappings)
  by blast



lemma mmu_layout_upd':
  "\<lbrakk> mmu_layout s; p \<notin> kernel_data_area s \<rbrakk> \<Longrightarrow> mmu_layout (s\<lparr>p_state.heap := heap s(p \<mapsto> v)\<rparr>)"
  apply (clarsimp simp: mmu_layout_def)
  apply (subgoal_tac "p \<notin> kernel_data_area s")
   prefer 2
   apply blast
  apply (simp add: kernel_data_upd kernel_data_area_upd kernel_mapping_upd)
  apply rule
   apply (clarsimp simp: user_mappings_def)
   apply (subst (asm) pt_table_lift_trace_upd )
    apply (simp add: kernel_data_def kernel_data_area_def ptable_footprint_def roots_def)
   apply simp
   apply (frule_tac v = v and rt =rt and va = va in kernel_data_area_non_global, simp)
   apply (clarsimp simp: non_global_def)
  by (clarsimp simp: global_set_eq_def)


  
lemma mmu_layout_upd:
  "\<lbrakk> mmu_layout s; p \<notin> kernel_phy_mem \<rbrakk> \<Longrightarrow> mmu_layout (s\<lparr>p_state.heap := heap s(p \<mapsto> v)\<rparr>)"
  apply (rule mmu_layout_upd', assumption)
  apply (auto simp: mmu_layout_def)
  done

end