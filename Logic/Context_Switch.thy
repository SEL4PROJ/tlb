theory Context_Switch
                  
imports Kernel_Execution
        

begin               

locale heap_only =
  fixes f
  assumes heap_eq: "heap s = heap s' \<Longrightarrow> f s = f s'"
begin

lemma f_mode_upd[simp]:
  "f (mode_update upd s) = f s"
  by (rule heap_eq) simp

lemma f_root_upd[simp]:
  "f (root_update upd s) = f s"
  by (rule heap_eq) simp

lemma f_incon_set_upd[simp]:
  "f (incon_set_update upd s) = f s"
  by (rule heap_eq) simp

lemma f_ptable_snapshot_set_upd[simp]:
  "f (ptable_snapshot_update upd s) = f s"
  by (rule heap_eq) simp

lemma f_asid_upd[simp]:
  "f (p_state.asid_update upd s) = f s"
  by (rule heap_eq) simp

lemma f_gset_upd[simp]:
  "f (p_state.global_set_update upd s) = f s"
  by (rule heap_eq) simp

end


lemma ptable_footprint_heap_eq:
  "heap s = heap s' \<Longrightarrow> ptable_footprint s = ptable_footprint s'"
  by (rule ext) (simp add: ptable_footprint_def)

interpretation ptable_footprint: heap_only ptable_footprint
  by unfold_locales (rule ptable_footprint_heap_eq)

lemma root_log_heap_eq:
  "heap s = heap s' \<Longrightarrow> root_log s = root_log s'"
  by (simp add: root_log_def root_map_def map_of_set_def root_set_def)

interpretation rt_log: heap_only root_log
  by unfold_locales (rule root_log_heap_eq)

lemma root_map_heap_eq:
  "heap s = heap s' \<Longrightarrow> root_map s = root_map s'"
  by (simp add: root_map_def root_set_def)

interpretation rt_map: heap_only root_map
  by unfold_locales (rule root_map_heap_eq)

lemma kernel_date_area_heap_eq:
  assumes "heap s = heap s'"
  shows "kernel_data_area s = kernel_data_area s'"
  using assms
  by (simp add: kernel_data_area_def kernel_data_def ptable_footprint_heap_eq[OF assms] root_log_def
    root_map_def map_of_set_def root_set_def)

interpretation kernel_date_area: heap_only kernel_data_area
  by unfold_locales (rule kernel_date_area_heap_eq)
                                   
lemma non_overlapping_tables_heap_eq:
  assumes "heap s = heap s'"
  shows "non_overlapping_tables s = non_overlapping_tables s'"
  by (simp add: non_overlapping_tables_def root_log_heap_eq[OF assms] ptable_footprint_heap_eq[OF assms] roots_def)

interpretation overl: heap_only non_overlapping_tables
  by unfold_locales (rule non_overlapping_tables_heap_eq)

lemma user_mappings_heap_eq:
  assumes "heap s = heap s'"
  shows "user_mappings s = user_mappings s'"
  using assms by (simp add: user_mappings_def root_log_heap_eq[OF assms] roots_def)

interpretation user_mappings: heap_only user_mappings
  by unfold_locales (rule user_mappings_heap_eq)

lemma kernel_mappings_heap_eq:
  assumes "heap s = heap s'"
  shows "kernel_mappings s = kernel_mappings s'"
  using assms by (simp add: kernel_mappings_def global_mappings_def global_mappings'_def hptable_eq_def root_log_heap_eq[OF assms] roots_def)

interpretation kernel_mappings: heap_only kernel_mappings
  by unfold_locales (rule kernel_mappings_heap_eq)



lemma asids_consistentD:
  "\<lbrakk> asids_consistent {} s; root_map s (Addr r) = Some a; a \<noteq> asid s \<rbrakk> \<Longrightarrow>
     fst(ptable_snapshot s a) = {} \<and> (ptable_comp (snd (ptable_snapshot s a)) (pt_walk_pair a (heap s) (Addr r)) = {} )"
  by (clarsimp simp: asids_consistent_def)


definition
  \<I>\<C> :: "p_state \<Rightarrow> 32 word set"
where
  "\<I>\<C> s \<equiv>  {vp. Addr vp \<in> incon_set s}" 


lemma asid_con_mode_upd:
  "asids_consistent S (mode_update upd s) = asids_consistent S s"
  by (clarsimp simp: asids_consistent_def roots_def)

lemma [simp]:
  "a \<noteq> a' \<Longrightarrow>
     incon_load (cur_pt_snp' snp iset hp' rt' a) iset gset a' hp  = 
     incon_load snp iset gset a' hp "
  apply (clarsimp simp: cur_pt_snp'_def  cur_pt_snp_def)
  apply rule
  by (clarsimp simp: incon_load_def)


lemma mmu_layout_roots_elem[simp]:
  "mmu_layout s \<Longrightarrow> root s \<in> roots s"
  apply (rule rootsI)
  by (clarsimp simp: mmu_layout_def root_map_def )


lemma mmu_layout_global_set_imp_global:
  "\<lbrakk>mmu_layout s; va \<in> global_set s ; rt \<in> roots s \<rbrakk>
           \<Longrightarrow> global (heap s) rt va"
  apply (clarsimp simp: global_def)
  apply (clarsimp simp: mmu_layout_def global_set_eq_def)
  apply (subgoal_tac "root s r+ pd_idx_offset (addr_val va) \<in> high_ptable (root s)")
   prefer 2
   apply blast
  apply (clarsimp simp: kernel_mappings_def global_mappings_def global_mappings'_def)
  apply (drule_tac x = "root s" in bspec) 
  using root_map_rootsD apply blast
  apply clarsimp
  apply (drule_tac x = "addr_val va" in spec, clarsimp)
  by (metis Addr_addr_val hptable_eq_def option.inject pde.inject(2) pde.simps(14) root_map_rootsD)


lemma kw_lower_leq_vadd_off:
  "\<lbrakk>is_aligned rt pd_bits ; kernel_window_lower_bound < 2 ^ pd_bits; rt + kernel_window_lower_bound \<le> rt +  v \<rbrakk> \<Longrightarrow>
     kernel_window_lower_bound \<le>  v"
  apply (rule_tac x = rt in word_plus_mcs_4)
   apply (simp add: add.commute)
  apply (subgoal_tac "rt \<le> rt + kernel_window_lower_bound")
   apply (simp add: add.commute)
  by (rule_tac sz = pd_bits in  is_aligned_no_wrap', simp, simp)


lemma kw_upper_leq_vadd_off:
  "\<lbrakk>is_aligned rt pd_bits ; v < 2 ^ pd_bits; rt + v \<le> rt + kernel_window_upper_bound\<rbrakk> \<Longrightarrow>
     v \<le>  kernel_window_upper_bound"
  apply (rule_tac x = rt in word_plus_mcs_4)
   apply (simp add: add.commute)
  apply (simp add: add.commute)
  by (rule_tac sz =  pd_bits in is_aligned_no_wrap', simp, simp)

thm plus_one_helper
  word_add_increasing
  word_plus_mcs_3
  word_plus_mcs_4
  word_plus_mcs_4'
  word_plus_mono_left
find_theorems "(+)" "(\<le>)" is_aligned
find_theorems "(+)" "(\<le>)" "_ ::'a :: len word" 

lemma word_leq_plus_comm:
  "(a ::'a :: len word) + b  \<le> c + d \<Longrightarrow> b + a \<le> d + c"
  by (simp add: linordered_field_class.sign_simps(2))


lemma word_leq_plus_comm':
  "(a ::'a :: len word)  \<le> b + c \<Longrightarrow> (a \<le> c + b)"
  by (simp add: linordered_field_class.sign_simps(2))



lemma high_ptable_vaddr_set_eq:
  "\<lbrakk>mmu_layout s ; rt \<in> roots s \<rbrakk> \<Longrightarrow>   
           {va::vaddr. root s  r+ pd_idx_offset (addr_val va) \<in> high_ptable (root s)} =
           {va::vaddr. rt r+ pd_idx_offset (addr_val va) \<in> high_ptable rt}"
  apply safe
   apply (clarsimp simp: high_ptable_def addr_add_def)
   apply (rule conjI)
    apply (subgoal_tac "kernel_window_lower_bound \<le> pd_idx_offset (addr_val x)")
     prefer 2
     apply (rule_tac rt = "addr_val (root s)" in kw_lower_leq_vadd_off)
       apply (clarsimp simp: mmu_layout_def aligned_def)
      apply (clarsimp simp: mmu_layout_def kernel_mappings_def kwindow_bound_def)
     apply simp
    apply (rule word_leq_plus_comm)
    apply (rule word_plus_mcs_3, simp)
    apply (simp add: add.commute)
    apply (rule_tac sz = pd_bits in is_aligned_no_wrap')
     apply (clarsimp simp: mmu_layout_def aligned_def )
    apply (clarsimp simp: pd_idx_offset_def vaddr_pd_index_def pd_bits_def mask_def)
    apply word_bitwise
   apply (subgoal_tac "pd_idx_offset (addr_val x) \<le> kernel_window_upper_bound")
    prefer 2
    apply (rule_tac rt = "addr_val (root s)" in kw_upper_leq_vadd_off)
      apply (clarsimp simp: mmu_layout_def aligned_def)
     apply (clarsimp simp: pd_idx_offset_def vaddr_pd_index_def pd_bits_def mask_def)
     apply word_bitwise
    apply simp
   apply (rule word_leq_plus_comm)
   apply (rule word_plus_mcs_3, simp)
   apply (rule word_leq_plus_comm')
   apply (rule_tac sz = pd_bits in is_aligned_no_wrap')
    apply (clarsimp simp: mmu_layout_def aligned_def )
   apply (clarsimp simp: mmu_layout_def kernel_mappings_def kwindow_bound_def)
  apply (clarsimp simp: high_ptable_def addr_add_def)
  apply (rule conjI)
   apply (subgoal_tac "kernel_window_lower_bound \<le> pd_idx_offset (addr_val x)")
    prefer 2
    apply (rule_tac rt = "addr_val rt" in kw_lower_leq_vadd_off)
      apply (clarsimp simp: mmu_layout_def aligned_def)
     apply (clarsimp simp: mmu_layout_def kernel_mappings_def kwindow_bound_def)
    apply simp
   apply (rule word_leq_plus_comm)
   apply (rule word_plus_mcs_3, simp)
   apply (rule word_leq_plus_comm')
   apply (rule_tac sz = pd_bits in is_aligned_no_wrap')
    apply (clarsimp simp: mmu_layout_def aligned_def )
   apply (clarsimp simp: pd_idx_offset_def vaddr_pd_index_def pd_bits_def mask_def)
   apply word_bitwise
  apply (subgoal_tac "pd_idx_offset (addr_val x) \<le> kernel_window_upper_bound")
   prefer 2
   apply (rule_tac rt = "addr_val rt" in kw_upper_leq_vadd_off)
     apply (clarsimp simp: mmu_layout_def aligned_def)
    apply (clarsimp simp: pd_idx_offset_def vaddr_pd_index_def pd_bits_def mask_def)
    apply word_bitwise
   apply simp
  apply (rule word_leq_plus_comm)
  apply (rule word_plus_mcs_3, simp)
  apply (rule word_leq_plus_comm')
  apply (rule_tac sz = pd_bits in is_aligned_no_wrap')
   apply (clarsimp simp: mmu_layout_def aligned_def )
  by (clarsimp simp: mmu_layout_def kernel_mappings_def kwindow_bound_def)
   

lemma mmu_layout_global_offset_eq:
  "\<lbrakk>mmu_layout s; va \<in> global_set s ; rt \<in> roots s \<rbrakk>
           \<Longrightarrow> rt r+ pd_idx_offset (addr_val va) \<in> high_ptable rt"
  using global_set_eq_def mmu_layout_def high_ptable_vaddr_set_eq by fastforce


lemma mmu_layout_root_map_eq:
  "\<lbrakk> mmu_layout s ; root_map s r = Some (asid s) \<rbrakk> \<Longrightarrow> r = root s"
  apply (clarsimp simp: mmu_layout_def partial_inj_def)
  by fastforce


lemma  mmu_layout_roots_global_entries_eq:
  " \<lbrakk>mmu_layout s ; rt \<in> roots s\<rbrakk>
         \<Longrightarrow> (\<Union>x\<in>global_entries (ran (pt_walk a' (heap s) rt)). range_of x) =
             global_set s"
  apply (subst mmu_layout_global_set_subset', simp, simp)
  apply (frule_tac rt = rt in  high_ptable_vaddr_set_eq, simp)
  by (clarsimp simp: mmu_layout_def global_set_eq_def)


lemma mmu_layout_global_pt_walk_roots_eq:
  "\<lbrakk>mmu_layout s; va \<in> global_set s ; rt \<in> roots s ; rt' \<in> roots s\<rbrakk>
           \<Longrightarrow> pt_walk_pair a (heap s) rt  va = pt_walk_pair a' (heap s) rt' va"
  apply (frule_tac rt = rt  in mmu_layout_global_offset_eq; simp?)
  apply (clarsimp simp: mmu_layout_def kernel_mappings_def  hptable_eq_def)
  apply (drule_tac x = rt in spec)
  apply (drule_tac x = rt' in spec, simp)
  apply (drule_tac x = "addr_val va" in spec, simp)
  apply (clarsimp simp: global_mappings_def)
  apply (drule_tac x = rt in bspec, simp)
  apply (clarsimp simp: global_mappings'_def)
  apply (drule_tac x = "addr_val va" in spec, clarsimp)
  by (clarsimp simp: pt_walk_pair_def map_opt_def pdc_walk_def tag_conv_def to_tlb_flags_def split:option.splits)


lemma context_switch_invariants:
  "\<Turnstile> \<lbrace> \<lambda>s. mmu_layout s \<and> asids_consistent {} s \<and> mode s = Kernel \<and>  \<I>\<C> s = {} \<and>
            0 \<notin> ran (root_map s)  \<and> root_map s (Addr r) = Some a\<rbrace>
            UpdateASID 0 ;; UpdateTTBR0 (Const r) ;; UpdateASID a ;; SetMode User
      \<lbrace>\<lambda>s. mmu_layout s \<and> \<I>\<C> s = {} \<and> mode s = User \<and> asids_consistent {} s \<rbrace>"
  apply vcgm
  apply (subgoal_tac "a \<noteq> 0")
   prefer 2  apply (clarsimp simp: ran_def)
  apply (rule conjI)
   apply (clarsimp simp: mmu_layout_def kernel_data_def roots_def)
   apply (clarsimp simp: global_set_eq_def)
   apply (subgoal_tac "(\<Union>x\<in>global_entries (ran (pt_walk 0 (heap s) (Addr r))). range_of x) = 
                {va. Addr (r + pd_idx_offset (addr_val va)) \<in> high_ptable (Addr r)}")
    prefer 2
    apply (simp only: addr_addr_add [symmetric])
    apply (rule mmu_layout_global_set_subset')
     apply (clarsimp simp: mmu_layout_def kernel_data_def global_set_eq_def root_map_def roots_def)
    apply (simp add: root_map_rootsD)
   apply (simp only: addr_addr_add [symmetric])
   apply (subgoal_tac "global_set s = {va. Addr r r+ pd_idx_offset (addr_val va) \<in> high_ptable (Addr r)}")
    apply blast
   apply (subgoal_tac " {va::vaddr. root s  r+ pd_idx_offset (addr_val va) \<in> high_ptable (root s)}  =
                    {va. Addr r r+ pd_idx_offset (addr_val va) \<in> high_ptable (Addr r)}")
    apply clarsimp
   apply (rule high_ptable_vaddr_set_eq, simp add: mmu_layout_def kernel_data_def global_set_eq_def roots_def)
   apply (simp add: root_map_rootsD)
  apply (rule conjI)
   apply (clarsimp simp: \<I>\<C>_def)
   apply (subgoal_tac "Addr x \<notin> fst (cur_pt_snp' (ptable_snapshot s) (incon_set s) (heap s) (root s) (asid s) a)")
    apply (subgoal_tac "(\<Union>x\<in>global_entries (ran (pt_walk 0 (heap s) (Addr r))). range_of x) = 
                {va. Addr (r + pd_idx_offset (addr_val va)) \<in> high_ptable (Addr r)}")
     prefer 2
     apply (simp only: addr_addr_add [symmetric])
     apply (rule mmu_layout_global_set_subset')
      apply (clarsimp simp: mmu_layout_def kernel_data_def global_set_eq_def root_map_def)
     apply (simp add: root_map_rootsD)
    apply (simp only: addr_addr_add [symmetric])
    apply (thin_tac "(\<Union>x\<in>global_entries (ran (pt_walk 0 (heap s) (Addr r))). range_of x) = {va. Addr r r+ pd_idx_offset (addr_val va) \<in> high_ptable (Addr r)}")
    apply (subgoal_tac "Addr x \<notin> (incon_load (cur_pt_snp' (ptable_snapshot s) (incon_set s) (heap s) (root s) (asid s)) (incon_set s) (global_set s) 0 (heap s) (root s) \<union>
                 incon_comp 0 0 (heap s) (heap s) (root s) (Addr r)) \<inter> (global_set s \<union> {va. Addr r r+ pd_idx_offset (addr_val va) \<in> high_ptable (Addr r)}) ")
     apply (subgoal_tac "Addr x \<notin> ptable_comp (snd (cur_pt_snp' (ptable_snapshot s) (incon_set s) (heap s) (root s) (asid s) a)) (pt_walk_pair a (heap s) (Addr r))")
      apply (clarsimp simp: incon_load_def)
     prefer 3
     apply (clarsimp simp: cur_pt_snp'_def cur_pt_snp_def asids_consistent_def split: if_split_asm)
    apply (clarsimp simp: cur_pt_snp'_def cur_pt_snp_def split: if_split_asm)
     apply (subgoal_tac "Addr r = root s", clarsimp)
      apply (clarsimp simp: ptable_comp_def)
     apply (rule mmu_layout_root_map_eq; simp add: mmu_layout_def kernel_data_def global_set_eq_def) 
    apply (clarsimp simp: cur_pt_snp'_def cur_pt_snp_def asids_consistent_def split: if_split_asm) 
   apply (thin_tac "Addr x
            \<in> incon_load (cur_pt_snp' (ptable_snapshot s) (incon_set s) (heap s) (root s) (asid s))
                (incon_load (cur_pt_snp' (ptable_snapshot s) (incon_set s) (heap s) (root s) (asid s)) (incon_set s) (global_set s) 0 (heap s) (root s) \<union> incon_comp 0 0 (heap s) (heap s) (root s) (Addr r))
                (global_set s \<union> {va. Addr r r+ pd_idx_offset (addr_val va) \<in> high_ptable (Addr r)}) a (heap s) (Addr r)")
   apply (thin_tac "  Addr x \<notin> fst (cur_pt_snp' (ptable_snapshot s) (incon_set s) (heap s) (root s) (asid s) a)")
   apply (subgoal_tac "{va. Addr r r+ pd_idx_offset (addr_val va) \<in> high_ptable (Addr r)} =  
                          global_set s")
    apply clarsimp
    apply (thin_tac " {va. Addr (r + pd_idx_offset (addr_val va)) \<in> high_ptable (Addr r)} = global_set s")
    apply (clarsimp simp: incon_load_def cur_pt_snp'_def cur_pt_snp_def incon_comp_def split: if_split_asm)
     apply (erule disjE)
      apply (clarsimp simp: ptable_comp_def)
     apply (subgoal_tac "pt_walk_pair 0 (heap s) (root s) (Addr x)  = pt_walk_pair 0 (heap s) (Addr r) (Addr x )")
      apply (clarsimp simp: ptable_comp_def)
     apply (rule mmu_layout_global_pt_walk_roots_eq, simp, simp, rule mmu_layout_roots_elem, simp, rule rootsI, simp)
    apply (erule disjE)
     apply (clarsimp simp: asids_consistent_def)
     apply (subgoal_tac " Addr r \<in> roots s \<and> root_map s (Addr r) \<noteq> Some 0")
      apply blast 
     apply rule
      apply (rule rootsI)
      apply force
     apply force
    apply (erule disjE)
     apply (clarsimp simp: asids_consistent_def)
     apply (subgoal_tac "root s  \<in> roots s \<and> root_map s (root s) \<noteq> Some 0")
      apply blast
     apply force
    apply (subgoal_tac "pt_walk_pair 0 (heap s) (root s) (Addr x)  = pt_walk_pair 0 (heap s) (Addr r) (Addr x )")
     apply (clarsimp simp: ptable_comp_def)
    apply (rule mmu_layout_global_pt_walk_roots_eq, simp, simp, rule mmu_layout_roots_elem, simp, rule rootsI, simp)
   apply (subgoal_tac " {va. Addr r r+ pd_idx_offset (addr_val va) \<in> high_ptable (Addr r)} = {va::vaddr. root s  r+ pd_idx_offset (addr_val va) \<in> high_ptable (root s)}  ")
    apply (clarsimp simp: mmu_layout_def global_set_eq_def)
   apply (rule high_ptable_vaddr_set_eq [symmetric], simp)
  using rootsI apply blast
  apply (clarsimp simp: asids_consistent_def)
  apply (rule conjI)
   apply clarsimp
   apply (rule conjI)
    apply (case_tac "aa = asid s")
     apply (clarsimp simp: cur_pt_snp'_def cur_pt_snp_def \<I>\<C>_def) 
     apply (metis (mono_tags, hide_lams) Addr_addr_val ex_in_conv option.inject ranI ran_def root_map_def root_set_def)
    apply (clarsimp simp: incon_load_def cur_pt_snp'_def cur_pt_snp_def split: if_split_asm)
    apply (clarsimp simp: mmu_layout_def ran_def) 
    apply blast
   apply (clarsimp simp: cur_pt_snp'_def cur_pt_snp_def)
   apply (case_tac "aa = asid s")
    apply (clarsimp)
    apply (subgoal_tac "ra = root s")
     apply (clarsimp simp: ptable_comp_def ranI) 
    apply (simp add: mmu_layout_root_map_eq)
   apply clarsimp
   apply (simp add: ranI)
  apply (clarsimp simp: roots_def)
  apply (subgoal_tac "asid s \<noteq> 0")
   prefer 2
  using mmu_layout_def ran_def apply fastforce
  apply (subgoal_tac "(\<Union>x\<in>global_entries (ran (pt_walk 0 (heap s) (Addr r))). range_of x) = global_set s")
   apply clarsimp
   apply (clarsimp simp: cur_pt_snp'_def cur_pt_snp_def incon_load_def)
   apply (case_tac "aa = asid s"; clarsimp?)
    apply safe [1]
     apply (clarsimp simp: \<I>\<C>_def)
     apply (metis Addr_addr_val ex_in_conv)
    apply (subgoal_tac "pt_walk_pair (asid s) (heap s) (root s) x = pt_walk_pair (asid s) (heap s) ra x")
     apply (clarsimp simp: ptable_comp_def)
    apply (rule mmu_layout_global_pt_walk_roots_eq, simp, simp, simp) 
    apply (simp add: roots_def)
   apply safe [1]
       apply (subgoal_tac "ra \<in> set (root_log s) \<and> root_map s ra \<noteq> Some 0")
        apply force
       apply blast
      apply (clarsimp simp: \<I>\<C>_def)
      apply (metis Addr_addr_val ex_in_conv)
     apply (subgoal_tac "root s \<in> set (root_log s) \<and> root_map s (root s) \<noteq> Some 0")
      apply blast
  using mmu_layout_roots_elem roots_def apply force
    apply (clarsimp simp: incon_comp_def)
    apply (subgoal_tac "pt_walk_pair 0 (heap s) (root s) x = pt_walk_pair 0 (heap s) (Addr r) x")
     apply (clarsimp simp: ptable_comp_def)
    apply (rule mmu_layout_global_pt_walk_roots_eq, simp, simp, simp) 
    apply (simp add: roots_def) 
  using root_map_rootsD roots_def apply force
   apply (subgoal_tac "pt_walk_pair 0 (heap s) (Addr r) x = pt_walk_pair 0 (heap s) ra x")
    apply (clarsimp simp: ptable_comp_def)
   apply (rule mmu_layout_global_pt_walk_roots_eq, simp, simp) 
    apply (simp add: roots_def) 
  using root_map_rootsD roots_def apply force
   apply (simp add: roots_def)   apply (rule mmu_layout_roots_global_entries_eq,simp)
  apply (simp add: roots_def) 
  using root_map_rootsD roots_def by force


end

