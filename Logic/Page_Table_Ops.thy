theory Page_Table_Ops
                  
imports User_Execution


begin               


lemma mmu_layout_global_set_pt_walk_pair:
  "\<lbrakk>mmu_layout s; va \<in> global_set s \<rbrakk>
           \<Longrightarrow> \<exists>e e'. pt_walk_pair a (heap s) (root s)  va = Full_Walk e e'"
  apply (clarsimp simp: mmu_layout_def global_set_eq_def kernel_mappings_def 
      global_mappings_def global_mappings'_def)
  apply (drule_tac x = "root s" in bspec)
  using root_map_rootsD apply blast
  apply clarsimp
  apply (drule_tac x = "addr_val va" in spec) 
  apply (drule_tac x = "addr_val va" in spec)
  apply (subgoal_tac  "root s r+ pd_idx_offset (addr_val va) \<in> high_ptable (root s)")
   prefer 2
   apply blast
  apply clarsimp
  by (clarsimp simp: pt_walk_pair_def pdc_walk_def)


definition "pde_tlb_entry'  a (base :: paddr) perms  (va :: vaddr) = Some (EntrySection (Some a) 
                                                                 (ucast (addr_val va >> 20) :: 12 word) 
                                                                ((ucast (addr_val base >> 20)) :: 12 word)
                                                                 (to_tlb_flags perms))"
 


lemma pt_walk_section:
  "\<lbrakk> hp p = Some w; addr_val r >> pd_bits = addr_val p >> pd_bits;  
     \<forall>ptp va:: vaddr. decode_pde (the (hp (r r+ (vaddr_pd_index (addr_val va) << 2)))) = PageTablePDE ptp \<longrightarrow>
       p \<noteq> ptp r+ (vaddr_pt_index (addr_val va) << 2);
           decode_pde w = InvalidPDE; decode_pde pde = SectionPDE base perms; arm_p_nG perms = 1 \<rbrakk> \<Longrightarrow>
          pt_walk a (hp(p \<mapsto> pde)) r = 
      (\<lambda>va. if p\<in> ptable_trace' hp r va  then pde_tlb_entry' a  base perms va else pt_walk a hp r va)"
  apply rule+
  apply (case_tac "p \<in> ptable_trace' hp r va")
   defer
   apply clarsimp
   apply (rule pt_walk_pt_trace_upd', simp)
  apply clarsimp
  apply (clarsimp simp:  ptable_trace'_def Let_def split: pde.splits)
  apply (clarsimp simp: pt_walk_def map_opt_def split: option.splits)
  apply (rule conjI)
   apply clarsimp
   apply (clarsimp simp: pdc_walk_def get_pde'_def decode_heap_pde'_def split: option.splits)
  apply clarsimp
  by (clarsimp simp: pdc_walk_def get_pde'_def decode_heap_pde'_def pde_tlb_entry'_def tag_conv_def to_tlb_flags_def split: option.splits)



lemma first_level_ptable_trace_defined:
  "\<lbrakk> addr_val rt >> pd_bits = addr_val pa >> pd_bits; 
        is_aligned (addr_val rt) pd_bits; is_aligned (addr_val pa) 2 \<rbrakk> \<Longrightarrow> 
        pa \<in> ptable_footprint s rt"
  apply (subgoal_tac " \<exists>va. pa \<in> ptable_trace' (heap s) rt va")
   apply (clarsimp simp: ptable_footprint_def)
  apply (rule_tac x = "Addr (((addr_val pa >> 2) && mask 12) << 20)" in exI)
  apply (subgoal_tac "pa = rt r+ (vaddr_pd_index ((addr_val pa >> 2) && mask 12 << 20) << 2)")
   apply (clarsimp simp: ptable_trace'_def Let_def split: pde.splits)
  apply (clarsimp simp: vaddr_pd_index_def pd_bits_def is_aligned_mask mask_def addr_add_def)
  apply (case_tac pa)   apply (case_tac rt) apply clarsimp
  apply word_bitwise
  by (clarsimp simp: carry_def xor3_def)


lemma map_section_current_asid:
  "\<Turnstile> \<lbrace>\<lambda>s. \<exists> SM w base perms. mmu_layout s \<and> mode s = Kernel \<and> safe_set (kernel_safe s) s \<and> 
      Addr vp \<in> SM \<and>
      SM = kernel_safe s \<and>
      asids_consistent {} s \<and>
      addr_val (root s) >> pd_bits = addr_val (k_phy_ad vp) >> pd_bits \<and>
       is_aligned (addr_val (k_phy_ad vp)) 2 \<and>
      (\<forall>ptp va::vaddr. decode_pde (the (heap s (root s r+ (vaddr_pd_index (addr_val va) << 2)))) = 
            PageTablePDE ptp \<longrightarrow> k_phy_ad vp \<noteq> ptp r+ (vaddr_pt_index (addr_val va) << 2)) \<and>
      heap s (k_phy_ad vp) = Some w \<and>
      decode_pde w = InvalidPDE \<and> 
      decode_pde pde = SectionPDE base perms \<and> arm_p_nG perms = 1 \<rbrace>
      Const vp ::= Const pde
   \<lbrace>\<lambda>s.  asids_consistent {} s\<rbrace>" 
  apply (vcgm vcg: weak_pre_write')
  apply (subgoal_tac "k_phy_ad vp \<in>  ptable_footprint s (root s)")
   prefer 2 
   apply (rule first_level_ptable_trace_defined, clarsimp simp: k_phy_ad_def, 
      simp add: mmu_layout_def aligned_def, simp add: k_phy_ad_def)
  apply (rule conjI)
   apply (clarsimp simp: asids_consistent_def safe_set_def con_set_def)
  apply (subgoal_tac "ptable_lift' (heap s) (root s) (Addr vp) = Some (Addr vp r-  global_offset)" , clarsimp)
   prefer 2
   apply (clarsimp simp: kernel_region_offset')
  apply (subgoal_tac "Addr (vp - global_offset) \<notin> root_map_area")
   prefer 2
   apply (subgoal_tac "root s \<in> set (root_log s)")
    apply (clarsimp simp: mmu_layout_def kernel_data_def k_phy_ad_def, blast) 
   apply (clarsimp simp: mmu_layout_def root_log_def)
   apply (rule_tac x = "addr_val (root s)" in image_eqI, simp, force)
  apply (clarsimp simp: asids_consistent_def)
  apply (rule conjI)
   apply (subgoal_tac "root_map (s\<lparr> heap := heap s(Addr (vp - global_offset) \<mapsto> pde)\<rparr>) = root_map s")
    apply clarsimp
    apply (drule_tac x = r in spec, drule_tac x = a in spec, clarsimp)
    apply (clarsimp simp: ptable_comp_def)
    apply (drule_tac x = x in spec)
    apply (subgoal_tac " pt_walk_pair a (heap s(Addr (vp - global_offset) \<mapsto> pde)) r x = pt_walk_pair a (heap s) r x")
     apply force
    apply (rule pt_walk_pair_pt_trace_upd')
    apply (subgoal_tac " Addr (vp - global_offset) \<notin> ptable_footprint s r")
  using ptable_footprint_def apply blast
    apply clarsimp
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
     apply (clarsimp simp: ptable_footprint_def) 
  using mmu_layout_roots_elem apply blast
    apply rule
     apply (clarsimp simp: roots_def mmu_layout_def root_log_def)
     apply (rule_tac x = "addr_val r" in image_eqI, simp, force)
  using mmu_layout_def rootsI apply force
   apply (clarsimp simp: k_phy_ad_def ptable_footprint_def)
  apply (clarsimp simp: roots_def)
  apply (subgoal_tac "(\<Union>x\<in>global_entries (ran (pt_walk (asid s)  (heap s(Addr (vp - global_offset) \<mapsto> pde)) (root s))). range_of x) = global_set s")
   apply clarsimp
   apply (thin_tac "(\<Union>x\<in>global_entries (ran (pt_walk (asid s) (heap s(Addr (vp - global_offset) \<mapsto> pde)) (root s))). range_of x) =   global_set s")
   apply (case_tac "r = root s")
    apply clarsimp
    apply (drule_tac x = "root s" in spec)
    apply (drule_tac x = "root s" in spec)
    apply (subgoal_tac "root s \<in> set (root_log s)")
     prefer 2
     apply (drule_tac s = s and v = pde in roots_upd', simp add: roots_def)
    apply (drule_tac x = a in spec) 
    apply (rule Int_emptyI)
    apply (case_tac "x \<in> fst (ptable_snapshot s a)")
     apply blast
    apply clarsimp
    apply (subgoal_tac "x \<notin> ptable_comp (snd (ptable_snapshot s a)) (pt_walk_pair a (heap s) (root s))")
     prefer 2
     apply blast
    apply (thin_tac "root_map s (root s) = Some a \<and> a \<noteq> asid s \<longrightarrow>
        fst (ptable_snapshot s a) = {} \<and> ptable_comp (snd (ptable_snapshot s a)) (pt_walk_pair a (heap s) (root s)) = {}")
    apply (clarsimp simp: ptable_comp_def entry_leq_def)
    apply (subgoal_tac "pt_walk_pair a (heap s) (root s) x = pt_walk_pair a (heap s(Addr (vp - global_offset) \<mapsto> pde)) (root s) x")
     apply clarsimp
    apply (rule pt_walk_pair_pt_trace_upd)
    apply (subgoal_tac "ptable_trace' (heap s) (root s) x \<subseteq> high_ptable(root s)")
     apply (clarsimp simp: kernel_safe_def   k_phy_ad_def)
     apply (clarsimp simp: vas_of_current_state_mapped_to_global_mappings_of_all_processes_def vas_mapped_by_global_mappings_def)
     apply (rule_tac x = "root s" in bexI)
      apply (clarsimp simp: mmu_layout_def kernel_mappings_def global_mappings_def global_mappings'_def)
      apply (drule_tac x = "root s" in bspec)
       apply (drule_tac s = s and v = pde in roots_upd', simp add: roots_def)
      apply clarsimp
      apply (drule_tac x = vp in spec)
      apply clarsimp
      apply (clarsimp simp: ptable_trace'_def Let_def pd_idx_offset_def get_pde'_def decode_heap_pde'_def split: option.splits pde.splits)
  using roots_def apply blast
    apply (clarsimp simp: mmu_layout_def global_set_eq_def kernel_mappings_def global_mappings_def global_mappings'_def)
    apply (drule_tac x = "root s" in bspec)
     apply (drule_tac s = s and v = pde in roots_upd', simp add: roots_def)
    apply clarsimp
    apply (drule_tac x = "addr_val x" in spec)
    apply clarsimp
    apply (subgoal_tac " root s r+ pd_idx_offset (addr_val x) \<in> high_ptable (root s)" )
     apply (clarsimp simp: ptable_trace'_def Let_def pd_idx_offset_def   split: option.splits pde.splits)
    apply blast
   apply (drule_tac x = r in spec)
   apply (drule_tac x = r in spec)
   apply (subgoal_tac "r \<in> set (root_log s)")
    prefer 2
    apply (drule_tac s = s and v = pde in roots_upd', simp add: roots_def)
   apply (drule_tac x = a in spec)
   apply (rule Int_emptyI)
   apply (case_tac "x \<in> fst (ptable_snapshot s a)")
    apply blast
   apply clarsimp
   apply (subgoal_tac "x \<notin> ptable_comp (snd (ptable_snapshot s a)) (pt_walk_pair a (heap s) r)")
    prefer 2
    apply blast
   apply (thin_tac  "root_map s r = Some a \<and> a \<noteq> asid s \<longrightarrow> fst (ptable_snapshot s a) = {} \<and> ptable_comp (snd (ptable_snapshot s a)) (pt_walk_pair a (heap s) r) = {}")
   apply (clarsimp simp: ptable_comp_def entry_leq_def)
   apply (subgoal_tac "pt_walk_pair a (heap s) r x = pt_walk_pair a (heap s(Addr (vp - global_offset) \<mapsto> pde)) r x")
    apply clarsimp
   apply (rule pt_walk_pair_pt_trace_upd)
   apply (clarsimp simp: k_phy_ad_def ptable_footprint_def mmu_layout_def )
   apply (drule non_overlapping_tables_from_kernel_data)
   apply (clarsimp simp: non_overlapping_tables_def ptable_footprint_def)
   apply (drule_tac x = "root s"  in spec)
   apply (drule_tac x = r  in spec)
  using  root_map_rootsD roots_def apply blast
  apply (frule_tac p = "k_phy_ad vp" and r = "root s" and pde = pde and base = base and a = "asid s" in  pt_walk_section,
      simp, simp add: k_phy_ad_def, simp,simp, simp,simp) 
  apply (simp add: k_phy_ad_def) 
  apply safe
   apply (clarsimp simp: ran_def global_entries_def)
   apply (rename_tac va)
   apply (case_tac "Addr (vp - global_offset) \<in> ptable_trace' (heap s) (root s) va")
    apply clarsimp
    apply (clarsimp simp: pde_tlb_entry'_def)
   apply clarsimp
   apply (subgoal_tac "x \<in> {va. root s r+ pd_idx_offset (addr_val va) \<in> high_ptable (root s)}" )
    apply (clarsimp simp: mmu_layout_def global_set_eq_def)
   apply clarsimp
   apply (case_tac " root s r+ pd_idx_offset (addr_val x) \<in> high_ptable (root s)"; clarsimp)
   apply (subgoal_tac "pt_walk (asid s) (heap s) (root s) va = pt_walk (asid s) (heap s) (root s) x")
    apply (clarsimp simp: mmu_layout_def kernel_mappings_def global_mappings_def global_mappings'_def)
    apply (drule_tac x = "root s" in bspec)
     apply (simp add: rootsI)
    apply clarsimp
    apply (drule_tac x = "addr_val x" in spec)
    apply (drule_tac x = "addr_val x" in spec)
    apply (clarsimp simp: non_global_def pt_walk_def map_opt_def pdc_walk_def pte_tlb_entry_def to_tlb_flags_def tag_conv_def 
      split: option.splits pde.splits pte.splits)
   apply (rule va_entry_set_pt_palk_same', simp add: is_fault_def, simp)
  apply (rename_tac v)
  apply (rule_tac a = "the (pt_walk (asid s) (heap s) (root s) v)" in UN_I)
   apply (clarsimp simp: global_entries_def ran_def)
   apply (rule conjI)
    apply (rule_tac x = v in exI)
    apply (rule conjI)
     apply clarsimp
     apply (subgoal_tac "v \<in> {va. p_state.root s r+ pd_idx_offset (addr_val va) \<in> high_ptable (root s)}")
      prefer 2
      apply (clarsimp simp: mmu_layout_def global_set_eq_def)
     apply clarsimp
     apply (clarsimp simp: mmu_layout_def kernel_mappings_def global_mappings_def global_mappings'_def)
     apply (drule_tac x = "root s" in bspec)
  using root_map_rootsD apply blast
     apply (clarsimp)
     apply (drule_tac x = "addr_val v" in spec)
     apply (drule_tac x = "addr_val v" in spec)
     apply (clarsimp simp: ptable_trace'_def k_phy_ad_def get_pde'_def decode_heap_pde'_def)
    apply (clarsimp)
    apply (subgoal_tac "pt_walk (asid s) (heap s) (root s) v \<noteq> None")
     apply clarsimp
  using mmu_layout_global_set_pt_walk_pair pt_walk_pair_no_fault_pt_walk apply blast
   apply (subgoal_tac "v \<in> (\<Union>x\<in>global_entries (ran (pt_walk (asid s) (heap s) (root s))). range_of x)")
    apply (clarsimp simp: global_entries_def ran_def) 
    apply (subgoal_tac "pt_walk (asid s) (heap s) (root s) a =pt_walk (asid s) (heap s) (root s) v")
     apply clarsimp
    apply (rule va_entry_set_pt_palk_same', simp add: is_fault_def, simp)
   apply (subst mmu_layout_global_set_subset'; simp add: mmu_layout_def global_set_eq_def)
  apply (simp only: pt_walk'_pt_walk [symmetric])
  apply (rule asid_va_entry_range_pt_entry)
  apply (simp only: pt_walk'_pt_walk)
  apply (subgoal_tac "v \<in> {va. p_state.root s r+ pd_idx_offset (addr_val va) \<in> high_ptable (root s)}")
   prefer 2
   apply (clarsimp simp: mmu_layout_def global_set_eq_def)
  apply (clarsimp simp: mmu_layout_def kernel_mappings_def global_mappings_def global_mappings'_def)
  apply (drule_tac x = "root s" in bspec)
  using root_map_rootsD apply blast
  apply (clarsimp)
  apply (drule_tac x = "addr_val v" in spec)
  apply (drule_tac x = "addr_val v" in spec)
  by (clarsimp simp: pt_walk_def map_opt_def is_fault_def pdc_walk_def split: option.splits pde.splits)







lemma map_section_current_asid':
  "\<Turnstile> \<lbrace>\<lambda>s. \<exists> SM w base perms. mmu_layout s \<and> mode s = Kernel \<and> safe_set (kernel_safe s) s \<and> 
      Addr vp \<in> SM \<and>
      SM = kernel_safe s \<and>
      \<I>\<C> s = {} \<and>
      asids_consistent {} s \<and>
      addr_val (root s) >> pd_bits = addr_val (k_phy_ad vp) >> pd_bits \<and>
       is_aligned (addr_val (k_phy_ad vp)) 2 \<and>
      (\<forall>ptp va::vaddr. decode_pde (the (heap s (root s r+ (vaddr_pd_index (addr_val va) << 2)))) = 
            PageTablePDE ptp \<longrightarrow> k_phy_ad vp \<noteq> ptp r+ (vaddr_pt_index (addr_val va) << 2)) \<and>
      heap s (k_phy_ad vp) = Some w \<and>
      decode_pde w = InvalidPDE \<and> 
      decode_pde pde = SectionPDE base perms \<and> arm_p_nG perms = 1 \<rbrace>
      Const vp ::= Const pde
   \<lbrace>\<lambda>s. \<I>\<C> s = {}\<rbrace>"
  apply (vcgm vcg: weak_pre_write')
  apply (rule conjI)
   apply (clarsimp simp: \<I>\<C>_def)
  apply (rule_tac x = "k_phy_ad vp" in exI)
  apply (clarsimp simp:  \<I>\<C>_def)
  apply (rule conjI)
   prefer 2
   apply (metis (no_types, hide_lams) addr_val.simps k_phy_ad_def kernel_region_offset')
  apply (clarsimp simp: incon_comp_def ptable_comp_def)
  apply (case_tac "k_phy_ad vp \<in>  ptable_trace' (heap s) (root s) (Addr x)")
   defer
   apply (frule_tac a = "asid s" and v = pde in pt_walk_pair_pt_trace_upd, simp)
  apply (subgoal_tac " pt_walk_pair (asid s) (heap s) (p_state.root s) (Addr x) = Fault")
   apply (clarsimp simp: entry_leq_def)
  apply (clarsimp simp: ptable_trace'_def Let_def split: pde.splits)
   apply (clarsimp simp: pt_walk_pair_def pdc_walk_def get_pde'_def decode_heap_pde'_def)
  apply (erule_tac disjE)
   defer
   apply clarsimp
  by (metis (no_types, hide_lams) addr_addr_sub addr_sub_def addr_val.simps decode_pde_def inc.simps(1) 
      inc.simps(2) k_phy_ad_def word_size_bits_def)



lemma unmap_map_section:
  "\<Turnstile> \<lbrace>\<lambda>s. \<exists> SM w base perms. mmu_layout s \<and> mode s = Kernel \<and> safe_set (kernel_safe s) s \<and> 
      Addr vp \<in> SM \<and>
      SM = kernel_safe s \<and>
      \<I>\<C> s = {} \<and>
      asids_consistent {} s \<and>
      addr_val (root s) >> pd_bits = addr_val (k_phy_ad vp) >> pd_bits \<and>
       is_aligned (addr_val (k_phy_ad vp)) 2 \<and>
      (\<forall>ptp va::vaddr. decode_pde (the (heap s (root s r+ (vaddr_pd_index (addr_val va) << 2)))) = 
            PageTablePDE ptp \<longrightarrow> k_phy_ad vp \<noteq> ptp r+ (vaddr_pt_index (addr_val va) << 2)) \<and>
      heap s (k_phy_ad vp) = Some w \<and>
      decode_pde w = InvalidPDE \<and> 
      decode_pde pde = SectionPDE base perms \<and> arm_p_nG perms = 1 \<rbrace>
      Const vp ::= Const pde
   \<lbrace>\<lambda>s. \<I>\<C> s = {} \<and> asids_consistent {} s \<rbrace>"
  apply (rule hoare_post_conj, rule map_section_current_asid')
  apply (rule weak_pre)
   apply (rule map_section_current_asid)
  by blast


lemma pt_walk_section':
  "\<lbrakk> hp p = Some pde; addr_val r >> pd_bits = addr_val p >> pd_bits;  
     \<forall>ptp va:: vaddr. decode_pde (the (hp (r r+ (vaddr_pd_index (addr_val va) << 2)))) = PageTablePDE ptp \<longrightarrow>
       p \<noteq> ptp r+ (vaddr_pt_index (addr_val va) << 2);
           decode_pde pde =  SectionPDE base perms; decode_pde pde' = InvalidPDE \<rbrakk> \<Longrightarrow>
          pt_walk a (hp(p \<mapsto> pde')) r = 
      (\<lambda>va. if p\<in> ptable_trace' hp r va  then None else pt_walk a hp r va)"
 apply rule+
  apply (case_tac "p \<in> ptable_trace' hp r va")
   defer
   apply clarsimp
   apply (rule pt_walk_pt_trace_upd', simp)
  apply clarsimp
  apply (clarsimp simp:  ptable_trace'_def Let_def split: pde.splits)
   apply (clarsimp simp: pt_walk_def map_opt_def split: option.splits)
  by (clarsimp simp: pdc_walk_def get_pde'_def decode_heap_pde'_def split: option.splits)


lemma map_unmap_section:
  "\<Turnstile> \<lbrace>\<lambda>s. \<exists> SM w base perms pde. mmu_layout s \<and> mode s = Kernel \<and> safe_set (kernel_safe s) s \<and> 
      Addr vp \<in> SM \<and>
      SM = kernel_safe s \<and>
      \<I>\<C> s = {} \<and>
      asids_consistent {} s \<and>
      addr_val (root s) >> pd_bits = addr_val (k_phy_ad vp) >> pd_bits \<and>
       is_aligned (addr_val (k_phy_ad vp)) 2 \<and>
      (\<forall>ptp va::vaddr. decode_pde (the (heap s (root s r+ (vaddr_pd_index (addr_val va) << 2)))) = 
            PageTablePDE ptp \<longrightarrow> k_phy_ad vp \<noteq> ptp r+ (vaddr_pt_index (addr_val va) << 2)) \<and>
      heap s (k_phy_ad vp) = Some pde \<and>
      decode_pde pde = SectionPDE base perms \<and> arm_p_nG perms = 1 \<and>
      decode_pde pde' = InvalidPDE \<rbrace>
      Const vp ::= Const pde'
    \<lbrace>\<lambda>s.  asids_consistent {asid s} s\<rbrace>"
  apply (vcgm vcg: weak_pre_write')
  apply (subgoal_tac "k_phy_ad vp \<in>  ptable_footprint s (root s)")
   prefer 2 
   apply (rule first_level_ptable_trace_defined, clarsimp simp: k_phy_ad_def, 
      simp add: mmu_layout_def aligned_def, simp add: k_phy_ad_def)
  apply (rule conjI)
   apply (clarsimp simp: asids_consistent_def safe_set_def con_set_def)
  apply (subgoal_tac "ptable_lift' (heap s) (root s) (Addr vp) = Some (Addr vp r-  global_offset)" , clarsimp)
   prefer 2
   apply (clarsimp simp: kernel_region_offset')
  apply (subgoal_tac "Addr (vp - global_offset) \<notin> root_map_area")
   prefer 2
   apply (subgoal_tac "root s \<in> set (root_log s)")
    apply (clarsimp simp: mmu_layout_def kernel_data_def k_phy_ad_def, blast) 
   apply (clarsimp simp: mmu_layout_def root_log_def)
   apply (rule_tac x = "addr_val (root s)" in image_eqI, simp, force)
  apply (clarsimp simp: asids_consistent_def)
  apply (rule conjI)
   apply (subgoal_tac "root_map (s\<lparr> heap := heap s(Addr (vp - global_offset) \<mapsto> pde)\<rparr>) = root_map s")
    apply clarsimp
    apply (drule_tac x = r in spec, drule_tac x = a in spec, clarsimp)
    apply (clarsimp simp: ptable_comp_def)
    apply (drule_tac x = x in spec)
    apply (subgoal_tac " pt_walk_pair a (heap s(Addr (vp - global_offset) \<mapsto> pde')) r x = pt_walk_pair a (heap s) r x")
     apply force
    apply (rule pt_walk_pair_pt_trace_upd')
    apply (subgoal_tac " Addr (vp - global_offset) \<notin> ptable_footprint s r")
  using ptable_footprint_def apply blast
    apply clarsimp
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
     apply (clarsimp simp: ptable_footprint_def) 
  using mmu_layout_roots_elem apply blast
    apply rule
     apply (clarsimp simp: roots_def mmu_layout_def root_log_def)
     apply (rule_tac x = "addr_val r" in image_eqI, simp, force)
  using mmu_layout_def rootsI apply force
   apply (clarsimp simp: k_phy_ad_def ptable_footprint_def)
  apply (clarsimp simp: roots_def)
  apply (subgoal_tac "(\<Union>x\<in>global_entries (ran (pt_walk (asid s)  (heap s(Addr (vp - global_offset) \<mapsto> pde')) (root s))). range_of x) = global_set s")
   apply clarsimp
   apply (thin_tac "(\<Union>x\<in>global_entries (ran (pt_walk (asid s) (heap s(Addr (vp - global_offset) \<mapsto> pde')) (root s))). range_of x) =   global_set s")
   apply (case_tac "r = root s")
    apply clarsimp
    apply (drule_tac x = "root s" in spec)
    apply (drule_tac x = "root s" in spec)
    apply (subgoal_tac "root s \<in> set (root_log s)")
     prefer 2
     apply (drule_tac s = s and v = pde' in roots_upd', simp add: roots_def)
    apply (drule_tac x = a in spec) 
    apply (rule Int_emptyI)
    apply (case_tac "x \<in> fst (ptable_snapshot s a)")
     apply blast
    apply clarsimp
    apply (subgoal_tac "x \<notin> ptable_comp (snd (ptable_snapshot s a)) (pt_walk_pair a (heap s) (root s))")
     prefer 2
     apply blast
    apply (thin_tac "root_map s (root s) = Some a \<and> a \<noteq> asid s \<longrightarrow>
        fst (ptable_snapshot s a) = {} \<and> ptable_comp (snd (ptable_snapshot s a)) (pt_walk_pair a (heap s) (root s)) = {}")
    apply (clarsimp simp: ptable_comp_def entry_leq_def)
    apply (subgoal_tac "pt_walk_pair a (heap s) (root s) x = pt_walk_pair a (heap s(Addr (vp - global_offset) \<mapsto> pde')) (root s) x")
     apply clarsimp
    apply (rule pt_walk_pair_pt_trace_upd)
    apply (subgoal_tac "ptable_trace' (heap s) (root s) x \<subseteq> high_ptable(root s)")
     apply (clarsimp simp: kernel_safe_def   k_phy_ad_def)
     apply (clarsimp simp: vas_of_current_state_mapped_to_global_mappings_of_all_processes_def vas_mapped_by_global_mappings_def)
     apply (rule_tac x = "root s" in bexI)
      apply (clarsimp simp: mmu_layout_def kernel_mappings_def global_mappings_def global_mappings'_def)
      apply (drule_tac x = "root s" in bspec)
       apply (drule_tac s = s and v = pde' in roots_upd', simp add: roots_def)
      apply clarsimp
      apply (drule_tac x = vp in spec)
      apply clarsimp
      apply (clarsimp simp: ptable_trace'_def Let_def pd_idx_offset_def get_pde'_def decode_heap_pde'_def split: option.splits pde.splits)
  using roots_def apply blast
    apply (clarsimp simp: mmu_layout_def global_set_eq_def kernel_mappings_def global_mappings_def global_mappings'_def)
    apply (drule_tac x = "root s" in bspec)
     apply (drule_tac s = s and v = pde' in roots_upd', simp add: roots_def)
    apply clarsimp
    apply (drule_tac x = "addr_val x" in spec)
    apply clarsimp
    apply (subgoal_tac " root s r+ pd_idx_offset (addr_val x) \<in> high_ptable (root s)" )
     apply (clarsimp simp: ptable_trace'_def Let_def pd_idx_offset_def   split: option.splits pde.splits)
    apply blast
   apply (drule_tac x = r in spec)
   apply (drule_tac x = r in spec)
   apply (subgoal_tac "r \<in> set (root_log s)")
    prefer 2
    apply (drule_tac s = s and v = pde' in roots_upd', simp add: roots_def)
   apply (drule_tac x = a in spec)
   apply (rule Int_emptyI)
   apply (case_tac "x \<in> fst (ptable_snapshot s a)")
    apply blast
   apply clarsimp
   apply (subgoal_tac "x \<notin> ptable_comp (snd (ptable_snapshot s a)) (pt_walk_pair a (heap s) r)")
    prefer 2
    apply blast
   apply (thin_tac  "root_map s r = Some a \<and> a \<noteq> asid s \<longrightarrow> fst (ptable_snapshot s a) = {} \<and> ptable_comp (snd (ptable_snapshot s a)) (pt_walk_pair a (heap s) r) = {}")
   apply (clarsimp simp: ptable_comp_def entry_leq_def)
   apply (subgoal_tac "pt_walk_pair a (heap s) r x = pt_walk_pair a (heap s(Addr (vp - global_offset) \<mapsto> pde')) r x")
    apply clarsimp
   apply (rule pt_walk_pair_pt_trace_upd)
   apply (clarsimp simp: k_phy_ad_def ptable_footprint_def mmu_layout_def )
   apply (drule non_overlapping_tables_from_kernel_data)
   apply (clarsimp simp: non_overlapping_tables_def ptable_footprint_def)
   apply (drule_tac x = "root s"  in spec)
   apply (drule_tac x = r  in spec)
  using  root_map_rootsD roots_def apply blast
  apply (frule_tac r = "root s" and a = "asid s" and base = base and perms = perms 
      in pt_walk_section', simp, simp add: k_phy_ad_def, simp, simp, simp, simp) 
  apply (simp add: k_phy_ad_def) 
  apply safe
   apply (clarsimp simp: ran_def global_entries_def)
   apply (rename_tac va)
   apply (case_tac "Addr (vp - global_offset) \<in> ptable_trace' (heap s) (root s) va")
    apply clarsimp
   apply (clarsimp simp: pde_tlb_entry'_def)
   apply (subgoal_tac "x \<in> {va. root s r+ pd_idx_offset (addr_val va) \<in> high_ptable (root s)}" )
    apply (clarsimp simp: mmu_layout_def global_set_eq_def)
   apply clarsimp
   apply (case_tac " root s r+ pd_idx_offset (addr_val x) \<in> high_ptable (root s)"; clarsimp)
   apply (subgoal_tac "pt_walk (asid s) (heap s) (root s) va = pt_walk (asid s) (heap s) (root s) x")
    apply (clarsimp simp: mmu_layout_def kernel_mappings_def global_mappings_def global_mappings'_def)
    apply (drule_tac x = "root s" in bspec)
     apply (simp add: rootsI)
    apply clarsimp
    apply (drule_tac x = "addr_val x" in spec)
    apply (drule_tac x = "addr_val x" in spec)
    apply (clarsimp simp: non_global_def pt_walk_def map_opt_def pdc_walk_def pte_tlb_entry_def to_tlb_flags_def tag_conv_def 
      split: option.splits pde.splits pte.splits)
   apply (rule va_entry_set_pt_palk_same', simp add: is_fault_def, simp)
  apply (rename_tac v)
  apply (rule_tac a = "the (pt_walk (asid s) (heap s) (root s) v)" in UN_I)
   apply (clarsimp simp: global_entries_def ran_def)
   apply (rule conjI)
    apply (rule_tac x = v in exI)
    apply (rule conjI)
     apply clarsimp
     apply (subgoal_tac "v \<in> {va. p_state.root s r+ pd_idx_offset (addr_val va) \<in> high_ptable (root s)}")
      prefer 2
      apply (clarsimp simp: mmu_layout_def global_set_eq_def)
     apply clarsimp
     apply (clarsimp simp: mmu_layout_def kernel_mappings_def global_mappings_def global_mappings'_def)
     apply (drule_tac x = "root s" in bspec)
  using root_map_rootsD apply blast
     apply (clarsimp)
     apply (drule_tac x = "addr_val v" in spec)
     apply (drule_tac x = "addr_val v" in spec)
     apply (clarsimp simp: ptable_trace'_def k_phy_ad_def get_pde'_def decode_heap_pde'_def)
    apply (clarsimp)
    apply (subgoal_tac "pt_walk (asid s) (heap s) (root s) v \<noteq> None")
     apply clarsimp 
    apply (frule_tac va = v and a = "asid s" in  mmu_layout_global_set_pt_walk_pair, simp)
  using pt_walk_pair_no_fault_pt_walk apply blast
   apply (subgoal_tac "v \<in> (\<Union>x\<in>global_entries (ran (pt_walk (asid s) (heap s) (root s))). range_of x)")
    apply (clarsimp simp: global_entries_def ran_def) 
    apply (subgoal_tac "pt_walk (asid s) (heap s) (root s) a =pt_walk (asid s) (heap s) (root s) v")
     apply clarsimp
    apply (rule va_entry_set_pt_palk_same', simp add: is_fault_def, simp)
   apply (subst mmu_layout_global_set_subset'; simp add: mmu_layout_def global_set_eq_def)
  apply (simp only: pt_walk'_pt_walk [symmetric])
  apply (rule asid_va_entry_range_pt_entry)
  apply (simp only: pt_walk'_pt_walk)
  apply (subgoal_tac "v \<in> {va. p_state.root s r+ pd_idx_offset (addr_val va) \<in> high_ptable (root s)}")
   prefer 2
   apply (clarsimp simp: mmu_layout_def global_set_eq_def)
  apply (clarsimp simp: mmu_layout_def kernel_mappings_def global_mappings_def global_mappings'_def)
  apply (drule_tac x = "root s" in bspec)
  using root_map_rootsD apply blast
  apply (clarsimp)
  apply (drule_tac x = "addr_val v" in spec)
  apply (drule_tac x = "addr_val v" in spec)
  apply (clarsimp simp: pt_walk_def map_opt_def is_fault_def pdc_walk_def split: option.splits pde.splits)
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
  apply (clarsimp simp: asids_consistent_def Times_Diff_distrib1 Diff_Int_distrib2 ptable_comp_def entry_leq_def roots_def')
  by blast

  



lemma flush_one_asid_rest:
  "\<Turnstile> \<lbrace>\<lambda>s. mmu_layout s \<and> mode s = Kernel \<and> safe_set (kernel_safe s) s\<rbrace>
       Flush (flushASID a)
   \<lbrace>\<lambda>s. mmu_layout s \<and> mode s = Kernel \<and> safe_set (kernel_safe s) s\<rbrace>"
  apply vcgm
  by (simp add: mmu_layout_def safe_set_def safe_memory_def con_set_def ptrace_set_def kernel_data_def
   global_set_eq_def aligned_def is_aligned_def pd_bits_def roots_def)
  

end
