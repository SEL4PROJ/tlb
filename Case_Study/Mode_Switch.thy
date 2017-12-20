theory Mode_Switch
                  
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

end

lemma ptable_footprint_heap_eq:
  "heap s = heap s' \<Longrightarrow> ptable_footprint s = ptable_footprint s'"
  by (rule ext) (simp add: ptable_footprint_def)

interpretation ptable_footprint: heap_only ptable_footprint
  by unfold_locales (rule ptable_footprint_heap_eq)

lemma root_log_heap_eq:
  "heap s = heap s' \<Longrightarrow> root_log s = root_log s'"
  by (simp add: root_log_def)

interpretation rt_log: heap_only root_log
  by unfold_locales (rule root_log_heap_eq)

lemma root_map_heap_eq:
  "heap s = heap s' \<Longrightarrow> root_map s = root_map s'"
  by (simp add: root_map_def root_set_def)

interpretation rt_map: heap_only root_map
  by unfold_locales (rule root_map_heap_eq)

lemma kernel_data_heap_eq:
  assumes "heap s = heap s'"
  shows "kernel_data s = kernel_data s'"
  using assms
  by (simp add: kernel_data_def ptable_footprint_heap_eq[OF assms] root_log_def)

interpretation kernel_data: heap_only kernel_data
  by unfold_locales (rule kernel_data_heap_eq)

lemma non_overlapping_tables_heap_eq:
  assumes "heap s = heap s'"
  shows "non_overlapping_tables s = non_overlapping_tables s'"
  by (simp add: non_overlapping_tables_def root_log_heap_eq[OF assms] ptable_footprint_heap_eq[OF assms])

interpretation overl: heap_only non_overlapping_tables
  by unfold_locales (rule non_overlapping_tables_heap_eq)

lemma user_mappings_heap_eq:
  assumes "heap s = heap s'"
  shows "user_mappings s = user_mappings s'"
  using assms by (simp add: user_mappings_def root_log_heap_eq[OF assms])

interpretation user_mappings: heap_only user_mappings
  by unfold_locales (rule user_mappings_heap_eq)

lemma kernel_mappings_heap_eq:
  assumes "heap s = heap s'"
  shows "global_mappings_of_all_processes s = global_mappings_of_all_processes s'"
  using assms by (simp add: global_mappings_of_all_processes_def root_log_heap_eq[OF assms])

interpretation kernel_mappings: heap_only global_mappings_of_all_processes
  by unfold_locales (rule kernel_mappings_heap_eq)

lemma ptable_comp_asid:
  "\<lbrakk> (a, v) \<in> ptable_comp b hp hp' rt rt'; a \<noteq> b \<rbrakk> \<Longrightarrow> False"
  by (auto simp: ptable_comp_def)

lemma asids_consistentD:
  "\<lbrakk> asids_consistent {} s; root_map s (Addr r) = Some a \<rbrakk> \<Longrightarrow> (a, v) \<notin> incon_set s"
  by (clarsimp simp: asids_consistent_def ran_def) blast



lemma pde_comp_def_x:
 "ptable_comp a hp hp' rt rt' =
  (let walk = pt_walk a hp rt; walk' = pt_walk a hp' rt'
  in {a} \<times>
     {va. \<not>is_fault (walk va) \<and> \<not> is_fault (walk' va) \<and> walk va \<noteq> walk' va \<or> 
          \<not>is_fault (walk va) \<and> is_fault (walk' va)})"
 by (auto simp add: ptable_comp_def Let_def)




lemma pde_comp_def:
 "ptable_comp a hp hp' rt rt' \<equiv>
  let walk = pt_walk a hp rt; walk' = pt_walk a hp' rt'
  in {a} \<times>
     {va. \<not>is_fault (walk va) \<and> \<not> is_fault (walk' va) \<and> walk va \<noteq> walk' va \<or> 
          \<not>is_fault (walk va) \<and> is_fault (walk' va)}"
 by (simp add: pde_comp_def_x)


definition
  \<I>\<C> :: "p_state \<Rightarrow> 32 word set"
where
  "\<I>\<C> s \<equiv>  {vp. (asid s, Addr vp) \<in> incon_set s}" 



(* have new conditions for tlb_snapshot *)


(* it is a lookup type, which means that we have to assume that from tlb_rel that, 
  in the start, the tlb_snanpshot will be miss, no incon and no hit, so lets assume that  *)


definition
  "snap_not_incon S s \<equiv> \<forall>a\<in>(ran (root_map s) - S). \<forall>v. ptable_snapshot s a v \<noteq> Incon"

(* we can only specify the subset condition *)

definition
  "snap_miss_or_consistent_hit snp a mem rt \<equiv> \<forall>v. snp a v = Miss \<or> snp a v = Hit (pt_walk a mem rt v)"


(* context switch code from sel4
     /*
     * On ARMv7, speculative refills that complete between switching
     * ASID and PD can cause TLB entries to be Tagged with the wrong
     * ASID. The correct method to avoid this problem is to
     * either cycle the context switch through a reserved ASID or
     * through a page directory that has only global mappings.
     * The reserved Page directory method has shown to perform better
     * than the reserved ASID method.
     *
     * We do not call setCurrentPD here as we want to perform a
     * minimal number of DSB and ISBs and the second PD switch we
     * do does not need a DSB
     */
    dsb();
    writeTTBR0(addrFromPPtr(armKSGlobalPD));
    isb();
    setHardwareASID(hw_asid);
    writeTTBR0(addrFromPPtr(cap_pd));
    isb();

*)

definition "snp_incon_constraint S s \<equiv> {(a,v). a\<in>(ran (root_map s) - S) \<and> ptable_snapshot s a v = Incon }  \<subseteq>  incon_set s"

(* we assume that the flush has happened after write to the page table *)

lemma
  "\<lbrakk>snp_incon_constraint S s ; asids_consistent {} s \<rbrakk>  \<Longrightarrow> snap_not_incon S s"
  apply (clarsimp simp: snp_incon_constraint_def ptable_snapshot_def asids_consistent_def ran_def snap_not_incon_def)
  by blast


lemma new_context_switch:
  "\<Turnstile> \<lbrace> \<lambda>s. mmu_layout s \<and> asids_consistent {} s \<and> mode s = Kernel \<and> snp_incon_constraint {} s \<and>  
           snap_miss_or_consistent_hit (ptable_snapshot s) a (heap s) (Addr r) \<and> 
            0 \<notin> ran (root_map s) \<and> root_map s (Addr r) = Some a \<and> Addr r \<in> root_log s\<rbrace>
            UpdateASID 0 ;; UpdateTTBR0 (Const r) ;; UpdateASID a ;; SetMode User
      \<lbrace>\<lambda>s. mmu_layout s \<and> \<I>\<C> s = {} \<and> mode s = User \<and> asids_consistent {} s \<rbrace>"
  (* may not be true in its current form *)

(* what should we have for the paper? same concept as asid 0?*)

  apply vcgm
  apply (rule conjI)
   apply (clarsimp simp: mmu_layout_def)  
  apply (rule conjI)
   apply (clarsimp simp: \<I>\<C>_def asids_consistentD)
   apply (rule conjI, clarsimp)
    apply (clarsimp simp: incon_load_def  snapshot_update_current'_def  snapshot_update_current_def ran_def)
   apply (rule conjI)
    apply (clarsimp simp: asids_consistent_def pde_comp_def Let_def times_Int_times Int_Un_distrib ran_def)
   apply clarsimp
   apply (simp only: incon_load_def  snapshot_update_current'_def  snapshot_update_current_def  snapshot_update_new'_def snapshot_update_new_def)
  apply safe [1]




(*
   apply (clarsimp simp: incon_load_def  snapshot_update_current'_def  snapshot_update_current_def  snapshot_update_new'_def snapshot_update_new_def)
   apply safe [1]
     apply (clarsimp simp: ran_def)
    apply (clarsimp simp: asids_consistent_def pde_comp_def Let_def times_Int_times Int_Un_distrib ran_def)
  apply auto [1]
 apply (clarsimp simp: ran_def)
   apply (erule ptable_comp_asid)
   apply (clarsimp simp: ran_def)
  apply (clarsimp simp: asids_consistent_def pde_comp_def Let_def times_Int_times Int_Un_distrib)

*)



  sorry

end



