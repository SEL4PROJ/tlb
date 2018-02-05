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
  shows "global_mappings_of_all_processes s = global_mappings_of_all_processes s'"
  using assms by (simp add: global_mappings_of_all_processes_def root_log_heap_eq[OF assms] roots_def)

interpretation kernel_mappings: heap_only global_mappings_of_all_processes
  by unfold_locales (rule kernel_mappings_heap_eq)



lemma asids_consistentD:
  "\<lbrakk> asids_consistent {} s; root_map s (Addr r) = Some a; a \<noteq> asid s \<rbrakk> \<Longrightarrow>
     ptable_snapshot s a v \<noteq> Incon \<and> ((ptable_snapshot s) a v = Miss \<or> 
                          (ptable_snapshot s) a v = Hit (pt_walk a (heap s) (Addr r) v) )"
  apply (clarsimp simp: asids_consistent_def)
  by (metis lookup_type.distinct(1) lookup_type.distinct(5))
  


lemma pde_comp_def_x:
 "ptable_comp a hp hp' rt rt' =
  (let walk = pt_walk a hp rt; walk' = pt_walk a hp' rt'
  in  {va. \<not>is_fault (walk va) \<and> \<not> is_fault (walk' va) \<and> walk va \<noteq> walk' va \<or> 
          \<not>is_fault (walk va) \<and> is_fault (walk' va)})"
 by (auto simp add: ptable_comp_def Let_def)




lemma pde_comp_def:
 "ptable_comp a hp hp' rt rt' \<equiv>
  let walk = pt_walk a hp rt; walk' = pt_walk a hp' rt'
  in  {va. \<not>is_fault (walk va) \<and> \<not> is_fault (walk' va) \<and> walk va \<noteq> walk' va \<or> 
          \<not>is_fault (walk va) \<and> is_fault (walk' va)}"
 by (simp add: pde_comp_def_x)


definition
  \<I>\<C> :: "p_state \<Rightarrow> 32 word set"
where
  "\<I>\<C> s \<equiv>  {vp. Addr vp \<in> incon_set s}" 


lemma asid_con_mode_upd:
  "asids_consistent S (mode_update upd s) = asids_consistent S s"
  by (clarsimp simp: asids_consistent_def)



lemma [simp]:
  "a \<noteq> a' \<Longrightarrow>
     incon_load_incon (snapshot_update_current'2 snp iset hp' rt' a) a' hp  = 
     incon_load_incon snp a' hp "
  by (clarsimp simp: incon_load_incon_def snapshot_update_current'2_def snapshot_update_current2_def)

lemma  [simp]:
  "a \<noteq> a' \<Longrightarrow> 
     incon_load2 (snapshot_update_current'2 snap is hp' rt' a) a' hp rt =
     incon_load2 snap  a' hp rt"
  by (clarsimp simp: incon_load2_def snapshot_update_current'2_def)

lemma asid_rewrite:
  "\<lbrakk>asids_consistent {} 
     (s\<lparr>root := Addr r, asid := a, incon_set := {}, ptable_snapshot := pt,  mode := User\<rparr>);  0 \<notin> ran (root_map s) ; 0 \<noteq> asid s\<rbrakk>  \<Longrightarrow> 
    asids_consistent {}  (s\<lparr>root := Addr r, asid := a, incon_set := {}, ptable_snapshot := snapshot_update_current'2 pt is'  (heap s) (Addr r) 0, mode := User\<rparr>)"
  by (clarsimp simp: asids_consistent_def snapshot_update_current'2_def snapshot_update_current2_def ran_def)

lemma asid_rewrite2:
  "\<lbrakk>asids_consistent {} 
     (s\<lparr> incon_set := {},  ptable_snapshot := pt,   mode := User\<rparr>);  0 \<notin> ran (root_map s) ; 0 \<noteq> asid s\<rbrakk>  \<Longrightarrow> 
    asids_consistent {}   (s\<lparr> incon_set := {},    ptable_snapshot :=   snapshot_update_current'2 pt  is'  (heap s) (root s) 0, mode := User\<rparr>)"
  by (clarsimp simp: asids_consistent_def snapshot_update_current'2_def snapshot_update_current2_def ran_def)

lemma asids_consistent_def2:
  "asids_consistent S s = 
  (\<forall>r a. root_map s r = Some a \<longrightarrow> a \<notin> S \<union> {asid s} \<longrightarrow> 
  (\<forall>v. ptable_snapshot s a v \<noteq> Incon \<and> (ptable_snapshot s a v = Miss \<or> ptable_snapshot s a v = Hit (pt_walk a (heap s) r v))))"
  apply (clarsimp simp: asids_consistent_def)
  by (metis lookup_type.distinct(1) lookup_type.distinct(5))



lemma context_switch_invariants:
  "\<Turnstile> \<lbrace> \<lambda>s. mmu_layout s \<and> asids_consistent {} s \<and> mode s = Kernel \<and>  \<I>\<C> s = {} \<and>
            0 \<notin> ran (root_map s)  \<and> root_map s (Addr r) = Some a\<rbrace>
            UpdateASID 0 ;; UpdateTTBR0 (Const r) ;; UpdateASID a ;; SetMode User
      \<lbrace>\<lambda>s. mmu_layout s \<and> \<I>\<C> s = {} \<and> mode s = User \<and> asids_consistent {} s \<rbrace>"
  apply vcgm
  apply (subgoal_tac "a \<noteq> 0")
   prefer 2  apply (clarsimp simp: ran_def)
  apply (rule conjI)
   apply (clarsimp simp: mmu_layout_def kernel_data_def)
  apply (rule conjI, clarsimp simp: \<I>\<C>_def)
   apply (clarsimp simp: incon_load2_def incon_load_incon_def snapshot_update_current'2_def snapshot_update_current2_def split: if_split_asm, rule conjI, clarsimp)
    apply (rule conjI, clarsimp)
     apply (subgoal_tac "Addr r = root s", clarsimp)
     apply (clarsimp simp: mmu_layout_def ran_def partial_inj_def, force)
    apply (clarsimp simp: asids_consistent_def2)
    apply (drule_tac x = "Addr r" in spec, drule_tac x = a in spec, simp, drule_tac x = "Addr x" in spec)
    apply (erule conjE, erule disjE, clarsimp, clarsimp)
   apply (clarsimp simp: asids_consistent_def2)
   apply (drule_tac x = "Addr r" in spec, drule_tac x = a in spec, clarsimp)
   apply (drule_tac x = "Addr x" in spec, erule conjE, erule disjE, clarsimp, clarsimp)
  apply (subgoal_tac "asid s \<noteq> 0 ")
   prefer 2
   apply (clarsimp simp: mmu_layout_def ran_def)
  apply (case_tac "a \<noteq> asid s")
   apply (subgoal_tac "incon_load_incon (ptable_snapshot s) a (heap s)  = {}")
    prefer 2
    apply (clarsimp simp: incon_load_incon_def asids_consistent_def2)
   apply (subgoal_tac "incon_load2 (ptable_snapshot s) a (heap s) (Addr r) = {}")
    prefer 2
    apply (clarsimp simp: incon_load2_def asids_consistent_def2)  
    apply (drule_tac x = "Addr r" in spec, drule_tac x = a in spec , simp, drule_tac x = x in spec, force)
   apply clarsimp
   apply (rule asid_rewrite; clarsimp simp: asids_consistent_def2)
   apply (rule conjI)
    apply (clarsimp simp: snapshot_update_current'2_def snapshot_update_current2_def)
    apply (rule conjI)
     apply (clarsimp simp : \<I>\<C>_def, drule_tac x = "addr_val v" in spec, simp)
    apply (clarsimp simp : \<I>\<C>_def, drule_tac x = "addr_val v" in spec, simp)
   apply (case_tac "aa \<noteq> asid s")
    apply (subgoal_tac "snapshot_update_current'2 (ptable_snapshot s) (incon_set s) (heap s) (root s) (asid s) aa v =
                        (ptable_snapshot s)  aa v") 
     apply (drule_tac x = ra in spec, drule_tac x = aa in spec, clarsimp)
    apply (clarsimp simp: snapshot_update_current'2_def snapshot_update_current2_def)+
   apply (rule)+            
     apply (clarsimp simp : \<I>\<C>_def, drule_tac x = "addr_val v" in spec, simp)
    apply (subgoal_tac "ra =  root s", simp)
    apply (clarsimp simp: mmu_layout_def ran_def partial_inj_def, fastforce)
   apply (clarsimp simp : \<I>\<C>_def, drule_tac x = "addr_val v" in spec, simp)
  apply (subgoal_tac "incon_load_incon (snapshot_update_current'2 (ptable_snapshot s) (incon_set s) (heap s) (root s) (asid s))
                      (asid s) (heap s) = {}")
   prefer 2
   apply (clarsimp simp: incon_load_incon_def snapshot_update_current'2_def snapshot_update_current2_def)
   apply (rule)+
    apply (clarsimp simp : \<I>\<C>_def, drule_tac x = "addr_val x" in spec, simp)
   apply (rule)+
   apply (clarsimp simp : \<I>\<C>_def, drule_tac x = "addr_val x" in spec, simp)
  apply simp
  apply (subgoal_tac "Addr r = root s")
   prefer 2
   apply (clarsimp simp: mmu_layout_def ran_def partial_inj_def, fastforce)
  apply (subgoal_tac "incon_load2 (snapshot_update_current'2 (ptable_snapshot s) (incon_set s) (heap s) (root s) (asid s)) (asid s) (heap s) (root s) =
                        {}")
   prefer 2
   apply (clarsimp simp: asids_consistent_def incon_load2_def snapshot_update_current'2_def 
      snapshot_update_current2_def)
  apply simp
  apply (rule asid_rewrite2; clarsimp simp: asids_consistent_def2)
  apply (rule conjI)
   apply (clarsimp simp: snapshot_update_current'2_def snapshot_update_current2_def)
  apply (case_tac "aa \<noteq> asid s")
   apply (subgoal_tac "snapshot_update_current'2 (ptable_snapshot s) (incon_set s) (heap s) (root s) (asid s) aa v =
                       (ptable_snapshot s)  aa v")
    apply (simp only:)
   apply (drule_tac x = ra in spec, drule_tac x = aa in spec, clarsimp)
  by (clarsimp simp: snapshot_update_current'2_def snapshot_update_current2_def)+


end



