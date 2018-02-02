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
  by (simp add: kernel_data_area_def ptable_footprint_heap_eq[OF assms] root_log_def
    root_map_def map_of_set_def root_set_def)

interpretation kernel_date_area: heap_only kernel_data_area
  by unfold_locales (rule kernel_date_area_heap_eq)
                                   
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

(*
lemma ptable_comp_asid:
  "\<lbrakk> (a, v) \<in> ptable_comp b hp hp' rt rt'; a \<noteq> b \<rbrakk> \<Longrightarrow> False"
  by (auto simp: ptable_comp_def)
*)



lemma asids_consistentD:
  "\<lbrakk> asids_consistent {} s; root_map s (Addr r) = Some a ; Addr r \<in> root_log s ; a \<noteq> asid s \<rbrakk> \<Longrightarrow>
              (ptable_snapshot s) a v \<noteq> Incon \<and> ((ptable_snapshot s) a v = Miss \<or> 
                                 (ptable_snapshot s) a v = Hit (pt_walk a (heap s) (Addr r) v) )"
  by (clarsimp simp: asids_consistent_def ran_def) 
  

(*
lemma kernel_date_area_asid_consistent_eq:
  assumes "heap s = heap s'"
  shows "asids_consistent {} s = asids_consistent {} s'"
  using assms
  apply (simp add: asids_consistent_def)


interpretation asids_consistent: heap_only "asids_consistent {}"
  by unfold_locales (rule kernel_date_area_heap_eq)
*)

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


(*
definition
  "snap_not_incon S s \<equiv> \<forall>a\<in>(ran (root_map s) - S). \<forall>v. ptable_snapshot s a v \<noteq> Incon"

(* we can only specify the subset condition *)

definition
  "snap_miss_or_consistent_hit snp a mem rt \<equiv> \<forall>v. snp a v = Miss \<or> snp a v = Hit (pt_walk a mem rt v)"
*)


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

(* we assume that the flush has happened after write to the page table *)

(*
lemma asids_diff_incon_load_empty:
  "a \<noteq> a' \<Longrightarrow>  {a} \<times> UNIV \<inter> incon_load snp a' m rt = {}"
  apply (clarsimp simp: incon_load_def) 
  by blast
*)

(*
lemma asids_diff_ptable_comp_empty:
  "a \<noteq> a' \<Longrightarrow>  {a} \<times> UNIV \<inter> ptable_comp a' h h' r r' = {}"
  apply (clarsimp simp: ptable_comp_def) 
  by blast




lemma  asids_diff_snap_update_current_incon_load_same [simp]:
  "a \<noteq> a' \<Longrightarrow> incon_load  (snapshot_update_current' snp iset mem ttbr0 a') a m r = incon_load  snp a m r"
  by (clarsimp simp: incon_load_def snapshot_update_current'_def) 


lemma asids_diff_snap_update_new_incon_load_same [simp]:
  "a \<noteq> a' \<Longrightarrow>  incon_load (snapshot_update_new' snp iset m_to_h h_to_h hp ttbr0 a') a m rt = incon_load snp a m rt"
  by (clarsimp simp: incon_load_def snapshot_update_new'_def) 
 *)


lemma asid_con_mode_upd:
  "asids_consistent S (mode_update upd s) = asids_consistent S s"
  by (clarsimp simp: asids_consistent_def)

(*
lemma asid_con_root_upd:
  "asids_consistent S (root_update upd s) = asids_consistent S s"
  by (clarsimp simp: asids_consistent_def)
*)

(*
lemma asid_con_asid_upd:
  "asids_consistent S (asid_update upd s) = asids_consistent S s"
  by (clarsimp simp: asids_consistent_def)
*)

(*
lemma asid_con_upd [simp]:
  "asids_consistent S (s\<lparr>root := r, asid := a, incon_set := is, ptable_snapshot := snp,   mode := m\<rparr>) = 
                 asids_consistent S (s\<lparr> incon_set := is\<rparr>)"
  by (clarsimp simp: asids_consistent_def)
*)

(*
lemma not_range_asid_con_simp [simp]:
  "  0 \<notin> ran (root_map s)
         \<Longrightarrow> asids_consistent {} (s\<lparr>incon_set := incon_set s \<union> incon_load (ptable_snapshot s) 0 (heap s) (root s) \<union> ptable_comp 0 (heap s) (heap s) (root s) (Addr r) \<union> incon_load (ptable_snapshot s) a (heap s) (Addr r) \<rparr>) = 
      asids_consistent {} (s\<lparr>incon_set := incon_set s \<union> incon_load (ptable_snapshot s) a (heap s) (Addr r) \<rparr>)"
  apply (clarsimp simp: asids_consistent_def incon_load_def ran_def ptable_comp_def) by blast
*)

(*
lemma not_range_asid_con_simp' [simp]:
  "  0 \<notin> ran (root_map s)
         \<Longrightarrow> asids_consistent {}
              (s\<lparr>incon_set := incon_set s \<union> incon_load (ptable_snapshot s) 0 (heap s) (Addr r) \<union> ptable_comp 0 (heap s) (heap s) (Addr r) (Addr r) \<union>
                              incon_load (snapshot_update_current' (ptable_snapshot s) ({asid s} \<times> UNIV \<inter> incon_set s) (heap s) (Addr r) (asid s)) (asid s) (heap s) (Addr r)\<rparr>) = 
     asids_consistent {}
              (s\<lparr>incon_set := incon_set s \<union> incon_load (snapshot_update_current' (ptable_snapshot s) ({asid s} \<times> UNIV \<inter> incon_set s) (heap s) (Addr r) (asid s)) (asid s) (heap s) (Addr r)\<rparr>)"
  apply (clarsimp simp: asids_consistent_def incon_load_def ran_def ptable_comp_def) by blast
*)


lemma [simp]:
  "asid s \<noteq> 0 \<Longrightarrow>
  incon_load_incon (snapshot_update_current'2 (ptable_snapshot s) (incon_set s) (heap s) (root s) (asid s)) 0 (heap s)  = 
   incon_load_incon (ptable_snapshot s) 0 (heap s) "
  by (clarsimp simp: incon_load_incon_def snapshot_update_current'2_def snapshot_update_current2_def)

lemma  [simp]:
  " asid s \<noteq> 0 \<Longrightarrow> 
     incon_load2 (snapshot_update_current'2 (ptable_snapshot s) (incon_set s) (heap s) (root s) (asid s)) 0 (heap s) (root s) =
     incon_load2 (ptable_snapshot s)  0 (heap s) (root s)"
  by (clarsimp simp: incon_load2_def snapshot_update_current'2_def)

lemma [simp]:
  "0 \<noteq> a \<Longrightarrow> incon_load_incon
                      (snapshot_update_current'2
                        (snapshot_update_current'2 (ptable_snapshot s) (incon_set s) (heap s) (root s) (asid s))
                        iset'
                        (heap s) (Addr r) 0)
                      a (heap s)   = 
    incon_load_incon
                      (snapshot_update_current'2 (ptable_snapshot s) (incon_set s) (heap s) (root s) (asid s))
                      a (heap s) "
  by (clarsimp simp: incon_load_incon_def snapshot_update_current'2_def snapshot_update_current2_def)


lemma  [simp]:
  " a \<noteq> asid s \<Longrightarrow> incon_load_incon (snapshot_update_current'2 (ptable_snapshot s) (incon_set s) (heap s) (root s) (asid s)) 
                        a
                      (heap s) 
                        = 
     incon_load_incon (ptable_snapshot s) 
                        a
                      (heap s) 
                       "
  by (clarsimp simp: incon_load_incon_def snapshot_update_current'2_def snapshot_update_current2_def)

lemma [simp]:
  "a \<noteq> asid s \<and> a \<noteq> 0 \<Longrightarrow> 
    incon_load2
                      (snapshot_update_current'2 (snapshot_update_current'2 (ptable_snapshot s) (incon_set s) (heap s) (root s) (asid s))
                        iset'
                        (heap s) (Addr r) 0)
                      a (heap s) (Addr r) = 
   incon_load2
                     (ptable_snapshot s)
                      a (heap s) (Addr r)"
  by (clarsimp simp: incon_load2_def snapshot_update_current'2_def snapshot_update_current2_def) 

lemma asid_rewrite:
  "\<lbrakk>asids_consistent {} 
     (s\<lparr>root := Addr r, asid := a, incon_set := {},
                   ptable_snapshot := pt,
                   mode := User\<rparr>);  0 \<notin> ran (root_map s) ; 0 \<noteq> asid s\<rbrakk>  \<Longrightarrow> 
    asids_consistent {} 
      (s\<lparr>root := Addr r, asid := a, incon_set := {},
                   ptable_snapshot :=
                     snapshot_update_current'2
                      pt
                     is'
                      (heap s) (Addr r) 0,
                   mode := User\<rparr>)"
  apply (clarsimp simp: asids_consistent_def)
  apply (rule conjI)
   apply (clarsimp simp: snapshot_update_current'2_def snapshot_update_current2_def)
   apply (rule conjI)
    apply (clarsimp simp: ran_def)
   apply (clarsimp simp: ran_def)

  apply (subgoal_tac "aa \<noteq> 0")
   apply (subgoal_tac "snapshot_update_current'2 pt is' (heap s) (Addr r) 0 aa v =
                         pt aa v  ")
    apply (simp only:)
    apply (drule_tac x = ra in spec)
    apply (drule_tac x = aa in spec)
    apply clarsimp
    apply (clarsimp simp: snapshot_update_current'2_def snapshot_update_current2_def)
  by  (clarsimp simp: ran_def)

lemma asid_rewrite2:
  "\<lbrakk>asids_consistent {} 
     (s\<lparr> incon_set := {},
                   ptable_snapshot := pt,
                   mode := User\<rparr>);  0 \<notin> ran (root_map s) ; 0 \<noteq> asid s\<rbrakk>  \<Longrightarrow> 
    asids_consistent {} 
      (s\<lparr> incon_set := {},
                   ptable_snapshot :=
                     snapshot_update_current'2
                      pt
                     is'
                      (heap s) (root s) 0,
                   mode := User\<rparr>)"
  apply (clarsimp simp: asids_consistent_def)
  apply (rule conjI)
   apply (clarsimp simp: snapshot_update_current'2_def snapshot_update_current2_def)
   apply (rule conjI ; clarsimp simp: ran_def)



  apply clarsimp
  apply (clarsimp simp: snapshot_update_current'2_def snapshot_update_current2_def)
  apply (rule conjI)
   apply (clarsimp simp: ran_def)
   apply (rule conjI)
    apply (clarsimp simp: ran_def)
   apply (clarsimp simp: ran_def)
   apply (drule_tac x = r in spec)
   apply (drule_tac x = a in spec)
   apply clarsimp
   apply (drule_tac x = v in spec, simp)
  apply clarsimp
  apply (rule conjI)
   apply clarsimp
   apply (rule conjI)
    apply (clarsimp simp: ran_def)
   apply clarsimp
   apply (drule_tac x = r in spec)
   apply (drule_tac x = a in spec)
   apply clarsimp
   apply (drule_tac x = v in spec, simp)
  apply clarsimp
  apply (drule_tac x = r in spec)
  apply (drule_tac x = a in spec)
  apply clarsimp
  by (drule_tac x = v in spec, simp)


lemma new_context_switch:
  "\<Turnstile> \<lbrace> \<lambda>s. mmu_layout s \<and> asids_consistent {} s \<and> mode s = Kernel \<and>  \<I>\<C> s = {} \<and>
            0 \<notin> ran (root_map s)  \<and> root_map s (Addr r) = Some a \<and> Addr r \<in> root_log s\<rbrace>
            UpdateASID 0 ;; UpdateTTBR0 (Const r) ;; UpdateASID a ;; SetMode User
      \<lbrace>\<lambda>s. mmu_layout s \<and> \<I>\<C> s = {} \<and> mode s = User \<and> asids_consistent {} s \<rbrace>"
  apply vcgm
  apply (subgoal_tac "a \<noteq> 0")
   prefer 2
   apply (clarsimp simp: ran_def)
  apply (rule conjI)
   apply (clarsimp simp: mmu_layout_def)  
  apply (rule conjI)
   apply (clarsimp simp: \<I>\<C>_def)
   apply (rule conjI)
    apply (clarsimp simp: incon_load_incon_def snapshot_update_current'2_def snapshot_update_current2_def)
    apply (rule conjI)
     apply clarsimp
     apply (clarsimp simp: asids_consistent_def)
    apply (clarsimp simp: asids_consistent_def)
   apply (clarsimp simp: incon_load2_def snapshot_update_current'2_def snapshot_update_current2_def split: if_split_asm)
   apply (rule conjI)
    apply clarsimp
    apply (rule conjI)
     apply (clarsimp simp:)
     apply (subgoal_tac "Addr r = root s")
      apply clarsimp
     apply (clarsimp simp: mmu_layout_def)
     apply (clarsimp simp: ran_def partial_inj_def)
     apply force
    apply (clarsimp simp:)
    apply (clarsimp simp: asids_consistent_def)
    apply (drule_tac x = "Addr r" in spec)
    apply (drule_tac x = a in spec)
    apply clarsimp
    apply (drule_tac x = "Addr x" in spec)
    apply (erule conjE)
    apply (erule disjE)
     apply clarsimp
    apply clarsimp
   apply (clarsimp simp:) 
   apply (clarsimp simp: asids_consistent_def)
   apply (drule_tac x = "Addr r" in spec)
   apply (drule_tac x = a in spec)
   apply clarsimp
   apply (drule_tac x = "Addr x" in spec)
   apply (erule conjE)
   apply (erule disjE)
    apply clarsimp
   apply clarsimp
  apply (subgoal_tac "asid s \<noteq> 0 ")
   prefer 2
   apply (clarsimp simp: mmu_layout_def ran_def)
  apply clarsimp
  apply (case_tac "a \<noteq> asid s")
   apply clarsimp
   apply (subgoal_tac "incon_load_incon (ptable_snapshot s) a (heap s)  = {}")
    prefer 2
    apply (clarsimp simp: incon_load_incon_def asids_consistent_def)
   apply clarsimp
   apply (subgoal_tac "incon_load2 (ptable_snapshot s) a (heap s) (Addr r) = {}")
    prefer 2
    apply (clarsimp simp: incon_load2_def asids_consistent_def)
    apply (drule_tac x = "Addr r" in spec)
    apply (drule_tac x = a in spec , simp)
    apply (drule_tac x = x in spec)
    apply force
   apply clarsimp
   apply (rule asid_rewrite)
     prefer 2
     apply clarsimp
    prefer 2
    apply simp
   apply (clarsimp simp: asids_consistent_def)
   apply (rule conjI)
    apply (clarsimp simp: snapshot_update_current'2_def snapshot_update_current2_def)
    apply (rule conjI)
     apply (clarsimp simp : \<I>\<C>_def)  
     apply (drule_tac x = "addr_val v" in spec, simp)
    apply clarsimp
    apply (clarsimp simp : \<I>\<C>_def) 
    apply (drule_tac x = "addr_val v" in spec, simp)
   apply (case_tac "aa \<noteq> asid s")
    apply (subgoal_tac "snapshot_update_current'2 (ptable_snapshot s) (incon_set s) (heap s) (root s) (asid s) aa v =
           (ptable_snapshot s)  aa v")
     apply (simp only:)
     apply (drule_tac x = ra in spec)
     apply (drule_tac x = aa in spec)
     apply clarsimp
    apply (clarsimp simp: snapshot_update_current'2_def snapshot_update_current2_def)
   apply (clarsimp simp: snapshot_update_current'2_def snapshot_update_current2_def)
   apply (rule)+
     apply (clarsimp simp : \<I>\<C>_def) 
     apply (drule_tac x = "addr_val v" in spec, simp)
    apply clarsimp
    apply (subgoal_tac "ra =  root s", simp)
    apply (clarsimp simp: mmu_layout_def)
    apply (clarsimp simp: ran_def partial_inj_def)
    apply fastforce
   apply clarsimp
   apply (clarsimp simp : \<I>\<C>_def) 
   apply (drule_tac x = "addr_val v" in spec, simp)
  apply clarsimp
  apply (subgoal_tac "incon_load_incon (snapshot_update_current'2 (ptable_snapshot s) (incon_set s) (heap s) (root s) (asid s))
                      (asid s) (heap s) = {}")
   prefer 2
   apply (clarsimp simp: incon_load_incon_def snapshot_update_current'2_def snapshot_update_current2_def)
   apply (rule)+
    apply (clarsimp simp : \<I>\<C>_def) 
    apply (drule_tac x = "addr_val x" in spec, simp)
   apply (rule)+
   apply (clarsimp simp : \<I>\<C>_def) 
   apply (drule_tac x = "addr_val x" in spec, simp)
  apply simp
  apply (subgoal_tac "incon_load2
                      (snapshot_update_current'2
                        (snapshot_update_current'2 (ptable_snapshot s) (incon_set s) (heap s) (root s) (asid s))
                        (incon_load_incon (ptable_snapshot s) 0 (heap s) \<union> incon_load2 (ptable_snapshot s) 0 (heap s) (root s) \<union>
                         ptable_comp 0 (heap s) (heap s) (root s) (Addr r))
                        (heap s) (Addr r) 0)
                      (asid s) (heap s) (Addr r) = 
   incon_load2         (snapshot_update_current'2 (ptable_snapshot s) (incon_set s) (heap s) (root s) (asid s))
                      (asid s) (heap s) (Addr r)")

   prefer 2
   apply (clarsimp simp: incon_load2_def snapshot_update_current'2_def snapshot_update_current2_def)
  apply simp
  apply (subgoal_tac "Addr r = root s")
   prefer 2
   apply (clarsimp simp: mmu_layout_def)
   apply (clarsimp simp: ran_def partial_inj_def)
   apply fastforce
  apply simp
  apply (thin_tac "incon_load2
           (snapshot_update_current'2 (snapshot_update_current'2 (ptable_snapshot s) (incon_set s) (heap s) (root s) (asid s))
             (incon_load_incon (ptable_snapshot s) 0 (heap s) \<union> incon_load2 (ptable_snapshot s) 0 (heap s) (root s) \<union> ptable_comp 0 (heap s) (heap s) (root s) (root s)) (heap s) (root s) 0)
           (asid s) (heap s) (root s) =
          incon_load2 (snapshot_update_current'2 (ptable_snapshot s) (incon_set s) (heap s) (root s) (asid s)) (asid s) (heap s) (root s)")
  apply (thin_tac "incon_load_incon (snapshot_update_current'2 (ptable_snapshot s) (incon_set s) (heap s) (root s) (asid s)) (asid s)
           (heap s) =
          {}")
  apply (subgoal_tac "incon_load2 (snapshot_update_current'2 (ptable_snapshot s) (incon_set s) (heap s) (root s) (asid s)) (asid s) (heap s) (root s) =
                        {}")
   prefer 2
   apply (clarsimp simp: asids_consistent_def incon_load2_def snapshot_update_current'2_def 
      snapshot_update_current2_def)
  apply simp
  apply (rule asid_rewrite2)
    prefer 2
    apply simp
   prefer 2 apply simp
  apply (clarsimp simp: asids_consistent_def)
  apply (rule conjI)
   apply (clarsimp simp: snapshot_update_current'2_def snapshot_update_current2_def)
  apply (case_tac "aa \<noteq> asid s")
   apply (subgoal_tac "snapshot_update_current'2 (ptable_snapshot s) (incon_set s) (heap s) (root s) (asid s) aa v =
           (ptable_snapshot s)  aa v")
    apply (simp only:)
   apply (drule_tac x = ra in spec)
   apply (drule_tac x = aa in spec)
   apply clarsimp
   apply (clarsimp simp: snapshot_update_current'2_def snapshot_update_current2_def)
  by (clarsimp simp: snapshot_update_current'2_def snapshot_update_current2_def)


end



