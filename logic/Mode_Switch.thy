theory Mode_Switch

imports Memory_Model


begin


declare assign_sound [vcg del]

(*
there is a need of a memory model now, a typed memory, that
explicitly differentiate between page tables and rest of the memory
*)

(*
first theorem, kernel wrote to the memory but it didn't change the page tables at all, then there should not be TLB flush,
here we should only tag the heap with page_tables, lets gp ans see the program state

*)

definition
  kernel_state :: "p_state \<Rightarrow> bool"
where
  "kernel_state s \<equiv>     \<exists>rt a. root s = rt  \<and> mode s = Kernel \<and>
                        asid s = a  \<and> root_map s rt = Some a \<and> partial_inj (root_map s) \<and> rt\<in>root_log s \<and>
                        global_mappings_of_all_processes s \<and> non_overlapping_page_tables s  \<and>
                        \<Union>(ptable_trace' (heap s) (root s) ` UNIV) \<subseteq> kernel_phy_mem"


lemma kernel_state_implies_current_page_table:
  "kernel_state s \<Longrightarrow>  current_page_table s"
  apply (clarsimp simp: kernel_state_def non_overlapping_page_tables_def current_page_table_def)
done


lemma kernel_state_implies_page_tables:
  "kernel_state s \<Longrightarrow> page_tables s"
  apply (clarsimp simp: kernel_state_def non_overlapping_page_tables_def page_tables_def)
done


(* when kernel doesn't write to any of the page-table *)

lemma [simp]:
  "\<lbrakk>kernel_state s; assigned_asids_consistent (root_map s) (incon_set s)\<rbrakk> \<Longrightarrow>
                    con_set VA s"
  apply (clarsimp simp: assigned_asids_consistent_def con_set_def kernel_state_def assigned_asid_va_map_def ran_def)
  by force


lemma [simp]:
  "\<lbrakk>kernel_state s;  va \<in> kernel_safe_region' s\<rbrakk> \<Longrightarrow> ptable_lift_m (heap s) (root s) (mode s) (Addr va) = Some (Addr va r- global_offset) "
  by (clarsimp simp: kernel_state_def global_mappings_of_all_processes_def kernel_safe_region'_def vas_mapped_by_global_mappings_def)


lemma global_mappings_decode':
  "\<lbrakk>kernel_state s  ; va \<in> kernel_safe_region' s\<rbrakk> \<Longrightarrow>
         \<exists>p perm. decode_heap_pde' (heap s) (root s r+ (vaddr_pd_index va << 2)) =  Some (SectionPDE p perm)"
  apply (clarsimp simp: kernel_safe_region'_def vas_mapped_by_global_mappings_def global_mappings_of_all_processes_def global_mappings_def
                        pd_idx_offset_def get_pde'_def kernel_state_def)
  by force


lemma  kernel_safe_region_ptable_trace' [simp]:
  "\<lbrakk>kernel_state s; vp' \<in> kernel_safe_region' s; vp \<in> kernel_safe_region' s\<rbrakk> \<Longrightarrow> Addr (vp' - global_offset) \<notin> ptable_trace' (heap s) (root s) (Addr vp)"
  apply (frule_tac va = vp in global_mappings_decode')
   apply (clarsimp simp: kernel_state_def) apply clarsimp
  by (clarsimp simp: kernel_state_def ptable_trace'_def kernel_safe_region'_def vas_mapped_by_global_mappings_def vas_of_current_state_mapped_to_global_mappings_of_all_processes_def pd_idx_offset_def)+




(* can not put in the simp set *)
lemma kernel_state_mode:
  "kernel_state s \<Longrightarrow> mode s = Kernel"
  by (clarsimp simp: kernel_state_def)


lemma  mode_switch_safe_set_when_not_in_current_page_table:
  "\<Turnstile> \<lbrace> \<lambda>s. kernel_state s \<and> aval lval s = Some vp \<and> aval rval s = Some v \<and> vp \<in> SM \<and> SM = kernel_safe_region' s \<and>
           assigned_asids_consistent (root_map s) (incon_set s)  \<and>
            (Addr vp r- global_offset) \<notin> \<Union>(ptable_trace' (heap s) (root s) ` UNIV) \<rbrace>
                     lval ::= rval ;; SetMode User
                  \<lbrace>\<lambda>s. safe_set (SM_user (heap s) (root s)) s \<and>  heap s (Addr vp r- global_offset) = Some v\<rbrace>"
  apply (vcgm vcg: weak_pre_write [of SM])
  apply (rule conjI)
   apply (clarsimp simp: safe_set_def safe_memory_def ptrace_set_def)
  apply (rule conjI)
   apply (clarsimp simp: kernel_state_def)
  apply (clarsimp simp: safe_set_def)
  apply (rule conjI)
   apply (clarsimp simp: safe_memory_def SM_user_def  ptrace_set_def)
  by (clarsimp simp: pde_comp_empty)



lemma  mode_switch_invariant_for_current_asid:
  "\<Turnstile> \<lbrace> \<lambda>s. kernel_state s \<and> aval lval s = Some vp \<and> aval rval s = Some v \<and> vp \<in> SM \<and> SM = kernel_safe_region' s \<and>
           assigned_asids_consistent (root_map s) (incon_set s)  \<and>
            (Addr vp r- global_offset) \<notin> \<Union>(ptable_trace' (heap s) (root s) ` UNIV) \<rbrace>
                     lval ::= rval ;; SetMode User
                  \<lbrace>\<lambda>s. {asid s} \<times> UNIV  \<inter> incon_set s = {}\<rbrace>"
  apply (vcgm vcg: assign_sound)
  apply (rule conjI)
   apply (clarsimp simp: assigned_asids_consistent_def assigned_asid_va_map_def ran_def kernel_state_def)
   apply force
  apply (rule conjI)
   apply (clarsimp simp: kernel_state_def)
  apply (clarsimp simp: pde_comp_empty)
  apply (clarsimp simp: assigned_asids_consistent_def assigned_asid_va_map_def ran_def kernel_state_def)
  by auto


(* might not a be a good use case *)

(* similar to kernel_state, except that it talks about all of the base tables *)

lemma mode_switch_safe_set_when_not_in_page_table:
  "\<Turnstile> \<lbrace> \<lambda>s. kernel_state s \<and> aval lval s = Some vp \<and> aval rval s = Some v \<and> vp \<in> SM \<and> SM = kernel_safe_region' s \<and>
             assigned_asids_consistent (root_map s) (incon_set s)  \<and> (tagged_heap s) (Addr vp r- global_offset) \<noteq> page_table \<rbrace>
                     lval ::= rval ;; SetMode User
                  \<lbrace>\<lambda>s. safe_set (SM_user (heap s) (root s)) s \<and>  heap s (Addr vp r- global_offset) = Some v\<rbrace>"
  apply (vcgm vcg: weak_pre_write [of SM])
  apply (frule kernel_state_implies_page_tables)
  apply (rule conjI)
   apply (clarsimp simp: safe_set_def safe_memory_def ptrace_set_def)
  apply (rule conjI)
   apply (clarsimp simp: kernel_state_def)
  apply (clarsimp simp: safe_set_def)
  apply (rule conjI)
   apply (clarsimp simp: safe_memory_def SM_user_def  ptrace_set_def)
  apply (subgoal_tac "(Addr vp r- global_offset) \<notin> \<Union>(ptable_trace' (heap s) (root s) ` UNIV)")
   apply (clarsimp simp: pde_comp_empty)
  apply (clarsimp simp: kernel_state_def page_tables_def)
done


lemma mode_switch_invariant_for_all_assigned_asid:
  "\<Turnstile> \<lbrace> \<lambda>s. kernel_state s \<and> aval lval s = Some vp \<and> aval rval s = Some v \<and> vp \<in> SM \<and> SM = kernel_safe_region' s \<and>
             assigned_asids_consistent (root_map s) (incon_set s)  \<and> (tagged_heap s) (Addr vp r- global_offset) \<noteq> page_table \<rbrace>
                     lval ::= rval ;; SetMode User
                  \<lbrace>\<lambda>s. assigned_asids_consistent (root_map s) (incon_set s) \<rbrace>"
  apply (vcgm vcg:  assign_sound)
  apply (rule conjI)
   apply (clarsimp simp: assigned_asids_consistent_def assigned_asid_va_map_def ran_def kernel_state_def)
   apply force
  apply (rule conjI)
   apply (clarsimp simp: kernel_state_def)
  apply (frule kernel_state_implies_page_tables)
  apply (subgoal_tac "(Addr vp r- global_offset) \<notin> \<Union>(ptable_trace' (heap s) (root s) ` UNIV)")
   apply (clarsimp simp: pde_comp_empty)
  apply (clarsimp simp: kernel_state_def page_tables_def)
done


(* address writing is in the user mappings of the page table *)
(* ptable_mapped should not have globally mapped addresses   *)
(* different processes are not sharing the addresses space   *)

lemma mode_switch_safe_set_in_current_page_table:
  "\<Turnstile> \<lbrace> \<lambda>s. kernel_state s \<and> aval lval s = Some vp \<and> aval rval s = Some v \<and> vp \<in> SM \<and> SM = kernel_safe_region' s \<and>
      assigned_asids_consistent (root_map s) (incon_set s)  \<and>
            Addr vp \<in> ptable_mapped (heap s) (root s) \<and> asid s = a \<rbrace>
                     lval ::= rval ;; Flush (flushASID a) ;; SetMode User
                  \<lbrace>\<lambda>s. safe_set (SM_user (heap s) (root s)) s  \<and> heap s (Addr vp r- global_offset) = Some v\<rbrace>"
  apply (vcgm vcg: weak_pre_write [of SM])
  apply (rule conjI)
   apply (clarsimp simp: safe_set_def safe_memory_def ptrace_set_def)
  apply (rule conjI)
   apply (clarsimp simp: kernel_state_def)
  apply (clarsimp simp: safe_set_def)
  apply (rule conjI)
   apply (clarsimp simp: safe_memory_def SM_user_def ptrace_set_def)
  by (clarsimp simp: con_set_def)


lemma  mode_switch_invariant_flush_current_asid:
  "\<Turnstile> \<lbrace> \<lambda>s. kernel_state s \<and> aval lval s = Some vp \<and> aval rval s = Some v \<and> vp \<in> SM \<and> SM = kernel_safe_region' s \<and>
         assigned_asids_consistent (root_map s) (incon_set s)  \<and>
            Addr vp \<in> ptable_mapped (heap s) (root s) \<and> asid s = a \<rbrace>
                     lval ::= rval ;; Flush (flushASID a) ;; SetMode User
                  \<lbrace>\<lambda>s. {asid s} \<times> UNIV  \<inter> incon_set s = {}\<rbrace>"
  apply (vcgm vcg:  assign_sound)
  apply (rule conjI)
   apply (clarsimp simp: assigned_asids_consistent_def assigned_asid_va_map_def ran_def kernel_state_def)
   apply force
  apply (rule conjI)
   apply (clarsimp simp: kernel_state_def)
  by force



lemma pde_comp_asid_incon:
  "{av. (av \<in> incon_set s \<or> av \<in> pde_comp' (asid s) (heap s) (heap s(Addr (vp - global_offset) \<mapsto> v)) (root s)) \<and> fst av \<noteq> asid s} =
   {av. av \<in> incon_set s  \<and> fst av \<noteq> asid s}"
  apply (clarsimp simp: pde_comp'_def)
  apply force
done

thm kernel_state_def

(* this is important *)
lemma  mode_switch_invariant_flush_all_assigned_asid:
  "\<Turnstile> \<lbrace> \<lambda>s. kernel_state s \<and> aval lval s = Some vp \<and> aval rval s = Some v \<and> vp \<in> SM \<and> SM = kernel_safe_region' s \<and>
         assigned_asids_consistent (root_map s) (incon_set s)  \<and>  Addr vp \<in> ptable_mapped (heap s) (root s) \<and> asid s = a \<rbrace>
                     lval ::= rval ;; Flush (flushASID a) ;; SetMode User
                  \<lbrace>\<lambda>s. assigned_asids_consistent (root_map s) (incon_set s) \<rbrace>"
  apply (vcgm vcg:  assign_sound)
  apply (rule conjI)
   apply (clarsimp simp: assigned_asids_consistent_def assigned_asid_va_map_def ran_def kernel_state_def)
   apply force
  apply (rule conjI)
   apply (clarsimp simp: kernel_state_def)
  apply (clarsimp simp: assigned_asids_consistent_def pde_comp_asid_incon)
  apply force
done


(*  it can change multiple addresses, because of multiple level page table*)

thm lookup_pde'_def

(* when kernel is writing to the section *)


(* here *)
lemma  ptable_lift_user_implies_ptable_lift:
  "ptable_lift_m h r User va = Some pa \<Longrightarrow> ptable_lift' h r va = Some pa"
  by (clarsimp simp: ptable_lift_m_def lookup_pde_perm_def filter_pde_def ptable_lift'_def split:option.splits split_if_asm)

(* important use case *)
lemma pde_comp_simp_vset_flush:
  "{av. (av \<in> incon_set s \<or> av \<in> (\<lambda>x. (asid s, addr_val x)) ` vspace_section_entry (heap s) (root s) (SectionPDE p p_bits)) \<and> snd av \<notin> addr_val ` vspace_section_entry (heap s) (root s) (SectionPDE p p_bits)} =
   {av. av \<in> incon_set s  \<and> snd av \<notin> addr_val ` vspace_section_entry (heap s) (root s) (SectionPDE p p_bits)}"
  apply (force)
done

lemma incon_set_flsuhVA_section_simp:
  "{asid s} \<times> UNIV \<inter> incon_set s = {} \<Longrightarrow>
       {asid s} \<times> UNIV \<inter> {av \<in> incon_set s. snd av \<notin> addr_val ` vspace_section_entry (heap s) (root s) (SectionPDE p p_bits)} = {}"
  apply force
done


lemma  remaining:
  "\<Turnstile> \<lbrace> \<lambda>s. kernel_state s \<and> aval lval s = Some vp \<and> aval rval s = Some v \<and> vp \<in> SM \<and> SM = kernel_safe_region' s \<and>
      assigned_asids_consistent (root_map s) (incon_set s)  \<and>  Addr vp \<in> ptable_mapped (heap s) (root s) \<and>
               (\<exists>p p_bits. get_pde' (heap s) (root s) (Addr vp) = Some (SectionPDE p p_bits) \<and> V = vspace_section_entry (heap s) (root s) (SectionPDE p p_bits) ) \<rbrace>
                               lval ::= rval ;; Flush (flushvarange V) ;; SetMode User
                  \<lbrace>\<lambda>s. {asid s} \<times> UNIV \<inter> incon_set s = {}\<rbrace>"
  apply (vcgm vcg:  assign_sound)
  apply (rule conjI)
   apply (clarsimp simp: assigned_asids_consistent_def assigned_asid_va_map_def ran_def  kernel_state_def)
   apply force
  apply (rule conjI)
   apply (clarsimp simp: kernel_state_def)
  apply (subgoal_tac "pde_comp' (asid s) (heap s) (heap s(Addr (vp - global_offset) \<mapsto> v)) (root s) =
                (\<lambda>x. (asid s, addr_val x)) ` vspace_section_entry (heap s) (root s) (SectionPDE p p_bits) \<or>
               pde_comp' (asid s) (heap s) (heap s(Addr (vp - global_offset) \<mapsto> v)) (root s) = {}")
   apply (erule disjE)
    apply (clarsimp simp: pde_comp_simp_vset_flush)
    apply (rule incon_set_flsuhVA_section_simp , clarsimp simp: kernel_state_def
                assigned_asids_consistent_def assigned_asid_va_map_def ran_def)
(*    apply force
   apply (clarsimp simp: kernel_state_def assigned_asids_consistent_def assigned_asid_va_map_def ran_def)
   apply fastforce
  apply (case_tac "(heap s(Addr (vp - global_offset) \<mapsto> v)) (Addr (vp - global_offset)) = heap s (Addr (vp - global_offset))")
   apply (rule disjI2)
   apply (subgoal_tac "heap s = (heap s(Addr (vp - global_offset) \<mapsto> v))")
    prefer 2
    apply (clarsimp)
   apply (clarsimp simp: pde_comp_def)
  apply (rule disjI1)
  (* gave cases about the different pde entries  *)
  apply clarsimp
  apply (clarsimp simp: pde_comp_def)
  apply (subgoal_tac "{va. \<exists>p1. ptable_lift' (heap s) (root s) va = Some p1 \<and> (\<exists>p2. ptable_lift' (heap s(Addr (vp - global_offset) \<mapsto> v)) (root s) va = Some p2 \<and> p1 \<noteq> p2)} =
                         vspace_section_entry (heap s) (root s) (SectionPDE p p_bits) ")
  apply (clarsimp simp: vspace_section_entry_def)
   apply safe
  (*  here *)
  (* discuss with Gerwin, reasoning can be done but a little bit tricky, this theorem worth to spend time on?  *)
  *)
oops


(* invariant preserved *)

lemma
  "\<Turnstile> \<lbrace> \<lambda>s. kernel_state s \<and> aval lval s = Some vp \<and> aval rval s = Some v \<and> vp \<in> SM \<and> SM = kernel_safe_region' s \<and>
      assigned_asids_consistent (root_map s) (incon_set s)  \<and>  Addr vp \<in> ptable_mapped (heap s) (root s) \<and>
               (\<exists>p p_bits. get_pde' (heap s) (root s) (Addr vp) = Some (SectionPDE p p_bits) \<and> V = vspace_section_entry (heap s) (root s) (SectionPDE p p_bits) ) \<rbrace>
                               lval ::= rval ;; Flush (flushvarange V) ;; SetMode User
                  \<lbrace>\<lambda>s. safe_set (SM_user (heap s) (root s)) s \<and>  heap s (Addr vp r- global_offset) = Some v\<rbrace>"
  apply (vcgm vcg: weak_pre_write [of SM])
  apply (rule conjI)
   apply (clarsimp simp: safe_set_def safe_memory_def ptrace_set_def)
  apply (rule conjI)
   apply (clarsimp simp: kernel_state_def)
  apply (clarsimp simp: safe_set_def)
  apply (rule conjI)
   apply (clarsimp simp: safe_memory_def SM_user_def ptrace_set_def)
  apply (clarsimp simp: con_set_def)
  apply (rule conjI)
   apply (clarsimp simp: kernel_state_def assigned_asids_consistent_def assigned_asid_va_map_def ran_def)
   apply fastforce
 (* remaining, can be done but it requires reasoning *)

oops


(* form here *)

(* if the physical address of vp is any of the page table, then the asid assigned to the respective root should be flushed  *)

lemma screwed:
  " \<lbrakk> a \<in> ptable_trace' h r1 xa; (\<Union>x. ptable_trace' h r1 x) \<inter> (\<Union>x. ptable_trace' h r2 x) = {}\<rbrakk>  \<Longrightarrow>
           a \<notin> ptable_trace' h r2 x"
  by force


lemma assigned_rt_map_update:
  "assigned_asids_consistent (root_map s) (incon_set s) \<and>  {a} \<times> UNIV \<inter>incon_set s = {}  \<Longrightarrow>
              assigned_asids_consistent (root_map s(Addr r \<mapsto> a)) (incon_set s)"
  apply (clarsimp simp: assigned_asids_consistent_def  assigned_asid_va_map_def ran_def )
  by force

thm pde_comp_asid_incon


lemma non_overlapping_page_tables_ptrace:
  "\<lbrakk>non_overlapping_page_tables_assertion rtlog hp ; rt \<in> rtlog; rt' \<in> rtlog ; rt \<noteq> rt' ; p \<in> \<Union>(ptable_trace' hp rt ` UNIV)  \<rbrakk>  \<Longrightarrow>
                  p \<notin> \<Union>(ptable_trace' hp rt' ` UNIV)"
  apply (clarsimp simp: non_overlapping_page_tables_def non_overlapping_page_tables_assertion_def)
  by fastforce


lemma kernel_writing_to_inactive_process_page_table_and_flush:
  "\<Turnstile> \<lbrace> \<lambda>s. kernel_state s \<and> aval lval s = Some vp \<and> aval rval s = Some v \<and> vp \<in> SM \<and> SM = kernel_safe_region' s \<and>
         assigned_asids_consistent (root_map s) (incon_set s)  \<and> rt \<in> root_log s \<and> rt \<noteq> root s \<and>
                  Addr vp r- global_offset \<in> \<Union>(ptable_trace' (heap s) rt ` UNIV) \<and> root_map s rt = Some a \<rbrace>
                     lval ::= rval ;; Flush (flushASID a) ;; SetMode User
                  \<lbrace>\<lambda>s. assigned_asids_consistent (root_map s) (incon_set s) \<rbrace>"
  apply (vcgm vcg:  assign_sound)
  apply (rule conjI)
   apply (clarsimp simp: assigned_asids_consistent_def  assigned_asid_va_map_def ran_def kernel_state_def)
   apply auto [1]
  apply (rule conjI)
   apply (clarsimp simp: kernel_state_def)
  find_theorems "pde_comp'"
  apply (subgoal_tac "pde_comp' (asid s) (heap s) (heap s(Addr (vp - global_offset) \<mapsto> v)) (root s) = {}")
   apply clarsimp
   apply (clarsimp simp: assigned_asids_consistent_def)
   apply force
  apply (rule ptable_trace_pde_comp)
  apply (clarsimp simp: kernel_state_def)
  apply (frule_tac rt = rt and rt' = "root s" and hp = "heap s" and p = "Addr vp r- global_offset" in non_overlapping_page_tables_ptrace ; clarsimp)
  by force


(* changing of vspace? , updating of asid, or making a new asid   *)

(* update root register to an assigned root, that also has an assigned asid  *)


lemma  context_swtich_to_assigned_root_valid_asid:
  "\<Turnstile> \<lbrace> \<lambda>s. kernel_state s \<and> aval rt s = Some r \<and> Addr r \<in> root_log s \<and> root_map s (Addr r) = Some a \<and>
            assigned_asids_consistent (root_map s) (incon_set s) \<rbrace>
                      UpdateTTBR0 rt ;; UpdateASID a
                  \<lbrace>\<lambda>s. assigned_asids_consistent (root_map s) (incon_set s) \<rbrace>"
  apply vcgm
  by (clarsimp simp: kernel_state_def)


(* context switching and prepare for the meeting *)

definition
  "asid_assumption s  \<equiv>  \<forall>a.  {a} \<times> UNIV \<inter> incon_set s = {} "

lemma [simp]:
  "\<forall>rts. root_map s rts  \<noteq> Some a \<Longrightarrow>  a \<notin> ran (root_map s)"
  by (simp add: ran_def)


lemma parital_inj_update:
  "\<lbrakk>mode s = Kernel; aval rt s = Some v; root_map s (Addr v) = None; \<forall>rt. root_map s rt \<noteq> Some a; partial_inj (root_map s)\<rbrakk> \<Longrightarrow> partial_inj (root_map s(Addr v \<mapsto> a))"
  unfolding partial_inj_def
  by (metis fun_upd_apply)



lemma context_switch:
  "\<Turnstile> \<lbrace> \<lambda>s. kernel_state s \<and> aval rt s = Some r \<and> Addr r \<in> root_log s \<and> root_map s (Addr r) = None \<and> (\<forall>rts. root_map s rts \<noteq> Some a) \<and>
            asid_assumption s \<rbrace>
                       UpdateRTMap rt a ;; UpdateTTBR0 rt ;; UpdateASID a
                  \<lbrace>\<lambda>s. assigned_asids_consistent (root_map s) (incon_set s) \<and> partial_inj (root_map s)\<rbrace>"
  apply (vcgm vcg: rt_map_update_partial)
  (* how to use rt_map_update_partial with vcg *)
  apply (rule conjI)
   apply (clarsimp simp: kernel_state_def)
  apply (rule conjI)
   apply (rule assigned_rt_map_update)
   apply (clarsimp simp: asid_assumption_def  assigned_asids_consistent_def assigned_asid_va_map_def ran_def)
   apply force
  apply (rule_tac rt = rt in  parital_inj_update ; clarsimp simp: kernel_state_def)
done



(* map, remap and unmap  *)

(*  transition in map    : invalid to valid (no flush/invalidate)
                  remap  : valid to valid   (flush by asid/VA range)
                  unmap  : valid yo invalid (flush by asid/VA range)
  *)


thm pde_comp'_def

(*definition
  pde_comp_n :: "asid \<Rightarrow> heap \<Rightarrow> heap \<Rightarrow> paddr \<Rightarrow> (asid \<times> 32 word) set"
where
  "pde_comp_n a hp1 hp2 rt \<equiv>
         (\<lambda>x. (a, addr_val x)) ` {va. (\<exists>p1 p2. ptable_lift' hp1 rt va = Some p1 \<and> ptable_lift' hp2 rt va = Some p2 \<and> p1 \<noteq> p2 )
   (* it won't flush  if it re-maps the page to itself, this might not be consistent with seL4, there is some PR though *)
                                   \<or>  (\<exists>p. ptable_lift' hp1 rt va = Some p \<and> ptable_lift' hp2 rt va = None )}"
*)
(* pde_comp will work in the case of map and remap, but not in the case of unmap, because pde_comp will still be empty *)

(*  Mapping *)

thm get_pde'_def

lemma ptrace_invalid_ptable_lift_none:
  "\<lbrakk>p \<in> ptable_trace' h r v; h p = Some w; decode_pde w = InvalidPDE \<or> decode_pte_small w = InvalidPTE\<rbrakk>   \<Longrightarrow>
        ptable_lift'  h r v = None"
  apply (clarsimp simp: ptable_trace'_def Let_def decode_heap_pde'_def split: option.splits)
  apply (case_tac "decode_pde x2" ; clarsimp)
     apply (clarsimp simp: ptable_lift'_def lookup_pde'_def get_pde'_def decode_heap_pde'_def)
    apply (clarsimp simp: ptable_lift'_def lookup_pde'_def get_pde'_def decode_heap_pde'_def)
   prefer 2
   apply (clarsimp simp: decode_pde_def decode_pte_small_def)
  apply (erule_tac P = "p = x3 r+ (vaddr_pt_index (addr_val v) << 2)" in disjE)
   apply (erule disjE)
    prefer 2
    apply (clarsimp simp: decode_pde_def decode_pte_small_def)
   apply (clarsimp simp: ptable_lift'_def lookup_pde'_def get_pde'_def decode_heap_pde'_def lookup_pte'_def get_pte'_def decode_heap_pte'_def decode_pte_def)
   apply (case_tac "decode_pte_small w")
    apply clarsimp
   apply (clarsimp simp: decode_pde_def Let_def decode_pte_small_def decode_pde_pt_def) apply (clarsimp split: split_if_asm)
        apply (clarsimp simp:  decode_pde_pt_def)
       apply (clarsimp simp: decode_pde_section_def)
      apply word_bitwise apply force
     apply (clarsimp simp: decode_pde_section_def)
    apply (clarsimp simp: decode_pde_section_def)
   apply word_bitwise apply force
  apply (clarsimp simp: decode_pde_def decode_pte_small_def Let_def)
done

(* have specific theorem for map, remap and unmap condition and pde_comp, will make life easier *)



thm pde_comp'_def
(* true only for remap *)
lemma
  "pde_comp' a h (h(p \<mapsto> v)) r = {a} \<times> addr_val `{va. p \<in> ptable_trace' h t va}"
  apply (clarsimp simp: pde_comp'_def ptable_trace'_def Let_def)
oops

lemma ptable_trace_get_pde:
  "\<lbrakk>p \<notin> ptable_trace' h r x;  get_pde' h r x = Some pde\<rbrakk>  \<Longrightarrow>
                   get_pde' (h(p \<mapsto> v)) r x = Some pde"
  apply (clarsimp simp: ptable_trace'_def Let_def get_pde'_def decode_heap_pde'_def )
  by (case_tac " decode_pde z" ; clarsimp)


lemma ptable_trace_get_pte:
  "\<lbrakk>p \<notin> ptable_trace' h r x;  get_pde' h r x = Some (PageTablePDE x3) ; get_pte' h x3 x = Some x2\<rbrakk> \<Longrightarrow>
             get_pte' (h(p \<mapsto> v)) x3 x = Some x2"
  apply (subgoal_tac "get_pde' (h(p \<mapsto> v)) r x = Some (PageTablePDE x3)")
   prefer 2
   apply (clarsimp simp: ptable_trace_get_pde)
  by (clarsimp simp: ptable_trace'_def Let_def get_pde'_def get_pte'_def decode_heap_pde'_def decode_heap_pte'_def)


lemma ptable_trace_lookup_pte:
  "\<lbrakk>p \<notin> ptable_trace' h r x;  get_pde' h r x = Some (PageTablePDE x3); lookup_pte' (h(p \<mapsto> v)) x3 x = None\<rbrakk> \<Longrightarrow>
                lookup_pte' h x3 x = None"
  apply (clarsimp simp: lookup_pte'_def  Let_def)
  apply (clarsimp split: option.splits)
   by (clarsimp simp: ptable_trace_get_pte)+


lemma
  " \<lbrakk>h p = Some w; decode_pde w = InvalidPDE\<rbrakk> \<Longrightarrow> is_fault (pt_walk a h r x)"
  apply (clarsimp simp: pt_walk_def is_fault_def get_pde'_def decode_heap_pde'_def Let_def  vaddr_pd_index_def mask_def
                  split:option.splits pde.splits pte.splits split_if_asm)
  apply safe



oops

lemma rewrite_or:
  "(\<not> P \<Longrightarrow> \<not>Q \<Longrightarrow> R) \<Longrightarrow> P \<or> Q \<or> R"
   by auto



lemma is_fault_pt_trace:
   "\<not> is_fault (pt_walk a h r x) \<Longrightarrow> ptable_trace' h r x \<noteq> {}"
   by (clarsimp simp: pt_walk_def is_fault_def ptable_trace'_def Let_def get_pde'_def split:option.splits pde.splits)

find_theorems "ptable_trace'"


lemma  pt_walk_preserved':
  "\<lbrakk>p \<notin> ptable_trace' h r x; \<not> is_fault (pt_walk a h r x) \<rbrakk> \<Longrightarrow>
       pt_walk a h r x = pt_walk a (h(p \<mapsto> v)) r x"
  apply (frule is_fault_pt_trace)
  apply (clarsimp simp: pt_walk_def is_fault_def  lookup_pde'_def get_pde'_def ptable_trace'_def Let_def split: option.splits)
  apply (case_tac x2; clarsimp simp: decode_heap_pde'_def lookup_pte'_def split: option.splits)
  apply (case_tac x2a ; clarsimp)
  apply (rule conjI)
   apply (rule_tac x = "(SmallPagePTE x21 x22)" in exI, clarsimp simp: get_pte'_def decode_heap_pte'_def , clarsimp)
  by (case_tac x2 ; clarsimp simp:get_pte'_def decode_heap_pte'_def)



lemma ptrace_invalid_pt_walk_is_fault:
  "\<lbrakk>p \<in> ptable_trace' h r v; h p = Some w; decode_pde w = InvalidPDE \<or> decode_pte_small w = InvalidPTE \<rbrakk>   \<Longrightarrow>
        is_fault (pt_walk a h r v)"
  apply (clarsimp simp: ptable_trace'_def Let_def decode_heap_pde'_def split: option.splits)
  apply (case_tac "decode_pde x2" ; clarsimp)
     apply (clarsimp simp: is_fault_def pt_walk_def  get_pde'_def decode_heap_pde'_def)
    apply (clarsimp simp: is_fault_def pt_walk_def  get_pde'_def decode_heap_pde'_def)
   prefer 2
   apply (clarsimp simp: decode_pde_def decode_pte_small_def)
  apply (erule_tac P = "p = x3 r+ (vaddr_pt_index (addr_val v) << 2)" in disjE)
   apply (erule disjE)
    prefer 2
    apply (clarsimp simp: decode_pde_def decode_pte_small_def)
   apply (clarsimp simp: is_fault_def pt_walk_def  get_pde'_def decode_heap_pde'_def lookup_pte'_def get_pte'_def decode_heap_pte'_def decode_pte_def)
   apply (case_tac "decode_pte_small w")
    apply clarsimp
   apply (clarsimp simp: decode_pde_def Let_def decode_pte_small_def decode_pde_pt_def) apply (clarsimp split: split_if_asm)
        apply (clarsimp simp:  decode_pde_pt_def)
       apply (clarsimp simp: decode_pde_section_def)
      apply word_bitwise apply force
     apply (clarsimp simp: decode_pde_section_def)
    apply (clarsimp simp: decode_pde_section_def)
   apply word_bitwise apply force
  by (clarsimp simp: decode_pde_def decode_pte_small_def Let_def)

lemma
  "\<lbrakk> \<not> is_fault (pt_walk a h r x); pt_walk a h r x = pt_walk a (h(p \<mapsto> v)) r x\<rbrakk>   \<Longrightarrow>
       \<not> is_fault (pt_walk a (h(p \<mapsto> v)) r x)"


oops

lemma   map_pde_comp_empty:
  "h p = Some w \<and> (decode_pde w = InvalidPDE \<or> decode_pte_small w = InvalidPTE) \<Longrightarrow>
         pde_comp' a h (h(p \<mapsto> v)) r = {}"
  apply (clarsimp simp: pde_comp'_def)
  apply (rule conjI)
   apply (case_tac "p \<notin> ptable_trace' h r x")
    apply (rule rewrite_or)
    apply (case_tac "ptable_trace' h r x = {}")
     apply (clarsimp simp: is_fault_pt_trace)
    apply (frule_tac p = p and v = v in  pt_walk_preserved' [rotated] ; clarsimp)
   apply (rule , simp)
   apply (erule disjE)
    apply (clarsimp simp: ptrace_invalid_pt_walk_is_fault)
   apply (clarsimp simp: ptrace_invalid_pt_walk_is_fault)
  apply (case_tac "p \<notin> ptable_trace' h r x")
   apply clarsimp
   apply (frule_tac a = a and v = v in pt_walk_preserved' ; clarsimp)
  apply (rule, simp)
  apply (clarsimp simp: ptrace_invalid_pt_walk_is_fault)
 done



lemma  kernel_map_invariant:
  "\<Turnstile> \<lbrace> \<lambda>s. kernel_state s \<and> aval lval s = Some vp \<and> aval rval s = Some v \<and> vp \<in> SM \<and> SM = kernel_safe_region' s \<and>
             assigned_asids_consistent (root_map s) (incon_set s)  \<and>
            (Addr vp r- global_offset) \<in> \<Union>(ptable_trace' (heap s) (root s) ` UNIV) \<and>
                 ((heap s) (Addr vp r- global_offset)) = Some w \<and>
                (decode_pde w = InvalidPDE \<or> decode_pte_small w = InvalidPTE) \<and>
               (\<exists>p pbits. decode_pde v = SectionPDE p pbits \<or> decode_pte_small v = SmallPagePTE p pbits) \<rbrace>
                          lval ::= rval
                  \<lbrace>\<lambda>s. {asid s} \<times> UNIV \<inter> incon_set s = {} \<rbrace>"
  apply (vcgm vcg:  assign_sound)
  apply (rule conjI)
   apply (clarsimp simp: assigned_asids_consistent_def assigned_asid_va_map_def ran_def kernel_state_def)
   apply fastforce
  apply (subgoal_tac "pde_comp' (asid s) (heap s) (heap s(Addr (vp - global_offset) \<mapsto> v)) (root s) = {}")
   apply clarsimp
   apply (clarsimp simp: asid_assumption_def assigned_asids_consistent_def assigned_asid_va_map_def ran_def kernel_state_def)
   apply fastforce
  apply (clarsimp simp: map_pde_comp_empty)
 done




lemma  kernel_map_invariant':
  "\<Turnstile> \<lbrace> \<lambda>s. kernel_state s \<and> aval lval s = Some vp \<and> aval rval s = Some v \<and> vp \<in> SM \<and> SM = kernel_safe_region' s \<and>
         assigned_asids_consistent (root_map s) (incon_set s)  \<and>
            (Addr vp r- global_offset) \<in> \<Union>(ptable_trace' (heap s) (root s) ` UNIV) \<and> ((heap s) (Addr vp r- global_offset)) = Some w \<and>
                (decode_pde w = InvalidPDE \<or> decode_pte_small w = InvalidPTE) \<and>
               (\<exists>p pbits. decode_pde v = SectionPDE p pbits \<or> decode_pte_small v = SmallPagePTE p pbits) \<rbrace>
                          lval ::= rval
                  \<lbrace>\<lambda>s. assigned_asids_consistent (root_map s) (incon_set s) \<rbrace>"
  apply (vcgm vcg:  assign_sound)
  apply (rule conjI)
   apply (clarsimp simp: assigned_asids_consistent_def assigned_asid_va_map_def ran_def kernel_state_def)
   apply fastforce
  apply (subgoal_tac "pde_comp' (asid s) (heap s) (heap s(Addr (vp - global_offset) \<mapsto> v)) (root s) = {}")
   prefer 2
   apply (clarsimp simp: map_pde_comp_empty)
  by clarsimp

(*  there should be multiple assignments, if we are updating the  different levels of page tables *)




(* do this along with the ptable and pttrace etc  *)

(* might have to see the multilevel page table assigning, or rampping*)


(*  does kernel remaps the pages of the inactive processes (or inactive asids) *)

lemma
  "\<Turnstile> \<lbrace> \<lambda>s. kernel_state s \<and> aval lval s = Some vp \<and> aval rval s = Some v \<and> vp \<in> SM \<and> SM = kernel_safe_region' s \<and>
         assigned_asids_consistent (root_map s) (incon_set s)  \<and>  rt \<in> root_log s \<and> rt \<noteq> root s \<and>
            (Addr vp r- global_offset) \<in> \<Union>(ptable_trace' (heap s) rt ` UNIV) \<and> ((heap s) (Addr vp r- global_offset)) = Some w \<and> (decode_pde w = InvalidPDE \<or> decode_pte_small w = InvalidPTE) \<and>
               (\<exists>p pbits. decode_pde v = SectionPDE p pbits \<or> decode_pte_small v = SmallPagePTE p pbits) \<rbrace>
                             lval ::= rval
                  \<lbrace>\<lambda>s. some_invariant \<rbrace>"

oops



(*  remap, in case of section  *)

find_theorems "Flush (flushASID _)"


lemma  remap_section_entry_current_page_table:
  "\<Turnstile> \<lbrace> \<lambda>s. kernel_state s \<and> aval lval s = Some vp \<and> aval rval s = Some v \<and> vp \<in> SM \<and> SM = kernel_safe_region' s \<and>
             assigned_asids_consistent (root_map s) (incon_set s)  \<and>
             (Addr vp r- global_offset) \<in> \<Union>(ptable_trace' (heap s) (root s) ` UNIV) \<and>
                ((heap s) (Addr vp r- global_offset)) = Some w \<and> (\<exists>p pbits. decode_pde w = SectionPDE p pbits) \<and>
                   (\<exists>p pbits. decode_pde v = SectionPDE p pbits) \<and> asid s = a \<rbrace>
                          lval ::= rval ;; Flush (flushASID a)
                  \<lbrace>\<lambda>s. {asid s} \<times> UNIV \<inter> incon_set s = {} \<rbrace>"
(* simple to prove in case of asid flush, it should be va flush *)
  apply (vcgm vcg:  assign_sound)
  apply (rule conjI)
   apply (clarsimp simp: assigned_asids_consistent_def assigned_asid_va_map_def ran_def kernel_state_def)
   apply fastforce
  apply (rule conjI)
   apply (clarsimp simp: kernel_state_def)
  by force


lemma remap_section_entry_inactive_page_table:
  "\<Turnstile> \<lbrace> \<lambda>s. kernel_state s \<and> aval lval s = Some vp \<and> aval rval s = Some v \<and> vp \<in> SM \<and> SM = kernel_safe_region' s \<and>
         assigned_asids_consistent (root_map s) (incon_set s)  \<and> rt \<in> root_log s \<and> rt \<noteq> root s \<and>  (* remove this condition later *)
                  (Addr vp r- global_offset) \<in> \<Union>(ptable_trace' (heap s) rt ` UNIV) \<and> ((heap s) (Addr vp r- global_offset)) = Some w \<and> (\<exists>p pbits. decode_pde w = SectionPDE p pbits) \<and>
                   (\<exists>p pbits. decode_pde v = SectionPDE p pbits) \<and> root_map s rt = Some a \<rbrace>
                     lval ::= rval ;; Flush (flushASID a)
                  \<lbrace>\<lambda>s. assigned_asids_consistent (root_map s) (incon_set s) \<rbrace>"
   (* do it with kernel_writing_to_inactive_process_page_table_and_flush *)
  apply (vcgm vcg:  assign_sound)
  apply (rule conjI)
   apply (clarsimp simp: assigned_asids_consistent_def  assigned_asid_va_map_def ran_def kernel_state_def)
   apply auto [1]
  apply (rule conjI)
   apply (clarsimp simp: kernel_state_def)
  apply (subgoal_tac "pde_comp' (asid s) (heap s) (heap s(Addr (vp - global_offset) \<mapsto> v)) (root s) = {}")
   apply clarsimp
   apply (clarsimp simp: assigned_asids_consistent_def)
   apply force
  apply (rule ptable_trace_pde_comp)
  apply (clarsimp simp: kernel_state_def)
  apply (frule_tac rt = rt and rt' = "root s" and hp = "heap s" and p = "Addr vp r- global_offset" in non_overlapping_page_tables_ptrace ; clarsimp)
  by force



lemma  remap_scond_level_entry_inactive_page_table:   (* not relevant to entries as we are flushing asid, will be relevant if we flush vadder set *)
  "\<Turnstile> \<lbrace> \<lambda>s. kernel_state s \<and> aval lval s = Some vp \<and> aval rval s = Some v \<and> vp \<in> SM \<and> SM = kernel_safe_region' s \<and>
             assigned_asids_consistent (root_map s) (incon_set s)  \<and>
             (Addr vp r- global_offset) \<in> \<Union>(ptable_trace' (heap s) (root s) ` UNIV) \<and>
                ((heap s) (Addr vp r- global_offset)) = Some w \<and> (\<exists>p pbits. decode_pte w = SmallPagePTE p pbits) \<and>
                   (\<exists>p pbits. decode_pte v = SmallPagePTE p pbits) \<and> asid s = a \<rbrace>
                          lval ::= rval ;; Flush (flushASID a)
                  \<lbrace>\<lambda>s. {asid s} \<times> UNIV \<inter> incon_set s = {} \<rbrace>"
 apply (vcgm vcg:  assign_sound)
  apply (rule conjI)
   apply (clarsimp simp: assigned_asids_consistent_def assigned_asid_va_map_def ran_def kernel_state_def)
   apply fastforce
  apply (rule conjI)
   apply (clarsimp simp: kernel_state_def)
  by force


lemma remap_second_level_entry_inactive_page_table:
  "\<Turnstile> \<lbrace> \<lambda>s. kernel_state s \<and> aval lval s = Some vp \<and> aval rval s = Some v \<and> vp \<in> SM \<and> SM = kernel_safe_region' s \<and>
         assigned_asids_consistent (root_map s) (incon_set s)  \<and> rt \<in> root_log s \<and> rt \<noteq> root s \<and>  (* remove this condition later *)
                  (Addr vp r- global_offset) \<in> \<Union>(ptable_trace' (heap s) rt ` UNIV) \<and> ((heap s) (Addr vp r- global_offset)) = Some w \<and> (\<exists>p pbits. decode_pte w = SmallPagePTE p pbits) \<and>
                   (\<exists>p pbits. decode_pte v = SmallPagePTE p pbits) \<and> root_map s rt = Some a \<rbrace>
                     lval ::= rval ;; Flush (flushASID a)
                  \<lbrace>\<lambda>s. assigned_asids_consistent (root_map s) (incon_set s) \<rbrace>"
  (* same proof as remap_section_entry_inactive_page_table *)
  apply (vcgm vcg:  assign_sound)
  apply (rule conjI)
   apply (clarsimp simp: assigned_asids_consistent_def  assigned_asid_va_map_def ran_def kernel_state_def)
   apply auto [1]
  apply (rule conjI)
   apply (clarsimp simp: kernel_state_def)
  apply (subgoal_tac "pde_comp' (asid s) (heap s) (heap s(Addr (vp - global_offset) \<mapsto> v)) (root s) = {}")
   apply clarsimp
   apply (clarsimp simp: assigned_asids_consistent_def)
   apply force
  apply (rule ptable_trace_pde_comp)
  apply (clarsimp simp: kernel_state_def)
  apply (frule_tac rt = rt and rt' = "root s" and hp = "heap s" and p = "Addr vp r- global_offset" in non_overlapping_page_tables_ptrace ; clarsimp)
  by force

(*  above four theorems should be combined in one case *)

thm get_pte'_def


lemma
  "\<Turnstile> \<lbrace> \<lambda>s. kernel_state s \<and> aval lval s = Some vp \<and> aval rval s = Some v \<and> vp \<in> SM \<and> SM = kernel_safe_region' s \<and>
             assigned_asids_consistent (root_map s) (incon_set s)  \<and>
             (Addr vp r- global_offset) \<in> \<Union>(ptable_trace' (heap s) (root s) ` UNIV) \<and>
                ((heap s) (Addr vp r- global_offset)) = Some w \<and>
            (\<exists>p. decode_pde w = PageTablePDE p \<and>  (\<exists>w p1 pbits. (heap s) (p r+ ((vaddr_pt_index  vp) << 2))  = Some w \<and>  decode_pte w  = SmallPagePTE p1 pbits)) \<and>
                   (\<exists>p pbits. decode_pde v = SectionPDE p pbits) \<and> asid s = a \<rbrace>
                          lval ::= rval ;; Flush (flushASID a)
                  \<lbrace>\<lambda>s. {asid s} \<times> UNIV \<inter> incon_set s = {} \<rbrace>"

(*  *)


oops













end
