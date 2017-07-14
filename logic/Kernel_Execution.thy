theory Kernel_Execution
                  
imports Memory_Model
        

begin               


definition
  va_to_pa_offset :: "vaddr \<Rightarrow> 32 word \<Rightarrow> vaddr set \<rightharpoonup> paddr"
where
  "va_to_pa_offset va offset S \<equiv> if va \<in> S then Some (Addr (addr_val(va r+ offset))) else None"


(* here incon_set is not empty *)

definition
  state_initial :: "p_state \<Rightarrow> bool"
where
  "state_initial s \<equiv> heap s (root s) = Some 0x00000002 \<and> heap s (root s r+ 4) = Some 0x00100002 \<and> root s = Addr 0  \<and>
                      mode s = Kernel \<and> asid s = 0 \<and> root_map s (Addr 0) = Some 0 \<and> partial_inj (root_map s)"


definition
  vspace_section :: "32 word set"
where
  "vspace_section \<equiv> {va. (pd_idx_offset va = 0 \<or>  pd_idx_offset va = 4 )  }"


definition
  vadd_entries :: "32 word set"
where
  "vadd_entries \<equiv> {0x00000000 , 0x00000004}"


definition 
  kernel_memory :: "32 word set"
where
  "kernel_memory  = vspace_section - vadd_entries"


lemma state_intitial_ptable_lift_offset':
  "\<lbrakk>state_initial s \<rbrakk> \<Longrightarrow>
        \<forall>va\<in>vspace_section.  ptable_lift_m (heap s) (root s) (mode s) (Addr va) = va_to_pa_offset (Addr va) 0 (Addr `vspace_section)"
  apply (clarsimp simp: state_initial_def vspace_section_def va_to_pa_offset_def ptable_lift_m_def lookup_pde'_def get_pde'_def decode_heap_pde'_def vaddr_pd_index_def pd_idx_offset_def
                decode_pde_def decode_pde_section_def addr_base_def vaddr_offset_def mask_def)
   by word_bitwise
  

lemma state_intitial_ptable_lift_offset2:
  "\<lbrakk>state_initial s \<rbrakk> \<Longrightarrow>
        \<forall>va\<in>kernel_memory.  ptable_lift_m (heap s) (root s) (mode s) (Addr va) = va_to_pa_offset (Addr va) 0 (Addr `vspace_section)"
  using state_intitial_ptable_lift_offset' by (clarsimp simp: kernel_memory_def)
 
lemma [simp]:
  "state_initial s \<Longrightarrow> mode s = Kernel"
  by (simp add: state_initial_def)

lemma state_intitial_ptable_lift_offset2':
  "\<lbrakk>state_initial s \<rbrakk> \<Longrightarrow>
        \<forall>va\<in>kernel_memory.  ptable_lift' (heap s) (root s) (Addr va) = va_to_pa_offset (Addr va) 0 (Addr `vspace_section)"
  using state_intitial_ptable_lift_offset' by (clarsimp simp: kernel_memory_def)
 

lemma [simp]:
  "safe_memory S (s\<lparr>incon_set := IS\<rparr>) =  safe_memory S s "
  by (clarsimp simp: safe_memory_def ptrace_set_def)


lemma [simp]:
  "con_set S (s\<lparr>heap := hp ,  incon_set := IS\<rparr>) =  con_set S (s\<lparr>incon_set := IS\<rparr>) "
  by (clarsimp simp: con_set_def)


lemma ptable_lift_write:
  "\<lbrakk>state_initial s ; vp' \<in> kernel_memory; vp \<in> kernel_memory \<rbrakk> \<Longrightarrow>
     ptable_lift_m (heap s(Addr vp' \<mapsto> x)) (root s) (mode s) (Addr vp) =  ptable_lift_m  (heap s)  (root s) (mode s)  (Addr vp)"
  apply (clarsimp simp: kernel_memory_def vspace_section_def vadd_entries_def)
  apply (erule_tac P = "pd_idx_offset vp = 0" in  disjE)
   by (clarsimp simp: state_initial_def ptable_lift'_def lookup_pde'_def get_pde'_def
     decode_heap_pde'_def Let_def pd_idx_offset_def vaddr_pd_index_def decode_pde_def decode_pde_section_def)+
 

lemma ptable_lift_write':
  "\<lbrakk> state_initial s ; vp' \<in> kernel_memory; vp \<in> kernel_memory \<rbrakk> \<Longrightarrow>
     ptable_lift' (heap s(Addr vp' \<mapsto> x)) (root s)  (Addr vp) =  ptable_lift'  (heap s)  (root s)  (Addr vp)"
  apply (clarsimp simp: kernel_memory_def vspace_section_def vadd_entries_def)
  apply (erule_tac P = "pd_idx_offset vp = 0" in  disjE)
   by (clarsimp simp: state_initial_def ptable_lift'_def lookup_pde'_def get_pde'_def
     decode_heap_pde'_def Let_def pd_idx_offset_def vaddr_pd_index_def decode_pde_def decode_pde_section_def)+
 

lemma kernel_memory_vspace:
  "vp : kernel_memory \<Longrightarrow> vp : vspace_section"
  by (simp add: kernel_memory_def)


lemma va_to_pa_offset_0 [simp]:
  "vp : kernel_memory \<Longrightarrow> va_to_pa_offset (Addr vp) 0 (Addr ` vspace_section) = Some (Addr vp)"
  by (simp add: va_to_pa_offset_def kernel_memory_vspace)


lemma state_intial_element_ptrace [simp]:
  "\<lbrakk>state_initial s;  va \<in> kernel_memory \<rbrakk> \<Longrightarrow>  Addr va \<notin> ptrace_set kernel_memory s"
  apply (clarsimp simp: state_initial_def ptrace_set_def kernel_memory_def vspace_section_def)
  apply (erule_tac P = "pd_idx_offset a = 0" in disjE)
   apply (subgoal_tac "ptable_trace' (heap s) (Addr 0) (Addr a) = {Addr 0}")
    using vadd_entries_def  apply force
   apply (clarsimp simp: ptable_trace'_def Let_def pd_idx_offset_def decode_heap_pde'_def
              decode_pde_def decode_pde_section_def)
  apply (subgoal_tac "ptable_trace' (heap s) (Addr 0) (Addr a) = {Addr 4}")
   using vadd_entries_def  apply force
  by (clarsimp simp: ptable_trace'_def Let_def pd_idx_offset_def decode_heap_pde'_def
                decode_pde_def decode_pde_section_def)


declare assign_sound [vcg del] 


lemma safe_set_preserved_kernel:
  "\<Turnstile> \<lbrace> \<lambda>s. state_initial s \<and> aval lval s = Some vp \<and> aval rval s = Some v \<and> vp \<in> kernel_memory \<and>  safe_set (kernel_memory) s\<rbrace>
                          lval ::= rval  \<lbrace>\<lambda>s. safe_set (kernel_memory) s\<rbrace>"
  apply (rule weak_pre)
  by (rule safe_set_preserved  , clarsimp)
 
(* partial injectivity is not being used here *)


lemma  [simp]:
  "state_initial s \<Longrightarrow> asid s \<in> set_of_assigned_asids (root_map s)"
  apply (clarsimp simp: state_initial_def set_of_assigned_asids_def)
  by force

lemma [simp]:
  "\<lbrakk>state_initial s; assinged_asids_consistent (root_map s) (incon_set s)\<rbrakk> \<Longrightarrow> con_set kernel_memory s"
  apply (clarsimp simp: assinged_asids_consistent_def con_set_def asids_va_set_def set_of_assigned_asids_def asid_va_set_def state_initial_def)
  apply force
done

lemma assign_safe:               
  "\<Turnstile> \<lbrace> \<lambda>s. state_initial s \<and> aval lval s = Some vp \<and> aval rval s = Some v \<and> vp \<in> kernel_memory \<and> 
             assinged_asids_consistent (root_map s) (incon_set s) \<rbrace>    (* assumption added for consistency*)
                     lval ::= rval  
                  \<lbrace>\<lambda>s. safe_set (kernel_memory) s \<and>  heap s (Addr vp) = Some v\<rbrace>"
  apply_trace (vcg vcg: weak_pre_write')
  apply (clarsimp simp: safe_set_def)
  by (clarsimp simp: state_intitial_ptable_lift_offset2' safe_memory_def)



lemma assignments_safe_kernel:
  "\<Turnstile> \<lbrace> \<lambda>s. state_initial s \<and> aval lval1 s = Some vp1 \<and> aval rval1 s = Some v1 \<and> vp1 \<in> kernel_memory \<and> 
            aval lval2 (s\<lparr>heap := heap s(Addr vp1 \<mapsto> v1)\<rparr>) = Some vp2 \<and> 
            aval rval2 (s\<lparr>heap := heap s(Addr vp1 \<mapsto> v1)\<rparr>) = Some v2 \<and> vp2 \<in> kernel_memory  \<and>  
           assinged_asids_consistent (root_map s) (incon_set s)\<rbrace>  
                  lval1 ::= rval1 ;; lval2 ::= rval2 
      \<lbrace>\<lambda>s. safe_set (kernel_memory) s \<and> heap s (Addr vp2) = Some v2\<rbrace>"
  apply_trace (vcg vcg: weak_pre_write')
  apply (clarsimp simp: safe_set_def)
  by (clarsimp simp: ptable_lift_write' state_intitial_ptable_lift_offset2' safe_memory_def)


(* kernel code *)

(* function types are not very good *)

(* in systems, kernel window is all of the memory except the devices, but in our case (from verification point of view),
     it should be all of the memory except the kernel mappings themselves and kernel code  *)

definition 
  kernel_window :: "32 word set \<Rightarrow> 32 word set"
where
  "kernel_window  KC =  kernel_memory - KC"


lemma safe_set_safe_set_kernel [simp]:
  "safe_set kernel_memory s \<Longrightarrow>  safe_set (kernel_window  KC) s"
  by (clarsimp simp: kernel_window_def safe_set_def con_set_def safe_memory_def ptrace_set_def , force)
 


lemma assign_safe_kernel_window:
  "\<Turnstile> \<lbrace> \<lambda>s.  state_initial s \<and> aval lval s = Some vp \<and> aval rval s = Some v \<and> vp \<in> kernel_window KC  \<and> KC \<subseteq> kernel_memory \<and>  
           assinged_asids_consistent (root_map s) (incon_set s) (* this is an extra assumption *)  \<rbrace>  
                lval ::= rval  
                       \<lbrace>\<lambda>s. safe_set (kernel_window  KC) s\<rbrace>"
  apply (rule conseq_sound)
   apply (rule assign_safe [where vp = vp and v = v], clarsimp)
  by (clarsimp simp: kernel_window_def)


lemma assignments_safe_kernel_window:
  "\<Turnstile> \<lbrace> \<lambda>s. state_initial s \<and> aval lval1 s = Some vp1 \<and> aval rval1 s = Some v1 \<and> vp1 \<in> kernel_window KC  \<and> KC \<subseteq> kernel_memory \<and>
            aval lval2 (s\<lparr>heap := heap s(Addr vp1 \<mapsto> v1)\<rparr>) = Some vp2 \<and> aval rval2 (s\<lparr>heap := heap s(Addr vp1 \<mapsto> v1)\<rparr>) = Some v2 \<and> vp2 \<in> kernel_window KC \<and>  
           assinged_asids_consistent (root_map s) (incon_set s) \<rbrace>  
                lval1 ::= rval1 ;; lval2 ::= rval2  \<lbrace>\<lambda>s. safe_set (kernel_window KC) s\<rbrace>"
  apply (rule conseq_sound)
   apply (rule assignments_safe_kernel [of _ vp1 _ v1 _ vp2 _ v2])
  apply clarsimp
  by (clarsimp simp: kernel_window_def)



(* Kernel execution phase, it should not write to the global mappings of current and inactive processes  *)

definition
  kernel_state :: "p_state \<Rightarrow> bool"
where
  "kernel_state s \<equiv> \<exists>rt a. root s = rt  \<and> current_page_table s \<and> mode s = Kernel \<and> 
                        asid s = a  \<and> root_map s rt = Some a \<and> partial_inj (root_map s) \<and> rt\<in>root_log s \<and>
                        global_mappings_of_all_processes s \<and> \<Union>(ptable_trace' (heap s) (root s) ` UNIV) \<subseteq> kernel_phy_mem" 

lemma [simp]:
  "\<lbrakk>kernel_state s; assinged_asids_consistent (root_map s) (incon_set s)\<rbrakk> \<Longrightarrow> 
                    con_set VA s"
  apply (clarsimp simp: assinged_asids_consistent_def con_set_def asids_va_set_def set_of_assigned_asids_def asid_va_set_def kernel_state_def)
  apply force
done

lemma [simp]:
  "\<lbrakk>kernel_state s;  va \<in> kernel_safe_region' s\<rbrakk> \<Longrightarrow> ptable_lift_m (heap s) (root s) (mode s) (Addr va) = Some (Addr va r- global_offset) "
  by (clarsimp simp: kernel_state_def global_mappings_of_all_processes_def kernel_safe_region'_def vas_mapped_by_global_mappings_def)
  

lemma global_mappings_decode':
  "\<lbrakk>kernel_state s  ; va \<in> kernel_safe_region' s\<rbrakk> \<Longrightarrow> 
         \<exists>p perm. decode_heap_pde' (heap s) (root s r+ (vaddr_pd_index va << 2)) =  Some (SectionPDE p perm)"
  apply (clarsimp simp: kernel_safe_region'_def vas_mapped_by_global_mappings_def global_mappings_of_all_processes_def pd_idx_offset_def get_pde'_def kernel_state_def)
  by force


lemma  kernel_safe_region_ptable_trace' [simp]:
  " \<lbrakk>kernel_state s; vp' \<in> kernel_safe_region' s; vp \<in> kernel_safe_region' s\<rbrakk> \<Longrightarrow> Addr (vp' - global_offset) \<notin> ptable_trace' (heap s) (root s) (Addr vp)"
  apply (frule_tac va = vp in  global_mappings_decode')
   apply (clarsimp simp: kernel_state_def) apply clarsimp
  apply(clarsimp simp:  kernel_state_def ptable_trace'_def kernel_safe_region'_def vas_mapped_by_global_mappings_def vas_of_current_state_mapped_to_global_mappings_of_all_processes_def pd_idx_offset_def)+
done


lemma  kernel_execution_assign:          
  "\<Turnstile> \<lbrace> \<lambda>s. kernel_state s \<and> aval lval s = Some vp \<and> aval rval s = Some v \<and> vp \<in> SM \<and> SM = kernel_safe_region' s \<and>
             assinged_asids_consistent (root_map s) (incon_set s) \<rbrace>    (* assumption added for consistency *)
                     lval ::= rval  
                  \<lbrace>\<lambda>s. safe_set SM s \<and>  heap s (Addr vp r- global_offset) = Some v\<rbrace>"
  apply_trace (vcg vcg: weak_pre_write')
  by (clarsimp simp: safe_set_def safe_memory_def ptrace_set_def)
 

named_theorems imp_gen

method imp_gen declares imp_gen = (drule imp_gen, simp)

lemma [imp_gen]:
  "kernel_state s  \<Longrightarrow> \<exists>rt a. root s = rt  \<and> mode s = Kernel \<and>  rt \<in> root_log s \<and> global_mappings_of_all_processes s "
  by (clarsimp simp: kernel_state_def)



lemma boot_kerenl_region_offset':
  "kernel_state s  \<Longrightarrow>
        \<forall>va\<in>kernel_safe_region' s.  ptable_lift' (heap s) (root s) (Addr va) = Some (Addr va r- global_offset)"
  by imp_gen



(* do with imp_gen *)
lemma ptable_lift_write_n:
  "\<lbrakk>kernel_state s ; vp' \<in> kernel_safe_region' s; vp \<in> kernel_safe_region' s \<rbrakk> \<Longrightarrow>
     ptable_lift_m (heap s(Addr vp' r- global_offset \<mapsto> x)) (root s)  (mode s) (Addr vp) =  ptable_lift_m  (heap s)  (root s)  (mode s) (Addr vp)"
  apply clarsimp
  apply (subgoal_tac "Addr (vp' - global_offset) \<notin> ptable_trace' (heap s) (root s) (Addr vp)")
   apply (frule_tac pa = "Addr (vp - global_offset)" and v = x in ptable_lift_preserved')
    apply (clarsimp simp: boot_kerenl_region_offset')
   apply (clarsimp simp: kernel_state_def)
  by clarsimp


lemma kernel_execution_multi_assign:
  "\<Turnstile> \<lbrace> \<lambda>s. kernel_state s \<and> aval lval1 s = Some vp1 \<and> aval rval1 s = Some v1 \<and> vp1 \<in> SM \<and> 
            aval lval2 (s\<lparr>heap := heap s(Addr vp1 r- global_offset \<mapsto> v1)\<rparr>) = Some vp2 \<and> 
            aval rval2 (s\<lparr>heap := heap s(Addr vp1 r- global_offset \<mapsto> v1)\<rparr>) = Some v2 \<and> vp2 \<in> SM  \<and>  
           assinged_asids_consistent (root_map s) (incon_set s) \<and>  SM = kernel_safe_region' s\<rbrace>  
                  lval1 ::= rval1 ;; lval2 ::= rval2 
           \<lbrace>\<lambda>s. safe_set SM s \<and> heap s (Addr vp2 r- global_offset) = Some v2\<rbrace>"
  apply_trace (vcg vcg: weak_pre_write')
  apply (rule conjI)
   apply (clarsimp simp: safe_set_def safe_memory_def ptrace_set_def)
  using  ptable_lift_write_n by force


end



