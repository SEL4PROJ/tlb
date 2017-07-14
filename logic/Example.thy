theory Example
                  
imports Safe_Set
        

begin               


definition 
   pd_idx_offset :: "32 word \<Rightarrow> machine_word"
where
  "pd_idx_offset vp = ((vaddr_pd_index vp) << 2)"


definition
  va_to_pa_offset :: "vaddr \<Rightarrow> 32 word \<Rightarrow> vaddr set \<rightharpoonup> paddr"
where
  "va_to_pa_offset va offset S \<equiv> if va \<in> S then Some (Addr (addr_val(va r+ offset))) else None"


definition
  state_initial :: "p_state \<Rightarrow> bool"
where
  "state_initial s \<equiv> heap s (root s) = Some 0x00000002 \<and> heap s (root s r+ 4) = Some 0x00100002 \<and> root s = Addr 0 
                          \<and> mode s = Kernel \<and> asid s = 0 \<and> root_map s (Addr 0) = Some 0 \<and> partial_inj (root_map s) "


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
  "\<lbrakk> state_initial s ; vp' \<in> kernel_memory; vp \<in> kernel_memory \<rbrakk> \<Longrightarrow>
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
  
 
lemma state_initial_safe_set [simp]:
  "state_initial s \<Longrightarrow> safe_set kernel_memory (s\<lparr>incon_set := {}\<rparr>)"
  apply (frule state_intitial_ptable_lift_offset2)
  apply (clarsimp simp: safe_set_def con_set_def)
  by (clarsimp simp: safe_memory_def)


declare assign_sound [vcg del] 


lemma safe_set_preserved_kernel:
  "\<Turnstile> \<lbrace> \<lambda>s. state_initial s \<and> aval lval s = Some vp \<and> aval rval s = Some v \<and> vp \<in> kernel_memory \<and>  safe_set (kernel_memory) s\<rbrace>
                          lval ::= rval  \<lbrace>\<lambda>s. safe_set (kernel_memory) s\<rbrace>"
  apply (rule weak_pre)
  by (rule safe_set_preserved  , clarsimp)
 

lemma flush_assign_safe:
  "\<Turnstile> \<lbrace> \<lambda>s. state_initial s \<and> aval lval s = Some vp \<and> aval rval s = Some v \<and> vp \<in> kernel_memory \<rbrace>  
                Flush flushTLB ;; lval ::= rval  
                     \<lbrace>\<lambda>s. safe_set (kernel_memory) s\<rbrace>"
  apply vcg
    apply (rule safe_set_preserved)
   by (rule flush_sound , clarsimp simp: state_initial_def)
 


lemma flush_assignments_safe_kernel:
  "\<Turnstile> \<lbrace> \<lambda>s. state_initial s \<and> aval lval1 s = Some vp1 \<and> aval rval1 s = Some v1 \<and> vp1 \<in> kernel_memory \<and> 
            aval lval2 (s\<lparr>heap := heap s(Addr vp1 \<mapsto> v1)\<rparr>) = Some vp2 \<and> 
            aval rval2 (s\<lparr>heap := heap s(Addr vp1 \<mapsto> v1)\<rparr>) = Some v2 \<and> vp2 \<in> kernel_memory  \<rbrace>  
                Flush flushTLB ;; lval1 ::= rval1 ;; lval2 ::= rval2 
      \<lbrace>\<lambda>s. safe_set (kernel_memory) s \<and> heap s (Addr vp2) = Some v2\<rbrace>"
  apply_trace (vcg vcg: weak_pre_write')
  by (clarsimp simp: ptable_lift_write' state_intitial_ptable_lift_offset2')

 
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

lemma asid_assgin_safe:               
  "\<Turnstile> \<lbrace> \<lambda>s. state_initial s \<and> aval lval s = Some vp \<and> aval rval s = Some v \<and> vp \<in> kernel_memory \<and> 
             assinged_asids_consistent (root_map s) (incon_set s) \<rbrace>    (* work on these two assumption *)
                     lval ::= rval  
                  \<lbrace>\<lambda>s. safe_set (kernel_memory) s \<and>  heap s (Addr vp) = Some v\<rbrace>"
  apply_trace (vcg vcg: weak_pre_write')
  apply (clarsimp simp: safe_set_def)
  by (clarsimp simp: state_intitial_ptable_lift_offset2' safe_memory_def)
  



lemma asid_assignments_safe_kernel:
  "\<Turnstile> \<lbrace> \<lambda>s. state_initial s \<and> aval lval1 s = Some vp1 \<and> aval rval1 s = Some v1 \<and> vp1 \<in> kernel_memory \<and> 
            aval lval2 (s\<lparr>heap := heap s(Addr vp1 \<mapsto> v1)\<rparr>) = Some vp2 \<and> 
            aval rval2 (s\<lparr>heap := heap s(Addr vp1 \<mapsto> v1)\<rparr>) = Some v2 \<and> vp2 \<in> kernel_memory  \<and>  
           assinged_asids_consistent (root_map s) (incon_set s)\<rbrace>  
                  lval1 ::= rval1 ;; lval2 ::= rval2 
      \<lbrace>\<lambda>s. safe_set (kernel_memory) s \<and> heap s (Addr vp2) = Some v2\<rbrace>"
  apply_trace (vcg vcg: weak_pre_write')
  apply (clarsimp simp: safe_set_def)
  by (clarsimp simp: ptable_lift_write' state_intitial_ptable_lift_offset2' safe_memory_def)


declare assign_sound [vcg add] 


(* kernel code *)

(* function types are not very good *)

(* in systems, kernel window is all of the memory except the devices, but in our case (from verification point of view),
     it should be all of the memory except the kernel mappings themselves and kernel code  *)

definition 
  kernel_window :: "32 word set \<Rightarrow> 32 word set"
where
  "kernel_window  KC =  kernel_memory - KC"

thm state_initial_safe_set

lemma state_initial_safe_set_kernel [simp]:
  "state_initial s \<Longrightarrow> safe_set (kernel_window KC)  (s\<lparr>incon_set := {}\<rparr>)"
  apply (frule state_initial_safe_set)
  by (clarsimp simp: kernel_window_def safe_set_def con_set_def safe_memory_def ptrace_set_def , force)
  


lemma safe_set_safe_set_kernel [simp]:
  "safe_set kernel_memory s \<Longrightarrow>  safe_set (kernel_window  KC) s"
  by (clarsimp simp: kernel_window_def safe_set_def con_set_def safe_memory_def ptrace_set_def , force)
 


lemma flush_assign_safe_kernel_window:
  "\<Turnstile> \<lbrace> \<lambda>s.  state_initial s \<and> aval lval s = Some vp \<and> aval rval s = Some v \<and> vp \<in> kernel_window KC  \<and> KC \<subseteq> kernel_memory (* this is an extra assumption *)  \<rbrace>  
                Flush flushTLB ;; lval ::= rval  
                       \<lbrace>\<lambda>s. safe_set (kernel_window  KC) s\<rbrace>"
  apply (rule conseq_sound)
   apply (rule flush_assign_safe [where vp = vp and v = v], clarsimp)
  by (clarsimp simp: kernel_window_def)


lemma flush_assignments_safe_kernel_window:
  "\<Turnstile> \<lbrace> \<lambda>s. state_initial s \<and> aval lval1 s = Some vp1 \<and> aval rval1 s = Some v1 \<and> vp1 \<in> kernel_window KC  \<and> KC \<subseteq> kernel_memory \<and>
            aval lval2 (s\<lparr>heap := heap s(Addr vp1 \<mapsto> v1)\<rparr>) = Some vp2 \<and> aval rval2 (s\<lparr>heap := heap s(Addr vp1 \<mapsto> v1)\<rparr>) = Some v2 \<and> vp2 \<in> kernel_window KC  \<rbrace>  
                Flush flushTLB ;; lval1 ::= rval1 ;; lval2 ::= rval2  \<lbrace>\<lambda>s. safe_set (kernel_window KC) s\<rbrace>"
  apply (rule conseq_sound)
   apply (rule flush_assignments_safe_kernel [of _ vp1 _ v1 _ vp2 _ v2])
  apply clarsimp
  by (clarsimp simp: kernel_window_def)

  

definition
  st_initial :: "p_state \<Rightarrow> bool"
where
  "st_initial s   \<equiv>   heap s (root s) = Some 0x00000002 \<and> heap s (root s r+ 0x4) = Some 0x00100002 \<and> 
                           heap s (root s r+ 0x8) = Some 0x00000C01 \<and>  heap s (root s r+ 0x00000C00) = Some 0x0000F032 \<and>
                           root s = Addr 0 \<and>  mode s = Kernel  \<and> asid s = 0 \<and> root_map s (Addr 0) = Some 0 \<and> partial_inj (root_map s)"


definition
  user_vas :: "32 word set"
where
  "user_vas  \<equiv> {va. pd_idx_offset va = 0x8 \<and> 0xC00 + ((va >> 12) && 0xFF << 2) = 0x00000C00} - {0x00000000 , 0x00000004 , 0x00000008 , 0x00000C00}"


lemma aval_state_heap_mode_eq[simp]:
  "(aval e (s\<lparr> mode := m, heap := h\<rparr>) = Some v) = (aval e (s\<lparr>heap := h\<rparr>) = Some v)"
  by (induct e arbitrary: v; clarsimp split: option.splits; fastforce)
            


lemma  [simp]:
  "st_initial s \<Longrightarrow> mode s = Kernel"
  by (clarsimp simp: st_initial_def)


lemma  user_ptrace:
  "\<lbrakk>st_initial s;  va \<in> user_vas\<rbrakk>
              \<Longrightarrow> ptable_trace' (heap s) (root s) (Addr va) = {Addr 8, Addr 0xC00}"
  apply (clarsimp simp: vaddr_offset_def mask_def user_vas_def pd_idx_offset_def vaddr_pd_index_def ptable_trace'_def Let_def decode_heap_pde'_def st_initial_def decode_pde_def decode_pde_pt_def
                           pt_base_mask_def vaddr_pt_index_def)
  by blast

lemma [simp]:
  "ptrace_set U (s\<lparr>incon_set := is, mode := m\<rparr>) = ptrace_set U s"
  by (clarsimp simp: ptrace_set_def)


lemma user_ptable_lift_defined:
  "\<lbrakk>st_initial s;  va \<in> user_vas\<rbrakk>  \<Longrightarrow> ptable_lift_m (heap s) (root s) User (Addr va) = Some ((Addr 0xF000) r+ vaddr_offset ArmSmallPage va)"
  apply (clarsimp simp: user_vas_def ptable_lift_m_def lookup_pde_perm_def filter_pde_def lookup_pde'_def get_pde'_def vaddr_pd_index_def pd_idx_offset_def)
  apply (clarsimp simp: decode_heap_pde'_def st_initial_def)
  apply (clarsimp simp: decode_pde_def decode_pde_pt_def  lookup_pte'_def get_pte'_def pt_base_mask_def decode_heap_pte'_def vaddr_pt_index_def mask_def)
  apply (clarsimp simp: decode_pte_def decode_pte_small_def user_perms_def perm_bits_pte_small_def addr_base_def mask_def)
done


lemma  user_vas_ptace:
  "\<lbrakk>st_initial s; vp1 \<in> user_vas;  vp2 \<in> user_vas\<rbrakk>
         \<Longrightarrow> Addr (0xF000 + vaddr_offset ArmSmallPage vp1) \<notin> ptable_trace' (heap s) (root s) (Addr vp2)"
  apply (frule_tac va = vp2 in  user_ptrace; clarsimp simp: vaddr_offset_def mask_def)
  by word_bitwise


declare assign_sound [vcg del] 
           
lemma ptable_lift_preserved_m':
  "\<lbrakk>ptable_lift_m h r m vp = Some pa; p \<notin> ptable_trace' h r vp\<rbrakk> \<Longrightarrow> ptable_lift_m (h(p \<mapsto> v)) r m vp = Some pa"
 by (clarsimp simp: ptable_lift_preserved_m)


lemma st_initial_user_safe_set [simp]:
  "st_initial s \<Longrightarrow> safe_set user_vas (s\<lparr>incon_set := {}, mode := User\<rparr>)"
  apply (clarsimp simp: safe_set_def con_set_def safe_memory_def)
  apply (frule_tac va = va in user_ptable_lift_defined; clarsimp simp: ptrace_set_def user_ptrace vaddr_offset_def mask_def)
  by word_bitwise
 
(*  safe set established after changing the mode  *)

lemma flush_assignments_safe_kernel_user:
  "\<Turnstile> \<lbrace> \<lambda>s. st_initial s \<and> aval lval1 s = Some vp1 \<and> aval rval1 s = Some v1 \<and> vp1 \<in> user_vas \<and> 
            aval lval2 (s\<lparr>heap := heap s(Addr 0xF000 r+ vaddr_offset ArmSmallPage vp1 \<mapsto> v1)\<rparr>) = Some vp2 \<and> 
            aval rval2 (s\<lparr>heap := heap s(Addr 0xF000 r+ vaddr_offset ArmSmallPage vp1 \<mapsto> v1)\<rparr>) = Some v2 \<and> vp2 \<in> user_vas  \<rbrace>  
                Flush flushTLB ;; SetMode User;;  lval1 ::= rval1 ;; lval2 ::= rval2 
            \<lbrace>\<lambda>s. safe_set user_vas s \<and> heap s (Addr 0xF000 r+ vaddr_offset ArmSmallPage vp2) = Some v2\<rbrace>"
  apply_trace (vcg vcg: weak_pre_write')
   (* clarsimp is giving me problems *)
  apply (frule_tac va = vp1 in user_ptable_lift_defined ; clarsimp)
  apply (frule_tac va = vp2 in user_ptable_lift_defined ; clarsimp)
  by (frule_tac p = "Addr (0xF000 + vaddr_offset ArmSmallPage vp1)" and vp = "Addr vp2"  and v = v1 in  ptable_lift_preserved_m' ; clarsimp simp: user_vas_ptace)
  
lemma [simp]:
  "con_set user_vas (s\<lparr>mode := User\<rparr>) =  con_set user_vas s"
  by (clarsimp simp: con_set_def)


lemma   st_initial_user_safe_set' [simp]:
  "\<lbrakk>st_initial s; assinged_asids_consistent (root_map s) (incon_set s)\<rbrakk>
         \<Longrightarrow> safe_set user_vas (s\<lparr>mode := User\<rparr>)"
  apply (clarsimp simp: safe_set_def)
  apply (rule)
  prefer 2
  apply (clarsimp simp: con_set_def st_initial_def assinged_asids_consistent_def asids_va_set_def set_of_assigned_asids_def asid_va_set_def) 
   apply force 
  apply (clarsimp simp: safe_set_def con_set_def safe_memory_def)
  apply (frule_tac va = va in user_ptable_lift_defined; clarsimp simp: ptrace_set_def user_ptrace vaddr_offset_def mask_def)
  by word_bitwise



lemma asid_assignments_safe_kernel_user:
  "\<Turnstile> \<lbrace> \<lambda>s. st_initial s \<and> aval lval1 s = Some vp1 \<and> aval rval1 s = Some v1 \<and> vp1 \<in> user_vas \<and> 
            aval lval2 (s\<lparr>heap := heap s(Addr 0xF000 r+ vaddr_offset ArmSmallPage vp1 \<mapsto> v1)\<rparr>) = Some vp2 \<and> 
            aval rval2 (s\<lparr>heap := heap s(Addr 0xF000 r+ vaddr_offset ArmSmallPage vp1 \<mapsto> v1)\<rparr>) = Some v2 \<and> vp2 \<in> user_vas \<and>
                assinged_asids_consistent (root_map s) (incon_set s)  \<rbrace>  
                 SetMode User;;  lval1 ::= rval1 ;; lval2 ::= rval2 
            \<lbrace>\<lambda>s. safe_set user_vas s \<and> heap s (Addr 0xF000 r+ vaddr_offset ArmSmallPage vp2) = Some v2\<rbrace>"
  apply_trace (vcg vcg: weak_pre_write')
   (* clarsimp is giving me problems *)
  apply (frule_tac va = vp1 in user_ptable_lift_defined ; clarsimp)
  apply (frule_tac va = vp2 in user_ptable_lift_defined ; clarsimp)
  by (frule_tac p = "Addr (0xF000 + vaddr_offset ArmSmallPage vp1)" and vp = "Addr vp2"  and v = v1 in  ptable_lift_preserved_m' ; clarsimp simp: user_vas_ptace) 



(* same as st_initial except mode = user *)

definition
  st_initial' :: "p_state \<Rightarrow> bool"
where
  "st_initial' s   \<equiv>   heap s (root s) = Some 0x00000002 \<and> heap s (root s r+ 0x4) = Some 0x00100002 \<and> 
                           heap s (root s r+ 0x8) = Some 0x00000C01 \<and>  heap s (root s r+ 0x00000C00) = Some 0x0000F032 \<and>
                           root s = Addr 0 \<and>  mode s = User \<and> asid s = 0 \<and> root_map s (Addr 0) = Some 0 \<and> partial_inj (root_map s)"


lemma user_ptable_lift_defined':
  "\<lbrakk>st_initial' s;  va \<in> user_vas\<rbrakk>  \<Longrightarrow> ptable_lift_m (heap s) (root s) (mode s) (Addr va) = Some ((Addr 0xF000) r+ vaddr_offset ArmSmallPage va)"
  apply (clarsimp simp: user_vas_def ptable_lift_m_def lookup_pde'_def lookup_pde_perm_def filter_pde_def get_pde'_def vaddr_pd_index_def pd_idx_offset_def)
  apply (clarsimp simp: decode_heap_pde'_def st_initial'_def)
  apply (clarsimp simp: decode_pde_def decode_pde_pt_def  lookup_pte'_def get_pte'_def pt_base_mask_def decode_heap_pte'_def vaddr_pt_index_def mask_def)
  apply (clarsimp simp: decode_pte_def decode_pte_small_def user_perms_def perm_bits_pte_small_def addr_base_def mask_def)
done


lemma  user_ptrace':
  "\<lbrakk>st_initial' s;  va \<in> user_vas\<rbrakk>
              \<Longrightarrow> ptable_trace' (heap s) (root s) (Addr va) = {Addr 8, Addr 0xC00}"
  apply (clarsimp simp: vaddr_offset_def mask_def user_vas_def pd_idx_offset_def vaddr_pd_index_def ptable_trace'_def Let_def decode_heap_pde'_def st_initial'_def decode_pde_def decode_pde_pt_def
                           pt_base_mask_def vaddr_pt_index_def)
  by blast


lemma  user_vas_ptace':
  "\<lbrakk>st_initial' s; vp1 \<in> user_vas;  vp2 \<in> user_vas\<rbrakk>
         \<Longrightarrow> Addr (0xF000 + vaddr_offset ArmSmallPage vp1) \<notin> ptable_trace' (heap s) (root s) (Addr vp2)"
  apply (frule_tac va = vp2 in  user_ptrace'; clarsimp simp: vaddr_offset_def mask_def)
  by word_bitwise


lemma st'_initial_user_safe_set[simp]:
  "st_initial' s \<and> incon_set s = {} \<Longrightarrow> safe_set user_vas s"
  apply (clarsimp simp: safe_set_def con_set_def safe_memory_def)
  by(frule_tac va = va in user_ptable_lift_defined';  clarsimp simp:  ptrace_set_def user_vas_ptace')

lemma st'_initial_user_safe_set'[simp]:
  "st_initial' s \<and>  assinged_asids_consistent (root_map s) (incon_set s) \<Longrightarrow> safe_set user_vas s"
  apply (clarsimp simp: safe_set_def safe_memory_def)
  apply (rule conjI)
  prefer 2
  apply (clarsimp simp: con_set_def st_initial'_def assinged_asids_consistent_def asids_va_set_def set_of_assigned_asids_def asid_va_set_def) 
   apply force 
  apply clarsimp
  apply (frule_tac va = va in user_ptable_lift_defined';  clarsimp simp:  ptrace_set_def user_vas_ptace')
done


lemma flush_assignments_safe_user:
  "\<Turnstile> \<lbrace> \<lambda>s. st_initial' s \<and> aval lval1 s = Some vp1 \<and> aval rval1 s = Some v1 \<and> vp1 \<in> user_vas \<and> 
            aval lval2 (s\<lparr>heap := heap s(Addr 0xF000 r+ vaddr_offset ArmSmallPage vp1 \<mapsto> v1)\<rparr>) = Some vp2 \<and> 
            aval rval2 (s\<lparr>heap := heap s(Addr 0xF000 r+ vaddr_offset ArmSmallPage vp1 \<mapsto> v1)\<rparr>) = Some v2 \<and> vp2 \<in> user_vas \<and> incon_set s = {} \<rbrace>  
                     lval1 ::= rval1 ;; lval2 ::= rval2 
      \<lbrace>\<lambda>s. safe_set (user_vas) s \<and> heap s (Addr 0xF000 r+ vaddr_offset ArmSmallPage vp2) = Some v2\<rbrace>"
  apply_trace (vcg vcg: weak_pre_write')
  by(clarsimp simp: user_ptable_lift_defined'  ptable_lift_preserved_m' user_vas_ptace')
 

lemma asid_assignments_safe_user:
  "\<Turnstile> \<lbrace> \<lambda>s. st_initial' s \<and> aval lval1 s = Some vp1 \<and> aval rval1 s = Some v1 \<and> vp1 \<in> user_vas \<and> 
            aval lval2 (s\<lparr>heap := heap s(Addr 0xF000 r+ vaddr_offset ArmSmallPage vp1 \<mapsto> v1)\<rparr>) = Some vp2 \<and> 
            aval rval2 (s\<lparr>heap := heap s(Addr 0xF000 r+ vaddr_offset ArmSmallPage vp1 \<mapsto> v1)\<rparr>) = Some v2 \<and> vp2 \<in> user_vas \<and> 
                 assinged_asids_consistent (root_map s) (incon_set s)\<rbrace>  
                     lval1 ::= rval1 ;; lval2 ::= rval2 
      \<lbrace>\<lambda>s. safe_set (user_vas) s \<and> heap s (Addr 0xF000 r+ vaddr_offset ArmSmallPage vp2) = Some v2\<rbrace>"
  apply_trace (vcg vcg: weak_pre_write')
  by (clarsimp simp: user_ptable_lift_defined'  ptable_lift_preserved_m' user_vas_ptace')



definition
  state_initial' :: "p_state \<Rightarrow> bool"
where
  "state_initial' s \<equiv> heap s (root s) = Some 0x00000002 \<and> heap s (root s r+ 4) = Some 0x00100002 \<and> 
                        heap s (root s r+ 0xA) = Some 0x00000002 \<and> heap s (root s r+ 0xE) = Some 0x00100002 \<and> 
                        heap s (root s r+ 0x12) = Some 0x00000C01 \<and>  heap s (root s r+ 0x00000C00) = Some 0x0000F032  \<and> (* small page translation table entry for user *) 
                           root s = Addr 0 \<and>  mode s = Kernel"


(* addresses mapped by the page_table_ entry *)

thm safe_set_def
thm user_vas_def
thm st_initial'_def


lemma user_ptable_lift_defined_constant:
  "\<lbrakk>state_initial' s;  va \<in> user_vas\<rbrakk>  \<Longrightarrow> ptable_lift_m (heap s) (Addr 0xA)  User (Addr va) =  Some ((Addr 0xF000) r+ vaddr_offset ArmSmallPage va)"
  apply (clarsimp simp: user_vas_def ptable_lift_m_def lookup_pde'_def get_pde'_def vaddr_pd_index_def pd_idx_offset_def lookup_pde_perm_def filter_pde_def)
  apply (clarsimp simp: decode_heap_pde'_def state_initial'_def)
  apply (clarsimp simp: decode_pde_def decode_pde_pt_def  lookup_pte'_def get_pte'_def pt_base_mask_def decode_heap_pte'_def vaddr_pt_index_def mask_def)
  apply (clarsimp simp: decode_pte_def decode_pte_small_def user_perms_def perm_bits_pte_small_def addr_base_def mask_def)
done



lemma  user_ptrace_physical:
  "\<lbrakk>state_initial' s;  va \<in> user_vas\<rbrakk>
              \<Longrightarrow> ptable_trace' (heap s) (Addr 0xA) (Addr va) = {Addr 0x12, Addr 0xC00}"
  apply (clarsimp simp: vaddr_offset_def mask_def user_vas_def pd_idx_offset_def vaddr_pd_index_def ptable_trace'_def Let_def decode_heap_pde'_def state_initial'_def decode_pde_def decode_pde_pt_def
                           pt_base_mask_def vaddr_pt_index_def)
  by blast


lemma  user_vas_ptace_physical:
  "\<lbrakk>state_initial' s; vp1 \<in> user_vas;  vp2 \<in> user_vas\<rbrakk>
         \<Longrightarrow> Addr (0xF000 + vaddr_offset ArmSmallPage vp1) \<notin> ptable_trace' (heap s) (Addr 0xA) (Addr vp2)"
  apply (frule_tac va = vp2 in  user_ptrace_physical; clarsimp simp: vaddr_offset_def mask_def)
  by word_bitwise



(*  modify it here *)
(* there should be no need for the flushing, if  we are swtiching to the asid fro the log 
          a good idea is to ogranize everything before that  and then start wrting the code here, otherwise I will be more lost make a new folder *)

lemma  context_switch:
  "\<Turnstile> \<lbrace> \<lambda>s. state_initial' s \<rbrace>  
                UpdateTTBR0 (Const 0xA) ;; UpdateASID (0x1) ;;  Flush (flushASID 0x1) ;;  SetMode User 
           \<lbrace>\<lambda>s. safe_set user_vas s \<rbrace>"
  apply_trace vcg
  apply (rule conjI)
   apply (clarsimp simp: state_initial'_def)
  apply (clarsimp simp: safe_set_def con_set_def safe_memory_def)
  apply (frule_tac va = va in user_ptable_lift_defined_constant , clarsimp, clarsimp)
  apply (clarsimp simp: ptrace_set_def user_vas_ptace_physical)
done



lemma  context_switch_write:
  "\<Turnstile> \<lbrace> \<lambda>s. state_initial' s \<and> aval lval1 (s\<lparr>root := Addr 0xA, asid := 1\<rparr>) = Some vp1 \<and> 
                  aval rval1 (s\<lparr>root := Addr 0xA, asid := 1\<rparr>) = Some v1 \<and> vp1 \<in> user_vas \<and> 
                   aval lval2 (s\<lparr>root := Addr 0xA, asid := 1,heap := heap s(Addr 0xF000 r+ vaddr_offset ArmSmallPage vp1 \<mapsto> v1)\<rparr>) = Some vp2 \<and> 
            aval rval2 (s\<lparr>root := Addr 0xA, asid := 1,heap := heap s(Addr 0xF000 r+ vaddr_offset ArmSmallPage vp1 \<mapsto> v1)\<rparr>) = Some v2 \<and> vp2 \<in> user_vas \<rbrace>  
                UpdateTTBR0 (Const 0xA) ;; UpdateASID (0x1) ;;  Flush (flushASID 0x1) ;;  SetMode User ;;
                  lval1 ::= rval1 ;; lval2 ::= rval2 
           \<lbrace>\<lambda>s. safe_set user_vas s  \<and> heap s (Addr 0xF000 r+ vaddr_offset ArmSmallPage vp2) = Some v2\<rbrace>"
  apply_trace (vcg vcg: weak_pre_write')
  apply (rule conjI)
   apply (clarsimp simp: state_initial'_def)
  apply (rule conjI)
   apply (clarsimp simp: safe_set_def con_set_def safe_memory_def)
   apply (frule_tac va = va in user_ptable_lift_defined_constant ; clarsimp)
   apply (clarsimp simp: ptrace_set_def user_vas_ptace_physical)
  apply (frule_tac va = vp1 in user_ptable_lift_defined_constant ; clarsimp)
  apply (frule_tac va = vp2 in user_ptable_lift_defined_constant ; clarsimp)
  by (frule_tac p = "Addr (0xF000 + vaddr_offset ArmSmallPage vp1)" and vp = "Addr vp2"  and v = v1 in  ptable_lift_preserved_m' ; clarsimp simp: user_vas_ptace_physical)





lemma
  "\<Turnstile> \<lbrace> \<lambda>s. state_initial' s  \<rbrace>  
                UpdateTTBR0 (Const 0xA) ;; UpdateASID (0x1) ;;  Flush (flushASID 0x1) ;;  SetMode User 
           \<lbrace>\<lambda>s. con_set UNIV s \<and> root s = Addr 0xA \<and>
                     heap s (Addr 0xA) = Some 0x00000002 \<and> heap s (Addr 0xE) = Some 0x00100002 \<and> asid s = 0x1 \<and> mode s = User\<rbrace>"
  apply vcg
  by (clarsimp simp: state_initial'_def con_set_def)


lemma
  "\<Turnstile> \<lbrace> \<lambda>s. state_initial' s  \<rbrace>  
                UpdateTTBR0 (Const 0xA) ;; UpdateASID (0x1) ;;  Flush (flushASID 0x1) ;;  SetMode User 
           \<lbrace>\<lambda>s. (asid s, 0xA) \<notin> incon_set s \<and> root s = Addr 0xA \<and>
                     heap s (Addr 0xA) = Some 0x00000002 \<and> heap s (Addr 0xE) = Some 0x00100002 \<and> asid s = 0x1 \<and> mode s = User\<rbrace>"
  apply vcg
  by (clarsimp simp: state_initial'_def)



find_theorems "safe_set" "kernel_memory"

(* MAKE THINGS GENERIC *)

(*  set of all the virtual addresses that are mapped by kernel entries *)
(* hoe to differentiate between kernel and user translation entries, lets assume that all of 
  the kernel addresses are mapped by the sections *)

definition
  kernel_mapped_vas :: "p_state \<Rightarrow> 32 word set"
where
  "kernel_mapped_vas s \<equiv> {va. \<exists>bpa perms. get_pde' (heap s) (root s) (Addr va) =  Some (SectionPDE bpa perms) }"

(*Later we will assume in our memory settings that none of the sections are mapped by the user *)

definition
  kernel_entries_vas :: "p_state \<Rightarrow> 32 word set"
where
  "kernel_entries_vas s \<equiv> {va. va \<in> kernel_mapped_vas s \<and> 
              the (ptable_lift' (heap s) (root s) (Addr va)) \<in> \<Union>(ptable_trace' (heap s) (root s) ` Addr `(kernel_mapped_vas s)) }"

(* IMP they should also be contigious for the address space, have to add in the assumption too? *)


definition 
  kernel_v_memory :: "p_state \<Rightarrow> 32 word set"
where                              
  "kernel_v_memory s = kernel_mapped_vas s - kernel_entries_vas s"



(* assume that kernel is at the high address space, lets suppose that the partition between kernel and user mapped addresses are 
        F0000000, then  we should have the constantly mapped virtually addresses , upper 12 bits are sued for the section *)

fun
  pde_ba :: "pde option \<Rightarrow>  32 word option"
where
  "pde_ba None = None"
|
  "pde_ba (Some InvalidPDE) = None"
|
  "pde_ba (Some ReservedPDE) = None"
|
  "pde_ba (Some (PageTablePDE paddr)) = None"
|
  "pde_ba (Some (SectionPDE paddr arm_perm_bits)) = Some (addr_val paddr)"



definition
  bpa_va  :: "p_state \<Rightarrow> 32 word \<Rightarrow> 32 word option"
where
  "bpa_va s va \<equiv> pde_ba (get_pde' (heap s) (root s) (Addr va))"
  

definition 
  "vir_kern_mem \<equiv> {0xF0000000 .. (0xFFFFFFFF)::32 word}"

definition 
  "vir_usr_mem \<equiv> {Addr 0x00000000 .. Addr (0xEFFFFFFF)}"


definition
  memory_enforcemnet :: "p_state \<Rightarrow> bool"
where
  "memory_enforcemnet s \<equiv>  \<forall>bpa perm. Some (SectionPDE bpa perm) \<notin> (get_pde' (heap s) (root s) ` vir_usr_mem) \<and> 
                            kernel_mapped_vas s = vir_kern_mem \<and> 
                            (\<forall>va\<in>kernel_mapped_vas s. (ucast ((word_extract 27 20 va)::8 word)::32 word) << 20 = the (bpa_va s va))"
 



definition
  va_to_pa_offset' :: "vaddr \<Rightarrow> 32 word \<Rightarrow> vaddr set \<rightharpoonup> paddr"
where
  "va_to_pa_offset' va offset S \<equiv> if va \<in> S then Some (Addr (addr_val(va r- offset))) else None"


lemma kenrel_memory_defined:
  "va \<in> kernel_v_memory s  \<Longrightarrow> \<exists>p. ptable_lift' (heap s) (root s) (Addr va) = Some p "
   by (clarsimp simp: kernel_v_memory_def kernel_mapped_vas_def ptable_lift'_def lookup_pde'_def)

lemma global_window_defined:
  "va \<in> kernel_mapped_vas s  \<Longrightarrow> \<exists>p. ptable_lift' (heap s) (root s) (Addr va) = Some p "
   by (clarsimp simp:  kernel_mapped_vas_def ptable_lift'_def lookup_pde'_def)

lemma global_window_defined':
  "va \<in> kernel_mapped_vas s  \<Longrightarrow> \<exists>bpa perms. get_pde' (heap s) (root s) (Addr va) = Some (SectionPDE bpa perms)"
   by (clarsimp simp:  kernel_mapped_vas_def ptable_lift'_def lookup_pde'_def)



lemma state_intitial_ptable_lift_offset'':
  "\<lbrakk>memory_enforcemnet s \<rbrakk> \<Longrightarrow>
        \<forall>va\<in>kernel_mapped_vas s.  ptable_lift_m (heap s) (root s) Kernel (Addr va) = va_to_pa_offset' (Addr va) (0xF0000000) (Addr `kernel_mapped_vas s)"
  apply (clarsimp simp: va_to_pa_offset'_def)
  apply (clarsimp simp: ptable_lift'_def lookup_pde'_def)
  apply (frule global_window_defined', clarsimp)
  apply (subgoal_tac "va : vir_kern_mem \<and> bpa = Addr ((ucast (ucast ((va >> 20) && mask 8)::8 word)) << 20)")
   apply (clarsimp simp: vir_kern_mem_def vaddr_offset_def mask_def)
   apply (word_bitwise , force)
  by (clarsimp simp: memory_enforcemnet_def vir_usr_mem_def vir_kern_mem_def va_to_pa_offset'_def kernel_mapped_vas_def bpa_va_def)


lemma state_intitial_ptable_lift_offset2'':
  "\<lbrakk>memory_enforcemnet s  \<rbrakk> \<Longrightarrow>
        \<forall>va\<in>kernel_v_memory s.  ptable_lift_m (heap s) (root s) Kernel (Addr va) = va_to_pa_offset' (Addr va) (0xF0000000) (Addr `kernel_v_memory s)"
  using state_intitial_ptable_lift_offset'' by (clarsimp simp:  kernel_v_memory_def va_to_pa_offset'_def)


lemma state_intitial_ptable_lift_offset2':
  "\<lbrakk>memory_enforcemnet s  \<rbrakk> \<Longrightarrow>
        \<forall>va\<in>kernel_v_memory s.  ptable_lift_m (heap s) (root s) Kernel (Addr va) = va_to_pa_offset' (Addr va) (0xF0000000) (Addr `kernel_mapped_vas s)"
  using state_intitial_ptable_lift_offset'' by (clarsimp simp:  kernel_v_memory_def)
 
lemma abc' [simp]:
  "\<lbrakk>memory_enforcemnet s \<rbrakk>\<Longrightarrow>
      \<forall>vp \<in> kernel_v_memory s. ptable_lift_m (heap s) (root s) Kernel (Addr vp) = Some (Addr vp r- 0xF0000000)"
  apply(frule state_intitial_ptable_lift_offset2'') by (clarsimp simp: va_to_pa_offset'_def)

lemma abc [simp]:
  "\<lbrakk>memory_enforcemnet s ; vp \<in> kernel_v_memory s \<rbrakk>\<Longrightarrow>
     ptable_lift_m (heap s) (root s) Kernel (Addr vp) = Some (Addr vp r- 0xF0000000)"
  apply(frule state_intitial_ptable_lift_offset2'') by (clarsimp simp: va_to_pa_offset'_def)


(* what are the physical address of the corresponding virtual address *)
(* vp r- 0xF0000000) *)


lemma
  " vp \<in> kernel_v_memory s  \<Longrightarrow>
     the (ptable_lift_m (heap s) (root s) Kernel (Addr vp)) \<notin>  ptable_trace'  (heap s)  (root s)  (Addr vp)"
  apply (clarsimp simp: kernel_v_memory_def kernel_mapped_vas_def kernel_entries_vas_def)
  by force


lemma kernel_memory_vspace' [simp]:
  "vp : kernel_v_memory s \<Longrightarrow> vp : kernel_mapped_vas s"
  by (simp add: kernel_v_memory_def)


lemma va_to_pa_offset_0' [simp]:
  "\<lbrakk>memory_enforcemnet s ; vp \<in> kernel_v_memory s \<rbrakk> \<Longrightarrow> va_to_pa_offset' (Addr vp) (0xF0000000)  (Addr ` kernel_mapped_vas s) = Some (Addr vp r- 0xF0000000)"
   by (clarsimp simp: va_to_pa_offset'_def)



(* not being usede for the time being *)
lemma state_intial_element_ptrace':
  "\<lbrakk>memory_enforcemnet s;  va \<in> kernel_v_memory s  \<rbrakk> \<Longrightarrow>  Addr va \<notin> ptrace_set kernel_memory s"
sorry
 


lemma safe_set_preserved_kernel':
  "\<Turnstile> \<lbrace> \<lambda>s. memory_enforcemnet s \<and> mode s = Kernel \<and> aval lval s = Some vp \<and> aval rval s = Some v \<and> vp \<in> kernel_v_memory s \<and>  SM = kernel_v_memory s \<and> safe_set SM s\<rbrace> 
                    lval ::= rval  \<lbrace>\<lambda>s. safe_set SM s\<rbrace>"
  apply (rule weak_pre)
   by (rule safe_set_preserved [of _ vp _ v] , clarsimp)
 

thm kernel_memory_vspace'

lemma va_kernel_mem_trace:
  "\<lbrakk>vp \<in> kernel_v_memory s ;  vp' \<in> kernel_v_memory s\<rbrakk>\<Longrightarrow>
     the (ptable_lift_m (heap s) (root s) Kernel (Addr vp')) \<notin>  ptable_trace'  (heap s)  (root s)  (Addr vp)"
  apply (clarsimp simp: kernel_v_memory_def kernel_mapped_vas_def kernel_entries_vas_def)
  by force


lemma ptable_lift_write':
  "\<lbrakk>memory_enforcemnet s ; memory_enforcemnet s; vp' \<in> kernel_v_memory s; vp \<in> kernel_v_memory s \<rbrakk> \<Longrightarrow>
     ptable_lift_m (heap s(Addr vp' r- 0xF0000000 \<mapsto> x)) (root s) Kernel (Addr vp) =  ptable_lift_m  (heap s)  (root s) Kernel  (Addr vp)"
  apply (clarsimp simp: kernel_v_memory_def)
  apply (clarsimp simp: kernel_mapped_vas_def)
  apply (clarsimp simp: kernel_entries_vas_def)
  apply (subgoal_tac "Addr (vp' - 0xF0000000) \<notin> ptable_trace' (heap s) (root s) (Addr vp)")
   apply (subgoal_tac "ptable_lift' (heap s) (root s) (Addr vp) = Some (Addr vp r- 0xF0000000) ")
    apply (frule_tac pa = "(Addr vp r- 0xF0000000)" and v = x in ptable_lift_preserved' , clarsimp, clarsimp)
   apply (frule_tac vp = vp in abc , clarsimp simp: kernel_v_memory_def  kernel_mapped_vas_def kernel_entries_vas_def)
   apply (clarsimp simp: memory_enforcemnet_def ptable_lift'_def lookup_pde'_def vaddr_offset_def kernel_mapped_vas_def)
  apply (subgoal_tac "vp' \<in> kernel_v_memory s")
   apply (subgoal_tac "vp \<in> kernel_v_memory s")
    apply (insert va_kernel_mem_trace [of vp s vp'])
    apply clarsimp
    apply (insert abc [of s vp'])
    apply clarsimp
   apply (clarsimp simp: kernel_v_memory_def kernel_mapped_vas_def kernel_entries_vas_def)+
done



lemma mem_en_safe:
  "\<lbrakk>memory_enforcemnet s; mode s = Kernel \<rbrakk> \<Longrightarrow>  safe_memory (kernel_v_memory s) s"
  apply (clarsimp simp: safe_memory_def memory_enforcemnet_def)
  apply (frule kenrel_memory_defined)
  apply (clarsimp simp: ptrace_set_def)
  apply (frule_tac vp' = va and vp = a in va_kernel_mem_trace; clarsimp)
done
  

lemma mem_en_safe':
  "\<lbrakk>memory_enforcemnet s; mode s = Kernel \<rbrakk> \<Longrightarrow>  safe_set (kernel_v_memory s) (s\<lparr>incon_set := {}\<rparr>)"
  apply (clarsimp simp: safe_set_def con_set_def safe_memory_def)
  apply (clarsimp simp: memory_enforcemnet_def)
  apply (frule kenrel_memory_defined)
  apply (clarsimp simp: ptrace_set_def)
  apply (frule_tac vp' = va and vp = a in va_kernel_mem_trace ; clarsimp)
done

lemma flush_assign_safe':
  "\<Turnstile> \<lbrace> \<lambda>s. memory_enforcemnet s \<and> mode s = Kernel \<and> aval lval s = Some vp \<and> aval rval s = Some v \<and> vp \<in> kernel_v_memory s \<and> SM = kernel_v_memory s \<rbrace>  
                Flush flushTLB ;; lval ::= rval  
                     \<lbrace>\<lambda>s. safe_set SM s\<rbrace>"
  apply vcg
    apply (rule_tac v = v and vp = vp in safe_set_preserved)
   apply (rule flush_sound)
  apply (clarsimp simp: safe_set_def con_set_def)
  apply (clarsimp simp: mem_en_safe)
done




lemma flush_assignments_safe_kernel':
  "\<Turnstile> \<lbrace> \<lambda>s. memory_enforcemnet s \<and> mode s = Kernel \<and> aval lval1 s = Some vp1 \<and> aval rval1 s = Some v1 \<and> vp1 \<in> kernel_v_memory s \<and> 
            aval lval2 (s\<lparr>heap := heap s(Addr vp1 r- 0xF0000000 \<mapsto> v1)\<rparr>) = Some vp2 \<and> 
            aval rval2 (s\<lparr>heap := heap s(Addr vp1 r- 0xF0000000 \<mapsto> v1)\<rparr>) = Some v2 \<and> vp2 \<in> kernel_v_memory s \<and> SM = kernel_v_memory s \<rbrace>  
                 Flush flushTLB ;; lval1 ::= rval1 ;; lval2 ::= rval2 
      \<lbrace>\<lambda>s. safe_set SM s \<and> heap s (Addr vp2 r- 0xF0000000) = Some v2\<rbrace>"
  apply_trace (vcg vcg: weak_pre_write')
  apply (rule conjI)
   apply (clarsimp simp: mem_en_safe')
  apply (frule_tac vp = vp1 in abc ; clarsimp)
  apply (frule_tac vp = vp2 in abc ; clarsimp)
  apply (subgoal_tac "Addr (vp2 - 0xF0000000) = the (ptable_lift' (heap s(the (ptable_lift' (heap s) (root s) (Addr vp1)) \<mapsto> v1)) (root s) (Addr vp2))" ; clarsimp)
  apply (frule_tac vp' = vp1 and vp = vp2 and x = v1 in ptable_lift_write' ; clarsimp)
done






(* not good reasoning *)


lemma
  "\<Turnstile> \<lbrace> \<lambda>s. state_initial s  \<rbrace>  
        Flush (flushva (Addr 0xA)) ;; Flush (flushva (Addr 0xE)) ;; Const 0xA ::= Const 0x00000002  ;; Const 0xE ::= Const 0x00100002 ;; UpdateTTBR0 (Const 0xA) ;;
                 UpdateASID (0x1) ;;  Flush (flushASID 0x1) ;;  SetMode User 
           \<lbrace>\<lambda>s. (asid s, 0xA) \<notin> incon_set s \<and> root s = Addr 0xA \<and> heap s (Addr 0xA) = Some 0x00000002 \<and> 
heap s (Addr 0xE) = Some 0x00100002 \<and> asid s = 0x1 \<and> mode s = User \<and> 
                           ptable_lift_m (heap s) (root s) (mode s) (Addr 0xA) = None\<rbrace>"
  apply vcg
  apply (subgoal_tac "0xA\<in>kernel_memory \<and> 0xE\<in>kernel_memory")
   prefer 2
   apply (clarsimp simp: kernel_memory_def vspace_section_def pd_idx_offset_def vaddr_pd_index_def mask_def vadd_entries_def)
  apply (rule_tac x = "Addr 0xA" in exI , clarsimp simp: state_intitial_ptable_lift_offset2)
  apply (rule conjI)
   apply (subgoal_tac "lookup_pde' (heap s) (root s) (Addr 0xE) = lookup_pde' (heap s(Addr 0xA \<mapsto> 2)) (root s) (Addr 0xE)")
    apply (clarsimp simp: pde_comp_def)
   apply (clarsimp simp: state_initial_def lookup_pde'_def get_pde'_def decode_heap_pde'_def Let_def vaddr_pd_index_def decode_pde_def decode_pde_section_def)
  apply (rule_tac x = "Addr 0xE" in exI , clarsimp)
  apply (frule ptable_lift_write [of _ "0xA" "0xE" 2] , clarsimp , clarsimp)
  apply (clarsimp simp: state_intitial_ptable_lift_offset2)
  apply (subgoal_tac "Addr 0xA \<in> ptable_mapped' (heap s(Addr 0xA \<mapsto> 2, Addr 0xE \<mapsto> 0x100002)) (Addr 0xA)")
   apply (clarsimp simp: ptable_lift_new_def)
  apply (clarsimp simp: ptable_mapped'_def)
  apply (rule_tac x = "Addr 0xA" in exI)
  apply (rule conjI)
   apply (clarsimp simp: ptable_lift'_def lookup_pde'_def get_pde'_def decode_heap_pde'_def Let_def decode_pde_def
                          decode_pde_section_def vaddr_offset_def vaddr_pd_index_def addr_base_def mask_def)
  apply (rule_tac x = "Addr 0xA" in exI)
  apply (clarsimp simp: ptable_trace'_def Let_def decode_heap_pde'_def vaddr_pd_index_def decode_pde_def decode_pde_section_def)
done



lemma [simp]:
  " safe_memory S (s\<lparr>heap := h, root := r, asid := a,
    incon_set := is , mode := m\<rparr>) = 
   safe_memory S (s\<lparr>heap := h, root := r, asid := a, mode := m\<rparr>)"
  by (clarsimp simp: safe_memory_def ptrace_set_def) 



lemma
  "\<Turnstile> \<lbrace> \<lambda>s.  safe_set (kernel_memory) s \<and> state_initial s \<and> vp1 \<in> kernel_memory \<and> vp2 \<in> kernel_memory \<and> vp1 \<noteq> vp2\<rbrace>  
        (* Flush (flushva (Addr vp1)) ;; Flush (flushva (Addr vp2)) ;;  *) Const vp1 ::= Const 0x00000002  ;; Const vp2 ::= Const 0x00100002 ;; UpdateTTBR0 (Const vp1) ;;
                 UpdateASID (0x1) ;;  Flush (flushASID 0x1) ;;  SetMode User 
           \<lbrace>\<lambda>s. (asid s, vp1) \<notin> incon_set s \<and> root s = Addr vp1 \<and> heap s (Addr vp1) = Some 0x00000002 \<and>
 heap s (Addr vp2) = Some 0x00100002 \<and> asid s = 0x1 \<and> mode s = User \<and> 
              ptable_lift_m (heap s) (root s) (mode s) (Addr vp1) = None \<and>  safe_set (kernel_memory - {vp1, vp2}) s\<rbrace>"
 apply vcg
  apply (rule_tac x = "Addr vp1" in exI , clarsimp simp: state_intitial_ptable_lift_offset2)
  apply (rule conjI)
   apply (subgoal_tac "lookup_pde' (heap s) (root s) (Addr vp2) = lookup_pde' (heap s(Addr vp1 \<mapsto> 2)) (root s) (Addr vp2)")
    apply (clarsimp simp: pde_comp_def)
   prefer 2
  apply (rule_tac x = "Addr vp2" in exI , clarsimp simp: state_intitial_ptable_lift_offset2)
   apply (rule conjI)
   prefer 2
     apply (clarsimp simp: safe_set_def)
    apply (rule)
   apply (clarsimp simp: safe_memory_def ptrace_set_def ptable_lift_new_def Let_def)
     

oops


find_theorems "safe_set" "state_initial"



lemma
  "\<Turnstile> \<lbrace> \<lambda>s. state_initial s  \<rbrace>  
                Flush (flushva (Addr 0xA)) ;; Flush (flushva (Addr 0xE)) ;; UpdateTTBR0 (Const 0xA) ;; 
                    Const 0xA ::= Const 0x00000002 ;;  Const 0xE ::= Const 0x00100002 ;; UpdateASID (0x1) ;; 
                  Flush (flushASID 0x1) ;;  SetMode User  ;;  Const 0xA ::= Const 0x00000000 
                      \<lbrace>\<lambda>s.  ptable_lift_m (heap s) (root s) (mode s) (Addr 0xA) = None \<rbrace>"
  apply vcg
  apply (clarsimp simp: state_initial_def)  
  apply (rule_tac x = "Addr 0xA" in exI)

   find_theorems name: "2" "state_initial"

(* how to have the concept of memory access privilege etc, should i add things in the semantics? or have theorems related to that *)

oops



















definition
  defined_trans_safe :: "32 word set \<Rightarrow> p_state \<Rightarrow> bool"
where
  "defined_trans_safe S' s \<equiv>  \<forall>va \<in> S'. (asid s, va) \<notin> incon_set s \<and>
             (\<exists>p. ptable_lift' (heap s) (root s) (Addr va) = Some p)  "


definition
  unmapped_vas :: "p_state \<Rightarrow> 32 word set"
where
  "unmapped_vas s \<equiv> {va. ptable_trace' (heap s) (root s) (Addr va) = {} }" 






(*important *)

(* user execution *)

lemma  user_incon_set_preserved:
  "\<Turnstile> \<lbrace> \<lambda>s. aval lval s = Some vp \<and> aval rval s = Some v \<and> vp \<in> DTS \<and> defined_trans_safe DTS s \<and>
            vp \<notin> ptable_mapped s \<and> unmapped_vas s = unmapped_vas (s \<lparr>heap := heap s (the (ptable_lift' (heap s) (root s) (Addr vp)) \<mapsto> v)\<rparr>) \<and> incon_set s = is \<rbrace>  
       lval ::= rval  \<lbrace>\<lambda>s. incon_set s = is \<rbrace>"
  apply vcg
  apply (clarsimp simp: defined_trans_safe_def)
  apply (drule_tac x = vp in bspec)
   apply clarsimp
  apply clarsimp
  apply (subgoal_tac "pde_comp (asid s) (heap s) (heap s(p \<mapsto> v)) (root s) = {}")
   apply clarsimp
  apply (clarsimp simp: pde_comp_def lookup_pde'_def unmapped_vas_def)
  apply (subgoal_tac "get_pde' (heap s) (root s) x = get_pde' (heap s(p \<mapsto> v)) (root s) x")
   apply (clarsimp split: option.splits)
   apply (case_tac x2 ; clarsimp)
   apply (clarsimp simp: lookup_pte'_def)
   apply (subgoal_tac "get_pte' (heap s) x3 x = get_pte' (heap s(p \<mapsto> v)) x3 x ")
    apply clarsimp
   apply (clarsimp simp: ptable_mapped_def)
   apply (drule_tac x = x  in spec)
   apply (clarsimp simp: ptable_trace'_def Let_def get_pde'_def split: option.splits)
   apply (clarsimp simp: get_pte'_def decode_heap_pte'_def)
  apply (clarsimp simp: ptable_mapped_def)
  apply (drule_tac x = x  in spec)
  apply (case_tac "ptable_trace' (heap s) (root s) x = {}")
   prefer 2
   apply (clarsimp simp: get_pde'_def ptable_trace'_def Let_def split:option.splits)
   apply (case_tac x2 ; clarsimp simp: decode_heap_pde'_def)
  apply (subgoal_tac "\<exists>nv. nv = addr_val x")
   prefer 2
   apply force
  apply (erule exE)
  apply (subgoal_tac "ptable_trace' (heap s) (root s) (Addr nv) = {}")
   prefer 2
   apply clarsimp
  apply (subgoal_tac "ptable_trace' (heap s(p \<mapsto> v)) (root s) (Addr nv) = {}")
   prefer 2
   apply (thin_tac "ptable_trace' (heap s) (root s) x = {}")
   apply (thin_tac "nv = addr_val x")
   apply force
  apply (subgoal_tac "ptable_trace' (heap s(p \<mapsto> v)) (root s) x = {}")
   prefer 2
   apply force
  apply (thin_tac "ptable_trace' (heap s(p \<mapsto> v)) (root s) (Addr nv) = {}")
  apply (thin_tac "ptable_trace' (heap s) (root s) (Addr nv) = {}")
  apply (thin_tac "nv = addr_val x")
  apply (clarsimp simp: ptable_trace'_def get_pde'_def Let_def)
  by (clarsimp split: option.splits ; (case_tac x2 ; clarsimp))


(* start new code here *)

(* Kernel Section-Mappings *)

definition 
  kernel_pdes :: "p_state \<Rightarrow> pde set"
where
  "kernel_pdes s  \<equiv> {decode_pde_section (the(heap s (root s r+ 1))),
                      decode_pde_section (the(heap s (root s r+ 2))) }"


(* Safe Set *)


definition
  vspace_section :: "p_state \<Rightarrow> 32 word set"
where
  "vspace_section s \<equiv> {va. (\<exists>p. ptable_lift' (heap s) (root s) (Addr va) = Some p) \<and> 
                         ( (pd_idx_offset va = 0 \<and>  get_pde' (heap s) (root s) (Addr va) = Some (decode_pde_section (the(heap s (root s))))) \<or>
                          (pd_idx_offset va = 1 \<and>  get_pde' (heap s) (root s) (Addr va) = Some (decode_pde_section (the(heap s (root s r+ 1))))) )  }"

lemma [simp]:
  "root s r+ 0 = root s"
   by (clarsimp simp: addr_add_def)


lemma ptable_trace_va_section:
  "\<forall>va\<in>vspace_section s. ptable_trace' (heap s) (root s) (Addr va) = {root s} \<or>
          ptable_trace' (heap s) (root s) (Addr va) = {root s r+ 1}"
  apply (clarsimp simp: vspace_section_def  del: disjCI)
  apply (erule_tac disjE)
   apply (rule disjI1)
   by (clarsimp simp: ptable_trace'_def Let_def pd_idx_offset_def get_pde'_def decode_pde_section_def)+



definition
  vadd_entries :: "p_state \<Rightarrow> 32 word set"
where
  "vadd_entries s \<equiv> {va\<in>vspace_section s.  (ptable_lift' (heap s) (root s) (Addr va) = Some (root s) \<or>
                              ptable_lift' (heap s) (root s) (Addr va) = Some (root s r+ 1))}"

lemma ptable_trace_va_entries:
  "\<forall>va\<in>vadd_entries s. ptable_trace' (heap s) (root s) (Addr va) = {root s} \<or>
          ptable_trace' (heap s) (root s) (Addr va) = {root s r+ 1}"
  apply (clarsimp simp: vadd_entries_def vspace_section_def  del: disjCI)
  apply (erule_tac disjE)
   apply (rule disjI1)
   by (clarsimp simp: ptable_trace'_def Let_def pd_idx_offset_def get_pde'_def decode_pde_section_def)+



definition 
  kernel_memory :: "p_state \<Rightarrow> 32 word set"
where
  "kernel_memory s = vspace_section s - vadd_entries s"


lemma ok:
  "vspace_section (s\<lparr>heap := heap s(p \<mapsto> v), incon_set := incon_set s \<union> pde_comp (asid s) (heap s) (heap s(p \<mapsto> v)) (root s)\<rparr>) =
     vspace_section (s\<lparr>heap := heap s(p \<mapsto> v)\<rparr>)"
  by (clarsimp simp: vspace_section_def)

lemma ok1:
  "vadd_entries (s\<lparr>heap := heap s(p \<mapsto> v), incon_set := incon_set s \<union> pde_comp (asid s) (heap s) (heap s(p \<mapsto> v)) (root s)\<rparr>) =
     vadd_entries (s\<lparr>heap := heap s(p \<mapsto> v)\<rparr>)"
  by (clarsimp simp: vadd_entries_def vspace_section_def)


lemma get_pde_trace_some:
  "get_pde' h r vp = Some pa \<Longrightarrow>  ptable_trace' h r vp \<noteq> {}"
  apply (clarsimp simp:  get_pde'_def ptable_trace'_def Let_def split:option.splits)
  by (case_tac pa ; clarsimp)


lemma  get_pde_preserved':
  " \<lbrakk>p \<notin> ptable_trace' (heap s) (root s) (Addr va); get_pde' (heap s) (root s) (Addr va) = Some (decode_pde_section w)\<rbrakk> 
            \<Longrightarrow>  get_pde' (heap s(p \<mapsto> v)) (root s) (Addr va) = Some (decode_pde_section w)"
  apply (frule get_pde_trace_some , clarsimp simp:get_pde'_def ptable_trace'_def Let_def decode_pde_section_def split: option.splits)
  by (clarsimp simp: decode_heap_pde'_def lookup_pte'_def split: option.splits)
  
lemma  get_pde_preserved'':
  " \<lbrakk>p \<notin> ptable_trace' (heap s(p \<mapsto> v)) (root s) (Addr va); get_pde' (heap s(p \<mapsto> v)) (root s) (Addr va) = Some (decode_pde_section w)\<rbrakk> 
            \<Longrightarrow>  get_pde' (heap s) (root s) (Addr va) = Some (decode_pde_section w)"
  apply (frule get_pde_trace_some , clarsimp simp:get_pde'_def ptable_trace'_def Let_def decode_pde_section_def split: option.splits)
  by (clarsimp simp: decode_heap_pde'_def lookup_pte'_def split: option.splits)

lemma vspace_get_pde:
  "\<lbrakk>p \<noteq> root s ; p \<noteq> root s r+ 1 \<rbrakk> \<Longrightarrow>  
       \<forall>va\<in>vspace_section s. get_pde' (heap s) (root s) (Addr va) = get_pde' (heap s(p \<mapsto> v)) (root s) (Addr va)"
  apply (clarsimp simp: vspace_section_def)
  apply (erule disjE)
   apply (erule conjE)
   apply (subgoal_tac "p \<notin> ptable_trace' (heap s) (root s) (Addr va)")
    apply (frule_tac w = "(the (heap s (root s)))" and v = v in get_pde_preserved' ; clarsimp)
   apply (clarsimp simp: ptable_trace'_def Let_def pd_idx_offset_def get_pde'_def decode_pde_section_def)
  apply (subgoal_tac "p \<notin> ptable_trace' (heap s) (root s) (Addr va)")
   apply (frule_tac w = "(the (heap s (root s r+ 1)))" and v = v in get_pde_preserved' ; clarsimp)
  by (clarsimp simp: ptable_trace'_def Let_def pd_idx_offset_def get_pde'_def decode_pde_section_def)


find_theorems "ptable_trace'" "ptable_lift'"

lemma  ptable_lift_preserved_m:
  " \<lbrakk> p \<notin> ptable_trace' (heap s(p \<mapsto> v)) (root s) (Addr va);  ptable_lift' (heap s(p \<mapsto> v)) (root s) (Addr va) = Some pa\<rbrakk> 
            \<Longrightarrow>  ptable_lift' (heap s) (root s) (Addr va) = Some pa"
 apply (frule ptlift_trace_some , clarsimp simp:ptable_lift'_def lookup_pde'_def get_pde'_def ptable_trace'_def Let_def split: option.splits)
  apply (case_tac x2; clarsimp simp: decode_heap_pde'_def lookup_pte'_def split: option.splits)
  apply (case_tac x2a ; clarsimp)
  apply (rule conjI)
   apply (rule_tac x = "(SmallPagePTE a b)" in exI, clarsimp simp: get_pte'_def decode_heap_pte'_def , clarsimp)
  by (case_tac x2 ; clarsimp simp:get_pte'_def decode_heap_pte'_def)



lemma  vspace_preserved:
  "\<lbrakk> root s \<noteq> p  ; root s r+ 1 \<noteq> p \<rbrakk>  \<Longrightarrow>
                        vspace_section (s\<lparr>heap := heap s(p \<mapsto> v)\<rparr>) = vspace_section s"
  apply (clarsimp simp: vspace_section_def)
  apply (clarsimp simp: Collect_eq)
  apply (rule iffI)
   apply clarsimp
   apply (rule conjI)
    apply (rule_tac x = pa in exI)
    apply (erule disjE)
     apply clarsimp
     apply (subgoal_tac "p \<notin> ptable_trace' (heap s(p \<mapsto> v)) (root s) (Addr va)")
      prefer 2
      apply (clarsimp simp: ptable_trace'_def Let_def pd_idx_offset_def get_pde'_def decode_pde_section_def)
     apply (clarsimp simp : ptable_lift_preserved_m)
    apply (subgoal_tac "p \<notin> ptable_trace' (heap s(p \<mapsto> v)) (root s) (Addr va)")
     prefer 2
     apply (clarsimp simp: ptable_trace'_def Let_def pd_idx_offset_def get_pde'_def decode_pde_section_def)
    apply (clarsimp simp : ptable_lift_preserved_m)
   apply (erule disjE)
    apply (rule disjI1)
    apply clarsimp
    apply (subgoal_tac "p \<notin> ptable_trace' (heap s(p \<mapsto> v)) (root s) (Addr va)")
     prefer 2
     apply (clarsimp simp: ptable_trace'_def Let_def pd_idx_offset_def get_pde'_def decode_pde_section_def)
    apply (frule_tac w = "(the (heap s (root s )))" and v = v in get_pde_preserved'' ; clarsimp)
   apply (subgoal_tac "p \<notin> ptable_trace' (heap s(p \<mapsto> v)) (root s) (Addr va)")
    prefer 2
    apply (clarsimp simp: ptable_trace'_def Let_def pd_idx_offset_def get_pde'_def decode_pde_section_def)
   apply (frule_tac w = "(the (heap s (root s r+ 1)))" and v = v in get_pde_preserved'' ; clarsimp)
  apply clarsimp
  apply (rule conjI)
   apply (rule_tac x = pa in exI)
   apply (erule disjE)
    apply clarsimp
    apply (subgoal_tac "p \<notin> ptable_trace' (heap s) (root s) (Addr va)")
     prefer 2
     apply (clarsimp simp: ptable_trace'_def Let_def pd_idx_offset_def get_pde'_def decode_pde_section_def)
    apply (clarsimp simp : ptable_lift_preserved')
   apply (subgoal_tac "p \<notin> ptable_trace' (heap s) (root s) (Addr va)")
    prefer 2
    apply (clarsimp simp: ptable_trace'_def Let_def pd_idx_offset_def get_pde'_def decode_pde_section_def)
   apply (clarsimp simp : ptable_lift_preserved')
  apply (erule disjE)
   apply (rule disjI1)
   apply clarsimp
   apply (subgoal_tac "p \<notin> ptable_trace' (heap s) (root s) (Addr va)")
    prefer 2
    apply (clarsimp simp: ptable_trace'_def Let_def pd_idx_offset_def get_pde'_def decode_pde_section_def)
   apply (frule_tac w = "(the (heap s (root s)))" and v = v in get_pde_preserved' ; clarsimp)
  apply (subgoal_tac "p \<notin> ptable_trace' (heap s) (root s) (Addr va)")
   prefer 2
   apply (clarsimp simp: ptable_trace'_def Let_def pd_idx_offset_def get_pde'_def decode_pde_section_def)
  apply (frule_tac w = "(the (heap s (root s r+ 1)))" and v = v in get_pde_preserved' ; clarsimp)
done



lemma  vadd_entries_preserved:
  "\<lbrakk> root s \<noteq> p  ; root s r+ 1 \<noteq> p \<rbrakk>  \<Longrightarrow>
                        vadd_entries (s\<lparr>heap := heap s(p \<mapsto> v)\<rparr>) = vadd_entries s"
  apply (clarsimp simp: vadd_entries_def)
  apply (clarsimp simp: Collect_eq)
  apply (rule iffI)
   apply clarsimp
   apply (rule conjI)
    using vspace_preserved apply blast
   apply (erule disjE)
    apply (rule disjI1)
    apply (subgoal_tac "p \<notin> ptable_trace' (heap s(p \<mapsto> v)) (root s) (Addr va)")
     apply (clarsimp simp : ptable_lift_preserved_m)
    apply (clarsimp simp: vspace_section_def)
    apply (erule_tac disjE)
     apply clarsimp
     apply (clarsimp simp: ptable_trace'_def Let_def pd_idx_offset_def get_pde'_def decode_pde_section_def)
    apply (clarsimp simp: ptable_trace'_def Let_def pd_idx_offset_def get_pde'_def decode_pde_section_def)
   apply (rule disjI2)
   apply (subgoal_tac "p \<notin> ptable_trace' (heap s(p \<mapsto> v)) (root s) (Addr va)")
    apply (clarsimp simp : ptable_lift_preserved_m)
   apply (clarsimp simp: vspace_section_def)
   apply (erule_tac disjE)
    apply clarsimp
    apply (clarsimp simp: ptable_trace'_def Let_def pd_idx_offset_def get_pde'_def decode_pde_section_def)
   apply (clarsimp simp: ptable_trace'_def Let_def pd_idx_offset_def get_pde'_def decode_pde_section_def)
  apply clarsimp
  apply (rule conjI)
   using vspace_preserved apply blast
  apply (erule disjE)
   apply (rule disjI1)
   apply (subgoal_tac "p \<notin> ptable_trace' (heap s) (root s) (Addr va)")
    apply (clarsimp simp : ptable_lift_preserved')
   apply (clarsimp simp: vspace_section_def)
   apply (erule_tac disjE)
    apply clarsimp
    apply (clarsimp simp: ptable_trace'_def Let_def pd_idx_offset_def get_pde'_def decode_pde_section_def)
   apply (clarsimp simp: ptable_trace'_def Let_def pd_idx_offset_def get_pde'_def decode_pde_section_def)
  apply (rule disjI2)
  apply (subgoal_tac "p \<notin> ptable_trace' (heap s) (root s) (Addr va)")
   apply (clarsimp simp : ptable_lift_preserved')
  apply (clarsimp simp: vspace_section_def)
  apply (erule_tac disjE)
   apply clarsimp
   by (clarsimp simp: ptable_trace'_def Let_def pd_idx_offset_def get_pde'_def decode_pde_section_def)+


lemma kernel_memory_equal:
   "\<lbrakk>vp \<in> kernel_memory s;  ptable_lift' (heap s) (root s) (Addr vp) = Some p\<rbrakk>
              \<Longrightarrow> kernel_memory s = kernel_memory (s\<lparr>heap := heap s(p \<mapsto> v), incon_set := incon_set s \<union> pde_comp (asid s) (heap s) (heap s(p \<mapsto> v)) (root s)\<rparr>)"
  apply (clarsimp simp: kernel_memory_def)
  apply (match premises in H[thin]: "vp \<in> vspace_section _"  \<Rightarrow> \<open>insert H[unfolded vspace_section_def]\<close>)
  apply clarsimp
  apply (clarsimp simp: ok ok1)
  apply (match premises in H[thin]: "vp \<notin> vadd_entries _"  \<Rightarrow> \<open>insert H[unfolded vadd_entries_def]\<close>)
  apply clarsimp
  apply (subgoal_tac "vp \<in> vspace_section s")
   prefer 2
   apply (clarsimp simp: vspace_section_def)
  by (clarsimp simp: vadd_entries_preserved vspace_preserved)

(* important *)
lemma  kernel_memory_preserved:
  "\<Turnstile> \<lbrace> \<lambda>s. aval lval s = Some vp \<and> aval rval s = Some v \<and> vp \<in> kernel_memory s \<and>
               safe_set (kernel_memory s) s \<rbrace>  lval ::= rval  \<lbrace>\<lambda>s. safe_set (kernel_memory s) s\<rbrace>"
  apply vcg
  apply (rule conjI, clarsimp simp: safe_set_def  con_set_def)
  apply (clarsimp simp: safe_set_def safe_memory_def)
  apply (frule_tac x = vp in bspec ; safe)
  apply (rule_tac x = p in exI , simp)
  apply (rule_tac conjI, clarsimp simp: safe_memory_def)
   apply (frule_tac x = "va" in bspec)
    using kernel_memory_equal apply blast
   apply safe
   apply (rule_tac x = pa in exI)
   apply (rule conjI, clarsimp simp: ptrace_set_def)
    apply (drule_tac x = va in bspec)
     using kernel_memory_equal apply blast
    apply (rule ptable_lift_preserved' ; simp)
    using kernel_memory_equal apply blast
   apply (clarsimp simp:  ptrace_set_def)
   apply (drule_tac x = a in bspec)
    using kernel_memory_equal apply blast
   apply (drule_tac x = a in bspec , clarsimp)+
    using kernel_memory_equal apply blast
   apply (drule_tac x = a in bspec , clarsimp)+
    using kernel_memory_equal apply blast
   apply (clarsimp simp: ptable_trace_preserved')
  apply (subgoal_tac "kernel_memory s =
                      kernel_memory (s\<lparr>heap := heap s(p \<mapsto> v), incon_set := incon_set s \<union> pde_comp (asid s) (heap s) (heap s(p \<mapsto> v)) (root s)\<rparr>)")
   apply (clarsimp simp: con_set_def cons_set_preserved)
  using kernel_memory_equal apply blast
done


lemma vspace_section_preserved:
  "\<Turnstile> \<lbrace> \<lambda>s. aval lval s = Some vp \<and> aval rval s = Some v \<and> vp \<in> kernel_memory s \<and> 
             (asid s, vp) \<notin> incon_set s \<and>  vspace_section s  = mp \<rbrace>  lval ::= rval 
                          \<lbrace>\<lambda>s.  vspace_section s = mp\<rbrace>"
  apply vcg
  apply (thin_tac "mp = vspace_section s")
  apply (clarsimp simp: kernel_memory_def)
  apply (subst (asm) vspace_section_def)
  apply clarsimp
  apply (clarsimp simp: vadd_entries_def)
  apply (subgoal_tac "vp \<in> vspace_section s")
   prefer 2
   apply (clarsimp simp: vspace_section_def)
  apply clarsimp
  apply (clarsimp simp: ok)
  apply (clarsimp simp: vspace_preserved)
done

lemma vadd_entries_section_preserved:
  "\<Turnstile> \<lbrace> \<lambda>s. aval lval s = Some vp \<and> aval rval s = Some v \<and> vp \<in> kernel_memory s \<and>  (asid s, vp) \<notin> incon_set s \<and>  vadd_entries s  = mp \<rbrace>  lval ::= rval 
            \<lbrace>\<lambda>s.  vadd_entries s = mp\<rbrace>"
  apply vcg
  apply (thin_tac "mp = vadd_entries s")
  apply (clarsimp simp: kernel_memory_def)
  apply (subst (asm) vspace_section_def)
  apply clarsimp
  apply (clarsimp simp: ok1)
  apply (subst (asm)vadd_entries_def)
  apply clarsimp
  apply (subgoal_tac "vp \<in> vspace_section s")
   prefer 2
   apply (clarsimp simp: vspace_section_def)
  apply clarsimp
  apply (clarsimp simp: vadd_entries_preserved)
done


lemma mapping_section_con_set_preserved:
  "\<Turnstile> \<lbrace> \<lambda>s. aval lval s = Some vp \<and> aval rval s = Some v \<and> vp \<in> kernel_memory s \<and>  (asid s, vp) \<notin> incon_set s \<and>  
                      con_set (vadd_entries s) s \<rbrace>  lval ::= rval \<lbrace>\<lambda>s. con_set (vadd_entries s) s\<rbrace>"
  apply vcg
  apply (clarsimp simp: kernel_memory_def)
  apply (subst (asm) vspace_section_def)
  apply clarsimp
  apply (clarsimp simp: ok1)
  apply (clarsimp simp: con_set_def)
  apply (rule conjI)
   apply (match premises in H[thin]: "vp \<notin> vadd_entries _"  \<Rightarrow> \<open>insert H[unfolded vadd_entries_def]\<close>)
   apply clarsimp
   apply (subgoal_tac "vp \<in> vspace_section s")
    prefer 2
    apply (clarsimp simp: vspace_section_def)
   apply clarsimp
   apply (drule_tac  s = "root s" in not_sym)
   apply (drule_tac v = v in vadd_entries_preserved ; clarsimp)
  apply (subgoal_tac "lookup_pde' (heap s) (root s) (Addr va) =  lookup_pde' (heap s(p \<mapsto> v)) (root s) (Addr va)")
   apply (clarsimp simp: pde_comp_def)
  apply (match premises in H[thin]: "vp \<notin> vadd_entries _"  \<Rightarrow> \<open>insert H[unfolded vadd_entries_def]\<close>)
  apply clarsimp
  apply (subgoal_tac "vp \<in> vspace_section s")
   prefer 2
   apply (clarsimp simp: vspace_section_def)
  apply clarsimp
  apply (frule_tac  s = "root s" in not_sym)
  apply (drule_tac v = v in vadd_entries_preserved ; clarsimp)
  apply (clarsimp simp: vadd_entries_def)
  apply (clarsimp simp: vspace_section_def)
  apply (erule_tac P = " pd_idx_offset va = 0 \<and> get_pde' (heap s) (root s) (Addr va) = Some (decode_pde_section (the (heap s (root s))))" in disjE)
   apply clarsimp
   apply (subgoal_tac "p \<notin> ptable_trace' (heap s) (root s) (Addr va)")
    apply (subgoal_tac "get_pde' (heap s(p \<mapsto> v)) (root s) (Addr va) = Some (decode_pde_section (the (heap s (root s))))")
     apply (clarsimp simp: lookup_pde'_def decode_pde_section_def)
    using get_pde_preserved' apply force
   apply (clarsimp simp: ptable_trace'_def Let_def pd_idx_offset_def get_pde'_def decode_pde_section_def)
  apply clarsimp
  apply (subgoal_tac "p \<notin> ptable_trace' (heap s) (root s) (Addr va)")
   apply (subgoal_tac "get_pde' (heap s(p \<mapsto> v)) (root s) (Addr va) = Some (decode_pde_section (the (heap s (root s r+ 1))))")
    apply (clarsimp simp: lookup_pde'_def decode_pde_section_def)
   using get_pde_preserved' apply force
  by (clarsimp simp: ptable_trace'_def Let_def pd_idx_offset_def get_pde'_def decode_pde_section_def)
  


lemma safe_memory_preserved:
  "\<Turnstile> \<lbrace> \<lambda>s. aval lval s = Some vp \<and> aval rval s = Some v \<and> vp \<in> kernel_memory s \<and>  (asid s, vp) \<notin> incon_set s \<and>  
                      kernel_memory s = mp \<rbrace>  lval ::= rval \<lbrace>\<lambda>s. kernel_memory s = mp\<rbrace>"
  apply vcg
  apply (thin_tac "mp = kernel_memory s")
  apply (clarsimp simp: kernel_memory_def)
  apply (subst (asm) vspace_section_def)
  apply clarsimp
  apply (clarsimp simp: ok ok1)
  apply (subst (asm)vadd_entries_def)
  apply clarsimp
  apply (subgoal_tac "vp \<in> vspace_section s")
   prefer 2
   apply (clarsimp simp: vspace_section_def)
  apply (clarsimp simp: vadd_entries_preserved vspace_preserved)
done



lemma imp:
  "\<lbrakk>state_initial s  \<rbrakk> \<Longrightarrow>
  \<forall>va\<in>vspace_section'. ptable_lift' (heap s) (root s) (Addr va) = va_to_pa_offset (Addr va) 0 (Addr `vspace_section')"
  apply (clarsimp simp: state_initial_def vspace_section'_def)
  apply safe
   apply (clarsimp simp: va_to_pa_offset_def)
   apply (clarsimp simp: ptable_lift'_def lookup_pde'_def)
   apply (clarsimp simp: get_pde'_def decode_heap_pde'_def vaddr_pd_index_def pd_idx_offset_def)
   apply (clarsimp simp: decode_pde_def decode_pde_section_def addr_base_def vaddr_offset_def mask_def)
   apply word_bitwise
  apply (clarsimp simp: va_to_pa_offset_def)
  apply (clarsimp simp: ptable_lift'_def lookup_pde'_def)
  apply (clarsimp simp: get_pde'_def decode_heap_pde'_def vaddr_pd_index_def pd_idx_offset_def)
  apply (clarsimp simp: decode_pde_def decode_pde_section_def addr_base_def vaddr_offset_def mask_def)
  apply word_bitwise
  done


lemma imp1:
  "\<lbrakk>state_initial s  \<rbrakk> \<Longrightarrow>  \<forall>va\<in>vspace_section'. ptable_lift' (heap s) (root s) (Addr va) = Some (Addr va)"
  apply (clarsimp simp: state_initial_def vspace_section'_def)
  apply safe
   apply (clarsimp simp: ptable_lift'_def lookup_pde'_def)
   apply (clarsimp simp: get_pde'_def decode_heap_pde'_def vaddr_pd_index_def pd_idx_offset_def)
   apply (clarsimp simp: decode_pde_def decode_pde_section_def  addr_base_def vaddr_offset_def mask_def)
   apply word_bitwise
  apply (clarsimp simp: ptable_lift'_def lookup_pde'_def)
  apply (clarsimp simp: get_pde'_def decode_heap_pde'_def vaddr_pd_index_def pd_idx_offset_def)
  apply (clarsimp simp: decode_pde_def decode_pde_section_def addr_base_def vaddr_offset_def mask_def)
  apply word_bitwise
  done


definition
  safe_memory' :: "32 word set \<Rightarrow> bool"
where
  "safe_memory' SM \<equiv> \<forall>va \<in> SM. \<exists>p. va_to_pa_offset (Addr va) 0 (Addr ` SM) = Some p \<and>  
                                 addr_val p \<notin> {0x00000000 , 0x00000004} "


definition
  safe_set' :: "32 word set \<Rightarrow> p_state \<Rightarrow> bool"
where
  "safe_set' SA s \<equiv>  (safe_memory' SA \<and> con_set SA s)"


lemma
  "\<lbrakk> state_initial s  ; safe_set (kernel_memory') s \<rbrakk>  \<Longrightarrow> safe_set' (kernel_memory') s"
  apply (clarsimp simp:safe_set_def safe_set'_def)
  apply (clarsimp simp: safe_memory_def safe_memory'_def)
  apply (rule_tac x = "Addr va" in exI)
  apply (clarsimp simp: va_to_pa_offset_def kernel_memory'_def vadd_entries'_def)
done





lemma
  "\<Turnstile> \<lbrace> \<lambda>s. state_initial s \<and> aval lval s = Some vp \<and> aval rval s = Some v \<and> vp \<in> kernel_memory' \<and>
               safe_set' (kernel_memory') s \<rbrace>  lval ::= rval  \<lbrace>\<lambda>s. safe_set' (kernel_memory') s\<rbrace>"
  apply vcg
  apply (rule conjI, clarsimp simp: safe_set'_def con_set_def)
  apply (clarsimp simp: safe_set'_def safe_memory'_def)
  apply (frule_tac x = vp in bspec ; safe)
  apply (rule_tac x = "Addr vp" in exI)
  apply (rule conjI)
   prefer 2
   apply (frule_tac imp1)
   apply (clarsimp simp: kernel_memory'_def)
  apply (clarsimp simp: con_set_def)
  apply (clarsimp simp: pde_comp_def)
  apply (clarsimp simp: kernel_memory'_def vspace_section'_def)
  apply (erule_tac P = "pd_idx_offset (addr_val x) = 0" in disjE)
   apply (subgoal_tac "get_pde' (heap s) (root s) x =  Some (SectionPDE (Addr (addr_base ArmSection 0x00000002))
                        (perm_bits_pde_sections 0x00000002))")
    apply (subgoal_tac "get_pde' (heap s(Addr vp \<mapsto> v)) (root s) x =  Some (SectionPDE (Addr (addr_base ArmSection 0x00000002))
                         (perm_bits_pde_sections 0x00000002))")
     apply (clarsimp simp: lookup_pde'_def)
    prefer 2
    apply (clarsimp simp: state_initial_def get_pde'_def decode_heap_pde'_def Let_def vaddr_pd_index_def mask_def pd_idx_offset_def)
    apply (clarsimp simp: decode_pde_def decode_pde_section_def)
   apply (subgoal_tac "Addr vp \<notin> ptable_trace' (heap s) (root s) x")
    apply (subgoal_tac "\<exists>u. x = Addr u")
     apply clarsimp
     apply (drule_tac p = "Addr vp" and w = "0x00000002" and v = v in get_pde_preserved')
      apply (clarsimp simp: decode_pde_section_def)
     apply (clarsimp simp: decode_pde_section_def)
    apply (rule_tac x = "addr_val x" in exI)
    apply clarsimp
   apply (subgoal_tac "ptable_trace' (heap s) (root s) x = {Addr 0x00000000}")
    prefer 2
    apply (clarsimp simp: ptable_trace'_def Let_def pd_idx_offset_def decode_heap_pde'_def state_initial_def)
    apply (clarsimp simp: decode_pde_def decode_pde_section_def)
   apply clarsimp
   apply (drule_tac x = "addr_val x" in bspec)
    apply force
   apply (clarsimp simp: va_to_pa_offset_def)
  apply (subgoal_tac "get_pde' (heap s) (root s) x =  Some (SectionPDE (Addr (addr_base ArmSection 0x00100002))
                      (perm_bits_pde_sections 0x00100002))")
   apply (subgoal_tac "get_pde' (heap s(Addr vp \<mapsto> v)) (root s) x =  Some (SectionPDE (Addr (addr_base ArmSection 0x00100002))
                      (perm_bits_pde_sections 0x00100002))")
    apply (clarsimp simp: lookup_pde'_def)
   prefer 2
   apply (clarsimp simp: state_initial_def get_pde'_def decode_heap_pde'_def Let_def vaddr_pd_index_def mask_def pd_idx_offset_def)
   apply (clarsimp simp: decode_pde_def decode_pde_section_def)
  apply (subgoal_tac "Addr vp \<notin> ptable_trace' (heap s) (root s) x")
   apply (subgoal_tac "\<exists>u. x = Addr u")
    apply clarsimp
    apply (drule_tac p = "Addr vp" and w = "0x00100002" and v = v in get_pde_preserved')
     apply (clarsimp simp: decode_pde_section_def)
    apply (clarsimp simp: decode_pde_section_def)
   apply (rule_tac x = "addr_val x" in exI)
   apply clarsimp
  apply (subgoal_tac "ptable_trace' (heap s) (root s) x = {Addr 4}")
   prefer 2
   apply (clarsimp simp: ptable_trace'_def Let_def pd_idx_offset_def decode_heap_pde'_def state_initial_def)
   apply (subgoal_tac "heap s (Addr 4) = Some 0x00100002")
    apply (clarsimp simp: decode_pde_def decode_pde_section_def)
    apply force
   apply clarsimp
   apply (drule_tac x = "addr_val x" in bspec)
    apply force
   apply (clarsimp simp: va_to_pa_offset_def)
done
 

(*
  For the new lemma, it goes in the right direction, 
but I wouldn’t change the definition of safe_memory, but instead try to prove an equation that says that the old definition of safe_memory 
is equivalent to the new version you have. Then all the old theorems still hold and you don’t need to re-prove anything 
this instantiation is supposed to be not much work, i.e. if we have to prove much, something is wrong).
*)

definition
  vspace_defined :: "bool"
where
  "vspace_defined  \<equiv>  \<forall>va\<in>vspace_section'. \<exists>p. va_to_pa_offset va 0 (vspace_section') = Some p"





definition 
  kernel_memory' :: " 32 word set"
where
  "kernel_memory'  = vspace_section' - vadd_entries'"

definition
  safe_memory' :: "32 word set  \<Rightarrow> bool"
where
  "safe_memory' SM \<equiv> \<forall>va \<in> SM. \<exists>p. va_to_pa_offset va 0 (vspace_section') = Some p \<and>  
                        p \<notin> {0x00000000 , 0x00000004} "


definition
  safe_set' :: "32 word set \<Rightarrow> p_state \<Rightarrow> bool"
where
  "safe_set' SA s \<equiv>   (safe_memory' SA \<and> con_set SA s)"


lemma  kernel_memory_preserved:
  "\<Turnstile> \<lbrace> \<lambda>s. aval lval s = Some vp \<and> aval rval s = Some v \<and> vp \<in> kernel_memory' \<and>
               safe_set' (kernel_memory') s \<rbrace>  lval ::= rval  \<lbrace>\<lambda>s. safe_set' (kernel_memory') s\<rbrace>"
  apply vcg
  apply (rule conjI, clarsimp simp: safe_set'_def  con_set_def)
  apply (clarsimp simp: safe_set'_def safe_memory'_def)
  apply (frule_tac x = vp in bspec ; safe)
  apply (rule_tac x = p in exI , simp)

oops
(*  va_to_pa_offset va 0 (vspace_section' s)  *)
(* it has to be 4 *)

value "pd_idx_offset (0x001FFFFF)"



(* page_table mapped by kernel entries *)
                  






(* constant page table mapping for address translation  
 concept of global mappings  and their affect on the TLB 
 locked and unlocked entries 
 there is an address space for every process and that address space has a portion for the global entries. and these entries are for kernel mappings
  and they don't change during the course of all the executions and that's why the tlb remain inconsistent for these entries *)


consts
   global_mappings' :: "p_state \<Rightarrow> 32 word set"



definition
  global_mappings :: "32 word set \<Rightarrow> p_state \<Rightarrow> bool"
where
  "global_mappings S' s \<equiv>  \<forall>va \<in> S'. (\<exists>p. ptable_lift' (heap s) (root s) (Addr va) = Some p)"



(* during booting , boot process is an assumption in seL4? *)

(*lemma
"\<Turnstile> \<lbrace> \<lambda>s. global_mappings = {} \<and> 
aval lval s = Some vp \<and> aval rval s = Some v " *)




(* During run-time  *)


lemma   global_mapp_preserved:
  "\<Turnstile> \<lbrace> \<lambda>s. global_mappings GM s \<and> aval lval s = Some vp \<and> aval rval s = Some v \<and> vp \<in> DTS \<and>
        defined_trans_safe DTS s \<and>  the (ptable_lift' (heap s) (root s) (Addr vp)) \<notin> ptrace_set GM s\<rbrace>  
           lval ::= rval  \<lbrace>\<lambda>s. global_mappings GM s\<rbrace>"
  apply vcg
  apply (clarsimp simp: defined_trans_safe_def)
  apply (drule_tac x = vp in bspec)
   apply clarsimp
  apply clarsimp
  apply (clarsimp simp: global_mappings_def)
  apply (drule_tac x = va in bspec)
   apply clarsimp
  apply clarsimp
  apply (rule_tac x = pa in exI)
  apply (clarsimp simp: ptrace_set_def)
  apply (drule_tac x = va in bspec)
   apply clarsimp
  apply (clarsimp simp: ptable_lift_preserved')
  done

(*  hp = heap s ?? *)

lemma
  "\<lbrakk> lookup_pde' (heap s(p \<mapsto> v)) (root s) (Addr x) = lookup_pde' (heap s) (root s) (Addr x)  \<rbrakk>  \<Longrightarrow> 
        ptable_lift'  (heap s(p \<mapsto> v)) (root s) (Addr x) = ptable_lift' (heap s) (root s) (Addr x)"
  by (clarsimp simp: ptable_lift'_def)

(*

lemma
  "\<Turnstile> \<lbrace>\<lambda>s. P (fun (heap s))\<rbrace>  lval ::= rval 
       \<lbrace>\<lambda>s. P (fun (heap s))\<rbrace>"

oops  *)

lemma  global_lookup_preserved:
  "\<Turnstile> \<lbrace> \<lambda>s. global_mappings GM s \<and> aval lval s = Some vp \<and> aval rval s = Some v \<and> vp \<in> DTS \<and> defined_trans_safe DTS s \<and> 
          the (ptable_lift' (heap s) (root s) (Addr vp)) \<notin> ptrace_set GM s \<and> hp = heap s\<rbrace>  lval ::= rval 
       \<lbrace>\<lambda>s. \<forall>x. x \<in> GM \<longrightarrow> lookup_pde' (heap s) (root s ) (Addr x)  = lookup_pde' hp (root s) (Addr x)\<rbrace>"
  apply vcg
  apply (clarsimp simp: defined_trans_safe_def)
  apply (drule_tac x = vp in bspec ; clarsimp)
  apply (clarsimp simp: global_mappings_def ptrace_set_def)
  apply (drule_tac x = x in bspec ; clarsimp)
  apply (drule_tac x = x in bspec , clarsimp)
  apply (clarsimp simp: lookup_pde'_def ptable_trace'_def  ptable_lift'_def decode_heap_pde'_def Let_def)
  apply (clarsimp  simp: get_pde'_def decode_heap_pde'_def split: option.splits)
  apply (clarsimp simp:get_pde'_def decode_heap_pde'_def Let_def)
  by (case_tac "decode_pde x2" ; clarsimp simp: lookup_pte'_def get_pte'_def  decode_heap_pte'_def split: option.splits)

  
lemma global_map_incon_set_constant:
  "\<Turnstile> \<lbrace> \<lambda>s. global_mappings GM s \<and> aval lval s = Some vp \<and> aval rval s = Some v \<and> vp \<in> DTS \<and> defined_trans_safe DTS s \<and> 
          the (ptable_lift' (heap s) (root s) (Addr vp)) \<notin> ptrace_set GM s \<and> 
         (\<forall>va. va \<in> GM \<longrightarrow> (asid s, va) \<notin> incon_set s)\<rbrace>  lval ::= rval  \<lbrace>\<lambda>s.  (\<forall>va. va \<in> GM \<longrightarrow> (asid s, va) \<notin> incon_set s)\<rbrace>"
  apply vcg
  apply (clarsimp simp: defined_trans_safe_def)
  apply (drule_tac x = vp in bspec ; clarsimp)
  apply (subgoal_tac "\<forall>x\<in>GM. lookup_pde' (heap s(p \<mapsto> v)) (root s) (Addr x) = lookup_pde' (heap s) (root s) (Addr x)")
   using  pde_comp_def apply force
  (* how to drule " global_lookup_preserved" here *)
  apply (clarsimp simp: global_mappings_def ptrace_set_def)
  apply (drule_tac x = x in bspec ; clarsimp)
  apply (drule_tac x = x in bspec , clarsimp)
  apply (clarsimp simp: lookup_pde'_def ptable_trace'_def  ptable_lift'_def decode_heap_pde'_def Let_def)
  apply (clarsimp  simp: get_pde'_def decode_heap_pde'_def split: option.splits)
  apply (clarsimp simp:get_pde'_def decode_heap_pde'_def Let_def)
  by (case_tac "decode_pde x2" ; clarsimp simp: lookup_pte'_def get_pte'_def  decode_heap_pte'_def split: option.splits)



(* User can not make TLB inconsistent *)

(* in seL4, there is no kernel process, there is a program running and whenever there is a systemcall,
the kernel privilege mode is turned in the hardware, that has privilege to run in with complete access, and then TLB mapping can be changed *)


(* redundant may be, we have results already *)

definition 
  usr_mode :: "32 word set \<Rightarrow> p_state \<Rightarrow> bool"
where
  "usr_mode usr s \<equiv> safe_memory usr s"
                           



definition
  safe_usr :: "32 word set \<Rightarrow> p_state \<Rightarrow> bool"
where
  "safe_usr SA s \<equiv>  (usr_mode SA s \<and> con_set SA s)"
              


    (*important *)
lemma safe_usr_preserved:
  "\<Turnstile> \<lbrace> \<lambda>s. aval lval s = Some vp \<and> aval rval s = Some v \<and> vp \<in> USR \<and> safe_usr USR s \<rbrace>
             lval ::= rval  \<lbrace>\<lambda>s. safe_usr USR s \<rbrace>"
  apply vcg
  apply (rule conjI, clarsimp simp: safe_usr_def usr_mode_def safe_memory_def con_set_def)
  apply (clarsimp simp: safe_usr_def usr_mode_def safe_memory_def)
  apply (frule_tac x = vp in bspec ; safe)
  apply (rule_tac x = p in exI , simp)
  apply (rule_tac conjI, clarsimp simp: safe_memory_def)
   apply (frule_tac x = "va" in bspec ; safe)
   apply (rule_tac x = pa in exI)
   apply (rule conjI, clarsimp simp: ptrace_set_def)
    apply (drule_tac x = va in bspec ; simp)
    apply (rule ptable_lift_preserved' ; simp)
   apply (clarsimp simp:  ptrace_set_def)
   apply (drule_tac x = a in bspec ; clarsimp)
   apply (drule_tac x = a in bspec , clarsimp)+
   apply (clarsimp simp: ptable_trace_preserved')
  by (clarsimp simp: con_set_def cons_set_preserved)




(* Context Switch *)






lemma decode_val_section_page_table:
  "\<lbrakk> ptable_lift' hp1 rt v = Some p ; lookup_pde' hp1 rt v = lookup_pde' (hp1 (p \<mapsto> val)) rt v ;
     rt r+ ((vaddr_pd_index (addr_val v)) << 2) = p \<rbrakk> \<Longrightarrow> 
         (\<exists>a b. decode_pde val = SectionPDE a b) \<or> (\<exists>x. decode_pde val = PageTablePDE x)"
  apply (simp only: ptable_lift'_def lookup_pde'_def split: option.splits)
         apply (clarsimp+)[7]
  apply (simp only: Let_def get_pde'_def decode_heap_pde'_def  split: option.splits)
  apply (case_tac x2 )
     apply clarsimp
    apply clarsimp
   apply simp
   apply (rule_tac disjI2)
   apply clarsimp
   apply (case_tac "decode_pde val" ; clarsimp)
  apply (rule_tac disjI1)
  apply clarsimp
  apply (case_tac "decode_pde val" ; clarsimp)
 done


lemma decode_val_page_table:
  "\<lbrakk> ptable_lift' hp1 rt v = Some p ; lookup_pde' hp1 rt v = lookup_pde' (hp1 (p \<mapsto> val)) rt v ; get_pde' hp1 rt v = Some (PageTablePDE ba);
      p = ba r+ (vaddr_pt_index (addr_val v) << 2); rt r+ ((vaddr_pd_index (addr_val v)) << 2) \<noteq> p \<rbrakk> \<Longrightarrow> 
          \<exists>a b. decode_pte val = SmallPagePTE a b"
  apply (subgoal_tac " get_pde' (hp1 (p \<mapsto> val)) rt v = Some (PageTablePDE ba)")
   prefer 2
   apply (clarsimp simp: get_pde'_def decode_heap_pde'_def)
  apply (subgoal_tac "\<exists>a aa b.  lookup_pte' hp1 ba v = Some (a, aa, b)")
   prefer 2
   apply (clarsimp simp: ptable_lift'_def lookup_pde'_def)
  apply clarsimp
  apply (rule_tac x = "a" in exI)
  apply (rule_tac x = "b" in exI)
  apply (clarsimp simp:  ptable_lift'_def lookup_pde'_def split: option.splits)
  apply (clarsimp simp:lookup_pte'_def decode_heap_pte'_def  split: option.splits)
  apply (case_tac x2 ; clarsimp)
  apply (case_tac x2a ; clarsimp)
  apply (clarsimp simp: get_pte'_def decode_heap_pte'_def Let_def )
done



lemma pt_lift_get_pde_none:
  "ptable_lift' hp rt va = Some pa \<Longrightarrow> get_pde' hp rt va \<noteq> None"
  by (clarsimp simp: ptable_lift'_def lookup_pde'_def split: option.splits)


lemma imp1:
  "\<lbrakk> lookup_pde' hp rt va = Some (a, ArmSection, b) ; lookup_pde' hp rt va =  lookup_pde' (hp (pa \<mapsto> val)) rt va\<rbrakk> \<Longrightarrow> 
               get_pde' hp rt va  =  get_pde' (hp(pa \<mapsto> val)) rt va "
  apply (clarsimp simp: lookup_pde'_def split:option.splits)
  apply (case_tac x2 ; clarsimp)
   apply (case_tac x2a ; clarsimp)
    apply (clarsimp simp: lookup_pte'_def split:option.splits)
    apply (case_tac x2a ; clarsimp)
    apply (case_tac x2 ; clarsimp)
   apply (clarsimp simp: lookup_pte'_def split:option.splits)
   apply (case_tac x2 ; clarsimp)
  apply (case_tac x2a ; clarsimp)
  apply (clarsimp simp: lookup_pte'_def split:option.splits)
  apply (case_tac x2 ; clarsimp)
done



lemma imp2:
  "\<lbrakk> lookup_pde' (heap s) (root s) (Addr vb) = Some (a, ArmSection, b)  \<rbrakk> \<Longrightarrow> 
     get_pde' (heap s) (root s) (Addr vb)  =  Some (SectionPDE a b)"
  apply (clarsimp simp: lookup_pde'_def split:option.splits)
  apply (case_tac x2 ; clarsimp)
  apply (clarsimp simp: lookup_pte'_def split:option.splits)
  by (case_tac x2 ; clarsimp)
 

lemma imp3:
  "\<lbrakk> lookup_pde' hp rt va = Some (a, ArmSection, b) ; lookup_pde' hp rt va =  lookup_pde' (hp (pa \<mapsto> val)) rt va ; 
           lookup_pde' hp rt va =  lookup_pde' (hp (pb \<mapsto> vala)) rt va \<rbrakk> \<Longrightarrow> 
    get_pde' (hp(pa \<mapsto> val)(pb \<mapsto> vala)) rt va =  get_pde' hp rt va "
  apply (clarsimp simp: lookup_pde'_def split:option.splits)
  apply (case_tac x2 ; clarsimp)
   apply (case_tac x2a ; clarsimp)
    apply (clarsimp simp: lookup_pte'_def split:option.splits)
    apply (case_tac x2a ; clarsimp)
    apply (case_tac x2 ; clarsimp)
   apply (clarsimp simp: lookup_pte'_def split:option.splits)
   apply (case_tac x2 ; clarsimp)
  apply (case_tac x2a ; clarsimp)
   apply (clarsimp simp: lookup_pte'_def split:option.splits)
   apply (case_tac x2 ; clarsimp)
  apply (case_tac x2b ; clarsimp)
   apply (clarsimp simp: lookup_pte'_def split:option.splits)
   apply (case_tac x2 ; clarsimp)
  apply (clarsimp simp: get_pde'_def decode_heap_pde'_def Let_def)
done



lemma imp4:
  "\<lbrakk>lookup_pde' (heap s) (root s) (Addr vb) = Some (a, ArmSection, b)  ; 
       get_pde' (heap s(pb \<mapsto> val)(pa \<mapsto> vala)) (root s) (Addr vb) =  get_pde' (heap s) (root s) (Addr vb) \<rbrakk> \<Longrightarrow> 
    lookup_pde' (heap s(pb \<mapsto> val)(pa \<mapsto> vala)) (root s) (Addr vb) =  lookup_pde' (heap s) (root s) (Addr vb) "
  apply (clarsimp simp: lookup_pde'_def split:option.splits)
  apply (case_tac x2 ; clarsimp)
    apply (clarsimp simp: lookup_pte'_def split:option.splits)
    apply (case_tac x2 ; clarsimp)
 done


lemma ok1:
  "lookup_pde' hp rt va = Some (a, ArmSmallPage, b) \<Longrightarrow> \<exists>ba. get_pde' hp rt va = Some (PageTablePDE ba)"
  apply (clarsimp simp: lookup_pde'_def split: option.splits)
  by (case_tac x2 ; clarsimp)  



lemma imp11:
  "\<lbrakk> lookup_pde' hp rt va = Some (a, ArmSmallPage, b) ; lookup_pde' hp rt va =  lookup_pde' (hp (pa \<mapsto> val)) rt va ; 
        get_pde' hp rt va = Some (PageTablePDE ba) ; get_pde' (hp(pa \<mapsto> val)) rt va = Some (PageTablePDE ba1)\<rbrakk> \<Longrightarrow> 
          lookup_pte' hp ba va = lookup_pte' (hp(pa \<mapsto> val)) ba1 va"
  by (clarsimp simp: lookup_pde'_def split:option.splits)



lemma imp11':
  "\<lbrakk> lookup_pde' hp rt va = Some (a, ArmSmallPage, b) ; lookup_pde' hp rt va =  lookup_pde' (hp (pa \<mapsto> val)) rt va \<rbrakk> \<Longrightarrow> 
          \<exists>ba ba1. lookup_pte' hp ba va = lookup_pte' (hp(pa \<mapsto> val)) ba1 va"
  apply (frule_tac ok1)
  apply (subgoal_tac "lookup_pde' (hp(pa \<mapsto> val)) rt va = Some (a, ArmSmallPage, b)")
   prefer 2
   apply clarsimp
  apply (frule_tac hp = "(hp(pa \<mapsto> val))" in  ok1)
  apply clarsimp
  apply (rule_tac x = ba in exI)
  apply (rule_tac x = baa in exI)
  by (force simp: lookup_pde'_def split:option.splits)




end



