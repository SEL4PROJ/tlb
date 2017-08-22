theory Kernel_Execution
                  
imports Memory_Model
        

begin  

lemma [simp]:
  "safe_memory S (s\<lparr>incon_set := IS\<rparr>) =  safe_memory S s "
  by (clarsimp simp: safe_memory_def ptrace_set_def)


lemma [simp]:
  "con_set S (s\<lparr>heap := hp ,  incon_set := IS\<rparr>) =  con_set S (s\<lparr>incon_set := IS\<rparr>) "
  by (clarsimp simp: con_set_def)

declare assign_sound [vcg del] 


(* kernel code *)

(* function types are not very good *)

(* in systems, kernel window is all of the memory except the devices, but in our case (from verification point of view),
     it should be all of the memory except the kernel mappings themselves and kernel code  *)

(* Kernel execution phase, it should not write to the global mappings of current and inactive processes  *)

definition
  kernel_state :: "p_state \<Rightarrow> bool"
where
  "kernel_state s \<equiv> \<exists>rt a. root s = rt  \<and> current_page_table s \<and> mode s = Kernel \<and> 
                        asid s = a  \<and> root_map s rt = Some a \<and> partial_inj (root_map s) \<and> rt\<in>root_log s \<and>
                        global_mappings_of_all_processes s \<and> \<Union>(ptable_trace' (heap s) (root s) ` UNIV) \<subseteq> kernel_phy_mem" 

lemma [simp]:
  "\<lbrakk>kernel_state s; assigned_asids_consistent (root_map s) (incon_set s)\<rbrakk> \<Longrightarrow> 
                    con_set VA s"
  apply (clarsimp simp: assigned_asids_consistent_def con_set_def  kernel_state_def assigned_asid_va_map_def ran_def)
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
  " \<lbrakk>kernel_state s; vp' \<in> kernel_safe_region' s; vp \<in> kernel_safe_region' s\<rbrakk> \<Longrightarrow> Addr (vp' - global_offset) \<notin> ptable_trace' (heap s) (root s) (Addr vp)"
  apply (frule_tac va = vp in  global_mappings_decode')
   apply (clarsimp simp: kernel_state_def) apply clarsimp
  apply(clarsimp simp:  kernel_state_def ptable_trace'_def kernel_safe_region'_def vas_mapped_by_global_mappings_def vas_of_current_state_mapped_to_global_mappings_of_all_processes_def pd_idx_offset_def)+
done


lemma  kernel_execution_assign:          
  "\<Turnstile> \<lbrace> \<lambda>s. kernel_state s \<and> aval lval s = Some vp \<and> aval rval s = Some v \<and> vp \<in> SM \<and> SM = kernel_safe_region' s \<and>
             assigned_asids_consistent (root_map s) (incon_set s) \<rbrace>    (* assumption added for consistency *)
                     lval ::= rval  
                  \<lbrace>\<lambda>s. safe_set SM s \<and>  heap s (Addr vp r- global_offset) = Some v\<rbrace>"
  apply (vcgm vcg: weak_pre_write')
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
            aval lval2 (s\<lparr>heap := heap s(Addr vp1 r- global_offset \<mapsto> v1) , incon_set := incon_set s \<union> pde_comp' (asid s) (heap s) (heap s(Addr (vp1 - global_offset) \<mapsto> v1)) (root s)\<rparr>) = Some vp2 \<and> 
            aval rval2 (s\<lparr>heap := heap s(Addr vp1 r- global_offset \<mapsto> v1) , incon_set := incon_set s \<union> pde_comp' (asid s) (heap s) (heap s(Addr (vp1 - global_offset) \<mapsto> v1)) (root s)\<rparr>) = Some v2 \<and> vp2 \<in> SM  \<and>  
           assigned_asids_consistent (root_map s) (incon_set s)  \<and>  SM = kernel_safe_region' s\<rbrace>  
                  lval1 ::= rval1 ;; lval2 ::= rval2 
           \<lbrace>\<lambda>s. safe_set SM s \<and> heap s (Addr vp2 r- global_offset) = Some v2\<rbrace>"
  apply (vcgm vcg: weak_pre_write')
  apply (rule conjI)
   apply (clarsimp simp: safe_set_def safe_memory_def ptrace_set_def)
  using  ptable_lift_write_n by force
  


end



