theory Boot
                  
imports Memory_Model
        

begin               


declare assign_sound [vcg del] 


definition
  boot_state :: "p_state \<Rightarrow> bool"
where                                           
  "boot_state s \<equiv> \<exists>rt a. root s = rt  \<and> current_page_table s \<and> mode s = Kernel \<and> 
                        asid s = a \<and> incon_set s = {} \<and> root_map s rt = Some a \<and> partial_inj (root_map s) \<and> root_log s = {rt} \<and>
                        global_mappings (heap s) (root s) \<and> \<Union>(ptable_trace' (heap s) (root s) ` UNIV) \<subseteq> kernel_phy_mem"


(* vspace_section = vas_mapped_by_global_mappings
  vadd_entries = vas_mapped_to_global_mappings
*)

(*lemma boot_state_page_lift_m [simp]:
  "boot_state s \<Longrightarrow> ptable_lift_m (heap s) (root s) (mode s) v = ptable_lift' (heap s) (root s) v"
  by (clarsimp simp: boot_state_def)*)


lemma boot_kerenl_region_offset':
  "boot_state s  \<Longrightarrow>
        \<forall>va\<in>kernel_safe_region s.  ptable_lift' (heap s) (root s) (Addr va) = Some (Addr va r- global_offset)"
  by (clarsimp simp: boot_state_def global_mappings_def kernel_safe_region_def vas_mapped_by_global_mappings_def)
 
lemma boot_kerenl_region_offset[simp]:
  "\<lbrakk>boot_state s;  va \<in> kernel_safe_region s\<rbrakk> \<Longrightarrow> ptable_lift_m (heap s) (root s) (mode s) (Addr va) = Some (Addr va r- global_offset) "
  by (clarsimp simp: boot_state_def global_mappings_def kernel_safe_region_def vas_mapped_by_global_mappings_def)


lemma global_mappings_decode:
  "\<lbrakk>global_mappings  (heap s) (root s) ; va \<in> kernel_safe_region s\<rbrakk> \<Longrightarrow> 
         \<exists>p perm. decode_heap_pde' (heap s) (root s r+ (vaddr_pd_index va << 2)) =  Some (SectionPDE p perm)"
  apply (clarsimp simp: kernel_safe_region_def vas_mapped_by_global_mappings_def global_mappings_def pd_idx_offset_def get_pde'_def)
  by force

lemma boot_state_con_set [simp]:
  "boot_state s \<Longrightarrow> con_set (kernel_safe_region s) s"
  by (clarsimp simp: boot_state_def con_set_def)

lemma  kernel_safe_region_ptable_trace [simp]:
  " \<lbrakk>boot_state s; vp' \<in> kernel_safe_region s; vp \<in> kernel_safe_region s\<rbrakk> \<Longrightarrow> Addr (vp' - global_offset) \<notin> ptable_trace' (heap s) (root s) (Addr vp)"
  apply (frule_tac va = vp in  global_mappings_decode [rotated])
   apply (clarsimp simp: boot_state_def)
  by (clarsimp simp: boot_state_def ptable_trace'_def kernel_safe_region_def vas_mapped_by_global_mappings_def vas_mapped_to_global_mappings_def pd_idx_offset_def)+

lemma [simp]:
  "boot_state s \<Longrightarrow> safe_set (kernel_safe_region s) s"
  apply (clarsimp simp: safe_set_def)
 by (clarsimp simp: safe_memory_def ptrace_set_def)
 


lemma ptable_lift_write_n:
  "\<lbrakk> boot_state  s ; vp' \<in> kernel_safe_region s; vp \<in> kernel_safe_region s \<rbrakk> \<Longrightarrow>
     ptable_lift_m (heap s(Addr vp' r- global_offset \<mapsto> x)) (root s)  (mode s) (Addr vp) =  ptable_lift_m  (heap s)  (root s)  (mode s) (Addr vp)"
  apply clarsimp
  apply (subgoal_tac "Addr (vp' - global_offset) \<notin> ptable_trace' (heap s) (root s) (Addr vp)")
   apply (frule_tac pa = "Addr (vp - global_offset)" and v = x in ptable_lift_preserved')
    apply (clarsimp simp: boot_kerenl_region_offset')
   apply (clarsimp simp: boot_state_def)
  by clarsimp
 

lemma  assign_safe_kernel_region:
  "\<Turnstile> \<lbrace> \<lambda>s. boot_state s \<and> aval lval s = Some vp \<and> aval rval s = Some v \<and> vp \<in> SM \<and> SM = kernel_safe_region s \<rbrace>  
                        lval ::= rval  
                     \<lbrace>\<lambda>s. safe_set SM s\<rbrace>"
  apply (rule weak_pre)
   apply (rule safe_set_preserved)
  by clarsimp
 

lemma  assign_safe_kernel_region':
  "\<Turnstile> \<lbrace> \<lambda>s. boot_state s \<and> aval lval s = Some vp \<and> aval rval s = Some v \<and> vp \<in> SM \<and> SM = kernel_safe_region s \<rbrace>  
                        lval ::= rval  
                     \<lbrace>\<lambda>s. safe_set SM s \<and> heap s (Addr vp r- global_offset) = Some v\<rbrace>"
  by (vcg vcg: weak_pre_write')
 
 

lemma assignments_safe_kernel_region:
  "\<Turnstile> \<lbrace> \<lambda>s.  boot_state s \<and> aval lval1 s = Some vp1 \<and> aval rval1 s = Some v1 \<and> vp1 \<in> SM \<and> 
            aval lval2 (s\<lparr>heap := heap s(Addr vp1 r- global_offset \<mapsto> v1)\<rparr>) = Some vp2 \<and> 
            aval rval2 (s\<lparr>heap := heap s(Addr vp1 r- global_offset \<mapsto> v1)\<rparr>) = Some v2 \<and> vp2 \<in> SM \<and> SM = kernel_safe_region s  \<rbrace>  
               lval1 ::= rval1 ;; lval2 ::= rval2 
      \<lbrace>\<lambda>s. safe_set SM s \<and> heap s (Addr vp2 r- global_offset) = Some v2\<rbrace>"
  apply_trace (vcg vcg: weak_pre_write')
  using  ptable_lift_write_n by force
   


definition
  boot_state' :: "p_state \<Rightarrow> bool"
where
  "boot_state' s \<equiv> \<exists>rt a. root s = rt  \<and> current_page_table s \<and> mode s = Kernel \<and> 
                        asid s = a \<and> incon_set s = {} \<and> root_map s rt = Some a \<and> partial_inj (root_map s) \<and> root_log s = {rt} \<and>
                        global_mappings_of_all_processes s \<and> \<Union>(ptable_trace' (heap s) (root s) ` UNIV) \<subseteq> kernel_phy_mem"

lemma [simp]:
  "boot_state' s   \<Longrightarrow>  boot_state s "
  apply (simp only: boot_state'_def global_mappings_of_all_processes_def global_mappings_def boot_state_def )
  by force


lemma [simp]:
  "boot_state' s   \<Longrightarrow> kernel_safe_region' s = kernel_safe_region s "
  by (clarsimp simp: boot_state'_def kernel_safe_region'_def kernel_safe_region_def global_mappings_of_all_processes_def
   vas_of_current_state_mapped_to_global_mappings_of_all_processes_def vas_mapped_to_global_mappings_def vas_mapped_by_global_mappings_def)


lemma  assign_safe_kernel_region_n:
  "\<Turnstile> \<lbrace> \<lambda>s. boot_state' s \<and> aval lval s = Some vp \<and> aval rval s = Some v \<and> vp \<in> SM \<and> SM = kernel_safe_region' s \<rbrace>  
                        lval ::= rval  
                     \<lbrace>\<lambda>s. safe_set SM s\<rbrace>"
  apply (rule weak_pre)
   apply (rule assign_safe_kernel_region [of _ vp _ v])
  by clarsimp



lemma assignments_safe_kernel_region':
  "\<Turnstile> \<lbrace> \<lambda>s.  boot_state' s \<and> aval lval1 s = Some vp1 \<and> aval rval1 s = Some v1 \<and> vp1 \<in> SM \<and> 
            aval lval2 (s\<lparr>heap := heap s(Addr vp1 r- global_offset \<mapsto> v1)\<rparr>) = Some vp2 \<and> 
            aval rval2 (s\<lparr>heap := heap s(Addr vp1 r- global_offset \<mapsto> v1)\<rparr>) = Some v2 \<and> vp2 \<in> SM \<and> SM = kernel_safe_region' s  \<rbrace>  
               lval1 ::= rval1 ;; lval2 ::= rval2 
      \<lbrace>\<lambda>s. safe_set SM s \<and> heap s (Addr vp2 r- global_offset) = Some v2\<rbrace>"
  apply (rule weak_pre)
  apply (rule assignments_safe_kernel_region [of _ vp1 _ v1])
  by clarsimp
   

(* more of an kernel execution *)

definition
  boot_state'' :: "p_state \<Rightarrow> bool"
where
  "boot_state'' s \<equiv> \<exists>rt a. root s = rt  \<and> current_page_table s \<and> mode s = Kernel \<and> 
                        asid s = a \<and> incon_set s = {} \<and> root_map s rt = Some a \<and> partial_inj (root_map s) \<and> root s \<in> root_log s \<and>
                        global_mappings_of_all_processes s \<and> \<Union>(ptable_trace' (heap s) (root s) ` UNIV) \<subseteq> kernel_phy_mem"


lemma [simp]:
  "boot_state'' s \<Longrightarrow> con_set (kernel_safe_region' s) s"
  by (clarsimp simp: boot_state''_def con_set_def)

lemma [simp]:
  "\<lbrakk>boot_state'' s;  va \<in> kernel_safe_region' s\<rbrakk> \<Longrightarrow> ptable_lift_m (heap s) (root s) (mode s) (Addr va) = Some (Addr va r- global_offset) "
  by (clarsimp simp: boot_state''_def global_mappings_of_all_processes_def kernel_safe_region'_def vas_mapped_by_global_mappings_def)


lemma global_mappings_decode':
  "\<lbrakk>boot_state'' s  ; va \<in> kernel_safe_region' s\<rbrakk> \<Longrightarrow> 
         \<exists>p perm. decode_heap_pde' (heap s) (root s r+ (vaddr_pd_index va << 2)) =  Some (SectionPDE p perm)"
  apply (clarsimp simp: kernel_safe_region'_def vas_mapped_by_global_mappings_def global_mappings_of_all_processes_def global_mappings_def 
                        pd_idx_offset_def get_pde'_def boot_state''_def)
  by force

lemma  kernel_safe_region_ptable_trace' [simp]:
  " \<lbrakk>boot_state'' s; vp' \<in> kernel_safe_region' s; vp \<in> kernel_safe_region' s\<rbrakk> \<Longrightarrow> Addr (vp' - global_offset) \<notin> ptable_trace' (heap s) (root s) (Addr vp)"
  apply (frule_tac va = vp in  global_mappings_decode')
   apply (clarsimp simp: boot_state''_def) apply clarsimp
  apply(clarsimp simp: boot_state''_def ptable_trace'_def kernel_safe_region'_def vas_mapped_by_global_mappings_def vas_of_current_state_mapped_to_global_mappings_of_all_processes_def pd_idx_offset_def)+ 
done


lemma  assign_safe_kernel_region_not_boot:
  "\<Turnstile> \<lbrace> \<lambda>s. boot_state'' s \<and> aval lval s = Some vp \<and> aval rval s = Some v \<and> vp \<in> SM \<and> SM = kernel_safe_region' s \<rbrace>  
                        lval ::= rval  
                     \<lbrace>\<lambda>s. safe_set SM s\<rbrace>"
  apply (rule weak_pre)
   apply (rule safe_set_preserved)
  by (clarsimp simp: safe_set_def safe_memory_def ptrace_set_def)

(* Ideally, current page table theorems should be derived from the theorems of all the page tables *)


end