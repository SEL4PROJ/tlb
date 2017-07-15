theory Memory_Model
                  
imports Safe_Set
        

begin               


consts rt_lower_bound :: "32 word"
consts rt_upper_bound :: "32 word"
consts global_offset :: "32 word"
consts ker_phy_lower_bound :: "paddr"
consts ker_phy_upper_bound :: "paddr"


definition
  high_mem_phy_add :: "paddr \<Rightarrow> paddr set"
where
  "high_mem_phy_add rt  = {rt r+ rt_lower_bound .. rt r+ rt_upper_bound}"


definition
  "kernel_phy_mem  = {ker_phy_lower_bound .. ker_phy_upper_bound}"


definition 
   pd_idx_offset :: "32 word \<Rightarrow> machine_word"
where      
  "pd_idx_offset vp = ((vaddr_pd_index vp) << 2)"

definition
  va_to_pid_offset :: "vaddr set \<Rightarrow> 32 word set"
where
  "va_to_pid_offset V = pd_idx_offset ` addr_val ` V"


(*definition
  global_mappings :: "p_state  \<Rightarrow> bool"
where
  "global_mappings s  \<equiv> \<forall>va. root s r+ pd_idx_offset va \<in> high_mem_phy_add (root s) \<longrightarrow>
                         (\<exists>p perms. get_pde' (heap s) (root s) (Addr va) = Some (SectionPDE p perms) \<and> \<not>user_perms perms ) \<and>
        ptable_lift_m (heap s) (root s) Kernel (Addr va)  =  Some (Addr va r- global_offset) \<and> (Addr va r- global_offset) \<in> kernel_phy_mem"
*)


definition
  global_mappings :: "heap \<Rightarrow> paddr  \<Rightarrow> bool"
where
  "global_mappings h r  \<equiv> \<forall>va. r r+ pd_idx_offset va \<in> high_mem_phy_add r \<longrightarrow>
                         (\<exists>p perms. get_pde' h r (Addr va) = Some (SectionPDE p perms) \<and> \<not>user_perms perms ) \<and>
        ptable_lift_m h r Kernel (Addr va)  =  Some (Addr va r- global_offset) \<and> (Addr va r- global_offset) \<in> kernel_phy_mem"

(*
lemma
  "global_mappings s = global_mappings' (heap s) (root s)"
  by (clarsimp simp: global_mappings'_def global_mappings_def) *)


definition
  vas_mapped_by_global_mappings :: "paddr \<Rightarrow> 32 word set"
where
  "vas_mapped_by_global_mappings r \<equiv> {va. r r+ pd_idx_offset va \<in> high_mem_phy_add r }"

(*
definition
  vas_mapped_by_global_mappings' :: "p_state \<Rightarrow> 32 word set"
where
  "vas_mapped_by_global_mappings' s \<equiv> {va. root s r+ pd_idx_offset va \<in> high_mem_phy_add (root s) }"

lemma
  "vas_mapped_by_global_mappings (root s) = vas_mapped_by_global_mappings' s"
  by (clarsimp simp: vas_mapped_by_global_mappings'_def vas_mapped_by_global_mappings_def)
*)


definition
  vas_mapped_to_global_mappings :: "heap \<Rightarrow> paddr \<Rightarrow> 32 word set"
where
  "vas_mapped_to_global_mappings h r  \<equiv> {va. r r+ pd_idx_offset va \<in> high_mem_phy_add r \<and> 
                                           ptable_trace' h r (Addr va) \<subseteq> high_mem_phy_add r}"


(*
definition
  vas_mapped_to_global_mappings' :: "p_state \<Rightarrow> 32 word set"
where
  "vas_mapped_to_global_mappings' s \<equiv> {va. root s r+ pd_idx_offset va \<in> high_mem_phy_add (root s) \<and> 
                                           ptable_trace' (heap s) (root s) (Addr va) \<subseteq> high_mem_phy_add (root s)}"

lemma
  "vas_mapped_to_global_mappings (heap s) (root s) = vas_mapped_to_global_mappings' s"
  by (clarsimp simp: vas_mapped_to_global_mappings_def vas_mapped_to_global_mappings'_def)
*)


definition                   
  kernel_safe_region :: "p_state \<Rightarrow> 32 word set"
where
  "kernel_safe_region s = vas_mapped_by_global_mappings (root s) - 
                          vas_mapped_to_global_mappings (heap s) (root s)"



(*  we have to see the global mappings of the inactive processes, from the root log  *)

(* assuming that kernel\global mappings are physically copied to the high memory of all  *)

(* we can also change ptable_lift' here *)

thm global_mappings_def

definition
  global_mappings_of_all_processes :: "p_state  \<Rightarrow> bool"
where
  "global_mappings_of_all_processes s  \<equiv> \<forall>rt\<in>root_log s. global_mappings (heap s) rt"



(*definition
  global_mappings_of_all_processes' :: "p_state  \<Rightarrow> bool"
where
  "global_mappings_of_all_processes' s  \<equiv> \<forall>rt\<in>root_log s. \<forall>va. rt r+ pd_idx_offset va \<in> high_mem_phy_add rt \<longrightarrow>
                         (\<exists>p perms. get_pde' (heap s) rt (Addr va) = Some (SectionPDE p perms) \<and> \<not>user_perms perms ) \<and>
        ptable_lift_m (heap s) rt Kernel (Addr va)  =  Some (Addr va r- global_offset) \<and> (Addr va r- global_offset) \<in> kernel_phy_mem"


lemma
  "global_mappings_of_all_processes s = global_mappings_of_all_processes' s"
  by (clarsimp simp: global_mappings_of_all_processes_def global_mappings_of_all_processes'_def global_mappings_def)
*)

(* can it be possible *)

definition
  vas_of_current_state_mapped_to_global_mappings_of_all_processes :: "p_state \<Rightarrow> 32 word set"
where
  "vas_of_current_state_mapped_to_global_mappings_of_all_processes s = {va\<in>vas_mapped_by_global_mappings (root s). 
                                                                         ptable_trace' (heap s) (root s) (Addr va) \<subseteq> \<Union>(high_mem_phy_add ` root_log s)}"


definition                   
  kernel_safe_region' :: "p_state \<Rightarrow> 32 word set"
where
  "kernel_safe_region' s = vas_mapped_by_global_mappings (root s) - vas_of_current_state_mapped_to_global_mappings_of_all_processes s"


(* the actual kernel safe set is the global mappings addresses removed *)


(* set of all the virtual addresses that are translated by the current kernel mappings 
      and happen to fall  in the global mapping of other processes *)


(*  not being use for the time being, shift them to the memory model *)

lemma generic_thm0' [simp]:
  "\<exists>rt. root s = rt \<and> mode s = Kernel \<and>  rt \<in> root_log s \<and>   global_mappings_of_all_processes s  \<Longrightarrow>
        \<forall>va\<in>kernel_safe_region' s.  ptable_lift' (heap s) (root s) (Addr va) = Some (Addr va r- global_offset)"
  by (clarsimp simp:  global_mappings_of_all_processes_def kernel_safe_region'_def vas_mapped_by_global_mappings_def global_mappings_def
    vas_of_current_state_mapped_to_global_mappings_of_all_processes_def ) 

lemma generic_thm0:
  "\<lbrakk>\<exists>rt. root s = rt \<and> rt  \<in> root_log s ;
                        global_mappings_of_all_processes s;  va \<in> kernel_safe_region' s\<rbrakk> \<Longrightarrow> ptable_lift_m (heap s) (root s) Kernel (Addr va) = Some (Addr va r- global_offset) "
  by (clarsimp simp:  global_mappings_of_all_processes_def kernel_safe_region'_def vas_mapped_by_global_mappings_def global_mappings_def)


lemma generic_thm:
  "\<lbrakk>\<exists>rt. root s = rt \<and> rt  \<in> root_log s ;
                        global_mappings_of_all_processes s ; va \<in> kernel_safe_region' s\<rbrakk> \<Longrightarrow> 
         \<exists>p perm. decode_heap_pde' (heap s) (root s r+ (vaddr_pd_index va << 2)) =  Some (SectionPDE p perm)"
  apply (clarsimp simp: kernel_safe_region'_def vas_mapped_by_global_mappings_def global_mappings_of_all_processes_def pd_idx_offset_def get_pde'_def global_mappings_def)
  apply force
done


lemma  generic_thm1:
  " \<lbrakk>\<exists>rt. root s = rt \<and> rt  \<in> root_log s ;
                        global_mappings_of_all_processes s ; vp' \<in> kernel_safe_region' s; vp \<in> kernel_safe_region' s\<rbrakk> \<Longrightarrow> Addr (vp' - global_offset) \<notin> ptable_trace' (heap s) (root s) (Addr vp)"
  apply (frule_tac va = vp in  generic_thm [rotated, rotated])
   apply (clarsimp simp:) 
  apply (clarsimp simp: ptable_trace'_def kernel_safe_region'_def vas_mapped_by_global_mappings_def vas_of_current_state_mapped_to_global_mappings_of_all_processes_def pd_idx_offset_def)+ 
   apply force
done


lemma  generic_thm3:
  " \<lbrakk>\<exists>rt. root s = rt \<and> mode s = Kernel \<and> rt  \<in> root_log s \<and>  global_mappings_of_all_processes s; vp' \<in> kernel_safe_region' s; vp \<in> kernel_safe_region' s\<rbrakk> \<Longrightarrow> 
       Addr (vp' - global_offset) \<notin> ptable_trace' (heap s) (root s) (Addr vp)"
  apply (frule_tac va = vp in  generic_thm [rotated , rotated])
   apply (clarsimp simp: ) apply clarsimp
  apply(clarsimp simp:  ptable_trace'_def kernel_safe_region'_def vas_mapped_by_global_mappings_def vas_of_current_state_mapped_to_global_mappings_of_all_processes_def pd_idx_offset_def)+ apply force
done


lemma generic_thm4:
  "\<lbrakk>\<exists>rt. root s = rt \<and> mode s = Kernel \<and> rt  \<in> root_log s \<and>  global_mappings_of_all_processes s ; vp' \<in> kernel_safe_region' s; vp \<in> kernel_safe_region' s \<rbrakk> \<Longrightarrow>
     ptable_lift_m (heap s(Addr vp' r- global_offset \<mapsto> x)) (root s)  (mode s) (Addr vp) =  ptable_lift_m  (heap s)  (root s)  (mode s) (Addr vp)"
  apply (clarsimp simp: generic_thm0')
  apply (subgoal_tac "Addr (vp' - global_offset) \<notin> ptable_trace' (heap s) (root s) (Addr vp)")
   apply (frule_tac pa = "Addr (vp - global_offset)" and v = x in ptable_lift_preserved' ; clarsimp simp: generic_thm0')
  by (clarsimp simp: generic_thm3)


(* have a \<Rightarrow> b thing in the next files, for later, or for now?
   it will make things easier *)



end