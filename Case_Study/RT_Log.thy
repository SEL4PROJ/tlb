theory RT_Log
imports RT_Map
begin

(* The roots that map an ASID in the root_map; slightly obscure to get a list *)
definition
  root_log :: "p_state \<Rightarrow> paddr list"
where
  "root_log s = map Addr (filter (\<lambda>r. root_map s (Addr r) \<noteq> None) enum)"

definition
  "roots s = set (root_log s)"

(* More natural definition *)
lemma roots_def':
  "roots s = {r. \<exists>a. root_map s r = Some a}"
  by (auto simp: root_log_def roots_def image_iff) (metis Addr_addr_val)


lemma [simp]:
  "roots s = roots (s \<lparr>incon_set := is\<rparr>)"
  by (clarsimp simp: root_log_def root_map_def map_of_set_def root_set_def roots_def)

lemma [simp]:
  "roots (s \<lparr>heap := h , incon_set := is\<rparr>) = roots (s \<lparr>heap := h\<rparr>)"
  by (clarsimp simp: root_log_def root_map_def map_of_set_def  root_set_def roots_def)


(* assumption of non-sharing address space of the processes, pages can be shared, but even 
   then every process will have its own  page table entry *)


definition
  non_overlapping_defined_page_tables :: "p_state \<Rightarrow> bool"
where
  "non_overlapping_defined_page_tables s \<equiv> 
                     \<forall>x y. x\<in>roots s \<and> y \<in> roots s \<and>
                              x\<noteq>y \<longrightarrow> \<Union>(ptable_trace' (heap s) x ` UNIV) \<inter> \<Union>(ptable_trace' (heap s) y ` UNIV) = {}"

definition
  "asids_consistent S s \<equiv>  
            \<forall>r a. root_map s r = Some a  \<longrightarrow> a \<notin> S \<union> {asid s}  \<longrightarrow> 
                  (\<forall>v. ptable_snapshot s a v = Miss \<or> 
                       ptable_snapshot s a v = Hit (pt_walk a (heap s) r v))"

end