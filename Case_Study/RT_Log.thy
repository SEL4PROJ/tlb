theory RT_Log
imports RT_Map
        

begin

(*
consts root_log_low :: "paddr"

consts root_log_high :: "paddr"


definition
  "root_log_fp = map Addr [addr_val root_log_low .e. addr_val root_log_high]"

definition
  root_log' :: "p_state \<Rightarrow> paddr list"
where
  "root_log' s  =  map (Addr o the o heap s) root_log_fp"
*)


definition
  root_log :: "p_state \<Rightarrow> paddr set"
where
  "root_log s  = {r. \<exists>a. root_map s r = Some a}"




lemma [simp]:
  "root_log s = root_log (s \<lparr>incon_set := is\<rparr>)"
  by (clarsimp simp: root_log_def root_map_def map_of_set_def  root_set_def)

lemma [simp]:
  "root_log (s \<lparr>heap := h , incon_set := is\<rparr>) = root_log (s \<lparr>heap := h\<rparr>)"
  by (clarsimp simp: root_log_def root_map_def map_of_set_def  root_set_def)

(*
lemma  rootI:
  "p \<notin> set root_log_fp \<Longrightarrow> root_log (s \<lparr>heap := heap s (p \<mapsto> v1)\<rparr>) = root_log s"
  by (clarsimp simp: root_log_def root_map_def map_of_set_def  root_set_def)


lemma  rootI1:
  "\<lbrakk>p \<notin> set root_log_fp; p1 \<notin> set root_log_fp \<rbrakk> \<Longrightarrow> 
    root_log (s \<lparr>heap := heap s (p \<mapsto> v1 , p1 \<mapsto> v2)\<rparr>) = root_log s"
  by (auto simp: root_log_def)

*)

(* assumption of non-sharing address space of the processes, pages can be shared, but even 
   then every process will have its own  page table entry *)


definition
  non_overlapping_defined_page_tables :: "p_state \<Rightarrow> bool"
where
  "non_overlapping_defined_page_tables s \<equiv> 
                     \<forall>x y. x\<in>(root_log s) \<and> y \<in> (root_log s) \<and>
                              x\<noteq>y \<longrightarrow> \<Union>(ptable_trace' (heap s) x ` UNIV) \<inter> \<Union>(ptable_trace' (heap s) y ` UNIV) = {}"

lemma 
  "root_map s r = Some a  \<longrightarrow> r \<in> root_log s"
  by (clarsimp simp: root_log_def)


definition
  "asids_consistent S s \<equiv>  
           (\<forall> r a. root_map s r = Some a  \<longrightarrow> a \<notin> S \<union> {asid s}  \<longrightarrow> 
                  (\<forall>v. (ptable_snapshot s) a v \<noteq> Incon \<and> ((ptable_snapshot s) a v = Miss \<or> 
                                 (ptable_snapshot s) a v = Hit (pt_walk a (heap s) r v) )))"



end