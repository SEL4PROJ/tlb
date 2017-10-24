theory RT_Log
imports RT_Map
        

begin


consts root_log_low :: "paddr"

consts root_log_high :: "paddr"




definition
  root_log :: "p_state \<Rightarrow> paddr set"
where
  "root_log s  =  Addr ` the ` (heap s) ` {root_log_low .. root_log_high}"


lemma [simp]:
  "root_log s = root_log (s \<lparr>incon_set := is\<rparr>)"
  by (clarsimp simp: root_log_def)

lemma [simp]:
  "root_log (s \<lparr>heap := h , incon_set := is\<rparr>) = root_log (s \<lparr>heap := h\<rparr>)"
  by (clarsimp simp: root_log_def)

lemma  rootI:
  "p \<notin>   {root_log_low .. root_log_high} \<Longrightarrow> root_log (s \<lparr>heap := heap s (p \<mapsto> v1)\<rparr>) = root_log s"
  by (clarsimp simp: root_log_def)


lemma  rootI1:
  "\<lbrakk>p \<notin>   {root_log_low .. root_log_high} ; p1 \<notin>   {root_log_low .. root_log_high} \<rbrakk> \<Longrightarrow> 
    root_log (s \<lparr>heap := heap s (p \<mapsto> v1 , p1 \<mapsto> v2)\<rparr>) = root_log s"
  by (clarsimp simp: root_log_def)
 
(* assumption of non-sharing address space of the processes, pages can be shared, but even 
   then every process will have its own  page table entry *)


definition
  non_overlapping_defined_page_tables :: "p_state \<Rightarrow> bool"
where
  "non_overlapping_defined_page_tables s \<equiv> 
                     \<forall>x y. x\<in>(root_log s) \<and> y\<in>(root_log s) \<and>
                              x\<noteq>y \<longrightarrow> \<Union>(ptable_trace' (heap s) x ` UNIV) \<inter> \<Union>(ptable_trace' (heap s) y ` UNIV) = {}"




end