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

lemma [simp]:
  "roots (s \<lparr>heap := h , global_set := gs\<rparr>) = roots (s \<lparr>heap := h\<rparr>)"
  by (clarsimp simp: root_log_def root_map_def map_of_set_def  root_set_def roots_def)


lemma [simp]:
  "root_log (s \<lparr>heap := h , global_set := gd\<rparr>) = root_log (s \<lparr>heap := h\<rparr>)"
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
           (\<forall>r a. root_map s r = Some a  \<and> a \<notin> S \<union> {asid s}  \<longrightarrow> 
                   (fst(ptable_snapshot s a) = {} \<and>
                   ptable_comp (snd (ptable_snapshot s a)) (pt_walk_pair a (heap s) r) = {})) \<and>

        (\<forall>r a. r \<in> roots s \<longrightarrow> (global_set s \<inter> 
             (fst (ptable_snapshot s a) \<union> 
            ptable_comp (snd (ptable_snapshot s a)) (pt_walk_pair a (heap s) r)) = {})  )"




lemma asids_consistent_def':
  "asids_consistent S s \<equiv>
            (\<forall>r a. let is = fst(ptable_snapshot s a) ; snp_pt = snd (ptable_snapshot s a); 
                     ptwalk = pt_walk_pair a (heap s) r in 
         (root_map s r = Some a  \<and> a \<notin> S \<union> {asid s}  \<longrightarrow> 
                   (is  = {} \<and>
                   ptable_comp snp_pt ptwalk = {}) ) ) \<and>

        (\<forall>r a. let is = fst(ptable_snapshot s a) ; snp_pt = snd (ptable_snapshot s a) ;
                  ptwalk = pt_walk_pair a (heap s) r in 
           (r \<in> roots s \<longrightarrow> (global_set s \<inter> 
             (is \<union> 
            ptable_comp snp_pt ptwalk) = {})  ))"
  by (clarsimp simp: asids_consistent_def)


end