theory RT_Map

imports Safe_Set


begin

(* Layout of root to asid map in kernel memory *)



consts rtmap_low :: "paddr"
consts rtmap_high :: "paddr"

definition
  "root_map_area = {rtmap_low .. rtmap_high}"

definition
  rt_int :: "(paddr \<times> paddr) set"
where
  "rt_int = (root_map_area \<times> root_map_area) \<inter> ((\<lambda>x. (Addr (x * 2), Addr (x * 2 + 1))) ` UNIV)"

definition
  root_set :: "p_state \<Rightarrow> (paddr \<times> asid option) set"
where
  "root_set s = (\<lambda>(x,y). (Addr (the (heap s x)) , map_option ucast  (heap s y))) ` rt_int"


definition
  map_of_set :: "('a \<times> 'b option) set \<Rightarrow> 'a \<Rightarrow> 'b option"
where
  "map_of_set S \<equiv> \<lambda>x. if x \<in> fst ` S then  (SOME y. (x,y) \<in> S) else None"


definition
  root_map :: "p_state \<Rightarrow> (paddr \<rightharpoonup> 8 word)"
where
  "root_map s = map_of_set (root_set s )"




lemma [simp]:
  "root_map (s\<lparr>heap := h, incon_set := is, mode := m\<rparr>) =  root_map (s\<lparr>heap := h\<rparr>)"
  by (clarsimp simp: root_map_def  map_of_set_def  root_set_def)

lemma [simp]:
  "root_map (s\<lparr>heap := h, global_set := gs\<rparr>) =  root_map (s\<lparr>heap := h\<rparr>)"
  by (clarsimp simp: root_map_def  map_of_set_def  root_set_def)

lemma root_map_rt_int:
  "\<lbrakk> p \<notin> root_map_area; (x, y) \<in> rt_int \<rbrakk> \<Longrightarrow> p \<noteq> x \<and> p \<noteq> y"
  by (fastforce simp: rt_int_def)

lemma root_set_not_elem: 
  "p \<notin> root_map_area  \<Longrightarrow>  root_set s  = root_set (s\<lparr>heap := heap s(p \<mapsto> v)\<rparr>)"  
  apply safe
   apply (clarsimp simp: root_set_def image_iff split_def)
   apply (drule (1) root_map_rt_int)
   apply (rule bexI)
    prefer 2
    apply assumption
   apply clarsimp
  apply (clarsimp simp: root_set_def image_iff split_def)
  apply (drule (1) root_map_rt_int)
  apply clarsimp
  by force 


lemma  root_set_up: 
  "root_set s  = root_set (s\<lparr>heap := heap s(p \<mapsto> v)\<rparr>) \<Longrightarrow> 
              root_map s  = root_map (s\<lparr>heap := heap s(p \<mapsto> v)\<rparr>)"
  by (clarsimp simp: root_set_def root_map_def)

lemma  rt_map_simp:
  "p \<notin> root_map_area \<Longrightarrow> 
     root_map s  = root_map (s\<lparr>heap := heap s(p \<mapsto> v)\<rparr>)"
  by (clarsimp simp: root_set_not_elem root_set_up)



lemma [simp]:
  "root_map (s\<lparr>heap := h, incon_set := is\<rparr>) =  root_map (s\<lparr>heap := h\<rparr>)"
  by(clarsimp simp: root_map_def map_of_set_def root_set_def)

 

(* partial injectivity for root_map  *)


definition
  partial_inj :: "('a \<Rightarrow> 'b option ) \<Rightarrow> bool"
where
  "partial_inj f \<equiv>  (\<forall>x y. x \<noteq> y \<longrightarrow> f x \<noteq> f y \<or> f x = None \<and> f y = None)"



lemma  rt_map_none_partial_inj:
  "(\<forall>rt. root_map s rt = None) \<Longrightarrow> partial_inj (root_map s)"
  by (clarsimp simp: partial_inj_def)


lemma part_inj_root_map_different_asids:
  "\<lbrakk>a \<in> ran rt_map ; partial_inj rt_map\<rbrakk> \<Longrightarrow> \<exists>x. rt_map x = Some a \<and> (\<forall>y. x \<noteq> y \<longrightarrow> rt_map y \<noteq> Some a)"
  apply (clarsimp simp: ran_def partial_inj_def)
  by force


end
