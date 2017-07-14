theory RT_Map
                  
imports Con_set
        

begin               

(* vmroot table  *)

(*   we have to keep the record of ASIDs assgined to the particular roots. roots are of 32 bits, and asids are 8 bits *)


definition
  partial_inj :: "('a \<Rightarrow> 'b option ) \<Rightarrow> bool"
where
  "partial_inj f \<equiv> \<forall>x. \<forall>y. if   x = y 
                           then f x = f y
                           else if f x = f y
                                then f x = None \<and> f y = None
                                else \<exists>a1 a2. a1 \<noteq> a2 \<and> f x = a1 \<and> f y = a2"

lemma "partial_inj f = (\<forall>x y. x \<noteq> y \<longrightarrow> f x \<noteq> f y \<or> f x = None \<and> f y = None)"
  by (auto simp add: partial_inj_def)

(* update the logic semantics to assign the asids for the root *)

(*  boot conditions *)


lemma aval_state_rt_map_eq[simp]:
  "(aval e (s\<lparr>root_map := root_map s(Addr r \<mapsto> a)\<rparr>) = Some v) = (aval e s = Some v)"
  by (induct e arbitrary: v; clarsimp split: option.splits; fastforce)



lemma  rt_map_none_partial_inj:
  "(\<forall>rt. root_map s rt = None) \<Longrightarrow> partial_inj (root_map s)"
  by (clarsimp simp: partial_inj_def)



lemma rt_map_update_none_partial:
  "\<Turnstile> \<lbrace> \<lambda>s. mode s = Kernel \<and>  aval rt s = Some v \<and> (\<forall>rt. root_map s rt = None)\<rbrace>
                UpdateRTMap rt a  \<lbrace>\<lambda>s. partial_inj (root_map s)\<rbrace>"
  apply vcg
  by (clarsimp simp: partial_inj_def)


lemma rt_map_update_partial:   (* for vcg *)
  "\<Turnstile> \<lbrace> \<lambda>s. mode s = Kernel \<and> 
      aval rt s = Some v \<and> root_map s (Addr v) = None \<and> (\<forall>rt. root_map s rt \<noteq> Some a) \<and> partial_inj (root_map s) \<rbrace>
                UpdateRTMap rt a  \<lbrace>\<lambda>s. partial_inj (root_map s)\<rbrace>"
  apply vcg
  unfolding partial_inj_def
  by (metis fun_upd_apply)

lemma rt_map_update_partial':
  "\<Turnstile> \<lbrace> \<lambda>s. mode s = Kernel \<and> aval rt s = Some v \<and>
           root_map s (Addr v) = None \<and> (\<forall>rt. root_map s rt \<noteq> Some a) \<and> partial_inj (root_map s) \<rbrace>
                UpdateRTMap rt a  \<lbrace>\<lambda>s. partial_inj (root_map s) \<and> root_map s (Addr v) = Some a\<rbrace>"
  apply vcg
  unfolding partial_inj_def
  by (metis fun_upd_apply)
  

lemma rt_map_update_not_partial:
  "\<Turnstile> \<lbrace> \<lambda>s. mode s = Kernel \<and> aval rt s = Some v \<and>
           root_map s (Addr v) = None \<and> (\<exists>rt. rt \<noteq> Addr v \<and> root_map s rt = Some a) \<and> partial_inj (root_map s) \<rbrace>
                UpdateRTMap rt a  \<lbrace>\<lambda>s. \<not>partial_inj (root_map s)\<rbrace>"
  apply vcg
  (* should be solved from force *)
  unfolding partial_inj_def
  apply (drule_tac x = "rta" in spec)
  apply (drule_tac x = "rta" in spec)
  apply (drule_tac x = "Addr v" in spec)
  apply (drule_tac x = "Addr v" in spec)
  apply clarsimp
done



definition
  set_of_assigned_asids :: "rt_map_t \<Rightarrow> asid set"
where
  "set_of_assigned_asids rt_map \<equiv> {a. \<exists>x. rt_map x = Some a}" term "ran rtmap"

(* have some lemmas about partial_injectivity *)

lemma
  "\<lbrakk>a1 \<in> set_of_assigned_asids rt_map\<rbrakk> \<Longrightarrow> \<exists>x. rt_map x = Some a1"
  apply (clarsimp simp: set_of_assigned_asids_def)
done


lemma part_inj_root_map_different_asids:
  "\<lbrakk>a \<in> set_of_assigned_asids rt_map ; partial_inj rt_map\<rbrakk> \<Longrightarrow> \<exists>x. rt_map x = Some a \<and> (\<forall>y. x \<noteq> y \<longrightarrow> rt_map y \<noteq> Some a)"
  apply (clarsimp simp: set_of_assigned_asids_def)
  apply (rule_tac x = x in exI) 
  apply simp
  apply (rule allI)
  apply (rule impI)
  unfolding partial_inj_def
  apply (erule_tac x = x in allE)
  apply (erule_tac x = y in allE)
  by auto


definition  "asid_va_set (a::asid) \<equiv> (\<lambda>va::32 word. (a , va)) ` UNIV"   term "{a} \<times> UNIV" 

definition "asids_va_set rt_map   \<equiv> \<Union>((\<lambda>x. asid_va_set x) ` set_of_assigned_asids rt_map)"
                                                                         
definition "assinged_asids_consistent rt_map iset  \<equiv> asids_va_set rt_map \<inter> iset = {}"



(*  trivial *)
lemma rt_map_update_boot_incon_set:
  "\<Turnstile> \<lbrace> \<lambda>s. mode s = Kernel \<and> (\<exists>v. aval rt s = Some v) \<and> incon_set s = {} \<and> (\<forall>rt. root_map s rt = None)\<rbrace>
                UpdateRTMap rt a  \<lbrace>\<lambda>s. partial_inj (root_map s) \<and> asids_va_set (root_map s) \<inter> incon_set s = {} \<rbrace>"
  apply vcg
  by (clarsimp simp: partial_inj_def)


(*  trivial *)
lemma rt_map_update_boot_incon_set:
  "\<Turnstile> \<lbrace> \<lambda>s. mode s = Kernel \<and> (\<exists>v. aval rt s = Some v) \<and>  asids_va_set (root_map s) \<inter> incon_set s = {} \<and> (\<forall>rt. root_map s rt = None)\<rbrace>
                UpdateRTMap rt a  \<lbrace>\<lambda>s. partial_inj (root_map s) \<and> asids_va_set (root_map s) \<inter> incon_set s = {} \<rbrace>"
  apply vcg
  apply (clarsimp simp: partial_inj_def asids_va_set_def set_of_assigned_asids_def asid_va_set_def)
oops











end
