theory RT_Map
                  
imports Con_Set
        

begin               

(* vmroot table  *)

(*   we have to keep the record of ASIDs assgined to the particular roots. roots are of 32 bits, and asids are 8 bits *)


definition
  partial_inj :: "('a \<Rightarrow> 'b option ) \<Rightarrow> bool"
where
  "partial_inj f \<equiv>  (\<forall>x y. x \<noteq> y \<longrightarrow> f x \<noteq> f y \<or> f x = None \<and> f y = None)"


lemma  rt_map_none_partial_inj:
  "(\<forall>rt. root_map s rt = None) \<Longrightarrow> partial_inj (root_map s)"
  by (clarsimp simp: partial_inj_def)

lemma rt_map_update_none_partial:
  "\<Turnstile> \<lbrace> \<lambda>s. mode s = Kernel \<and>  aval rt s = Some v \<and> (\<forall>rt. root_map s rt = None)\<rbrace>
                UpdateRTMap rt a  \<lbrace>\<lambda>s. partial_inj (root_map s)\<rbrace>"
  apply vcgm
  by (clarsimp simp: partial_inj_def)


lemma rt_map_update_partial:   (* for vcgm *)
  "\<Turnstile> \<lbrace> \<lambda>s. mode s = Kernel \<and> 
      aval rt s = Some v \<and> root_map s (Addr v) = None \<and> (\<forall>rt. root_map s rt \<noteq> Some a) \<and> partial_inj (root_map s) \<rbrace>
                UpdateRTMap rt a  \<lbrace>\<lambda>s. partial_inj (root_map s)\<rbrace>"
  apply vcgm
  unfolding partial_inj_def
  by (metis fun_upd_apply)

lemma rt_map_update_partial':
  "\<Turnstile> \<lbrace> \<lambda>s. mode s = Kernel \<and> aval rt s = Some v \<and>
           root_map s (Addr v) = None \<and> (\<forall>rt. root_map s rt \<noteq> Some a) \<and> partial_inj (root_map s) \<rbrace>
                UpdateRTMap rt a  \<lbrace>\<lambda>s. partial_inj (root_map s) \<and> root_map s (Addr v) = Some a\<rbrace>"
  apply vcgm
  unfolding partial_inj_def
  by (metis fun_upd_apply)
  

lemma rt_map_update_not_partial:
  "\<Turnstile> \<lbrace> \<lambda>s. mode s = Kernel \<and> aval rt s = Some v \<and>
           root_map s (Addr v) = None \<and> (\<exists>rt. rt \<noteq> Addr v \<and> root_map s rt = Some a) \<and> partial_inj (root_map s) \<rbrace>
                UpdateRTMap rt a  \<lbrace>\<lambda>s. \<not>partial_inj (root_map s)\<rbrace>"
  apply vcgm
  (* should be solved from force *)
  unfolding partial_inj_def
  apply (drule_tac x = "rta" in spec)
  apply (drule_tac x = "rta" in spec)
  apply (drule_tac x = "Addr v" in spec)
  apply (drule_tac x = "Addr v" in spec)
  apply clarsimp
done



lemma
  "\<lbrakk>a1 \<in> ran rt_map\<rbrakk> \<Longrightarrow> \<exists>x. rt_map x = Some a1"
  apply (clarsimp simp:  ran_def)
done


lemma part_inj_root_map_different_asids:
  "\<lbrakk>a \<in> ran rt_map ; partial_inj rt_map\<rbrakk> \<Longrightarrow> \<exists>x. rt_map x = Some a \<and> (\<forall>y. x \<noteq> y \<longrightarrow> rt_map y \<noteq> Some a)"
  apply (clarsimp simp: ran_def partial_inj_def)
  by force


definition "assigned_asid_va_map rt_map   \<equiv> \<Union>((\<lambda>x. {x} \<times> UNIV) ` ran rt_map)"

definition "assigned_asids_consistent rt_map iset  \<equiv> assigned_asid_va_map rt_map \<inter> iset = {}"


(*definition
  set_of_assigned_asids :: "rt_map_t \<Rightarrow> asid set"
where
  "set_of_assigned_asids rt_map \<equiv> ran rt_map" *)    

                                                                         
(*definition  "asid_va_set (a::asid) \<equiv> {a} \<times> UNIV" *)

(*definition "assinged_asids_consistent rt_map iset  \<equiv> asids_va_set rt_map \<inter> iset = {}"*)


(* trivial *)
lemma rt_map_update_boot_incon_set:
  "\<Turnstile> \<lbrace> \<lambda>s. mode s = Kernel \<and> (\<exists>v. aval rt s = Some v) \<and> incon_set s = {} \<and> (\<forall>rt. root_map s rt = None)\<rbrace>
                UpdateRTMap rt a  \<lbrace>\<lambda>s. partial_inj (root_map s) \<and> assigned_asid_va_map  (root_map s) \<inter> incon_set s = {} \<rbrace>"
  apply vcgm
  by (clarsimp simp: partial_inj_def)






end
