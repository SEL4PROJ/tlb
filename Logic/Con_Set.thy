theory Con_Set
                  
imports VCG_Check
        

begin               


definition
  con_set :: "vaddr set \<Rightarrow> p_state \<Rightarrow> bool"
where
  "con_set V s \<equiv>  \<forall>va\<in>V. va \<notin> incon_set s"




lemma [simp]:
  "con_set va (s\<lparr>heap := hp ,  incon_set := iset , mode := m\<rparr>) =  con_set va (s\<lparr>incon_set := iset\<rparr>) "
  by (clarsimp simp: con_set_def)


lemma [simp]:
  "con_set V (s\<lparr>heap := hp, incon_set := iset \<rparr>) = con_set V (s\<lparr>incon_set := iset\<rparr>)"
 by (clarsimp simp: con_set_def)


end