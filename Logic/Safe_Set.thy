theory Safe_Set
                  
imports Con_Set
        

begin               


(* notion of safe set  *)


definition
  ptrace_set ::"vaddr set \<Rightarrow> p_state \<Rightarrow> paddr set"
where
  "ptrace_set V s = \<Union>(ptable_trace' (heap s) (root s) ` V) "


definition
  safe_memory :: "vaddr set \<Rightarrow> p_state \<Rightarrow> bool"
where
  "safe_memory V s \<equiv> \<forall>va \<in> V. \<exists>p. ptable_lift_m (heap s) (root s) (mode s) va= Some p \<and>  
                                 p \<notin> ptrace_set V s" 


definition
  safe_set :: "vaddr set \<Rightarrow> p_state \<Rightarrow> bool"
where
  "safe_set V s \<equiv>  (safe_memory V s \<and> con_set V s)"
 

lemma cons_set_preserved:
  "\<lbrakk> \<forall>va\<in>SM. \<exists>p.  ptable_lift_m (heap s) (root s) (mode s) va = Some p \<and> p \<notin> ptrace_set SM s;
          \<forall>va\<in>SM. va \<notin> incon_set s; p \<notin> ptrace_set SM s; va \<in> SM\<rbrakk>  \<Longrightarrow> 
              va \<notin> incon_comp (asid s) (asid s) (heap s) (heap s(p \<mapsto> v)) (root s) (root s)"
  apply (case_tac "mode s")
   apply (drule_tac x = va in bspec ; clarsimp)
   apply (drule_tac x = va in bspec, simp)
   apply (clarsimp simp: incon_comp_def ptable_comp_def entry_leq_def pt_walk_pair_def pdc_walk_def pte_tlb_entry_def  ptrace_set_def)
   apply (drule_tac x = va in bspec , simp)
   apply (clarsimp simp: ptable_trace'_def  Let_def lookup_pde'_def  get_pde'_def decode_heap_pde'_def pte_tlb_entry_def
                        lookup_pte'_def get_pte'_def decode_heap_pte'_def
                   split: option.splits pde.splits pte.splits)
  apply (drule_tac x = va in bspec ; clarsimp)
  apply (frule ptable_lift_m_user)
  apply (drule_tac x = va in bspec , simp)
  apply (clarsimp simp: incon_comp_def ptable_comp_def entry_leq_def pt_walk_pair_def pdc_walk_def pte_tlb_entry_def   ptrace_set_def)
  apply (drule_tac x = va in bspec , simp)
  by (clarsimp simp: ptable_trace'_def  Let_def lookup_pde'_def  get_pde'_def decode_heap_pde'_def pte_tlb_entry_def
                        lookup_pte'_def get_pte'_def decode_heap_pte'_def
                  split: option.splits pde.splits pte.splits)
  

lemma safe_set_preserved:
  "\<Turnstile> \<lbrace> \<lambda>s. safe_set SM s \<and> (\<exists>vp v. aval lval s = Some vp \<and> aval rval s = Some v \<and> Addr vp \<in> SM)\<rbrace>
                lval ::= rval  \<lbrace>\<lambda>s. safe_set SM s \<rbrace>"
  apply vcgm
  apply (rule conjI, clarsimp simp: safe_set_def  con_set_def)
  apply (clarsimp simp: safe_set_def safe_memory_def)
  apply (frule_tac x = "Addr vp" in bspec ; safe)
  apply (rule_tac x = p in exI , simp)
  apply (rule_tac conjI; clarsimp simp: con_set_def cons_set_preserved)
  apply (frule_tac x = "va" in bspec ; safe)
  apply (rule_tac x = pa in exI)
  apply (rule conjI, clarsimp simp: ptrace_set_def)
   apply (drule_tac x = va in bspec ; simp)
   apply (rule ptable_lift_preserved_m ; simp)
  apply (clarsimp simp:  ptrace_set_def)
  apply (drule_tac x = x in bspec ; clarsimp)+
  apply (clarsimp simp: ptable_trace_preserved_m)
done
 

lemma safe_set_preserved':
  " \<Turnstile> \<lbrace>\<lambda>s. safe_set SM s \<and> (\<exists>vp v. aval lval s = Some vp \<and> aval rval s = Some v \<and> Addr vp \<in> SM \<and>
     Q (s\<lparr>heap := heap s(the ( ptable_lift_m (heap s) (root s) (mode s) (Addr vp)) \<mapsto> v), 
            incon_set := incon_set s \<union> incon_comp (asid s) (asid s) (heap s) (heap s(the ( ptable_lift_m (heap s) (root s) (mode s) (Addr vp)) \<mapsto> v)) (root s) (root s) ,
            global_set := global_set s \<union> (\<Union>x\<in>global_entries (ran (pt_walk (asid s) (heap s(the ( ptable_lift_m (heap s) (root s) (mode s) (Addr vp)) \<mapsto> v)) (root s))). range_of x)\<rparr>)) \<rbrace>
                       lval ::= rval \<lbrace>\<lambda>s. safe_set SM s \<rbrace>"
  by (rule weak_pre, rule safe_set_preserved, force)


lemma weak_pre_write:
  "\<Turnstile> \<lbrace> \<lambda>s. safe_set SM s \<and> (\<exists>vp v. aval lval s = Some vp \<and> aval rval s = Some v \<and> Addr vp \<in> SM \<and> 
     Q (s \<lparr> heap := heap s (the (ptable_lift_m (heap s) (root s) (mode s) (Addr vp)) \<mapsto> v),
             incon_set := incon_set s \<union> incon_comp (asid s) (asid s) (heap s) 
   (heap s(the (ptable_lift_m (heap s) (root s) (mode s) (Addr vp)) \<mapsto> v)) (root s) (root s) ,
    global_set := global_set s \<union> (\<Union>x\<in>global_entries (ran (pt_walk (asid s)  (heap s(the (ptable_lift_m (heap s) (root s) (mode s) (Addr vp)) \<mapsto> v)) (root s))). range_of x)\<rparr>)) \<rbrace> 
           lval ::= rval  \<lbrace>Q\<rbrace>"
  apply (vcgm , clarsimp simp: safe_set_def safe_memory_def con_set_def)
  by fastforce
 

lemma hoare_post_conj:
  "\<lbrakk> \<Turnstile> \<lbrace>P\<rbrace> c \<lbrace>Q\<rbrace> ; \<Turnstile> \<lbrace>P\<rbrace> c \<lbrace>S\<rbrace> \<rbrakk>  \<Longrightarrow> \<Turnstile> \<lbrace>P\<rbrace> c \<lbrace>\<lambda>s. Q s \<and> S s\<rbrace>"
  apply (clarsimp simp: hoare_valid_def)
  by blast


lemma weak_pre_write':
  "\<Turnstile> \<lbrace> \<lambda>s. safe_set SM s \<and> (\<exists>vp v. aval lval s = Some vp \<and> aval rval s = Some v \<and> Addr vp \<in> SM \<and> 
     Q (s \<lparr>heap := heap s (the ( ptable_lift_m (heap s) (root s) (mode s) (Addr vp)) \<mapsto> v),
             incon_set := incon_set s \<union> incon_comp (asid s) (asid s) (heap s) (heap s(the (ptable_lift_m (heap s)
                           (root s) (mode s) (Addr vp)) \<mapsto> v)) (root s) (root s) ,
  global_set := global_set s \<union> (\<Union>x\<in>global_entries (ran (pt_walk (asid s)  (heap s(the (ptable_lift_m (heap s)
                           (root s) (mode s) (Addr vp)) \<mapsto> v)) (root s))). range_of x)\<rparr>)) \<rbrace>
             lval ::= rval  \<lbrace>\<lambda>s. safe_set SM s \<and> Q s \<rbrace>"
  by (rule hoare_post_conj, rule safe_set_preserved', rule weak_pre_write)


lemma ptable_trace_global_set:
  "\<forall>x. p \<notin> ptable_trace' h r x \<Longrightarrow> (\<Union>x\<in>global_entries (ran (pt_walk a (h(p \<mapsto> v)) r)). range_of x) =
   (\<Union>x\<in>global_entries (ran (pt_walk a h r)). range_of x)"
  apply safe
   apply clarsimp
   apply (rule_tac x = xa in bexI)
    apply clarsimp
   apply (clarsimp simp: global_entries_def ran_def)
  using pt_walk_pt_trace_upd apply force
  apply (clarsimp simp: global_entries_def ran_def)
  using pt_walk_pt_trace_upd by force




lemma weak_pre_write'_user:
  "\<Turnstile> \<lbrace> \<lambda>s. safe_set SM s \<and> (\<exists>vp v. aval lval s = Some vp \<and> aval rval s = Some v \<and> Addr vp \<in> SM \<and> 
                  (\<forall>v\<in>SM. v \<notin> ptable_mapped (heap s) (root s)) \<and>  global_set s =  (\<Union>x\<in>global_entries (ran (pt_walk (asid s) (heap s) (root s))). range_of x) \<and>
       Q (s \<lparr> heap := heap s (the ( ptable_lift_m (heap s) (root s) (mode s) (Addr vp)) \<mapsto> v) \<rparr> ) ) \<rbrace>
             lval ::= rval  \<lbrace>\<lambda>s. safe_set SM s \<and> Q s \<rbrace>" 
  apply (rule hoare_post_conj)
   apply (rule weak_pre)
    apply (rule safe_set_preserved)
   apply force
  apply (rule weak_pre)
   apply (rule assign_sound)
  apply clarsimp
  apply (clarsimp simp: safe_set_def con_set_def safe_memory_def)
  apply (drule_tac x = "Addr vp" in bspec; clarsimp)
  apply (subgoal_tac "incon_set s = incon_set s \<union> incon_comp (asid s) (asid s) (heap s)
                     (heap s(the (ptable_lift_m (heap s) (root s) (mode s) (Addr vp)) \<mapsto> v)) (root s) (root s) \<and>
                      global_set s = global_set s \<union>  (\<Union>x\<in>global_entries (ran (pt_walk (asid s) (heap s(the (ptable_lift_m (heap s) (root s) (mode s) (Addr vp)) \<mapsto> v))(root s))). range_of x)")
   apply (clarsimp simp: safe_set_def con_set_def safe_memory_def)
   apply (case_tac s)
   apply force
  apply (subgoal_tac "incon_comp (asid s) (asid s) (heap s) (heap s(the (ptable_lift_m (heap s) (root s)
                      (mode s) (Addr vp)) \<mapsto> v)) (root s) (root s)= {}")
   apply clarsimp
  defer
  apply (drule_tac x = "Addr vp" in bspec , clarsimp)
  apply (clarsimp simp: ptable_mapped_def)
  apply (clarsimp simp: ptable_lift_m_implies_ptlift)
   apply (clarsimp simp: ptable_trace_pde_comp)
 apply (drule_tac x = "Addr vp" in bspec , clarsimp)
  apply (clarsimp simp: ptable_mapped_def)
  apply (clarsimp simp: ptable_lift_m_implies_ptlift)
  by (clarsimp simp: ptable_trace_global_set)


 
lemma weak_pre_write'':
  "\<Turnstile> \<lbrace> \<lambda>s. aval lval s = Some vp \<and> aval rval s = Some v \<and> Addr vp \<in> SM \<and> safe_set SM s \<and> 
     Q ((heap s) (the ( ptable_lift_m (heap s) (root s) (mode s) (Addr vp)) \<mapsto> v)) \<rbrace> lval ::= rval  \<lbrace>\<lambda>s. Q (heap s)\<rbrace>"
  by (rule weak_pre , rule_tac Q = "\<lambda>s. Q (heap s)" and SM = SM in  weak_pre_write, clarsimp)




(* safe set in the context switch, not being used
    in the example *)
definition
  SM_user :: "heap \<Rightarrow> paddr \<Rightarrow> vaddr set"
where
  "SM_user h r  \<equiv> {va. \<exists>p. ptable_lift_m h r User va = Some p \<and> p \<notin> \<Union>range (ptable_trace' h r)} "


lemma [simp]:
  "con_set S (s\<lparr>root := rt, asid := a, incon_set := is, mode := m\<rparr>) = con_set S (s\<lparr>asid := a, incon_set := is\<rparr>)"
  by (clarsimp simp: con_set_def)

lemma [simp]:
  "safe_memory S (s\<lparr>root := r, asid := a, incon_set := is, mode := m\<rparr>) = safe_memory S (s\<lparr>root := r,  mode := m\<rparr>)"
   by (clarsimp simp: safe_memory_def ptrace_set_def)

lemma [simp]:
  " safe_memory (SM_user (heap s) (Addr rt)) (s\<lparr>root := Addr rt, mode := User\<rparr>)"
 apply (clarsimp simp: safe_memory_def)
  apply (subst (asm) SM_user_def)
  apply simp
  apply (erule exE)
  apply simp
  apply (clarsimp simp: SM_user_def)
   apply (clarsimp simp: ptrace_set_def)
done


lemma [simp]:
  "safe_memory (SM_user (heap s) (Addr rt))
                 (s\<lparr>root := Addr rt, asid := a, incon_set := is', ptable_snapshot :=  snp',   mode := User\<rparr>)"
 apply (clarsimp simp: safe_memory_def)
  apply (subst (asm) SM_user_def)
  apply simp
  apply (erule exE)
  apply simp
  apply (clarsimp simp: SM_user_def)
   apply (clarsimp simp: ptrace_set_def)
done

lemma [simp]:
  "safe_memory va (s\<lparr>heap := hp , incon_set := iset , mode := m\<rparr>) =  safe_memory va (s\<lparr>heap := hp , mode := m\<rparr>)"
  by (clarsimp simp: safe_memory_def ptrace_set_def)


lemma [simp]:
  "ptrace_set V (s\<lparr>heap := hp, incon_set := iset \<rparr>) = ptrace_set V (s\<lparr>heap := hp\<rparr>)"
 by (clarsimp simp: ptrace_set_def)




end
