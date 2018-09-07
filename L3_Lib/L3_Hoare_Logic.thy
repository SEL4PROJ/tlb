theory L3_Hoare_Logic
imports L3_Lib
   "~/verification/l4v/lib/Apply_Trace_Cmd" 
  "~/verification/l4v/lib/Monad_WP/wp/WP"
  "~/verification/l4v/lib/Monad_WP/wp/WPC"
  "~/verification/l4v/lib/Monad_WP/wp/WPFix"
  "~/verification/l4v/lib/Monad_WP/Strengthen"
  "~/verification/l4v/lib/Simp_No_Conditional"
       
begin

(* Wrap up the standard usage pattern of wp/wpc/simp into its own command: *)
method wpsimp uses wp wp_del simp simp_del split split_del cong =
  ((determ \<open>wpfix | wp add: wp del: wp_del | wpc |
            clarsimp_no_cond simp: simp simp del: simp_del split: split split del: split_del cong: cong |
            clarsimp simp: simp simp del: simp_del split: split split del: split_del cong: cong\<close>)+)[1]


definition 
  l3_valid ::  "('s \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> 'r \<times> 's) \<Rightarrow> ('r \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> bool"
  ("\<lbrace>_\<rbrace> _ \<lbrace>_\<rbrace>")
where 
  "\<lbrace>P\<rbrace> f \<lbrace>P'\<rbrace> \<equiv> \<forall>s s' r. f s = (r, s') \<longrightarrow> P s \<longrightarrow> P' r s'"


lemma l3_valid_weak_pre[wp_pre]:
  "\<lbrakk> l3_valid P f Q; (\<And>s . P' s \<Longrightarrow> P s) \<rbrakk> \<Longrightarrow> l3_valid P' f Q"
  by (simp add: l3_valid_def)

context strengthen_implementation begin

lemma strengthen_hoare [strg]:
  "(\<And>r s. st F (\<longrightarrow>) (Q r s) (R r s))
    \<Longrightarrow> st F (\<longrightarrow>) (\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>) (\<lbrace>P\<rbrace> f \<lbrace>R\<rbrace>)"
  by (cases F, auto simp: l3_valid_def)

lemma wpfix_strengthen_hoare:
  "(\<And>s. st (\<not> F) (\<longrightarrow>) (P s) (P' s))
    \<Longrightarrow> (\<And>r s. st F (\<longrightarrow>) (Q r s) (Q' r s))
    \<Longrightarrow> st F (\<longrightarrow>) (\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>) (\<lbrace>P'\<rbrace> f \<lbrace>Q'\<rbrace>)"
  by (cases F, auto simp: l3_valid_def)

end

declare strengthen_implementation.wpfix_strengthen_hoare[wp_fix_strgs]

lemma wpc_helper_valid:
  "\<lbrace>Q\<rbrace> g \<lbrace>S\<rbrace> \<Longrightarrow> wpc_helper (P, P') (Q, Q') \<lbrace>P\<rbrace> g \<lbrace>S\<rbrace>"
  by (clarsimp simp: wpc_helper_def elim!: l3_valid_weak_pre)

wpc_setup "\<lambda>m. \<lbrace>P\<rbrace> m \<lbrace>Q\<rbrace>" wpc_helper_valid

lemma l3_valid_return[wp]:
  "l3_valid (\<lambda>s. P () s)  (return ()) P"
  by (clarsimp simp: l3_valid_def return_def)

lemma l3_valid_return'[wp]:
  "l3_valid (\<lambda>s. P f s)  (Pair f) P"
  by (clarsimp simp: l3_valid_def)

lemma l3_valid_bind_weak[wp_split]:
  "\<lbrakk> \<And>r. l3_valid (P' r) (g r) Q; l3_valid P f P' \<rbrakk> \<Longrightarrow> l3_valid P (bind f g) Q"
  by (simp add: l3_valid_def bind_def split: prod.splits)

lemma read_state_weak[wp]:
  "l3_valid (\<lambda>s. P (f s) s)  (read_state f) P"
  by (clarsimp simp: l3_valid_def read_state_def)

lemma update_state_weak[wp]:
  "l3_valid (\<lambda>s. \<forall>r. P r (f s)) (update_state f) P"
  by (clarsimp simp: l3_valid_def update_state_def)

lemma extend_state_weak[wp]:
  "\<lbrakk> l3_valid P f (\<lambda>r s. Q r (snd s)) \<rbrakk> \<Longrightarrow> l3_valid (\<lambda>s. P (v,s)) (extend_state v f) Q"
  apply (clarsimp simp: l3_valid_def extend_state_def )
   by (fastforce split: prod.splits)


lemma trim_state_weak[wp]:
  " \<lbrakk>\<And>s'. l3_valid (P s') f  (\<lambda>r s.  Q r (s', s) ) \<rbrakk> \<Longrightarrow> l3_valid (\<lambda>s. P (fst s) (snd s)) (trim_state f) Q"
  apply (clarsimp simp: l3_valid_def trim_state_def)
   by (fastforce split: prod.splits)

lemma l3_valid_conj_post[wp_comb]:
 "\<lbrakk>l3_valid P  f Q; l3_valid P  f R \<rbrakk> \<Longrightarrow> 
       l3_valid P f (\<lambda>r s. Q r s \<and> R r s)"
  by (simp add: l3_valid_def)

lemma l3_valid_if_else[wp]:
  "\<lbrakk> b \<Longrightarrow> l3_valid T f Q; \<not>b \<Longrightarrow> l3_valid F g Q \<rbrakk> \<Longrightarrow> 
     l3_valid (if b then T else F) (\<lambda>s. if b then f s else g s) Q"
  by (clarsimp simp: l3_valid_def split: if_split_asm)

lemma l3_valid_if_else'[wp]:
  "\<lbrakk> b \<Longrightarrow> l3_valid T  f Q; \<not>b \<Longrightarrow> l3_valid F  g Q \<rbrakk> \<Longrightarrow> 
     l3_valid (if b then T else F) (if b then f else g) Q"
  by (clarsimp simp: l3_valid_def split: if_split_asm)


lemma l3_valid_if_else'':
  "\<lbrakk> \<And>s. b s \<Longrightarrow> l3_valid T f Q; \<And>s. \<not>b s \<Longrightarrow> l3_valid F g Q \<rbrakk> \<Longrightarrow> 
     l3_valid (\<lambda>s. if b s then T s else F s) (\<lambda>s. if b s then f s else g s) Q"
  by (clarsimp simp: l3_valid_def split: if_split_asm)

lemma l3_valid_return''[wp]:
  "l3_valid (\<lambda>s. P f s)  (return f) P"
  by (clarsimp simp: l3_valid_def return_def)

end