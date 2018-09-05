theory L3_Hoare_Logic
imports L3_Lib
          
begin



definition 
  l3_valid ::  "('s \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> 'r \<times> 's) \<Rightarrow> ('r \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> bool"
where 
  "l3_valid P f P' \<equiv> \<forall>s s' r. f s = (r, s') \<longrightarrow> P s \<longrightarrow> P' r s'"


named_theorems wp_pre

lemma l3_valid_weak_pre[wp_pre]:
  "\<lbrakk> l3_valid P f Q; (\<And>s. P' s \<Longrightarrow> P s) \<rbrakk> \<Longrightarrow> l3_valid P' f Q"
  by (simp add: l3_valid_def)

named_theorems wp

lemma l3_valid_return[wp]:
  "l3_valid (\<lambda>s.  P () s) (return ()) P"
  by (clarsimp simp: l3_valid_def return_def)

lemma l3_valid_return'[wp]:
  "l3_valid (\<lambda>s. P f s) (Pair f) P"
  by (clarsimp simp: l3_valid_def)


lemma l3_valid_bind:
  "l3_valid (\<lambda>s. P (fst ( g (fst (f s)) (snd (f s)))) (snd ( g (fst (f s)) (snd (f s))))) (bind f g) P"
  apply (clarsimp simp: bind_def split_def Let_def)
  by (clarsimp simp: l3_valid_def)

lemma l3_valid_bind_weak[wp]:
  "\<lbrakk> \<And>r. l3_valid (P' r) (g r) Q; l3_valid P f P' \<rbrakk> \<Longrightarrow> l3_valid P (bind f g) Q"
  by (simp add: l3_valid_def bind_def split: prod.splits)


lemma read_state_weak[wp]:
  "l3_valid (\<lambda>s. \<forall>r. P r s) (read_state f) P"
  by (clarsimp simp: l3_valid_def read_state_def)

lemma update_state_weak[wp]:
  "l3_valid (\<lambda>s. \<forall>r. P r (f s)) (update_state f) P"
  by (clarsimp simp: l3_valid_def update_state_def)

lemma extend_state_weak [wp]:
  "l3_valid (\<lambda>s. P (fst (f (v, s))) (snd (snd (f (v, s))))) (extend_state v f) P"
  by (clarsimp simp: l3_valid_def extend_state_def split_def Let_def)


lemma trim_state_weak [wp]:
  "l3_valid (\<lambda>s. \<forall>a b. P (fst (f b)) (a, snd (f b)) ) (trim_state f ) P"
  by (clarsimp simp: l3_valid_def trim_state_def split_def Let_def)


end