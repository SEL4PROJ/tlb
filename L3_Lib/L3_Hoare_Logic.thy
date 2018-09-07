theory L3_Hoare_Logic
imports L3_Lib
          
begin

definition 
  l3_valid ::  "('s \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> 'r \<times> 's) \<Rightarrow> ('r \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> bool"
where 
  "l3_valid P f P' \<equiv> \<forall>s s' r. f s = (r, s') \<longrightarrow> P s \<longrightarrow> P' r s'"

(*
definition 
  "l3_valid P prj f P' \<equiv> \<forall>s s' r. f s = (r, s') \<longrightarrow> P (prj s) \<longrightarrow> P' r (prj s')"
*)

named_theorems wp_pre

lemma l3_valid_weak_pre[wp_pre]:
  "\<lbrakk> l3_valid P f Q; (\<And>s . P' s \<Longrightarrow> P s) \<rbrakk> \<Longrightarrow> l3_valid P' f Q"
  by (simp add: l3_valid_def)

named_theorems wp

lemma l3_valid_return[wp]:
  "l3_valid (\<lambda>s. P () s)  (return ()) P"
  by (clarsimp simp: l3_valid_def return_def)

lemma l3_valid_return'[wp]:
  "l3_valid (\<lambda>s. P f s)  (Pair f) P"
  by (clarsimp simp: l3_valid_def)

lemma l3_valid_bind_weak[wp]:
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

(*
lemma trim_state_weak':
  " \<lbrakk>l3_valid P f Q\<rbrakk> \<Longrightarrow> l3_valid (\<lambda>s. P (snd s)) (trim_state f) (\<lambda>r s'. Q r (snd s'))"
  apply (clarsimp simp: l3_valid_def trim_state_def)
  by (fastforce split: prod.splits)
*)

lemma trim_state_weak[wp]:
  " \<lbrakk>\<And>s'. l3_valid (P s') f  (\<lambda>r s.  Q r (s', s) ) \<rbrakk> \<Longrightarrow> l3_valid (\<lambda>s. P (fst s) (snd s)) (trim_state f) Q"
  apply (clarsimp simp: l3_valid_def trim_state_def)
   by (fastforce split: prod.splits)

(*
lemma extend_state_weak[wp, intro!, simp]:
  "\<lbrakk> \<And>v. l3_valid P (prj o snd) f Q \<rbrakk> \<Longrightarrow> l3_valid P prj (extend_state v f) Q"
  apply (clarsimp simp: l3_valid_def extend_state_def )
   by (fastforce split: prod.splits)
  *)

(*
lemma trim_state_weak[wp, intro!, simp]:
  "l3_valid P prj f Q \<Longrightarrow> l3_valid P (prj o snd) (trim_state f) Q"
   unfolding trim_state_def l3_valid_def
   by (fastforce split: prod.splits)


lemma trim_state_weak'[wp, intro!, simp]:
  "l3_valid P id f Q \<Longrightarrow> l3_valid P snd (trim_state f) Q"
   unfolding trim_state_def l3_valid_def
   by (fastforce split: prod.splits)
*)

lemma l3_valid_conj_post:
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





















(*
definition 
  l3_valid ::  "('s \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> 'r \<times> 's) \<Rightarrow> ('r \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> bool"
where 
  "l3_valid P f P' \<equiv> \<forall>s s' r. f s = (r, s') \<longrightarrow> P s \<longrightarrow> P' r s'"

named_theorems wp_pre

lemma l3_valid_weak_pre[wp_pre]:
  "\<lbrakk> l3_valid P f Q; (\<And>s. P' s \<Longrightarrow> P s) \<rbrakk> \<Longrightarrow> l3_valid P' f Q"
  by (simp add: l3_valid_def)

named_theorems wp

lemma l3_valid_return[wp,intro!, simp]:
  "l3_valid (\<lambda>s. P () s) (return ()) P"
  by (clarsimp simp: l3_valid_def return_def)

lemma l3_valid_return'[wp,intro!, simp]:
  "l3_valid (\<lambda>s. P f s) (Pair f) P"
  by (clarsimp simp: l3_valid_def)


lemma l3_valid_bind:
  "l3_valid (\<lambda>s. P (fst ( g (fst (f s)) (snd (f s)))) (snd ( g (fst (f s)) (snd (f s))))) (bind f g) P"
  apply (clarsimp simp: bind_def split_def Let_def)
  by (clarsimp simp: l3_valid_def)

lemma l3_valid_bind_weak[wp,intro!, simp]:
  "\<lbrakk> \<And>r. l3_valid (P' r) (g r) Q; l3_valid P f P' \<rbrakk> \<Longrightarrow> l3_valid P (bind f g) Q"
  by (simp add: l3_valid_def bind_def split: prod.splits)


lemma read_state_weak[wp,intro!, simp]:
  "l3_valid (\<lambda>s. \<forall>r. P r s) (read_state f) P"
  by (clarsimp simp: l3_valid_def read_state_def)

lemma update_state_weak[wp,intro!, simp]:
  "l3_valid (\<lambda>s. \<forall>r. P r (f s)) (update_state f) P"
  by (clarsimp simp: l3_valid_def update_state_def)


lemma extend_state_weak:
  "l3_valid (\<lambda>s. P (fst (f (v, s))) (snd (snd (f (v, s))))) (extend_state v f) P"
  by (clarsimp simp: l3_valid_def extend_state_def split_def Let_def)


lemma extend_state_weak':
  "l3_valid (\<lambda>s. \<forall>r v. P r ( snd (snd (f (v,s))) )) (extend_state v f) P"
   by (clarsimp simp: l3_valid_def extend_state_def split_def Let_def)


lemma extend_state_weak'':
  "\<lbrakk> \<And>v. l3_valid P (\<lambda>s. (fst (f (v, s)), snd(snd(f (v, s))))) Q \<rbrakk> \<Longrightarrow> l3_valid P (extend_state v f) Q"
  by (simp add: l3_valid_def extend_state_def split_def Let_def)


lemma trim_state_weak:
  "l3_valid (\<lambda>s. \<forall>a b. P (fst (f b)) (a, snd (f b)) ) (trim_state f ) P"
  by (clarsimp simp: l3_valid_def trim_state_def split_def Let_def)

*)





end