theory Con_Set
                  
imports VCG_Check
        

begin               


definition
  con_set :: "vaddr set \<Rightarrow> p_state \<Rightarrow> bool"
where
  "con_set V s \<equiv>  \<forall>va\<in>V. (asid s, va) \<notin> incon_set s"


(* vcg check for the flush and con_set memory writes, in Kernel Mode  *)

lemma flush_TLB_mem_write':
  "\<Turnstile> \<lbrace> \<lambda>s. aval lval s = Some vp \<and> aval rval s = Some v \<and> Addr vp \<notin> SA  \<and> con_set SA s \<and> mode s = Kernel \<and> 
      ptable_lift_m (heap s) (root s) (mode s) (Addr vp) = Some pp \<rbrace>  Flush flushTLB ;; lval ::= rval \<lbrace>\<lambda>s. heap s pp = Some v \<rbrace>"
   by vcgm


lemma flush_ASID_mem_write':
  "\<Turnstile> \<lbrace> \<lambda>s. aval lval s = Some vp \<and> aval rval s = Some v \<and> asid s = a \<and>  Addr vp \<notin> SA \<and> con_set SA s \<and> mode s = Kernel \<and> 
      ptable_lift_m (heap s) (root s) (mode s) (Addr vp) = Some pp \<rbrace>  Flush (flushASID a) ;; lval ::= rval \<lbrace>\<lambda>s. heap s pp = Some v \<rbrace>"
  by vcgm


lemma [simp]:
  " mem_read_hp' (asid sa) (incon_set sa) (heap sa) (root sa) (mode sa)(Addr x2) = Some v
                \<Longrightarrow> mem_read_hp' (asid sa) {av \<in> incon_set sa. fst av \<noteq> s \<and> snd av \<noteq> vp} (heap sa) (root sa) (mode sa) (Addr x2) = Some v"
 by (clarsimp simp: mem_read_hp'_def split: if_split_asm)

lemma  [simp]:
  "aval e sa = Some v \<Longrightarrow> aval e (sa\<lparr>incon_set := {av \<in> incon_set sa. fst av \<noteq> s \<and> snd av \<noteq> vp}\<rparr>) = Some v "
  by (induct e arbitrary: v; clarsimp split: option.splits; fastforce)


lemma  [simp]:
  "aval e sa = Some v \<Longrightarrow> aval e (sa\<lparr>incon_set := {av \<in> incon_set sa. fst av \<noteq> s \<and> snd av \<noteq> vp} , 
         ptable_snapshot := \<lambda>x y. if x = s \<and> y =  vp then Miss else ptable_snapshot sa x y\<rparr>) = Some v "
  by (induct e arbitrary: v; clarsimp split: option.splits; fastforce)


lemma flush_ASID_va_mem_write':
  "\<Turnstile> \<lbrace> \<lambda>s. aval lval s = Some vp \<and> aval rval s = Some v \<and> asid s = a \<and> Addr vp \<notin> SA \<and> con_set SA s \<and> mode s = Kernel \<and> 
      ptable_lift_m (heap s) (root s) (mode s)(Addr vp) = Some pp \<rbrace>  Flush (flushASIDvarange s  {Addr vp}) ;; lval ::= rval \<lbrace>\<lambda>s. heap s pp = Some v \<rbrace>"
  by vcgm


lemma [simp]:
  "con_set va (s\<lparr>heap := hp ,  incon_set := iset , mode := m\<rparr>) =  con_set va (s\<lparr>incon_set := iset\<rparr>) "
  by (clarsimp simp: con_set_def)


lemma [simp]:
  "con_set V (s\<lparr>heap := hp, incon_set := iset \<rparr>) = con_set V (s\<lparr>incon_set := iset\<rparr>)"
 by (clarsimp simp: con_set_def)


end