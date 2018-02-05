theory VCG_Check
                  
imports Logic
        

begin               


(* theorems for the checking the correctness of vcg *)


lemma  write_consistent_defined_address:
  "\<Turnstile> \<lbrace> \<lambda>s. aval lval s = Some vp \<and> aval rval s = Some v \<and> Addr vp \<notin> incon_set s \<and>
      ptable_lift_m (heap s) (root s) (mode s) (Addr vp) = Some pp \<rbrace>  lval ::= rval \<lbrace>\<lambda>s. heap s pp = Some v \<rbrace>"
   by vcgm
 
(* successful memory writes to inconsistent address after flushing, in Kernel Mode *) 


lemma [simp]:
  "mem_read_hp'  (incon_set s) (heap s) (root s) (mode s) (Addr x2) = Some v
                \<Longrightarrow> mem_read_hp'  {} (heap s) (root s) (mode s) (Addr x2) = Some v"
  by (clarsimp simp: mem_read_hp'_def split: if_split_asm)




lemma [simp]:
  "aval e s = Some v \<Longrightarrow> aval e (s\<lparr>incon_set := {}\<rparr>) = Some v "
  by (induct e arbitrary: v; clarsimp split: option.splits; fastforce)


lemma [simp]:
  "aval e s = Some v \<Longrightarrow> aval e (s\<lparr>incon_set := {}, ptable_snapshot := \<lambda>a v. Miss\<rparr>) = Some v "
  by (induct e arbitrary: v; clarsimp split: option.splits; fastforce)


lemma flush_TLB_mem_write:
  "\<Turnstile> \<lbrace> \<lambda>s. aval lval s = Some vp \<and> aval rval s = Some v \<and> Addr vp \<in> incon_set s \<and>  mode s = Kernel \<and> 
      ptable_lift_m (heap s) (root s) (mode s) (Addr vp) = Some pp \<rbrace>  Flush flushTLB ;; lval ::= rval \<lbrace>\<lambda>s. heap s pp = Some v \<rbrace>"
  by vcgm



end