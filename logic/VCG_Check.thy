theory VCG_Check
                  
imports Logic
        

begin               


(* theorems for the checking the correctness of vcg *)



lemma  write_consistent_defined_address:
  "\<Turnstile> \<lbrace> \<lambda>s. aval lval s = Some vp \<and> aval rval s = Some v \<and> (asid s, vp) \<notin> incon_set s \<and>
      ptable_lift_m (heap s) (root s) (mode s) (Addr vp) = Some pp \<rbrace>  lval ::= rval \<lbrace>\<lambda>s. heap s pp = Some v \<rbrace>"
   by vcgm
 
(* successful memory writes to inconsistent address after flushing, in Kernel Mode *) 

(* new stuff *)
lemma [simp]:
  "mem_read_hp' (asid s) (incon_set s) (heap s) (root s) (Addr x2) = Some v
                \<Longrightarrow> mem_read_hp' (asid s) {} (heap s) (root s) (Addr x2) = Some v"
  apply (clarsimp simp: mem_read_hp'_def split: split_if_asm)
done


lemma [simp]:
  "aval e s = Some v \<Longrightarrow> aval e (s\<lparr>incon_set := {}\<rparr>) = Some v "
  by (induct e arbitrary: v; clarsimp split: option.splits; fastforce)

(* new stuff *)
lemma flush_TLB_mem_write:
  "\<Turnstile> \<lbrace> \<lambda>s. aval lval s = Some vp \<and> aval rval s = Some v \<and> (asid s, vp) \<in> incon_set s \<and>  mode s = Kernel \<and> 
      ptable_lift_m (heap s) (root s) (mode s) (Addr vp) = Some pp \<rbrace>  Flush flushTLB ;; lval ::= rval \<lbrace>\<lambda>s. heap s pp = Some v \<rbrace>"
  by vcgm

lemma[simp]:
  "mem_read_hp' (asid s) (incon_set s) (heap s) (root s) (Addr x2) = Some v
                \<Longrightarrow> mem_read_hp' (asid s) {av \<in> incon_set s. fst av \<noteq> asid s} (heap s) (root s) (Addr x2) = Some v"
  by (clarsimp simp: mem_read_hp'_def split: split_if_asm)



lemma [simp]:
  "aval e s = Some v \<Longrightarrow>  aval e (s\<lparr>incon_set := {av \<in> incon_set s. fst av \<noteq> asid s}\<rparr>) = Some v"
 by (induct e arbitrary: v; clarsimp split: option.splits; fastforce)

(* apply (induct e arbitrary: v s)
  apply (clarsimp)
apply ( clarsimp split: option.splits)
apply ( clarsimp split: option.splits)
  
  apply ( clarsimp split: option.splits) *)

 
lemma flush_ASID_mem_write:
  "\<Turnstile> \<lbrace> \<lambda>s. aval lval s = Some vp \<and> aval rval s = Some v \<and> asid s = a \<and>  (a, vp) \<in> incon_set s \<and> mode s = Kernel \<and> 
      ptable_lift_m (heap s) (root s) (mode s) (Addr vp) = Some pp \<rbrace>  Flush (flushASID a) ;; lval ::= rval \<lbrace>\<lambda>s. heap s pp = Some v \<rbrace>"
  by vcgm

lemma [simp]:
  "mem_read_hp' (asid sa) (incon_set sa) (heap sa) (root sa) (Addr x2) = Some v
                \<Longrightarrow> mem_read_hp' (asid sa) {av \<in> incon_set sa. fst av \<noteq> asid s \<and> snd av \<noteq> vp} (heap sa) (root sa) (Addr x2) = Some v"
 by (clarsimp simp: mem_read_hp'_def split: split_if_asm)

lemma  [simp]:
  "aval e sa = Some v \<Longrightarrow>  aval e (sa\<lparr>incon_set := {av \<in> incon_set sa. fst av \<noteq> asid s \<and> snd av \<noteq> vp}\<rparr>) = Some v"
 by (induct e arbitrary: v; clarsimp split: option.splits; fastforce)

lemma flush_ASID_va_mem_write:
  "\<Turnstile> \<lbrace> \<lambda>s. aval lval s = Some vp \<and> aval rval s = Some v \<and>  asid s = a \<and> (asid s, vp) \<in> incon_set s \<and> mode s = Kernel \<and> 
      ptable_lift_m (heap s) (root s) (mode s) (Addr vp) = Some pp \<rbrace>  Flush (flushASIDva (asid s)  (Addr vp)) ;; lval ::= rval \<lbrace>\<lambda>s. heap s pp = Some v \<rbrace>"
  by vcgm
 


end