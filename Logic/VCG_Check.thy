theory VCG_Check
                  
imports Logic
        

begin               


(* theorems for the checking the correctness of vcg *)


lemma  write_consistent_defined_address:
  "\<Turnstile> \<lbrace> \<lambda>s. aval lval s = Some vp \<and> aval rval s = Some v \<and> (asid s, Addr vp) \<notin> incon_set s \<and>
      ptable_lift_m (heap s) (root s) (mode s) (Addr vp) = Some pp \<rbrace>  lval ::= rval \<lbrace>\<lambda>s. heap s pp = Some v \<rbrace>"
   by vcgm
 
(* successful memory writes to inconsistent address after flushing, in Kernel Mode *) 


lemma [simp]:
  "mem_read_hp' (asid s) (incon_set s) (heap s) (root s) (mode s)(Addr x2) = Some v
                \<Longrightarrow> mem_read_hp' (asid s) {} (heap s) (root s) (mode s) (Addr x2) = Some v"
  by (clarsimp simp: mem_read_hp'_def split: if_split_asm)



lemma [simp]:
  "aval e s = Some v \<Longrightarrow> aval e (s\<lparr>incon_set := {}\<rparr>) = Some v "
  by (induct e arbitrary: v; clarsimp split: option.splits; fastforce)


lemma [simp]:
  "aval e s = Some v \<Longrightarrow> aval e (s\<lparr>incon_set := {}, ptable_snapshot := \<lambda>a v. Miss\<rparr>) = Some v "
  by (induct e arbitrary: v; clarsimp split: option.splits; fastforce)


lemma flush_TLB_mem_write:
  "\<Turnstile> \<lbrace> \<lambda>s. aval lval s = Some vp \<and> aval rval s = Some v \<and> (asid s, Addr vp) \<in> incon_set s \<and>  mode s = Kernel \<and> 
      ptable_lift_m (heap s) (root s) (mode s) (Addr vp) = Some pp \<rbrace>  Flush flushTLB ;; lval ::= rval \<lbrace>\<lambda>s. heap s pp = Some v \<rbrace>"
  by vcgm

lemma[simp]:
  "mem_read_hp' (asid s) (incon_set s) (heap s) (root s) (mode s) (Addr x2) = Some v
                \<Longrightarrow> mem_read_hp' (asid s) {av \<in> incon_set s. fst av \<noteq> asid s} (heap s) (root s) (mode s) (Addr x2) = Some v"
  by (clarsimp simp: mem_read_hp'_def split: if_split_asm)



lemma [simp]:
  "aval e s = Some v \<Longrightarrow>  aval e (s\<lparr>incon_set := {av \<in> incon_set s. fst av \<noteq> asid s}\<rparr>) = Some v"
 by (induct e arbitrary: v; clarsimp split: option.splits; fastforce)


lemma [simp]:
  "aval e s = Some v \<Longrightarrow>  aval e (s\<lparr>incon_set := {av \<in> incon_set s. fst av \<noteq> asid s} ,ptable_snapshot := (ptable_snapshot s)(asid s := \<lambda>v. Miss)\<rparr>) = Some v"
 by (induct e arbitrary: v; clarsimp split: option.splits; fastforce)


 
lemma flush_ASID_mem_write:
  "\<Turnstile> \<lbrace> \<lambda>s. aval lval s = Some vp \<and> aval rval s = Some v \<and> asid s = a \<and>  (a, Addr vp) \<in> incon_set s \<and> mode s = Kernel \<and> 
      ptable_lift_m (heap s) (root s) (mode s) (Addr vp) = Some pp \<rbrace>  Flush (flushASID a) ;; lval ::= rval \<lbrace>\<lambda>s. heap s pp = Some v \<rbrace>"
  by vcgm

lemma [simp]:
  "mem_read_hp' (asid sa) (incon_set sa) (heap sa) (root sa) (mode sa) (Addr x2) = Some v
                \<Longrightarrow> mem_read_hp' (asid sa) {av \<in> incon_set sa. fst av \<noteq> asid s \<and> snd av \<noteq> vp} (heap sa) (root sa) (mode sa) (Addr x2) = Some v"
  by (clarsimp simp: mem_read_hp'_def split: if_split_asm)

lemma  [simp]:
  "aval e sa = Some v \<Longrightarrow>  aval e (sa\<lparr>incon_set := {av \<in> incon_set sa. fst av \<noteq> asid s \<and> snd av \<noteq> vp}\<rparr>) = Some v"
  by(induct e arbitrary: v sa; clarsimp split: option.splits)


lemma  [simp]:
  "aval e sa = Some v \<Longrightarrow>  aval e (sa\<lparr>incon_set := {av \<in> incon_set sa. fst av \<noteq> asid s \<and> snd av \<noteq> vp}, 
         ptable_snapshot := (\<lambda>x y. if x = asid s \<and> y = vp then Miss else ptable_snapshot sa x y)\<rparr>) = Some v"
  by(induct e arbitrary: v sa; clarsimp split: option.splits)


lemma flush_ASID_va_mem_write:
  "\<Turnstile> \<lbrace> \<lambda>s. aval lval s = Some vp \<and> aval rval s = Some v \<and>  asid s = a \<and> (asid s, Addr vp) \<in> incon_set s \<and> mode s = Kernel \<and> 
      ptable_lift_m (heap s) (root s) (mode s) (Addr vp) = Some pp \<rbrace>  Flush (flushASIDvarange (asid s)  {Addr vp}) ;; lval ::= rval \<lbrace>\<lambda>s. heap s pp = Some v \<rbrace>"
  by vcgm
 


end