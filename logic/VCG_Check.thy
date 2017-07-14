theory VCG_Check
                  
imports Logic
        

begin               


(* theorems for the checking the correctness of vcg *)

(* simplification theorems for the aval *)

lemma aval_state_incon_eq[simp]:
  "(aval e (s\<lparr>incon_set := iset\<rparr>) = Some v) = (aval e s = Some v)"
  by (induct e arbitrary: v; clarsimp split: option.splits; fastforce)

lemma aval_state_mode_eq[simp]:
  "(aval e (s\<lparr>mode := m\<rparr>) = Some v) = (aval e s = Some v)"
  by (induct e arbitrary: v; clarsimp split: option.splits; fastforce)

lemma aval_state_incon_mode_eq[simp]:
  "(aval e (s\<lparr>incon_set := iset, mode := m\<rparr>) = Some v) = (aval e s = Some v)"
  by clarsimp



lemma  write_consistent_defined_address:
  "\<Turnstile> \<lbrace> \<lambda>s. aval lval s = Some vp \<and> aval rval s = Some v \<and> (asid s, vp) \<notin> incon_set s \<and>
      ptable_lift_m (heap s) (root s) (mode s) (Addr vp) = Some pp \<rbrace>  lval ::= rval \<lbrace>\<lambda>s. heap s pp = Some v \<rbrace>"
   by vcg
 
(* successful memory writes to inconsistent address after flushing, in Kernel Mode *) 

lemma flush_TLB_mem_write:
  "\<Turnstile> \<lbrace> \<lambda>s. aval lval s = Some vp \<and> aval rval s = Some v \<and> (asid s, vp) \<in> incon_set s \<and>  mode s = Kernel \<and> 
      ptable_lift_m (heap s) (root s) (mode s) (Addr vp) = Some pp \<rbrace>  Flush flushTLB ;; lval ::= rval \<lbrace>\<lambda>s. heap s pp = Some v \<rbrace>"
  by vcg
 

lemma flush_ASID_mem_write:
  "\<Turnstile> \<lbrace> \<lambda>s. aval lval s = Some vp \<and> aval rval s = Some v \<and> asid s = a \<and>  (a, vp) \<in> incon_set s \<and> mode s = Kernel \<and> 
      ptable_lift_m (heap s) (root s) (mode s) (Addr vp) = Some pp \<rbrace>  Flush (flushASID a) ;; lval ::= rval \<lbrace>\<lambda>s. heap s pp = Some v \<rbrace>"
    by vcg


lemma flush_va_mem_write:
  "\<Turnstile> \<lbrace> \<lambda>s. aval lval s = Some vp \<and> aval rval s = Some v \<and> (asid s, vp) \<in> incon_set s \<and> mode s = Kernel \<and> 
      ptable_lift_m (heap s) (root s) (mode s) (Addr vp) = Some pp \<rbrace>  Flush (flushva (Addr vp)) ;; lval ::= rval \<lbrace>\<lambda>s. heap s pp = Some v \<rbrace>"
  by vcg


lemma flush_ASID_va_mem_write:
  "\<Turnstile> \<lbrace> \<lambda>s. aval lval s = Some vp \<and> aval rval s = Some v \<and>  asid s = a \<and> (asid s, vp) \<in> incon_set s \<and> mode s = Kernel \<and> 
      ptable_lift_m (heap s) (root s) (mode s) (Addr vp) = Some pp \<rbrace>  Flush (flushASIDva (asid s)  (Addr vp)) ;; lval ::= rval \<lbrace>\<lambda>s. heap s pp = Some v \<rbrace>"
   by vcg



end