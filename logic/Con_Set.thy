theory Con_Set
                  
imports VCG_Check
        

begin               


definition
  con_set :: "32 word set \<Rightarrow> p_state \<Rightarrow> bool"
where
  "con_set V s \<equiv>  \<forall>va\<in>V. (asid s, va) \<notin> incon_set s"


(* vcg check for the flush and con_set memory writes, in Kernel Mode  *)

lemma flush_TLB_mem_write':
  "\<Turnstile> \<lbrace> \<lambda>s. aval lval s = Some vp \<and> aval rval s = Some v \<and> vp \<notin> SA  \<and> con_set SA s \<and> mode s = Kernel \<and> 
      ptable_lift_m (heap s) (root s) (mode s) (Addr vp) = Some pp \<rbrace>  Flush flushTLB ;; lval ::= rval \<lbrace>\<lambda>s. heap s pp = Some v \<rbrace>"
   by vcg


lemma flush_ASID_mem_write':
  "\<Turnstile> \<lbrace> \<lambda>s. aval lval s = Some vp \<and> aval rval s = Some v \<and> asid s = a \<and>  vp \<notin> SA \<and> con_set SA s \<and> mode s = Kernel \<and> 
      ptable_lift_m (heap s) (root s) (mode s) (Addr vp) = Some pp \<rbrace>  Flush (flushASID a) ;; lval ::= rval \<lbrace>\<lambda>s. heap s pp = Some v \<rbrace>"
  by vcg

lemma flush_va_mem_write':
  "\<Turnstile> \<lbrace> \<lambda>s. aval lval s = Some vp \<and> aval rval s = Some v \<and> vp \<notin> SA  \<and> con_set SA s \<and> mode s = Kernel \<and> 
     ptable_lift_m (heap s) (root s) (mode s) (Addr vp) = Some pp \<rbrace>  Flush (flushva (Addr vp)) ;; lval ::= rval \<lbrace>\<lambda>s. heap s pp = Some v \<rbrace>"
  by vcg

lemma flush_ASID_va_mem_write':
  "\<Turnstile> \<lbrace> \<lambda>s. aval lval s = Some vp \<and> aval rval s = Some v \<and> asid s = a \<and> vp \<notin> SA \<and> con_set SA s \<and> mode s = Kernel \<and> 
      ptable_lift_m (heap s) (root s) (mode s)(Addr vp) = Some pp \<rbrace>  Flush (flushASIDva s  (Addr vp)) ;; lval ::= rval \<lbrace>\<lambda>s. heap s pp = Some v \<rbrace>"
   by vcg


end