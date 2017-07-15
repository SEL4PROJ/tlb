theory Logic
                  
imports MMU_Prg_Logic
        

begin               

datatype aexp = Const val 
              | UnOp "(val \<Rightarrow> val)" aexp 
              | BinOp "(val \<Rightarrow> val \<Rightarrow> val)" aexp aexp 
              | HeapLookup aexp
(*
    There is no need of that, as we can have the asid or heaplookup from the state
              | RootLookup            (* of the current state, its a separate reg so doesn't require an address *)
              | AsidLookup            (* not sure about that *)
*)


fun aval :: "aexp \<Rightarrow> p_state  \<rightharpoonup> val" where
  "aval (Const c) s = Some c" 
|
  "aval (UnOp f e) s = 
         (case (aval e s) of Some v \<Rightarrow> Some (f v) | None \<Rightarrow> None )"
|                                  
  "aval (BinOp f e1 e2) s =
         (case (aval e1 s , aval e2 s) of (Some v1, Some v2) \<Rightarrow> Some (f v1 v2) | _ \<Rightarrow> None )"
|
  "aval (HeapLookup vp) s = 
         (case (aval vp s) of None \<Rightarrow> None | Some v \<Rightarrow> mem_read_hp (heap s) (root s) (Addr v))"
(*
   just leaving it here, to be removed later
|                                                             
  "aval RootLookup s =  Some (addr_val (root s))"
|
  "aval AsidLookup s =  Some (ucast (asid s))"   
*)


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


lemma aval_state_rt_map_eq[simp]:
  "(aval e (s\<lparr>root_map := root_map s(Addr r \<mapsto> a)\<rparr>) = Some v) = (aval e s = Some v)"
  by (induct e arbitrary: v; clarsimp split: option.splits; fastforce)

                             
thm aval.induct

datatype bexp = BConst bool 
              | BComp "(val \<Rightarrow> val \<Rightarrow> bool)" aexp aexp 
              | BBinOp "(bool \<Rightarrow> bool \<Rightarrow> bool)" bexp bexp 
              | BNot bexp



fun bval :: "bexp \<Rightarrow> p_state \<rightharpoonup> bool"
 where
  "bval (BConst b) s = Some b" 
|
  "bval (BComp f e1 e2) s = 
    (case (aval e1 s , aval e2 s) of (Some v1, Some v2) \<Rightarrow> Some (f v1 v2) | _ \<Rightarrow> None )"
|
  "bval (BBinOp f b1 b2) s = 
    (case (bval b1 s , bval b2 s) of (Some v1, Some v2) \<Rightarrow> Some (f v1 v2) | _ \<Rightarrow> None )"
|
"bval (BNot b) s = 
    (case (bval b s) of Some v \<Rightarrow> Some (\<not>v) | _ \<Rightarrow> None )"




datatype flush_type = flushTLB
                    | flushASID    asid
                    | flushvarange "vaddr set"  (*  new one *)
                    | flushASIDva  asid vaddr


datatype com =  SKIP 
             |  Assign aexp aexp      ("_ ::= _" [100, 61] 61)
             |  Seq com com           ("_;;/ _"  [60, 61] 60)
             |  If bexp com com       ("(IF _/ THEN _/ ELSE _)"  [0, 0, 61] 61)
             |  While bexp com        ("(WHILE _/ DO _)"  [0, 61] 61)
             |  Flush flush_type
             |  UpdateTTBR0 aexp       (* should this be 32 word instead of aexp? *)
             |  UpdateASID asid
             |  UpdateRTMap aexp asid  (* should this be 32 word instead of aexp *)
             |  SetMode mode_t
             
            


fun
  flush_effect ::"flush_type \<Rightarrow> (asid \<times> 32 word) set \<Rightarrow> (asid \<times> 32 word) set"
where
  "flush_effect flushTLB iset  = {}"
|
  "flush_effect (flushASID a) iset = {av\<in>iset. fst av \<noteq> a}"                                                          
| 
  "flush_effect (flushvarange vset) iset = {av\<in>iset. snd av \<notin> addr_val ` vset}"
|
  "flush_effect (flushASIDva a va) iset = {av\<in>iset. fst av \<noteq> a \<and> snd av \<noteq> (addr_val va)}"


(*

definition 
  pde_comp :: "asid \<Rightarrow> heap \<Rightarrow> heap \<Rightarrow> paddr \<Rightarrow> (asid \<times> 32 word) set"
where
  "pde_comp a hp1 hp2 rt \<equiv> 
         (\<lambda>x. (a, addr_val x)) ` {va. \<exists>x1 x2. lookup_pde' hp1 rt va = Some x1 \<and> lookup_pde' hp2 rt va = Some x2 \<and> 
                                       lookup_pde' hp1 rt va \<noteq> lookup_pde' hp2 rt va }"                                   
*)

(* wrong *)

(*definition 
  pde_comp :: "asid \<Rightarrow> heap \<Rightarrow> heap \<Rightarrow> paddr \<Rightarrow> (asid \<times> 32 word) set"
where
  "pde_comp a hp1 hp2 rt \<equiv> 
         (\<lambda>x. (a, addr_val x)) ` {va. \<exists>x1 x2. lookup_pde' hp1 rt va = Some x1 \<and> lookup_pde' hp2 rt va = Some x2 \<and> 
                                       x1 \<noteq> x2 }"
*)


(*definition 
  pde_comp :: "asid \<Rightarrow> heap \<Rightarrow> heap \<Rightarrow> paddr \<Rightarrow> (asid \<times> 32 word) set"
where
  "pde_comp a hp1 hp2 rt \<equiv> 
         (\<lambda>x. (a, addr_val x)) ` {va. \<exists>p1 p2. ptable_lift' hp1 rt va = Some p1 \<and> ptable_lift' hp2 rt va = Some p2 \<and> p1 \<noteq> p2 }"
*)


definition 
  pde_comp :: "asid \<Rightarrow> heap \<Rightarrow> heap \<Rightarrow> paddr \<Rightarrow> (asid \<times> 32 word) set"
where
  "pde_comp a hp1 hp2 rt \<equiv> 
         (\<lambda>x. (a, addr_val x)) ` {va. (\<exists>p1 p2. ptable_lift' hp1 rt va = Some p1 \<and> ptable_lift' hp2 rt va = Some p2 \<and> p1 \<noteq> p2 )  \<or> 
                                      (\<exists>p. ptable_lift' hp1 rt va = Some p \<and> ptable_lift' hp2 rt va = None )}"


(* previous version of pde_comp  *)

(*definition 
  pde_comp' :: "asid \<Rightarrow> heap \<Rightarrow> heap \<Rightarrow> paddr \<Rightarrow> (asid \<times> 32 word) set"
where
  "pde_comp' a hp1 hp2 rt \<equiv> 
         (\<lambda>x. (a, addr_val x)) ` {va. (\<exists>p1 p2. ptable_lift' hp1 rt va = Some p1 \<and> ptable_lift' hp2 rt va = Some p2 \<and> p1 \<noteq> p2 )}"

lemma
  "va \<in> pde_comp' a hp1 hp2 rt \<Longrightarrow> va \<in> pde_comp a hp1 hp2 rt"
  by (clarsimp simp: pde_comp_def pde_comp'_def)
*)


lemma ptable_trace_pde_comp:
  "\<forall>x. p \<notin> ptable_trace' h r x \<Longrightarrow> pde_comp a  h (h(p \<mapsto> v)) r = {}"
  apply (clarsimp simp: ptable_trace'_def pde_comp_def Let_def)
  apply (drule_tac x = x in spec)
  apply (clarsimp simp: ptable_lift'_def lookup_pde'_def get_pde'_def decode_heap_pde'_def decode_heap_pte'_def vaddr_pt_index_def vaddr_pd_index_def lookup_pte'_def
                        get_pte'_def  split:option.splits split: pde.splits split: pte.splits)
  using Let_def by auto


lemma pde_comp_empty:
  "p \<notin> \<Union>(ptable_trace' h r ` UNIV) \<Longrightarrow> pde_comp a  h (h(p \<mapsto> v)) r = {}"
  apply (drule union_imp_all)
  by (clarsimp simp: ptable_trace_pde_comp)



lemma plift_equal_not_in_pde_comp [simp]:
  "\<lbrakk> ptable_lift' h1 r (Addr va) =  Some pa ; ptable_lift' h2 r (Addr va) = Some pa \<rbrakk> \<Longrightarrow>  
            (a, va) \<notin> pde_comp a h1 h2 r"
  by (clarsimp simp: pde_comp_def) 
 


inductive
  big_step :: "com \<times> p_state \<Rightarrow> p_state option \<Rightarrow> bool" (infix "\<Rightarrow>" 55)
where
  Skip:            "(SKIP,s) \<Rightarrow> Some s"   
|
  AssignFail1:     "\<lbrakk>aval lval s = None \<or> aval rval s = None \<rbrakk>  \<Longrightarrow> (lval ::= rval , s) \<Rightarrow> None" 
|
  AssignFail2:     "\<lbrakk>aval lval s = Some vp ; aval rval s = Some v ; (asid s, vp) \<in> incon_set s \<or>
                           ptable_lift_m (heap s) (root s) (mode s) (Addr vp) = None \<rbrakk>  \<Longrightarrow> (lval ::= rval , s) \<Rightarrow> None"  
|
  Assign:          "\<lbrakk>aval lval s = Some vp ; aval rval s = Some v ; (asid s, vp) \<notin> incon_set s;
                         ptable_lift_m (heap s) (root s) (mode s) (Addr vp) = Some pp \<rbrakk>  \<Longrightarrow> 
                          (lval ::= rval , s) \<Rightarrow> Some (s \<lparr> heap := heap s (pp \<mapsto> v) , 
                            incon_set := incon_set s \<union>  pde_comp (asid s)  (heap s)  (heap s (pp \<mapsto> v)) (root s) \<rparr>)" 
| 
  Seq:             "\<lbrakk>(c1,s1) \<Rightarrow> Some s2;  (c2,s2) \<Rightarrow> s3 \<rbrakk> \<Longrightarrow> (c1;;c2, s1) \<Rightarrow> s3" 
|
  SeqFail:         "(c1,s1) \<Rightarrow> None \<Longrightarrow> (c1;;c2, s1) \<Rightarrow> None" 
|
  IfTrue:          "\<lbrakk>bval b s = Some True; (c1,s) \<Rightarrow> t \<rbrakk> \<Longrightarrow> (IF b THEN c1 ELSE c2, s) \<Rightarrow> t" 
|
  IfFalse:         "\<lbrakk>bval b s = Some False; (c2,s) \<Rightarrow> t \<rbrakk> \<Longrightarrow> (IF b THEN c1 ELSE c2, s) \<Rightarrow> t" 
|
  IfFail:          "bval b s = None \<Longrightarrow> (IF b THEN c1 ELSE c2, s) \<Rightarrow> None" 
|                                                             
  WhileFalse:      "bval b s = Some False \<Longrightarrow> (WHILE b DO c, s) \<Rightarrow> Some s" 
| 
  WhileTrue:       "\<lbrakk>bval b s = Some True; (c, s) \<Rightarrow> Some s''; (WHILE b DO c, s'') \<Rightarrow> s' \<rbrakk> \<Longrightarrow> (WHILE b DO c, s) \<Rightarrow> s'" 
|
  WhileFail1:      "\<lbrakk>bval b s = Some True; (c, s) \<Rightarrow> None \<rbrakk>\<Longrightarrow> (WHILE b DO c, s) \<Rightarrow> None" 
|
  WhileFail2:      "bval b s = None \<Longrightarrow> (WHILE b DO c , s) \<Rightarrow> None" 
|
  Flush:           "mode s = Kernel \<Longrightarrow> (Flush f, s) \<Rightarrow>  Some (s \<lparr>incon_set := flush_effect f (incon_set s)\<rparr>)" 
|
  FlushFail:       "mode s = User \<Longrightarrow> (Flush f, s) \<Rightarrow>  None" 
| 
  UpdateTTBR0Fail: "mode s = User \<or> aval rt s = None \<Longrightarrow> (UpdateTTBR0 rt, s) \<Rightarrow>  None" 
|
  UpdateTTBR0:     "mode s = Kernel \<and> aval rt s = Some v \<Longrightarrow> (UpdateTTBR0 rt, s) \<Rightarrow>  Some (s \<lparr>root := Addr v \<rparr>)" 
|
  UpdateASID:      "mode s = Kernel \<Longrightarrow> (UpdateASID a , s) \<Rightarrow>  Some (s \<lparr>asid := a\<rparr>)"
|
  UpdateASIDFail:  "mode s = User \<Longrightarrow> (UpdateASID a , s) \<Rightarrow>  None"
|
  SetMode:          "mode s = Kernel \<Longrightarrow> (SetMode m, s) \<Rightarrow> Some (s \<lparr>mode := m \<rparr>)"
|
  SetModeFail:      "mode s = User \<Longrightarrow> (SetMode m, s) \<Rightarrow> None"
|
  UpdateRTMapFail: "mode s = User \<or> aval rt s = None \<Longrightarrow> (UpdateRTMap rt a , s) \<Rightarrow> None"  (* is this ok? a is not being used in the assumption *)
|
  UpdateRTMap:     "mode s = Kernel \<and> aval rt s = Some v \<Longrightarrow> (UpdateRTMap rt a , s) \<Rightarrow> Some (s \<lparr> root_map := root_map s (Addr v \<mapsto> a) \<rparr>)"




print_theorems 
code_pred big_step .
declare big_step.intros [intro]
thm big_step.induct

lemmas big_step_induct = big_step.induct [split_format (complete)]
thm big_step_induct

inductive_cases
  SkipE [elim!]:   "(SKIP, s) \<Rightarrow> s'" and
  AssignE [elim!]: "(x ::= a, s) \<Rightarrow> s'" and
  SeqE [elim!]:    "(c1;; c2, s) \<Rightarrow> s'" and
  IfE [elim!]:     "(IF b THEN c1 ELSE c2, s) \<Rightarrow> s'" and
  WhileE:          "(WHILE b DO c OD, s) \<Rightarrow> s'" and
  FlushE [elim!]:  "(Flush f, s) \<Rightarrow> s'" and
  TTBR0E [elim!]:  "(UpdateTTBR0 rt, s) \<Rightarrow>  s'" and
  UpdateAE [elim!]:"(UpdateASID a , s) \<Rightarrow>  s'" and 
  SetME [elim!]:   "(SetMode flg, s) \<Rightarrow>  s'" and
  UpdateRTMapE [elim!] : "(UpdateRTMap rt a , s) \<Rightarrow> s'"

thm SkipE
    AssignE
    SeqE
    IfE
    WhileE
    FlushE
    TTBR0E
    UpdateAE
    SetME
    UpdateRTMapE



definition
  hoare_valid :: "(p_state \<Rightarrow> bool) \<Rightarrow> com \<Rightarrow> (p_state \<Rightarrow> bool) \<Rightarrow> bool" ("\<Turnstile> \<lbrace>(1_)\<rbrace>/ (_)/ \<lbrace>(1_)\<rbrace>" 50) where
  "\<Turnstile> \<lbrace>P\<rbrace> c \<lbrace>Q\<rbrace> \<equiv> \<forall>s s'. (c,s) \<Rightarrow> s' \<and> P s \<longrightarrow> (\<exists>r. s' = Some r \<and> Q r)"



(* not in the vcg *)
lemma seq_sound:
  "\<lbrakk> \<Turnstile> \<lbrace>P\<rbrace> c1 \<lbrace>Q\<rbrace> ; \<Turnstile> \<lbrace>Q\<rbrace> c2 \<lbrace>R\<rbrace> \<rbrakk>  \<Longrightarrow> \<Turnstile> \<lbrace>P\<rbrace> c1;;c2 \<lbrace>R\<rbrace>"
  apply (clarsimp simp: hoare_valid_def)
  by blast


lemma conseq_sound:
  "\<lbrakk> \<Turnstile> \<lbrace>P\<rbrace> c \<lbrace>Q\<rbrace> ; (\<forall>s. P' s \<longrightarrow> P s) \<and> (\<forall>s. Q s \<longrightarrow> Q' s) \<rbrakk>  
         \<Longrightarrow> \<Turnstile> \<lbrace>P'\<rbrace> c \<lbrace>Q'\<rbrace>"
  apply (clarsimp simp: hoare_valid_def)
  by blast

lemma conj_sound:
  "\<lbrakk> \<Turnstile> \<lbrace>P\<rbrace> c \<lbrace>Q\<rbrace> ; \<Turnstile> \<lbrace>R\<rbrace> c \<lbrace>S\<rbrace> \<rbrakk>  \<Longrightarrow> \<Turnstile> \<lbrace>\<lambda>s. P s \<and> R s\<rbrace> c \<lbrace>\<lambda>s. Q s \<and> S s\<rbrace>"
  apply (clarsimp simp: hoare_valid_def)
  by blast


lemma disj_sound:
  "\<lbrakk> \<Turnstile> \<lbrace>P\<rbrace> c \<lbrace>Q\<rbrace> ; \<Turnstile> \<lbrace>R\<rbrace> c \<lbrace>S\<rbrace> \<rbrakk>  \<Longrightarrow> \<Turnstile> \<lbrace>\<lambda>s. P s \<or> R s\<rbrace> c \<lbrace>\<lambda>s. Q s \<or> S s\<rbrace>"
  apply (clarsimp simp: hoare_valid_def)
  by blast


lemma while_final:
  "\<lbrakk>(prog, s'') \<Rightarrow> s';  
     \<forall>s. P s \<and> bval b s = Some True \<longrightarrow> (\<forall>s'. (c, s) \<Rightarrow> s' \<longrightarrow> (\<exists>r. s' = Some r \<and> P r));  P s'';
       \<forall>s. P s \<longrightarrow> (\<exists>y. bval b s = Some y); prog = WHILE b DO c \<rbrakk>  \<Longrightarrow> 
        \<exists>r. s' = Some r \<and> P r \<and> bval b r = Some False"
  apply(induct rule: big_step_induct)
  apply fastforce+
  done

lemma while_sound:
  "\<lbrakk> \<Turnstile> \<lbrace>\<lambda>s. P s \<and> bval b s = Some True \<rbrace> c \<lbrace>P\<rbrace> ;
        (\<forall>s. P s \<longrightarrow> bval b s \<noteq> None) \<rbrakk>  \<Longrightarrow>
        \<Turnstile> \<lbrace>P\<rbrace> WHILE b DO c \<lbrace>\<lambda>s. P s \<and> bval b s = Some False\<rbrace>"
  apply (clarsimp simp:  hoare_valid_def)
  apply (erule WhileE)
     prefer 2
     apply(rule_tac c = c and s'' = s'' in while_final) apply fastforce +
done


(* Eisbach method for vcg *)

named_theorems vcg
named_theorems vcg_pre

method vcg declares vcg = (rule vcg_pre, (rule vcg)+, (assumption|clarsimp split del: split_if)?)


lemma skip_sound[vcg]:
  "\<Turnstile> \<lbrace>P\<rbrace> SKIP \<lbrace>P\<rbrace>"
  by (clarsimp simp: hoare_valid_def)

lemma  assign_sound[vcg]:
  " \<Turnstile> \<lbrace>\<lambda>s. \<exists>vp v pp. aval l s = Some vp \<and> aval r s = Some v \<and> (asid s , vp) \<notin> incon_set s \<and>
           P (s \<lparr>heap := heap s (pp \<mapsto> v) , incon_set := incon_set s \<union>  pde_comp (asid s)  (heap s)  (heap s (pp \<mapsto> v)) (root s)\<rparr>)
            \<and>   ptable_lift_m (heap s) (root s) (mode s) (Addr vp) = Some pp\<rbrace>  l ::= r \<lbrace>P\<rbrace>" 
  apply (clarsimp simp: hoare_valid_def)
  apply auto
done


lemma seq_sound'[vcg]:
  "\<lbrakk> \<Turnstile> \<lbrace>Q\<rbrace> c2 \<lbrace>R\<rbrace>; \<Turnstile> \<lbrace>P\<rbrace> c1 \<lbrace>Q\<rbrace> \<rbrakk>  \<Longrightarrow> \<Turnstile> \<lbrace>P\<rbrace> c1;;c2 \<lbrace>R\<rbrace>"
  by (rule seq_sound)


lemma weak_pre [vcg_pre]:
  "\<lbrakk> \<Turnstile> \<lbrace>P\<rbrace> c \<lbrace>Q\<rbrace> ; \<And>s. P' s \<Longrightarrow> P s \<rbrakk>  \<Longrightarrow> \<Turnstile> \<lbrace>P'\<rbrace> c \<lbrace>Q\<rbrace>"
  by (blast intro: conseq_sound)


lemma if_sound[vcg]:
  "\<lbrakk> \<Turnstile> \<lbrace>\<lambda>s. P s \<and> bval b s = Some True \<rbrace> c1 \<lbrace>Q\<rbrace> ; 
     \<Turnstile> \<lbrace>\<lambda>s. P s \<and> bval b s = Some False\<rbrace> c2 \<lbrace>Q\<rbrace> \<rbrakk>  \<Longrightarrow>
        \<Turnstile> \<lbrace>\<lambda>s. P s \<and> bval b s \<noteq> None\<rbrace> IF b THEN c1 ELSE c2 \<lbrace>Q\<rbrace>"
  apply (clarsimp simp:  hoare_valid_def)
  by fastforce
 

definition
  "WhileI b c Inv \<equiv> WHILE b DO c"

notation
  WhileI ("WHILE _ DO _ INV _")

lemma while_inv[vcg]:
  "\<lbrakk> \<Turnstile> \<lbrace>\<lambda>s. Inv s \<and> bval b s = Some True \<rbrace> c \<lbrace>Inv\<rbrace>;
     \<And>s. Inv s \<Longrightarrow> bval b s \<noteq> None; 
     \<And>s. \<lbrakk> bval b s = Some False; Inv s \<rbrakk> \<Longrightarrow> P s \<rbrakk>  \<Longrightarrow>
        \<Turnstile> \<lbrace>Inv\<rbrace> WHILE b DO c INV Inv \<lbrace>P\<rbrace>"
  unfolding WhileI_def
  by (rule conseq_sound, erule while_sound; simp)


lemma  flush_sound[vcg]:
  "\<Turnstile>\<lbrace>\<lambda>s. mode s = Kernel \<and> P (s \<lparr>incon_set := flush_effect f (incon_set s) \<rparr>)\<rbrace>  Flush f \<lbrace>P\<rbrace>"
  apply (clarsimp simp:  hoare_valid_def)
  by auto

lemma updateTTBR0_sound[vcg]:
  "\<Turnstile>\<lbrace>\<lambda>s.  mode s = Kernel \<and> (\<exists>rt. aval ttbr0 s = Some rt \<and> P (s \<lparr>root := Addr rt\<rparr>))\<rbrace>  UpdateTTBR0 ttbr0 \<lbrace>P\<rbrace>"
  apply (clarsimp simp: hoare_valid_def)
  by auto

lemma updateASID_sound[vcg]:
  "\<Turnstile>\<lbrace>\<lambda>s. mode s = Kernel \<and> P (s \<lparr>asid := a \<rparr> )\<rbrace>  UpdateASID a \<lbrace>P\<rbrace>"
  apply (clarsimp simp: hoare_valid_def)
  by auto

lemma set_mode_sound[vcg]:
  "\<Turnstile>\<lbrace>\<lambda>s. mode s = Kernel \<and> P (s \<lparr>mode := flg\<rparr>)\<rbrace>  SetMode flg \<lbrace>P\<rbrace>"
  apply (clarsimp simp: hoare_valid_def)
  by auto

lemma update_rtmap_sound[vcg]:
  "\<Turnstile>\<lbrace>\<lambda>s. \<exists>v. mode s = Kernel \<and>  aval rt s = Some v  \<and> P (s \<lparr>root_map := root_map s (Addr v \<mapsto> a)\<rparr>)\<rbrace>  UpdateRTMap rt a \<lbrace>P\<rbrace>"
  apply (clarsimp simp: hoare_valid_def)
  by auto



end