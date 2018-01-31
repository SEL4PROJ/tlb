theory Logic

imports MMU_Prg_Logic


begin

datatype aexp = Const val
              | UnOp "(val \<Rightarrow> val)" aexp
              | BinOp "(val \<Rightarrow> val \<Rightarrow> val)" aexp aexp
              | HeapLookup aexp



datatype bexp = BConst bool
              | BComp "(val \<Rightarrow> val \<Rightarrow> bool)" aexp aexp
              | BBinOp "(bool \<Rightarrow> bool \<Rightarrow> bool)" bexp bexp
              | BNot bexp




datatype com =  SKIP
             |  Assign aexp aexp      ("_ ::= _" [100, 61] 61)
             |  Seq com com           ("_;;/ _"  [60, 61] 60)
             |  If bexp com com       ("(IF _/ THEN _/ ELSE _)"  [0, 0, 61] 61)
             |  While bexp com        ("(WHILE _/ DO _)"  [0, 61] 61)
             |  Flush flush_type
             |  UpdateTTBR0 aexp     
             |  UpdateASID asid
             |  SetMode mode_t



fun aval :: "aexp \<Rightarrow> p_state  \<rightharpoonup> val" ( "\<lbrakk>_\<rbrakk> _" [100, 61] 61) where
  "aval (Const c) s = Some c"
|
  "aval (UnOp f e) s =
         (case (aval e s) of Some v \<Rightarrow> Some (f v) | None \<Rightarrow> None )"
|
  "aval (BinOp f e1 e2) s =
         (case (aval e1 s , aval e2 s) of (Some v1, Some v2) \<Rightarrow> Some (f v1 v2) | _ \<Rightarrow> None )"
|
  "aval (HeapLookup vp) s =
         (case (aval vp s) of None \<Rightarrow> None | Some v \<Rightarrow> mem_read_hp' (asid s) (incon_set s) (heap s) (root s) (mode s) (Addr v))"




fun bval :: "bexp \<Rightarrow> p_state \<rightharpoonup> bool"  ( "\<lbrakk>_\<rbrakk>\<^sub>b _" [100, 61] 61)
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


(*  big step semantics *)

inductive
  big_step :: "com \<times> p_state \<Rightarrow> p_state option \<Rightarrow> bool" (infix "\<Rightarrow>" 55)
where
  Skip:            "(SKIP,s) \<Rightarrow> Some s"
|
  AssignFail1:     "\<lbrakk>aval lval s = None \<or> aval rval s = None \<rbrakk>  \<Longrightarrow> (lval ::= rval , s) \<Rightarrow> None"
|
  AssignFail2:     "\<lbrakk>aval lval s = Some vp ; aval rval s = Some v ; (asid s, Addr vp) \<in> incon_set s \<or>
                           ptable_lift_m (heap s) (root s) (mode s) (Addr vp) = None \<rbrakk>  \<Longrightarrow> (lval ::= rval , s) \<Rightarrow> None"
|
  Assign:          "\<lbrakk>aval lval s = Some vp ; aval rval s = Some v ; (asid s, Addr vp) \<notin> incon_set s;
                         ptable_lift_m (heap s) (root s) (mode s) (Addr vp) = Some pp \<rbrakk>  \<Longrightarrow>
                          (lval ::= rval , s) \<Rightarrow> Some (s \<lparr> heap := heap s (pp \<mapsto> v) ,
                            incon_set := incon_set s \<union>  ptable_comp (asid s)  (heap s)  (heap s (pp \<mapsto> v)) (root s) (root s) \<rparr>)"
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
  Flush:           "mode s = Kernel \<Longrightarrow> (Flush f, s) \<Rightarrow>  Some (s \<lparr>incon_set := flush_effect f (incon_set s) , 
                                                                  ptable_snapshot := flush_effect_snp f (ptable_snapshot s) \<rparr>)"
|
  FlushFail:       "mode s = User \<Longrightarrow> (Flush f, s) \<Rightarrow>  None"
|
  UpdateTTBR0Fail: "mode s = User \<or> aval rt s = None \<Longrightarrow> (UpdateTTBR0 rt, s) \<Rightarrow>  None"
|
  UpdateTTBR0:     "mode s = Kernel \<and> aval rte s = Some rt \<Longrightarrow> (UpdateTTBR0 rte, s) \<Rightarrow>  Some (s \<lparr>root := Addr rt ,
                            incon_set := incon_set s \<union>  ptable_comp (asid s)  (heap s) (heap s) (root s) (Addr rt) \<rparr>)"
|
  UpdateASID:      " \<lbrakk>snp_cur  = snapshot_update_current' (ptable_snapshot s) (({asid s} \<times> UNIV) \<inter> incon_set s) (heap s) (root s) (asid s) ; 
                              il       = incon_load snp_cur a (heap s) (root s) ; 
                              iset'    = ({a} \<times> UNIV) \<inter> (incon_set s); 
                              m_to_h   = miss_to_hit  snp_cur a (heap s) (root s) ;
                              h_to_h   = consistent_hit snp_cur a (heap s) (root s);  
                         mode s = Kernel\<rbrakk> \<Longrightarrow> 
                                 (UpdateASID a , s) \<Rightarrow>  Some (s \<lparr>asid := a , incon_set := incon_set s \<union> il , ptable_snapshot := snapshot_update_new'  snp_cur (iset' \<union> il) m_to_h h_to_h (heap s) (root s) a \<rparr>)"
   (* 'let' gives this error:
      "Conclusion of introduction rule must be an inductive predicate" *)
|
  UpdateASIDFail:  "mode s = User \<Longrightarrow> (UpdateASID a , s) \<Rightarrow>  None"
|
  SetMode:          "mode s = Kernel \<Longrightarrow> (SetMode m, s) \<Rightarrow> Some (s \<lparr>mode := m \<rparr>)"
|
  SetModeFail:      "mode s = User \<Longrightarrow> (SetMode m, s) \<Rightarrow> None"

code_pred big_step .
declare big_step.intros [intro]
thm big_step.induct

lemmas big_step_induct = big_step.induct [split_format (complete)]


inductive_cases
  SkipE [elim!]:   "(SKIP, s) \<Rightarrow> s'" and
  AssignE [elim!]: "(x ::= a, s) \<Rightarrow> s'" and
  SeqE [elim!]:    "(c1;; c2, s) \<Rightarrow> s'" and
  IfE [elim!]:     "(IF b THEN c1 ELSE c2, s) \<Rightarrow> s'" and
  WhileE:          "(WHILE b DO c OD, s) \<Rightarrow> s'" and
  FlushE [elim!]:  "(Flush f, s) \<Rightarrow> s'" and
  TTBR0E [elim!]:  "(UpdateTTBR0 rt, s) \<Rightarrow>  s'" and
  UpdateAE [elim!]:"(UpdateASID a , s) \<Rightarrow>  s'" and
  SetME [elim!]:   "(SetMode flg, s) \<Rightarrow>  s'" 
 


(* first do it without the root_map *)


definition "snp_incon_subset s \<equiv>  {(a,v). ptable_snapshot s a v = Incon }  \<subseteq>  incon_set s"
(*

lemma [simp]:
  "\<lbrakk>(x1 ::= x2, s) \<Rightarrow> Some s' ; snp_incon_subset s\<rbrakk> \<Longrightarrow> snp_incon_subset s'"
  apply (clarsimp simp: snp_incon_subset_def)
  by force

lemma [simp] :
  "\<lbrakk>(Flush x, s) \<Rightarrow> Some s'; snp_incon_subset s\<rbrakk> \<Longrightarrow> snp_incon_subset s'"
  apply (erule FlushE ; simp)
  apply (induct x arbitrary: s s' ; clarsimp simp: snp_incon_subset_def split: if_split_asm)
  by force+

lemma [simp]:
  "\<lbrakk>(UpdateTTBR0 x, s) \<Rightarrow> Some s'; snp_incon_subset s\<rbrakk> \<Longrightarrow> snp_incon_subset s'"
  apply (clarsimp simp: snp_incon_subset_def)
  by force

lemma [simp]:
  "\<lbrakk>(SetMode x, s) \<Rightarrow> Some s'; snp_incon_subset s\<rbrakk> \<Longrightarrow> snp_incon_subset s'"
  apply (clarsimp simp: snp_incon_subset_def)
  by force

lemma  [simp]:
  "\<lbrakk>(UpdateASID x, s) \<Rightarrow> Some s'; snp_incon_subset s\<rbrakk> \<Longrightarrow> snp_incon_subset s'"
  apply (erule UpdateAE ; simp)
  apply (clarsimp simp: snp_incon_subset_def incon_load_def snapshot_update_current'_def
         snapshot_update_current_def snapshot_update_new'_def snapshot_update_new_def split: if_split_asm)
  by force+
 
*)

theorem
  shows "(c,s) \<Rightarrow> s' \<Longrightarrow> snp_incon_subset s \<Longrightarrow> s' = Some s'' \<Longrightarrow> snp_incon_subset s''"
proof (induct arbitrary: s'' rule: big_step_induct)
next
  case (Assign lval s1 vp rval v pp)
  thus ?case by (force simp: snp_incon_subset_def)
next
  case SetMode
  thus ?case by (force simp: snp_incon_subset_def)
next
  case UpdateTTBR0
  thus ?case by (force simp: snp_incon_subset_def)
next 
  case UpdateASID
  thus ?case by (force simp: snp_incon_subset_def incon_load_def snapshot_update_current'_def
                             snapshot_update_current_def snapshot_update_new'_def snapshot_update_new_def split: if_split_asm)
next 
  case (Flush s f)
  thus ?case by (induct f; clarsimp simp: snp_incon_subset_def split: if_split_asm ; force)
qed auto




(* snap_incon_subset rlues  *)

(* an option, generic form of snap_incon_subset, f will be root_map later *)

(*
definition "gen_f f S s \<equiv> (ran (f s) - S)"

definition "snp_incon_subset' f S s \<equiv> 
               {(a,v). a\<in> gen_f f S s \<and> ptable_snapshot s a v = Incon }  \<subseteq>  incon_set s"


*)


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

method vcgm declares vcg = (rule vcg_pre, (rule vcg)+, (assumption|clarsimp split del: if_split)?)


lemma skip_sound[vcg]:
  "\<Turnstile> \<lbrace>P\<rbrace> SKIP \<lbrace>P\<rbrace>"
  by (clarsimp simp: hoare_valid_def)

lemma  assign_sound[vcg]:
  " \<Turnstile> \<lbrace>\<lambda>s. \<exists>vp v pp. aval l s = Some vp \<and> aval r s = Some v \<and> (asid s , Addr vp) \<notin> incon_set s \<and>
   P (s \<lparr>heap := heap s (pp \<mapsto> v) , incon_set := incon_set s \<union>
            ptable_comp (asid s)  (heap s)  (heap s (pp \<mapsto> v)) (root s) (root s)\<rparr>)
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
  "\<Turnstile>\<lbrace>\<lambda>s. mode s = Kernel \<and> P (s \<lparr>incon_set := flush_effect f (incon_set s), 
                              ptable_snapshot := flush_effect_snp f (ptable_snapshot s) \<rparr>)\<rbrace>  Flush f \<lbrace>P\<rbrace>"
  apply (clarsimp simp:  hoare_valid_def)
  by auto

lemma updateTTBR0_sound[vcg]:
  "\<Turnstile>\<lbrace>\<lambda>s.  mode s = Kernel \<and> (\<exists>rt. aval ttbr0 s = Some rt \<and> P (s \<lparr>root := Addr rt ,
       incon_set := incon_set s \<union>
            ptable_comp (asid s)  (heap s)  (heap s) (root s) (Addr rt)\<rparr>))\<rbrace>  UpdateTTBR0 ttbr0 \<lbrace>P\<rbrace>"
  apply (clarsimp simp: hoare_valid_def)
  by auto

lemma updateASID_sound[vcg]:
  "\<Turnstile>\<lbrace>\<lambda>s.  \<exists>snp_cur il iset' m_to_h' m_to_h h_to_h. mode s = Kernel \<and> snp_cur  = snapshot_update_current' (ptable_snapshot s) (({asid s} \<times> UNIV) \<inter> incon_set s) (heap s) (root s) (asid s) \<and> 
                              il       = incon_load snp_cur a (heap s) (root s) \<and>
                              iset'    = ({a} \<times> UNIV) \<inter> (incon_set s) \<and>
                              m_to_h   = miss_to_hit  snp_cur a (heap s) (root s) \<and>
                              h_to_h   = consistent_hit snp_cur a (heap s) (root s) \<and> 
          P (s \<lparr>asid := a , incon_set := incon_set s \<union> il , ptable_snapshot := snapshot_update_new'  snp_cur (iset' \<union> il) m_to_h h_to_h (heap s) (root s) a \<rparr> )\<rbrace>  UpdateASID a \<lbrace>P\<rbrace>"
  apply (clarsimp simp: hoare_valid_def)
  by auto


lemma set_mode_sound[vcg]:
  "\<Turnstile>\<lbrace>\<lambda>s. mode s = Kernel \<and> P (s \<lparr>mode := flg\<rparr>)\<rbrace>  SetMode flg \<lbrace>P\<rbrace>"
  apply (clarsimp simp: hoare_valid_def)
  by auto




end
