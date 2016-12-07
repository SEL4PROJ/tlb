theory Program_Logic

imports Invalid_Ops

begin               



(*------- LOGIC  --------- *)
(*  operational semantics  *)


type_synonym val = "32 word"


datatype aexp = Const val 
              | UnOp "(val \<Rightarrow> val)" aexp 
              | BinOp "(val \<Rightarrow> val \<Rightarrow> val)" aexp aexp 
              | HeapLookup aexp

datatype bexp = BConst bool | 
                BComp "(val \<Rightarrow> val \<Rightarrow> bool)" aexp aexp | 
                BBinOp "(bool \<Rightarrow> bool \<Rightarrow> bool)" bexp bexp |
                BNot bexp



datatype com =  SKIP 
             |  Assign aexp aexp      ("_ ::= _" [1000, 61] 61)
             |  Seq com com           ("_;;/ _"  [60, 61] 60)
             |  If bexp com com       ("(IF _/ THEN _/ ELSE _)"  [0, 0, 61] 61)
             |  While bexp com        ("(WHILE _/ DO _)"  [0, 61] 61)




   (* Semantics *)

fun aval :: "aexp \<Rightarrow> 'a::mem_op state_scheme \<Rightarrow> val option \<times> 'a state_scheme " where
"aval (Const c)  = return (Some c)" |
"aval (BinOp f e1 e2) = do {
                           avale1 <- aval e1;
                           avale2 <- aval e2;
                           case (avale1  , avale2) of (Some v1 , Some v2) \<Rightarrow> return (Some (f v1 v2)) |
                                 _ \<Rightarrow> return (None) }" |
"aval (UnOp f e) = do {
                           avale <- aval e;
                           case avale of Some v \<Rightarrow> return (Some (f v)) |
                                 _ \<Rightarrow> return (None) }" |
"aval (HeapLookup vp)  = do { 
                            avalvp <- aval vp; 
                            case avalvp of None \<Rightarrow> return None  | Some v \<Rightarrow> 
                               do {
                                   bl <-  mmu_read_size (Addr v , 4);
                                   exp <- read_state exception;
                                   if exp = NoException 
                                   then do {
                                      return  
                                        (Some (of_bl (bitstring_field 31 0 bl)))
                                        }
                                   else return None
                                }
                              }"



fun bval :: "bexp \<Rightarrow> 'a::mem_op state_scheme \<Rightarrow> bool option \<times> 'a state_scheme" where
"bval (BConst b)  = return (Some b)" |
"bval (BComp f e1 e2) = do {
                           v1 <- aval e1;
                           v2 <- aval e2;
                           case (v1  , v2) of (Some v1 , Some v2) \<Rightarrow> return (Some (f v1 v2)) |
                                 _ \<Rightarrow> return (None) }" |
"bval (BBinOp f b1 b2) = do {
                           bvale1 <- bval b1;
                           bvale2 <- bval b2;
                           case (bvale1  , bvale2) of (Some v1 , Some v2) \<Rightarrow> return (Some (f v1 v2)) |
                                 _ \<Rightarrow> return (None) }"|
"bval (BNot b)  = do { 
                          bvale <- bval b;
                          case bvale of Some v \<Rightarrow> return (Some (\<not>v)) |
                                 _ \<Rightarrow> return (None) }"



inductive
  big_step :: "com \<times> 'a::mem_op state_scheme \<Rightarrow> 'a state_scheme option \<Rightarrow> bool" (infix "\<Rightarrow>" 55)
where
Skip:       "(SKIP,s) \<Rightarrow> Some s"   |
AssignFail: "\<lbrakk>aval lval s = (None, _) \<or> aval rval s = (None, _) \<rbrakk>  \<Longrightarrow> (lval ::= rval , s) \<Rightarrow> None" |
Assign:     "\<lbrakk>aval lval s = (Some vp, _) ; aval rval s = (Some v, _) \<rbrakk>  \<Longrightarrow> (lval ::= rval , s) \<Rightarrow> None"|
Seq:        "\<lbrakk>(c1,s1) \<Rightarrow> Some s2;  (c2,s2) \<Rightarrow> s3 \<rbrakk> \<Longrightarrow> (c1;;c2, s1) \<Rightarrow> s3" |
SeqFail:    "(c1,s1) \<Rightarrow> None \<Longrightarrow> (c1;;c2, s1) \<Rightarrow> None" |
IfTrue:     "\<lbrakk>bval b s = (Some True, _); (c1,s) \<Rightarrow> t \<rbrakk> \<Longrightarrow> (IF b THEN c1 ELSE c2, s) \<Rightarrow> t" |
IfFalse:    "\<lbrakk>bval b s = (Some False, _); (c2,s) \<Rightarrow> t \<rbrakk> \<Longrightarrow> (IF b THEN c1 ELSE c2, s) \<Rightarrow> t" |
IfFail:     "bval b s = (None,_) \<Longrightarrow> (IF b THEN c1 ELSE c2, s) \<Rightarrow> None" | 
WhileFalse: "bval b s = (Some False,_) \<Longrightarrow> (WHILE b DO c , s) \<Rightarrow> Some s" | 
WhileTrue:  "\<lbrakk>bval b s = (Some True, _) ; (c, s) \<Rightarrow> Some s''; (WHILE b DO c , s'') \<Rightarrow> s' \<rbrakk> \<Longrightarrow> (WHILE b DO c , s) \<Rightarrow> s'" |
WhileFail1: "\<lbrakk>bval b s = (Some True, _) ; (c, s) \<Rightarrow> None \<rbrakk>\<Longrightarrow> (WHILE b DO c , s) \<Rightarrow> None" |
WhileFail2: "bval b s = (None, _) \<Longrightarrow> (WHILE b DO c , s) \<Rightarrow> None" 


thm big_step.induct
lemmas big_step_induct = big_step.induct [split_format (complete)]
thm big_step_induct

inductive_cases
  SkipE [elim!]:   "(SKIP, s) \<Rightarrow> s'" and
  AssignE [elim!]: "(x ::= a, s) \<Rightarrow> s'" and
  SeqE [elim!]:   "(c1;; c2, s) \<Rightarrow> s'" and
  IfE [elim!]:   "(IF b THEN c1 ELSE c2, s) \<Rightarrow> s'" and
  WhileE:          "(WHILE b DO c OD, s) \<Rightarrow> s'"

thm SkipE
    AssignE
    SeqE
    IfE
    WhileE
    


(*type_synonym assn = "state \<Rightarrow> bool" *)

definition
  hoare_valid :: "('a::mem_op state_scheme \<Rightarrow> bool) \<Rightarrow> com \<Rightarrow> ('a::mem_op state_scheme \<Rightarrow> bool) \<Rightarrow> bool" ("\<Turnstile> \<lbrace>(1_)\<rbrace>/ (_)/ \<lbrace>(1_)\<rbrace>" 50) where
  "\<Turnstile> \<lbrace>P\<rbrace> c \<lbrace>Q1\<rbrace> \<equiv> \<forall>s s'. (c,s) \<Rightarrow> s' \<and> P s \<longrightarrow> (\<exists>r. s' = Some r \<and> Q1 r)"

lemma skip_sound:
  "\<Turnstile> \<lbrace>P\<rbrace> SKIP \<lbrace>P\<rbrace>"
  by (clarsimp simp: hoare_valid_def)

lemma seq_sound:
  "\<lbrakk> \<Turnstile> \<lbrace>P\<rbrace> c1 \<lbrace>Q1\<rbrace> \<and> \<Turnstile> \<lbrace>Q1\<rbrace> c2 \<lbrace>R1\<rbrace> \<rbrakk>  \<Longrightarrow> \<Turnstile> \<lbrace>P\<rbrace> c1;;c2 \<lbrace>R1\<rbrace>"
  apply (clarsimp simp: hoare_valid_def)
  by blast


lemma conseq_sound:
  "\<lbrakk> \<Turnstile> \<lbrace>P\<rbrace> c \<lbrace>Q1\<rbrace> \<and> (\<forall>s. P' s \<longrightarrow> P s) \<and> (\<forall>s. Q1 s \<longrightarrow> Q' s) \<rbrakk>  
         \<Longrightarrow> \<Turnstile> \<lbrace>P'\<rbrace> c \<lbrace>Q'\<rbrace>"
  apply (clarsimp simp: hoare_valid_def)
  by blast

lemma conj_sound:
  "\<lbrakk> \<Turnstile> \<lbrace>P\<rbrace> c \<lbrace>Q1\<rbrace> \<and> \<Turnstile> \<lbrace>R1\<rbrace> c \<lbrace>S1\<rbrace> \<rbrakk>  \<Longrightarrow> \<Turnstile> \<lbrace>\<lambda>s. P s \<and> R1 s\<rbrace> c \<lbrace>\<lambda>s. Q1 s \<and> S1 s\<rbrace>"
  apply (clarsimp simp: hoare_valid_def)
  by blast


lemma disj_sound:
  "\<lbrakk> \<Turnstile> \<lbrace>P\<rbrace> c \<lbrace>Q1\<rbrace> \<and> \<Turnstile> \<lbrace>R1\<rbrace> c \<lbrace>S1\<rbrace> \<rbrakk>  \<Longrightarrow> \<Turnstile> \<lbrace>\<lambda>s. P s \<or> R1 s\<rbrace> c \<lbrace>\<lambda>s. Q1 s \<or> S1 s\<rbrace>"
  apply (clarsimp simp: hoare_valid_def)
  by blast


lemma if_sound:
  "\<lbrakk> \<Turnstile> \<lbrace>\<lambda>s. P s \<and> fst (bval b s) = Some True \<rbrace> c1 \<lbrace>Q1\<rbrace> \<and> 
     \<Turnstile> \<lbrace>\<lambda>s. P s \<and> fst (bval b s) = Some False\<rbrace> c2 \<lbrace>Q1\<rbrace> \<rbrakk>  \<Longrightarrow>
        \<Turnstile> \<lbrace>\<lambda>s. P s \<and> fst (bval b s) \<noteq> None\<rbrace> IF b THEN c1 ELSE c2 \<lbrace>Q1\<rbrace>"
  apply (clarsimp simp:  hoare_valid_def)
  by fastforce
 
lemma while_final:
  "\<lbrakk>(prog, s'') \<Rightarrow> s';  
     \<forall>s. P s \<and> fst (bval b s) = Some True \<longrightarrow> (\<forall>s'. (c, s) \<Rightarrow> s' \<longrightarrow> (\<exists>r. s' = Some r \<and> P r));  P s'';
       \<forall>s. P s \<longrightarrow> (\<exists>y. fst (bval b s) = Some y); prog = WHILE b DO c \<rbrakk>  \<Longrightarrow> 
        \<exists>r. s' = Some r \<and> P r \<and> fst (bval b r) = Some False"
  apply(induct rule: big_step_induct)
  apply fastforce+
  done

lemma while_sound:
  "\<lbrakk> \<Turnstile> \<lbrace>\<lambda>s. P s \<and> fst (bval b s) = Some True \<rbrace> c \<lbrace>P\<rbrace> \<and> 
        (\<forall>s. P s \<longrightarrow> fst (bval b s) \<noteq> None) \<rbrakk>  \<Longrightarrow>
        \<Turnstile> \<lbrace>P\<rbrace> WHILE b DO c \<lbrace>\<lambda>s. P s \<and> fst (bval b s) = Some False\<rbrace>"
  apply (clarsimp simp:  hoare_valid_def)
  apply (erule WhileE)
     prefer 2
     apply(rule_tac c = c and s'' = s'' in while_final) apply fastforce +
done

print_theorems 

(* Assign Sound *)
lemma 
  "\<Turnstile> \<lbrace>P\<rbrace> l ::= r \<lbrace>P\<rbrace>" (* remaining *)
  apply (clarsimp simp: hoare_valid_def)

oops



declare [[show_types]]

thm Run_def

thm DecodeARM_def

end