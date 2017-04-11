theory Prg_Logic

imports  "../MMU_ARM"
        

begin               

type_synonym val        = "32 word"
type_synonym word_type  = "32 word"
type_synonym heap       = "paddr \<rightharpoonup> byte"
type_synonym heap_word  = "paddr \<rightharpoonup> 32 word"
type_synonym rootreg    = "paddr"    (* should we take 32 word only as now we are abstracting logic 
                                   without the details of machine *)


record p_state =
  MEM   :: "paddr \<rightharpoonup> word_type"  (* partial function, none for exceptions. 32 bit output type as this is a dummy language *)
  ASID  :: asid 
  TTBR0 :: "paddr"   (* can be paddr as well *)
  incon_set :: "(asid \<times> 32 word) set"


datatype aexp = Const val 
              | UnOp "(val \<Rightarrow> val)" aexp 
              | BinOp "(val \<Rightarrow> val \<Rightarrow> val)" aexp aexp 
              | HeapLookup aexp
              | RootLookup rootreg   (* Isnt it a separate register *)
              | AsidLookup asid    (* not sure about that *)



definition 
  load_list_word_hp :: "heap_word \<Rightarrow> nat \<Rightarrow> paddr \<rightharpoonup> val list"
where
  "load_list_word_hp h n p = load_list h n p"

definition
  from_word :: "32 word list => 'b :: len0 word" where
  "from_word \<equiv> word_rcat \<circ> rev"

definition 
  load_value_word_hp :: "heap_word \<Rightarrow> paddr \<rightharpoonup> val"
where
  "load_value_word_hp h p = map_option from_word (load_list_word_hp h 4 p)"


definition 
  mem_read_word_heap :: "paddr \<Rightarrow> p_state \<rightharpoonup> word_type"
where
  "mem_read_word_heap p s = load_value_word_hp (p_state.MEM s) p "
          

definition
  decode_heap_pde' :: "heap_word \<Rightarrow> paddr \<rightharpoonup> pde" where
  "decode_heap_pde' h p \<equiv> 
     map_option decode_pde ( h p)"

definition
  get_pde' :: "heap_word \<Rightarrow> paddr \<Rightarrow> vaddr \<rightharpoonup> pde" where
  "get_pde' h root vp \<equiv>
     let 
       pd_idx_offset = ((vaddr_pd_index (addr_val vp)) << 2)
     in
       decode_heap_pde' h (root r+ pd_idx_offset)"

definition
  decode_heap_pte' :: "heap_word \<Rightarrow> paddr \<rightharpoonup> pte" where
  "decode_heap_pte' h p \<equiv> map_option decode_pte (h p)"


definition
  get_pte' :: "heap_word \<Rightarrow> paddr \<Rightarrow> vaddr \<rightharpoonup> pte" where
  "get_pte' h pt_base vp \<equiv> 
     let 
       pt_idx_offset = ((vaddr_pt_index (addr_val vp)) << 2) 
     in
       decode_heap_pte' h (pt_base r+ pt_idx_offset)"


definition
  lookup_pte' :: "heap_word \<Rightarrow> paddr \<Rightarrow> vaddr \<rightharpoonup> (paddr \<times> page_type \<times> arm_perm_bits)"
  where
  "lookup_pte' h pt_base vp \<equiv>
   case_option None
    (\<lambda>pte. case pte 
             of InvalidPTE \<Rightarrow> None
              | SmallPagePTE base perms \<Rightarrow> Some (base, ArmSmallPage, perms))
    (get_pte' h pt_base vp)"


definition
  lookup_pde' :: "heap_word \<Rightarrow> paddr \<Rightarrow> vaddr \<rightharpoonup> (paddr \<times> page_type \<times> arm_perm_bits)"
  where
  "lookup_pde' h root vp \<equiv>
   case_option None
    (\<lambda>pde. case pde 
            of InvalidPDE \<Rightarrow> None
             | ReservedPDE \<Rightarrow> None
             | SectionPDE base perms \<Rightarrow> Some (base, ArmSection, perms)
             | PageTablePDE pt_base \<Rightarrow> lookup_pte' h pt_base vp)
    (get_pde' h root vp)"


definition
  ptable_lift' :: "heap_word \<Rightarrow> paddr \<Rightarrow> vaddr \<rightharpoonup> paddr" where
  "ptable_lift' h pt_root vp \<equiv>
     let
       vp_val = addr_val vp
     in
       map_option 
         (\<lambda>(base, pg_size, perms). 
             base r+ (vaddr_offset pg_size vp_val))
         (lookup_pde' h pt_root vp)"


definition
  mem_read_word_hp' :: "heap_word \<Rightarrow> paddr \<Rightarrow> vaddr \<rightharpoonup> val"
where
  "mem_read_word_hp' hp root vp =  (ptable_lift' hp root \<rhd>o load_value_word_hp hp) vp" 



fun aval :: "aexp \<Rightarrow> p_state \<Rightarrow> val option" where
  "aval (Const c) s = Some c" 
|
  "aval (UnOp f e) s = 
         (case (aval e s) of Some v \<Rightarrow> Some (f v) | None \<Rightarrow> None )"
|                                  
  "aval (BinOp f e1 e2) s =
         (case (aval e1 s , aval e2 s) of (Some v1, Some v2) \<Rightarrow> Some (f v1 v2) | _ \<Rightarrow> None )"
|
  "aval (HeapLookup vp) s = 
         (case (aval vp s) of None \<Rightarrow> None | Some v \<Rightarrow> mem_read_word_hp' (MEM s) (TTBR0 s) (Addr v))"     
|
  "aval (RootLookup rt_ad) s =  mem_read_word_heap rt_ad s"    

(* what we have to do with asid lookup *)
(*|
  "aval (AsidLookup asid) s =  None"  *)   (* not sure about this one for the time being, why we need this in the language, 
                                                       where it should be used, and what it should return *)
                                        (* if the output is the set of addresses, we should have differend constructors for val *)


datatype bexp = BConst bool 
              | BComp "(val \<Rightarrow> val \<Rightarrow> bool)" aexp aexp 
              | BBinOp "(bool \<Rightarrow> bool \<Rightarrow> bool)" bexp bexp 
              | BNot bexp



fun bval :: "bexp \<Rightarrow> p_state \<Rightarrow> bool option" where
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



datatype com =  SKIP 
             |  Assign aexp aexp      ("_ ::= _" [1000, 61] 61)
             |  Seq com com           ("_;;/ _"  [60, 61] 60)
             |  If bexp com com       ("(IF _/ THEN _/ ELSE _)"  [0, 0, 61] 61)
             |  While bexp com        ("(WHILE _/ DO _)"  [0, 61] 61)
             |  InvalidTLB
             |  InvalidASID 
             |  UpdateTTBR0 aexp
(* add more invalidate commands *)

(* we should first see what we have  *)

inductive
  big_step :: "com \<times> p_state \<Rightarrow> p_state option \<Rightarrow> bool" (infix "\<Rightarrow>" 55)
where
  Skip:       "(SKIP,s) \<Rightarrow> Some s"   
|
  AssignFail1: "\<lbrakk>aval lval s = None \<or> aval rval s = None \<rbrakk>  \<Longrightarrow> (lval ::= rval , s) \<Rightarrow> None" 
|
  AssignFail2: "\<lbrakk>aval lval s = Some vp ; aval rval s = Some v ; (ASID s, vp) \<in> incon_set s \<or>
                 ptable_lift' (MEM s) (TTBR0 s) (Addr vp) = None \<rbrakk>  \<Longrightarrow> (lval ::= rval , s) \<Rightarrow> None"  (* trivial? *)
|
  Assign:     "\<lbrakk>aval lval s = Some vp ; aval rval s = Some v ; (ASID s, vp) \<notin> incon_set s ;
                ptable_lift' (MEM s) (TTBR0 s) (Addr vp) = Some pp \<rbrakk>  \<Longrightarrow> 
                                     (lval ::= rval , s) \<Rightarrow> Some (s \<lparr> MEM := MEM s (pp \<mapsto> v) \<rparr>)"
| 
  Seq:        "\<lbrakk>(c1,s1) \<Rightarrow> Some s2;  (c2,s2) \<Rightarrow> s3 \<rbrakk> \<Longrightarrow> (c1;;c2, s1) \<Rightarrow> s3" 
|
  SeqFail:    "(c1,s1) \<Rightarrow> None \<Longrightarrow> (c1;;c2, s1) \<Rightarrow> None" 
|
  IfTrue:     "\<lbrakk>bval b s = Some True; (c1,s) \<Rightarrow> t \<rbrakk> \<Longrightarrow> (IF b THEN c1 ELSE c2, s) \<Rightarrow> t" 
|
  IfFalse:    "\<lbrakk>bval b s = Some False; (c2,s) \<Rightarrow> t \<rbrakk> \<Longrightarrow> (IF b THEN c1 ELSE c2, s) \<Rightarrow> t" 
|
  IfFail:     "bval b s = None \<Longrightarrow> (IF b THEN c1 ELSE c2, s) \<Rightarrow> None" 
| 
  WhileFalse: "bval b s = Some False \<Longrightarrow> (WHILE b DO c, s) \<Rightarrow> Some s" 
| 
  WhileTrue:  "\<lbrakk>bval b s = Some True; (c, s) \<Rightarrow> Some s''; (WHILE b DO c, s'') \<Rightarrow> s' \<rbrakk> \<Longrightarrow> (WHILE b DO c, s) \<Rightarrow> s'" 
|
  WhileFail1: "\<lbrakk>bval b s = Some True; (c, s) \<Rightarrow> None \<rbrakk>\<Longrightarrow> (WHILE b DO c, s) \<Rightarrow> None" 
|
  WhileFail2: "bval b s = None \<Longrightarrow> (WHILE b DO c , s) \<Rightarrow> None" 
|
  InvalidTLB: "(InvalidTLB, s) \<Rightarrow>  Some (s \<lparr> incon_set := {} \<rparr>)" 
| (* change it here *) 
  InvalidASID: "(InvalidASID, s) \<Rightarrow>  Some s" 
| 
  AccessTTBR0Fail: "aval rt s = None \<Longrightarrow> (UpdateTTBR0 rt, s) \<Rightarrow>  None" 
|
  AccessTTBR0: "aval rt s = Some v \<Longrightarrow> (UpdateTTBR0 rt, s) \<Rightarrow>  Some (s \<lparr> TTBR0 := Addr v \<rparr>)" 




print_theorems 
code_pred big_step .
declare big_step.intros [intro]
thm big_step.induct

lemmas big_step_induct = big_step.induct [split_format (complete)]
thm big_step_induct

inductive_cases
  SkipE [elim!]:   "(SKIP, s) \<Rightarrow> s'" and
  AssignE [elim!]: "(x ::= a, s) \<Rightarrow> s'" and
  SeqE [elim!]:   "(c1;; c2, s) \<Rightarrow> s'" and
  IfE [elim!]:   "(IF b THEN c1 ELSE c2, s) \<Rightarrow> s'" and
  WhileE:          "(WHILE b DO c OD, s) \<Rightarrow> s'" and
  TTBR0E [elim!]:  "(UpdateTTBR0 rt, s) \<Rightarrow>  s'"


thm SkipE
    AssignE
    SeqE
    IfE
    WhileE
    TTBR0E




definition
  hoare_valid :: "(p_state \<Rightarrow> bool) \<Rightarrow> com \<Rightarrow> (p_state \<Rightarrow> bool) \<Rightarrow> bool" ("\<Turnstile> \<lbrace>(1_)\<rbrace>/ (_)/ \<lbrace>(1_)\<rbrace>" 50) where
  "\<Turnstile> \<lbrace>P\<rbrace> c \<lbrace>Q1\<rbrace> \<equiv> \<forall>s s'. (c,s) \<Rightarrow> s' \<and> P s \<longrightarrow> (\<exists>r. s' = Some r \<and> Q1 r)"


lemma skip_sound:
  "\<Turnstile> \<lbrace>P\<rbrace> SKIP \<lbrace>P\<rbrace>"
  by (clarsimp simp: hoare_valid_def)

lemma  assign_sound:
  " \<Turnstile> \<lbrace>\<lambda>s. aval l s = Some vp \<and> aval r s = Some v \<and> (ASID s, vp) \<notin> incon_set s \<and>
           P (s \<lparr>MEM := MEM s (pp \<mapsto> v)\<rparr>) \<and>  ptable_lift' (MEM s) (TTBR0 s) (Addr vp) = Some pp\<rbrace>  l ::= r \<lbrace>P\<rbrace>" 
  apply (clarsimp simp: hoare_valid_def)
  apply auto
done

lemma seq_sound:
  "\<lbrakk> \<Turnstile> \<lbrace>P\<rbrace> c1 \<lbrace>QQ\<rbrace> ; \<Turnstile> \<lbrace>QQ\<rbrace> c2 \<lbrace>R1\<rbrace> \<rbrakk>  \<Longrightarrow> \<Turnstile> \<lbrace>P\<rbrace> c1;;c2 \<lbrace>R1\<rbrace>"
  apply (clarsimp simp: hoare_valid_def)
  by blast


lemma conseq_sound:
  "\<lbrakk> \<Turnstile> \<lbrace>P\<rbrace> c \<lbrace>Q1\<rbrace> ; (\<forall>s. P' s \<longrightarrow> P s) \<and> (\<forall>s. Q1 s \<longrightarrow> Q' s) \<rbrakk>  
         \<Longrightarrow> \<Turnstile> \<lbrace>P'\<rbrace> c \<lbrace>Q'\<rbrace>"
  apply (clarsimp simp: hoare_valid_def)
  by blast

lemma conj_sound:
  "\<lbrakk> \<Turnstile> \<lbrace>P\<rbrace> c \<lbrace>Q1\<rbrace> ; \<Turnstile> \<lbrace>R1\<rbrace> c \<lbrace>S1\<rbrace> \<rbrakk>  \<Longrightarrow> \<Turnstile> \<lbrace>\<lambda>s. P s \<and> R1 s\<rbrace> c \<lbrace>\<lambda>s. Q1 s \<and> S1 s\<rbrace>"
  apply (clarsimp simp: hoare_valid_def)
  by blast


lemma disj_sound:
  "\<lbrakk> \<Turnstile> \<lbrace>P\<rbrace> c \<lbrace>Q1\<rbrace> ; \<Turnstile> \<lbrace>R1\<rbrace> c \<lbrace>S1\<rbrace> \<rbrakk>  \<Longrightarrow> \<Turnstile> \<lbrace>\<lambda>s. P s \<or> R1 s\<rbrace> c \<lbrace>\<lambda>s. Q1 s \<or> S1 s\<rbrace>"
  apply (clarsimp simp: hoare_valid_def)
  by blast


lemma if_sound:
  "\<lbrakk> \<Turnstile> \<lbrace>\<lambda>s. P s \<and> bval b s = Some True \<rbrace> c1 \<lbrace>Q1\<rbrace> ; 
     \<Turnstile> \<lbrace>\<lambda>s. P s \<and> bval b s = Some False\<rbrace> c2 \<lbrace>Q1\<rbrace> \<rbrakk>  \<Longrightarrow>
        \<Turnstile> \<lbrace>\<lambda>s. P s \<and> bval b s \<noteq> None\<rbrace> IF b THEN c1 ELSE c2 \<lbrace>Q1\<rbrace>"
  apply (clarsimp simp:  hoare_valid_def)
  by fastforce
 
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






end
