theory Prg_Logic_prototype

imports  "../MMU_ARM"
        

begin               

type_synonym val        = "32 word"
type_synonym word_type  = "32 word"
type_synonym heap       = "paddr \<rightharpoonup> byte"
type_synonym heap_word  = "paddr \<rightharpoonup> 32 word"
type_synonym rootreg    = "paddr"    (* should we take 32 word only as now we are abstracting logic 
                                   without the details of machine *)


record p_state' =
  MEM   :: "paddr \<rightharpoonup> byte"  (* partial function, none for exceptions. 32 bit output type as this is a dummy language *)
  ASID  :: asid 
  TTBR0 :: "paddr"   (* can be paddr as well *)
  incon_set :: "(asid \<times> 32 word) set"


datatype aexp = Const val 
              | UnOp "(val \<Rightarrow> val)" aexp 
              | BinOp "(val \<Rightarrow> val \<Rightarrow> val)" aexp aexp 
              | HeapLookup aexp
              | RootLookup rootreg   (* Isnt it a separate register *)
              | AsidLookup asid


(* asid lookup is for retrieving/assigning the asid, rootlookup is for assigning the root lookup or reading it, and heap lookup is for 
   assigning things to memory *)


definition 
  load_value_byte_hp :: "heap \<Rightarrow> paddr \<rightharpoonup> val"
where
  "load_value_byte_hp h p = map_option from_bytes (load_list h 4 p)"
             


definition 
  mem_read_byte_heap :: "paddr \<Rightarrow> p_state' \<rightharpoonup> word_type"
where
  "mem_read_byte_heap p s = load_value_byte_hp (p_state'.MEM s) p "


definition
  mem_read_byte_hp' :: "heap \<Rightarrow> paddr \<Rightarrow> vaddr \<rightharpoonup> val"
where
  "mem_read_byte_hp' hp root vp =  (ptable_lift hp root \<rhd>o load_value_byte_hp hp) vp" 



fun aval :: "aexp \<Rightarrow> p_state' \<Rightarrow> val option" where
  "aval (Const c) s = Some c" 
|
  "aval (UnOp f e) s = 
         (case (aval e s) of Some v \<Rightarrow> Some (f v) | None \<Rightarrow> None )"
|                                  
  "aval (BinOp f e1 e2) s =
         (case (aval e1 s , aval e2 s) of (Some v1, Some v2) \<Rightarrow> Some (f v1 v2) | _ \<Rightarrow> None )"
|
  "aval (HeapLookup vp) s = 
         (case (aval vp s) of None \<Rightarrow> None | Some v \<Rightarrow> mem_read_byte_hp' (MEM s) (TTBR0 s) (Addr v))"      (*    Here first we have to check   *)
|
  "aval (RootLookup rt_ad) s =  mem_read_byte_heap rt_ad s"    (*there will always be a root though, we can get none if its not accessible etc*)

(* what we have to do with asid lookup *)
|
  "aval (AsidLookup asid) s =  None"    (* not sure about this one for the time being, why we need this in the language, 
                                                       where it should be used, and what it should return *)
                                        (* if the output is the set of addresses, we should have differend constructors for val *)


datatype bexp = BConst bool 
              | BComp "(val \<Rightarrow> val \<Rightarrow> bool)" aexp aexp 
              | BBinOp "(bool \<Rightarrow> bool \<Rightarrow> bool)" bexp bexp 
              | BNot bexp



fun bval :: "bexp \<Rightarrow> p_state' \<Rightarrow> bool option" where
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
             |  AccessTTBR0
(* add more invalidate commands *)

(* we should first see what we have  *)

inductive
  big_step :: "com \<times> p_state' \<Rightarrow> p_state' option \<Rightarrow> bool" (infix "\<Rightarrow>" 55)
where
Skip:       "(SKIP,s) \<Rightarrow> Some s"   |
AssignFail: "\<lbrakk>aval lval s = None \<or> aval rval s = None \<rbrakk>  \<Longrightarrow> (lval ::= rval , s) \<Rightarrow> None" |
Assign:     "\<lbrakk>aval lval s = Some vp ; aval rval s = Some v ; (ASID s, vp) \<notin> incon_set s ;
              ptable_lift (MEM s) (TTBR0 s) (Addr vp) = Some pp \<rbrakk>  \<Longrightarrow> 
                                     (lval ::= rval , s) \<Rightarrow> Some (s \<lparr> MEM := MEM s (pp \<mapsto> v) \<rparr>)"|  (* here it should be only a value update*)  
Seq:        "\<lbrakk>(c1,s1) \<Rightarrow> Some s2;  (c2,s2) \<Rightarrow> s3 \<rbrakk> \<Longrightarrow> (c1;;c2, s1) \<Rightarrow> s3" |
SeqFail:    "(c1,s1) \<Rightarrow> None \<Longrightarrow> (c1;;c2, s1) \<Rightarrow> None" |
IfTrue:     "\<lbrakk>bval b s = Some True; (c1,s) \<Rightarrow> t \<rbrakk> \<Longrightarrow> (IF b THEN c1 ELSE c2, s) \<Rightarrow> t" |
IfFalse:    "\<lbrakk>bval b s = Some False; (c2,s) \<Rightarrow> t \<rbrakk> \<Longrightarrow> (IF b THEN c1 ELSE c2, s) \<Rightarrow> t" |
IfFail:     "bval b s = None \<Longrightarrow> (IF b THEN c1 ELSE c2, s) \<Rightarrow> None" | 
WhileFalse: "bval b s = Some False \<Longrightarrow> (WHILE b DO c , s) \<Rightarrow> Some s" | 
WhileTrue:  "\<lbrakk>bval b s = Some True ; (c, s) \<Rightarrow> Some s''; (WHILE b DO c , s'') \<Rightarrow> s' \<rbrakk> \<Longrightarrow> (WHILE b DO c , s) \<Rightarrow> s'" |
WhileFail1: "\<lbrakk>bval b s = Some True ; (c, s) \<Rightarrow> None \<rbrakk>\<Longrightarrow> (WHILE b DO c , s) \<Rightarrow> None" |
WhileFail2: "bval b s = None \<Longrightarrow> (WHILE b DO c , s) \<Rightarrow> None" |
InvalidTLB: "(InvlaidTLB, s) \<Rightarrow>  Some s" | (* chagne it here *) 
InvalidASID: "(InvlaidASID, s) \<Rightarrow>  Some s" | (* chagne it here *) 
AccessTTBR0: "(InvlaidTTBR0, s) \<Rightarrow>  Some s" (* chagne it here *) 







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
  WhileE:          "(WHILE b DO c OD, s) \<Rightarrow> s'"

thm SkipE
    AssignE
    SeqE
    IfE
    WhileE
    






end
