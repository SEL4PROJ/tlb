theory Translation_Abs
  imports arm_12
          
begin


declare return_def [simp add]


(* start from the l3 vlaid def  *)

(*  then state the lemma *)






(*  and then see the simplification rules  *)







definition 
  excp_pas :: "('a \<Rightarrow> 'b state_scheme) \<Rightarrow> ('a \<Rightarrow> 'c \<times> 'a) \<Rightarrow> bool"
where
  "excp_pas prj f \<equiv> (\<forall> s s' a. f s = (a,s') \<longrightarrow> exception (prj s') = NoException \<longrightarrow> exception (prj s) = NoException)"


lemma excp_pas_bind [intro!, simp]:
  "\<lbrakk>(\<And>x. excp_pas prj (g x)); excp_pas prj f \<rbrakk> \<Longrightarrow> excp_pas prj (bind f g)"
  apply (clarsimp simp: excp_pas_def bind_def)
  apply (clarsimp simp: split_def)
  using prod.exhaust_sel by blast

lemma excp_pas_pair_simp [intro!, simp]:
  "excp_pas prj (Pair p)"
  by (clarsimp simp: excp_pas_def)

lemma excp_pas_read_st_simp [intro!, simp]:
  "excp_pas prj (read_state f)"
  by (clarsimp simp: excp_pas_def read_state_def)

lemma excp_pas_extend_st_simp [intro!, simp]:
  "excp_pas (prj o snd) f \<Longrightarrow> excp_pas prj (extend_state v f)"
  unfolding extend_state_def excp_pas_def
  by (fastforce split: prod.splits)

(*
lemma
  "\<forall>s. exception (f s) \<noteq> NoException \<Longrightarrow> excp_pas prj (update_state f)"
  apply (clarsimp simp: excp_pas_def update_state_def)
  oops
*)

(*  we have to have the record update simplifiers *)

thm update_state_def

(*lemma excp_pas_update_st_mem_simp [intro!, simp]:
  "excp_pas prj (update_state (MEM_update v))"
  apply (clarsimp simp: excp_pas_def update_state_def)

*)


lemma excp_pas_if_else [intro!, simp]:
  "\<lbrakk> b \<longrightarrow> excp_pas prj f; \<not>b \<longrightarrow> excp_pas prj g \<rbrakk> \<Longrightarrow> 
     excp_pas prj (\<lambda>s. if b then f s else g s ) "
  by (clarsimp simp: excp_pas_def split: if_split_asm)

lemma excp_pas_if_else' [intro!, simp]:
  "\<lbrakk> \<forall>s. b s \<longrightarrow> excp_pas prj f; \<forall>s. \<not>b s \<longrightarrow> excp_pas prj g \<rbrakk> \<Longrightarrow> 
     excp_pas prj (\<lambda>s. if b s then f s else g s ) "
  apply (clarsimp simp: excp_pas_def split: if_split_asm)
  by blast

lemma excp_pas_if_else'' [intro!, simp]:
  "\<lbrakk> b \<longrightarrow> excp_pas prj f; \<not>b \<longrightarrow>excp_pas prj g \<rbrakk> \<Longrightarrow>  excp_pas prj (if b then f  else g  ) "
  by (clarsimp simp: excp_pas_def split: if_split_asm)

(*lemma excp_pas_raise_excp [intro!, simp]:
  "excp_pas id (raise'exception e)"
  oops
*)

lemma translation_root_excp [intro!, simp]:
  "excp_pas prj (translation_root mva)"
  by (clarsimp simp: translation_root_def)

lemma  HaveSecurityExt_excp [intro!, simp]:
  "excp_pas prj (HaveSecurityExt ())"
  by (clarsimp simp: HaveSecurityExt_def)


lemma excp_pas_pair_raise_excp' [intro!, simp]:
  "excp_pas id (case x of None \<Rightarrow> raise'exception (UNPREDICTABLE ''undefined memory'') | Some v \<Rightarrow> Pair v)"
  apply (clarsimp split: option.splits)
  apply (clarsimp simp: raise'exception_def)
  apply (rule+; clarsimp?)
  apply (clarsimp simp: excp_pas_def update_state_def)
  (* the assumption is false  *)

  oops


lemma excp_pas_pair_mem1 [intro!, simp]:
  "excp_pas prj (mem1 p)"
  apply (clarsimp simp: mem1_def)
  apply (rule excp_pas_bind; clarsimp)
  apply (rule excp_pas_bind; clarsimp simp:  option.splits) 
  oops


lemma excp_pas_pair_mem [intro!, simp]:
  "excp_pas prj (mem (p, n))"
  (* apply (clarsimp simp: mem_def) *)

  oops

lemma excp_pas_pair_write_mem [intro!, simp]:
  "excp_pas prj (write'mem (bl, p, n))"
  apply (clarsimp simp: write'mem_def)
  oops

lemma level1_desc_address_and_desc_excp:
  "excp_pas prj (level1_desc_address_and_desc (a, b, mva))"
  apply (simp only: level1_desc_address_and_desc_def)
  sorry

lemma level2_desc_address_and_desc_excp_pas:
  "excp_pas prj (level2_desc_address_and_desc (b, mva, a))"
  apply (simp only: level2_desc_address_and_desc_def)
  sorry



 lemma writing_access_flag_excp_pas:
  "excp_pas id (writing_access_flag (a, b, c, d, e ,f, g ,h, i, j,k, l, m))"
   apply (clarsimp simp: writing_access_flag_def)
   sorry

lemma TLBResult_excp_pas:
  "excp_pas prj (TLBResult (a, b, c, d, e, f, g, h, i, j, k, l))"
  (*apply (clarsimp simp: TLBResult_def) *)
  sorry



lemma word_mask_two_bits_false [simp]:
  "\<lbrakk>n < 31; ucast ((w:: 32 word) && 3) \<noteq> (0 :: 2 word); ucast (w && 3) \<noteq> (1 :: 2 word); 
      ucast (w && 3) \<noteq> (2 :: 2 word); ucast (w && 3) \<noteq> (3 :: 2 word)\<rbrakk> \<Longrightarrow> False"
   apply word_bitwise
  by force


lemma remaining_induct_n[simp]:
  "\<lbrakk>word_extract (Suc n) n (w:: 32 word) \<noteq> (0 :: 2 word);
    word_extract (Suc n) n w \<noteq> (1 :: 2 word);
    word_extract (Suc n) n w \<noteq> (2 :: 2 word);
    word_extract (Suc n) n w \<noteq> (3 :: 2 word); (n:: nat) < 32 ;  n < 31 \<rbrakk> \<Longrightarrow> False"
  apply (clarsimp simp: word_extract_def word_bits_def mask_def )
  by (frule_tac w = "(w >> n)" in  word_mask_two_bits_false; clarsimp)



(*lemma two_bits_width_false [simp]: 
  "\<lbrakk> word_extract (Suc 0) 0 (w :: 32 word) \<noteq> (0::2 word); word_extract (Suc 0) 0 w \<noteq> 1;
      word_extract (Suc 0) 0 w \<noteq> 2;  word_extract (Suc 0) 0 w \<noteq> 3  \<rbrakk> \<Longrightarrow>  False"
  apply (clarsimp simp: word_extract_def word_bits_def mask_def)
  by word_bitwise
*)

lemma  TranslationTableWalkSD_exp_pas:
  "excp_pas 
   (TranslationTableWalkSD (mva, iswrite, sz))"              
  apply (clarsimp simp: TranslationTableWalkSD_def)
  apply ((rule; clarsimp), (rule;clarsimp), (rule  ; clarsimp))
  apply (rule, clarsimp simp: level1_desc_address_and_desc_excp)
  apply (rule allI, simp only: split_def)
  apply (rule excp_pas_if_else'')
  apply (rule)+
   apply (clarsimp simp: Let_def, safe; (clarsimp simp: level2_desc_address_and_desc_excp_pas writing_access_flag_excp_pas TLBResult_excp_pas)?)
  apply (rule, clarsimp simp only: Let_def)
  apply (rule) apply (rule impI) apply rule apply simp apply (rule allI)  
   apply ((rule)+,(clarsimp simp: TLBResult_excp_pas)+)
  by (drule remaining_induct_n; clarsimp)
 

(* have a clear configuration for the mmu state *)


definition 
  MMU_config_assert_isa :: "'a state_scheme \<Rightarrow> bool"
where
  "MMU_config_assert_isa s \<equiv>  Architecture s = ARMv7_A \<and> 
                              Extensions s = {} \<and>
                              PID (FCSEIDR(CP15 s)) = 0 \<and>
                              PSR.M (CPSR s) \<in> {0x10, 0x1F} \<and>
                              \<not>HSCTLR.M (HSCTLR(CP15 s))  \<and>
                              VSCTLR.M (VSCTLR(CP15 s)) \<and>
                              TTBCR.N (TTBCR(CP15 s)) = 0 \<and> 
                              \<not>TTBCR.PD0 (TTBCR(CP15 s))  \<and> 
                              \<not>reg'TTBR0 (TTBR0 (CP15 s)) !! 0 \<and>
                              \<not>VSCTLR.EE (VSCTLR(CP15 s)) \<and>
                              VSCTLR.AFE (VSCTLR(CP15 s)) \<and>
                              VSCTLR.TRE (VSCTLR(CP15 s))"


lemma sanity_check_MMU_config_assert:
  "MMU_config_assert () s = (True, s) \<Longrightarrow> MMU_config_assert_isa s"
  by (clarsimp simp: MMU_config_assert_def MMU_config_assert_isa_def  bind_def split_def read_state_def
                   split:if_split_asm)


definition 
  "mmu_config f \<equiv> 
        (\<forall> s s'. snd (f s) = s' \<longrightarrow>
                 MMU_config_assert_isa s \<longrightarrow> MMU_config_assert_isa s' )"


lemma mmu_config_bind [intro!, simp]:
  "\<lbrakk> mmu_config f; \<forall> x. mmu_config (g x) \<rbrakk> \<Longrightarrow> mmu_config (bind f g)"
  apply (clarsimp simp: mmu_config_def bind_def)
  by (clarsimp simp: split_def)



lemma mmu_config_if_else [intro!, simp]:
  "\<lbrakk> b \<longrightarrow> mmu_config f; \<not>b \<longrightarrow> mmu_config g \<rbrakk> \<Longrightarrow> 
     mmu_config (\<lambda>s. if b then f s else g s ) "
  by (clarsimp simp: mmu_config_def split: if_split_asm)

lemma mmu_config_if_else' [intro!, simp]:
  "\<lbrakk> b \<longrightarrow> mmu_config f; \<not>b \<longrightarrow> mmu_config g \<rbrakk> \<Longrightarrow> 
     mmu_config (if b then f else g ) "
  by (clarsimp simp: mmu_config_def split: if_split_asm)

lemma mmu_config_pair_simp [intro!, simp]:
  "mmu_config (Pair ())"
  by (clarsimp simp: mmu_config_def)
  

lemma mmu_config_read_st_simp [intro!, simp]:
  "mmu_config (read_state f)"
  by (clarsimp simp: mmu_config_def)


lemma mmu_config_update_st_mem_simp [intro!, simp]:
  "mmu_config (update_state (MEM_update v))"
  by (clarsimp simp: mmu_config_def MMU_config_assert_isa_def bind_def read_state_def)


lemma mmu_config_raise_excp [intro!, simp]:
  "mmu_config (raise'exception e)"
  apply (clarsimp simp: mmu_config_def raise'exception_def fst_def snd_def)
  by (clarsimp simp: bind_def read_state_def update_state_def MMU_config_assert_isa_def split: if_split_asm)


lemma mmu_config_pair_simp' [intro!, simp]:
  "mmu_config (Pair p)"
  by (clarsimp simp: mmu_config_def)

lemma mmu_config_pair_raise_excp' [intro!, simp]:
  "mmu_config (case x of None \<Rightarrow> raise'exception (UNPREDICTABLE ''undefined memory'') | Some v \<Rightarrow> Pair v)"
  by (clarsimp split: option.splits)


lemma mmu_config_pair_mem1 [intro!, simp]:
  "mmu_config (mem1 p)"
  apply (clarsimp simp: mem1_def)
  apply (rule mmu_config_bind; clarsimp)
  by (rule mmu_config_bind; clarsimp simp:  option.splits) 
  


lemma mmu_config_pair_mem [intro!, simp]:
  "mmu_config (mem (p, n))"
  by (clarsimp simp: mem_def)
 

lemma mmu_config_pair_write_mem [intro!, simp]:
  "mmu_config (write'mem (bl, p, n))"
  by (clarsimp simp: write'mem_def)


lemma mmu_config_translation_root [intro!, simp]:
  "mmu_config (translation_root va)"
  by (clarsimp simp: translation_root_def)


lemma mmu_config_HaveSecurityExt [intro!, simp]:
  "mmu_config (HaveSecurityExt ())"
  by (clarsimp simp: HaveSecurityExt_def)

lemma mmu_config_level1_desc_address_and_desc:
  "mmu_config (level1_desc_address_and_desc (a, b, mva))"
  sorry

lemma mmu_config_level2_desc_address_and_desc:
  "mmu_config (level2_desc_address_and_desc (b, mva, a))"
  sorry


lemma mmu_config_writing_access_flag:
  "mmu_config (writing_access_flag (a, b, c, d, e ,f, g ,h, i, j,k, l, m))"
  by (clarsimp simp: writing_access_flag_def)

lemma mmu_config_TLBResult:
  "mmu_config (TLBResult (a, b, c, d, e, f, g, h, i, j, k, l))"
  apply (clarsimp simp: TLBResult_def)
  sorry


lemma mmu_config_TranslationTableWalkSD:
  "mmu_config  (TranslationTableWalkSD (mva, iswrite, sz))"
  apply (clarsimp simp: TranslationTableWalkSD_def)
  apply (rule, simp)
  apply (clarsimp simp: split_def)
  apply (rule, simp)
  apply (clarsimp, rule+, simp, simp, rule+)
   apply (clarsimp simp: mmu_config_level1_desc_address_and_desc)
  apply (rule+)
   apply clarsimp
   apply safe
     apply (clarsimp simp: Let_def)
     apply (rule)+
      apply (clarsimp simp: mmu_config_level2_desc_address_and_desc)
     apply (rule)
     apply (simp only: split_def, rule+, simp, rule+)
      apply (clarsimp simp: mmu_config_writing_access_flag)
     apply (rule)+
      apply (clarsimp simp: mmu_config_TLBResult)
     apply (rule, simp add: mmu_config_TLBResult)
    apply (clarsimp simp: Let_def, rule+, simp add: mmu_config_level2_desc_address_and_desc)
    apply (rule)+
    apply (simp only: split_def)
    apply (rule)+ apply clarsimp
    apply (rule)+
     apply (clarsimp simp: mmu_config_writing_access_flag)
    apply (rule)+
     apply (clarsimp simp: mmu_config_TLBResult)
    apply (rule)+
    apply (clarsimp simp: mmu_config_TLBResult)
   apply (simp only: Let_def)
   apply (rule)
    apply clarsimp
   apply rule+
       apply clarsimp
      apply clarsimp
     apply clarsimp
    apply clarsimp
   apply rule+
    apply (clarsimp simp: mmu_config_TLBResult)
   apply (clarsimp simp: mmu_config_TLBResult)
  by (drule remaining_induct_n; clarsimp)



(*
definition l3_valid where 
  "l3_valid P f Q1 \<equiv> \<forall>s. P s \<longrightarrow> (\<forall>r s'. f s = (r, s') \<longrightarrow> Q1 r s')"
*)


definition l3_valid where 
  "l3_valid P f P' \<equiv> \<forall>s s' r. f s = (r, s') \<longrightarrow> P s \<longrightarrow> P' r s'"


named_theorems wp_pre


lemma l3_valid_weak_pre[wp_pre]:
  "\<lbrakk> l3_valid P f Q'; (\<And>s. P' s \<Longrightarrow> P s) \<rbrakk> \<Longrightarrow> l3_valid P' f Q'"
  by (simp add: l3_valid_def)

named_theorems wp

lemma l3_valid_return[wp]:
  "l3_valid (\<lambda>s.  P () s) (return ()) P"
  by (clarsimp simp: l3_valid_def)

lemma l3_valid_return'[wp]:
  "l3_valid (\<lambda>s. P f s) (Pair f) P"
  by (clarsimp simp: l3_valid_def)


lemma l3_valid_bind:
  "l3_valid (\<lambda>s. P (fst ( g (fst (f s)) (snd (f s)))) (snd ( g (fst (f s)) (snd (f s))))) (bind f g) P"
  apply (clarsimp simp: bind_def split_def Let_def)
  by (clarsimp simp: l3_valid_def)

(* is this week pre or strong post? *)
lemma l3_valid_bind_weak[wp]:
  "\<lbrakk> \<And>r. l3_valid (P1 r) (g r) P2; l3_valid P f P1 \<rbrakk> \<Longrightarrow> l3_valid P (bind f g) P2"
  by (simp add: l3_valid_def bind_def split: prod.splits)


lemma read_state_weak[wp]:
  "l3_valid (\<lambda>s. \<forall>r. P r s) (read_state f) P"
  by (clarsimp simp: l3_valid_def read_state_def)

lemma update_state_weak[wp]:
  "l3_valid (\<lambda>s. \<forall>r. P r (f s)) (update_state f) P"
  by (clarsimp simp: l3_valid_def update_state_def)

lemma extend_state_weak:
  "l3_valid (\<lambda>s. P (fst (f (v, s))) (snd (snd (f (v, s))))) (extend_state v f) P"
  by (clarsimp simp: l3_valid_def extend_state_def split_def Let_def)


lemma trim_state_weak:
  "l3_valid (\<lambda>s. \<forall>a b. P (fst (f b)) (a, snd (f b)) ) (trim_state f ) P"
  by (clarsimp simp: l3_valid_def trim_state_def split_def Let_def)


(*  main lemma *)

lemma
  "\<lbrakk>MMU_config_assert_isa s;
    TranslationTableWalkSD (va , iswrite, siz) s = (tlben, s'); exception s' = NoException; 
       ptable_lift (map_mem (MEM s)) (Addr (reg'TTBR0 (TTBR0 (CP15 s)))) (Addr va) = Some p \<rbrakk> \<Longrightarrow> 
       addr_val p = physicaladdress (paddress (addrdesc tlben))"
  oops



lemma
  "l3_valid (\<lambda>s. MMU_config_assert_isa s \<and>  ptable_lift (map_mem (MEM s)) (Addr (reg'TTBR0 (TTBR0 (CP15 s)))) (Addr va) =
        Some p   )
            (TranslationTableWalkSD (va , iswrite, siz)) 
              (\<lambda>r s'. exception s' = NoException \<longrightarrow> addr_val p = physicaladdress (paddress (addrdesc tlben)))"
  apply (clarsimp simp: TranslationTableWalkSD_def)
  apply (rule wp_pre)
  apply (rule wp)+
    apply (simp only: translation_root_def)
    apply (rule wp) 
  apply (rule l3_valid_weak_pre)
   apply (clarsimp simp: TranslationTableWalkSD_def)
   apply (rule l3_valid_bind_weak)
    apply (clarsimp simp: translation_root_def)
    apply rule
     apply (rule impI)
     apply (rule l3_valid_bind_weak)
      apply (rule read_state_weak)
     apply (clarsimp)
     apply (rule l3_valid_bind_weak)+
          apply (rule l3_valid_return')
         apply (clarsimp, rule l3_valid_return')
        apply (clarsimp, rule l3_valid_return')+
      apply clarsimp
      apply rule+
       apply (rule l3_valid_return')
      apply rule+
      apply (rule l3_valid_bind_weak)+
       apply (rule read_state_weak)
      apply (clarsimp)
      apply (rule l3_valid_bind_weak)+
           apply (rule l3_valid_return')
          apply (rule)
          apply (rule l3_valid_return')
         apply (rule)
         apply (rule l3_valid_return')
        apply (rule)
        apply (rule l3_valid_return')
       apply (rule)
       apply (rule l3_valid_return')
      apply rule+
      apply clarsimp
      apply rule+
       apply clarsimp
       apply (clarsimp simp:l3_valid_def )
       apply force
      apply rule+
      apply (rule l3_valid_bind_weak)+
       apply clarsimp
       apply (clarsimp simp:l3_valid_def)
       apply force
      apply rule+
      apply (clarsimp simp:l3_valid_def)
     apply clarsimp
     apply rule+
      apply (clarsimp simp:l3_valid_def)
      apply force
     apply rule+
     apply (clarsimp simp:l3_valid_def)
    apply (clarsimp)
    apply (clarsimp simp:l3_valid_def)
   apply clarsimp
   prefer 2
  apply clarsimp
  oops







lemma l3_valid_bind:
  "\<lbrakk> l3_valid P f P1; \<forall>r. l3_valid (P1 r) (g r) P2 \<rbrakk> \<Longrightarrow> l3_valid P (bind f g) P2"
  apply (simp add: l3_valid_def bind_def split: prod.splits)
  by blast


lemma l3_valid_use':
  " \<lbrakk>l3_valid P f P1; P s; f s = (r, s')\<rbrakk> \<Longrightarrow> P1 r s'"
   by (simp add: l3_valid_def split: prod.splits)

lemma l3_valid_use:
  "\<lbrakk> l3_valid P f P1; P s \<rbrakk> \<Longrightarrow> case f s of (r, s') \<Rightarrow> P1 r s'"
  by (simp add: l3_valid_def split: prod.splits)

lemma l3_validI:
  "\<lbrakk> f s = (r, s'); P s; l3_valid P f P1 \<rbrakk> \<Longrightarrow> P1 r s'"
  by (simp add: l3_valid_def split: prod.splits)

lemma l3_validI':
  "\<lbrakk>  P s; f s = (r, s'); Q' s'; l3_valid P f P1 \<rbrakk> \<Longrightarrow> P1 r s'"
  by (simp add: l3_valid_def split: prod.splits)


lemma
  "\<lbrakk>(\<lambda>s. MMU_config_assert_isa s \<and>  ptable_lift (map_mem (MEM s)) (Addr (reg'TTBR0 (TTBR0 (CP15 s)))) (Addr va) = Some p ) s;
    TranslationTableWalkSD (va , iswrite, siz) s = (tlben, s'); (\<lambda>s'. exception s' = NoException) s' \<rbrakk> \<Longrightarrow> 
       addr_val p = physicaladdress (paddress (addrdesc tlben))"
  apply (rule_tac 
         P = "(\<lambda>s. MMU_config_assert_isa s \<and>  ptable_lift (map_mem (MEM s)) (Addr (reg'TTBR0 (TTBR0 (CP15 s)))) (Addr va) = Some p )" and 
         f = "TranslationTableWalkSD (va , iswrite, siz)" and 
         s' = s' and 
         Q' = "(\<lambda>s'. exception s' = NoException)" in  l3_validI' ,
              simp, simp, simp)
  apply clarsimp
  apply (subgoal_tac "exception s = NoException")
  prefer 2
   apply (subgoal_tac "excp_pas (TranslationTableWalkSD (va , iswrite, siz))")
    apply (clarsimp simp: excp_pas_def)
   apply (clarsimp simp: TranslationTableWalkSD_exp_pas)
  apply (clarsimp simp: TranslationTableWalkSD_def)
  apply (rule l3_valid_bind)
  apply (clarsimp simp: bind_associativity)
  apply ()
  apply (clarsimp simp: )

  find_theorems "L3_Lib.bind"
  apply (clarsimp simp: bind_def)

  oops


lemma
  "\<lbrakk>MMU_config_assert_isa s;
    TranslationTableWalkSD (va , iswrite, siz) s = (tlben, s'); exception s' = NoException; 
       ptable_lift (map_mem (MEM s)) (Addr (reg'TTBR0 (TTBR0 (CP15 s)))) (Addr va) = Some p \<rbrakk> \<Longrightarrow> 
       addr_val p = physicaladdress (paddress (addrdesc tlben))"
  apply (subgoal_tac "exception s = NoException")
  prefer 2
   apply (subgoal_tac "excp_pas (TranslationTableWalkSD (va , iswrite, siz))")
    apply (clarsimp simp: excp_pas_def)
   apply (clarsimp simp: TranslationTableWalkSD_exp_pas)
  apply (clarsimp simp: TranslationTableWalkSD_def)
  apply (clarsimp simp: bind_associativity)
  apply ()
  apply (clarsimp simp: )

  find_theorems "L3_Lib.bind"
  apply (clarsimp simp: bind_def)

  oops






(*
definition 
  "mmu_config f \<equiv> 
        (\<forall> s s'. snd (f s) = s' \<longrightarrow>
                  fst (MMU_config_assert () s)  \<longrightarrow> fst (MMU_config_assert () s') )"



lemma mmu_config_bind [intro!, simp]:
  "\<lbrakk> mmu_config f; \<forall> x. mmu_config (g x) \<rbrakk> \<Longrightarrow> mmu_config (bind f g)"
  apply (clarsimp simp: mmu_config_def bind_def)
  by (clarsimp simp: split_def)

lemma
  " mmu_config(extend_state v f )"

  oops


lemma lets_see:
  "\<lbrakk> \<forall> x. mmu_config (\<lambda>s. (fst (f (v, s)), snd (snd (f (v, s))))) \<rbrakk> \<Longrightarrow>  mmu_config(extend_state v f )"
  by (clarsimp simp: extend_state_def split_def Let_def)


  

lemma mmu_config_if_else [intro!, simp]:
  "\<lbrakk> mmu_config f; mmu_config g \<rbrakk> \<Longrightarrow> 
     mmu_config (\<lambda>s. if b then f s else g s ) "
  by (clarsimp simp: mmu_config_def split: if_split_asm)



lemma mmu_config_read_st_simp [intro!, simp]:
  "mmu_config (read_state f)"
  by (clarsimp simp: mmu_config_def)

(*
lemma mmu_config_extend_st_simp [intro!, simp]:
  "\<lbrakk>mmu_config (\<lambda>s. (fst (f (v, s)), snd (snd (f (v, s)))) ) \<rbrakk> \<Longrightarrow>
      mmu_config (extend_state v f)"
  by (clarsimp simp: extend_state_def split_def Let_def)
*)



lemma 
  " mmu_config (extend_state HOL.undefined f)"
  apply (clarsimp simp: extend_state_def split_def Let_def)
  oops



lemma mmu_config_update_st_mem_simp [intro!, simp]:
  "mmu_config (update_state (MEM_update v))"
  by (clarsimp simp: mmu_config_def MMU_config_assert_def bind_def read_state_def)


lemma mmu_config_raise_excp [intro!, simp]:
  "mmu_config (raise'exception e)"
  apply (clarsimp simp: mmu_config_def raise'exception_def fst_def snd_def)
  by (clarsimp simp: bind_def read_state_def update_state_def MMU_config_assert_def split: if_split_asm)


lemma mmu_config_pair_simp [intro!, simp]:
  "mmu_config (Pair p)"
  by (clarsimp simp: mmu_config_def)

lemma mmu_config_pair_raise_excp' [intro!, simp]:
  "mmu_config (case x of None \<Rightarrow> raise'exception (UNPREDICTABLE ''undefined memory'') | Some v \<Rightarrow> Pair v)"
  by (clarsimp split: option.splits)


lemma mmu_config_pair_mem1 [intro!, simp]:
  "mmu_config (mem1 p)"
  apply (clarsimp simp: mem1_def)
  apply (rule mmu_config_bind; clarsimp)
  by (rule mmu_config_bind; clarsimp simp:  option.splits) 
  


lemma mmu_config_pair_mem [intro!, simp]:
  "mmu_config (mem (p, n))"
  by (clarsimp simp: mem_def)
 

lemma mmu_config_pair_write_mem [intro!, simp]:
  "mmu_config (write'mem (bl, p, n))"
  by (clarsimp simp: write'mem_def)




lemma mmu_config_translation_root [intro!, simp]:
  "mmu_config (translation_root va)"
  by (clarsimp simp: translation_root_def)
 

lemma mmu_config_same_state:
  "mmu_config 
    (TranslationTableWalkSD (mva, iswrite, sz))"
  apply (clarsimp simp: TranslationTableWalkSD_def 
          extend_state_def bind_def update_state_def trim_state_def)
  apply (clarsimp simp: mmu_config_def)
  apply (case_tac" translation_root mva s"; clarsimp)
  oops

*)

(*  apply (clarsimp simp: split_def)
  apply (rule excp_pas_if_else')
   apply (rule excp_pas_state)
    apply (clarsimp)
   apply (rule excp_pas_state_back)
   apply (rule excp_pas_state_fnc_state)
    apply clarsimp
  apply (clarsimp simp: not_sure)

*)





definition
  "excp_pas' g \<equiv> (\<forall> s s'. g s = s' \<longrightarrow> exception s' = NoException \<longrightarrow> exception s = NoException)"


lemma excp_pas_state:
  "\<lbrakk> excp_pas f ; excp_pas' g \<rbrakk> \<Longrightarrow>  excp_pas (\<lambda>s. f (g s))"
  by (clarsimp simp: excp_pas_def excp_pas'_def)


lemma excp_pas_state_back:
  "excp_pas f \<Longrightarrow>  excp_pas' (\<lambda>s. snd (f s))"
  apply (clarsimp simp: excp_pas_def excp_pas'_def)
  using surjective_pairing by blast


lemma  excp_pas_state_fnc_state:
  "\<lbrakk> \<forall>s. excp_pas (f s); excp_pas' g \<rbrakk> \<Longrightarrow>  excp_pas (\<lambda>s. (f s) (g s))"
  by (clarsimp simp: excp_pas_def excp_pas'_def)



(* what is it for a state to be exception free *)

(*
lemma excp_pas_comb_simp:
  "\<lbrakk> \<forall> x. excp_pas (f x) \<rbrakk> \<Longrightarrow> excp_pas (\<lambda>s. case f s of g \<Rightarrow> d g s)"
  apply (clarsimp simp: excp_pas_def)
  sorry
*)



lemma excp_pas_translation_root [intro!, simp]:
  "excp_pas (translation_root va)"
  by (clarsimp simp: translation_root_def)
term "trim_state"


lemma
  " excp_pas (extend_state v f)"
  apply (clarsimp simp: extend_state_def)
  apply (clarsimp simp: excp_pas_def)
  oops

  thm bind_def

lemma
  "\<lbrakk> \<forall>x. excp_pas (\<lambda>s. g x)   \<rbrakk> \<Longrightarrow> excp_pas (\<lambda>s. g (translation_root va s))"
  apply (clarsimp simp: excp_pas_def)
 

  oops

  thm allE


lemma
  "\<lbrakk>  excp_pas f ; \<forall>x. excp_pas (\<lambda>s. g (x s))   \<rbrakk> \<Longrightarrow> excp_pas (\<lambda>s. g (f s))"
  apply (clarsimp simp: excp_pas_def)
  
  oops


lemma lets_see':
  "\<lbrakk> \<forall> x. excp_pas (\<lambda>s. (fst (f (x, s)), snd (snd (f (x, s))))) \<rbrakk> \<Longrightarrow>  excp_pas (extend_state v f )"
  by (clarsimp simp: extend_state_def split_def Let_def)



lemma lets_see'':
  "\<lbrakk> something \<rbrakk> \<Longrightarrow> 
        excp_pas (\<lambda>s. (fst ((bind f g) (x, s)), snd (snd ((bind f g) (x, s)))))"
  apply (clarsimp simp: excp_pas_def)
  oops



lemma lets_see'':
  "\<lbrakk> \<forall>x. excp_pas (\<lambda>s. (fst (f (x, s)), snd (snd (f (x, s)))));
    \<forall>f x. excp_pas (\<lambda>s. (fst (g f (x, s)), snd (snd (g f (x, s)))))  \<rbrakk> \<Longrightarrow> 
        excp_pas (\<lambda>s. (fst ((bind f g) (x, s)), snd (snd ((bind f g) (x, s)))))"
  apply (clarsimp simp: bind_def split_def Let_def)
 

  sorry






end