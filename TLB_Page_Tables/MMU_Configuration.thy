theory MMU_Configuration
imports
         MMU_Translate_Refine
         MMU_ARM.ARM_Monadic
    
begin



definition 
  MMU_config_assert_isa :: "state \<Rightarrow> bool"
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
                              \<not>VSCTLR.AFE (VSCTLR(CP15 s)) \<and>  \<comment> \<open>hardware access flag is disabled\<close>
                              \<not>VSCTLR.TRE (VSCTLR(CP15 s))"


fun
  mem_typcast :: "MemType_t \<Rightarrow> memtyp_t"
where
  "mem_typcast MemType_Normal = MemNormal"
| "mem_typcast MemType_Device = MemDevice"
| "mem_typcast MemType_StronglyOrdered = MemStronglyOrdered"





definition
  mematr_typcast :: "MemoryAttributes \<Rightarrow> memattribs_t"
where
  "mematr_typcast mematr = \<lparr> 
     memtyp         = mem_typcast (MemType mematr),
     innerattrs      = innerhints mematr,
     outerattrs      = outerattrs mematr,
     innerhints      = innerhints mematr,
     outerhints      = outerhints mematr,
     innertransient  = innertransient mematr,
     outertransient  = outertransient mematr,
     shareable       = shareable mematr,
     outershareable  = outershareable mematr\<rparr>"


fun
  excp_typcast :: "ARM_Monadic.exception \<Rightarrow> excpt_t"
where
  "excp_typcast (ASSERT string)                  = MMUException string"
| "excp_typcast (IMPLEMENTATION_DEFINED string)  = MMUException string"
| "excp_typcast (MMU_Exception string)           = MMUException string"
| "excp_typcast  NoException                     = NoExcp "
| "excp_typcast (UNPREDICTABLE string)           = MMUException string"
| "excp_typcast (VFP_EXCEPTION string)           = MMUException string"



definition
  state_comp :: "state \<Rightarrow> tlbs_set cstate_scheme \<Rightarrow> bool"
where
  "state_comp s t \<equiv>  
      (\<lambda>p. (MEM s) (addr_val p))          = heap t \<and>
      (Addr (reg'TTBR0 (TTBR0 (CP15 s)))) = ttbr0 t \<and> 
      ASID (CONTEXTIDR (CP15 s) )         = asid t \<and>
      excp_typcast(exception  s)          = excpt t \<and>      
      (reg'PRRR (PRRR (CP15 s) ) )        = prrr t \<and>
      (reg'NMRR (NMRR (CP15 s) ) )        = nmrr t \<and>
      (reg'DACR (DACR (CP15 s) ) )        = dacr t"



(*fun
  tagtypcast :: "tag_t \<Rightarrow> 8 word option"
where
  "tagtypcast None = None"
| "tagtypcast (Some a) = Some a"

*)

definition
  perm_typcast :: "Permissions \<Rightarrow> permissions_t"
where                                  
  "perm_typcast perm = \<lparr> 
     accessperm   = ap perm,
     executenever   = xn perm,
     pexecutenever  = pxn perm \<rparr>"


fun
  flagtypcast :: "TLBEntry \<Rightarrow> flags_t"
where
  "flagtypcast (EntryLarge elr)   = \<lparr> memattribs = mematr_typcast (EntryLarge_t.memattrs elr) , 
                                      permissions = perm_typcast (EntryLarge_t.perms elr), 
                                      domain = EntryLarge_t.domain elr , 
                                      level= EntryLarge_t.level elr\<rparr>"
| "flagtypcast (EntrySection ese) = \<lparr> memattribs = mematr_typcast (EntrySection_t.memattrs ese) , 
                                      permissions = perm_typcast (EntrySection_t.perms ese), 
                                      domain = EntrySection_t.domain ese , 
                                      level= EntrySection_t.level ese\<rparr>"
| "flagtypcast (EntrySmall esm)   = \<lparr> memattribs = mematr_typcast (EntrySmall_t.memattrs esm) , 
                                      permissions = perm_typcast (EntrySmall_t.perms esm), 
                                      domain = EntrySmall_t.domain esm , 
                                      level= EntrySmall_t.level esm\<rparr>"
| "flagtypcast (EntrySuper esp)   = \<lparr> memattribs = mematr_typcast (EntrySuper_t.memattrs esp) , 
                                      permissions = perm_typcast (EntrySuper_t.perms esp), 
                                      domain = EntrySuper_t.domain esp , 
                                      level= EntrySuper_t.level esp\<rparr>"

fun
  tlbtypcast :: "TLBEntry \<Rightarrow> tlb_entry"
where
  "tlbtypcast (EntryLarge elr)   = Entrylarge   (EntryLarge_t.tag elr)   (vadLr elr)  (padLr elr)  (flagtypcast (EntryLarge elr))"
| "tlbtypcast (EntrySection ese) = Entrysection (EntrySection_t.tag ese) (vadSec ese) (padSec ese) (flagtypcast(EntrySection ese))"
| "tlbtypcast (EntrySmall esm)   = Entrysmall   (EntrySmall_t.tag esm)   (vadSm esm)  (padSm esm)  (flagtypcast(EntrySmall esm))"
| "tlbtypcast (EntrySuper esp)   = Entrysuper   (EntrySuper_t.tag esp)   (vadSup esp) (padSup esp) (flagtypcast(EntrySuper esp))"


definition
  tlb_rel :: "state \<Rightarrow> tlbs_set cstate_scheme \<Rightarrow> bool"
where
  "tlb_rel s t \<equiv>  state_comp s t \<and>
                  tlbtypcast ` ran (micro_DataTLB s)  \<subseteq> dtlb_set (cstate.more t) \<and> 
                  tlbtypcast ` ran (micro_InstrTLB s) \<subseteq> itlb_set (cstate.more t) \<and> 
                  tlbtypcast ` ran (main_TLB s)       \<subseteq> unitlb_set (cstate.more t) "


(* consistent   *)

definition
  "consistent0 m a rt prr nmr tlb va \<equiv>
     (lookup tlb a (addr_val va) = TLB.Hit (the (pt_walk a m rt prr nmr va)) \<and> pt_walk a m rt prr nmr va \<noteq> None)  \<or>
      lookup tlb a (addr_val va) = TLB.Miss"


abbreviation
  "dtlb_consistent (s::tlbs_set cstate_scheme) \<equiv>
               consistent0 (heap s) (asid s) (ttbr0 s) (prrr s) (nmrr s) (dtlb_set (cstate.more s))"


abbreviation
  "itlb_consistent (s::tlbs_set cstate_scheme) \<equiv>
               consistent0 (heap s) (asid s) (ttbr0 s) (prrr s) (nmrr s) (itlb_set (cstate.more s))"

abbreviation
  "unitlb_consistent (s::tlbs_set cstate_scheme) \<equiv>
               consistent0 (heap s) (asid s) (ttbr0 s) (prrr s) (nmrr s) (unitlb_set (cstate.more s))"


definition 
  typ_tlb :: "'a tlb_state_scheme \<Rightarrow> tlbs_set cstate_scheme"
where
  "typ_tlb s =  cstate.extend (cstate.truncate s) (tlbs_set s)"



definition 
  map_mem :: "(32 word \<Rightarrow> 8 word option) \<Rightarrow> (paddr \<Rightarrow> 8 word option)"
where 
  "map_mem m = (\<lambda>x. m (addr_val x))"



definition 
  mmu_config :: "('a \<Rightarrow> state) \<Rightarrow> ('a \<Rightarrow> 'c \<times> 'a) \<Rightarrow> bool"
where
  "mmu_config prj f \<equiv> 
        (\<forall> s s' a. f s = (a,s') \<longrightarrow>
                 MMU_config_assert_isa (prj s) \<longrightarrow> MMU_config_assert_isa (prj s') )"

context 
  notes return_def[simp]
begin

named_theorems mmu_intros

lemma mmu_config_bind [mmu_intros, intro!, simp]:
  "\<lbrakk>  \<And>x. mmu_config prj (g x); mmu_config prj f \<rbrakk> \<Longrightarrow> mmu_config prj (bind f g)"
  apply (clarsimp simp: mmu_config_def bind_def)
  apply (clarsimp simp: split_def)
  by (metis prod.collapse)


lemma mmu_config_pair_simp [mmu_intros,intro!, simp]:
  "mmu_config prj (Pair p)"
  by (clarsimp simp: mmu_config_def)

lemma mmu_config_read_st_simp [mmu_intros,intro!, simp]:
  "mmu_config prj (read_state f)"
  by (clarsimp simp: mmu_config_def read_state_def)

lemma mmu_config_main_update_state [mmu_intros, intro!, simp]:
  " mmu_config prj (\<lambda>a. ((), (f a))) \<Longrightarrow> mmu_config prj (update_state f)"
  by (clarsimp simp: mmu_config_def update_state_def)


lemma excp_pas_extend_st_simp [mmu_intros,intro!, simp]:
  "mmu_config (prj o snd) f \<Longrightarrow> mmu_config prj (extend_state v f)"
  unfolding extend_state_def mmu_config_def
  by (fastforce split: prod.splits)


lemma excp_pas_trim_st_simp [mmu_intros,intro!, simp]:
  "mmu_config prj f \<Longrightarrow> mmu_config (prj o snd) (trim_state f)"
   unfolding trim_state_def mmu_config_def
   by (fastforce split: prod.splits)


lemma excp_pas_trim_st_simp' [mmu_intros,intro!, simp]:
  "mmu_config id f \<Longrightarrow> mmu_config snd (trim_state f)"
   unfolding trim_state_def mmu_config_def
   by (fastforce split: prod.splits)


lemma mmu_config_if_else [mmu_intros, intro!, simp]:
  "\<lbrakk> b \<longrightarrow> mmu_config prj f; \<not>b \<longrightarrow> mmu_config prj g \<rbrakk> \<Longrightarrow> 
     mmu_config prj (\<lambda>s. if b then f s else g s ) "
  by (clarsimp simp: mmu_config_def split: if_split_asm)

lemma mmu_config_if_else' [mmu_intros, intro!, simp]:
  "\<lbrakk> b \<longrightarrow> mmu_config prj f; \<not>b \<longrightarrow> mmu_config prj g \<rbrakk> \<Longrightarrow> 
     mmu_config prj (if b then f else g ) "
  by (clarsimp simp: mmu_config_def split: if_split_asm)



lemma mmu_config_update_st_mem_simp [mmu_intros, intro!, simp]:
  "mmu_config id (update_state (MEM_update v))"
  apply (rule mmu_intros)
  by (clarsimp simp: mmu_config_def MMU_config_assert_isa_def)



lemma mmu_config_raise_excp [mmu_intros, intro!, simp]:
  "mmu_config id (raise'exception e)"
  apply (clarsimp simp: mmu_config_def raise'exception_def fst_def snd_def)
  by (clarsimp simp: bind_def read_state_def update_state_def MMU_config_assert_isa_def split: if_split_asm)


lemma mmu_config_pair_raise_excp' [mmu_intros, intro!, simp]:
  "mmu_config id (case x of None \<Rightarrow> raise'exception (UNPREDICTABLE ''undefined memory'') | Some v \<Rightarrow> Pair v)"
  by (clarsimp split: option.splits)

lemma mmu_config_pair_mem1 [mmu_intros, intro!, simp]:
  "mmu_config id (mem1 p)"
  apply (clarsimp simp: mem1_def)
  by (rule mmu_config_bind ; clarsimp simp:  option.splits) 

lemma mmu_config_lookup_cases' [mmu_intros,intro!, simp]: 
  "\<lbrakk> \<forall>e. lva = ARM_Monadic.lookup_type.Hit e \<longrightarrow>  mmu_config prj (AH e); mmu_config prj AI; mmu_config prj AM \<rbrakk> \<Longrightarrow> 
          mmu_config prj  (case lva of ARM_Monadic.lookup_type.Hit e \<Rightarrow> AH e 
                          | ARM_Monadic.lookup_type.Incon \<Rightarrow> AI
                          | ARM_Monadic.lookup_type.Miss \<Rightarrow> AM)"
  by (cases lva; clarsimp)
 

lemma  mmu_config_CheckPermission [mmu_intros, intro!, simp]:
  "mmu_config id
            (CheckPermission (pe, va, le, de, iswrite, ispriv, b', b''))"
  apply (simp only: CheckPermission_def split_def)
  apply ((rule mmu_intros)+ ; clarsimp?)
   apply word_bitwise
   apply force
  apply ((rule mmu_intros)+ ; clarsimp?)
  apply ((rule mmu_intros)+ ; clarsimp?)
  by (clarsimp simp: update_state_def mmu_config_def)

lemma mmu_config_CheckDomain [mmu_intros, intro!, simp]:
  "mmu_config id (CheckDomain (de, va, le, iswrite))"
  apply (simp only: CheckDomain_def split_def)
  apply ((rule mmu_intros)+ ; clarsimp?)
  apply word_bitwise
  by force

lemma  mmu_config_main_TLB_update [mmu_intros, intro!, simp]:
  "mmu_config id (\<lambda>s. ((), s\<lparr>main_TLB := x\<rparr>))"
  by (clarsimp simp: mmu_config_def MMU_config_assert_isa_def)

lemma mmu_config_main_write'unified_mainTLB [mmu_intros, intro!, simp]:
  "mmu_config id (write'unified_mainTLB (a, b))"
  by (clarsimp simp: write'unified_mainTLB_def)
 

lemma  mmu_config_date_TLB_update [mmu_intros, intro!, simp]:
  "mmu_config id (\<lambda>s. ((), s\<lparr>micro_DataTLB := x\<rparr>))"
  by (clarsimp simp: mmu_config_def MMU_config_assert_isa_def)

lemma  mmu_config_main_write'DataTLB [mmu_intros, intro!, simp]:
  "mmu_config id (write'DataTLB (a, b))"
  by (clarsimp simp: write'DataTLB_def)

lemma mmu_config_HaveSecurityExt [mmu_intros, intro!, simp]:
  "mmu_config prj (HaveSecurityExt ())"
  by (clarsimp simp: HaveSecurityExt_def)

lemma mmu_config_ArchVersion [mmu_intros, intro!, simp]:
  "mmu_config prj (ArchVersion ())"
  by (clarsimp simp: ArchVersion_def)


lemma mmu_config_HaveVirtExtt [mmu_intros, intro!, simp]:
  "mmu_config prj (HaveVirtExt ())"
  by (clarsimp simp: HaveVirtExt_def)
  

lemma mmu_config_BadMode [mmu_intros, intro!, simp]:
  "mmu_config prj (BadMode xa)"
  by (clarsimp simp: BadMode_def)
 

lemma mmu_config_CurrentModeIsHyp [mmu_intros, intro!, simp]:
  "mmu_config id (CurrentModeIsHyp ())"
  by (clarsimp simp: CurrentModeIsHyp_def)


lemma mmu_config_FCSETranslate [mmu_intros, intro!, simp]:
  "mmu_config id (FCSETranslate va)"
  by (clarsimp simp: FCSETranslate_def)

lemma mmu_config_update_state' [mmu_intros, intro!, simp]:
  "mmu_config snd (update_state (\<lambda>s. (xs, snd s)))"
  apply (rule mmu_intros)
  by (clarsimp simp: mmu_config_def)

lemma mmu_config_IsSecure [mmu_intros, intro!, simp]:
  "mmu_config prj (IsSecure ())"
  by (clarsimp simp: IsSecure_def)


lemma mmu_config_TranslateAddressVS1Off [mmu_intros, intro!, simp]:
  "mmu_config id (TranslateAddressVS1Off x)"
  by (clarsimp simp: TranslateAddressVS1Off_def)



lemma mmu_config_state_function_only:
  "\<lbrakk>\<forall>s r s'. f a s = (r , s')  \<longrightarrow> s = s'  \<rbrakk> \<Longrightarrow> mmu_config id (f a)  "
  apply (clarsimp simp: mmu_config_def  MMU_config_assert_isa_def)
   by fastforce


lemma  mmu_config_exception_update_function_only:
  "\<lbrakk>\<forall>s r s'. f a s = (r , s')  \<longrightarrow> s' = s\<lparr> exception := exception s' \<rparr>  \<rbrakk> \<Longrightarrow> mmu_config id (f a)  "
  apply (clarsimp simp: mmu_config_def  MMU_config_assert_isa_def)
  apply (case_tac s, case_tac s')
  by fastforce


lemma mmu_config_DefaultTEXDecode [mmu_intros, intro!, simp]:
  "mmu_config id (DefaultTEXDecode (a, b))"
  apply (rule mmu_config_exception_update_function_only, clarsimp)
  apply (clarsimp simp: DefaultTEXDecode_def extend_state_def bind_def split: if_split_asm)
  by (clarsimp simp: bind_def read_state_def update_state_def extend_state_def trim_state_def
      raise'exception_def split: if_split_asm)+


lemma mmu_config_trivial [mmu_intros, intro!, simp]:
  "mmu_config snd (\<lambda>a. ((), x, snd a))"
 by (clarsimp simp: mmu_config_def)

lemma word_mask_two_bits_false:
  "\<lbrakk>n < 31; ucast ((w:: 32 word) && 3) \<noteq> (0 :: 2 word); ucast (w && 3) \<noteq> (1 :: 2 word); 
      ucast (w && 3) \<noteq> (2 :: 2 word); ucast (w && 3) \<noteq> (3 :: 2 word)\<rbrakk> \<Longrightarrow> False"
   apply word_bitwise
  by force

lemma remaining_induct_n:
  "\<lbrakk>word_extract (Suc n) n (w:: 32 word) \<noteq> (0 :: 2 word);
    word_extract (Suc n) n w \<noteq> (1 :: 2 word);
    word_extract (Suc n) n w \<noteq> (2 :: 2 word);
    word_extract (Suc n) n w \<noteq> (3 :: 2 word); (n:: nat) < 32 ;  n < 31 \<rbrakk> \<Longrightarrow> False"
  apply (clarsimp simp: word_extract_def word_bits_def mask_def )
  by (frule_tac w = "(w >> n)" in  word_mask_two_bits_false; clarsimp)


lemma three_bits_less_than_16:
  "nat (uint ((word_extract 2 0  (w:: 5 word)) :: 3 word)) < 16"
  sorry

lemma three_bits_less_than_31:
  "2 * nat (uint ((word_extract 2 0  (w:: 5 word)) :: 3 word)) < 31"
  sorry


lemma mmu_config_RemappedTEXDecode [mmu_intros, intro!, simp]:
  "mmu_config id (RemappedTEXDecode (a, b))"
 (* apply (rule mmu_config_state_function_only, clarsimp)
  apply (clarsimp simp: RemappedTEXDecode_def extend_state_def bind_def read_state_def split: if_split_asm)
        apply (clarsimp simp: update_state_def)+
     apply (clarsimp simp: bind_def  read_state_def split: if_split_asm)
    apply (clarsimp simp: update_state_def bind_def  read_state_def split: if_split_asm)
   apply (clarsimp simp: update_state_def)
  by (frule remaining_induct_n; (clarsimp simp: three_bits_less_than_16 three_bits_less_than_31)?)
  *)
  sorry

lemma mmu_config_TLBResult [mmu_intros, intro!, simp]:
  "mmu_config id (TLBResult( a, b, c, d, e, f, g, h, i, j, k, l))"
  by (clarsimp simp: TLBResult_def)


lemma mmu_config_case_split [mmu_intros]:
  "\<lbrakk> \<And>a.  x = a \<longrightarrow>  mmu_config id (f a)\<rbrakk> \<Longrightarrow> 
   mmu_config id (case x of a \<Rightarrow> f a)"
  by  (clarsimp simp:)

lemma mmu_config_case_split' [mmu_intros]:
  "\<lbrakk> \<And>a b. (x , y) = (a , b) \<longrightarrow>  mmu_config id (f a b)\<rbrakk> \<Longrightarrow> 
   mmu_config id (case (x , y) of (a , b) \<Rightarrow> f a b)"
  by  (clarsimp simp:)


lemma mmu_config_pair_mem [mmu_intros, intro!, simp]:
  "mmu_config id (mem (p, n))"
  by (clarsimp simp: mem_def)
 
lemma mmu_config_pair_write_mem [mmu_intros, intro!, simp]:
  "mmu_config id (write'mem (bl, p, n))"
  by (clarsimp simp: write'mem_def)

lemma mmu_config_writing_access_flag [mmu_intros, intro!, simp]:
  "mmu_config id (writing_access_flag (a, b))"
(*  by (clarsimp simp: writing_access_flag_def) *)
   sorry

lemma mmu_config_BigEndianReverse [mmu_intros, intro!, simp]:
  "mmu_config id (BigEndianReverse (a, b))"
  by (clarsimp simp: BigEndianReverse_def)


lemma mmu_config_CheckPermissionS2 [mmu_intros, intro!, simp]:
  "mmu_config id (CheckPermissionS2 (a, aa, ab, ac, ad, b))"
  apply (clarsimp simp: CheckPermissionS2_def)
  apply (((rule mmu_intros)+ ; safe) ; clarsimp?)
  by (clarsimp simp: mmu_config_def)
  

lemma mmu_config_SecondStageTranslate [mmu_intros, intro!, simp]:
  "mmu_config id (SecondStageTranslate (ab, ba))"
  apply (simp only: SecondStageTranslate_def)
  apply (rule mmu_config_case_split', rule)
  by (((rule mmu_intros)+ ; safe); clarsimp simp: Let_def mmu_config_def)


lemma mmu_config_level2_desc[mmu_intros, intro!, simp]:
  "mmu_config id (level2_desc_address_and_desc (b, mva, a))"
  apply (simp only: level2_desc_address_and_desc_def)
  apply (rule mmu_intros)
  by (safe; (clarsimp simp: mmu_config_def)?)

lemma mmu_config_HaveMPExt[mmu_intros, intro!, simp]:
  "mmu_config id (HaveMPExt ())"
  by (clarsimp simp: HaveMPExt_def)

lemma mmu_config_level1_desc[mmu_intros, intro!, simp]:
  "mmu_config id (level1_desc_address_and_desc (a, b, mva))"
  apply (simp only: level1_desc_address_and_desc_def)
  apply (rule mmu_intros)
  by (safe; (clarsimp simp: mmu_config_def)?)

lemma mmu_config_translation_root [mmu_intros, intro!, simp]:
  "mmu_config prj (translation_root va)"
  by (clarsimp simp: translation_root_def)

lemma mmu_config_TranslationTableWalkSD [mmu_intros, intro!, simp]:
  "mmu_config id (TranslationTableWalkSD (va, iswrite, siz))"
 (* apply (clarsimp simp: TranslationTableWalkSD_def)
  apply ((rule mmu_intros)+ ; clarsimp?)
  apply (((rule mmu_intros)+, safe); (clarsimp simp: Let_def)?)
   apply (safe; clarsimp?) 
  by (frule remaining_induct_n; clarsimp)
*)
  sorry


lemma mmu_config_TranslateAddressV [mmu_intros, intro!, simp]:
  "mmu_config id (TranslateAddressV (va, ispriv, iswrite, siz))"
  apply (clarsimp simp: TranslateAddressV_def)
  by ((rule mmu_intros)+ ; clarsimp?)+
 
lemma
  "\<forall>i s. mmu_config prj (a (i s))  \<Longrightarrow> 
       mmu_config prj (for_loop (i, j, a ))"
  apply (clarsimp simp: mmu_config_def)
  apply (cases "i = j")
  apply (clarsimp simp: for_loop.simps )
   apply (clarsimp simp: for_loop.simps)
  apply (clarsimp simp: bind_def split_def)
   apply (clarsimp split: if_split_asm)
   apply (clarsimp simp: MMU_config_assert_isa_def)
  (* from here *)
oops




lemma mmu_config_prj_state_function_only:
  "\<lbrakk>\<forall>s r s'. f a s = (r , s')  \<longrightarrow> s = s'  \<rbrakk> \<Longrightarrow> mmu_config prj (f a)  "
  apply (clarsimp simp: mmu_config_def  MMU_config_assert_isa_def)
   by fastforce
 

lemma mmu_config_micro_InstrTLB_update [mmu_intros, intro!, simp]:
  "mmu_config id (\<lambda>a. ((), a\<lparr>micro_InstrTLB := x\<rparr>))"
  by (clarsimp simp: mmu_config_def MMU_config_assert_isa_def)

lemma mmu_config_write'InstrTLB [mmu_intros, intro!, simp]:
  "mmu_config id (write'InstrTLB (a, b))"
  by (clarsimp simp: write'InstrTLB_def)
 

lemma  mmu_config_InstrTLB [mmu_intros, intro!, simp]:
  "mmu_config id (InstrTLB n)"
  by (clarsimp simp: InstrTLB_def)


lemma mmu_config_microInstrTLB_evict [mmu_intros, intro!, simp]:
  "mmu_config id (microInstrTLB_evict ())"
  apply (clarsimp simp: microInstrTLB_evict_def)
  apply ((rule mmu_intros)+ ; clarsimp simp: microInstrTLBEntries_def)
  apply (clarsimp simp: for_loop.simps)
  by ((rule mmu_intros)+ ; clarsimp?)+


lemma  mmu_config_DataTLB [mmu_intros, intro!, simp]:
  "mmu_config id (DataTLB n)"
  by (clarsimp simp: DataTLB_def)


lemma  mmu_config_unified_mainTLB [mmu_intros, intro!, simp]:
  "mmu_config id (unified_mainTLB n)"
  by (clarsimp simp: unified_mainTLB_def)


lemma mmu_config_microDataTLB_evict [mmu_intros, intro!, simp]:
  "mmu_config id (microDataTLB_evict ())"
  apply (clarsimp simp: microDataTLB_evict_def)
  apply ((rule mmu_intros)+ ; clarsimp simp: microDataTLBEntries_def)
  apply (clarsimp simp: for_loop.simps)
  by ((rule mmu_intros)+ ; clarsimp?)+


lemma mmu_config_mainTLB_evict [mmu_intros, intro!, simp]:
  "mmu_config id (mainTLB_evict ())"
  apply (clarsimp simp: mainTLB_evict_def)
  apply ((rule mmu_intros)+ ; clarsimp simp: mainTLBEntries_def)
  apply (clarsimp simp: for_loop.simps)
  by ((rule mmu_intros)+ ; clarsimp?)+
 

lemma mmu_config_option' [mmu_intros, intro!, simp]:
  "\<lbrakk> mmu_config prj f  ; \<forall>y. x = Some y \<longrightarrow> mmu_config prj (g y)\<rbrakk> \<Longrightarrow>
        mmu_config prj (case x of None \<Rightarrow> f 
                       | Some y \<Rightarrow> g y)"
  by (clarsimp split: option.splits)

lemma mmu_config_entry_list_data_micro [mmu_intros, intro!, simp]:
  "mmu_config id (entry_list_data_micro (a, b))"
  apply (clarsimp simp: entry_list_data_micro_def)
  apply (rule mmu_intros)+
  apply (clarsimp simp: microDataTLBEntries_def)
  by (clarsimp simp: for_loop.simps)

lemma mmu_config_lookupTLB_Data_micro [mmu_intros, intro!, simp]:
  "mmu_config id (lookupTLB_Data_micro (a, b))"
  by (clarsimp simp: lookupTLB_Data_micro_def)


lemma mmu_config_entry_list_instr_micro [mmu_intros, intro!, simp]:
  "mmu_config id (entry_list_instr_micro (a, b))"
  apply (clarsimp simp: entry_list_instr_micro_def)
  apply (rule mmu_intros)+
  apply (clarsimp simp: microInstrTLBEntries_def)
  apply (clarsimp simp: for_loop.simps)
  by ((rule mmu_intros)+; clarsimp)

lemma mmu_config_lookupTLB_Instr_micro [mmu_intros, intro!, simp]:
  "mmu_config id (lookupTLB_Instr_micro (a, b))"
  by (clarsimp simp: lookupTLB_Instr_micro_def)


declare mmu_config_option' [simp del]

lemma mmu_config_entry_list_main [mmu_intros, intro!, simp]:
  "mmu_config id (entry_list_main (a, b))"
  apply (clarsimp simp: entry_list_main_def)
  apply (rule mmu_intros)+
  apply (clarsimp simp: mainTLBEntries_def)
  apply (clarsimp simp: for_loop.simps)
  apply ((rule mmu_intros)+; clarsimp?)
  by (clarsimp simp: mmu_config_option')+ 


lemma mmu_config_lookupTLB_main [mmu_intros, intro!, simp]:
  "mmu_config id (lookupTLB_main (a, b))"
  by (clarsimp simp: lookupTLB_main_def)

lemma mmu_config_TranslateAddress [mmu_intros, intro!, simp]:
  "mmu_config  id (TranslateAddress (va, ispriv, iswrite, siz, True))"
  apply (clarsimp simp:  TranslateAddress_def)
  by ((rule mmu_intros)+ ; clarsimp?)+
 
end

end