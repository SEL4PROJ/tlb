theory Ins_Cycle1

imports ARM_REF.MMU_ARMv7_Ref

begin               


declare word_extract_def [simp add]
declare word_bits_def [simp add]
declare nat_to_bitstring_def [simp add]


definition  CP14' :: "CP14"
where
  "CP14' \<equiv> \<lparr> TEEHBR = (0::32 word)  \<rparr>"


definition
  HCR' :: "HCR"
where 
  "HCR' \<equiv> \<lparr>
   AMO =  True,
   BSU =  (1::2 word),
   DC =   True,
   FB =   True,
   FMO =  True,
   IMO =  True,
   PTW =  True,
   SWIO = True ,
   TAC =  True ,
   TGE =  True ,
   TID =  (1::4 word),
   TIDCP =True,
   TPC =  True,
   TPU =  True,
   TSC =  True,
   TSW =  True,
   TTLB = True,
   TVM =  True,
   TWE =  True,
   TWI =  True,
   VA =   True,
   VF =   True,
   VI =   True,
   VM =   True,
   hcr'rst  =  (1::4 word) \<rparr>"

definition 
  HSCTLR' :: "HSCTLR"
where
  "HSCTLR' \<equiv> \<lparr>
    A = True,
    C = True,
    CP15BEN = True,
    EE = True,
    FI = True,
    I = True,
    M = True,
    TE = True,
    WXN = True,
    hsctlr'rst = 1::23 word \<rparr> "



definition
  HSR' ::"HSR" 
where
  "HSR' \<equiv> \<lparr>
    EC = 1::6 word,
    IL = True, 
    ISS = 1::25 word \<rparr> "

definition
  NSACR' ::"NSACR"
where
  "NSACR' \<equiv> \<lparr>
   NSASEDIS = True,
   NSD32DIS = True,
   NSTRCDIS = True,
   RFR = True,
   cp = 1::14 word,
   nsacr'rst = 1::14 word \<rparr>"

definition 
  SCR' :: "SCR"
where
  "SCR' \<equiv> \<lparr>
  AW = True,
  EA = True,
  FIQ = True,
  FW = True,
  HCE = True,
  IRQ = True,
  NS = True,
  SCD = True,
  SIF = True,
  nET = True,
  scr'rst = 1::22 word  \<rparr>"

definition
  SCTLR' :: "SCTLR"
where
  "SCTLR' \<equiv> \<lparr>
  ARM_Monadic.SCTLR.A = True,  (* from setting *)
  B = True,
  BR = True,
  C = True,
  DZ = True,
  EE = True,
  FI = True,
  I = True,
  IE = True,
  M = True,
  NMFI = True,
  RR = True,
  SW = True,
  TE = True,
  U = False,  (* from setting *)
  V = False,  (* from setting *)
  VE = True,
  Z = True,
  sctlr'rst = 1::14 word
\<rparr> "

definition 
  CP15' :: "CP15"
where
  "CP15' \<equiv> \<lparr>
  HCR = HCR',
  HSCTLR =HSCTLR',
  HSR = HSR',
  MVBAR = 1::32 word,
  NSACR = NSACR',
  SCR = SCR',
  SCTLR = SCTLR',
  VBAR = 1::32 word
  \<rparr>"

definition
  CPSR' :: PSR 
where
  "CPSR' \<equiv> \<lparr>
  ARM_Monadic.PSR.A = True,
  C = True,
  E = False,         
  F = True,
  GE = 1::4 word,
  I = True,
  IT = 0::8 word,    
  J = False,          
  M = 0x10::5 word,
  N = True,
  Q = True,
  T = False,        
  V = True,
  Z = True,
  psr'rst = 1::4 word\<rparr>"

definition
  FPSCR' :: FPSCR
where
  "FPSCR' \<equiv> \<lparr>
  AHP = True,
  C = True,
  DN = True,
  DZC = True,
  DZE = True,
  FZ = True,
  IDC = True,
  IDE = True,
  IOC = True,
  IOE = True,
  IXC = True,
  IXE = True,
  N = True,
  OFC = True,
  OFE = True,
  QC = True,
  RMode = 1::2 word,
  UFC = True,
  UFE = True,
  V = True,
  Z = True,
  fpscr'rst = 1::10 word\<rparr>"

definition
  FP' :: FP
where
  "FP' \<equiv> \<lparr>
    FPSCR = FPSCR' ,
    REG = (\<lambda>x. 1::64 word)\<rparr>"

definition
  SPSR_abt' :: PSR 
where
  "SPSR_abt' \<equiv> \<lparr>
  ARM_Monadic.PSR.A = True,
  C = True,
  E = True,
  F = True,
  GE = 1::4 word,
  I = True,
  IT = 1::8 word,
  J = True,
  M = 1::5 word,
  N = True,
  Q = True,
  T = True,
  V = True,
  Z = True,
  psr'rst = 1::4 word\<rparr>"

definition
  SPSR_fiq' :: PSR 
where
  "SPSR_fiq' \<equiv> \<lparr>
  ARM_Monadic.PSR.A = True,
  C = True,
  E = True,
  F = True,
  GE = 1::4 word,
  I = True,
  IT = 1::8 word,
  J = True,
  M = 1::5 word,
  N = True,
  Q = True,
  T = True,
  V = True,
  Z = True,
  psr'rst = 1::4 word\<rparr>"

definition
  SPSR_hyp' :: PSR 
where
  "SPSR_hyp' \<equiv> \<lparr>
  ARM_Monadic.PSR.A = True,
  C = True,
  E = True,
  F = True,
  GE = 1::4 word,
  I = True,
  IT = 1::8 word,
  J = True,
  M = 1::5 word,
  N = True,
  Q = True,
  T = True,
  V = True,
  Z = True,
  psr'rst = 1::4 word\<rparr>"

definition
  SPSR_irq' :: PSR 
where
  "SPSR_irq' \<equiv> \<lparr>
  ARM_Monadic.PSR.A = True,
  C = True,
  E = True,
  F = True,
  GE = 1::4 word,
  I = True,
  IT = 1::8 word,
  J = True,
  M = 1::5 word,
  N = True,
  Q = True,
  T = True,
  V = True,
  Z = True,
  psr'rst = 1::4 word\<rparr>"

definition
  SPSR_mon' :: PSR 
where
  "SPSR_mon' \<equiv> \<lparr>
  ARM_Monadic.PSR.A = True,
  C = True,
  E = True,
  F = True,
  GE = 1::4 word,
  I = True,
  IT = 1::8 word,
  J = True,
  M = 1::5 word,
  N = True,
  Q = True,
  T = True,
  V = True,
  Z = True,
  psr'rst = 1::4 word\<rparr>"

definition
  SPSR_svc' :: PSR 
where
  "SPSR_svc' \<equiv> \<lparr>
  ARM_Monadic.PSR.A = True,
  C = True,
  E = True,
  F = True,
  GE = 1::4 word,
  I = True,
  IT = 1::8 word,
  J = True,
  M = 1::5 word,
  N = True,
  Q = True,
  T = True,
  V = True,
  Z = True,
  psr'rst = 1::4 word\<rparr>"

definition
  SPSR_und' :: PSR 
where
  "SPSR_und' \<equiv> \<lparr>
  ARM_Monadic.PSR.A = True,
  C = True,
  E = True,
  F = True,
  GE = 1::4 word,
  I = True,
  IT = 1::8 word,
  J = True,
  M = 1::5 word,
  N = True,
  Q = True,
  T = True,
  V = True,
  Z = True,
  psr'rst = 1::4 word\<rparr>"

definition
  Reg_Bank :: "ARM_Monadic.RName \<Rightarrow> 32 word"
where
  "Reg_Bank Reg \<equiv> 
      case Reg of RName_0usr  \<Rightarrow> 1
           |      RName_1usr  \<Rightarrow> 1
           |      RName_2usr  \<Rightarrow> 0
           |      RName_3usr  \<Rightarrow> 1
           |      RName_4usr  \<Rightarrow> 1
           |      RName_5usr  \<Rightarrow> 1
           |      RName_6usr  \<Rightarrow> 1
           |      RName_7usr  \<Rightarrow> 1
           |      RName_8usr  \<Rightarrow> 1
           |      RName_8fiq  \<Rightarrow> 1
           |      RName_9usr  \<Rightarrow> 1
           |      RName_9fiq  \<Rightarrow> 1
           |      RName_10usr  \<Rightarrow>1
           |      RName_10fiq  \<Rightarrow>1
           |      RName_11usr  \<Rightarrow>1
           |      RName_11fiq  \<Rightarrow>1
           |      RName_12usr  \<Rightarrow>1
           |      RName_12fiq  \<Rightarrow>1
           |      RName_SPusr  \<Rightarrow>1
           |      RName_SPfiq  \<Rightarrow>1
           |      RName_SPirq  \<Rightarrow>1
           |      RName_SPsvc  \<Rightarrow>1
           |      RName_SPabt  \<Rightarrow>1
           |      RName_SPund  \<Rightarrow>1
           |      RName_SPmon  \<Rightarrow>1
           |      RName_SPhyp  \<Rightarrow>1
           |      RName_LRusr  \<Rightarrow>1
           |      RName_LRfiq  \<Rightarrow>1
           |      RName_LRirq  \<Rightarrow>1
           |      RName_LRsvc  \<Rightarrow>1
           |      RName_LRabt  \<Rightarrow>1
           |      RName_LRund  \<Rightarrow>1 
           |      RName_LRmon  \<Rightarrow> 1
           |      RName_PC     \<Rightarrow> 0x000000FC (* set to the virtual address *)"


definition 
  MEM' :: "paddr \<Rightarrow> (8 word option)"
where
  "MEM' x \<equiv> 
        if (addr_val x) = 0 then Some 2 
   else if (addr_val x) = 1 then Some 0 
   else if (addr_val x) = 2 then Some 0 
   else if (addr_val x) = 3 then Some 0 


 else if (addr_val x) = 4 then Some 1 
 else if (addr_val x) = 5 then Some 1 
 else if (addr_val x) = 6 then Some 1 
 else if (addr_val x) = 7 then Some 1 



   else if (addr_val x) = 0xFC then Some 0x04 
   else if (addr_val x) = 0xFD then Some (0x10:: 8 word) 
   else if (addr_val x) = 0xFE then Some 0x82 
   else if (addr_val x) = 0xFF then Some 0xE5 
   else None"




definition 
  state' :: "state"
where
  "state' \<equiv> 
    \<lparr> 
  Architecture =         ARMv7_A ,
  CP14 =                 CP14' ,
  CP15  =                CP15' ,
  CPSR  =                CPSR',
  CurrentCondition  =    1:: 4 word  ,
  ELR_hyp  =             1:: 32 word ,
  Encoding  =            Encoding_ARM,
  Extensions  =          {Extension_Virtualization}  ,
  FP  =                  FP' ,
  MEM  =                 MEM',
  REG  =                 Reg_Bank,
  SPSR_abt  =            SPSR_abt',
  SPSR_fiq  =            SPSR_fiq' ,
  SPSR_hyp  =            SPSR_hyp' ,
  SPSR_irq  =            SPSR_irq' ,
  SPSR_mon  =            SPSR_mon' ,
  SPSR_svc  =            SPSR_svc',
  SPSR_und  =            SPSR_und',
  VFPExtension      =     NoVFP,
  exception  =           NoException,
  undefined  =           False,
  (* additional MMU 'b state_scheme *)
  TTBR0  =               (Addr 0)::paddr,
  ASID  =                1::8 word
  \<rparr>"

definition 
  tlb_state' :: "tlb_state"
where
  "tlb_state' \<equiv> 
    \<lparr> 
  Architecture =         ARMv7_A ,
  CP14 =                 CP14' ,
  CP15  =                CP15' ,
  CPSR  =                CPSR',
  CurrentCondition  =    1:: 4 word  ,
  ELR_hyp  =             1:: 32 word ,
  Encoding  =            Encoding_ARM,
  Extensions  =          {Extension_Virtualization}  ,
  FP  =                  FP' ,
  MEM  =                 MEM',
  REG  =                 Reg_Bank,
  SPSR_abt  =            SPSR_abt',
  SPSR_fiq  =            SPSR_fiq' ,
  SPSR_hyp  =            SPSR_hyp' ,
  SPSR_irq  =            SPSR_irq' ,
  SPSR_mon  =            SPSR_mon' ,
  SPSR_svc  =            SPSR_svc',
  SPSR_und  =            SPSR_und',
  VFPExtension      =     NoVFP,
  exception  =           NoException,
  undefined  =           False,
  (* additional MMU 'b state_scheme *)
  TTBR0  =               (Addr 0)::paddr,
  ASID  =                1::8 word,
  tlb_set = {} 
  \<rparr>"

lemma get_pde_section_MEM':
  "get_pde MEM' (Addr 0) (Addr 0xFC) = Some (SectionPDE (Addr 0) 
      \<lparr>arm_p_APX = 0, arm_p_AP = 0, arm_p_TEX = 0, arm_p_S = 0, arm_p_XN = 0, arm_p_C = 0, arm_p_B = 0, arm_p_nG = 0\<rparr>)"
  apply (clarsimp simp: get_pde_def decode_heap_pde_def vaddr_pd_index_def)
  apply (rule_tac x = 2 in exI)
  by (simp add: load_machine_word_def load_value_def load_list_def load_list_basic_def MEM'_def
                  deoption_list_def from_bytes_word_def machine_b2w_def word_rcat_bl  decode_pde_def decode_pde_section_def addr_base_def mask_def perm_bits_pde_sections_def split: option.splits)
  
lemma pt_walk_section_MEM':
  "pt_walk 1 MEM' (Addr 0) (Addr 0xFC) = 
             EntrySection 1 (ucast ((0xFC::32 word) >> 20) :: 12 word) (Some (0::12 word)) (0::8 word)"
  apply (simp only: pt_walk_def)
  apply (subgoal_tac "get_pde MEM' (Addr 0) (Addr 0xFC) = Some (SectionPDE (Addr 0) \<lparr>arm_p_APX = 0, arm_p_AP = 0, arm_p_TEX = 0, arm_p_S = 0, arm_p_XN = 0, arm_p_C = 0, arm_p_B = 0, arm_p_nG = 0\<rparr>)")
   prefer 2
   apply (clarsimp simp: get_pde_section_MEM')
  apply clarsimp
done
  
   
lemma not_is_fault_MEM':
  "\<not>is_fault (pt_walk 1 MEM' (Addr 0) (Addr 0xFC))"
  apply (clarsimp simp: is_fault_def)
  apply (subgoal_tac "pt_walk 1 MEM' (Addr 0) (Addr 0xFC) =   EntrySection 1 (ucast ((0xFC::32 word) >> 20) :: 12 word) (Some (0::12 word)) (0::8 word)")
   apply clarsimp
  apply (clarsimp simp: pt_walk_section_MEM')
done



lemma mmu_translate_MEM':
  "mmu_translate (Addr 0xFC) tlb_state' =  ((Addr 0xFC), 
      tlb_state' \<lparr> tlb_set := {pt_walk 1 MEM' (Addr 0) (Addr 0xFC)}    \<rparr> )"
  apply (clarsimp simp:  mmu_translate_tlb_state_ext_def)
  apply (clarsimp simp: tlb_state'_def lookup_def entry_set_def Let_def)
  apply (clarsimp simp: not_is_fault_MEM')
  apply (clarsimp simp: va_to_pa_def pt_walk_section_MEM' mask_def)
done




(*  ----- IMPORTANT ---- *)


lemma fetch_ins1:
 "Fetch  tlb_state' = (ARM 0xE5821004, 
 \<lparr>Architecture = ARMv7_A, CP14 = CP14',
       CP15 = \<lparr>HCR = HCR', HSCTLR = HSCTLR', HSR = HSR', MVBAR = 1, NSACR = NSACR', SCR = SCR',
                 SCTLR = \<lparr>SCTLR.A = True, B = True, BR = True, C = True, DZ = True, EE = True, FI = True, I = True, IE = True,
                            M = True, NMFI = True, RR = True, SW = True, TE = True, U = False, V = False, VE = True, Z = True,
                            sctlr'rst = 1\<rparr>, VBAR = 1\<rparr>,  CPSR = \<lparr>PSR.A = True, C = True, E = False, F = True, GE = 1, I = True, IT = 0, J = False, M = 0x10, N = True, Q = True,
                 T = False, V = True, Z = True, psr'rst = 1\<rparr>,  CurrentCondition = 1, ELR_hyp = 1, Encoding = Encoding_ARM, Extensions = {Extension_Virtualization}, FP = FP', MEM = MEM',
              REG = Reg_Bank, SPSR_abt = SPSR_abt', SPSR_fiq = SPSR_fiq', SPSR_hyp = SPSR_hyp', SPSR_irq = SPSR_irq', SPSR_mon = SPSR_mon', SPSR_svc = SPSR_svc', SPSR_und = SPSR_und',  VFPExtension   =  NoVFP, exception = NoException, undefined = False, TTBR0 = Addr 0, ASID = 1, tlb_set = {pt_walk 1 MEM' (Addr 0) (Addr 0xFC)}\<rparr>)"
  apply (clarsimp simp: Fetch_def CurrentInstrSet_def ISETSTATE_def word_cat_def tlb_state'_def CPSR'_def split:if_split_asm)
  apply ( clarsimp simp:  Reg_Bank_def  MemA_def CurrentModeIsNotUser_def BadMode_def MemA_with_priv_def CP15'_def SCTLR'_def Aligned1_def Align1_def  mmu_read_size_tlb_state_ext_def)
  apply (subgoal_tac "mmu_translate (Addr 0xFC) \<lparr>Architecture = ARMv7_A, CP14 = CP14',  CP15 = \<lparr>HCR = HCR', HSCTLR = HSCTLR', HSR = HSR', MVBAR = 1, NSACR = NSACR', SCR = SCR',
   SCTLR = \<lparr>SCTLR.A = True, B = True, BR = True, C = True, DZ = True, EE = True, FI = True, I = True, IE = True,
   M = True, NMFI = True, RR = True, SW = True, TE = True, U = False, V = False, VE = True, Z = True,
   sctlr'rst = 1\<rparr>,  VBAR = 1\<rparr>,
   CPSR = \<lparr>PSR.A = True, C = True, E = False, F = True, GE = 1, I = True, IT = 0, J = False, M = 0x10, N = True, Q = True,
   T = False, V = True, Z = True, psr'rst = 1\<rparr>,
   CurrentCondition = 1, ELR_hyp = 1, Encoding = Encoding_ARM, Extensions = {Extension_Virtualization}, FP = FP',
   MEM = MEM', REG = Reg_Bank, SPSR_abt = SPSR_abt', SPSR_fiq = SPSR_fiq', SPSR_hyp = SPSR_hyp', SPSR_irq = SPSR_irq',
   SPSR_mon = SPSR_mon', SPSR_svc = SPSR_svc', SPSR_und = SPSR_und',  VFPExtension   =  NoVFP,exception = NoException, undefined = False,
   TTBR0 = Addr 0, ASID = 1, tlb_set = {}\<rparr>
   =  ((Addr 0xFC),   \<lparr>Architecture = ARMv7_A, CP14 = CP14',
   CP15 = \<lparr>HCR = HCR', HSCTLR = HSCTLR', HSR = HSR', MVBAR = 1, NSACR = NSACR', SCR = SCR',
   SCTLR = \<lparr>SCTLR.A = True, B = True, BR = True, C = True, DZ = True, EE = True, FI = True, I = True, IE = True,
   M = True, NMFI = True, RR = True, SW = True, TE = True, U = False, V = False, VE = True, Z = True,
   sctlr'rst = 1\<rparr>,  VBAR = 1\<rparr>,
   CPSR = \<lparr>PSR.A = True, C = True, E = False, F = True, GE = 1, I = True, IT = 0, J = False, M = 0x10, N = True, Q = True,
   T = False, V = True, Z = True, psr'rst = 1\<rparr>,
   CurrentCondition = 1, ELR_hyp = 1, Encoding = Encoding_ARM, Extensions = {Extension_Virtualization}, FP = FP',
   MEM = MEM', REG = Reg_Bank, SPSR_abt = SPSR_abt', SPSR_fiq = SPSR_fiq', SPSR_hyp = SPSR_hyp', SPSR_irq = SPSR_irq',
   SPSR_mon = SPSR_mon', SPSR_svc = SPSR_svc', SPSR_und = SPSR_und',  VFPExtension   =  NoVFP,exception = NoException, undefined = False,
   TTBR0 = Addr 0, ASID = 1, tlb_set = {}\<rparr> \<lparr> tlb_set := {pt_walk 1 MEM' (Addr 0) (Addr 0xFC)}    \<rparr> )")
   prefer 2
   apply (clarsimp simp:  mmu_translate_tlb_state_ext_def tlb_state'_def lookup_def entry_set_def Let_def not_is_fault_MEM')
   apply (clarsimp simp: va_to_pa_def pt_walk_section_MEM' mask_def)
  apply (clarsimp simp: mem_read1_def Let_def mem1_def MEM'_def)
  apply (subgoal_tac "229 = Suc (228) \<and> 130 = Suc (129) \<and> 16 = Suc (15) \<and> 4 = Suc (3)")
   apply (clarsimp simp:"log2.simps" )
   apply (clarsimp simp: bitstring_field_def bitstring_shiftr_def fixwidth_def pad_left_def)
  apply simp
  done




lemma decode_ins1:
  "Decode (ARM 0xE5821004) 
\<lparr>Architecture = ARMv7_A, CP14 = CP14',
       CP15 = \<lparr>HCR = HCR', HSCTLR = HSCTLR', HSR = HSR', MVBAR = 1, NSACR = NSACR', SCR = SCR',
                 SCTLR = \<lparr>SCTLR.A = True, B = True, BR = True, C = True, DZ = True, EE = True, FI = True, I = True, IE = True,
                            M = True, NMFI = True, RR = True, SW = True, TE = True, U = False, V = False, VE = True, Z = True,
                            sctlr'rst = 1\<rparr>,
                 VBAR = 1\<rparr>,
       CPSR = \<lparr>PSR.A = True, C = True, E = False, F = True, GE = 1, I = True, IT = 0, J = False, M = 0x10, N = True, Q = True,
                 T = False, V = True, Z = True, psr'rst = 1\<rparr>,
       CurrentCondition = 1, ELR_hyp = 1, Encoding = Encoding_ARM, Extensions = {Extension_Virtualization}, FP = FP', MEM = MEM',
       REG = Reg_Bank, SPSR_abt = SPSR_abt', SPSR_fiq = SPSR_fiq', SPSR_hyp = SPSR_hyp', SPSR_irq = SPSR_irq', SPSR_mon = SPSR_mon',
       SPSR_svc = SPSR_svc', SPSR_und = SPSR_und',  VFPExtension   =  NoVFP,exception = NoException, undefined = False, TTBR0 = Addr 0, ASID = 1,
       tlb_set = {pt_walk 1 MEM' (Addr 0) (Addr 0xFC)}\<rparr> = (Store (StoreWord (True, True, False, 1, 2, immediate_form1 4)) , 
       \<lparr>Architecture = ARMv7_A, CP14 = CP14',
       CP15 = \<lparr>HCR = HCR', HSCTLR = HSCTLR', HSR = HSR', MVBAR = 1, NSACR = NSACR', SCR = SCR',
                 SCTLR = \<lparr>SCTLR.A = True, B = True, BR = True, C = True, DZ = True, EE = True, FI = True, I = True, IE = True,
                            M = True, NMFI = True, RR = True, SW = True, TE = True, U = False, V = False, VE = True, Z = True,
                            sctlr'rst = 1\<rparr>,    VBAR = 1\<rparr>,
       CPSR = \<lparr>PSR.A = True, C = True, E = False, F = True, GE = 1, I = True, IT = 0, J = False, M = 0x10, N = True, Q = True,
                 T = False, V = True, Z = True, psr'rst = 1\<rparr>,
       CurrentCondition = 0xE, ELR_hyp = 1, Encoding = Encoding_ARM, Extensions = {Extension_Virtualization}, FP = FP', MEM = MEM',
       REG = Reg_Bank, SPSR_abt = SPSR_abt', SPSR_fiq = SPSR_fiq', SPSR_hyp = SPSR_hyp', SPSR_irq = SPSR_irq', SPSR_mon = SPSR_mon',
       SPSR_svc = SPSR_svc', SPSR_und = SPSR_und',  VFPExtension   =  NoVFP,exception = NoException, undefined = False, TTBR0 = Addr 0, ASID = 1,
       tlb_set = {pt_walk 1 MEM' (Addr 0) (Addr 0xFC)}\<rparr> )"
  apply (clarsimp simp: Decode_def DecodeARM_def Let_def Do_def ConditionPassed_def  CurrentCond_def  mask_def)
done






lemma pt_walk_section_MEM'_new:
  "pt_walk 1 MEM' (Addr 0) (Addr 0x4) = 
             EntrySection 1 (ucast ((0x4::32 word) >> 20) :: 12 word) (Some (0::12 word)) (0::8 word)"
  apply (simp only: pt_walk_def)
  apply (subgoal_tac "get_pde MEM' (Addr 0) (Addr 0x4) = Some (SectionPDE (Addr 0)
          \<lparr>arm_p_APX = 0, arm_p_AP = 0, arm_p_TEX = 0, arm_p_S = 0, arm_p_XN = 0, arm_p_C = 0, arm_p_B = 0, arm_p_nG = 0\<rparr>)")
   prefer 2
   apply (clarsimp simp: get_pde_def decode_heap_pde_def vaddr_pd_index_def)
   apply (rule_tac x = 2 in exI)
   apply (simp add: load_machine_word_def load_value_def load_list_def load_list_basic_def MEM'_def deoption_list_def from_bytes_word_def machine_b2w_def word_rcat_bl
         decode_pde_def decode_pde_section_def addr_base_def mask_def perm_bits_pde_sections_def split: option.splits)
  apply clarsimp
done
  



lemma run_ins1:
  "\<lbrakk>  lookup ({EntrySection 1 0 (Some 0) 0} -
             tlb_evict
              \<lparr>Architecture = ARMv7_A, CP14 = CP14',
                 CP15 = \<lparr>HCR = HCR', HSCTLR = HSCTLR', HSR = HSR', MVBAR = 1, NSACR = NSACR', SCR = SCR',
                           SCTLR = \<lparr>SCTLR.A = True, B = True, BR = True, C = True, DZ = True, EE = True, FI = True, I = True,
                                      IE = True, M = True, NMFI = True, RR = True, SW = True, TE = True, U = False, V = False,
                                      VE = True, Z = True, sctlr'rst = 1\<rparr>,
                           VBAR = 1\<rparr>,
                 CPSR = \<lparr>PSR.A = True, C = True, E = False, F = True, GE = 1, I = True, IT = 0, J = False, M = 0x10, N = True,
                           Q = True, T = False, V = True, Z = True, psr'rst = 1\<rparr>,
                 CurrentCondition = 0xE, ELR_hyp = 1, Encoding = Encoding_ARM, Extensions = {Extension_Virtualization}, FP = FP',
                 MEM = MEM', REG = Reg_Bank, SPSR_abt = SPSR_abt', SPSR_fiq = SPSR_fiq', SPSR_hyp = SPSR_hyp', SPSR_irq = SPSR_irq',
                 SPSR_mon = SPSR_mon', SPSR_svc = SPSR_svc', SPSR_und = SPSR_und', VFPExtension   =  NoVFP, exception = NoException, undefined = False,
                 TTBR0 = Addr 0, ASID = 1, \<dots> = {EntrySection 1 0 (Some 0) 0}\<rparr>)
      1 4 \<noteq>
     Incon ; Run (Store (StoreWord (True, True, False, 1, 2, immediate_form1 4)))
   \<lparr>Architecture = ARMv7_A, CP14 = CP14',
       CP15 = \<lparr>HCR = HCR', HSCTLR = HSCTLR', HSR = HSR', MVBAR = 1, NSACR = NSACR', SCR = SCR',
                 SCTLR = \<lparr>SCTLR.A = True, B = True, BR = True, C = True, DZ = True, EE = True, FI = True, I = True, IE = True,
                            M = True, NMFI = True, RR = True, SW = True, TE = True, U = False, V = False, VE = True, Z = True,
                            sctlr'rst = 1\<rparr>,
                 VBAR = 1\<rparr>,
       CPSR = \<lparr>PSR.A = True, C = True, E = False, F = True, GE = 1, I = True, IT = 0, J = False, M = 0x10, N = True, Q = True,
                 T = False, V = True, Z = True, psr'rst = 1\<rparr>,
       CurrentCondition = 0xE, ELR_hyp = 1, Encoding = Encoding_ARM, Extensions = {Extension_Virtualization}, FP = FP', MEM = MEM',
       REG = Reg_Bank, SPSR_abt = SPSR_abt', SPSR_fiq = SPSR_fiq', SPSR_hyp = SPSR_hyp', SPSR_irq = SPSR_irq', SPSR_mon = SPSR_mon',
       SPSR_svc = SPSR_svc', SPSR_und = SPSR_und',  VFPExtension   =  NoVFP,exception = NoException, undefined = False, TTBR0 = Addr 0, ASID = 1,
       tlb_set = {pt_walk 1 MEM' (Addr 0) (Addr 0xFC)}\<rparr>  = (() , s')\<rbrakk> \<Longrightarrow>
    REG s' =  Reg_Bank(RName_PC := 0x100) \<and> MEM s' = MEM'(Addr 4 \<mapsto> 1, Addr 5 \<mapsto> 0, Addr 6 \<mapsto> 0, Addr 7 \<mapsto> 0)"
  apply (clarsimp simp: Run_def dfn'StoreWord_def NullCheckIfThumbEE_def
      CurrentInstrSet_def ISETSTATE_def word_cat_def R_def Rmode_def IsSecure_def HaveSecurityExt_def LookUpRName_def Let_def UnalignedSupport_def ArchVersion_def
          write'MemU_def CurrentModeIsNotUser_def BadMode_def write'MemU_with_priv_def Aligned1_def Align1_def Reg_Bank_def write'MemA_with_priv_def mmu_write_size_tlb_state_ext_def mmu_translate_tlb_state_ext_def pt_walk_section_MEM' typ_tlb_def state.defs)
  apply (case_tac "lookup ({EntrySection 1 0 (Some 0) 0} -
                  tlb_evict
                   \<lparr>Architecture = ARMv7_A, CP14 = CP14',
                      CP15 = \<lparr>HCR = HCR', HSCTLR = HSCTLR', HSR = HSR', MVBAR = 1, NSACR = NSACR', SCR = SCR',
                                SCTLR = \<lparr>SCTLR.A = True, B = True, BR = True, C = True, DZ = True, EE = True, FI = True, I = True,
                                           IE = True, M = True, NMFI = True, RR = True, SW = True, TE = True, U = False, V = False,
                                           VE = True, Z = True, sctlr'rst = 1\<rparr>,
                                VBAR = 1\<rparr>,
                      CPSR = \<lparr>PSR.A = True, C = True, E = False, F = True, GE = 1, I = True, IT = 0, J = False, M = 0x10, N = True,
                                Q = True, T = False, V = True, Z = True, psr'rst = 1\<rparr>,
                      CurrentCondition = 0xE, ELR_hyp = 1, Encoding = Encoding_ARM, Extensions = {Extension_Virtualization}, FP = FP',
                      MEM = MEM', REG = Reg_Bank, SPSR_abt = SPSR_abt', SPSR_fiq = SPSR_fiq', SPSR_hyp = SPSR_hyp',
                      SPSR_irq = SPSR_irq', SPSR_mon = SPSR_mon', SPSR_svc = SPSR_svc', SPSR_und = SPSR_und',  VFPExtension   =  NoVFP,exception = NoException,
                      undefined = False, TTBR0 = Addr 0, ASID = 1, \<dots> = {EntrySection 1 0 (Some 0) 0}\<rparr>) 1 4 ")
    apply (clarsimp simp: Let_def is_fault_def  va_to_pa_def pt_walk_section_MEM'_new mask_def write'mem1_def IncPC_def ThisInstrLength_def BranchTo_def Reg_Bank_def)
    apply (clarsimp simp:"log2.simps" )
    apply (clarsimp simp: bitstring_field_def bitstring_shiftr_def fixwidth_def pad_left_def)
   apply clarsimp
  apply (subgoal_tac "x3 = EntrySection 1 0 (Some 0) 0")
   apply (clarsimp simp: is_fault_def va_to_pa_def mask_def write'mem1_def IncPC_def ThisInstrLength_def BranchTo_def Reg_Bank_def)
   apply (clarsimp simp:"log2.simps" )
   apply (clarsimp simp: bitstring_field_def bitstring_shiftr_def fixwidth_def pad_left_def)
  apply (clarsimp simp: lookup_def entry_set_def split:if_split_asm)
   apply blast+
  done






end