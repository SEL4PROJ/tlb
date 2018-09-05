-----------------------------------------------------------------------
-- Formal Specification of the ARMv7-AR instruction set architecture --
-- (c) Anthony Fox, University of Cambridge                          --
-----------------------------------------------------------------------

-- Preliminaries

-----------------------------------
-- Word sizes (32-bit architecture)
-----------------------------------

type reg  = bits(4)
type cond = bits(4)
type byte = bits(8)
type half = bits(16)
type word = bits(32)
type dword = bits(64)

---------------------------
-- Specification exceptions
---------------------------

exception ASSERT :: string
exception UNPREDICTABLE :: string
exception IMPLEMENTATION_DEFINED :: string
exception MMU_Exception :: string
--exception AlignmentFault :: word

------------------------
-- Architecture versions
------------------------

construct Architecture {
   ARMv4    ARMv4T
   ARMv5T   ARMv5TE
   ARMv6    ARMv6K    ARMv6T2
   ARMv7_A  ARMv7_R
}

declare Architecture :: Architecture

nat ArchVersion() =
   match Architecture
   { case ARMv4 or ARMv4T            => 4
     case ARMv5T or ARMv5TE          => 5
     case ARMv6 or ARMv6K or ARMv6T2 => 6
     case ARMv7_A or ARMv7_R         => 7
   }

--------------------------
-- Architecture extensions
--------------------------

construct Extensions {
   Extension_ThumbEE
   Extension_Security
   Extension_Multiprocessing
   Extension_Virtualization
   Extension_AdvanvedSIMD
}

declare Extensions :: Extensions set

bool HaveDSPSupport() = Architecture notin set {ARMv4, ARMv4T, ARMv5T}

bool HaveThumb2() = Architecture in set {ARMv6T2, ARMv7_A, ARMv7_R}

bool HaveThumbEE() =
   Architecture == ARMv7_A or
   Architecture == ARMv7_R and Extension_ThumbEE in Extensions

bool HaveMPExt() =
   ArchVersion() >= 7 and Extension_Multiprocessing in Extensions

bool HaveSecurityExt() =
   Architecture in set {ARMv6K, ARMv7_A} and Extension_Security in Extensions

bool HaveVirtExt() =
   ArchVersion() >= 7 and Extension_Virtualization in Extensions

----------------------------------
-- Program Status Registers (PSRs)
----------------------------------

register PSR :: word {
   31:    N     -- Condition flag (Negative)
   30:    Z     -- Condition flag (Zero)
   29:    C     -- Condition flag (Carry)
   28:    V     -- Condition flag (oVerflow)
   27:    Q     -- Cumulative saturation flag
   15-10,
   26-25: IT    -- If-Then
   24:    J     -- Jazelle bit
   23-20: RAZ!  -- reserved
   19-16: GE    -- Greater-equal flags (SIMD)
   9:     E     -- Endian bit (T: Big, F: Little)
   8:     A     -- Asynchronous abort disable
   7:     I     -- Interrupt disable
   6:     F     -- Fast interrupt disable
   5:     T     -- Thumb mode
   4-0:   M     -- Mode field
}

declare {
   CPSR     :: PSR
   SPSR_fiq :: PSR
   SPSR_irq :: PSR
   SPSR_svc :: PSR
   SPSR_mon :: PSR
   SPSR_abt :: PSR
   SPSR_hyp :: PSR
   SPSR_und :: PSR
}

-----------------
-- CP14 registers
-----------------

record CP14 {
   TEEHBR :: word -- ThumbEE Handler Base Register
}

declare CP14 :: CP14

-----------------
-- CP15 registers
-----------------

-- System Control Register (PMSA)

register SCTLR :: word {
   31:    IE    -- Instruction endianness (T: Big, F: Little)
   30:    TE    -- Thumb exception enable (T: Handled in Thumb state, F: in ARM)
   29-28: RAZ!
   27:    NMFI  -- Non-maskable fast interupts (T: non-maskable, F: maskable)
   26:    RAZ!
   25:    EE    -- Exception endianness (T: Big, F: Little)
   24:    VE    -- Interrupt vectors enable
   23:    RAO!
   22:    U     -- Alignment model
   21:    FI    -- Fast interrupts configuration
   20:    RAZ!
   19:    DZ    -- Divide by Zero fault enable
   18:    RAO!
   17:    BR    -- Background region bit
   16:    RAO!
   15:    RAZ!
   14:    RR    -- Round Robin bit
   13:    V     -- Vectors bit
   12:    I     -- Instruction cache enable
   11:    Z     -- Branch prediction enable
   10:    SW    -- SWP/SWPB enable
   9-8:   RAZ!
   7:     B     -- Endian model
   6-3:   RAO!
   2:     C     -- Cache enable bit
   1:     A     -- Alignment check enable bit
   0:     M     -- MPU enable bit
}

-- Hyp System Control Register (VMSA)

register HSCTLR :: word {
   31:    RAZ!
   30:    TE      -- Thumb exception enable
   29-28: RAO!
   27-26: RAZ!
   25:    EE      -- Exception endianness
   24:    RAZ!
   23-22: RAO!
   21:    FI      -- Fast interrupts configuration
   20:    RAZ!
   19:    WXN     -- Write permission implies XN
   18:    RAO!
   17:    RAZ!
   16:    RAO!
   15-13: RAZ!
   12:    I       -- Instruction cache enable
   11:    RAO!
   10-7:  RAZ!
   6:     RAO!
   5:     CP15BEN -- CP15 barrier enable
   4-3:   RAO!
   2:     C       -- Cache enable bit
   1:     A       -- Alignment check enable bit
   0:     M       -- MPU enable bit
}

-- Hyp System Control Register (VMSA)

register HSR :: word {
   31-26: EC   -- Exception class
   25:    IL   -- Instruction length
   24-0:  ISS  -- Instruction-specific syndrome
}

-- Secure Configuration Register (VMSA only)

register SCR :: word {
   31-10: UNK!
   9:     SIF   -- Secure instruction fetch
   8:     HCE   -- Hyp Call enable
   7:     SCD   -- Secure Monitor Call disable
   6:     nET   -- Not early termination (T: disable early termination)
   5:     AW    -- "A" bit writable
   4:     FW    -- "F" bit writable
   3:     EA    -- External abort handler (T: Monitor mode, F: Abort mode)
   2:     FIQ   -- FIQ handler (T: Monitor mode, F: Abort mode)
   1:     IRQ   -- IRQ handler (T: Monitor mode, F: Abort mode)
   0:     NS    -- Non secure bit
}

-- Non-Secure Access Control Register (VMSA only)

register NSACR :: word {
   31-21: UNK!
   20:    NSTRCDIS  -- Disable Non-secure access to CP14 trace registers
   19:    RFR       -- Reserve FIQ registers
   18-16: UNK!      -- Implemenation defined
   15:    NSASEDIS  -- Disable non-secure Advanced SIMD functionality
   14:    NSD32DIS  -- Disable non-secure use of D16-D31 of the VFP registers
   13-0:  cp        -- Non-secure acceess to copreocessor cp<n>
}

-- Hyp Configuration Register (VMSA, Virtualization Extensions only)

register HCR :: word {
   31-28: UNK!
   27:    TGE       -- Trap general exceptions
   26:    TVM       -- Trap virtual memory controls
   25:    TTLB      -- Trap TLB maintenance operations
   24:    TPU       -- Trap cache maintenance to point of unification operations
   23:    TPC       -- Trap cache maintenance to point of coherency operations
   22:    TSW       -- Trap set/way cache maintenance operations
   21:    TAC       -- Trap ACTLR accesses
   20:    TIDCP     -- Trap lockdown
   19:    TSC       -- Trap SMC instruction
   18-15: TID       -- Trap ID register groups
   14:    TWE       -- Trap WFE instruction
   13:    TWI       -- Trap WFI instruction
   12:    DC        -- Default cacheable
   11-10: BSU       -- Barrier shareability upgrade
   9:     FB        -- Force broadcast
   8:     VA        -- Virtual asynchronous abort
   7:     VI        -- Virtual IRQ
   6:     VF        -- Virtual FIQ
   5:     AMO       -- Overides CPSR.A bit
   4:     IMO       -- Overides CPSR.I bit
   3:     FMO       -- Overides CPSR.F bit
   2:     PTW       -- Protected table walk
   1:     SWIO      -- Set/way invalidation override
   0:     VM        -- Virtualization MMU enable bit
}

{-
-- Coprocessor Access Control Register (PMSA)

register CPACR :: word {
  31:    ASEDIS  -- Disable Adcanced SIMD functionality
  30:    D32DIS  -- Disable use of D16-D31 of the floating-point register file
  29:    RAZ!
  28:    TRCDIS  -- Disable CP14 access to trace registers
  27-26: cp13    -- Access rights for coprocessor
  25-24: cp12
  23-22: cp11
  21-20: cp10
  19-18: cp9
  17-16: cp8
  15-14: cp7
  13-12: cp6
  11-10: cp5
  9-8:   cp4
  7-6:   cp3
  5-4:   cp2
  3-2:   cp1
  1-0:   cp0
}
-}




--*******************************************--
-- Adding CP15 registers here from the architecure reference manual --
--*******************************************--

-- B4.1.1
-- IMPLEMENTATION DEFINED Auxiliary Control Register, VMSA
register ACTLR :: word {
   31-0: ACTLR_IMPLEMENTATION_DEFINED_BITS
}


-- B4.1.2
-- Auxiliary Data Fault Status Registers, VMSA
register ADFSR :: word {
   31-0: ADFSR_IMPLEMENTATION_DEFINED_BITS
}

-- B4.1.3
-- IMPLEMENTATION DEFINED Auxiliary ID Register, VMSA
register AIDR :: word {
   31-0: AIDR_IMPLEMENTATION_DEFINED_BITS    
   
}
-- B4.1.4
-- Auxiliary Instruction Fault Status Registers, VMSA
register AIFSR :: word {
   31-0: AIFSR_IMPLEMENTATION_DEFINED_BITS
}



-- B4.1.5
-- Auxiliary Memory Attribute Indirection Registers 0, VMSA
register AMAIR0 :: word {
   31-0: AMAIR0_IMPLEMENTATION_DEFINED_BITS
}

-- B4.1.5
-- Auxiliary Memory Attribute Indirection Registers 1, VMSA
register AMAIR1 :: word {
   31-0: AMAIR1_IMPLEMENTATION_DEFINED_BITS
}


-- B4.1.6
-- ATS12NSOPR, Address Translate Stages 1 and 2 Non-secure PL1 Read, VMSA only

-- B4.1.7
-- ATS12NSOPW, Address Translate Stages 1 and 2 Non-secure PL1 Write, VMSA only

-- B4.1.8
-- ATS12NSOUR, Address Translate Stages 1 and 2 Non-secure Unprivileged Read, VMSA only

-- B4.1.9
-- ATS12NSOUW, Address Translate Stages 1 and 2 Non-secure Unprivileged Write, VMSA only

-- B4.1.10
-- ATS1CPR, Address Translate Stage 1 Current state PL1 Read, VMSA only

-- B4.1.11
-- ATS1CPW, Address Translate Stage 1 Current state PL1 Write, VMSA only

-- B4.1.12
-- ATS1CUR, Address Translate Stage 1 Current state Unprivileged Read, VMSA only

-- B4.1.13
-- ATS1CUW, Address Translate Stage 1 Current state Unprivileged Write, VMSA only

-- B4.1.14
-- ATS1HR, Address Translate Stage 1 Hyp mode Read, VMSA only

-- B4.1.15
-- ATS1HW, Address Translate Stage 1 Hyp mode Write, VMSA only

-- B4.1.16
-- BPIALL, Branch Predictor Invalidate All, VMSA

-- B4.1.17
-- BPIALLIS, Branch Predictor Invalidate All, Inner Shareable, VMSA

-- B4.1.18
-- BPIMVA, Branch Predictor Invalidate by MVA, VMSA

-- B4.1.19
-- Cache Size ID Registers, VMSA
register CCSIDR :: word {
    31:    WT    
    30:    WB
    29:    RA
    28:    WA
    27-13: NUMSETS 
    12-3:  ASSOCIATIVITY
    2-0:   LINESIZE       
}


-- B4.1.20
-- Cache Level ID Register, VMSA
register CLIDR :: word {
    31: UNK!    
    30: UNK!
    29-27: LOUU
    26-24: LOC
    23-21: LOUIS
    20-18: CTYPE7
    17-15: CTYPE6
    14-12: CTYPE5
    11-9:  CTYPE4
    8-6:   CTYPE3
    5-3:   CTYPE2    
    2-0:   CTYPE1
}

-- B4.1.21
-- Counter Frequency register, VMSA
register CNTFRQ :: word {
    31-0: CLOCK_FREQUENCY
}

-- B4.1.22
-- Timer PL2 Control register, Virtualization Extensions
register CNTHCTL :: word {
    31-8: UNK!    
    7-4:  EVNTI
    3:    EVNTDIR
    2:    EVNTEN
    1:    PL1PCEN
    0:    PL1PCTEN
}


-- B4.1.23
-- PL2 Physical Timer Control register, Virtualization Extension
register CNTHP_CTL :: word {
    31-3: UNK!    
    2:    ISTATUS
    1:    IMASK
    0:    ENABLE
}


-- B4.1.24
-- PL2 Physical Timer CompareValue register, Virtualization Extensions
register CNTHP_CVAL :: dword {
    63-0: COMPAREVALUE    
}


-- B4.1.25
-- PL2 Physical TimerValue register, Virtualization Extensions
register CNTHP_TVAL :: word {
    31-0: TIMERVALUE
}


-- B4.1.26
-- Timer PL1 Control register, VMSA
register CNTKCTL :: word {
    31-10: UNK!
    9:     PL0PTEN
    8:     PL0VTEN
    7-4:   EVNTI
    3:     EVNTDIR
    2:     EVNTEN
    1:     PL0VCTEN
    0:     PL0PCTEN
}


-- B4.1.27
-- PL1 Physical Timer Control register, VMSA
register CNTP_CTL :: word {
    31-3: UNK!
    2:    ISTATUS
    1:    IMASK
    0:    ENABLE
}

-- B4.1.28
-- PL1 Physical Timer CompareValue register, VMSA
register CNTP_CVAL :: dword {
    63-0: COMPAREVALUE
}

-- B4.1.29
-- PL1 Physical TimerValue register, VMSA
register CNTP_TVAL :: word {
    31-0: TIMERVALUE
}


-- B4.1.30
-- Physical Count register, VMSA
register CNTPCT :: dword {
    63-0: PHYSICALCOUNT
}

-- B4.1.31
-- Virtual Timer Control register, VMSA
register CNTV_CTL :: word {
    31-3: UNK!
    2:    ISTATUS
    1:    IMASK
    0:    ENABLE
}

-- B4.1.32
-- Virtual Timer CompareValue register, VMSA
register CNTV_CVAL :: dword {
    63-0: COMPAREVALUE
}

-- B4.1.33
-- Virtual TimerValue register, VMSA
-- PL1 Physical TimerValue register, VMSA
register CNTV_TVAL :: word {
    31-0: TIMERVALUE
}

-- B4.1.34
-- Virtual Count register, VMSA
register CNTVCT :: dword {
    63-0: VIRTUALCOUNT
}


-- B4.1.35
-- Virtual Offset register, VMSA
register CNTVOFF :: dword {
    63-0: VIRTUALOFFSET
}

-- B4.1.36
-- Context ID Register, VMSA
register CONTEXTIDR :: word {
    31-8: PROCID
	  7-0:  ASID
}


-- B4.1.37
-- CP15DMB, CP15 Data Memory Barrier operation, VMSA

-- B4.1.38
-- CP15DSB, CP15 Data Synchronization Barrier operation, VMSA

-- B4.1.39
-- CP15ISB, CP15 Instruction Synchronization Barrier operation, VMSA

-- B4.1.40
-- Coprocessor Access Control Register, VMSA
register CPACR :: word {
   31:    ASEDIS    
   30:    D32DIS
   29:    UNK!
   28:    TRCDIS
   27-26: cp13
   25-24: cp12
   23-22: cp11
   21-20: cp10
   19-18: cp9
   17-16: cp8
   15-14: cp7
   13-12: cp6
   11-10: cp5
   9-8:   cp4
   7-6:   cp3
   5-4:   cp2
   3-2:   cp1
   1-0:   cp0
}


-- B4.1.41
-- Cache Size Selection Register, VMSA
register CSSELR :: word {
   31-4: UNK!    
   3-1:  LEVEL
   0:    IND
}

-- B4.1.42
-- Cache Type Register, VMSA
register CTR :: word {
   31-29:  FORMAT
   28:     RAZ!
   27-24:  CWG
   23-20:  ERG
   19-16:  DMINLINE
   15-14:  L1IP
   13-4:   RAZ!
   3-0:    IMINLINE
}

-- B4.1.43
-- Domain Access Control Register, VMSA
register DACR :: word {
   31-30: D15
   29-28: D14
   27-26: D13
   25-24: D12
   23-22: D11
   21-20: D10
   19-18: D9
   17-16: D8
   15-14: D7
   13-12: D6
   11-10: D5
   9-8:   D4
   7-6:   D3
   5-4:   D2
   3-2:   D1
   1-0:   D0
}

-- B4.1.44
-- Data Cache Clean and Invalidate by MVA to PoC, VMSA


-- B4.1.45
-- Data Cache Clean and Invalidate by Set/Way, VMSA

-- B4.1.46
-- Data Cache Clean by MVA to PoC, VMSA


-- B4.1.47
-- Data Cache Clean by MVA to PoU, VMSA


-- B4.1.48
-- Data Cache Clean by Set/Way, VMSA


-- B4.1.49
-- Data Cache Invalidate by MVA to PoC, VMSA

-- B4.1.50
-- Data Cache Invalidate by Set/Way, VMSA


-- B4.1.51
-- Data Fault Address Register, VMSA
register DFAR :: word {
   31-0: VA_FAULT_ADDRESS
}

-- B4.1.52
-- Data Fault Status Register, VMSA
register DFSR :: word {
   31-14: UNK!    
   13:    CM
   12:    EXT
   11:    WNR   
   10:    FS_1
   9:     LPAE
   8:     UNK!
   7-4:   DOMAIN
   3-0:   FS_2
}

-- B4.1.53
-- Data TLB Invalidate All, VMSA only

-- B4.1.54
-- Data TLB Invalidate by ASID, VMSA only

-- B4.1.55
-- Data TLB Invalidate by MVA, VMSA only


-- B4.1.56
-- FCSE Process ID Register, VMSA
register FCSEIDR :: word {
    31-25:  PID   
    24-0: UNK!
}

-- B4.1.57
-- Floating-Point Exception Control register, VMSA
register FPEXC :: word {
   31:   EX   
   30:   EN
   29-0: SUBARCHITECTURE_DEFINED
}

--already there
-- B4.1.58
-- Floating-point Status and Control Register, VMSA
--register FPSCR :: word {
--    31:    N   
--    30:    Z
--    29:    C
--    28:    V
--    27:    QC
--    26:    AHP
--    25:    DN
--    24:    FZ
--    23-22: RMODE
--    21-20: STRIDE
--    19:    FPSCR_RESERVED0
--    18-16: LEN
--    15:    IDE
--    14-13: FPSCR_RESERVED1
--    12:    IXE
--    11:    UFE       
--    10:    OFE
--    9:     DZE
--    8:     IOE
--    7:     IDC
--    6-5:   FPSCR_RESERVED2
--    4:     IXC
--    3:     UFC
--    2:     OFC
--    1:     DZC
--    0:     IOC
--}

-- B4.1.59
-- Floating-point System ID Register, VMSA
register FPSID :: word {
    31-24: IMPLEMENTER
    23:    SW
    22-16: SUBARCHITECTURE
    15-8:  PART_NUMBER
    7-4:   VARIANT
    3-0:   REVISION
}

-- B4.1.60
-- Hyp Auxiliary Configuration Register, Virtualization Extensions
register HACR :: word {
    31-0: HACR_IMPLEMENTATION_DEFINED 

}

-- B4.1.61
-- Hyp Auxiliary Control Register, Virtualization Extensions
register HACTLR :: word {
    31-0: HACTLR_IMPLEMENTATION_DEFINED 
}

-- B4.1.62
-- Hyp Auxiliary Fault Syndrome Registers, Virtualization Extensions
register HADFSR :: word {
    31-0: HADFSR_IMPLEMENTATION_DEFINED 
}

-- B4.1.62
-- Hyp Auxiliary Fault Syndrome Registers, Virtualization Extensions
register HAIFSR :: word {
    31-0: HAIFSR_IMPLEMENTATION_DEFINED 
}

-- B4.1.63
-- Hyp Auxiliary Memory Attribute Indirection Registers 0
register HAMAIR0 :: word {
    31-0: HAMAIR0_IMPLEMENTATION_DEFINED 
}

-- B4.1.63
-- Hyp Auxiliary Memory Attribute Indirection Registers 1
register HAMAIR1 :: word {
    31-0: HAMAIR1_IMPLEMENTATION_DEFINED 
}


-- B4.1.64
-- 
register HCPTR :: word {
    31:    TCPAC    
    30-21: UNK!
    20:    TTA
    19-16: UNK!
    15:    TASE
    14:    UNK!
    13:    TCP13
    12:    TCP12
    11:    TCP11     
    10:    TCP10
    9:     TCP9
    8:     TCP8
    7:     TCP7
    6:     TCP6
    5:     TCP5
    4:     TCP4
    3:     TCP3
    2:     TCP2
    1:     TCP1
    0:     TCP0
}

--already there
-- B4.1.65
-- Hyp Configuration Register, Virtualization Extensions
--register HCR :: word {
--    31-28: UNK!
--  27:    TGE
--  26:    TVM
--    25:    TTLB
--    24:    TPU
--    23:    TPC
--    22:    TSW
--    21:    TAC
--    20:    TIDCP
--    19:    TSC
--    18:    TID3
--    17:    TID2
--    16:    TID1
--    15:    TID0
--    14:    TWE
--    13:    TW1
--    12:    DC
--    11-10: BSU
--    9:     FB
--    8:     VA
--    7:     VI
--    6:     VF
--    5:     AMO
--    4:     IMO
--    3:     FMO
--    2:     PTW
--    1:     SWIO
--    0:     VM
--}


-- B4.1.66
-- Hyp Debug Configuration Register, Virtualization Extensions
register HDCR :: word {
    31-12: UNK!
    11:    TDRA       
    10:    TDOSA
    9:     TDA
    8:     TDE
    7:     HPME   -- implementation defined
    6:     TPM
    5:     TPMCR
    4-0:   HPMN    
}


-- B4.1.67
-- Hyp Data Fault Address Register, Virtualization Extensions
register HDFAR :: word {
  31-0: VA_FAULT   
}


-- B4.1.68
-- Hyp Instruction Fault Address Register, Virtualization Extensions
register HIFAR :: word {
   31-0: VA_FAULT
}


-- B4.1.69
-- HMAIR0, Hyp Memory Attribute Indirection Registers 0, Virtualization Extensions
register HMAIR0 :: word {
   31-0: HMAIR0_BITS
}

-- B4.1.69
-- HMAIR0, Hyp Memory Attribute Indirection Registers 1, Virtualization Extensions
register HMAIR1 :: word {
   31-0: HMAIR1_BITS 
}

-- B4.1.70
-- Hyp IPA Fault Address Register, Virtualization Extensions
register HPFAR :: word {
   31-4: FIPA
   3-0 : UNK! 
}

-- already there
-- B4.1.71
-- Hyp System Control Register, Virtualization Extensions
--register HSCTLR :: word {
--   
--}


-- already there
-- B4.1.72
-- Hyp Syndrome Register, Virtualization Extensions
--register HSR :: word {
--
--}


-- B4.1.73
-- Hyp System Trap Register, Virtualization Extensions
register HSTR :: word {
    31-18:  UNK!    
    17:  TJDBX
    16:  TTEE
    15:  T15
    14:  RAZ!
    13:  T13
    12:  T12
    11:  T11      
    10:  T10
    9:   T9
    8:   T8
    7:   T7
    6:   T6
    5:   T5
    4:   RAZ!
    3:   T3
    2:   T2
    1:   T1
    0:   T0
}


-- B4.1.74
-- Hyp Translation Control Register, Virtualization Extensions
register HTCR :: word {
    31: UNK!   
    30: HTCR_IMPLEMENTATION_DEFINED
    29-14: UNK!
    13-12: SH0
    11-10: ORGN0       
    9-8:   IRGN0
    7-3:   UNK!
    2-0:   T0SZ
}

-- B4.1.75
-- Hyp Software Thread ID Register, Virtualization Extensions
register HTPIDR :: word {
    31-0: HTPIDR_BITS 
}

-- B4.1.76
-- Hyp Translation Table Base Register, Virtualization Extensions
register HTTBR :: dword {
    63-0: HTTBR_BITS 
}

-- B4.1.77
-- 
register  HVBAR :: word {
    31-5: HYP_VECTOR_BASE_ADDRESS
    4-0:  UNK! 
}

-- B4.1.78
-- ICIALLU, Instruction Cache Invalidate All to PoU, VMSA


-- B4.1.79
-- ICIALLUIS, Instruction Cache Invalidate All to PoU, Inner Shareable, VMSA


-- B4.1.80
-- ICIMVAU, Instruction Cache Invalidate by MVA to PoU, VMSA



-- B4.1.81
-- Auxiliary Feature Register 0, VMSA
register ID_AFR0 :: word {
    31-16: UNK!
    15-12: ID_AFR0_IMPLEMENTATION_DEFINED0
	11-8:  ID_AFR0_IMPLEMENTATION_DEFINED1
	7-4:   ID_AFR0_IMPLEMENTATION_DEFINED2
	3-0:   ID_AFR0_IMPLEMENTATION_DEFINED3
}


-- B4.1.82
-- Debug Feature Register 0, VMSA
register ID_DFR0 :: word {
    31-0: ID_DFR0_BITS  
}
-- B4.1.83
-- Instruction Set Attribute Register 0, VMSA
register ID_ISAR0 :: word {
    31-0: ID_ISAR0_BITS  
}

-- B4.1.84
-- Instruction Set Attribute Register 1, VMSA
register  ID_ISAR1 :: word {
    31-0: ID_ISAR1_BITS  
}

-- B4.1.85
-- Instruction Set Attribute Register 2, VMSA
register  ID_ISAR2 :: word {
    31-0: ID_ISAR2_BITS  
}

-- B4.1.86
-- Instruction Set Attribute Register 3, VMSA
register  ID_ISAR3 :: word {
    31-0: ID_ISAR3_BITS  
}


-- B4.1.87
-- Instruction Set Attribute Register 4, VMSA
register ID_ISAR4 :: word {
    31-0: ID_ISAR4_BITS  
}


-- B4.1.88
-- Instruction Set Attribute Register 5, VMSA
register ID_ISAR5 :: word {
    31-0: ID_ISAR5_BITS  
}


-- B4.1.89
-- Memory Model Feature Register 0, VMSA
register ID_MMFR0 :: word {
    31-0: ID_MMFR0_BITS  
}


-- B4.1.90
-- Memory Model Feature Register 1, VMSA
register  ID_MMFR1 :: word {
    31-0: ID_MMFR1_BITS  
}


-- B4.1.91
-- Memory Model Feature Register 2, VMSA
register ID_MMFR2 :: word {
    31-0: ID_MMFR2_BITS  
}


-- B4.1.92
-- Memory Model Feature Register 3, VMSA
register ID_MMFR3 :: word {
    31-0: ID_MMFR3_BITS  
}


-- B4.1.93
-- Processor Feature Register 0, VMSA
register ID_PFR0 :: word {
    31-0: ID_PFR0_BITS  
}

-- B4.1.94
-- Processor Feature Register 1, VMSA
register  ID_PFR1 :: word {
    31-0: ID_PFR1_BITS  
}


-- B4.1.95
-- Instruction Fault Address Register, VMSA
register  IFAR :: word {
    31-0: IFAR_BITS  
}


-- B4.1.96
-- Instruction Fault Status Register, VMSA
register  IFSR :: word {
    31-0: IFSR_BITS  
}


-- B4.1.97
-- Interrupt Status Register, Security Extensions
register ISR :: word {
    31-0: ISR_BITS  
}


-- B4.1.98
-- ITLBIALL, Instruction TLB Invalidate All, VMSA only



-- B4.1.99
-- ITLBIASID, Instruction TLB Invalidate by ASID, VMSA only




-- B4.1.100
-- ITLBIMVA, Instruction TLB Invalidate by MVA, VMSA only


-- B4.1.101
-- Jazelle ID Register, VMSA
register JIDR :: word {
    31-0: JIDR_BITS  
}


-- B4.1.102
-- Jazelle Main Configuration Register, VMSA
register JMCR :: word {
    31-0: JMCR_BITS  
}


-- B4.1.103
-- Jazelle OS Control Register, VMSA
register  JOSCR :: word {
    31-0: JOSCR_BITS  
}


-- B4.1.104
-- Memory Attribute Indirection Registers 0, VMSA
register MAIR0 :: word {
    31-0: MAIR0_BITS  
}

-- B4.1.104
-- Memory Attribute Indirection Registers 1, VMSA
register MAIR1 :: word {
    31-0: MAIR1_BITS  
}





-- B4.1.105
-- Main ID Register, VMSA
-- provides identification information for the processor, including an implementer code for the device and a device ID number

register MIDR :: word {
   31-24: IMPLEMENTER    		-- sholud be 0x41 for ARM  
   23-20: VARIANT        		-- IMPLEMENTATION DEFINED 
   19-16: ARCHITECTURE          -- 0x7 for ARMv7 (Defined by CPUID scheme)
   15-4:  PRIMARY_PART_NUMBER   -- IMPLEMENTATION DEFINED
   3-0:   REVISION    			-- IMPLEMENTATION DEFINED
}


-- B4.1.106
-- Multiprocessor Affinity Register, VMSA
-- MPIDR fields depend on the fact the the implementation supports multiprocessing extensions or not, since Cortex-A9 does, so this register has the following format

register MPIDR :: word {
   31:    RAO!   
   30:    U      -- uniprocessor bit
   29-25: UNK!
   24:    MT    -- Affinity levels
   23-16: AFF2  -- Affinity level 2
   15-8:  AFF1  -- Affinity level 1
   7-0:   AFF0  -- Affinity level 0
}



-- B4.1.107
-- Monitor Vector Base Address Register, Security Extensions
--  holds the exception base address for all exceptions that are taken to Monitor mode

register MVBAR :: word {
   31-5: MONITOR_VECTOR_BASE_ADDRESS  -- base address of the exception vectors for exceptions that are taken to Monitor mode
   4-0: UNK!   -- UNK/SBZP
}


-- B4.1.108
--  Media and VFP Feature Register 0, VMSA
-- Describes the features provided by the Advanced SIMD and Floating-point Extensions
register MVFR0 :: word {
   31-28: VFP_ROUNDING_MODES   -- Indicates the rounding modes supported by the Floating-point Extension hardware
   27-24: SHORT_VECTORS        -- Indicates the hardware support for VFP short vectors
   23-20: SQUARE_ROOT         -- Indicates the hardware support for the Floating-point Extension square root operations
   19-16: DIVIDE              -- Indicates the hardware support for Floating-point Extension divide operations
   15-12: VFP_EXCEPTION_TRAPPING  -- Indicates whether the Floating-point Extension hardware implementation supports exception trapping
   11-8:  DOUBLE_PRECISION  -- Indicates the hardware support for the Floating-point Extension double-precision operations
   7-4:   SINGLE_PRECISION  -- Indicates the hardware support for the Floating-point Extension single-precision operations.
   3-0:   A_SIMD_REGISTERS  -- Indicates support for the Advanced SIMD register bank
}


-- B4.1.109
-- Media and VFP Feature Register 1, VMSA
-- Describes the features provided by the Advanced SIMD and Floating-point Extensions

register MVFR1 :: word {
   31-28: A_SIMD_FMAC    
   27-24: VFP_HPFP
   23-20: A_SIMD_HPFP
   19-16: A_SIMD_SPFP
   15-12: A_SIMD_INTEGER
   11-8:  A_SIMD_LOAD_STORE
   7-4:   D_NAN_MODE
   3-0:   FTZ_MODE
}


-- B4.1.110
-- Normal Memory Remap Register, VMSA
-- provides additional mapping controls for memory regions that are mapped as Normal memory by their entry in the PRRR

register NMRR :: word {
   31-30: OR7     -- Outer Cacheable property mapping
   29-28: OR6
   27-26: OR5
   25-24: OR4
   23-22: OR3
   21-20: OR2
   19-18: OR1
   17-16: OR0
   15-14: IR7    -- Inner Cacheable property mapping
   13-12: IR6
   11-10: IR5
   9-8:   IR4
   7-6:   IR3
   5-4:   IR2
   3-2:   IR1
   1-0:   IR0
}

-- B4.1.111
-- Non-Secure Access Control Register, Security Extensions
-- Defines the Non-secure access permissions to coprocessors CP0 to CP13
--ALREADY_THERE
--register NSACR :: word {
 --  31-21: UNK!
 --  20: NSTRCDIS
 --  19: RFR
 --  18-16: IMPLEMENTATION_DEFINED
 --  15: NSASEDIS
 --  14: NSD32DIS
 --  13: CP13
 --  12: CP12
 --  11: CP11     
 --  10: CP10
 --  9:  CP9
--   8:  CP8
--   7:  CP7
--   6:  CP6
 --  5:  CP5
 --  4:  CP4
 --  3:  CP3
 --  2:  CP2
 --  1:  CP1
 --  0:  CP0
 --}


-- B4.1.112
-- Physical Address Register, VMSA
-- Receives the PA from any address translation operation
-- heavily depend on the implementation 

register PAR :: word {
   31-12: PA    
   11:    LPAE  --  implementation defined, couldn't find it's vaue in the cortex manual for the time being      
   10:    NOS
   9:     NS
   8:     IMPLEMENTATION_DEFINE
   7:     SH
   6-4:   INNER
   3-2:   OUTER
   1:     SS
   0:     F
}


-- B4.1.113
-- Performance Monitors Cycle Count Register, VMSA
-- The PMCCNTR holds the value of the processor Cycle Counter, CCNT, that counts processor clock cycles
register PMCCNTR :: word {
   31-0: CCNT
}


-- The PMCEIDn registers define which common architectural and common microarchitectural feature events are implemented.
-- B4.1.114
-- Performance Monitors Common Event ID registers, VMSA
register PMCEID0 :: word {
   31-0: PMCEID0_BITS  -- leaving as this for the time-being, little confusing
}

-- B4.1.114
-- Performance Monitors Common Event ID registers, VMSA
register PMCEID1 :: word {
   31-0:  RAZ!
}


-- B4.1.115
-- Performance Monitors Count Enable Clear register, VMSA
register PMCNTENCLR :: word {
   31-0:  PMCNTENCLR_BITS
}


-- B4.1.116
-- Performance Monitors Count Enable Set register, VMSA
register PMCNTENSET :: word {
   31-0:  PMCNTENSET_BITS
}


-- B4.1.117
-- Performance Monitors Control Register, VMSA
register PMCR :: word {
   31-0:  PMCR_BITS
}


-- B4.1.118
--  Performance Monitors Interrupt Enable Clear register, VMSA
register PMINTENCLR :: word {
   31-0:  PMINTENCLR_BITS
}


-- B4.1.119
-- Performance Monitors Interrupt Enable Set register, VMSA
register PMINTENSET :: word {
   31-0:  PMINTENSET_BITS
}


-- B4.1.120
-- Performance Monitors Overflow Flag Status Register, VMSA
register PMOVSR :: word {
   31-0:  PMOVSR_BITS
}



-- B4.1.121
-- Performance Monitors Overflow Flag Status Set register, Virtualization
register PMOVSSET :: word {
   31-0:  PMOVSSET_BITS
}


-- B4.1.122
-- Performance Monitors Event Counter Selection Register, VMSA
register PMSELR :: word {
   31-0:  PMSELR_BITS
}


-- B4.1.123
-- Performance Monitors Software Increment register, VMSA
register PMSWINC :: word {
   31-0:  PMSWINC_BITS
}


-- B4.1.124
-- Performance Monitors User Enable Register, VMSA
register PMUSERENR :: word {
   31-0:  PMUSERENR_BITS
}


-- B4.1.125
-- Performance Monitors Event Count Register, VMSA
register PMXEVCNTR :: word {
   31-0:  PMXEVCNTR_BITS
}


-- B4.1.126
-- Performance Monitors Event Type Select Register, VMSA
register PMXEVTYPER :: word {
   31-0:  PMXEVTYPER_BITS
}


-- B4.1.127
-- Primary Region Remap Register, VMSA
register PRRR :: word {
   31:    NOS7  
   30:    NOS6
   29:    NOS5
   28:    NOS4
   27:    NOS3
   26:    NOS2
   25:    NOS1
   24:    NOS0
   23-20: UNK!
   19:    NS1
   18:    NS0
   17:    DS1
   16:    DS0
   15-14: TR7
   13-12: TR6
   11-10: TR5
   9-8:   TR4
   7-6:   TR3
   5-4:   TR2
   3-2:   TR1
   1-0:   TR0
}


-- B4.1.128
-- Revision ID Register, VMSA
register REVIDR :: word {
   31-0:  REVIDR_BITS
}


-- B4.1.129
-- Secure Configuration Register, Security Extensions
--register SCR :: word {
--  31-0:  SCR_BITS
--}


-- B4.1.130
-- System Control Register, VMSA
-- SCTLR in the manual
register  VSCTLR :: word {
   31: UNK!    
   30: TE
   29: AFE
   28: TRE
   27: NMFI
   26: RAZ!
   25: EE
   24: VE
   23: RAO!
   22: U
   21: FI
   20: UWXN
   19: WXN
   18: RAO!
   17: HA
   16: RAO!
   15: RAZ!
   14: RR
   13: V
   12: I
   11: Z    
   10: SW
   9:  RAZ!
   8:  RAZ!
   7:  B
   6:  RAO!
   5:  CP15BEN
   4:  RAO!
   3:  RAO!
   2:  C
   1:  A
   0:  M
}


-- B4.1.131
-- Secure Debug Enable Register, Security Extensions
register SDER :: word {
  31-0:  SDER_BITS
}


-- B4.1.132
-- TCM Type Register, VMSA
register TCMTR :: word {
  31-0:  TCMTR_BITS
}


-- B4.1.133
-- ThumbEE Configuration Register, VMSA
register TEECR :: word {
  31-0:  TEECR_BITS
}


-- B4.1.134
-- ThumbEE Handler Base Register, VMSA
register TEEHBR :: word {
  31-0:  TEEHBR_BITS
}


-- B4.1.135
-- TLBIALL, TLB Invalidate All, VMSA only


-- B4.1.136
-- TLBIALLH, TLB Invalidate All, Hyp mode, Virtualization Extensions



-- B4.1.137
-- TLBIALLHIS, TLB Invalidate All, Hyp mode, Inner Shareable, Virtualization Extensions


-- B4.1.138
-- TLBIALLIS, TLB Invalidate All, Inner Shareable, VMSA only



-- B4.1.139
-- TLBIALLNSNH, TLB Invalidate all Non-secure Non-Hyp, Virtualization Extensions


-- B4.1.140
-- TLBIALLNSNHIS, TLB Invalidate all Non-secure Non-Hyp IS, Virtualization Extensions


-- B4.1.141
-- TLBIASID, TLB Invalidate by ASID, VMSA only

-- B4.1.142
-- TLBIASIDIS, TLB Invalidate by ASID, Inner Shareable, VMSA only

-- B4.1.143
-- TLBIMVA, TLB Invalidate by MVA, VMSA only

-- B4.1.144
-- TLBIMVAA, TLB Invalidate by MVA, all ASIDs, VMSA only

-- B4.1.145
-- TLBIMVAAIS, TLB Invalidate by MVA, all ASIDs, Inner Shareable, VMSA only

-- B4.1.146
-- TLBIMVAH, TLB Invalidate by MVA, Hyp mode, Virtualization Extensions


-- B4.1.147
-- TLBIMVAHIS, TLB Invalidate by MVA, Hyp mode, Inner Shareable, Virtualization Extensions

-- B4.1.148
-- TLBIMVAIS, TLB Invalidate by MVA, Inner Shareable, VMSA only


-- B4.1.149
-- TLB Type Register, VMSA
register TLBTR :: word {
  31-0:  TLBTR_BITS
}


-- B4.1.150
-- PL1 only Thread ID Register, VMSA
register TPIDRPRW :: word {
  31-0:  TPIDRPRW_BITS
}


-- B4.1.151
--  User Read-Only Thread ID Register, VMSA
register TPIDRURO :: word {
  31-0:  TPIDRURO_BITS
}


-- B4.1.152
-- User Read/Write Thread ID Register, VMSA
register TPIDRURW :: word {
  31-0:  TPIDRURW_BITS
}


-- B4.1.153
-- Translation Table Base Control Register, VMSA
register TTBCR :: word {
    31: EAE   
    30-6: UNK!
    5:    PD1
    4:    PD0
    3:    RAZ!
    2-0:  N 

}


-- B4.1.154
-- Translation Table Base Register 0, VMSA
register TTBR0 :: word {
  31-0:  TTBR0_BITS
}


-- B4.1.155
-- Translation Table Base Register 1, VMSA
register TTBR1 :: word {
  31-0:  TTBR1_BITS
}


-- B4.1.156
-- Vector Base Address Register, Security Extensions
register VBAR :: word {
  31-0:  VBAR_BITS
}


-- B4.1.157
-- Virtualization Multiprocessor ID Register, Virtualization Extensions
register VMPIDR :: word {
  31-0:  VMPIDR_BITS
}


-- B4.1.158
-- Virtualization Processor ID Register, Virtualization Extensions
register VPIDR :: word {
  31-0:  VPIDR_BITS
}

-- B4.1.159
-- Virtualization Translation Control Register, Virtualization Extensions
register VTCR :: word {
  31-0:  VTCR_BITS
}

-- B4.1.160
-- Virtualization Translation Table Base Register, Virtualization Extensions
register VTTBR :: word {
  31-0:  VTTBR_BITS
}

record CP15 {
   SCTLR  :: SCTLR
   HSCTLR :: HSCTLR
   SCR    :: SCR    -- VMSA only
   NSACR  :: NSACR  -- VMSA only
   VBAR   :: word   -- VMSA only
   MVBAR  :: word   -- VMSA only
   HSR    :: HSR    -- VMSA only
   HCR    :: HCR    -- VMSA only
   ----------------
   -------new------
   FCSEIDR :: FCSEIDR
   VSCTLR  :: VSCTLR
   TTBCR   :: TTBCR
   HTCR    :: HTCR
   HTTBR   :: HTTBR
   DACR    :: DACR
   TTBR0   :: TTBR0
   TTBR1   :: TTBR1
   DFSR    :: DFSR
   DFAR    :: DFAR
   HDFAR   :: HDFAR
   HPFAR   :: HPFAR
   PRRR    :: PRRR
   NMRR    :: NMRR
   CONTEXTIDR :: CONTEXTIDR
   HSTR   :: HSTR
}

declare CP15 :: CP15

------------------------
-- Mode/state operations
------------------------

int ProcessorID() = 0

bool IsExternalAbort() = UNKNOWN

bool IsSecure() =
   not HaveSecurityExt() or not CP15.SCR.NS or CPSR.M == 0b10110 -- Monitor mode

bool UnalignedSupport() =
{  v = ArchVersion();
   v >= 7 or (v == 6 and CP15.SCTLR.U)
}

bool BadMode (mode::bits(5)) =
   match mode
   { case '10000' => false              -- User mode
     case '10001' => false              -- FIQ mode
     case '10010' => false              -- IRQ mode
     case '10011' => false              -- Supervisor mode
     case '10110' => !HaveSecurityExt() -- Monitor mode
     case '10111' => false              -- Abort mode
     case '11010' => !HaveVirtExt()     -- Hyp mode
     case '11011' => false              -- Undefined mode
     case '11111' => false              -- System mode
     case _ => true
   }

bool CurrentModeIsNotUser() =
{  when BadMode (CPSR.M) do #UNPREDICTABLE("BadMode: " : [CPSR.M]);
   not CPSR.M == 0b10000
}

bool CurrentModeIsUserOrSystem() =
{  when BadMode (CPSR.M) do #UNPREDICTABLE("BadMode: " : [CPSR.M]);
   ( CPSR.M in set { 0b10000, 0b11111 } )
}

bool CurrentModeIsHyp() =
{  when BadMode (CPSR.M) do #UNPREDICTABLE("BadMode: " : [CPSR.M]);
   CPSR.M == 0b11010
}

bool IntegerZeroDivideTrappingEnabled() = CP15.SCTLR.DZ

component ISETSTATE :: bits(2)
{  value = [CPSR.J] : [CPSR.T]
   assign value =
   {  CPSR.J <- value<1>;
      CPSR.T <- value<0>
   }
}

construct InstrSet {
   InstrSet_ARM  InstrSet_Thumb  InstrSet_Jazelle  InstrSet_ThumbEE
}

construct Encoding {
   Encoding_Thumb  Encoding_Thumb2  Encoding_ARM
}

declare Encoding :: Encoding

InstrSet CurrentInstrSet() =
   match ISETSTATE
   { case '00' => InstrSet_ARM
     case '01' => InstrSet_Thumb
     case '10' => InstrSet_Jazelle
     case '11' => InstrSet_ThumbEE
   }

unit SelectInstrSet (iset::InstrSet) =
   match iset
   { case InstrSet_ARM =>
        if CurrentInstrSet() == InstrSet_ThumbEE then
           #UNPREDICTABLE("SelectInstrSet")
        else
           ISETSTATE <- 0b00
     case InstrSet_Thumb =>
        ISETSTATE <- 0b01
     case InstrSet_Jazelle =>
        ISETSTATE <- 0b10
     case InstrSet_ThumbEE =>
        ISETSTATE <- 0b11
   }

component ITSTATE :: byte
{  value = ( if HaveThumb2() then CPSR.IT else 0b00000000 )
   assign value = CPSR.IT <- value
}

unit ITAdvance() =
   when HaveThumb2() and Encoding != Encoding_ARM do
      if ITSTATE<2:0> == 0b000 then
         ITSTATE <- 0b00000000
      else
         ITSTATE<4:0> <- ITSTATE<4:0> << 1

bool InITBlock() = ITSTATE<3:0> != 0b0000
bool LastInITBlock() = ITSTATE<3:0> == 0b1000

bits(4) ThumbCondition () =
   if ITSTATE == 0b00000000 then
      0b1110
   else if CPSR.IT<3:0> != 0b0000 then
      CPSR.IT<7:4>
   else
      #UNPREDICTABLE("ThumbCondition")

bool BigEndian() = ( CPSR.E )

-- Exclusive monitor stubs - implementation defined

unit SetExclusiveMonitors (address::word, n::nat) = ()
bool ExclusiveMonitorsPass (address::word, n::nat) = UNKNOWN
unit ClearExclusiveLocal (id::int) = ()

-- Conditional instructions

declare CurrentCondition :: cond

cond CurrentCond() = CurrentCondition

bool ConditionPassed() =
{  cond = CurrentCond();

   -- Evaluate base condition
   result = match cond<3:1>
            {  case '000' => CPSR.Z                           -- EQ or NE
               case '001' => CPSR.C                           -- CS or CC
               case '010' => CPSR.N                           -- MI or PL
               case '011' => CPSR.V                           -- VS or VC
               case '100' => CPSR.C and not CPSR.Z            -- HI or LS
               case '101' => CPSR.N == CPSR.V                 -- GE or LT
               case '110' => CPSR.N == CPSR.V and not CPSR.Z  -- GT or LE
               case '111' => true                             -- AL
            };

   -- Condition flag values in the set '111x' indicate the instruction is
   -- always run.  Otherwise, invert condition if necessary.
   if cond<0> and cond != 0b1111 then
      not result
   else
      result
}

-----------------
-- PSR operations
-----------------

component SPSR :: PSR
{  value =
      if BadMode (CPSR.M) then
         #UNPREDICTABLE("SPSR: BadMode: " : [CPSR.M])
      else
         match CPSR.M
         { case '10001' => SPSR_fiq  -- FIQ mode
           case '10010' => SPSR_irq  -- IRQ mode
           case '10011' => SPSR_svc  -- Supervisor mode
           case '10110' => SPSR_mon  -- Monitor mode
           case '10111' => SPSR_abt  -- Abort mode
           case '11010' => SPSR_hyp  -- Hyp mode
           case '11011' => SPSR_und  -- Undefined mode
           case _ => #UNPREDICTABLE("SPSR")
         }
   assign value =
      if BadMode (CPSR.M) then
         #UNPREDICTABLE("SPSR: BadMode: " : [CPSR.M])
      else
         match CPSR.M
         { case '10001' => SPSR_fiq <- value  -- FIQ mode
           case '10010' => SPSR_irq <- value  -- IRQ mode
           case '10011' => SPSR_svc <- value  -- Supervisor mode
           case '10110' => SPSR_mon <- value  -- Monitor mode
           case '10111' => SPSR_abt <- value  -- Abort mode
           case '11010' => SPSR_hyp <- value  -- Hyp mode
           case '11011' => SPSR_und <- value  -- Undefined mode
           case _ => #UNPREDICTABLE("SPSR")
         }
}

unit CPSRWriteByInstr (value::word, bytemask::bits(4), is_excpt_return::bool) =
{  privileged = CurrentModeIsNotUser();
   nmfi = CP15.SCTLR.NMFI;

   when bytemask<3> do
   {  &CPSR<31:27> <- value<31:27>;    -- N, Z, C, V, Q flags
      when is_excpt_return do
         &CPSR<26:24> <- value<26:24>  -- IT<1:0>, J state bits
   };

   when bytemask<2> do
      -- bits <23:20> are reserved SBZP bits
      &CPSR<19:16> <- value<19:16>;    -- GE<3:0> flags

   when bytemask<1> do
   {  when is_excpt_return do
         &CPSR<15:10> <- value<15:10>; -- IT<7:2> state bits
      &CPSR<9> <- value<9>;            -- E bit is user-writable
      when privileged and (IsSecure() or CP15.SCR.AW) do
         &CPSR<8> <- value<8>          -- A interrupt mask
   };

   when bytemask<0> do
   {  when privileged do
         &CPSR<7> <- value<7>;         -- I interrupt mask
      when privileged and (not nmfi or not value<6>) and
           (IsSecure() or CP15.SCR.FW or HaveVirtExt()) do
         &CPSR<6> <- value<6>;         -- F interrupt mask
      when is_excpt_return do
         &CPSR<5> <- value<5>;         -- T state bit
      when privileged do
         if BadMode (value<4:0>) then
            #UNPREDICTABLE("CPSRWriteByInstr: BadMode: " : [value<4:0>])
         else 
         { -- Check for attempts to enter modes only permitted in Secure state
           -- from Non-secure state. These are Monitor mode ('10110'), and FIQ
           -- mode ('10001') if the Security Extensions have reserved it. The
           -- definition of UNPREDICTABLE does not permit the resulting
           -- behavior to be a security hole.
           when not IsSecure() and value<4:0> == 0b10110 do
              #UNPREDICTABLE("CPSRWriteByInstr");
           when not IsSecure() and value<4:0> == 0b10001 and CP15.NSACR.RFR do
              #UNPREDICTABLE("CPSRWriteByInstr");
           -- There is no Hyp mode ('11010') in Secure state, so that is
           -- UNPREDICTABLE
           when not CP15.SCR.NS and value<4:0> == 0b11010 do
              #UNPREDICTABLE("CPSRWriteByInstr");
           -- Cannot move into Hyp mode directly from a Non-secure PL1 mode
           when !IsSecure() and CPSR.M != 0b11010 and value<4:0> == 0b11010 do
              #UNPREDICTABLE("CPSRWriteByInstr");
           -- Cannot move out of Hyp mode with this function except on an
           -- exception return
           when CPSR.M == 0b11010 and value<4:0> != 0b11010 and
                !is_excpt_return do
              #UNPREDICTABLE("CPSRWriteByInstr");

           &CPSR<4:0> <- value<4:0>    -- M<4:0> mode bits
         }
   }
}

unit SPSRWriteByInstr (value::word, bytemask::bits(4)) =
{  when CurrentModeIsUserOrSystem() do #UNPREDICTABLE("SPSRWriteByInstr");

   when bytemask<3> do
      &SPSR<31:24> <- value<31:24>;  -- N, Z, C, V, Q flags, IT<1:0>,
                                     -- J state bits

   when bytemask<2> do
      -- bits <23:20> are reserved SBZP bits
      &SPSR<19:16> <- value<19:16>;  -- GE<3:0> flags

   when bytemask<1> do
      &SPSR<15:8> <- value<15:8>;    -- IT<7:2> state bits, E bit, A mask

   when bytemask<0> do
   {  &SPSR<7:5> <- value<7:5>;      -- I, F masks, T state bit
      if BadMode (value<4:0>) then   -- Mode bits
         #UNPREDICTABLE("SPSRWriteByInstr: BadMode: " : [value<4:0>])
      else
         &SPSR<4:0> <- value<4:0>
   }
}

-------------------------------------
-- General Purpose Registers (banked)
-------------------------------------

construct RName {
   RName_0usr   RName_1usr   RName_2usr   RName_3usr  RName_4usr   RName_5usr
   RName_6usr   RName_7usr   RName_8usr   RName_8fiq  RName_9usr   RName_9fiq
   RName_10usr  RName_10fiq  RName_11usr  RName_11fiq RName_12usr  RName_12fiq
   RName_SPusr  RName_SPfiq  RName_SPirq  RName_SPsvc
   RName_SPabt  RName_SPund  RName_SPmon  RName_SPhyp
   RName_LRusr  RName_LRfiq  RName_LRirq  RName_LRsvc
   RName_LRabt  RName_LRund  RName_LRmon
   RName_PC
}

declare REG :: RName -> word
declare ELR_hyp :: word

RName RBankSelect (mode::bits(5),
                   usr::RName, fiq::RName, irq::RName, svc::RName,
                   abt::RName, und::RName, mon::RName, hyp::RName) =
   if BadMode (mode) then
      #UNPREDICTABLE("RBankSelect: BadMode" : [mode])
   else
      match mode
      { case '10000' => usr  -- User mode
        case '10001' => fiq  -- FIQ mode
        case '10010' => irq  -- IRQ mode
        case '10011' => svc  -- Supervisor mode
        case '10110' => mon  -- Monitor mode
        case '10111' => abt  -- Abort mode
        case '11010' => hyp  -- Hyp mode
        case '11011' => und  -- Undefined mode
        case '11111' => usr  -- System mode uses User mode registers
      }

RName RfiqBankSelect (mode::bits(5), usr::RName, fiq::RName) =
   RBankSelect (mode, usr, fiq, usr, usr, usr, usr, usr, usr)

RName LookUpRName (n::reg, mode::bits(5)) =
   match n
   { case 0  => RName_0usr
     case 1  => RName_1usr
     case 2  => RName_2usr
     case 3  => RName_3usr
     case 4  => RName_4usr
     case 5  => RName_5usr
     case 6  => RName_6usr
     case 7  => RName_7usr
     case 8  => RfiqBankSelect (mode, RName_8usr, RName_8fiq)
     case 9  => RfiqBankSelect (mode, RName_9usr, RName_9fiq)
     case 10 => RfiqBankSelect (mode, RName_10usr, RName_10fiq)
     case 11 => RfiqBankSelect (mode, RName_11usr, RName_11fiq)
     case 12 => RfiqBankSelect (mode, RName_12usr, RName_12fiq)
     case 13 => RBankSelect (mode, RName_SPusr, RName_SPfiq, RName_SPirq,
                             RName_SPsvc, RName_SPabt, RName_SPund,
                             RName_SPmon, RName_SPhyp)
     case 14 => RBankSelect (mode, RName_LRusr, RName_LRfiq, RName_LRirq,
                             RName_LRsvc, RName_LRabt, RName_LRund,
                             RName_LRmon, RName_LRusr)
     case 15 => #ASSERT("LookUpRName: n >= 0 and n <= 14")
   }

component Rmode (n::reg, mode::bits(5)) :: word
{  value =
   {
      -- In Non-secure state, check for attempted use of Monitor mode
      -- ('10110'), or of FIQ mode ('10001') when the Security Extensions are
      -- reserving the FIQ registers. The definition of UNPREDICTABLE does not
      -- permit this to be a security hole.
      notSecure = not IsSecure();
      when notSecure and mode == 0b10110 do #UNPREDICTABLE("Rmode");
      when notSecure and mode == 0b10001 and
           CP15.NSACR.RFR do #UNPREDICTABLE("Rmode");
      REG(LookUpRName (n, mode))
   }
   assign value =
   {
      notSecure = not IsSecure();
      when notSecure and mode == 0b10110 do #UNPREDICTABLE("Rmode");
      when notSecure and mode == 0b10001
           and CP15.NSACR.RFR do #UNPREDICTABLE("Rmode");

     -- Writes of non word-aligned values to SP are only permitted in ARM state.
      when n == 13 and value<1:0> != 0 and CurrentInstrSet() != InstrSet_ARM do
         #UNPREDICTABLE("Rmode");

      REG(LookUpRName (n, mode)) <- value
   }
}

component R (n::reg) :: word
{  value =
      if n == 15 then
      {  offset = if CurrentInstrSet() == InstrSet_ARM then 8 else 4;
         REG(RName_PC) + offset
      }
      else
         Rmode(n, CPSR.M)
   assign value =
      -- n >= 0 and n <= 14 asserted in LookUpRName
      Rmode(n, CPSR.M) <- value
}

component SP :: word { value = R(13) assign value = R(13) <- value }
component LR :: word { value = R(14) assign value = R(14) <- value }
word PC = R(15)

unit BranchTo (address::word) = REG(RName_PC) <- address

word PCStoreValue() =
   -- This function returns the PC value. On architecture versions before
   -- ARMv7, it is permitted to instead return PC+4, provided it does so
   -- consistently. It is used only to describe ARM instructions, so it returns
   -- the address of the current instruction plus 8 (normally) or 12 (when the
   -- alternative is permitted).
   PC

unit BranchWritePC (address::word) =
   if CurrentInstrSet() == InstrSet_ARM then
   {  when ArchVersion() < 6 and address<1:0> != 0b00 do
         #UNPREDICTABLE("BranchWritePC");
      BranchTo (address<31:2> : '00')
   }
   else -- ARM reference has extra logic for Jazelle here
      BranchTo (address<31:1> : '0')

unit BXWritePC (address::word) =
   if CurrentInstrSet() == InstrSet_ThumbEE then
      if address<0> then
         BranchTo (address<31:1> : '0') -- Remain in ThumbEE state
      else
         #UNPREDICTABLE("BXWritePC")
   else
      if address<0> then
      {  SelectInstrSet(InstrSet_Thumb);
         BranchTo (address<31:1> : '0')
      }
      else if not address<1> then
      {  SelectInstrSet(InstrSet_ARM);
         BranchTo (address)
      }
      else -- address<1:0> == 0b10
         #UNPREDICTABLE("BXWritePC")

unit LoadWritePC (address::word) =
   if ArchVersion() >= 5 then
      BXWritePC (address)
   else
      BranchWritePC (address)

unit ALUWritePC (address::word) =
   if ArchVersion() >= 7 and CurrentInstrSet() == InstrSet_ARM then
      BXWritePC (address)
   else
      BranchWritePC (address)

nat ThisInstrLength() = if Encoding == Encoding_Thumb then 16 else 32

unit IncPC() =
   BranchTo (REG (RName_PC) + if ThisInstrLength() == 16 then 2 else 4)

--------------
-- Main Memory
--------------

--Memory data type definitions

-- Types of memory

construct MemType_t {
   MemType_Normal 
   MemType_Device 
   MemType_StronglyOrdered
}

-- Memory attributes descriptor
record MemoryAttributes
{
   MemType      :: MemType_t
   innerattrs		:: bits(2)     -- The possible encodings for each attributes field are as follows:
   outerattrs		:: bits(2)     -- '00' = Non-cacheable; '10' = Write-Through
                               -- '11' = Write-Back; '01' = RESERVED
   innerhints		:: bits(2)     -- the possible encodings for the hints are as follows
   outerhints		:: bits(2)     -- '00' = No-Allocate; '01' = Write-Allocate
   								             -- '10' = Read-Allocate; ;'11' = Read-Allocate and Write-Allocate
   innertransient   :: bool
   outertransient   :: bool
   shareable        :: bool
   outershareable   :: bool
}


-- Physical address type, with extra bits used by some VMSA features
record FullAddress {
   physicaladdress :: bits(32)   -- second stage translation and LDR format 
                                 -- are not supported for the time being
   --NS			         :: bits(1)  -- '0' = Secure, '1' = Non-secure (not supported)
}


-- Descriptor used to access the underlying memory array
record AddressDescriptor {
   memattrs  :: MemoryAttributes
   -- paddress	 :: FullAddress
   paddress	 :: bits(32)
}


-- Access permissions descriptor
record Permissions {
   ap   :: bits(3)
   xn	  :: bits(1)
   pxn  :: bits(1)
}

-- Memory Architecture
-- only VMSA is supported, exluding PMSA for now

--construct MemArch 
-- {
--   MemArch_VMSA 
--   MemArch_PMSA
-- }
--declare MemArch  :: MemArch
--MemArch MemorySystemArchitecture() = MemArch

-- Main memory

declare MEM :: bits(32) -> byte option

--bool list mem1 (address::bits(32)) = [MEM(address)]

bool list mem1 (address::bits(32)) = 
  match MEM(address)
  {
    case None => #UNPREDICTABLE("undefined memory")
    case Some (v) => return [v]

   }


-- Basic memory accesses
-- _Mem[] in the manual
-- the following function ignores the 
-- memory attributes of the address descriptors, the manual mentions that 
-- The attributes in memaddrdesc.memattrs are used by the memory system to determine caching and ordering behaviors 
-- as described in Memory types and attributes and the memory order model on page A3-125

component mem (memaddrdesc::AddressDescriptor, size::nat) :: bool list
{  value =
      match size
      { case 1 => (mem1(memaddrdesc.paddress  + 0))<7:0>
        case 2 => (mem1(memaddrdesc.paddress  + 1) : mem1(memaddrdesc.paddress  + 0))<15:0>
        case 4 => (mem1(memaddrdesc.paddress  + 3) : mem1(memaddrdesc.paddress  + 2) :
                   mem1(memaddrdesc.paddress  + 1) : mem1(memaddrdesc.paddress  + 0))<31:0>
        case 8 => (mem1(memaddrdesc.paddress  + 7) : mem1(memaddrdesc.paddress  + 6) :
                   mem1(memaddrdesc.paddress  + 5) : mem1(memaddrdesc.paddress  + 4) :
                   mem1(memaddrdesc.paddress  + 3) : mem1(memaddrdesc.paddress  + 2) :
                   mem1(memaddrdesc.paddress  + 1) : mem1(memaddrdesc.paddress  + 0))<63:0>
        case _ => #ASSERT("mem: size in {1, 2, 4, 8}")
      }
   assign value =
      match size
      { case 1 =>   MEM(memaddrdesc.paddress  + 0) <- Some ([value<7:0>])
        case 2 => { MEM(memaddrdesc.paddress  + 0) <- Some ([value<7:0>]);
                    MEM(memaddrdesc.paddress  + 1) <- Some ([value<15:8>])
                  }
        case 4 => { MEM(memaddrdesc.paddress  + 0) <- Some ([value<7:0>]);
                    MEM(memaddrdesc.paddress  + 1) <- Some ([value<15:8>]);
                    MEM(memaddrdesc.paddress  + 2) <- Some ([value<23:16>]);
                    MEM(memaddrdesc.paddress  + 3) <- Some ([value<31:24>])
                  }
        case 8 => { MEM(memaddrdesc.paddress  + 0) <- Some ([value<7:0>]);
                    MEM(memaddrdesc.paddress  + 1) <- Some ([value<15:8>]);
                    MEM(memaddrdesc.paddress  + 2) <- Some ([value<23:16>]);
                    MEM(memaddrdesc.paddress  + 3) <- Some ([value<31:24>]);
                    MEM(memaddrdesc.paddress  + 4) <- Some ([value<39:32>]);
                    MEM(memaddrdesc.paddress  + 5) <- Some ([value<47:40>]);
                    MEM(memaddrdesc.paddress  + 6) <- Some ([value<55:48>]);
                    MEM(memaddrdesc.paddress  + 7) <- Some ([value<63:56>])
                  }
        case _ => #ASSERT("mem: size in {1, 2, 4, 8}")
      }
}


bool list BigEndianReverse (value::bool list, n::nat) =
   match n
   { case 1 => value<7:0>
     case 2 => value<7:0> : value<15:8>
     case 4 => value<7:0> : value<15:8> : value<23:16> : value<31:24>
     case 8 => value<7:0> : value<15:8> : value<23:16> : value<31:24> :
               value<39:32> : value<47:40> : value<55:48> : value<63:56>
     case _ => #ASSERT("BigEndianReverse: n in {1, 2, 4, 8}")
   }

bits(N) Align (w::bits(N), n::nat) = [n * ([w] div n)]

bool Aligned (w::bits(N), n::nat) = w == Align (w, n)




-- TLBRecord
record TLBRecord 
{
	perms            :: Permissions 
	nG               :: bits(1)       -- '0' = Global, '1' = not Global
	domain 			     :: bits(4)
	-- contiguoushint   :: bool  
  level 			     :: int           -- generalises Section/Page to Table level
	blocksize 		   :: nat           -- describes size of memory translated in KBytes
	addrdesc 		     :: AddressDescriptor  -- mematrbts are inside
}


-- FCSETranslate() 
bits(32) FCSETranslate (va ::bits(32)) = 
       if va<31:25> == '0000000' then 
         return CP15.FCSEIDR.PID : va<24:0> else
         return va

-- not supported
bool TLBLookupCameFromCacheMaintenance() = false

-- not supported
-- Returns TRUE if the implementation includes 
-- the Large Physical Address Extension
bool HaveLPAE () = false

-- Data Abort types.
construct DAbort {
    DAbort_AccessFlag  DAbort_Alignment DAbort_Background  
    DAbort_Domain  DAbort_Permission  DAbort_Translation 
    DAbort_SyncExternal DAbort_SyncExternalonWalk DAbort_SyncParity 
    DAbort_SyncParityonWalk DAbort_AsyncParity DAbort_AsyncExternal 
    DAbort_DebugEvent DAbort_TLBConflict DAbort_Lockdown 
    DAbort_Coproc DAbort_ICacheMaint}


--EncodeLDFSR()
-- Function that gives the Long-descriptor FSR code for 
--different types of Data Abort
-- This function should not be called

bits(6) EncodeLDFSR( dabtype :: DAbort, level :: int) = 
{ 
  var result :: bits(6);
  match dabtype
  {
    case DAbort_AccessFlag => 
         {
          result<5:2> <- '0010';
          result<1:0> <- ([level]:: bits(4))<1:0>
          }
    case DAbort_Alignment =>
          result<5:0> <- '100001' 
    case DAbort_Permission =>
         {
          result<5:2> <- '0011';
          result<1:0> <- ([level]:: bits(4))<1:0>
           }
    case DAbort_Translation =>
         {
          result<5:2> <- '0001';
          result<1:0> <- ([level]:: bits(4))<1:0>
           } 
    case DAbort_SyncExternal =>
           result<5:0> <- '010000' 
    case DAbort_SyncExternalonWalk =>
         {
          result<5:2> <- '0101';
          result<1:0> <- ([level]:: bits(4))<1:0>
           } 
    case DAbort_SyncParity =>
          result<5:0> <- '011000' 
    case DAbort_SyncParityonWalk =>
         {
          result<5:2> <- '0111';
          result<1:0> <- ([level]:: bits(4))<1:0>
           } 
    case DAbort_AsyncParity =>
          result<5:0> <- '011001'
    case DAbort_AsyncExternal =>
         result<5:0> <- '010001'
    case DAbort_DebugEvent =>
         result<5:0> <- '100010'
    case DAbort_TLBConflict =>
         result<5:0> <- '110000' 
    case DAbort_Lockdown =>
         result<5:0> <- '110100'
    case DAbort_Coproc =>
         result<5:0> <- '111010'
    case _  =>
          result<5:0> <- UNKNOWN
    };
  return result
}


-- EncodeSDFSR()
-- Function that gives the Short-descriptor FSR code for different types of Data Abort

bits(5) EncodeSDFSR (dabtype :: DAbort, level :: int) =  
{
  var result :: bits(5);
  match dabtype
  {
    case DAbort_AccessFlag =>
           if level == 1 then 
            result<4:0> <- '00011'
           else
            result<4:0> <- '00110'
    case DAbort_Alignment =>
           result<4:0> <- '00001'
     case DAbort_Permission  => 
         {
           result<4:2> <- '011'; 
           result<0> <- true; 
           result<1> <- ([level]:: bits(4))<1>
          }
     case DAbort_Domain => 
         {
           result<4:2> <- '010'; 
           result<0> <- true; 
           result<1> <- ([level]:: bits(4))<1>
           }
     case DAbort_Translation => 
         {
           result<4:2> <- '001'; 
           result<0> <- true; 
           result<1> <- ([level]:: bits(4))<1>
          }
     case DAbort_SyncExternal => 
           result<4:0> <- '01000'
     case DAbort_SyncExternalonWalk => 
         {
           result<4:2> <- '011'; 
           result<0> <- false;
           result<1> <- ([level]:: bits(4))<1>
          }
      case DAbort_SyncParity => 
           result<4:0> <- '11001'
      case DAbort_SyncParityonWalk =>
        {  
           result<4:2> <- '111'; 
           result<0> <- false; 
           result<1> <- ([level]:: bits(4))<1>
         }
      case DAbort_AsyncParity => 
           result<4:0> <- '11000'
      case DAbort_AsyncExternal => 
           result<4:0> <- '10110'
      case DAbort_DebugEvent => 
           result<4:0> <- '00010'
      case DAbort_TLBConflict => 
           result<4:0> <- '10000'
      case DAbort_Lockdown => 
           result<4:0> <- '10100'
      case DAbort_Coproc => 
           result<4:0> <- '11010'
      case DAbort_ICacheMaint => 
           result<4:0> <- '00100'
      case _ =>
      result<4:0> <- UNKNOWN
   };
  return result
}

-- not supported
-- This function returns the extended syndrome information for a fault reported in the HSR.
bits(9) LSInstructionSyndrome() =  0`9
 

-- function from the original l3 specs
-- The WriteHSR() pseudocode function writes a syndrome value to the HSR

unit WriteHSR (ec::bits(6), HSRString::bits(25)) =
{  var HSRValue = 0;
   HSRValue<31:26> <- ec;

   -- HSR.IL not valid for Prefetch Aborts (0x20, 0x21) and Data Aborts (0x24,
   -- 0x25) for which the ISS information is not valid.
   when ec<5:3> != 0b100 or ec<2> and HSRString<24> do
      HSRValue<25> <- ThisInstrLength() == 32;

   -- Condition code valid for EC[5:4] nonzero
   if ec<5:4> == 0b00 and ec<3:0> != 0b0000 then
      if CurrentInstrSet() == InstrSet_ARM then
      {  -- in the ARM instruction set
         HSRValue<24> <- true;
         HSRValue<23:20> <- CurrentCond()
      }
      else
      {  HSRValue<24> <- UNKNOWN; -- IMPLEMENTATION_DEFINED
         when HSRValue<24> do
            if ConditionPassed() then
               HSRValue<23:20> <- if UNKNOWN then CurrentCond() else 0b1110
            else
               HSRValue<23:20> <- CurrentCond();
         HSRValue<19:0> <- HSRString<19:0>
      }
   else
      HSRValue<24:0> <- HSRString;

   CP15.&HSR <- HSRValue
}

-- function from the original l3 specs
unit EnterMonitorMode
       (new_spsr_value::PSR, new_lr_value::word, vect_offset::word) =
{  CPSR.M <- 0b10110;
   SPSR <- new_spsr_value;
   R(14) <- new_lr_value;
   CPSR.J <- false;
   CPSR.T <- CP15.SCTLR.TE;
   CPSR.E <- CP15.SCTLR.EE;
   CPSR.A <- true;
   CPSR.F <- true;
   CPSR.I <- true;
   CPSR.IT <- 0b00000000;
   BranchTo (CP15.MVBAR + vect_offset)
}

--  function from the original l3 specs
unit EnterHypMode
       (new_spsr_value::PSR, new_lr_value::word, vect_offset::word) =
{  CPSR.M <- 0b11010;
   SPSR <- new_spsr_value;
   R(14) <- new_lr_value;
   CPSR.J <- false;
   CPSR.T <- CP15.SCTLR.TE;
   CPSR.E <- CP15.SCTLR.EE;
   CPSR.A <- true;
   CPSR.F <- true;
   CPSR.I <- true;
   CPSR.IT <- 0b00000000;
   BranchTo (CP15.MVBAR + vect_offset)
}



---------------------
-- Exception handling
---------------------
--  function from the original l3 specs
word ExcVectorBase() =
   if CP15.SCTLR.V then -- Hivecs selected, base = 0xFFFF000
      0xFFFF000
   else if HaveSecurityExt() then
      CP15.VBAR
   else
      0x00000000

--  function from the original l3 specs
unit TakeDataAbortException() =
{  -- Determine return information. SPSR is to be the current CPSR, and LR is
   -- to be the current PC plus 4 for Thumb or 0 for ARM, to change the PC
   -- offsets of 4 or 8 respectively from the address of the current
   -- instruction into the required address of the current instruction plus 8.
   -- For an asynchronous abort, the PC and CPSR are considered to have already
   -- moved on to their values for the instruction following the instruction
   -- boundary at which the exception occurred.

   new_lr_value = if CPSR.T then PC+4 else PC;
   new_spsr_value = CPSR;
   vect_offset = 16;
   preferred_exceptn_return = new_lr_value - 8;

   -- Determine whether this is an external abort to be routed to Monitor mode.
   route_to_monitor = HaveSecurityExt() and CP15.SCR.EA and IsExternalAbort();

   -- Check whether to take exception to Hyp mode
   -- if in Hyp mode then stay in Hyp mode
   take_to_hyp = HaveVirtExt() and HaveSecurityExt() and CP15.SCR.NS and
                 CPSR.M == 0b11010;
   -- otherwise, check whether to take to Hyp mode through Hyp Trap vector
   route_to_hyp = false;
   -- if HCR.TGE == '1' and in a Non-secure PL1 mode, the effect is
   -- UNPREDICTABLE

   if route_to_monitor then
   {  -- Ensure Secure state if initially in Monitor ('10110') mode. This
      -- affects the Banked versions of various registers accessed later in the
      -- code.
      when CPSR.M == 0b10110 do CP15.SCR.NS <- false;
      EnterMonitorMode (new_spsr_value, new_lr_value, vect_offset)
   }
   else if take_to_hyp then
      -- Note that whatever called TakePrefetchAbortException() will have set
      -- the HSR
      EnterHypMode (new_spsr_value, preferred_exceptn_return, vect_offset)
   else if route_to_hyp then
      EnterHypMode (new_spsr_value, preferred_exceptn_return, 20)
   else
   {  -- Handle in Abort mode. Ensure Secure state if initially in Monitor
      -- mode. This affects the Banked versions of various registers accessed
      -- later in the code.
      when HaveSecurityExt() and CPSR.M == 0b10110 do CP15.SCR.NS <- false;
      CPSR.M <- 0b10111;

      -- Write return information to registers, and make further CPSR changes:
      -- IRQs disabled, other interrupts disabled if appropriate, IT state
      -- reset, instruction set and endianness to SCTLR-configured values.
      SPSR <- new_spsr_value;
      R(14) <- new_lr_value;
      CPSR.I <- true;
      when not HaveSecurityExt() or HaveVirtExt() or not CP15.SCR.NS or
           CP15.SCR.AW do
        CPSR.A <- true;
      CPSR.IT <- 0b00000000;
      CPSR.J <- false;  CPSR.T <- CP15.SCTLR.TE; -- TE=0: ARM, TE=1: Thumb
      CPSR.E <- CP15.SCTLR.EE; -- EE=0: little-endian, EE=1: big-endian

      BranchTo (ExcVectorBase() + vect_offset)
   }
}


-- DataAbort() from page B2-1302, section 2.4.10
-- Data Abort handling for Memory Management generated aborts
unit DataAbort (vaddress :: bits(32), ipaddress ::  bits(40), domain :: bits(4), level :: int, 
                iswrite :: bool, dabtype :: DAbort, taketohypmode :: bool, secondstageabort :: bool, 
                ipavalid :: bool, LDFSRformat :: bool, s2fs1walk :: bool) =
 { 
   if !taketohypmode then
    {
      CP15.&DFSR  <- UNKNOWN;
      CP15.&DFAR <- UNKNOWN;

      if !(dabtype in set {DAbort_AsyncParity, DAbort_AsyncExternal, DAbort_DebugEvent}) then
          CP15.&DFAR <- vaddress
      else 
         when dabtype == DAbort_DebugEvent do -- Watchpoint
                                              -- DFAR is updated only for synchronous watchpoints in v7.1 Debug. Otherwise 
                                              -- it is explicitly UNKNOWN.
            CP15.&DFAR <- UNKNOWN; --IMPLEMENTATION_DEFINED bits(32) UNKNOWN or vaddress;
     
      if LDFSRformat then -- new format
       {
         CP15.&DFSR<13> <- TLBLookupCameFromCacheMaintenance();
         if dabtype in set {DAbort_AsyncExternal,DAbort_SyncExternal} then
            CP15.&DFSR<12> <- UNKNOWN   --IMPLEMENTATION_DEFINED 
         else
            CP15.&DFSR<12> <- false;
         CP15.&DFSR<11> <- if iswrite then true else false; 
         CP15.&DFSR<10> <- UNKNOWN;
         CP15.&DFSR<9> <- true;
         CP15.&DFSR<8:6> <-UNKNOWN;
         CP15.&DFSR<5:0> <- EncodeLDFSR(dabtype, level)
        }
      else  --SDFSR
       {
         CP15.&DFSR<13> <- TLBLookupCameFromCacheMaintenance();
         if dabtype in set {DAbort_AsyncExternal,DAbort_SyncExternal} then
             CP15.&DFSR<12> <- UNKNOWN  --IMPLEMENTATION_DEFINED
         else
              CP15.&DFSR<12> <- false;
         CP15.&DFSR<11> <- if iswrite then true else false; 
         CP15.&DFSR<9> <- false;
         CP15.&DFSR<8> <- UNKNOWN;

         var domain_valid = ((dabtype == DAbort_Domain) or ((level == 2) and 
                        (dabtype in set {DAbort_Translation, DAbort_AccessFlag, 
                                     DAbort_SyncExternalonWalk, DAbort_SyncParityonWalk} )) or 
                          (!HaveLPAE() and (dabtype == DAbort_Permission)));
         if domain_valid then 
            CP15.&DFSR<7:4> <- domain
         else
            CP15.&DFSR<7:4> <- UNKNOWN;
         CP15.&DFSR<10> <- EncodeSDFSR(dabtype, level)<4>;
         CP15.&DFSR<3:0> <- EncodeSDFSR(dabtype, level)<3:0> 
       }
    } 
   else   -- taketohypmode (should not be executed in our case)
    {
      var  HSRString :: bits(25);
      HSRString <- 0`25; 
      var ec :: bits(6);
      CP15.&HDFAR <- vaddress;
      when ipavalid do
         CP15.&HPFAR<31:4> <- ipaddress<39:12>; 
      if secondstageabort then
       {
         ec <- '100100';
         HSRString<24:16> <- LSInstructionSyndrome()
         }
      else
       {
        ec <- '100101';
        HSRString<24> <- false
        };  -- Instruction syndrome not valid 
      if dabtype in set {DAbort_AsyncExternal,DAbort_SyncExternal} then
        HSRString<9> <- UNKNOWN -- IMPLEMENTATION_DEFINED 
      else
        HSRString<9> <- false;
    
      HSRString<8> <- TLBLookupCameFromCacheMaintenance();
      HSRString<7> <- if s2fs1walk then true else false;
      HSRString<6> <- if iswrite then true else false;
      HSRString<5:0> <- EncodeLDFSR(dabtype, level);
      WriteHSR(ec, HSRString)
      };

 TakeDataAbortException()  --an existing l3 function

}

--CheckPermission() -- for stage 1
--Function used for permission checking at stage 1 of the translation process for the: 
--VMSA Long-descriptor format 
--VMSA Short-descriptor format 
--PMSA format, (we are not suppoerting PMSA)

unit CheckPermission (perms :: Permissions, mva :: bits(32), level :: int, domain :: bits(4), iswrite :: bool, 
                      ispriv :: bool, taketohypmode :: bool, LDFSRformat :: bool) =
 {
  -- variable for the DataAbort function with fixed values
--  var secondstageabort = false; 
--  var ipavalid = false; 
--  var s2fs1walk = false;
--  var ipa :: bits(40);
--  ipa <- UNKNOWN;
--  var abort :: bool;
  var ap_perms = perms.ap;
  when CP15.VSCTLR.AFE do ap_perms<0> <- true;
  match ap_perms
  {
   case '000' => #MMU_Exception ("permission fault")
   case '001' => if !ispriv then #MMU_Exception ("permission fault") else nothing
   case '010' => if (!ispriv and iswrite) then #MMU_Exception ("permission fault") else nothing
   case '011' => nothing
   case '100' => #UNPREDICTABLE("access fault")
   case '101' => if (!ispriv or iswrite) then #MMU_Exception ("permission fault") else nothing
   case '110' => if iswrite then #MMU_Exception ("permission fault") else nothing
   case '111' => if iswrite then #MMU_Exception ("permission fault") else nothing
  }
 -- when abort do #MMU_Exception ("permission fault")
 }



-- CheckDomain()
bool CheckDomain(domain :: bits(4), mva :: bits(32),  level :: int,  iswrite :: bool) =

-- variables used for dataabort function 
--  var ipaddress :: bits (40);
--  ipaddress <-  UNKNOWN; 
--  var taketohypmode = false;
--  var secondstageabort = false; 
--  var ipavalid = false;
--  var LDFSRformat = false; 
--  var s2fs1walk = false;
--  var permissioncheck :: bool;

--  var bitpos = 2 * ([domain] :: nat);
  match CP15.&DACR<(2 * ([domain] :: nat))+1:(2 * ([domain] :: nat))>  
   {
    --case '00' => DataAbort(mva, ipaddress, domain, level, iswrite, DAbort_Domain, 
    --                       taketohypmode, secondstageabort, ipavalid, LDFSRformat, s2fs1walk)
	
	case '00' => #MMU_Exception "DACR fail"
    case '01' => return (true) 
    case '10' => #UNPREDICTABLE "DACR fail"
    case '11' => return (false)
  }




-- should not be used
-- CheckPermissionS2()

unit CheckPermissionS2 (perms :: Permissions, mva ::  bits(32), ipa :: bits(40), 
                        level :: int, iswrite :: bool,  s2fs1walk :: bool) =
{
  var abort = (iswrite and !perms.ap<2>) or (!iswrite and !perms.ap<1>);
  when abort do
  {
    var domain :: bits(4);
    domain <- UNKNOWN;
    var taketohypmode = true;
    var secondstageabort = true;
    var ipavalid = s2fs1walk;
    var LDFSRformat = true;
	 #MMU_Exception "DAbort exception"
    --DataAbort(mva, ipa, domain, level, iswrite, DAbort_Permission,
    --          taketohypmode, secondstageabort, ipavalid, LDFSRformat, s2fs1walk)
    }
}


-- should not be used
-- CombineS1S2Desc() 

AddressDescriptor CombineS1S2Desc(s1desc :: AddressDescriptor, s2desc :: AddressDescriptor) =
{
  -- Combines the address descriptors from stage 1 and stage 2 
  var  result :: AddressDescriptor;
  
  result.paddress <- s2desc.paddress;

  -- default values:
  result.memattrs.innerattrs <- UNKNOWN;
  result.memattrs.outerattrs <- UNKNOWN; 
  result.memattrs.innerhints <- UNKNOWN; 
  result.memattrs.outerhints <- UNKNOWN;
  result.memattrs.shareable <- true; 
  result.memattrs.outershareable <- true;

  if s2desc.memattrs.MemType == MemType_StronglyOrdered or s1desc.memattrs.MemType == MemType_StronglyOrdered then
     result.memattrs.MemType <- MemType_StronglyOrdered

  else if s2desc.memattrs.MemType == MemType_Device or s1desc.memattrs.MemType == MemType_Device then
          result.memattrs.MemType <- MemType_Device
       else
          result.memattrs.MemType <- MemType_Normal;


  when result.memattrs.MemType == MemType_Normal do
   {
     if s2desc.memattrs.innerattrs == '01' or s1desc.memattrs.innerattrs == '01' then
          -- either encoding reserved
          result.memattrs.innerattrs <- UNKNOWN
     else if s2desc.memattrs.innerattrs == '00' or s1desc.memattrs.innerattrs == '00' then 
              -- either encoding Non-cacheable 
              result.memattrs.innerattrs <- '00'
          else if s2desc.memattrs.innerattrs == '10' or s1desc.memattrs.innerattrs == '10' then
                  -- either encoding Write-Through cacheable
                  result.memattrs.innerattrs <- '10'
               else
                 -- both encodings Write-Back 
                 result.memattrs.innerattrs <- '11';

     when s2desc.memattrs.outerattrs == '01' or  s1desc.memattrs.outerattrs == '01' do 
         -- either encoding reserved
         result.memattrs.outerattrs <- UNKNOWN;
    if s2desc.memattrs.outerattrs == '00' or s1desc.memattrs.outerattrs == '00' then
       -- either encoding Non-cacheable
       result.memattrs.outerattrs <- '00'
       else if s2desc.memattrs.outerattrs == '10' or s1desc.memattrs.outerattrs == '10' then 
            -- either encoding Write-Through cacheable 
            result.memattrs.outerattrs <- '10'
            else
              --both encodings Write-Back 
              result.memattrs.outerattrs <- '11'
      };

  result.memattrs.innerhints <- s1desc.memattrs.innerhints; 
  result.memattrs.outerhints <- s1desc.memattrs.outerhints;
  result.memattrs.shareable <- (s1desc.memattrs.shareable or s2desc.memattrs.shareable);
  result.memattrs.outershareable <- (s1desc.memattrs.outershareable or s2desc.memattrs.outershareable);
  when result.memattrs.MemType == MemType_Normal do 
   {
     when result.memattrs.innerattrs == '00' and result.memattrs.outerattrs == '00' do
       { --something Non-cacheable at each level is Outer Shareable 
         result.memattrs.outershareable <- true; 
         result.memattrs.shareable <- true
        }
   };
  return result

}
						
bool IsBVZero (bv :: bits(n) ) = bv == (0`n)

-- ConvertAttrsHints
-- Converts the Short-descriptor attribute fields for Normal memory as used
-- in the TTBR and TEX fields to the orthogonal concepts of Attributes and Hints 

bits(4) ConvertAttrsHints (RGN :: bits(2) ) =
{
  var attributes :: bits(2);
  var hints ::  bits(2);
  if RGN == '00' then -- Non-cacheable 
    {
     attributes <- '00';
     hints <- '00'
   }
  else if RGN<0> then -- Write-Back 
        {
          attributes <- '11';
          hints <- 1`1 : [!RGN<1>]:: bits (1)
        }
       else
        {
          attributes <- '10'; -- Write-Through
           hints <- '10'
         };

  return hints : attributes
}



-- SecondStageTranslate()
--  This function is called from a stage 1 translation table walk when
--  the accesses generated from that requires a second stage of translation
--  this fuction should not be called in these specs

AddressDescriptor SecondStageTranslate (s1outaddrdesc :: AddressDescriptor, mva ::  bits(32) ) =
{
  var result :: AddressDescriptor; 
  var tlbrecordS2 :: TLBRecord;
  var s2ia;
  var is_write;
  var stage1;
  var s2fs1walk;
  var domain :: bits(4);
  var taketohypmode;
  var secondstageabort;
  var ipavalid;
  var LDFSRformat;

  if HaveVirtExt() and !IsSecure() and !CurrentModeIsHyp() then 
  {
    when CP15.HCR.VM  do  -- second stage enabled
     {
      s2ia <- s1outaddrdesc.paddress ; 
      is_write <- false;
      stage1 <- false;
      s2fs1walk <- true;
      tlbrecordS2 <- tlbrecordS2  -- TranslationTableWalkLD(s2ia, mva, is_write, stage1, s2fs1walk)
     };
    -- s2ia is inconsistent with the manual for the time being
    CheckPermissionS2 (tlbrecordS2.perms, mva, 0`8: s2ia, tlbrecordS2.level, is_write, s2fs1walk);
    when CP15.HCR.PTW  do
     {
      -- protected table walk
      when tlbrecordS2.addrdesc.memattrs.MemType != MemType_Normal do
        {
         domain <- UNKNOWN;
         taketohypmode <- true;
         secondstageabort <- true;
         ipavalid <- true;
         LDFSRformat <- true;
         s2fs1walk <- true;
         -- s2ia is inconsistent with the manual for the time being
		 #MMU_Exception "DAbort exception"
         --DataAbort (mva, 0`8:s2ia, domain, tlbrecordS2.level, is_write, DAbort_Permission, taketohypmode,
          --           secondstageabort, ipavalid, LDFSRformat, s2fs1walk)
          }
        }; 
    result <- CombineS1S2Desc(s1outaddrdesc, tlbrecordS2.addrdesc)
   }
  else
   result <- s1outaddrdesc;

  return result
}

-- should not be used
bool RemapRegsHaveResetValues() = false


-- DefaultTEXDecode()
MemoryAttributes DefaultTEXDecode (texcb :: bits(5), S :: bits(1) ) = 
 {
  var memattrs :: MemoryAttributes;
  
  match texcb 
  {
    case  '00000' => -- Strongly-ordered
      {
        memattrs.MemType    <- MemType_StronglyOrdered;
        memattrs.innerattrs <- UNKNOWN;
        memattrs.innerhints <- UNKNOWN; 
        memattrs.outerattrs <- UNKNOWN;
        memattrs.outerhints <- UNKNOWN;
        memattrs.shareable  <- true
       }
    case '00001' =>  -- Shareable Device 
      {
        memattrs.MemType    <- MemType_Device; 
        memattrs.innerattrs <- UNKNOWN; 
        memattrs.innerhints <- UNKNOWN; 
        memattrs.outerattrs <- UNKNOWN; 
        memattrs.outerhints <- UNKNOWN; 
        memattrs.shareable  <- true
       }
    case '00010' => -- Outer and Inner Write-Through, no Write-Allocate 
      {
        memattrs.MemType    <- MemType_Normal;
        memattrs.innerattrs <- '10';
        memattrs.innerhints <- '10';
        memattrs.outerattrs <- '10'; 
        memattrs.outerhints <- '10'; 
        memattrs.shareable  <- [S]:: bool
       }
    case '00011' => -- Outer and Inner Write-Back, no Write-Allocate
      {
        memattrs.MemType    <- MemType_Normal;
        memattrs.innerattrs <- '11';
        memattrs.innerhints <- '10';
        memattrs.outerattrs <- '11'; 
        memattrs.outerhints <- '10'; 
        memattrs.shareable  <- [S] :: bool
       }
    case '00100' => -- Outer and Inner Non-cacheable
      {
        memattrs.MemType    <- MemType_Normal;
        memattrs.innerattrs <- '00';
        memattrs.innerhints <- '00';
        memattrs.outerattrs <- '00'; 
        memattrs.outerhints <- '00'; 
        memattrs.shareable  <- [S]:: bool
       }
    case '00110' => -- IMPLEMENTATION_DEFINED setting of memattrs
      {
        memattrs.MemType    <- UNKNOWN;
        memattrs.innerattrs <- UNKNOWN;
        memattrs.innerhints <- UNKNOWN;
        memattrs.outerattrs <- UNKNOWN; 
        memattrs.outerhints <- UNKNOWN; 
        memattrs.shareable  <- UNKNOWN
       }
    case '00111' => -- Outer and Inner Write-Back, Write-Allocate
      {
        memattrs.MemType    <- MemType_Normal;
        memattrs.innerattrs <- '11';
        memattrs.innerhints <- '11';
        memattrs.outerattrs <- '11'; 
        memattrs.outerhints <- '11'; 
        memattrs.shareable  <- [S]:: bool
       }
    case '01000' => -- Non-shareable Device
      {
        memattrs.MemType    <- MemType_Device;
        memattrs.innerattrs <- UNKNOWN;
        memattrs.innerhints <- UNKNOWN;
        memattrs.outerattrs <- UNKNOWN; 
        memattrs.outerhints <- UNKNOWN; 
        memattrs.shareable  <- true
       }

    case '10000' => -- Cacheable, <3:2> = Outer attrs, <1:0> = Inner attrs 
      {
        memattrs.MemType    <- MemType_Normal;
        var hintsattrs      = ConvertAttrsHints(texcb<1:0>);
        memattrs.innerattrs <- hintsattrs<1:0>;
        memattrs.innerhints <- hintsattrs<3:2>; 
        hintsattrs          <- ConvertAttrsHints(texcb<3:2>); 
        memattrs.outerattrs <- hintsattrs<1:0>; 
        memattrs.outerhints <- hintsattrs<3:2>
       }
    case '10001' => -- Cacheable, <3:2> = Outer attrs, <1:0> = Inner attrs 
      {
        memattrs.MemType    <- MemType_Normal;
        var hintsattrs      = ConvertAttrsHints(texcb<1:0>);
        memattrs.innerattrs <- hintsattrs<1:0>;
        memattrs.innerhints <- hintsattrs<3:2>; 
        hintsattrs          <- ConvertAttrsHints(texcb<3:2>); 
        memattrs.outerattrs <- hintsattrs<1:0>; 
        memattrs.outerhints <- hintsattrs<3:2>
       }
    case '10010' => -- Cacheable, <3:2> = Outer attrs, <1:0> = Inner attrs 
      {
        memattrs.MemType    <- MemType_Normal;
        var hintsattrs      = ConvertAttrsHints(texcb<1:0>);
        memattrs.innerattrs <- hintsattrs<1:0>;
        memattrs.innerhints <- hintsattrs<3:2>; 
        hintsattrs          <- ConvertAttrsHints(texcb<3:2>); 
        memattrs.outerattrs <- hintsattrs<1:0>; 
        memattrs.outerhints <- hintsattrs<3:2>
       }
    case '10011' => -- Cacheable, <3:2> = Outer attrs, <1:0> = Inner attrs 
      {
        memattrs.MemType    <- MemType_Normal;
        var hintsattrs      = ConvertAttrsHints(texcb<1:0>);
        memattrs.innerattrs <- hintsattrs<1:0>;
        memattrs.innerhints <- hintsattrs<3:2>; 
        hintsattrs          <- ConvertAttrsHints(texcb<3:2>); 
        memattrs.outerattrs <- hintsattrs<1:0>; 
        memattrs.outerhints <- hintsattrs<3:2>
       }
    case '10100' => -- Cacheable, <3:2> = Outer attrs, <1:0> = Inner attrs 
      {
        memattrs.MemType    <- MemType_Normal;
        var hintsattrs      = ConvertAttrsHints(texcb<1:0>);
        memattrs.innerattrs <- hintsattrs<1:0>;
        memattrs.innerhints <- hintsattrs<3:2>; 
        hintsattrs          <- ConvertAttrsHints(texcb<3:2>); 
        memattrs.outerattrs <- hintsattrs<1:0>; 
        memattrs.outerhints <- hintsattrs<3:2>
       }
    case '10101' => -- Cacheable, <3:2> = Outer attrs, <1:0> = Inner attrs 
      {
        memattrs.MemType    <- MemType_Normal;
        var hintsattrs      = ConvertAttrsHints(texcb<1:0>);
        memattrs.innerattrs <- hintsattrs<1:0>;
        memattrs.innerhints <- hintsattrs<3:2>; 
        hintsattrs          <- ConvertAttrsHints(texcb<3:2>); 
        memattrs.outerattrs <- hintsattrs<1:0>; 
        memattrs.outerhints <- hintsattrs<3:2>
       }
    case '10110' => -- Cacheable, <3:2> = Outer attrs, <1:0> = Inner attrs 
      {
        memattrs.MemType    <- MemType_Normal;
        var hintsattrs      = ConvertAttrsHints(texcb<1:0>);
        memattrs.innerattrs <- hintsattrs<1:0>;
        memattrs.innerhints <- hintsattrs<3:2>; 
        hintsattrs          <- ConvertAttrsHints(texcb<3:2>); 
        memattrs.outerattrs <- hintsattrs<1:0>; 
        memattrs.outerhints <- hintsattrs<3:2>
       }
    case '10111' => -- Cacheable, <3:2> = Outer attrs, <1:0> = Inner attrs 
      {
        memattrs.MemType    <- MemType_Normal;
        var hintsattrs      = ConvertAttrsHints(texcb<1:0>);
        memattrs.innerattrs <- hintsattrs<1:0>;
        memattrs.innerhints <- hintsattrs<3:2>; 
        hintsattrs          <- ConvertAttrsHints(texcb<3:2>); 
        memattrs.outerattrs <- hintsattrs<1:0>; 
        memattrs.outerhints <- hintsattrs<3:2>
       }
    case '11000' => -- Cacheable, <3:2> = Outer attrs, <1:0> = Inner attrs 
      {
        memattrs.MemType    <- MemType_Normal;
        var hintsattrs      = ConvertAttrsHints(texcb<1:0>);
        memattrs.innerattrs <- hintsattrs<1:0>;
        memattrs.innerhints <- hintsattrs<3:2>; 
        hintsattrs          <- ConvertAttrsHints(texcb<3:2>); 
        memattrs.outerattrs <- hintsattrs<1:0>; 
        memattrs.outerhints <- hintsattrs<3:2>
       }
    case '11001' => -- Cacheable, <3:2> = Outer attrs, <1:0> = Inner attrs 
      {
        memattrs.MemType    <- MemType_Normal;
        var hintsattrs      = ConvertAttrsHints(texcb<1:0>);
        memattrs.innerattrs <- hintsattrs<1:0>;
        memattrs.innerhints <- hintsattrs<3:2>; 
        hintsattrs          <- ConvertAttrsHints(texcb<3:2>); 
        memattrs.outerattrs <- hintsattrs<1:0>; 
        memattrs.outerhints <- hintsattrs<3:2>
       }
    case '11010' => -- Cacheable, <3:2> = Outer attrs, <1:0> = Inner attrs 
      {
        memattrs.MemType    <- MemType_Normal;
        var hintsattrs      = ConvertAttrsHints(texcb<1:0>);
        memattrs.innerattrs <- hintsattrs<1:0>;
        memattrs.innerhints <- hintsattrs<3:2>; 
        hintsattrs          <- ConvertAttrsHints(texcb<3:2>); 
        memattrs.outerattrs <- hintsattrs<1:0>; 
        memattrs.outerhints <- hintsattrs<3:2>
       }
    case '11011' => -- Cacheable, <3:2> = Outer attrs, <1:0> = Inner attrs 
      {
        memattrs.MemType    <- MemType_Normal;
        var hintsattrs      = ConvertAttrsHints(texcb<1:0>);
        memattrs.innerattrs <- hintsattrs<1:0>;
        memattrs.innerhints <- hintsattrs<3:2>; 
        hintsattrs          <- ConvertAttrsHints(texcb<3:2>); 
        memattrs.outerattrs <- hintsattrs<1:0>; 
        memattrs.outerhints <- hintsattrs<3:2>
       }
    case '11100' => -- Cacheable, <3:2> = Outer attrs, <1:0> = Inner attrs 
      {
        memattrs.MemType    <- MemType_Normal;
        var hintsattrs      = ConvertAttrsHints(texcb<1:0>);
        memattrs.innerattrs <- hintsattrs<1:0>;
        memattrs.innerhints <- hintsattrs<3:2>; 
        hintsattrs          <- ConvertAttrsHints(texcb<3:2>); 
        memattrs.outerattrs <- hintsattrs<1:0>; 
        memattrs.outerhints <- hintsattrs<3:2>
       }
    case '11101' => -- Cacheable, <3:2> = Outer attrs, <1:0> = Inner attrs 
      {
        memattrs.MemType    <- MemType_Normal;
        var hintsattrs      = ConvertAttrsHints(texcb<1:0>);
        memattrs.innerattrs <- hintsattrs<1:0>;
        memattrs.innerhints <- hintsattrs<3:2>; 
        hintsattrs          <- ConvertAttrsHints(texcb<3:2>); 
        memattrs.outerattrs <- hintsattrs<1:0>; 
        memattrs.outerhints <- hintsattrs<3:2>
       }
    case '11110' => -- Cacheable, <3:2> = Outer attrs, <1:0> = Inner attrs 
      {
        memattrs.MemType    <- MemType_Normal;
        var hintsattrs      = ConvertAttrsHints(texcb<1:0>);
        memattrs.innerattrs <- hintsattrs<1:0>;
        memattrs.innerhints <- hintsattrs<3:2>; 
        hintsattrs          <- ConvertAttrsHints(texcb<3:2>); 
        memattrs.outerattrs <- hintsattrs<1:0>; 
        memattrs.outerhints <- hintsattrs<3:2>
       }
    case '11111' => -- Cacheable, <3:2> = Outer attrs, <1:0> = Inner attrs 
      {
        memattrs.MemType    <- MemType_Normal;
        var hintsattrs      = ConvertAttrsHints(texcb<1:0>);
        memattrs.innerattrs <- hintsattrs<1:0>;
        memattrs.innerhints <- hintsattrs<3:2>; 
        hintsattrs          <- ConvertAttrsHints(texcb<3:2>); 
        memattrs.outerattrs <- hintsattrs<1:0>; 
        memattrs.outerhints <- hintsattrs<3:2>
       }
    case _ => #UNPREDICTABLE ("UNPREDICTABLE")
  };
  memattrs.outershareable <- memattrs.shareable; 
  return memattrs
}


int UInt (w::bits(N)) = [[w]::nat]



-- original function
-- RemappedTEXDecode()
 MemoryAttributes RemappedTEXDecode (texcb :: bits(5), S :: bits(1) ) = 
  {
   var memattrs :: MemoryAttributes;
   var hintsattrs :: bits(4);
   var region = [(texcb<2:0>)] :: nat; -- texcb<4:3> are ignored in this mapping scheme 
   if region == 6 then
      memattrs <- UNKNOWN  --IMPLEMENTATION_DEFINED setting of memattrs; 
   else
    {
      match CP15.&PRRR<(2*region+1):2*region> 
       {
        case  '00' =>
         {
           memattrs.MemType    <- MemType_StronglyOrdered; 
           memattrs.innerattrs <- UNKNOWN;
           memattrs.outerattrs <- UNKNOWN; 
           memattrs.innerhints <- UNKNOWN; 
           memattrs.outerhints <- UNKNOWN; 
           memattrs.shareable  <- true; 
           memattrs.outershareable <- true
           }
        case '01' =>
         {
           memattrs.MemType    <- MemType_Device; 
           memattrs.innerattrs <- UNKNOWN;
           memattrs.outerattrs <- UNKNOWN;
           memattrs.innerhints <- UNKNOWN; 
           memattrs.outerhints <- UNKNOWN; 
           memattrs.shareable  <- true; 
           memattrs.outershareable <- true
            }
        case  '10' =>
         {
           memattrs.MemType <- MemType_Normal;
           var hintattrs = ConvertAttrsHints(CP15.&NMRR<(2*region+1):2*region>); 
           memattrs.innerattrs <- hintsattrs<1:0>;
           memattrs.innerhints <- hintsattrs<3:2>;
           hintattrs <- ConvertAttrsHints(CP15.&NMRR<(2*region+17):(2*region+16)>); 
           memattrs.outerattrs <- hintsattrs<1:0>;
           memattrs.outerhints <- hintsattrs<3:2>;
           var s_bit = if ([S]:: bool) then CP15.PRRR.NS0 else CP15.PRRR.NS1;
           memattrs.shareable <- s_bit;
           memattrs.outershareable <- s_bit and !(CP15.&PRRR<region+24>)
           }
        case '11' =>  -- reserved
        {
          memattrs.MemType        <- UNKNOWN; 
          memattrs.innerattrs     <- UNKNOWN; 
          memattrs.outerattrs     <- UNKNOWN; 
          memattrs.innerhints     <- UNKNOWN; 
          memattrs.outerhints     <- UNKNOWN; 
          memattrs.shareable      <- UNKNOWN;
          memattrs.outershareable <- UNKNOWN
           }
        }
     };
   return memattrs
 }

-- our version

--MemoryAttributes RemappedTEXDecode (texcb :: bits(5), S :: bits(1) ) = 
-- {
--  var memattrs :: MemoryAttributes;
--  var hintsattrs :: bits(4);
--  var region = [(texcb<2:0>)] :: nat; -- texcb<4:3> are ignored in this mapping scheme 
--  if region == 6 then
--        #MMU_Exception "Implementation_defined settings not supported" -- memattrs <- UNKNOWN  IMPLEMENTATION_DEFINED --setting of memattrs; 
--  else
--   {
--     match CP15.&PRRR<(2*region+1):2*region> 
--      {
--       case  '00' =>  #MMU_Exception "MemType_StronglyOrdered settings not supported"
        
--       case '01' => #MMU_Exception "MemType_Device settings not supported"
        
--       case  '10' =>
--        {
--          memattrs.MemType <- MemType_Normal;
--          var hintattrs = ConvertAttrsHints(CP15.&NMRR<(2*region+1):2*region>); 
--          memattrs.innerattrs <- hintsattrs<1:0>;
--          memattrs.innerhints <- hintsattrs<3:2>;
--          hintattrs <- ConvertAttrsHints(CP15.&NMRR<(2*region+17):(2*region+16)>); 
--          memattrs.outerattrs <- hintsattrs<1:0>;
--          memattrs.outerhints <- hintsattrs<3:2>;
--          var s_bit = if ([S]:: bool) then CP15.PRRR.NS0 else CP15.PRRR.NS1;
--          memattrs.shareable <- s_bit;
--          memattrs.outershareable <- s_bit and !(CP15.&PRRR<region+24>)
--          }
--       case '11' =>  #MMU_Exception "reserved settings not supported" -- reserved

--       }
--    };
--  return memattrs
--}



-- AlignmentFaultV() 
unit AlignmentFaultV (address :: bits(32), iswrite :: bool, taketohyp :: bool) =
 {
  -- parameters for calling DataAbort 
  var ipaddress :: bits(40);
  ipaddress <- UNKNOWN;
  var domain :: bits(4);
  domain <- UNKNOWN; 
  var level :: int;
  level <- UNKNOWN; 
  var secondstageabort = false;
  var ipavalid = false;
  var LDFSRformat = taketohyp or CP15.TTBCR.EAE;
  var s2fs1walk = false;

  var mva = FCSETranslate(address);
  DataAbort(mva, ipaddress, domain, level, iswrite, DAbort_Alignment, CurrentModeIsHyp(),
          secondstageabort, ipavalid, LDFSRformat, s2fs1walk)
}


AddressDescriptor * AddressDescriptor * bits(32)
      level1_desc_address_and_desc (n :: nat, ttbr :: bits(32), mva :: bits(32)) =
 {
  var l1descaddr;
  var l1descaddr2; -- to return
  var l1desc; -- to return
  var hintsattrs;  -- to return
 
  -- Obtain First level descriptor.
  if n==0 then  l1descaddr.paddress  <-  ttbr<31:(14-0)> : mva<(31-0):20> : '00'
  else if n == 1 then l1descaddr.paddress  <-  ttbr<31:(14-1)> : mva<(31-1):20> : '00'
  else if n == 2 then l1descaddr.paddress  <-  ttbr<31:(14-2)> : mva<(31-2):20> : '00'
  else if n == 3 then l1descaddr.paddress  <-  ttbr<31:(14-3)> : mva<(31-3):20> : '00'
  else if n == 4 then l1descaddr.paddress  <-  ttbr<31:(14-4)> : mva<(31-4):20> : '00'
  else if n == 5 then l1descaddr.paddress  <-  ttbr<31:(14-5)> : mva<(31-5):20> : '00'
  else if n == 6 then l1descaddr.paddress  <-  ttbr<31:(14-6)> : mva<(31-6):20> : '00'
  else l1descaddr.paddress  <-  ttbr<31:(14-7)> : mva<(31-7):20> : '00';
  --l1descaddr.paddress.NS              <- if IsSecure() then '0' else '1';
  l1descaddr.memattrs.MemType         <- MemType_Normal;
  l1descaddr.memattrs.shareable       <- ttbr<1> ;
  l1descaddr.memattrs.outershareable  <- !ttbr<5> and ttbr<1>;
  hintsattrs                          <-  ConvertAttrsHints(ttbr<4:3>);
  l1descaddr.memattrs.outerattrs      <- hintsattrs<1:0>;
  l1descaddr.memattrs.outerhints      <-  hintsattrs<3:2>;

  if HaveMPExt() then
  {
   hintsattrs <- ConvertAttrsHints([ttbr<0>]:: bits(1) : [ttbr<6>] :: bits(1));
   l1descaddr.memattrs.innerattrs <- hintsattrs<1:0>; 
   l1descaddr.memattrs.innerhints <- hintsattrs<3:2>
   }
  else
    {  
     if !ttbr<0> then
     {
      hintsattrs <- ConvertAttrsHints('00'); 
      l1descaddr.memattrs.innerattrs <- hintsattrs<1:0>; 
      l1descaddr.memattrs.innerhints <- hintsattrs<3:2>
       }
     else
     {
      l1descaddr.memattrs.innerattrs <- UNKNOWN;  --IMPLEMENTATION_DEFINED 10 or 11;
      l1descaddr.memattrs.innerhints <- UNKNOWN   --IMPLEMENTATION_DEFINED 01 or 11
       }
    };

  if !HaveVirtExt() or IsSecure() then
       l1descaddr2 <- l1descaddr 
  else   
      l1descaddr2 <- SecondStageTranslate(l1descaddr, mva);
  
  l1desc <- [mem(l1descaddr2, 4)] :: bits (32);
  when CP15.VSCTLR.EE  do  l1desc <- [BigEndianReverse(mem(l1descaddr2, 4), 4)] :: bits(32);

  return (l1descaddr, l1descaddr2, l1desc)
}



-- Determine correct Translation Table Base Register to use
nat * bool * bits(32)  translation_root (mva :: bits(32)) =
 { 
  if  ([CP15.TTBCR.N] :: nat) == 0 or (([CP15.TTBCR.N] :: nat) == 1 and IsBVZero([mva<31>] :: bits(1))) or 
     (([CP15.TTBCR.N] :: nat) == 2 and IsBVZero(mva<31:30>)) or (([CP15.TTBCR.N] :: nat) == 3 and IsBVZero(mva<31:29>)) or 
     (([CP15.TTBCR.N] :: nat) == 4 and IsBVZero(mva<31:28>)) or (([CP15.TTBCR.N] :: nat) == 5 and IsBVZero(mva<31:27>)) or 
     (([CP15.TTBCR.N] :: nat) == 6 and IsBVZero(mva<31:26>)) or (([CP15.TTBCR.N] :: nat) == 7 and IsBVZero(mva<31:25>))
  then
    return (([CP15.TTBCR.N] :: nat), CP15.TTBCR.PD0, CP15.&TTBR0)
    
  else
    return (0, CP15.TTBCR.PD1, CP15.&TTBR1)
}


-- Obtain Second level descriptor. 
AddressDescriptor * bits(32)
      level2_desc_address_and_desc (l1desc :: bits(32), mva :: bits(32), l1descaddr :: AddressDescriptor) =
 {
   var l2desc;
   var l2descaddr;	 

   l2descaddr.paddress  <-  l1desc<31:10> : mva<19:12> : 0 :: bits(2); 
   
   l2descaddr.memattrs <- l1descaddr.memattrs;
   
   
     l2descaddr2 = if !HaveVirtExt() or IsSecure() then
       -- if only 1 stage of translation 
       l2descaddr
     else
        SecondStageTranslate(l2descaddr, mva);
		
       -- this does not work (review?)
	   -- l2desc = if CP15.VSCTLR.EE then (BigEndianReverse(mem(l2descaddr2, 4),4)] :: bits(32))
   	   -- else ([mem(l2descaddr2, 4)] :: bits(32));
		
      l2desc <- [mem(l2descaddr2, 4)] :: bits(32); 
      when CP15.VSCTLR.EE do l2desc <- [BigEndianReverse(mem(l2descaddr2, 4),4)] :: bits(32);
     return ( l2descaddr2, l2desc )
}


unit writing_access_flag 
   (l2desc:: bits (32), l2descaddr2 :: AddressDescriptor, mva :: bits (32), IA :: bits (40), domain :: bits(4), level :: int, 
                iswrite :: bool, dabtype :: DAbort, taketohypmode :: bool, secondstageabort :: bool, 
                ipavalid :: bool, LDFSRformat :: bool, s2fs1walk :: bool) =
    when CP15.VSCTLR.AFE and !l2desc<4> do
           {   
            if !CP15.VSCTLR.HA  then
               #MMU_Exception "DAbort_AccessFlag exception"
               --DataAbort(mva, IA, domain, level, iswrite, dabtype, taketohypmode, 
                 --                secondstageabort, ipavalid, LDFSRformat, s2fs1walk)
            else -- Hardware-managed Access flag must be set in memory 
              if CP15.VSCTLR.EE  then  mem (l2descaddr2,4)<28> <- true
              else  mem(l2descaddr2,4)<4> <- true
             }



TLBRecord TLBResult (texcb :: bits (5), S:: bits(1), ap :: bits(3), xn :: bits(1), pxn :: bits(1), 
       nG :: bits (1), domain :: bits (4), level :: int, blocksize :: nat, size :: nat,
       physicaladdressi :: bits (32), mva :: bits (32)) = 
{
  var result;
 -- Decode the TEX, C, B and S bits to produce the TLBRecord's memory attributes 
  if !CP15.VSCTLR.TRE  then
       if RemapRegsHaveResetValues() then result.addrdesc.memattrs <- DefaultTEXDecode(texcb, S)
       else  result.addrdesc.memattrs <- UNKNOWN --IMPLEMENTATION_DEFINED setting of result.addrdesc.memattrs
  else
      if !CP15.VSCTLR.M  then result.addrdesc.memattrs <- DefaultTEXDecode(texcb, S) 
      else result.addrdesc.memattrs <- RemappedTEXDecode(texcb, S);

  --transient bits are not supported in this format 
  result.addrdesc.memattrs.innertransient <- false; 
  result.addrdesc.memattrs.outertransient <- false;
  -- Set the rest of the TLBRecord, try to add it to the TLB, and return it. 
  result.perms.ap <- ap;
  result.perms.xn <- xn;
  result.perms.pxn <- pxn;
  result.nG <- nG;
  result.domain <- domain;
  result.level <- level;
  result.blocksize <- blocksize;
  result.addrdesc.paddress <- physicaladdressi; 
  --result.addrdesc.paddress.NS <- if IsSecure() then NS else '1';

 -- check for alignment issues if memory type is SO or Device 
  when (result.addrdesc.memattrs.MemType == MemType_Device or result.addrdesc.memattrs.MemType == MemType_StronglyOrdered) do 
     when mva != Align(mva, size) do #MMU_Exception "Alignment Fault" ;

  return (result)
}

-- TranslationTableWalkSD()
-- Returns a result of a translation table walk using
-- the Short-descriptor format for TLBRecord
-- Implementations might cache information from memory in any
-- number of non-coherent TLB caching structures, and so avoid
-- memory accesses that have been expressed in this pseudocode
-- The use of such TLBs is not expressed in this pseudocode.

-- make it an option datatype for the ease of mutable vriables, this differs from the manual 

TLBRecord TranslationTableWalkSD (mva :: bits(32), is_write :: bool, size  :: nat) = 
{
 

  -- Determine correct Translation Table Base Register to use. 
   n, disabled, ttbr =  translation_root (mva);

  -- Check this Translation Table Base Register is not disabled. 
  when HaveSecurityExt() and disabled do  #MMU_Exception "root disabled";

  -- Obtain First level descriptor
  l1descaddr, l1descaddr2, l1desc =  level1_desc_address_and_desc (n, ttbr, mva);
  
 -- Process First level descriptor 
  match l1desc<1:0> 
   {
     case 0  =>    -- Fault, Reserved 
         {
          #MMU_Exception "invalid page directory entry"
          }
      case 1 => -- Large page or Small page  
         {
          domain = l1desc<8:5> ;
          level = 2;
          pxn = [l1desc<2>] :: bits(1);
          --NS <- [l1desc<3>] :: bits(1) ;
            
          -- Obtain Second level descriptor. 
          (l2descaddr2, l2desc)  = level2_desc_address_and_desc (l1desc, mva, l1descaddr);
         
 
          -- Process Second level descriptor. 
          when l2desc<1:0> == '00' do #MMU_Exception "invalid page directory entry";
           
          S   = [l2desc<10>] :: bits(1); 
          ap  = [l2desc<9>] :: bits(1) : [l2desc<5>] :: bits(1): [l2desc<4>] :: bits(1); 
          nG  = [l2desc<11>] :: bits(1);


          writing_access_flag (l2desc, l2descaddr2, mva, UNKNOWN, domain, level, is_write, DAbort_AccessFlag, false, 
                                 false, false, false, false );

            if !l2desc<1> then -- Large page 
             {
              texcb = l2desc<14:12> : [l2desc<3>] :: bits(1) : [l2desc<2>] :: bits(1);
              xn    = [l2desc<15>] :: bits(1);
              blocksize = 64;
              physicaladdressi = l2desc<31:16> : mva<15:0>;
			  return  (TLBResult (texcb, S, ap , xn , pxn , 
			                       nG , domain , level , blocksize , size,
			                       physicaladdressi , mva ))
              } 
            else -- Small page
             {
              texcb = l2desc<8:6> : [l2desc<3>] :: bits(1) : [l2desc<2>] :: bits(1);
              xn = [l2desc<0>]:: bits(1);
              blocksize = 4;
              physicaladdressi = l2desc<31:12> : mva<11:0>;
			  return  (TLBResult (texcb, S, ap , xn , pxn , 
			                       nG , domain , level , blocksize , size,
			                       physicaladdressi , mva ))
             }
         }
      case 2 => -- Section or Supersection 
       {
        texcb = l1desc<14:12> : [l1desc<3>] :: bits(1) : [l1desc<2>] :: bits(1);
        S  = [l1desc<16>] :: bits(1);
        ap = [l1desc<15>] :: bits(1) : l1desc<11:10>;
        xn = [l1desc<4>] :: bits(1); 
        pxn = [l1desc<0>] :: bits(1); 
        nG  = [l1desc<17>] :: bits(1); 
        level = 1;
        when CP15.VSCTLR.AFE  and !l1desc<10> do
         {   
          if !CP15.VSCTLR.HA  then
          #MMU_Exception "DAbort_AccessFlag exception"
          else -- Hardware-managed Access flag must be set in memory 
            if CP15.VSCTLR.EE  then  mem(l1descaddr2,4)<18> <- true  else  mem(l1descaddr2,4)<10> <- true
           };
         if !l1desc<18> then -- Section
          { 
           domain = l1desc<8:5>;
           blocksize = 1024; 
           physicaladdressi = l1desc<31:20> : mva<19:0>;
		  return (TLBResult (texcb, S, ap , xn , pxn , 
		                       nG , domain , level , blocksize , size,
		                       physicaladdressi , mva ))
           }
         else -- Supersection 
          { 
           domain = '0000';
           blocksize = 16384; 
           physicaladdressi = l1desc<31:24> : mva<23:0>;
		  return (TLBResult (texcb, S, ap , xn , pxn , 
		                       nG , domain , level , blocksize , size,
		                       physicaladdressi , mva ))
            }
         }
        case 3  =>    -- Fault, Reserved 
         {
          #MMU_Exception "reserved directory entry"
          }
       }
}



-- TranslateAddressVS1Off() 
-- Only called for data accesses. Does not define instruction fetch behavior. 

TLBRecord TranslateAddressVS1Off (va :: bits(32)) = 
  {
   var result :: TLBRecord;
   if !CP15.HCR.DC or IsSecure() or CurrentModeIsHyp() then 
    {
     result.addrdesc.memattrs.MemType    <- MemType_StronglyOrdered; 
     result.addrdesc.memattrs.innerattrs <- UNKNOWN; 
     result.addrdesc.memattrs.innerhints <- UNKNOWN; 
     result.addrdesc.memattrs.outerattrs <- UNKNOWN; 
     result.addrdesc.memattrs.outerhints <- UNKNOWN; 
     result.addrdesc.memattrs.shareable  <- true;
     result.addrdesc.memattrs.outershareable <- true
      }
  else
   {
     result.addrdesc.memattrs.MemType <- MemType_Normal; 
     result.addrdesc.memattrs.innerattrs <- '11'; 
     result.addrdesc.memattrs.innerhints <- '11'; 
     result.addrdesc.memattrs.outerattrs <- '11'; 
     result.addrdesc.memattrs.outerhints <- '11'; 
     result.addrdesc.memattrs.shareable <- false; 
     result.addrdesc.memattrs.outershareable <- false; 
     when CP15.HCR.VM != true do #UNPREDICTABLE("HCR.DC not true")
    };

  result.perms.ap <- UNKNOWN;
  result.perms.xn <- '0';
  result.perms.pxn <- '0';
  result.nG <- UNKNOWN;
  -- result.contiguoushint <- UNKNOWN;
  result.domain <- UNKNOWN;
  result.level <- UNKNOWN;
  result.blocksize <-  UNKNOWN; 
  result.addrdesc.paddress <- va; 
  --result.addrdesc.paddress.NS <- if IsSecure() then '0' else '1';
  return result
}



unit MMU_configuration () = 
{
   
  -- Architecture
  Architecture <- ARMv7_A;

  Extensions <- set {};

  -- though cortex-a9 support these 
  -- Extensions <- set {Extension_Security,  Extension_Multiprocessing, Extension_AdvanvedSIMD};
  -- Vector Floating-Point version  as well, but it's not complete in l3 model


  -- Fast Context Switch Extensions: in the Cortex-A9 processor, VA and MVA are identical 
  -- CP15.FCSEIDR.PID should be zero so that FCSETranslate ensures mva = va in  TranslateAddressV
  CP15.FCSEIDR.PID <- 0; 

  -- only user mode and system mode are supported, have to check about supervisor mode
  when CPSR.M notin set {0b10000, 0b11111} do
        #MMU_Exception "only user mode and system mode are supported";

  -- Hypervisor MMU is disbaled
  CP15.HSCTLR.M <- false;

  --VMSA MMU is enabled
  CP15.VSCTLR.M <- true;


  -- we will select TTBR0 as the root, therefore making CP15.TTBCR.N zero
  CP15.TTBCR.N <- 0`3;
  CP15.TTBCR.PD0 <- false; 

  -- making the translation table walk to inner non-cachable memory for the function level1_desc_address_and_desc
   CP15.&TTBR0<0> <- false;

  -- descriptors are in big endian, in level2_desc_address_and_desc
  CP15.VSCTLR.EE <- false;
  
  -- access flag is enable, in writing_access_flag
  CP15.VSCTLR.AFE <- true;

  -- to avoid RemapRegsHaveResetValues in TLBResult
  CP15.VSCTLR.TRE <- true

  -- we will be using only RemappedTEXDecode
  -- we should avoid region == 6, but it depends on the texcb which is coming from 
  -- the page table descriptors, therefore putting an exception there
  

  -- LPAE is optional in the v7-A architecture and is presently supported by the Cortex-A7, Cortex-A12, and Cortex-A15 processors
  --  CP15.TTBCR.EAE <- false
}




bool MMU_config_assert () = 
{
   
  -- Architecture
  Architecture == ARMv7_A and 

  -- though cortex-a9 support these 
  -- Extensions <- set {Extension_Security,  Extension_Multiprocessing, Extension_AdvanvedSIMD};
  -- Vector Floating-Point version  as well, but it's not complete in l3 model
  Extensions == set {} and

  -- Fast Context Switch Extensions: in the Cortex-A9 processor, VA and MVA are identical 
  -- CP15.FCSEIDR.PID should be zero so that FCSETranslate ensures mva = va in  TranslateAddressV
  CP15.FCSEIDR.PID == 0`7 and

  -- only user mode and system mode are supported, have to check about supervisor mode
  CPSR.M in set {0b10000, 0b11111} and

  -- Hypervisor MMU is disbaled
  !CP15.HSCTLR.M and

  --VMSA MMU is enabled
  CP15.VSCTLR.M and


  -- we will select TTBR0 as the root, therefore making CP15.TTBCR.N zero
  CP15.TTBCR.N == 0`3 and
  !CP15.TTBCR.PD0 and

  -- making the translation table walk to inner non-cachable memory for the function level1_desc_address_and_desc
   !CP15.&TTBR0<0> and

  -- descriptors are in big endian, in level2_desc_address_and_desc
  !CP15.VSCTLR.EE and
  
  -- access flag is enable, in writing_access_flag
  CP15.VSCTLR.AFE and

  -- to avoid RemapRegsHaveResetValues in TLBResult
  CP15.VSCTLR.TRE

  -- we will be using only RemappedTEXDecode
  -- we should avoid region == 6, but it depends on the texcb which is coming from 
  -- the page table descriptors, therefore putting an exception there
  

  -- LPAE is optional in the v7-A architecture and is presently supported by the Cortex-A7, Cortex-A12, and Cortex-A15 processors
  --  CP15.TTBCR.EAE <- false
}



-- this function does the address translation from page tables, we have to 
-- add TLB before that
-- TranslateAddressV() 
AddressDescriptor * TLBRecord 
      TranslateAddressV (va :: bits(32), ispriv :: bool, iswrite :: bool,  size :: nat) =
{
  --MMU_configuration () ; -- we should add this as an assertion instead
  --var mva         :: bits(32);
  --var ia_in       :: bits(40);
  --var result      :: AddressDescriptor;
  --var tlbrecordS1 :: TLBRecord;

  mva = FCSETranslate(va);

  -- FirstStageTranslation 
  --var ishyp = CurrentModeIsHyp();

  tlbrecordS1 = if (CurrentModeIsHyp() and CP15.HSCTLR.M) or (!CurrentModeIsHyp() and CP15.VSCTLR.M) 
                then TranslationTableWalkSD (mva, iswrite, size)
                else TranslateAddressVS1Off(mva);
	
	 when (CurrentModeIsHyp() and CP15.HSCTLR.M) or (!CurrentModeIsHyp() and CP15.VSCTLR.M) do
	    when CheckDomain(tlbrecordS1.domain, mva, tlbrecordS1.level, iswrite) do
            CheckPermission(tlbrecordS1.perms, mva, tlbrecordS1.level, tlbrecordS1.domain,iswrite, ispriv, CurrentModeIsHyp(), false); -- making usesLD false 
  

  -- we do not support second stage translation
  result = tlbrecordS1.addrdesc;
  return (result , tlbrecordS1)
 }

-- we are only supporting TranslateAddressV
-- TranslateAddress()
--AddressDescriptor (VA :: bits(32) , ispriv :: bool, iswrite :: bool, size :: nat) =
--   match MemorySystemArchitecture()
--    {
--      case MemArch_VMSA => return  Fst(TranslateAddressV(VA, ispriv, iswrite, size))
--      case MemArch_PMSA => #ASSERT ("PMSA not supported by these specs")
--     }



-- earlier this was only an exception with the address, now it is a function

-- AlignmentFault() 
-- This function calls the VMSA-specific functions to handle Alignment faults

unit AlignmentFault(address :: bits (32), iswrite :: bool) =  
              AlignmentFaultV(address, iswrite, CurrentModeIsHyp() or CP15.HCR.TGE)
 




