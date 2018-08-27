-----------------------------------------------------------------------
-- Formal Specification of the ARMv7-AR instruction set architecture --
-- Floating-point specification for VFPv4-D32                        --
-- (c) Anthony Fox, University of Cambridge                          --
-----------------------------------------------------------------------

-------------------------------------------------------------------------
-- NOTE: This specification is incomplete.
-- In particular, it does not attempt to properly model the behaviour
-- of exceptions and NaNs. Also skips fixed-point instructions.
-------------------------------------------------------------------------

type dreg  = bits(5)

construct VFPExtension {
   NoVFP
   VFPv2
   VFPv3
   VFPv4
}

declare VFPExtension :: VFPExtension

---------------------------------------------
-- Floating-point and Advanced SIMD registers
---------------------------------------------

-- Floating-point Status and Control Register (PMSA)

register FPSCR :: word {
   31:    N     -- Condition flag (Negative)
   30:    Z     -- Condition flag (Zero)
   29:    C     -- Condition flag (Carry)
   28:    V     -- Condition flag (oVerflow)
   27:    QC    -- Cumulative saturation bit, Advanced SIMD only
   26:    AHP   -- Alternative half-precision control bit
   25:    DN    -- Default NaN mode control bit
   24:    FZ    -- Flush-to-zero mode control bit
   23-22: RMode -- Rounding mode: 00 - RN, 01 - RP, 10 - RM, 11 - RZ
   21-20: RAZ!  -- previously Stride
   19:    RAZ!  -- Reserved
   18-16: RAZ!  -- previously Len
   15:    IDE   -- Input Denormal exception trap enable
   14-13: RAZ!  -- Reserved
   12:    IXE   -- Inexact exception trap enable
   11:    UFE   -- Underflow exception trap enable
   10:    OFE   -- Overflow exception trap enable
   9:     DZE   -- Division by Zero exception trap enable
   8:     IOE   -- Invalid Operation exception trap enable
   7:     IDC   -- Input Denormal cumulative exception bit
   6-5:   RAZ!  -- Reserved
   4:     IXC   -- Inexact cumulative exception bit
   3:     UFC   -- Underflow cumulative exception bit
   2:     OFC   -- Overflow cumulative exception bit
   1:     DZC   -- Division by Zero cumulative exception bit
   0:     IOC   -- Invalid Operation cumulative exception bit
}

record FP {
   REG :: dreg -> dword  -- 32 64-bit registers (D32)
                         -- Some processors will only have 16 registers
                         -- e.g. VFPv2, VFPv3-D16.
   FPSCR :: FPSCR
}

declare FP :: FP

--------------------
-- Helper Operations
--------------------

exception VFP_EXCEPTION :: string

ieee_rounding RoundingMode =
   match FP.FPSCR.RMode
   {
      case '00' => roundTiesToEven
      case '01' => roundTowardPositive
      case '10' => roundTowardNegative
      case '11' => roundTowardZero
   }

word FPAdd32 (op1::word, op2::word) = FP32_Add (RoundingMode, op1, op2)
word FPSub32 (op1::word, op2::word) = FP32_Sub (RoundingMode, op1, op2)
word FPMul32 (op1::word, op2::word) = FP32_Mul (RoundingMode, op1, op2)

dword FPAdd64 (op1::dword, op2::dword) = FP64_Add (RoundingMode, op1, op2)
dword FPSub64 (op1::dword, op2::dword) = FP64_Sub (RoundingMode, op1, op2)
dword FPMul64 (op1::dword, op2::dword) = FP64_Mul (RoundingMode, op1, op2)

word FPToFixed32 (operand::word, unsigned::bool, round_towards_zero::bool) =
{
  mode = if round_towards_zero then roundTowardZero else RoundingMode;
  match FP32_ToInt (mode, operand)
  {
    case Some (i) =>
      { result, overflow = SatQ (i, 32, unsigned);
        if overflow then
           -- L3 model does not cover VFP exceptions
           #VFP_EXCEPTION "FPToFixed32: overflow exception"
        else
           result
      }
    case None => #VFP_EXCEPTION "FPToFixed32: NaN or infinity"
  }
}

word FPToFixed64 (operand::dword, unsigned::bool, round_towards_zero::bool) =
{
  mode = if round_towards_zero then roundTowardZero else RoundingMode;
  match FP64_ToInt (mode, operand)
  {
    case Some (i) =>
      { result, overflow = SatQ (i, 32, unsigned);
        if overflow then
           -- L3 model does not cover VFP exceptions
           #VFP_EXCEPTION "FPToFixed64: overflow exception"
        else
           result
      }
    case None => #VFP_EXCEPTION "FPToFixed64: NaN or infinity"
  }
}

word FixedToFP32 (operand::word, unsigned::bool, round_to_nearest::bool) =
{
  mode = if round_to_nearest then roundTiesToEven else RoundingMode;
  int_operand = if unsigned then [[operand]::nat] else [operand];
  FP32_FromInt (mode, int_operand)
}

dword FixedToFP64 (operand::word, unsigned::bool, round_to_nearest::bool) =
{
  mode = if round_to_nearest then roundTiesToEven else RoundingMode;
  int_operand = if unsigned then [[operand]::nat] else [operand];
  FP64_FromInt (mode, int_operand)
}

component D (n::dreg) :: dword
{
  value = FP.REG (n)
  assign value = FP.REG (n) <- value
}

component S (n::dreg) :: word
{
  value = if n<0> then D(n div 2)<63:32> else D(n div 2)<31:0>
  assign value = if n<0> then
                    D(n div 2)<63:32> <- value
                 else
                    D(n div 2)<31:0> <- value
}

dword VFPExpandImm (imm8::byte, single::bool) =
   if single then
      ZeroExtend (imm8<7:7> : ~imm8<6:6> : imm8<6:6> ^ 5 : imm8<5:0> : '0' ^ 19)
   else
      imm8<7:7> : ~imm8<6:6> : imm8<6:6> ^ 8 : imm8<5:0> : '0' ^ 48

bits(4) FPCompare32 (op1::word, op2::word) =
   if FP32_IsNan (op1) or FP32_IsNan (op2) then
      '0011'
   else if FP32_Equal (op1, op2) then
      '0110'
   else if FP32_LessThan (op1, op2) then
      '1000'
   else
      '0010'

bits(4) FPCompare64 (op1::dword, op2::dword) =
   if FP64_IsNan (op1) or FP64_IsNan (op2) then
      '0011'
   else if FP64_Equal (op1, op2) then
      '0110'
   else if FP64_LessThan (op1, op2) then
      '1000'
   else
      '0010'

bits(32) FPZero32 (sign::bits(1)) = sign : 0`31
bits(64) FPZero64 (sign::bits(1)) = sign : 0`63

------------------------
-- Instruction Semantics
------------------------

-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- VMOV<c>.F64 <Dd>, #<imm>
-- VMOV<c>.F32 <Sd>, #<imm>
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~
define VFP > vmov_imm (single_register::bool, d::dreg, imm64::dword) =
{
   if single_register then
      S(d) <- imm64<31:0>
   else
      D(d) <- imm64;
   IncPC()
}

-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- VMOV<c>.F64 <Dd>, <Dm>
-- VMOV<c>.F32 <Sd>, <Sm>
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~
define VFP > vmov (single_register::bool, d::dreg, m::dreg) =
{
   if single_register then
      S(d) <- S(m)
   else
      D(d) <- D(m);
   IncPC()
}

-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- VMOV<c> <Sn>, <Rt>
-- VMOV<c> <Rt>, <Sn>
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~
define VFP > vmov_single (to_arm_register::bool, t::reg, n::dreg) =
{
   if to_arm_register then
      R(t) <- S(n)
   else
      S(n) <- R(t);
   IncPC()
}

-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- VMOV<c> <Sm>, <Sm1>, <Rt>, <Rt2>
-- VMOV<c> <Rt>, <Rt2>, <Sm>, <Sm1>
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
define VFP > vmov_two_singles
  (to_arm_registers::bool, t::reg, t2::reg, m::dreg) =
{
   if to_arm_registers then
   {
      R(t) <- S(m);
      R(t2) <- S(m+1)
   }
   else
   {
      S(m) <- R(t);
      S(m+1) <- R(t2)
   };
   IncPC()
}

-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- VMOV<c> <Dm>, <Rt>, <Rt2>
-- VMOV<c> <Rt>, <Rt2>, <Dm>
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
define VFP > vmov_double
  (to_arm_registers::bool, t::reg, t2::reg, m::dreg) =
{
   if to_arm_registers then
   {
      R(t) <- D(m)<31:0>;
      R(t2) <- D(m)<63:32>
   }
   else
   {
      D(m)<31:0> <- R(t);
      D(m)<63:32> <- R(t2)
   };
   IncPC()
}

-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- VABS<c>.F64 <Dd>, <Dm>
-- VABS<c>.F32 <Sd>, <Sm>
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~
define VFP > vabs (dp_operation::bool, d::dreg, m::dreg) =
{
   if dp_operation then
      D(d) <- FP64_Abs (D(m))
   else
      S(d) <- FP32_Abs (S(m));
   IncPC()
}

-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- VNEG<c>.F64 <Dd>, <Dm>
-- VNEG<c>.F32 <Sd>, <Sm>
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~
define VFP > vneg (dp_operation::bool, d::dreg, m::dreg) =
{
   if dp_operation then
      D(d) <- FP64_Neg (D(m))
   else
      S(d) <- FP32_Neg (S(m));
   IncPC()
}

-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- VSQRT<c>.F64 <Dd>, <Dm>
-- VSQRT<c>.F32 <Sd>, <Sm>
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~
define VFP > vsqrt (dp_operation::bool, d::dreg, m::dreg) =
{
   if dp_operation then
      D(d) <- FP64_Sqrt (RoundingMode, D(m))
   else
      S(d) <- FP32_Sqrt (RoundingMode, S(m));
   IncPC()
}

-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- VCVT<c>.F64.F32 <Dd>, <Sm>
-- VCVT<c>.F32.F64 <Sd>, <Dm>
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
define VFP > vcvt_float (double_to_single::bool, d::dreg, m::dreg) =
{
   if double_to_single then
      S(d) <- FP64_ToFP32 (RoundingMode, D(m))
   else
      D(d) <- FP32_ToFP64 (S(m));
   IncPC()
}

-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- VCVT{R}<c>.S32.F64 <Sd>, <Dm>
-- VCVT{R}<c>.S32.F32 <Sd>, <Sm>
-- VCVT{R}<c>.U32.F64 <Sd>, <Dm>
-- VCVT{R}<c>.U32.F32 <Sd>, <Sm>
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
define VFP > vcvt_to_integer
  (dp_operation::bool, unsigned::bool, round_zero::bool, d::dreg, m::dreg) =
{
   if dp_operation then
      S(d) <- FPToFixed64 (D(m), unsigned, round_zero)
   else
      S(d) <- FPToFixed32 (S(m), unsigned, round_zero);
   IncPC()
}

-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- VCVT<c>.F64.S32 <Dd>, <Sm>
-- VCVT<c>.F64.U32 <Dd>, <Sm>
-- VCVT<c>.F32.S32 <Sd>, <Sm>
-- VCVT<c>.F32.U32 <Sd>, <Sm>
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
define VFP > vcvt_from_integer
  (dp_operation::bool, unsigned::bool, d::dreg, m::dreg) =
{
   if dp_operation then
      D(d) <- FixedToFP64 (S(m), unsigned, false)
   else
      S(d) <- FixedToFP32 (S(m), unsigned, false);
   IncPC()
}

-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- VCMP{E}<c>.F64 <Dd>, <Dm>
-- VCMP{E}<c>.F64 <Dd>, #0.0
-- VCMP{E}<c>.F32 <Sd>, <Sm>
-- VCMP{E}<c>.F32 <Sd>, #0.0
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~
define VFP > vcmp (dp_operation::bool, d::dreg, m_with_zero::dreg option) =
{
   if dp_operation then
   {
      op2 = match m_with_zero
            {
               case Some (m) => D(m)
               case None => FPZero64 ('0')
            };
      FP.&FPSCR<31:28> <- FPCompare64 (D(d), op2)
   }
   else
   {
      op2 = match m_with_zero
            {
               case Some (m) => S(m)
               case None => FPZero32 ('0')
            };
      FP.&FPSCR<31:28> <- FPCompare32 (S(d), op2)
   };
   IncPC()
}

-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- VMSR<c> FPSCR, <Rt>
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~
define VFP > vmsr (t::reg) =
{
   FP.&FPSCR <- R(t);
   IncPC()
}

-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- VMRS<c> <Rt>, FPSCR
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~
define VFP > vmrs (t::reg) =
{
   if t != 15 then
      R(t) <- FP.&FPSCR
   else
   {
      CPSR.N <- FP.FPSCR.N;
      CPSR.Z <- FP.FPSCR.Z;
      CPSR.C <- FP.FPSCR.C;
      CPSR.V <- FP.FPSCR.V
   };
   IncPC()
}

-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- VADD<c>.F64 <Dd>, <Dn>, <Dm>
-- VADD<c>.F32 <Sd>, <Sn>, <Sm>
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~
define VFP > vadd (dp_operation::bool, d::dreg, n::dreg, m::dreg) =
{
   if dp_operation then
      D(d) <- FPAdd64 (D(n), D(m))
   else
      S(d) <- FPAdd32 (S(n), S(m));
   IncPC()
}

-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- VSUB<c>.F64 <Dd>, <Dn>, <Dm>
-- VSUB<c>.F32 <Sd>, <Sn>, <Sm>
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~
define VFP > vsub (dp_operation::bool, d::dreg, n::dreg, m::dreg) =
{
   if dp_operation then
      D(d) <- FPSub64 (D(n), D(m))
   else
      S(d) <- FPSub32 (S(n), S(m));
   IncPC()
}

-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- VMUL<c>.F64 <Dd>, <Dn>, <Dm>
-- VMUL<c>.F32 <Sd>, <Sn>, <Sm>
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~
define VFP > vmul (dp_operation::bool, d::dreg, n::dreg, m::dreg) =
{
   if dp_operation then
      D(d) <- FPMul64 (D(n), D(m))
   else
      S(d) <- FPMul32 (S(n), S(m));
   IncPC()
}

-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- VDIV<c>.F64 <Dd>, <Dn>, <Dm>
-- VDIV<c>.F32 <Sd>, <Sn>, <Sm>
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~
define VFP > vdiv (dp_operation::bool, d::dreg, n::dreg, m::dreg) =
{
   if dp_operation then
      D(d) <- FP64_Div (RoundingMode, D(n), D(m))
   else
      S(d) <- FP32_Div (RoundingMode, S(n), S(m));
   IncPC()
}

-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- VMLA<c>.F64 <Dd>, <Dn>, <Dm>
-- VMLA<c>.F32 <Sd>, <Sn>, <Sm>
-- VMLS<c>.F64 <Dd>, <Dn>, <Dm>
-- VMLS<c>.F32 <Sd>, <Sn>, <Sm>
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~
define VFP > vmla_vmls
   (dp_operation::bool, add::bool, d::dreg, n::dreg, m::dreg) =
{
   if dp_operation then
   {
      product = FPMul64 (D(n), D(m));
      addend = if add then product else FP64_Neg (product);
      D(d) <- FPAdd64 (D(n), addend)
   }
   else
   {
      product = FPMul32 (S(n), S(m));
      addend = if add then product else FP32_Neg (product);
      S(d) <- FPAdd32 (S(n), addend)
   };
   IncPC()
}

-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- VFMA<c>.F64 <Dd>, <Dn>, <Dm>
-- VFMA<c>.F32 <Sd>, <Sn>, <Sm>
-- VFMS<c>.F64 <Dd>, <Dn>, <Dm>
-- VFMS<c>.F32 <Sd>, <Sn>, <Sm>
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~
define VFP > vfma_vfms
   (dp_operation::bool, add::bool, d::dreg, n::dreg, m::dreg) =
{
   if dp_operation then
   {
      op64 = D(n);
      op64 = if add then op64 else FP64_Neg (op64);
      D(d) <- FP64_MulAdd (RoundingMode, op64, D(m), D(d))
   }
   else
   {
      op32 = S(n);
      op32 = if add then op32 else FP32_Neg (op32);
      S(d) <- FP32_MulAdd (RoundingMode, op32, S(m), S(d))
   };
   IncPC()
}

-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- VFNMA<c>.F64 <Dd>, <Dn>, <Dm>
-- VFNMA<c>.F32 <Sd>, <Sn>, <Sm>
-- VFNMS<c>.F64 <Dd>, <Dn>, <Dm>
-- VFNMS<c>.F32 <Sd>, <Sn>, <Sm>
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~
define VFP > vfnma_vfnms
   (dp_operation::bool, add::bool, d::dreg, n::dreg, m::dreg) =
{
   if dp_operation then
   {
      op64 = D(n);
      op64 = if add then op64 else FP64_Neg (op64);
      D(d) <- FP64_MulAdd (RoundingMode, op64, D(m), FP64_Neg (D(d)))
   }
   else
   {
      op32 = S(n);
      op32 = if add then op32 else FP32_Neg (op32);
      S(d) <- FP32_MulAdd (RoundingMode, op32, S(m), FP32_Neg (S(d)))
   };
   IncPC()
}

construct VFPNegMul {VFPNegMul_VNMLA, VFPNegMul_VNMLS, VFPNegMul_VNMUL}

-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- VNMUL<c>.F64 <Dd>, <Dn>, <Dm>
-- VNMUL<c>.F32 <Sd>, <Sn>, <Sm>
-- VNMLA<c>.F64 <Dd>, <Dn>, <Dm>
-- VNMLA<c>.F32 <Sd>, <Sn>, <Sm>
-- VNMLS<c>.F64 <Dd>, <Dn>, <Dm>
-- VNMLS<c>.F32 <Sd>, <Sn>, <Sm>
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
define VFP > vneg_mul
   (dp_operation::bool, typ::VFPNegMul, d::dreg, n::dreg, m::dreg) =
{
   if dp_operation then
   {
      product = FPMul64 (D(n), D(m));
      match typ
      {
         case VFPNegMul_VNMLA =>
            D(d) <- FPAdd64 (FP64_Neg (D(d)), FP64_Neg (product))
         case VFPNegMul_VNMLS => D(d) <- FPAdd64 (FP64_Neg (D(d)), product)
         case VFPNegMul_VNMUL => D(d) <- FP64_Neg (product)
      }
   }
   else
   {
      product = FPMul32 (S(n), S(m));
      match typ
      {
         case VFPNegMul_VNMLA =>
            S(d) <- FPAdd32 (FP32_Neg (S(d)), FP32_Neg (product))
         case VFPNegMul_VNMLS => S(d) <- FPAdd32 (FP32_Neg (S(d)), product)
         case VFPNegMul_VNMUL => S(d) <- FP32_Neg (product)
      }
   };
   IncPC()
}

-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- VLDR<c> <Dd>, [<Rn>{, #+/-<imm>}]
-- VLDR<c> <Sd>, [<Rn>{, #+/-<imm>}]
-- VLDR<c> <Dd>, <label>
-- VLDR<c> <Sd>, <label>
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
define VFP > vldr (single_reg::bool, add::bool, d::dreg, n::reg, imm32::word) =
{
   base = if n == 15 then Align(PC, 4) else R(n);
   address = if add then base + imm32 else base - imm32;
   if single_reg then
      S(d) <- MemA (address, 4)
   else
   {
      word1 = MemA (address, 4) :: word;
      word2 = MemA (address + 4, 4) :: word;
      D(d) <- if BigEndian() then word1:word2 else word2:word1
   };
   IncPC()
}

-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- VSTR<c> <Dd>, [<Rn>{, #+/-<imm>}]
-- VSTR<c> <Sd>, [<Rn>{, #+/-<imm>}]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
define VFP > vstr (single_reg::bool, add::bool, d::dreg, n::reg, imm32::word) =
{
   address = if add then R(n) + imm32 else R(n) - imm32;
   if single_reg then
      MemA (address, 4) <- S(d)
   else
   {
      word = D(d);
      MemA (address, 4) <- if BigEndian() then word<63:32> else word<31:0>;
      MemA (address + 4, 4) <- if BigEndian() then word<31:0> else word<63:32>
   };
   IncPC()
}

-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- VLDM{IA|DB}<c>{.<size>} <Rn>{!}, <list>
-- VPOP<c>{.<size>} <list>
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
define VFP > vldm
   (single_regs::bool, add::bool, wback::bool, d::dreg, n::reg, imm8::byte) =
{
   imm32 = ZeroExtend (imm8 : '00');
   regs = if single_regs then [imm8] else [imm8] div 0n2;
   var address = if add then R(n) else R(n) - imm32;
   for r in 0 .. regs - 1 do
      if single_regs then
      {
         S(d + [r]) <- MemA(address, 4);
         address <- address + 4
      }
      else
      {
         word1 = MemA(address, 4) :: word;
         word2 = MemA(address + 4, 4) :: word;
         address <- address + 8;
         D(d + [r]) <- if BigEndian() then word1 : word2 else word2 : word1
      };
   when wback do R(n) <- if add then R(n) + imm32 else R(n) - imm32;
   IncPC()
}

-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- VSTM{IA|DB}<c>{.<size>} <Rn>{!}, <list>
-- VPUSH<c>{.<size>} <list>
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
define VFP > vstm
   (single_regs::bool, add::bool, wback::bool, d::dreg, n::reg, imm8::byte) =
{
   imm32 = ZeroExtend (imm8 : '00');
   regs = if single_regs then [imm8] else [imm8] div 0n2;
   var address = if add then R(n) else R(n) - imm32;
   for r in 0 .. regs - 1 do
      if single_regs then
      {
         MemA(address, 4) <- S(d + [r]);
         address <- address + 4
      }
      else
      {
         d = D(d + [r]);
         MemA(address, 4) <- if BigEndian() then d<63:32> else d<31:0>;
         MemA(address + 4, 4) <- if BigEndian() then d<31:0> else d<63:32>;
         address <- address + 8
      };
   when wback do R(n) <- if add then R(n) + imm32 else R(n) - imm32;
   IncPC()
}
