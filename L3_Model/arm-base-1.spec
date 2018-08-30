-- Remaining from arm-base.spec --

component MemA_with_priv
            (address::word, size::nat, privileged::bool, data_ins :: bool) :: bits(N)
            with N in 8,16,32,64
{  value =
   {  
      var VA;
      -- Sort out aligment
      if address == Align (address, size) then
         VA <- address
      else if CP15.VSCTLR.A or CP15.VSCTLR.U then
         AlignmentFault(address, false)
      else -- if legacy non alignment-checking configuration
         VA <- Align (address, size);


	    -- MMU or MPU
	    memaddrdesc = TranslateAddress(VA, privileged, false, size, data_ins);

      -- Memory array access, and sort out endianness
      var value = mem(memaddrdesc, size);
      when CPSR.E do
         value <- BigEndianReverse (value, size);

      [value]
   }

   assign value =
   {
      var VA;

      -- Sort out aligment
      if address == Align (address, size) then
         VA <- address
      else if CP15.VSCTLR.A or CP15.VSCTLR.U then
         AlignmentFault(address, false)
           else -- if legacy non alignment-checking configuration
                VA <- Align (address, size);

	    -- MMU or MPU
	    memaddrdesc = TranslateAddress(VA, privileged, true, size, data_ins);
	  

    -- excluding for the time-being
	  -- Effect on exclusives
	  --when memaddrdesc.memattrs.shareable do
	  -- ClearExclusiveByAddress(memaddrdesc.physicaladdress, ProcessorID(), size);
	  
      -- Sort out endianness, then memory array access
      end_value = if CPSR.E then BigEndianReverse ([value], size) else [value];

      mem(memaddrdesc, size) <- end_value
   }
}




component MemA_unpriv (address::word, size::nat, data_ins :: bool) :: bits(N) with N in 8,16,32,64
{  value = MemA_with_priv (address, size, false, data_ins)
   assign value = MemA_with_priv (address, size, false, data_ins) <- value
}

component MemA (address::word, size::nat, data_ins :: bool) :: bits(N) with N in 8,16,32,64
{  value = MemA_with_priv (address, size, CurrentModeIsNotUser(), data_ins)
   assign value =
     MemA_with_priv (address, size, CurrentModeIsNotUser(), data_ins) <- value
}

component MemU_with_priv
             (address::word, size::nat, privileged::bool, data_ins :: bool) :: bits(N)
             with N in 8,16,32,64
{  value =
   {  -- when 8 * size <> N do
      --   #ASSERT("MemU_with_priv: 8 * " : [size] : "<>" : [N]);
      var value = 0s0 ^ 64;

      -- Legacy non alignment-checking configuration forces accesses
      -- to be aligned
      VA = if not CP15.SCTLR.A and not CP15.SCTLR.U then
              Align(address, size)
           else
              address;

      -- Do aligned acess, take alignment failt, or do sequence of bytes
      if Aligned (VA, size) then
         value <- [MemA_with_priv (VA, size, privileged, data_ins)::bits(N)]
      else if CP15.SCTLR.A then
         AlignmentFault(address, false)
      else { -- if unaligned access, not SCTLR.A, and SCTLR.U
         for i in 0 .. size - 1 do
            value<8*i+7:8*i> <- [MemA_with_priv (VA+[i], 1, privileged, data_ins)::byte];
         when CPSR.E do
            value <- BigEndianReverse (value, size)
      };

      [value]
   }

   assign value =
   {
      -- Legacy non alignment-checking configuration forces accesses
      -- to be aligned
      VA = if not CP15.SCTLR.A and not CP15.SCTLR.U then
              Align (address, size)
           else
              address;

      -- Do aligned acess, take alignment failt, or do sequence of bytes
      if Aligned (VA, size) then
         MemA_with_priv (VA, size, privileged, data_ins) <- value
      else if CP15.SCTLR.A then
         AlignmentFault(address, true)
      else { -- if unaligned access, not SCTLR.A, and SCTLR.U
         v = if CPSR.E then BigEndianReverse ([value], size) else [value];
         for i in 0 .. size - 1 do
            MemA_with_priv (VA + [i], 1, privileged, data_ins) <- [v<8*i+7:8*i>]::byte
      }
   }
}

component MemU_unpriv (address::word, size::nat, data_ins :: bool) :: bits(N) with N in 8,16,32,64
{  value = MemU_with_priv (address, size, false, data_ins)
   assign value = MemU_with_priv (address, size, false, data_ins) <- value
}

component MemU (address::word, size::nat, data_ins :: bool) :: bits(N) with N in 8,16,32,64
{  value = MemU_with_priv (address, size, CurrentModeIsNotUser(), data_ins)
   assign value =
     MemU_with_priv (address, size, CurrentModeIsNotUser(), data_ins) <- value
}

bool NullCheckIfThumbEE (n::reg) =
{  var EndOfInstruction = false;
   when CurrentInstrSet() == InstrSet_ThumbEE do
      if n == 15 then
         when Align (PC, 4) == 0 do #UNPREDICTABLE("NullCheckIfThumbEE")
      else if n == 13 then
         when SP == 0 do #UNPREDICTABLE("NullCheckIfThumbEE")
      else when R(n) == 0 do
      {  LR <- PC<31:1> : '1'; -- PC holds this instruction’s address plus 4
         ITSTATE <- 0b00000000;
         BranchWritePC (CP14.TEEHBR - 4);
         EndOfInstruction <- true
      };
   not EndOfInstruction
}

--------------------------------
-- Bit and arithmetic operations
--------------------------------

int HighestSetBit (w::bits(N)) = if w == 0 then -1 else [Log2 (w)]

nat CountLeadingZeroBits (w::bits(N)) = [[N] - 0i1 - HighestSetBit (w)]

nat LowestSetBit (w::bits(N)) = CountLeadingZeroBits (Reverse (w))

nat BitCount (w::bits(N)) =
{  var result = 0;
   for i in 0 .. N - 1 do
      when w<i> do result <- result + 0n1;
   result
}

bits(N) SignExtendFrom (w::bits(N), p::nat) =
{  s = N - 1 - p;
   w << s >> s
}

bits(N) Extend (unsigned::bool, w::bits(M)) =
   if unsigned then ZeroExtend (w) else SignExtend (w)

-- Saturating arithmetic --

bits(M) * bool SignedSatQ (i::int, N::nat) =
{  when M < N do #ASSERT("SignedSatQ: M < N");
   max = [(2 ** (N - 1)) :: nat] :: int;
   if i > max - 1 then
      [max - 1], true
   else if i < -max then
      [-max], true
   else
      [i], false
}

bits(M) * bool UnsignedSatQ (i::int, N::nat) =
{  when M < N do #ASSERT("UnsignedSatQ: M < N");
   max = [(2 ** N - 1) :: nat] :: int;
   if i > max then
      [max], true
   else if i < 0 then
      0, true
   else
      [i], false
}

bits(M) * bool SatQ (i::int, N::nat, unsigned::bool) =
  if unsigned then
    UnsignedSatQ (i, N)
  else
    SignedSatQ (i, N)

bits(M) SignedSat (i::int, N::nat) = Fst (SignedSatQ (i, N))
bits(M) UnsignedSat (i::int, N::nat) = Fst (UnsignedSatQ (i, N))
-- bits(M) Sat (i::int, N::nat, unsigned::bool) = Fst (SatQ (i, N, unsigned))

-- Shifts --

bits(N) * bool LSL_C (x::bits(N), shift::nat) =
{  when shift == 0 do #ASSERT "LSL_C";
   extended_x = [x] : (0s0 ^ shift);
   ( x << shift, extended_x<N> )
}

bits(N) LSL (x::bits(N), shift::nat) =
   if shift == 0 then
      x
   else
      Fst (LSL_C (x, shift))

bits(N) * bool LSR_C (x::bits(N), shift::nat) =
{  when shift == 0 do #ASSERT "LSR_C";
   ( x >>+ shift, shift <= N and x<shift-1> )
}

bits(N) LSR (x::bits(N), shift::nat) =
   if shift == 0 then
      x
   else
      Fst (LSR_C (x, shift))

bits(N) * bool ASR_C (x::bits(N), shift::nat) =
{  when shift == 0 do #ASSERT "ASR_C";
   ( x >> shift, x<Min(N, shift)-1> )
}

bits(N) ASR (x::bits(N), shift::nat) =
   if shift == 0 then
      x
   else
      Fst (ASR_C (x, shift))

bits(N) * bool ROR_C (x::bits(N), shift::nat) =
{  when shift == 0 do #ASSERT "ROR_C";
   result = x #>> shift;
   ( result, Msb (result) )
}

bits(N) ROR (x::bits(N), shift::nat) =
   if shift == 0 then
      x
   else
      Fst (ROR_C (x, shift))

bits(N) * bool RRX_C (x::bits(N), carry_in::bool) =
{  result = [[carry_in] : ([x]::bool list)<N-1:1>] :: bits(N);
   ( result, x<0> )
}

bits(N) RRX (x::bits(N), carry_in::bool) =
   Fst (RRX_C (x, carry_in))

-- Decode immediate values

construct SRType { SRType_LSL SRType_LSR SRType_ASR SRType_ROR SRType_RRX }

SRType * nat DecodeImmShift (typ::bits(2), imm5::bits(5)) =
   match typ
   { case '00' => SRType_LSL, [imm5]
     case '01' => SRType_LSR, if imm5 == 0b00000 then 32 else [imm5]
     case '10' => SRType_ASR, if imm5 == 0b00000 then 32 else [imm5]
     case '11' => if imm5 == 0b00000 then SRType_RRX, 1 else SRType_ROR, [imm5]
   }

SRType DecodeRegShift (typ::bits(2)) =
   match typ
   { case '00' => SRType_LSL
     case '01' => SRType_LSR
     case '10' => SRType_ASR
     case '11' => SRType_ROR
   }

bits(N) * bool Shift_C
                 (value::bits(N), typ::SRType, amount::nat, carry_in::bool) =
{  -- when typ == SRType_RRX and amount != 1 do #ASSERT("Shift_C");

   if amount == 0 then
      value, carry_in
   else
      match typ
      { case SRType_LSL => LSL_C (value, amount)
        case SRType_LSR => LSR_C (value, amount)
        case SRType_ASR => ASR_C (value, amount)
        case SRType_ROR => ROR_C (value, amount)
        case SRType_RRX => RRX_C (value, carry_in)
      }
}

bits(N) Shift (value::bits(N), typ::SRType, amount::nat, carry_in::bool) =
   Fst (Shift_C (value, typ, amount, carry_in))

word * bool ARMExpandImm_C (imm12::bits(12), carry_in::bool) =
{  unroatated_value = ZeroExtend (imm12<7:0>);
   Shift_C (unroatated_value, SRType_ROR, 0n2 * [imm12<11:8>], carry_in)
}

word ARMExpandImm (imm12::bits(12)) =
   -- APSR.C argument to following function call does not affect the imm32
   -- result
   Fst (ARMExpandImm_C (imm12, CPSR.C))

word * bool ThumbExpandImm_C (imm12::bits(12), carry_in::bool) =
   if imm12<11:10> == 0b00 then
   {  imm32 = match imm12<9:8>
              { case '00' =>
                  ZeroExtend (imm12<7:0>)
                case '01' =>
                  if imm12<7:0> == 0b00000000 then
                     #UNPREDICTABLE("ThumbExpandImm_C")
                  else
                     '00000000' : imm12<7:0> : '00000000' : imm12<7:0>
                case '10' =>
                  if imm12<7:0> == 0b00000000 then
                     #UNPREDICTABLE("ThumbExpandImm_C")
                  else
                     imm12<7:0> : '00000000' : imm12<7:0> : '00000000'
                case '11' =>
                  if imm12<7:0> == 0b00000000 then
                     #UNPREDICTABLE("ThumbExpandImm_C")
                  else
                     imm12<7:0> : imm12<7:0> : imm12<7:0> : imm12<7:0>
              };
      imm32, carry_in
   }
   else
   {  unroatated_value = ZeroExtend ('1' : imm12<6:0>);
      ROR_C (unroatated_value, [imm12<11:7>])
   }

word * bool ExpandImm_C (imm12::bits(12), carry_in::bool) =
   if Encoding == Encoding_Thumb2 then
      ThumbExpandImm_C (imm12, carry_in)
   else
      ARMExpandImm_C (imm12, carry_in)

{-
word ThumbExpandImm (imm12::bits(12)) =
   -- APSR.C argument to following function call does not affect the imm32
   -- result
   Fst (ThumbExpandImm_C (imm12, CPSR.C))
-}

-- Data processing operations

bits(N) * bool * bool AddWithCarry (x::bits(N), y::bits(N), carry_in::bool) =
{  unsigned_sum = [x] + [y] + [carry_in] :: nat;
   signed_sum = [x] + [y] + [carry_in] :: int;
   result = [unsigned_sum]::bits(N);
   carry_out = [result] != unsigned_sum;
   overflow = [result] != signed_sum;
   result, carry_out, overflow
}

word * bool * bool DataProcessingALU (opc::bits(4), a::word, b::word, c::bool) =
   match opc
   { case '0000' or '1000' => a && b, c, UNKNOWN          -- AND, TST
     case '0001' or '1001' => a ?? b, c, UNKNOWN          -- EOR, TEQ
     case '0010' or '1010' => AddWithCarry (a, ~b, true)  -- SUB, CMP
     case '0011'           => AddWithCarry (~a, b, true)  -- RSB
     case '0100' or '1011' => AddWithCarry (a, b, false)  -- ADD, CMN
     case '0101'           => AddWithCarry (a, b, c)      -- ADC
     case '0110'           => AddWithCarry (a, ~b, c)     -- SBC
     case '0111'           => AddWithCarry (~a, b, c)     -- RSC
     case '1100'           => a || b, c, UNKNOWN          -- ORR
     case '1101'           => b, c, UNKNOWN               -- MOV
     case '1110'           => a && ~b, c, UNKNOWN         -- BIC
     case '1111'           => a || ~b, c, UNKNOWN         -- MVN, ORN
   }

bool ArithmeticOpcode (opc::bits(4)) =
   (opc<2> or opc<1>) and not (opc<3> and opc<2>)




unit TakeReset() =
{  -- Enter Supervisor mode and (if relevant) Secure state, and reset CP15.
   -- This affects the banked versions and values of various registers accessed
   -- later in the code.  Also reset other system components.
   CPSR.M <- 0b10011;
   when HaveSecurityExt() do CP15.SCR.NS <- false;

   -- A bunch of system level logic from the ARM reference is missing here
   -- ResetCP15Registers() ??

   -- Further CPSR changes: all interrupts disabled, IT state reset,
   -- instruction set and endianness according to the SCTLR values produced
   -- by the above call to ResetCP15Registers().

   CPSR.I <- true;  CPSR.F <- true;  CPSR.A <- true;
   CPSR.IT <- 0b00000000;
   CPSR.J <- false;  CPSR.T <- CP15.SCTLR.TE;  -- TE=0: ARM, TE=1: Thumb
   CPSR.E <- CP15.SCTLR.EE;  -- EE=0: little-endian, EE=1: big-endian

   -- All registers, bits and fields not reset by the above pseudocode or by
   -- the BranchTo() call below are UNKNOWN bitstrings after reset. In
   -- particular, the return information registers R14_svc and SPSR_svc have
   -- UNKNOWN values, so that it is impossible to return from a reset in an
   -- architecturally defined way.

   -- Branch to Reset vector
   BranchTo (ExcVectorBase() + 0)
}

unit TakeUndefInstrException() =
{  -- Determine return information. SPSR is to be the current CPSR, and LR is
   -- to be the current PC minus 2 for Thumb or 4 for ARM, to change the PC
   -- offsets of 4 or 8 respectively from the address of the current
   -- instruction into the required return address offsets of 2 or 4
   -- respectively.
   new_lr_value = if CPSR.T then PC-2 else PC-4;
   new_spsr_value = CPSR;
   vect_offset = 4;

   -- Check whether to take exception to Hyp mode if in Hyp mode then stay in
   -- Hyp mode
   take_to_hyp = HaveVirtExt() and HaveSecurityExt() and
                 CP15.SCR.NS and CPSR.M == 0b11010;
   -- if HCR.TGE is set, take to Hyp mode through Hyp Trap vector
   route_to_hyp = HaveVirtExt() and HaveSecurityExt() and !IsSecure() and
                  CP15.HCR.TGE and CPSR.M == 0b10000;
   -- User mode if HCR.TGE == '1' and in a Non-secure PL1 mode, the effect is
   -- UNPREDICTABLE

   return_offset = if CPSR.T then 2 else 4;
   preferred_exceptn_return = new_lr_value - return_offset;
   if take_to_hyp then
      -- Note that whatever called TakeUndefInstrException() will have set the
      -- HSR
      EnterHypMode(new_spsr_value, preferred_exceptn_return, vect_offset)
   else if route_to_hyp then
      -- Note that whatever called TakeUndefInstrException() will have set the
      -- HSR
      EnterHypMode(new_spsr_value, preferred_exceptn_return, 20)
   else
   {  -- Enter Undefined (‘11011’) mode, and ensure Secure state if initially in
      -- Monitor (‘10110’) mode. This affects the banked versions of various
      -- registers accessed later in the code.
      when CPSR.M == 0b10110 do CP15.SCR.NS <- false;
      CPSR.M <- 0b11011;

      -- Write return information to registers, and make further CPSR
      -- changes: IRQs disabled, IT state reset, instruction set and endianness
      -- to SCTLR-configured values.
      SPSR <- new_spsr_value;
      R(14) <- new_lr_value;
      CPSR.I <- true;
      CPSR.IT <- 0b00000000;
      CPSR.J <- false;  CPSR.T <- CP15.SCTLR.TE; -- TE=0: ARM, TE=1: Thumb
      CPSR.E <- CP15.SCTLR.EE; -- EE=0: little-endian, EE=1: big-endian

      -- Branch to Undefined Instruction vector.
      BranchTo (ExcVectorBase() + vect_offset)
   }
}

unit TakeSVCException() =
{  -- Determine return information. SPSR is to be the current CPSR, after
   -- changing the IT[] bits to give them the correct values for the following
   -- instruction, and LR is to be the current PC minus 2 for Thumb or 4 for
   -- ARM, to change the PC offsets of 4 or 8 respectively from the address of
   -- the current instruction into the required address of the next instruction
   -- (the SVC instruction having size 2 or 4 bytes respectively).
   ITAdvance();
   new_lr_value = if CPSR.T then PC-2 else PC-4;
   new_spsr_value = CPSR;
   vect_offset = 8;

   -- Check whether to take exception to Hyp mode if in Hyp mode then stay in
   -- Hyp mode
   take_to_hyp = HaveVirtExt() and HaveSecurityExt() and
                 CP15.SCR.NS and CPSR.M == 0b11010;
   -- if HCR.TGE is set, take to Hyp mode through Hyp Trap vector
   route_to_hyp = HaveVirtExt() and HaveSecurityExt() and !IsSecure() and
                  CP15.HCR.TGE and CPSR.M == 0b10000;
   -- User mode if HCR.TGE == '1' and in a Non-secure PL1 mode, the effect is
   -- UNPREDICTABLE

   preferred_exceptn_return = new_lr_value;
   if take_to_hyp then
      -- Note that whatever called TakeUndefInstrException() will have set the
      -- HSR
      EnterHypMode(new_spsr_value, preferred_exceptn_return, vect_offset)
   else if route_to_hyp then
      -- Note that whatever called TakeUndefInstrException() will have set the
      -- HSR
      EnterHypMode(new_spsr_value, preferred_exceptn_return, 20)
   else
   {  -- Enter Supervisor (‘10011’) mode, and ensure Secure state if initially
      -- in Monitor (‘10110’) mode. This affects the banked versions of various
      -- registers accessed later in the code.
      when CPSR.M == 0b10110 do CP15.SCR.NS <- false;
      CPSR.M <- 0b10011;

      -- Write return information to registers, and make further CPSR changes:
      -- IRQs disabled, IT state reset, instruction set and endianness to
      -- SCTLR-configured values.
      SPSR <- new_spsr_value;
      R(14) <- new_lr_value;
      CPSR.I <- true;
      CPSR.IT <- 0b00000000;
      CPSR.J <- false;  CPSR.T <- CP15.SCTLR.TE; -- TE=0: ARM, TE=1: Thumb
      CPSR.E <- CP15.SCTLR.EE; -- EE=0: little-endian, EE=1: big-endian

      -- Branch to SVC vector.
      BranchTo (ExcVectorBase() + vect_offset)
   }
}

unit TakeSMCException() =
{  -- Determine return information. SPSR is to be the current CPSR, after
   -- changing the IT[] bits to give them the correct values for the following
   -- instruction, and LR is to be the current PC minus 0 for Thumb or 4 for
   -- ARM, to change the PC offsets of 4 or 8 respectively from the address of
   -- the current instruction into the required address of the next instruction
   -- (with the SMC instruction always being 4 bytes in length).
   ITAdvance();
   new_lr_value = if CPSR.T then PC else PC-4;
   new_spsr_value = CPSR;
   vect_offset = 8;

   -- Enter Monitor (‘10110’) mode, and ensure Secure state if initially in
   -- Monitor mode.  This affects the banked versions of various registers
   -- accessed later in the code.
   when CPSR.M == 0b10110 do CP15.SCR.NS <- false;
   CPSR.M <- 0b10110;

   EnterMonitorMode (new_spsr_value, new_lr_value, vect_offset)
}

unit TakeHVCException() =
{  -- Determine return information. SPSR is to be the current CPSR, after
   -- changing the IT[] bits to give them the correct values for the following
   -- instruction, and LR is to be the current PC minus 0 for Thumb or 4 for
   -- ARM, to change the PC offsets of 4 or 8 respectively from the address of
   -- the current instruction into the required address of the next instruction
   -- (with the HVC instruction always being 4 bytes in length).
   ITAdvance();
   preferred_exceptn_return = if CPSR.T then PC else PC - 4;
   new_spsr_value = CPSR;

   -- Enter Hyp mode. HVC pseudocode has checked that use of HVC is valid.
   -- Required vector offset depends on whether current mode is Hyp mode.
   if CPSR.M == 0b11010 then
      EnterHypMode (new_spsr_value, preferred_exceptn_return, 8)
   else
      EnterHypMode (new_spsr_value, preferred_exceptn_return, 20)
}



unit TakePrefetchAbortException() =
{  -- Determine return information. SPSR is to be the current CPSR, and LR is
   -- to be the current PC minus 0 for Thumb or 4 for ARM, to change the PC
   -- offsets of 4 or 8 respectively from the address of the current
   -- instruction into the required address of the current instruction plus 4.
   new_lr_value = if CPSR.T then PC else PC-4;
   new_spsr_value = CPSR;
   vect_offset = 12;
   preferred_exceptn_return = new_lr_value - 4;

   -- Determine whether this is an external abort to be routed to Monitor mode.
   route_to_monitor = HaveSecurityExt() and CP15.SCR.EA and IsExternalAbort();

   -- Check whether to take exception to Hyp mode
   -- if in Hyp mode then stay in Hyp mode
   take_to_hyp = HaveVirtExt() and HaveSecurityExt() and CP15.SCR.NS and
                 CPSR.M == 0b11010;
   -- otherwise, check whether to take to Hyp mode through Hyp Trap vector
   -- route_to_hyp = ??  **Hard to model this**
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

unit TakePhysicalIRQException() =
{  -- Determine return information. SPSR is to be the current CPSR, and LR is
   -- to be the current PC minus 0 for Thumb or 4 for ARM, to change the PC
   -- offsets of 4 or 8 respectively from the address of the current
   -- instruction into the required address of the instruction boundary at
   -- which the interrupt occurred plus 4. For this purpose, the PC and CPSR
   -- are considered to have already moved on to their values for the
   -- instruction following that boundary.
   new_lr_value = if CPSR.T then PC else PC-4;
   new_spsr_value = CPSR;
   vect_offset = 24;

   -- Determine whether IRQs are routed to Monitor mode.
   route_to_monitor = HaveSecurityExt() and CP15.SCR.IRQ;

   -- Determine whether IRQs are routed to Hyp mode.
   route_to_hyp = (HaveVirtExt() and HaveSecurityExt() and not CP15.SCR.IRQ and
                   CP15.HCR.IMO and not IsSecure()) or CPSR.M == 0b11010;

   if route_to_monitor then
   {  -- Ensure Secure state if initially in Monitor ('10110') mode. This
      -- affects the Banked versions of various registers accessed later in the
      -- code.
      when CPSR.M == 0b10110 do CP15.SCR.NS <- false;
      EnterMonitorMode (new_spsr_value, new_lr_value, vect_offset)
   }
   else if route_to_hyp then
   {  CP15.HSR <- UNKNOWN;
      preferred_exceptn_return = new_lr_value - 4;
      EnterHypMode (new_spsr_value, preferred_exceptn_return, vect_offset)
   }
   else
   {  -- Handle in IRQ mode. Ensure Secure state if initially in Monitor mode.
      -- This affects the Banked versions of various registers accessed later
      -- in the code.
      when CPSR.M == 0b10110 do CP15.SCR.NS <- false;
      CPSR.M <- 0b10010;

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

      -- Branch to correct IRQ vector.
      if CP15.SCTLR.VE then
         #IMPLEMENTATION_DEFINED("branch to an IRQ vector")
      else
         BranchTo (ExcVectorBase() + vect_offset)
   }
}

unit TakeVirtualIRQException() =
{  -- Determine return information. SPSR is to be the current CPSR, and LR is
   -- to be the current PC minus 0 for Thumb or 4 for ARM, to change the PC
   -- offsets of 4 or 8 respectively from the address of the current
   -- instruction into the required address of the instruction boundary at
   -- which the interrupt occurred plus 4. For this purpose, the PC and CPSR
   -- are considered to have already moved on to their values for the
   -- instruction following that boundary.
   new_lr_value = if CPSR.T then PC else PC-4;
   new_spsr_value = CPSR;
   vect_offset = 24;

   CPSR.M <- 0b10010;

   -- Write return information to registers, and make further CPSR changes:
   -- IRQs disabled, other interrupts disabled if appropriate, IT state
   -- reset, instruction set and endianness to SCTLR-configured values.
   SPSR <- new_spsr_value;
   R(14) <- new_lr_value;
   CPSR.I <- true;
   CPSR.A <- true;
   CPSR.IT <- 0b00000000;
   CPSR.J <- false;  CPSR.T <- CP15.SCTLR.TE; -- TE=0: ARM, TE=1: Thumb
   CPSR.E <- CP15.SCTLR.EE; -- EE=0: little-endian, EE=1: big-endian

   -- Branch to correct IRQ vector.
   if CP15.SCTLR.VE then
      #IMPLEMENTATION_DEFINED("branch to an IRQ vector")
   else
      BranchTo (ExcVectorBase() + vect_offset)
}

unit TakePhysicalFIQException() =
{  -- Determine return information. SPSR is to be the current CPSR, and LR is
   -- to be the current PC minus 0 for Thumb or 4 for ARM, to change the PC
   -- offsets of 4 or 8 respectively from the address of the current
   -- instruction into the required address of the instruction boundary at
   -- which the interrupt occurred plus 4. For this purpose, the PC and CPSR
   -- are considered to have already moved on to their values for the
   -- instruction following that boundary.
   new_lr_value = if CPSR.T then PC else PC-4;
   new_spsr_value = CPSR;
   vect_offset = 28;

   -- Determine whether FIQs are routed to Monitor mode.
   route_to_monitor = HaveSecurityExt() and CP15.SCR.FIQ;

   -- Determine whether FIQs are routed to Hyp mode.
   route_to_hyp = (HaveVirtExt() and HaveSecurityExt() and not CP15.SCR.FIQ and
                   CP15.HCR.FMO and not IsSecure()) or CPSR.M == 0b11010;

   if route_to_monitor then
   {  -- Ensure Secure state if initially in Monitor ('10110') mode. This
      -- affects the Banked versions of various registers accessed later in the
      -- code.
      when CPSR.M == 0b10110 do CP15.SCR.NS <- false;
      EnterMonitorMode (new_spsr_value, new_lr_value, vect_offset)
   }
   else if route_to_hyp then
   {  CP15.HSR <- UNKNOWN;
      preferred_exceptn_return = new_lr_value - 4;
      EnterHypMode (new_spsr_value, preferred_exceptn_return, vect_offset)
   }
   else
   {  -- Handle in FIQ mode. Ensure Secure state if initially in Monitor mode.
      -- This affects the Banked versions of various registers accessed later
      -- in the code.
      when CPSR.M == 0b10110 do CP15.SCR.NS <- false;
      CPSR.M <- 0b10001;

      -- Write return information to registers, and make further CPSR changes:
      -- FIQs disabled, other interrupts disabled if appropriate, IT state
      -- reset, instruction set and endianness to SCTLR-configured values.
      SPSR <- new_spsr_value;
      R(14) <- new_lr_value;
      CPSR.I <- true;
      when not HaveSecurityExt() or HaveVirtExt() or not CP15.SCR.NS or
           CP15.SCR.FW do
        CPSR.F <- true;
      when not HaveSecurityExt() or HaveVirtExt() or not CP15.SCR.NS or
           CP15.SCR.AW do
        CPSR.A <- true;

      CPSR.IT <- 0b00000000;
      CPSR.J <- false;  CPSR.T <- CP15.SCTLR.TE; -- TE=0: ARM, TE=1: Thumb
      CPSR.E <- CP15.SCTLR.EE; -- EE=0: little-endian, EE=1: big-endian

      -- Branch to correct FIQ vector.
      if CP15.SCTLR.VE then
         #IMPLEMENTATION_DEFINED("branch to an FIQ vector")
      else
         BranchTo (ExcVectorBase() + vect_offset)
    }
}

unit TakeVirtualFIQException() =
{  -- Determine return information. SPSR is to be the current CPSR, and LR is
   -- to be the current PC minus 0 for Thumb or 4 for ARM, to change the PC
   -- offsets of 4 or 8 respectively from the address of the current
   -- instruction into the required address of the instruction boundary at
   -- which the interrupt occurred plus 4. For this purpose, the PC and CPSR
   -- are considered to have already moved on to their values for the
   -- instruction following that boundary.
   new_lr_value = if CPSR.T then PC else PC-4;
   new_spsr_value = CPSR;
   vect_offset = 28;

   CPSR.M <- 0b10001;

   -- Write return information to registers, and make further CPSR changes:
   -- FIQs disabled, other interrupts disabled if appropriate, IT state
   -- reset, instruction set and endianness to SCTLR-configured values.
   SPSR <- new_spsr_value;
   R(14) <- new_lr_value;
   CPSR.I <- true;
   CPSR.F <- true;
   CPSR.A <- true;
   CPSR.IT <- 0b00000000;
   CPSR.J <- false;  CPSR.T <- CP15.SCTLR.TE; -- TE=0: ARM, TE=1: Thumb
   CPSR.E <- CP15.SCTLR.EE; -- EE=0: little-endian, EE=1: big-endian

   -- Branch to correct FIQ vector.
   if CP15.SCTLR.VE then
      #IMPLEMENTATION_DEFINED("branch to an FIQ vector")
   else
      BranchTo (ExcVectorBase() + vect_offset)
}

unit TakeHypTrapException() =
{  -- HypTrapException is caused by executing an instruction that is trapped to
   -- Hyp mode as a result of a trap set by a bit in the HCR, HCPTR, HSTR or
   -- HDCR. By definition, it can only be generated in a Non-secure mode other
   -- than Hyp mode.  Note that, when a Supervisor Call exception is taken to
   -- Hyp mode because HCR.TGE==1, this is not a trap of the SVC instruction.
   -- See the TakeSVCException() pseudocode for this case.
   preferred_exceptn_return = if CPSR.T then PC-4 else PC-8;
   new_spsr_value = CPSR;
   EnterHypMode (new_spsr_value, preferred_exceptn_return, 20)
}



unit CallSupervisor (immediate::half) =
{  when CurrentModeIsHyp() or
        HaveVirtExt() and not IsSecure() and not CurrentModeIsNotUser() and
        CP15.HCR.TGE do
   {  -- will be taken to Hyp mode so must set HSR
      var HSRString = 0;
      HSRString<15:0> <- if CurrentCond() == 0b1110 then immediate else UNKNOWN;
      WriteHSR (0b010010, HSRString)
   };
   TakeSVCException()
}

unit CallHypervisor (immediate::half) =
{  HSRString = immediate : 0;
   WriteHSR (0b010010, HSRString);
   TakeHVCException()
}

----------------------------------------------------
-- Support for Banked register transfer instructions
----------------------------------------------------

unit BankedRegisterAccessValid (SYSm::bits(5), mode::bits(5)) =
   if SYSm<4:3> == 0b00 then
      if SYSm<2:0> == 0b111 then
         #UNPREDICTABLE("BankedRegisterAccessValid")
      else if SYSm<2:0> == 0b110 then
         when mode in set { 0b11010, 0b11111 } do
            #UNPREDICTABLE("BankedRegisterAccessValid")
      else if SYSm<2:0> == 0b101 then
         when mode == 0b11111 do
            #UNPREDICTABLE("BankedRegisterAccessValid")
      else when mode != 0b10001 do
         #UNPREDICTABLE("BankedRegisterAccessValid")
   else if SYSm<4:3> == 0b01 then
      when SYSm<2:0> == 0b111 or mode == 0b10001 or
           CP15.NSACR.RFR and not IsSecure() do
         #UNPREDICTABLE("BankedRegisterAccessValid")
   else when SYSm<4:3> == 0b11 do
      if not SYSm<2> then
         #UNPREDICTABLE("BankedRegisterAccessValid")
      else if not SYSm<1> then
         when not IsSecure() or mode == 0b10110 do
            #UNPREDICTABLE("BankedRegisterAccessValid")
      else
         when mode != 0b10110 do
            #UNPREDICTABLE("BankedRegisterAccessValid")

unit SPSRAccessValid (SYSm::bits(5), mode::bits(5)) =
   match SYSm
   { case '01110' =>                                 -- SPSR_fiq
        when not IsSecure() and CP15.NSACR.RFR or    -- 10001 is FIQ mode
             mode == 0b10001 do
           #UNPREDICTABLE("SPSRAccessValid")
     case '10000' =>                                 -- SPSR_irq
        when mode == 0b10010 do                      -- 10010 is IRQ mode
           #UNPREDICTABLE("SPSRAccessValid")
     case '10010' =>                                 -- SPSR_svc
        when mode == 0b10011 do                      -- 10011 is Supervisor mode
           #UNPREDICTABLE("SPSRAccessValid")
     case '10100' =>                                 -- SPSR_abt
        when mode == 0b10111 do                      -- 10111 is Abort mode
           #UNPREDICTABLE("SPSRAccessValid")
     case '10110' =>                                 -- SPSR_und
        when mode == 0b11011 do                      -- 11011 is Undefined mode
           #UNPREDICTABLE("SPSRAccessValid")
     case '11100' =>                                 -- SPSR_mon
        when mode == 0b10110 or not IsSecure() do    -- 10110 is Monitor mode
           #UNPREDICTABLE("SPSRAccessValid")
     case '11110' =>                                 -- SPSR_hyp
        when mode != 0b10110 do
           #UNPREDICTABLE("SPSRAccessValid")
     case _ => #UNPREDICTABLE("SPSRAccessValid")
   }

bool InstrIsPL0Undefined ( instr :: bits (32)) = true

unit GenerateCoprocessorException () =  #UNPREDICTABLE ("exception from co-processor")

bool CP15InstrDecode(instr :: bits(32)) = true

-- Coproc_Accepted() only for cp15

-- Coproc_Accepted()
-- Determines whether the coprocessor instruction is accepted.

bool Coproc_Accepted (instr :: bits(32)) =
{
  var CrNnum;
  var two_reg;
  var HSRString :: bits (25);
  --  Only MCR/MCRR/MRRC/MRC are supported in CP15
  if instr<27:24> == '1110' and instr<4> and instr<31:28> != '1111' then
  -- MCR/MRC
  {
    CrNnum <- [instr<19:16>] :: nat; 
    two_reg <- false
     }
  else if instr<27:21> == '1100010' and instr<31:28> != '1111' then 
     -- MCRR/MRRC
     {
       CrNnum <- [instr<3:0>] :: nat;
       two_reg <- true
      } 
       else
         #UNPREDICTABLE ("undefined");
  
  when CrNnum == 4 do #UNPREDICTABLE ("undefined");

  -- Check for coarse-grained Hyp traps

  -- Check against HSTR for PL1 accesses
  when HaveSecurityExt() and HaveVirtExt() and !IsSecure() and !CurrentModeIsHyp() and CrNnum != 14 and CP15.&HSTR<CrNnum>  do
   {
    when !CurrentModeIsNotUser() and InstrIsPL0Undefined(instr) do #UNPREDICTABLE ("undefined"); --IMPLEMENTATION_CHOICE to be UNDEFINED
    HSRString <- 0`25; 
    if two_reg then
     {
       HSRString<19:16> <- instr<7:4>; 
       HSRString<13:10> <- instr<19:16>; 
       HSRString<8:5> <- instr<15:12>; 
       HSRString<4:1> <- instr<3:0>; 
       HSRString<0> <- instr<20>; 
       WriteHSR('000100', HSRString)
       }
    else
     {
      HSRString<19:17> <- instr<7:5>; 
      HSRString<16:14> <- instr<23:21>; 
      HSRString<13:10> <- instr<19:16>; 
      HSRString<8:5> <- instr<15:12>; 
      HSRString<4:1> <- instr<3:0>; 
      HSRString<0> <- instr<20>; 
      WriteHSR('000011', HSRString)
       };
  TakeHypTrapException()
  };

  -- Check for TIDCP as a coarse-grain check for PL1 accesses
  when HaveSecurityExt() and HaveVirtExt() and !IsSecure() and !CurrentModeIsHyp() and CP15.HCR.TIDCP and !two_reg do
  {
   var CrMnum = [instr<3:0>] :: nat;
   when (CrNnum == 9 and CrMnum in set {0,2,5,6,7,8}) or (CrNnum == 10 and CrMnum in set {0,1,4,8}) or (CrNnum == 11 and CrMnum in set {0,1,2,3,4,5,6,7,8,15}) do
       {
         when !CurrentModeIsNotUser() and InstrIsPL0Undefined(instr) do #UNPREDICTABLE ("undefined"); --IMPLEMENTATION_CHOICE to be UNDEFINED
         HSRString <- 0`25; 
         HSRString<19:17> <- instr<7:5>; 
         HSRString<16:14> <- instr<23:21>;
         HSRString<13:10> <- instr<19:16>; 
         HSRString<8:5>   <- instr<15:12>; 
         HSRString<4:1>   <- instr<3:0>; 
         HSRString<0>     <- instr<20>; 
         WriteHSR('000011', HSRString); 
         TakeHypTrapException()
        }
     };
  return CP15InstrDecode(instr)
  }
