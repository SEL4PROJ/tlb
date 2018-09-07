--------------
-- TLB
--------------

nat N_super = 24
nat N_sec   = 20
nat N_large = 16
nat N_small = 12


construct tag_t {
	 Asid :: bits (8)
     Global }
	 
	 
record EntrySuper_t
{
  tag    :: tag_t
  vadSup  :: bits(8)
  padSup  :: bits(8)
  -- NS      :: bits(1) 
  memattrs  :: MemoryAttributes
  perms            :: Permissions 
	-- nG               :: bits(1)       -- '0' = Global, '1' = not Global
	domain 			     :: bits(4)
  -- contiguoushint   :: bool
  -- NSTID            :: bits(1)  
  level            :: int
}

record EntrySection_t
{
  tag    :: tag_t
  vadSec  :: bits(12)
  padSec  :: bits(12)
  -- NS      :: bits(1) 
  memattrs  :: MemoryAttributes
  perms            :: Permissions 
	-- nG               :: bits(1)       -- '0' = Global, '1' = not Global
	domain 			     :: bits(4)
  -- contiguoushint   :: bool 
  -- NSTID            :: bits(1) 
  level            :: int
}

record EntryLarge_t
{
  tag    :: tag_t
  vadLr  :: bits(16)
  padLr  :: bits(16)
  -- NS      :: bits(1) 
  memattrs  :: MemoryAttributes
  perms            :: Permissions 
	--nG               :: bits(1)       -- '0' = Global, '1' = not Global
	domain 			     :: bits(4)
  -- contiguoushint   :: bool 
  -- NSTID            :: bits(1) 
  level            :: int
}

record EntrySmall_t
{
  tag    :: tag_t
  vadSm  :: bits(20)
  padSm  :: bits(20)
  -- NS      :: bits(1) 
  memattrs  :: MemoryAttributes
  perms            :: Permissions 
	--nG               :: bits(1)       -- '0' = Global, '1' = not Global
	domain 			     :: bits(4)
  -- contiguoushint   :: bool 
  -- NSTID            :: bits(1) 
  level            :: int
}

construct TLBEntry 
{
  EntrySmall   :: EntrySmall_t, 
  EntryLarge   :: EntryLarge_t, 
	EntrySection :: EntrySection_t, 
	EntrySuper   :: EntrySuper_t
}


-- couldn't find more details on NSTID, except on a github repo, https://github.com/andysan/gem5/blob/master/src/arch/arm/tlb.cc
-- so the idea is to have it in the format of TLB


-- have a function to map this to existing TLB types

TLBEntry TLBTypeCast (e :: TLBRecord, a :: bits(8), va :: bits(32) ) =
   match e.blocksize
    { 
     case 4    =>  --small page
      {
       var e1 :: EntrySmall_t;
       if e.nG == '0' 
	     then e1.tag  <- Global 
	     else e1.tag   <- Asid (a);
       e1.vadSm          <- va<31:12>;
       e1.padSm          <- e.addrdesc.paddress<31:12>;
       -- e1.NS             <- e.addrdesc.paddress.NS;
       e1.memattrs       <- e.addrdesc.memattrs;
       e1.perms          <- e.perms;
      -- e1.nG             <- e.nG;
       e1.domain         <- e.domain;
       -- e1.contiguoushint <- e.contiguoushint;
       -- e1.NSTID          <- e.addrdesc.paddress.NS;
       e1.level          <- e.level;
      return EntrySmall(e1)
      }
     case 64   =>  --large page
      {
       var e1:: EntryLarge_t;
       if e.nG == '0' 
	     then e1.tag  <- Global 
	     else e1.tag   <- Asid (a);
       e1.vadLr          <- va<31:16>;
       e1.padLr          <- e.addrdesc.paddress<31:16>;
       -- e1.NS             <- e.addrdesc.paddress.NS;
       e1.memattrs       <- e.addrdesc.memattrs;
       e1.perms          <- e.perms;
       --e1.nG             <- e.nG;
       e1.domain         <- e.domain;
       -- e1.contiguoushint <- e.contiguoushint;
       -- e1.NSTID          <- e.addrdesc.paddress.NS;
       e1.level          <- e.level;
      return EntryLarge(e1)
      }
     case 1024 =>  -- section
      {
       var e1:: EntrySection_t;
       if e.nG == '0' 
	     then e1.tag  <- Global 
	     else e1.tag   <- Asid (a);
       e1.vadSec          <- va<31:20>;
       e1.padSec          <- e.addrdesc.paddress<31:20>;
       -- e1.NS              <- e.addrdesc.paddress.NS;
       e1.memattrs        <- e.addrdesc.memattrs;
       e1.perms           <- e.perms;
       --e1.nG              <- e.nG;
       e1.domain          <- e.domain;
       -- e1.contiguoushint  <- e.contiguoushint;
       -- e1.NSTID           <- e.addrdesc.paddress.NS;
       e1.level           <- e.level;
      return EntrySection(e1)
      }
     case _    =>  -- supersection
      {
       var e1:: EntrySuper_t;
       if e.nG == '0' 
	     then e1.tag  <- Global 
	     else e1.tag   <- Asid (a);
       e1.vadSup          <- va<31:24>;
       e1.padSup          <- e.addrdesc.paddress<31:24>;
       -- e1.NS             <- e.addrdesc.paddress.NS;
       e1.memattrs        <- e.addrdesc.memattrs;
       e1.perms           <- e.perms;
       --e1.nG              <- e.nG;
       e1.domain          <- e.domain;
       -- e1.contiguoushint  <- e.contiguoushint;
       -- e1.NSTID           <- e.addrdesc.paddress.NS;
       e1.level          <- e.level;
      return EntrySuper(e1)
      }
    }


construct lookup_type 
      {   Miss, 
          Incon, 
          Hit::TLBEntry  }

--from cortex A9 reference manual--

nat microInstrTLBEntries = 64
nat microDataTLBEntries = 32
nat mainTLBEntries = 256

type MicroInstrTLBMap = bits(6) -> TLBEntry option
type MicroDataTLBMap  = bits(5) -> TLBEntry option
type MainTLBMap       = bits(8) -> TLBEntry option

declare
{
  micro_InstrTLB :: MicroInstrTLBMap
  micro_DataTLB  :: MicroDataTLBMap
  main_TLB       :: MainTLBMap
}


component InstrTLB (i::bits(6)) :: TLBEntry option
{
  value = micro_InstrTLB(i)
  assign value = micro_InstrTLB(i) <- value
}

component DataTLB (i::bits(5)) :: TLBEntry option
{
  value = micro_DataTLB(i)
  assign value = micro_DataTLB(i) <- value
}

component unified_mainTLB (i::bits(8)) :: TLBEntry option
{
  value = main_TLB(i)
  assign value = main_TLB(i) <- value
}


-- this is same as fully associative lookup
bool MatchingEntry (a:: bits(8), vad::bits(32), e::TLBEntry) =
  match e 
   {
    case EntrySmall   (e1)  => if e1.tag == Global then e1.vadSm  == vad<31:12> 
								else (e1.tag == Asid (a) and e1.vadSm  == vad<31:12>) 
    case EntryLarge   (e1)  => if e1.tag == Global then e1.vadLr  == vad<31:16> 
	                            else (e1.tag == Asid (a) and e1.vadLr  == vad<31:16>) 
    case EntrySection (e1)  => if e1.tag == Global then e1.vadSec == vad<31:20> 
	                            else (e1.tag == Asid (a) and e1.vadSec == vad<31:20>) 
    case EntrySuper   (e1)  => if e1.tag == Global then e1.vadSup == vad<31:24> 
	                            else (e1.tag == Asid (a) and e1.vadSup == vad<31:24>) 
   } 
   
--   -- this is same as fully associative lookup
--   bool MatchingEntry (a:: bits(8), vad::bits(32), e::TLBEntry) =
--     match e 
--      {
 --      case EntrySmall   (e1)  => (e1.asid == a or ![e1.nG] :: bool) and e1.vadSm  == vad<31:12> -- and (CP15.SCR.NS == [e1.NSTID] :: bool) 
 --      case EntryLarge   (e1)  => (e1.asid == a or ![e1.nG] :: bool) and e1.vadLr  == vad<31:16> -- and (CP15.SCR.NS == [e1.NSTID] :: bool)
  --     case EntrySection (e1)  => (e1.asid == a or ![e1.nG] :: bool) and e1.vadSec == vad<31:20> -- and (CP15.SCR.NS == [e1.NSTID] :: bool)
 --      case EntrySuper   (e1)  => (e1.asid == a or ![e1.nG] :: bool) and e1.vadSup == vad<31:24> -- and (CP15.SCR.NS == [e1.NSTID] :: bool)
--      }


TLBEntry list entry_list_instr_micro (a :: bits(8), vad :: bits(32) ) =
{
  var found = Nil;
  for i in 0 .. microInstrTLBEntries - 1 do
   match InstrTLB ([i])
    {
     case Some (e) => when MatchingEntry (a, vad, e) do found <- (e) @ found
     case None => nothing
     };
  return found
}

TLBEntry list entry_list_data_micro (a::bits(8), vad::bits(32)) =
{
  var found = Nil;
  for i in 0 .. microDataTLBEntries - 1 do
    match DataTLB ([i])
     {
       case Some (e) =>  when MatchingEntry (a, vad, e) do found <- (e) @ found
       case None => nothing
     }; 
  return found
}

lookup_type lookupTLB_Instr_micro (a::bits(8), vad::bits(32)) =
  match entry_list_instr_micro (a, vad)
  {   
    case Nil => Miss
		case (e1) @ Nil => Hit(e1)
		case _ => Incon
	}

lookup_type lookupTLB_Data_micro (a::bits(8), vad::bits(32)) =
  match entry_list_data_micro (a, vad)
	{   
   case Nil => Miss
	 case (e1) @ Nil => Hit(e1)
	 case _ => Incon
	}


TLBEntry list entry_list_main (a::bits(8), vad::bits(32)) = 
 {
  var found = Nil;
	for i in 0 .. mainTLBEntries - 1 do
     match unified_mainTLB ([i])
	   {
       case Some (e) => when MatchingEntry (a, vad, e) do found <- (e) @ found
	     case _ => nothing
	    };
  return found
  }

lookup_type lookupTLB_main (a::bits(8), vad::bits(32)) =
  match entry_list_main (a, vad)
	 { 
    case Nil => Miss
		case (e1) @ Nil => Hit(e1)
		case _ => Incon
		}


--unit microInstrTLB_evict1 (indx_lst :: bits(6) list) = 
--   for i in 0 .. Length (indx_lst) - 1 do InstrTLB(Element (i,indx_lst)) <- None

 -- FIFO, for fix five locations
unit microInstrTLB_evict () = 
 {  
  InstrTLB([microInstrTLBEntries - 1]:: bits(6)) <- None;
  
  for i in (microInstrTLBEntries - 1) .. 0 do 
           InstrTLB([i + 1]:: bits(6)) <- InstrTLB([i]:: bits(6));
  
  InstrTLB([0::nat]:: bits(6)) <- None
 }
 
  
--unit microInstrTLB_evict () = 
-- {  
--  for i in 0 .. microInstrTLBEntries - 6 do 
--           InstrTLB([i + 5]:: bits(6)) <- InstrTLB([i]:: bits(6));
  
--  for i in 0 .. 5 do 
--           InstrTLB([i]:: bits(6)) <- None
-- }


--unit microDataTLB_evict1 (indx_lst :: bits(5) list) = 
--   for i in 0 .. Length (indx_lst) - 1 do DataTLB(Element (i,indx_lst)) <- None


 -- FIFO, for fix five locations
unit microDataTLB_evict () = 
 {  
     DataTLB([microDataTLBEntries - 1]:: bits(5)) <- None;
  
     for i in (microDataTLBEntries - 1) .. 0 do 
              DataTLB([i + 1]:: bits(5)) <- DataTLB([i]:: bits(5));
  
     DataTLB([0::nat]:: bits(5)) <- None
 }

--unit mainTLB_evict1(indx_lst :: bits(8) list) = 
--   for i in 0 .. Length (indx_lst) - 1 do unified_mainTLB(Element (i,indx_lst)) <- None

 -- FIFO, for fix five locations
unit mainTLB_evict ()= 
 {   
     unified_mainTLB([mainTLBEntries - 1]:: bits(8)) <- None;
  
     for i in (mainTLBEntries - 1) .. 0 do 
              unified_mainTLB([i + 1]:: bits(8)) <- unified_mainTLB([i]:: bits(8));
  
     unified_mainTLB([0::nat]:: bits(8)) <- None
	 
 }

AddressDescriptor va_to_pa  (v :: bits(32), e :: TLBEntry) = 
  {
   var adresdec :: AddressDescriptor;
    match e 
    {
 	   case EntrySmall (sme) => 
      {
        adresdec.paddress <-  sme.padSm  : v<11:0>;
        --adresdec.paddress.NS              <- sme.NS;
        adresdec.memattrs                 <- sme.memattrs
       }  
 	   case EntryLarge   (lre) => 
      {
        adresdec.paddress<- lre.padLr  : v<15:0>;
        --adresdec.paddress.NS              <- lre.NS;
        adresdec.memattrs                 <- lre.memattrs
       }

 	   case EntrySection (sce) =>
      {
        adresdec.paddress <- sce.padSec : v<19:0>;
        --adresdec.paddress.NS              <- sce.NS;
        adresdec.memattrs                 <- sce.memattrs
       }
 	   case EntrySuper (spe) => 
      {
        adresdec.paddress <- spe.padSup : v<23:0>;
        --adresdec.paddress.NS              <- spe.NS;
        adresdec.memattrs                 <- spe.memattrs
       }
   };
   return adresdec
 }


bits(4) domain_entry (e:: TLBEntry) =
  match e
  {
   case EntrySmall   (e1) => e1.domain 
   case EntryLarge   (e1) => e1.domain 
   case EntrySection (e1) => e1.domain 
   case EntrySuper   (e1) => e1.domain  
   }

int level_entry (e:: TLBEntry) =
  match e
  {
   case EntrySmall   (e1) => e1.level 
   case EntryLarge   (e1) => e1.level 
   case EntrySection (e1) => e1.level 
   case EntrySuper   (e1) => e1.level  
   }

Permissions perms_entry (e:: TLBEntry) =
  match e
  {
   case EntrySmall   (e1) => e1.perms 
   case EntryLarge   (e1) => e1.perms 
   case EntrySection (e1) => e1.perms 
   case EntrySuper   (e1) => e1.perms  
   }

tag_t tag_entry (e:: TLBEntry) =
  match e
  {
   case EntrySmall   (e1) => e1.tag 
   case EntryLarge   (e1) => e1.tag 
   case EntrySection (e1) => e1.tag 
   case EntrySuper   (e1) => e1.tag  
   }


AddressDescriptor TranslateAddress (address :: bits(32), privileged :: bool, iswrite :: bool,  size :: nat, data_ins :: bool) =
{
  microInstrTLB_evict();
  microDataTLB_evict();
  mainTLB_evict();
  -- the current asid
  --var asid = CP15.CONTEXTIDR.ASID;

  if data_ins == true then 
   match lookupTLB_Data_micro (CP15.CONTEXTIDR.ASID, address)
   {
	  case Miss => 
         match lookupTLB_main (CP15.CONTEXTIDR.ASID, address)
			    {
				   case Miss => 
				    {
					   (memaddrdesc,tlb_entry)  = TranslateAddressV(address, privileged, iswrite, size);
						 -- replacement
             --var tlb_entry1 = TLBTypeCast (tlb_entry, CP15.CONTEXTIDR.ASID, address);
             DataTLB(0`5) <- Some (TLBTypeCast (tlb_entry, CP15.CONTEXTIDR.ASID, address));
             unified_mainTLB(0`8) <-  Some (TLBTypeCast (tlb_entry, CP15.CONTEXTIDR.ASID, address));
             return memaddrdesc
					   }  
				   case Hit (e) => 
              { 
				DataTLB(0`5) <- Some (e);
				-- here: CheckPermission and CheckDomain, from the tlb entry (0 --ishyp, 0 --usesLD)
                when CheckDomain(domain_entry(e), address, level_entry(e), iswrite) do
                CheckPermission(perms_entry(e), address, level_entry(e), domain_entry(e), iswrite, privileged, false, false);
               return va_to_pa (address, e)
               }
				   case Incon => #IMPLEMENTATION_DEFINED("set on fire")
			      }
		case Hit (e) =>  { -- here: CheckPermission and CheckDomain, from the tlb entry (0 --ishyp, 0 --usesLD)
                when CheckDomain(domain_entry(e), address, level_entry(e), iswrite) do
                CheckPermission(perms_entry(e), address, level_entry(e), domain_entry(e), iswrite, privileged, false, false);
                 -- point 3 of page 6.6 of cortex a9
                return va_to_pa (address, e)
               }
		case Incon => #IMPLEMENTATION_DEFINED("set on fire")
	  }
  else
  match lookupTLB_Instr_micro (CP15.CONTEXTIDR.ASID, address)
   {
	  case Miss => 
         match lookupTLB_main (CP15.CONTEXTIDR.ASID, address)
			    {
				   case Miss => 
				    {
             
					   (memaddrdesc,  tlb_entry) = TranslateAddressV(address, privileged, iswrite, size);
						 -- replacement
             --var tlb_entry1 = TLBTypeCast (tlb_entry, CP15.CONTEXTIDR.ASID, address);
             InstrTLB(0`6) <- Some (TLBTypeCast (tlb_entry, CP15.CONTEXTIDR.ASID, address));
             unified_mainTLB(0`8) <-  Some (TLBTypeCast (tlb_entry, CP15.CONTEXTIDR.ASID, address));
             return memaddrdesc
					   }  
				   case Hit (e) => 
              { 
				InstrTLB(0`6) <- Some (e); 
				-- here: CheckPermission and CheckDomain, from the tlb entry (0 --ishyp, 0 --usesLD)
                when CheckDomain(domain_entry(e), address, level_entry(e), iswrite) do
                CheckPermission(perms_entry(e), address, level_entry(e), domain_entry(e), iswrite, privileged, false, false);
               return va_to_pa (address, e)
               }
				   case Incon => #IMPLEMENTATION_DEFINED("set on fire")
			      }
		case Hit (e) =>  { -- here: CheckPermission and CheckDomain, from the tlb entry (0 --ishyp, 0 --usesLD)
                when CheckDomain(domain_entry(e), address, level_entry(e), iswrite) do
                CheckPermission(perms_entry(e), address, level_entry(e), domain_entry(e), iswrite, privileged, false, false);
                 -- point 3 of page 6.6 of cortex a9
                return va_to_pa (address, e)
               }
		case Incon => #IMPLEMENTATION_DEFINED("set on fire")
	  }
  
  
  }


bool mva_entry_match (e :: TLBEntry option, mva :: bits (20)) =
  match e 
  {
   case None => false
   case Some (e1) =>
     match e1 
     {
      case EntrySmall   (e2) => e2.vadSm == mva 
      case EntryLarge   (e2) => e2.vadLr == mva<19:4>
      case EntrySection (e2) => e2.vadSec == mva<19:8>
      case EntrySuper   (e2) => e2.vadSup == mva<19:12>
    }
  
}



