theory MMU_Translate_Refine
imports  TLB
         L3_LIB.L3_Lib
begin


(* page table walk function *)

type_synonym prrr = "32 word"
type_synonym nmrr = "32 word"
type_synonym ttbr0 = paddr


definition 
cnvrtattrshints  :: "2 word \<Rightarrow> 4 word"
where 
  "cnvrtattrshints RGN \<equiv> if RGN = 0x0 then 0x0
                           else if RGN !! 0 then 
                                   (if RGN !! 1 then 0xB else 0xF)
                                else 0xA"


definition
  MemAtt :: "5 word \<Rightarrow> 1 word \<Rightarrow> 32 word \<Rightarrow> 32 word \<Rightarrow> memattribs_t"
where
  "MemAtt texcb S prrr nmrr \<equiv> if uint ((ucast texcb) :: 3 word) = 6 
                             then \<lparr>
                                     memtyp         = HOL.undefined  ,
                                     innerattrs		   = HOL.undefined,
                                     outerattrs		   = HOL.undefined,
                                     innerhints		   = HOL.undefined,
                                     outerhints		   = HOL.undefined,
                                     innertransient  = False,
                                     outertransient  = False,
                                     shareable       = HOL.undefined,
                                     outershareable  = HOL.undefined \<rparr> 
                             else (if word_extract (2 * (unat ((ucast texcb) :: 3 word)) + 1) (2 * (unat ((ucast texcb) :: 3 word))) prrr = (0x0 :: 2 word) then 
                                   \<lparr>
                                     memtyp         = MemStronglyOrdered ,
                                     innerattrs		   = HOL.undefined,
                                     outerattrs		   = HOL.undefined,
                                     innerhints		   = HOL.undefined,
                                     outerhints		   = HOL.undefined,
                                     innertransient  = False,
                                     outertransient  = False,
                                     shareable       = True,
                                     outershareable  = True \<rparr>  
                                  else if word_extract (2 * (unat ((ucast texcb) :: 3 word)) + 1) (2 * (unat ((ucast texcb) :: 3 word))) prrr = (0x1 :: 2 word) then 
                                   \<lparr>
                                     memtyp         = MemDevice  ,
                                     innerattrs		   = HOL.undefined,
                                     outerattrs		   = HOL.undefined,
                                     innerhints		   = HOL.undefined,
                                     outerhints		   = HOL.undefined,
                                     innertransient  = False,
                                     outertransient  = False,
                                     shareable       = True,
                                     outershareable  = True \<rparr>  
                                  else if word_extract (2 * (unat ((ucast texcb) :: 3 word)) + 1) (2 * (unat ((ucast texcb) :: 3 word))) prrr = (0x2 :: 2 word) then  \<comment> \<open>update this case with the vlaues \<close>
                                   \<lparr>
                                     memtyp         = MemNormal,

                                     innerattrs		   = word_extract 1 0 (cnvrtattrshints (word_extract (2 * (unat ((ucast texcb) :: 3 word)) + 1) (2 * (unat ((ucast texcb) :: 3 word))) nmrr)),
                                     outerattrs		   = word_extract 1 0 (cnvrtattrshints (word_extract (2 * (unat ((ucast texcb) :: 3 word)) + 17) (2 * (unat ((ucast texcb) :: 3 word)) +16) nmrr)),

                                     innerhints		   =  word_extract 3 2 (cnvrtattrshints (word_extract (2 * (unat ((ucast texcb) :: 3 word)) + 1) (2 * (unat ((ucast texcb) :: 3 word))) nmrr)),
                                     outerhints		   = word_extract 3 2 (cnvrtattrshints (word_extract (2 * (unat ((ucast texcb) :: 3 word)) + 17) (2 * (unat ((ucast texcb) :: 3 word)) +16) nmrr)),
                                     innertransient  = False,
                                     outertransient  = False,
                                     shareable       = if S = 0x0 then prrr!! 18 else prrr !! 19,
                                     outershareable  = if S = 0x0 then (prrr!! 18) & (\<not>prrr!! ((unat ((ucast texcb) :: 3 word)) + 24)) else (prrr !! 19) & (\<not>prrr!! ((unat ((ucast texcb) :: 3 word)) + 24)) \<rparr>   
                                    else \<lparr>
                                     memtyp         = HOL.undefined,
                                     innerattrs		   = HOL.undefined,
                                     outerattrs		   = HOL.undefined,
                                     innerhints		   = HOL.undefined,
                                     outerhints		   = HOL.undefined,
                                     innertransient  = False,
                                     outertransient  = False,
                                     shareable       = HOL.undefined,
                                     outershareable  = HOL.undefined \<rparr>   ) "




definition
  perms_to_tlb_fl :: "arm_perm_bits \<Rightarrow> 32 word \<Rightarrow> 32 word \<Rightarrow> flags_t"
where
  "perms_to_tlb_fl pb prrr nmrr \<equiv> \<lparr> 
   memattribs = MemAtt (((ucast (arm_p_TEX pb) :: 5 word) << 2) && ((ucast (arm_p_C pb) :: 5 word) << 1) && (ucast (arm_p_B pb) :: 5 word))  (arm_p_S pb) prrr nmrr, 
   permissions = \<lparr>accessperm  = ((ucast (arm_p_APX pb) :: 3 word) << 2)  && ucast(arm_p_AP pb), 
                         executenever = arm_p_XN pb , pexecutenever = arm_p_PXN pb \<rparr>,
   domain  =  arm_p_domain pb,
   level = arm_p_level pb \<rparr>"


definition
  perms_to_tlb_tag :: "arm_perm_bits \<Rightarrow> asid \<Rightarrow> asid option"
where
  "perms_to_tlb_tag pb a \<equiv> if arm_p_nG pb = 0x1 then Some a else None"


definition
 pt_walk :: "asid \<Rightarrow> heap \<Rightarrow> ttbr0 \<Rightarrow> prrr \<Rightarrow> nmrr \<Rightarrow> vaddr \<Rightarrow> tlb_entry option"
where
  "pt_walk  asid heap ttbr0 prrr nmrr v \<equiv>
      case get_pde heap ttbr0 v
       of None                 \<Rightarrow> None
       | Some InvalidPDE       \<Rightarrow> None
       | Some ReservedPDE      \<Rightarrow> None
       | Some (SectionPDE p fl) \<Rightarrow>
          Some (Entrysection (perms_to_tlb_tag fl asid) (ucast (addr_val v >> 20) :: 12 word)
                              (ucast ((addr_val p >> 20) && mask 12) :: 12 word)  (perms_to_tlb_fl fl prrr nmrr))
       | Some (SuperSectionPDE p fl) \<Rightarrow>
         Some (Entrysuper (perms_to_tlb_tag fl asid) (ucast (addr_val v >> 24) :: 8 word)
                            (ucast ((addr_val p >> 24) && mask 8) :: 8 word)  (perms_to_tlb_fl fl prrr nmrr))
       | Some (PageTablePDE p) \<Rightarrow>
               (case get_pte heap p v
                 of None                     \<Rightarrow> None
                 |  Some InvalidPTE          \<Rightarrow> None
                 |  Some (SmallPagePTE p fl) \<Rightarrow> 
                         Some (Entrysmall (perms_to_tlb_tag fl asid) (ucast (addr_val v >> 12) :: 20 word)
                                             (ucast ((addr_val p >> 12) && mask 20) :: 20 word) (perms_to_tlb_fl fl prrr nmrr))
                 |  Some (LargePagePTE p fl) \<Rightarrow> 
                         Some (Entrylarge (perms_to_tlb_tag fl asid) (ucast (addr_val v >> 16) :: 16 word)
                                             (ucast ((addr_val p >> 16) && mask 16) :: 16 word) (perms_to_tlb_fl fl prrr nmrr)))"



(*
record AdrDes = phy_ad :: paddr
                memattrs :: MemoryAttributes 



definition
  ptable_lift_adrdesc :: "heap \<Rightarrow> paddr  \<Rightarrow> prrr \<Rightarrow> prrr \<Rightarrow> vaddr \<rightharpoonup> AdrDes" where
  "ptable_lift_adrdesc h pt_root prrr nmrr vp \<equiv>
     let
       vp_val = addr_val vp
     in
       map_option 
         (\<lambda>(base, pg_size, perms). 
            \<lparr>phy_ad = base r+ (vaddr_offset pg_size vp_val),
             memattrs = MemAtt (((ucast (arm_p_TEX perms) :: 5 word) << 2) && ((ucast (arm_p_C perms) :: 5 word) << 1) && (ucast (arm_p_B perms) :: 5 word))  (arm_p_S perms) prrr nmrr \<rparr>)
         (lookup_pde h pt_root vp)"
*)


(* building up new state *)


datatype excpt_t =   NoExcp  | MMUException string
  
record cstate =
  heap :: "paddr \<rightharpoonup> byte"
  ttbr0 :: paddr 
  asid :: asid
  excpt :: excpt_t
  prrr :: "32 word" \<comment> \<open>for memory attributes\<close>
  nmrr :: "32 word" \<comment> \<open>for memory attributes\<close>
  dacr :: "32 word" \<comment> \<open>for domain\<close>



(*
definition 
  raise'exception'  :: "Exception \<Rightarrow> 'a cstate_scheme \<Rightarrow> 'r \<times> 'a cstate_scheme"
where 
  "raise'exception' \<equiv> \<lambda>e. do {
                        v \<leftarrow> read_state Exception;
                        _ \<leftarrow> do {
                            b \<leftarrow> return (v = NoExcp);
                            if b then update_state (Exception_update (\<lambda>_. e)) else return ()
                          };
                        return HOL.undefined
                      }"
*)

definition 
  raise'exception'  :: "excpt_t \<Rightarrow> 'a cstate_scheme \<Rightarrow> 'r \<times> 'a cstate_scheme"
where 
  "raise'exception' \<equiv> \<lambda>e s. let (v, s) = (excpt s, s); (u, y) = let (b, y) = (v = NoExcp, s) in (if b then \<lambda>s. ((), s\<lparr>excpt := e\<rparr>) else Pair ()) y in (undefined, y)"



(* classes proto-types *)
(* should we take vaddr in the end of the inputs?*)
class mmu =
  fixes mmu_translate :: "vaddr \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow>'a cstate_scheme \<Rightarrow> (paddr \<times> memattribs_t) \<times> 'a cstate_scheme" 

class mem_op = mmu +
  fixes mmu_read :: "vaddr \<Rightarrow> 'a cstate_scheme \<Rightarrow> bool list \<times> 'a cstate_scheme"
  fixes mmu_read_size :: "vaddr \<times> nat  \<Rightarrow> 'a cstate_scheme \<Rightarrow> bool list \<times> 'a cstate_scheme"
  fixes mmu_write_size :: "bool list \<times> vaddr \<times> nat \<Rightarrow> 'a cstate_scheme \<Rightarrow> unit \<times> 'a cstate_scheme"

class  reg_tlb_op =
  fixes update_TTBR0 :: "paddr \<Rightarrow> 'a cstate_scheme \<Rightarrow>  unit \<times> 'a cstate_scheme" 
  fixes update_ASID :: "asid \<Rightarrow> 'a cstate_scheme \<Rightarrow>  unit \<times> 'a cstate_scheme" 
  fixes Flush_TLB :: "'a cstate_scheme \<Rightarrow>  unit \<times> 'a cstate_scheme" 
  fixes Flush_ASID :: "asid \<Rightarrow> 'a cstate_scheme \<Rightarrow>  unit \<times> 'a cstate_scheme" 
  fixes Flush_varange :: "vaddr set \<Rightarrow> 'a cstate_scheme \<Rightarrow>  unit \<times> 'a cstate_scheme" 
  fixes Flush_ASIDvarange :: "asid \<Rightarrow> vaddr set \<Rightarrow> 'a cstate_scheme \<Rightarrow>  unit \<times> 'a cstate_scheme" 



record tlbs_set =
       dtlb_set    :: "tlb_entry set"
       itlb_set    :: "tlb_entry set"
       unitlb_set  :: "tlb_entry set"


record tlb_state = cstate + 
                   tlbs_set :: tlbs_set


definition 
  typ_tlbs :: "'a tlb_state_scheme \<Rightarrow> tlbs_set cstate_scheme"
where
  "typ_tlbs s =  cstate.extend (cstate.truncate s) (tlbs_set s)"

lemma tlbs_more [simp]:
  "cstate.more (typ_tlbs s) = tlbs_set s"
  by (clarsimp simp: typ_tlbs_def cstate.defs)

lemma tlbs_truncate [simp]:
  "cstate.truncate (typ_tlbs s') = cstate.truncate s'"
  by (clarsimp simp: typ_tlbs_def cstate.defs)

lemma typ_tlbs_prim_parameter [simp]:
  "asid (typ_tlbs s) = asid s \<and> ttbr0 (typ_tlbs s) =  ttbr0 s \<and> heap (typ_tlbs s) = heap s \<and>
      excpt (typ_tlbs s) = excpt s"
  by (clarsimp simp: typ_tlbs_def  cstate.defs)


(*
consts dtlb_evict :: "tlbs_set cstate_scheme \<Rightarrow> tlb_entry set"

consts itlb_evict :: "tlbs_set cstate_scheme \<Rightarrow> tlb_entry set"

consts unitlb_evict :: "tlbs_set cstate_scheme \<Rightarrow> tlb_entry set"

*)


definition 
  tlb_entry_to_adrdesc :: "vaddr \<Rightarrow> tlb_entry \<Rightarrow> (paddr \<times> memattribs_t)"
where
  "tlb_entry_to_adrdesc v entry = ((Addr (va_to_pa (addr_val v) entry)),
                                       memattribs (flags entry))"


definition 
  memtyp_entry :: "tlb_entry \<Rightarrow> memtyp_t" 
where
  "memtyp_entry e = memtyp (memattribs (flags e))"


definition 
align :: "'a::len0 word \<times> nat \<Rightarrow> 'a word"
where
  "align \<equiv> \<lambda>(w, n). word_of_int (int (n * (nat (uint w) div n)))"


definition 
checkdomain :: "4 word \<Rightarrow> 32 word  \<Rightarrow> 32 word \<Rightarrow> bool option"
where
  "checkdomain dm va dcr \<equiv> 
           if word_extract (2 * (unat dm) + 1) (2 * (unat dm)) dcr = (0x0 :: 2 word) then None
           else if  word_extract (2 * (unat dm) + 1) (2 * (unat dm)) dcr = (0x1 :: 2 word) then Some True
           else if  word_extract (2 * (unat dm) + 1) (2 * (unat dm)) dcr = (0x2 :: 2 word) then None
           else Some False"


definition 
checkpermission :: "permissions_t \<Rightarrow> bool  \<Rightarrow> bool \<Rightarrow> bool option"
where
  "checkpermission perm ispriv iswrite \<equiv> 
             if accessperm (perm) = 0x0 then  Some True
             else if accessperm (perm) = 0x1 then  Some (\<not>ispriv)
             else if accessperm (perm) = 0x2 then  Some (\<not>ispriv & iswrite)
             else if accessperm (perm) = 0x3 then  Some False
             else if accessperm (perm) = 0x4 then  None
             else if accessperm (perm) = 0x5 then  Some (\<not>ispriv \<or> iswrite)
             else if accessperm (perm) = 0x6 then  Some iswrite
             else Some iswrite"





definition 
  align_dom_perm_entry_check  :: "tlb_entry \<Rightarrow> vaddr \<Rightarrow> nat \<Rightarrow> 32 word \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> 'a cstate_scheme \<Rightarrow> (paddr \<times> memattribs_t) \<times> 'a cstate_scheme" 
where 
  "align_dom_perm_entry_check \<equiv> \<lambda> entry v siz dacr ispriv iswrite. if (memtyp_entry entry = MemDevice \<or> memtyp_entry entry = MemStronglyOrdered) \<and> addr_val v \<noteq> align (addr_val v, siz)  
                                         then raise'exception' (MMUException ''Alignment Fault'')
                                         else do {
                                                  let chkdm = checkdomain (domain (flags entry)) (addr_val v) dacr;
                                                  if chkdm = None then raise'exception' (MMUException ''Domain Fault'')  else
                                                  if chkdm = Some True then  
                                                          do{let chkprm = checkpermission (permissions (flags entry)) ispriv iswrite;  \<comment> \<open>encodes abort\<close>
                                                               if chkprm = None then raise'exception' (MMUException ''Permission Fault'')
                                                                else if  chkprm = Some True then raise'exception' (MMUException ''Permission Fault'')
                                                                else return (tlb_entry_to_adrdesc v entry)}
                                                    else return (tlb_entry_to_adrdesc v entry)}"



instantiation tlb_state_ext :: (type) mmu   
begin
  definition   
  "(mmu_translate v siz ispriv iswrite data_ins :: ('a tlb_state_scheme \<Rightarrow> _))
  = do {
     tlbs  <- read_state tlbs_set;
     let dtlb =  dtlb_set tlbs;
     let itlb =  itlb_set tlbs;
     let maintlb =  unitlb_set tlbs;
     heap   <- read_state heap;
     asid  <- read_state asid;
     ttbr0 <- read_state ttbr0;
     prrr  <- read_state prrr;
     nmrr  <- read_state nmrr;
     dacr <- read_state dacr;
     let lookup_first_stage = (if data_ins then lookup dtlb asid (addr_val v) else lookup itlb asid (addr_val v));
     case lookup_first_stage of
          Hit entry \<Rightarrow>  align_dom_perm_entry_check entry v siz dacr ispriv iswrite
        | Miss \<Rightarrow> (case lookup maintlb asid (addr_val v) of
                             Hit entry \<Rightarrow> do {
                                                 let tlb_rld = (if data_ins then tlbs \<lparr> dtlb_set := dtlb \<union> {entry} \<rparr> else tlbs \<lparr> itlb_set := itlb \<union> {entry} \<rparr> );
                                                 update_state (\<lambda>s. s\<lparr> tlbs_set := tlb_rld \<rparr>);
                                                 align_dom_perm_entry_check entry v siz dacr ispriv iswrite}
                          |  Miss \<Rightarrow> (case pt_walk asid heap ttbr0 prrr nmrr v of 
                                            None \<Rightarrow> raise'exception' (MMUException ''more info'')
                                         |  Some entry \<Rightarrow> do {
                                                 \<comment> \<open>it seems like from the manual that TLB is loaded first, alignment and  domain checking is performed afterwards\<close>
                                                 let tlb_rld = (if data_ins then tlbs \<lparr> dtlb_set := dtlb \<union> {entry}, unitlb_set := maintlb \<union> {entry} \<rparr>
                                                                            else tlbs \<lparr> itlb_set := itlb \<union> {entry}, unitlb_set := maintlb \<union> {entry} \<rparr> );
                                                 update_state (\<lambda>s. s\<lparr> tlbs_set := tlb_rld \<rparr>);
                                                 align_dom_perm_entry_check entry v siz dacr ispriv iswrite })
                          | Incon \<Rightarrow> raise'exception' (MMUException ''set on fire''))
        | Incon \<Rightarrow> raise'exception' (MMUException ''set on fire'') 
   }"

thm mmu_translate_tlb_state_ext_def                     
  instance ..
end


(*

instantiation tlb_state_ext :: (type) mmu   
begin
  definition   
  "(mmu_translate v siz ispriv iswrite data_ins :: ('a tlb_state_scheme \<Rightarrow> _))
  = do {
     tlbs  <- read_state tlbs_set;
     let dtlb =  dtlb_set tlbs;
     let itlb =  itlb_set tlbs;
     let maintlb =  unitlb_set tlbs;
     heap   <- read_state heap;
     asid  <- read_state asid;
     ttbr0 <- read_state ttbr0;
     prrr  <- read_state prrr;
     nmrr  <- read_state nmrr;
     dacr <- read_state dacr;
     if data_ins then
           case lookup dtlb asid (addr_val v) of
                Hit entry \<Rightarrow>  align_dom_perm_entry_check entry v siz dacr ispriv iswrite
              | Miss \<Rightarrow> (case lookup maintlb asid (addr_val v) of
                             Hit entry \<Rightarrow> do {
                                              let tlb_rld = tlbs \<lparr> dtlb_set := dtlb \<union> {entry} \<rparr>;
                                                 update_state (\<lambda>s. s\<lparr> tlbs_set := tlb_rld \<rparr>);
                                                 align_dom_perm_entry_check entry v siz dacr ispriv iswrite}
                          |  Miss \<Rightarrow> (case pt_walk asid heap ttbr0 prrr nmrr v of 
                                            None \<Rightarrow> raise'exception' (MMUException ''more info'')
                                         |  Some entry \<Rightarrow> do {
                                                 \<comment> \<open>it seems like from the manual that TLB is loaded first, alignment and  domain checking is performed afterwards\<close>
                                                 let tlb_rld = tlbs \<lparr> dtlb_set := dtlb \<union> {entry}, 
                                                                       unitlb_set := maintlb \<union> {entry} \<rparr>;
                                                 update_state (\<lambda>s. s\<lparr> tlbs_set := tlb_rld \<rparr>);
                                                 align_dom_perm_entry_check entry v siz dacr ispriv iswrite })
                          | Incon \<Rightarrow> raise'exception' (MMUException ''set on fire''))
              | Incon \<Rightarrow> raise'exception' (MMUException ''set on fire'') 
          else 
           case lookup itlb asid (addr_val v) of
                Hit entry \<Rightarrow>  align_dom_perm_entry_check entry v siz dacr ispriv iswrite
              | Miss \<Rightarrow> (case lookup maintlb asid (addr_val v) of
                             Hit entry \<Rightarrow>  do {
                                                let tlb_rld = tlbs \<lparr> itlb_set := itlb \<union> {entry} \<rparr>;
                                                 update_state (\<lambda>s. s\<lparr> tlbs_set := tlb_rld \<rparr>);
                                                  align_dom_perm_entry_check entry v siz dacr ispriv iswrite }
                          |  Miss \<Rightarrow> (case pt_walk asid heap ttbr0 prrr nmrr v of 
                                            None \<Rightarrow> raise'exception' (MMUException ''more info'')
                                        |  Some entry \<Rightarrow> do {
                                                 \<comment> \<open>it seems like from the manual that TLB is loaded first, alignment and  domain checking is performed afterwards\<close>
                                                 let tlb_rld = tlbs \<lparr> itlb_set := itlb \<union> {entry}, 
                                                                       unitlb_set := maintlb \<union> {entry} \<rparr>;
                                                 update_state (\<lambda>s. s\<lparr> tlbs_set := tlb_rld \<rparr>);
                                                 align_dom_perm_entry_check entry v siz dacr ispriv iswrite })
                          | Incon \<Rightarrow> raise'exception' (MMUException ''set on fire''))
              | Incon \<Rightarrow> raise'exception' (MMUException ''set on fire'') 
   }"

thm mmu_translate_tlb_state_ext_def                     
  instance ..
end

*)

thm mmu_translate_tlb_state_ext_def

end