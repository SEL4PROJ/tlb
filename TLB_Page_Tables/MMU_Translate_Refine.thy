theory MMU_Translate_Refine
imports  TLB
begin


datatype Exception =
    ASSERT string
  | IMPLEMENTATION_DEFINED string
  | MMU_Exception string
  | NoException
  | UNPREDICTABLE string
  | VFP_EXCEPTION string


record cstate =
  mem :: "paddr \<rightharpoonup> byte"
  ttbr0 :: paddr 
  asid :: asid
  Exception :: Exception
  data_exe :: bool
  prrr :: "32 word" \<comment> \<open>for memory attributes\<close>
  nmrr :: "32 word" \<comment> \<open>for memory attributes\<close>



definition 
  raise'exception  :: "Exception \<Rightarrow> 'a cstate_scheme \<Rightarrow> 'r \<times> 'a cstate_scheme"
where 
  "raise'exception \<equiv> \<lambda>e. do {
                        v \<leftarrow> read_state Exception;
                        _ \<leftarrow> do {
                            b \<leftarrow> return (v = NoException);
                            if b then update_state (Exception_update (\<lambda>_. e)) else return ()
                          };
                        return HOL.undefined
                      }"



class mmu =
  fixes mmu_translate :: "vaddr \<Rightarrow> 'a cstate_scheme \<Rightarrow> (paddr \<times> MemoryAttributes) \<times> 'a cstate_scheme" 

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
  "asid (typ_tlbs s) = asid s \<and> ttbr0 (typ_tlbs s) =  ttbr0 s \<and> mem (typ_tlbs s) = mem s \<and>
      Exception (typ_tlbs s) = Exception s"
  by (clarsimp simp: typ_tlbs_def  cstate.defs)


(*
consts dtlb_evict :: "tlbs_set cstate_scheme \<Rightarrow> tlb_entry set"

consts itlb_evict :: "tlbs_set cstate_scheme \<Rightarrow> tlb_entry set"

consts unitlb_evict :: "tlbs_set cstate_scheme \<Rightarrow> tlb_entry set"

*)

fun
  flags_entry :: "tlb_entry \<Rightarrow> flags"
where
  "flags_entry (EntrySmall   a x y fl) = fl"
| "flags_entry (EntryLarge   a x y fl) = fl"
| "flags_entry (EntrySection a x y fl) = fl"
| "flags_entry (EntrySuper   a x y fl) = fl"


definition 
  tlb_entry_to_adrdesc :: "vaddr \<Rightarrow> tlb_entry \<Rightarrow> (paddr \<times> MemoryAttributes)"
where
  "tlb_entry_to_adrdesc v entry = ((Addr (va_to_pa (addr_val v) entry)),
                                       MemoryAttributes(flags_entry entry))"

(* address check and return the address descriptor  *)

(* we should remove evict from here  *)

instantiation tlb_state_ext :: (type) mmu   
begin
  definition   
  "(mmu_translate v :: ('a tlb_state_scheme \<Rightarrow> _))
  = do {
     \<comment> \<open>tlbs  <- read_state tlbs_set;
     update_state (\<lambda>s. s\<lparr> tlbs_set :=  tlbs \<lparr> dtlb_set   := dtlb_set tlbs  -  dtlb_evict(typ_tlbs s) ,
                                             itlb_set   := itlb_set tlbs   -  itlb_evict(typ_tlbs s) ,
                                             unitlb_set := unitlb_set tlbs -  unitlb_evict(typ_tlbs s) \<rparr> \<rparr>); \<close>
     tlbs  <- read_state tlbs_set;
     let dtlb =  dtlb_set tlbs;
     let itlb =  itlb_set tlbs;
     let maintlb =  unitlb_set tlbs;
     df    <- read_state data_exe;
     mem   <- read_state mem;
     asid  <- read_state asid;
     ttbr0 <- read_state ttbr0;
     prrr  <- read_state prrr;
     nmrr  <- read_state nmrr;
     if df then
           case lookup dtlb asid (addr_val v) of
                Hit entry \<Rightarrow>  return (tlb_entry_to_adrdesc v entry)
              | Miss \<Rightarrow> (case lookup maintlb asid (addr_val v) of
                             Hit entry \<Rightarrow>  return (tlb_entry_to_adrdesc v entry)
                          |  Miss \<Rightarrow> (case pt_walk asid mem ttbr0 prrr nmrr v of 
                                            None \<Rightarrow> raise'exception (MMU_Exception ''more info'')
                                         |  Some entry \<Rightarrow> do {
                                                 let tlb_rld = tlbs \<lparr> dtlb_set := dtlb \<union> {entry}, 
                                                                       unitlb_set := maintlb \<union> {entry} \<rparr>;
                                                 update_state (\<lambda>s. s\<lparr> tlbs_set := tlb_rld \<rparr>);
                                                 return (tlb_entry_to_adrdesc v entry)
                                             } )
                          | Incon \<Rightarrow> raise'exception (IMPLEMENTATION_DEFINED ''set on fire''))
              | Incon \<Rightarrow> raise'exception (IMPLEMENTATION_DEFINED ''set on fire'') 
          else 
           case lookup itlb asid (addr_val v) of
                Hit entry \<Rightarrow>  return (tlb_entry_to_adrdesc v entry)
              | Miss \<Rightarrow> (case lookup maintlb asid (addr_val v) of
                             Hit entry \<Rightarrow>  return (tlb_entry_to_adrdesc v entry)
                          |  Miss \<Rightarrow> (case pt_walk asid mem ttbr0 prrr nmrr v of 
                                            None \<Rightarrow> raise'exception (MMU_Exception ''more info'')
                                         |  Some entry \<Rightarrow> do {
                                                 let tlb_rld = tlbs \<lparr> itlb_set := itlb \<union> {entry}, 
                                                                       unitlb_set := maintlb \<union> {entry} \<rparr>;
                                                 update_state (\<lambda>s. s\<lparr> tlbs_set := tlb_rld \<rparr>);
                                                 return (tlb_entry_to_adrdesc v entry)
                                             } )
                          | Incon \<Rightarrow> raise'exception (IMPLEMENTATION_DEFINED ''set on fire''))
              | Incon \<Rightarrow> raise'exception (IMPLEMENTATION_DEFINED ''set on fire'') 
   }"

thm mmu_translate_tlb_state_ext_def
(* print_context *)                      
  instance ..
end



end