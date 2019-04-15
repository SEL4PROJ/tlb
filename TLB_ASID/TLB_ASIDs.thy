theory TLB_ASIDs
imports
  TLBJ.TLB
begin


definition
  asid_range_of :: "tlb_entry \<Rightarrow> (asid option \<times> vaddr) set"
  where
 "asid_range_of e \<equiv> {asid_of e} \<times> range_of e"


definition 
  global_entries :: "tlb \<Rightarrow>  tlb"
where
  "global_entries t = {e\<in>t. asid_of e = None}"


definition
  non_global_entries :: "tlb \<Rightarrow> tlb"
where
  "non_global_entries t =  {e\<in>t. \<exists>a. asid_of e = Some a}"

definition
  va_range_set :: "_ \<Rightarrow> vaddr set"
where
  "va_range_set t \<equiv> \<Union> (range_of ` t)"



definition  tagged_entry_set  :: "tlb \<Rightarrow> asid \<Rightarrow> vaddr \<Rightarrow> tlb"
where
 "tagged_entry_set t a v \<equiv> {e. e\<in>entry_set t v \<and> (asid_of e = None \<or> asid_of e = Some a)}"
 



type_synonym ttbr0 = paddr

definition "asid_vadr_tlb t \<equiv> 
                       \<Union> (asid_range_of ` t)"






end
