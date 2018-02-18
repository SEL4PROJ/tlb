theory PD_Cache
imports 
 TLB
begin



datatype bpa_pde_type = bpa_sec "32 word" 
                 |      bpa_sm  "32 word"

datatype pde_entry =  EntryPDE asid vSe "bpa_pde_type option" fl

type_synonym pde_cache = "pde_entry set"


datatype lookup_pde_type  =  Miss_pde  | Incon_pde  |  Hit_pde "pde_entry" 



fun 
  pde_entry_asid :: "pde_entry \<Rightarrow> asid"
where
  "pde_entry_asid (EntryPDE a va pa f)= a" 



(* Address Range of an Entry *)
fun 
  pde_entry_range :: "pde_entry \<Rightarrow> vaddr set"
where
  "pde_entry_range (EntryPDE a va pa f) =  Addr ` {(ucast va::32 word) << 20 ..
                                                            ((ucast va::32 word) << 20) + (2^20 - 1)}" 


(* Address Range of an entry with ASID tag *)
definition 
  pde_entry_range_asid_tags :: "pde_entry \<Rightarrow> (asid \<times> vaddr) set"
where
  "pde_entry_range_asid_tags E \<equiv> image (\<lambda>v. (pde_entry_asid E , v)) (pde_entry_range E)"
 



(* Set of all the entries covering a virtual address and an ASID *)
definition 
  pde_entry_set :: "pde_cache \<Rightarrow> asid \<Rightarrow> vaddr \<Rightarrow> (pde_entry set)"
where
  "pde_entry_set t a v \<equiv> {E\<in>t. (a,v) : pde_entry_range_asid_tags E } "



(* Lookup for a virtual address along with an ASID *)
definition 
  lookup_pde :: "pde_cache \<Rightarrow> asid \<Rightarrow> vaddr \<Rightarrow> lookup_pde_type" 
where  
  "lookup_pde t a va \<equiv> if pde_entry_set t a va = {} then Miss_pde
                   else if \<exists>x. pde_entry_set t a va = {x} then Hit_pde (the_elem (pde_entry_set t a va)) 
                        else Incon_pde"



definition 
 pt_walk_pde :: "asid \<Rightarrow> heap \<Rightarrow> ttbr0 \<Rightarrow> vaddr \<Rightarrow> pde_entry"
where
  "pt_walk_pde asid heap ttbr0 v \<equiv>
      case get_pde heap ttbr0 v
       of None                 \<Rightarrow> EntryPDE asid (ucast (addr_val v >> 20) :: 12 word) None 0
       | Some InvalidPDE       \<Rightarrow> EntryPDE asid (ucast (addr_val v >> 20) :: 12 word) None 0
       | Some ReservedPDE      \<Rightarrow> EntryPDE asid (ucast (addr_val v >> 20) :: 12 word) None 0
       | Some (SectionPDE p a) \<Rightarrow> 
          EntryPDE asid (ucast (addr_val v >> 20) :: 12 word) (Some (bpa_sec (addr_val p)))  0 
       | Some (PageTablePDE p) \<Rightarrow> 
            EntryPDE asid (ucast (addr_val v >> 20) :: 12 word)  (Some (bpa_sm (addr_val p))) 0" 



fun 
  bpa_pde_entry :: "pde_entry \<Rightarrow>  bpa_pde_type option"
where                                    
  "bpa_pde_entry (EntryPDE _ _ p _) =  p"


definition
  "is_fault_pde e = (bpa_pde_entry e = None)"


instantiation lookup_pde_type :: order
begin
  definition 
    less_eq_lookup_pde_type: "e \<le> e' \<equiv> e' = Incon_pde \<or> e' = e \<or> e = Miss_pde"

  definition 
    less_lookup_pde_type: "e < (e'::lookup_pde_type) \<equiv> e \<le> e' \<and> e \<noteq> e'"

  instance
     by intro_classes (auto simp add: less_lookup_pde_type less_eq_lookup_pde_type)
end


lemma Incon_pde_top [iff]: "e \<le> Incon_pde"
  by (simp add: less_eq_lookup_pde_type)

lemma Incon_pde_leq [simp]: "(Incon_pde \<le> e) = (e = Incon_pde)"
  by (auto simp add: less_eq_lookup_pde_type)

lemma Miss_pde_bottom [iff]: "Miss_pde \<le> e"
  by (simp add: less_eq_lookup_pde_type)

lemma leq_pde_Miss [simp]: "(e \<le> Miss_pde) = (e = Miss_pde)"
  by (auto simp add: less_eq_lookup_pde_type)

lemma Hits_pde_le [simp]:
  "(Hit_pde h \<le> Hit_pde h') = (h = h')"
  by (auto simp add: less_eq_lookup_pde_type)

lemma tlb_mono_pde_entry_set:
  "t \<subseteq> t' \<Longrightarrow> pde_entry_set t a v \<subseteq> pde_entry_set t' a v"
  by (simp add: pde_entry_set_def) blast

lemma tlb_pde_mono:
  "t \<subseteq> t' \<Longrightarrow> lookup_pde t a v \<le> lookup_pde t' a v"
  by (drule tlb_mono_pde_entry_set) (fastforce simp: lookup_pde_def)


end













