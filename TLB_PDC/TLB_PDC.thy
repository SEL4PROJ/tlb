theory TLB_PDC
imports
  TLB_ASID_REFJ.TLB_ASIDs


begin

(* every ptable pointer is asid-specific, and it does not have flags *)

datatype pdc_entry =  PDE_Section "asid option" "12 word" (bpa_pdc_entry :"32 word") tlb_flags
                   |  PDE_Table   asid          "12 word" (bpa_pdc_entry : "32 word")

type_synonym pdc = "pdc_entry set"

definition
  "asid_of_pdc e \<equiv>  case e of PDE_Section a va pa f \<Rightarrow> a
                             | PDE_Table a va pa     \<Rightarrow> Some a"


instantiation pdc_entry :: entry_op   
begin

definition "range_of e \<equiv>
                       case e of PDE_Section a va pa f  \<Rightarrow> Addr ` {(ucast va::32 word) << 20 ..
                                                            ((ucast va::32 word) << 20) + (2^20 - 1)} 
                              |
                                PDE_Table a va pa       \<Rightarrow> Addr ` {(ucast va::32 word) << 20 ..
                                                            ((ucast va::32 word) << 20) + (2^20 - 1)}"

instance ..
end

definition  tagged_pdc_entry_set :: "pdc \<Rightarrow> asid \<Rightarrow> vaddr \<Rightarrow> pdc"
where
 "tagged_pdc_entry_set p a v \<equiv> {e. e\<in>entry_set p v \<and> (asid_of_pdc e = None \<or> asid_of_pdc e = Some a)}"


definition
  asid_range_of_pdc :: "pdc_entry\<Rightarrow> (asid option \<times> vaddr) set"
  where
 "asid_range_of_pdc e \<equiv> {asid_of_pdc e} \<times> range_of e"


definition "tag_vadr_pdc p \<equiv> 
                       \<Union> (asid_range_of_pdc ` p)"



section "encoding page table walk to entries"

datatype pt_walk_typ = Fault 
                     | Partial_Walk pdc_entry
                     | Full_Walk tlb_entry pdc_entry



definition 
 pdc_walk :: "asid \<Rightarrow> heap \<Rightarrow> ttbr0 \<Rightarrow> vaddr \<Rightarrow> pdc_entry option"
where
  "pdc_walk a hp rt v \<equiv>
      case get_pde hp rt v
       of Some (SectionPDE p perms) \<Rightarrow> Some (PDE_Section 
                                             (tag_conv a (to_tlb_flags perms))
                                             (ucast (addr_val v >> 20) :: 12 word) 
                                             (addr_val p) 
                                             (to_tlb_flags perms))
       |  Some (PageTablePDE p) \<Rightarrow> Some (PDE_Table a (ucast (addr_val v >> 20) :: 12 word) (addr_val p))
       |  _ \<Rightarrow> None" 


definition
  pte_tlb_entry :: "asid \<Rightarrow> heap \<Rightarrow> paddr \<Rightarrow> vaddr \<Rightarrow> tlb_entry option"
where
  "pte_tlb_entry a heap p v \<equiv> case get_pte heap p v 
                 of Some (SmallPagePTE p' perms) \<Rightarrow> Some (EntrySmall (tag_conv a (to_tlb_flags perms))
                                                                     (ucast (addr_val v >> 12) :: 20 word)
                                                                     ((word_extract 31 12 (addr_val p')):: 20 word)
                                                                     (to_tlb_flags perms))
                 |  _                        \<Rightarrow> None"


fun
  pde_tlb_entry :: "pdc_entry \<Rightarrow> heap  \<Rightarrow> vaddr \<Rightarrow> tlb_entry option"
where
  "pde_tlb_entry (PDE_Section asid vba pba flags) mem va = Some (EntrySection asid (ucast (addr_val va >> 20) :: 12 word) ((ucast (pba >> 20)) :: 12 word)  flags)"
| "pde_tlb_entry (PDE_Table   asid vba pba)       mem va = pte_tlb_entry asid mem (Addr pba) va"


definition
 map_opt :: "('a \<Rightarrow> 'b option) \<Rightarrow> 'a option \<Rightarrow> 'b option"
where
  "map_opt f x  \<equiv> case x of None  \<Rightarrow> None | Some y  \<Rightarrow> f y"

definition
 pt_walk' :: "asid \<Rightarrow> heap \<Rightarrow> ttbr0 \<Rightarrow> vaddr \<Rightarrow> tlb_entry option"
where
  "pt_walk' asid heap ttbr0 v \<equiv> map_opt (\<lambda>pde. pde_tlb_entry pde heap v) (pdc_walk asid heap ttbr0 v)"
     

definition
 pt_walk_pair :: "asid \<Rightarrow> heap \<Rightarrow> ttbr0 \<Rightarrow> vaddr \<Rightarrow> pt_walk_typ"
where
  "pt_walk_pair asid heap ttbr0 v \<equiv>
      case pdc_walk asid heap ttbr0 v
       of None      \<Rightarrow> Fault           
       | Some pde   \<Rightarrow> (case pde_tlb_entry pde heap v 
                        of  None \<Rightarrow> Partial_Walk pde
                        |   Some tlbentry \<Rightarrow> Full_Walk tlbentry pde)"


definition
  tlb_pdc_walk :: "asid \<Rightarrow> pdc \<Rightarrow> heap \<Rightarrow> ttbr0 \<Rightarrow> vaddr \<Rightarrow>  tlb_entry option set"
where
  "tlb_pdc_walk asid pde_set mem ttbr0 v \<equiv>
      case lookup (tagged_pdc_entry_set pde_set asid) v
          of Hit pde  \<Rightarrow> {pde_tlb_entry pde mem v}
          |  Miss  \<Rightarrow> {pt_walk asid mem ttbr0 v}
          |  Incon \<Rightarrow> (\<lambda>x. pde_tlb_entry x mem v) ` tagged_pdc_entry_set pde_set asid v"


definition
 entry_leq :: " pt_walk_typ \<Rightarrow> pt_walk_typ \<Rightarrow> bool" ("(_/ \<preceq> _)" [51, 51] 50)
 where
 "a \<preceq> b \<equiv> a = Fault \<or> a = b \<or> (\<exists>y. a = Partial_Walk y \<and> (\<exists>x. b = Full_Walk x y))"


definition
 entry_less :: "pt_walk_typ \<Rightarrow> pt_walk_typ \<Rightarrow> bool" ("(_/ \<prec> _)" [51, 51] 50)
 where
 "a \<prec> b = (a \<preceq> b \<and> a \<noteq> b)"


interpretation entry: order entry_leq entry_less
  apply unfold_locales
  by (auto simp: entry_leq_def entry_less_def)

(*  faults  *)

definition
 pairsub :: "'a set \<times> 'b set \<Rightarrow> _"
where
  "pairsub a b = (fst a - fst b , snd a - snd b)"

fun
 pairunion ::  "'a set \<times> 'b set \<Rightarrow> _"
where
  "pairunion (a,b) (c,d) = (a \<union> c , b \<union> d)"




end
