theory MMU_Prg_Logic

imports  "../MMU_ARM"
        

begin

type_synonym val        = "32 word"
type_synonym word_type  = "32 word"
type_synonym heap  = "paddr \<rightharpoonup> 32 word"
type_synonym rootreg    = "32 word"    (* should we take 32 word only as now we are abstracting logic 
                                   without the details of machine *)

record p_state =
  MEM   :: "paddr \<rightharpoonup> word_type"  (* partial function, none for exceptions. 32 bit output type as this is a dummy language *)
  ASID  :: asid 
  TTBR0 :: "paddr"   (* can be paddr as well *)
  incon_set :: "(asid \<times> 32 word) set"


definition 
  load_list_word_hp :: "heap \<Rightarrow> nat \<Rightarrow> paddr \<rightharpoonup> val list"
where
  "load_list_word_hp h n p = load_list h n p"

definition
  from_word :: "32 word list => 'b :: len0 word" where
  "from_word \<equiv> word_rcat \<circ> rev"

definition 
  load_value_word_hp :: "heap \<Rightarrow> paddr \<rightharpoonup> val"
where
  "load_value_word_hp h p = map_option from_word (load_list_word_hp h 4 p)"


definition 
  mem_read_word_heap :: "paddr \<Rightarrow> p_state \<rightharpoonup> word_type"
where
  "mem_read_word_heap p s = load_value_word_hp (p_state.MEM s) p "
          

definition
  decode_heap_pde' :: "heap \<Rightarrow> paddr \<rightharpoonup> pde" where
  "decode_heap_pde' h p \<equiv> 
     map_option decode_pde ( h p)"

definition
  get_pde' :: "heap \<Rightarrow> paddr \<Rightarrow> vaddr \<rightharpoonup> pde" where
  "get_pde' h root vp \<equiv>
     let 
       pd_idx_offset = ((vaddr_pd_index (addr_val vp)) << 2)
     in
       decode_heap_pde' h (root r+ pd_idx_offset)"

definition
  decode_heap_pte' :: "heap \<Rightarrow> paddr \<rightharpoonup> pte" where
  "decode_heap_pte' h p \<equiv> map_option decode_pte (h p)"


definition
  get_pte' :: "heap \<Rightarrow> paddr \<Rightarrow> vaddr \<rightharpoonup> pte" where
  "get_pte' h pt_base vp \<equiv> 
     let 
       pt_idx_offset = ((vaddr_pt_index (addr_val vp)) << 2) 
     in
       decode_heap_pte' h (pt_base r+ pt_idx_offset)"


definition
  lookup_pte' :: "heap \<Rightarrow> paddr \<Rightarrow> vaddr \<rightharpoonup> (paddr \<times> page_type \<times> arm_perm_bits)"
  where
  "lookup_pte' h pt_base vp \<equiv>
   case_option None
    (\<lambda>pte. case pte 
             of InvalidPTE \<Rightarrow> None
              | SmallPagePTE base perms \<Rightarrow> Some (base, ArmSmallPage, perms))
    (get_pte' h pt_base vp)"


definition
  lookup_pde' :: "heap \<Rightarrow> paddr \<Rightarrow> vaddr \<rightharpoonup> (paddr \<times> page_type \<times> arm_perm_bits)"
  where
  "lookup_pde' h root vp \<equiv>
   case_option None
    (\<lambda>pde. case pde 
            of InvalidPDE \<Rightarrow> None
             | ReservedPDE \<Rightarrow> None
             | SectionPDE base perms \<Rightarrow> Some (base, ArmSection, perms)
             | PageTablePDE pt_base \<Rightarrow> lookup_pte' h pt_base vp)
    (get_pde' h root vp)"


definition
  ptable_lift' :: "heap \<Rightarrow> paddr \<Rightarrow> vaddr \<rightharpoonup> paddr" where
  "ptable_lift' h pt_root vp \<equiv>
     let
       vp_val = addr_val vp
     in
       map_option 
         (\<lambda>(base, pg_size, perms). 
             base r+ (vaddr_offset pg_size vp_val))
         (lookup_pde' h pt_root vp)"


definition
  mem_read_hp :: "heap \<Rightarrow> paddr \<Rightarrow> vaddr \<rightharpoonup> val"
where
  "mem_read_hp hp root vp =  (ptable_lift' hp root \<rhd>o load_value_word_hp hp) vp" 




end