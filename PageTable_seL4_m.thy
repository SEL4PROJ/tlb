(* @LICENSE(NICTA_CORE) *)

(*  Author:     Rafal Kolanski, NICTA & UNSW 

    The seL4 page table on ARMv6. See ASSUMPTIONS.
*)

theory PageTable_seL4_m
imports
  PageTable
  MachineARM
  Heaps
  MapExtra
  Misc
begin

declare map_add_assoc [simp del] (* required for MapExtra *)

text {* 
  The base of the page table is one physical root. 
  This page table structure is the part after the ASID table lookup.
  one for the user side *}
type_synonym ptable_base = paddr

text {*
  ASSUMPTIONS:

  Things I think are always the case in seL4:
  - subpage AP bits disabled (ARMv6 page table format, subpages disabled)
  - don't use extended physical addresses (40-bit address space)
  - don't use domains (domain is always 0)

  *}

text {*
  Conventions:
  A Page Directory is the first level of a two-level page table.
  A Page Table is the second level of a two-level page table.
  Entries are called PDEs for the former and PTEs for the latter.

  Both PDEs and PTEs are the size of a machine word (32 bits)

  The offset is the index into the structure we resolve to when looking up,
  i.e. page index for pages, section index for sections
  *}

text {* Supported page types *}

datatype page_type =
   ArmSmallPage
 | ArmSection


primrec
  page_bits :: "page_type \<Rightarrow> nat"
where
 "page_bits ArmSmallPage    = 12" |
 "page_bits ArmSection      = 20" 

definition
  page_size :: "page_type \<Rightarrow> nat" where
  "page_size page_type \<equiv> 2 ^ (page_bits page_type)"


text {* Offset calculation common to all sizes *}

definition
  vaddr_offset :: "page_type \<Rightarrow> machine_word \<Rightarrow> machine_word" where
  "vaddr_offset p w \<equiv> w AND mask (page_bits p)"

definition
  "page_aligned page_type p = (vaddr_offset page_type p = 0)"

lemma "map (\<lambda>p. vaddr_offset p 0xFEDCBAAA) [ArmSmallPage, ArmSection] = [0xAAA, 0xCBAAA]"
  by (clarsimp simp: vaddr_offset_def mask_def)

text {* Get the non-offset part of an address for a given page size *}
definition
  addr_base :: "page_type \<Rightarrow> machine_word \<Rightarrow> machine_word" where
  "addr_base sz w \<equiv> w AND (NOT mask (page_bits sz))"

lemma "addr_base ArmSmallPage 0xFFFFFFFF = 0xFFFFF000" (* sanity check *)
  unfolding addr_base_def mask_def by simp


text {*
  Permissions bits as per the reference manual. These are not translated into
  anything more abstract, because currently they aren't used in the logic.
  I suppose the best way to go about this is to add another "guard", like a
  permissions guard, rather than fiddling around with a set of flags, since
  on the ARM the permissions decoding is not so straightforward.
  *}

record arm_perm_bits =
    arm_p_APX :: "1 word"
    arm_p_AP  :: "2 word"
    arm_p_TEX :: "3 word"
    arm_p_S   :: "1 word"
    arm_p_XN  :: "1 word"
    arm_p_C   :: "1 word"
    arm_p_B   :: "1 word"
    arm_p_nG  :: "1 word"



section {* Page Directory Entry (PDE) Decoding *}

datatype pde =
   InvalidPDE
 | ReservedPDE
 -- "the paddr is address of a page table"
 | PageTablePDE paddr
 -- "the paddr is base address of section"
 | SectionPDE paddr arm_perm_bits


definition
  perm_bits_pde_sections :: "machine_word \<Rightarrow> arm_perm_bits" where
  "perm_bits_pde_sections w \<equiv> 
     \<lparr> arm_p_APX = ucast ((w >> 15) AND 0x1),
       arm_p_AP  = ucast ((w >> 10) AND 0x3),
       arm_p_TEX = ucast ((w >> 12) AND 0x7),
       arm_p_S   = ucast ((w >> 16) AND 0x1),
       arm_p_XN  = ucast ((w >> 4) AND 0x1),
       arm_p_C   = ucast ((w >> 3) AND 0x1),
       arm_p_B   = ucast ((w >> 2) AND 0x1),
       arm_p_nG  = ucast ((w >> 17) AND 0x1) \<rparr>"

definition
  "decode_pde_section w \<equiv> SectionPDE (Addr (addr_base ArmSection w))
                                     (perm_bits_pde_sections w)"


definition
  pt_base_mask :: machine_word where
  "pt_base_mask \<equiv> NOT (mask 9)" (* FIXME TODO: check *again* that this is right *)
definition
  "decode_pde_pt w \<equiv> PageTablePDE (Addr (w AND pt_base_mask))"

lemma (* sanity check *)
  "pt_base_mask \<equiv> 0xFFFFFE00" unfolding pt_base_mask_def mask_def by simp

definition
  decode_pde :: "machine_word \<Rightarrow> pde" where
  "decode_pde w \<equiv> let pde_type = w AND 0x3
            in
              if pde_type = 1 then (decode_pde_pt w)
              else if pde_type = 2 then decode_pde_section w
              else if pde_type = 3 then ReservedPDE
              else InvalidPDE"

(* update form Hira: changed Option.map to map_option *)
definition
  decode_heap_pde :: "heap \<Rightarrow> paddr \<rightharpoonup> pde" where
  "decode_heap_pde h p \<equiv> 
     map_option decode_pde (load_machine_word h p)"



section {* Page Table Entry (PTE) Decoding *}

datatype pte =
   InvalidPTE
   -- "the paddr is the page base address"
 | SmallPagePTE paddr arm_perm_bits

definition
  perm_bits_pte_small :: "machine_word \<Rightarrow> arm_perm_bits" where
  "perm_bits_pte_small w =
     \<lparr> arm_p_APX = ucast ((w >> 9) AND 0x1),
       arm_p_AP  = ucast ((w >> 4) AND 0x3),
       arm_p_TEX = ucast ((w >> 6) AND 0x7),
       arm_p_S   = ucast ((w >> 10) AND 0x1),
       arm_p_XN  = ucast (w AND 0x1),
       arm_p_C   = ucast ((w >> 3) AND 0x1),
       arm_p_B   = ucast ((w >> 2) AND 0x1),
       arm_p_nG  = ucast ((w >> 11) AND 0x1) \<rparr>"

definition
  "decode_pte_small w \<equiv> SmallPagePTE (Addr (addr_base ArmSmallPage w))
                                     (perm_bits_pte_small w)"



definition
  large_base_mask :: "32 word" where
  "large_base_mask \<equiv> NOT (mask 16)"


lemma (* sanity check *)
  "large_base_mask \<equiv> 0xFFFF0000" by (simp add: large_base_mask_def mask_def)

definition
  decode_pte :: "machine_word \<Rightarrow> pte" where
  "decode_pte w \<equiv> if w AND 3 = 0 
            then InvalidPTE
            else decode_pte_small w"

(* update form Hira: changed Option.map to map_option *)
definition
  decode_heap_pte :: "heap \<Rightarrow> paddr \<rightharpoonup> pte" where
  "decode_heap_pte h p \<equiv> map_option decode_pte (load_machine_word h p)"


section {* Performing a Lookup *}

text {*
  Bits 20-31 of virtual addresses represent an index into the page directory.*}
definition
  vaddr_pd_index :: "machine_word \<Rightarrow> machine_word" where
  "vaddr_pd_index w \<equiv> (w >> 20) AND mask 12"

lemma vaddr_pd_index_simp: "((w::machine_word) >> 20) AND mask 12 = w >> 20"
  by (clarsimp simp: and_mask_eq_iff_shiftr_0 shiftr_shiftr 
                     le_mask_iff[symmetric])
     (unfold mask_def, rule order_trans, rule word_n1_ge, simp)

text {*
  Bits 12-19 of virtual addresses represent an index into the page table. *}
definition
  vaddr_pt_index :: "machine_word \<Rightarrow> machine_word" where
  "vaddr_pt_index w \<equiv> (w >> 12) AND mask 8"


subsection {* Get Frame *}

text {*
  Decode the correct page directory entry from the page directory at some
  physical location given a virtual address to look up.
*}
definition
  get_pde :: "heap \<Rightarrow> paddr \<Rightarrow> vaddr \<rightharpoonup> pde" where
  "get_pde h root vp \<equiv>
     let 
       pd_idx_offset = ((vaddr_pd_index (addr_val vp)) << 2)
     in
       decode_heap_pde h (root r+ pd_idx_offset)"

text {*                  
  Decode the correct page table entry from a page table at some
  physical location given a virtual address to look up.
*}
definition
  get_pte :: "heap \<Rightarrow> paddr \<Rightarrow> vaddr \<rightharpoonup> pte" where
  "get_pte h pt_base vp \<equiv> 
     let 
       pt_idx_offset = ((vaddr_pt_index (addr_val vp)) << 2) 
     in
       decode_heap_pte h (pt_base r+ pt_idx_offset)"

text {*
  The basic lookup mechanism we perform is figuring out the size of the page
  a virtual address is on, then figuring out where in physical memory that
  page maps to.
  *}

definition
  lookup_pte :: "heap \<Rightarrow> paddr \<Rightarrow> vaddr \<rightharpoonup> (paddr \<times> page_type \<times> arm_perm_bits)"
  where
  "lookup_pte h pt_base vp \<equiv>
   case_option None
    (\<lambda>pte. case pte 
             of InvalidPTE \<Rightarrow> None
              | SmallPagePTE base perms \<Rightarrow> Some (base, ArmSmallPage, perms))
    (get_pte h pt_base vp)"

definition
  lookup_pde :: "heap \<Rightarrow> paddr \<Rightarrow> vaddr \<rightharpoonup> (paddr \<times> page_type \<times> arm_perm_bits)"
  where
  "lookup_pde h root vp \<equiv>
   case_option None
    (\<lambda>pde. case pde 
            of InvalidPDE \<Rightarrow> None
             | ReservedPDE \<Rightarrow> None
             | SectionPDE base perms \<Rightarrow> Some (base, ArmSection, perms)
             | PageTablePDE pt_base \<Rightarrow> lookup_pte h pt_base vp)
    (get_pde h root vp)"


subsection {* Get Page *}

text {*
  Find out which page a virtual address is on, along with permissions.

  Getting a page is a bit more complicated with superpages, as we can't really
  ``get a *page*''. So we get the virtual base address of the page *and* 
  the page size. For that, we need to essentially perform a lookup. 
  Once we know the page size, we can just mask it out of the virtual pointer.
  *}

definition
  get_page :: "heap \<Rightarrow> paddr \<Rightarrow> vaddr \<rightharpoonup> (vaddr \<times> page_type \<times> arm_perm_bits)"
  where
  "get_page h root vp \<equiv>
     let
       vp_val = addr_val vp
     in
       map_option 
         (\<lambda>(base, pg_size, perms). (Addr (addr_base pg_size vp_val), 
                                     pg_size, perms))
         (lookup_pde h root vp)"


subsection {* Lookup *}

text {*
  Lookup of a virtual pointer in a Page Table given its base address.
  To obtain the physical address, we get the frame and the page size, 
  then mask in offset bits from the virtual pointer into the frame base
  address.
  *}
definition
  ptable_lift :: "heap \<Rightarrow> paddr \<Rightarrow> vaddr \<rightharpoonup> paddr" where
  "ptable_lift h pt_root vp \<equiv>
     let
       vp_val = addr_val vp
     in
       map_option 
         (\<lambda>(base, pg_size, perms). 
             base r+ (vaddr_offset pg_size vp_val))
         (lookup_pde h pt_root vp)"


subsection {* Trace *}

text {*
  Trace of looking up a virtual pointer in a Page Directory given its base 
  address. *}
definition
  ptable_trace :: "heap \<Rightarrow> paddr \<Rightarrow> vaddr \<Rightarrow> paddr set" where
  "ptable_trace h root vp \<equiv>
     let 
       vp_val = addr_val vp ;
       pd_idx_offset = ((vaddr_pd_index vp_val) << 2) ;
       pt_idx_offset = ((vaddr_pt_index vp_val) << 2) ;
       pd_touched = set (addr_seq (root r+ pd_idx_offset) 4) ;
       pt_touched = (\<lambda>pt_base. set (addr_seq (pt_base r+ pt_idx_offset) 4))
     in
      (case decode_heap_pde h (root r+ pd_idx_offset)
         of Some pde \<Rightarrow> 
              (case pde 
                 of PageTablePDE pt_base \<Rightarrow> pd_touched \<union> pt_touched pt_base
                  | _ \<Rightarrow> pd_touched)
          | None \<Rightarrow> {})"


section {* Properties, Instantiation to pagetable Locale *}

text {* Heap monotonicity and Frame monotonicity for on option result *}

definition
  heap_mono_option :: "(('a \<rightharpoonup> 'b) \<Rightarrow> 'c option) \<Rightarrow> bool" where
  "heap_mono_option f \<equiv> \<forall>h h' v. h \<bottom> h' \<and> f h = Some v \<longrightarrow> f (h ++ h') = Some v"

lemma heap_mono_optionE:
  "\<lbrakk> heap_mono_option f ; f h = Some v ; h \<bottom> h' \<rbrakk> \<Longrightarrow> f (h ++ h') = Some v"
  unfolding heap_mono_option_def by blast

lemma heap_mono_option_simp:
  "\<lbrakk> heap_mono_option f ; f h = Some v ; h \<bottom> h' \<rbrakk> \<Longrightarrow> f (h ++ h') = f h"
  by (frule (2) heap_mono_optionE, simp)

definition
  frame_mono_option :: "(('a \<rightharpoonup> 'b) \<Rightarrow> 'c option) \<Rightarrow> bool" where
  "frame_mono_option f \<equiv> \<forall>h h' v. h \<bottom> h' \<and> f (h ++ h') = Some v 
                           \<longrightarrow> (f h = Some v \<or> f h = None)"

lemma frame_mono_optionE:
  "\<lbrakk> frame_mono_option f ; f (h ++ h') = Some v ; h \<bottom> h' \<rbrakk> 
   \<Longrightarrow> f h = Some v \<or> f h = None"
  unfolding frame_mono_option_def by fastforce


subsection {* Heap monotonicity *}

lemma load_list_basic_heap_mono_simp:
  assumes disj: "h \<bottom> h'"
  assumes some: "\<forall>v \<in> set (load_list_basic h n p). v \<noteq> None"
  shows "load_list_basic (h ++ h') n p = load_list_basic h n p"
  using disj some
proof (induct n arbitrary: p)
  case 0 thus ?case by simp
next
  case (Suc n)
  thus ?case by (clarsimp, subst map_add_eval_left, auto)
qed

lemma Some_set_member:
  assumes some: "None \<notin> S" 
  assumes x: "x \<in> S"
  shows "\<exists>y. x = Some y"
proof -
  { assume a: "x = None"
    hence False using some x by auto
  }
  thus ?thesis by blast
qed

lemma load_list_heap_mono_option:
  "heap_mono_option (\<lambda>h. load_list h n p)"
  unfolding heap_mono_option_def load_list_def
  by (clarify, subst load_list_basic_heap_mono_simp)
     (auto simp: deoption_list_def elim!: Some_set_member split: split_if_asm)

lemmas load_list_heap_mono_simp = heap_mono_option_simp[OF load_list_heap_mono_option]
lemmas load_list_heap_mono = heap_mono_optionE[OF load_list_heap_mono_option]

lemma decode_pde_heap_mono_option:
  "heap_mono_option (\<lambda>h. decode_heap_pde h p)"
  unfolding heap_mono_option_def decode_pde_def decode_heap_pde_def
  by (auto simp: load_machine_word_def load_value_def 
                 load_list_heap_mono Let_def 
           split: option.splits)

lemmas decode_pde_heap_mono_simp = heap_mono_option_simp[OF decode_pde_heap_mono_option]
lemmas decode_pde_heap_mono = heap_mono_optionE[OF decode_pde_heap_mono_option]

lemma decode_pte_heap_mono_option:
  "heap_mono_option (\<lambda>h. decode_heap_pte h p)"
  unfolding heap_mono_option_def decode_pte_def decode_heap_pte_def Let_def
  by (clarsimp simp: load_machine_word_def load_value_def Let_def 
                     load_list_heap_mono
               split: option.splits)
  
lemmas decode_pte_heap_mono_simp = heap_mono_option_simp[OF decode_pte_heap_mono_option]
lemmas decode_pte_heap_mono = heap_mono_optionE[OF decode_pte_heap_mono_option]

lemma lookup_pte_heap_mono_option:
  "heap_mono_option (\<lambda>h. lookup_pte h r vp)"
  unfolding heap_mono_option_def lookup_pte_def get_pte_def Let_def
  by (clarsimp simp: decode_pte_heap_mono split: option.splits)

lemmas lookup_pte_heap_mono_simp = heap_mono_option_simp[OF lookup_pte_heap_mono_option]
lemmas lookup_pte_heap_mono = heap_mono_optionE[OF lookup_pte_heap_mono_option]

lemma lookup_pde_heap_mono_option:
  "heap_mono_option (\<lambda>h. lookup_pde h r vp)"
  unfolding heap_mono_option_def lookup_pde_def get_pde_def Let_def
  by (clarsimp simp: decode_pde_heap_mono lookup_pte_heap_mono 
               split: option.splits pde.splits)

thm heap_mono_option_simp[OF lookup_pde_heap_mono_option]

lemmas lookup_pde_heap_mono_simp = heap_mono_option_simp[OF lookup_pde_heap_mono_option]
lemmas lookup_pde_heap_mono = heap_mono_optionE[OF lookup_pde_heap_mono_option]

lemma ptable_lift_heap_mono_option:
  "heap_mono_option (\<lambda>h. ptable_lift h r vp)"
  unfolding heap_mono_option_def ptable_lift_def Let_def
  by (clarsimp simp: lookup_pde_heap_mono
               split: option.splits pde.splits)

lemmas ptable_lift_heap_mono_simp = heap_mono_option_simp[OF ptable_lift_heap_mono_option]
lemmas ptable_lift_heap_mono = heap_mono_optionE[OF ptable_lift_heap_mono_option]

lemma get_page_heap_mono_option:
  "heap_mono_option (\<lambda>h. get_page h r vp)"
  unfolding heap_mono_option_def get_page_def Let_def
  by (clarsimp simp: lookup_pde_heap_mono split: option.splits)

lemmas get_page_disj_heap_mono_simp = heap_mono_option_simp[OF get_page_heap_mono_option]
lemmas get_page_disj_heap_mono = heap_mono_optionE[OF get_page_heap_mono_option]

text {* Heap monotonicity of ptable_trace works a bit differently as it just
  returns a set, so it depends on ptable_lift's monotonicity *}

(*XXX: fold into not_in_trace_not_in_pde?*)
lemma lift_valid_pde_valid:
  "\<lbrakk> ptable_lift h r vp = Some p \<rbrakk> 
   \<Longrightarrow> decode_heap_pde h (r r+ (vaddr_pd_index (addr_val vp) << 2)) \<noteq> None"
  unfolding ptable_lift_def lookup_pde_def Let_def get_pde_def
  by (auto split: option.splits)

lemma ptable_trace_heap_mono_simp:
  "\<lbrakk> ptable_lift h r vp = Some p ; h \<bottom> h' \<rbrakk>
   \<Longrightarrow> ptable_trace (h ++ h') r vp = ptable_trace h r vp"
  unfolding ptable_trace_def Let_def
  apply (case_tac "decode_heap_pde h (r r+ (vaddr_pd_index (addr_val vp) << 2))")
   apply (drule lift_valid_pde_valid, blast)
  apply (subst decode_pde_heap_mono_simp, assumption+)
  apply simp
  done
(*XXX: any set-like monotonicity properties can be derived from this*)


subsection {* Frame Monotonicity *}

lemma load_list_frame_mono_option:
  "frame_mono_option (\<lambda>h. load_list h n p)"
  unfolding frame_mono_option_def load_list_def
  by (clarsimp simp: deoption_list_def, subst load_list_basic_heap_mono_simp)
     (auto elim: Some_set_member)

lemmas load_list_frame_mono = frame_mono_optionE[OF load_list_frame_mono_option]

lemma decode_pde_frame_mono_option:
  "frame_mono_option (\<lambda>h. decode_heap_pde h p)"
  unfolding frame_mono_option_def decode_pde_def decode_heap_pde_def load_machine_word_def load_value_def
            Let_def
  by (intro allI impI, elim conjE)
     (case_tac "load_list h (size_of TYPE(32 word)) p", 
      auto simp: load_list_heap_mono)

lemmas decode_pde_frame_mono = frame_mono_optionE[OF decode_pde_frame_mono_option]

lemma decode_pte_frame_mono_option:
  "frame_mono_option (\<lambda>h. decode_heap_pte h p)"
  unfolding frame_mono_option_def decode_pte_def decode_heap_pte_def load_machine_word_def load_value_def
            Let_def
  by (intro allI impI, elim conjE)
     (case_tac "load_list h (size_of TYPE(32 word)) p", 
      auto simp: load_list_heap_mono)

lemmas decode_pte_frame_mono = frame_mono_optionE[OF decode_pte_frame_mono_option]

lemma lookup_pte_frame_mono_option:
  "frame_mono_option (\<lambda>h. lookup_pte h r vp)"
  unfolding frame_mono_option_def lookup_pte_def load_machine_word_def 
            load_value_def Let_def get_pte_def
  by (intro allI impI, elim conjE)
     (case_tac "decode_heap_pte h (r r+ (vaddr_pt_index (addr_val vp) << 2))",
      auto simp: decode_pte_heap_mono)

lemmas lookup_pte_frame_mono = frame_mono_optionE[OF lookup_pte_frame_mono_option]

lemma lookup_pde_frame_mono_option:
  "frame_mono_option (\<lambda>h. lookup_pde h r vp)"
  unfolding frame_mono_option_def lookup_pde_def load_machine_word_def 
            load_value_def Let_def get_pde_def
  apply (intro allI impI, elim conjE)
  apply (case_tac "decode_heap_pde h (r r+ (vaddr_pd_index (addr_val vp) << 2))")
   apply simp
  apply simp
  apply (drule (1) decode_pde_heap_mono)
  apply simp
  apply (case_tac a)
      apply (auto elim!: lookup_pte_frame_mono)
  done

lemmas lookup_pde_frame_mono = frame_mono_optionE[OF lookup_pde_frame_mono_option]

lemma ptable_lift_frame_mono_option:
  "frame_mono_option (\<lambda>h. ptable_lift h r vp)"
  unfolding frame_mono_option_def ptable_lift_def Let_def
  apply (intro allI impI, elim conjE)
  apply (case_tac "lookup_pde (h ++ h') r vp", simp)
  apply (frule (1) lookup_pde_frame_mono)
  apply clarsimp
  done

lemmas ptable_lift_frame_mono = frame_mono_optionE[OF ptable_lift_frame_mono_option]

lemma get_page_frame_mono_option:
  "frame_mono_option (\<lambda>h. get_page h r vp)"
  unfolding frame_mono_option_def get_page_def Let_def
  apply (intro allI impI, elim conjE)
  apply (case_tac "lookup_pde (h ++ h') r vp", simp)
  apply (frule (1) lookup_pde_frame_mono)
  apply clarsimp
  done

lemmas get_page_frame_mono = frame_mono_optionE[OF get_page_frame_mono_option]


subsection {* Preservation of trace and lift During Updates Outside a Trace  *}

lemma decode_pde_update_eq:
  "\<lbrakk> p \<notin> set (addr_seq start 4) \<rbrakk>
   \<Longrightarrow> decode_heap_pde (h(p \<mapsto> v)) start = decode_heap_pde h start"
  unfolding decode_pde_def decode_heap_pde_def load_machine_word_def
  by (simp add: load_value_update_eq)

lemma decode_pte_update_eq:
  "\<lbrakk> p \<notin> set (addr_seq start 4) \<rbrakk>
   \<Longrightarrow> decode_heap_pte (h(p \<mapsto> v)) start = decode_heap_pte h start"
  unfolding decode_pte_def decode_heap_pte_def load_machine_word_def
  by (simp add: load_value_update_eq)

lemma not_in_trace_not_in_pde:
  assumes trace: "p \<notin> ptable_trace h r vp"
  assumes lift: "ptable_lift h r vp = Some p"
  shows "p \<notin> set (addr_seq (r r+ (vaddr_pd_index (addr_val vp) << 2)) 4)"
proof -
  from lift 
  obtain pde where 
    "decode_heap_pde h (r r+ (vaddr_pd_index (addr_val vp) << 2)) = Some pde "
    by (auto dest: lift_valid_pde_valid)
  thus ?thesis using trace unfolding ptable_trace_def Let_def
    by (cases pde, auto)
qed

(*XXX:name modified to not conflict with instantiation of locale*)
lemma ptable_trace_preserved':
  "\<lbrakk> p \<notin> ptable_trace h r vp ; ptable_lift h r vp = Some p \<rbrakk> 
  \<Longrightarrow> ptable_trace (h(p \<mapsto> v)) r vp = ptable_trace h r vp"
  apply (frule (1) not_in_trace_not_in_pde)
  apply (unfold ptable_trace_def ptable_lift_def Let_def lookup_pde_def)
  apply (simp add: decode_pde_update_eq)
  done

(*XXX:name modified to not conflict with instantiation of locale*)
lemma ptable_lift_preserved':
  "\<lbrakk> p \<notin> ptable_trace h r vp ; ptable_lift h r vp = Some p \<rbrakk>
    \<Longrightarrow> ptable_lift (h(p \<mapsto> v)) r vp = Some p"
  apply (frule (1) not_in_trace_not_in_pde)
  apply (unfold ptable_trace_def ptable_lift_def lookup_pde_def lookup_pte_def Let_def)
  apply clarsimp
  apply (case_tac "decode_heap_pde h (r r+ (vaddr_pd_index (addr_val vp) << 2))")
   apply (simp add: get_pde_def)
  apply (rule_tac x=a and y=aa in exI2)
  apply clarsimp
  apply (rename_tac pde)
  apply (case_tac pde)
      apply (clarsimp simp: get_pde_def get_pte_def Let_def 
                            decode_pde_update_eq decode_pte_update_eq)+
  done
  (*XXX: shorter, but still ugly proof*)

interpretation (*XXX: no requirements on get_page so ignored in proof, but is it taken into account for the interpretation?*)
  pagetable ptable_lift ptable_trace get_page
  by (unfold_locales)
     (auto elim!: ptable_lift_heap_mono ptable_lift_frame_mono
                  ptable_trace_heap_mono_simp
                  ptable_lift_preserved' ptable_trace_preserved')

end
