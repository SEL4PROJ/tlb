theory MMU_Prg_Logic

imports
     "HOL-Word.Word" 
     PTABLE_TLBJ.PageTable_seL4
     "./../Eisbach/Rule_By_Method"

begin

type_synonym val         = "32 word"
type_synonym asid        = "8 word"
type_synonym word_t      = "32 word"
type_synonym heap        = "paddr \<rightharpoonup> word_t"
type_synonym incon_set   = "vaddr set"
type_synonym global_set   = "vaddr set"

datatype mode_t = Kernel | User


type_synonym vSm = "20 word"
type_synonym pSm = "20 word"

type_synonym vSe = "12 word"
type_synonym pSe = "12 word"

record tlb_flags =
  nG       :: "1 word"  (* nG = 0 means global *) 
  perm_APX :: "1 word"  (* Access permission bit 2 *)
  perm_AP  :: "2 word"  (* Access permission bits 1 and 0 *)
  perm_XN  :: "1 word"  (* Execute-never bit *)

datatype pdc_entry =  PDE_Section "asid option" "12 word" (bpa_pdc_entry :"32 word") tlb_flags
                   |  PDE_Table   asid          "12 word" (bpa_pdc_entry : "32 word")


datatype tlb_entry = EntrySmall    (asid_of : "asid option") vSm pSm tlb_flags
                   | EntrySection  (asid_of : "asid option") vSe pSe tlb_flags

datatype pt_walk_typ = Fault 
                     | Partial_Walk pdc_entry
                     | Full_Walk tlb_entry pdc_entry

type_synonym ptable_snapshot   = "asid \<Rightarrow> (vaddr set \<times> (vaddr \<Rightarrow> pt_walk_typ))"

record p_state =
  heap      :: heap
  asid      :: asid 
  root      :: paddr
  incon_set :: incon_set
  global_set :: global_set
  ptable_snapshot :: ptable_snapshot
  mode      :: mode_t

  
definition
  load_list_word_hp :: "heap \<Rightarrow> nat \<Rightarrow> paddr \<rightharpoonup> val list"
where
  "load_list_word_hp h n p = load_list h n p"


definition
  from_word :: "32 word list => 'b :: len0 word" 
where
  "from_word \<equiv> word_rcat \<circ> rev"

definition
  load_value_word_hp :: "heap \<Rightarrow> paddr \<rightharpoonup> val"
where
  "load_value_word_hp h p = map_option from_word (load_list_word_hp h 1 p)"


definition
  mem_read_word_heap :: "paddr \<Rightarrow> p_state \<rightharpoonup> word_t"
where
  "mem_read_word_heap p s = load_value_word_hp (heap s) p "


definition
  decode_heap_pde' :: "heap \<Rightarrow> paddr \<rightharpoonup> pde"
where
"decode_heap_pde' h p \<equiv> map_option decode_pde (h p)"

definition
  get_pde' :: "heap \<Rightarrow> paddr \<Rightarrow> vaddr \<rightharpoonup> pde" 
where
  "get_pde' h rt vp \<equiv>
        let
          pd_idx_offset = ((vaddr_pd_index (addr_val vp)) << 2)
        in
          decode_heap_pde' h (rt r+ pd_idx_offset)"

definition
  decode_heap_pte' :: "heap \<Rightarrow> paddr \<rightharpoonup> pte" 
where
  "decode_heap_pte' h p \<equiv> map_option decode_pte (h p)"


definition
  get_pte' :: "heap \<Rightarrow> paddr \<Rightarrow> vaddr \<rightharpoonup> pte" 
where
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
  "lookup_pde' h rt vp \<equiv>
      case_option None
       (\<lambda>pde. case pde
               of InvalidPDE \<Rightarrow> None
                | ReservedPDE \<Rightarrow> None
                | SectionPDE base perms \<Rightarrow> Some (base, ArmSection, perms)
                | PageTablePDE pt_base \<Rightarrow> lookup_pte' h pt_base vp)
       (get_pde' h rt vp)"


(* page table look-up *) 

definition
  ptable_lift' :: "heap \<Rightarrow> paddr \<Rightarrow> vaddr \<rightharpoonup> paddr" 
where
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
     "mem_read_hp hp rt vp =  (ptable_lift' hp rt \<rhd>o load_value_word_hp hp) vp"


definition 
  ptable_trace' :: "heap \<Rightarrow> paddr \<Rightarrow> vaddr \<Rightarrow> paddr set" 
where
  "ptable_trace' h rt vp \<equiv>
        let
          vp_val = addr_val vp ;
          pd_idx_offset = ((vaddr_pd_index vp_val) << 2) ;
          pt_idx_offset = ((vaddr_pt_index vp_val) << 2) ;
          pd_touched = {rt r+ pd_idx_offset};
          pt_touched = (\<lambda>pt_base. {pt_base r+ pt_idx_offset})
        in
         (case decode_pde (the (h (rt r+ pd_idx_offset)))
            of  PageTablePDE pt_base \<Rightarrow> pd_touched \<union> pt_touched pt_base
                 | _ \<Rightarrow> pd_touched)"

definition 
  pde_trace' :: "heap \<Rightarrow> paddr \<Rightarrow> vaddr \<rightharpoonup> paddr" 
where
  "pde_trace' h rt vp \<equiv>
        let
          vp_val = addr_val vp ;
          pd_idx_offset = ((vaddr_pd_index vp_val) << 2) ;
          pd_touched = rt r+ pd_idx_offset
        in
         (case decode_heap_pde' h (rt r+ pd_idx_offset)
            of Some pde \<Rightarrow>  Some pd_touched
             | None \<Rightarrow> None)"


lemma ptlift_trace_some:
  "ptable_lift' h r vp = Some pa \<Longrightarrow>  ptable_trace' h r vp \<noteq> {}"
  by (clarsimp simp: ptable_lift'_def lookup_pde'_def  get_pde'_def ptable_trace'_def Let_def
          split:option.splits pde.splits)


lemma ptable_lift_preserved':
  " \<lbrakk>p \<notin> ptable_trace' h r vp; ptable_lift' h r  vp = Some pa\<rbrakk> \<Longrightarrow> ptable_lift' (h(p \<mapsto> v)) r  vp = Some pa"
  apply (frule ptlift_trace_some , clarsimp simp: ptable_lift'_def lookup_pde'_def get_pde'_def ptable_trace'_def Let_def split: option.splits)
  apply (case_tac x2; clarsimp simp: decode_heap_pde'_def lookup_pte'_def split: option.splits)
  apply (case_tac x2a ; clarsimp)
  apply (rule conjI)
   apply (rule_tac x = "(SmallPagePTE a b)" in exI, clarsimp simp: get_pte'_def decode_heap_pte'_def , clarsimp)
  by (case_tac x2 ; clarsimp simp:get_pte'_def decode_heap_pte'_def)



lemma ptable_trace_get_pde:
  "\<lbrakk>p \<notin> ptable_trace' h r x;  get_pde' h r x = Some pde\<rbrakk>  \<Longrightarrow> 
                   get_pde' (h(p \<mapsto> v)) r x = Some pde"
  apply (clarsimp simp: ptable_trace'_def Let_def get_pde'_def decode_heap_pde'_def )
  by (case_tac " decode_pde z" ; clarsimp)


lemma ptable_trace_preserved':
  "\<lbrakk>ptable_lift' h r vp = Some pb; p \<notin> ptable_trace' h r vp;
          pa \<notin> ptable_trace' h r vp \<rbrakk>  \<Longrightarrow>  pa \<notin> ptable_trace' (h(p \<mapsto> v)) r vp"
  apply (frule ptlift_trace_some)
  apply (subgoal_tac "ptable_trace' (h(p \<mapsto> v)) r vp \<noteq> {}")
   prefer 2
   apply (clarsimp simp: ptable_lift'_def lookup_pde'_def get_pde'_def ptable_trace'_def Let_def split: option.splits)
   apply (case_tac x2 ; clarsimp simp:  decode_heap_pde'_def)
  by (clarsimp simp: ptable_lift'_def lookup_pde'_def get_pde'_def decode_heap_pde'_def ptable_trace'_def Let_def split: option.splits pde.splits)


lemma ptable_trace_get_pde':
  "\<lbrakk> get_pde' (h(p \<mapsto> v)) r x = Some pde; p \<notin> ptable_trace' h r x \<rbrakk>  \<Longrightarrow> 
                  get_pde' h r x = Some pde "
  apply (clarsimp simp: ptable_trace'_def Let_def get_pde'_def decode_heap_pde'_def )
  by (case_tac " decode_pde (the (h (r r+ (vaddr_pd_index (addr_val x) << 2))))" ; clarsimp)


lemma  [simp]:
  "get_pde' h r va = Some (SectionPDE p perms) \<Longrightarrow> 
  decode_pde (the (h 
          (r r+ (vaddr_pd_index (addr_val va) << 2)))) =  SectionPDE p perms  "
  by (clarsimp simp: get_pde'_def decode_heap_pde'_def)



lemma pt_table_lift_trace_upd'':
  "p \<notin> ptable_trace' h r x \<Longrightarrow> ptable_lift' (h(p \<mapsto> v)) r  x = ptable_lift' h r  x"
  apply (clarsimp simp: ptable_trace'_def Let_def ptable_lift'_def lookup_pde'_def get_pde'_def)
  apply (subgoal_tac "decode_heap_pde' (h(p \<mapsto> v)) (r r+ (vaddr_pd_index (addr_val x) << 2)) =
   decode_heap_pde' h (r r+ (vaddr_pd_index (addr_val x) << 2))")
   apply clarsimp
   apply (clarsimp simp: decode_heap_pde'_def)
   apply (clarsimp split: option.splits)
   apply (clarsimp split: pde.splits)
   apply (clarsimp simp: lookup_pte'_def get_pte'_def)
   apply (subgoal_tac "decode_heap_pte' (h(p \<mapsto> v)) (x3 r+ (vaddr_pt_index (addr_val x) << 2)) =
    decode_heap_pte' h (x3 r+ (vaddr_pt_index (addr_val x) << 2))")
    apply (clarsimp)
   apply (clarsimp simp: decode_heap_pte'_def)
  by (clarsimp simp: decode_heap_pde'_def decode_pde_def Let_def split: pde.splits)


(* page table look-up with mode and access permissions *) 
 
definition
  "user_perms perms  = (arm_p_AP perms = 0x2 \<or> arm_p_AP perms = 0x3)"

definition
  "filter_pde  m =    (\<lambda>x. case x of None \<Rightarrow> None
                           |  Some (base, pg_size, perms) \<Rightarrow>
                              if (m = Kernel) \<or> (m = User \<and> user_perms perms)
                               then Some (base, pg_size, perms)
                               else None) "

definition
  lookup_pde_perm :: "heap \<Rightarrow> paddr \<Rightarrow> mode_t \<Rightarrow> vaddr \<rightharpoonup> (paddr \<times> page_type \<times> arm_perm_bits)"
where
  "lookup_pde_perm h r m vp = filter_pde m (lookup_pde' h r vp)"

definition
  ptable_lift_m :: "heap \<Rightarrow> paddr \<Rightarrow> mode_t \<Rightarrow> vaddr \<rightharpoonup> paddr"
where
  "ptable_lift_m h r m vp \<equiv>
           map_option  (\<lambda>(base, pg_size, perms).  base r+ (vaddr_offset pg_size (addr_val vp)))
                         (lookup_pde_perm h r m vp) "


lemma lookup_pde_kernel[simp]:
  "lookup_pde_perm h r Kernel vp = lookup_pde' h r vp"
  by(clarsimp simp: lookup_pde_perm_def filter_pde_def split:option.splits)


lemma  [simp]:
  "ptable_lift_m h r Kernel va =  ptable_lift' h r va"
  by (clarsimp simp: ptable_lift_m_def ptable_lift'_def )


lemma  ptable_lift_m_user [simp]:
  "ptable_lift_m h r  User va = Some pa \<Longrightarrow>
  ptable_lift_m h r  User va =  ptable_lift' h r va"
  by (clarsimp simp: ptable_lift_m_def ptable_lift'_def lookup_pde_perm_def filter_pde_def split: option.splits if_split_asm)



lemma ptlift_trace_some':
  "ptable_lift_m h r m vp = Some pa \<Longrightarrow>  ptable_trace' h r vp \<noteq> {}"
  by (case_tac m , simp add:  ptlift_trace_some , simp, frule ptable_lift_m_user, simp add: ptlift_trace_some)


lemma ptable_trace_preserved_m:
  "\<lbrakk>ptable_lift_m h r m vp = Some pb; p \<notin> ptable_trace' h r vp;
  pa \<notin> ptable_trace' h r vp \<rbrakk>  \<Longrightarrow>  pa \<notin> ptable_trace' (h(p \<mapsto> v)) r vp"
  by (case_tac m ,simp add: ptable_trace_preserved', simp, frule ptable_lift_m_user, simp add: ptable_trace_preserved')

lemma  ptable_lift_user_implies_ptable_lift:
  "ptable_lift_m h r User va = Some pa \<Longrightarrow> ptable_lift' h r va = Some pa"
  by (clarsimp simp: ptable_lift_m_def lookup_pde_perm_def filter_pde_def 
         ptable_lift'_def split:option.splits if_split_asm)


lemma ptable_lift_preserved_m:
  "\<lbrakk>p \<notin> ptable_trace' h r vp; ptable_lift_m h r m vp = Some pa\<rbrakk> \<Longrightarrow> ptable_lift_m (h(p \<mapsto> v)) r m vp = Some pa"
  apply (case_tac m ; simp add: ptable_lift_preserved')
  apply (frule ptable_lift_m_user ; simp)
  apply (frule_tac pa = pa and v = v in  ptable_lift_preserved' , simp)
  apply (clarsimp simp:  ptable_trace'_def Let_def ptable_lift'_def lookup_pde'_def get_pde'_def split: option.splits)
     apply (case_tac x2 ; clarsimp)
      prefer 2
      apply (clarsimp simp:  decode_heap_pde'_def)
      apply (clarsimp simp: ptable_lift_m_def lookup_pde'_def get_pde'_def decode_heap_pde'_def lookup_pde_perm_def filter_pde_def)
     apply (clarsimp simp:  ptable_lift_m_def lookup_pde'_def get_pde'_def lookup_pde_perm_def filter_pde_def lookup_pte'_def get_pte'_def decode_heap_pte'_def
                            split:if_split_asm split: option.splits)
     by (case_tac "decode_pte x2" ; clarsimp simp: decode_heap_pde'_def lookup_pte'_def get_pte'_def decode_heap_pte'_def)


lemma ptable_lift_m_implies_ptlift:
  "ptable_lift_m (heap s) (root s) (mode s) (Addr vp) = Some p \<Longrightarrow> ptable_lift' (heap s) (root s) (Addr vp) = Some p"
  by (clarsimp simp: ptable_lift_m_def ptable_lift'_def lookup_pde_perm_def filter_pde_def user_perms_def split: option.splits if_split_asm)


lemma union_imp_all:
     "p \<notin> \<Union>(ptable_trace' h r ` UNIV) \<Longrightarrow> \<forall>x. p \<notin> ptable_trace' h r x"
     by (clarsimp)


  (* Mapped page table, used for later in the kernel execution  *)
definition
  ptable_mapped :: "heap \<Rightarrow> paddr \<Rightarrow> vaddr set"
where
  "ptable_mapped h r  \<equiv>   {va. \<exists>p. ptable_lift' h r va = Some p \<and>  p \<in> \<Union>(ptable_trace' h r ` UNIV) } "



(*  Memory Operations for Logic  *)


definition
  mem_read_hp' :: "vaddr set \<Rightarrow> heap \<Rightarrow> paddr \<Rightarrow> mode_t \<Rightarrow> vaddr \<rightharpoonup> val"
where
  "mem_read_hp'  iset hp rt m vp \<equiv>  if vp \<notin> iset then
        (ptable_lift_m hp rt m \<rhd>o load_value_word_hp hp) vp else None"



definition "pagetable_lookup \<equiv> ptable_lift_m"


definition
  if_filter :: "bool \<Rightarrow> 'a option \<rightharpoonup> 'a" (infixl "\<then>" 55)
where
  "if_filter a b \<equiv> if a then b else None"


definition
  "physical_address iset hp rt m va \<equiv> (va \<notin> iset) \<then> pagetable_lookup hp rt m va"


definition
  mem_read_hp'' :: "vaddr set \<Rightarrow> heap \<Rightarrow> paddr \<Rightarrow> mode_t \<Rightarrow> vaddr \<rightharpoonup> val"
where
  "mem_read_hp'' iset hp rt m va \<equiv>
    (physical_address iset hp rt m \<rhd>o load_value_word_hp hp) va"

definition
  "fun_update' f g v  \<equiv>
      case f  of Some y \<Rightarrow> Some (g (y \<mapsto> v))
         | None \<Rightarrow> None "



definition
  mem_write :: "vaddr set \<Rightarrow> heap \<Rightarrow> paddr \<Rightarrow> mode_t \<Rightarrow> vaddr \<Rightarrow> val \<rightharpoonup> heap"
where
  "mem_write iset hp rt m va v \<equiv>
    fun_update' (physical_address iset hp rt m va) hp v "


(*Flush Operations for incon_set  *)

datatype flush_type = flushTLB
                    | flushASID    asid
                    | flushvarange "vaddr set"
                    | flushASIDvarange  asid "vaddr set"








(* ptable_comp function *)


fun word_bits :: "nat \<Rightarrow> nat \<Rightarrow> 'a::len word \<Rightarrow> 'a::len word" where
  "word_bits h l w = (w >> l) AND mask (Suc h - l)"

fun word_extract :: "nat \<Rightarrow> nat \<Rightarrow> 'a::len word \<Rightarrow> 'b::len word" where
  "word_extract h l w = ucast (word_bits h l w)"

definition
  to_tlb_flags :: "arm_perm_bits \<Rightarrow> tlb_flags"
where
  "to_tlb_flags perms \<equiv> \<lparr>nG = arm_p_nG perms, perm_APX = arm_p_APX perms,  perm_AP = arm_p_AP perms, perm_XN = arm_p_XN perms \<rparr>"

definition "tag_conv (a::asid) fl \<equiv> (if  nG fl = 0 then None else Some a)"


definition 
 pdc_walk :: "asid \<Rightarrow> heap \<Rightarrow> paddr \<Rightarrow> vaddr \<Rightarrow> pdc_entry option"
where
  "pdc_walk a hp rt v \<equiv>
      case get_pde' hp rt v
       of Some (SectionPDE p perms) \<Rightarrow> Some (PDE_Section 
                                             (tag_conv a (to_tlb_flags perms))
                                             (ucast (addr_val v >> 20) :: 12 word) 
                                             (addr_val p) 
                                             (to_tlb_flags perms))
       |  Some (PageTablePDE p) \<Rightarrow> Some (PDE_Table a (ucast (addr_val v >> 20) :: 12 word) (addr_val p))
       |  _ \<Rightarrow> None" 


definition
  pte_tlb_entry :: "asid \<Rightarrow> heap \<Rightarrow> paddr \<Rightarrow> vaddr \<Rightarrow>  tlb_entry option"
where
  "pte_tlb_entry a hp p v \<equiv> case get_pte' hp p v 
                 of Some (SmallPagePTE p' perms) \<Rightarrow> Some (EntrySmall (tag_conv a (to_tlb_flags perms))
                                                                     (ucast (addr_val v >> 12) :: 20 word)
                                                                     ((word_extract 31 12 (addr_val p')):: 20 word)
                                                                     (to_tlb_flags perms))
                 |  _                        \<Rightarrow> None"


fun
  pde_tlb_entry :: "pdc_entry \<Rightarrow> heap  \<Rightarrow> vaddr \<Rightarrow>  tlb_entry option"
where
  "pde_tlb_entry (PDE_Section a vba pba flags) mem va = Some (EntrySection a (ucast (addr_val va >> 20) :: 12 word) ((ucast (pba >> 20)) :: 12 word)  flags)"
| "pde_tlb_entry (PDE_Table   a vba pba)       mem va = pte_tlb_entry a mem (Addr pba) va"



definition
 map_opt :: "('a \<Rightarrow> 'b option) \<Rightarrow> 'a option \<Rightarrow> 'b option"
where
  "map_opt f x  \<equiv> case x of None  \<Rightarrow> None | Some y  \<Rightarrow> f y"


definition
 pt_walk :: "asid \<Rightarrow> heap \<Rightarrow> paddr \<Rightarrow> vaddr \<Rightarrow> tlb_entry option"
where
  "pt_walk a m r v \<equiv> map_opt (\<lambda>pde. pde_tlb_entry pde m v) (pdc_walk a m r v)"
     

definition
 pt_walk_pair :: "asid \<Rightarrow> heap \<Rightarrow> paddr \<Rightarrow> vaddr \<Rightarrow> pt_walk_typ"
where
  "pt_walk_pair a mem ttbr0 v \<equiv>
      case pdc_walk a mem  ttbr0 v
       of None      \<Rightarrow> Fault           
       | Some pde   \<Rightarrow> (case pde_tlb_entry pde mem v 
                        of  None \<Rightarrow> Partial_Walk pde
                        |   Some tlbentry \<Rightarrow> Full_Walk tlbentry pde)"


definition
 entry_leq :: "pt_walk_typ \<Rightarrow> pt_walk_typ \<Rightarrow> bool" ("(_/ \<preceq> _)" [51, 51] 50)
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
  "is_fault e \<equiv> (e = None)"


definition
  ptable_comp :: "(vaddr \<Rightarrow> pt_walk_typ) \<Rightarrow> (vaddr \<Rightarrow> pt_walk_typ) \<Rightarrow> vaddr set"
where
  "ptable_comp walk walk'  \<equiv> {va. \<not>(walk va \<preceq> walk' va)}"

definition
  incon_comp :: "asid \<Rightarrow> asid \<Rightarrow> heap \<Rightarrow> heap \<Rightarrow> paddr \<Rightarrow> paddr \<Rightarrow> vaddr set"
where
  "incon_comp a a' hp hp' rt rt' \<equiv> ptable_comp (pt_walk_pair a hp rt) (pt_walk_pair a' hp' rt')"


lemma ptable_trace_pde_comp:
  "\<forall>x. p \<notin> ptable_trace' h r x \<Longrightarrow> incon_comp a a  h (h(p \<mapsto> v)) r  r= {}"
  apply (clarsimp simp: ptable_trace'_def incon_comp_def ptable_comp_def Let_def)
  apply (drule_tac x = x in spec)                                                                
  apply (clarsimp simp: entry_leq_def pt_walk_pair_def pdc_walk_def  pte_tlb_entry_def get_pde'_def
                        decode_heap_pde'_def decode_pde_def  split: option.splits pde.splits pte.splits)
 using Let_def apply auto [1]
     apply (clarsimp simp: Let_def split: if_split_asm)  
     apply (clarsimp simp: Let_def split: if_split_asm)
  using Let_def apply auto [1]
     apply (clarsimp simp: Let_def split: if_split_asm)   
    apply (clarsimp simp: Let_def split: if_split_asm)
 using Let_def apply auto [1]
   apply (clarsimp simp: Let_def pte_tlb_entry_def get_pte'_def decode_heap_pte'_def  split: if_split_asm option.splits pte.splits)   
  apply (clarsimp simp: Let_def pte_tlb_entry_def get_pte'_def decode_heap_pte'_def  split: if_split_asm option.splits pte.splits)
  using Let_def apply auto [1]
 apply (clarsimp simp: Let_def pte_tlb_entry_def get_pte'_def decode_heap_pte'_def   split: if_split_asm option.splits pte.splits) +
done


lemma pde_comp_empty:
  "p \<notin> \<Union>(ptable_trace' h r ` UNIV) \<Longrightarrow> incon_comp a a h (h(p \<mapsto> v)) r r = {}"
  apply (drule union_imp_all)
  by (clarsimp simp: ptable_trace_pde_comp)


lemma plift_equal_not_in_pde_comp [simp]:
  "\<lbrakk>pt_walk_pair a h r va =  e ; pt_walk_pair a h' r va = e \<rbrakk> \<Longrightarrow>
            va \<notin> incon_comp a a h h' r r"
  by (clarsimp simp: incon_comp_def ptable_comp_def)


lemma pt_walk_pair_pt_trace_upd:
  "p \<notin> ptable_trace' h r x \<Longrightarrow> pt_walk_pair a h r x = pt_walk_pair a (h(p \<mapsto> v)) r x"
  apply (clarsimp simp: ptable_trace'_def Let_def pt_walk_pair_def pdc_walk_def)
  apply (subgoal_tac "get_pde' h r x = get_pde' (h(p \<mapsto> v)) r x" , clarsimp)
   apply (cases "get_pde' (h(p \<mapsto> v)) r x" ;clarsimp)
   apply (case_tac aa ; clarsimp simp: pte_tlb_entry_def)
   apply (subgoal_tac "get_pte' h x3 x = get_pte' (h(p \<mapsto> v)) x3 x")
    apply clarsimp
   apply (clarsimp simp: get_pde'_def decode_heap_pde'_def get_pte'_def decode_heap_pte'_def)
  by (clarsimp simp: get_pde'_def decode_heap_pde'_def Let_def split: pde.splits)

lemma pt_walk_pt_trace_upd:
  "p \<notin> ptable_trace' h r x \<Longrightarrow> pt_walk a h r x = pt_walk a (h(p \<mapsto> v)) r x"
  apply (clarsimp simp: ptable_trace'_def Let_def pt_walk_def pdc_walk_def map_opt_def)
  apply (subgoal_tac "get_pde' h r x = get_pde' (h(p \<mapsto> v)) r x" , clarsimp)
   apply (cases "get_pde' (h(p \<mapsto> v)) r x" ;clarsimp)
   apply (case_tac aa ; clarsimp simp: pte_tlb_entry_def)
   apply (subgoal_tac "get_pte' h x3 x = get_pte' (h(p \<mapsto> v)) x3 x")
    apply clarsimp
   apply (clarsimp simp: get_pde'_def decode_heap_pde'_def get_pte'_def decode_heap_pte'_def)
  by (clarsimp simp: get_pde'_def decode_heap_pde'_def Let_def split: pde.splits)


lemma  pt_trace_upd:
  "p \<notin> ptable_trace' h r x \<Longrightarrow> ptable_trace' (h (p \<mapsto> v)) r x = ptable_trace' h r x"
  by (clarsimp simp:  ptable_trace'_def Let_def split: pde.splits)


lemma pt_table_lift_trace_upd:
  "p \<notin> ptable_trace' h r x \<Longrightarrow> ptable_lift_m (h(p \<mapsto> v)) r m x = ptable_lift_m h r m x"
  apply (clarsimp simp: ptable_trace'_def Let_def ptable_lift_m_def
                        lookup_pde_perm_def lookup_pde'_def get_pde'_def)
  apply (subgoal_tac "decode_heap_pde' (h(p \<mapsto> v)) (r r+ (vaddr_pd_index (addr_val x) << 2)) =
                      decode_heap_pde' h (r r+ (vaddr_pd_index (addr_val x) << 2))")
   apply clarsimp
   apply (clarsimp simp: decode_heap_pde'_def)
   apply (clarsimp split: option.splits)
   apply (clarsimp split: pde.splits)
   apply (clarsimp simp: lookup_pte'_def get_pte'_def)
   apply (subgoal_tac "decode_heap_pte' (h(p \<mapsto> v)) (x3 r+ (vaddr_pt_index (addr_val x) << 2)) =
                       decode_heap_pte' h (x3 r+ (vaddr_pt_index (addr_val x) << 2))")
    apply (clarsimp)
   apply (clarsimp simp: decode_heap_pte'_def)
  by (clarsimp simp: decode_heap_pde'_def decode_pde_def Let_def split: pde.splits)


lemma pt_table_lift_trace_upd':
  "p \<notin> ptable_trace' h r x \<Longrightarrow>  ptable_lift' h r  x = ptable_lift' (h(p \<mapsto> v)) r  x"
  apply (clarsimp simp: ptable_trace'_def Let_def ptable_lift'_def
  lookup_pde_perm_def lookup_pde'_def get_pde'_def)
  apply (subgoal_tac "decode_heap_pde' (h(p \<mapsto> v)) (r r+ (vaddr_pd_index (addr_val x) << 2)) =
   decode_heap_pde' h (r r+ (vaddr_pd_index (addr_val x) << 2))")
   apply clarsimp
   apply (clarsimp simp: decode_heap_pde'_def)
   apply (clarsimp split: option.splits)
   apply (clarsimp split: pde.splits)
   apply (clarsimp simp: lookup_pte'_def get_pte'_def)
   apply (subgoal_tac "decode_heap_pte' (h(p \<mapsto> v)) (x3 r+ (vaddr_pt_index (addr_val x) << 2)) =
    decode_heap_pte' h (x3 r+ (vaddr_pt_index (addr_val x) << 2))")
    apply (clarsimp)
   apply (clarsimp simp: decode_heap_pte'_def)
  by (clarsimp simp: decode_heap_pde'_def decode_pde_def Let_def split: pde.splits)


lemma pt_walk_pt_trace_upd':
  "p \<notin> ptable_trace' h r x \<Longrightarrow> pt_walk a (h(p \<mapsto> v)) r x = pt_walk a h r x"
  using pt_walk_pt_trace_upd by auto

lemma pt_walk_pair_pt_trace_upd':
  "p \<notin> ptable_trace' h r x \<Longrightarrow> pt_walk_pair a (h(p \<mapsto> v)) r x = pt_walk_pair a h r x"
  using pt_walk_pair_pt_trace_upd by auto

lemma no_fault_pt_walk_no_fault_pdc_walk:
  "\<not>is_fault (pt_walk a m r va) \<Longrightarrow> \<not>is_fault (pdc_walk a m r va)"
  by (clarsimp simp: is_fault_def pt_walk_def map_opt_def split: option.splits)

lemma pt_walk_pair_no_fault_pdc_walk:
  "\<lbrakk>pt_walk_pair a m rt v = Full_Walk entry entry'\<rbrakk> \<Longrightarrow> pdc_walk a m rt v = Some entry'"
  by (clarsimp simp: pt_walk_pair_def pdc_walk_def split: option.splits pde.splits pte.splits)


lemma pt_walk_pair_pair_fault_pdc_walk:
  "\<lbrakk>pt_walk_pair a m r v = Partial_Walk y\<rbrakk> \<Longrightarrow> pdc_walk a m r v = Some y"
  by (clarsimp simp: pt_walk_pair_def is_fault_def pdc_walk_def split: option.splits pde.splits pte.splits)


lemma  pt_walk_pair_fault_pdc_walk_fault':
  "\<lbrakk>pt_walk_pair a m rt v = Fault\<rbrakk> \<Longrightarrow> pdc_walk a m rt v = None"
  by (clarsimp simp: pt_walk_pair_def pdc_walk_def split: option.splits pde.splits pte.splits)


lemma  pt_walk_pair_fault_pt_walk_fault':
  "\<lbrakk>pt_walk_pair a m rt v = Fault\<rbrakk> \<Longrightarrow> pt_walk a m rt v = None"
  by (clarsimp simp: pt_walk_pair_def pt_walk_def map_opt_def pdc_walk_def split: option.splits pde.splits pte.splits)


lemma pt_walk_pair_equal_pdc_walk:
  "pt_walk_pair a m rt v = pt_walk_pair a' m' rt' v \<Longrightarrow> pdc_walk a m rt v = pdc_walk a' m' rt' v"
  by (cases "pt_walk_pair a m rt v"; cases "pt_walk_pair a' m' rt' v";
               clarsimp simp: pt_walk_pair_fault_pdc_walk_fault' pt_walk_pair_pair_fault_pdc_walk
                              pt_walk_pair_no_fault_pdc_walk)

lemma pt_walk_pair_equal_pdc_walk':
  "\<lbrakk>pt_walk_pair a m rt v = pt_walk_pair a' m' rt' v\<rbrakk> \<Longrightarrow> 
                     the(pdc_walk a m rt v) = the(pdc_walk a' m' rt' v)"
  by (cases "pt_walk_pair a m rt v"; cases "pt_walk_pair a' m' rt' v";
               clarsimp simp: pt_walk_pair_fault_pdc_walk_fault' pt_walk_pair_pair_fault_pdc_walk
                              pt_walk_pair_no_fault_pdc_walk)


lemma pt_walk_pair_pdc_no_fault:
  "\<lbrakk>pt_walk_pair a m rt v = pt_walk_pair a' m' rt' v; \<not>is_fault (pdc_walk a' m' rt' v) \<rbrakk> \<Longrightarrow> 
                     \<not>is_fault (pdc_walk a m rt v)"
  by (cases "pt_walk_pair a m rt v"; cases "pt_walk_pair a' m' rt' v";
               clarsimp simp: pt_walk_pair_fault_pdc_walk_fault' pt_walk_pair_pair_fault_pdc_walk
                              pt_walk_pair_no_fault_pdc_walk)

lemma pt_walk_pair_fault_pt_walk_fault:
  "\<lbrakk>pt_walk_pair a m r v = Partial_Walk y\<rbrakk> \<Longrightarrow> is_fault (pt_walk a m r v)"
   by (clarsimp simp: pt_walk_pair_def is_fault_def pt_walk_def map_opt_def split: option.splits pde.splits)


lemma pt_walk_pair_no_fault_pt_walk:
  "\<lbrakk>pt_walk_pair a m rt v = Full_Walk entry entry'\<rbrakk> \<Longrightarrow> pt_walk a m rt v = Some entry"
  by (clarsimp simp: pt_walk_pair_def pt_walk_def map_opt_def split: option.splits pde.splits pte.splits)


lemma pt_walk_pair_no_fault_pt_walk':
  "pt_walk_pair a m r v = Full_Walk te pe \<Longrightarrow> \<not>is_fault (pt_walk a m r v)"
  by (simp add: is_fault_def pt_walk_pair_no_fault_pt_walk)


lemma pt_walk_full_no_pdc_fault:
  "pt_walk_pair a m r v = Full_Walk te pe \<Longrightarrow> \<not>is_fault (pdc_walk a m r v)"
  using no_fault_pt_walk_no_fault_pdc_walk pt_walk_pair_no_fault_pt_walk' by auto


lemma pt_walk_pair_pt_no_fault:
  "\<lbrakk>pt_walk_pair a m rt v = pt_walk_pair a' m' rt' v; \<not>is_fault (pt_walk a' m' rt' v) \<rbrakk> \<Longrightarrow> 
                     \<not>is_fault (pt_walk a m rt v)"
  by (cases "pt_walk_pair a m rt v"; cases "pt_walk_pair a' m' rt' v";
               clarsimp simp: pt_walk_pair_fault_pt_walk_fault' pt_walk_pair_fault_pt_walk_fault
                              pt_walk_pair_no_fault_pt_walk')

lemma pdc_walk_pt_trace_upd:
  "p \<notin> ptable_trace' h r x \<Longrightarrow> pdc_walk a (h(p \<mapsto> v)) r x =  pdc_walk a h r x"
  apply (clarsimp simp: ptable_trace'_def Let_def pdc_walk_def split: option.splits)
  apply (subgoal_tac "get_pde' h r x = get_pde' (h(p \<mapsto> v)) r x" , clarsimp)
  by (clarsimp simp: get_pde'_def decode_pde_def Let_def decode_heap_pde'_def split: pde.splits if_split_asm)


lemma pt_walk_not_full_walk_fault:
  "pt_walk_pair a m r v \<noteq> Full_Walk (the (pt_walk a m r v)) (the (pdc_walk a m r v)) \<Longrightarrow>
                         is_fault (pt_walk a m r v)"
  by (clarsimp simp: pt_walk_pair_def is_fault_def pt_walk_def map_opt_def split: option.splits)
  

lemma pt_walk_not_full_walk_partial_pdc:
  "\<lbrakk>\<forall>te. pt_walk_pair a m r v \<noteq> Full_Walk te (the (pdc_walk a m r v)); 
            \<not>is_fault (pdc_walk a m r v)\<rbrakk> \<Longrightarrow> pt_walk_pair a m r v = Partial_Walk (the (pdc_walk a m r v))"
  by (metis is_fault_def le_boolD option.sel order_refl pt_walk_not_full_walk_fault pt_walk_pair_fault_pdc_walk_fault' 
         pt_walk_pair_no_fault_pt_walk' pt_walk_pair_pair_fault_pdc_walk pt_walk_typ.exhaust)

lemma pt_walk_pair_disj:
  "pt_walk_pair a m r v = Fault \<or> pt_walk_pair a m r v = Partial_Walk (the (pdc_walk a m r v)) \<or> 
          pt_walk_pair a m r v = Full_Walk (the (pt_walk a m r v)) (the (pdc_walk a m r v))"
  by (clarsimp simp: pt_walk_pair_def is_fault_def pt_walk_def map_opt_def split: option.splits)



(* snapshot functions *)



definition 
  cur_pt_snp :: "vaddr set \<Rightarrow> heap \<Rightarrow> paddr  \<Rightarrow> asid \<Rightarrow> (vaddr set \<times> (vaddr \<Rightarrow> pt_walk_typ))"
where
  "cur_pt_snp ist m r  \<equiv> \<lambda>a. (ist, \<lambda>v. pt_walk_pair a m r v)"


definition 
  cur_pt_snp' :: "(asid \<Rightarrow> (vaddr set \<times> (vaddr \<Rightarrow> pt_walk_typ))) \<Rightarrow> vaddr set \<Rightarrow> 
                                 heap \<Rightarrow> paddr \<Rightarrow> asid \<Rightarrow> (asid \<Rightarrow> (vaddr set \<times> (vaddr \<Rightarrow> pt_walk_typ)))"
where
  "cur_pt_snp' snp ist mem ttbr0 a \<equiv> snp (a := cur_pt_snp ist mem ttbr0 a)"



definition
  "range_of (e :: tlb_entry) \<equiv>
                     case e of EntrySmall a vba pba fl   \<Rightarrow> Addr ` {(ucast vba) << 12 ..
                                                                    ((ucast vba) << 12) + (2^12 - 1)}
                             | EntrySection a vba pba fl \<Rightarrow>  Addr ` {(ucast vba) << 20 ..
                                                                      ((ucast vba) << 20) + (2^20 - 1)}"

definition 
  global_entries :: " tlb_entry set \<Rightarrow> tlb_entry set"
where
  "global_entries t = {e\<in>t. asid_of e = None}"


definition 
  incon_load :: "ptable_snapshot \<Rightarrow> vaddr set \<Rightarrow> vaddr set \<Rightarrow>  asid \<Rightarrow> heap \<Rightarrow> paddr \<Rightarrow> vaddr set"
  where
  "incon_load  snp iset gset a m r \<equiv>  fst (snp a) \<union> (iset \<inter> gset)  \<union> ptable_comp (snd(snp a)) (pt_walk_pair a m r)"





fun
  flush_effect_iset ::"flush_type \<Rightarrow> vaddr set \<Rightarrow> vaddr set \<Rightarrow> asid \<Rightarrow> vaddr set"
where
  "flush_effect_iset flushTLB iset gset a' = {}"
|
  "flush_effect_iset (flushASID a) iset gset a' = (if a = a' then  iset \<inter> gset else iset)"
|
  "flush_effect_iset (flushvarange vset) iset gset a' = iset - vset"
|
  "flush_effect_iset (flushASIDvarange a vset) iset gset a' =  (if a = a' then iset - (vset - gset)  else iset)"


fun
  flush_effect_glb ::"flush_type \<Rightarrow> vaddr set  \<Rightarrow> asid \<Rightarrow> heap \<Rightarrow> paddr \<Rightarrow> vaddr set"
where
  "flush_effect_glb flushTLB  gset a' m rt = (\<Union>x\<in>global_entries (ran(pt_walk a' m rt)). range_of x)"
|
  "flush_effect_glb (flushASID a)  gset a' m rt = gset"
|
  "flush_effect_glb (flushvarange vset)  gset a' m rt = (gset - vset) \<union> (\<Union>x\<in>global_entries (ran(pt_walk a' m rt)). range_of x)"
|
  "flush_effect_glb (flushASIDvarange a vset)  gset a' m rt =  gset"


fun
  flush_effect_snp :: "flush_type  \<Rightarrow> ptable_snapshot \<Rightarrow> asid \<Rightarrow>  ptable_snapshot"
where
  "flush_effect_snp flushTLB snp a' =  (\<lambda>a. ({}, \<lambda>v. Fault))"
|   
  "flush_effect_snp (flushASID a) snp a'= (if a = a' then snp else snp(a := ({}, \<lambda>v. Fault)))"
|
  "flush_effect_snp (flushvarange vset) snp a' = (\<lambda>a. (fst (snp a) - vset,  \<lambda>v. if v \<in> vset then Fault else snd (snp a) v ))"
|   
  "flush_effect_snp (flushASIDvarange a vset)  snp  a'= (if a = a' then snp else 
                                                        (\<lambda>x. if x = a then (fst (snp x) - vset, \<lambda>v. if v \<in> vset then Fault else snd (snp x) v) else snp x))"







(* for global set  *)


definition
  pt_walk' :: "asid \<Rightarrow> heap \<Rightarrow> paddr \<Rightarrow> vaddr \<Rightarrow> tlb_entry option"
where
  "pt_walk' a hp rt v \<equiv>
      case get_pde' hp rt v
       of None                 \<Rightarrow> None
       | Some InvalidPDE       \<Rightarrow> None
       | Some ReservedPDE      \<Rightarrow> None
       | Some (SectionPDE bpa perms) \<Rightarrow> Some (EntrySection (tag_conv a (to_tlb_flags perms))  (ucast (addr_val v >> 20) :: 12 word)
                                      ((word_extract 31 20 (addr_val bpa)):: 12 word) 
                                       (to_tlb_flags perms))
       | Some (PageTablePDE p) \<Rightarrow>
               (case get_pte' hp p v
                 of None                     \<Rightarrow> None
                 |  Some InvalidPTE          \<Rightarrow> None
                 |  Some (SmallPagePTE bpa perms) \<Rightarrow> Some(EntrySmall (tag_conv a (to_tlb_flags perms)) (ucast (addr_val v >> 12) :: 20 word)
                                                     ((word_extract 31 12 (addr_val bpa)):: 20 word) 
                                                     (to_tlb_flags perms)))"


lemma pt_walk'_pt_walk:
  "pt_walk' a h rt v = pt_walk a h rt v"
  apply (clarsimp simp: pt_walk'_def pt_walk_def pdc_walk_def pte_tlb_entry_def  map_opt_def
                           mask_def split:option.splits pde.splits pte.splits )
  by word_bitwise



lemma va_20_left [simp]:
  fixes va :: "32 word"
  shows "ucast (ucast (va >> 20) :: 12 word) << 20 \<le> va"
  by word_bitwise

lemma va_12_left [simp]:
  fixes va :: "32 word"
  shows "ucast (ucast (va >> 12) :: 20 word) << 12 \<le> va"
  by word_bitwise

lemma va_20_right [simp]:
  fixes va :: "32 word"
  shows "va \<le> (ucast (ucast (va >> 20) :: 12 word) << 20) + 0x000FFFFF"
  by word_bitwise

lemma va_12_right [simp]:
  fixes va :: "32 word"
  shows "va \<le> (ucast (ucast (va >> 12) :: 20 word) << 12) + 0x00000FFF"
  by word_bitwise

lemma va_offset_add:
  " (va::32 word) : {ucast (ucast ((x:: 32 word) >> 12):: 20 word) << 12  .. 
    (ucast (ucast (x >> 12):: 20 word) << 12) + mask 12 } \<Longrightarrow>
      \<exists>a.  (0 \<le> a \<and> a \<le> mask 12) \<and>
  va = (ucast (ucast ((x:: 32 word) >> 12):: 20 word) << 12)  + a"
  apply (rule_tac x = "va - (ucast (ucast ((x:: 32 word) >> 12):: 20 word) << 12) " in exI)
  apply (clarsimp simp: mask_def)
  apply uint_arith
done

lemma shift_to_mask:
  "x AND NOT mask 12 = (ucast (ucast ((x::32 word) >> 12):: 20 word)::32 word) << 12"
  apply (rule word_eqI)
  apply (simp add : word_ops_nth_size word_size)
  apply (simp add : nth_shiftr nth_shiftl nth_ucast)
  apply auto
  done

lemma nth_bits_false:
  "\<lbrakk>(n::nat) < 20; (a::32 word) \<le> 0xFFF\<rbrakk> \<Longrightarrow> \<not>(a !! (n + 12))"
  apply word_bitwise
  apply clarsimp
  apply (case_tac "n = 0")
   apply clarsimp
  apply (case_tac "n = 1")
   apply clarsimp
  apply (case_tac "n = 2")
   apply clarsimp
  apply (case_tac "n = 3")
   apply clarsimp
  apply (case_tac "n = 4")
   apply clarsimp
  apply (case_tac "n = 5")
   apply clarsimp
  apply (case_tac "n = 6")
   apply clarsimp
  apply (case_tac "n = 7")
   apply clarsimp
  apply (case_tac "n = 8")
   apply clarsimp
  apply (case_tac "n = 9")
   apply clarsimp
  apply (case_tac "n = 10")
   apply clarsimp
  apply (case_tac "n = 11")
   apply clarsimp
  apply (case_tac "n = 12")
   apply clarsimp
  apply (case_tac "n = 13")
   apply clarsimp
  apply (case_tac "n = 14")
   apply clarsimp
  apply (case_tac "n = 15")
   apply clarsimp
  apply (case_tac "n = 16")
   apply clarsimp
  apply (case_tac "n = 17")
   apply clarsimp
  apply (case_tac "n = 18")
   apply clarsimp
  apply (case_tac "n = 19")
   apply clarsimp
  apply (thin_tac "\<not> a !! P" for P)+
  apply arith
done

lemma nth_bits_offset_equal: "\<lbrakk>n < 20 ; (a::32 word) \<le> 0x00000FFF \<rbrakk> \<Longrightarrow> 
        (((x::32 word) && 0xFFFFF000) || a) !!  (n + 12) = x !! (n + 12)"
  apply clarsimp
  apply (rule iffI)
   apply (erule disjE)
    apply clarsimp
   apply (clarsimp simp: nth_bits_false)
  apply clarsimp
  apply (simp only: test_bit_int_def [symmetric])
  apply (case_tac "n = 0")
   apply clarsimp
  apply (case_tac "n = 1")
   apply clarsimp
  apply (case_tac "n = 2")
   apply clarsimp
  apply (case_tac "n = 3")
   apply clarsimp
  apply (case_tac "n = 4")
   apply clarsimp
  apply (case_tac "n = 5")
   apply clarsimp
  apply (case_tac "n = 6")
   apply clarsimp
  apply (case_tac "n = 7")
   apply clarsimp
  apply (case_tac "n = 8")
   apply clarsimp
  apply (case_tac "n = 9")
   apply clarsimp
  apply (case_tac "n = 10")
   apply clarsimp
  apply (case_tac "n = 11")
   apply clarsimp
  apply (case_tac "n = 12")
   apply clarsimp
  apply (case_tac "n = 13")
   apply clarsimp
  apply (case_tac "n = 14")
   apply clarsimp
  apply (case_tac "n = 15")
   apply clarsimp
  apply (case_tac "n = 16")
   apply clarsimp
  apply (case_tac "n = 17")
   apply clarsimp
  apply (case_tac "n = 18")
   apply clarsimp
  apply (case_tac "n = 19")
   apply clarsimp
  by presburger

lemma add_to_or:
  "(a::32 word) \<le> 0xFFF \<Longrightarrow>
     ((x::32 word) && 0xFFFFF000) + a =  (x && 0xFFFFF000) || a"
  apply word_bitwise
  apply clarsimp
  using xor3_simps carry_simps apply auto
 done

lemma va_offset_higher_bits: 
   " \<lbrakk>ucast (ucast ((x:: 32 word) >> 12):: 20 word) << 12 \<le> va ; 
      va \<le> (ucast (ucast (x >> 12):: 20 word) << 12) + 0x00000FFF \<rbrakk> \<Longrightarrow>
        (ucast (x >> 12)::20 word) = (ucast ((va:: 32 word) >> 12)::20 word)"
  apply (subgoal_tac "(va::32 word) : {ucast (ucast ((x:: 32 word) >> 12):: 20 word) << 12  ..
   (ucast (ucast (x >> 12):: 20 word) << 12) + mask 12 }")
   prefer 2
   apply (clarsimp simp: mask_def)
  apply (frule va_offset_add)
  apply simp
  apply (erule exE)
  apply (erule conjE)
  apply (simp add: mask_def)
  apply (subgoal_tac "(ucast ((((ucast (ucast ((x:: 32 word) >> 12):: 20 word) << 12)::32 word)  + a) >> 12):: 20 word) =
                       (ucast (((ucast (ucast ((x:: 32 word) >> 12):: 20 word) << 12)::32 word)   >> 12):: 20 word) ")
   apply clarsimp
   apply (word_bitwise) [1]
  apply (subgoal_tac "ucast ((ucast (ucast ((x::32 word) >> 12):: 20 word)::32 word) << 12 >> 12) =
                      (ucast (x >> 12) :: 20 word)")
   prefer 2
   apply (word_bitwise) [1]
  apply simp
  apply (clarsimp simp: shift_to_mask [symmetric])
  apply (rule word_eqI)
  apply (simp only: nth_ucast)
  apply clarsimp
  apply (subgoal_tac "n < 20")
   prefer 2
   apply word_bitwise [1]
  apply clarsimp
  apply (clarsimp simp: nth_shiftr)
  apply (clarsimp simp: mask_def)
  apply (frule_tac a = a in nth_bits_offset_equal) apply clarsimp
  apply (drule_tac x= x in add_to_or)
  apply (simp only: )
 done

lemma n_bit_shift:
  "\<lbrakk> \<forall>n::nat. n \<in> {12 .. 31} \<longrightarrow>(a::32 word) !! n = (b::32 word) !! n  \<rbrakk>  \<Longrightarrow> a >> 12 = b >> 12"
  apply word_bitwise
  by auto
 lemma nth_bits_offset: "\<lbrakk> n \<in> {12..31} ; (a::32 word) \<le> 0x00000FFF \<rbrakk> \<Longrightarrow> 
        (x::32 word) !! n = (x && 0xFFFFF000 || a) !! n"
   apply (rule iffI)
   apply (case_tac "n = 12")
    apply clarsimp
   apply (case_tac "n = 13")
    apply clarsimp
   apply (case_tac "n = 14")
    apply clarsimp
   apply (case_tac "n = 15")
    apply clarsimp
   apply (case_tac "n = 16")
    apply clarsimp
   apply (case_tac "n = 17")
    apply clarsimp
   apply (case_tac "n = 18")
    apply clarsimp
   apply (case_tac "n = 19")
    apply clarsimp
   apply (case_tac "n = 20")
    apply clarsimp
   apply (case_tac "n = 21")
    apply clarsimp
   apply (case_tac "n = 22")
    apply clarsimp
   apply (case_tac "n = 23")
    apply clarsimp
   apply (case_tac "n = 24")
    apply clarsimp
   apply (case_tac "n = 25")
    apply clarsimp
   apply (case_tac "n = 26")
    apply clarsimp
   apply (case_tac "n = 27")
    apply clarsimp
   apply (case_tac "n = 28")
    apply clarsimp
   apply (case_tac "n = 29")
    apply clarsimp
   apply (case_tac "n = 30")
    apply clarsimp
   apply (case_tac "n = 31")
    apply clarsimp
   prefer 2
   apply (case_tac "n = 12")
    apply word_bitwise [1] apply clarsimp
   apply (case_tac "n = 13")
    apply word_bitwise [1] apply clarsimp
   apply (case_tac "n = 14")
    apply word_bitwise [1]  apply clarsimp
   apply (case_tac "n = 15")
    apply word_bitwise [1]  apply clarsimp
   apply (case_tac "n = 16")
    apply word_bitwise [1] apply clarsimp
   apply (case_tac "n = 17")
    apply word_bitwise [1] apply clarsimp
   apply (case_tac "n = 18")
    apply word_bitwise [1] apply clarsimp
   apply (case_tac "n = 19")
    apply word_bitwise [1] apply clarsimp
   apply (case_tac "n = 20")
    apply word_bitwise [1] apply clarsimp
   apply (case_tac "n = 21")
    apply word_bitwise [1] apply clarsimp
   apply (case_tac "n = 22")
    apply word_bitwise [1] apply clarsimp
   apply (case_tac "n = 23")
    apply word_bitwise [1] apply clarsimp
   apply (case_tac "n = 24")
    apply word_bitwise [1] apply clarsimp
   apply (case_tac "n = 25")
    apply word_bitwise [1] apply clarsimp
   apply (case_tac "n = 26")
    apply word_bitwise [1]  apply clarsimp
   apply (case_tac "n = 27")
    apply word_bitwise [1] apply clarsimp
   apply (case_tac "n = 28")
    apply word_bitwise [1] apply clarsimp
   apply (case_tac "n = 29")
    apply word_bitwise [1] apply clarsimp
   apply (case_tac "n = 30")
    apply word_bitwise [1] apply clarsimp
   apply (case_tac "n = 31")
    apply word_bitwise [1] apply clarsimp
   apply clarsimp
   apply arith
  apply clarsimp
  apply arith
done

lemma offset_mask_eq:
 "\<lbrakk>ucast (ucast ((x:: 32 word) >> 12):: 20 word) << 12 \<le> va ; 
      va \<le> (ucast (ucast (x >> 12):: 20 word) << 12) + 0x00000FFF\<rbrakk>
          \<Longrightarrow> (( x >> 12) && mask 8 << 2) =  ((va >> 12) && mask 8 << 2)"
  apply (subgoal_tac "(va::32 word) : {ucast (ucast ((x:: 32 word) >> 12):: 20 word) << 12  ..
                      (ucast (ucast (x >> 12):: 20 word) << 12) + mask 12 }")
   prefer 2
   apply (clarsimp simp: mask_def)
  apply (frule va_offset_add)
  apply simp
  apply (erule exE)
  apply (erule conjE)
  apply (simp add: mask_def)
  apply (rule_tac f = "(\<lambda>x. x && 0xFF << 2)" in  arg_cong)
  apply (clarsimp simp: shift_to_mask [symmetric])
  apply (simp add: mask_def)
  apply (rule n_bit_shift)
  apply (rule allI)
  apply (rule impI)
  apply (frule_tac x= x in add_to_or)
  apply (frule_tac x= x in nth_bits_offset)
   apply (simp only:)+
done

lemma n_bit_shift_1:
  "\<lbrakk> \<forall>n::nat. n \<in> {12 .. 31} \<longrightarrow>(a::32 word) !! n = (b::32 word) !! n  \<rbrakk>  \<Longrightarrow>  a >> 20 = b >> 20"
  apply word_bitwise
  by auto

lemma offset_mask_eq_1:
  "\<lbrakk>ucast (ucast ((x:: 32 word) >> 12):: 20 word) << 12 \<le> va ; 
      va \<le> (ucast (ucast (x >> 12):: 20 word) << 12) + 0x00000FFF\<rbrakk>
          \<Longrightarrow>((x >> 20) && mask 12 << 2) =  ((va >> 20) && mask 12 << 2)"
  apply (subgoal_tac "(va::32 word) : {ucast (ucast ((x:: 32 word) >> 12):: 20 word) << 12  ..
   (ucast (ucast (x >> 12):: 20 word) << 12) + mask 12 }")
   prefer 2
   apply (clarsimp simp: mask_def)
  apply (frule va_offset_add)
  apply simp
  apply (erule exE)
  apply (erule conjE)
  apply (simp add: mask_def)
  apply (rule_tac f = "(\<lambda>x. x && 0xFFF << 2)" in  arg_cong)
  apply (clarsimp simp: shift_to_mask [symmetric])
  apply (simp add: mask_def)
  apply (rule n_bit_shift_1)
  apply (rule allI)
  apply (rule impI)
  apply (frule_tac x= x in add_to_or)
  apply (frule_tac x= x in nth_bits_offset)
   apply (simp only:)+
  done

lemma va_offset_add_1:
  " (va::32 word) : {ucast (ucast ((x:: 32 word) >> 20):: 12 word) << 20  .. 
    (ucast (ucast (x >> 20):: 12 word) << 20) + mask 20 } \<Longrightarrow>
      \<exists>a.  (0 \<le> a \<and> a \<le> mask 20) \<and>
      va = (ucast (ucast ((x:: 32 word) >> 20):: 12 word) << 20)  + a"
  apply (rule_tac x = "va - (ucast (ucast ((x:: 32 word) >> 20):: 12 word) << 20) " in exI)
  apply (clarsimp simp: mask_def)
  apply uint_arith
done

lemma shift_to_mask_1:
  "x AND NOT mask 20 = (ucast (ucast ((x::32 word) >> 20):: 12 word)::32 word) << 20"
  apply (rule word_eqI)
  apply (simp add : word_ops_nth_size word_size)
  apply (simp add : nth_shiftr nth_shiftl nth_ucast)
  apply auto
done

lemma nth_bits_false_1:
  "\<lbrakk>(n::nat) < 12; (a::32 word) \<le> 0xFFFFF\<rbrakk> \<Longrightarrow> \<not>(a !! (n + 20))"
  apply word_bitwise
  apply clarsimp
  apply (case_tac "n = 0")
   apply clarsimp
  apply (case_tac "n = 1")
   apply clarsimp
  apply (case_tac "n = 2")
   apply clarsimp
  apply (case_tac "n = 3")
   apply clarsimp
  apply (case_tac "n = 4")
   apply clarsimp
  apply (case_tac "n = 5")
   apply clarsimp
  apply (case_tac "n = 6")
   apply clarsimp
  apply (case_tac "n = 7")
   apply clarsimp
  apply (case_tac "n = 8")
   apply clarsimp
  apply (case_tac "n = 9")
   apply clarsimp
  apply (case_tac "n = 10")
   apply clarsimp
  apply (case_tac "n = 11")
   apply clarsimp
  apply (thin_tac "\<not> a !! P" for P)+
  apply arith
  done

lemma nth_bits_offset_equal_1: "\<lbrakk>n < 12 ; (a::32 word) \<le> 0x000FFFFF \<rbrakk> \<Longrightarrow> 
        (((x::32 word) && 0xFFF00000) || a) !!  (n + 20) = x !! (n + 20)"
  apply clarsimp
  apply (rule iffI)
   apply (erule disjE)
    apply clarsimp
   apply (clarsimp simp: nth_bits_false_1)
  apply clarsimp
  apply (simp only: test_bit_int_def [symmetric])
  apply (case_tac "n = 0")
   apply clarsimp
  apply (case_tac "n = 1")
   apply clarsimp
  apply (case_tac "n = 2")
   apply clarsimp
  apply (case_tac "n = 3")
   apply clarsimp
  apply (case_tac "n = 4")
   apply clarsimp
  apply (case_tac "n = 5")
   apply clarsimp
  apply (case_tac "n = 6")
   apply clarsimp
  apply (case_tac "n = 7")
   apply clarsimp
  apply (case_tac "n = 8")
   apply clarsimp
  apply (case_tac "n = 9")
   apply clarsimp
  apply (case_tac "n = 10")
   apply clarsimp
  apply (case_tac "n = 11")
   apply clarsimp
  by presburger

lemma add_to_or_1:
  "(a::32 word) \<le> 0xFFFFF \<Longrightarrow>
     ((x::32 word) && 0xFFF00000) + a =  (x && 0xFFF00000) || a"
  apply word_bitwise
  apply clarsimp
  using xor3_simps carry_simps apply auto
  done

lemma va_offset_higher_bits_1: 
   " \<lbrakk>ucast (ucast ((x:: 32 word) >> 20):: 12 word) << 20 \<le> va ; 
      va \<le> (ucast (ucast (x >> 20):: 12 word) << 20) + 0x000FFFFF \<rbrakk> \<Longrightarrow>
        (ucast (x >> 20):: 12 word) = (ucast ((va:: 32 word) >> 20)::12 word)"
  apply (subgoal_tac "(va::32 word) : {ucast (ucast ((x:: 32 word) >> 20):: 12 word) << 20 ..
                      (ucast (ucast (x >> 20):: 12 word) << 20) + mask 20 }")
   prefer 2
   apply (clarsimp simp: mask_def)
  apply (frule va_offset_add_1)
  apply simp
  apply (erule exE)
  apply (erule conjE)
  apply (simp add: mask_def)
  apply (subgoal_tac "(ucast ((((ucast (ucast ((x:: 32 word) >> 20):: 12 word) << 20)::32 word)  + a) >> 20):: 12 word) =
                      (ucast (((ucast (ucast ((x:: 32 word) >> 20):: 12 word) << 20)::32 word)   >> 20):: 12 word) ")
   apply clarsimp
   apply (word_bitwise) [1]
  apply (subgoal_tac "ucast ((ucast (ucast ((x::32 word) >> 20):: 12 word)::32 word) << 20 >> 20) =
   (ucast (x >> 20) :: 12 word)")
   prefer 2
   apply (word_bitwise) [1]
  apply simp
  apply (clarsimp simp: shift_to_mask_1 [symmetric])
  apply (rule word_eqI)
  apply (simp only: nth_ucast)
  apply clarsimp
  apply (subgoal_tac "n < 12")
   prefer 2
   apply word_bitwise [1]
  apply clarsimp
  apply (clarsimp simp: nth_shiftr)
  apply (clarsimp simp: mask_def)
  apply (frule_tac a = a in nth_bits_offset_equal_1) apply clarsimp
  apply (drule_tac x= x in add_to_or_1)
  apply (simp only: )
  done

lemma n_bit_shift_2:
  "\<lbrakk> \<forall>n::nat. n \<in> {20 .. 31} \<longrightarrow>(a::32 word) !! n = (b::32 word) !! n  \<rbrakk>  \<Longrightarrow>  a >> 20 = b >> 20"
  apply word_bitwise
  by auto


lemma nth_bits_offset_1: "\<lbrakk> n \<in> {20..31} ; (a::32 word) \<le> 0x000FFFFF \<rbrakk> \<Longrightarrow> 
        (x::32 word) !! n = (x && 0xFFF00000 || a) !! n"
  apply (rule iffI)
   apply (case_tac "n = 20")
    apply clarsimp
   apply (case_tac "n = 21")
    apply clarsimp
   apply (case_tac "n = 22")
    apply clarsimp
   apply (case_tac "n = 23")
    apply clarsimp
   apply (case_tac "n = 24")
    apply clarsimp
   apply (case_tac "n = 25")
    apply clarsimp
   apply (case_tac "n = 26")
    apply clarsimp
   apply (case_tac "n = 27")
    apply clarsimp
   apply (case_tac "n = 28")
    apply clarsimp
   apply (case_tac "n = 29")
    apply clarsimp
   apply (case_tac "n = 30")
    apply clarsimp
   apply (case_tac "n = 31")
    apply clarsimp
   prefer 2
   apply (case_tac "n = 20")
    apply word_bitwise [1] apply clarsimp
   apply (case_tac "n = 21")
    apply word_bitwise [1] apply clarsimp
   apply (case_tac "n = 22")
    apply word_bitwise [1] apply clarsimp
   apply (case_tac "n = 23")
    apply word_bitwise [1] apply clarsimp
   apply (case_tac "n = 24")
    apply word_bitwise [1] apply clarsimp
   apply (case_tac "n = 25")
    apply word_bitwise [1] apply clarsimp
   apply (case_tac "n = 26")
    apply word_bitwise [1]  apply clarsimp
   apply (case_tac "n = 27")
    apply word_bitwise [1] apply clarsimp
   apply (case_tac "n = 28")
    apply word_bitwise [1] apply clarsimp
   apply (case_tac "n = 29")
    apply word_bitwise [1] apply clarsimp
   apply (case_tac "n = 30")
    apply word_bitwise [1] apply clarsimp
   apply (case_tac "n = 31")
    apply word_bitwise [1] apply clarsimp
   apply clarsimp
   apply arith
  apply clarsimp
  apply arith
done

lemma  shfit_mask_eq:
  "\<lbrakk>ucast (ucast ((x:: 32 word) >> 20):: 12 word) << 20 \<le> va ; 
      va \<le> (ucast (ucast (x >> 20):: 12 word) << 20) + 0x000FFFFF \<rbrakk>
    \<Longrightarrow>   ((x >> 20) && mask 12 << 2) = ((va >> 20) && mask 12 << 2)"
  apply (subgoal_tac "(va::32 word) : {ucast (ucast ((x:: 32 word) >> 20):: 12 word) << 20 ..
   (ucast (ucast (x >> 20):: 12 word) << 20) + mask 20 }")
   prefer 2
   apply (clarsimp simp: mask_def)
  apply (frule va_offset_add_1)
  apply simp
  apply (erule exE)
  apply (erule conjE)
  apply (simp add: mask_def)
  apply (rule_tac f = "(\<lambda>x. x && 0xFFF << 2)" in  arg_cong)
  apply (clarsimp simp: shift_to_mask_1 [symmetric])
  apply (simp add: mask_def)
  apply (rule n_bit_shift_2)
  apply (rule allI)
  apply (rule impI)
  apply (frule_tac x= x in add_to_or_1)
  apply (frule_tac x= x and a = a in nth_bits_offset_1)
   apply (simp only:)+
  done




lemma asid_entry_range [simp, intro!]:
  "pt_walk' a m r v \<noteq> None \<Longrightarrow> v \<in> range_of (the (pt_walk' a m r v))"
  apply (clarsimp simp: range_of_def pt_walk'_def Let_def  split: option.splits ) 
  apply (case_tac x2; clarsimp split:  option.splits)
  apply (case_tac x2a; clarsimp split:  option.splits)
  apply (metis (no_types, hide_lams) Addr_addr_val atLeastAtMost_iff image_iff va_12_left va_12_right)
  by (metis (no_types, hide_lams) Addr_addr_val atLeastAtMost_iff image_iff va_20_left va_20_right)

lemma asid_va_entry_range_pt_entry:
  "\<not>is_fault(pt_walk' a m r v) \<Longrightarrow> 
      v \<in> range_of (the(pt_walk' a m r v))"
  by (clarsimp simp:   is_fault_def)


lemma  va_entry_set_pt_palk_same':
  "\<lbrakk>\<not>is_fault (pt_walk a' m r x) ;
           va \<in> range_of (the (pt_walk a' m r x))\<rbrakk> \<Longrightarrow>
              pt_walk a' m r x = pt_walk a' m r va"
  apply (simp only: pt_walk'_pt_walk [symmetric])
 apply (subgoal_tac "x \<in> range_of (the(pt_walk' a' m r x))")
   prefer 2
   apply (clarsimp simp: asid_va_entry_range_pt_entry is_fault_def)
  apply (cases "the (pt_walk' a' m r x)")
     apply (simp only: )
   apply (clarsimp simp:   range_of_def  is_fault_def)
   apply (cases "get_pde' m r x" ; clarsimp simp: pt_walk'_def)
   apply (case_tac a ; clarsimp)
   apply (case_tac "get_pte' m x3 x " ; clarsimp)
   apply (subgoal_tac "get_pde' m r (Addr xaa) = get_pde' m r  (Addr xa)" ; clarsimp)
    apply (subgoal_tac "get_pte' m x3 (Addr xaa) = get_pte' m x3  (Addr xa)" ; clarsimp)
     apply (case_tac a ; clarsimp)
  using va_offset_higher_bits apply blast
    apply (case_tac a ; clarsimp)
    apply (clarsimp simp:  get_pte'_def vaddr_pt_index_def)
    apply (subgoal_tac "(( xaa >> 12) && mask 8 << 2) =
                          (( xa >> 12) && mask 8 << 2) ")
     prefer 2
  using offset_mask_eq apply force
    apply force
   apply (case_tac a ; clarsimp)
   apply (clarsimp simp: get_pde'_def vaddr_pd_index_def)
   apply (subgoal_tac "((xaa >> 20) && mask 12 << 2) =
                         ((xa >> 20) && mask 12 << 2) ")
    prefer 2
  using offset_mask_eq_1 apply force
   apply force
  apply (simp only: )
  apply (clarsimp simp:   range_of_def  is_fault_def)
  apply (cases "get_pde' m r x" ; clarsimp simp: pt_walk'_def)
  apply (case_tac a ; clarsimp)
   apply (case_tac "get_pte' m x3 x" ; clarsimp)
   apply (subgoal_tac "get_pde' m r (Addr xaa) = get_pde' m r (Addr xa)" ; clarsimp)
    apply (subgoal_tac "get_pte' m x3 (Addr xaa) = get_pte' m x3 (Addr xa)" ; clarsimp)
     apply (case_tac a ; clarsimp)
    apply (case_tac a ; clarsimp simp: get_pte'_def vaddr_pt_index_def)
   apply (case_tac a ; clarsimp simp: get_pde'_def vaddr_pd_index_def)
  apply (cases "get_pde' m r x" ; clarsimp)
  apply (subgoal_tac "get_pde' m r (Addr xaa) = get_pde' m r (Addr xa)" ; clarsimp)
  using va_offset_higher_bits_1 apply blast
  apply (clarsimp simp: get_pde'_def vaddr_pd_index_def)
  apply (subgoal_tac "((xaa >> 20) && mask 12 << 2) = ((xa >> 20) && mask 12 << 2)")
   apply force
  using shfit_mask_eq by force


end
