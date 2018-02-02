theory MMU_Prg_Logic

imports
     "HOL-Word.Word" 
     PTABLE.PageTable_seL4 
     "./../Eisbach/Rule_By_Method"

             
begin

type_synonym val         = "32 word"
type_synonym asid        = "8 word"
type_synonym word_t      = "32 word"
type_synonym heap        = "paddr \<rightharpoonup> word_t"
type_synonym incon_set   = "vaddr set"
(* type_synonym incon_set   = "(asid \<times> vaddr) set" *)


datatype mode_t = Kernel | User



type_synonym vSm = "20 word"
type_synonym pSm = "20 word"

type_synonym vSe = "12 word"
type_synonym pSe = "12 word"

type_synonym fl     = "8 word"


datatype tlb_entry =
    EntrySmall   asid vSm "pSm option" fl
  | EntrySection asid vSe "pSe option" fl


datatype lookup_type  =  Miss  | Incon  |  Hit "tlb_entry"
type_synonym ptable_snapshot   = "(asid \<Rightarrow> vaddr \<Rightarrow> lookup_type)"

record p_state =
  heap      :: heap
  asid      :: asid
  root      :: paddr
  incon_set :: incon_set
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



fun
  flush_effect ::"flush_type \<Rightarrow> vaddr set \<Rightarrow> asid \<Rightarrow> vaddr set"
where
  "flush_effect flushTLB iset  a' = {}"
|
  "flush_effect (flushASID a)  iset a' = (if a = a' then {} else iset)"
|
  "flush_effect (flushvarange vset)  iset a' = iset - vset"
|
  "flush_effect (flushASIDvarange a vset)  iset a' =  (if a =a' then iset - vset else iset)"






(* ptable_comp function *)


fun word_bits :: "nat \<Rightarrow> nat \<Rightarrow> 'a::len word \<Rightarrow> 'a::len word" where
  "word_bits h l w = (w >> l) AND mask (Suc h - l)"

fun word_extract :: "nat \<Rightarrow> nat \<Rightarrow> 'a::len word \<Rightarrow> 'b::len word" where
  "word_extract h l w = ucast (word_bits h l w)"

definition
 pt_walk :: "asid \<Rightarrow> heap \<Rightarrow> paddr \<Rightarrow> vaddr \<Rightarrow> tlb_entry"
where
  "pt_walk a h rt v \<equiv>
      case get_pde' h rt v
       of None                 \<Rightarrow> EntrySection a (ucast (addr_val v >> 20) :: 12 word) None 0
       | Some InvalidPDE       \<Rightarrow> EntrySection a (ucast (addr_val v >> 20) :: 12 word) None 0
       | Some ReservedPDE      \<Rightarrow> EntrySection a (ucast (addr_val v >> 20) :: 12 word) None 0
       | Some (SectionPDE p ac) \<Rightarrow>
          EntrySection a (ucast (addr_val v >> 20) :: 12 word)
                            (Some  ((word_extract 31 20 (addr_val p)):: 12 word))  (0::8 word)
       | Some (PageTablePDE p) \<Rightarrow>
               (case get_pte' h p v
                 of None                     \<Rightarrow> EntrySmall a (ucast (addr_val v >> 12) :: 20 word) None 0
                 |  Some InvalidPTE          \<Rightarrow> EntrySmall a (ucast (addr_val v >> 12) :: 20 word) None 0
                 |  Some (SmallPagePTE p1 ac) \<Rightarrow> EntrySmall a (ucast (addr_val v >> 12) :: 20 word)
                                                 (Some ((word_extract 31 12 (addr_val p1)):: 20 word)) 0)"

datatype bpa = Bpsm "20 word" | Bpse "12 word"

fun
  bpa_entry :: "tlb_entry \<Rightarrow> bpa option"
where
  "bpa_entry (EntrySmall _ _ p _)   = map_option Bpsm p"
| "bpa_entry (EntrySection _ _ p _) = map_option Bpse p"


definition
  "is_fault e = (bpa_entry e = None)"



definition
  ptable_comp :: "asid \<Rightarrow> heap \<Rightarrow> heap \<Rightarrow> paddr \<Rightarrow> paddr \<Rightarrow> vaddr set"
where
  "ptable_comp a hp1 hp2 rt1 rt2 \<equiv>
                {va. (\<exists>e1 e2. pt_walk a hp1 rt1 va = e1 \<and> pt_walk a hp2 rt2 va = e2  \<and> \<not>is_fault e1 \<and> \<not>is_fault e2 \<and> e1 \<noteq> e2 )  \<or>
                (\<exists>e1 e2. pt_walk a hp1 rt1 va = e1 \<and> pt_walk a hp2 rt2 va = e2  \<and> \<not>is_fault e1 \<and> is_fault e2 )}"

definition
  lift_pt :: "(vaddr \<Rightarrow> tlb_entry) \<Rightarrow> vaddr \<Rightarrow> lookup_type"
where
  "lift_pt walk \<equiv> \<lambda>va. if is_fault (walk va) then Miss else Hit (walk va)"

lemma ptable_trace_pde_comp:
  "\<forall>x. p \<notin> ptable_trace' h r x \<Longrightarrow> ptable_comp a  h (h(p \<mapsto> v)) r  r= {}"
  apply (clarsimp simp: ptable_trace'_def ptable_comp_def Let_def)
  apply (drule_tac x = x in spec)

 apply (clarsimp simp: pt_walk_def is_fault_def lookup_pde'_def get_pde'_def decode_heap_pde'_def decode_heap_pte'_def vaddr_pt_index_def vaddr_pd_index_def lookup_pte'_def
                        get_pte'_def  split:option.splits split: pde.splits split: pte.splits)
 using Let_def by auto


lemma pde_comp_empty:
  "p \<notin> \<Union>(ptable_trace' h r ` UNIV) \<Longrightarrow> ptable_comp a  h (h(p \<mapsto> v)) r r = {}"
  apply (drule union_imp_all)
  by (clarsimp simp: ptable_trace_pde_comp)



lemma plift_equal_not_in_pde_comp [simp]:
  "\<lbrakk> pt_walk a h1 r va =  e ; pt_walk a h2 r va = e \<rbrakk> \<Longrightarrow>
            va \<notin> ptable_comp a h1 h2 r r"
  by (clarsimp simp: ptable_comp_def)


lemma pt_walk_pt_trace_upd:
  "p \<notin> ptable_trace' h r x \<Longrightarrow> pt_walk a h r x = pt_walk a (h(p \<mapsto> v)) r x"
  apply (clarsimp simp: ptable_trace'_def Let_def pt_walk_def )
  apply (subgoal_tac "get_pde' h r x = get_pde' (h(p \<mapsto> v)) r x" , clarsimp)
   apply (cases "get_pde' (h(p \<mapsto> v)) r x" ;clarsimp)
   apply (case_tac aa ; clarsimp)
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

lemma pt_walk_pt_trace_upd':
  "p \<notin> ptable_trace' h r x \<Longrightarrow> pt_walk a (h(p \<mapsto> v)) r x = pt_walk a h r x"
  using pt_walk_pt_trace_upd by auto



(* snapshot functions *)



definition 
  snapshot_update_current2 :: "vaddr set \<Rightarrow> heap \<Rightarrow> paddr  \<Rightarrow> (asid \<Rightarrow> vaddr \<Rightarrow> lookup_type)"
where
  "snapshot_update_current2 iset mem ttbr0  \<equiv> (\<lambda>a v. if v \<in>  iset then Incon else 
                            if (\<not>is_fault (pt_walk a mem ttbr0 v)) then  Hit (pt_walk a mem ttbr0 v) else Miss)"


definition 
  snapshot_update_current'2 :: "(asid \<Rightarrow> vaddr \<Rightarrow> lookup_type) \<Rightarrow> vaddr set \<Rightarrow> 
                                 heap \<Rightarrow> paddr \<Rightarrow> asid \<Rightarrow> (asid \<Rightarrow> vaddr \<Rightarrow> lookup_type)"
where
  "snapshot_update_current'2 snp iset mem ttbr0 a \<equiv> snp (a := snapshot_update_current2 iset mem ttbr0 a)"



definition 
  incon_load2 :: "(asid \<Rightarrow> vaddr \<Rightarrow> lookup_type) \<Rightarrow> asid \<Rightarrow> heap \<Rightarrow> paddr \<Rightarrow> vaddr set"
  where
  "incon_load2 snp a m rt \<equiv>  {v. \<exists>x. snp a v = Hit x \<and> x \<noteq> pt_walk a m rt v}"


definition 
  incon_load_incon:: "(asid \<Rightarrow> vaddr \<Rightarrow> lookup_type) \<Rightarrow> asid \<Rightarrow> heap  \<Rightarrow> vaddr set"
  where
  "incon_load_incon snp a m  \<equiv>  {v. snp a v = Incon}"


(*
definition 
  incon_load :: "ptable_snapshot \<Rightarrow> asid \<Rightarrow> heap \<Rightarrow> paddr \<Rightarrow> incon_set"
  where
  "incon_load snp a m rt \<equiv> (\<lambda>v. (a, v) ) ` 
                            {v. \<exists>x. snp a v = Hit x \<and> x \<noteq> pt_walk a m rt v}"


definition 
  snapshot_update_current :: "incon_set \<Rightarrow> heap \<Rightarrow> paddr \<Rightarrow> ptable_snapshot"
where
  "snapshot_update_current iset mem ttbr0  \<equiv> (\<lambda>x y. if (x,y) \<in>  iset then Incon else 
                                                if (\<not>is_fault (pt_walk x mem ttbr0 y)) then  Hit (pt_walk x mem ttbr0 y) else Miss)"


definition 
  snapshot_update_current' :: "ptable_snapshot \<Rightarrow> incon_set \<Rightarrow>  heap \<Rightarrow> paddr \<Rightarrow> asid \<Rightarrow> ptable_snapshot"
where
  "snapshot_update_current' snp iset mem ttbr0 a \<equiv> snp (a := snapshot_update_current iset mem ttbr0 a)"



definition
  incon_for_snapshot :: "incon_set \<Rightarrow> ptable_snapshot \<Rightarrow> asid \<Rightarrow> heap \<Rightarrow> paddr \<Rightarrow> incon_set"
  where
  "incon_for_snapshot iset snp a hp rt =  ({a} \<times> UNIV) \<inter> iset \<union>  incon_load snp a hp rt"




definition 
  miss_to_hit :: "ptable_snapshot \<Rightarrow> asid \<Rightarrow> heap \<Rightarrow> paddr \<Rightarrow> incon_set"
 where
  "miss_to_hit snp a m rt \<equiv> (\<lambda>v. (a, v) ) ` 
                              {v. snp a v = Miss \<and>  \<not>is_fault (pt_walk a m rt v)}"

definition 
  consistent_hit :: "ptable_snapshot\<Rightarrow> asid \<Rightarrow> heap \<Rightarrow> paddr  \<Rightarrow> incon_set"
 where
  "consistent_hit snp a m rt \<equiv> (\<lambda>v. (a, v) ) ` 
                                 {v. snp a v = Hit (pt_walk a m rt v)}"



definition 
  snapshot_update_new :: "(asid \<times> vaddr) set \<Rightarrow> (asid \<times> vaddr) set \<Rightarrow> (asid \<times> vaddr) set \<Rightarrow> 
                          heap \<Rightarrow> paddr \<Rightarrow>  ptable_snapshot"
where
  "snapshot_update_new iset m_to_h h_to_h hp ttbr0 \<equiv> (\<lambda>x y. if (x,y) \<in>  iset then Incon 
                                                     else if (x,y) \<in> m_to_h then Hit (pt_walk x hp ttbr0 y) 
                                                     else if (x,y) \<in> h_to_h then Hit (pt_walk x hp ttbr0 y) 
                                                     else Miss)"

definition 
  snapshot_update_new' :: "ptable_snapshot \<Rightarrow> (asid \<times> vaddr) set \<Rightarrow> (asid \<times> vaddr) set \<Rightarrow> (asid \<times> vaddr) set \<Rightarrow> 
                              heap \<Rightarrow> paddr \<Rightarrow> asid \<Rightarrow> ptable_snapshot"
where
  "snapshot_update_new' snp iset m_to_h h_to_h hp ttbr0 a \<equiv> 
                               snp (a := snapshot_update_new iset m_to_h h_to_h hp ttbr0 a)"
*)

 

fun
  flush_effect_snp :: "flush_type  \<Rightarrow> ptable_snapshot \<Rightarrow> asid \<Rightarrow>  ptable_snapshot"
where
  "flush_effect_snp flushTLB   snp a' = (\<lambda>a v. Miss)"
|   
  "flush_effect_snp (flushASID a)  snp a'= (if a = a' then snp else snp(a := \<lambda>v. Miss))"
|
  "flush_effect_snp (flushvarange vset)  snp a' = (\<lambda>x y. if (x,y) \<in> UNIV \<times> vset then Miss else snp x y)"
|   
  "flush_effect_snp (flushASIDvarange a vset)  snp  a'= (if a = a' then snp else (\<lambda>x y. if (x, y) \<in> {a} \<times> vset then Miss else snp x y))"

end
