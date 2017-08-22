theory MMU_Prg_Logic

imports
 "~~/src/HOL/Word/Word" "./../PageTable_seL4_m" "./../L3_Lib"
   "./../Rule_By_Method"


begin

type_synonym val         = "32 word"
type_synonym asid        = "8 word"
type_synonym word_type   = "32 word"
type_synonym heap        = "paddr \<rightharpoonup> 32 word"
type_synonym rootreg     = "32 word"    (* should we take 32 word only as now we are abstracting logic
                                   without the details of machine *)
type_synonym rt_map_t    = "paddr \<rightharpoonup> asid"

datatype mode_t = Kernel | User

datatype typ_tag'  = fst_lvl_pg_tbl |
                     snd_lvl_pg_tbl |
                     untype_mem

datatype typ_tag  = page_table |
                    untype_mem

type_synonym heap_typ   = "paddr \<Rightarrow> typ_tag"

record p_state =
  heap   :: "paddr \<rightharpoonup> word_type"  (* partial function, none for exceptions. 32 bit output type as this is a dummy language *)
  tagged_heap :: heap_typ
  root_log :: "paddr set"
  root_map :: "paddr \<rightharpoonup> asid"       (* what about address sharing *)
  asid  :: asid
  root :: "paddr"
  incon_set :: "(asid \<times> 32 word) set"
  mode :: mode_t


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
  "load_value_word_hp h p = map_option from_word (load_list_word_hp h 1 p)"


definition
  mem_read_word_heap :: "paddr \<Rightarrow> p_state \<rightharpoonup> word_type"
where
  "mem_read_word_heap p s = load_value_word_hp (heap s) p "


definition
  decode_heap_pde' :: "heap \<Rightarrow> paddr \<rightharpoonup> pde" where
  "decode_heap_pde' h p \<equiv>
     map_option decode_pde (h p)"

definition
  get_pde' :: "heap \<Rightarrow> paddr \<Rightarrow> vaddr \<rightharpoonup> pde" where
  "get_pde' h rt vp \<equiv>
     let
       pd_idx_offset = ((vaddr_pd_index (addr_val vp)) << 2)
     in
       decode_heap_pde' h (rt r+ pd_idx_offset)"

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
  "lookup_pde' h rt vp \<equiv>
   case_option None
    (\<lambda>pde. case pde
            of InvalidPDE \<Rightarrow> None
             | ReservedPDE \<Rightarrow> None
             | SectionPDE base perms \<Rightarrow> Some (base, ArmSection, perms)
             | PageTablePDE pt_base \<Rightarrow> lookup_pte' h pt_base vp)
    (get_pde' h rt vp)"


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
  "mem_read_hp hp rt vp =  (ptable_lift' hp rt \<rhd>o load_value_word_hp hp) vp"


definition
  ptable_trace' :: "heap \<Rightarrow> paddr \<Rightarrow> vaddr \<Rightarrow> paddr set" where
  "ptable_trace' h rt vp \<equiv>
     let
       vp_val = addr_val vp ;
       pd_idx_offset = ((vaddr_pd_index vp_val) << 2) ;
       pt_idx_offset = ((vaddr_pt_index vp_val) << 2) ;
       pd_touched = {rt r+ pd_idx_offset};
       pt_touched = (\<lambda>pt_base. {pt_base r+ pt_idx_offset})
     in
      (case decode_heap_pde' h (rt r+ pd_idx_offset)
         of Some pde \<Rightarrow>
              (case pde
                 of PageTablePDE pt_base \<Rightarrow> pd_touched \<union> pt_touched pt_base
                  | _ \<Rightarrow> pd_touched)
          | None \<Rightarrow> {})"

definition
  pde_trace' :: "heap \<Rightarrow> paddr \<Rightarrow> vaddr \<rightharpoonup> paddr" where
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
  apply (clarsimp simp: ptable_lift'_def lookup_pde'_def  get_pde'_def ptable_trace'_def Let_def split:option.splits)
  by (case_tac x2 ; clarsimp)



lemma ptable_lift_preserved':
  " \<lbrakk>p \<notin> ptable_trace' h r vp; ptable_lift' h r  vp = Some pa\<rbrakk> \<Longrightarrow> ptable_lift' (h(p \<mapsto> v)) r  vp = Some pa"
  apply (frule ptlift_trace_some , clarsimp simp: ptable_lift'_def lookup_pde'_def get_pde'_def ptable_trace'_def Let_def split: option.splits)
  apply (case_tac x2; clarsimp simp: decode_heap_pde'_def lookup_pte'_def split: option.splits)
  apply (case_tac x2a ; clarsimp)
  apply (rule conjI)
   apply (rule_tac x = "(SmallPagePTE a b)" in exI, clarsimp simp: get_pte'_def decode_heap_pte'_def , clarsimp)
  by (case_tac x2 ; clarsimp simp:get_pte'_def decode_heap_pte'_def)




lemma ptable_trace_preserved':
  "\<lbrakk>ptable_lift' h r vp = Some pb; p \<notin> ptable_trace' h r vp;
        pa \<notin> ptable_trace' h r vp \<rbrakk>  \<Longrightarrow>  pa \<notin> ptable_trace' (h(p \<mapsto> v)) r vp"
  apply (frule ptlift_trace_some)
  apply (subgoal_tac "ptable_trace' (h(p \<mapsto> v)) r vp \<noteq> {}")
   prefer 2
   apply (clarsimp simp: ptable_lift'_def lookup_pde'_def get_pde'_def ptable_trace'_def Let_def split: option.splits)
   apply (case_tac x2 ; clarsimp simp:  decode_heap_pde'_def)
  by (clarsimp simp: ptable_lift'_def lookup_pde'_def get_pde'_def decode_heap_pde'_def ptable_trace'_def Let_def split: option.splits pde.splits)


(* Mapped page table, used for later in the kernel execution  *)
definition
  ptable_mapped :: "heap \<Rightarrow> paddr \<Rightarrow> vaddr set"
where
  "ptable_mapped h r  \<equiv>   {va. \<exists>p. ptable_lift' h r va = Some p \<and>  p \<in> \<Union>(ptable_trace' h r ` UNIV) } "


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
  "lookup_pde_perm h r m vp = filter_pde  m (lookup_pde' h r vp)"

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
  " ptable_lift_m h r  User va = Some pa \<Longrightarrow>
         ptable_lift_m h r  User va =  ptable_lift' h r va"
  by (clarsimp simp: ptable_lift_m_def ptable_lift'_def lookup_pde_perm_def filter_pde_def split: option.splits split_if_asm)



lemma ptlift_trace_some':
  "ptable_lift_m h r m vp = Some pa \<Longrightarrow>  ptable_trace' h r vp \<noteq> {}"
  by (case_tac m , simp add:  ptlift_trace_some , simp, frule ptable_lift_m_user, simp add: ptlift_trace_some)


lemma ptable_trace_preserved_m:
  "\<lbrakk>ptable_lift_m h r m vp = Some pb; p \<notin> ptable_trace' h r vp;
        pa \<notin> ptable_trace' h r vp \<rbrakk>  \<Longrightarrow>  pa \<notin> ptable_trace' (h(p \<mapsto> v)) r vp"
  by (case_tac m ,simp add: ptable_trace_preserved', simp, frule ptable_lift_m_user, simp add: ptable_trace_preserved')



lemma ptable_lift_preserved_m:
  " \<lbrakk>p \<notin> ptable_trace' h r vp; ptable_lift_m h r m vp = Some pa\<rbrakk> \<Longrightarrow> ptable_lift_m (h(p \<mapsto> v)) r m vp = Some pa"
  apply (case_tac m ; simp add: ptable_lift_preserved')
  apply (frule ptable_lift_m_user ; simp)
  apply (frule_tac pa = pa and v = v in  ptable_lift_preserved' , simp)
  apply (clarsimp simp:  ptable_trace'_def Let_def ptable_lift'_def lookup_pde'_def get_pde'_def split: option.splits)
  apply (case_tac x2 ; clarsimp)
   prefer 2
   apply (clarsimp simp:  decode_heap_pde'_def)
   apply (clarsimp simp: ptable_lift_m_def lookup_pde'_def get_pde'_def decode_heap_pde'_def lookup_pde_perm_def filter_pde_def)
  apply (clarsimp simp:  ptable_lift_m_def lookup_pde'_def get_pde'_def lookup_pde_perm_def filter_pde_def lookup_pte'_def get_pte'_def decode_heap_pte'_def
                         split:split_if_asm split: option.splits)
  by (case_tac "decode_pte x2" ; clarsimp simp: decode_heap_pde'_def lookup_pte'_def get_pte'_def decode_heap_pte'_def)


lemma ptable_lift_m_implies_ptlift:
  "ptable_lift_m (heap s) (root s) (mode s) (Addr vp) = Some p \<Longrightarrow> ptable_lift' (heap s) (root s) (Addr vp) = Some p"
  by (clarsimp simp: ptable_lift_m_def ptable_lift'_def lookup_pde_perm_def filter_pde_def user_perms_def split: option.splits split_if_asm)


lemma union_imp_all:
  "p \<notin> \<Union>(ptable_trace' h r ` UNIV) \<Longrightarrow> \<forall>x. p \<notin> ptable_trace' h r x"
  by (clarsimp)

(* tagged heap *)

(* the following two definitions are not being used for the time being *)

definition
  update_mem_tag :: "heap_typ \<Rightarrow> paddr \<Rightarrow>  typ_tag \<Rightarrow> heap_typ"
where
  "update_mem_tag ht p t \<equiv>  ht (p := t) "

consts update_mem_tag_set :: "heap_typ \<Rightarrow> paddr set \<Rightarrow>  typ_tag \<Rightarrow> heap_typ"

definition
  update_mem_tag_set' :: "heap_typ \<Rightarrow> paddr set \<Rightarrow>  typ_tag \<Rightarrow> bool"
where
  "update_mem_tag_set' ht P t \<equiv> \<forall>x\<in>P. ht x = t"



(* first level is defined along with the tags of all the levels *)



definition
  first_level_defined_page_table :: "heap \<Rightarrow> heap_typ \<Rightarrow> paddr \<Rightarrow> bool"
where
  "first_level_defined_page_table  h ht r \<equiv> \<forall>v. \<exists>pde. get_pde' h r v = Some pde \<and>
                (\<forall>x\<in>\<Union>(ptable_trace' h r ` UNIV). ht x = page_table)"


definition
  page_tables_of_roots :: "heap \<Rightarrow> heap_typ \<Rightarrow> paddr set \<Rightarrow>  bool"
where
  "page_tables_of_roots h ht rset \<equiv> \<forall>r\<in>rset. \<forall>v. \<exists>pde. get_pde' h r v = Some pde \<and>
        (\<forall>x\<in>\<Union>(ptable_trace' h r ` UNIV). ht x = page_table)"


(* page tables of state of state *)

(* list of all the page tables for all the assigned roots in the state *)


definition
  current_page_table :: "p_state \<Rightarrow> bool"
where
  "current_page_table s \<equiv> first_level_defined_page_table (heap s) (tagged_heap s)  (root s)"


definition
  page_tables :: "p_state \<Rightarrow> bool"
where
  "page_tables s \<equiv> page_tables_of_roots (heap s) (tagged_heap s) (root_log s)"



(* may be remove later , if its giving problem in simp*)

lemma [simp]: "current_page_table s =  (\<forall>v. \<exists>pde. get_pde' (heap s) (root s) v = Some pde \<and>
        (\<forall>x\<in>\<Union>(ptable_trace' (heap s) (root s) ` UNIV). (tagged_heap s) x = page_table))"
  by (clarsimp simp: current_page_table_def first_level_defined_page_table_def)

lemma [simp]: "page_tables s = (\<forall>rt\<in>root_log s. \<forall>v. \<exists>pde. get_pde' (heap s) rt v = Some pde \<and>
                              (\<forall>x\<in>\<Union>(ptable_trace' (heap s) rt ` UNIV). (tagged_heap s) x = page_table))"
  by(clarsimp simp: page_tables_def page_tables_of_roots_def)




(* assumption of non-sharing address space of the processes, pages can be shared, but even then every process will have its own
          page table entry *)


definition
  non_overlapping_page_tables_assertion :: "paddr set \<Rightarrow> heap \<Rightarrow> bool"
where
  "non_overlapping_page_tables_assertion rset h \<equiv>
           (\<forall>x y. x\<in>rset \<and> y\<in>rset \<and> x\<noteq>y \<longrightarrow> \<Union>(ptable_trace' h x ` UNIV) \<inter> \<Union>(ptable_trace' h y ` UNIV) = {})"



definition
  non_overlapping_page_tables :: "p_state \<Rightarrow> bool"
where
  "non_overlapping_page_tables s \<equiv> page_tables s \<and> non_overlapping_page_tables_assertion (root_log s) (heap s)"


(* brackets might be an issue *)

lemma [simp]:
  "non_overlapping_page_tables s = ((\<forall>rt\<in>root_log s. (\<forall>v. \<exists>pde. get_pde' (heap s) rt v = Some pde) \<and>
         (\<forall>a. \<forall>x\<in>ptable_trace' (heap s) rt a. tagged_heap s x = page_table)) \<and> non_overlapping_page_tables_assertion (root_log s) (heap s))"
  by (clarsimp simp: non_overlapping_page_tables_def)


(* previous version, have to remove later *)

definition
  non_overlapping_page_tables' :: "p_state \<Rightarrow> bool"
where
  "non_overlapping_page_tables' s \<equiv> (\<forall>rt\<in>root_log s. \<forall>v. \<exists>pde. get_pde' (heap s) rt v = Some pde \<and>
                                  (\<forall>x\<in>\<Union>(ptable_trace' (heap s) rt ` UNIV). (tagged_heap s) x = page_table)) \<and>
             (\<forall>x y. x\<in>root_log s \<and> y\<in>root_log s \<and> x\<noteq>y \<longrightarrow> \<Union>(ptable_trace' (heap s) x ` UNIV) \<inter> \<Union>(ptable_trace' (heap s) y ` UNIV) = {})"


(* range of virtual addresses mapped by a section entry , entry can be valid or invalid
  we might use this in the flush by vaddr set
   is there any better way of stating this, like ran or dom ? *)



definition
  vspace_section_entry :: "heap \<Rightarrow> paddr \<Rightarrow> pde \<Rightarrow> vaddr set"
where
  "vspace_section_entry h r pde  \<equiv> {va. get_pde' h r va = Some pde}"






end
