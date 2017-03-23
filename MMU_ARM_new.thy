theory MMU_ARM_new

imports ARM_Monadic_Ops  PED_Cache

begin               



record tlb_state = state + 
           tlb_set :: "tlb_entry set \<times> pde_entry set"


record tlb_det_state = state + 
           tlb_det_set :: "tlb_entry set \<times> pde_entry set"

record tlb_sat_state = state + 
           tlb_sat_set :: "tlb_entry set \<times> pde_entry set"

record tlb_sat_state' = state + 
           tlb_sat_set' :: "tlb_entry set"

record tlb_incon_state = state + 
           tlb_incon_set :: "(asid \<times> va) set"




consts tlb_evict :: "(tlb_entry set \<times> pde_entry set) state_scheme \<Rightarrow> tlb_entry set \<times> pde_entry set"



definition 
  typ_tlb :: "'a tlb_state_scheme \<Rightarrow> (tlb_entry set \<times> pde_entry set) state_scheme"
where
  "typ_tlb s =  state.extend (state.truncate s)  (tlb_set s)"


definition 
  typ_det_tlb :: "'a tlb_det_state_scheme \<Rightarrow> (tlb_entry set \<times> pde_entry set) state_scheme"
where
  "typ_det_tlb s =  state.extend (state.truncate s) (tlb_det_set s)"


definition 
  typ_sat_tlb :: "'a tlb_sat_state_scheme \<Rightarrow> (tlb_entry set \<times> pde_entry set) state_scheme"
where
  "typ_sat_tlb s =  state.extend (state.truncate s) (tlb_sat_set s)"

definition 
  typ_sat_tlb' :: "'a tlb_sat_state'_scheme \<Rightarrow> tlb_entry set state_scheme"
where
  "typ_sat_tlb' s =  state.extend (state.truncate s) (tlb_sat_set' s)"


definition 
  typ_incon :: "'a tlb_incon_state_scheme \<Rightarrow> (asid \<times> va) set state_scheme"
where
  "typ_incon s =  state.extend (state.truncate s) (tlb_incon_set s)"



lemma tlb_more [simp]:
  "state.more (typ_tlb s) = tlb_set s"
  by (clarsimp simp: typ_tlb_def state.defs)


lemma tlb_det_more [simp]:
  "state.more (typ_det_tlb s) = tlb_det_set s"
  by (clarsimp simp: typ_det_tlb_def state.defs)


lemma tlb_sat_more [simp]:
  "state.more (typ_sat_tlb s) = tlb_sat_set s"
  by (clarsimp simp: typ_sat_tlb_def state.defs)

lemma tlb_sat_more' [simp]:
  "state.more (typ_sat_tlb' s) = tlb_sat_set' s"
  by (clarsimp simp: typ_sat_tlb'_def state.defs)

lemma tlb_incon_more [simp]:
  "state.more (typ_incon s) = tlb_incon_set s"
  by (clarsimp simp: typ_incon_def state.defs)

lemma tlb_truncate [simp]:
  "state.truncate (typ_tlb s') = state.truncate s'"
  by (clarsimp simp: typ_tlb_def state.defs)

lemma tlb_det_truncate [simp]:
  "state.truncate (typ_det_tlb s') = state.truncate s'"
  by (clarsimp simp: typ_det_tlb_def state.defs)

lemma tlb_sat_truncate [simp]:
  "state.truncate (typ_sat_tlb s') = state.truncate s'"
  by (clarsimp simp: typ_sat_tlb_def state.defs)

lemma tlb_sat_truncate' [simp]:
  "state.truncate (typ_sat_tlb' s') = state.truncate s'"
  by (clarsimp simp: typ_sat_tlb'_def state.defs)


lemma tlb_incon_truncate [simp]:
  "state.truncate (typ_incon s') = state.truncate s'"
  by (clarsimp simp: typ_incon_def state.defs)


lemma typ_prim_parameter [simp]:
  "ASID (typ_tlb s) = ASID s \<and> TTBR0 (typ_tlb s) =  TTBR0 s \<and> MEM (typ_tlb s) = MEM s \<and>
      exception (typ_tlb s) = exception s"
  by (clarsimp simp: typ_tlb_def  state.defs)


lemma typ_det_prim_parameter [simp]:
  "ASID (typ_det_tlb s) = ASID s \<and> TTBR0 (typ_det_tlb s) =  TTBR0 s \<and> MEM (typ_det_tlb s) = MEM s \<and>
      exception (typ_det_tlb s) = exception s"
  by (clarsimp simp: typ_det_tlb_def state.defs)


lemma typ_sat_prim_parameter [simp]:
  "ASID (typ_sat_tlb s) = ASID s \<and> TTBR0 (typ_sat_tlb s) =  TTBR0 s \<and> MEM (typ_sat_tlb s) = MEM s \<and>
      exception (typ_sat_tlb s) = exception s"
  by (clarsimp simp: typ_sat_tlb_def state.defs)


lemma typ_sat_prim_parameter' [simp]:
  "ASID (typ_sat_tlb' s) = ASID s \<and> TTBR0 (typ_sat_tlb' s) =  TTBR0 s \<and> MEM (typ_sat_tlb' s) = MEM s \<and>
      exception (typ_sat_tlb' s) = exception s"
  by (clarsimp simp: typ_sat_tlb'_def state.defs)


lemma typ_incon_prim_parameter [simp]:
  "ASID (typ_incon s) = ASID s \<and> TTBR0 (typ_incon s) =  TTBR0 s \<and> MEM (typ_incon s) = MEM s \<and>
      exception (typ_incon s) = exception s"
  by (clarsimp simp: typ_incon_def state.defs)


definition
  va_to_pa_sec :: "32 word \<Rightarrow> 32 word \<Rightarrow> 32 word"
where
  "va_to_pa_sec ba va \<equiv> (ucast ba << 12) OR (va AND mask 12)"

definition
  pte_tlb_entry :: "asid \<Rightarrow> heap \<Rightarrow> paddr \<Rightarrow> vaddr \<Rightarrow> tlb_entry"
where
    "pte_tlb_entry asid heap p v \<equiv> case get_pte heap p v 
                 of None                     \<Rightarrow> EntrySmall asid (ucast (addr_val v >> 12) :: 20 word) None 0
                 |  Some InvalidPTE          \<Rightarrow> EntrySmall asid (ucast (addr_val v >> 12) :: 20 word) None 0
                 |  Some (SmallPagePTE p1 a) \<Rightarrow> EntrySmall asid (ucast (addr_val v >> 12) :: 20 word) 
                                            (Some  ((word_extract 31 12 (addr_val p1)):: 20 word)) 0"


(*base address of the page table *)
fun
  pde_tlb_entry :: "pde_entry \<Rightarrow> heap  \<Rightarrow> vaddr \<Rightarrow> tlb_entry"
where
    "pde_tlb_entry (EntryPDE asid vSe None fl) mem  va = EntrySection asid (ucast (addr_val va >> 20) :: 12 word) None fl"
  | "pde_tlb_entry (EntryPDE asid vSe (Some (bpa_sec ba)) fl) mem  va = EntrySection asid (ucast (addr_val va >> 20) :: 12 word) (Some ((ucast (ba >> 20)) :: 12 word)) fl"
  | "pde_tlb_entry (EntryPDE asid vSe (Some (bpa_sm ba)) fl) mem  va = 
          pte_tlb_entry asid mem (Addr ba) va"

definition
 pairsub :: "tlb_entry set \<times> pde_entry set \<Rightarrow> tlb_entry set \<times> pde_entry set \<Rightarrow> tlb_entry set \<times> pde_entry set"
where
  "pairsub a b = (fst a - fst b , snd a - snd b)"

fun
 pairunion :: "tlb_entry set \<times> pde_entry set \<Rightarrow> tlb_entry set \<times> pde_entry set \<Rightarrow> tlb_entry set \<times> pde_entry set"
where
  "pairunion (a,b) (c,d) = (a \<union> c , b \<union> d)"


definition
  pde_walk :: "asid \<Rightarrow> heap \<Rightarrow> ttbr0 \<Rightarrow> vaddr \<Rightarrow> pde_entry"
where
  "pde_walk asid heap ttbr0 v\<equiv>
      case get_pde heap ttbr0 v
       of None                 \<Rightarrow> EntryPDE asid (ucast (addr_val v >> 20) :: 12 word) None 0
       | Some InvalidPDE       \<Rightarrow> EntryPDE asid (ucast (addr_val v >> 20) :: 12 word) None 0
       | Some ReservedPDE      \<Rightarrow> EntryPDE asid (ucast (addr_val v >> 20) :: 12 word) None 0
       | Some (SectionPDE p a) \<Rightarrow> 
          EntryPDE asid (ucast (addr_val v >> 20) :: 12 word) (Some (bpa_sec (addr_val p) ))  0
       | Some (PageTablePDE p) \<Rightarrow> 
              EntryPDE asid (ucast (addr_val v >> 20) :: 12 word) (Some (bpa_sm (addr_val p)))  0"

(* it should be a set, because we have to propagate the inconsistency in pde_cache to tlb*)
thm pde_entry_set_def



definition
  tlb_pde_walk :: "asid \<Rightarrow> pde_cache \<Rightarrow> heap \<Rightarrow> ttbr0 \<Rightarrow> vaddr \<Rightarrow> tlb_entry set"
where
  "tlb_pde_walk asid pde_set mem ttbr0 v \<equiv>
      case lookup_pde pde_set asid (addr_val v)
       of Hit_pde pde  \<Rightarrow> (case bpa_pde_entry pde of 
                                     None \<Rightarrow> {EntrySection asid (ucast (addr_val v >> 20) :: 12 word) None 0}
                                  |  Some (bpa_sec bps) \<Rightarrow> 
                                        {EntrySection asid (ucast (addr_val v >> 20) :: 12 word) (Some ((word_extract 31 20  bps):: 12 word))  0}      
                                  |  Some (bpa_sm ba) \<Rightarrow> {pte_tlb_entry asid mem (Addr ba) v} )
   |    Miss_pde  \<Rightarrow> {pt_walk asid mem ttbr0 v}
   |    Incon_pde \<Rightarrow> (\<lambda>x. pde_tlb_entry x mem v) ` pde_entry_set pde_set asid (addr_val v)"




(* TLB doesn't store page faults in this level of the model *)
definition
  "no_faults tlb pde_set \<equiv> (\<forall>e \<in> tlb. \<not>is_fault e) \<and>  (\<forall>e \<in> pde_set. \<not>is_fault_pde e)"



definition 
   asid_va_incon :: "tlb  \<Rightarrow> (asid \<times> va) set"
where                                                         
  "asid_va_incon tlb   \<equiv>  {(asid, va). lookup tlb asid va = Incon} "
       

definition 
   asid_va_incon' :: "tlb \<Rightarrow> pde_cache \<Rightarrow> (asid \<times> va) set"
where                                                         
  "asid_va_incon' tlb  pde_set \<equiv>  {(asid, va). lookup tlb asid va = Incon} \<union> {(asid, va). lookup_pde pde_set asid va = Incon_pde}"
       
definition
  saturated :: "(tlb_entry set \<times> pde_entry set) state_scheme \<Rightarrow> bool"
where
  "saturated s  \<equiv> pt_walk (ASID s) (MEM s) (TTBR0 s) ` UNIV \<subseteq> fst (state.more s) \<and>
  pde_walk (ASID s) (MEM s) (TTBR0 s) ` UNIV \<subseteq> snd (state.more s)"

definition
  saturated' :: "tlb_entry set state_scheme \<Rightarrow> bool"
where
  "saturated' s  \<equiv> pt_walk (ASID s) (MEM s) (TTBR0 s) ` UNIV \<subseteq> state.more s "

definition
  tlb_rel :: "(tlb_entry set \<times> pde_entry set) state_scheme \<Rightarrow> (tlb_entry set \<times> pde_entry set) state_scheme \<Rightarrow> bool"
where
  "tlb_rel s t \<equiv> state.truncate s = state.truncate t \<and> fst (state.more s) \<subseteq> fst (state.more t) \<and> snd (state.more s) \<subseteq> snd (state.more t) 
                  \<and> no_faults (fst (state.more t)) (snd (state.more t))"

thm tlb_rel_def
definition
  tlb_rel_flt :: "(tlb_entry set \<times> pde_entry set) state_scheme \<Rightarrow> (tlb_entry set \<times> pde_entry set) state_scheme \<Rightarrow> bool"
where
  "tlb_rel_flt s t \<equiv> state.truncate s = state.truncate t \<and> fst (state.more s) \<subseteq> fst (state.more t) \<and> snd (state.more s) \<subseteq> snd (state.more t) "


definition 
  tlb_rel_sat :: "(tlb_entry set \<times> pde_entry set) state_scheme \<Rightarrow> (tlb_entry set \<times> pde_entry set) state_scheme \<Rightarrow> bool"
where                                                                
  "tlb_rel_sat s t \<equiv> state.truncate s = state.truncate t \<and> fst (state.more s) \<subseteq> fst (state.more t) \<and> snd (state.more s) \<subseteq> snd (state.more t)  \<and>  
                     saturated t"
definition 
  tlb_rel_sat' :: " (tlb_entry set \<times> pde_entry set) state_scheme \<Rightarrow> tlb_entry set  state_scheme \<Rightarrow> bool"
where                                                                
  "tlb_rel_sat' s t \<equiv> state.truncate s = state.truncate t \<and> fst(state.more s) \<subseteq> state.more t  \<and>  saturated s \<and>
                     saturated' t"
      
     
definition 
  tlb_rel_abs :: "tlb_entry set  state_scheme \<Rightarrow> (asid \<times> va) set state_scheme \<Rightarrow> bool"
where                                                                
  "tlb_rel_abs s t \<equiv> state.truncate s = state.truncate t \<and> asid_va_incon  (state.more s) \<subseteq> state.more t"

 
definition 
  tlb_rel_abs' :: "(tlb_entry set \<times> pde_entry set) state_scheme \<Rightarrow> (asid \<times> va) set state_scheme \<Rightarrow> bool"
where                                                                
  "tlb_rel_abs' s t \<equiv> state.truncate s = state.truncate t \<and> asid_va_incon' (fst (state.more s)) (snd (state.more s)) \<subseteq> state.more t"



instantiation tlb_state_ext :: (type) mmu       
begin
  definition                          
  "(mmu_translate v :: ('a tlb_state_scheme \<Rightarrow> _))
 = do {
     update_state (\<lambda>s. s\<lparr> tlb_set := pairsub (tlb_set s)  (tlb_evict (typ_tlb s)) \<rparr>);
     mem   <- read_state MEM;
     asid  <- read_state ASID;
     ttbr0 <- read_state TTBR0;
     tlb_pde   <- read_state tlb_set;
     let tlb = fst tlb_pde;
     let pde_cache  = snd tlb_pde;
          case lookup tlb asid (addr_val v) of 
               Hit entry \<Rightarrow> if is_fault entry
                   then raise'exception(PAGE_FAULT ''more info'') 
                   else return (Addr (va_to_pa (addr_val v) entry))
          |    Miss \<Rightarrow> 
                   (case lookup_pde pde_cache asid (addr_val v) of
                         Hit_pde pde_entry \<Rightarrow> do { 
                                    if is_fault_pde pde_entry
                                    then raise'exception (PAGE_FAULT ''more info'')
                                    else do {
                                         let entry = pde_tlb_entry pde_entry mem v;
                                         if is_fault entry 
                                         then raise'exception (PAGE_FAULT ''more info'')
                                         else do {
                                              update_state (\<lambda>s. s\<lparr> tlb_set := pairunion (tlb_set s)  ({entry} , {}) \<rparr>);
                                              return (Addr (va_to_pa (addr_val v) entry)) }
                                              } 
                                           }
                     |   Miss_pde \<Rightarrow> do { 
                                    let pde  = pde_walk asid mem ttbr0 v;
                                    if is_fault_pde pde
                                    then raise'exception (PAGE_FAULT ''more info'')
                                    else do {
                                         update_state (\<lambda>s. s\<lparr> tlb_set := pairunion (tlb_set s)  ({} , {pde}) \<rparr>);
                                         let entry = pt_walk asid mem ttbr0 v;
                                         if is_fault entry 
                                         then raise'exception (PAGE_FAULT ''more info'')
                                         else do {
                                              update_state (\<lambda>s. s\<lparr> tlb_set := pairunion (tlb_set s)  ({entry} , {}) \<rparr>);
                                              return (Addr (va_to_pa (addr_val v) entry)) }
                                              } 
                                           }
                      |   Incon_pde  \<Rightarrow> raise'exception (IMPLEMENTATION_DEFINED ''set on fire''))
         | Incon \<Rightarrow> raise'exception (IMPLEMENTATION_DEFINED ''set on fire'') 
   }"

thm mmu_translate_tlb_state_ext_def                    
  instance ..
end



instantiation tlb_det_state_ext :: (type) mmu       
begin
  definition                          
  "(mmu_translate v :: ('a tlb_det_state_scheme \<Rightarrow> _))
 = do {
     mem   <- read_state MEM;
     asid  <- read_state ASID;
     ttbr0 <- read_state TTBR0;
     tlb_pde   <- read_state tlb_det_set;
     let tlb = fst tlb_pde;
     let pde_cache  = snd tlb_pde;
          case lookup tlb asid (addr_val v) of 
               Hit entry \<Rightarrow> if is_fault entry
                   then raise'exception(PAGE_FAULT ''more info'') 
                   else return (Addr (va_to_pa (addr_val v) entry))
          |    Miss \<Rightarrow> 
                   (case lookup_pde pde_cache asid (addr_val v) of
                         Hit_pde pde_entry \<Rightarrow> do { 
                                    if is_fault_pde pde_entry
                                    then raise'exception (PAGE_FAULT ''more info'')
                                    else do {
                                         let entry = pde_tlb_entry pde_entry mem v;
                                         if is_fault entry 
                                         then raise'exception (PAGE_FAULT ''more info'')
                                         else do {
                                              update_state (\<lambda>s. s\<lparr> tlb_det_set := pairunion (tlb_det_set s)  ({entry} , {}) \<rparr>);
                                              return (Addr (va_to_pa (addr_val v) entry)) }
                                              } 
                                           }
                     |   Miss_pde \<Rightarrow> do { 
                                    let pde  = pde_walk asid mem ttbr0 v;
                                    if is_fault_pde pde
                                    then raise'exception (PAGE_FAULT ''more info'')
                                    else do {
                                         update_state (\<lambda>s. s\<lparr> tlb_det_set := pairunion (tlb_det_set s)  ({} , {pde}) \<rparr>);
                                         let entry = pt_walk asid mem ttbr0 v;
                                         if is_fault entry 
                                         then raise'exception (PAGE_FAULT ''more info'')
                                         else do {
                                              update_state (\<lambda>s. s\<lparr> tlb_det_set := pairunion (tlb_det_set s)  ({entry} , {}) \<rparr>);
                                              return (Addr (va_to_pa (addr_val v) entry)) }
                                              } 
                                           }
                      |   Incon_pde  \<Rightarrow> raise'exception (IMPLEMENTATION_DEFINED ''set on fire''))
         | Incon \<Rightarrow> raise'exception (IMPLEMENTATION_DEFINED ''set on fire'') 
   }"
                  
  instance ..
end


thm pde_walk_def

thm tlb_pde_walk_def


instantiation tlb_sat_state_ext :: (type) mmu    
begin
definition   
 "(mmu_translate v :: ('a tlb_sat_state_scheme \<Rightarrow> _))
 = do {
     mem   <- read_state MEM;
     asid  <- read_state ASID;
     ttbr0 <- read_state TTBR0;
     let all_pdes = pde_walk asid mem ttbr0 ` UNIV;
     let all_tlbes = \<Union>(tlb_pde_walk asid all_pdes mem ttbr0 ` UNIV);
     tlb_pde0   <- read_state tlb_sat_set;
     let tlb0 = fst tlb_pde0;
     let pde_cache0  = snd tlb_pde0;
     let tlb_pde = pairunion tlb_pde0 (all_tlbes , all_pdes) ;
     update_state (\<lambda>s. s\<lparr> tlb_sat_set := tlb_pde \<rparr>);
          case lookup (fst tlb_pde) asid (addr_val v) of
            Hit entry \<Rightarrow> if is_fault entry 
              then raise'exception (PAGE_FAULT ''more info'')
                else return (Addr (va_to_pa (addr_val v) entry))
          | Miss \<Rightarrow> raise'exception (ASSERT ''impossible'')
          | Incon \<Rightarrow> raise'exception (IMPLEMENTATION_DEFINED ''set on fire'')
   }" 
   
  instance ..
end


instantiation tlb_sat_state'_ext :: (type) mmu    
begin
definition   
 "(mmu_translate v :: ('a tlb_sat_state'_scheme \<Rightarrow> _))
 = do {
     mem   <- read_state MEM;
     asid  <- read_state ASID;
     ttbr0 <- read_state TTBR0;
     let all_entries = pt_walk asid mem ttbr0 ` UNIV;
     tlb0   <- read_state tlb_sat_set';
     let tlb = tlb0 \<union> all_entries;
     update_state (\<lambda>s. s\<lparr> tlb_sat_set' := tlb \<rparr>);
          case lookup tlb asid (addr_val v) of
            Hit entry \<Rightarrow> if is_fault entry 
              then raise'exception (PAGE_FAULT ''more info'')
                else return (Addr (va_to_pa (addr_val v) entry))
          | Miss \<Rightarrow> raise'exception (ASSERT ''impossible'')
          | Incon \<Rightarrow> raise'exception (IMPLEMENTATION_DEFINED ''set on fire'')
   }" 
   
  instance ..
end

thm  mmu_translate_tlb_sat_state'_ext_def


instantiation tlb_incon_state_ext :: (type) mmu    
begin
definition   
 "(mmu_translate v :: ('a tlb_incon_state_scheme \<Rightarrow> _))
  = do {
     mem   <- read_state MEM;
     asid  <- read_state ASID;
     ttbr0 <- read_state TTBR0;
     incon_set <- read_state tlb_incon_set;
     if (asid , addr_val v) \<in> incon_set
       then raise'exception (IMPLEMENTATION_DEFINED ''set on fire'')
       else let entry = pt_walk asid mem ttbr0 v in 
             if is_fault entry
              then raise'exception (PAGE_FAULT ''more info'')
              else return (Addr (va_to_pa (addr_val v) entry))
    }"

  instance ..
end

thm mmu_translate_tlb_incon_state_ext_def

(* thm arg_cong
thm state.cases_scheme  *)


definition
  "consistent0 m asid ttbr0 tlb pde_cache va \<equiv>
     lookup tlb asid (addr_val va) = Hit (pt_walk asid m ttbr0 va) \<or>
     (lookup tlb asid (addr_val va) = Miss \<and> 
      (lookup_pde pde_cache asid (addr_val va) = Miss_pde \<or> lookup_pde pde_cache asid (addr_val va) = Hit_pde (pde_walk asid m ttbr0 va)) ) "



abbreviation
  "consistent (s:: (tlb_entry set \<times> pde_entry set) state_scheme) \<equiv>
               consistent0 (MEM s) (ASID s) (TTBR0 s) (fst (state.more s)) (snd (state.more s))"

(* TLB consistency for an address va: if we look up va, the result is not Incon, 
   and if it is Hit, then it agrees with the page table *)

lemma tlb_relD:
  "tlb_rel s t \<Longrightarrow> ASID t = ASID s \<and> MEM t = MEM s \<and> TTBR0 t = TTBR0 s \<and>
      fst (state.more s) \<subseteq> fst (state.more t) \<and> snd (state.more s) \<subseteq> snd (state.more t)  \<and> exception t = exception s"
  by (clarsimp simp: tlb_rel_def state.defs)


definition
  "consistent0' m asid ttbr0 tlb pde_cache va \<equiv>
     (lookup tlb asid (addr_val va) = Hit (pt_walk asid m ttbr0 va) \<or>  lookup tlb asid (addr_val va) = Miss ) \<and> 
     (lookup_pde pde_cache asid (addr_val va) = Miss_pde \<or> lookup_pde pde_cache asid (addr_val va) = Hit_pde (pde_walk asid m ttbr0 va))  "


abbreviation
  "consistent' (s:: (tlb_entry set \<times> pde_entry set) state_scheme) \<equiv>
               consistent0' (MEM s) (ASID s) (TTBR0 s) (fst (state.more s)) (snd (state.more s))"

lemma consistent_not_Incon_01:
  "consistent0' m asid ttbr0 tlb pde_set va \<Longrightarrow>
  (lookup tlb asid (addr_val va) \<noteq> Incon \<and> (\<forall>e. lookup tlb asid (addr_val va) = Hit e \<longrightarrow> e = pt_walk asid m ttbr0 va) \<and>
  lookup_pde pde_set asid (addr_val va) \<noteq> Incon_pde \<and> (\<forall>e. lookup_pde pde_set asid (addr_val va) = Hit_pde e \<longrightarrow> e = pde_walk asid m ttbr0 va) ) "
  apply (clarsimp simp: consistent0'_def) by force


lemma consistent_not_Incon_02:
  " (lookup tlb asid (addr_val va) \<noteq> Incon \<and> (\<forall>e. lookup tlb asid (addr_val va) = Hit e \<longrightarrow> e = pt_walk asid m ttbr0 va) \<and>
  lookup_pde pde_set asid (addr_val va) \<noteq> Incon_pde \<and> (\<forall>e. lookup_pde pde_set asid (addr_val va) = Hit_pde e \<longrightarrow> e = pde_walk asid m ttbr0 va) ) \<Longrightarrow>
  consistent0' m asid ttbr0 tlb pde_set va"
  apply (clarsimp simp: consistent0'_def)
  by (metis lookup_pde_type.exhaust lookup_type.exhaust)

lemma consistent_not_Incon':
  "consistent0' m asid ttbr0 tlb pde_set va =
   (lookup tlb asid (addr_val va) \<noteq> Incon \<and> (\<forall>e. lookup tlb asid (addr_val va) = Hit e \<longrightarrow> e = pt_walk asid m ttbr0 va) \<and>
  lookup_pde pde_set asid (addr_val va) \<noteq> Incon_pde \<and> (\<forall>e. lookup_pde pde_set asid (addr_val va) = Hit_pde e \<longrightarrow> e = pde_walk asid m ttbr0 va) )"
apply (rule iffI)
   apply (clarsimp simp: consistent_not_Incon_01)
by (clarsimp simp: consistent_not_Incon_02)



definition
  "consistent0'' m asid ttbr0 tlb va \<equiv>
     lookup tlb asid (addr_val va) = Hit (pt_walk asid m ttbr0 va) \<or>
     lookup tlb asid (addr_val va) = Miss"

abbreviation
  "consistent'' (s::tlb_entry set state_scheme) \<equiv>
               consistent0'' (MEM s) (ASID s) (TTBR0 s) (state.more s)"


lemma consistent_not_Incon'':
  "consistent0'' m asid ttbr0 tlb va = 
  (lookup tlb asid (addr_val va) \<noteq> Incon \<and> (\<forall>e. lookup tlb asid (addr_val va) = Hit e \<longrightarrow> e = pt_walk asid m ttbr0 va))"
  by (cases "lookup tlb asid (addr_val va)"; simp add: consistent0''_def)


lemma consistent_not_Incon''_implies:
  "consistent0'' m asid ttbr0 tlb va \<Longrightarrow>
  (lookup tlb asid (addr_val va) \<noteq> Incon \<and> (\<forall>e. lookup tlb asid (addr_val va) = Hit e \<longrightarrow> e = pt_walk asid m ttbr0 va))"
  by (cases "lookup tlb asid (addr_val va)"; simp add: consistent0''_def)


lemma tlb_rel_consistent:
  "\<lbrakk> tlb_rel s t; consistent' t va \<rbrakk> \<Longrightarrow> consistent' s va"
  by (insert tlb_relD [of s t] , clarsimp , drule tlb_mono [of _ _ "ASID s" "(addr_val va)"],
      drule tlb_pde_mono [of _ _ "ASID s" "(addr_val va)"] , auto simp: consistent0'_def less_eq_lookup_type less_eq_lookup_pde_type typ_det_tlb_def state.defs)



lemma tlb_rel_fltD:
  "tlb_rel_flt s t \<Longrightarrow>
     ASID t = ASID s \<and> MEM t = MEM s \<and> TTBR0 t = TTBR0 s \<and> fst (state.more s) \<subseteq> fst (state.more t) \<and> snd (state.more s) \<subseteq> snd (state.more t) \<and> exception t = exception s"
   by (clarsimp simp: tlb_rel_flt_def state.defs)


lemma tlb_rel_flt_consistent:
  "\<lbrakk> tlb_rel_flt s t; consistent' t va \<rbrakk> \<Longrightarrow> consistent' s va"
  by (insert tlb_rel_fltD [of s t] , clarsimp , drule tlb_mono [of _ _ "ASID s" "addr_val va"] , 
    drule tlb_pde_mono [of _ _ "ASID s" "(addr_val va)"] , auto simp: consistent0'_def less_eq_lookup_type less_eq_lookup_pde_type)



lemma tlb_rel_satD:
  "tlb_rel_sat s t \<Longrightarrow>
      ASID t = ASID s \<and> MEM t = MEM s \<and> TTBR0 t = TTBR0 s \<and> fst (state.more s) \<subseteq> fst (state.more t) \<and> snd (state.more s) \<subseteq> snd (state.more t) \<and> 
      exception t = exception s  \<and> saturated t"
  by (clarsimp simp: tlb_rel_sat_def state.defs)



lemma subset_pairunion [simp]:
   "\<lbrakk>a \<subseteq> fst s; b \<subseteq> snd s\<rbrakk>  \<Longrightarrow> s = pairunion s (a, b)"
 by (metis pairunion.simps prod.collapse sup.orderE)


lemma sat_state_tlb :
  "\<lbrakk>saturated s \<rbrakk> \<Longrightarrow> 
     state.more s = pairunion (state.more s)  (pt_walk (ASID s) (MEM s) (TTBR0 s) ` UNIV, pde_walk (ASID s) (MEM s) (TTBR0 s) ` UNIV)"
  by (clarsimp simp: saturated_def )

  
lemma tlb_rel_sat_consistent:
  "\<lbrakk> tlb_rel_sat s t; consistent' t va \<rbrakk> \<Longrightarrow> consistent' s va"
  by (insert tlb_rel_satD [of s t] , clarsimp ,drule tlb_mono [of _ _ "ASID s" "(addr_val va)"] ,
      drule tlb_pde_mono [of _ _ "ASID s" "(addr_val va)"], auto simp: consistent0'_def less_eq_lookup_type less_eq_lookup_pde_type)
  



lemma tlb_rel_satD':
  "tlb_rel_sat' s t \<Longrightarrow>
      ASID t = ASID s \<and> MEM t = MEM s \<and> TTBR0 t = TTBR0 s \<and> fst (state.more s) \<subseteq> state.more t \<and> 
      exception t = exception s  \<and> saturated' t"
  by (clarsimp simp: tlb_rel_sat'_def state.defs)


lemma sat_state_tlb':
  "\<lbrakk>saturated' s \<rbrakk> \<Longrightarrow> 
     state.more s = state.more s \<union> pt_walk (ASID s) (MEM s) (TTBR0 s) ` UNIV"
  by (fastforce simp: saturated'_def)


lemma tlb_rel_sat_consistent':
  "\<lbrakk> tlb_rel_sat' s t; consistent'' t va \<rbrakk> \<Longrightarrow> 
   lookup (fst (state.more s)) (ASID s) (addr_val va) = Hit (pt_walk (ASID s) (MEM s) (TTBR0 s) va) \<or>
     lookup (fst (state.more s)) (ASID s) (addr_val va) = Miss"
  by (insert tlb_rel_satD' [of s t] , clarsimp , 
   drule tlb_mono [of _ _ "ASID s" "(addr_val va)"] , auto simp: consistent0''_def  consistent0'_def less_eq_lookup_type)
 


lemma lookup_in_tlb:
  "lookup tlb asid va = Hit e \<Longrightarrow> e \<in> tlb"
  by (auto simp: lookup_def entry_set_def split: split_if_asm)


lemma pde_lookup_in_tlb:
  "lookup_pde pde asid va = Hit_pde e \<Longrightarrow> e \<in> pde"
  by (auto simp: lookup_pde_def pde_entry_set_def split: split_if_asm)

lemma entry_set_insert:
  "\<lbrakk> entry_set tlb asid va = {}; asid_entry e = asid; va \<in> entry_range e \<rbrakk> \<Longrightarrow> 
  entry_set (insert e tlb) asid va = {e}"
  by (auto simp add: entry_set_def entry_range_asid_tags_def)

lemma asid_entry_pt_walk [simp]:
  "asid_entry (pt_walk asid m ttbr0 va) = asid"
  apply (simp add: pt_walk_def Let_def)
  apply ((((cases "get_pde m ttbr0 va" ; clarsimp) , case_tac a ; clarsimp) , 
      case_tac "get_pte m x3 va" ; clarsimp) , case_tac a ; clarsimp)
  done

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

lemma asid_entry_range [simp, intro!]:
  "addr_val va \<in> entry_range (pt_walk asid m ttbr0 va)"
  apply (clarsimp simp: entry_range_def pt_walk_def Let_def)
  by ((((cases "get_pde m ttbr0 va" ; clarsimp) , case_tac a ; clarsimp) , 
      case_tac "get_pte m x3 va" ; clarsimp) , case_tac a ; clarsimp)

lemma asid_entry_range1 [simp, intro!]:
  "va \<in> entry_range (pt_walk asid m ttbr0 (Addr va))"
  apply (clarsimp simp: entry_range_def pt_walk_def Let_def)
  by ((((cases "get_pde m ttbr0 (Addr va)" ; clarsimp) , case_tac a ; clarsimp) , 
      case_tac "get_pte m x3 (Addr va)" ; clarsimp) , case_tac a ; clarsimp)


lemma pde_asid_entry_range1 [simp, intro!]:
  "va \<in> pde_entry_range (pde_walk asid m ttbr0 (Addr va))"
  by (clarsimp simp: pde_walk_def Let_def, ((cases "get_pde m ttbr0 (Addr va)" ; clarsimp) , case_tac a ; clarsimp))


lemma lookup_refill:
  "lookup tlb asid (addr_val va) = Miss \<Longrightarrow>
   lookup (insert (pt_walk asid m ttrb0 va) tlb) asid (addr_val va) = Hit (pt_walk asid m ttrb0 va)"
   by (clarsimp simp: lookup_def entry_set_insert [where e="pt_walk asid m ttrb0 va"] split: split_if_asm)



lemma sat_state_lookup_not_miss:
  "\<lbrakk>saturated s\<rbrakk> \<Longrightarrow> \<forall>va. lookup (fst (state.more s)) (ASID s) va \<noteq> Miss"
  by (clarsimp simp: saturated_def lookup_def entry_set_def entry_range_asid_tags_def,  force)
 


lemma sat_state_lookup_not_miss':
  "\<lbrakk>saturated' s\<rbrakk> \<Longrightarrow> \<forall>va. lookup (state.more s) (ASID s) va \<noteq> Miss"
  by (clarsimp simp: saturated'_def lookup_def entry_set_def entry_range_asid_tags_def split:split_if_asm , force)



lemma entry_set_ptwalk_not_miss [simp]:
  "entry_set (range (pt_walk asid mem ttbr0)) asid v \<noteq> {}"
  by (clarsimp simp: entry_set_def  , rule_tac x = "pt_walk asid mem ttbr0 (Addr v)" in exI,
         simp add: entry_range_asid_tags_def)

lemma saturated_fst_not_miss:
  "lookup (fst (tlb_sat_set s) \<union> range (pt_walk asid mem ttbr0)) asid v \<noteq> Miss"
  by (clarsimp simp: lookup_def split:split_if_asm , insert entry_set_ptwalk_not_miss [of asid mem ttbr0 v],
         force simp: entry_set_def)


lemma  asid_pde_walk:
  "pde_entry_asid (pde_walk asid mem ttbr0 v) = asid"
  by (clarsimp simp: pde_walk_def , cases "get_pde mem ttbr0 v" , simp  ,case_tac a ; simp)


lemma saturated_pde_entry_set [intro!]:
  "\<lbrakk>saturated s\<rbrakk> \<Longrightarrow>pde_entry_set (snd (state.more s)) (ASID s) va \<noteq> {}"
  apply (clarsimp simp: pde_entry_set_def pde_entry_range_asid_tags_def ,rule_tac x= "pde_walk (ASID s) (MEM s) (TTBR0 s) (Addr va)" in exI , simp add: asid_pde_walk)
  using contra_subsetD saturated_def by auto

lemma pde_sat_state_lookup_not_miss:
  "\<lbrakk>saturated s\<rbrakk> \<Longrightarrow> \<forall>va. lookup_pde (snd (state.more s)) (ASID s) va \<noteq> Miss_pde"
  apply (clarsimp simp: lookup_pde_def split:split_if_asm)
  apply (insert saturated_pde_entry_set [of s _])
  apply simp
  done


lemma pde_entry_set_insert [simp]:
  "\<lbrakk> pde_entry_set tlb asid va = {}; pde_entry_asid e = asid; va \<in> pde_entry_range e \<rbrakk> \<Longrightarrow> 
  pde_entry_set (insert e tlb) asid va = {e}"
  by (auto simp add: pde_entry_set_def pde_entry_range_asid_tags_def)


lemma to_do:
  " PED_Cache.lookup_pde pde_set asid (addr_val va) = Miss_pde \<Longrightarrow>
    PED_Cache.lookup_pde (insert (pde_walk asid m ttrb0 va) pde_set) asid (addr_val va) = Hit_pde (pde_walk asid m ttrb0 va) "
  apply (clarsimp simp: lookup_pde_def pde_entry_set_insert [where e="pde_walk asid m ttrb0 va"] split: split_if_asm)
  apply (rule conjI , clarsimp simp: pde_entry_set_def , blast)
  apply (rule_tac x = "pde_walk asid m ttrb0 va" in exI, clarsimp simp: pde_entry_set_def )
  by ((safe ; clarsimp simp: pde_entry_range_asid_tags_def pde_walk_def) ,((cases "get_pde m ttrb0 va" ; clarsimp) , case_tac a; clarsimp ))

  
lemma awesome:
  "pde_tlb_entry (pde_walk (ASID s) (MEM s) (TTBR0 s) va) (MEM s) va =
       pt_walk (ASID s) (MEM s) (TTBR0 s) va "
  apply ((clarsimp simp: pde_walk_def pt_walk_def, cases "get_pde (MEM s) (TTBR0 s) va" ; clarsimp), (case_tac a ; clarsimp simp: mask_def))
  by ((case_tac "get_pte (MEM s) x3 va" ; clarsimp simp: pte_tlb_entry_def), word_bitwise)


definition
  tlb_rel' :: "(tlb_entry set \<times> pde_entry set) state_scheme \<Rightarrow> (tlb_entry set \<times> pde_entry set) state_scheme \<Rightarrow> bool"
where
  "tlb_rel' s t \<equiv> state.truncate s = state.truncate t \<and> fst (state.more s) \<subseteq> fst (state.more t)  \<and> no_faults (fst (state.more t)) (snd (state.more t))"


definition
  tlb_rel_flt' :: "(tlb_entry set \<times> pde_entry set) state_scheme \<Rightarrow> (tlb_entry set \<times> pde_entry set) state_scheme \<Rightarrow> bool"
where
  "tlb_rel_flt' s t \<equiv> state.truncate s = state.truncate t \<and> fst (state.more s) \<subseteq> fst (state.more t) "


lemma  mmu_translate_det_refine:
  "\<lbrakk> mmu_translate va s = (pa, s'); consistent' (typ_det_tlb t) va;  tlb_rel (typ_det_tlb s) (typ_det_tlb t) \<rbrakk> \<Longrightarrow>
  let (pa', t') = mmu_translate va t
  in pa' = pa \<and> consistent' (typ_det_tlb t') va \<and> tlb_rel' (typ_det_tlb s') (typ_det_tlb t')"
  apply (frule (1) tlb_rel_consistent , clarsimp)
  apply (frule consistent_not_Incon_01 , clarsimp)
  apply (frule tlb_relD , clarsimp)
  apply (insert tlb_mono [of "fst (tlb_det_set s)"  "fst (tlb_det_set t)" "ASID s" "(addr_val va)"])
  apply (clarsimp simp: mmu_translate_tlb_det_state_ext_def split_def Let_def tlb_rel_def tlb_rel'_def typ_det_tlb_def split: split_if_asm)
  apply (cases "lookup (fst (tlb_det_set t)) (ASID s) (addr_val va)" ; clarsimp)
   apply (cases "PED_Cache.lookup_pde (snd (tlb_det_set t)) (ASID s) (addr_val va) " ; clarsimp)
    apply (subgoal_tac "PED_Cache.lookup_pde (snd (tlb_det_set s)) (ASID s) (addr_val va) = Miss_pde" )
     prefer 2
     apply (clarsimp simp: consistent0'_def, drule_tac a = "(ASID s)" and v = "addr_val va" in  tlb_pde_mono; clarsimp)
    apply ((clarsimp simp: Let_def raise'exception_def  state.defs consistent0'_def split_def split:split_if_asm);
            (cases "tlb_det_set t", cases "tlb_det_set s" , clarsimp simp: no_faults_def subset_insertI2 to_do  lookup_refill  fst_def snd_def) )
   apply (cases "PED_Cache.lookup_pde (snd (tlb_det_set s)) (ASID s) (addr_val va)" ; clarsimp simp: Let_def consistent0'_def)
    apply (clarsimp split: split_if_asm)
     apply (clarsimp simp: raise'exception_def  state.defs split:split_if_asm)
    apply ((clarsimp simp: Let_def awesome split: split_if_asm) ,
              ((clarsimp simp: raise'exception_def  fst_def snd_def state.defs split:split_if_asm) ,
                   (cases "tlb_det_set t", cases "tlb_det_set s" , fastforce) ,  (cases "tlb_det_set t", cases "tlb_det_set s", fastforce)))
    apply ((clarsimp simp:  consistent0'_def fst_def snd_def state.defs),
               (cases "tlb_det_set t", cases "tlb_det_set s" , clarsimp simp: no_faults_def subset_insertI2 to_do pde_lookup_in_tlb lookup_refill))
   apply (clarsimp simp: raise'exception_def  fst_def snd_def state.defs split: split_if_asm)
   apply ((clarsimp simp: Let_def raise'exception_def fst_def snd_def state.defs split: split_if_asm),
           ((clarsimp simp: awesome consistent0'_def fst_def snd_def  state.defs) ,
                  (cases "tlb_det_set t", cases "tlb_det_set s" , clarsimp simp: no_faults_def subset_insertI2 to_do pde_lookup_in_tlb lookup_refill)))
  apply (cases "lookup (fst (tlb_det_set s)) (ASID s) (addr_val va)" ; clarsimp)
   apply (cases "PED_Cache.lookup_pde (snd (tlb_det_set s)) (ASID s) (addr_val va)" ; clarsimp)
     apply (clarsimp simp: Let_def split: split_if_asm)
        apply (clarsimp simp: raise'exception_def  fst_def snd_def state.defs split:split_if_asm)
       apply (clarsimp simp: is_fault_def is_fault_pde_def pt_walk_def pde_walk_def ; (cases "get_pde (MEM s) (TTBR0 s) va" ; clarsimp; case_tac a ; clarsimp))
      apply ((clarsimp simp: raise'exception_def  fst_def snd_def state.defs split:split_if_asm) ;
                   ((cases "tlb_det_set t", cases "tlb_det_set s") , clarsimp , blast))
     apply (clarsimp simp: fst_def snd_def state.defs split:split_if_asm)
     apply (cases "tlb_det_set t", cases "tlb_det_set s" , fastforce simp: lookup_in_tlb)
    apply (clarsimp simp: consistent0'_def)
   apply (subgoal_tac "x3 = pde_walk (ASID s) (MEM s) (TTBR0 s) va")
    prefer 2
    apply (clarsimp simp: consistent0'_def)
   apply (clarsimp split: split_if_asm)
      apply (clarsimp simp: raise'exception_def  fst_def snd_def state.defs split:split_if_asm)
     apply (subgoal_tac "is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) va)" ; clarsimp)
     apply ((clarsimp simp: is_fault_def is_fault_pde_def pt_walk_def pde_walk_def , cases "get_pde (MEM s) (TTBR0 s) va"; clarsimp), (case_tac a ; clarsimp))
    apply (clarsimp simp: awesome raise'exception_def fst_def snd_def state.defs split:split_if_asm)
   apply (clarsimp simp: awesome Let_def fst_def snd_def state.defs split:split_if_asm)
   apply (cases "tlb_det_set t", cases "tlb_det_set s"  , fastforce simp: lookup_in_tlb)
  apply (clarsimp simp: raise'exception_def  fst_def snd_def state.defs split:split_if_asm)
done



lemma [simp]: 
  "fst (tlb_set s) \<subseteq> fst (tlb_det_set t) \<Longrightarrow> fst (tlb_set s) - fst (tlb_evict (typ_tlb s)) \<subseteq> fst (tlb_det_set t)"
  by blast

lemma [simp]: 
  "snd (tlb_set s) \<subseteq> snd (tlb_det_set t) \<Longrightarrow> snd (tlb_set s) - snd (tlb_evict (typ_tlb s)) \<subseteq> snd (tlb_det_set t)"
  by blast


lemma is_fault_pde_is_fault_pt :
  "is_fault_pde (pde_walk (ASID s) (MEM s) (TTBR0 s) va) \<Longrightarrow> is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) va)"
  by ((clarsimp simp: is_fault_def is_fault_pde_def pt_walk_def pde_walk_def) , (cases "get_pde (MEM s) (TTBR0 s) va"; clarsimp) ,
        (case_tac a ; clarsimp))



(* refinement between eviction and deterministic TLB lookups *)
lemma  mmu_translate_det_evict_refine:
  "\<lbrakk> mmu_translate va s = (pa, s');  consistent' (typ_det_tlb t) va; tlb_rel (typ_tlb s) (typ_det_tlb t) \<rbrakk> \<Longrightarrow>
  let (pa', t') = mmu_translate va t
  in pa' = pa  \<and> consistent' (typ_det_tlb t') va \<and> tlb_rel' (typ_tlb s') (typ_det_tlb t')"
  apply (frule (1) tlb_rel_consistent , clarsimp)
  apply (frule consistent_not_Incon_01 , clarsimp)
  apply (frule tlb_relD , clarsimp)
  apply (insert tlb_mono [of "(fst (tlb_set s) - fst (tlb_evict (typ_tlb s)))"  "(fst(tlb_det_set t))" "ASID s" "(addr_val va)"] , simp )
  apply (insert tlb_pde_mono [of "(snd (tlb_set s) - snd (tlb_evict (typ_tlb s)))"  "(snd(tlb_det_set t))" "ASID s" "(addr_val va)"] ,simp)
  apply (insert Diff_subset [of "fst (tlb_set s)" "fst (tlb_evict (typ_tlb s))"])
  apply (insert Diff_subset [of "snd (tlb_set s)" "snd (tlb_evict (typ_tlb s))"])
  apply (clarsimp simp: mmu_translate_tlb_state_ext_def mmu_translate_tlb_det_state_ext_def split_def Let_def pairsub_def
  tlb_rel_def tlb_rel'_def typ_det_tlb_def typ_tlb_def  split: split_if_asm)
  apply (cases "lookup (fst(tlb_det_set t)) (ASID s) (addr_val va)" ; clarsimp)
   apply (cases "PED_Cache.lookup_pde (snd (tlb_det_set t)) (ASID s) (addr_val va) " ; clarsimp)
    apply (clarsimp simp: Let_def split:split_if_asm)
      apply (((clarsimp simp: raise'exception_def Let_def  state.defs split:split_if_asm) , blast) ,
             ((clarsimp simp: consistent0'_def fst_def snd_def) , (cases "tlb_det_set t", cases "tlb_set s"), fastforce))
     apply ((clarsimp simp: raise'exception_def consistent0'_def fst_def snd_def  no_faults_def subset_insertI2 state.defs split:split_if_asm);
            ((cases "tlb_det_set t", cases "tlb_set s") , (force simp: to_do) ))
    apply ((clarsimp simp: fst_def snd_def state.defs), (cases "tlb_det_set t", cases "tlb_set s") ,
         (clarsimp simp: consistent0'_def to_do lookup_refill no_faults_def subset_insertI2 fst_def snd_def))
   apply (cases "lookup_pde (snd (tlb_set s) - snd (tlb_evict (state.extend (state.truncate s) (tlb_set s)))) (ASID s) (addr_val va)" ; clarsimp)
    apply (clarsimp simp: Let_def split_if_asm)
    apply ((clarsimp simp: raise'exception_def state.defs split:split_if_asm) ,blast, blast)
    apply (clarsimp simp: Let_def awesome split_if_asm)
    apply ((clarsimp simp: raise'exception_def state.defs split:split_if_asm) , blast , blast)
    apply (clarsimp simp: consistent0'_def fst_def snd_def state.defs,
             cases "tlb_det_set t", cases "tlb_set s" , clarsimp simp: no_faults_def subset_insertI2 fst_def snd_def lookup_refill split:split_if_asm)
   apply (clarsimp split: split_if_asm)
    apply ((clarsimp simp: raise'exception_def state.defs split:split_if_asm) ,blast , blast)
   apply (clarsimp simp: Let_def split: split_if_asm)
    apply ((clarsimp simp: raise'exception_def  state.defs split:split_if_asm) , blast, blast)
   apply (clarsimp simp: awesome consistent0'_def fst_def snd_def  state.defs, cases "tlb_det_set t", cases "tlb_set s", clarsimp simp: no_faults_def subset_insertI2 fst_def snd_def lookup_refill  split:split_if_asm)
  apply (cases "lookup (fst (tlb_set s) - fst (tlb_evict (state.extend (state.truncate s) (tlb_set s)))) (ASID s) (addr_val va) " ; clarsimp)
   apply (cases "lookup_pde (snd (tlb_set s) - snd (tlb_evict (state.extend (state.truncate s) (tlb_set s)))) (ASID s) (addr_val va)"; clarsimp)
    apply (clarsimp simp: Let_def split: split_if_asm)
      apply (clarsimp simp: raise'exception_def state.defs split:split_if_asm) apply blast apply blast
     apply (clarsimp simp: is_fault_def is_fault_pde_def pt_walk_def pde_walk_def)
     apply ((cases "get_pde (MEM s) (TTBR0 s) va" ; clarsimp) , (case_tac a ; clarsimp))
     apply (clarsimp simp: raise'exception_def state.defs split:split_if_asm , blast, blast)
    apply ((clarsimp simp: raise'exception_def lookup_in_tlb state.defs split:split_if_asm) , blast)
   apply (subgoal_tac "x3 = pde_walk (ASID s) (MEM s) (TTBR0 s) va")
    apply ((clarsimp simp: Let_def awesome raise'exception_def state.defs is_fault_pde_is_fault_pt lookup_in_tlb split:split_if_asm) ; blast)
   apply (simp add: less_eq_lookup_pde_type)
  apply ((clarsimp simp: raise'exception_def state.defs split: split_if_asm); force+)

done
    


(* refinement between two deterministic TLB lookups, tlb_rel_flt states that TLBs store page faults  *)
lemma  mmu_translate_det_flt_refine:
  "\<lbrakk> mmu_translate va s = (pa, s'); consistent' (typ_det_tlb t) va;  tlb_rel_flt (typ_det_tlb s) (typ_det_tlb t) \<rbrakk> \<Longrightarrow>
  let (pa', t') = mmu_translate va t
  in pa' = pa \<and> consistent' (typ_det_tlb t') va \<and> tlb_rel_flt' (typ_det_tlb s') (typ_det_tlb t')"
  apply (frule (1) tlb_rel_flt_consistent , clarsimp)
  apply (frule consistent_not_Incon_01 , clarsimp)
  apply (frule tlb_rel_fltD , clarsimp)
  apply (insert tlb_mono [of "fst (tlb_det_set s)"  "fst (tlb_det_set t)" "ASID s" "(addr_val va)"])
  apply (clarsimp simp: mmu_translate_tlb_det_state_ext_def split_def Let_def tlb_rel_flt_def tlb_rel_flt'_def typ_det_tlb_def split: split_if_asm)
  apply (cases "lookup (fst (tlb_det_set t)) (ASID s) (addr_val va)" ; clarsimp)
   apply (cases "PED_Cache.lookup_pde (snd (tlb_det_set t)) (ASID s) (addr_val va) " ; clarsimp)
    apply (subgoal_tac "PED_Cache.lookup_pde (snd (tlb_det_set s)) (ASID s) (addr_val va) = Miss_pde" )
     prefer 2
     apply (clarsimp simp: consistent0'_def, drule_tac a = "(ASID s)" and v = "addr_val va" in  tlb_pde_mono; clarsimp)
    apply ((clarsimp simp: Let_def raise'exception_def  state.defs consistent0'_def split_def split:split_if_asm);
            (cases "tlb_det_set t", cases "tlb_det_set s" , clarsimp simp: no_faults_def subset_insertI2 to_do  lookup_refill  fst_def snd_def) )
   apply (cases "PED_Cache.lookup_pde (snd (tlb_det_set s)) (ASID s) (addr_val va)" ; clarsimp simp: Let_def consistent0'_def)
    apply (clarsimp split: split_if_asm)
     apply (clarsimp simp: raise'exception_def  state.defs split:split_if_asm)
    apply ((clarsimp simp: Let_def awesome split: split_if_asm) ,
              ((clarsimp simp: raise'exception_def  fst_def snd_def state.defs split:split_if_asm) ,
                   (cases "tlb_det_set t", cases "tlb_det_set s" , fastforce) ,  (cases "tlb_det_set t", cases "tlb_det_set s", fastforce)))
    apply ((clarsimp simp:  consistent0'_def fst_def snd_def state.defs),
               (cases "tlb_det_set t", cases "tlb_det_set s" , clarsimp simp: no_faults_def subset_insertI2 to_do pde_lookup_in_tlb lookup_refill))
   apply (clarsimp simp: raise'exception_def  fst_def snd_def state.defs split: split_if_asm)
   apply ((clarsimp simp: Let_def raise'exception_def fst_def snd_def state.defs split: split_if_asm),
           ((clarsimp simp: awesome consistent0'_def fst_def snd_def  state.defs) ,
                  (cases "tlb_det_set t", cases "tlb_det_set s" , clarsimp simp: no_faults_def subset_insertI2 to_do pde_lookup_in_tlb lookup_refill)))
  apply (cases "lookup (fst (tlb_det_set s)) (ASID s) (addr_val va)" ; clarsimp)
   apply (cases "PED_Cache.lookup_pde (snd (tlb_det_set s)) (ASID s) (addr_val va)" ; clarsimp)
     apply (clarsimp simp: Let_def split: split_if_asm)
        apply (clarsimp simp: raise'exception_def  fst_def snd_def state.defs split:split_if_asm)
       apply (clarsimp simp: is_fault_def is_fault_pde_def pt_walk_def pde_walk_def ; (cases "get_pde (MEM s) (TTBR0 s) va" ; clarsimp; case_tac a ; clarsimp))
      apply ((clarsimp simp: raise'exception_def  fst_def snd_def state.defs split:split_if_asm) ;
                   ((cases "tlb_det_set t", cases "tlb_det_set s") , clarsimp , blast))
     apply (clarsimp simp: fst_def snd_def state.defs split:split_if_asm)
     apply (cases "tlb_det_set t", cases "tlb_det_set s" , fastforce simp: lookup_in_tlb)
    apply (clarsimp simp: consistent0'_def)
   apply (subgoal_tac "x3 = pde_walk (ASID s) (MEM s) (TTBR0 s) va")
    prefer 2
    apply (clarsimp simp: consistent0'_def)
   apply (clarsimp split: split_if_asm)
      apply (clarsimp simp: raise'exception_def  fst_def snd_def state.defs split:split_if_asm)
     apply (subgoal_tac "is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) va)" ; clarsimp)
     apply ((clarsimp simp: is_fault_def is_fault_pde_def pt_walk_def pde_walk_def , cases "get_pde (MEM s) (TTBR0 s) va"; clarsimp), (case_tac a ; clarsimp))
    apply (clarsimp simp: awesome raise'exception_def fst_def snd_def state.defs split:split_if_asm)
   apply (clarsimp simp: awesome Let_def fst_def snd_def state.defs split:split_if_asm)
   apply (cases "tlb_det_set t", cases "tlb_det_set s"  , fastforce simp: lookup_in_tlb)
  apply (clarsimp simp: raise'exception_def  fst_def snd_def state.defs split:split_if_asm)
done



(* refinement between eviction and deterministic TLB lookups *)
lemma  mmu_translate_flt_refine_det:
  "\<lbrakk> mmu_translate va s = (pa, s');  consistent' (typ_det_tlb t) va; tlb_rel_flt (typ_tlb s) (typ_det_tlb t) \<rbrakk> \<Longrightarrow>
  let (pa', t') = mmu_translate va t
  in pa' = pa  \<and> consistent' (typ_det_tlb t') va \<and> tlb_rel_flt' (typ_tlb s') (typ_det_tlb t')"
  apply (frule (1) tlb_rel_flt_consistent , clarsimp)
  apply (frule consistent_not_Incon_01 , clarsimp)
  apply (frule tlb_rel_fltD , clarsimp)
  apply (insert tlb_mono [of "(fst (tlb_set s) - fst (tlb_evict (typ_tlb s)))"  "(fst(tlb_det_set t))" "ASID s" "(addr_val va)"] , simp )
  apply (insert tlb_pde_mono [of "(snd (tlb_set s) - snd (tlb_evict (typ_tlb s)))"  "(snd(tlb_det_set t))" "ASID s" "(addr_val va)"] ,simp)
  apply (insert Diff_subset [of "fst (tlb_set s)" "fst (tlb_evict (typ_tlb s))"])
  apply (insert Diff_subset [of "snd (tlb_set s)" "snd (tlb_evict (typ_tlb s))"])
  apply (clarsimp simp: mmu_translate_tlb_state_ext_def mmu_translate_tlb_det_state_ext_def split_def Let_def pairsub_def
           tlb_rel_flt_def tlb_rel_flt'_def typ_det_tlb_def typ_tlb_def  split: split_if_asm)
  apply (cases "lookup (fst(tlb_det_set t)) (ASID s) (addr_val va)" ; clarsimp)
   apply (cases "PED_Cache.lookup_pde (snd (tlb_det_set t)) (ASID s) (addr_val va) " ; clarsimp)
    apply (clarsimp simp: Let_def split:split_if_asm)
      apply (((clarsimp simp: raise'exception_def Let_def  state.defs split:split_if_asm) , blast) ,
             ((clarsimp simp: consistent0'_def fst_def snd_def) , (cases "tlb_det_set t", cases "tlb_set s"), fastforce))
     apply ((clarsimp simp: raise'exception_def consistent0'_def fst_def snd_def  no_faults_def subset_insertI2 state.defs split:split_if_asm);
            ((cases "tlb_det_set t", cases "tlb_set s") , (force simp: to_do) ))
    apply ((clarsimp simp: fst_def snd_def state.defs), (cases "tlb_det_set t", cases "tlb_set s") ,
         (clarsimp simp: consistent0'_def to_do lookup_refill no_faults_def subset_insertI2 fst_def snd_def))
   apply (cases "lookup_pde (snd (tlb_set s) - snd (tlb_evict (state.extend (state.truncate s) (tlb_set s)))) (ASID s) (addr_val va)" ; clarsimp)
    apply (clarsimp simp: Let_def split_if_asm)
    apply ((clarsimp simp: raise'exception_def state.defs split:split_if_asm) ,blast, blast)
    apply (clarsimp simp: Let_def awesome split_if_asm)
    apply ((clarsimp simp: raise'exception_def state.defs split:split_if_asm) , blast , blast)
    apply (clarsimp simp: consistent0'_def fst_def snd_def state.defs,
             cases "tlb_det_set t", cases "tlb_set s" , clarsimp simp: no_faults_def subset_insertI2 fst_def snd_def lookup_refill split:split_if_asm)
   apply (clarsimp split: split_if_asm)
    apply ((clarsimp simp: raise'exception_def state.defs split:split_if_asm) ,blast , blast)
   apply (clarsimp simp: Let_def split: split_if_asm)
    apply ((clarsimp simp: raise'exception_def  state.defs split:split_if_asm) , blast, blast)
   apply (clarsimp simp: awesome consistent0'_def fst_def snd_def  state.defs, cases "tlb_det_set t", cases "tlb_set s", clarsimp simp: no_faults_def subset_insertI2 fst_def snd_def lookup_refill  split:split_if_asm)
  apply (cases "lookup (fst (tlb_set s) - fst (tlb_evict (state.extend (state.truncate s) (tlb_set s)))) (ASID s) (addr_val va) " ; clarsimp)
   apply (cases "lookup_pde (snd (tlb_set s) - snd (tlb_evict (state.extend (state.truncate s) (tlb_set s)))) (ASID s) (addr_val va)"; clarsimp)
    apply (clarsimp simp: Let_def split: split_if_asm)
      apply (clarsimp simp: raise'exception_def state.defs split:split_if_asm) apply blast apply blast
     apply (clarsimp simp: is_fault_def is_fault_pde_def pt_walk_def pde_walk_def)
     apply ((cases "get_pde (MEM s) (TTBR0 s) va" ; clarsimp) , (case_tac a ; clarsimp))
     apply (clarsimp simp: raise'exception_def state.defs split:split_if_asm , blast, blast)
    apply ((clarsimp simp: raise'exception_def lookup_in_tlb state.defs split:split_if_asm) , blast)
   apply (subgoal_tac "x3 = pde_walk (ASID s) (MEM s) (TTBR0 s) va")
    apply ((clarsimp simp: Let_def awesome raise'exception_def state.defs is_fault_pde_is_fault_pt lookup_in_tlb split:split_if_asm) ; blast)
   apply (simp add: less_eq_lookup_pde_type)
  apply ((clarsimp simp: raise'exception_def state.defs split: split_if_asm); force+)

done
    


lemma sat_states_parameters:
  "\<lbrakk> mmu_translate va t = (pa', t') ; saturated' (typ_sat_tlb' t) \<rbrakk> \<Longrightarrow>
      state.more t' = state.more t \<and> ASID t' = ASID t \<and> MEM t' = MEM t \<and> TTBR0 t' = TTBR0 t \<and> saturated' (typ_sat_tlb' t')"
  apply (frule sat_state_tlb', clarsimp simp: mmu_translate_tlb_sat_state'_ext_def Let_def saturated'_def)
  by (cases "lookup (tlb_sat_set' t) (ASID t) (addr_val va)" ; clarsimp simp: raise'exception_def split:split_if_asm)+
  

lemma lookup_incon_subset [simp]:
  "\<lbrakk> s \<subseteq> t ; lookup s a va = Incon \<rbrakk> \<Longrightarrow>  lookup t a va = Incon"
  by (metis less_eq_lookup_type lookup_type.simps(3) tlb_mono)



lemma  lookup_pde_saturate_not_miss:
  "PED_Cache.lookup_pde (range (pde_walk (ASID s) (MEM s) (TTBR0 s))) (ASID s) v \<noteq> Miss_pde"
  apply (subgoal_tac " pde_entry_set (range (pde_walk (ASID s) (MEM s) (TTBR0 s))) (ASID s) v \<noteq> {}", clarsimp simp: lookup_pde_def )
  by (clarsimp simp: pde_entry_set_def pde_entry_range_asid_tags_def ,rule_tac x= "pde_walk (ASID s) (MEM s) (TTBR0 s) (Addr v)" in exI , simp add: asid_pde_walk)
 


lemma entry_set_hit_entry_range:
  "entry_set t a va = {x} \<Longrightarrow> (a , va) \<in> entry_range_asid_tags x"
   by (force simp: entry_set_def split:split_if_asm)
  


lemma asid_va_entry_range_pt_entry1:
  "(asid, addr_val va) \<in> entry_range_asid_tags (pt_walk asid mem ttbr0 va)"
  apply (clarsimp simp: pt_walk_def)
  apply (cases "get_pde mem ttbr0 va" , clarsimp simp: pt_walk_def entry_range_asid_tags_def entry_range_def)
  apply (case_tac a ; clarsimp simp: entry_range_asid_tags_def entry_range_def)
  apply (case_tac "get_pte mem x3 va" , clarsimp simp: entry_range_asid_tags_def entry_range_def)
  apply (case_tac a ; clarsimp simp: entry_range_asid_tags_def entry_range_def)
done


lemma shift_to_mask:
  "x AND NOT mask 12 = (ucast (ucast ((x::32 word) >> 12):: 20 word)::32 word) << 12"
  by (rule word_eqI ,auto simp:word_ops_nth_size word_size  nth_shiftr nth_shiftl nth_ucast)



lemma va_offset_add:
  " (va::32 word) : {ucast (ucast ((x:: 32 word) >> 12):: 20 word) << 12  .. 
    (ucast (ucast (x >> 12):: 20 word) << 12) + mask 12 } \<Longrightarrow>
      \<exists>a.  (0 \<le> a \<and> a \<le> mask 12) \<and>
  va = (ucast (ucast ((x:: 32 word) >> 12):: 20 word) << 12)  + a"
  by (rule_tac x = "va - (ucast (ucast ((x:: 32 word) >> 12):: 20 word) << 12) " in exI , uint_arith)


lemma nth_bits_false:
  "\<lbrakk>(n::nat) < 20; (a::32 word) \<le> 0xFFF\<rbrakk> \<Longrightarrow> \<not>(a !! (n + 12))"
  apply word_bitwise  apply clarsimp
  by (case_tac "n = 0"  , clarsimp ,case_tac "n = 1" ,clarsimp ,case_tac "n = 2"
   , clarsimp ,case_tac "n = 3" ,clarsimp,case_tac "n = 4" , clarsimp ,case_tac "n = 5" , clarsimp , case_tac "n = 6"
   , clarsimp ,case_tac "n = 7" , clarsimp , case_tac "n = 8" , clarsimp , case_tac "n = 9"  , clarsimp , case_tac "n = 10"  , clarsimp ,case_tac "n = 11" , clarsimp ,case_tac "n = 12"
   , clarsimp ,case_tac "n = 13"  , clarsimp ,case_tac "n = 14"  , clarsimp ,case_tac "n = 15"  ,clarsimp, case_tac "n = 16", clarsimp,case_tac "n = 17"
    , clarsimp,case_tac "n = 18" , clarsimp ,case_tac "n = 19" ,clarsimp , ((thin_tac "\<not> a !! P" for P)+ ,arith))



lemma nth_bits_offset_equal: "\<lbrakk>n < 20 ; (a::32 word) \<le> 0x00000FFF \<rbrakk> \<Longrightarrow> 
        (((x::32 word) && 0xFFFFF000) || a) !!  (n + 12) = x !! (n + 12)"
  apply clarsimp
  apply (rule iffI)
   apply (erule disjE)
    apply clarsimp
   apply (clarsimp simp: nth_bits_false)
  apply (simp only: test_bit_int_def [symmetric])
  by (case_tac "n = 0"  , clarsimp ,case_tac "n = 1" ,clarsimp ,case_tac "n = 2"
   , clarsimp ,case_tac "n = 3" ,clarsimp,case_tac "n = 4" , clarsimp ,case_tac "n = 5" , clarsimp , case_tac "n = 6"
   , clarsimp ,case_tac "n = 7" , clarsimp , case_tac "n = 8" , clarsimp , case_tac "n = 9"  , clarsimp , case_tac "n = 10"  , clarsimp ,case_tac "n = 11" , clarsimp ,case_tac "n = 12"
   , clarsimp ,case_tac "n = 13"  , clarsimp ,case_tac "n = 14"  , clarsimp ,case_tac "n = 15"  ,clarsimp, case_tac "n = 16", clarsimp,case_tac "n = 17"
    , clarsimp,case_tac "n = 18" , clarsimp ,case_tac "n = 19" ,clarsimp , presburger)

   
lemma add_to_or:
  "(a::32 word) \<le> 0xFFF \<Longrightarrow>
     ((x::32 word) && 0xFFFFF000) + a =  (x && 0xFFFFF000) || a"
  apply word_bitwise
  using xor3_simps carry_simps by auto
 

lemma va_offset_higher_bits: 
   " \<lbrakk>ucast (ucast ((x:: 32 word) >> 12):: 20 word) << 12 \<le> va ; 
      va \<le> (ucast (ucast (x >> 12):: 20 word) << 12) + 0x00000FFF \<rbrakk> \<Longrightarrow>
        (ucast (x >> 12)::20 word) = (ucast ((va:: 32 word) >> 12)::20 word)"
  apply (subgoal_tac "(va::32 word) : {ucast (ucast ((x:: 32 word) >> 12):: 20 word) << 12  .. (ucast (ucast (x >> 12):: 20 word) << 12) + mask 12 }")
   prefer 2  apply (clarsimp simp: mask_def)
  apply (frule va_offset_add, simp)
  apply (erule exE ,erule conjE , simp add: mask_def)
  apply (subgoal_tac "(ucast ((((ucast (ucast ((x:: 32 word) >> 12):: 20 word) << 12)::32 word)  + a) >> 12):: 20 word) =
   (ucast (((ucast (ucast ((x:: 32 word) >> 12):: 20 word) << 12)::32 word)   >> 12):: 20 word) ")
   apply (clarsimp , word_bitwise) [1]
  apply (subgoal_tac "ucast ((ucast (ucast ((x::32 word) >> 12):: 20 word)::32 word) << 12 >> 12) =
   (ucast (x >> 12) :: 20 word)")
   prefer 2 apply (word_bitwise) [1]
  apply (clarsimp simp: shift_to_mask [symmetric] , rule word_eqI, clarsimp simp: nth_ucast)
  apply (subgoal_tac "n < 20")
   prefer 2 apply word_bitwise [1]
  by (clarsimp simp: nth_shiftr mask_def, frule_tac a = a in nth_bits_offset_equal, clarsimp, drule_tac x= x in add_to_or , simp)
 

lemma n_bit_shift:
  "\<lbrakk> \<forall>n::nat. n \<in> {12 .. 31} \<longrightarrow>(a::32 word) !! n = (b::32 word) !! n  \<rbrakk>  \<Longrightarrow>  a >> 12 = b >> 12"
  apply word_bitwise  by auto


lemma nth_bits_offset: "\<lbrakk> n \<in> {12..31} ; (a::32 word) \<le> 0x00000FFF \<rbrakk> \<Longrightarrow> 
        (x::32 word) !! n = (x && 0xFFFFF000 || a) !! n"
  apply (rule iffI)  apply (case_tac "n = 12")   apply clarsimp  apply (case_tac "n = 13")   apply clarsimp  apply (case_tac "n = 14")   apply clarsimp  apply (case_tac "n = 15")
       apply clarsimp  apply (case_tac "n = 16")   apply clarsimp  apply (case_tac "n = 17")   apply clarsimp  apply (case_tac "n = 18")   apply clarsimp
   apply (case_tac "n = 19")   apply clarsimp  apply (case_tac "n = 20")   apply clarsimp  apply (case_tac "n = 21")   apply clarsimp  apply (case_tac "n = 22")
    apply clarsimp  apply (case_tac "n = 23")   apply clarsimp  apply (case_tac "n = 24")   apply clarsimp  apply (case_tac "n = 25")   apply clarsimp  apply (case_tac "n = 26")
    apply clarsimp  apply (case_tac "n = 27")   apply clarsimp  apply (case_tac "n = 28")   apply clarsimp  apply (case_tac "n = 29")   apply clarsimp
   apply (case_tac "n = 30")   apply clarsimp  apply (case_tac "n = 31")   apply clarsimp  prefer 2  apply (case_tac "n = 12")   apply word_bitwise [1] apply clarsimp
    apply (case_tac "n = 13")  apply word_bitwise [1] apply clarsimp apply (case_tac "n = 14")  apply word_bitwise [1]  apply clarsimp apply (case_tac "n = 15")  apply word_bitwise [1]  apply clarsimp
   apply (case_tac "n = 16")  apply word_bitwise [1] apply clarsimp apply (case_tac "n = 17")  apply word_bitwise [1] apply clarsimp apply (case_tac "n = 18")  apply word_bitwise [1] apply clarsimp
    apply (case_tac "n = 19")  apply word_bitwise [1] apply clarsimp apply (case_tac "n = 20")  apply word_bitwise [1] apply clarsimp  apply (case_tac "n = 21")
    apply word_bitwise [1] apply clarsimp apply (case_tac "n = 22") apply word_bitwise [1] apply clarsimp apply (case_tac "n = 23")  apply word_bitwise [1] apply clarsimp apply (case_tac "n = 24")
    apply word_bitwise [1] apply clarsimp apply (case_tac "n = 25")  apply word_bitwise [1] apply clarsimp apply (case_tac "n = 26")  apply word_bitwise [1]  apply clarsimp
   apply (case_tac "n = 27")  apply word_bitwise [1] apply clarsimp apply (case_tac "n = 28")  apply word_bitwise [1] apply clarsimp apply (case_tac "n = 29")
    apply word_bitwise [1] apply clarsimp apply (case_tac "n = 30")  apply word_bitwise [1] apply clarsimp apply (case_tac "n = 31")  apply word_bitwise [1] apply clarsimp apply clarsimp
   apply arith apply clarsimp apply arith
done


lemma offset_mask_eq:
 "\<lbrakk>ucast (ucast ((x:: 32 word) >> 12):: 20 word) << 12 \<le> va ; 
      va \<le> (ucast (ucast (x >> 12):: 20 word) << 12) + 0x00000FFF\<rbrakk>
          \<Longrightarrow> (( x >> 12) && mask 8 << 2) = 
         ((va >> 12) && mask 8 << 2)"
  apply (subgoal_tac "(va::32 word) : {ucast (ucast ((x:: 32 word) >> 12):: 20 word) << 12  ..
                      (ucast (ucast (x >> 12):: 20 word) << 12) + mask 12 }")
   prefer 2
   apply (clarsimp simp: mask_def)
  apply (frule va_offset_add, erule exE, erule conjE, simp add: mask_def , rule_tac f = "(\<lambda>x. x && 0xFF << 2)" in  arg_cong , clarsimp simp: shift_to_mask [symmetric] mask_def
    , rule n_bit_shift , rule allI , rule impI , frule_tac x= x in add_to_or  , frule_tac x= x in nth_bits_offset) by  force+
 


lemma n_bit_shift_1:
  "\<lbrakk> \<forall>n::nat. n \<in> {12 .. 31} \<longrightarrow>(a::32 word) !! n = (b::32 word) !! n  \<rbrakk>  \<Longrightarrow>  a >> 20 = b >> 20"
  apply word_bitwise  by auto


lemma offset_mask_eq_1:
  "\<lbrakk>ucast (ucast ((x:: 32 word) >> 12):: 20 word) << 12 \<le> va ; 
      va \<le> (ucast (ucast (x >> 12):: 20 word) << 12) + 0x00000FFF\<rbrakk>
          \<Longrightarrow>((x >> 20) && mask 12 << 2) =
                          ((va >> 20) && mask 12 << 2)"
  apply (subgoal_tac "(va::32 word) : {ucast (ucast ((x:: 32 word) >> 12):: 20 word) << 12  ..
   (ucast (ucast (x >> 12):: 20 word) << 12) + mask 12 }")
   prefer 2
   apply (clarsimp simp: mask_def , frule va_offset_add , erule exE,  erule conjE,  simp add: mask_def,  rule_tac f = "(\<lambda>x. x && 0xFFF << 2)" in  arg_cong
          , clarsimp simp: shift_to_mask [symmetric], simp add: mask_def, rule n_bit_shift_1, rule allI, rule impI, frule_tac x= x in add_to_or, frule_tac x= x in nth_bits_offset)
   apply (simp only:)+
done


lemma va_offset_add_1:
  " (va::32 word) : {ucast (ucast ((x:: 32 word) >> 20):: 12 word) << 20  .. 
    (ucast (ucast (x >> 20):: 12 word) << 20) + mask 20 } \<Longrightarrow>
      \<exists>a.  (0 \<le> a \<and> a \<le> mask 20) \<and>
      va = (ucast (ucast ((x:: 32 word) >> 20):: 12 word) << 20)  + a"
  apply (rule_tac x = "va - (ucast (ucast ((x:: 32 word) >> 20):: 12 word) << 20) " in exI)
   using mask_def  by uint_arith



lemma shift_to_mask_1:
  "x AND NOT mask 20 = (ucast (ucast ((x::32 word) >> 20):: 12 word)::32 word) << 20"
  apply (rule word_eqI, simp add : word_ops_nth_size word_size  nth_shiftr nth_shiftl nth_ucast)
  by auto


lemma nth_bits_false_1:
  "\<lbrakk>(n::nat) < 12; (a::32 word) \<le> 0xFFFFF\<rbrakk> \<Longrightarrow> \<not>(a !! (n + 20))"
  apply word_bitwise
  apply clarsimp apply (case_tac "n = 0") apply clarsimp apply (case_tac "n = 1") apply clarsimp apply (case_tac "n = 2") apply clarsimp apply (case_tac "n = 3")
   apply clarsimp apply (case_tac "n = 4")  apply clarsimp apply (case_tac "n = 5") apply clarsimp apply (case_tac "n = 6")
   apply clarsimp apply (case_tac "n = 7")  apply clarsimp apply (case_tac "n = 8") apply clarsimp apply (case_tac "n = 9")  apply clarsimp  apply (case_tac "n = 10")
   apply clarsimp apply (case_tac "n = 11")  apply clarsimp apply (thin_tac "\<not> a !! P" for P)+ by arith


lemma nth_bits_offset_equal_1: "\<lbrakk>n < 12 ; (a::32 word) \<le> 0x000FFFFF \<rbrakk> \<Longrightarrow> 
        (((x::32 word) && 0xFFF00000) || a) !!  (n + 20) = x !! (n + 20)"
  apply clarsimp apply (rule iffI)  apply (erule disjE)  apply clarsimp  apply (clarsimp simp: nth_bits_false_1) apply clarsimp apply (simp only: test_bit_int_def [symmetric])
  apply (case_tac "n = 0") apply clarsimp apply (case_tac "n = 1")  apply clarsimp apply (case_tac "n = 2")  apply clarsimp apply (case_tac "n = 3")  apply clarsimp
  apply (case_tac "n = 4")  apply clarsimp apply (case_tac "n = 5") apply clarsimp apply (case_tac "n = 6")  apply clarsimp apply (case_tac "n = 7")
   apply clarsimp  apply (case_tac "n = 8")  apply clarsimp  apply (case_tac "n = 9")  apply clarsimp  apply (case_tac "n = 10")  apply clarsimp apply (case_tac "n = 11")  apply clarsimp
  by presburger

lemma add_to_or_1:
  "(a::32 word) \<le> 0xFFFFF \<Longrightarrow>
     ((x::32 word) && 0xFFF00000) + a =  (x && 0xFFF00000) || a"
  apply word_bitwise
  using xor3_simps carry_simps by auto


lemma va_offset_higher_bits_1: 
   " \<lbrakk>ucast (ucast ((x:: 32 word) >> 20):: 12 word) << 20 \<le> va ; 
      va \<le> (ucast (ucast (x >> 20):: 12 word) << 20) + 0x000FFFFF \<rbrakk> \<Longrightarrow>
        (ucast (x >> 20):: 12 word) = (ucast ((va:: 32 word) >> 20)::12 word)"
  apply (subgoal_tac "(va::32 word) : {ucast (ucast ((x:: 32 word) >> 20):: 12 word) << 20 ..
                      (ucast (ucast (x >> 20):: 12 word) << 20) + mask 20 }")
   prefer 2  apply (clarsimp simp: mask_def)
  apply (frule va_offset_add_1 , simp , erule exE, erule conjE, simp add: mask_def)
  apply (subgoal_tac "(ucast ((((ucast (ucast ((x:: 32 word) >> 20):: 12 word) << 20)::32 word)  + a) >> 20):: 12 word) =
                      (ucast (((ucast (ucast ((x:: 32 word) >> 20):: 12 word) << 20)::32 word)   >> 20):: 12 word) ")
   apply clarsimp  apply (word_bitwise) [1]
  apply (subgoal_tac "ucast ((ucast (ucast ((x::32 word) >> 20):: 12 word)::32 word) << 20 >> 20) =
   (ucast (x >> 20) :: 12 word)")
   prefer 2  apply (word_bitwise) [1]  apply (clarsimp simp: shift_to_mask_1 [symmetric], rule word_eqI,  simp only: nth_ucast, clarsimp )
  apply (subgoal_tac "n < 12")  prefer 2 apply word_bitwise [1] apply (clarsimp simp: nth_shiftr  mask_def)
  apply (frule_tac a = a in nth_bits_offset_equal_1) apply clarsimp  apply (drule_tac x= x in add_to_or_1)
  by force



lemma n_bit_shift_2:
  "\<lbrakk> \<forall>n::nat. n \<in> {20 .. 31} \<longrightarrow>(a::32 word) !! n = (b::32 word) !! n  \<rbrakk>  \<Longrightarrow>  a >> 20 = b >> 20"
  apply word_bitwise by auto


lemma nth_bits_offset_1: "\<lbrakk> n \<in> {20..31} ; (a::32 word) \<le> 0x000FFFFF \<rbrakk> \<Longrightarrow> 
        (x::32 word) !! n = (x && 0xFFF00000 || a) !! n"
  apply (rule iffI) apply (case_tac "n = 20")  apply clarsimp apply (case_tac "n = 21")  apply clarsimp apply (case_tac "n = 22")  apply clarsimp apply (case_tac "n = 23")
    apply clarsimp  apply (case_tac "n = 24")  apply clarsimp apply (case_tac "n = 25")  apply clarsimp apply (case_tac "n = 26")  apply clarsimp apply (case_tac "n = 27")
    apply clarsimp apply (case_tac "n = 28")  apply clarsimp apply (case_tac "n = 29")  apply clarsimp apply (case_tac "n = 30")  apply clarsimp apply (case_tac "n = 31")
    apply clarsimp prefer 2 apply (case_tac "n = 20")  apply word_bitwise [1] apply clarsimp  apply (case_tac "n = 21")   apply word_bitwise [1] apply clarsimp
   apply (case_tac "n = 22")  apply word_bitwise [1] apply clarsimp apply (case_tac "n = 23")  apply word_bitwise [1] apply clarsimp apply (case_tac "n = 24")  apply word_bitwise [1] apply clarsimp
   apply (case_tac "n = 25") apply word_bitwise [1] apply clarsimp apply (case_tac "n = 26") apply word_bitwise [1]  apply clarsimp
   apply (case_tac "n = 27") apply word_bitwise [1] apply clarsimp apply (case_tac "n = 28")  apply word_bitwise [1] apply clarsimp apply (case_tac "n = 29")  apply word_bitwise [1] apply clarsimp
   apply (case_tac "n = 30")  apply word_bitwise [1] apply clarsimp apply (case_tac "n = 31")  apply word_bitwise [1] apply clarsimp
   apply clarsimp apply arith apply clarsimp by arith


lemma  shfit_mask_eq:
  "\<lbrakk>ucast (ucast ((x:: 32 word) >> 20):: 12 word) << 20 \<le> va ; 
      va \<le> (ucast (ucast (x >> 20):: 12 word) << 20) + 0x000FFFFF \<rbrakk>
    \<Longrightarrow>   ((x >> 20) && mask 12 << 2) = ((va >> 20) && mask 12 << 2)"
  apply (subgoal_tac "(va::32 word) : {ucast (ucast ((x:: 32 word) >> 20):: 12 word) << 20 ..
   (ucast (ucast (x >> 20):: 12 word) << 20) + mask 20 }")
   prefer 2
   apply (clarsimp simp: mask_def)
  apply (frule va_offset_add_1 , simp, erule exE, erule conjE , simp add: mask_def , rule_tac f = "(\<lambda>x. x && 0xFFF << 2)" in  arg_cong , clarsimp simp: shift_to_mask_1 [symmetric]
     , simp add: mask_def , rule n_bit_shift_2 , rule allI , rule impI,  frule_tac x= x in add_to_or_1 , frule_tac x= x and a = a in nth_bits_offset_1)
   by force+


lemma  va_entry_set_pt_palk_same:
  "(asid, va) \<in> entry_range_asid_tags (pt_walk asid mem ttbr0 x) \<Longrightarrow>
       pt_walk asid mem ttbr0 x = pt_walk asid mem ttbr0 (Addr va)"
  apply (subgoal_tac "(asid, addr_val x) \<in> entry_range_asid_tags (pt_walk asid mem ttbr0 x)")
   prefer 2
   apply (clarsimp simp: asid_va_entry_range_pt_entry1)
  apply (cases "pt_walk asid mem ttbr0 x") apply (case_tac "x13" ; simp)  apply (clarsimp simp: entry_range_asid_tags_def entry_range_def pt_walk_def)  apply (cases "get_pde mem ttbr0 x" ; clarsimp)
    apply (case_tac a ; clarsimp) apply (case_tac " get_pte mem x3 x " ; clarsimp)  apply (subgoal_tac "get_pde mem ttbr0 x = get_pde mem ttbr0 (Addr va)" ; clarsimp)
      apply (subgoal_tac "get_pte mem x3 x = get_pte mem x3 (Addr va)" ; clarsimp)  using va_offset_higher_bits apply blast
      apply (clarsimp simp:  get_pte_def vaddr_pt_index_def)  apply (subgoal_tac "((addr_val x >> 12) && mask 8 << 2) =  ((va >> 12) && mask 8 << 2) ")
       prefer 2  using offset_mask_eq apply blast  apply force  apply (clarsimp simp: get_pde_def vaddr_pd_index_def)
     apply (subgoal_tac "((addr_val x >> 20) && mask 12 << 2) = ((va >> 20) && mask 12 << 2) ")  prefer 2  using offset_mask_eq_1 apply blast apply force apply (case_tac a ; clarsimp)
    apply (subgoal_tac "get_pde mem ttbr0 x = get_pde mem ttbr0 (Addr va)" ; clarsimp) apply (subgoal_tac "get_pte mem x3 x = get_pte mem x3 (Addr va)" ; clarsimp)
      using va_offset_higher_bits apply blast apply (clarsimp simp: get_pte_def vaddr_pt_index_def) apply (case_tac "get_pde mem ttbr0 (Addr va)" ; clarsimp) apply (subgoal_tac "((addr_val x >> 12) && mask 8 << 2) =  ((va >> 12) && mask 8 << 2) ")
      prefer 2  using offset_mask_eq apply blast apply force apply (clarsimp simp: get_pde_def vaddr_pd_index_def)
    apply (subgoal_tac "((addr_val x >> 20) && mask 12 << 2) = ((va >> 20) && mask 12 << 2) ")  prefer 2 using offset_mask_eq_1 apply blast  apply force
   apply (clarsimp simp: entry_range_asid_tags_def entry_range_def pt_walk_def) apply (cases "get_pde mem ttbr0 x" ; clarsimp) apply (case_tac aa ; clarsimp)
   apply (case_tac "get_pte mem x3 x" ; clarsimp)  apply (subgoal_tac "get_pde mem ttbr0 x = get_pde mem ttbr0 (Addr va)" ; clarsimp)
    apply (subgoal_tac "get_pte mem x3 x = get_pte mem x3 (Addr va)" ; clarsimp)   apply (case_tac aa ; clarsimp)
     using va_offset_higher_bits apply blast  apply (case_tac aa ; clarsimp simp: get_pte_def vaddr_pt_index_def)
    apply (subgoal_tac "((addr_val x >> 12) && mask 8 << 2) = ((va >> 12) && mask 8 << 2) ")   prefer 2   using offset_mask_eq apply blast
    apply force  apply (case_tac aa ; clarsimp simp: get_pde_def vaddr_pd_index_def)  apply (subgoal_tac "((addr_val x >> 20) && mask 12 << 2) = ((va >> 20) && mask 12 << 2) ")
    prefer 2  using offset_mask_eq_1 apply blast apply force apply (clarsimp)
  apply (case_tac "x23" ; clarsimp simp: entry_range_asid_tags_def entry_range_def pt_walk_def)  apply (cases "get_pde mem ttbr0 x" ; clarsimp)
    apply (subgoal_tac "get_pde mem ttbr0 (Addr va) = get_pde mem ttbr0 x" ; clarsimp)   using va_offset_higher_bits_1 apply blast  apply (clarsimp simp: get_pde_def vaddr_pd_index_def)
    apply (subgoal_tac "((addr_val x >> 20) && mask 12 << 2) = ((va >> 20) && mask 12 << 2)")   apply force  using shfit_mask_eq apply blast
   apply (case_tac a , clarsimp)   apply (subgoal_tac "get_pde mem ttbr0 (Addr va) = get_pde mem ttbr0 x" ; clarsimp)   using va_offset_higher_bits_1 apply blast
      apply (clarsimp simp: get_pde_def vaddr_pd_index_def) apply (subgoal_tac "((addr_val x >> 20) && mask 12 << 2) = ((va >> 20) && mask 12 << 2)")
       apply force using shfit_mask_eq apply blast apply clarsimp  apply (subgoal_tac "get_pde mem ttbr0 (Addr va) = get_pde mem ttbr0 x" ; clarsimp)
      using va_offset_higher_bits_1 apply blast   apply (clarsimp simp: get_pde_def vaddr_pd_index_def)
     apply (subgoal_tac "((addr_val x >> 20) && mask 12 << 2) = ((va >> 20) && mask 12 << 2)")   apply force  using shfit_mask_eq apply blast apply clarsimp apply (case_tac "get_pte mem x3 x" ; clarsimp)
    apply (case_tac a , clarsimp) apply clarsimp apply (case_tac a ; clarsimp) apply (cases "get_pde mem ttbr0 x" ; clarsimp)apply (case_tac aa ; clarsimp)
   apply (case_tac "get_pte mem x3 x" ; clarsimp) apply (case_tac aa ; clarsimp)
  apply (subgoal_tac "get_pde mem ttbr0 (Addr va) = get_pde mem ttbr0 x" ; clarsimp) using va_offset_higher_bits_1 apply blast
  apply (clarsimp simp: get_pde_def vaddr_pd_index_def)apply (subgoal_tac "((addr_val x >> 20) && mask 12 << 2) = ((va >> 20) && mask 12 << 2)") apply force
  using shfit_mask_eq by blast




lemma asid_va_entry_range_pt_entry:
  "(asid, va) \<in> entry_range_asid_tags (pt_walk asid mem ttbr0 (Addr va))"
  by ((clarsimp simp: pt_walk_def), (cases "get_pde mem ttbr0 (Addr va)" ; clarsimp simp: entry_range_asid_tags_def entry_range_def),
    (case_tac a ; clarsimp simp: entry_range_asid_tags_def entry_range_def), (case_tac "get_pte mem x3 (Addr va)" ; clarsimp simp: entry_range_asid_tags_def entry_range_def),  (case_tac a ; clarsimp simp: entry_range_asid_tags_def entry_range_def))


theorem entry_range_single_elementI:
  "\<lbrakk>x\<in> t ; (a, v) \<in> entry_range_asid_tags x ; (\<forall>y\<in>t. y\<noteq>x \<longrightarrow> (a, v) \<notin> entry_range_asid_tags y) \<rbrakk> \<Longrightarrow> 
         {E \<in> t. (a, v) \<in> entry_range_asid_tags E} = {x}" 
   by force

lemma lookup_range_pt_walk_hit:
  "lookup (range (pt_walk asid mem ttbr0)) asid va = Hit (pt_walk asid mem ttbr0 (Addr va))"
  apply (clarsimp simp: lookup_def)
  apply safe
    apply simp
   apply (subgoal_tac "x = pt_walk asid mem ttbr0 (Addr va)" , force)
   apply (clarsimp simp: entry_set_def)
   apply (drule entry_range_single_element)
   apply safe
   apply (unfold Ball_def) [1]
   apply (erule_tac x = "pt_walk asid mem ttbr0 (Addr va)" in allE)
   apply (clarsimp simp: asid_va_entry_range_pt_entry)
  apply (rule_tac x = "pt_walk asid mem ttbr0 (Addr va)" in exI)
  apply (clarsimp simp: entry_set_def)
  apply (rule entry_range_single_elementI)
    apply force
   apply (clarsimp simp: asid_va_entry_range_pt_entry)
  apply safe
  apply (drule va_entry_set_pt_palk_same , simp)
done

theorem pde_entry_range_single_element:
  "{E \<in> t. (a, v) \<in> pde_entry_range_asid_tags E} = {x} \<Longrightarrow> (a, v) \<in> pde_entry_range_asid_tags x
         \<and> (\<forall>y\<in>t. y\<noteq>x \<longrightarrow> (a, v) \<notin> pde_entry_range_asid_tags y)" 
   by force


lemma asid_va_pde_entry_range_pt_entry:
  "(asid, va) \<in> pde_entry_range_asid_tags (pde_walk asid mem ttbr0 (Addr va))"
  apply (clarsimp simp: pde_walk_def)
  apply (cases "get_pde mem ttbr0 (Addr va)" ; clarsimp simp: pde_entry_range_asid_tags_def)
  apply (case_tac a ; clarsimp simp: pde_entry_range_asid_tags_def)
done


theorem pde_entry_range_single_elementI:
  "\<lbrakk>x\<in> t ; (a, v) \<in> pde_entry_range_asid_tags x ; (\<forall>y\<in>t. y\<noteq>x \<longrightarrow> (a, v) \<notin> pde_entry_range_asid_tags y) \<rbrakk> \<Longrightarrow> 
         {E \<in> t. (a, v) \<in> pde_entry_range_asid_tags E} = {x}" 
   by force


lemma asid_va_pde_entry_range_pt_entry1:
  "(asid, addr_val va) \<in> pde_entry_range_asid_tags (pde_walk asid mem ttbr0 va)"
  apply (clarsimp simp: pde_walk_def)
  apply (cases "get_pde mem ttbr0 va" ,  clarsimp simp: pde_entry_range_asid_tags_def )
  apply (case_tac a ; clarsimp simp: pde_entry_range_asid_tags_def)
done


lemma  va_pde_entry_set_pt_palk_same:
  "(asid, va) \<in> pde_entry_range_asid_tags (pde_walk asid mem ttbr0 x) \<Longrightarrow>
       pde_walk asid mem ttbr0 x = pde_walk asid mem ttbr0 (Addr va)"
  apply (subgoal_tac "(asid, addr_val x) \<in> pde_entry_range_asid_tags (pde_walk asid mem ttbr0 x)")
   prefer 2
   apply (clarsimp simp: asid_va_pde_entry_range_pt_entry1)
  apply (clarsimp simp: pde_entry_range_asid_tags_def  pde_walk_def)
  apply (cases "get_pde mem ttbr0 x" ; clarsimp)
   apply (subgoal_tac "get_pde mem ttbr0 x = get_pde mem ttbr0 (Addr va)" ; clarsimp)
    using va_offset_higher_bits_1 apply blast
   apply (clarsimp simp:  get_pde_def vaddr_pd_index_def)
   apply (subgoal_tac "((addr_val x >> 20) && mask 12 << 2) =
    ((va >> 20) && mask 12 << 2) ")
    apply force
   using  shfit_mask_eq apply blast
  apply (case_tac a ; clarsimp)
    apply (subgoal_tac "get_pde mem ttbr0 x = get_pde mem ttbr0 (Addr va)" ; clarsimp)
    using va_offset_higher_bits_1 apply blast
apply (clarsimp simp:  get_pde_def vaddr_pd_index_def)
apply (subgoal_tac "((addr_val x >> 20) && mask 12 << 2) =
    ((va >> 20) && mask 12 << 2) ")
    apply force
   using  shfit_mask_eq apply blast

  apply (subgoal_tac "get_pde mem ttbr0 x = get_pde mem ttbr0 (Addr va)" ; clarsimp)
    using va_offset_higher_bits_1 apply blast
apply (clarsimp simp:  get_pde_def vaddr_pd_index_def)
apply (subgoal_tac "((addr_val x >> 20) && mask 12 << 2) =
    ((va >> 20) && mask 12 << 2) ")
    apply force
   using  shfit_mask_eq apply blast

  apply (subgoal_tac "get_pde mem ttbr0 x = get_pde mem ttbr0 (Addr va)" ; clarsimp)
    using va_offset_higher_bits_1 apply blast
apply (clarsimp simp:  get_pde_def vaddr_pd_index_def)
apply (subgoal_tac "((addr_val x >> 20) && mask 12 << 2) =
    ((va >> 20) && mask 12 << 2) ")
    apply force
   using  shfit_mask_eq apply blast
  apply (subgoal_tac "get_pde mem ttbr0 x = get_pde mem ttbr0 (Addr va)" ; clarsimp)
    using va_offset_higher_bits_1 apply blast
apply (clarsimp simp:  get_pde_def vaddr_pd_index_def)
apply (subgoal_tac "((addr_val x >> 20) && mask 12 << 2) =
    ((va >> 20) && mask 12 << 2) ")
    apply force
   using  shfit_mask_eq apply blast
done




lemma lookup_pde_saturate_hit:
  "PED_Cache.lookup_pde (range (pde_walk asid mem ttbr0)) asid va = 
    Hit_pde (pde_walk asid mem ttbr0 (Addr va))"
  apply (clarsimp simp: lookup_pde_def)
  apply safe
    apply (clarsimp simp: pde_entry_set_def)
    apply (subgoal_tac "x = pde_walk asid mem ttbr0 (Addr va)" , force)
   apply (clarsimp simp: pde_entry_set_def)
   apply (drule pde_entry_range_single_element)
   apply safe
   apply (unfold Ball_def) [1]
   apply (erule_tac x = "pde_walk asid mem ttbr0 (Addr va)" in allE)
   apply (clarsimp simp: asid_va_pde_entry_range_pt_entry)
  apply (rule_tac x = "pde_walk asid mem ttbr0 (Addr va)" in exI)
  apply (clarsimp simp: pde_entry_set_def)
  apply (rule pde_entry_range_single_elementI)
    apply force
   apply (clarsimp simp: asid_va_pde_entry_range_pt_entry)
  apply safe
  apply (drule  va_pde_entry_set_pt_palk_same , simp)
done





lemma tlb_pde_union_walk   [simp]:
  "(\<Union>x. tlb_pde_walk (asid) (range (pde_walk (asid) (mem) (ttbr0))) (mem) (ttbr0) x)  =  range (pt_walk (asid) (mem) (ttbr0)) "
 apply (safe)
   apply (rule_tac x = xa in range_eqI)
   apply (clarsimp simp: tlb_pde_walk_def)
   apply (case_tac "PED_Cache.lookup_pde (range (pde_walk asid mem ttbr0)) asid (addr_val xa)")
     using lookup_pde_saturate_hit apply force
    apply (clarsimp simp:lookup_pde_saturate_hit)
   apply (clarsimp simp:lookup_pde_saturate_hit)
   apply (case_tac "bpa_pde_entry (pde_walk asid mem ttbr0 xa)" ; clarsimp)
    apply (clarsimp simp: pt_walk_def pde_walk_def)
    apply (case_tac "get_pde mem ttbr0 xa" ; clarsimp) apply (case_tac a ; clarsimp)

   apply (case_tac a ; clarsimp simp: mask_def pt_walk_def  pde_walk_def)
    apply (case_tac "get_pde mem ttbr0 xa" ; clarsimp) apply (case_tac a ; clarsimp simp: mask_def)
   apply (case_tac "get_pde mem ttbr0 xa" ; clarsimp) apply (case_tac a ; clarsimp)
   apply (case_tac "get_pte mem x3 xa" ; clarsimp simp: pte_tlb_entry_def)
  apply clarsimp
  apply (rule_tac x = "xa" in exI)
  apply (clarsimp simp: tlb_pde_walk_def)
  apply (case_tac "PED_Cache.lookup_pde (range (pde_walk asid mem ttbr0)) asid (addr_val xa)")
    using lookup_pde_saturate_hit apply force
   apply (clarsimp simp:lookup_pde_saturate_hit)
  apply (clarsimp simp:lookup_pde_saturate_hit)
  apply (case_tac "bpa_pde_entry (pde_walk asid mem ttbr0 xa)" ; clarsimp)
   apply (clarsimp simp: pt_walk_def pde_walk_def)
   apply (case_tac "get_pde mem ttbr0 xa" ; clarsimp) apply (case_tac a ; clarsimp)
  apply (case_tac a ; clarsimp simp: mask_def pt_walk_def  pde_walk_def)
   apply (case_tac "get_pde mem ttbr0 xa" ; clarsimp) apply (case_tac a ; clarsimp simp: mask_def)
  apply (case_tac "get_pde mem ttbr0 xa" ; clarsimp) apply (case_tac a ; clarsimp)
  apply (case_tac "get_pte mem x3 xa" ; clarsimp simp: pte_tlb_entry_def)
done




lemma fst_union_tlb:
  "fst (pairunion (tlb_sat_set t) (range (pt_walk (ASID s) (MEM s) (TTBR0 s)), range (pde_walk (ASID s) (MEM s) (TTBR0 s)))) =
fst (tlb_sat_set t) \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s))"
by (metis fst_conv pairunion.simps prod.collapse)

lemma fst_union_tlb':
  "fst (pairunion  t (range (pt_walk asid mem ttbr0), range (pde_walk asid mem ttbr0))) =
fst t \<union> range (pt_walk asid mem ttbr0)"
by (metis fst_conv pairunion.simps prod.collapse)


lemma to_do_incon:
  "\<lbrakk>consistent' (typ_sat_tlb t) va; tlb_rel_sat (typ_det_tlb s) (typ_sat_tlb t) \<rbrakk> \<Longrightarrow>  
           PED_Cache.lookup_pde (snd (tlb_det_set s)) (ASID s) (addr_val va) \<noteq> Incon_pde  "
  apply (subgoal_tac "PED_Cache.lookup_pde (snd (tlb_sat_set t)) (ASID s) (addr_val va) \<noteq> Incon_pde")
   apply (subgoal_tac "lookup_pde (snd(tlb_det_set s)) (ASID s) (addr_val va) \<le> lookup_pde (snd (tlb_sat_set t)) (ASID s) (addr_val va)")
    apply clarsimp
   apply (frule tlb_rel_satD , clarsimp)
   apply (drule_tac a = "ASID s" and v = "(addr_val va)" in  tlb_pde_mono)
   apply clarsimp
  apply (frule (1) tlb_rel_sat_consistent , clarsimp)
  apply (frule consistent_not_Incon_01 , clarsimp)
  apply (frule tlb_rel_satD , clarsimp)
done


lemma saturated_tlb_pde:
  "saturated (typ_sat_tlb s) \<Longrightarrow> fst (tlb_sat_set s) = fst (tlb_sat_set s) \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s)) \<and>
     snd (tlb_sat_set s) = snd (tlb_sat_set s) \<union> range (pde_walk (ASID s) (MEM s) (TTBR0 s))"
 apply (clarsimp simp: tlb_rel_sat_def saturated_def fst_def) apply (cases "tlb_sat_set s" ; clarsimp)  by blast


(* important *)
lemma mmu_translate_det_sat_refine:
  "\<lbrakk> mmu_translate va s = (pa, s'); consistent' (typ_sat_tlb t) va; tlb_rel_sat (typ_det_tlb s) (typ_sat_tlb t)  \<rbrakk> \<Longrightarrow>
  let (pa', t') = mmu_translate va t
  in pa' = pa \<and> consistent' (typ_sat_tlb t') va \<and> tlb_rel_sat (typ_det_tlb s') (typ_sat_tlb t')"
  apply (frule (1) tlb_rel_sat_consistent , clarsimp)
  apply (frule consistent_not_Incon_01 , clarsimp)
  apply (frule tlb_rel_satD , clarsimp)
  apply (insert tlb_mono [of "(fst(tlb_det_set s))"  "(fst (tlb_sat_set t) \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s)))" "ASID s" "(addr_val va)"])
  apply (insert tlb_pde_mono [of "(snd(tlb_det_set s))"  "(snd (tlb_sat_set t) \<union> range (pde_walk (ASID s) (MEM s) (TTBR0 s)))" "ASID s" "(addr_val va)"])
  apply (insert saturated_tlb_pde [of t] , clarsimp)
  apply (clarsimp simp: mmu_translate_tlb_det_state_ext_def  mmu_translate_tlb_sat_state_ext_def   fst_union_tlb split_def Let_def)
  apply (cases "lookup (fst (tlb_sat_set t)) (ASID s) (addr_val va)"; clarsimp)
   apply (drule  sat_state_lookup_not_miss , clarsimp)
  apply (cases "lookup (fst (tlb_det_set s)) (ASID s) (addr_val va)" ; clarsimp simp: tlb_rel_sat_def typ_sat_tlb_def typ_det_tlb_def)
   apply (cases" PED_Cache.lookup_pde (snd (tlb_det_set s)) (ASID s) (addr_val va)" ; clarsimp)
    apply (clarsimp simp: Let_def  saturated_def split: split_if_asm)
       apply (clarsimp simp: raise'exception_def split_def state.defs split:split_if_asm) using subset_pairunion apply presburger  using subset_pairunion apply presburger
      apply (clarsimp simp: is_fault_pde_is_fault_pt)
     apply ((clarsimp simp:  raise'exception_def split_def state.defs split:split_if_asm);
            (smt Un_insert_right fst_conv insert_subset pairunion.simps prod.collapse rangeI set_rev_mp snd_conv sup_bot.right_neutral))
    apply ((clarsimp simp:  split_def state.defs split:split_if_asm), (smt Un_insert_right fst_conv insert_subset pairunion.simps prod.collapse rangeI snd_conv subsetCE sup_bot.right_neutral))
   apply (subgoal_tac "x3 = pde_walk (ASID s) (MEM s) (TTBR0 s) va")
    prefer 2
    apply (clarsimp simp: consistent0'_def)
   apply (clarsimp simp: saturated_def tlb_rel_sat_def awesome split: split_if_asm)
      apply (clarsimp simp: raise'exception_def  split_def state.defs split:split_if_asm)
       using subset_pairunion apply presburger using subset_pairunion apply presburger
     apply (clarsimp simp: is_fault_pde_is_fault_pt)
    apply (clarsimp simp:  raise'exception_def split_def state.defs split:split_if_asm)
     using subset_pairunion apply presburger  using subset_pairunion apply presburger
   apply (clarsimp simp:  split_def state.defs split:split_if_asm)
   apply (smt Un_insert_right fst_conv insert_subset pairunion.simps prod.collapse rangeI rev_subsetD snd_conv sup_bot.right_neutral)
  apply (clarsimp  simp: saturated_def split: split_if_asm)
   apply (clarsimp simp: raise'exception_def  split_def state.defs split:split_if_asm)
    using subset_pairunion apply presburger  using subset_pairunion apply presburger
  apply (clarsimp simp: split_def state.defs split:split_if_asm)
  using subset_pairunion by presburger
 

lemma [simp]: 
  "fst (tlb_set s) \<subseteq> fst (tlb_sat_set t) \<Longrightarrow> fst (tlb_set s) - fst (tlb_evict (typ_tlb s)) \<subseteq> fst (tlb_sat_set t)"
  by blast

lemma [simp]: 
  "snd (tlb_set s) \<subseteq> snd (tlb_sat_set t) \<Longrightarrow> snd (tlb_set s) - snd (tlb_evict (typ_tlb s)) \<subseteq> snd (tlb_sat_set t)"
  by blast


lemma mmu_translate_sat_refine_non_det:
 "\<lbrakk> mmu_translate va s = (pa, s'); consistent' (typ_sat_tlb t) va; tlb_rel_sat (typ_tlb s) (typ_sat_tlb t)  \<rbrakk> \<Longrightarrow>
  let (pa', t') = mmu_translate va t
  in pa' = pa \<and> consistent' (typ_sat_tlb t') va \<and> tlb_rel_sat (typ_tlb s') (typ_sat_tlb t')"
  apply (frule (1) tlb_rel_sat_consistent , clarsimp)
  apply (frule consistent_not_Incon_01 , clarsimp)
  apply (frule tlb_rel_satD , clarsimp)
  apply (insert tlb_mono [of "(fst (tlb_set s) - fst (tlb_evict (typ_tlb s)))"  "(fst (tlb_sat_set t) \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s)))" "ASID s" "(addr_val va)"])
  apply (insert tlb_pde_mono [of "(snd (tlb_set s) - snd (tlb_evict (typ_tlb s)))"  "(snd (tlb_sat_set t) \<union> range (pde_walk (ASID s) (MEM s) (TTBR0 s)))" "ASID s" "(addr_val va)"])
  apply (insert saturated_tlb_pde [of t] , clarsimp)
  apply (clarsimp simp:mmu_translate_tlb_state_ext_def mmu_translate_tlb_sat_state_ext_def pairsub_def fst_union_tlb split_def Let_def)
  apply (cases "lookup (fst (tlb_sat_set t)) (ASID s) (addr_val va)"; clarsimp)
   apply (drule  sat_state_lookup_not_miss , clarsimp)
  apply (cases "lookup (fst (tlb_set s) - fst (tlb_evict (typ_tlb s))) (ASID s) (addr_val va)" ; clarsimp simp: tlb_rel_sat_def typ_sat_tlb_def typ_tlb_def)
   apply (cases "lookup_pde (snd (tlb_set s) - snd (tlb_evict (state.extend (state.truncate s) (tlb_set s)))) (ASID s) (addr_val va)" ; clarsimp)
    apply (clarsimp simp: Let_def  saturated_def split: split_if_asm)
       apply ((clarsimp simp: raise'exception_def split_def state.defs split:split_if_asm) ; smt Diff_subset subset_pairunion subset_trans)
      apply (clarsimp simp: is_fault_pde_is_fault_pt)
     apply ((clarsimp simp: raise'exception_def split_def state.defs split:split_if_asm); smt Diff_subset rangeI set_rev_mp subset_pairunion subset_trans)
    apply ((clarsimp simp:  split_def state.defs split:split_if_asm), smt Diff_subset rangeI set_rev_mp subset_pairunion subset_trans)
   apply (subgoal_tac "x3 = pde_walk (ASID s) (MEM s) (TTBR0 s) va")
    prefer 2
    apply (clarsimp simp: consistent0'_def)using less_eq_lookup_pde_type apply force
   apply (clarsimp simp: saturated_def tlb_rel_sat_def awesome split: split_if_asm)
      apply ((clarsimp simp: raise'exception_def  split_def state.defs split:split_if_asm) ; smt Diff_subset subset_pairunion subset_trans)
     apply (clarsimp simp: is_fault_pde_is_fault_pt)
    apply ((clarsimp simp:  raise'exception_def split_def state.defs split:split_if_asm) ; smt Diff_subset subset_pairunion subset_trans)
   apply (clarsimp simp:  split_def state.defs split:split_if_asm)
   apply (smt Diff_subset pairunion.simps rangeI subsetCE subset_trans surjective_pairing)
  apply (clarsimp  simp: saturated_def split: split_if_asm)
   apply ((clarsimp simp: raise'exception_def  split_def state.defs split:split_if_asm) ; smt Diff_subset subset_pairunion subset_trans)
  by ((clarsimp simp: split_def state.defs split:split_if_asm), smt Diff_subset subset_pairunion subset_trans)
 


lemma saturated'_tlb:
  "saturated' (typ_sat_tlb' s) \<Longrightarrow> tlb_sat_set' s =  tlb_sat_set' s \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s)) "
 apply (clarsimp simp: tlb_rel_sat'_def saturated'_def)  by blast


lemma saturated_tlb:
  "saturated (typ_sat_tlb s) \<Longrightarrow> fst (tlb_sat_set s) = fst (tlb_sat_set s) \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s)) "
 apply (clarsimp simp: tlb_rel_sat_def saturated_def fst_def) apply (cases "tlb_sat_set s" ; clarsimp)  by blast


lemma sat_sat_refine:
  "\<lbrakk> mmu_translate va s = (pa, s'); consistent'' (typ_sat_tlb' t) va; tlb_rel_sat' (typ_sat_tlb s) (typ_sat_tlb' t)  \<rbrakk> \<Longrightarrow>
  let (pa', t') = mmu_translate va t
  in pa' = pa \<and> consistent'' (typ_sat_tlb' t') va \<and> tlb_rel_sat' (typ_sat_tlb s') (typ_sat_tlb' t')"
  apply (frule (1) tlb_rel_sat_consistent' , clarsimp)
  apply (frule consistent_not_Incon''_implies , clarsimp)
  apply (frule tlb_rel_satD' , clarsimp)
  apply (insert tlb_mono [of "(fst(tlb_sat_set s)) "  "(tlb_sat_set' t \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s)))" "ASID s" "(addr_val va)"])
  apply (insert saturated'_tlb [of t], insert saturated_tlb [of s] , clarsimp simp: tlb_rel_sat'_def)
  apply (clarsimp simp: mmu_translate_tlb_sat_state_ext_def mmu_translate_tlb_sat_state'_ext_def split_def Let_def fst_union_tlb)
  apply (cases "lookup (tlb_sat_set' t \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s))) (ASID s) (addr_val va)" ;clarsimp)
   apply (frule sat_state_lookup_not_miss' , clarsimp)
  apply (cases "lookup (fst (tlb_sat_set s)) (ASID s) (addr_val va)" ; clarsimp simp: tlb_rel_sat'_def typ_sat_tlb_def typ_sat_tlb'_def)
   apply (insert  sat_state_lookup_not_miss [of "(typ_sat_tlb s)"] ; clarsimp simp: saturated_def state.defs)
  apply (clarsimp simp: saturated'_def saturated_def raise'exception_def split_def state.defs split: split_if_asm)
    using subset_pairunion by presburger+
  


lemma entry_set_hit_pt_walk [simp]:
  "\<lbrakk>entry_set (tlb_sat_set' s) (ASID s) (addr_val va) = {x} ; saturated' (typ_sat_tlb' s)\<rbrakk> \<Longrightarrow>
       x = pt_walk (ASID s) (MEM s) (TTBR0 s) va"
  apply (clarsimp simp: saturated'_def)
  apply (subgoal_tac "(ASID s, (addr_val va)) \<in> entry_range_asid_tags  (pt_walk (ASID s) (MEM s) (TTBR0 s) va )")
   apply (subgoal_tac "\<forall>y\<in>(tlb_sat_set' s). y \<noteq> x \<longrightarrow> (ASID s, addr_val va) \<notin> entry_range_asid_tags y")
    apply (drule_tac x = "pt_walk (ASID s) (MEM s) (TTBR0 s) va" in bspec)
     apply blast
    apply clarsimp
   apply (clarsimp simp: entry_set_def ; blast)
  apply (cases "pt_walk (ASID s) (MEM s) (TTBR0 s) va")
   apply (subgoal_tac "x11 = ASID s \<and> x12 = (ucast (addr_val va >> 12)) \<and> x14 = 0")
    prefer 2
    apply (clarsimp simp:pt_walk_def)
    apply (cases "get_pde (MEM s) (TTBR0 s) va"; clarsimp)
    apply (case_tac a ; clarsimp)
    apply (case_tac "get_pte (MEM s) x3 va" ; clarsimp)
    apply (case_tac a ; clarsimp)
   apply (case_tac x13)
    apply (clarsimp simp: pt_walk_def split:option.splits)
    apply (case_tac x2 ; clarsimp)
    apply (case_tac "get_pte (MEM s) x3 va")
     apply (clarsimp simp: entry_range_asid_tags_def entry_range_def)
    apply (case_tac a ; clarsimp simp: entry_range_asid_tags_def entry_range_def)
   apply (clarsimp simp: pt_walk_def)
   apply (cases "get_pde (MEM s) (TTBR0 s) va" ; clarsimp)
   apply (case_tac aa ; clarsimp)
   apply (case_tac "get_pte (MEM s) x3 va" ; clarsimp)
   apply (case_tac aa ; clarsimp simp: entry_range_asid_tags_def entry_range_def)
  apply (case_tac x23)
   apply (clarsimp simp: pt_walk_def)
   apply (cases "get_pde (MEM s) (TTBR0 s) va")
    apply (clarsimp simp: entry_range_asid_tags_def entry_range_def)
   apply (case_tac a ; clarsimp simp: entry_range_asid_tags_def entry_range_def)
   apply (case_tac "get_pte (MEM s) x3 va" ; clarsimp)
   apply (case_tac a ; clarsimp)
  apply (clarsimp simp: pt_walk_def)
  apply (cases "get_pde (MEM s) (TTBR0 s) va" ; clarsimp)
  apply (case_tac aa ; clarsimp)
   apply (case_tac "get_pte (MEM s) x3 va" ; clarsimp)
   apply (case_tac aa ; clarsimp)
  apply (clarsimp simp: entry_range_asid_tags_def entry_range_def)
done


lemma not_member_incon_consistent:
  "\<lbrakk>(ASID s , addr_val va) \<notin> asid_va_incon (tlb_sat_set' s);  saturated' (typ_sat_tlb' s) \<rbrakk> \<Longrightarrow> consistent'' (typ_sat_tlb' s) va"
  by (clarsimp simp: asid_va_incon_def consistent0''_def lookup_def
                  split:split_if_asm)


lemma tlb_rel_absD:
  "tlb_rel_abs s t \<Longrightarrow>
     ASID t = ASID s \<and> MEM t = MEM s \<and> TTBR0 t = TTBR0 s \<and>  asid_va_incon (state.more s) \<subseteq> state.more t \<and> exception t = exception s"
   by (clarsimp simp: tlb_rel_abs_def state.defs)


lemma tlb_rel_abs_consistent:
  "\<lbrakk>(ASID t, addr_val va) \<notin> (tlb_incon_set t) ;  tlb_rel_abs (typ_sat_tlb' s) (typ_incon t) ;  saturated' (typ_sat_tlb' s) \<rbrakk>
            \<Longrightarrow> consistent'' (typ_sat_tlb' s) va" 
  apply (rule not_member_incon_consistent ; clarsimp)
  apply (clarsimp simp: tlb_rel_abs_def)
  apply (subgoal_tac "ASID s = ASID t")
   apply simp
   apply blast
  apply (cases s , cases t , clarsimp simp: state.defs)
done


lemma mmu_translate_sat_TLB_union:
  "mmu_translate v s = (p,t) \<Longrightarrow> 
      tlb_sat_set' t = tlb_sat_set' s \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s))"
  apply (clarsimp simp:  mmu_translate_tlb_sat_state'_ext_def Let_def)
  apply (cases "lookup (tlb_sat_set' s \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s))) (ASID s) (addr_val v)")
    apply (clarsimp simp:raise'exception_def split:split_if_asm) +
done

lemma mmu_sat_eq_ASID_TTBR0_MEM:
  "\<lbrakk> mmu_translate va (s::'a tlb_sat_state'_scheme) = (pa , s') \<rbrakk>  \<Longrightarrow> ASID s = ASID s' \<and> TTBR0 s = TTBR0 s' \<and>
                      MEM s = MEM s'"
   apply (clarsimp simp: mmu_translate_tlb_sat_state'_ext_def Let_def)
   apply (cases "lookup (tlb_sat_set' s \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s))) (ASID s) (addr_val va) ")
   by (clarsimp simp:raise'exception_def split: split_if_asm)+


lemma mmu_translate_sa_consistent:
  assumes A: "mmu_translate va s = (pa, s')"
  shows
  "\<lbrakk>  consistent'' (typ_sat_tlb' s) va ; saturated' (typ_sat_tlb' s)\<rbrakk>  \<Longrightarrow>  consistent'' (typ_sat_tlb' s') va"
  thm mmu_translate_sat_TLB_union
  by (simp add: saturated'_def sup.absorb1 mmu_translate_sat_TLB_union[OF A] mmu_sat_eq_ASID_TTBR0_MEM[OF A])



lemma mmu_translate_abs_rel:
  "\<lbrakk>  mmu_translate va t = (pa', t')\<rbrakk>  \<Longrightarrow> (t'::'a tlb_incon_state_scheme) = t\<lparr>exception := exception t'\<rparr>"
  by (clarsimp simp: mmu_translate_tlb_incon_state_ext_def Let_def raise'exception_def split: split_if_asm)


lemma mmu_sat_rel:
  "\<lbrakk> mmu_translate va s = (p, s') \<rbrakk>  \<Longrightarrow> s' = s \<lparr> tlb_sat_set' := tlb_sat_set' s' , exception:= exception s' \<rparr>"
  apply (clarsimp simp: mmu_translate_tlb_sat_state'_ext_def Let_def  split:lookup_type.splits)
    apply (clarsimp simp: raise'exception_def split:split_if_asm)+
done


lemma saturated_not_miss:
  "lookup (state.more s \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s))) (ASID s) (addr_val (v::vaddr)) \<noteq> Miss"
  apply clarsimp
  apply (clarsimp simp: lookup_def split:split_if_asm)
  apply (subgoal_tac "entry_set (range (pt_walk (ASID s) (MEM s) (TTBR0 s))) (ASID s) (addr_val v) \<noteq> {}")
   using entry_set_def apply fastforce[1]
  apply (clarsimp simp: entry_set_def)
  apply (rule_tac x = "pt_walk (ASID s) (MEM s) (TTBR0 s) v" in exI)
  apply (clarsimp simp: entry_range_asid_tags_def)
done

lemma mmu_translate_sat_abs_refine:
  "\<lbrakk> mmu_translate va s = (pa, s');  mmu_translate va t = (pa', t') ;
      saturated' (typ_sat_tlb' s); (ASID t, addr_val va) \<notin> (tlb_incon_set t) ; tlb_rel_abs (typ_sat_tlb' s) (typ_incon t) \<rbrakk> \<Longrightarrow> 
            tlb_rel_abs  (typ_sat_tlb' s') (typ_incon t')"
  apply (insert tlb_rel_abs_consistent[of t va s] ,frule tlb_rel_absD ,frule mmu_translate_sa_consistent ; clarsimp simp: tlb_rel_abs_def)
  apply (subgoal_tac "s' = s\<lparr>exception := exception s'\<rparr> \<and> t' = t\<lparr>exception := exception t'\<rparr>")
   apply (subgoal_tac "exception t' = exception s'")
    apply (cases t, cases t, cases s, cases s', clarsimp simp: state.defs)
  apply (subgoal_tac "tlb_sat_set' s' = tlb_sat_set' s \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s)) \<and> ASID s' = ASID s
   \<and> MEM s' = MEM s \<and> TTBR0 s' = TTBR0 s")
   apply (clarsimp simp: mmu_translate_tlb_sat_state'_ext_def split_def Let_def)
   apply (cases "lookup (tlb_sat_set' s \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s))) (ASID s) (addr_val va)")
     apply (metis (no_types, lifting) saturated_not_miss tlb_sat_more' typ_sat_prim_parameter')
    apply (clarsimp simp: consistent0''_def)
   apply clarsimp
   apply (clarsimp simp: mmu_translate_tlb_incon_state_ext_def Let_def)
   apply (subgoal_tac "x3 = pt_walk (ASID s) (MEM s) (TTBR0 s) va")
    apply (clarsimp simp: raise'exception_def split:split_if_asm)
   apply (clarsimp simp: consistent0''_def)
  apply (clarsimp simp: mmu_translate_sat_TLB_union mmu_sat_eq_ASID_TTBR0_MEM)

 apply (frule mmu_translate_abs_rel, clarsimp)
   apply (subgoal_tac "tlb_sat_set' s' = tlb_sat_set' s")
    apply (drule mmu_sat_rel, clarsimp)
   using mmu_translate_sat_TLB_union sat_state_tlb' apply fastforce

done

(* lemma mmu_translate_sat_abs_refine:
assumes A:"mmu_translate va s = (pa, s')"
assumes B:"mmu_translate va t = (pa', t') "
shows
  "\<lbrakk> saturated' (typ_sat_tlb' s); (ASID t, addr_val va) \<notin> (tlb_incon_set t) ; tlb_rel_abs (typ_sat_tlb' s) (typ_incon t) \<rbrakk> \<Longrightarrow> 
            tlb_rel_abs  (typ_sat_tlb' s') (typ_incon t')"
  apply (insert tlb_rel_abs_consistent[of t va s] ,frule tlb_rel_absD ,insert mmu_translate_sa_consistent [OF A] ,
           insert mmu_translate_abs_rel [OF B]; clarsimp simp: tlb_rel_abs_def)

  apply (subgoal_tac "s' = s\<lparr>exception := exception s'\<rparr> ")

   apply (subgoal_tac "exception t' = exception s'")
    apply (cases t, cases t, cases s, cases s', clarsimp simp: state.defs)
  
  
  apply (subgoal_tac "tlb_sat_set' s' = tlb_sat_set' s \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s)) \<and> ASID s' = ASID s
   \<and> MEM s' = MEM s \<and> TTBR0 s' = TTBR0 s")
   apply (clarsimp simp: mmu_translate_tlb_sat_state'_ext_def split_def Let_def)
   apply (cases "lookup (tlb_sat_set' s \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s))) (ASID s) (addr_val va)")
     apply (metis (no_types, lifting) saturated_not_miss tlb_sat_more' typ_sat_prim_parameter')
    apply (clarsimp simp: consistent0''_def)
   apply (clarsimp simp: mmu_translate_tlb_incon_state_ext_def Let_def)
   apply (subgoal_tac "x3 = pt_walk (ASID s) (MEM s) (TTBR0 s) va")
    apply (clarsimp simp: raise'exception_def split:split_if_asm)
   apply (clarsimp simp: consistent0''_def)
  apply (clarsimp simp: mmu_translate_sat_TLB_union mmu_sat_eq_ASID_TTBR0_MEM)

 apply (frule mmu_translate_abs_rel, clarsimp)
   apply (subgoal_tac "tlb_sat_set' s' = tlb_sat_set' s")
    apply (drule mmu_sat_rel, clarsimp)
   using mmu_translate_sat_TLB_union sat_state_tlb' apply fastforce

done *)

lemma mmu_translate_det_sat_pa:
  "\<lbrakk> mmu_translate va s = (pa, s'); consistent' (typ_sat_tlb t) va; tlb_rel_sat (typ_det_tlb s) (typ_sat_tlb t) ;
  mmu_translate va t = (pa', t')  \<rbrakk> \<Longrightarrow> pa = pa'"
using mmu_translate_det_sat_refine by fastforce
 


lemma mmu_translate_sat_sat':
  "mmu_translate v s = (p,t) \<Longrightarrow>  saturated (typ_sat_tlb t)"
  apply (clarsimp simp: mmu_translate_tlb_sat_state_ext_def Let_def  )
  apply (cases "lookup (fst (pairunion (tlb_sat_set s) (range (pt_walk (ASID s) (MEM s) (TTBR0 s)),
    range (pde_walk (ASID s) (MEM s) (TTBR0 s))))) (ASID s) (addr_val v)" ; clarsimp)
    apply (metis fst_union_tlb saturated_fst_not_miss)
   apply (clarsimp simp:saturated_def raise'exception_def split:split_if_asm)
    apply (smt Pair_inject Un_upper2 pairunion.simps prod.collapse)
   apply (smt Pair_inject Un_upper2 pairunion.simps prod.collapse)
  apply (clarsimp split:split_if_asm)
   apply (clarsimp simp:saturated_def raise'exception_def split:split_if_asm)
    apply (smt Pair_inject Un_upper2 pairunion.simps prod.collapse)
   apply (smt Pair_inject Un_upper2 pairunion.simps prod.collapse)
  apply (clarsimp simp: saturated_def)
  apply (smt Pair_inject Un_upper2 pairunion.simps prod.collapse)
done




lemma write'mem1_eq_TLB:
  "\<lbrakk> write'mem1 (val, va, sz) s = ((), s') \<rbrakk>  \<Longrightarrow> state.more s' = state.more s"
   by (clarsimp simp: write'mem1_def raise'exception_def split: split_if_asm)



lemma mmu_det_rel:
  "\<lbrakk> mmu_translate va s = (p, s') \<rbrakk>  \<Longrightarrow> s' = s \<lparr> tlb_det_set := tlb_det_set s' , exception:= exception s' \<rparr>"
  apply (clarsimp simp: mmu_translate_tlb_det_state_ext_def Let_def  split:lookup_type.splits lookup_pde_type.splits split_if_asm)
    apply (clarsimp simp: raise'exception_def split:split_if_asm)+
done


lemma mmu_rel:
  "\<lbrakk> mmu_translate va s = (p, s') \<rbrakk>  \<Longrightarrow> s' = s \<lparr> tlb_set := tlb_set s' , exception:= exception s' \<rparr>"
  apply (clarsimp simp: mmu_translate_tlb_state_ext_def Let_def  split:lookup_type.splits lookup_pde_type.splits split_if_asm)
    apply (clarsimp simp: raise'exception_def split:split_if_asm)+
done



lemma write'mem1_eq_ASID_TTBR0:
  "\<lbrakk> write'mem1 (val, va, sz) s = ((), s') \<rbrakk>  \<Longrightarrow> ASID s' = ASID s \<and> TTBR0 s' = TTBR0 s"
   by (clarsimp simp: write'mem1_def raise'exception_def split: split_if_asm)
  
lemma mmu_incon_eq_ASID_TTBR0_MEM:
  "\<lbrakk> mmu_translate va (s::'a tlb_incon_state_scheme) = (pa , s') \<rbrakk>  \<Longrightarrow> ASID s = ASID s' \<and> TTBR0 s = TTBR0 s' \<and>
                      MEM s = MEM s'"
   apply (clarsimp simp: mmu_translate_tlb_incon_state_ext_def Let_def split: split_if_asm)
   by (clarsimp simp:raise'exception_def split: split_if_asm)+


lemma mmu_det_eq_ASID_TTBR0_MEM:
  "\<lbrakk> mmu_translate va (s::'a tlb_det_state_scheme) = (pa , s') \<rbrakk>  \<Longrightarrow> ASID s = ASID s' \<and> TTBR0 s = TTBR0 s' \<and>
                      MEM s = MEM s'"
  apply (clarsimp simp: mmu_translate_tlb_det_state_ext_def Let_def  split:lookup_type.splits lookup_pde_type.splits split_if_asm)
    apply (clarsimp simp: raise'exception_def split:split_if_asm)+
done
 


lemma mmu_sat_eq_ASID_TTBR0_MEM':
  "\<lbrakk> mmu_translate va (s::'a tlb_sat_state_scheme) = (pa , s') \<rbrakk>  \<Longrightarrow> ASID s = ASID s' \<and> TTBR0 s = TTBR0 s' \<and>
                      MEM s = MEM s'"
 apply (clarsimp simp: mmu_translate_tlb_sat_state_ext_def Let_def  split:lookup_type.splits lookup_pde_type.splits split_if_asm)
    apply (clarsimp simp: raise'exception_def split:split_if_asm)+
done
 


lemma mmu_eq_ASID_TTBR0_MEM:
  "\<lbrakk> mmu_translate va (s::'a tlb_state_scheme) = (pa , s') \<rbrakk>  \<Longrightarrow> ASID s = ASID s' \<and> TTBR0 s = TTBR0 s' \<and>
                      MEM s = MEM s'"
 apply (clarsimp simp: mmu_translate_tlb_state_ext_def Let_def  split:lookup_type.splits lookup_pde_type.splits split_if_asm)
    apply (clarsimp simp: raise'exception_def split:split_if_asm)+
done

lemma write_same_mem:
  "\<lbrakk> write'mem1 (val, va, sz) s = ((), s') ; write'mem1 (val, va, sz) t = ((), t') ;
      MEM s = MEM t\<rbrakk>  \<Longrightarrow>  MEM s' = MEM t'"
  by (clarsimp simp: write'mem1_def raise'exception_def split:split_if_asm)

lemma write_same_mem_excep:
  "\<lbrakk> write'mem1 (val, pa, sz) s = ((), s') ; write'mem1 (val, pa, sz) t = ((), t') ;
      MEM s = MEM t ; exception s = exception t \<rbrakk>  \<Longrightarrow> exception s' = exception t'"
   apply (clarsimp simp: write'mem1_def raise'exception_def split:split_if_asm)
done

 
lemma mmu_translate_mem_excep:
  "\<lbrakk> mmu_translate va s = (p, s') ; mmu_translate va t = (p, t') ;
     consistent' (typ_sat_tlb t) va; tlb_rel_sat (typ_det_tlb s) (typ_sat_tlb t)\<rbrakk>  \<Longrightarrow> MEM s' = MEM t' \<and> exception s' = exception t'"
  apply (subgoal_tac "tlb_rel_sat (typ_det_tlb s') (typ_sat_tlb t')")
   apply (clarsimp simp: tlb_rel_sat_def state.defs)
  apply (drule (2) mmu_translate_det_sat_refine, clarsimp simp: Let_def)
 done

lemma mmu_translate_mem_excep1:
  "\<lbrakk> mmu_translate va s = (p, s') ; mmu_translate va t = (p, t') ;
     consistent' (typ_sat_tlb t) va; tlb_rel_sat (typ_tlb s) (typ_sat_tlb t)\<rbrakk>  \<Longrightarrow> MEM s' = MEM t' \<and> exception s' = exception t'"
  apply (subgoal_tac "tlb_rel_sat (typ_tlb s') (typ_sat_tlb t')")
   apply (clarsimp simp: tlb_rel_sat_def state.defs)
  apply (drule (2)  mmu_translate_sat_refine_non_det, clarsimp simp: Let_def)
 done

 
lemma mmu_translate_excep:
  "\<lbrakk> mmu_translate va s = (p, s') ; mmu_translate va t = (p, t') ;
     consistent' (typ_sat_tlb t) va; tlb_rel_sat (typ_det_tlb s) (typ_sat_tlb t)\<rbrakk>  \<Longrightarrow>  exception s' = exception t'"
  apply (subgoal_tac "tlb_rel_sat (typ_det_tlb s') (typ_sat_tlb t')")
   apply (clarsimp simp: tlb_rel_sat_def state.defs)
  apply (drule (2) mmu_translate_det_sat_refine, clarsimp simp: Let_def)
 done



lemma mmu_translate_excep1:
  "\<lbrakk> mmu_translate va s = (p, s') ; mmu_translate va t = (p, t') ;
     consistent' (typ_sat_tlb t) va; tlb_rel_sat (typ_tlb s) (typ_sat_tlb t)\<rbrakk>  \<Longrightarrow>  exception s' = exception t'"
  apply (subgoal_tac "tlb_rel_sat (typ_tlb s') (typ_sat_tlb t')")
   apply (clarsimp simp: tlb_rel_sat_def state.defs)
  apply (drule (2) mmu_translate_sat_refine_non_det, clarsimp simp: Let_def)
 done

lemma write'mem1_rel:
  "\<lbrakk> write'mem1 (val, va, sz) s = ((), s') \<rbrakk>  \<Longrightarrow> s' = s \<lparr> MEM:= MEM s' , exception:= exception s' \<rparr>"
   by (clarsimp simp: write'mem1_def raise'exception_def split: split_if_asm)





(*  mem instants *)

instantiation tlb_state_ext :: (type) mem_op 
begin

definition   
  "(mmu_read  :: (vaddr  \<Rightarrow>  'a tlb_state_scheme \<Rightarrow> bool list \<times>  'a tlb_state_scheme))
   \<equiv>  \<lambda>va. do {
                     pa  \<leftarrow> mmu_translate va;
                     mem1 pa
  }"

definition
 "(mmu_read_size  :: (vaddr \<times> nat \<Rightarrow>  'a tlb_state_scheme \<Rightarrow> bool list \<times>  'a tlb_state_scheme))
  \<equiv> \<lambda>(va,size). do {
                     pa  \<leftarrow> mmu_translate va;
                     mem_read1 (pa , size)
  }"

thm  mmu_read_size_tlb_state_ext_def

definition   
  "(mmu_write_size  :: (bool list \<times> vaddr \<times> nat \<Rightarrow> 'a tlb_state_scheme \<Rightarrow> unit \<times> 'a tlb_state_scheme))
   \<equiv> \<lambda>(value, vaddr, size). do {
     paddr <- mmu_translate vaddr;
     exception <- read_state exception;
     if exception = NoException 
       then  write'mem1 (value, paddr, size)
       else return ()
  }"
(* print_context *)                      
  instance ..
end

thm  mmu_write_size_tlb_state_ext_def

instantiation tlb_det_state_ext :: (type) mem_op   
begin


definition   
  "(mmu_read  :: (vaddr  \<Rightarrow>  'a tlb_det_state_scheme \<Rightarrow> bool list \<times>  'a tlb_det_state_scheme))
   \<equiv>  \<lambda>va. do {
                     pa  \<leftarrow> mmu_translate va;
                     mem1 pa
  }"

definition
 "(mmu_read_size  :: (vaddr \<times> nat \<Rightarrow>  'a tlb_det_state_scheme \<Rightarrow> bool list \<times>  'a tlb_det_state_scheme))
  \<equiv> \<lambda>(va,size). do {
                     pa  \<leftarrow> mmu_translate va;
                     mem_read1 (pa , size)
  }"

definition   
  "(mmu_write_size  :: (bool list \<times> vaddr \<times> nat \<Rightarrow> 'a tlb_det_state_scheme \<Rightarrow> unit \<times> 'a tlb_det_state_scheme))
   \<equiv> \<lambda>(value, vaddr, size). do {
     paddr <- mmu_translate vaddr;
     exception <- read_state exception;
     if exception = NoException 
       then  write'mem1 (value, paddr, size)
       else return ()
  }"
  instance ..
end


instantiation tlb_sat_state_ext :: (type) mem_op    
begin

definition   
  "(mmu_read  :: (vaddr  \<Rightarrow>  'a tlb_sat_state_scheme \<Rightarrow> bool list \<times>  'a tlb_sat_state_scheme))
   \<equiv>  \<lambda>va. do {
                     pa  \<leftarrow> mmu_translate va;
                     mem1 pa
  }"

definition
 "(mmu_read_size  :: (vaddr \<times> nat \<Rightarrow>  'a tlb_sat_state_scheme \<Rightarrow> bool list \<times>  'a tlb_sat_state_scheme))
  \<equiv> \<lambda>(va,size). do {
                     pa  \<leftarrow> mmu_translate va;
                     mem_read1 (pa , size)
  }"


definition   
  "(mmu_write_size  :: (bool list \<times> vaddr \<times> nat \<Rightarrow> 'a tlb_sat_state_scheme \<Rightarrow> unit \<times> 'a tlb_sat_state_scheme))
   \<equiv> \<lambda>(value, vaddr, size).  do {
     ttbr0 <- read_state TTBR0;
     asid <- read_state ASID;
     pa <- mmu_translate vaddr;
     tlb_pde0   <- read_state tlb_sat_set;
     exception <- read_state exception;
     if exception = NoException 
      then do { 
           write'mem1 (value, pa, size); 
           mem1  <- read_state MEM;
           let all_pdes = pde_walk asid mem1 ttbr0 ` UNIV;
           let all_tlbes = \<Union>(tlb_pde_walk asid all_pdes mem1 ttbr0 ` UNIV);
           let tlb_pde = pairunion tlb_pde0 (all_tlbes , all_pdes) ;
           update_state (\<lambda>s. s\<lparr> tlb_sat_set := tlb_pde \<rparr>)
          } 
      else return () 
    }" 
  instance ..
end




instantiation tlb_sat_state'_ext :: (type) mem_op    
begin

definition   
  "(mmu_read  :: (vaddr  \<Rightarrow>  'a tlb_sat_state'_scheme \<Rightarrow> bool list \<times>  'a tlb_sat_state'_scheme))
   \<equiv>  \<lambda>va. do {
                     pa  \<leftarrow> mmu_translate va;
                     mem1 pa
  }"

definition
 "(mmu_read_size  :: (vaddr \<times> nat \<Rightarrow>  'a tlb_sat_state'_scheme \<Rightarrow> bool list \<times>  'a tlb_sat_state'_scheme))
  \<equiv> \<lambda>(va,size). do {
                     pa  \<leftarrow> mmu_translate va;
                     mem_read1 (pa , size)
  }"

definition   
  "(mmu_write_size  :: (bool list \<times> vaddr \<times> nat \<Rightarrow> 'a tlb_sat_state'_scheme \<Rightarrow> unit \<times> 'a tlb_sat_state'_scheme))
   \<equiv> \<lambda>(value, vaddr, size).  do {
     ttbr0 <- read_state TTBR0;
     asid <- read_state ASID;
     pa <- mmu_translate vaddr;
     tlb0  <- read_state tlb_sat_set';
     exception <- read_state exception;
     if exception = NoException 
      then do { 
           write'mem1 (value, pa, size); 
           mem1  <- read_state MEM;
           let all_entries = pt_walk asid mem1 ttbr0 ` UNIV;
           let tlb = tlb0 \<union> all_entries;  (* what about inconsistency here ? *)
           update_state (\<lambda>s. s\<lparr> tlb_sat_set' := tlb \<rparr>)
          } 
      else return () 
    }"
  instance ..
end


definition 
  ptable_asid_va :: "asid \<Rightarrow> heap \<Rightarrow> ttbr0 \<Rightarrow> (asid \<times> va) set"
where
  "ptable_asid_va  asid heap ttbr0 \<equiv> \<Union>(entry_range_asid_tags `(pt_walk asid heap ttbr0 ` UNIV))"


definition 
  ptable_comp :: "asid \<Rightarrow> heap \<Rightarrow> heap \<Rightarrow> ttbr0 \<Rightarrow> (asid \<times> va) set"
where
  "ptable_comp  asid hp1 hp2 ttbr0 \<equiv> 
         (\<lambda>x. (asid, addr_val x)) ` {va. pt_walk asid hp1 ttbr0 va \<noteq> pt_walk asid hp2 ttbr0 va }"


instantiation tlb_incon_state_ext :: (type) mem_op     
begin

definition   
  "(mmu_read  :: (vaddr  \<Rightarrow>  'a tlb_incon_state_scheme \<Rightarrow> bool list \<times>  'a tlb_incon_state_scheme))
   \<equiv>  \<lambda>va. do {
                     pa  \<leftarrow> mmu_translate va;
                     mem1 pa
  }"

definition
 "(mmu_read_size  :: (vaddr \<times> nat \<Rightarrow>  'a tlb_incon_state_scheme \<Rightarrow> bool list \<times>  'a tlb_incon_state_scheme))
  \<equiv> \<lambda>(va,size). do {
                     pa  \<leftarrow> mmu_translate va;
                     mem_read1 (pa , size)
  }"


definition   
  "(mmu_write_size  :: (bool list \<times> vaddr \<times> nat \<Rightarrow> 'a tlb_incon_state_scheme \<Rightarrow> unit \<times> 'a tlb_incon_state_scheme))
   \<equiv> \<lambda>(value, vaddr, size). do {
      ttbr0 <- read_state TTBR0;
      asid  <- read_state ASID;
      mem   <- read_state MEM; 
      paddr <- mmu_translate vaddr;
      incon_set <- read_state tlb_incon_set; 
      exception <- read_state exception;
      if exception = NoException 
        then  do {
                   write'mem1 (value, paddr, size);
                   mem' <- read_state MEM;
                   ptable_asid_va <- return (ptable_comp asid mem mem' ttbr0);
                   update_state (\<lambda>s. s\<lparr> tlb_incon_set :=  incon_set \<union> ptable_asid_va \<rparr>)
            }
        else return ()
   }"

  instance ..
end

  

lemma write_size_saturated:
  "\<lbrakk>mmu_write_size (val,va,sz) s = ((), t)  \<rbrakk>  \<Longrightarrow> saturated (typ_sat_tlb t)"
  apply (clarsimp simp: mmu_write_size_tlb_sat_state_ext_def Let_def)
  apply (cases "mmu_translate va s" ; clarsimp)
  apply (clarsimp split: split_if_asm)
   apply (case_tac "write'mem1 (val, a, sz) b" ; clarsimp simp: Let_def)
   apply (clarsimp simp: saturated_def)
   apply (rule conjI)
    apply (clarsimp simp:  )
    apply (subgoal_tac "ASID s = ASID ba \<and> TTBR0 s = TTBR0 ba ")
     apply (clarsimp simp: saturated_def fst_def)
     apply (metis UnI2 fst_conv fst_union_tlb rangeI)
    apply (subgoal_tac "ASID s = ASID b \<and> TTBR0 s = TTBR0 b")
     apply (clarsimp simp:  write'mem1_def Let_def raise'exception_def )
     apply (clarsimp split:split_if_asm)
     apply (clarsimp simp:  write'mem1_def Let_def raise'exception_def)
    apply (clarsimp simp: mmu_translate_tlb_sat_state_ext_def
   Let_def raise'exception_def split:lookup_type.splits lookup_pde_type.splits split_if_asm)
   apply (clarsimp simp:  )
   apply (subgoal_tac "ASID s = ASID ba \<and> TTBR0 s = TTBR0 ba ")
    apply (clarsimp simp: saturated_def snd_def)
    apply (metis (no_types, lifting) Pair_inject Un_upper2 pairunion.simps prod.collapse rangeI set_rev_mp)
   prefer 2
   apply (simp add: mmu_translate_sat_sat')
  apply (subgoal_tac "ASID s = ASID b \<and> TTBR0 s = TTBR0 b")
   apply (clarsimp simp:  write'mem1_def Let_def raise'exception_def )
   apply (clarsimp split:split_if_asm)
   apply (clarsimp simp:  write'mem1_def Let_def raise'exception_def)
  apply (clarsimp simp: mmu_translate_tlb_sat_state_ext_def
                          Let_def raise'exception_def split:lookup_type.splits lookup_pde_type.splits split_if_asm)
done
   
  

lemma mem1_exception:
  "mem1 p b = (val, r) \<Longrightarrow>  r = b\<lparr>exception := exception r\<rparr>"
  apply (clarsimp simp: mem1_def)
  apply (cases "MEM b p")
   apply (clarsimp simp: raise'exception_def split: split_if_asm)
  apply clarsimp
done


lemma mem1_read_exception:
  "mem_read1 (a, sz) b = (val, r) \<Longrightarrow> r = b \<lparr>exception := exception r\<rparr>"
  apply (clarsimp simp: mem_read1_def)
  apply (clarsimp split: split_if_asm)
      apply (case_tac "mem1 (a r+ 0) b" , clarsimp)
      apply (clarsimp simp: mem1_exception)
     apply (case_tac "mem1 (a r+ 1) b" , clarsimp)
     apply (case_tac "mem1 (a r+ 0) ba", clarsimp)
     apply (drule mem1_exception)
     apply (drule mem1_exception)
     apply (cases b, case_tac ba, cases r ,clarsimp)
    apply (case_tac "mem1 (a r+ 3) b" , clarsimp)
    apply (case_tac "mem1 (a r+ 2) ba", clarsimp)
    apply (case_tac "mem1 (a r+ 1) baa", clarsimp)
    apply (case_tac "mem1 (a r+ 0) bb", clarsimp)
    apply (drule mem1_exception)
    apply (drule mem1_exception)
    apply (drule mem1_exception)
    apply (drule mem1_exception)
    apply (cases b, case_tac ba, case_tac baa, case_tac bb , cases r ,clarsimp)
   apply (case_tac "mem1 (a r+ 7) b" , clarsimp)
   apply (case_tac "mem1 (a r+ 6) ba", clarsimp)
   apply (case_tac "mem1 (a r+ 5) baa", clarsimp)
   apply (case_tac "mem1 (a r+ 4) bb", clarsimp)
   apply (case_tac "mem1 (a r+ 3) bc", clarsimp)
   apply (case_tac "mem1 (a r+ 2) bd", clarsimp)
   apply (case_tac "mem1 (a r+ 1) be", clarsimp)
   apply (case_tac "mem1 (a r+ 0) bf", clarsimp)
   apply (drule mem1_exception)
   apply (drule mem1_exception)
   apply (drule mem1_exception)
   apply (drule mem1_exception)
   apply (drule mem1_exception)
   apply (drule mem1_exception)
   apply (drule mem1_exception)
   apply (drule mem1_exception)
   apply (cases b, case_tac ba, case_tac baa, case_tac bb ,case_tac bc ,
                   case_tac bd ,  case_tac be ,  case_tac bf , cases r ,clarsimp)
  apply (clarsimp simp: raise'exception_def split:split_if_asm)
done


lemma pt_walk_range:
  "\<forall>va. pt_walk (ASID s) (MEM s) (TTBR0 s) va =  pt_walk (ASID s') (MEM s') (TTBR0 s') va  \<Longrightarrow> 
     pt_walk (ASID s) (MEM s) (TTBR0 s) ` UNIV = pt_walk (ASID s') (MEM s') (TTBR0 s') ` UNIV"
  by auto


lemma write'mem'det1_TLBs1:
  "\<lbrakk> mmu_write_size (val,va, sz) s = ((), s') \<rbrakk> \<Longrightarrow>
     fst(tlb_det_set s') = fst(tlb_det_set s) \<or>  fst(tlb_det_set s') = fst(tlb_det_set s) \<union> {pt_walk (ASID s) (MEM s) (TTBR0 s) va} \<or>
     fst(tlb_det_set s') = fst(tlb_det_set s) \<union>  (\<lambda>x. pde_tlb_entry x (MEM s) va) ` {x. lookup_pde (snd(tlb_det_set s)) (ASID s) (addr_val va) = Hit_pde x }"
  apply (cases "lookup (fst(tlb_det_set s)) (ASID s) (addr_val va)")
    prefer 3
    apply (clarsimp simp:  mmu_write_size_tlb_det_state_ext_def mmu_translate_tlb_det_state_ext_def split_def Let_def raise'exception_def write'mem1_eq_TLB
                    split:split_if_asm)
    apply (drule write'mem1_eq_TLB state.defs)
    apply (cases s , cases s' ; clarsimp)
   prefer 2
   apply (rule disjI1)
   apply (clarsimp simp:  mmu_write_size_tlb_det_state_ext_def mmu_translate_tlb_det_state_ext_def split_def Let_def raise'exception_def write'mem1_eq_TLB
                   split:split_if_asm)
  apply (cases "lookup_pde (snd(tlb_det_set s)) (ASID s) (addr_val va)")
    apply (cases " is_fault_pde (pde_walk (ASID s) (MEM s) (TTBR0 s) va)")
     apply (rule disjI1)
     apply (clarsimp simp: mmu_write_size_tlb_det_state_ext_def mmu_translate_tlb_det_state_ext_def split_def Let_def
                    raise'exception_def write'mem1_eq_TLB split:split_if_asm)
    apply (cases " is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) va)")

     apply (rule disjI1)
     apply (clarsimp simp: mmu_write_size_tlb_det_state_ext_def mmu_translate_tlb_det_state_ext_def split_def Let_def
      raise'exception_def write'mem1_eq_TLB  split:split_if_asm)
      apply (metis Pair_inject pairunion.simps prod.collapse sup_bot.comm_neutral)
     apply (metis Pair_inject pairunion.simps prod.collapse sup_bot.comm_neutral)

    apply (rule disjI2) apply (rule disjI1)
    apply (clarsimp simp: mmu_write_size_tlb_det_state_ext_def mmu_translate_tlb_det_state_ext_def split_def Let_def raise'exception_def
     split:split_if_asm)
     apply (drule write'mem1_eq_TLB state.defs)
     apply (cases s , cases s' ; clarsimp)
    apply (cases s , cases s' ; clarsimp)
   apply (rule disjI1)
   apply (clarsimp simp:  mmu_write_size_tlb_det_state_ext_def mmu_translate_tlb_det_state_ext_def split_def Let_def raise'exception_def write'mem1_eq_TLB
  split:split_if_asm)
  apply (case_tac "is_fault_pde x3")
   apply (rule disjI1)
   apply (clarsimp simp:  mmu_write_size_tlb_det_state_ext_def mmu_translate_tlb_det_state_ext_def split_def Let_def raise'exception_def write'mem1_eq_TLB
  split:split_if_asm)
  apply (case_tac "is_fault (pde_tlb_entry x3 (MEM s) va)")
   apply (rule disjI1)
   apply (clarsimp simp:  mmu_write_size_tlb_det_state_ext_def mmu_translate_tlb_det_state_ext_def split_def Let_def raise'exception_def write'mem1_eq_TLB
  split:split_if_asm)
  apply (rule disjI2) apply (rule disjI2)
  apply (clarsimp simp:  mmu_write_size_tlb_det_state_ext_def mmu_translate_tlb_det_state_ext_def split_def Let_def raise'exception_def write'mem1_eq_TLB
   split:split_if_asm)

   apply (drule write'mem1_eq_TLB state.defs)
   apply (cases s , cases s' ; clarsimp)
  apply (cases s , cases s' ; clarsimp)

done

find_theorems "mmu_translate" "_ \<union> _"

lemma mmu_translate_sat_TLB_union':
  "mmu_translate v s = (p,t) \<Longrightarrow> 
      fst (tlb_sat_set t) = fst(tlb_sat_set s)  \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s))"
  apply (clarsimp simp:  mmu_translate_tlb_sat_state_ext_def Let_def)

  apply (subgoal_tac "(fst (pairunion (tlb_sat_set s) (range (pt_walk (ASID s) (MEM s) (TTBR0 s)), range (pde_walk (ASID s) (MEM s) (TTBR0 s))))) = 
     fst(tlb_sat_set s)  \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s))   ")
  apply (cases "lookup (fst (tlb_sat_set s) \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s))) (ASID s) (addr_val v)")
    apply (clarsimp simp:raise'exception_def split:split_if_asm) +
by (simp add: fst_union_tlb)

lemma mmu_translate_sat_pde_union':
  "mmu_translate v s = (p,t) \<Longrightarrow> 
      snd (tlb_sat_set t) = snd(tlb_sat_set s)  \<union> range (pde_walk (ASID s) (MEM s) (TTBR0 s))"
  apply (clarsimp simp:  mmu_translate_tlb_sat_state_ext_def Let_def)

  apply (subgoal_tac "(fst (pairunion (tlb_sat_set s) (range (pt_walk (ASID s) (MEM s) (TTBR0 s)), range (pde_walk (ASID s) (MEM s) (TTBR0 s))))) = 
     fst(tlb_sat_set s)  \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s))   ")
 apply (subgoal_tac "(snd (pairunion (tlb_sat_set s) (range (pt_walk (ASID s) (MEM s) (TTBR0 s)), range (pde_walk (ASID s) (MEM s) (TTBR0 s))))) = 
     snd(tlb_sat_set s)  \<union> range (pde_walk (ASID s) (MEM s) (TTBR0 s))   ")
  apply (cases "lookup (fst (tlb_sat_set s) \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s))) (ASID s) (addr_val v)")
    apply (clarsimp simp:raise'exception_def split:split_if_asm) +
prefer 2 
apply (simp add: fst_union_tlb)
by (metis (no_types, lifting) old.prod.inject pairunion.simps prod.collapse)



lemma write'mem'sat_TLBs1:
  "\<lbrakk>mmu_write_size (val,va, sz) s = ((), s') \<rbrakk> \<Longrightarrow>
     fst(tlb_sat_set s') = fst(tlb_sat_set s) \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s)) \<or>
     fst(tlb_sat_set s') = fst(tlb_sat_set s) \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s)) \<union> range (pt_walk (ASID s') (MEM s') (TTBR0 s'))"
 apply (cases "exception (snd (mmu_translate va s)) \<noteq> NoException")
   apply (rule disjI1)
   apply (clarsimp simp: mmu_write_size_tlb_sat_state_ext_def Let_def) apply (cases " mmu_translate va s" ; clarsimp)
   apply (clarsimp simp: mmu_translate_sat_TLB_union')
  apply (rule disjI2)
   apply (clarsimp simp: mmu_write_size_tlb_sat_state_ext_def Let_def) apply (cases " mmu_translate va s" ; clarsimp)
   apply (case_tac "write'mem1 (val, a, sz) b" ; clarsimp simp: Let_def)
  apply (frule mmu_translate_sat_TLB_union')
  apply (clarsimp simp:fst_def)
  apply (case_tac "pairunion (tlb_sat_set b) (\<Union>x. tlb_pde_walk (ASID s) 
    (range (pde_walk (ASID s) (MEM ba) (TTBR0 s))) (MEM ba) (TTBR0 s) x, range (pde_walk (ASID s) (MEM ba) (TTBR0 s)))" ; clarsimp)
  apply (case_tac "tlb_sat_set s" ,case_tac "tlb_sat_set b" ; clarsimp)
  apply (subgoal_tac "ASID s = ASID ba \<and> TTBR0 s = TTBR0 ba" , clarsimp simp:  )
   apply (subgoal_tac "ASID ba = ASID b \<and> TTBR0 ba = TTBR0 b")
  using mmu_sat_eq_ASID_TTBR0_MEM' apply force
  using write'mem1_eq_ASID_TTBR0 by blast



lemma write'mem'det1_TLBs_pde:
  "\<lbrakk> mmu_write_size (val,va, sz) s = ((), s') \<rbrakk> \<Longrightarrow>
     snd(tlb_det_set s') = snd(tlb_det_set s) \<or>  snd(tlb_det_set s') = snd(tlb_det_set s) \<union> {pde_walk (ASID s) (MEM s) (TTBR0 s) va}"
  apply (cases "lookup (fst(tlb_det_set s)) (ASID s) (addr_val va)")
    prefer 3
    apply (clarsimp simp:  mmu_write_size_tlb_det_state_ext_def mmu_translate_tlb_det_state_ext_def split_def Let_def raise'exception_def write'mem1_eq_TLB
    split:split_if_asm)
    apply (drule write'mem1_eq_TLB state.defs)
    apply (cases s , cases s' ; clarsimp)
   prefer 2
   apply (rule disjI1)
   apply (clarsimp simp:  mmu_write_size_tlb_det_state_ext_def mmu_translate_tlb_det_state_ext_def split_def Let_def raise'exception_def write'mem1_eq_TLB
  split:split_if_asm)
  apply (cases "lookup_pde (snd(tlb_det_set s)) (ASID s) (addr_val va)")
    apply (cases " is_fault_pde (pde_walk (ASID s) (MEM s) (TTBR0 s) va)")
     apply (rule disjI1)
     apply (clarsimp simp: mmu_write_size_tlb_det_state_ext_def mmu_translate_tlb_det_state_ext_def split_def Let_def
    raise'exception_def write'mem1_eq_TLB split:split_if_asm)
    apply (rule disjI2)
    apply (clarsimp simp: mmu_write_size_tlb_det_state_ext_def
       mmu_translate_tlb_det_state_ext_def  Let_def
       raise'exception_def write'mem1_eq_TLB split:split_if_asm)
       apply (metis Pair_inject Un_insert_right pairunion.simps prod.collapse sup_bot.comm_neutral)
      apply (metis Pair_inject Un_insert_right pairunion.simps prod.collapse sup_bot.comm_neutral)
     apply (drule write'mem1_eq_TLB state.defs)
     apply (cases s , cases s' , clarsimp)
    apply (metis Pair_inject Un_insert_right pairunion.simps prod.collapse sup_bot.right_neutral)
   apply (rule disjI1)
   apply (clarsimp simp: mmu_write_size_tlb_det_state_ext_def mmu_translate_tlb_det_state_ext_def split_def Let_def
  raise'exception_def write'mem1_eq_TLB split:split_if_asm)
  apply (rule disjI1)
  apply (clarsimp simp: mmu_write_size_tlb_det_state_ext_def mmu_translate_tlb_det_state_ext_def split_def Let_def
   raise'exception_def write'mem1_eq_TLB split:split_if_asm)
   apply (drule write'mem1_eq_TLB state.defs)
   apply (cases s , cases s' , clarsimp)
  apply (metis Pair_inject pairunion.simps prod.collapse sup_bot.right_neutral)
done


lemma write'mem'sat_TLBs_pde:
  "\<lbrakk>mmu_write_size (val,va, sz) s = ((), s') \<rbrakk> \<Longrightarrow>
     snd(tlb_sat_set s') = snd(tlb_sat_set s) \<union> range (pde_walk (ASID s) (MEM s) (TTBR0 s)) \<or>
     snd(tlb_sat_set s') = snd(tlb_sat_set s) \<union> range (pde_walk (ASID s) (MEM s) (TTBR0 s)) \<union> range (pde_walk (ASID s') (MEM s') (TTBR0 s'))"
apply (cases "exception (snd (mmu_translate va s)) \<noteq> NoException")
   apply (rule disjI1)
 apply (clarsimp simp: mmu_write_size_tlb_sat_state_ext_def Let_def) apply (cases " mmu_translate va s" ; clarsimp)
   apply (clarsimp simp: mmu_translate_sat_pde_union')
  apply (rule disjI2)
  apply (clarsimp simp: mmu_write_size_tlb_sat_state_ext_def Let_def) apply (cases " mmu_translate va s" ; clarsimp)
   apply (case_tac "write'mem1 (val, a, sz) b" ; clarsimp simp: Let_def)
  apply (frule mmu_translate_sat_pde_union')
  apply (clarsimp simp:snd_def)
  apply (case_tac "pairunion (tlb_sat_set b) (\<Union>x. tlb_pde_walk (ASID s) 
    (range (pde_walk (ASID s) (MEM ba) (TTBR0 s))) (MEM ba) (TTBR0 s) x, range (pde_walk (ASID s) (MEM ba) (TTBR0 s)))" ; clarsimp)
  apply (case_tac "tlb_sat_set s" ,case_tac "tlb_sat_set b" ; clarsimp)
  apply (subgoal_tac "ASID s = ASID ba \<and> TTBR0 s = TTBR0 ba" , clarsimp simp:  )
   apply (subgoal_tac "ASID ba = ASID b \<and> TTBR0 ba = TTBR0 b")
  using mmu_sat_eq_ASID_TTBR0_MEM' apply force
  using write'mem1_eq_ASID_TTBR0 by blast



lemma tlb_rel_write1:
  "\<lbrakk> mmu_write_size (val,va, sz) s = ((), s'); tlb_rel_sat (typ_det_tlb s) (typ_sat_tlb t) ; consistent' (typ_sat_tlb t) va ;
  mmu_write_size (val,va, sz) t = ((), t') \<rbrakk> \<Longrightarrow> fst (tlb_det_set s') \<subseteq> fst(tlb_sat_set t') \<and>
  snd (tlb_det_set s') \<subseteq> snd (tlb_sat_set t')"
  apply (rule conjI)
   apply (frule tlb_rel_satD)
   apply (subgoal_tac "lookup (fst(tlb_det_set s)) (ASID s) (addr_val va) \<le> lookup (fst(tlb_sat_set t) \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s))) (ASID s) (addr_val va)")
    prefer 2
    apply (simp add: saturated_def sup.absorb1 tlb_mono tlb_rel_sat_def)
   apply (frule write'mem'det1_TLBs1)
   apply (frule write'mem'sat_TLBs1)
   apply (erule disjE)
    apply (clarsimp simp: typ_det_tlb_def typ_sat_tlb_def state.defs)
    apply blast
   apply (erule_tac P = " fst (tlb_det_set s') = fst (tlb_det_set s) \<union> {pt_walk (ASID s) (MEM s) (TTBR0 s) va} " in disjE)
    apply (clarsimp simp: tlb_rel_sat_def) apply blast
   apply clarsimp
   apply (rule conjI)
    apply blast
   apply (clarsimp simp: )
   apply (subgoal_tac "xa = pde_walk (ASID s) (MEM s) (TTBR0 s) va")
    apply (clarsimp simp: awesome) apply blast
   apply (subgoal_tac "lookup_pde (snd(tlb_det_set s)) (ASID s) (addr_val va) \<le> lookup_pde (snd(tlb_sat_set t)) (ASID s) (addr_val va)")
    prefer 2
    apply (subgoal_tac "snd(tlb_det_set s) \<subseteq> snd(tlb_sat_set t)")
     apply (drule_tac a = "(ASID s)" and v = " (addr_val va)" in  tlb_pde_mono)  apply clarsimp
    apply (simp add:  tlb_rel_sat_def)
   apply clarsimp
   apply (cases "PED_Cache.lookup_pde (snd (tlb_sat_set t)) (ASID s) (addr_val va)")
     apply force
    apply (clarsimp simp: consistent0'_def)
   apply (clarsimp simp: consistent0'_def)

  apply (frule tlb_rel_satD)
 apply (subgoal_tac "lookup_pde (snd(tlb_det_set s)) (ASID s) (addr_val va) \<le> lookup_pde (snd(tlb_sat_set t) \<union> range (pde_walk (ASID s) (MEM s) (TTBR0 s))) (ASID s) (addr_val va)")
    prefer 2
    apply (simp add: saturated_def sup.absorb1 tlb_pde_mono tlb_rel_sat_def)
  apply (frule write'mem'det1_TLBs_pde)
   apply (frule write'mem'sat_TLBs_pde)

  apply (erule disjE)
    apply (clarsimp simp: typ_det_tlb_def typ_sat_tlb_def state.defs)
    apply blast
   apply (erule disjE)
apply (clarsimp simp: typ_det_tlb_def typ_sat_tlb_def state.defs)
    apply blast
    apply auto
done



lemma  write'mem'det1_rel1:
  "\<lbrakk>mmu_write_size (val,va, sz) s = ((), s')\<rbrakk>   \<Longrightarrow> 
      s' = s \<lparr> tlb_det_set := tlb_det_set s' , MEM:= MEM s' , exception:= exception s' \<rparr>"
  apply (clarsimp simp:  mmu_write_size_tlb_det_state_ext_def Let_def)
  apply (cases "mmu_translate va s")
  apply (clarsimp split: split_if_asm)
   apply (drule write'mem1_rel)
   apply (cases "mmu_translate va s" , clarsimp)
   apply (drule mmu_det_rel)
   apply (cases s, cases s', case_tac b)
   apply clarsimp
  apply (clarsimp simp: mmu_translate_tlb_det_state_ext_def Let_def)
  apply (cases "lookup (fst (tlb_det_set s)) (ASID s) (addr_val va)" ; clarsimp)
  apply ( cases "PED_Cache.lookup_pde (snd (tlb_det_set s)) (ASID s) (addr_val va)" ; clarsimp simp: Let_def)
   apply (clarsimp simp: Let_def raise'exception_def split:split_if_asm)+
done

lemma mmu_sat_rel':
  "\<lbrakk> mmu_translate va s = (p, s') \<rbrakk>  \<Longrightarrow> s' = s \<lparr> tlb_sat_set := tlb_sat_set s' , exception:= exception s' \<rparr>"
  apply (clarsimp simp: mmu_translate_tlb_sat_state_ext_def Let_def  split:lookup_type.splits)
    apply (clarsimp simp: raise'exception_def split:split_if_asm)+
done

lemma write'mem'sat_rel1:
  "\<lbrakk>mmu_write_size (val,va, sz) s = ((), s')\<rbrakk>   \<Longrightarrow> 
      s' = s \<lparr> tlb_sat_set:= tlb_sat_set s' , MEM:= MEM s' , exception:= exception s' \<rparr>"
  apply (clarsimp simp:  mmu_write_size_tlb_sat_state_ext_def Let_def)
  apply (cases "mmu_translate va s")
  apply (clarsimp split: split_if_asm) apply (case_tac "write'mem1 (val, a, sz) b" ; clarsimp)
   apply (drule write'mem1_rel)
   apply (cases "mmu_translate va s" , clarsimp simp: Let_def)

   apply (drule mmu_sat_rel')
   apply (cases s, cases s', case_tac b ,  case_tac ba)
   apply clarsimp
  apply (clarsimp simp: mmu_translate_tlb_sat_state_ext_def Let_def)

  apply (cases "lookup (fst (pairunion (tlb_sat_set s)
                              (range (pt_walk (ASID s) (MEM s) (TTBR0 s)), range (pde_walk (ASID s) (MEM s) (TTBR0 s)))))
                 (ASID s) (addr_val va)" ; clarsimp)
apply (clarsimp simp: Let_def raise'exception_def split:split_if_asm)+

done



lemma write_mem_det_sat_MEM11:
  "\<lbrakk> mmu_write_size (val,va, sz) s = ((), s');  tlb_rel_sat (typ_det_tlb s) (typ_sat_tlb t) ; consistent' (typ_sat_tlb t) va; 
       mmu_write_size (val,va, sz) t = ((), t') \<rbrakk> \<Longrightarrow> MEM s' = MEM t'"
  apply (frule tlb_rel_satD)
  apply (clarsimp simp:  mmu_write_size_tlb_det_state_ext_def , cases "mmu_translate va s" , clarsimp)
  apply (clarsimp simp:  mmu_write_size_tlb_sat_state_ext_def , cases "mmu_translate va t" , clarsimp)
  apply (clarsimp split: split_if_asm)
     apply (case_tac "write'mem1 (val, aa, sz) ba" , clarsimp simp: Let_def)
     apply (subgoal_tac "MEM b = MEM ba \<and> aa = a")
      apply (metis write_same_mem)
     apply (rule conjI)
      apply (simp add: mmu_det_eq_ASID_TTBR0_MEM mmu_sat_eq_ASID_TTBR0_MEM')
     apply (frule_tac s= "(typ_det_tlb s)" and va= "va" in tlb_rel_sat_consistent, clarsimp)
     apply (subgoal_tac "lookup (fst(tlb_det_set s)) (ASID s) (addr_val va) \<le> lookup (fst(tlb_sat_set t) \<union>
      range (pt_walk (ASID s) (MEM s) (TTBR0 s))) (ASID s) (addr_val va)")
      prefer 2
      apply (subgoal_tac "fst (tlb_sat_set t) =  fst (tlb_sat_set t) \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s))")
       apply (simp add: saturated_def sup.absorb1 tlb_mono tlb_rel_sat_def)
      apply (metis mmu_det_eq_ASID_TTBR0_MEM saturated_def sup.orderE tlb_sat_more typ_sat_prim_parameter)
     apply (clarsimp simp:  mmu_translate_tlb_det_state_ext_def  mmu_translate_tlb_sat_state_ext_def split_def Let_def)
     apply (subgoal_tac "fst(tlb_sat_set t) = fst(tlb_sat_set t) \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s))")
      prefer 2
      apply (metis (no_types, lifting) saturated_def sup.orderE tlb_rel_satD tlb_sat_more typ_det_prim_parameter)
     apply (clarsimp simp:  )
     thm awesome  
     apply (cases "lookup (fst (pairunion (tlb_sat_set t) (range (pt_walk (ASID s) (MEM s) (TTBR0 s)),
       range (pde_walk (ASID s) (MEM s) (TTBR0 s))))) (ASID s) (addr_val va)")
       apply (clarsimp simp: tlb_rel_sat_def fst_union_tlb)
       apply (metis (no_types, lifting) saturated_fst_not_miss)
      apply (clarsimp simp: fst_union_tlb consistent0'_def)
     apply (clarsimp)
     apply (cases "lookup (fst (tlb_det_set s)) (ASID s) (addr_val va)"; clarsimp)
       apply (clarsimp simp: consistent0_def Let_def tlb_rel_sat_def
       lookup_in_tlb raise'exception_def split: split_if_asm)
       apply (cases "PED_Cache.lookup_pde (snd (tlb_det_set s)) (ASID s) (addr_val va)" ; clarsimp simp: Let_def)
         apply (clarsimp simp: consistent0_def Let_def tlb_rel_sat_def
         lookup_in_tlb raise'exception_def    split: split_if_asm)
         apply (subgoal_tac "x3 = pt_walk (ASID s) (MEM s) (TTBR0 s) va")
          apply clarsimp
         apply (clarsimp simp: fst_union_tlb consistent0'_def)
        apply (clarsimp simp: fst_union_tlb consistent0'_def)
       apply (clarsimp split: split_if_asm)
        apply (subgoal_tac "x3 = pt_walk (ASID s) (MEM s) (TTBR0 s) va")
         apply (subgoal_tac "x3a = pde_walk (ASID s) (MEM s) (TTBR0 s) va")
          apply clarsimp
          apply (clarsimp simp: is_fault_def is_fault_pde_def pt_walk_def pde_walk_def)
          apply (cases "get_pde (MEM s) (TTBR0 s) va" ; clarsimp)
          apply (case_tac aa ; clarsimp)
         prefer 2
         apply (clarsimp simp: fst_union_tlb consistent0'_def)
        apply (clarsimp simp:  consistent0'_def)
       apply (clarsimp simp: Let_def split:split_if_asm)
        apply (subgoal_tac "x3 = pt_walk (ASID s) (MEM s) (TTBR0 s) va")
         prefer 2
         apply (clarsimp simp: fst_union_tlb consistent0'_def)
        apply (subgoal_tac "x3a = pde_walk (ASID s) (MEM s) (TTBR0 s) va")
         prefer 2
         apply (clarsimp simp:  consistent0'_def)
        apply (clarsimp simp: awesome)
       apply (subgoal_tac "x3 = pt_walk (ASID s) (MEM s) (TTBR0 s) va")
        prefer 2
        apply (clarsimp simp: fst_union_tlb consistent0'_def)
       apply (subgoal_tac "x3a = pde_walk (ASID s) (MEM s) (TTBR0 s) va")
        prefer 2
        apply (clarsimp simp:  consistent0'_def)
       apply (clarsimp simp: awesome)
      apply (clarsimp simp:  consistent0'_def)
     apply (subgoal_tac "x3a = pt_walk (ASID s) (MEM s) (TTBR0 s) va")
      prefer 2
      apply (clarsimp simp: fst_union_tlb consistent0'_def)
     apply (subgoal_tac "x3 = pt_walk (ASID s) (MEM s) (TTBR0 s) va")
      prefer 2
      apply (clarsimp simp: fst_union_tlb consistent0'_def)
      apply (clarsimp simp: raise'exception_def split: split_if_asm)
    apply (metis mmu_translate_det_sat_pa mmu_translate_excep tlb_sat_more typ_sat_prim_parameter)
   apply (metis (mono_tags, lifting) mmu_translate_det_sat_pa mmu_translate_excep tlb_sat_more typ_sat_prim_parameter)
by (simp add: mmu_det_eq_ASID_TTBR0_MEM mmu_sat_eq_ASID_TTBR0_MEM')

 



lemma tlb_rel_2'1:
  "\<lbrakk>mmu_write_size (val,va, sz) s = ((), s'); tlb_rel_sat (typ_det_tlb s) (typ_sat_tlb t) ; consistent' (typ_sat_tlb t) va;
  mmu_write_size (val,va, sz) t = ((), t')\<rbrakk> \<Longrightarrow> state.truncate t' = state.truncate s'"
  apply (frule (3) write_mem_det_sat_MEM11)
  apply (frule tlb_rel_satD, clarsimp)
  apply (frule write'mem'det1_rel1)
  apply (rotate_tac)
  apply (frule write'mem'sat_rel1)
  apply (clarsimp simp: tlb_rel_sat_def)
  apply (subgoal_tac "exception s' = exception t'")
   apply (cases s, cases t, cases s' , cases t')
   apply (clarsimp simp: state.defs tlb_sat_state.defs)
  apply (clarsimp simp: mmu_write_size_tlb_sat_state_ext_def mmu_write_size_tlb_det_state_ext_def Let_def)
  apply (case_tac "mmu_translate va t" , case_tac "write'mem1 (val, a, sz) b" , clarsimp)
  apply (case_tac "mmu_translate va s" , clarsimp)
  apply (subgoal_tac "exception b = exception bb \<and> a = aa")
   apply (clarsimp simp: Let_def split: split_if_asm)
   apply (subgoal_tac "MEM b = MEM bb ")
    apply (frule_tac s="bb" and s'="s'" and t = b and t' = ba in write_same_mem_excep ; clarsimp)
   apply (frule_tac s="s" and s'="bb" and t = t and t' = b in mmu_translate_mem_excep ; clarsimp simp: consistent0'_def tlb_rel_sat_def)
  apply (rule conjI)
   prefer 2
   apply (subgoal_tac "lookup (fst(tlb_det_set s)) (ASID s) (addr_val va) \<le> lookup (fst(tlb_sat_set t) \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s))) (ASID s) (addr_val va)")
    prefer 2
    apply (simp add: saturated_def sup.absorb1 tlb_mono tlb_rel_sat_def)
   apply (frule_tac  s =s and t = t and s' = bb and t' = b and pa' = a in  mmu_translate_det_sat_pa ;clarsimp simp: tlb_rel_sat_def)
  apply (frule_tac s = "s" and s' = "bb" and t = "t" and t' = "b" in   mmu_translate_excep ;
  clarsimp simp: tlb_rel_sat_def)
  apply (frule_tac  s =s and t = t and s' = bb and t' = b and pa' = a in  mmu_translate_det_sat_pa ;clarsimp simp: tlb_rel_sat_def)
done


lemma write'mem'det1_sat_refine1:
  "\<lbrakk> mmu_write_size (val,va, sz) s = ((), s'); tlb_rel_sat (typ_det_tlb s) (typ_sat_tlb t) ; consistent' (typ_sat_tlb t) va;
        mmu_write_size (val,va, sz) t = ((), t') \<rbrakk> \<Longrightarrow> tlb_rel_sat (typ_det_tlb s') (typ_sat_tlb t')"
  apply (clarsimp simp: tlb_rel_sat_def)
  apply (clarsimp simp:  write_size_saturated)
  apply (rule conjI)
   prefer 2
   apply (frule_tac s="s" and s'="s'" and t="t" and t'="t'" in tlb_rel_write1; clarsimp simp: tlb_rel_sat_def)
  apply (frule_tac s="s" and s'="s'" and t="t" and t'="t'" in tlb_rel_2'1; clarsimp simp: tlb_rel_sat_def)
  done



lemma write'mem'_TLBs_pde:
  "\<lbrakk> mmu_write_size (val,va, sz) s = ((), s') \<rbrakk> \<Longrightarrow>
     snd(tlb_set s') = snd (pairsub (tlb_set s) (tlb_evict (typ_tlb s))) \<or>
     snd(tlb_set s') = snd (pairsub (tlb_set s) (tlb_evict (typ_tlb s))) \<union> {pde_walk (ASID s) (MEM s) (TTBR0 s) va}"
   apply (cases "lookup (fst (pairsub (tlb_set s) (tlb_evict (typ_tlb s)))) (ASID s) (addr_val va) ")
    prefer 3
    apply (clarsimp simp:  mmu_write_size_tlb_state_ext_def mmu_translate_tlb_state_ext_def pairsub_def split_def Let_def raise'exception_def write'mem1_eq_TLB
                    split:split_if_asm)
    apply (drule write'mem1_eq_TLB state.defs)
    apply (cases s , cases s' ; clarsimp)
   prefer 2
   apply (rule disjI1)
   apply (clarsimp simp:  mmu_write_size_tlb_state_ext_def mmu_translate_tlb_state_ext_def pairsub_def split_def Let_def raise'exception_def write'mem1_eq_TLB
                   split:split_if_asm)
  apply (cases "lookup_pde (snd (pairsub (tlb_set s) (tlb_evict (typ_tlb s)))) (ASID s) (addr_val va)")
    apply (cases " is_fault_pde (pde_walk (ASID s) (MEM s) (TTBR0 s) va)")
     apply (rule disjI1)
     apply (clarsimp simp: mmu_write_size_tlb_state_ext_def mmu_translate_tlb_state_ext_def split_def Let_def
                       raise'exception_def write'mem1_eq_TLB split:split_if_asm)
    apply (rule disjI2)
    apply (clarsimp simp: mmu_write_size_tlb_state_ext_def
                          mmu_translate_tlb_state_ext_def  Let_def pairsub_def  raise'exception_def write'mem1_eq_TLB split:split_if_asm)
    apply (drule write'mem1_eq_TLB state.defs)
    apply (cases s , cases s' ; clarsimp)
   apply (rule disjI1)
   apply (clarsimp simp: mmu_write_size_tlb_state_ext_def mmu_translate_tlb_state_ext_def split_def Let_def
  raise'exception_def write'mem1_eq_TLB split:split_if_asm)
  apply (rule disjI1)
  apply (clarsimp simp: mmu_write_size_tlb_state_ext_def mmu_translate_tlb_state_ext_def split_def Let_def
   raise'exception_def write'mem1_eq_TLB split:split_if_asm)
   apply (drule write'mem1_eq_TLB state.defs)
   apply (cases s , cases s' , clarsimp simp: pairsub_def)
  apply (metis Pair_inject pairunion.simps prod.collapse sup_bot.right_neutral)
done


lemma write'mem'det1_TLBs11:
  "\<lbrakk> mmu_write_size (val,va, sz) s = ((), s') \<rbrakk> \<Longrightarrow>
     fst(tlb_set s') = fst (pairsub (tlb_set s) (tlb_evict (typ_tlb s))) \<or>
   fst(tlb_set s') = fst (pairsub (tlb_set s) (tlb_evict (typ_tlb s))) \<union> {pt_walk (ASID s) (MEM s) (TTBR0 s) va} \<or>
     fst(tlb_set s') = fst (pairsub (tlb_set s) (tlb_evict (typ_tlb s))) \<union>  (\<lambda>x. pde_tlb_entry x (MEM s) va) ` {x. lookup_pde (snd (pairsub (tlb_set s) (tlb_evict (typ_tlb s)))) (ASID s) (addr_val va) = Hit_pde x }"
  apply (cases "lookup (fst (pairsub (tlb_set s) (tlb_evict (typ_tlb s)))) (ASID s) (addr_val va) ")
    prefer 3
    apply (clarsimp simp:  mmu_write_size_tlb_state_ext_def mmu_translate_tlb_state_ext_def split_def pairsub_def Let_def raise'exception_def write'mem1_eq_TLB
                    split:split_if_asm)
    apply (drule write'mem1_eq_TLB state.defs)
    apply (cases s , cases s' ; clarsimp)
   prefer 2
   apply (rule disjI1)
   apply (clarsimp simp:  mmu_write_size_tlb_state_ext_def mmu_translate_tlb_state_ext_def split_def pairsub_def Let_def raise'exception_def write'mem1_eq_TLB
                   split:split_if_asm)
  apply (cases "lookup_pde (snd (pairsub (tlb_set s) (tlb_evict (typ_tlb s)))) (ASID s) (addr_val va)")
    apply (cases " is_fault_pde (pde_walk (ASID s) (MEM s) (TTBR0 s) va)")
     apply (rule disjI1)
     apply (clarsimp simp: mmu_write_size_tlb_state_ext_def mmu_translate_tlb_state_ext_def split_def Let_def
                    raise'exception_def write'mem1_eq_TLB split:split_if_asm)
    apply (cases " is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) va)")
     apply (rule disjI1)
     apply (clarsimp simp: mmu_write_size_tlb_state_ext_def mmu_translate_tlb_state_ext_def pairsub_def split_def Let_def
      raise'exception_def write'mem1_eq_TLB  split:split_if_asm)

    apply (rule disjI2) apply (rule disjI1)
    apply (clarsimp simp: mmu_write_size_tlb_state_ext_def mmu_translate_tlb_state_ext_def split_def Let_def raise'exception_def
     split:split_if_asm)
     apply (drule write'mem1_eq_TLB state.defs)
     apply (cases s , cases s' ; clarsimp simp: pairsub_def)
    apply (cases s , cases s' ; clarsimp simp: pairsub_def)
   apply (rule disjI1)
   apply (clarsimp simp:  mmu_write_size_tlb_state_ext_def mmu_translate_tlb_state_ext_def split_def Let_def raise'exception_def write'mem1_eq_TLB
  split:split_if_asm)
  apply (case_tac "is_fault_pde x3")
   apply (rule disjI1)
   apply (clarsimp simp:  mmu_write_size_tlb_state_ext_def mmu_translate_tlb_state_ext_def split_def Let_def raise'exception_def write'mem1_eq_TLB
  split:split_if_asm)
  apply (case_tac "is_fault (pde_tlb_entry x3 (MEM s) va)")
   apply (rule disjI1)
   apply (clarsimp simp:  mmu_write_size_tlb_state_ext_def mmu_translate_tlb_state_ext_def split_def Let_def raise'exception_def write'mem1_eq_TLB
  split:split_if_asm)
  apply (rule disjI2) apply (rule disjI2)
 
  
  apply (clarsimp simp:  mmu_write_size_tlb_state_ext_def mmu_translate_tlb_state_ext_def split_def Let_def  pairsub_def raise'exception_def write'mem1_eq_TLB
   split:split_if_asm)
   apply (drule write'mem1_eq_TLB state.defs)
   apply (cases s , cases s' ; clarsimp simp: fst_def)
done

lemma leq_lookup_pde:
  "Hit_pde xa \<le> PED_Cache.lookup_pde (snd (tlb_set s)) (ASID s) (addr_val va) \<Longrightarrow>
   Hit_pde xa = PED_Cache.lookup_pde (snd (tlb_set s)) (ASID s) (addr_val va) \<or> lookup_pde (snd (tlb_set s)) (ASID s) (addr_val va) = Incon_pde"
using less_eq_lookup_pde_type by auto



lemma tlb_rel_write11:
  "\<lbrakk> mmu_write_size (val,va, sz) s = ((), s'); tlb_rel_sat (typ_tlb s) (typ_sat_tlb t) ; consistent' (typ_sat_tlb t) va ;
  mmu_write_size (val,va, sz) t = ((), t') \<rbrakk> \<Longrightarrow> fst (tlb_set s') \<subseteq> fst(tlb_sat_set t') \<and>
  snd (tlb_set s') \<subseteq> snd (tlb_sat_set t')"
  apply (rule conjI)
   apply (frule tlb_rel_satD)
   apply (subgoal_tac "lookup (fst (pairsub (tlb_set s) (tlb_evict (typ_tlb s)))) (ASID s) (addr_val va) \<le>
    lookup (fst (tlb_sat_set t) \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s))) (ASID s) (addr_val va)")
    prefer 2
    apply (clarsimp simp: saturated_def sup.absorb1 tlb_mono pairsub_def tlb_rel_sat_def)
    
   apply (frule write'mem'det1_TLBs11)
   apply (frule write'mem'sat_TLBs1)
   apply (erule disjE)
    apply (clarsimp simp: typ_tlb_def typ_sat_tlb_def pairsub_def state.defs)
    apply blast
   apply (erule_tac P = "fst (tlb_set s') = fst (pairsub (tlb_set s) (tlb_evict (typ_tlb s))) \<union> {pt_walk (ASID s) (MEM s) (TTBR0 s) va} " in disjE)
    apply (clarsimp simp: tlb_rel_sat_def pairsub_def) apply blast
   apply clarsimp
   apply (rule conjI)
   apply (clarsimp simp: tlb_rel_sat_def pairsub_def saturated_def) apply blast
   apply (clarsimp simp: )
   apply (subgoal_tac "xa = pde_walk (ASID s) (MEM s) (TTBR0 s) va")
    apply (clarsimp simp: awesome) apply blast

   apply (subgoal_tac "lookup_pde (snd (pairsub (tlb_set s) (tlb_evict (typ_tlb s)))) (ASID s) (addr_val va) \<le> lookup_pde (snd(tlb_set s)) (ASID s) (addr_val va)")
    prefer 2
    apply (subgoal_tac "(snd (pairsub (tlb_set s) (tlb_evict (typ_tlb s)))) \<subseteq> snd (tlb_set s)")
     apply (drule_tac t = "(snd (pairsub (tlb_set s) (tlb_evict (typ_tlb s))))" and a = "(ASID s)" and v = "(addr_val va)" in  tlb_pde_mono)   apply (simp add:  tlb_rel_sat_def)
    apply (simp add:  pairsub_def) apply blast

   apply (clarsimp simp:  tlb_rel_sat_def)
   apply (drule leq_lookup_pde) apply (erule_tac P = "Hit_pde xa = PED_Cache.lookup_pde (snd (tlb_set s)) (ASID s) (addr_val va)" in disjE)
    prefer 2
    apply (clarsimp simp: consistent0'_def)
    apply (subgoal_tac "lookup_pde (snd (tlb_set s)) (ASID s) (addr_val va) \<le> lookup_pde (snd(tlb_sat_set t)) (ASID s) (addr_val va)")
     apply simp
    apply (drule_tac a = "(ASID s)" and v = "addr_val va"  in tlb_pde_mono) apply clarsimp
   apply clarsimp
   apply (subgoal_tac "lookup_pde (snd (tlb_set s)) (ASID s) (addr_val va) \<le> lookup_pde (snd(tlb_sat_set t)) (ASID s) (addr_val va)")
    apply (clarsimp simp: consistent0'_def)
    apply (erule_tac P = " PED_Cache.lookup_pde (snd (tlb_sat_set t)) (ASID s) (addr_val va) = Miss_pde" in disjE)   apply simp
    apply (metis Hits_pde_le)
   apply (drule_tac a = "(ASID s)" and v = "addr_val va"  in tlb_pde_mono) apply clarsimp  apply (frule tlb_rel_satD)
  apply (subgoal_tac "lookup_pde (snd(tlb_set s)) (ASID s) (addr_val va) \<le> lookup_pde (snd(tlb_sat_set t) \<union> range (pde_walk (ASID s) (MEM s) (TTBR0 s))) (ASID s) (addr_val va)")
   prefer 2
   apply (simp add: saturated_def sup.absorb1 tlb_pde_mono tlb_rel_sat_def)
  apply (frule write'mem'_TLBs_pde)
  apply (frule write'mem'sat_TLBs_pde)

  apply (erule disjE)
   apply (clarsimp simp: typ_det_tlb_def typ_sat_tlb_def pairsub_def state.defs)
   apply blast
  apply (erule disjE)
   apply (clarsimp simp: typ_det_tlb_def typ_sat_tlb_def pairsub_def state.defs)
   apply blast

  using pairsub_def  apply auto
done


lemma mmu_translate_sat_pa:
  "\<lbrakk> mmu_translate va s = (pa, s'); consistent' (typ_sat_tlb t) va; tlb_rel_sat (typ_tlb s) (typ_sat_tlb t) ;
  mmu_translate va t = (pa', t')  \<rbrakk> \<Longrightarrow> pa = pa'"
  apply (drule_tac t = t in  mmu_translate_sat_refine_non_det ; clarsimp)
done


lemma write_mem_sat_MEM11:
  "\<lbrakk> mmu_write_size (val,va, sz) s = ((), s');  tlb_rel_sat (typ_tlb s) (typ_sat_tlb t) ; consistent' (typ_sat_tlb t) va; 
       mmu_write_size (val,va, sz) t = ((), t') \<rbrakk> \<Longrightarrow> MEM s' = MEM t'"
  apply (frule tlb_rel_satD)
  apply (clarsimp simp:  mmu_write_size_tlb_state_ext_def , cases "mmu_translate va s" , clarsimp)
  apply (clarsimp simp:  mmu_write_size_tlb_sat_state_ext_def , cases "mmu_translate va t" , clarsimp)
thm mmu_translate_sat_refine_non_det
  apply (frule_tac s = s and t = t and s' = b  and pa = a  in 
      mmu_translate_sat_refine_non_det ; clarsimp)
apply (subgoal_tac " exception b =  exception ba")
prefer 2
   apply (clarsimp simp: tlb_rel_sat_def state.defs)
    apply (clarsimp split: split_if_asm)
  apply (case_tac "write'mem1 (val, a, sz) ba" ; clarsimp simp: Let_def  )

apply (subgoal_tac " MEM b = MEM ba")
  using write_same_mem apply blast
 apply (clarsimp simp: tlb_rel_sat_def state.defs)
apply (frule_tac s = s and t = t and s' = s' and t' = t' and p = a  in 
      mmu_translate_mem_excep1 ; clarsimp)
done



lemma  write'mem'_rel1:
  "\<lbrakk>mmu_write_size (val,va, sz) s = ((), s')\<rbrakk>   \<Longrightarrow> 
      s' = s \<lparr> tlb_set := tlb_set s' , MEM:= MEM s' , exception:= exception s' \<rparr>"
  apply (clarsimp simp:  mmu_write_size_tlb_state_ext_def Let_def)
  apply (cases "mmu_translate va s")
  apply (clarsimp split: split_if_asm)
   apply (drule write'mem1_rel)
   apply (cases "mmu_translate va s" , clarsimp)
   apply (drule mmu_rel)
   apply (cases s, cases s', case_tac b)
   apply clarsimp
  apply (clarsimp simp: mmu_translate_tlb_state_ext_def Let_def)
  apply (cases "lookup (fst (pairsub (tlb_set s) (tlb_evict (typ_tlb s)))) (ASID s) (addr_val va)" ; clarsimp)
  apply ( cases "PED_Cache.lookup_pde (snd (pairsub (tlb_set s) (tlb_evict (typ_tlb s)))) (ASID s) (addr_val va)" ; clarsimp simp: Let_def)
   apply (clarsimp simp: Let_def raise'exception_def split:split_if_asm)+ 
done




lemma tlb_rel_2'11:
  "\<lbrakk>mmu_write_size (val,va, sz) s = ((), s'); tlb_rel_sat (typ_tlb s) (typ_sat_tlb t) ; consistent' (typ_sat_tlb t) va;
  mmu_write_size (val,va, sz) t = ((), t')\<rbrakk> \<Longrightarrow> state.truncate t' = state.truncate s'"
apply (frule (3) write_mem_sat_MEM11)
  apply (frule tlb_rel_satD, clarsimp)
  apply (frule write'mem'_rel1)
  apply (rotate_tac)
  apply (frule write'mem'sat_rel1)
  apply (clarsimp simp: tlb_rel_sat_def)
  apply (subgoal_tac "exception s' = exception t'")
   apply (cases s, cases t, cases s' , cases t')
   apply (clarsimp simp: state.defs tlb_sat_state.defs)
  apply (clarsimp simp: mmu_write_size_tlb_sat_state_ext_def mmu_write_size_tlb_state_ext_def Let_def)
  apply (case_tac "mmu_translate va t" , case_tac "write'mem1 (val, a, sz) b" , clarsimp)
  apply (case_tac "mmu_translate va s" , clarsimp)
  apply (subgoal_tac "exception b = exception bb \<and> a = aa")
   apply (clarsimp simp: Let_def split: split_if_asm)
   apply (subgoal_tac "MEM b = MEM bb ")
    apply (frule_tac s="bb" and s'="s'" and t = b and t' = ba in write_same_mem_excep ; clarsimp)
   apply (frule_tac s="s" and s'="bb" and t = t and t' = b in mmu_translate_mem_excep1 ; clarsimp simp: consistent0'_def tlb_rel_sat_def)
  apply (rule conjI)
   prefer 2
   apply (frule_tac  s =s and t = t and s' = bb and t' = b and pa' = a in  mmu_translate_sat_pa ;clarsimp simp: tlb_rel_sat_def)
  apply (frule_tac s = "s" and s' = "bb" and t = "t" and t' = "b" in   mmu_translate_excep1 ;
  clarsimp simp: tlb_rel_sat_def)
  apply (frule_tac  s =s and t = t and s' = bb and t' = b and pa' = a in  mmu_translate_sat_pa ;clarsimp simp: tlb_rel_sat_def)
done


find_theorems name: "_pa"  "mmu_translate"


lemma write'mem'_sat_refine1:
  "\<lbrakk> mmu_write_size (val,va, sz) s = ((), s'); tlb_rel_sat (typ_tlb s) (typ_sat_tlb t) ; consistent' (typ_sat_tlb t) va;
        mmu_write_size (val,va, sz) t = ((), t') \<rbrakk> \<Longrightarrow> tlb_rel_sat (typ_tlb s') (typ_sat_tlb t')"
  apply (clarsimp simp: tlb_rel_sat_def)
  apply (clarsimp simp:  write_size_saturated)
  apply (rule conjI)                              
   prefer 2
   apply (frule_tac s="s" and s'="s'" and t="t" and t'="t'" in tlb_rel_write11; clarsimp simp: tlb_rel_sat_def)
  apply (frule_tac s="s" and s'="s'" and t="t" and t'="t'" in tlb_rel_2'11; clarsimp simp: tlb_rel_sat_def)
  done




(* sat sat refine *)


lemma write'mem'sat'_TLBs1:
  "\<lbrakk>mmu_write_size (val,va, sz) s = ((), s') \<rbrakk> \<Longrightarrow>
     tlb_sat_set' s' = tlb_sat_set' s \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s)) \<or>
     tlb_sat_set' s' = tlb_sat_set' s \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s)) \<union> range (pt_walk (ASID s') (MEM s') (TTBR0 s'))"
  apply (cases "exception (snd (mmu_translate va s)) \<noteq> NoException")
   apply (rule disjI1)
   apply (clarsimp simp: mmu_write_size_tlb_sat_state'_ext_def Let_def split_def)
   apply (metis mmu_translate_sat_TLB_union prod.collapse)
  apply (clarsimp simp: mmu_write_size_tlb_sat_state'_ext_def Let_def split_def)
  apply (subgoal_tac "tlb_sat_set' (snd (write'mem1 (val, fst (mmu_translate va s), sz) (snd (mmu_translate va s)))) = tlb_sat_set' (snd (mmu_translate va s))")
   apply (subgoal_tac "tlb_sat_set' (snd (mmu_translate va s)) = tlb_sat_set' s \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s))")
    apply (subgoal_tac "ASID (snd (write'mem1 (val, fst (mmu_translate va s), sz) (snd (mmu_translate va s)))) = ASID s \<and>
                        TTBR0 (snd (write'mem1 (val, fst (mmu_translate va s), sz) (snd (mmu_translate va s)))) = TTBR0 s")
     apply clarsimp
    apply (clarsimp simp: snd_def fst_def)
    apply (case_tac " mmu_translate va s" , clarsimp)
    apply (case_tac "write'mem1 (val, a, sz) b" , clarsimp)
    apply (subgoal_tac "ASID b = ASID s \<and> TTBR0 b = TTBR0 s")
     apply (clarsimp simp: write'mem1_eq_ASID_TTBR0)
    apply (clarsimp simp: mmu_sat_eq_ASID_TTBR0_MEM)
   apply (clarsimp simp: snd_def)
   apply (case_tac " mmu_translate va s" , clarsimp)
   apply (clarsimp simp: mmu_translate_sat_TLB_union)
  apply (clarsimp simp: snd_def fst_def)
  apply (cases "mmu_translate va s" , clarsimp)
  apply (case_tac "write'mem1 (val, a, sz) b" , clarsimp)
  apply (drule write'mem1_eq_TLB)
  apply (case_tac ba , case_tac b ; clarsimp)
done

lemma write_sat_subset_tlbs:
  " \<lbrakk> mmu_write_size (val,va, sz) s = ((), s'); tlb_rel_sat' (typ_sat_tlb s) (typ_sat_tlb' t) ; consistent'' (typ_sat_tlb' t) va ;
  mmu_write_size (val,va, sz) t = ((), t') \<rbrakk> \<Longrightarrow> fst (tlb_sat_set s') \<subseteq> tlb_sat_set' t'"
  apply (frule tlb_rel_satD'; simp)
  apply (simp add: mmu_write_size_tlb_sat_state_ext_def mmu_write_size_tlb_sat_state'_ext_def Let_def)
  apply (cases " mmu_translate va s" , cases " mmu_translate va t" ; simp)
  apply (frule_tac t = t in sat_sat_refine ; simp add: tlb_rel_sat'_def)
  apply (subgoal_tac " exception b =  exception ba")
   prefer 2
   apply (clarsimp simp: state.defs)
   apply (simp split:split_if_asm)
  apply (case_tac "write'mem1 (val, a, sz) ba", case_tac "write'mem1 (val, a, sz) b" ;  simp add: Let_def)
  apply (subgoal_tac "tlb_sat_set' t' = tlb_sat_set' t \<union>  range (pt_walk (ASID s) (MEM bb) (TTBR0 s))")
 apply (subgoal_tac "fst(tlb_sat_set s') = fst(tlb_sat_set s) \<union>  range (pt_walk (ASID s) (MEM bc) (TTBR0 s))")
  apply simp
  apply (subgoal_tac "MEM bc = MEM bb")
  apply ( simp add: tlb_rel_sat'_def ) apply blast 
apply (metis mmu_sat_eq_ASID_TTBR0_MEM mmu_sat_eq_ASID_TTBR0_MEM' write_same_mem)
  apply (clarsimp simp:   fst_union_tlb') 
  apply (subgoal_tac "fst (tlb_sat_set b) = fst (tlb_sat_set s)")
  apply simp
  apply (clarsimp simp: mmu_translate_tlb_sat_state_ext_def Let_def   fst_union_tlb saturated_def)
  apply (case_tac "lookup (fst (tlb_sat_set s) \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s))) (ASID s) (addr_val va)" ;
       clarsimp simp: raise'exception_def Let_def split:split_if_asm)
   apply (simp add: fst_union_tlb sup.absorb1)

  apply (clarsimp simp: mmu_translate_tlb_sat_state'_ext_def Let_def  saturated'_def)
  apply (case_tac "lookup (tlb_sat_set' t \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s))) (ASID s) (addr_val va) " ;
       clarsimp simp: raise'exception_def Let_def split:split_if_asm)
   apply blast
done
  

lemma ok1:
  "\<lbrakk>mmu_write_size (val,va, sz) s = ((), s'); tlb_rel_sat' (typ_sat_tlb s) (typ_sat_tlb' t) ; consistent'' (typ_sat_tlb' t) va;
  mmu_write_size (val,va, sz) t = ((), t')\<rbrakk> \<Longrightarrow> state.truncate t' = state.truncate s'"
  apply (frule tlb_rel_satD'; simp)
  apply (simp add: mmu_write_size_tlb_sat_state_ext_def mmu_write_size_tlb_sat_state'_ext_def Let_def)
  apply (cases " mmu_translate va s" , cases " mmu_translate va t" ; simp)
  apply (frule_tac t = t in sat_sat_refine ; simp add: tlb_rel_sat'_def)
  apply (subgoal_tac " exception b =  exception ba")
   prefer 2
   apply (clarsimp simp: state.defs)
   apply (simp split:split_if_asm)
  apply (case_tac "write'mem1 (val, a, sz) ba", case_tac "write'mem1 (val, a, sz) b" ;  simp add: Let_def)
  apply clarsimp
   
apply (subgoal_tac " state.truncate bb = state.truncate bc")
  apply (case_tac bb, case_tac bc) apply (clarsimp simp: state.defs)
apply (clarsimp simp:write'mem1_def)
  apply (clarsimp split: split_if_asm)
  apply (clarsimp simp: Let_def)
  apply (clarsimp simp: state.defs)
 apply (clarsimp simp: state.defs)
 apply (clarsimp simp: state.defs)
 apply (clarsimp simp: state.defs)
  apply (clarsimp simp: raise'exception_def state.defs split: split_if_asm)
done


lemma mmu_translate_sat_sat:
  "mmu_translate v s = (p,t) \<Longrightarrow>  saturated' (typ_sat_tlb' t)"
  apply (clarsimp simp: mmu_translate_tlb_sat_state'_ext_def Let_def)
  apply (cases "lookup (tlb_sat_set' s \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s))) (ASID s) (addr_val v)")
    apply (clarsimp simp: saturated'_def raise'exception_def split:split_if_asm)+
done

lemma write_size_saturated':
  "\<lbrakk>mmu_write_size (val,va,sz) s = ((), t)  \<rbrakk>  \<Longrightarrow> saturated' (typ_sat_tlb' t)"
 apply (clarsimp simp: mmu_write_size_tlb_sat_state'_ext_def split_def Let_def)
  apply (clarsimp split: split_if_asm)
   apply (clarsimp simp: split_def)
   apply (subgoal_tac "ASID s = ASID (snd (write'mem1 (val, fst (mmu_translate va s), sz) (snd (mmu_translate va s)))) \<and>
                        TTBR0 s = TTBR0 (snd (write'mem1 (val, fst (mmu_translate va s), sz) (snd (mmu_translate va s)))) ")
    apply (clarsimp simp: saturated'_def)
   apply (subgoal_tac "ASID s = ASID (snd(mmu_translate va s)) \<and> TTBR0 s = TTBR0 (snd(mmu_translate va s))")
    apply (clarsimp simp:  write'mem1_def Let_def raise'exception_def)
   apply (clarsimp simp: mmu_translate_tlb_sat_state'_ext_def Let_def raise'exception_def split:lookup_type.splits)
  using mmu_translate_sat_sat surjective_pairing by blast
  


lemma write'mem'_sat_sat_refine:
  "\<lbrakk> mmu_write_size (val,va, sz) s = ((), s'); tlb_rel_sat' (typ_sat_tlb s) (typ_sat_tlb' t) ; consistent'' (typ_sat_tlb' t) va;
        mmu_write_size (val,va, sz) t = ((), t') \<rbrakk> \<Longrightarrow> tlb_rel_sat' (typ_sat_tlb s') (typ_sat_tlb' t')"
  apply (clarsimp simp: tlb_rel_sat'_def  write_size_saturated write_size_saturated')
  apply (rule conjI) prefer 2
  apply (frule_tac s="s" and s'="s'" and t="t" and t'="t'" in write_sat_subset_tlbs; clarsimp simp: tlb_rel_sat'_def)
   apply (frule_tac s="s" and s'="s'" and t="t" and t'="t'" in ok1; clarsimp simp: tlb_rel_sat'_def)  
done


lemma mmu_translate_sat_abs_refine_pa:
  "\<lbrakk>mmu_translate va s = (pa, s');  mmu_translate va t = (pa', t') ;
      saturated' (typ_sat_tlb' s); (ASID t, addr_val va) \<notin> (tlb_incon_set t) ; tlb_rel_abs (typ_sat_tlb' s) (typ_incon t) \<rbrakk> \<Longrightarrow>  pa = pa'"
  apply (frule_tac s = s in tlb_rel_abs_consistent ; clarsimp )
  apply (frule tlb_rel_absD , clarsimp)
  apply (frule_tac mmu_translate_sa_consistent ; clarsimp simp: tlb_rel_abs_def)
  apply (subgoal_tac "tlb_sat_set' s' = tlb_sat_set' s \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s)) \<and> ASID s' = ASID s
                      \<and> MEM s' = MEM s \<and> TTBR0 s' = TTBR0 s")
   apply (clarsimp simp: mmu_translate_tlb_sat_state'_ext_def split_def Let_def)
   apply (cases "lookup (tlb_sat_set' s \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s))) (ASID s) (addr_val va)")
     apply (metis (no_types, lifting) saturated_not_miss tlb_sat_more' typ_sat_prim_parameter')
    apply (clarsimp simp: consistent0''_def)
   apply clarsimp
   apply (clarsimp simp: mmu_translate_tlb_incon_state_ext_def Let_def)
   apply (subgoal_tac "x3 = pt_walk (ASID s) (MEM s) (TTBR0 s) va")
    apply (clarsimp simp: raise'exception_def split:split_if_asm)
   apply (clarsimp simp: consistent0''_def)
  apply (clarsimp simp: mmu_translate_sat_TLB_union mmu_sat_eq_ASID_TTBR0_MEM)
done



lemma write_mem_state_trun_equal:
  "\<lbrakk>  write'mem1 (val, pa, sz) s = ((), s'); write'mem1 (val, pa, sz) t = ((), t'); 
     state.truncate s = state.truncate t \<rbrakk>  \<Longrightarrow> state.truncate s' = state.truncate t'"
  apply (frule write'mem1_rel)
  apply rotate_tac
  apply (frule write'mem1_rel)
  apply (subgoal_tac "MEM s' = MEM t' \<and> exception s' = exception t'")
   apply clarsimp
   apply (cases s, cases t, cases s', cases t', clarsimp simp: state.defs)
  apply (cases s, cases t, cases s', cases t', clarsimp simp: state.defs)
  apply (clarsimp simp: write'mem1_def Let_def state.defs raise'exception_def split:split_if_asm)
done



lemma  union_incon_cases1:
  "lookup (t1 \<union> t2) a va = Incon \<Longrightarrow> 
      (lookup t1 a va = Incon \<and> lookup t2 a va = Incon)                       \<or>
      ((\<exists>x\<in>t1. lookup t1 a va = Hit x)  \<and> (\<exists>x\<in>t2. lookup t2 a va = Hit x) \<and>  lookup t1 a va \<noteq>  lookup t2 a va)    \<or>
      (lookup t2 a va = Incon \<and> (\<exists>x\<in>t1. lookup t1 a va = Hit x) )             \<or>
      ((\<exists>x\<in>t2. lookup t2 a va = Hit x)  \<and> lookup t1 a va = Incon)             \<or>
      (lookup t1 a va = Miss \<and> lookup t2 a va = Incon)                        \<or>
      (lookup t1 a va = Incon \<and> lookup t2 a va = Miss) "
  apply (clarsimp simp: lookup_def entry_set_def split: split_if_asm)
  apply auto
   apply force+
done


lemma entry_set_hit_pt_walk1:
  "\<lbrakk>entry_set (tlb_sat_set' s) (ASID s) va = {x} ; saturated' (typ_sat_tlb' s)\<rbrakk> \<Longrightarrow>
       x = pt_walk (ASID s) (MEM s) (TTBR0 s) (Addr va)"
  apply (clarsimp simp: saturated'_def)

done






lemma lookup_range_pt_walk_not_incon:
  "lookup (range (pt_walk asid mem ttbr0)) asid va \<noteq> Incon"
  by (clarsimp simp: lookup_range_pt_walk_hit)


lemma sat_state_lookup_not_miss1:
  "saturated' (typ_sat_tlb' s) \<Longrightarrow>   \<forall>va. lookup (tlb_sat_set' s) (ASID s) va \<noteq> Miss"
  apply (clarsimp simp: saturated'_def)
  apply (clarsimp simp: lookup_def split:split_if_asm)
  apply (subgoal_tac "pt_walk (ASID s) (MEM s) (TTBR0 s) (Addr va) \<in>  range (pt_walk (ASID s) (MEM s) (TTBR0 s))")
   prefer 2
   apply simp
  apply (subgoal_tac "pt_walk (ASID s) (MEM s) (TTBR0 s) (Addr va) \<in> tlb_sat_set' s")
   prefer 2
   apply fastforce
  apply (subgoal_tac "va \<in> entry_range (pt_walk (ASID s) (MEM s) (TTBR0 s) (Addr va) )")
   prefer 2
   apply (clarsimp)
  apply (subgoal_tac "entry_set (tlb_sat_set' s) (ASID s) va \<noteq> {}" , simp)
  using entry_set_def entry_range_asid_tags_def apply force
done


lemma asid_entry_set_pt_walk1 [simp]:
  "asid_entry ` (pt_walk asid m ttbr0 `UNIV) = {asid}"
  by force

 

lemma asid_lookup_miss:
  "\<lbrakk>asid_entry ` tlb = aset ; a \<notin> aset \<rbrakk> \<Longrightarrow> lookup tlb a va = Miss "
  using lookup_def entry_set_def entry_range_asid_tags_def by fastforce

  

lemma asid_unequal_miss:
  " a \<noteq> ASID b \<Longrightarrow>
   lookup (range (pt_walk (ASID b) (MEM bc) (TTBR0 b))) a bb = Miss"
  apply (subgoal_tac "asid_entry ` ((pt_walk (ASID b) (MEM bc) (TTBR0 b)) `UNIV) = {ASID b}")
   prefer 2
   apply fastforce
   using asid_lookup_miss by force


lemma write_asid_incon_set_rel:
  "\<lbrakk> saturated' (typ_sat_tlb' b) ; asid_va_incon (tlb_sat_set' b) \<subseteq> tlb_incon_set ba \<rbrakk> \<Longrightarrow>
    asid_va_incon (tlb_sat_set' b \<union> range (pt_walk (ASID b) (MEM bc) (TTBR0 b)))
           \<subseteq> tlb_incon_set ba \<union> ptable_comp (ASID b) (MEM b) (MEM bc) (TTBR0 b)"
  apply (clarsimp simp: asid_va_incon_def ptable_comp_def)
  apply (case_tac "a = ASID b" , clarsimp)
   apply (subgoal_tac "pt_walk (ASID b) (MEM b) (TTBR0 b) (Addr bb) =
    pt_walk (ASID b) (MEM bc) (TTBR0 b) (Addr bb)")
    prefer 2
    apply force
   apply (subgoal_tac "(ASID b, bb) \<in> {(asid, va). lookup (tlb_sat_set' b) asid va = Incon}")
    apply blast
   apply (subgoal_tac "lookup (tlb_sat_set' b) (ASID b) bb = Incon" , clarsimp)
   apply (drule union_incon_cases1 , clarsimp)
   apply (erule disjE , clarsimp)
   apply (erule disjE , clarsimp)
    apply (clarsimp simp: lookup_def split:split_if_asm)
    apply (drule_tac s = b and va = bb and x = x in entry_set_hit_pt_walk1 , clarsimp)
    apply (subgoal_tac "(ASID b , bb) \<in> entry_range_asid_tags (pt_walk (ASID b) (MEM bc) (TTBR0 b) xa)")
     prefer 2
     apply (clarsimp simp: entry_set_hit_entry_range)
    apply (drule va_entry_set_pt_palk_same , clarsimp)
   apply (erule disjE , clarsimp simp: lookup_range_pt_walk_not_incon )
   apply (erule disjE , force)
   apply (erule disjE)
    apply (drule_tac sat_state_lookup_not_miss1 , clarsimp)
   apply force
  apply (drule union_incon_cases1)
  apply (erule disjE , force)
  apply (erule disjE)
   apply (drule_tac bb = bb and bc = bc in asid_unequal_miss , clarsimp)
  apply (erule disjE)
   apply (drule_tac bb = bb and bc = bc in asid_unequal_miss , clarsimp)
  apply (erule disjE , force)
  apply (erule disjE)
   apply (drule_tac bb = bb and bc = bc in asid_unequal_miss , clarsimp)
  apply force
done



lemma write_refinement_saturated_incon_only:        
  "\<lbrakk> mmu_write_size (val,va, sz) s = ((), s'); (ASID t, addr_val va) \<notin> (tlb_incon_set t); saturated' (typ_sat_tlb' s);
         tlb_rel_abs (typ_sat_tlb' s) (typ_incon t) ;  mmu_write_size (val,va, sz) t = ((), t') \<rbrakk> \<Longrightarrow> 
         tlb_rel_abs (typ_sat_tlb' s') (typ_incon t')"
  apply (frule_tac s = s in tlb_rel_abs_consistent ; clarsimp)
  apply (frule_tac tlb_rel_absD , clarsimp)
  apply (clarsimp simp:  mmu_write_size_tlb_sat_state'_ext_def  mmu_write_size_tlb_incon_state_ext_def)
  apply (cases "mmu_translate va s" ,cases "mmu_translate va t" , clarsimp)
  apply (frule_tac t=t and pa'= aa and t' = ba in  mmu_translate_sat_abs_refine) apply clarsimp+
  apply (frule_tac t=t and pa'= aa and t' = ba in  mmu_translate_sat_abs_refine_pa) apply clarsimp+
  apply (clarsimp simp: tlb_rel_abs_def)
  apply (subgoal_tac "exception b = exception ba")
   prefer 2 apply (case_tac b , case_tac ba , clarsimp simp: state.defs)
  apply (clarsimp split: split_if_asm)
  apply (case_tac "write'mem1 (val, aa, sz) b " , case_tac "write'mem1 (val, aa, sz) ba" , clarsimp)
  apply (subgoal_tac "state.truncate bb = state.truncate bc")
   prefer 2 using write_mem_state_trun_equal apply blast
  apply (rule conjI , clarsimp simp: state.defs)
  apply (subgoal_tac "MEM bb = MEM bc  \<and> MEM s = MEM b" , simp)
   apply (subgoal_tac "ASID s = ASID b \<and> TTBR0 s = TTBR0 b" , simp)
    apply (subgoal_tac "saturated' (typ_sat_tlb' b)")
     prefer 2
     using mmu_translate_sat_sat apply blast
    apply (drule_tac b = b and ba = ba and bc = bc in write_asid_incon_set_rel) apply clarsimp+
   using mmu_sat_eq_ASID_TTBR0_MEM apply blast
  apply (rule conjI)
   apply (clarsimp simp: state.defs)
  using mmu_sat_eq_ASID_TTBR0_MEM by blast

find_theorems name:"refine" "mmu_translate"



thm lookup_range_pt_walk_hit


(* important theorems *)

thm mmu_translate_det_refine         (* with no faults , deterministic/deterministic *)
    mmu_translate_det_evict_refine   (* with no faults , deterministic/non-deterministic *)
    mmu_translate_det_flt_refine     (* with faults    , deterministic/deterministic *)
    mmu_translate_flt_refine_det     (* with faults    ,  deterministic/non-deterministic *)
    mmu_translate_det_sat_refine     (* deterministic/saturated (tlb + pde) *)
    mmu_translate_sat_refine_non_det (* non-deterministic/saturated (tlb + pde) *)
    sat_sat_refine                   (* saturated (tlb + pde)/ saturate (tlb only)  *)
    mmu_translate_sat_abs_refine     (* saturated (tlb only)/ incon set  *)

    
find_theorems name: "refine" "mmu_translate" 


thm mmu_translate_det_refine         (* with no faults , deterministic/deterministic *)
    mmu_translate_det_evict_refine   (* with no faults , deterministic/non-deterministic *)
    mmu_translate_det_flt_refine     (* with faults    , deterministic/deterministic *)
    mmu_translate_flt_refine_det     (* with faults    ,  deterministic/non-deterministic *)
    mmu_translate_det_sat_refine     (* deterministic/saturated (tlb + pde) *)
    mmu_translate_sat_refine_non_det (* non-deterministic/saturated (tlb + pde) *)
    sat_sat_refine                   (* saturated (tlb + pde)/ saturate (tlb only)  *)
    mmu_translate_sat_abs_refine     (* saturated (tlb only)/ incon set  *)


find_theorems name: "refine" name: "write"

thm write'mem'det1_sat_refine1            (* deterministic/saturated (tlb + pde) *)
    write'mem'_sat_refine1                (* non-deterministic/saturated (tlb + pde) *)
    write'mem'_sat_sat_refine             (* saturated (tlb + pde)/ saturate (tlb only)  *)
    write_refinement_saturated_incon_only (* saturated (tlb only)/ incon set  *)


(* Read Relation *)


(* for saturated tlb and pde*)

lemma saturated_tlb_const [simp]:
  "saturated (typ_sat_tlb s) \<Longrightarrow>
  fst(tlb_sat_set s) \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s)) = fst(tlb_sat_set s) \<and>
   snd(tlb_sat_set s) \<union> range (pde_walk (ASID s) (MEM s) (TTBR0 s)) = snd(tlb_sat_set s)"
  by (auto simp add: saturated_def)

thm lookup_type.splits
lemma mmu_translate_sat_const_tlb [simp]:
  "saturated (typ_sat_tlb s) \<Longrightarrow> fst(tlb_sat_set (snd (mmu_translate va s))) = fst(tlb_sat_set s) \<and>
     snd(tlb_sat_set (snd (mmu_translate va s))) = snd(tlb_sat_set s)"
  apply (simp add: mmu_translate_tlb_sat_state_ext_def Let_def raise'exception_def   fst_def
              split: lookup_type.splits lookup_pde_type.splits)
using sat_state_tlb by fastforce


lemma tlb_sat_set_mem1 [simp]:
  "fst(tlb_sat_set (snd (mem1 ps s))) = fst(tlb_sat_set s) \<and>
     snd(tlb_sat_set (snd (mem1 ps s))) = snd(tlb_sat_set s)"
  by (simp add: mem1_def raise'exception_def split: option.splits)


lemma mmu_read_sat_const [simp]:
  "saturated (typ_sat_tlb s) \<Longrightarrow> fst(tlb_sat_set (snd (mmu_read_size v s))) = fst(tlb_sat_set s) \<and>
       snd(tlb_sat_set (snd (mmu_read_size v s))) = snd(tlb_sat_set s)"
   by (clarsimp simp: mmu_read_size_tlb_sat_state_ext_def split_def Let_def
                      mem_read1_def raise'exception_def
               split: split_if_asm)

lemma mmu_read_sat_const':
  "\<lbrakk> mmu_read_size (va, sz) s = (val, t); saturated (typ_sat_tlb s) \<rbrakk> \<Longrightarrow>
     fst(tlb_sat_set t) = fst(tlb_sat_set s)  \<and>  snd(tlb_sat_set t) = snd(tlb_sat_set s)"
   by (drule sndI) clarsimp




(* for saturated tlb only *)


lemma saturated'_tlb_const [simp]:
  "saturated' (typ_sat_tlb' s) \<Longrightarrow>
  tlb_sat_set' s \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s)) = tlb_sat_set' s"
  by (auto simp add: saturated'_def)


lemma mmu_translate_sat'_const_tlb [simp]:
  "saturated' (typ_sat_tlb' s) \<Longrightarrow> tlb_sat_set' (snd (mmu_translate va s)) = tlb_sat_set' s"
  by (simp add: mmu_translate_tlb_sat_state'_ext_def Let_def raise'exception_def
         split: lookup_type.splits)


lemma tlb_sat'_set_mem1 [simp]:
  "tlb_sat_set' (snd (mem1 ps s)) = tlb_sat_set' s"
  by (simp add: mem1_def raise'exception_def split: option.splits)


lemma mmu_read_sat'_const [simp]:
  "saturated' (typ_sat_tlb' s) \<Longrightarrow> tlb_sat_set' (snd (mmu_read_size v s)) = tlb_sat_set' s"
   by (clarsimp simp: mmu_read_size_tlb_sat_state'_ext_def split_def Let_def
                      mem_read1_def raise'exception_def
               split: split_if_asm)


lemma mmu_read_sat'_const':
  "\<lbrakk> mmu_read_size (va, sz) s = (val, t); saturated' (typ_sat_tlb' s) \<rbrakk> \<Longrightarrow>
     tlb_sat_set' t = tlb_sat_set' s"
   by (drule sndI) clarsimp

find_theorems "saturated" "mmu_write_size"

lemma write_read_saturated_tlb:
  "\<lbrakk> mmu_write_size (val,va,sz) s = ((), t); mmu_read_size (va, sz) t = (val, r) \<rbrakk>  \<Longrightarrow> tlb_sat_set' t = tlb_sat_set' r"
  apply (cases "\<not> ptable_trace (MEM s) (TTBR0 s) va \<subseteq> \<Union>(ptable_trace (MEM s) (TTBR0 s) ` UNIV)" )
   apply (subgoal_tac "saturated' (typ_sat_tlb' t)")
    prefer 2
    apply (clarsimp simp: write_size_saturated)
   apply (clarsimp simp: mmu_read_size_tlb_sat_state'_ext_def)
   apply (cases "mmu_translate va t" , clarsimp)
   apply (clarsimp simp:  mmu_translate_tlb_sat_state'_ext_def Let_def)
   apply (cases "lookup (tlb_sat_set' t \<union> range (pt_walk (ASID t) (MEM t) (TTBR0 t))) (ASID t) (addr_val va)")
     apply (simp only: split_if_asm raise'exception_def saturated'_def, force)+
  apply simp
  apply (subgoal_tac "saturated' (typ_sat_tlb' t)")
   prefer 2
   apply (clarsimp simp:  write_size_saturated')
  apply (clarsimp simp: mmu_read_size_tlb_sat_state'_ext_def)
  apply (cases "mmu_translate va t" , clarsimp)
  apply (subgoal_tac "saturated' (typ_sat_tlb' b)")
   prefer 2
   apply (clarsimp simp: sat_states_parameters)
  apply (subgoal_tac "tlb_sat_set' t = tlb_sat_set' b")
   apply clarsimp
   apply (drule mem1_read_exception)
   apply (case_tac b , cases r , clarsimp)
  apply (subgoal_tac "ASID t = ASID b \<and> MEM t = MEM b \<and> TTBR0 t = TTBR0 b")
   apply (clarsimp simp: saturated'_def)
   apply (subgoal_tac "tlb_sat_set' b = tlb_sat_set' t \<union> range (pt_walk (ASID b) (MEM b) (TTBR0 b))")
    apply (subgoal_tac "range (pt_walk (ASID b) (MEM b) (TTBR0 b)) \<subseteq> tlb_sat_set' t")
     apply blast
    apply blast
   apply (clarsimp simp: mmu_translate_sat_TLB_union)
  apply (clarsimp simp: mmu_translate_tlb_sat_state'_ext_def Let_def)
  apply (cases "lookup (tlb_sat_set' t \<union> range (pt_walk (ASID t) (MEM t) (TTBR0 t))) (ASID t) (addr_val va)";
                clarsimp simp : raise'exception_def split: split_if_asm)
done





 
end
