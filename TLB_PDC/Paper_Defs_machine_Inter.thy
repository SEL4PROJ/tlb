(* Additional definitions and tweaks for the paper *)

theory Paper_Defs_machine_Inter
  imports
  	"~~/src/HOL/Library/LaTeXsugar"
	 Refinement
begin


lemma pt_walk_pair_def2:
"pt_walk_pair asid heap ttbr0 v \<equiv>
      case pdc_walk asid heap ttbr0 v
       of None      \<Rightarrow> Fault           
       | Some pde   \<Rightarrow> (case pde_tlb_entry pde heap v 
                        of  None \<Rightarrow> Partial_Walk pde
                        |   Some te \<Rightarrow> Full_Walk te pde)"
  by (clarsimp simp: pt_walk_pair_def)

lemma less_eq_lookup_type1:
  "e \<le> e' \<equiv> e = Miss \<or>  e' = e  \<or> e' = Incon"
  by (smt less_eq_lookup_type)



definition
  "read_state4 \<equiv> \<lambda>(a,b,c,d). do { 
    x <- read_state a;
    y <- read_state b;
    z <- read_state c;
    z2 <- read_state d;
    return (x,y,z,z2)
  }" 

lemma read_state4_conv:
  "do {
    f;
    (x,y,z,z2) <- read_state4 (a,b,c,d);
    g x y z z2
  } = do {
    f;
    x <- read_state a;
    y <- read_state b;
    z <- read_state c;
    z2 <- read_state d;
    g x y z z2
  }"
  by (auto simp: read_state4_def)


 
definition
  "read_state2 \<equiv> \<lambda>(a,b). do { 
    x <- read_state a;
    y <- read_state b;
    return (x,y)
  }"

lemma read_state2:
  "do {
    (x,y) <- read_state2 (a,b);
    f x y
  } = do {
    x <- read_state a;
    y <- read_state b;
    f x y
  }"
  by (auto simp: read_state2_def)

lemma read_state2_conv:
  "do {
    g;
    (x,y) <- read_state2 (a,b);
    f x y
  } = do {
    g;
    x <- read_state a;
    y <- read_state b;
    f x y
  }"
  by (auto simp: read_state2_def)

definition
  "read_state3 \<equiv> \<lambda>(a,b,c). do { 
    x <- read_state a;
    y <- read_state b;
    z <- read_state c;
    return (x,y,z)
  }"

lemma read_state3:
  "do {
    (x,y,z) <- read_state3 (a,b,c);
    f x y z
  } = do {
    x <- read_state a;
    y <- read_state b;
    z <- read_state c;
    f x y z
  }"
  by (auto simp: read_state3_def)

lemma read_state3_conv:
  "do {
    g;
    (x,y,z) <- read_state3 (a,b,c);
    f x y z
  } = do {
    g;
    x <- read_state a;
    y <- read_state b;
    z <- read_state c;
    f x y z
  }"
  by (auto simp: read_state3_def)




definition
  "K_bindn'' f g \<equiv> bind f (\<lambda>_. g)"


notation (output) K_bindn'' ("do { //_;//_ }")  

definition
  "tlb_pdc_reload entry pde = update_state (\<lambda>s. s\<lparr> non_det_tlb := pairunion (non_det_tlb s)  ({entry} , {pde}) \<rparr>)"


lemma mmu_translate_tlb_state_ext_def2':
"mmu_translate v = do {
    update_state (\<lambda>s. s\<lparr> non_det_tlb := pairsub (non_det_tlb s)  (tlb_evict (typ_non_det_tlb s)) \<rparr>);
     (m, rt, a,t,p) <- read_state4 (MEM, TTBR0, ASID,non_det_tlb);
          case lookup'' t a v of 
            Incon \<Rightarrow> raise'exception (IMPLEMENTATION_DEFINED ''set on fire'') 
          |     Hit te \<Rightarrow> return (va_to_pa v  te)
          |    Miss \<Rightarrow>  (case lookup_pdc p a v of
                        Incon  \<Rightarrow> raise'exception (IMPLEMENTATION_DEFINED ''set on fire'')
                      |   Hit pde \<Rightarrow> do {  
                                        let te = pde_tlb_entry pde m v;
                                        if is_fault te 
                                        then raise'exception (PAGE_FAULT ''more info'')
                                        else 
                                        K_bindn'' (update_state (\<lambda>s. s\<lparr> non_det_tlb := pairunion (non_det_tlb s)  ({the te} , {}) \<rparr>))
                                        (return  (va_to_pa v (the te)) )
                                           }
                      |   Miss \<Rightarrow> do { 
           let walk  = pt_walk_pair a m rt v;
           case walk of Fault \<Rightarrow> raise'exception (PAGE_FAULT ''more info'')
                     |  Partial_Walk pde \<Rightarrow> K_bindn'' ( update_state (\<lambda>s. s\<lparr> non_det_tlb := pairunion (non_det_tlb s)  ({} , {pde}) \<rparr>))
                                                (raise'exception (PAGE_FAULT ''more info''))
                     |  Full_Walk te pde \<Rightarrow>  
                                              K_bindn'' (tlb_pdc_reload te pde)
                                              (return (va_to_pa v te)) 
                                              } 
                      )
         
   }"

  apply (rule ext)
  apply (clarsimp simp:mmu_translate_non_det_tlb_state_ext_def  K_bindn''_def
                      Let_def  split_def  read_state4_def
                        pt_walk_pair_def
                      raise'exception_def is_fault_def 
               split: lookup_type.splits option.splits)
  apply (simp only: pt_walk'_pt_walk)
  apply (clarsimp simp: pt_walk'_def map_opt_def)
  apply (clarsimp simp: tlb_pdc_reload_def)
  apply (subgoal_tac "pairunion ({}, {x2}) ({x2a}, {}) = ({x2a}, {x2})")
   apply (metis (no_types, hide_lams) fst_conv old.prod.exhaust pairunion.elims pairunion.simps sup_bot.right_neutral ) 
  by force

definition
  flush_tlb_pdc_vset' :: " (tlb \<times> pdc) \<Rightarrow> vaddr set \<Rightarrow> (tlb \<times> pdc)"
where
  "flush_tlb_pdc_vset' tp vset = (let tlb = fst tp ;
                                      pdc = snd tp in 
            (tlb - \<Union>((\<lambda> v. {e\<in>tlb. v \<in> range_of e}) ` vset), 
            pdc  -  \<Union>((\<lambda> v. {e\<in>pdc. v \<in> range_of e}) ` vset)))"

lemma
  "flush_tlb_pdc_vset' tp vset = flush_tlb_pdc_vset tp vset"
  by (clarsimp simp: flush_tlb_pdc_vset'_def flush_tlb_pdc_vset_def Let_def)


definition
  flush_asid_tlb_pdc :: " (tlb \<times> pdc) \<Rightarrow> asid \<Rightarrow> (tlb \<times> pdc)"
where
  "flush_asid_tlb_pdc t a = (let tlb = fst t ;
                                pdc = snd t in 
          (tlb - {e\<in>tlb. asid_of e = Some a}, pdc - {e\<in>pdc. asid_of_pdc e = Some a}))"

definition
  flush_asid_vset_tlb_pdc :: " (tlb \<times> pdc) \<Rightarrow> asid \<Rightarrow> vaddr set \<Rightarrow> (tlb \<times> pdc)"
where
  "flush_asid_vset_tlb_pdc t a vset = 
  (let tlb = fst t ;
                                pdc = snd t in 
  (tlb - (\<Union>v\<in>vset. {e\<in>tlb. v \<in> range_of e \<and> asid_of e = Some a}),
   pdc - (\<Union>v\<in>vset. {e\<in>pdc. v \<in> range_of e \<and> asid_of_pdc e = Some a})))"


definition
  "no_fault e \<equiv> \<not>is_fault e"

definition
  "consistent0''  mem ttbr0 tlb pdc asid va \<equiv>
            consistent0'  mem  asid ttbr0  tlb pdc va"





(* take saturated trans *)


definition "mmu_translate_sat v \<equiv> mmu_translate v :: ('a sat_tlb_state_scheme \<Rightarrow> _)"

definition "mmu_write_sat  \<equiv> (mmu_write_size  :: (bool list \<times> vaddr \<times> nat \<Rightarrow> 'a sat_tlb_state_scheme \<Rightarrow> unit \<times> 'a sat_tlb_state_scheme))"


definition "mmu_read_sat  \<equiv> (mmu_read_size  :: (vaddr \<times> nat \<Rightarrow> 'a sat_tlb_state_scheme \<Rightarrow> bool list \<times> 'a sat_tlb_state_scheme))"

definition
  to_tlb :: "pdc \<Rightarrow> asid \<Rightarrow>heap \<Rightarrow> ttbr0 \<Rightarrow> vaddr \<Rightarrow>  tlb_entry option set"
where
  "to_tlb  pdc asid mem rt va  = tlb_pdc_walk asid pdc mem rt va "


lemma ran_Somes:
  "ran f = Somes (range f)"
  by (force simp: ran_def Somes_def)

definition
  "pdc_tlb_refill = do {
     (m, rt, a)   <- read_state3 (MEM, TTBR0, ASID);
     let pdes = ran (pdc_walk a m rt) ;
     let tes = Somes (\<Union>v. to_tlb pdes a m rt v);
     update_state (\<lambda>s. s\<lparr> sat_tlb := pairunion (sat_tlb s) (tes , pdes)\<rparr>)
  }"



lemma ran_pdc_walk_simp':
  "  Somes (\<Union>(range (to_tlb pdes a m rt))) = 
          the ` {e. (\<exists>x. e \<in> to_tlb pdes a m rt x) \<and> no_fault e}"
  apply (clarsimp simp: Somes_def is_fault_def no_fault_def)
  by force


lemma ran_pdc_walk_simp:
  "ran (pdc_walk a m rt) =  the ` {e\<in>pdc_walk a m rt ` UNIV. no_fault e}"
  apply (clarsimp simp: ran_def no_fault_def is_fault_def)
  by force
(*
lemma
  " the ` {e. (\<exists>x. e \<in> to_tlb pdes a m rt x) \<and> no_fault e} =  ran (to_tlb pdes a m rt)"
*)
  
lemma mmu_translate_sat_def2:
"mmu_translate_sat va  = do {
    pdc_tlb_refill;
   (a,t,p) <- read_state2 (ASID,sat_tlb);
         case lookup'' t a  va of
            Hit te \<Rightarrow> return (va_to_pa va te)
          | Miss \<Rightarrow> raise'exception (PAGE_FAULT ''more info'')
          | Incon \<Rightarrow> raise'exception (IMPLEMENTATION_DEFINED ''set on fire'')
   }" 
  apply (rule ext)
  apply (simp only: pdc_tlb_refill_def ran_pdc_walk_simp ran_pdc_walk_simp')
  by (clarsimp simp: mmu_translate_sat_def mmu_translate_sat_tlb_state_ext_def read_state3_def 
                     Let_def pdc_tlb_refill_def split_def read_state2_def   to_tlb_def  no_fault_def 
               split:lookup_type.splits ) 

           

definition
  when_no_exc ("when'_no'_exc _")
where
  "(when_no_exc f) = do {
     exception \<leftarrow> read_state exception;
     if exception = NoException then f else return ()
   }"

definition
  "K_bind f g \<equiv> bind f (\<lambda>_. g)"

abbreviation (K_bind)
  K_bind2 ("do { _; _ }")
where
  "K_bind2 \<equiv> K_bind"



lemma mmu_write_sat_def2:
  "mmu_write_sat (val, va, sz) = do {
                       pa <- mmu_translate_sat va;
                       when_no_exc (K_bind (write'mem1 (val, pa, sz)) (pdc_tlb_refill))
                     }"
  apply (rule ext)
  apply (simp add: mmu_write_sat_def  when_no_exc_def mmu_translate_sat_def)
  apply (simp add: mmu_write_size_sat_tlb_state_ext_def mmu_translate_sat_def [symmetric])
  apply (case_tac "mmu_translate_sat va x"; clarsimp)
  apply (case_tac "write'mem1 (val, a, sz) b"; clarsimp simp: K_bind_def)
  apply (simp only: pdc_tlb_refill_def ran_pdc_walk_simp ran_pdc_walk_simp')
  apply (clarsimp simp:  read_state3_def Let_def  no_fault_def)
  apply (subgoal_tac "ASID x = ASID ba \<and> TTBR0 x = TTBR0 ba \<and> sat_tlb b = sat_tlb ba") 
   apply (clarsimp simp: to_tlb_def)
  by (clarsimp simp: mmu_translate_sat_def to_tlb_def
      mmu_translate_sat_tlb_state_ext_def write'mem1_def raise'exception_def Let_def 
                  split: lookup_type.splits if_split_asm)
 

lemma mmu_read_sat_def2:
 "mmu_read_sat (va, sz) = do {
                 pa \<leftarrow> mmu_translate_sat va;
                 mem_read1 (pa, sz)
               }"
  by (simp add: mmu_read_size_sat_tlb_state_ext_def mmu_read_sat_def mmu_translate_sat_def)


definition "update_TTBR0_sat  \<equiv> (update_TTBR0  :: (paddr \<Rightarrow> 'a sat_tlb_state_scheme \<Rightarrow> unit \<times> 'a sat_tlb_state_scheme))"

definition "update_ASID_sat  \<equiv> (update_ASID  :: (asid \<Rightarrow> 'a sat_tlb_state_scheme \<Rightarrow> unit \<times> 'a sat_tlb_state_scheme))"


lemma upd_ttbr0_sat_def2:
  "update_TTBR0_sat r = do {
                       (K_bind (update_state (\<lambda>s. s\<lparr> TTBR0 := r \<rparr>)) (pdc_tlb_refill))
                     }"
  apply (simp only: pdc_tlb_refill_def ran_pdc_walk_simp ran_pdc_walk_simp')
  apply (simp add: update_TTBR0_sat_def update_TTBR0_sat_tlb_state_ext_def to_tlb_def
           split_def Let_def K_bind_def no_fault_def read_state3_def  cong: if_cong)
  done  

lemma upd_asid_sat_def2:
  "update_ASID_sat a = do {
                       (K_bind (update_state (\<lambda>s. s\<lparr> ASID := a \<rparr>)) (pdc_tlb_refill))
                     }"
  apply (simp only: pdc_tlb_refill_def ran_pdc_walk_simp ran_pdc_walk_simp')
  apply (simp add: update_ASID_sat_def update_ASID_sat_tlb_state_ext_def to_tlb_def
            split_def Let_def K_bind_def no_fault_def read_state3_def cong: if_cong)
   done


definition "flush_sat  \<equiv> (flush  :: (flush_type \<Rightarrow> 'a sat_tlb_state_scheme \<Rightarrow> unit \<times> 'a sat_tlb_state_scheme))"

(* to_do  *)

lemma flush_sat_def2:
  "flush_sat f = do {
            case f of FlushTLB \<Rightarrow> update_state (\<lambda>s. s\<lparr> sat_tlb := ({}, {}) \<rparr>)             
                  | Flushvarange vset \<Rightarrow> update_state (\<lambda>s. s\<lparr> sat_tlb := flush_tlb_pdc_vset' (sat_tlb s) vset  \<rparr>)
                  |  FlushASID a \<Rightarrow>update_state (\<lambda>s. s\<lparr> sat_tlb := flush_asid_tlb_pdc (sat_tlb s) a \<rparr>)
                  | FlushASIDvarange a vset \<Rightarrow> update_state (\<lambda>s. s\<lparr> sat_tlb := flush_asid_vset_tlb_pdc (sat_tlb s) a vset \<rparr>);
              pdc_tlb_refill   
                     }"
 apply (simp only: pdc_tlb_refill_def ran_pdc_walk_simp ran_pdc_walk_simp')
  by (clarsimp simp: flush_sat_def flush_sat_tlb_state_ext_def  flush_tlb_pdc_vset_def to_tlb_def
            split_def Let_def K_bind_def flush_tlb_pdc_vset'_def  no_fault_def read_state3_def    
          flush_asid_vset_tlb_pdc_def flush_asid_tlb_pdc_def  flush_tlb_pdc_asid_def flush_tlb_pdc_a_vset_def            
    split: flush_type.splits cong: if_cong)



definition
  tlb_saturated :: "'b sat_tlb_state_scheme \<Rightarrow> bool"
where
  "tlb_saturated s  \<equiv>  ran (pt_walk (ASID s) (MEM s) (TTBR0 s)) \<subseteq> fst(sat_tlb s) "


lemma tlb_sat_simp:
  "tlb_saturated s =  (the ` {e\<in>pt_walk (ASID s) (MEM s) (TTBR0 s) ` UNIV. no_fault e} \<subseteq> fst(sat_tlb s)) "
  apply (clarsimp simp: tlb_saturated_def ran_def is_fault_def no_fault_def)
  by force


definition
  pdc_saturated :: "'b sat_tlb_state_scheme \<Rightarrow> bool"
where
  "pdc_saturated s  \<equiv> 
    ran(pdc_walk (ASID s) (MEM s) (TTBR0 s)) \<subseteq> snd(sat_tlb s)"


lemma pdc_sat_simp:
  "pdc_saturated s =  (the ` {e\<in>pdc_walk (ASID s) (MEM s) (TTBR0 s) ` UNIV. no_fault e} \<subseteq> snd(sat_tlb s)) "
  apply (clarsimp simp: pdc_saturated_def ran_def is_fault_def no_fault_def)
  by force


definition
  saturated' :: "'b sat_tlb_state_scheme \<Rightarrow> bool"
where
  "saturated' s  \<equiv> tlb_saturated s  \<and> pdc_saturated s "
 

lemma
  "saturated' s = saturated (typ_sat_tlb s)"
  by (clarsimp simp: saturated'_def saturated_def typ_sat_tlb_def state.defs   tlb_sat_simp pdc_sat_simp
    no_fault_def)

definition "mmu_write_abs  \<equiv> (mmu_write_size  :: (bool list \<times> vaddr \<times> nat \<Rightarrow> 'a set_tlb_state_scheme \<Rightarrow> unit \<times> 'a set_tlb_state_scheme))"

definition "mmu_read_abs  \<equiv> (mmu_read_size  :: (vaddr \<times> nat \<Rightarrow> 'a set_tlb_state_scheme \<Rightarrow> bool list \<times> 'a set_tlb_state_scheme))"


definition "mmu_translate_abs v \<equiv> mmu_translate v :: ('a set_tlb_state_scheme \<Rightarrow> _)"

definition "mmu_write \<equiv> mmu_write_size "

definition "mmu_read \<equiv> mmu_read_size "

definition read_state_iset :: _ where
  "read_state_iset is  = (\<lambda>s. (is(set_tlb s), s))"

definition
  "read_state4i \<equiv> \<lambda>(a,b,c,d). do { 
    x <- read_state a;
    y <- read_state b;    
  z <- read_state c;
  i <- read_state_iset d;
    return (x,y,z,i)
  }"

definition
  "read_state5i \<equiv> \<lambda>(a,b,c,d,e). do { 
    x <- read_state a;
    y <- read_state b;    
  z <- read_state c;
  i <- read_state_iset d;
 g <- read_state_iset e;
    return (x,y,z,i,g)
  }"

definition
  "read_state6i \<equiv> \<lambda>(a,b,c,d,e,f). do { 
    x <- read_state a;
    y <- read_state b;    
  z <- read_state c;
  i <- read_state_iset d;
 g <- read_state_iset e;
f' <- read_state_iset f;
    return (x,y,z,i,g,f')
  }"

definition
  "global_varange' asid mem ttbr0 \<equiv> (\<Union>e\<in>global_entries (the ` {e\<in>pt_walk asid mem ttbr0 ` UNIV. \<not>is_fault e}). range_of e)"


definition
  "global_varange asid mem ttbr0 \<equiv> (\<Union>e\<in>global_entries (ran (pt_walk asid mem ttbr0)). range_of e)"

lemma global_varange_rewrite:
  "global_varange asid mem ttbr0 = global_varange' asid mem ttbr0"
  apply (clarsimp simp: global_varange_def global_varange'_def ran_def is_fault_def no_fault_def
                        image_def global_entries_def)
  by fastforce
  
  

definition
  "update_incon_set \<equiv> \<lambda>ist. do { 
       set_tlb <- read_state set_tlb; 
         let neww  = set_tlb \<lparr>iset := ist \<rparr>;
                   update_state (\<lambda>s. s\<lparr> set_tlb :=  neww \<rparr>)
  }" 

definition
  "update_global_set \<equiv> \<lambda>ist. do { 
       set_tlb <- read_state set_tlb; 
         let neww  = set_tlb \<lparr>global_set := ist \<rparr>;
                   update_state (\<lambda>s. s\<lparr> set_tlb :=  neww \<rparr>)
  }" 

definition
  "update_snapshot \<equiv> \<lambda>ist. do { 
       set_tlb <- read_state set_tlb; 
         let neww  = set_tlb \<lparr>snapshot := ist \<rparr>;
                   update_state (\<lambda>s. s\<lparr> set_tlb :=  neww \<rparr>)
  }" 


lemma   mmu_write_set_def2:
  "mmu_write_abs (val, va, sz)  
   = do {
      m   <- read_state MEM; rt <- read_state TTBR0;  a <- read_state ASID;
      iset <- read_state_iset iset;
      gset <- read_state_iset global_set;
      pa <- mmu_translate_abs va;
      when_no_exc  do {
                   write'mem1 (val, pa, sz);
                   m' <- read_state MEM;   
                    update_incon_set (iset \<union> ptable_comp (pt_walk_pair a m rt) (pt_walk_pair a m' rt));
                   update_global_set (gset \<union> global_varange a m' rt)
            }
   }"
  apply (simp only: global_varange_rewrite)
  apply rule
  apply (clarsimp simp: mmu_write_abs_def mmu_write_size_set_tlb_state_ext_def K_bind_def 
       when_no_exc_def 
     update_incon_set_def  mmu_translate_abs_def
       update_global_set_def   read_state_iset_def global_varange'_def
   split_def Let_def incon_comp_def split: if_split_asm)
  apply (subgoal_tac " set_tlb (snd (mmu_translate va x)) = set_tlb x") prefer 2
apply (clarsimp simp: mmu_translate_set_tlb_state_ext_def Let_def raise'exception_def split: if_split_asm)
  apply clarsimp
  apply (subgoal_tac "set_tlb (snd (write'mem1 (val, fst (mmu_translate va x), sz) (snd (mmu_translate va x)))) =  set_tlb x")
   apply clarsimp
  by (clarsimp simp: mmu_translate_set_tlb_state_ext_def Let_def write'mem1_def raise'exception_def split: if_split_asm)


lemma mmu_read_set_def2:
 "mmu_read_abs (va, sz) =
      do {
                     pa  \<leftarrow> mmu_translate_abs va ;
                     mem_read1 (pa , sz)
  }"
  by (clarsimp simp: mmu_read_abs_def mmu_read_size_set_tlb_state_ext_def mmu_translate_abs_def)


definition "update_TTBR0_abs  \<equiv> (update_TTBR0  :: (paddr \<Rightarrow> 'a::type set_tlb_state_scheme \<Rightarrow> unit \<times> 'a set_tlb_state_scheme))"

definition "update_ASID_abs  \<equiv> (update_ASID  :: (asid \<Rightarrow> 'a set_tlb_state_scheme \<Rightarrow> unit \<times> 'a set_tlb_state_scheme))"



definition "flush_abs  \<equiv> (flush  :: (flush_type \<Rightarrow> 'a set_tlb_state_scheme \<Rightarrow> unit \<times> 'a set_tlb_state_scheme))"



definition
  "K_bindn f g \<equiv> bind f (\<lambda>_. g)"


notation (output) K_bindn ("_ ; _")

lemma update_TTBR0_set_def2:
  "update_TTBR0_abs r  = do {
     
       m   <- read_state MEM; rt <- read_state TTBR0;  a <- read_state ASID;
      iset <- read_state_iset iset;
       gset <- read_state_iset global_set;
      K_bindn ( update_state (\<lambda>s. s\<lparr> TTBR0 := r \<rparr>)) (update_global_set (gset \<union> global_varange a m r));
     
        update_incon_set (iset \<union>  ptable_comp (pt_walk_pair a m rt) (pt_walk_pair a m r))
       
}"
  apply (simp only: global_varange_rewrite)
  apply (clarsimp simp: update_TTBR0_abs_def update_TTBR0_set_tlb_state_ext_def K_bindn_def   K_bind_def
       when_no_exc_def 
     update_incon_set_def  mmu_translate_abs_def
       update_global_set_def   read_state_iset_def global_varange'_def
   split_def Let_def incon_comp_def split: if_split_asm)
  apply rule+
  by (case_tac s; clarsimp)

  (*  read_state6i*)


lemma update_ASID_set_def2:
   "(update_ASID_abs asid :: ('a set_tlb_state_scheme \<Rightarrow> _))  = do {
     (m, rt, a, iset, gset, snp) <- read_state6i (MEM, TTBR0, ASID, iset, global_set, snapshot);  
      \<comment> \<open>snapshot update\<close>
      let snp' = snp_upd_cur' snp iset m rt a;

K_bindn (update_snapshot snp') ( update_state (\<lambda>s. s\<lparr> ASID := asid \<rparr>));

     \<comment> \<open>for the new iset\<close>
     let glb_iset = iset \<inter> gset;
     let snp_iset = fst (snp' asid);
     let pt_iset = ptable_comp (snd(snp' asid)) (pt_walk_pair asid m rt); 
      update_incon_set (glb_iset \<union> snp_iset  \<union> pt_iset)
}"
 by (clarsimp simp: read_state6i_def update_ASID_abs_def update_ASID_set_tlb_state_ext_def update_incon_set_def update_global_set_def K_bindn_def
    read_state_iset_def global_varange_def incon_comp_def update_snapshot_def Let_def Un_commute)





definition
  "upd_abs \<equiv> \<lambda>ist gs snp. do { 
       set_tlb <- read_state set_tlb; 
         let neww  = set_tlb \<lparr>iset := ist, global_set := gs, snapshot := snp \<rparr>;
                   update_state (\<lambda>s. s\<lparr> set_tlb :=  neww \<rparr>)
  }" 




lemma  flush_set_def2:
  "(flush_abs f :: ('a set_tlb_state_scheme \<Rightarrow> _))  = do  {
                      (m,rt,a, is, gs, snp) <- 
                            read_state6i (MEM,TTBR0,ASID,iset,global_set, snapshot);
                       case f of FlushTLB \<Rightarrow> 
                                   upd_abs  {} (global_varange a m rt) (\<lambda> a. ({}, \<lambda>v. Fault))
                                             
                               | Flushvarange vs \<Rightarrow>    upd_abs (is - vs)
                                                       ((gs  - vs)  \<union> global_varange a m rt )
                                                   ( \<lambda> a. (fst(snp a) - vs,  \<lambda>v. if v \<in> vs then Fault else snd(snp a) v))
                           |  FlushASID a' \<Rightarrow> 
                           if a' = a then 
                               update_incon_set (is \<inter> gs)
                           else update_snapshot (snp (a' := ({}, \<lambda>v. Fault)))
       | FlushASIDvarange a' vs \<Rightarrow> 
                       
                          if a' = a then 
                                update_incon_set (is - (vs - gs))
                          else do{ let iset = fst (snp a') ; pt = snd (snp a') in
    update_snapshot (\<lambda>a''. if a'' = a' then (iset - vs, 
                                 \<lambda>v. if v \<in> vs then Fault else pt v)  else snp a'' )}
    }"
apply (simp only: global_varange_rewrite upd_abs_def)
   apply (cases f)
  apply (clarsimp simp: flush_abs_def flush_set_tlb_state_ext_def update_incon_set_def update_global_set_def 
    read_state_iset_def global_varange'_def incon_comp_def update_snapshot_def Let_def Un_commute read_state6i_def split: flush_type.splits)
  apply (clarsimp simp: flush_abs_def flush_set_tlb_state_ext_def update_incon_set_def update_global_set_def 
    read_state_iset_def global_varange'_def incon_comp_def update_snapshot_def Let_def Un_commute read_state6i_def split: flush_type.splits)
 
  apply rule+
  apply (clarsimp simp: flush_abs_def flush_set_tlb_state_ext_def update_incon_set_def update_global_set_def 
    read_state_iset_def global_varange_def incon_comp_def update_snapshot_def Let_def Un_commute read_state6i_def split: flush_type.splits if_split_asm)
  apply (clarsimp simp: flush_abs_def flush_set_tlb_state_ext_def update_incon_set_def update_global_set_def 
    read_state_iset_def  incon_comp_def update_snapshot_def Let_def Un_commute read_state6i_def split: flush_type.splits if_split_asm)
  apply rule+
  apply (clarsimp simp: flush_abs_def flush_set_tlb_state_ext_def update_incon_set_def update_global_set_def 
    read_state_iset_def  incon_comp_def update_snapshot_def Let_def Un_commute read_state6i_def split: flush_type.splits if_split_asm)
  by (clarsimp simp:flush_abs_def flush_set_tlb_state_ext_def update_incon_set_def update_global_set_def 
    read_state_iset_def  incon_comp_def update_snapshot_def Let_def Un_commute read_state6i_def split: flush_type.splits if_split_asm)


definition
  iset' :: "_"
where
  "iset' t = iset (set_tlb t)"   

definition
  gset' :: "_"
where
  "gset' t = global_set (set_tlb t)"       

definition
  snp' :: "_"
where
  "snp' t = snapshot (set_tlb t)" 


definition                              
   tlb_incon_addrs :: _
where                                                         
  "tlb_incon_addrs s  \<equiv>  let tlb= fst (sat_tlb s) ; a = ASID s; m = MEM s ; rt = TTBR0 s  in 
      {va. lookup'' tlb a va = Incon} \<union> 
    {va. \<exists>e. lookup'' tlb a va = Hit e \<and>
        is_fault (pt_walk a m rt va)}"

definition                              
   pdc_incon_addrs :: _
where                                                         
  "pdc_incon_addrs s  \<equiv>  let pdc= snd (sat_tlb s) ; a = ASID s; m = MEM s ; rt = TTBR0 s  in 
         {va. lookup_pdc pdc a va = Incon} \<union>
  {va. \<exists>e. lookup_pdc pdc a va = Hit e \<and>
        is_fault (pdc_walk a m rt va)}"


definition                              
   incon_addrs' :: _
where                                                         
  "incon_addrs' s  \<equiv>  tlb_incon_addrs s \<union> pdc_incon_addrs s"


definition [simp]: "conjn = conj"
notation (output) conjn  ("((\<open>unbreakable\<close>_) \<and>/ (\<open>unbreakable\<close>_))" [30,30] 36)


definition                              
   incon_addrs'' :: _
where                                                         
  "incon_addrs'' s  \<equiv>  let tlb= fst (sat_tlb s) ;  pdc= snd (sat_tlb s) ; a = ASID s; m = MEM s ; rt = TTBR0 s  in 
      {va. lookup'' tlb a va = Incon \<or> lookup_pdc pdc a va = Incon} \<union> 
    {va. (\<exists>te. lookup'' tlb a va = Hit te \<and>
        is_fault (pt_walk a m rt va)) \<or> conjn (\<exists>pe. lookup_pdc pdc a va = Hit pe) 
        (is_fault (pdc_walk a m rt va))}"

lemma incon_simp: 
  "incon_addrs'' s = incon_addrs' s"
  apply (clarsimp simp: incon_addrs'_def incon_addrs''_def Let_def tlb_incon_addrs_def pdc_incon_addrs_def)
  by force


  definition                              
   tlb_global_range :: _
where                                                         
  "tlb_global_range s  \<equiv>  let tlb = fst (sat_tlb s) in 
           (\<Union>e\<in>global_entries tlb. range_of e)"

           
 definition                              
   pdc_global_range :: _
where                                                         
  "pdc_global_range s  \<equiv>  let pdc= snd (sat_tlb s) in 
                      (\<Union>e\<in>global_entries_pdc pdc. range_of e)"

         
               
  definition                              
   global_range' :: _
where                                                         
  "global_range' s  \<equiv>  tlb_global_range s \<union> pdc_global_range s"


  definition                              
   global_range'' :: _
where                                                         
  "global_range'' s  \<equiv>  let tlb = fst (sat_tlb s) ; pdc= snd (sat_tlb s) in 
           (\<Union>e\<in>global_entries tlb. range_of e) \<union>  (\<Union>e\<in>global_entries_pdc pdc. range_of e)"

lemma global_range_simp: 
  "global_range'' s = global_range' s"
  by (clarsimp simp: global_range''_def global_range'_def  tlb_global_range_def Let_def pdc_global_range_def )



definition
  snap_conv_tlb :: "(vaddr set \<times> (vaddr \<Rightarrow> pt_walk_typ)) \<Rightarrow> (vaddr \<Rightarrow> tlb_entry lookup_type)"
  where 
  "snap_conv_tlb snp  \<equiv> \<lambda>v. let iset = fst snp ; pt = snd snp in if v \<in> iset then Incon else  
                          case pt v of Fault              \<Rightarrow> Miss
                                           |  Partial_Walk pe    \<Rightarrow> Miss
                                           |  Full_Walk te pe    \<Rightarrow> if asid_of te = None 
                                                                      then Miss  else Hit te"


definition 
   "tlb_lookup_from snp a v \<equiv> snap_conv_tlb (snp a) v"

 

definition
  snap_conv_pdc :: "(vaddr set \<times> (vaddr \<Rightarrow> pt_walk_typ)) \<Rightarrow> (vaddr \<Rightarrow> pdc_entry lookup_type)"
  where 
  "snap_conv_pdc snp  \<equiv> \<lambda>v. let iset = fst snp ; pt = snd snp in if v \<in> iset then Incon else  
                          case pt v of Fault              \<Rightarrow> Miss
                                           |  Partial_Walk pe    \<Rightarrow> if asid_of_pdc pe = None then Miss else  Hit pe
                                           |  Full_Walk te pe    \<Rightarrow> (if asid_of te = None \<and> 
                                                                      asid_of_pdc pe = None then Miss else Hit pe) "



definition 
   "pdc_lookup_from snp a v \<equiv> snap_conv_pdc (snp a) v"

 definition
  tlb_rel_set :: "'a sat_tlb_state_scheme \<Rightarrow> 'b set_tlb_state_scheme \<Rightarrow> bool"
where
  "tlb_rel_set s t \<equiv> let tlb = fst(sat_tlb s) ; pdc = snd(sat_tlb s) ; a = ASID s ;
      snp = snp' t
      in 
            ( conjn (conjn (state.truncate s = state.truncate t)  
                  (saturated (typ_sat_tlb s))) 
        (incon_addrs'' s \<subseteq>  iset' t) \<and> 
                    global_range'' s \<subseteq> gset' t \<and> 
                     (\<forall>a' v. a' \<noteq> a \<longrightarrow>  
               lookup'' (non_global_entries tlb) a' v \<le> 
                                                          tlb_lookup_from snp a' v \<and>
          lookup_pdc (non_global_entries_pdc pdc) a' v \<le> 
                                                          pdc_lookup_from snp a' v ))" 

  lemma tlb_rel_set_eq:
    "tlb_rel_set s t = tlb_rel_abs (typ_sat_tlb s) (typ_set_tlb t)"
 apply (simp only: tlb_rel_set_def non_global_to_global non_global_to_global_pdc incon_simp global_range_simp)
   apply (clarsimp simp:  tlb_rel_abs_def global_range'_def global_range_def
tlb_global_range_def pdc_global_range_def incon_addrs'_def incon_addrs_def tlb_incon_addrs_def  pdc_incon_addrs_def Let_def 
inconsistent_vaddrs_def incoherrent_vaddrs_def   iset'_def mem_Collect_eq gset'_def snp'_def pdc_lookup_from_def tlb_lookup_from_def
  snap_conv_pdc_def snap_conv_tlb_def lookup_from'_def snap_conv'_def)
   apply  safe               
   apply (clarsimp split: if_split_asm pt_walk_typ.splits)
   apply safe [1]
   apply blast
   apply fastforce
   apply fastforce
   apply (metis (no_types, hide_lams) option.simps(3))
   apply (metis (mono_tags, hide_lams) option.simps(3))
    apply (clarsimp split: if_split_asm pt_walk_typ.splits)
    apply safe [1]
   apply blast
   apply fastforce
   apply fastforce
   apply (metis (no_types, hide_lams) option.simps(3))
   apply (metis (mono_tags, hide_lams) option.simps(3))
   apply (metis (mono_tags, hide_lams) option.simps(3))
     apply (metis (mono_tags, hide_lams) option.simps(3))
    apply (clarsimp split: if_split_asm pt_walk_typ.splits)
    apply safe [1]
   apply blast
   apply fastforce
   apply (metis (no_types, hide_lams) option.simps(3))
   apply (metis (mono_tags, hide_lams) option.simps(3))
  
                              apply (clarsimp split: if_split_asm pt_walk_typ.splits)
   apply safe [1]
   apply blast
   apply fastforce
   apply fastforce
   apply (metis (no_types, hide_lams) option.simps(3))
   by (metis (mono_tags, hide_lams) option.simps(3))  +               

end