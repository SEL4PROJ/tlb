












(*

lemma
  "\<lbrakk>write'mem1 (val, HOL.undefined , sz) (b\<lparr>exception := PAGE_FAULT ''more info''\<rparr>)  = ((), ba) \<rbrakk>  
       \<Longrightarrow>  exception ba = PAGE_FAULT ''more info''"
  by (clarsimp simp: write'mem1_def raise'exception_def split:split_if_asm)


lemma
  "\<lbrakk> mem1s (va, sz) (ba\<lparr>TLB := TLB ba \<union> range (pt_walk (ASID ba) (MEM ba) (TTBR0 ba))\<rparr>) = (val, r) ;
       exception ba = PAGE_FAULT ''more info'' \<rbrakk>   \<Longrightarrow> exception r = PAGE_FAULT ''more info''"
  apply (clarsimp simp: mem1s_def)
  apply (cases " mmu_translate_sat va (ba\<lparr>TLB := TLB ba \<union> range (pt_walk (ASID ba) (MEM ba) (TTBR0 ba))\<rparr>)" , clarsimp)
  (* first reason about exception of b *)
  apply (clarsimp simp: mmu_translate_sat_def Let_def)
  apply (cases "lookup (TLB ba \<union> range (pt_walk (ASID ba) (MEM ba) (TTBR0 ba))) (ASID ba) (addr_val va) ")
    prefer 3
    apply (clarsimp)
   apply (clarsimp simp: mem_def split:split_if_asm)
    apply (case_tac "mem1 (a r+ 0) b" , clarsimp)
    apply (clarsimp split: split_if_asm)
     apply (clarsimp simp: raise'exception_def split: split_if_asm)  


oops

lemma state:
  "\<lbrakk> write'mem'sat' (val,va,sz) s = ((), t); mem1s (va, sz) t = (val, r); consistent t va \<rbrakk> 
                       \<Longrightarrow> t = r"
  apply (clarsimp simp: write'mem'sat'_def)
  apply (cases "mmu_translate_sat va s" , clarsimp)
  apply (clarsimp simp: mmu_translate_sat_def Let_def)
  apply (cases "lookup (TLB s \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s))) (ASID s) (addr_val va)")
    apply (clarsimp simp: saturated_not_miss)
   apply (subgoal_tac "TLB s \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s)) = TLB t \<and> ASID s = ASID t")
    apply (clarsimp simp: consistent0_def)
   apply (case_tac "write'mem1 (val, a, sz) b" , clarsimp)
    apply (subgoal_tac "lookup (TLB s) (ASID s) (addr_val va) \<le> lookup (TLB s \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s))) (ASID s) (addr_val va)")
     prefer 2
     apply (simp add: tlb_mono)

    apply (clarsimp simp: consistent0_def)
   
   apply (clarsimp simp: write'mem'sat'_def)
   apply (cases "mmu_translate_sat va s" , clarsimp)
   apply (clarsimp simp: mmu_translate_sat_def Let_def)
   apply (cases "lookup (TLB s \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s))) (ASID s) (addr_val va)")
     apply (clarsimp simp: saturated_not_miss)
   apply (case_tac "write'mem1 (val, a, sz) b " , clarsimp)
   apply (subgoal_tac "consistent b va")
    apply (clarsimp simp: mmu_translate_sat_def Let_def)
    apply (cases "lookup (TLB s \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s))) (ASID s) (addr_val va)")
      apply (clarsimp simp: saturated_not_miss)
     apply (subgoal_tac "TLB s \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s)) = TLB b \<and>
                           ASID s = ASID b")
      apply (clarsimp simp: consistent0_def)
     apply (clarsimp simp: raise'exception_def split:split_if_asm)
    apply clarsimp
    apply (case_tac "is_fault x3")
     apply (clarsimp)
     apply (subgoal_tac "exception ba = PAGE_FAULT ''more info''")
      apply (clarsimp)



    apply (clarsimp split: split_if_asm)
     apply (clarsimp simp: raise'exception_def split: split_if_asm)
      
     


oops
 mem1s_def mmu_translate_sat_def Let_def split:prod.splits)
  apply (cases "lookup (TLB s \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s))) (ASID s) (addr_val va)")
    apply (clarsimp simp: saturated_not_miss)
   apply (subgoal_tac "TLB t = TLB s \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s))")
    apply (subgoal_tac "MEM x2b = MEM s \<and> ASID x2b = ASID s \<and> TTBR0 x2b = TTBR0 s \<and> TLB x2b = TLB s")
     apply (clarsimp simp: consistent0_def)
  apply (clarsimp simp: write'mem1_def)
  apply (clarsimp split: split_if_asm)
      apply (clarsimp simp: Let_def)
      apply (clarsimp simp: mem1s_def split: prod.splits)
      apply (clarsimp simp: mem_def split: prod.splits)
      apply (clarsimp split: split_if_asm)
         apply (clarsimp simp: raise'exception_def split:split_if_asm)


  
oops
lemma same_state:
  "\<lbrakk>mem1s (va, sz) t = (val, r) ; TLB t = TLB r; MEM t = MEM r \<rbrakk>  
      \<Longrightarrow> exception t = exception r"
  apply (clarsimp simp: mem1s_def split:prod.splits)
  apply (subgoal_tac "TLB t = TLB x2 \<and> MEM t = MEM x2 ")
   apply (subgoal_tac "exception t = exception x2")
    prefer 2
    apply (clarsimp simp: mmu_translate_sat_def Let_def split:prod.splits)
    apply (cases "lookup (TLB r \<union> range (pt_walk (ASID t) (MEM r) (TTBR0 t))) (ASID t) (addr_val va)")
    prefer 3
    apply (clarsimp simp: raise'exception_def split:split_if_asm)
oops

(*lemma
  "\<lbrakk> write'mem'det (val,va, sz) s = ((), s'); consistent t va; tlb_rel_sat s t ;
        write'mem'sat' (val,va, sz) t = ((), t') \<rbrakk> \<Longrightarrow> tlb_rel_sat s' t'"
  apply (clarsimp simp: tlb_rel_sat_def)
  apply (clarsimp simp:  write'_not_in_translation_tables_saturated)
  apply (rule conjI)
  prefer 2
  apply (frule_tac s="s" and s'="s'" and t="t" and t'="t'" in tlb_rel_1; clarsimp simp: tlb_rel_sat_def)
   apply (frule_tac s="s" and s'="s'" and t="t" and t'="t'" in tlb_rel_2; clarsimp simp: tlb_rel_sat_def)
  done
  *)


(*lemma inter:
  "\<lbrakk> mem1 pa s = (val, t) \<rbrakk>  \<Longrightarrow> t = s \<lparr>exception:= exception t\<rparr>"
  apply (clarsimp simp: mem1_def raise'exception_def split:option.splits split_if_asm)
done

lemma inter1:
  "\<lbrakk> mem1 pa s = (val, t) \<rbrakk>  \<Longrightarrow> TLB t = TLB s"
  apply (clarsimp simp: mem1_def raise'exception_def split:option.splits split_if_asm)
done

lemma inter2:
  "\<lbrakk> mem1 pa s = (val, t) \<rbrakk>  \<Longrightarrow> TLB (snd(mem1 pa s)) = TLB t"
  apply (clarsimp simp: mem1_def raise'exception_def split:option.splits split_if_asm)
done

lemma mem1_rewrite:
  "snd (mem1 p s) = s \<lparr>exception:= exception (snd (mem1 p s) ) \<rparr>"
  apply (clarsimp simp: mem1_def raise'exception_def split:option.splits split_if_asm)
  done

lemma mem1_rewrite_excpetion:
  "snd (mem1 p s)\<lparr>exception := UNPREDICTABLE ''undefined memory''\<rparr> = s
              \<lparr>exception := UNPREDICTABLE ''undefined memory''\<rparr>"
apply (clarsimp simp: mem1_def raise'exception_def split:option.splits split_if_asm)
  done

lemma aa:
  "mem (pa, 1) s = (val, t) \<Longrightarrow> t = s\<lparr>exception:= exception t\<rparr>"
  apply (subgoal_tac "\<forall>p s. snd (mem1 p s) = s \<lparr>exception:= exception (snd (mem1 p s))\<rparr>")
   apply (subgoal_tac "\<forall>p s. snd (mem1 p s) \<lparr>exception := UNPREDICTABLE ''undefined memory''\<rparr>  =
            s \<lparr>exception := UNPREDICTABLE ''undefined memory''\<rparr>")
    apply (clarsimp simp: mem_def split_def Let_def split: split_if_asm)
    apply (clarsimp simp: raise'exception_def split:split_if_asm)
   apply (clarsimp simp: mem1_def raise'exception_def split:option.splits split_if_asm)
  apply (clarsimp simp: mem1_def raise'exception_def split:option.splits split_if_asm)
done
    
   



lemma aa1:
  "mem (pa, 2) s = (val, t) \<Longrightarrow> t = s\<lparr>exception:= exception t\<rparr>"
  apply (subgoal_tac "\<forall>p s. snd (mem1 p s) = s \<lparr>exception:= exception (snd (mem1 p s))\<rparr>")
   apply (subgoal_tac "\<forall>p s. snd (mem1 p s) \<lparr>exception := UNPREDICTABLE ''undefined memory''\<rparr>  =
            s \<lparr>exception := UNPREDICTABLE ''undefined memory''\<rparr>")
     apply (clarsimp simp: mem_def split_def Let_def split: split_if_asm)
        apply (clarsimp simp: raise'exception_def split:split_if_asm)
       apply (clarsimp simp: raise'exception_def split:split_if_asm)
       apply (clarsimp simp: mem1_def raise'exception_def split:option.splits split_if_asm)
      apply (clarsimp simp: mem1_def raise'exception_def split:option.splits split_if_asm)
     apply (clarsimp simp: raise'exception_def split:split_if_asm)
    apply (clarsimp simp: mem1_def raise'exception_def split:option.splits split_if_asm)
   apply (clarsimp simp: mem1_def raise'exception_def split:option.splits split_if_asm)
  apply (clarsimp simp: mem1_def raise'exception_def split:option.splits split_if_asm)
  apply (clarsimp simp: mem1_def raise'exception_def split:option.splits split_if_asm)
done
  
lemma aa2:
  "mem (pa, sz) s = (val, t) \<Longrightarrow> t = s\<lparr>exception:= exception t\<rparr>"
  apply (subgoal_tac "\<forall>p s. snd (mem1 p s) = s \<lparr>exception:= exception (snd (mem1 p s))\<rparr>")
   apply (subgoal_tac "\<forall>p s. snd (mem1 p s) \<lparr>exception := UNPREDICTABLE ''undefined memory''\<rparr>  =
            s \<lparr>exception := UNPREDICTABLE ''undefined memory''\<rparr>")
    apply (clarsimp simp: mem_def split_def Let_def) 
    apply (clarsimp split: split_if_asm)
        apply (clarsimp simp: split_def Let_def raise'exception_def split:split_if_asm)
       apply (clarsimp simp: split_def Let_def raise'exception_def split:split_if_asm)
          apply (clarsimp simp: mem1_def raise'exception_def split:option.splits split_if_asm)
         apply (clarsimp simp: mem1_def raise'exception_def split:option.splits split_if_asm)
        apply (clarsimp simp: mem1_def raise'exception_def split:option.splits split_if_asm)
       apply (clarsimp simp: mem1_def raise'exception_def split:option.splits split_if_asm)
      apply (clarsimp simp: split_def Let_def raise'exception_def split:split_if_asm)
             apply (clarsimp simp: mem1_def raise'exception_def)
             apply (clarsimp split:option.splits split_if_asm)
             apply (clarsimp simp: raise'exception_def)
               apply (clarsimp simp: raise'exception_def)
        apply (clarsimp simp: mem1_def raise'exception_def)
             apply (clarsimp split:option.splits split_if_asm)

          apply (fastforce simp: raise'exception_def)
           apply (auto simp: raise'exception_def) [1]     
            apply (auto simp: raise'exception_def) [1]  
        apply (auto simp: raise'exception_def) [1]  
                apply (auto simp: raise'exception_def) [1]   
        apply (clarsimp simp: mem1_def raise'exception_def)
             apply (clarsimp simp: mem1_def raise'exception_def)
      apply (clarsimp split:option.splits split_if_asm)
     apply (auto simp: raise'exception_def) [1] 
    apply (auto simp: raise'exception_def) [1]
      apply (auto simp: raise'exception_def) [1]  
apply (auto simp: raise'exception_def) [9]  
apply (auto simp: raise'exception_def) [2]  
 apply (clarsimp simp: mem1_def raise'exception_def)
     
       
oops




lemma a:
  "mem (pa, sz) s = (val, t) \<Longrightarrow> TLB s = TLB t"
  apply (cases s , cases t)
  apply (drule aa)
  apply (clarsimp simp: aa)
  done

lemma b:
  "\<lbrakk> mem1s (va, sz) s = (val, t) ; saturated s \<rbrakk>  \<Longrightarrow> TLB t = TLB s"
  apply (clarsimp simp: mem1s_def split_def Let_def)
  apply (subgoal_tac "TLB (snd (mmu_translate_sat va s)) = TLB s")
   apply (subgoal_tac "TLB (snd (mem (fst (mmu_translate_sat va s), sz) (snd (mmu_translate_sat va s)))) =
    TLB s")
    apply clarsimp
   prefer 2
   apply (subgoal_tac "TLB (snd (mmu_translate_sat va s)) = TLB s \<union> pt_walk (ASID s) (MEM s) (TTBR0 s) ` UNIV")
    apply (clarsimp simp: saturated_def)
    apply blast
   apply (clarsimp simp: mmu_translate_sat_def Let_def split_def)
   apply (cases "lookup (TLB s \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s))) (ASID s) (addr_val va)"; clarsimp simp: raise'exception_def)
  apply clarsimp
  apply (subgoal_tac "TLB t = TLB (snd (mmu_translate_sat va s))")
   apply clarsimp
  apply (clarsimp simp: a)
  done
  

lemma write'_not_in_translation_tables_TLB:
  "\<lbrakk> write'mem'sat' (val,va,sz) s = ((), t); mem1s (va, sz) t = (val, r) \<rbrakk> 
        \<Longrightarrow> (TLB t) = (TLB r)"
  apply (cases "\<not> ptable_trace (MEM s) (TTBR0 s) va \<subseteq> \<Union>(ptable_trace (MEM s) (TTBR0 s) ` UNIV)" )
   apply (subgoal_tac "saturated t")
    prefer 2
    apply (clarsimp simp: write'_not_in_translation_tables_saturated)
   apply (clarsimp simp: mem1s_def)
   apply (cases "mmu_translate_sat va t" , clarsimp)
   apply (clarsimp simp: mmu_translate_sat_def Let_def)
   apply (cases
     "lookup (TLB t \<union> range (pt_walk (ASID t) (MEM t) (TTBR0 t))) (ASID t) (addr_val va)")
     apply (simp only: split_if_asm raise'exception_def saturated_def, force) +
  apply simp
  apply (subgoal_tac "saturated t")
   prefer 2
   apply (clarsimp simp: write'_not_in_translation_tables_saturated)
  apply (clarsimp simp: b)
done

*)



definition
  mem1s1 :: "vaddr \<times> nat \<Rightarrow> state \<Rightarrow> bool list \<times> state"
where
  "mem1s1 \<equiv> \<lambda>(va, sz). do {
                     pa  \<leftarrow> mmu_translate_sat va; 
                     if pa = HOL.undefined 
                     then return (HOL.undefined) 
                     else (mem (pa, sz))
  }"                           


definition
  "write'mem'sat'1" :: "bool list \<times> vaddr \<times> nat \<Rightarrow> state \<Rightarrow> unit \<times> state"
where
  "write'mem'sat'1 \<equiv> \<lambda>(value, va, size). do {
     mem   <- read_state MEM;
     ttbr0 <- read_state TTBR0;
     asid <- read_state ASID;
     (* original TLB before memory translation *)
     pa <- mmu_translate_sat va;
     if pa = HOL.undefined 
      then return (HOL.undefined) 
      else do { 
           write'mem1 (value, pa, size); 
           tlb0  <- read_state TLB;
           mem1  <- read_state MEM;
           let all_entries = pt_walk asid mem1 ttbr0 ` UNIV;
           let tlb = tlb0 \<union> all_entries;  (* what about inconsistency here ? *)
           update_state (\<lambda>s. s\<lparr> TLB := tlb \<rparr>)
          } 
    }"


lemma write'_not_in_translation_tables_saturated1:
  "\<lbrakk> write'mem'sat'1 (val,va,sz) s = ((), t)  \<rbrakk>  \<Longrightarrow> saturated t"
  apply (clarsimp simp: write'mem'sat'1_def split_def Let_def)
  apply (clarsimp split: split_if_asm)
   apply (clarsimp simp: mmu_translate_sat_sat)
  apply (clarsimp simp: split_def)
  apply (subgoal_tac "ASID s = ASID (snd (write'mem1 (val, fst (mmu_translate_sat va s), sz) (snd (mmu_translate_sat va s)))) \<and>
                       TTBR0 s = TTBR0 (snd (write'mem1 (val, fst (mmu_translate_sat va s), sz) (snd (mmu_translate_sat va s)))) ")
   apply (clarsimp simp: saturated_def)
  apply (subgoal_tac "ASID s = ASID (snd(mmu_translate_sat va s)) \<and> TTBR0 s = TTBR0 (snd(mmu_translate_sat va s))")
   apply (clarsimp simp:  write'mem1_def Let_def raise'exception_def)
  apply (clarsimp simp: mmu_translate_sat_def Let_def raise'exception_def split:lookup_type.splits)
  done 


(* see write'mem'det_TLBs *)
lemma write'mem'sat'1_TLBs:
  "\<lbrakk>write'mem'sat'1 (val,va, sz) s = ((), s') \<rbrakk> \<Longrightarrow>
     TLB s' = TLB s \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s)) \<or>
     TLB s' = TLB s \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s)) \<union> range (pt_walk (ASID s') (MEM s') (TTBR0 s'))"
  apply (cases "fst (mmu_translate_sat va s) = HOL.undefined")
   apply (simp only: write'mem'sat'1_def Let_def split_def)
   apply (rule disjI1)
   apply (clarsimp simp: split_def)
   apply (metis mmu_translate_sat_TLB_union prod.collapse)
  apply (clarsimp simp: write'mem'sat'1_def Let_def split_def)
  apply (subgoal_tac "TLB (snd (write'mem1 (val, fst (mmu_translate_sat va s), sz) (snd (mmu_translate_sat va s)))) = TLB (snd (mmu_translate_sat va s))")
   apply clarsimp
   apply (subgoal_tac "TLB (snd (mmu_translate_sat va s)) = TLB s \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s))")
    apply (subgoal_tac "ASID (snd (write'mem1 (val, fst (mmu_translate_sat va s), sz) (snd (mmu_translate_sat va s)))) = ASID s \<and>
                        TTBR0 (snd (write'mem1 (val, fst (mmu_translate_sat va s), sz) (snd (mmu_translate_sat va s)))) = TTBR0 s")
     apply clarsimp
    apply (clarsimp simp: snd_def fst_def)
    apply (case_tac " mmu_translate_sat va s" , clarsimp)
    apply (case_tac "write'mem1 (val, a, sz) b" , clarsimp)
    apply (subgoal_tac "ASID b = ASID s \<and> TTBR0 b = TTBR0 s")
     apply (clarsimp simp: write'mem1_eq_ASID_TTBR0)
    apply (clarsimp simp: mmu_sat_eq_ASID_TTBR0_MEM)
   apply (clarsimp simp: snd_def)
   apply (case_tac " mmu_translate_sat va s" , clarsimp)
   apply (clarsimp simp: mmu_translate_sat_TLB_union)
  apply (clarsimp simp: snd_def fst_def)
  apply (cases "mmu_translate_sat va s" , clarsimp)
  apply (case_tac "write'mem1 (val, a, sz) b" , clarsimp)
  apply (clarsimp simp: write'mem1_eq_TLB)
done


lemma
  "\<lbrakk> saturated t ; consistent t va\<rbrakk> \<Longrightarrow> t = snd (mmu_translate_sat va t)"
  apply (clarsimp simp: saturated_def mmu_translate_sat_def Let_def split_def)
  apply (cases "lookup (TLB t \<union> range (pt_walk (ASID t) (MEM t) (TTBR0 t))) (ASID t) (addr_val va)" ; clarsimp)
    using saturated_not_miss apply blast
   using sat_con_not_miss_incon sat_state_tlb saturated_def apply auto[1]
  apply (case_tac "is_fault x3")
   apply (clarsimp)
 (* can not do this *)
  

oops

lemma 
  "\<lbrakk> write'mem'sat'1 (val,va,sz) s = ((), t); mem1s1 (va, sz) t = (val, r); consistent t va \<rbrakk> 
                 \<Longrightarrow>  t = r "
  apply (subgoal_tac "MEM t = MEM r")
   apply (subgoal_tac "TLB t = TLB r")
    apply (subgoal_tac "consistent s va")
     apply (clarsimp simp: write'mem'sat'1_def Let_def split_def)
     apply (clarsimp simp: mmu_translate_sat_def Let_def)
     apply (cases " lookup (TLB s \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s))) (ASID s) (addr_val va)")
      using saturated_not_miss apply blast
     prefer 2
     apply clarsimp
    
    apply (subgoal_tac "mmu_translate_sat va t = mmu_translate_sat va r")


  apply (clarsimp simp: mem1s1_def Let_def split_def split:split_if_asm)


oops

lemma 
  "\<lbrakk> write'mem'sat'1 (val,va,sz) s = ((), t); mem1s1 (va, sz) t = (val, r); consistent t va \<rbrakk> 
                 \<Longrightarrow> fst (mmu_translate_sat va s) =  fst (mmu_translate_sat va t)"
  apply (subgoal_tac "TLB t = TLB s \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s)) \<or>
                      TLB t = TLB s \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s)) \<union> range (pt_walk (ASID t) (MEM t) (TTBR0 t))")
   prefer 2
   apply (clarsimp simp: write'mem'sat'1_TLBs)
  apply (subgoal_tac "saturated t")
   prefer 2
   apply (clarsimp simp: write'_not_in_translation_tables_saturated1)
  apply (subgoal_tac "lookup (TLB s) (ASID s) (addr_val va) \<le> lookup (TLB t) (ASID s) (addr_val va)")
   apply (clarsimp simp: mmu_translate_sat_def Let_def)
   apply (cases "lookup (TLB t \<union> range (pt_walk (ASID t) (MEM t) (TTBR0 t))) (ASID t) (addr_val va)")
     using saturated_not_miss apply blast
    using sat_con_not_miss_incon sat_state_tlb apply auto[1]
   apply (case_tac "is_fault x3")
    apply (erule disjE)
     apply (clarsimp simp:raise'exception_def)
   














  
   prefer 2
proof -
  assume "TLB t = TLB s \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s)) \<or> TLB t = TLB s \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s)) \<union> range (pt_walk (ASID t) (MEM t) (TTBR0 t))"
  then have "TLB s \<subseteq> TLB t"
    by blast
  then show "lookup (TLB s) (ASID s) (addr_val va) \<le> lookup (TLB t) (ASID s) (addr_val va)"
    by (meson tlb_mono)
next
  apply (clarsimp simp: mmu_translate_def)
 

   apply (clarsimp simp: tlb_mono)
  apply (clarsimp simp: write'mem'sat'1_def)
  apply (cases "mmu_translate_sat va s" , clarsimp)
  apply (clarsimp simp: mmu_translate_sat_def Let_def)
  apply (cases "lookup (TLB s \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s))) (ASID s) (addr_val va)")
    apply (clarsimp simp: saturated_not_miss)
   apply (subgoal_tac "TLB s \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s))
                             \<union> range (pt_walk (ASID t) (MEM t) (TTBR0 t))= TLB t \<and> ASID s = ASID t")
    apply (subgoal_tac "lookup (TLB s \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s))) (ASID s) (addr_val va) \<le> lookup (TLB s \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s))
                                      \<union> range (pt_walk (ASID t) (MEM t) (TTBR0 t))) (ASID s) (addr_val va)")
     apply (clarsimp simp: consistent0_def)
    apply (clarsimp simp: tlb_mono consistent0_def)
    apply (metis (no_types, hide_lams) lookup_incon_subset sup.cobounded1)
   apply (case_tac "write'mem1 (val, a, sz) b" , clarsimp)
   apply (clarsimp simp: raise'exception_def write'mem1_eq_ASID_TTBR0 write'mem1_eq_TLB split:split_if_asm)
  apply (clarsimp simp: mem1s1_def)
  apply (cases "mmu_translate_sat va t" , clarsimp)
  apply (clarsimp simp: mmu_translate_sat_def Let_def)
  apply (cases "lookup (TLB t \<union> range (pt_walk (ASID t) (MEM t) (TTBR0 t))) (ASID t) (addr_val va)")
    apply (clarsimp simp: saturated_not_miss)
   apply (subgoal_tac "TLB t = TLB t \<union> range (pt_walk (ASID t) (MEM t) (TTBR0 t))")
    apply (clarsimp simp: consistent0_def)
   using saturated_def apply blast
  apply (clarsimp split: split_if_asm)
      apply (clarsimp simp: raise'exception_def split:split_if_asm)
  
  
 



   apply (clarsimp simp: consistent0_def)
  apply (clarsimp split:split_if_asm)
    apply ()


oops

lemma
  "\<lbrakk>write'mem1 (val, HOL.undefined, sz) (b\<lparr>exception := PAGE_FAULT ''more info''\<rparr>) = ((), ba) \<rbrakk>   \<Longrightarrow> 
        (b\<lparr>exception := PAGE_FAULT ''more info''\<rparr>) = ba"
  apply (clarsimp simp: write'mem1_def split:split_if_asm)
    apply (clarsimp simp: Let_def)

oops

lemma state:
  "\<lbrakk> write'mem'sat'1 (val,va,sz) s = ((), t); mem1s (va, sz) t = (val, r); consistent t va \<rbrakk> 
                 \<Longrightarrow> t = r "
  apply (clarsimp simp: write'mem'sat'1_def)
  apply (cases "mmu_translate_sat va s" , clarsimp)
  apply (clarsimp simp: mmu_translate_sat_def Let_def)
  apply (cases "lookup (TLB s \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s))) (ASID s) (addr_val va)")
    apply (clarsimp simp: saturated_not_miss)
   apply (subgoal_tac "TLB s \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s))
                            \<union> range (pt_walk (ASID t) (MEM t) (TTBR0 t))= TLB t \<and> ASID s = ASID t")
    apply (subgoal_tac "lookup (TLB s \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s))) (ASID s) (addr_val va) \<le> lookup (TLB s \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s))
                            \<union> range (pt_walk (ASID t) (MEM t) (TTBR0 t))) (ASID s) (addr_val va)")
     apply (clarsimp simp: consistent0_def)
    apply (clarsimp simp: tlb_mono consistent0_def)
    apply (metis (no_types, hide_lams) lookup_incon_subset sup.cobounded1)
   apply (case_tac "write'mem1 (val, a, sz) b" , clarsimp)
   apply (clarsimp simp: raise'exception_def write'mem1_eq_ASID_TTBR0 write'mem1_eq_TLB split:split_if_asm)
  apply (clarsimp split:split_if_asm)
     apply (clarsimp simp: raise'exception_def split:split_if_asm)
   apply (case_tac "write'mem1 (val, a, sz) b" , clarsimp)
   apply (clarsimp simp: raise'exception_def)


    apply (clarsimp simp: consistent0_def)
   apply (case_tac "write'mem1 (val, a, sz) b" , clarsimp)
   apply (clarsimp simp : write'mem1_eq_ASID_TTBR0 raise'exception_def split:split_if_asm)
    apply (subgoal_tac "lookup (TLB s) (ASID s) (addr_val va) \<le> lookup (TLB s \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s))) (ASID s) (addr_val va)")
     prefer 2
     apply (simp add: tlb_mono)






















(* Redentant Code from here *)

definition 
  ttbr0_wrp_bit :: "32 word \<Rightarrow> bool"
where
  "ttbr0_wrp_bit ttbr0 = hd (to_bl (ucast (ttbr0 AND 0x1) :: 1 word))"


definition
  "write'mem'sat1" :: "bool list \<times> 32 word \<times> nat \<Rightarrow> state \<Rightarrow> unit \<times> state"
where
  "write'mem'sat1 \<equiv> \<lambda>(value, vaddr, size). do {
     (* original TLB before memory translation *)
     tlb0  <- read_state TLB;
     paddr <- mmu_translate_sat vaddr;
     asid  <- read_state ASID;
     ttbr0 <- read_state TTBR0;
     (* size is in {1, 2, 4, 8} and will be aligned, so will not cross page boundaries *)
     case ttbr0_wrp_bit ttbr0 of
           True \<Rightarrow> do {           (* translation table cant be changed *)
                    write'mem1 (value, paddr, size);
                    mem   <- read_state MEM;  (* may be this redundant *)
                    update_state (\<lambda>s. s\<lparr> MEM := mem \<rparr>)
                    (* ^^ do i have to do this update explicitly ? *)
                   }
         | False \<Rightarrow> do {          (* translation table can be changed *)
                    write'mem1 (value, paddr, size);
                    mem   <- read_state MEM;
                    let all_entries = pt_walk asid mem ttbr0 ` UNIV;
                    let tlb = tlb0 \<union> all_entries;
                    update_state (\<lambda>s. s\<lparr> TLB := tlb \<rparr>)
                   }
  }"

(* s has to be in saturated state *)
lemma TLB_same_saturated_wrp:
  "\<lbrakk>write'mem'sat1 (v,va,sz) s = ((), t) ; ttbr0_wrp_bit (TTBR0 s) ; saturated s \<rbrakk> 
              \<Longrightarrow> TLB t = TLB s"
  apply (clarsimp simp: write'mem'sat1_def)
  apply (cases "mmu_translate_sat va s" , clarsimp)
  apply (subgoal_tac "TTBR0 s = TTBR0 b \<and> TLB b = TLB t")
   apply (clarsimp)
   apply (subgoal_tac "TLB s = TLB b")
    apply (clarsimp)
   apply (clarsimp simp: mmu_translate_sat_def Let_def)
   apply (case_tac "lookup (TLB s \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 b))) (ASID s) va" )
     apply (frule saturated_lookup_not_miss)
     apply (frule sat_state_tlb ; clarsimp)
    apply (clarsimp simp:raise'exception_def split:split_if_asm)
     apply (frule sat_state_tlb)
     apply clarsimp
    apply (frule sat_state_tlb)
    apply clarsimp
   apply (frule sat_state_tlb)
   apply (clarsimp simp: raise'exception_def split:split_if_asm)
  apply (rule conjI)
   apply (clarsimp simp: mmu_translate_sat_def Let_def , cases " lookup (TLB s \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s))) (ASID s) va")
     apply (frule saturated_lookup_not_miss)
     apply (frule sat_state_tlb ; clarsimp)
    apply (clarsimp simp:raise'exception_def split:split_if_asm)
   apply (clarsimp simp:raise'exception_def split:split_if_asm)
  apply (subgoal_tac "TTBR0 s = TTBR0 b")
   apply clarsimp
   apply (clarsimp simp: write'mem1_def raise'exception_def split:split_if_asm)
  apply (clarsimp simp: mmu_translate_sat_def Let_def , cases " lookup (TLB s \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s))) (ASID s) va")
    apply (frule saturated_lookup_not_miss)
    apply (frule sat_state_tlb ; clarsimp)
   apply (clarsimp simp:raise'exception_def split:split_if_asm)+
done

lemma  write'mem1_tlb_same:
  "write'mem1 (v, a, sz) b = ((), t) \<Longrightarrow> TLB b = TLB t"
  apply (clarsimp simp: write'mem1_def raise'exception_def split:split_if_asm)
done


lemma write'mem'sat1_tlb_TLB_sat:
  "\<lbrakk>write'mem'sat1 (v,va,sz) s = ((), t); ttbr0_wrp_bit (TTBR0 s) \<rbrakk> \<Longrightarrow>
        TLB t = TLB s \<union> pt_walk (ASID s) (MEM s) (TTBR0 s) ` UNIV  "
  apply (clarsimp simp: write'mem'sat1_def)
  apply (cases "mmu_translate_sat va s", clarsimp)
  apply (subgoal_tac "ttbr0_wrp_bit (TTBR0 b)")
   apply clarsimp
   apply (subgoal_tac "TLB b = TLB s \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s))")
    apply (clarsimp simp: write'mem1_def raise'exception_def split:split_if_asm)
   apply (clarsimp simp:mmu_translate_sat_TLB_union)
  apply (subgoal_tac "TTBR0 b = TTBR0 s")
   apply (clarsimp simp: ttbr0_wrp_bit_def)
  apply (clarsimp simp: mmu_translate_sat_def Let_def)
  apply (cases "lookup (TLB s \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 s))) (ASID s) va")
    apply (clarsimp simp:raise'exception_def split:split_if_asm)+
done

lemma
  "\<lbrakk> TLB b = TLB t ; saturated b ; ASID t = ASID b ; TTBR0 t = TTBR0 b\<rbrakk> \<Longrightarrow> 
      saturated t"
  apply (unfold saturated_def) [1]
  apply simp
  apply (clarsimp simp: pt_walk_def Let_def)

oops

lemma
  "write'mem'sat1 (v, va, sz) s = ((), t) \<Longrightarrow> saturated t"
  apply (clarsimp simp: write'mem'sat1_def)
  apply (cases "mmu_translate_sat va s", clarsimp)
  apply (subgoal_tac "saturated b")
   apply (case_tac "ttbr0_wrp_bit (TTBR0 b)", clarsimp)
    apply (subgoal_tac "TLB b = TLB t")
     apply (unfold saturated_def) [1]
     (*apply ((clarsimp simp: write'mem1_def raise'exception_def split:split_if_asm))*)

oops


(* declare [[show_types]] *)
lemma
 "\<lbrakk>write'mem'sat1 (v,va,sz) s = ((), t) ; ttbr0_wrp_bit (TTBR0 s);
    write'mem'sat1 (v,va,sz) t = ((), r)  \<rbrakk> \<Longrightarrow> TLB t = TLB r"
  apply (subgoal_tac "ttbr0_wrp_bit (TTBR0 t)")
   apply (subgoal_tac "saturated t")
    apply (clarsimp simp: TLB_same_saturated_wrp)
   apply (clarsimp simp: write'mem'sat1_def)
   apply (cases "mmu_translate_sat va s" , clarsimp)
   apply (subgoal_tac "ttbr0_wrp_bit (TTBR0 b)")
    apply clarsimp
    apply (subgoal_tac "saturated b")
     apply (subgoal_tac "TLB b = TLB t")
   (* can't go any further without modifying write'mem1 for wrp bit *)

   apply (unfold saturated_def)
  apply (frule (1) write'mem'sat1_tlb_TLB_sat)
  apply (unfold saturated_def)
  apply (frule mem'write'sat_tlb_asid_ttbr0 ; erule conjE ; clarsimp)
  using saturated_def apply simp
   apply ()
   apply ()

oops

(*find the alignment of translation table *)
(* find the page table size , multiple levels as well *) 
(* assumption *)
definition
  tt_sz :: "ttbr0 \<Rightarrow> 32 word set"
where
  "tt_sz ttbr0 \<equiv> {x . ttbr0 \<le> x \<and> x \<le> (ttbr0 + 10)}"


definition
  "write'mem'sat2" :: "bool list \<times> 32 word \<times> nat \<Rightarrow> state \<Rightarrow> unit \<times> state"
where
  "write'mem'sat2 \<equiv> \<lambda>(value, vaddr, size). do {
     (* original TLB before memory translation *)
     tlb0  <- read_state TLB;
     paddr <- mmu_translate_sat vaddr;
     asid  <- read_state ASID;
     ttbr0 <- read_state TTBR0;
     let paddrset = {x. paddr \<le> x \<and> x \<le> (paddr + of_nat size)};
     (* size is in {1, 2, 4, 8} and will be aligned, so will not cross page boundaries *)
     if ttbr0_wrp_bit ttbr0 \<and> paddrset \<inter> tt_sz ttbr0 \<noteq> {} then 
         raise'exception (IMPLEMENTATION_DEFINED ''Page Table is Write Protected'')  
     else if ttbr0_wrp_bit ttbr0 \<and> paddrset \<inter> tt_sz ttbr0 = {} then 
          do {           (* translation table cant be changed *)
               write'mem1 (value, paddr, size);
               mem   <- read_state MEM;  (* may be this is redundant *)
               update_state (\<lambda>s. s\<lparr> MEM := mem \<rparr>)
                    (* ^^ do i have to do this update explicitly ? *)
     }
     else if \<not>ttbr0_wrp_bit ttbr0 \<and> paddrset \<inter> tt_sz ttbr0 = {} then 
          do {           (* translation table cant be changed *)
               write'mem1 (value, paddr, size);
               mem   <- read_state MEM;  (* may be this is redundant *)
               update_state (\<lambda>s. s\<lparr> MEM := mem \<rparr>)
                    (* ^^ do i have to do this update explicitly ? *)
     }
     else 
          do {          (* translation table can be changed *)
               write'mem1 (value, paddr, size);
               mem   <- read_state MEM;
               let all_entries = pt_walk asid mem ttbr0 ` UNIV;
               let tlb = tlb0 \<union> all_entries;
               update_state (\<lambda>s. s\<lparr> TLB := tlb \<rparr>)
     }
  }"



definition
  write'mem2 :: "bool list \<times> 32 word \<times> nat \<Rightarrow> state \<Rightarrow> unit \<times> state"
where
  "write'mem2 \<equiv> 
   \<lambda>(value, address, size).
   do {
   ttbr0 <- read_state TTBR0;
   if address \<notin> tt_sz ttbr0 then do {
   if size = 1 then do {
                      v \<leftarrow> read_state MEM;
                      v \<leftarrow> return (v(address + 0 := of_bl (bitstring_field 7 0 value)));
                      update_state (MEM_update (\<lambda>_. v))
                    }
   else if size = 2 then do {
                           do {
                               v \<leftarrow> read_state MEM;
                               v \<leftarrow> return (v(address + 0 := of_bl (bitstring_field 7 0 value)));
                               update_state (MEM_update (\<lambda>_. v))
                             };
                           v \<leftarrow> read_state MEM;
                           v \<leftarrow> return (v(address + 1 := of_bl (bitstring_field 15 8 value)));
                           update_state (MEM_update (\<lambda>_. v))
                         }
        else if size = 4 then do {
                                do {
                                    v \<leftarrow> read_state MEM;
                                    v \<leftarrow> return (v(address + 0 := of_bl (bitstring_field 7 0 value)));
                                    update_state (MEM_update (\<lambda>_. v))
                                  };
                                 do {
                                    v \<leftarrow> read_state MEM;
                                    v \<leftarrow> return (v(address + 1 := of_bl (bitstring_field 15 8 value)));
                                    update_state (MEM_update (\<lambda>_. v))
                                  };
                                 do {
                                    v \<leftarrow> read_state MEM;
                                    v \<leftarrow> return (v(address + 2 := of_bl (bitstring_field 23 16 value)));
                                    update_state (MEM_update (\<lambda>_. v))
                                  };
                                v \<leftarrow> read_state MEM;
                                v \<leftarrow> return (v(address + 3 := of_bl (bitstring_field 31 24 value)));
                                update_state (MEM_update (\<lambda>_. v))
                              }
             else if size = 8 then do {
                                      do {
                                         v \<leftarrow> read_state MEM;
                                         v \<leftarrow> return (v(address + 0 := of_bl (bitstring_field 7 0 value)));
                                         update_state (MEM_update (\<lambda>_. v))
                                       };
                                      do {
                                         v \<leftarrow> read_state MEM;
                                         v \<leftarrow> return (v(address + 1 := of_bl (bitstring_field 15 8 value)));
                                         update_state (MEM_update (\<lambda>_. v))
                                       };
                                     do {
                                         v \<leftarrow> read_state MEM;
                                         v \<leftarrow> return (v(address + 2 := of_bl (bitstring_field 23 16 value)));
                                         update_state (MEM_update (\<lambda>_. v))
                                       };
                                      do {
                                         v \<leftarrow> read_state MEM;
                                         v \<leftarrow> return (v(address + 3 := of_bl (bitstring_field 31 24 value)));
                                         update_state (MEM_update (\<lambda>_. v))
                                       };
                                     do {
                                         v \<leftarrow> read_state MEM;
                                         v \<leftarrow> return (v(address + 4 := of_bl (bitstring_field 39 32 value)));
                                         update_state (MEM_update (\<lambda>_. v))
                                       };
                                      do {
                                         v \<leftarrow> read_state MEM;
                                         v \<leftarrow> return (v(address + 5 := of_bl (bitstring_field 47 40 value)));
                                         update_state (MEM_update (\<lambda>_. v))
                                       };
                                      do {
                                         v \<leftarrow> read_state MEM;
                                         v \<leftarrow> return (v(address + 6 := of_bl (bitstring_field 55 48 value)));
                                         update_state (MEM_update (\<lambda>_. v))
                                       };
                                     v \<leftarrow> read_state MEM;
                                     v \<leftarrow> return (v(address + 7 := of_bl (bitstring_field 63 56 value)));
                                     update_state (MEM_update (\<lambda>_. v))
                                   }
                  else raise'exception (ASSERT ''mem: size in {1, 2, 4, 8}'')  
   }
  else  raise'exception (IMPLEMENTATION_DEFINED ''Page Table is Write Protected'')   
   }"


lemma abc:
  "\<lbrakk>write'mem'sat2 (v,va,sz) s = ((), t) ; ttbr0_wrp_bit (TTBR0 s) ; saturated s \<rbrakk> 
              \<Longrightarrow> TLB t = TLB s"
  apply (clarsimp simp: write'mem'sat2_def)
  apply (cases "mmu_translate_sat va s" , clarsimp)
  apply (subgoal_tac "ttbr0_wrp_bit (TTBR0 b)")
   apply (subgoal_tac "TTBR0 s = TTBR0 b \<and> TLB b = TLB t")
    apply (subgoal_tac "TLB s = TLB b")
     apply (case_tac "a \<in> tt_sz (TTBR0 b)")
      apply (clarsimp  simp: raise'exception_def split: split_if_asm)
     apply (clarsimp)
    apply (clarsimp simp: mmu_translate_sat_def Let_def)
    apply (case_tac "lookup (TLB s \<union> range (pt_walk (ASID s) (MEM s) (TTBR0 b))) (ASID s) va" )
      apply (frule saturated_lookup_not_miss)
      apply (frule sat_state_tlb ; clarsimp)
     apply (clarsimp simp: raise'exception_def saturated_def split:split_if_asm)
    apply (cases s, case_tac b, clarsimp)
    apply (cases s, cases t, force)
     apply (cases s, case_tac b, clarsimp)
     apply (cases s, cases t, force)
    sorry
      


lemma
 "\<lbrakk>write'mem'sat2 (v,va,sz) s = ((), t) ; ttbr0_wrp_bit (TTBR0 s);
    write'mem'sat2 (v,va,sz) t = ((), r)  \<rbrakk> \<Longrightarrow> TLB t = TLB r"
  apply (subgoal_tac "ttbr0_wrp_bit (TTBR0 t)")
   apply (subgoal_tac "saturated t")
    apply (clarsimp simp: abc)
   apply (clarsimp simp: write'mem'sat2_def)
   apply (cases "mmu_translate_sat va s" , clarsimp)
   apply (subgoal_tac "ttbr0_wrp_bit (TTBR0 b)")
    apply (case_tac "a \<in> tt_sz (TTBR0 b)")
     apply (clarsimp)
     apply (subgoal_tac "saturated b")
      apply (clarsimp simp: raise'exception_def
      split:split_if_asm)
      apply (unfold saturated_def) [1]
      apply simp
     apply (clarsimp simp:mmu_translate_sat_sat)
    apply (clarsimp)
    apply (frule mmu_translate_sat_sat)
    apply (frule write'mem1_tlb_same)
    apply (unfold saturated_def) [1]

oops

  apply (cases "mmu_translate_sat va s" , clarsimp)
  apply (subgoal_tac "ttbr0_wrp_bit (TTBR0 b)")
   apply (case_tac "a \<in> tt_sz (TTBR0 b)")
    apply (clarsimp simp: raise'exception_def split:split_if_asm)
  apply (subgoal_tac "ttbr0_wrp_bit (TTBR0 t)")
   apply (subgoal_tac "saturated t")
    apply (clarsimp simp: TLB_same_saturated_wrp)
   apply (clarsimp simp: write'mem'sat1_def)
   apply (cases "mmu_translate_sat va s" , clarsimp)
   apply (subgoal_tac "ttbr0_wrp_bit (TTBR0 b)")
    apply clarsimp
    apply (subgoal_tac "saturated b")
     apply (subgoal_tac "TLB b = TLB t")






thm write'mem1_def

thm MEM_update_def

(* ask Gerwin how to merge this value *)
 *)

