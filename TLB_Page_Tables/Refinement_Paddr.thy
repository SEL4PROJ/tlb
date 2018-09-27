theory Refinement_Paddr
imports  Refinement_Support

begin

lemma false_imp_post:
  "\<lbrace>\<lambda>_. False\<rbrace> f \<lbrace>\<lambda>r s. Q'  r s \<rbrace>"
  by (clarsimp simp: l3_valid_def)

lemma vcg_const_imp_lift:
  "\<lbrace>\<lambda>s. \<not>P s\<rbrace> f \<lbrace>\<lambda>_ s. \<not>P s\<rbrace> \<Longrightarrow> \<lbrace>\<lambda>s. P s \<longrightarrow> Q'\<rbrace> f \<lbrace>\<lambda>_ s. P s \<longrightarrow> Q'\<rbrace>"
  by (smt l3_valid_def)

lemma vcg_imp:
  "\<lbrakk> \<lbrace>\<lambda>s.  R' s \<longrightarrow> \<not>P s\<rbrace> f \<lbrace>\<lambda>_ s. \<not>P s\<rbrace>  \<rbrakk> \<Longrightarrow> 
    \<lbrace>\<lambda>s. P s \<longrightarrow> R' s \<longrightarrow> Q'\<rbrace> f \<lbrace>\<lambda>_ s. P s \<longrightarrow> Q'\<rbrace>"
  by (smt l3_valid_def)

lemma exception_exception[simp]:
  "exception (s\<lparr>exception := e\<rparr>) = e"
  by (cases s, simp)

lemma if_True1[simp]:
  "(if Q' then \<lambda>_. True else f) = (\<lambda>s. \<not>Q' \<longrightarrow> f s)"
  by auto

lemma if_True2[simp]:
  "(if Q' then  True else f) = ( \<not>Q' \<longrightarrow> f)"
  by auto

lemma if_True3[simp]:
  "(if Q' then f else (\<lambda>_. True)) = (\<lambda>s. Q' \<longrightarrow> f s)"
  by auto

lemma  if_False''[simp]:
  "(if Q' then  False else f) = (\<not> Q' \<and> (\<not> Q' \<longrightarrow> f))"
  by auto


lemma if_True4[simp]:
  "(\<forall>r. if r then MMU_config_assert_isa s else True) = (\<forall>r. r \<longrightarrow> MMU_config_assert_isa s)"
  by auto

lemma word_2_if_else[simp]:
  "(if (w::2 word) = 0 then A' else if w = 1 then B' else if w = 2 then C' else if  w = 3 then D' else E') =
   (if (w::2 word) = 0 then A' else if w = 1 then B' else if w = 2 then C' else  D')"
  by word_bitwise auto


definition
  "check X e \<equiv> (if \<not>X then raise'exception (ASSERT e) else return ())" 

lemma check:
  "\<lbrace>\<lambda>s. X \<longrightarrow> exception s \<noteq> NoException\<rbrace>
         check X e
      \<lbrace>\<lambda>_ s. exception s \<noteq> NoException\<rbrace>"
  unfolding check_def
  by wpsimp

lemma
  "\<lbrace>P\<rbrace>
    do {
      x \<leftarrow> f;
      check (X x) e;
     return x }
    \<lbrace>\<lambda>r s.  exception s = NoException \<longrightarrow> Q' r \<rbrace>"
  supply if_split[split del]
  apply (wpsimp wp: vcg_imp check)
  oops



lemma check':
  "\<lbrace>\<lambda>s. MMU_config_assert_isa s \<and> (((ap p \<noteq> 0 \<longrightarrow>  ( if ap p = 1 then ip \<longrightarrow> exception s \<noteq> NoException
             else if ap p = 2 then ((ip \<or> \<not> iw) \<longrightarrow> exception s \<noteq> NoException)
                  else if ap p = 3 then exception s \<noteq> NoException else ap p \<noteq> 4 \<longrightarrow> (if ap p = 5 then ip \<and> \<not> iw \<longrightarrow> exception s \<noteq> NoException else \<not> iw \<longrightarrow> exception s \<noteq> NoException) )) \<longrightarrow> exception s \<noteq> NoException) \<longrightarrow> exception s \<noteq> NoException )\<rbrace>
         CheckPermission (p, va, l, d, iw, ip, f', f'')
      \<lbrace>\<lambda>_ s. exception s \<noteq> NoException\<rbrace>"
  supply if_cong[cong] if_split[split del]
  apply (wpsimp simp: CheckPermission_def)
  apply (clarsimp simp: if_distribR   cong: conj_cong)
  using word_3_cases by fastforce

lemma vcg_imp':
  "\<lbrakk> \<lbrace>\<lambda>s. N' s \<and> (R' s \<longrightarrow> \<not>P s)\<rbrace> f \<lbrace>\<lambda>_ s. \<not>P s\<rbrace>  \<rbrakk> \<Longrightarrow> 
    \<lbrace>\<lambda>s. N' s \<and> (P s \<longrightarrow> R' s \<longrightarrow> Q')\<rbrace> f \<lbrace>\<lambda>_ s. P s \<longrightarrow> Q'\<rbrace>"
  by (smt l3_valid_def)

lemma  CurrentModeIsHyp_wp[wp]:
  "\<lbrace>\<lambda>s. MMU_config_assert_isa s \<and> P False s\<rbrace> CurrentModeIsHyp () \<lbrace>\<lambda>r s. P r s\<rbrace>"
  supply if_cong[cong] if_split[split del] 
  by (wpsimp simp: CurrentModeIsHyp_def BadMode_def HaveSecurityExt_def HaveVirtExt_def ArchVersion_def cong: conj_cong)


lemma MMU_config_writing_access_flag [wp]:
  " \<lbrace>\<lambda>s. MMU_config_assert_isa s \<and> P s\<rbrace> writing_access_flag  (a, b)  \<lbrace>\<lambda>_ s. P s\<rbrace>"
  supply if_cong[cong] if_split[split del] 
  apply (wpsimp simp: writing_access_flag_def write'mem_def if_distribR  Let_def cong: conj_cong)
        apply (wpsimp simp: mem_def mem1_def if_distribR  Let_def cong: conj_cong)
       apply (wpsimp simp: mem_def mem1_def if_distribR  Let_def cong: conj_cong)
      apply (wpsimp simp: mem_def mem1_def if_distribR  Let_def cong: conj_cong)
     apply (wpsimp simp: mem_def mem1_def if_distribR  Let_def cong: conj_cong)
    apply (wpsimp simp: mem_def mem1_def if_distribR  Let_def cong: conj_cong)
   apply (wpsimp simp: mem_def mem1_def if_distribR  Let_def cong: conj_cong)
  by clarsimp


lemma MMU_config_writing_access_first_level_flag [wp]:
  " \<lbrace>\<lambda>s. MMU_config_assert_isa s \<and> P s\<rbrace> writing_access_flag_first_level  (a, b)  \<lbrace>\<lambda>_ s.  P s\<rbrace>"
  supply if_cong[cong] if_split[split del] 
  apply (wpsimp simp: writing_access_flag_first_level_def write'mem_def if_distribR  Let_def cong: conj_cong)
        apply (wpsimp simp: mem_def mem1_def if_distribR  Let_def cong: conj_cong)
       apply (wpsimp simp: mem_def mem1_def if_distribR  Let_def cong: conj_cong)
      apply (wpsimp simp: mem_def mem1_def if_distribR  Let_def cong: conj_cong)
     apply (wpsimp simp: mem_def mem1_def if_distribR  Let_def cong: conj_cong)
    apply (wpsimp simp: mem_def mem1_def if_distribR  Let_def cong: conj_cong)
   apply (wpsimp simp: mem_def mem1_def if_distribR  Let_def cong: conj_cong)
  by clarsimp


lemma IsSecure_wp [wp]:
  "\<lbrace>\<lambda>s. MMU_config_assert_isa s \<and> P True s\<rbrace>  IsSecure ()  \<lbrace>\<lambda>r s.  P r s\<rbrace>"
  supply if_cong[cong] if_split[split del] 
  by (wpsimp simp: IsSecure_def HaveSecurityExt_def HaveVirtExt_def ArchVersion_def if_distribR cong: conj_cong)
 
lemma HaveVirtExt_wp [wp]:
  "\<lbrace>\<lambda>s. MMU_config_assert_isa s \<and> P False s\<rbrace> HaveVirtExt () \<lbrace>\<lambda>r s .  P r s\<rbrace>"
 supply if_cong[cong] if_split[split del] 
  by (wpsimp simp: HaveVirtExt_def ArchVersion_def cong: conj_cong)


lemma HaveMPExt_wp [wp]:
  "\<lbrace>\<lambda>s. MMU_config_assert_isa s \<and> P False s\<rbrace> HaveMPExt () \<lbrace>\<lambda>r s. P r s\<rbrace>"
 supply if_cong[cong] if_split[split del] 
  by (wpsimp simp:  HaveMPExt_def ArchVersion_def cong: conj_cong)

lemma HaveSecurityExt_wp [wp]:
  "\<lbrace>\<lambda>s. MMU_config_assert_isa s \<and> P False s\<rbrace> HaveSecurityExt () \<lbrace>\<lambda>r s. P r s\<rbrace>"
 supply if_cong[cong] if_split[split del] 
  by (wpsimp simp:  HaveSecurityExt_def  cong: conj_cong)

lemma translation_root_wp [wp]:
  "\<lbrace>\<lambda>s. MMU_config_assert_isa s \<and> P 0 False (reg'TTBR0 (TTBR0 (CP15 s))) s\<rbrace> 
       translation_root va \<lbrace>\<lambda>(n, disabled, ttbr) s . P n disabled ttbr s\<rbrace>"
 supply if_cong[cong] if_split[split del] 
  by (wpsimp simp:  translation_root_def  cong: conj_cong)


lemma if_then_strg:
  "Q' s \<and> P s \<longrightarrow> (if rg then \<lambda>s. Q' s \<and> P s else P) s"
  by auto

lemma function_state_weak':
  "(\<And>s0. \<lbrace>\<lambda>s. s = ([], s0) \<and> Q' s \<rbrace> f \<lbrace>\<lambda>_ s. s = g s0 \<rbrace>) \<Longrightarrow> \<lbrace>\<lambda>s. fst s = [] \<and> P () (g (snd s)) \<and> Q' s \<rbrace> f \<lbrace>P\<rbrace>"
  by (clarsimp simp : l3_valid_def)   


definition
  "main_TLB_entries l s = map (main_TLB s o word_of_int o int) [0..<l]"

definition
  "main_TLB_matching_entries l va s =
  rev (filter (\<lambda>e. MatchingEntry (ASID (CONTEXTIDR (CP15 s)), va, e))
     (map the (filter ((\<noteq>) None) (main_TLB_entries l s))))"


definition
  "data_TLB_entries l s = map (micro_DataTLB s o word_of_int o int) [0..<l]"

definition
  "data_TLB_matching_entries l va s =
  rev (filter (\<lambda>e. MatchingEntry (ASID (CONTEXTIDR (CP15 s)), va, e))
     (map the (filter ((\<noteq>) None) (data_TLB_entries l s))))"


lemma main_tlb_no_entry_filter:
  "main_TLB s (word_of_int (int 255)) = None \<Longrightarrow> 
    filter (\<lambda>x. \<exists>ya. main_TLB s (word_of_int (int x)) = Some ya) [0..<256] = filter (\<lambda>x. \<exists>ya. main_TLB s (word_of_int (int x)) = Some ya) [0..<255]"
  apply (simp add: comp_def)
  apply (subgoal_tac "[0..<256] = [0..<255] @ [255]")
   apply (simp only: filter_append)
   apply force
  apply (subgoal_tac "256 = Suc 255")
   apply (simp only: upt_Suc)
  by force+

lemma main_tlb_no_entry_filter_map:
  "main_TLB s 0xFF = None \<Longrightarrow> 
    filter (\<lambda>y. \<exists>ya. y = Some ya) (main_TLB_entries 256 s) = filter (\<lambda>y. \<exists>ya. y = Some ya) (main_TLB_entries 255 s)"
  by (clarsimp simp: main_TLB_entries_def comp_def filter_map main_tlb_no_entry_filter)
 
lemma main_tlb_no_entry_map:
  "main_TLB s 0xFF = None \<Longrightarrow> main_TLB_matching_entries 255 va s = main_TLB_matching_entries 256 va s"
  by (clarsimp simp: main_TLB_matching_entries_def main_tlb_no_entry_filter_map)

lemma filter_map_append:
  "filter f (map f' (filter g (map h [0..<256]))) =
     filter f (map f' (filter g (map h [0..<255]))) @
     filter f (map f' (filter g (map h [255])))"
  apply (subgoal_tac "[0..<256] = [0..<255] @ [255]")
   apply force
  apply (subgoal_tac "256 = Suc 255")
   apply (simp only: upt_Suc)
  by force+

lemma match_entry_head_append:
  "\<lbrakk>MatchingEntry (ASID (CONTEXTIDR (CP15 s)), va, x); main_TLB s 0xFF = Some x\<rbrakk> \<Longrightarrow>
       x # main_TLB_matching_entries 255 va s = main_TLB_matching_entries 256 va s"
  apply (clarsimp simp: main_TLB_matching_entries_def main_TLB_entries_def comp_def)
  apply (simp only: filter_map_append)
  by force


lemma no_match_entry_map:
  "\<lbrakk>\<not>MatchingEntry (ASID (CONTEXTIDR (CP15 s)), va, x); main_TLB s 0xFF = Some x\<rbrakk>  \<Longrightarrow> main_TLB_matching_entries 255 va s = main_TLB_matching_entries 256 va s"
  apply (clarsimp simp: main_TLB_matching_entries_def main_TLB_entries_def comp_def)
  apply (simp only: filter_map_append)
  by force
  

lemma specific_for_loop_wp:
  "\<lbrace> \<lambda>s. s = (main_TLB_matching_entries 0 va (snd s'), snd s') \<and> re = ASID (CONTEXTIDR (CP15 (snd s))) \<rbrace>
        for_loop (0, 255,
               \<lambda>i. do {
                    a \<leftarrow> trim_state (unified_mainTLB (word_of_int (int i)));
                    case a of None \<Rightarrow> return ()
                    | Some e \<Rightarrow>
                        if MatchingEntry (re, va, e) then do {
                 v \<leftarrow> read_state fst;
                 update_state (\<lambda>s. (e # v, snd s))
               } else return ()
             })
   \<lbrace>\<lambda>_ s. s = (main_TLB_matching_entries 256 va (snd s'), snd s') \<rbrace>"
  apply (rule for_loop_wp1[where e=255])
    prefer 3
    apply simp
   apply (wpsimp simp: unified_mainTLB_def)
   apply (simp add: main_TLB_matching_entries_def main_TLB_entries_def)
  apply (wpsimp simp: unified_mainTLB_def)
  by (simp add: main_tlb_no_entry_map match_entry_head_append no_match_entry_map)



lemma specific_main_tlb_for_loop_wp':
  "\<lbrace> \<lambda>s. fst s = [] \<and> P () (main_TLB_matching_entries 256 va (snd s), snd s) \<and> re = ASID (CONTEXTIDR (CP15 (snd s)))\<rbrace>
        for_loop (0, 255,
               \<lambda>i. do {
                    a \<leftarrow> trim_state (unified_mainTLB (word_of_int (int i)));
                    case a of None \<Rightarrow> return ()
                    | Some e \<Rightarrow>
                        if MatchingEntry (re, va, e) then do {
                 v \<leftarrow> read_state fst;
                 update_state (\<lambda>s. (e # v, snd s))
               } else return ()
             })
       \<lbrace>P\<rbrace>"
  supply if_cong[cong] if_split[split del] 
  apply (rule l3_valid_weak_pre)
   apply (rule_tac Q' = "\<lambda>s. re = ASID (CONTEXTIDR (CP15 (snd s)))" in function_state_weak')
   apply (rule l3_valid_weak_pre)
    apply (rule_tac s' = "([],s0)" in  specific_for_loop_wp)
   apply (clarsimp simp: main_TLB_matching_entries_def main_TLB_entries_def)
  by clarsimp


lemma data_tlb_no_entry_filter:
  "micro_DataTLB s (word_of_int (int 31)) = None \<Longrightarrow> 
    filter (\<lambda>x. \<exists>ya. micro_DataTLB s (word_of_int (int x)) = Some ya) [0..<32] = filter (\<lambda>x. \<exists>ya. micro_DataTLB s (word_of_int (int x)) = Some ya) [0..<31]"
  apply (simp add: comp_def)
  apply (subgoal_tac "[0..<32] = [0..<31] @ [31]")
   apply (simp only: filter_append)
   apply force
  apply (subgoal_tac "32 = Suc 31")
   apply (simp only: upt_Suc)
  by force+

lemma data_tlb_no_entry_filter_map:
  "micro_DataTLB s 0x1F = None \<Longrightarrow> 
    filter (\<lambda>y. \<exists>ya. y = Some ya) (data_TLB_entries 32s) = filter (\<lambda>y. \<exists>ya. y = Some ya) (data_TLB_entries 31 s)"
  by (clarsimp simp: data_TLB_entries_def comp_def filter_map data_tlb_no_entry_filter)


lemma data_tlb_no_entry_map:
  "micro_DataTLB s 0x1F = None \<Longrightarrow> data_TLB_matching_entries 31 va s = data_TLB_matching_entries 32 va s"
  by (clarsimp simp: data_TLB_matching_entries_def data_tlb_no_entry_filter_map)

lemma filter_map_append':
  "filter f (map f' (filter g (map h [0..<32]))) =
     filter f (map f' (filter g (map h [0..<31]))) @
     filter f (map f' (filter g (map h [31])))"
  apply (subgoal_tac "[0..<32] = [0..<31] @ [31]")
   apply force
  apply (subgoal_tac "32 = Suc 31")
   apply (simp only: upt_Suc)
  by force+

lemma match_entry_head_append':
  "\<lbrakk>MatchingEntry (ASID (CONTEXTIDR (CP15 s)), va, x); micro_DataTLB s 0x1F = Some x\<rbrakk> \<Longrightarrow>
       x # data_TLB_matching_entries 31 va s = data_TLB_matching_entries 32 va s"
  apply (clarsimp simp: data_TLB_matching_entries_def data_TLB_entries_def comp_def)
  apply (simp only: filter_map_append')
  by force

lemma no_match_entry_map':
  "\<lbrakk>\<not>MatchingEntry (ASID (CONTEXTIDR (CP15 s)), va, x); micro_DataTLB s 0x1F = Some x\<rbrakk>  \<Longrightarrow> data_TLB_matching_entries 31 va s = data_TLB_matching_entries 32 va s"
  apply (clarsimp simp: data_TLB_matching_entries_def data_TLB_entries_def comp_def)
  apply (simp only: filter_map_append')
  by force

lemma specific_data_tlb_for_loop_wp:
  "\<lbrace> \<lambda>s. s = (data_TLB_matching_entries 0 va (snd s'), snd s') \<and> re = ASID (CONTEXTIDR (CP15 (snd s))) \<rbrace>
         for_loop (0, 31,
                  \<lambda>i. do {
                       a \<leftarrow> trim_state (DataTLB (word_of_int (int i)));
                       case a of None \<Rightarrow> return () | Some e \<Rightarrow> if MatchingEntry (re, va, e) then do {
                        v \<leftarrow> read_state fst;
                         update_state (\<lambda>s. (e # v, snd s))}
                     else return ()
                     })
   \<lbrace>\<lambda>_ s. s = (data_TLB_matching_entries 32 va (snd s'), snd s') \<rbrace>"
   apply (rule for_loop_wp1[where e=31])
    prefer 3
    apply simp
   apply (wpsimp simp: DataTLB_def)
   apply (simp add: data_TLB_matching_entries_def data_TLB_entries_def)
  apply (wpsimp simp: DataTLB_def)
  by (simp add: data_tlb_no_entry_map match_entry_head_append' no_match_entry_map')



lemma specific_data_tlb_for_loop_wp':
  " \<lbrace>\<lambda>s. fst s = [] \<and> P () (data_TLB_matching_entries 32 va (snd s), snd s) \<and> re = ASID (CONTEXTIDR (CP15 (snd s)))\<rbrace> 
          for_loop
                 (0, 31,
                  \<lambda>i. do {
                       a \<leftarrow> trim_state (DataTLB (word_of_int (int i)));
                       case a of None \<Rightarrow> return () | Some e \<Rightarrow> if MatchingEntry (re, va, e) then do {
                        v \<leftarrow> read_state fst;
                         update_state (\<lambda>s. (e # v, snd s))}
                     else return ()
                     })
    \<lbrace>P\<rbrace>"
  supply if_cong[cong] if_split[split del] 
  apply (rule l3_valid_weak_pre)
   apply (rule_tac Q' = "\<lambda>s. re = ASID (CONTEXTIDR (CP15 (snd s)))" in function_state_weak')
   apply (rule l3_valid_weak_pre)
    apply (rule_tac s' = "([],s0)" in  specific_data_tlb_for_loop_wp)
    apply (clarsimp simp: data_TLB_matching_entries_def data_TLB_entries_def)
  by clarsimp


definition
  "TLB_entries_gen l (tlb :: 'a::len0 word \<Rightarrow> TLBEntry option) = 
      map (tlb o word_of_int o int) [0..<l]"


(* for i=0, we get the same tlb back, and for i = 255 we get the last state of tlb eviction,   *)

definition 
  "main_tlb_eviction i tlb =
      take (256 - i) (TLB_entries_gen 256 tlb) @ drop (255 - i) (butlast (TLB_entries_gen 256 tlb))"


definition
  from_list_to_tlb_map :: "TLBEntry option list \<Rightarrow> 'a::len0 word \<Rightarrow> TLBEntry option"
where
  "from_list_to_tlb_map tlb = (\<lambda>w. tlb ! unat w)"


lemma  to_do:
   "\<lbrace> \<lambda>s. P () (s\<lparr>main_TLB := from_list_to_tlb_map (main_tlb_eviction 255 (main_TLB s))\<rparr>) \<rbrace>
       for_loop
           (0, 254,
              \<lambda>i. do {
                 v \<leftarrow> do {
                     v \<leftarrow> read_state main_TLB;
                     return (v (word_of_int (int (254 - i))))
                   };
                 va \<leftarrow> read_state main_TLB;
                 update_state (main_TLB_update (\<lambda>_ b. if b = word_of_int (int (255 - i)) then v else va b))
               })  \<lbrace>P\<rbrace>"
  
  sorry


definition 
  "data_tlb_eviction i tlb =
      take (32 - i) (TLB_entries_gen 32 tlb) @ drop (31 - i) (butlast (TLB_entries_gen 32 tlb))"


lemma  to_do1:
   "\<lbrace> \<lambda>s. P () (s\<lparr>micro_DataTLB := from_list_to_tlb_map (data_tlb_eviction 31 (micro_DataTLB s))\<rparr>) \<rbrace>
      for_loop (0, 30, \<lambda>i. do {
                                     v \<leftarrow> do {
                                         v \<leftarrow> read_state micro_DataTLB;
                                         return (v (word_of_int (int (30 - i))))
                                       };
                                     va \<leftarrow> read_state micro_DataTLB;
                                     update_state (micro_DataTLB_update (\<lambda>_ b. if b = word_of_int (int (31 - i)) then v else va b))
                                   }) \<lbrace>P\<rbrace>"
  
  sorry

definition 
  "inst_tlb_eviction i tlb =
      take (64 - i) (TLB_entries_gen 64 tlb) @ drop (63 - i) (butlast (TLB_entries_gen 64 tlb))"

lemma  to_do2:
   "\<lbrace> \<lambda>s. P () (s\<lparr>micro_InstrTLB := from_list_to_tlb_map (inst_tlb_eviction 63 (micro_InstrTLB s))\<rparr>) \<rbrace>
     for_loop
                       (0, 62,
                        \<lambda>i. do {
                             v \<leftarrow> do {
                                 v \<leftarrow> read_state micro_InstrTLB;
                                 return (v (word_of_int (int (62 - i))))
                               };
                             va \<leftarrow> read_state micro_InstrTLB;
                             update_state
                              (micro_InstrTLB_update (\<lambda>_. va(word_of_int (int (63 - i)) := v)))
                           })   \<lbrace>P\<rbrace>"
  
  sorry
 
lemma  to_do2':
   "\<lbrace> \<lambda>s. P () (s\<lparr>micro_InstrTLB := from_list_to_tlb_map (inst_tlb_eviction 63 (micro_InstrTLB s))\<rparr>) \<rbrace>
     for_loop
                       (0, 62,
                        \<lambda>i. do {
                             v \<leftarrow> do {
                                 v \<leftarrow> read_state micro_InstrTLB;
                                 return (v (word_of_int (int (62 - i))))
                               };
                             va \<leftarrow> read_state micro_InstrTLB;
                             update_state
                              (micro_InstrTLB_update (\<lambda>_ b. if b = word_of_int (int (63 - i)) then v else va b))
                           })   \<lbrace>P\<rbrace>"
  
  sorry

lemma[simp]: 
  "data_TLB_matching_entries 32 va (s\<lparr>micro_InstrTLB := tlb, micro_DataTLB := tlb', main_TLB := tlb''\<rparr>) = 
                    data_TLB_matching_entries 32 va (s\<lparr> micro_DataTLB := tlb'\<rparr>)" 
  by (clarsimp simp: data_TLB_matching_entries_def data_TLB_entries_def)

lemma [simp]: 
  "main_TLB_matching_entries 256 va (s\<lparr>micro_InstrTLB := tlb, micro_DataTLB := tlb',  main_TLB :=tlb''\<rparr>) =
                  main_TLB_matching_entries 256 va (s\<lparr>main_TLB :=tlb''\<rparr>)" 
  by (clarsimp simp: main_TLB_matching_entries_def main_TLB_entries_def)

lemma [simp]:
  "data_TLB_matching_entries 32 va (s\<lparr>micro_InstrTLB := tlb, micro_DataTLB := tlb'\<rparr>) =
                 data_TLB_matching_entries 32 va (s\<lparr>micro_DataTLB := tlb'\<rparr>)"
  by (clarsimp simp: data_TLB_matching_entries_def data_TLB_entries_def)


lemma tlb_rel_evicted_hit:
  "\<lbrakk>tlb_rel s (typ_tlb t); dtlb_consistent (typ_tlb t) (Addr va);
        lookup (tlbtypcast ` ran (\<lambda>a. if a = 0 then None else from_list_to_tlb_map (data_tlb_eviction 31 (micro_DataTLB s)) a))
         (ASID (CONTEXTIDR (CP15 s))) va = TLB.lookup_type.Hit (tlbtypcast x)\<rbrakk>
       \<Longrightarrow> lookup (tlbtypcast ` ran (micro_DataTLB s)) (ASID (CONTEXTIDR (CP15 s))) va =
           TLB.lookup_type.Hit (tlbtypcast x)"
  apply (subgoal_tac "tlbtypcast ` ran (\<lambda>a. if a = 0 then None else from_list_to_tlb_map (data_tlb_eviction 31 (micro_DataTLB s)) a) \<subseteq>
                                         tlbtypcast ` ran (micro_DataTLB s)")
  prefer 2
  sorry


lemma [simp]:
  "unat (flags_t.domain (flags (tlbtypcast entry))) = nat (uint (domain_entry entry)) "
  by (cases entry; clarsimp simp: unat_def domain_entry_def)

lemma [simp]:
  "accessperm (permissions (flags (tlbtypcast entry))) = ap (perms_entry entry)"
  by (cases entry; clarsimp simp: perms_entry_def perm_typcast_def)

lemma [simp]:
  "MMU_config_assert_isa (s\<lparr>micro_InstrTLB := a, micro_DataTLB := b\<rparr>) = MMU_config_assert_isa s "
  by (simp only: MMU_config_assert_isa_def, case_tac s, force)

lemma [simp]:
  "MMU_config_assert_isa (s\<lparr>micro_InstrTLB := a\<rparr>) = MMU_config_assert_isa s "
  by (simp only: MMU_config_assert_isa_def, case_tac s, force)

lemma [simp]:
  "MMU_config_assert_isa (s\<lparr>micro_DataTLB := a\<rparr>) = MMU_config_assert_isa s "
  by (simp only: MMU_config_assert_isa_def, case_tac s, force)

lemma [simp]:
  "MMU_config_assert_isa (s\<lparr>micro_InstrTLB := a, micro_DataTLB := b, micro_DataTLB := c\<rparr>) = MMU_config_assert_isa s "
  by (simp only: MMU_config_assert_isa_def, case_tac s, force)

lemma filter_single_elem:
  "filter P lst = [x] \<Longrightarrow> P x \<and> (\<forall>y\<in>set lst. y\<noteq>x \<longrightarrow> \<not>P y)"
  by (smt Cons_eq_filterD filter_empty_conv filter_set member_filter set_ConsD)

lemma filter_elem_member:
  "filter P lst = [x] \<Longrightarrow> x\<in>set lst"
  by (metis filter_set list.set_intros(1) member_filter)

lemma filter_elem_pass:
  "filter P lst = [x] \<Longrightarrow> P x"
  by (meson filter_eq_ConsD)

lemma five_word_lt_32:
  "nat (uint (a::5 word)) < 32"
  apply (cases a, clarsimp simp: of_nat_def)
  apply word_bitwise 
  apply (clarsimp simp: )
  sorry

lemma eight_word_lt_256:
  "nat (uint (a::8 word)) < 256"
  apply (cases a, clarsimp simp: of_nat_def)
  apply word_bitwise 
  apply (clarsimp simp: )
  sorry

lemma entry_range_tags_MatchingEntry_rel:
  "(None, va) \<in> entry_range_tags (tlbtypcast x) \<Longrightarrow> MatchingEntry (ASID (CONTEXTIDR (CP15 s)), va, x)"
  apply (clarsimp simp: entry_range_tags_def entry_range_def MatchingEntry_def)
  apply (cases x; clarsimp)
  sorry


lemma entry_range_tags_MatchingEntry_rel':
  "(Some (ASID (CONTEXTIDR (CP15 s))), va) \<in> entry_range_tags (tlbtypcast x) \<Longrightarrow> MatchingEntry (ASID (CONTEXTIDR (CP15 s)), va, x)"
  apply (clarsimp simp: entry_range_tags_def entry_range_def MatchingEntry_def)
  apply (cases x; clarsimp)
  apply safe
  sorry


lemma data_TLB_matching_entries_lookup_equal:
  "\<lbrakk>data_TLB_matching_entries 32 va s = [entry]\<rbrakk>  \<Longrightarrow>
    lookup (tlbtypcast ` ran (micro_DataTLB s)) (ASID (CONTEXTIDR (CP15 s))) va = TLB.lookup_type.Hit (tlbtypcast entry)"
  apply (subgoal_tac "entry_set (tlbtypcast ` ran (micro_DataTLB s)) (ASID (CONTEXTIDR (CP15 s))) va = {tlbtypcast entry}")
   apply (clarsimp simp: lookup_def)
  apply (clarsimp simp: entry_set_def Compr_image_eq)
  apply (subgoal_tac " {E \<in> ran (micro_DataTLB s). \<exists>a'. (a', va) \<in> entry_range_tags (tlbtypcast E) \<and> (a' = None \<or> a' = Some (ASID (CONTEXTIDR (CP15 s))))} = {entry}")
   apply force
  apply (safe ; clarsimp simp: data_TLB_matching_entries_def data_TLB_entries_def comp_def ran_def)
     apply (drule filter_single_elem, clarsimp)
     apply (case_tac "x = entry"; clarsimp)
     apply (drule_tac x = "Some x" in spec)
     apply (clarsimp)
     apply (subgoal_tac "Some x \<in> (\<lambda>x. micro_DataTLB s (word_of_int (int x))) ` {0..<32}")
      prefer 2
      apply (rule_tac x = "unat a" in image_eqI)
       apply (clarsimp simp: unat_def)
      apply (clarsimp simp: unat_def five_word_lt_32) 
     apply (force simp: entry_range_tags_MatchingEntry_rel)
    apply (drule filter_single_elem, clarsimp)
    apply (case_tac "x = entry"; clarsimp)
    apply (drule_tac x = "Some x" in spec)
    apply (clarsimp)
    apply (subgoal_tac "Some x \<in> (\<lambda>x. micro_DataTLB s (word_of_int (int x))) ` {0..<32}")
     prefer 2
     apply (rule_tac x = "unat a" in image_eqI)
      apply (clarsimp simp: unat_def)
     apply (clarsimp simp: unat_def five_word_lt_32)
    apply clarsimp 
    apply (force simp: entry_range_tags_MatchingEntry_rel')
   apply (drule filter_elem_member)
   apply force
  apply (drule filter_elem_pass)   
  apply (clarsimp simp: MatchingEntry_def)
  apply (cases entry; clarsimp)
     apply (rule_tac x = "EntryLarge_t.tag x1" in exI, clarsimp simp: entry_range_tags_def entry_range_def split: if_split_asm)
      apply (rule imageI)
      defer
      apply (rule imageI)
      defer
      apply (rule_tac x = "EntrySection_t.tag x2" in exI, clarsimp simp: entry_range_tags_def entry_range_def split: if_split_asm)
       apply (rule imageI)
       defer
       apply (rule imageI)
       defer
       apply (rule_tac x = "EntrySmall_t.tag x3" in exI, clarsimp simp: entry_range_tags_def entry_range_def split: if_split_asm)
        apply (rule imageI)
        defer
        apply (rule imageI)
        defer
        apply (rule_tac x = "EntrySuper_t.tag x4" in exI, clarsimp simp: entry_range_tags_def entry_range_def split: if_split_asm)
         apply (rule imageI)
         defer
         apply (rule imageI)
         defer
   
  sorry

lemma [simp]:
  "main_TLB_matching_entries 256 va (s\<lparr>micro_InstrTLB := from_list_to_tlb_map (inst_tlb_eviction 63 (micro_InstrTLB s)), main_TLB := \<lambda>a. if a = 0 then None else from_list_to_tlb_map (main_tlb_eviction 255 (main_TLB s)) a\<rparr>) =
      main_TLB_matching_entries 256 va (s\<lparr> main_TLB := \<lambda>a. if a = 0 then None else from_list_to_tlb_map (main_tlb_eviction 255 (main_TLB s)) a\<rparr>)  "
  by (clarsimp simp: main_TLB_matching_entries_def main_TLB_entries_def)
  
  
lemma main_TLB_matching_entries_lookup_equal:
  "\<lbrakk>main_TLB_matching_entries 256 va s = [entry]\<rbrakk>  \<Longrightarrow>
    lookup (tlbtypcast ` ran (main_TLB s)) (ASID (CONTEXTIDR (CP15 s))) va = TLB.lookup_type.Hit (tlbtypcast entry)"
  apply (subgoal_tac "entry_set (tlbtypcast ` ran (main_TLB s)) (ASID (CONTEXTIDR (CP15 s))) va = {tlbtypcast entry}")
   apply (clarsimp simp: lookup_def)
  apply (clarsimp simp: entry_set_def Compr_image_eq)
  apply (subgoal_tac " {E \<in> ran (main_TLB s). \<exists>a'. (a', va) \<in> entry_range_tags (tlbtypcast E) \<and> (a' = None \<or> a' = Some (ASID (CONTEXTIDR (CP15 s))))} = {entry}")
   apply force
  apply (safe ; clarsimp simp: main_TLB_matching_entries_def main_TLB_entries_def comp_def ran_def)
     apply (drule filter_single_elem, clarsimp)
     apply (case_tac "x = entry"; clarsimp)
     apply (drule_tac x = "Some x" in spec)
     apply (clarsimp)
     apply (subgoal_tac "Some x \<in> (\<lambda>x. main_TLB s (word_of_int (int x))) ` {0..<256}")
      prefer 2
      apply (rule_tac x = "unat a" in image_eqI)
       apply (clarsimp simp: unat_def)
      apply (clarsimp simp: unat_def eight_word_lt_256) 
     apply (force simp: entry_range_tags_MatchingEntry_rel)
    apply (drule filter_single_elem, clarsimp)
    apply (case_tac "x = entry"; clarsimp)
    apply (drule_tac x = "Some x" in spec)
    apply (clarsimp)
    apply (subgoal_tac "Some x \<in> (\<lambda>x. main_TLB s (word_of_int (int x))) ` {0..<256}")
     prefer 2
     apply (rule_tac x = "unat a" in image_eqI)
      apply (clarsimp simp: unat_def)
     apply (clarsimp simp: unat_def eight_word_lt_256)
    apply clarsimp 
    apply (force simp: entry_range_tags_MatchingEntry_rel')
   apply (drule filter_elem_member)
   apply force
  apply (drule filter_elem_pass)   
  apply (clarsimp simp: MatchingEntry_def)
  apply (cases entry; clarsimp)
     apply (rule_tac x = "EntryLarge_t.tag x1" in exI, clarsimp simp: entry_range_tags_def entry_range_def split: if_split_asm)
      apply (rule imageI)
      defer
      apply (rule imageI)
      defer
      apply (rule_tac x = "EntrySection_t.tag x2" in exI, clarsimp simp: entry_range_tags_def entry_range_def split: if_split_asm)
       apply (rule imageI)
       defer
       apply (rule imageI)
       defer
       apply (rule_tac x = "EntrySmall_t.tag x3" in exI, clarsimp simp: entry_range_tags_def entry_range_def split: if_split_asm)
        apply (rule imageI)
        defer
        apply (rule imageI)
        defer
        apply (rule_tac x = "EntrySuper_t.tag x4" in exI, clarsimp simp: entry_range_tags_def entry_range_def split: if_split_asm)
         apply (rule imageI)
         defer
         apply (rule imageI)
         defer

  sorry


lemma tlb_rel_evicted_hit_main_tlb:
  "\<lbrakk>tlb_rel s (typ_tlb t); unitlb_consistent (typ_tlb t) (Addr va);
        lookup (tlbtypcast ` ran (\<lambda>a. if a = 0 then None else from_list_to_tlb_map (main_tlb_eviction 255 (main_TLB s)) a)) (ASID (CONTEXTIDR (CP15 s))) va = TLB.lookup_type.Hit (tlbtypcast x)\<rbrakk>
       \<Longrightarrow> lookup (tlbtypcast ` ran (main_TLB s)) (ASID (CONTEXTIDR (CP15 s))) va =  TLB.lookup_type.Hit (tlbtypcast x)"
 
  sorry

lemma tlb_rel_consistent_lookup_hit_main_tlb:
  "\<lbrakk>tlb_rel s (typ_tlb (t :: 'a tlb_state_scheme)); unitlb_consistent (typ_tlb t) (Addr va);
        lookup (tlbtypcast ` ran (main_TLB s)) (ASID (CONTEXTIDR (CP15 s))) va = TLB.lookup_type.Hit x\<rbrakk>
       \<Longrightarrow> lookup (unitlb_set (tlbs_set t)) (asid t) va = TLB.lookup_type.Hit x"
  apply (drule tlb_relD, clarsimp simp: typ_tlb_def cstate.defs)
  apply (clarsimp simp: consistent0_def ran_def)
  by (metis Hits_le TLB.lookup_type.simps(5) leq_Miss option.sel tlb_mono)




lemma mmu_translate_refinement_pa [wp]:
  "\<lbrace>\<lambda>s. \<exists>t mematr . MMU_config_assert_isa s \<and>
                 tlb_rel s (typ_tlb t) \<and>
                 dtlb_consistent (typ_tlb t) (Addr va) \<and>
                 unitlb_consistent (typ_tlb t) (Addr va) \<and>
                 mmu_translate  (Addr va) siz ispriv iswrite True (t :: 'a tlb_state_scheme) = ((pa', mematr), t')\<rbrace>
       TranslateAddress (va, ispriv, iswrite, siz, True) 
   \<lbrace>\<lambda>r s. exception s = NoException \<longrightarrow> pa' = Addr (paddress r)\<rbrace>"
  supply if_cong[cong] if_split[split del] translation_mmu_config [wp del]
  apply (wpsimp simp: TranslateAddress_def if_distribR  cong: conj_cong)
            apply (rule vcg_imp')
            apply (rule check')
           apply wpsimp
          apply (clarsimp simp:  if_distribR  cong: conj_cong)  
          apply (wpsimp simp: CheckDomain_def)
         apply wpsimp
        apply wpsimp
               apply (rule vcg_imp')
               apply (rule check')
              apply wpsimp
             apply (clarsimp simp: if_distribR  cong: conj_cong)  
             apply (wpsimp simp: CheckDomain_def)
            apply (clarsimp simp: if_distribR  cong: conj_cong)
            apply (wpsimp simp: write'DataTLB_def)
           apply wpsimp
          apply wpsimp
              apply (wpsimp simp: write'unified_mainTLB_def)
             apply wpsimp
            apply wpsimp
            apply (wpsimp simp: write'DataTLB_def)
           apply wpsimp
          apply wpsimp 
          apply (wpsimp simp: TranslateAddressV_def)
                   apply (rule vcg_imp')
                   apply (rule check')
                  apply (clarsimp simp: if_distribR  Let_def cong: conj_cong)
                  apply wpsimp
                 apply wpsimp 
                apply (clarsimp simp: if_distribR  Let_def cong: conj_cong)
                apply (wpsimp simp: CheckDomain_def)
               apply wpsimp
              apply wpsimp
             apply (clarsimp simp: if_distribR  Let_def cong: conj_cong)
             apply wpsimp
            apply (clarsimp simp: if_distribR  Let_def cong: conj_cong)
            apply wpsimp
              prefer 2
              apply (rule false_imp_post)
             apply (clarsimp simp: TranslationTableWalkSD_def Let_def)
             apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
              apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
               apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                 apply (wp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                   apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                    apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                     apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                      apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                      apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                       apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                        apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                         apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                          apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                           apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                            apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                             apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                            apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                           apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                          apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                         apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                        apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                       apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                        apply (rule well_formed_state)
                        apply (clarsimp simp: if_distribR  Let_def cong: conj_cong)
                        apply (wpsimp simp: TLBRMemAtrbts_def)
                        apply (clarsimp simp: RemappedTEXDecode_def if_distribR  Let_def cong: conj_cong)
                        apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                        apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                        apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                         apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                          apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                         apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                          apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                         apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                          apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                           apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                            apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                           apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                            apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                           apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                            apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                             apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                              apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                               apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                 apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                  apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                   apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                    apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                     apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                      apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                       apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                        apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                         apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                          apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                           apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                           apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                            apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                             apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                              apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                             apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                            apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                           apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                          apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                         apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                        apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                       apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                      apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                     apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                    apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                   apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                  apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                 apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                               apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                              apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                             apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                            apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                           apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                          apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                         apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                        apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                       apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                      apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                     apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                     apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                      apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                       apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                        apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                         apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                          apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                           apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                            apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                             apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)  
                              apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                               apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                              apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                             apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                            apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                           apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                          apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                         apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                        apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                       apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                      apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                       apply (wpsimp simp: TLBRMemAtrbts_def)
                       apply (clarsimp simp: RemappedTEXDecode_def if_distribR  Let_def cong: conj_cong)
                       apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                       apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                       apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                        apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                         apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                        apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                         apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                        apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                         apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                          apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                           apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                          apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                           apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                          apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                           apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                            apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                             apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                              apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                               apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                               apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                 apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                  apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                   apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                    apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                     apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                      apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                       apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                        apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                         apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                          apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                          apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                           apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                            apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                             apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                            apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                           apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                          apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                         apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                        apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                       apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                      apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                     apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                    apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                   apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                  apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                 apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                               apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                              apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                             apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                            apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                           apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                          apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                         apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                        apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                       apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                      apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                     apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                    apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                   apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                  apply (wpsimp simp: level2_desc_address_and_desc_def if_distribR  Let_def BigEndianReverse_def mem_def cong: conj_cong)
                               apply (wpsimp simp: mem1_def  if_distribR  Let_def cong: conj_cong)  apply clarsimp
                              apply (wpsimp simp: mem1_def  if_distribR  Let_def cong: conj_cong)  apply clarsimp
                             apply (wpsimp simp: mem1_def  if_distribR  Let_def cong: conj_cong)  apply clarsimp
                            apply (wpsimp simp: mem1_def  if_distribR  Let_def cong: conj_cong)  apply clarsimp
                           apply wpsimp
                          apply wpsimp
                         apply wpsimp
                        apply wpsimp
                           apply (wpsimp simp:  if_distribR  Let_def cong: conj_cong)  
                           apply (wpsimp simp: mem1_def  if_distribR  Let_def cong: conj_cong)  apply clarsimp
                          apply (wpsimp simp: mem1_def  if_distribR  Let_def cong: conj_cong)  apply clarsimp
                         apply (wpsimp simp: mem1_def  if_distribR  Let_def cong: conj_cong)  apply clarsimp
                        apply (wpsimp simp: mem1_def  if_distribR  Let_def cong: conj_cong)  apply clarsimp
                       apply wpsimp
                         apply (rule false_imp_post)
                        apply wpsimp
                       apply wpsimp
                      apply (clarsimp simp: if_distribR  cong: conj_cong)
                      apply wpsimp
                     apply wpsimp
                    apply wpsimp
                   apply wpsimp
                  apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                 apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                  apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                   apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                    apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                    apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                     apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                      apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                       apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                        apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                         apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                          apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                         apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                        apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                       apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                      apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                     apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                      apply (wpsimp simp: TLBRMemAtrbts_def)
                      apply (clarsimp simp: RemappedTEXDecode_def if_distribR  Let_def cong: conj_cong)
                      apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                      apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                      apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                       apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                        apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                       apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                        apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                       apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                        apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                         apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                          apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                         apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                          apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                         apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                          apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                           apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                            apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                             apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                              apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                              apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                               apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                 apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                  apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                   apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                    apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                     apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                      apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                       apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                        apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                         apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                         apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                          apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                           apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                            apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                           apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                          apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                         apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                        apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                       apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                      apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                     apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                    apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                   apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                  apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                 apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                               apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                              apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                             apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                            apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                           apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                          apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                         apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                        apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                       apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                      apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                     apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                    apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                   apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                   apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                    apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                     apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                      apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                       apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                        apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                         apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                        apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                       apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                      apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                     apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                    apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                     apply (wpsimp simp: TLBRMemAtrbts_def)
                     apply (clarsimp simp: RemappedTEXDecode_def if_distribR  Let_def cong: conj_cong)
                     apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                     apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                     apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                      apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                       apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                      apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                       apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                      apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                       apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                        apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                         apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                        apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                         apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                        apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                         apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                          apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                           apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                            apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                             apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                             apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                              apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                               apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                 apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                  apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                   apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                    apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                     apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                      apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                       apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                        apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                        apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                         apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                          apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                           apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                          apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                         apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                        apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                       apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                      apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                     apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                    apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                   apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                  apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                 apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                               apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                              apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                             apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                            apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                           apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                          apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                         apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                        apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                       apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                      apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                     apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                    apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                   apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                  apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                 apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                apply (wpsimp, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                 apply (clarsimp simp: level1_desc_address_and_desc_def if_distribR  Let_def BigEndianReverse_def mem_def cong: conj_cong)
                apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                 apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                  apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                   apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                    apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                     apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                      apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                       apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                        apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                         apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                          apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                           apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                            apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                             apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                              apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                               apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                 apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                  apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                   apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                    apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                     apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                      apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                       apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                      apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                       apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                      apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                     apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                    apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                   apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                    apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                     apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                      apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                     apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                      apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                     apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                      apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                      apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                      apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                      apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                      apply (rule false_imp_post)
                                     apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                      apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                     apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                     apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                     apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                     apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                     apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                      apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                       apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                      apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                       apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                        apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                       apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                        apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                         apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                        apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                         apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                                        apply (wpsimp simp: mem1_def  if_distribR  Let_def cong: conj_cong)  apply clarsimp
                                       apply (wpsimp simp: mem1_def  if_distribR  Let_def cong: conj_cong)  apply clarsimp
                                      apply (wpsimp simp: mem1_def  if_distribR  Let_def cong: conj_cong)  apply clarsimp
                                     apply (wpsimp simp: mem1_def  if_distribR  Let_def cong: conj_cong)  apply clarsimp
                                    apply wpsimp
                                   apply wpsimp
                                  apply wpsimp
                                 apply wpsimp
                                    apply (wpsimp simp:  if_distribR  Let_def cong: conj_cong)  
                                    apply (wpsimp simp: mem1_def  if_distribR  Let_def cong: conj_cong)  apply clarsimp
                                   apply (wpsimp simp: mem1_def  if_distribR  Let_def cong: conj_cong)  apply clarsimp
                                  apply (wpsimp simp: mem1_def  if_distribR  Let_def cong: conj_cong)  apply clarsimp
                                 apply (wpsimp simp: mem1_def  if_distribR  Let_def cong: conj_cong)  apply clarsimp
                                apply wpsimp
                               apply (wpsimp simp:  if_distribR  Let_def cong: conj_cong)   apply (clarsimp simp: if_distribR  Let_def cong: conj_cong)?
                                 apply (clarsimp simp: if_distribR  Let_def cong: conj_cong)?
                                 apply (rule false_imp_post)
                                apply (wpsimp simp: if_distribR Let_def cong: conj_cong)
                               apply (wpsimp simp: if_distribR Let_def cong: conj_cong)
                              apply (wpsimp simp: if_distribR Let_def cong: conj_cong)
                             apply (clarsimp simp: if_distribR  Let_def cong: conj_cong)
                             apply wpsimp
                            apply (wpsimp simp: if_distribR Let_def cong: conj_cong)
                           apply (clarsimp simp: if_distribR  cong: conj_cong) 
                           apply wpsimp
                          apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?) 
                         apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?) 
                          apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?) 
                           apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?) 
                          apply (wpsimp simp: if_distribR Let_def cong: conj_cong)
                         apply (clarsimp simp: if_distribR  cong: conj_cong) 
                         apply wpsimp
                        apply wpsimp
                       apply wpsimp
                      apply wpsimp
                     apply wpsimp
                    apply wpsimp
                   apply (clarsimp simp: if_distribR  Let_def cong: conj_cong)
                   apply wpsimp
                  apply wpsimp 
                 apply wpsimp
                apply (clarsimp simp: if_distribR  Let_def cong: conj_cong)
                apply wpsimp
               apply wpsimp
              apply wpsimp
             apply (clarsimp simp: if_distribR  Let_def cong: conj_cong)
             apply (clarsimp simp: translation_root_def if_distribR Let_def cong: conj_cong)
             apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?) 
              apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?) 
               apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?) 
                apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?) 
                 apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?) 
                  apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?) 
                   apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?) 
                  apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?) 
                   apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?) 
                  apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?) 
                 apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?) 
                apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?) 
               apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?) 
                apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?) 
                 apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?) 
                apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?) 
                 apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?) 
                apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?) 
               apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?) 
              apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?) 
               apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?) 
              apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?) 
               apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?) 
                apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?) 
               apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?) 
                 apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?) 
                apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?) 
                 apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?) 
                  apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?) 
                 apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?) 
                  apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?) 
                   apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?) 
                  apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?) 
                   apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?) 
                    apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?) 
                   apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?) 
                    apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
                     apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?) 
                    apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?) 
                     apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?) 
                    apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?) 
                   apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?) 
                  apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?) 
                 apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?) 
                apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?) 
               apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?) 
              apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?) 
             apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?) 
            apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?) 
             apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
              apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?) 
             apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?) 
              apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?) 
               apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?) 
                apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?) 
               apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?) 
              apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?) 
             apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?) 
            apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?) 
             apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?) 
              apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?) 
             apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?) 
            apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?)
           apply (wp_once, (clarsimp simp: if_distribR  Let_def cong: conj_cong)?) 
          apply (wpsimp simp: FCSETranslate_def)
         apply (wpsimp simp: lookupTLB_main_def entry_list_main_def mainTLBEntries_def)
         apply (rule_tac specific_main_tlb_for_loop_wp') 
        apply wpsimp
       apply (clarsimp simp: if_distribR Let_def cong: conj_cong)
       apply (wpsimp simp: lookupTLB_Data_micro_def entry_list_data_micro_def microDataTLBEntries_def)
       apply (rule_tac specific_data_tlb_for_loop_wp') 
      apply wpsimp
     apply (clarsimp simp: if_distribR Let_def cong: conj_cong)
     apply (wpsimp simp: mainTLB_evict_def mainTLBEntries_def write'unified_mainTLB_def unified_mainTLB_def)
     apply (rule to_do, clarsimp) 
    apply (wpsimp simp: write'DataTLB_def microDataTLB_evict_def microDataTLBEntries_def DataTLB_def)
    apply (rule to_do1, clarsimp)
   apply (wpsimp simp: microInstrTLB_evict_def microInstrTLBEntries_def write'InstrTLB_def InstrTLB_def)
   apply (rule to_do2)
(*  proof coming out of the wp *)
  apply (clarsimp simp: if_distribR Let_def cong: conj_cong)
  apply (rule conjI; clarsimp)
   apply (case_tac "data_TLB_matching_entries 32 va (s\<lparr>micro_DataTLB :=  \<lambda>a. if a = 0 then None else from_list_to_tlb_map (data_tlb_eviction 31 (micro_DataTLB s)) a\<rparr>)"; clarsimp)
   apply (case_tac list; clarsimp)
   apply (rename_tac entry)
   apply (subgoal_tac "lookup (tlbtypcast ` ran (micro_DataTLB  (s\<lparr>micro_DataTLB := \<lambda>a. if a = 0 then None else from_list_to_tlb_map (data_tlb_eviction 31 (micro_DataTLB s)) a\<rparr>))) (ASID (CONTEXTIDR (CP15 s))) va = TLB.lookup_type.Hit (tlbtypcast entry) ")
    prefer 2
    apply (drule data_TLB_matching_entries_lookup_equal) 
    apply (case_tac s, clarsimp)
   apply clarsimp
   apply (thin_tac "data_TLB_matching_entries 32 va  (s\<lparr>micro_DataTLB :=  \<lambda>a. if a = 0 then None else from_list_to_tlb_map (data_tlb_eviction 31 (micro_DataTLB s)) a\<rparr>) = [entry]")
   apply (subgoal_tac "lookup (tlbtypcast ` ran (micro_DataTLB s)) (ASID (CONTEXTIDR (CP15 s))) va =  TLB.lookup_type.Hit (tlbtypcast entry)")
    apply (thin_tac "lookup (tlbtypcast ` ran (\<lambda>a. if a = 0 then None else from_list_to_tlb_map (data_tlb_eviction 31 (micro_DataTLB s)) a)) (ASID (CONTEXTIDR (CP15 s))) va = TLB.lookup_type.Hit (tlbtypcast entry)")
    prefer 2
    apply (clarsimp simp: tlb_rel_evicted_hit)
   apply (subgoal_tac "lookup (dtlb_set (tlbs_set t)) (asid t) va = TLB.lookup_type.Hit (tlbtypcast entry)")
    prefer 2
    apply (clarsimp simp: tlb_rel_consistent_lookup_hit)
   apply (clarsimp simp: mmu_translate_tlb_state_ext_def read_state_def Let_def bind_def)
   apply (clarsimp split: if_split)
   apply (subgoal_tac "reg'DACR (DACR (CP15 s)) = dacr t")
    apply rule+
      apply (clarsimp simp: dom_perm_entry_check_def checkdomain_def Let_def checkpermission_def split: if_split_asm)
      apply (case_tac entry; clarsimp simp: tlb_entry_to_adrdesc_def va_to_pa_def TLB.va_to_pa_def return_def)
     apply rule+
     apply (clarsimp simp: dom_perm_entry_check_def checkdomain_def Let_def checkpermission_def split: if_split_asm)
     apply (case_tac entry; clarsimp simp: tlb_entry_to_adrdesc_def va_to_pa_def TLB.va_to_pa_def return_def)
    apply rule+
       apply (clarsimp simp: dom_perm_entry_check_def checkdomain_def Let_def checkpermission_def split: if_split_asm)
       apply (case_tac entry; clarsimp simp: tlb_entry_to_adrdesc_def va_to_pa_def TLB.va_to_pa_def return_def)
      apply rule+
      apply (clarsimp simp: dom_perm_entry_check_def checkdomain_def Let_def checkpermission_def split: if_split_asm)
      apply (case_tac entry; clarsimp simp: tlb_entry_to_adrdesc_def va_to_pa_def TLB.va_to_pa_def return_def)
     apply rule+
     apply (clarsimp simp: dom_perm_entry_check_def checkdomain_def Let_def checkpermission_def split: if_split_asm)
     apply (case_tac entry; clarsimp simp: tlb_entry_to_adrdesc_def va_to_pa_def TLB.va_to_pa_def return_def)
    apply rule+
      apply (clarsimp simp: dom_perm_entry_check_def checkdomain_def Let_def checkpermission_def split: if_split_asm)
      apply (case_tac entry; clarsimp simp: tlb_entry_to_adrdesc_def va_to_pa_def TLB.va_to_pa_def return_def)
     apply rule+
     apply (clarsimp simp: dom_perm_entry_check_def checkdomain_def Let_def checkpermission_def split: if_split_asm)
     apply (case_tac entry; clarsimp simp: tlb_entry_to_adrdesc_def va_to_pa_def TLB.va_to_pa_def return_def)
    apply rule+
     apply (clarsimp simp: dom_perm_entry_check_def checkdomain_def Let_def checkpermission_def split: if_split_asm)
      apply (case_tac entry; clarsimp simp: tlb_entry_to_adrdesc_def va_to_pa_def TLB.va_to_pa_def return_def)
     apply (case_tac entry; clarsimp simp: tlb_entry_to_adrdesc_def va_to_pa_def TLB.va_to_pa_def return_def)
    apply rule+
    apply (clarsimp simp: dom_perm_entry_check_def checkdomain_def Let_def checkpermission_def split: if_split_asm)
    apply (case_tac entry; clarsimp simp: tlb_entry_to_adrdesc_def va_to_pa_def TLB.va_to_pa_def return_def)
   apply (clarsimp simp: tlb_rel_def state_comp_def typ_tlb_def cstate.defs)
  apply (case_tac "data_TLB_matching_entries 32 va (s\<lparr>micro_DataTLB :=  \<lambda>a. if a = 0 then None else from_list_to_tlb_map (data_tlb_eviction 31 (micro_DataTLB s)) a\<rparr>)"; clarsimp)
   prefer 2
   apply (case_tac list; clarsimp)
  apply rule+
   apply (case_tac "main_TLB_matching_entries 256 va (s\<lparr>main_TLB := \<lambda>a. if a = 0 then None else from_list_to_tlb_map (main_tlb_eviction 255 (main_TLB s)) a\<rparr>)"; clarsimp)
   apply (case_tac list; clarsimp)
   apply (rename_tac entry)
   apply (subgoal_tac "lookup (tlbtypcast ` ran (main_TLB (s\<lparr>main_TLB := \<lambda>a. if a = 0 then None else from_list_to_tlb_map (main_tlb_eviction 255 (main_TLB s)) a\<rparr>))) (ASID (CONTEXTIDR (CP15 s))) va = TLB.lookup_type.Hit (tlbtypcast entry) ")
    prefer 2 
    apply (drule main_TLB_matching_entries_lookup_equal) 
    apply (case_tac s, clarsimp)
   apply clarsimp
   apply (thin_tac "main_TLB_matching_entries 256 va (s\<lparr>main_TLB := \<lambda>a. if a = 0 then None else from_list_to_tlb_map (main_tlb_eviction 255 (main_TLB s)) a\<rparr>) = [entry]")
   apply (subgoal_tac "lookup (tlbtypcast ` ran (main_TLB s)) (ASID (CONTEXTIDR (CP15 s))) va =  TLB.lookup_type.Hit (tlbtypcast entry)")
    apply (thin_tac "lookup (tlbtypcast ` ran (\<lambda>a. if a = 0 then None else from_list_to_tlb_map (main_tlb_eviction 255 (main_TLB s)) a)) (ASID (CONTEXTIDR (CP15 s))) va = TLB.lookup_type.Hit (tlbtypcast entry)")
    prefer 2
    apply (clarsimp simp: tlb_rel_evicted_hit_main_tlb)
   apply (subgoal_tac "lookup (unitlb_set (tlbs_set t)) (asid t) va = TLB.lookup_type.Hit (tlbtypcast entry)")
    prefer 2
    apply (clarsimp simp: tlb_rel_consistent_lookup_hit_main_tlb)
   apply (clarsimp simp: mmu_translate_tlb_state_ext_def read_state_def Let_def bind_def)
   apply (clarsimp split: if_split)
   apply (subgoal_tac "reg'DACR (DACR (CP15 s)) = dacr t")
    apply rule+
      apply (clarsimp simp: dom_perm_entry_check_def checkdomain_def Let_def checkpermission_def split: if_split_asm)
      apply (case_tac entry; clarsimp simp: tlb_entry_to_adrdesc_def va_to_pa_def TLB.va_to_pa_def return_def)
     apply rule+
     apply (clarsimp simp: dom_perm_entry_check_def checkdomain_def Let_def checkpermission_def split: if_split_asm)
     apply (case_tac entry; clarsimp simp: tlb_entry_to_adrdesc_def va_to_pa_def TLB.va_to_pa_def return_def)
    apply rule+
       apply (clarsimp simp: dom_perm_entry_check_def checkdomain_def Let_def checkpermission_def split: if_split_asm)
       apply (case_tac entry; clarsimp simp: tlb_entry_to_adrdesc_def va_to_pa_def TLB.va_to_pa_def return_def)
      apply rule+
      apply (clarsimp simp: dom_perm_entry_check_def checkdomain_def Let_def checkpermission_def split: if_split_asm)
      apply (case_tac entry; clarsimp simp: tlb_entry_to_adrdesc_def va_to_pa_def TLB.va_to_pa_def return_def)
     apply rule+
     apply (clarsimp simp: dom_perm_entry_check_def checkdomain_def Let_def checkpermission_def split: if_split_asm)
     apply (case_tac entry; clarsimp simp: tlb_entry_to_adrdesc_def va_to_pa_def TLB.va_to_pa_def return_def)
    apply rule+
      apply (clarsimp simp: dom_perm_entry_check_def checkdomain_def Let_def checkpermission_def split: if_split_asm)
      apply (case_tac entry; clarsimp simp: tlb_entry_to_adrdesc_def va_to_pa_def TLB.va_to_pa_def return_def)
     apply rule+
     apply (clarsimp simp: dom_perm_entry_check_def checkdomain_def Let_def checkpermission_def split: if_split_asm)
     apply (case_tac entry; clarsimp simp: tlb_entry_to_adrdesc_def va_to_pa_def TLB.va_to_pa_def return_def)
    apply rule+
     apply (clarsimp simp: dom_perm_entry_check_def checkdomain_def Let_def checkpermission_def split: if_split_asm)
      apply (case_tac entry; clarsimp simp: tlb_entry_to_adrdesc_def va_to_pa_def TLB.va_to_pa_def return_def)
     apply (case_tac entry; clarsimp simp: tlb_entry_to_adrdesc_def va_to_pa_def TLB.va_to_pa_def return_def)
    apply rule+
    apply (clarsimp simp: dom_perm_entry_check_def checkdomain_def Let_def checkpermission_def split: if_split_asm)
    apply (case_tac entry; clarsimp simp: tlb_entry_to_adrdesc_def va_to_pa_def TLB.va_to_pa_def return_def)
   apply (clarsimp simp: tlb_rel_def state_comp_def typ_tlb_def cstate.defs)
  
  
  
  
  
  
  
  
  oops

  
  
  
  
  
  
  
  
  
  
  
  
  oops





declare [[show_types]]


lemma
  "if P' then Q' \<longrightarrow> R' else R' = soemthing"
  apply clarsimp
  oops


(*
lemma CheckPermission_no_excp [wp]:
  "\<lbrace>\<lambda>s. P s \<longrightarrow> exception s \<noteq> NoException\<rbrace>
  CheckPermission (p, va, l, d, iw, ip, f', f'') \<lbrace>\<lambda>rf s. exception s \<noteq> NoException\<rbrace>"
  supply if_cong[cong] if_split[split del]
  apply (wpsimp simp: CheckPermission_def)
  apply (simp cong: conj_cong if_cong)
  apply safe
  by (wpsimp simp: if_distribR  Let_def cong: conj_cong)+

lemma vcg_const:
  "\<lbrace>\<lambda>_. P\<rbrace> f \<lbrace>\<lambda>_ _. P\<rbrace>"
  by (smt l3_valid_def)

lemma CheckDomain_no_excp [wp]:
  "\<lbrace>\<lambda>s. exception s \<noteq> NoException\<rbrace> CheckDomain (d, va, l, iw) \<lbrace>\<lambda>rf s. exception s \<noteq> NoException\<rbrace>"
  supply if_cong[cong] 
  apply (wpsimp simp: CheckDomain_def)
  apply word_bitwise by force

lemma CurrentModeIsHyp_no_excp [wp]:
  "\<lbrace>\<lambda>s. exception s \<noteq> NoException\<rbrace> CurrentModeIsHyp () \<lbrace>\<lambda>_ s. exception s \<noteq> NoException\<rbrace>"
  supply if_cong[cong] 
  by (wpsimp simp: CurrentModeIsHyp_def BadMode_def HaveSecurityExt_def HaveVirtExt_def ArchVersion_def cong: conj_cong)

lemma TLBRMemAtrbts_no_excp [wp]:
  "\<lbrace>\<lambda>s. exception s \<noteq> NoException\<rbrace>  TLBRMemAtrbts (a, b, c, d)  \<lbrace>\<lambda>_ s. exception s \<noteq> NoException\<rbrace>"
  supply if_cong[cong] if_split[split del] 
  apply (clarsimp simp: TLBRMemAtrbts_def)
  apply (wpsimp simp: if_distribR  cong: conj_cong)
   apply (clarsimp simp: RemappedTEXDecode_def)
   apply (wpsimp simp: if_distribR  Let_def cong: conj_cong)
  by (clarsimp simp: if_distribR  cong: conj_cong)




(* adding these rule to wp breaks checkdomain simplification in the start *)



lemma into_fst[simp]:
  "(\<forall>x. (\<exists>y. r = (x, y)) \<longrightarrow> P x) = P (fst r)"
  by (cases r) simp
term raise'exception
thm CheckPermission_def
lemma
  "\<lbrace>P\<rbrace>
    do {
      x \<leftarrow> f;
      (if \<not>X x then raise'exception (HOL.undefined)
    else return ());
     return x }
    \<lbrace>\<lambda>r s.  exception s = NoException \<longrightarrow> Q' r \<rbrace>"
  supply if_split[split del]
  apply_trace wp
  apply clarsimp

  oops
  
*)

lemma mmu_translate_refinement_pa [wp]:
  "\<lbrace>\<lambda>s. \<exists>t mematr . MMU_config_assert_isa s \<and>
                 tlb_rel s (typ_tlb t) \<and>
                 dtlb_consistent (typ_tlb t) (Addr va) \<and>
                 unitlb_consistent (typ_tlb t) (Addr va) \<and>
                 mmu_translate  (Addr va) siz ispriv iswrite True (t :: 'a tlb_state_scheme) = ((pa', mematr), t')\<rbrace>
       TranslateAddress (va, ispriv, iswrite, siz, True) 
   \<lbrace>\<lambda>r s. exception s = NoException \<longrightarrow> pa' = Addr (paddress r)\<rbrace>"
  supply if_cong[cong] if_split[split del] translation_mmu_config [wp del]
  apply (unfold TranslateAddress_def)
  apply wpsimp
             apply (wpsimp simp: write'DataTLB_def write'unified_mainTLB_def)+
  term CheckPermission
  apply (wpsimp simp: TranslateAddressV_def) 
              prefer 2
              apply (rule false_imp_post)
             apply (clarsimp simp: TranslationTableWalkSD_def Let_def)
             apply (wpsimp simp: if_distribR  cong: conj_cong)
    (* should we simplify based on the post-cond here? *)
                  apply (rule well_formed_state) 
                  apply (clarsimp  simp: if_distribR  cong: conj_cong) 
                  apply (wpsimp simp: level2_desc_address_and_desc_def if_distribR  Let_def BigEndianReverse_def mem_def cong: conj_cong)
                               apply (wpsimp simp: mem1_def  if_distribR  Let_def cong: conj_cong)  apply clarsimp
                              apply (wpsimp simp: mem1_def  if_distribR  Let_def cong: conj_cong)  apply clarsimp
                             apply (wpsimp simp: mem1_def  if_distribR  Let_def cong: conj_cong)  apply clarsimp
                            apply (wpsimp simp: mem1_def  if_distribR  Let_def cong: conj_cong)  apply clarsimp
                           apply wpsimp
                          apply wpsimp
                         apply wpsimp
                        apply wpsimp
                           apply (wpsimp simp:  if_distribR  Let_def cong: conj_cong)  
                           apply (wpsimp simp: mem1_def  if_distribR  Let_def cong: conj_cong)  apply clarsimp
                          apply (wpsimp simp: mem1_def  if_distribR  Let_def cong: conj_cong)  apply clarsimp
                         apply (wpsimp simp: mem1_def  if_distribR  Let_def cong: conj_cong)  apply clarsimp
                        apply (wpsimp simp: mem1_def  if_distribR  Let_def cong: conj_cong)  apply clarsimp
                       apply wpsimp
                         apply (rule false_imp_post)
                        apply wpsimp
                       apply wpsimp
                       apply (rule IsSecure_wp)
                      apply wpsimp
                      apply (clarsimp simp: if_distribR  cong: conj_cong) 
                      apply (rule HaveVirtExt_wp)
                     apply (clarsimp simp: if_distribR  cong: conj_cong) 
                     apply wpsimp
                    apply wpsimp
                   apply wpsimp
                  apply wpsimp
                 apply (wpsimp simp: if_distribR  Let_def cong: conj_cong)
                apply (clarsimp simp: if_distribR  cong: conj_cong) 
                apply (rule well_formed_state) 
                apply (clarsimp  simp: if_distribR  cong: conj_cong) 
                apply (wpsimp simp: level1_desc_address_and_desc_def if_distribR  Let_def BigEndianReverse_def mem_def cong: conj_cong)
                                        apply (wpsimp simp: mem1_def  if_distribR  Let_def cong: conj_cong)  apply clarsimp
                                       apply (wpsimp simp: mem1_def  if_distribR  Let_def cong: conj_cong)  apply clarsimp
                                      apply (wpsimp simp: mem1_def  if_distribR  Let_def cong: conj_cong)  apply clarsimp
                                     apply (wpsimp simp: mem1_def  if_distribR  Let_def cong: conj_cong)  apply clarsimp
                                    apply wpsimp
                                   apply wpsimp
                                  apply wpsimp
                                 apply wpsimp
                                    apply (wpsimp simp:  if_distribR  Let_def cong: conj_cong)  
                                    apply (wpsimp simp: mem1_def  if_distribR  Let_def cong: conj_cong)  apply clarsimp
                                   apply (wpsimp simp: mem1_def  if_distribR  Let_def cong: conj_cong)  apply clarsimp
                                  apply (wpsimp simp: mem1_def  if_distribR  Let_def cong: conj_cong)  apply clarsimp
                                 apply (wpsimp simp: mem1_def  if_distribR  Let_def cong: conj_cong)  apply clarsimp
                                apply wpsimp
                               apply (wpsimp simp:  if_distribR  Let_def cong: conj_cong)   apply (clarsimp simp: if_distribR  Let_def cong: conj_cong)?
                                 apply (clarsimp simp: if_distribR  Let_def cong: conj_cong)?
                                 apply (rule false_imp_post)
                                apply (wpsimp simp: if_distribR Let_def cong: conj_cong)
                               apply (wpsimp simp: if_distribR Let_def cong: conj_cong)
                               apply (rule IsSecure_wp)
                              apply (clarsimp simp: if_distribR  Let_def cong: conj_cong)
                              apply wpsimp
                              apply (rule HaveVirtExt_wp)
                             apply (clarsimp simp: if_distribR  cong: conj_cong) 
                             apply wpsimp
                            apply wpsimp
                            apply (rule HaveMPExt_wp)
                           apply (clarsimp simp: if_distribR  cong: conj_cong) 
                           apply wpsimp
                          apply wpsimp
                         apply wpsimp
                        apply wpsimp
                       apply wpsimp
                      apply wpsimp
                      apply (clarsimp simp: if_distribR  Let_def cong: conj_cong)
                     apply wpsimp
                    apply wpsimp 
                   apply wpsimp
                   apply (clarsimp simp: if_distribR  Let_def cong: conj_cong)
                  apply wpsimp
                 apply wpsimp
                apply wpsimp
               apply (clarsimp simp: if_distribR  Let_def cong: conj_cong)
               apply wpsimp
              apply (clarsimp simp: if_distribR  Let_def cong: conj_cong)
              apply (rule HaveSecurityExt_wp)
             apply (clarsimp simp: if_distribR Let_def cong: conj_cong)
             apply (wpsimp simp: translation_root_def if_distribR Let_def cong: conj_cong)
            apply (clarsimp simp: if_distribR Let_def cong: conj_cong)
            apply wpsimp
             apply (rule CurrentModeIsHyp_wp)  
            apply wpsimp
           apply (clarsimp simp: if_distribR Let_def cong: conj_cong)
           apply (rule CurrentModeIsHyp_wp)  
          apply (wpsimp simp: FCSETranslate_def)
         apply (wpsimp simp: lookupTLB_main_def entry_list_main_def mainTLBEntries_def)
         apply (clarsimp simp: if_distribR  Let_def cong: conj_cong)
         apply (rule_tac specific_main_tlb_for_loop_wp') 
        apply wpsimp
       apply (clarsimp simp: if_distribR Let_def cong: conj_cong)
       apply (wpsimp simp: lookupTLB_Data_micro_def entry_list_data_micro_def microDataTLBEntries_def)
       apply (rule_tac specific_data_tlb_for_loop_wp') 
      apply wpsimp
     apply (clarsimp simp: if_distribR Let_def cong: conj_cong)
    (* form here *)
     apply (wpsimp simp: write'unified_mainTLB_def mainTLB_evict_def mainTLBEntries_def unified_mainTLB_def)
     apply (rule to_do) apply clarsimp
    apply (wpsimp simp: write'DataTLB_def microDataTLB_evict_def microDataTLBEntries_def DataTLB_def)
    apply (rule to_do1) 
   apply (wpsimp simp: write'InstrTLB_def microInstrTLB_evict_def microInstrTLBEntries_def InstrTLB_def)
   apply (rule to_do2)
  apply (clarsimp simp: if_distribR Let_def cong: conj_cong)
  apply (rule conjI; clarsimp)
   apply (case_tac "data_TLB_matching_entries 32 va (s\<lparr>micro_DataTLB :=  \<lambda>a. if a = 0 then None else from_list_to_tlb_map (data_tlb_eviction 31 (micro_DataTLB s)) a\<rparr>)"; clarsimp)
   apply (case_tac list; clarsimp)
   apply (subgoal_tac "lookup (tlbtypcast ` ran (micro_DataTLB  (s\<lparr>micro_DataTLB :=
              \<lambda>a. if a = 0 then None else from_list_to_tlb_map (data_tlb_eviction 31 (micro_DataTLB s)) a\<rparr>)))
               (ASID (CONTEXTIDR (CP15 s))) va = TLB.lookup_type.Hit (tlbtypcast x) ")
    apply clarsimp
    apply (thin_tac "data_TLB_matching_entries 32 va  (s\<lparr>micro_DataTLB :=  \<lambda>a. if a = 0 then None else from_list_to_tlb_map (data_tlb_eviction 31 (micro_DataTLB s)) a\<rparr>) = [x]")
    apply (subgoal_tac "lookup (tlbtypcast ` ran (micro_DataTLB s)) (ASID (CONTEXTIDR (CP15 s))) va =  TLB.lookup_type.Hit (tlbtypcast x)")
     apply (thin_tac "lookup (tlbtypcast ` ran (\<lambda>a. if a = 0 then None else from_list_to_tlb_map (data_tlb_eviction 31 (micro_DataTLB s)) a)) (ASID (CONTEXTIDR (CP15 s))) va = TLB.lookup_type.Hit (tlbtypcast x)")
     prefer 2
     apply (clarsimp simp: tlb_rel_evicted_hit)
    apply (subgoal_tac "lookup (dtlb_set (tlbs_set t)) (asid t) va = TLB.lookup_type.Hit (tlbtypcast x)")
     prefer 2
     apply (clarsimp simp: tlb_rel_consistent_lookup_hit)
    apply (clarsimp simp: mmu_translate_tlb_state_ext_def read_state_def Let_def bind_def)
    (*  we have a problem here *)


    defer
    
  oops
  

lemma
  "\<lbrakk>data_TLB_matching_entries 32 va  (s\<lparr>micro_DataTLB := tlb\<rparr>) =  [x]\<rbrakk> \<Longrightarrow> 
       lookup(tlbtypcast ` ran (micro_DataTLB (s\<lparr>micro_DataTLB := tlb\<rparr>))) (ASID (CONTEXTIDR (CP15 s))) va = 
            TLB.lookup_type.Hit (tlbtypcast x)"
  apply (clarsimp simp: data_TLB_matching_entries_def data_TLB_entries_def MatchingEntry_def)

  oops
lemma
  "(\<lambda>lst. if lst = [] then TLB.lookup_type.Miss else 
          if \<exists>x. lst = [x] then TLB.lookup_type.Hit x 
          else TLB.lookup_type.Incon)  (data_TLB_matching_entries 32 va s) =
   lookup (tlbtypcast ` ran (micro_DataTLB s)) (ASID (CONTEXTIDR (CP15 s))) va"

  sorry


lemma  tlb_rel_not_miss:
  "\<lbrakk>tlb_rel s (typ_tlb (t :: 'a tlb_state_scheme)); 
       lookup (tlbtypcast ` ran (micro_DataTLB s)) (ASID (CONTEXTIDR (CP15 s))) va \<noteq> TLB.lookup_type.Miss\<rbrakk> \<Longrightarrow> 
          lookup (dtlb_set (tlbs_set t)) (asid t) va \<noteq> TLB.lookup_type.Miss"
  apply (drule tlb_relD cstate.defs typ_tlb_def)
 by (metis eq_iff less_eq_lookup_type tlb_mono tlbs_more typ_tlb_def typ_tlbs_def typ_tlbs_prim_parameter)



lemma
  "\<lbrakk> data_TLB_matching_entries 32 va (s\<lparr>micro_DataTLB := tlb\<rparr>) = [entry]\<rbrakk> \<Longrightarrow> 
    lookup (tlbtypcast ` ran (micro_DataTLB s)) (ASID (CONTEXTIDR (CP15 s))) va \<noteq> TLB.lookup_type.Miss"
  apply (subgoal_tac "entry_set (tlbtypcast ` ran (micro_DataTLB s)) (ASID (CONTEXTIDR (CP15 s))) va \<noteq> {}")
   apply (clarsimp simp: lookup_def)
  apply (subgoal_tac "tlbtypcast entry \<in> (tlbtypcast ` ran (micro_DataTLB s))")
   prefer 2
   apply (clarsimp simp: ran_def data_TLB_matching_entries_def data_TLB_entries_def filter_def)

  oops
lemma
  "\<lbrakk>MMU_config_assert_isa s; tlb_rel s (typ_tlb t); dtlb_consistent (typ_tlb t) (Addr va); unitlb_consistent (typ_tlb t) (Addr va); 
        mmu_translate (Addr va) siz ispriv iswrite True (t :: 'a tlb_state_scheme) = ((pa', mematr), t');
        exception s = NoException; data_TLB_matching_entries 32 va (s\<lparr>micro_DataTLB := tlb\<rparr>) = [x]\<rbrakk>
       \<Longrightarrow> pa' = Addr (paddress (ARM_Monadic.va_to_pa (va, x)))"
(*  apply (subgoal_tac "lookup (dtlb_set (tlbs_set t)) (asid t) va \<noteq> TLB.lookup_type.Miss")
   prefer 2
   apply (subgoal_tac "lookup (tlbtypcast ` ran (micro_DataTLB s)) (ASID (CONTEXTIDR (CP15 s))) va \<noteq> TLB.lookup_type.Miss")
    apply (clarsimp simp: tlb_rel_not_miss)


   apply (clarsimp simp: mmu_translate_tlb_state_ext_def read_state_def Let_def bind_def)
   apply (case_tac "lookup (dtlb_set (tlbs_set t)) (asid t) va"; clarsimp simp: )
    apply (clarsimp simp: consistent0_def typ_tlb_def cstate.defs)
   apply (thin_tac "unitlb_consistent (typ_tlb t) (Addr va)")
   apply (clarsimp simp: consistent0_def typ_tlb_def cstate.defs)
   apply (subgoal_tac "y = tlbtypcast x")
    prefer 2


    apply (clarsimp)
    apply (clarsimp simp: align_dom_perm_entry_check_def Let_def ARM_Monadic.va_to_pa_def 
                          tlb_entry_to_adrdesc_def checkdomain_def checkpermission_def align_def split: if_split_asm)
  apply (clarsimp simp: raise'exception'_def split: if_split_asm)
  apply (case_tac x; clarsimp simp:)
*)
(*
 apply (rename_tac s t mematr)
  subgoal premises prems for s t mematr 
  proof goal_cases
    have foo[simp]: "\<And>tlb tlb' tlb''. data_TLB_matching_entries 32 va (s\<lparr>micro_InstrTLB := tlb, micro_DataTLB := tlb', main_TLB := tlb''\<rparr>) = 
                    data_TLB_matching_entries 32 va (s\<lparr> micro_DataTLB := tlb'\<rparr>)" by (clarsimp simp: data_TLB_matching_entries_def data_TLB_entries_def)
    have foo1[simp]: "\<And>tlb tlb' tlb''. main_TLB_matching_entries 256 va (s\<lparr>micro_InstrTLB := tlb, micro_DataTLB := tlb',  main_TLB :=tlb''\<rparr>) =
                  main_TLB_matching_entries 256 va (s\<lparr>main_TLB :=tlb''\<rparr>)" by (clarsimp simp: main_TLB_matching_entries_def main_TLB_entries_def)
    case 1 show ?case
      apply (insert prems)
      apply clarsimp
      apply (rule conjI)
       apply (clarsimp)
       apply (case_tac "data_TLB_matching_entries 32 va (s\<lparr>micro_DataTLB := \<lambda>a. if a = 0 then None else entries_to_TLB (data_tlb_eviction 30 s) a\<rparr>)"; clarsimp)
       apply (case_tac list; clarsimp)
      sorry
  qed
  done
*)




(*





lemma mmu_translate_refinement_pa [wp]:
  "\<lbrace>\<lambda>s. \<exists>t mematr . MMU_config_assert_isa s \<and>
                 tlb_rel s (typ_tlb t) \<and>
                 dtlb_consistent (typ_tlb t) (Addr va) \<and>
                 unitlb_consistent (typ_tlb t) (Addr va) \<and>
                 mmu_translate  (Addr va) siz ispriv iswrite True (t :: 'a tlb_state_scheme) = ((pa', mematr), t')\<rbrace>
       TranslateAddress (va, ispriv, iswrite, siz, True) 
   \<lbrace>\<lambda>r s. exception s = NoException \<longrightarrow> pa' = Addr (paddress r)\<rbrace>"
  supply if_cong[cong] if_split[split del] 
  apply (wpsimp simp: TranslateAddress_def write'DataTLB_def write'unified_mainTLB_def)
          apply (wpsimp simp: TranslateAddressV_def)
                  apply (rule well_formed_state, simp)
                  apply (wpsimp simp: CurrentModeIsHyp_def)
                   apply (wpsimp simp: BadMode_def HaveSecurityExt_def HaveVirtExt_def ArchVersion_def cong: conj_cong)
                  apply wpsimp
                 apply wpsimp
                apply (rule well_formed_state, simp)
                apply (clarsimp simp: if_distribR  cong: conj_cong )
                apply (wpsimp simp: CheckDomain_def)
               apply wpsimp
              apply wpsimp
               apply (rule well_formed_state, simp)
               apply (clarsimp simp: if_distribR  cong: conj_cong )
               apply (wpsimp simp: CurrentModeIsHyp_def)
                apply (wpsimp simp: BadMode_def HaveSecurityExt_def HaveVirtExt_def ArchVersion_def cong: conj_cong)
               apply wpsimp
              apply wpsimp
             apply (rule well_formed_state, simp)
             apply (clarsimp simp: if_distribR  cong: conj_cong )
             apply (wpsimp simp: CurrentModeIsHyp_def)
              apply (wpsimp simp: BadMode_def HaveSecurityExt_def HaveVirtExt_def ArchVersion_def cong: conj_cong)
             apply wpsimp
            apply wpsimp
              apply (rule well_formed_state, simp)
              apply (clarsimp simp: if_distribR  cong: conj_cong )
              apply (rule l3_valid_conj_post) 
               apply (rule translation_mmu_config)
              apply (clarsimp split: if_split)
              apply (rule TranslateAddressV_pt_walk' [where ?'a = 'a] )
             apply (rule well_formed_state, simp)
             apply (clarsimp simp: if_distribR  cong: conj_cong)
             apply (rule TranslateAddressVS1Off_False)   (*  should we remove VS1Off altogerher? *)
            apply wpsimp
             apply (rule well_formed_state, simp)
             apply (clarsimp simp: if_distribR  cong: conj_cong )
             apply (wpsimp simp: CurrentModeIsHyp_def)
              apply (wpsimp simp: BadMode_def HaveSecurityExt_def HaveVirtExt_def ArchVersion_def cong: conj_cong)
             apply wpsimp
            apply wpsimp
           apply (rule well_formed_state, simp)
           apply (clarsimp simp: if_distribR  cong: conj_cong )
           apply (wpsimp simp: CurrentModeIsHyp_def)
            apply (wpsimp simp: BadMode_def HaveSecurityExt_def HaveVirtExt_def ArchVersion_def cong: conj_cong)
           apply wpsimp
          apply (rule well_formed_state, simp)
          apply (clarsimp simp: if_distribR  cong: conj_cong )
          apply (wpsimp simp: FCSETranslate_def)
         apply (clarsimp  cong: conj_cong)
         apply (wpsimp simp: lookupTLB_main_def entry_list_main_def mainTLBEntries_def)
         apply (rule for_loop_wp1; wpsimp simp: unified_mainTLB_def)
          apply (rename_tac s entry)
          apply (case_tac a; clarsimp split: if_split)
          apply (drule_tac x = "tlbtypcast entry" in spec)
          apply (subgoal_tac "pt_walk (asid t) (heap t) (ttbr0 t) (prrr t) (nmrr t) (Addr va) = Some (tlbtypcast entry)";
                                 (clarsimp simp: to_do5)?)
          apply (clarsimp simp: TLB.va_to_pa_def ARM_Monadic.va_to_pa_def split: TLBEntry.splits)
         apply (rename_tac entry)
         apply (case_tac a; clarsimp split: if_split)
         apply (drule_tac x = "tlbtypcast entry" in spec)
         apply (subgoal_tac "pt_walk (asid t) (heap t) (ttbr0 t) (prrr t) (nmrr t) (Addr va) = Some (tlbtypcast entry)";
                                (clarsimp simp: to_do5)?)
         apply (clarsimp simp: TLB.va_to_pa_def ARM_Monadic.va_to_pa_def split: TLBEntry.splits)
        apply (wpsimp)
       apply (wpsimp simp: lookupTLB_Data_micro_def entry_list_data_micro_def microDataTLBEntries_def)
       apply (rule for_loop_wp1; wpsimp simp: DataTLB_def)
        apply (rename_tac entry)
        apply (case_tac a; clarsimp split: if_split)
        apply (drule_tac x = "tlbtypcast entry" in spec)
        apply (subgoal_tac "pt_walk (asid t) (heap t) (ttbr0 t) (prrr t) (nmrr t) (Addr va) = Some (tlbtypcast entry)";
                           (clarsimp simp: to_do7)?)
        apply (clarsimp simp: TLB.va_to_pa_def ARM_Monadic.va_to_pa_def split: TLBEntry.splits)
       apply (rename_tac entry)
       apply (case_tac a; clarsimp split: if_split)
       apply (drule_tac x = "tlbtypcast entry" in spec)
       apply (subgoal_tac "pt_walk (asid t) (heap t) (ttbr0 t) (prrr t) (nmrr t) (Addr va) = Some (tlbtypcast entry)";
                              (clarsimp simp: to_do7)?)
       apply (clarsimp simp: TLB.va_to_pa_def ARM_Monadic.va_to_pa_def split: TLBEntry.splits)
      apply (wpsimp)
     apply clarsimp
     apply (wpsimp simp: mainTLB_evict_def write'unified_mainTLB_def mainTLBEntries_def)
     apply (rule for_loop_wp0' ; wpsimp simp: unified_mainTLB_def)
     defer
     apply (wpsimp simp: microDataTLB_evict_def write'DataTLB_def microDataTLBEntries_def)
     apply (rule for_loop_wp0' ; wpsimp simp: DataTLB_def) 
     defer
     apply (wpsimp simp: microInstrTLB_evict_def write'InstrTLB_def microInstrTLBEntries_def)
     apply (rule for_loop_wp0' ; wpsimp simp: InstrTLB_def)
     defer
     apply clarsimp
     apply (rule_tac x = t in exI)
     apply (rule, clarsimp simp: tlb_rel_none_update_preserved)
     apply (rule, clarsimp)
     apply (rule, clarsimp)
     apply (clarsimp)
     apply (clarsimp simp: mmu_translate_tlb_state_ext_def read_state_def Let_def bind_def)
     apply (case_tac "lookup (dtlb_set (tlbs_set t)) (asid t) va"; clarsimp)
       apply (case_tac "lookup (unitlb_set (tlbs_set t)) (asid t) va"; clarsimp)
         apply (clarsimp simp: bind_def update_state_def)
         apply (clarsimp simp: align_dom_perm_entry_check_def align_def Let_def split: if_split_asm)





  sorry
*)


(*
lemma domain_entry_constant_bool_pre_post[wp]:
  "\<lbrace>\<lambda>s. exception s = NoException \<longrightarrow> Q'\<rbrace> CheckDomain (de, va, l, iw) 
         \<lbrace>\<lambda>r s. exception s = NoException \<longrightarrow> Q'\<rbrace>"
  supply if_cong[cong] if_split[split del] 
  apply (wpsimp simp: CheckDomain_def)
  apply (clarsimp split: if_split)
  apply word_bitwise by force
*)


(*
lemma CheckPermission_constant_bool_pre_post [wp]:
  "\<lbrace>\<lambda>s. exception s = NoException \<longrightarrow> Q' \<rbrace> 
      CheckPermission (p, va, l, d, iw, ip, f, f')
      \<lbrace>\<lambda>rf s. exception s = NoException \<longrightarrow> Q'\<rbrace>"
  supply if_cong[cong] if_split[split del] 
  apply (wpsimp simp: CheckPermission_def)
  apply (case_tac "\<not>AFE (VSCTLR (CP15 s))", clarsimp )
   apply (clarsimp split: if_splits)
   apply word_bitwise apply force
   apply (clarsimp split: if_splits)
    apply word_bitwise by force
*)

end