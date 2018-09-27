theory L3_Hoare_Logic
imports L3_Lib
  "~/verification/l4v/lib/Apply_Trace_Cmd" 
  "~/verification/l4v/lib/Monad_WP/wp/WP"
  "~/verification/l4v/lib/Monad_WP/wp/WPC"
  "~/verification/l4v/lib/Monad_WP/wp/WPFix"
  "~/verification/l4v/lib/Monad_WP/Strengthen"
  "~/verification/l4v/lib/Simp_No_Conditional"


begin

(* Wrap up the standard usage pattern of wp/wpc/simp into its own command: *)
method wpsimp uses wp wp_del simp simp_del split split_del cong =
  ((determ \<open>wpfix | wp add: wp del: wp_del | wpc |
            clarsimp_no_cond simp: simp simp del: simp_del split: split split del: split_del cong: cong |
            clarsimp simp: simp simp del: simp_del split: split split del: split_del cong: cong\<close>)+)[1]


definition 
  l3_valid ::  "('s \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> 'r \<times> 's) \<Rightarrow> ('r \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> bool"
  ("\<lbrace>_\<rbrace> _ \<lbrace>_\<rbrace>")
where 
  "\<lbrace>P\<rbrace> f \<lbrace>P'\<rbrace> \<equiv> \<forall>s s' r. f s = (r, s') \<longrightarrow> P s \<longrightarrow> P' r s'"


lemma l3_valid_weak_pre[wp_pre]:
  "\<lbrakk> l3_valid P f Q; (\<And>s . P' s \<Longrightarrow> P s) \<rbrakk> \<Longrightarrow> l3_valid P' f Q"
  by (simp add: l3_valid_def)

context strengthen_implementation begin

lemma strengthen_hoare [strg]:
  "(\<And>r s. st F (\<longrightarrow>) (Q r s) (R r s))
    \<Longrightarrow> st F (\<longrightarrow>) (\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>) (\<lbrace>P\<rbrace> f \<lbrace>R\<rbrace>)"
  by (cases F, auto simp: l3_valid_def)

lemma wpfix_strengthen_hoare:
  "(\<And>s. st (\<not> F) (\<longrightarrow>) (P s) (P' s))
    \<Longrightarrow> (\<And>r s. st F (\<longrightarrow>) (Q r s) (Q' r s))
    \<Longrightarrow> st F (\<longrightarrow>) (\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>) (\<lbrace>P'\<rbrace> f \<lbrace>Q'\<rbrace>)"
  by (cases F, auto simp: l3_valid_def)

end

lemma l3_valid_triple [wp_trip]:
  "\<lbrace>P\<rbrace> f \<lbrace>Q'\<rbrace> = triple_judgement P f (postcondition Q' (\<lambda>s f. {f s}))"
  apply (clarsimp simp: l3_valid_def triple_judgement_def 
                        postcondition_def split_def)
  by force

declare strengthen_implementation.wpfix_strengthen_hoare[wp_fix_strgs]

lemma l3_valid_bind_weak[wp_split]:
  "\<lbrakk> \<And>r. l3_valid (P' r) (g r) Q; l3_valid P f P' \<rbrakk> \<Longrightarrow> l3_valid P (bind f g) Q"
  by (simp add: l3_valid_def bind_def split: prod.splits)

lemma l3_valid_conj_post[wp_comb]:
 "\<lbrakk>l3_valid P  f Q'; l3_valid P'  f R' \<rbrakk> \<Longrightarrow> 
       l3_valid (\<lambda>s. P s \<and> P' s) f (\<lambda>r s. Q' r s \<and> R' r s)"
  by (simp add: l3_valid_def)

lemma wpc_helper_valid:
  "\<lbrace>Q\<rbrace> g \<lbrace>S\<rbrace> \<Longrightarrow> wpc_helper (P, P') (Q, Q') \<lbrace>P\<rbrace> g \<lbrace>S\<rbrace>"
  by (clarsimp simp: wpc_helper_def elim!: l3_valid_weak_pre)

wpc_setup "\<lambda>m. \<lbrace>P\<rbrace> m \<lbrace>Q\<rbrace>" wpc_helper_valid

lemma l3_valid_return[wp]:
  "l3_valid (\<lambda>s. P () s)  (return ()) P"
  by (clarsimp simp: l3_valid_def return_def)

lemma l3_valid_return'[wp]:
  "l3_valid (\<lambda>s. P f s)  (Pair f) P"
  by (clarsimp simp: l3_valid_def)

lemma read_state_weak[wp]:
  "l3_valid (\<lambda>s. P (f s) s)  (read_state f) P"
  by (clarsimp simp: l3_valid_def read_state_def)

lemma update_state_weak[wp]:
  "l3_valid (\<lambda>s. P () (f s)) (update_state f) P"
  by (clarsimp simp: l3_valid_def update_state_def)

lemma extend_state_weak[wp]:
  "\<lbrakk> l3_valid P f (\<lambda>r s. Q r (snd s)) \<rbrakk> \<Longrightarrow> l3_valid (\<lambda>s. P (v,s)) (extend_state v f) Q"
  apply (clarsimp simp: l3_valid_def extend_state_def )
   by (fastforce split: prod.splits)

lemma trim_state_weak[wp]:
  " \<lbrakk>\<And>s'. l3_valid (P s') f  (\<lambda>r s.  Q r (s', s) ) \<rbrakk> \<Longrightarrow> l3_valid (\<lambda>s. P (fst s) (snd s)) (trim_state f) Q"
  apply (clarsimp simp: l3_valid_def trim_state_def)
   by (fastforce split: prod.splits)

lemma l3_valid_if_else[wp]:
  "\<lbrakk> b \<Longrightarrow> l3_valid T f Q; \<not>b \<Longrightarrow> l3_valid F g Q \<rbrakk> \<Longrightarrow> 
     l3_valid (if b then T else F) (\<lambda>s. if b then f s else g s) Q"
  by (clarsimp simp: l3_valid_def split: if_split_asm)

lemma l3_valid_if_else'[wp]:
  "\<lbrakk> b \<Longrightarrow> l3_valid T  f Q; \<not>b \<Longrightarrow> l3_valid F  g Q \<rbrakk> \<Longrightarrow> 
     l3_valid (if b then T else F) (if b then f else g) Q"
  by (clarsimp simp: l3_valid_def split: if_split_asm)

lemma l3_valid_return''[wp]:
  "l3_valid (\<lambda>s. P f s)  (return f) P"
  by (clarsimp simp: l3_valid_def return_def)



(* first, we had proved this, bit was not sufficient *)
lemma for_loop_wp0:
  "\<lbrakk> \<And>i. \<lbrakk> start \<le> i; i \<le> end \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> f i \<lbrace>\<lambda>_. P\<rbrace>; start \<le> end \<rbrakk> \<Longrightarrow>
  \<lbrace>P\<rbrace> for_loop (start, end, f) \<lbrace>\<lambda>_. P\<rbrace>"
  apply (induct "(start,end,f)" arbitrary: start rule: for_loop.induct)
  apply (subst for_loop.simps)
  apply clarsimp
  apply wpsimp
   apply force
  apply assumption
  done

lemma l3_valid_post:
  "\<lbrakk>\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>; \<And>r s. Q r s \<Longrightarrow> Q' r s\<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q'\<rbrace>"
  by (auto simp: l3_valid_def)

lemmas for_loop_wp = for_loop_wp0[THEN l3_valid_post]

(* and we were trying to prove the following  *)

lemma for_loop_wp1:
  "\<lbrakk> \<And>i. \<lbrakk> start \<le> i; i < e \<rbrakk> \<Longrightarrow> \<lbrace>Q i\<rbrace> f i \<lbrace>\<lambda>_. Q (i+1)\<rbrace>;
     \<lbrace>Q e\<rbrace> f e \<lbrace>\<lambda>_. P\<rbrace>; start \<le> e \<rbrakk> \<Longrightarrow>
  \<lbrace>Q start\<rbrace> for_loop (start, e, f) \<lbrace>\<lambda>_. P\<rbrace>"
  apply (induct "(start, e, f)" arbitrary: start rule: for_loop.induct)
  apply (subst for_loop.simps)
  apply clarsimp
  by (wpsimp, force, assumption)


lemma for_loop_wp2:
  "\<lbrakk> \<And>i. \<lbrakk> start \<ge> i; i > end \<rbrakk> \<Longrightarrow> \<lbrace>Q i\<rbrace> f i \<lbrace>\<lambda>_. Q (i-1)\<rbrace>;
     \<lbrace>Q end\<rbrace> f end \<lbrace>\<lambda>_. P\<rbrace>; start \<ge> end \<rbrakk> \<Longrightarrow>
  \<lbrace>Q start\<rbrace> for_loop (start, end, f) \<lbrace>\<lambda>_. P\<rbrace>"
  apply (induct "(start,end,f)" arbitrary: "end" start rule: for_loop.induct)
  apply (subst for_loop.simps)
  apply clarsimp
  by (wpsimp, force+) 
  

lemma l3_valid_conj_asum_false:
  "\<lbrakk> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>;  \<lbrace>P\<rbrace> f \<lbrace>T\<rbrace> ; \<And>s. P s \<Longrightarrow>  \<not>R (fst (f s)) (snd (f s)) \<rbrakk>\<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>(\<lambda>r s. Q r s \<and> (R r s \<longrightarrow> S) \<and> T r s)\<rbrace>"
   apply (auto simp: l3_valid_def )
  by force

(* keeping it in wp_split for the time being, have to ask Gerwin *)
lemma l3_valid_imp_conj_post [wp_comb]:
 "\<lbrakk> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>r s. A s \<longrightarrow> Q r s\<rbrace>;  \<lbrace>P'\<rbrace> f \<lbrace>\<lambda>r s. A s \<longrightarrow> R r s\<rbrace> \<rbrakk> \<Longrightarrow> 
        \<lbrace>\<lambda>s. P s \<and> P' s\<rbrace> f \<lbrace>\<lambda>r s. A s \<longrightarrow> Q r s \<and> R r s\<rbrace>"
  by (simp add: l3_valid_def)

lemma for_loop_wp0':
  "\<lbrakk> \<And>i. \<lbrakk> start \<ge> i; i \<ge> end \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> f i \<lbrace>\<lambda>_. P\<rbrace>; start \<ge> end \<rbrakk> \<Longrightarrow>
  \<lbrace>P\<rbrace> for_loop (start, end, f) \<lbrace>\<lambda>_. P\<rbrace>"
  apply (induct "(start,end,f)" arbitrary: "end" start rule: for_loop.induct)
  apply (subst for_loop.simps)
  apply clarsimp
  apply wpsimp
   apply force
  apply force
  apply assumption
  done

(*
function for_loop' :: "nat \<times> nat \<times> (nat \<Rightarrow> 'state \<Rightarrow> unit \<times> 'state) \<Rightarrow> 'state \<Rightarrow> unit \<times> 'state" where
  "for_loop' (i, j, a) =
   (if i = j then
      return ()
    else
      bind (a i) (\<lambda>u. for_loop' ((if i < j then i + 1 else i - 1), j, a)))"
  by auto
  termination by (relation "measure (\<lambda>(i, j, _). if i < j then j - i else i - j)") auto

declare for_loop'.simps[simp del]


lemma for_loop':
  "st \<le> en \<Longrightarrow> for_loop (st, en, f) = do { for_loop' (st, en, f); f en }"
  apply (induct "(st, en, f)" arbitrary: st en f rule: for_loop.induct)
  apply simp
  apply (subst for_loop.simps)
  apply simp
  apply (rule conjI; clarsimp)
   apply (simp add: for_loop'.simps)
  apply (subst (2) for_loop'.simps)
  apply (simp add: bind_associativity)
  done


lemma for_loop'_wp:
  "\<lbrakk> \<And>i. \<lbrakk> start \<le> i; i < e \<rbrakk> \<Longrightarrow> \<lbrace>Q i\<rbrace> f i \<lbrace>\<lambda>_. Q (i+1)\<rbrace>;  start \<le> e \<rbrakk> \<Longrightarrow>
            \<lbrace>Q start\<rbrace> for_loop' (start, e, f) \<lbrace>\<lambda>_. Q e\<rbrace>"
  apply (induct "(start, e, f)" arbitrary: start rule: for_loop'.induct)
  apply (subst for_loop'.simps)
  apply clarsimp
  apply (rule conjI; wpsimp)
   apply force
  apply assumption
  done
*)

(*

lemma specific_for_loop'_wp:
  "\<lbrace> \<lambda>s. s = (main_TLB_matching_entries 0 va s0,  s0) \<and> re = ASID (CONTEXTIDR (CP15 (snd s))) \<rbrace>
      for_loop' (0, 255,
               \<lambda>i. do {
                    a \<leftarrow> trim_state (unified_mainTLB (word_of_int (int i)));
                    case a of None \<Rightarrow> return ()
                    | Some e \<Rightarrow>
                        if MatchingEntry (re, va, e) then do {
                 v \<leftarrow> read_state fst;
                 update_state (\<lambda>s. (e # v, snd s))
               } else return ()
             })
     \<lbrace>\<lambda>_ s. s = (main_TLB_matching_entries 255 va  s0,  s0) \<and> re = ASID (CONTEXTIDR (CP15 (snd s)))\<rbrace>"
  apply (rule for_loop'_wp[where e=255])
   prefer 2
   apply simp
  apply (wpsimp simp: unified_mainTLB_def)
  (*  apply (rule conjI; clarsimp; erule subst[rotated, where P=P])*)
  apply (simp add: main_TLB_matching_entries_def main_TLB_entries_def)
  done

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
  apply (simp add: for_loop')
  apply (rule l3_valid_bind_weak)
  prefer 2
  apply (rule specific_for_loop'_wp)
  apply (wpsimp simp: unified_mainTLB_def)
  apply (subgoal_tac "256 = Suc 255")
   apply (simp only: upt_Suc main_TLB_matching_entries_def main_TLB_entries_def)
  apply simp
  apply simp
  done

lemma function_state_weak:
  "(\<And>s0. \<lbrace>\<lambda>s. s = s0 \<and> Q' s \<rbrace> f \<lbrace>\<lambda>_ s. s = g s0 \<rbrace>) \<Longrightarrow> \<lbrace>\<lambda>s. P () (g s) \<and> Q' s \<rbrace> f \<lbrace>P\<rbrace>"
  by (clarsimp simp : l3_valid_def)   

lemma specific_data_tlb_for_loop'_wp:
  "\<lbrace> \<lambda>s. s = (data_TLB_matching_entries 0 va s0,  s0) \<and> re = ASID (CONTEXTIDR (CP15 (snd s))) \<rbrace>
       for_loop' (0, 31,
                  \<lambda>i. do {
                       a \<leftarrow> trim_state (DataTLB (word_of_int (int i)));
                       case a of None \<Rightarrow> return () | Some e \<Rightarrow> if MatchingEntry (re, va, e) then do {
                        v \<leftarrow> read_state fst;
                         update_state (\<lambda>s. (e # v, snd s))}
                     else return ()
                     })
     \<lbrace>\<lambda>_ s. s = (data_TLB_matching_entries 31 va ( s0),  s0) \<and> re = ASID (CONTEXTIDR (CP15 (snd s))) \<rbrace>"
  apply (rule for_loop'_wp[where e=31])
   prefer 2
   apply simp
  apply (wpsimp simp: DataTLB_def)
  apply (simp add: data_TLB_matching_entries_def data_TLB_entries_def)
  done


lemma not_sure:
  " \<lbrace>\<lambda>s. oldtlb = main_TLB s  \<and> main_TLB_entries 256 s = main_tlb_eviction 0 oldtlb\<rbrace> 
                  for_loop'
                   (0, 254,
                    \<lambda>i. do {
                         v \<leftarrow> do {
                             v \<leftarrow> read_state main_TLB;
                             return (v (word_of_int (int (254 - i))))
                           };
                         va \<leftarrow> read_state main_TLB;
                         update_state (main_TLB_update (\<lambda>_ b. if b = word_of_int (int (255 - i)) then v else va b))
                       })  \<lbrace>\<lambda>_ s. main_TLB_entries 256 s = main_tlb_eviction 254 oldtlb \<rbrace>"
  apply (rule l3_valid_weak_pre)
   apply (rule for_loop'_wp[where e=254])
    prefer 2
    apply simp
   prefer 2
   apply (clarsimp simp:  main_TLB_entries_def main_tlb_eviction_def)
  apply wpsimp
  apply (clarsimp simp:  main_TLB_entries_def main_tlb_eviction_def TLB_entries_gen_def comp_def
      take_map drop_map butlast_map)
  apply (subgoal_tac "drop (255 - i) (butlast [0..<256]) =  [255 - i..<255]")
   apply (simp only: )
   apply (subgoal_tac "drop (254 - i) (butlast [0..<256]) =  [254 - i..<255]")
    apply (simp only: )
    apply (thin_tac "drop (254 - i) (butlast [0..<256]) =  [254 - i..<255]")
    apply (thin_tac "drop (255 - i) (butlast [0..<256]) =  [255 - i..<255]")
    prefer 2
    apply (clarsimp simp: drop_butlast) 
  sorry

 
lemma
   "\<lbrace> \<lambda>s. oldtlb =  main_TLB s  \<and> main_TLB_entries 256 s = main_tlb_eviction 0 oldtlb  \<rbrace>
       for_loop
           (0, 254,
              \<lambda>i. do {
                 v \<leftarrow> do {
                     v \<leftarrow> read_state main_TLB;
                     return (v (word_of_int (int (254 - i))))
                   };
                 va \<leftarrow> read_state main_TLB;
                 update_state (main_TLB_update (\<lambda>_ b. if b = word_of_int (int (255 - i)) then v else va b))
               })  \<lbrace>\<lambda>_ s. main_TLB_entries 256 s = main_tlb_eviction 255 oldtlb \<rbrace>"
  apply (simp add: for_loop')
  apply (rule l3_valid_bind_weak)
  prefer 2
  apply (rule not_sure)
  apply (wpsimp simp: )
   apply (simp only: main_TLB_entries_def main_tlb_eviction_def TLB_entries_gen_def comp_def)
  apply simp
  sorry

(*
lemma [simp]:
  "main_tlb_eviction n (s\<lparr>micro_InstrTLB := tlb, micro_DataTLB := tlb'\<rparr>) =  main_tlb_eviction n s"
  by (clarsimp simp: main_tlb_eviction_def main_TLB_entries_def)
  

lemma [simp]:
  "main_tlb_eviction n (s\<lparr>micro_InstrTLB := tlb\<rparr>) =  main_tlb_eviction n s"
  by (clarsimp simp: main_tlb_eviction_def main_TLB_entries_def)

lemma [simp]:
  "main_tlb_eviction n (s\<lparr>micro_DataTLB := tlb\<rparr>) =  main_tlb_eviction n s"
  by (clarsimp simp: main_tlb_eviction_def main_TLB_entries_def)


lemma [simp]:
  "data_tlb_eviction n (s\<lparr>micro_InstrTLB := tlb\<rparr>) =  data_tlb_eviction n s"
  by (clarsimp simp: data_tlb_eviction_def data_TLB_entries_def)

lemma [simp]:
  "data_tlb_eviction n (s\<lparr>micro_DataTLB := tlb, micro_InstrTLB := tlb', main_TLB := tlb''\<rparr>) =  data_tlb_eviction n (s\<lparr>micro_DataTLB := tlb\<rparr>)"
  by (clarsimp simp: data_tlb_eviction_def data_TLB_entries_def)



lemma datatlb_evited_subset:
  "(tlbtypcast ` ran (\<lambda>a:: 5 word. if a = 0 then None else entries_to_TLB (data_tlb_eviction 30 s) a)) \<subseteq>
                                         (tlbtypcast ` ran (micro_DataTLB s))"
  apply (clarsimp simp: ran_def)
  apply (clarsimp simp: entries_to_TLB_def data_tlb_eviction_def data_TLB_entries_def)
  apply (rule imageI)
  apply clarsimp
  apply (rule_tac x = "a - 1" in exI)
  apply (clarsimp simp: comp_def nth_append split: if_split_asm)
  using word_unat.Rep_inject apply fastforce
  apply (subgoal_tac "[0..<32] \<noteq> []")
   prefer 2
   apply (clarsimp simp:)
  apply (drule_tac f = "\<lambda>x. micro_DataTLB s (word_of_int (int x))" in butlast_map)
  apply (simp only:)
  apply (thin_tac "butlast (map (\<lambda>x. micro_DataTLB s (word_of_int (int x))) [0..<32]) =
        map (\<lambda>x. micro_DataTLB s (word_of_int (int x))) (butlast [0..<32])")
  apply (subgoal_tac "butlast [0..<32] = [0..<31]")
   prefer 2
   apply (subgoal_tac "[0..<32] = [0..<31] @ [31] ")
    apply (simp only: butlast_snoc)
   apply (subgoal_tac "32 = Suc 31", simp only:)
    apply (subgoal_tac "0 \<le>31")
     apply (drule upt_Suc_append, simp only:)
    apply (simp only:)
   apply (simp only:)
  apply clarsimp
  apply (thin_tac " butlast [0..<32] = [0..<31]")
  apply (subgoal_tac "(unat a - Suc 0) < 31 - 0")  (* may be false *)
   apply (drule_tac f = "\<lambda>x. micro_DataTLB s (word_of_int (int x))" in nth_map_upt)
   apply (clarsimp simp: )
   apply (subgoal_tac "word_of_int (int (unat a) - 1) = a - 1 ")
    apply clarsimp
(*
proof -
  fix xa :: TLBEntry and a :: "5 word"
  assume "0 < unat a"
  then have "0 < nat (uint a)"
    by (metis unat_def)
  then have "1 + word_of_int (uint a - 1) = a"
    by (metis add_diff_cancel_left' gr0_implies_Suc semiring_1_class.of_nat_simps(2) uint_nat unat_def word_of_nat word_unat.Rep_inverse)
  then show "word_of_int (int (unat a) - 1) = a - 1"
    by (metis add_diff_cancel_left' uint_nat)
next 
*)
  sorry

 
lemma tlb_rel_lookup_not_incon:
  "\<lbrakk>tlb_rel s (typ_tlb t); dtlb_consistent (typ_tlb t) (Addr va)\<rbrakk> \<Longrightarrow> 
        lookup (tlbtypcast ` ran (micro_DataTLB s)) (ASID (CONTEXTIDR (CP15 s))) va \<noteq> TLB.lookup_type.Incon"
  apply (drule tlb_relD, clarsimp simp: typ_tlb_def cstate.defs)
  apply (drule_tac v = va and a = "asid t" in tlb_mono)
  apply (subgoal_tac "lookup (dtlb_set (tlbs_set t)) (asid t) va \<noteq> TLB.lookup_type.Incon")
  by (auto simp: consistent0_def ran_def)
 

lemma tlb_rel_evicted_hit:
  "\<lbrakk>tlb_rel s (typ_tlb t); dtlb_consistent (typ_tlb t) (Addr va);
        lookup (tlbtypcast ` ran (\<lambda>a:: 5 word. if a = 0 then None else entries_to_TLB (data_tlb_eviction 30 s) a))
         (ASID (CONTEXTIDR (CP15 s))) va = TLB.lookup_type.Hit (tlbtypcast x)\<rbrakk>
       \<Longrightarrow> lookup (tlbtypcast ` ran (micro_DataTLB s)) (ASID (CONTEXTIDR (CP15 s))) va =
           TLB.lookup_type.Hit (tlbtypcast x)"
  apply (subgoal_tac "(tlbtypcast ` ran (\<lambda>a::5 word. if a = 0 then None else entries_to_TLB (data_tlb_eviction 30 s) a)) \<subseteq>
                                         (tlbtypcast ` ran (micro_DataTLB s))")
   prefer 2
   apply (rule datatlb_evited_subset)
  apply (drule_tac v = va and a = "(ASID (CONTEXTIDR (CP15 s)))" in tlb_mono)
  apply (subgoal_tac "lookup (tlbtypcast ` ran (micro_DataTLB s)) (ASID (CONTEXTIDR (CP15 s))) va \<noteq>
                      TLB.lookup_type.Incon")
   prefer 2
   apply (clarsimp simp: tlb_rel_lookup_not_incon)
  apply (subgoal_tac "lookup (tlbtypcast ` ran (micro_DataTLB s)) (ASID (CONTEXTIDR (CP15 s))) va = TLB.lookup_type.Incon \<or>
        lookup (tlbtypcast ` ran (micro_DataTLB s)) (ASID (CONTEXTIDR (CP15 s))) va =  TLB.lookup_type.Hit (tlbtypcast x)")
   apply (erule disjE; clarsimp)
  apply (rule_tac t = "(tlbtypcast ` ran (\<lambda>a::5 word. if a = 0 then None else entries_to_TLB (data_tlb_eviction 30 s) a))" in  lookup_leq_hit_incon)
  apply clarsimp by clarsimp 

*)

lemma
  "tlbtypcast ` ran (\<lambda>a:: 5word. if a = 0 then None else from_list_to_tlb_map (data_tlb_eviction 31 (micro_DataTLB s)) a) \<subseteq>
                                         tlbtypcast ` ran (micro_DataTLB s)"
  apply (rule image_mono)
  apply clarsimp
  apply (clarsimp simp: ran_def split: if_split_asm)
  apply (clarsimp simp: from_list_to_tlb_map_def data_tlb_eviction_def TLB_entries_gen_def comp_def
      butlast_map take_map)
  apply (rule_tac x = "a" in exI)
 

oops

*)

end
