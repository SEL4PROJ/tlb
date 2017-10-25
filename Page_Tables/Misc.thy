(* @LICENSE(NICTA_CORE) *)

(*  Author:     Rafal Kolanski, NICTA & UNSW 

    Miscellaneous development support.
*)

theory Misc
imports
  Word_Lib.Word_Enum

begin

(* from l4v/lib/Lib: *)
definition
  pred_conj :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)" (infixl "and" 35)
where
  "pred_conj P Q \<equiv> \<lambda>x. P x \<and> Q x"

definition
  pred_disj :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)" (infixl "or" 30)
where
  "pred_disj P Q \<equiv> \<lambda>x. P x \<or> Q x"

definition
  pred_neg :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)" ("not _" [40] 40)
where
  "pred_neg P \<equiv> \<lambda>x. \<not> P x"

definition "K \<equiv> \<lambda>x y. x"


text \<open>Reversed composition of partial functions\<close>
definition
  fun_rcomp_option :: "('a \<rightharpoonup> 'b) \<Rightarrow> ('b \<rightharpoonup> 'c) \<Rightarrow> ('a \<rightharpoonup> 'c)" (infixl "\<rhd>o" 55)
where
  "fun_rcomp_option f g \<equiv> (\<lambda>x. case f x of Some y \<Rightarrow> g y | None \<Rightarrow> None)"  

lemmas rco_def = fun_rcomp_option_def

lemma rco_middle_exists: 
  "(a \<rhd>o b) x = Some y \<Longrightarrow> \<exists>z. a x = Some z \<and> b z = Some y"
  by (clarsimp simp add: rco_def split: option.splits)

lemma rco_dom_left: "(vs \<rhd>o hs) v = Some val \<Longrightarrow> v \<in> dom vs"
  by (clarsimp simp add: rco_def cong: option.case_cong split: option.splits)

text \<open>Option magic\<close>

lemma None_not_eq [simp]: "(None \<noteq> x) = (\<exists>y. x = Some y)" by (cases x) auto
lemma None_com: "(None = x) = (x = None)" by fast
lemma Some_com: "(Some y = x) = (x = Some y)" by fast

lemma option_case_None_Some [simp]:
  "case_option None Some P = P"
  by (simp split: option.splits)

lemma map_the_map_Some [simp]:
  "map the (map Some xs) = xs"
  by (induct xs, auto)

lemma theSome [simp]: "the \<circ> Some = id"
  by (auto intro!: ext)



lemma allE2: "\<lbrakk> \<forall>x y. P x y ; P x y \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R" by blast
lemma allE3: "\<lbrakk> \<forall>x y z. P x y z ; P x y z \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R" by blast

lemma exI2: "P x y \<Longrightarrow> \<exists>x y. P x y" by blast
lemma exI3: "P x y z \<Longrightarrow> \<exists>x y. P x y z" by blast

lemma pred_conj_com:
  "(P and Q) = (Q and P)" 
  by (intro ext, simp add: pred_conj_def conj_commute) (*WTF:conj_commute?*)

lemma pred_conj_assoc:
  "(P and Q and R) = (P and (Q and R))"
  by (auto simp: pred_conj_def intro: ext)

lemma pred_conj_left_commute:
  "(P and (Q and R)) = (Q and (P and R))"
  by (intro ext, simp add: pred_conj_def conj_ac) (*WTF:conj_ac?*)

lemmas pred_conj_ac = pred_conj_assoc pred_conj_com pred_conj_left_commute

lemma set_double_minus:
  "A - B - C = A - (C \<union> B)"
  by blast

(* XXX: this should be in our word library somewhere *)

lemma twice_le_div:
  "n \<le> m div 2 \<Longrightarrow> 2 * n \<le> (m :: nat)"
  by simp


lemmas twice_le_div_trans = twice_le_div [OF order_trans]

lemma map_id [simp]: "map id xs = xs"
  by (induct xs, auto)

lemma length_obvious_assist:
  "xs = [] \<Longrightarrow> 0 < length xs \<Longrightarrow> False"
  by auto

lemma list_index_in_list:
  "lst ! i = v \<Longrightarrow> i < length lst \<Longrightarrow> v \<in> set lst"
  by auto

text \<open>Drop first or second part of pairs in the range of a map.\<close>

definition
  fst_all_opt :: "('a \<rightharpoonup> 'b \<times> 'c) \<Rightarrow> ('a \<rightharpoonup> 'b)" where
  "fst_all_opt m \<equiv> (map_option fst) \<circ> m"

definition
  snd_all_opt :: "('a \<rightharpoonup> 'b \<times> 'c) \<Rightarrow> ('a \<rightharpoonup> 'c)" where
  "snd_all_opt m \<equiv> (map_option snd) \<circ> m"

text \<open>List take/drop folding, useful when (un)serialising serialisables\<close>

lemma list_take_take_drop: 
  "take i x @ take j (drop i x) = take (i+j) x"
proof (induct x arbitrary: i)
  case Cons thus ?case by (cases i, auto)
qed simp

lemma list_take_drop_drop:
  assumes k: "k = i + j"
  shows "take i (drop j x) @ (drop k x) = drop j x"
proof -
  have "take i (drop j x) @ drop (i + j) x = drop j x"
  proof (induct x arbitrary: j)
    case Cons thus ?case by (cases j, auto)
  qed auto
  thus ?thesis using k by simp
qed

end