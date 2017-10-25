(* @LICENSE(NICTA_CORE) *)

(*  Author:     Rafal Kolanski, NICTA & UNSW 

    Type agnostic definition of address and pointer types.
*)

theory Pointers
imports Main
begin

text {* 
  A machine has two types of addresses: virtual and physical.
  Since very often they are the same size (e.g. 32-bit wide) we wish to 
  differentiate them at the type level.
  Convention: paddr_word is a word type of same width as physical addresses,
              vaddr_word is a word type of same width as virtual addresses
  
  The addr_t type represents the two different types of addresses, even if 
  their underlying widths are the same.
  Its parameters are the address size (such as "32 word") and the address 
  type (physical or virtual).
  *}
typedecl physical
typedecl virtual
datatype ('a, 'p) addr_t = Addr 'a

text {*
  Similarly to addr_t, we have pointers pointing to values of a specific 
  type. This type is denoted with an extra phantom type ('t).
  A typed pointer contains an addr_t.
  *}
datatype ('a, 'p, 't) ptr_t = Ptr "('a,'p) addr_t"

text {* NULL pointer (mostly used in C) *}
definition 
  NULL :: "('a::zero, 'p, 't) ptr_t" where
  "NULL \<equiv> Ptr (Addr 0)"

text {* Extraction of values/addresses from addresses/pointers. *}

fun
  addr_val :: "('a, 'p) addr_t \<Rightarrow> 'a" where
  "addr_val (Addr a) = a"
fun
  ptr_val :: "('a, 'p, 't) ptr_t \<Rightarrow> ('a,'p) addr_t" where
  "ptr_val (Ptr a) = a"

text {*
  Extracting the address from a pointer contained within a typed pointer *}
definition
  "ptr_addr x \<equiv> addr_val (ptr_val x)"

lemma addr_split: 
  "P (addr_val x) = (\<forall>y. x = Addr y \<longrightarrow> P y)"
  by (cases x, auto)

lemma addr_split_asm:
  "P (addr_val x) = (\<not>(\<exists>y. x = Addr y \<and> \<not> P y))"
  by (cases x, auto)

lemma Addr_addr_val [simp]: "Addr (addr_val i) = i"
  by (case_tac i, simp)

lemma Ptr_ptr_val [simp]: "Ptr (ptr_val i) = i"
  by (case_tac i, simp)

lemma ptr_split: 
  "P (ptr_val x) = (\<forall>y. x = Ptr y \<longrightarrow> P y)"
  by (cases x, auto)

lemma ptr_split_asm:
  "P (ptr_val x) = (\<not>(\<exists>y. x = Ptr y \<and> \<not> P y))"
  by (cases x, auto)

lemmas addr_splits = addr_split addr_split_asm
lemmas ptr_splits = addr_splits ptr_split ptr_split_asm


section {* Pointer Manipulation *}

text {* Type coertion / casting *}
fun
  ptr_coerce :: "('a,'p,'t) ptr_t \<Rightarrow> ('a,'p,'t2) ptr_t" where
  "ptr_coerce (Ptr p) = Ptr p"

text {* 
  Addition of an offset to an address. Note: adding two addresses makes 
  no sense. *}
definition
  addr_add :: "('a::semiring_1,'p) addr_t \<Rightarrow> 'a \<Rightarrow> ('a,'p) addr_t" (infixl "r+" 65) 
  where
  "a r+ x \<equiv> Addr (addr_val a + x)"

notation (latex output)
  addr_add (infixl "+" 65)

lemma addr_add_add [simp]:
  fixes a :: "('a::semiring_1, 'p) addr_t"
  shows "a r+ x r+ y = a r+ (x+y)"
  by (cases a, clarsimp simp: addr_add_def field_simps)

lemma addr_addr_add [simp]:
  fixes a :: "'a::semiring_1"
  shows "Addr a r+ x = Addr (a + x)"
  by (simp add: addr_add_def field_simps)

text {* Subtraction of an offset from an address. *}
definition
  addr_sub :: "('a::minus,'p) addr_t \<Rightarrow> 'a \<Rightarrow> ('a,'p) addr_t" (infixl "r-" 65) 
  where
  "a r- x \<equiv> Addr (addr_val a - x)"

notation (latex output)
  addr_sub (infixl "-" 65)

lemma addr_sub_sub [simp]:
  fixes a :: "('a::ring, 'p) addr_t"
  shows "a r- x r- y = a r- (x+y)"
  by (cases a, clarsimp simp: addr_sub_def)

lemma addr_addr_sub [simp]:
  fixes a :: "'a::ring"
  shows "Addr a r- x = Addr (a - x)"
  by (simp add: addr_sub_def)

text {* 
  A sequence of addresses of length n starting at a specific offset.
  Wrapping permitted. *}
primrec
  addr_seq :: "('a::semiring_1,'p) addr_t \<Rightarrow> nat \<Rightarrow> ('a,'p) addr_t list"
where
  "addr_seq p 0 = []" |
  "addr_seq p (Suc n) = p # (addr_seq (p r+ 1) n)"

lemma addr_seq_length [simp]:
  fixes p :: "('a::semiring_1,'b) addr_t"
  shows "length (addr_seq p sz) = sz"
  by (induct sz arbitrary: p, auto)


text {* Ordering of addresses/pointers *}

instantiation addr_t :: (ord,type) ord
begin
definition
  addr_less: "x < y \<equiv> addr_val x < addr_val y"
definition
  addr_le: "x \<le> y \<equiv> addr_val x \<le> addr_val y"
instance ..
end

instantiation ptr_t :: (ord,type,type) ord
begin
definition
  ptr_less: "x < y \<equiv> ptr_val x < ptr_val y"
definition
  ptr_le: "x \<le> y \<equiv> ptr_val x \<le> ptr_val y"
instance ..
end

instance addr_t :: (order,type) order
  by (intro_classes, 
      auto simp: addr_le addr_less order_less_le split: ptr_splits)

instance addr_t :: (linorder,type) linorder
  by (intro_classes, 
      simp add: addr_le linorder_linear split: ptr_splits)

instance ptr_t :: (order,type,type) order
  by (intro_classes, 
      auto simp: ptr_le ptr_less order_less_le split: ptr_splits)

instance ptr_t :: (linorder,type,type) linorder
  by (intro_classes, 
      simp add: ptr_le linorder_linear split: ptr_splits)

lemma Addr_le[simp]: "(Addr x \<le> Addr y) = (x \<le> y)"
  by (simp add: addr_le split: ptr_splits)

lemma Ptr_le[simp]: "(Ptr x \<le> Ptr y) = (x \<le> y)"
  by (simp add: ptr_le split: ptr_splits)

lemma Addr_less[simp]: "(Addr x < Addr y) = (x < y)"
  by (simp add: addr_less split: ptr_splits)
lemma Ptr_less[simp]: "(Ptr x < Ptr y) = (x < y)"
  by (simp add: ptr_less split: ptr_splits)

text {* Finiteness of pointer sets *}

lemma addr_t_UNIV: "(UNIV::('a,'p) addr_t set) = Addr ` UNIV"
  by (rule set_eqI, case_tac x, auto)
lemma ptr_t_UNIV: "(UNIV::('a,'p,'t) ptr_t set) = Ptr ` UNIV"
  by (rule set_eqI, case_tac x, auto)

instance addr_t :: (finite,type) finite
  by (intro_classes, simp add: addr_t_UNIV)

instance ptr_t :: (finite,type,type) finite
  by (intro_classes, simp add: ptr_t_UNIV)

text {* Misc *}

lemma addr_img[simp]: "(Addr x \<in> Addr ` xs) = (x \<in> xs)" by auto
lemma ptr_img[simp]: "(Ptr x \<in> Ptr ` xs) = (x \<in> xs)" by auto

end
