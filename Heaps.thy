(* @LICENSE(NICTA_CORE) *)

(*  Author:     Rafal Kolanski, NICTA & UNSW 

    Generic heap definitions and manipulations instantiated to a machine.
*)

theory Heaps
imports MemTypes WordTypes
begin

section {* Memory Views *}

text {*
  Apart from the heap, representing the physical machine memory, we recognise
  the virtual address map (mapping each virtual address to a physical one) and
  the virtual address space (mapping each virtual address to a byte).
  
  You can obtain a virtual map from lifting the page table from the heap, and
  an address space from combining a vmap and heap.
  
  All maps are partial. On the physical side, this denotes memory that has been
  allocated. On the virtual side, memory that has been mapped. Allocated memory
  may be unmapped, mapped memory may be unallocated.
  
  The heap is partial, defined on areas used by the program.

  A value space is a partial map from any kind of address to bytes.
  *}
type_synonym vmap = "vaddr \<rightharpoonup> paddr"
type_synonym heap = "paddr \<rightharpoonup> byte"
type_synonym addr_space = "vaddr \<rightharpoonup> byte"

translations
  (type) "vmap" <=(type) "vaddr \<rightharpoonup> paddr"
  (type) "heap" <=(type) "paddr \<rightharpoonup> byte"
  (type) "addr_space" <=(type) "vaddr \<rightharpoonup> byte"

type_synonym ('a,'p) value_space = "('a,'p) addr_t \<rightharpoonup> byte"


section {* Object Loading *}

text {* Obtaining a list of values (i.e. bytes) from a map with an addr_t domain. *}

primrec
  load_list_basic :: "(('a::semiring_1,'p) addr_t \<rightharpoonup> 'val) \<Rightarrow> nat 
                      \<Rightarrow> ('a,'p) addr_t \<Rightarrow> 'val option list"
where
  "load_list_basic h 0 p = []" |
  "load_list_basic h (Suc n) p = h p # load_list_basic h n (p r+ 1)"

definition
  deoption_list :: "'a option list \<rightharpoonup> 'a list" where
  "deoption_list xs \<equiv> if None \<in> set xs then None else Some (map the xs)"

definition
  "load_list h n p \<equiv> deoption_list (load_list_basic h n p)"

lemma length_load_list_basic [simp]:
  "length (load_list_basic h sz p) = sz"
  by (induct sz arbitrary: p, auto)


section {* Loading Objects from the Heap/Address Space *}

text {* Retrieving a stored value on the heap or addr\_space *}
(* FIXME: ugly return-type overloading, improve? *)

definition
  load_value :: "('a::semiring_1,'p) value_space \<Rightarrow> ('a,'p) addr_t 
                  \<rightharpoonup> ('t::mem_type)" where
  "load_value h p \<equiv> (case load_list h (size_of TYPE('t)) p 
                       of None \<Rightarrow> None
                        | Some bs \<Rightarrow> Some (from_bytes bs))"

(* update form Hira: changed Option.map to map_option *)
lemma load_value_def2:
  "((load_value h p)::'t option) \<equiv> map_option from_bytes (load_list h (size_of TYPE('t::mem_type)) p)"
  by (auto intro!: eq_reflection simp: load_value_def split: option.splits)

definition
  load_machine_word :: "('a::semiring_1,'p) value_space \<Rightarrow> ('a,'p) addr_t 
                        \<rightharpoonup> machine_word" where
  "load_machine_word \<equiv> load_value"

subsection {* Loading Objects After Unrelated Heap Updates *}

lemma load_list_basic_update_eq:
  assumes p: "p \<notin> set (addr_seq start sz)"
  shows "load_list_basic (h(p \<mapsto> v)) sz start = load_list_basic h sz start"
  using p proof (induct sz arbitrary: start)
  case 0 thus ?case by simp
next
  case (Suc sz start)
  hence IH: "p \<notin> set (addr_seq (start r+ 1) sz)
             \<Longrightarrow> load_list_basic (h(p \<mapsto> v)) sz (start r+ 1) = 
                 load_list_basic h sz (start r+ 1)"
    and ps: "p \<notin> set (addr_seq start (Suc sz))" by - assumption
  (*WTF:blast or simp don't work here? why?*)

  from ps have "p \<notin> set (addr_seq (start r+ 1) sz)" by auto

  hence "load_list_basic (h(p \<mapsto> v)) sz (start r+ 1) = 
           load_list_basic h sz (start r+ 1)" using IH by simp

  moreover 

  have "(\<lambda>a. if a = p then Some v else h a) = h(p \<mapsto> v)"
    by (rule ext, auto)

  moreover

  have "p \<noteq> start" using ps
    proof -
      assume "start = p"
      hence "p \<in> set (addr_seq start (Suc sz))" by simp
    qed (auto)

  ultimately show ?case by (clarsimp)
qed

lemma load_list_update_eq:
  "\<lbrakk> p \<notin> set (addr_seq start sz) \<rbrakk>
   \<Longrightarrow> load_list (h(p \<mapsto> v)) sz start = load_list h sz start"
  unfolding load_list_def deoption_list_def 
  by (simp add: load_list_basic_update_eq)

lemma load_value_update_eq:
  "\<lbrakk> p \<notin> set (addr_seq start (size_of TYPE('a::mem_type))) \<rbrakk>
   \<Longrightarrow> load_value (h(p \<mapsto> v)) start = ((load_value h start)::'a option)"
  unfolding load_machine_word_def load_value_def Let_def
  by (simp add: load_list_update_eq)

lemma load_list_basic_nth [simp]:
  fixes p :: "('a::len word,'b) addr_t"
  shows "i < sz \<Longrightarrow> load_list_basic h sz p ! i = h (p r+ (of_nat i))"
proof (induct sz arbitrary: p i)
  case 0 thus ?case by simp
next
  case (Suc sz)
  thus ?case
  by (clarsimp simp: nth_Cons')
     (cases i, auto simp add: addr_add_def add_ac split: nat.split)
qed

end
