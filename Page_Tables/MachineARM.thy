(* @LICENSE(NICTA_CORE) *)

(*  Author:     Rafal Kolanski, NICTA & UNSW 

    Machine setup for 32-bit little-endian ARM.

    Machines should export the types:
    * machine_word 
    * virtual/physical address width types: paddr_word, vaddr_word

    Machines should export the functions:
    * machine_w2b - transform words to bytes (of size \<le> machine_word)
    * machine_b2w - transform bytes to words (of size \<le> machine_word)

    FIXME: these can be derived if we know paddr_word, vaddr_word
    * address types: vaddr, paddr
    * memory_size - size of physical memory address space in bytes
    * addr_space_size - size of virtual memory address space in bytes

    Understanding is: a virtual pointer carrying a virtual address resolves to
    a physical address; the smallest granularity of memory is a byte.
*)

theory MachineARM
imports Pointers Word_Lib.Word_Lib
begin

text \<open>Address types\<close>

type_synonym machine_word = "32 word"
type_synonym vaddr_word = "32 word"
type_synonym paddr_word = "32 word"

type_synonym vaddr = "(vaddr_word,virtual) addr_t"
type_synonym paddr = "(paddr_word,physical) addr_t"

translations
  (type) "paddr" <=(type) "(32 word,physical) addr_t"
  (type) "vaddr" <=(type) "(32 word,virtual) addr_t"
  (*XXX: these can be derived, but you'd have to expand vaddr_word etc.*)

text \<open>Memory size\<close>

definition
  memory_size :: nat where
  "memory_size \<equiv> 2 ^ size (addr_val(undefined::paddr))"
definition
  addr_space_size :: nat where
  "addr_space_size \<equiv> 2 ^ size (addr_val(undefined::vaddr))"

(*XXX: not derivable*)
lemma memory_size: "memory_size = 2 ^ 32" (*XXX: used to be [simp]*)
  by (simp add: memory_size_def word_size)
lemma addr_space_size: "addr_space_size = 2 ^ 32" (*XXX: used to be [simp]*)
  by (simp add: addr_space_size_def word_size)

text \<open>Endianness setup\<close>

definition
  machine_w2b :: "'a::len0 word \<Rightarrow> 8 word list" where
  "machine_w2b \<equiv> rev \<circ> word_rsplit"

definition
  machine_b2w :: "8 word list => 'b :: len0 word" where
  "machine_b2w \<equiv> word_rcat \<circ> rev"

end
