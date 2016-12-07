(* @LICENSE(NICTA_CORE) *)

(*  Author:     Rafal Kolanski, NICTA & UNSW 

    Instantiation of pointers and heaps to a 32-bit system, along with
    typed pointer manipulation.
*)

theory TypedHeap
imports Heaps Misc
begin

(* XXX: Gerwin points out that calling things "value" will cause problems
  later on, as valid_value already exists in seL4. "entity" is not much
  better. Best to leave it for now, then rename if it's really necessary.
*)

section {* Types *}

text {* A pointer type is a mem_type if its address type is a mem_type  *}

text {* Can I be more specific than mem_type for addrs here? *}
instantiation ptr_t :: (mem_type, type, type) mem_type
begin
definition
  "to_bytes_ptr_t \<equiv> to_bytes o ptr_addr"
definition
  "from_bytes_ptr_t \<equiv> Ptr o Addr o from_bytes"
definition
  align_of_ptr_t :: "('a,'p,'t) ptr_t itself \<Rightarrow> nat" where
  "align_of_ptr_t x \<equiv> align_of TYPE ('a)"
definition
  size_of_ptr_t :: "('a,'p,'t) ptr_t itself \<Rightarrow> nat" where
  "size_of_ptr_t x \<equiv> size_of TYPE ('a)"
definition
  type_tag_ptr_t :: "('a,'p,'t) ptr_t itself \<Rightarrow> type_tag" where
  "type_tag_ptr_t x \<equiv> ''ptr_t'' @ type_tag TYPE ('a)"
instance
  by (intro_classes)
     (simp_all add: to_bytes_ptr_t_def from_bytes_ptr_t_def 
                    size_of_ptr_t_def align_of_ptr_t_def max_size[simplified]
                    storable restorable size_length some_size max_size 
                    sane_alignment ptr_addr_def)
end

declare size_of_ptr_t_def[simp]
declare align_of_ptr_t_def[simp]


text {* Instantiations of typed pointers based on instantiated address types *}

type_synonym 't pptr = "(paddr_word,physical,'t) ptr_t"
type_synonym 't vptr = "(vaddr_word,virtual,'t) ptr_t"

translations
  (type) "'t vptr" <= (type) "(32 word,virtual,'t) ptr_t"
  (type) "'t pptr" <= (type) "(32 word,physical,'t) ptr_t"

text {* 
  For virtual/physical agnostic operations, such as loading an value from
  an address space or heap. *}
type_synonym ('a,'p) value_space = "('a,'p) addr_t \<rightharpoonup> byte"

text {* 
  Pointers can be valid with respect to specific criteria enforced by guards, 
  e.g. disallowing null pointers. 
  *}
type_synonym ('a,'p,'t) ptr_guard = "('a,'p,'t) ptr_t \<Rightarrow> bool"
type_synonym 't pptr_guard = "(paddr_word,physical,'t) ptr_t \<Rightarrow> bool"
type_synonym 't vptr_guard = "(vaddr_word,virtual,'t) ptr_t \<Rightarrow> bool"

section {* Typed Pointer Manipulation *}

text {*
  Incrementing an address in a typed pointer by a specific number of bytes *}
definition
  ptr_raw_add :: "('a::semiring_1,'p,'t::mem_type) ptr_t \<Rightarrow> 'a
              \<Rightarrow> ('a,'p,'t) ptr_t" where
  "ptr_raw_add p x \<equiv> Ptr (ptr_val p r+ x)"

text {*
   Incrementing an address in a typed pointer by multiples of the size of what
   it points to (in bytes). E.g. adding an int to a pointer in C. *}
definition
  ptr_add :: "('a::semiring_1,'p,'t::mem_type) ptr_t \<Rightarrow> 'a
              \<Rightarrow> ('a,'p,'t) ptr_t"
    (infixl "p+" 65) where
  "p p+ x \<equiv> ptr_raw_add p (x * of_nat (size_of TYPE('t)))"

notation (latex output)
  ptr_add (infixl "+" 65)

lemma ptr_add_zero [simp]:
  "p p+ 0 = p"
  unfolding ptr_add_def ptr_raw_add_def addr_add_def
  by simp

lemma ptr_add_add:
  "p p+ x p+ y = p p+ (x + y)"
  unfolding ptr_add_def ptr_raw_add_def
  by (clarsimp simp: addr_add_add field_simps)


text {*
  Decrementing an address in a typed pointer by a specific number of bytes *}
definition
  ptr_raw_sub :: "('a::{minus},'p,'t::mem_type) ptr_t \<Rightarrow> 'a
              \<Rightarrow> ('a,'p,'t) ptr_t" where
  "ptr_raw_sub p x \<equiv> Ptr (ptr_val p r- x)"

text {*
   Decrementing an address in a typed pointer by multiples of the size of what
   it points to (in bytes). E.g. subtracting an int from a pointer in C. *}
definition
  ptr_sub :: "('a::{minus,semiring_1},'p,'t::mem_type) ptr_t \<Rightarrow> 'a
              \<Rightarrow> ('a,'p,'t) ptr_t"
    (infixl "p-" 65) where
  "p p- x \<equiv> ptr_raw_sub p (x * of_nat (size_of TYPE('t)))"

notation (latex output)
  ptr_sub (infixl "-" 65)

text {* Pointer to type 't aligned as required by type 't. *}
definition
  ptr_aligned :: "('a::len word,'p,'t::mem_type) ptr_t \<Rightarrow> bool" where
  "ptr_aligned p \<equiv> align_of TYPE('t) dvd unat (ptr_addr p)"

text {* 
  A sequence of typed pointers of length n starting at a specific offset.
  Wrapping permitted. *}
fun
  ptr_seq :: "('a::semiring_1, 'p, 't::mem_type) ptr_t \<Rightarrow> nat \<Rightarrow> ('a, 'p, 't) ptr_t list" where
  "ptr_seq p 0 = []" |
  "ptr_seq p (Suc n) = p # (ptr_seq (p p+ 1) n)"

lemma map_range_Suc_manipulation: (*FIXME move to misc*)
  assumes gf: "\<And>n. g (Suc n) = f n"
  shows "(g 0) # map f [0..<n] = map g [0..<Suc n]"
proof -
  have ss: "[Suc 0..<Suc n] = map Suc [0..<n]"
    by (subst map_Suc_upt[symmetric], rule refl)
  show ?thesis
  apply (subst upt_conv_Cons, simp)
  apply (subst ss)
  apply (simp add: gf)
  done
qed

lemma ptr_seq_as_map:
  fixes base :: "('a::semiring_1, 'p, 't::mem_type) ptr_t"
  shows "ptr_seq base sz = map (\<lambda>i. base p+ (of_nat i)) [0..<sz]"
proof (induct sz arbitrary: base)
  case 0 thus ?case by simp
next
  case (Suc n)
  hence IH: "\<And>(base::('a::semiring_1, 'p, 't::mem_type) ptr_t). ptr_seq base n = map (\<lambda>i. base p+ of_nat i) [0..<n]"
    by - assumption
  show ?case
    apply (clarsimp simp only: ptr_seq.simps IH)
    apply (subst map_range_Suc_manipulation[symmetric])
     apply (auto simp: ptr_add_add field_simps)
    done
qed

end
