(* @LICENSE(NICTA_CORE) *)

(*  Author:     Rafal Kolanski, NICTA & UNSW 

    Definition of the mem_type class (types which we can store on the heap as
    a sequence of bytes).
*)

theory MemTypes
imports MachineARM
begin

(*XXX: someone removed this in the main repo, where should it go now?*)
type_synonym byte = "8 word"

type_synonym type_tag = string
(*TODO: when working on structure types, this should be moved to where all the other stuff is defined (atomic/structure types etc) (XXX or removed when dropping the tagged heap *)

text {*
  The @{text "mem_type"} class represents a C-like values storable in memory.
  They:
   * must be convertable to a series of bytes, reversibly
   * the number of bytes used must be constant for the type, irrespective
     of value, so if we append its encoding to a byte stream, we know how
     many bytes to take off again to decode, thus knowing where the ``rest''
     of the stream is (e.g. encoding as part of a larger structure)
   * must have a nonzero size in bytes that is smaller than both the physical
     and virtual address spaces
   * may require an alignment that divides the both the physical and virtual
     address space sizes
*}
class mem_type = 
  -- "size of value in bytes"
  fixes size_of :: "'a itself \<Rightarrow> nat"
  assumes some_size: "0 < size_of (TYPE('a))"
  assumes max_size: "size_of (TYPE('a)) < min memory_size addr_space_size"

  fixes to_bytes :: "'a \<Rightarrow> byte list"
  fixes from_bytes :: "byte list \<Rightarrow> 'a"
  assumes storable: "from_bytes (to_bytes v) = v"
  assumes size_length: "length (to_bytes v) = size_of TYPE('a)"
  assumes restorable: "length bs = size_of TYPE('a)
                       \<Longrightarrow> to_bytes (from_bytes bs) = bs"

  -- "required alignment of value in bytes"
  fixes align_of :: "'a itself \<Rightarrow> nat"
  assumes sane_alignment: "align_of (TYPE('a)) dvd memory_size \<and>
                           align_of (TYPE('a)) dvd addr_space_size"
  -- "a unique type tag for this type of value"
  fixes type_tag :: "'a itself \<Rightarrow> type_tag"
  (*XXX: redundant since tags removed, but could be useful otherwise *)

begin

definition
  mem_type_decode :: "byte list \<Rightarrow> ('a \<times> byte list)" where
  "mem_type_decode bs \<equiv> let sz = size_of TYPE('a) in
                       (from_bytes (take sz bs), drop sz bs)"

lemma snd_mem_type_decode:
  "snd (mem_type_decode bs) = drop (size_of TYPE('a)) bs"
  unfolding mem_type_decode_def Let_def
  by simp (*XXX: unused?*)

end

text {* Extra mem\_type lemmas. *}

lemma to_bytes_nil_all:
  assumes a: "to_bytes (x::'a::mem_type) = []"
  shows "to_bytes (y::'a::mem_type) = []"
proof -
  have "length (to_bytes x) = length (to_bytes y)"
    by (simp add: size_length)
  thus ?thesis using a by auto
qed


text {* 
  In order to make records mem_types, we need to disregard their ability to
  be extended. When we discard the @{text "more"} part of a record for 
  encoding, we must somehow still reconstruct it after decoding. What we
  really want is to have a class of records extending unit. A class containing
  only unit isn't possible, but a class of types with only one member is
  sufficient, as @{text "undefined"} is a reliable reconstruction of any
  discarded extension.
*}
class unitary =
  fixes the_value :: "'a" 
  assumes only_one_value: "(x::'a) = y" (* Unused. Required to fix 'a. *)
(* XXX: this isn't currently used at Michael N's C parser uses L4 records which
        don't support extending, but do support recursive records *)

instance unit :: unitary (* XXX: magically ignores one_value instantiation *)
  by (intro_classes, simp)

lemma "x dvd memory_size \<Longrightarrow> 0 < x"
  (*XXX: not sure we'll need this, but we definitely don't need it as an assumption on alignment*)
  by (case_tac x, auto simp: memory_size)

end
