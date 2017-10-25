(* @LICENSE(NICTA_CORE) *)

(*  Author:     Rafal Kolanski, NICTA & UNSW 

    Generic definition of a page table.
*)

theory PageTable
imports MapExtra
begin

text \<open>
  The information on how the virtual address space is laid out is contained in
  the heap itself in the form of a page table. The page table has a base, which
  consists of one or more entrypoints (e.g. a page table root).
  Given the base, a vmap is obtainable from the heap (see Heap.thy).

  NOTE: All addresses touched in a lookup of a vaddr are to be in the trace,
  even if the vaddr is not mapped. Unallocated physical addresses must not be
  in the trace. This should allow saying things like "before the op, vp mapped
  halfway; after the op, it maps fully" for 2-level page tables.
  If an entry can't be loaded, such as when 3 bytes of a 4 byte entry are 
  mapped, the entry should not be in the trace.

  NOTE: For a single and two-level page tables without superpages, get_page 
  can be calculated from just the virtual address. With superpages, we actually
  need to look into the page table itself to figure out what kind of page an 
  address is on. It also becomes pointless to talk about what page an unmapped
  virtual address is on. As to what a "page" that get_page returns is, the 
  locale is purposefully ambiguous.

  XXX: accurate, but not addressed in this locale
  Modifying the heap is easier to reason about when it does not modify the page
  table. Hence, we are interested in all physical addresses that describe it. 

  XXX: consider how to shove permissions in here... do it like get_page?
  
  Not all bases are valid (e.g. due to address space overflow given a 
  too-large root). Implemenations of page tables should supply their own 
  version and assume the property holds. In proofs, it should be a guard. 
\<close>
locale pagetable =
  -- "Obtaining the virtual map"
  fixes ptable_lift :: "('paddr \<rightharpoonup> 'val) \<Rightarrow> 'base \<Rightarrow> 'vaddr \<rightharpoonup> 'paddr"
  -- "Tracing vaddr lookup"
  fixes ptable_trace :: "('paddr \<rightharpoonup> 'val) \<Rightarrow> 'base \<Rightarrow> 'vaddr \<Rightarrow> 'paddr set"
  -- "Obtain page from virtual ptr"
  fixes get_page :: "('paddr \<rightharpoonup> 'val) \<Rightarrow> 'base \<Rightarrow> 'vaddr \<Rightarrow> 'a"

  -- "the frame property"
  assumes ptable_lift_reduce:
  "\<lbrakk> ptable_lift (h\<^sub>0 ++ h\<^sub>1) r vp = Some p; h\<^sub>0 \<bottom> h\<^sub>1 \<rbrakk> 
   \<Longrightarrow> ptable_lift h\<^sub>0 r vp = Some p \<or> ptable_lift h\<^sub>0 r vp = None"

  -- "monotonicity of lift in heap merge"
  (* FIXME: why is this not a disj_add_simp?! *)
  assumes ptable_lift_disj_add:
  "\<lbrakk> ptable_lift h\<^sub>0 r vp = Some p; h\<^sub>0 \<bottom> h\<^sub>1 \<rbrakk> 
   \<Longrightarrow> ptable_lift (h\<^sub>0 ++ h\<^sub>1) r vp = Some p"

  -- "monotonicity of trace in heap merge"
  assumes ptable_trace_disj_add_simp:
  "\<lbrakk> ptable_lift h r vp = Some p ; h \<bottom> h' \<rbrakk> 
   \<Longrightarrow> ptable_trace (h ++ h') r vp = ptable_trace h r vp"

  -- "update outside the trace does not affect lift"
  assumes ptable_lift_preserved:
  "\<lbrakk> p \<notin> ptable_trace h r vp; ptable_lift h r vp = Some p \<rbrakk> 
   \<Longrightarrow> ptable_lift (h (p \<mapsto> v)) r vp = Some p" 

  -- "update outside the trace does not affect trace"
  assumes ptable_trace_preserved:
  "\<lbrakk>p \<notin> ptable_trace h r vp; 
    ptable_lift h r vp = Some p\<rbrakk>
  \<Longrightarrow> ptable_trace (h (p \<mapsto> v)) r vp = ptable_trace h r vp"

begin

lemma ptable_lift_mono:
  assumes nolift: "ptable_lift (h\<^sub>0 ++ h\<^sub>1) r vp = None"
  assumes disj: "h\<^sub>0 \<bottom> h\<^sub>1"
  shows "ptable_lift h\<^sub>0 r vp = None"
proof (rule classical)
  assume "ptable_lift h\<^sub>0 r vp \<noteq> None"
  thus ?thesis using nolift disj
    by (auto dest: ptable_lift_disj_add)
qed

lemma not_in_ptable_trace_update:
  "\<lbrakk> p \<notin> ptable_trace h r vp; 
    ptable_lift h r vp = Some p \<rbrakk>
   \<Longrightarrow>
   p \<notin> ptable_trace (h (p \<mapsto> v)) r vp"
  by (simp add: ptable_trace_preserved)
end

end
