theory MMU_Ops

imports ARM_Monadic

begin



class mmu =
  fixes mmu_translate :: "vaddr \<Rightarrow> 'a state_scheme \<Rightarrow> paddr \<times> 'a state_scheme" 


class mem_op =
  fixes mmu_read :: "vaddr \<Rightarrow> 'a::mmu state_scheme \<Rightarrow> bool list \<times> 'a::mmu state_scheme"
  fixes mmu_read_size :: "vaddr \<times> nat  \<Rightarrow> 'a::mmu state_scheme \<Rightarrow> bool list \<times> 'a::mmu state_scheme"
  fixes mmu_write_size :: "bool list \<times> vaddr \<times> nat \<Rightarrow> 'a::mmu state_scheme \<Rightarrow> unit \<times> 'a::mmu state_scheme"

end