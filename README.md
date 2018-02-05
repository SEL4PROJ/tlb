[![Build Status](https://travis-ci.org/SEL4PROJ/tlb.svg?branch=ITP18)](https://travis-ci.org/SEL4PROJ/tlb)

This folder contains .thy files for the project

##  Program Verification in the Presence of Cached Address Translation


The theories files in this repository are for [Isabelle2017][1].

To check the proofs, run

    Isabelle2017/bin/isabelle build -bv -d . CASE_STUDY

###### Theorems Information:

Theorems referred in the paper are

`safe_set_preserved:` Logic/Safe_Set.thy

`weak_pre_write:` Logic/Safe_Set.thy

`user_safe_assignment:` Case\_Study/User\_Execution.thy

`kernel_safe_assignemnt:` Case\_Study/Kernel\_Execution.thy

`context_switch_invariants:` Case\_Study/Mode\_Switch.thy


For refinement of the TLB model, please see the folder `MMU_ARMv7_Refinement_No_Fault`

###### Folder Information:

`Word_Lib:`
         extension to the Isabelle library for fixed-width
         machine words

`Page_Tables:`
         page table model for ARM architecture

`L3_Lib:`
         L3 library for ARM monadic model

`MMU_ARM:`
         TLB and MMU model embedded in ARM monadic model 


`MMU_ARMv7_Refinement:`
         refinement of ARMv7 memory operations

`MMU_ARMv7A_Refinement:`
         refinement of ARMv7A memory operations

`MMU_ARMv7_Refinement_No_Fault:`
         relaxed model and refinement for memory 
         model of program logic
		 refinement of root and asid update 

`Ins_Cycle:`
         instruction testing for MMU embedded in 
         ARM monadic model

`Invalidation_Operations:`
         TLB invalidation instructions for MMU embedded 
         in ARM monadic model

`Eisbach:`
         Eisbach tools for program logic

`Logic:`
         memory model, program logic and simplification 
         by safe set

`Case_Study:`
          os memory layout, reasoning for kernel- and 
          user-level executions, context switching 
          and page table operations



[1]: http://isabelle.in.tum.de "Isabelle Website"
