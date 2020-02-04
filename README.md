[![Build Status](https://travis-ci.org/SEL4PROJ/tlb.svg?branch=jar19)](https://travis-ci.org/SEL4PROJ/tlb)


This folder contains .thy files for the project

##  Formal Reasoning under Cached Address Translation


The theories files in this repository are for [Isabelle2018][1].

To check the proofs, run

    Isabelle2018/bin/isabelle build -bv -d . TLB_PDC_REFJ

###### Theorems Information:

Theorems referred in the paper are

`user_safe_assignment:` Logic/User\_Execution.thy

`kernel_safe_assignment:` Logic/Kernel\_Execution.thy

`context_switch_invariants:` Logic/Context\_Switch.thy

Reasoning about page table operations is present in Logic/Page\_Table\_Ops.thy
For refinement of the two-stage TLB model, please see the folder `TLB_PDC`

###### Folder Information:

`Word_Lib:`
         extension to the Isabelle library for fixed-width
         machine words

`Page_Tables:`
         page table model for ARM architecture

`L3_Lib:`
         L3 library for ARM monadic model

`TLB_No_ASID:`
         MMU model and refinement theorems for single-stage TLB
		 without ASIDs, basic TLB modeling for two-stage TLB


`TLB_ASID:`
         MMU model and refinement theorems for single-stage TLB
		 with ASIDs and global tags, basic TLB modeling for two-stage TLB

`TLB_PDC:`
         MMU model and refinement theorems for two-stage TLB
		 with ASIDs and global tags, as presented in the paper


`Eisbach:`
         Eisbach tools for program logic

`Logic:`
         memory model, program logic, simplification
         by safe set, os memory layout, reasoning for kernel-level
		 and user-level executions, context switching
         and page table operations





[1]: http://isabelle.in.tum.de "Isabelle Website"
