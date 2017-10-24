(* Library session imported from AFP *)
session Word_Lib (AFP) in "Word_Lib" = "HOL-Word" +
  options [timeout = 150]
  theories [document = false]
    "~~/src/HOL/Word/WordBitwise"
    "~~/src/HOL/Library/Prefix_Order"
  theories 
    "Word_Lemmas_32"
    "Word_Lemmas_64"
  document_files
    "root.tex"

(* Page tables for logic  *)
session PTABLE = Word_Lib +
  theories
    "./Page_Tables/PageTable_seL4"


(* Collection of base theories that change rarely *)
session L3_LIB = Word_Lib +
  theories
    "./L3_Lib/L3_Lib"
    "./Page_Tables/PageTable_seL4"

(* MMU_ARM *)
session MMU_ARM = L3_LIB +
  theories
    "./MMU_ARM/ARM_Monadic_Ops"
     

(* Refinement *)
session ARM_REF = MMU_ARM +
  theories
    "./MMU_ARMv7_Refinement/MMU_ARMv7_Ref"
    "./MMU_ARMv7_Refinement_No_Fault/Update_ASID_Refine"
    "./MMU_ARMv7_Refinement_No_Fault//Update_TTBR0_Refine"
    "./MMU_ARMv7A_Refinement/MMU_ARMv7A_Ref"
        


(* Case studies/examples on top of the model *)
session MMU_CASE = ARM_REF +
  theories
    "./Ins_Cycle/Ins_Cycle"
    "./ins_cycle/Ins_Cycle1"
    "./Invalidation_Operations/Invalid_Ops"


session LOGIC =  PTABLE +
   theories
   "./Logic/Safe_Set" 


session CASE_STUDY =  LOGIC +
   theories
   "./Case_Study/Page_Table_Ops"

