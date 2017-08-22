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

(* Collection of base theories that change rarely *)
session L3_LIB = Word_Lib +
  theories
    "L3_Lib"
    "PageTable_seL4_m"

(* Main TLB and ARM model *)
session ARM_TLB = L3_LIB +
  theories
    "MMU_ARM"
    "Invalid_Ops"
    "Update_ASID_Refine"
    "Update_TTBR0_Refine"

     

(* Partial Model *)
session ARM_Part = ARM_TLB +
  theories
    "PED_Cache"
    "MMU_ARM_partial"
        

(* No_Fault Model *)
session ARM_No_Fault = ARM_TLB +
  theories
    "MMU_ARM_Refine_No_Fault"
   



(* Case studies/examples on top of the model *)
session ARM_TLB_Examples = ARM_TLB +
  theories
    "./ins_cycle/Ins_Cycle"
    "/ins_cycle/IIns_Cycle1"



session logic =  L3_LIB +
   theories
   "./logic/Boot"
   "./logic/Kernel_Execution"
   "./logic/Mode_Switch" 

