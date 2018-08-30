chapter AFP

(* Library session imported from AFP *)
session Word_Lib (AFP) in "Word_Lib" = "HOL-Word" +
  options [timeout = 300]
  theories [document = false]
    "HOL-Word.WordBitwise"
    "HOL-Library.Prefix_Order"
  theories 
    Word_Lemmas_32
    Word_Lemmas_64
  document_files
    "root.tex"


chapter TLB


session L3_LIB = Word_Lib +
  theories
    "L3_Lib/L3_Lib"
    "L3_Lib/L3_Hoare_Logic"
	"Page_Tables/PageTable_seL4"
	
	
	
session PTABLE = Word_Lib +
  theories
    "Page_Tables/PageTable_seL4"
	
	
(* MMU_ARM *)
session MMU_ARM = L3_LIB +
  theories
    "MMU_ARM/ARM_Monadic"
    


     
(*
(* Refinement *)
session ARM_REF = MMU_ARM +
  theories
    "MMU_ARMv7_Refinement/MMU_ARMv7_Ref"
    "MMU_ARMv7_Refinement_No_Fault/ARMv7_Update_ASID_Ref"
    "MMU_ARMv7_Refinement_No_Fault/ARMv7_Flush_Ref"
    "MMU_ARMv7A_Refinement/MMU_ARMv7A_Ref"
        


(* Case studies/examples on top of the model *)
session MMU_CASE = ARM_REF +
  theories
    "Ins_Cycle/Ins_Cycle"
    "Ins_Cycle/Ins_Cycle1"
    "Invalidation_Operations/Invalid_Ops"
*)

session LOGIC =  PTABLE +
   theories
   "Logic/Safe_Set" 


session CASE_STUDY =  LOGIC +
   theories
   "Case_Study/Page_Table_Ops"
