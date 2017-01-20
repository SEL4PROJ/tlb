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
	"Program_Logic"

(* Case studies/examples on top of the model *)
session ARM_TLB_Examples = ARM_TLB +
  theories
    "Ins_Cycle"
    "Ins_Cycle1"
