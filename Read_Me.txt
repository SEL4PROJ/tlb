Files Information:

ARM_Monadic     - Initial Definitions of ARM Model upto memory write and read functions
                  Memory operations included:
                    1) mem1       :: "paddr ⇒ 'a state_scheme ⇒ bool list × 'a state_scheme"
                    2) mem_read1  :: "paddr × nat ⇒ 'b state_scheme ⇒ bool list × 'b state_scheme"
                    3) write'mem1 :: "bool list × paddr × nat ⇒ 'b state_scheme ⇒ unit × 'b state_scheme"


MMU_Ops         - classes definitions of MMU operations

ARM_Monadic_Ops - All of the remaining functions of ARM Model

MMU_ARM         - Instantiating definitions of MMU operations
                  MMU Refinement theorems
