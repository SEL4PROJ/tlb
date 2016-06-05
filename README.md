A formal TLB model for ARM
==========================

Work in progress to formalise (in [Isabelle/HOL][1]) the behaviour of the ARM
TLB (translation lookaside buffer) and develop that model into a program
logic that can be used to reason about programs in the presence of a TLB and
memory management unit.

These theories integrate with [Cambridge ARM model][2] by Fox et al.

Overview:

 * `TLB.thy`: base TLB model and theorems
 
 * `ARM_Monadic.thy`: the Cambridge ARM model, extended with read/write translation through the TLB.
 
 * `TLB_Refine.thy`: steps towards program logic, refinement stack for more abstract TLB models.
 
 * `L3_Lib.thy` and `L3.ML` slightly modified from upstream ARM model to include monad syntax.


Build
-----

You can run the theories in [Isabelle/HOL][1] with the following command:

    isabelle build -vD .


[1]: http://isabelle.in.tum.de
[2]: https://www.cl.cam.ac.uk/~acjf3/l3/isabelle/
