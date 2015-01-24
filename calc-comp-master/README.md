Calculating Correct Compilers
=============================

This repository contains the supplementary material for the paper
["Calculating Correct Compilers"](http://www.diku.dk/~paba/pubs/files/bahr14jfp-preprint.pdf)
by Patrick Bahr and Graham Hutton.  The material includes Coq
formalisations of all calculations in the paper. In addition, we also
include Coq formalisations for calculations that were mentioned but
not explicitly carried out in the paper.

The Coq proofs proceed as the calculations in the paper. There are,
however, two minor technical difference due to the nature of the Coq
system.

  1. In the paper the derived VMs are tail recursive, first-order
     functions. The Coq system must be able to prove termination of
     all recursive function definitions. Since Coq's termination
     checker is not powerful enough to prove termination for some of
     the VMs (VMs from sections 3.1, 4.1, 5) or the VMs are not
     expected to terminate in general (VMs for lambda calculi / for
     language with loops), we had to define the VMs as relations
     instead. In particular, all VMs are defined as a small-step
     semantics. Each tail recursive function of a VM corresponds to a
     configuration constructor in the small-step semantics. As a
     consequence, the calculations do not prove equations, but rather
     instances of the relation =>>, which is the transitive, reflexive
     closure of the relation ==> that defines the VM.

  2. The Coq files contain the final result of the calculation, and
     thus do not reflect the /process/ of discovering the definition
     of the compiler and the VM. That is, the files already contain
     the full definitions of the compiler and the virtual machine. But
     we used the same methodology as described in the paper to
     /develop/ the Coq proofs. This is achieved by initially defining
     the Code data type as an empty type, defining the VM relation as
     an empty relation (i.e. with no rules), and defining the compiler
     function using the term "Admit" (which corresponds to Haskell's
     "undefined"). This setup then allows us to calculate the
     definition of the Code data type, the VM, and the compiler as
     described in the paper.

Below we list the relevant Coq files for the calculations in the
paper:

 - [Arith.v](Arith.v): arithmetic expressions (section 2)
 - [Exceptions.v](Exceptions.v): exceptions, first approach (section 3.1)
 - [ExceptionsTwoCont.v](ExceptionsTwoCont.v): exceptions, second
   approach (section 3.2)
 - [StateGlobal.v](StateGlobal.v): global state (section 4.1)
 - [StateLocal.v](StateLocal.v): local state (section 4.2)
 - [Lambda.v](Lambda.v): call-by-value lambda calculus (section 5)

In addition we also include calculations for the following languages:

 - [LambdaCBName.v](LambdaCBName.v): call-by-name lambda calculus
 - [LambdaCBNeed.v](LambdaCBNeed.v): call-by-need lambda calculus
 - [Loop.v](Loop.v): a simple imperative language with while loops

The remaining files are used to define the Coq tactics to support
reasoning in calculation style ([Tactics.v](Tactics.v)) and to specify
auxiliary concepts ([Heap.v](Heap.v), [ListIndex.v](ListIndex.v)). We
recommend using the
[generated documentation](http://pa-ba.github.io/calc-comp/doc/toc.html)
to browse the Coq files.

The formalisations were developed using version 8.4pl4 of the Coq
system.
