# A proof of Baire's theorem (locally compact version) written in Coq

## The proof
The proof of the theorem is based on the one given here (in French): http://web.archive.org/web/20210414180128/http://www.les-mathematiques.net/c/a/b/node4.php

Several statements on compact sets are needed for the proof, and Proposition 2.3 on https://ncatlab.org/nlab/show/locally+compact+topological+space can be useful to better understand what is going on. 

The complete-metric-space version of Baire's theorem had been formalized with SSReflect: https://github.com/CuMathInfo/Topology/blob/master/BingShrinkingCriterion/BaireSpaces.v

However, to my knowledge (when I wrote this in 2021), this version of the theorem had never been formalized before.

## Files hierarchy
X > Y means "X depends on Y"

**BExamples.v > Baire.v > BCompactness.v > BTopSpace.v > BOrder.v > BFamily.v > BSet.v > BLogic.v**

BExamples.v contains an example of a topological space, namely cofinite sets of **N**. (Unfortunately it is not Hausdorff, so Baire's theorem cannot be applied to it

## To compile the project
First run the command
`coq_makefile -f _CoqProject -o Makefile`

And then `make`

