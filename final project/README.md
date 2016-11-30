# CS386L_PL_coq
Course project for CS386L programming language, using coq language

Tian Zhang ( tz3272 )

code avaialble on [github]( https://github.com/HugoTian/CS386L_PL_coq)

# Project Introduction

In this final project, I am working in program equivalence, program not equivalence, non-determinitic programming
and constant folding.

All the work is based on Imp.v and Map.v, and some idea of proof and implementation comes from advanced optional exercise from the software foundation book.

I planed to implement partial evaluation, however, all the detail are in PE.v file in the book. As a result, I just read and learn that
chapter, and do not implement my own version.



# Project Detail

* programEquivalence.v : define program equivalence and its properities, starting point of the project.
* forWhileEquiv.v : Idea comes from Midterm, prove that for and while loop are equivalent.
* programNotEquivalence.v : define and prove that program are not equivalent. Analysis arithmetic expression substitution.
* NonDeterministic.v : introduce Havoc, a non-deterministic command, and prove its behaviour equivalence. 
* ConstantFolding.v : implement constant folding for Imp language, and proof its soundness
* PartialEvaluation.v :  partial evaluation , same as PE.v, no my work in this file.
* Map.v : solution from software foundation book
* Imp.v : solution from software foundation book
* SamllStep.v : solution from software foundation book
