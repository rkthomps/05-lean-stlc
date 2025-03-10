# 05-STLC
Homework assignment 5 for CSE 230

**Base** ([Hw5.lean](Hw5.lean))
STLC + If
For the base points, do [Hw5.lean](Hw5.lean)

**Extra Credit** [Hw5_EC.lean](Hw5_EC.lean) 
STLC + If + Recursion
* First you must get full points in [Hw5.lean](Hw5.lean)
* Then repeat all the stuff, with the new language including `ERec`
* Of course, you can copy over / repeat any relevant bits from the [Hw5.lean](Hw5.lean) (most cases will "just work")

## Installation 
You do not have to install lean to do this assignment. Instead, you can use Github Codespaces to do the assignment with VSCode in your browser using an environment we have already set up. You can create a codespace by selecting (Code -> Create codespace). After that, you can use the same codespace across sessions of completing the assignment. When creating the codespace, please allow 1-2 minutes for the codespace to finish setting up, and 1-2 minutes for the lean language server to start.  


## Instructions
Follow the instructions in [Hw5.lean](Hw5.lean) and [Hw5_EC.lean](Hw5_EC.lean) complete definitions and proofs that are currently completed using `sorry`. 


## Grading
At any point, you may check your progress by running 
```
make grade
```
This command will show your progress on both `Hw5.lean` and `Hw5_EC.lean`. It will also show a combined score (which you can ignore). Note that you must get the full points for `Hw5.lean` before getting points on `Hw5_EC.lean` (even though the autograder may say otherwise). 

## Submitting
You can submit the assignment by running
```
make turnin
```
You may submit as often as you like. We will grade the latest submission at the assignment due date. 


## Research
During this quarter we will collect fine-grained information of edits you make to the `.lean` files in your assignments. We will use this information in the development of tools for the Lean theorem prover. You can find out more by looking at the [information sheet](InformationSheet.pdf) in this repo. This data will be kept private, besides its use by Kyle Thompson (one of the course TAs), Sorin Lerner, and their immediate collaborators. If at any point you would like to be removed from the study, please notify Kyle Thompson (r7thompson@ucsd.edu). 
