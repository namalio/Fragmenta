The following commands are used to check the metamodel:
* 'runhaskell PCs/PCs_MM.hs' checks abstract and concrete metamodel and the refinement between them.
* 'runhaskell PCS/PCs_MM.hs -g' does the base check above and generate the associated drawings (fragments, GFG, compositions, etc).
* 'runhaskell PCS/PCs_MM.hs -dt' does tbe base check and in addition generates the file 'PCs_MM_Names.hs' with the names of the metamodel to be used in the code (needed when there are new nodes or edges in the metamodel).
* 'runhaskell PCS/PCs_MM.hs -c' does the check on the individual fragments of the concrete model and corresponding type morphisms.
