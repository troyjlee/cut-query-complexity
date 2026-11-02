import CutQueryComplexity.StarContraction2022.Contraction.TwoOut.Components

/-!
The two-out construction and its component-count tail. The implementation
processes an actual sampled tape, conditions on complete processed-row
histories, and charges components to its constructed representatives.

The tail includes the number of deficient source rows explicitly. The
probability estimate uses conditional phase bounds and linearity of
expectation; it does not require independence between processing phases.
-/

#print axioms CutQueryComplexity.StarContraction2022.Contraction.TwoOut.componentCount_tail
#print axioms CutQueryComplexity.StarContraction2022.Contraction.TwoOut.componentCount_tail_of_forty
