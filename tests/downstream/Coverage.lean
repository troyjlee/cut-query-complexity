import CutQueryComplexity.Coverage

/-! A downstream client resolves all twenty-three coverage exports through the public entry point. -/

-- uu-allpairs-certificate
#check @CutQueryComplexity.Certificate.UnitAllPairs.exists_unit_allPairs_certificate
-- du-global-deterministic
#check @CutQueryComplexity.Reconstruction.CompressedDirected.global_deterministic
-- du-allpairs-deterministic
#check @CutQueryComplexity.Reconstruction.CompressedDirected.allPairs_deterministic
-- du-allpairs-randomized
#check @CutQueryComplexity.Reconstruction.CompressedDirected.allPairsRandomized_success
-- du-allpairs-certificate
#check @CutQueryComplexity.Reconstruction.CompressedDirected.allPairs_certificate
-- dw-global-deterministic
#check @CutQueryComplexity.Reconstruction.WeightedDirected.deterministic_global
-- dw-terminal-deterministic
#check @CutQueryComplexity.Reconstruction.WeightedDirected.deterministic_terminal
-- dw-allpairs-deterministic
#check @CutQueryComplexity.Reconstruction.WeightedDirected.deterministic_allPairs
-- dw-global-randomized
#check @CutQueryComplexity.Reconstruction.WeightedDirected.randomized_global
-- dw-terminal-randomized
#check @CutQueryComplexity.Reconstruction.WeightedDirected.randomized_terminal
-- dw-allpairs-randomized
#check @CutQueryComplexity.Reconstruction.WeightedDirected.randomized_allPairs
-- dw-allpairs-certificate
#check @CutQueryComplexity.Reconstruction.WeightedDirected.allPairs_certificate
-- uw-global-randomized
#check @CutQueryComplexity.WeightedMinCut.Endpoint.weighted_global
-- uw-terminal-deterministic
#check @CutQueryComplexity.Reconstruction.WeightedUndirected.deterministic_terminal
-- uw-terminal-randomized
#check @CutQueryComplexity.Reconstruction.WeightedUndirected.randomized_terminal
-- uw-allpairs-deterministic
#check @CutQueryComplexity.Reconstruction.WeightedUndirected.deterministic_allPairs
-- uw-allpairs-randomized
#check @CutQueryComplexity.Reconstruction.WeightedUndirected.randomized_allPairs
-- uw-allpairs-certificate
#check @CutQueryComplexity.Reconstruction.WeightedUndirected.allPairs_certificate
-- uu-terminal-quantum
#check @CutQueryComplexity.Quantum.LinearReconstruction.exists_unit_terminal
-- uu-allpairs-quantum
#check @CutQueryComplexity.Quantum.LinearReconstruction.exists_unit_allPairs
-- du-global-quantum
#check @CutQueryComplexity.Quantum.DirectedReconstruction.global_correct
-- du-terminal-quantum
#check @CutQueryComplexity.Quantum.DirectedReconstruction.terminal_correct
-- du-allpairs-quantum
#check @CutQueryComplexity.Quantum.DirectedReconstruction.allPairs_correct

open CutQueryComplexity.Quantum.LinearReconstruction
attribute [local instance] graphWorkDecidableEq
example (n : ℕ) : (recoverGraph n 1).len = 6 * n := recoverGraph_len_unit n
example (n : ℕ) : (recoverGraph n 2).len = 12 * n := recoverGraph_len_two n

#check @CutQueryComplexity.Quantum.DirectedReconstruction.physical_global_endpoint
#check @CutQueryComplexity.Quantum.DirectedReconstruction.physical_terminal_endpoint
#check @CutQueryComplexity.Quantum.DirectedReconstruction.physical_allPairs_endpoint

-- Refinements of the weighted quantum cells to integral capacities at most W
-- uw-global-quantum, uw-terminal-quantum, uw-allpairs-quantum
#check @CutQueryComplexity.Quantum.LinearReconstruction.exists_capacity_global
#check @CutQueryComplexity.Quantum.LinearReconstruction.exists_capacity_terminal
#check @CutQueryComplexity.Quantum.LinearReconstruction.exists_capacity_allPairs
-- dw-global-quantum, dw-terminal-quantum, dw-allpairs-quantum
#check @CutQueryComplexity.Quantum.DirectedReconstruction.exists_capacity_global
#check @CutQueryComplexity.Quantum.DirectedReconstruction.exists_capacity_terminal
#check @CutQueryComplexity.Quantum.DirectedReconstruction.exists_capacity_allPairs
example (n : ℕ) : CutQueryComplexity.Quantum.DirectedReconstruction.directedBudget n 1 = 50 * n :=
  CutQueryComplexity.Quantum.DirectedReconstruction.directedBudget_unit n
