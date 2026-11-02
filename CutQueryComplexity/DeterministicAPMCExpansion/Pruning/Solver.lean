import CutQueryComplexity.DeterministicAPMCExpansion.Pruning.CutAlgebra
import CutQueryComplexity.DeterministicAPMCExpansion.Flow.SharpBudget
import CutQueryComplexity.DeterministicAPMCExpansion.Flow.StarCut

/-!
# Producing the pruning minimum shore by the actual exact-flow program

The program receives only the public scale, half-degree parameter, and fake
degree table. It computes an exact flow and returns the original vertices of
the final residual shore. No minimizer or hidden graph is a program input.
The fake graph and its expansion certificate are used only in the semantic
composition theorem, after they have been constructed by matching rounds.
-/

set_option autoImplicit false

namespace CutQueryComplexity.DeterministicAPMCExpansion.Pruning

open Finset Flow AllPairsAudit
open scoped Classical
noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V]

def sourceShore (P : Finset V) : Finset (NetworkVertex V) :=
  insert source (P.map Function.Embedding.inl)

@[simp] theorem source_mem_sourceShore (P : Finset V) : source ∈ sourceShore P := by
  simp [sourceShore]

@[simp] theorem sink_notMem_sourceShore (P : Finset V) : sink ∉ sourceShore P := by
  simp [sourceShore, source, sink]

@[simp] theorem originalShore_sourceShore (P : Finset V) :
    originalShore (sourceShore P) = P := by
  ext v
  simp [sourceShore, source]

theorem pruning_cut_objective (J : WeightedGraph V) (R t : ℕ) (a : V → ℕ)
    (A : Finset (NetworkVertex V)) (hs : source ∈ A) (ht : sink ∉ A) :
    (twoStar (scaledInternal J R) a (fun _ => t)).cut A =
      starObjective J (fun v => (a v : ℝ)) (2 * t) R (originalShore A) := by
  rw [twoStar_source_cut _ _ _ _ hs ht]
  simp only [scaledInternal, WeightedGraph.cut_scale, sum_const, nsmul_eq_mul]
  have hsum := sum_shore_add_compl (fun v => (a v : ℝ)) (originalShore A)
  unfold starObjective
  nlinarith

def pruneProg (R t : ℕ) (a : V → ℕ) : Prog (Finset V) ℝ (Finset V) :=
  (scaledExactProg R a (fun _ => t)).map (fun result => originalShore result.shore)

theorem pruneProg_minimizer (J : WeightedGraph V) (hJ : Unweighted J)
    (R t : ℕ) (a : V → ℕ) :
    IsPruningMinimizer J (fun v => (a v : ℝ)) (2 * t) R ((pruneProg R t a).eval J.cut) := by
  let result := (scaledExactProg R a (fun _ => t)).eval J.cut
  have hc := scaledExactProg_correct J hJ R a (fun _ => t)
  change ExactCertificate (directed (twoStar (scaledInternal J R) a (fun _ => t))) result at hc
  simp only [pruneProg, Prog.eval_map]
  intro S
  have hm := hc.minimum_shore (sourceShore S) (source_mem_sourceShore S)
    (sink_notMem_sourceShore S)
  change (twoStar (scaledInternal J R) a (fun _ => t)).cut result.shore ≤
    (twoStar (scaledInternal J R) a (fun _ => t)).cut (sourceShore S) at hm
  rw [pruning_cut_objective J R t a result.shore hc.source_mem hc.sink_notMem,
    pruning_cut_objective J R t a (sourceShore S) (source_mem_sourceShore S)
      (sink_notMem_sourceShore S), originalShore_sourceShore] at hm
  exact hm

theorem pruneProg_cost (J : WeightedGraph V) (hJ : Unweighted J)
    (R t : ℕ) (hR : 1 ≤ R) (ht : 1 ≤ t) (hqpos : 1 ≤ Fintype.card V)
    (hq : Fintype.card V ≤ t ^ 3) (a : V → ℕ)
    (ha : (∑ v, a v) ≤ Fintype.card V * t) :
    (pruneProg R t a).cost J.cut ≤ exactSharpBudget V R t := by
  rw [pruneProg, Prog.cost_map]
  exact scaledExactProg_cost_sharp J hJ R R t hR le_rfl ht hqpos hq a (fun _ => t) ha

/-- Here the fake graph assumptions are intermediate invariants to be
discharged by its separate producer. The minimum shore itself is now produced
by `pruneProg`, rather than supplied as an assumption. -/
theorem pruneProg_structure (J D : WeightedGraph V) (hJ : Unweighted J)
    (R t : ℕ) (hR : 1 ≤ R) (ht : 1 ≤ t) (a : V → ℕ) (M : ℝ)
    (ha : ∀ v, (a v : ℝ) = D.degree v)
    (hdegree : ∀ v, D.degree v ≤ (R : ℝ) * (2 * t))
    (hM : (∑ v, D.degree v) = 2 * M)
    (hbudget : 32 * M ≤ (Fintype.card V : ℝ) * (2 * t))
    (hcertificate : FakeCertificate J D (2 * t) R) :
    let P := (pruneProg R t a).eval J.cut
    8 * P.card ≤ Fintype.card V ∧ J.cut P ≤ (2 * (t : ℝ)) * P.card ∧
      ∀ T : Finset V, T ⊆ Pᶜ →
        (2 * (t : ℝ)) * min (T.card : ℝ) ((Pᶜ \ T).card : ℝ) ≤
          4 * (R : ℝ) * J.localCut Pᶜ T := by
  have hmin := pruneProg_minimizer J hJ R t a
  have he : (fun v => (a v : ℝ)) = D.degree := funext ha
  rw [he] at hmin
  have hR' : (0 : ℝ) < R := by exact_mod_cast (show 0 < R by omega)
  have hb : (0 : ℝ) < 2 * t := by
    have ht' : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
    positivity
  exact ⟨prune_large_remainder J D (2 * t) R M hb hR'.le hM hbudget hmin,
    prune_boundary_le J D (2 * t) R hb hR' hdegree hmin,
    prune_induced_expansion J D (2 * t) R hcertificate hmin⟩

end
end CutQueryComplexity.DeterministicAPMCExpansion.Pruning

#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Pruning.pruneProg_minimizer
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Pruning.pruneProg_cost
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Pruning.pruneProg_structure
