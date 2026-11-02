import CutQueryComplexity.GHReduction.FrontierContraction
import CutQueryComplexity.Certificate.GomoryHu.Contraction

/-! # Minimum-cut safety for actual partial-tree quotients

A public representative is selected for each incident proxy. Minimum-cut
witnesses for the corresponding branch shores imply the protected-fiber
condition of the checked quotient-rounding theorem. Consequently a minimum
cut between original vertices of a block lifts through the actual frontier
map with its value unchanged. This is a local preservation theorem; it does
not assert that arbitrary separately witnessed shores already form a GH tree.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction
noncomputable section
open scoped Classical
open WeightedGraph

variable {V B : Type} [Fintype V] [DecidableEq V] [Fintype B] [DecidableEq B]

/-- This representative function depends only on public witnesses, not on an
optimization over the hidden graph. Original block vertices represent themselves. -/
def frontierRepresentative (p : V → B) (T : RootedTree B) (b : B)
    (r : frontierProxies T b → V) : FrontierVertex p T b → V :=
  Sum.elim Subtype.val r

theorem frontierRepresentative_section (p : V → B) (T : RootedTree B) (b : B)
    (r : frontierProxies T b → V)
    (hr : ∀ e, p (r e) ∈ frontierBranch T b e) :
    ∀ z, frontierMap p T b (frontierRepresentative p T b r z) = z := by
  intro z
  cases z with
  | inl u => exact (frontierMap_eq_inl p T b u.val u).mpr rfl
  | inr e => exact (frontierMap_eq_inr p T b (r e) e).mpr (hr e)

/-- Each proxy's cut witness can have its own pair of terminals. Only the
proxy-side terminal is used as a representative in the rounding theorem. -/
theorem frontierRepresentative_protected (G : WeightedGraph V)
    (p : V → B) (T : RootedTree B) (b : B) (r c : frontierProxies T b → V)
    (hcut : ∀ e, IsSTMinCut G (r e) (c e) (pull p (frontierBranch T b e))) :
    ∀ z, Certificate.GomoryHu.RootProtected G (fiber (frontierMap p T b) z)
      (frontierRepresentative p T b r z) := by
  intro z
  cases z with
  | inl u =>
    rw [frontierMap_original_fiber]
    exact Certificate.GomoryHu.rootProtected_singleton G u.val
  | inr e =>
    rw [frontierMap_proxy_fiber]
    exact Certificate.GomoryHu.RootProtected.of_minCut (hcut e)

theorem frontier_minCut_lift (G : WeightedGraph V)
    (p : V → B) (T : RootedTree B) (b : B) (r c : frontierProxies T b → V)
    (hcut : ∀ e, IsSTMinCut G (r e) (c e) (pull p (frontierBranch T b e)))
    {s t : fiber p b} {S : Finset (FrontierVertex p T b)}
    (hS : IsSTMinCut (G.contract (frontierMap p T b)) (Sum.inl s) (Sum.inl t) S) :
    IsSTMinCut G s.val t.val (pull (frontierMap p T b) S) := by
  apply Certificate.GomoryHu.lift_minCut (frontierMap p T b)
    (frontierRepresentative p T b r)
    (frontierRepresentative_section p T b r (fun e => (mem_pull _ _ _).mp (hcut e).1))
    (frontierRepresentative_protected G p T b r c hcut) hS

/-- Contraction preserves pair values for the original vertices kept in the
block, with no positivity assumption and including zero cuts. -/
theorem frontier_stValue (G : WeightedGraph V)
    (p : V → B) (T : RootedTree B) (b : B) (r c : frontierProxies T b → V)
    (hcut : ∀ e, IsSTMinCut G (r e) (c e) (pull p (frontierBranch T b e)))
    (s t : fiber p b) (hst : s ≠ t) :
    stValue (G.contract (frontierMap p T b)) (Sum.inl s) (Sum.inl t) =
      stValue G s.val t.val := by
  have hneq : (Sum.inl s : FrontierVertex p T b) ≠ Sum.inl t :=
    fun h => hst (Sum.inl.inj h)
  obtain ⟨S, hS, hval⟩ := exists_stMinCut (G.contract (frontierMap p T b)) hneq
  calc
    _ = (G.contract (frontierMap p T b)).cut S := hval.symm
    _ = G.cut (pull (frontierMap p T b) S) := cut_contract _ _ _
    _ = _ := stValue_eq_of_minCut G (frontier_minCut_lift G p T b r c hcut hS)

/-- The implemented primitive uses the actual quotient vertex count and one
original oracle call per quotient call. -/
def frontierSTProgram {M : ℕ} {Q : ℕ → ℕ} (A : CanonicalSTFamily M Q)
    (p : V → B) (T : RootedTree B) (b : B) (s t : fiber p b) :
    DTree (Finset V) ℝ (Finset V) (Q (Fintype.card (FrontierVertex p T b))) :=
  (contractDetProgram (frontierMap p T b)
    (canonicalSTProgram A (Sum.inl s) (Sum.inl t))).map (pull (frontierMap p T b))

theorem frontierSTProgram_correct {M : ℕ} {Q : ℕ → ℕ} (A : CanonicalSTFamily M Q)
    (G : WeightedGraph V) (hG : InputPromise M G)
    (p : V → B) (T : RootedTree B) (b : B) (r c : frontierProxies T b → V)
    (hcut : ∀ e, IsSTMinCut G (r e) (c e) (pull p (frontierBranch T b e)))
    (s t : fiber p b) (hst : s ≠ t) :
    IsSTMinCut G s.val t.val ((frontierSTProgram A p T b s t).eval G.cut) := by
  rw [frontierSTProgram, DTree.eval_map, contractDetProgram_eval]
  exact frontier_minCut_lift G p T b r c hcut
    (canonicalSTProgram_correct A _ (frontier_contraction_promise G hG p T b)
      (fun h => hst (Sum.inl.inj h))).1

theorem frontierSTProgram_cost {M : ℕ} {Q : ℕ → ℕ} (A : CanonicalSTFamily M Q)
    (p : V → B) (T : RootedTree B) (b : B) (s t : fiber p b)
    (read : Finset V → ℝ) :
    (frontierSTProgram A p T b s t).cost read ≤ Q (Fintype.card (FrontierVertex p T b)) :=
  DTree.cost_le _ _

end
end CutQueryComplexity.GHReduction
