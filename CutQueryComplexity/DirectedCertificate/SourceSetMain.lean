import CutQueryComplexity.FractionalForest.Progress
import CutQueryComplexity.DirectedCertificate.SourceSet

/-! # Unconditional deletion and source-set theorems (W4)

`forest_deletion`, `forest_deletion_uniform`, `small_source_set` and `small_source_set_flows`
take the unit-progress theorem as the hypothesis `hprog`. Here `unit_progress`
(`FractionalForest.Progress`) discharges it, giving the W4 endpoints for arbitrary real
weights with no remaining assumption.
-/

namespace CutQueryComplexity

open Finset

namespace FractionalForest

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Logarithm-free forest deletion** (`cor:forest-deletion`). -/
theorem forest_deletion_main {x : WeightedGraph V} (hx : IsFractionalForest x) {k : ℕ}
    (hk : 1 ≤ k) (hkn : k ≤ Fintype.card V) :
    ∃ Z : Finset V,
      Z.card ≤ (if k = 1 then Fintype.card V - 1 else budgetQ (Fintype.card V) k) ∧
      ∀ S ⊆ Zᶜ, mass x S ≤ (1 - 1 / (k : ℝ)) * S.card :=
  forest_deletion hx hk hkn fun _ hk3 _ hv => unit_progress hx hk3 hv

/-- **Forest deletion, uniform form:** `|Z| ≤ 2(⌈n/k⌉ − 1)`. -/
theorem forest_deletion_uniform_main {x : WeightedGraph V} (hx : IsFractionalForest x) {k : ℕ}
    (hk : 1 ≤ k) (hkn : k ≤ Fintype.card V) :
    ∃ Z : Finset V, Z.card ≤ 2 * (ceilA (Fintype.card V) k - 1) ∧
      ∀ S ⊆ Zᶜ, mass x S ≤ (1 - 1 / (k : ℝ)) * S.card :=
  forest_deletion_uniform hx hk hkn fun _ hk3 _ hv => unit_progress hx hk3 hv

end FractionalForest

namespace DirectedCertificate

open FractionalForest Certificate

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **A small common source set** (`cor:small-source-set`). -/
theorem small_source_set_main (H : WeightedDiGraph V) (r : V) {lam : ℝ} (hlam : 0 < lam)
    (a b : InArb r → ℝ) (ha : ∀ T, 0 ≤ a T) (hasum : ∑ T, a T = lam)
    (haload : ∀ u v, load a u v ≤ H.c u v)
    (hb : ∀ T, 0 ≤ b T) (hbsum : ∑ T, b T = lam) (hbload : ∀ u v, outLoad b u v ≤ H.c u v)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ Fintype.card V) :
    ∃ R : Finset V, r ∈ R ∧ R.card ≤ 4 * (ceilA (Fintype.card V) k - 1) + 1 ∧
      ∀ S : Finset V, Disjoint S R → lam / k * S.card ≤ H.out S ∧ lam / k * S.card ≤ H.out Sᶜ :=
  small_source_set H r hlam a b ha hasum haload hb hbsum hbload hk hkn
    fun _ hx _ hk3 _ hv => unit_progress hx hk3 hv

/-- **The two shared flows from the source set**, each carrying `λ/k` per outside vertex in
its own direction. They are separate feasible flows; nothing is claimed about their sum. -/
theorem small_source_set_flows_main (H : WeightedDiGraph V) (r : V) {lam : ℝ} (hlam : 0 < lam)
    (a b : InArb r → ℝ) (ha : ∀ T, 0 ≤ a T) (hasum : ∑ T, a T = lam)
    (haload : ∀ u v, load a u v ≤ H.c u v)
    (hb : ∀ T, 0 ≤ b T) (hbsum : ∑ T, b T = lam) (hbload : ∀ u v, outLoad b u v ≤ H.c u v)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ Fintype.card V) :
    ∃ R : Finset V, r ∈ R ∧ R.card ≤ 4 * (ceilA (Fintype.card V) k - 1) + 1 ∧
      (∃ f : V → V → ℝ, H.Feasible f ∧ (∀ v, v ∉ R → netOut f v = lam / k) ∧
        ∀ v ∈ R, netOut f v ≤ 0) ∧
      (∃ g : V → V → ℝ, H.Feasible g ∧ (∀ v, v ∉ R → netOut g v = -(lam / k)) ∧
        ∀ v ∈ R, 0 ≤ netOut g v) :=
  small_source_set_flows H r hlam a b ha hasum haload hb hbsum hbload hk hkn
    fun _ hx _ hk3 _ hv => unit_progress hx hk3 hv

end DirectedCertificate

end CutQueryComplexity
