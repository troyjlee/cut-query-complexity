import CutQueryComplexity.Graph.InducedCut
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum

/-!
# Cut algebra for the all-pairs audit

The input is the repository's loopless, symmetric, nonnegative `WeightedGraph`.
`Unweighted` says precisely that each unordered edge has weight zero or one.
Friendliness is expressed without division, so isolated vertices cause no ambiguity.
-/

set_option autoImplicit false

namespace CutQueryComplexity.AllPairsAudit

open WeightedGraph

noncomputable section
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

def Unweighted (G : WeightedGraph V) : Prop :=
  ∀ u v, G.w u v = 0 ∨ G.w u v = 1

def incident (G : WeightedGraph V) (v : V) (S : Finset V) : ℝ :=
  ∑ u ∈ S, G.w v u

def crossing (G : WeightedGraph V) (S : Finset V) (v : V) : ℝ :=
  if v ∈ S then incident G v Sᶜ else incident G v S

/-- One-sixth friendliness, equivalently at least one sixth of each degree stays inside. -/
def Friendly (G : WeightedGraph V) (S : Finset V) : Prop :=
  ∀ v, 6 * crossing G S v ≤ 5 * G.degree v

omit [Fintype V] [DecidableEq V] in
theorem incident_nonneg (G : WeightedGraph V) (v : V) (S : Finset V) :
    0 ≤ incident G v S := Finset.sum_nonneg fun _ _ => G.nonneg _ _

omit [Fintype V] [DecidableEq V] in
theorem incident_mono (G : WeightedGraph V) (v : V) {S T : Finset V} (h : S ⊆ T) :
    incident G v S ≤ incident G v T :=
  Finset.sum_le_sum_of_subset_of_nonneg h (fun _ _ _ => G.nonneg _ _)

theorem incident_add_compl (G : WeightedGraph V) (v : V) (S : Finset V) :
    incident G v S + incident G v Sᶜ = G.degree v :=
  Finset.sum_add_sum_compl _ _

omit [Fintype V] in
@[simp] theorem incident_erase_self (G : WeightedGraph V) (v : V) (S : Finset V) :
    incident G v (S.erase v) = incident G v S := by
  by_cases hv : v ∈ S
  · have h := Finset.sum_erase_add S (fun u => G.w v u) hv
    simpa [incident, G.diag] using h
  · simp [incident, Finset.erase_eq_of_notMem hv]

omit [Fintype V] in
theorem incident_erase_add (G : WeightedGraph V) (v : V) {s : V} {S : Finset V}
    (hs : s ∈ S) : incident G v (S.erase s) + G.w v s = incident G v S :=
  Finset.sum_erase_add _ _ hs

theorem incident_le_degree (G : WeightedGraph V) (v : V) (S : Finset V) :
    incident G v S ≤ G.degree v := by
  have := incident_add_compl G v S
  have := incident_nonneg G v Sᶜ
  linarith

omit [DecidableEq V] in
theorem degree_nonneg (G : WeightedGraph V) (v : V) : 0 ≤ G.degree v :=
  Finset.sum_nonneg fun _ _ => G.nonneg _ _

theorem crossing_nonneg (G : WeightedGraph V) (S : Finset V) (v : V) :
    0 ≤ crossing G S v := by
  unfold crossing
  split <;> exact incident_nonneg _ _ _

@[simp] theorem crossing_compl (G : WeightedGraph V) (S : Finset V) (v : V) :
    crossing G Sᶜ v = crossing G S v := by
  by_cases hv : v ∈ S <;> simp [crossing, hv]

@[simp] theorem friendly_compl (G : WeightedGraph V) (S : Finset V) :
    Friendly G Sᶜ ↔ Friendly G S := by simp [Friendly]

theorem cut_insert (G : WeightedGraph V) {S : Finset V} {v : V} (hv : v ∉ S) :
    G.cut (insert v S) = G.cut S + G.degree v - 2 * incident G v S := by
  have h := G.cross_eq_three_cuts (Finset.disjoint_singleton_left.mpr hv)
  have he : G.cross {v} S = incident G v S := by simp [cross, incident]
  rw [he, G.cut_singleton, Finset.singleton_union] at h
  linarith

/-- Removing a vertex changes the cut by degree minus twice its crossing degree. -/
theorem cut_erase (G : WeightedGraph V) {S : Finset V} {v : V} (hv : v ∈ S) :
    G.cut (S.erase v) = G.cut S + G.degree v - 2 * crossing G S v := by
  have h := cut_insert G (Finset.notMem_erase v S)
  rw [Finset.insert_erase hv, incident_erase_self] at h
  have hi := incident_add_compl G v S
  simp only [crossing, hv, ite_true]
  linarith

theorem crossing_erase_self (G : WeightedGraph V) {S : Finset V} {s : V} (hs : s ∈ S) :
    crossing G (S.erase s) s = G.degree s - crossing G S s := by
  simp only [crossing, Finset.notMem_erase, ite_false, hs, ite_true, incident_erase_self]
  have := incident_add_compl G s S
  linarith

theorem crossing_erase_inside (G : WeightedGraph V) {S : Finset V} {s x : V}
    (hs : s ∈ S) (hx : x ∈ S) (hxs : x ≠ s) :
    crossing G (S.erase s) x = crossing G S x + G.w x s := by
  have hxe : x ∈ S.erase s := Finset.mem_erase.mpr ⟨hxs, hx⟩
  have h1 := incident_add_compl G x (S.erase s)
  have h2 := incident_add_compl G x S
  have h3 := incident_erase_add G x hs
  simp only [crossing, hx, hxe, ite_true]
  linarith

theorem crossing_erase_outside (G : WeightedGraph V) {S : Finset V} {s x : V}
    (hx : x ∉ S) : crossing G (S.erase s) x ≤ crossing G S x := by
  have hxe : x ∉ S.erase s := fun h => hx (Finset.mem_of_mem_erase h)
  simp only [crossing, hx, hxe, ite_false]
  exact incident_mono G x (Finset.erase_subset _ _)

theorem crossing_le_cut (G : WeightedGraph V) (S : Finset V) (v : V) :
    crossing G S v ≤ G.cut S := by
  have aux (T : Finset V) (hv : v ∈ T) : incident G v Tᶜ ≤ G.cut T := by
    exact Finset.single_le_sum (fun x _ => incident_nonneg G x Tᶜ) hv
  by_cases hv : v ∈ S
  · simpa [crossing, hv] using aux S hv
  · simpa [crossing, hv] using aux Sᶜ (Finset.mem_compl.mpr hv)

theorem st_compl (G : WeightedGraph V) {s t : V} {S : Finset V}
    (hS : IsSTMinCut G s t S) : IsSTMinCut G t s Sᶜ := by
  refine ⟨by simpa using hS.2.1, by simpa using hS.1, ?_⟩
  intro T ht hs
  simpa using hS.2.2 Tᶜ (by simpa using hs) (by simpa using ht)

theorem st_cut_le_degree (G : WeightedGraph V) {s t : V} {S : Finset V}
    (hS : IsSTMinCut G s t S) : G.cut S ≤ G.degree s := by
  have hst : t ≠ s := fun h => hS.2.1 (h ▸ hS.1)
  simpa using hS.2.2 {s} (by simp) (by simpa using hst)

/-- Every nonterminal has at most half its degree crossing an optimal cut. -/
theorem nonterminal_half (G : WeightedGraph V) {s t x : V} {S : Finset V}
    (hS : IsSTMinCut G s t S) (hxs : x ≠ s) (hxt : x ≠ t) :
    2 * crossing G S x ≤ G.degree x := by
  have aux {a b : V} {T : Finset V} (hT : IsSTMinCut G a b T)
      (hx : x ∈ T) (hxa : x ≠ a) : 2 * crossing G T x ≤ G.degree x := by
    have hc := hT.2.2 (T.erase x)
      (Finset.mem_erase.mpr ⟨Ne.symm hxa, hT.1⟩)
      (fun h => hT.2.1 (Finset.mem_of_mem_erase h))
    rw [cut_erase G hx] at hc
    linarith
  by_cases hx : x ∈ S
  · exact aux hS hx hxs
  · simpa using aux (st_compl G hS) (Finset.mem_compl.mpr hx) hxt

omit [Fintype V] [DecidableEq V] in
theorem unweighted_edge_le_one {G : WeightedGraph V} (hG : Unweighted G) (u v : V) :
    G.w u v ≤ 1 := by rcases hG u v with h | h <;> simp [h]

omit [DecidableEq V] in
theorem unweighted_degree_le_card {G : WeightedGraph V} (hG : Unweighted G) (v : V) :
    G.degree v ≤ Fintype.card V := by
  calc
    _ ≤ ∑ _u : V, (1 : ℝ) := Finset.sum_le_sum fun u _ => unweighted_edge_le_one hG v u
    _ = _ := by simp

omit [Fintype V] in
theorem incident_integral {G : WeightedGraph V} (hG : Unweighted G) (v : V) (S : Finset V) :
    ∃ n : ℕ, incident G v S = n := by
  induction S using Finset.induction_on with
  | empty => exact ⟨0, by simp [incident]⟩
  | @insert u S hu ih =>
    obtain ⟨n, hn⟩ := ih
    rcases hG v u with hw | hw
    · exact ⟨n, by simp [incident, Finset.sum_insert hu, hw, ← hn, incident]⟩
    · exact ⟨n + 1, by simp [incident, Finset.sum_insert hu, hw, ← hn, incident]; ring⟩

theorem degree_integral {G : WeightedGraph V} (hG : Unweighted G) (v : V) :
    ∃ n : ℕ, G.degree v = n := incident_integral hG v Finset.univ

theorem crossing_integral {G : WeightedGraph V} (hG : Unweighted G) (S : Finset V) (v : V) :
    ∃ n : ℕ, crossing G S v = n := by
  unfold crossing
  split <;> exact incident_integral hG v _

end
end CutQueryComplexity.AllPairsAudit
