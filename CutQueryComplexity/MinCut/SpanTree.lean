import CutQueryComplexity.MinCut.RootedTree

/-! # Rooted spanning trees inside a connecting edge set

An edge set `F : Finset (V × V)` *connects* `V` when it crosses every proper cut.
Breadth-first layers from a root then give a `RootedTree` whose parent edges all
lie in `F` (in one orientation or the other).

For any tree whose parent edges lie in `F`, the number of tree edges crossing `S`
is at most the number of pairs `u ∈ S`, `v ∉ S` joined by `F`
(`card_crossSet_le`).
-/

namespace CutQueryComplexity
namespace SpanTree

noncomputable section
open scoped Classical
variable {V : Type} [Fintype V]

/-- `u` and `v` are joined by `F`. -/
def Adj (F : Finset (V × V)) (u v : V) : Prop := (u, v) ∈ F ∨ (v, u) ∈ F

omit [Fintype V] in
theorem adj_comm {F : Finset (V × V)} {u v : V} : Adj F u v ↔ Adj F v u := by
  unfold Adj; tauto

/-- `F` crosses every proper cut. -/
def Spans (F : Finset (V × V)) : Prop := ∀ S : Finset V, ProperShore S → ∃ e ∈ F, (e.1 ∈ S ↔ e.2 ∉ S)

/-- Vertices within `k` steps of `r`. -/
def reach (F : Finset (V × V)) (r : V) : ℕ → Finset V
  | 0 => {r}
  | k + 1 => reach F r k ∪ Finset.univ.filter fun v => ∃ u ∈ reach F r k, Adj F u v

theorem reach_mono (F : Finset (V × V)) (r : V) {j k : ℕ} (h : j ≤ k) :
    reach F r j ⊆ reach F r k := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans Finset.subset_union_left

theorem exists_reach {F : Finset (V × V)} (hF : Spans F) (r v : V) : ∃ k, v ∈ reach F r k := by
  by_contra hno
  push Not at hno
  set R := Finset.univ.filter fun x => ∃ k, x ∈ reach F r k
  have hR : ProperShore R := by
    refine ⟨⟨r, by simp only [R, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨0, by simp [reach]⟩⟩, ?_⟩
    intro h
    have : v ∈ R := h ▸ Finset.mem_univ v
    simp only [R, Finset.mem_filter, Finset.mem_univ, true_and] at this
    obtain ⟨k, hk⟩ := this
    exact hno k hk
  obtain ⟨⟨a, b⟩, he, hab⟩ := hF R hR
  have step : ∀ x y, x ∈ R → Adj F x y → y ∈ R := by
    intro x y hx hxy
    simp only [R, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    obtain ⟨k, hk⟩ := hx
    refine ⟨k + 1, Finset.mem_union_right _ ?_⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨x, hk, hxy⟩
  by_cases ha : a ∈ R
  · exact (hab.mp ha) (step a b ha (Or.inl he))
  · have hb : b ∈ R := by tauto
    exact ha (step b a hb (Or.inr he))

/-- BFS depth. -/
def bfsDepth (F : Finset (V × V)) (r : V) (v : V) : ℕ :=
  if h : ∃ k, v ∈ reach F r k then Nat.find h else 0

theorem mem_reach_depth {F : Finset (V × V)} (hF : Spans F) (r v : V) :
    v ∈ reach F r (bfsDepth F r v) := by
  have h := exists_reach hF r v
  simp only [bfsDepth, h, ↓reduceDIte]
  exact Nat.find_spec h

theorem depth_le_of_mem {F : Finset (V × V)} {r v : V} {k : ℕ} (hk : v ∈ reach F r k) :
    bfsDepth F r v ≤ k := by
  have h : ∃ k, v ∈ reach F r k := ⟨k, hk⟩
  simp only [bfsDepth, h, ↓reduceDIte]
  exact Nat.find_min' h hk

theorem exists_parent {F : Finset (V × V)} (hF : Spans F) {r v : V} (hv : v ≠ r) :
    ∃ u ∈ reach F r (bfsDepth F r v - 1), Adj F u v := by
  have hm := mem_reach_depth hF r v
  cases hd : bfsDepth F r v with
  | zero =>
      rw [hd] at hm
      simp [reach] at hm
      exact (hv hm).elim
  | succ d =>
      rw [hd] at hm
      simp only [reach, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hm
      rcases hm with hm | hm
      · have := depth_le_of_mem hm
        omega
      · simpa using hm

/-- Parent: a neighbour one layer up. -/
def bfsParent (F : Finset (V × V)) (r : V) (hF : Spans F) (v : V) : V :=
  if hv : v = r then r else (exists_parent hF hv).choose

/-- **The BFS tree** of a spanning edge set. -/
def bfsTree (F : Finset (V × V)) (r : V) (hF : Spans F) : RootedTree V where
  root := r
  parent := bfsParent F r hF
  depth := bfsDepth F r
  parent_root := by simp [bfsParent]
  depth_root := by
    have : bfsDepth F r r ≤ 0 := depth_le_of_mem (by simp [reach])
    omega
  depth_parent v hv := by
    simp only [bfsParent, hv, ↓reduceDIte]
    obtain ⟨hu, hadj⟩ := (exists_parent hF hv).choose_spec
    set u := (exists_parent hF hv).choose
    have h1 := depth_le_of_mem hu
    have h2 : bfsDepth F r v ≤ bfsDepth F r u + 1 :=
      depth_le_of_mem (k := bfsDepth F r u + 1) (Finset.mem_union_right _
        (by simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨u, mem_reach_depth hF r u, hadj⟩))
    have h3 : bfsDepth F r v ≠ 0 := by
      intro h0
      have := mem_reach_depth hF r v
      rw [h0] at this
      simp [reach] at this
      exact hv this
    omega

theorem bfsTree_adj {F : Finset (V × V)} {r : V} (hF : Spans F) {v : V}
    (hv : v ≠ (bfsTree F r hF).root) : Adj F ((bfsTree F r hF).parent v) v := by
  change v ≠ r at hv
  change Adj F (bfsParent F r hF v) v
  simp only [bfsParent, hv, ↓reduceDIte]
  exact (exists_parent hF hv).choose_spec.2

/-- **Crossing count.** Tree edges crossing `S` inject into the `F`-joined pairs
across `S`. -/
theorem card_crossSet_le (T : RootedTree V) (F : Finset (V × V))
    (hT : ∀ v, v ≠ T.root → Adj F (T.parent v) v) (S : Finset V) :
    (T.crossSet S).card ≤ ((S ×ˢ Sᶜ).filter fun e => Adj F e.1 e.2).card := by
  let g : V → V × V := fun v => if v ∈ S then (v, T.parent v) else (T.parent v, v)
  refine Finset.card_le_card_of_injOn g ?_ ?_
  · intro v hv
    have hv' := Finset.mem_filter.mp (Finset.mem_coe.mp hv)
    obtain ⟨hvr, hx⟩ := hv'.2
    refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ?_)
    by_cases hS : v ∈ S
    · have e : g v = (v, T.parent v) := by simp only [g, hS, ↓reduceIte]
      rw [e]
      exact ⟨Finset.mem_product.mpr ⟨hS, Finset.mem_compl.mpr (by tauto)⟩, adj_comm.mp (hT v hvr)⟩
    · have e : g v = (T.parent v, v) := by simp only [g, hS, ↓reduceIte]
      rw [e]
      exact ⟨Finset.mem_product.mpr ⟨by tauto, Finset.mem_compl.mpr hS⟩, hT v hvr⟩
  · intro u hu v hv huv
    have hu' := (Finset.mem_filter.mp (Finset.mem_coe.mp hu)).2
    have hv' := (Finset.mem_filter.mp (Finset.mem_coe.mp hv)).2
    have du := T.depth_parent u hu'.1
    have dv := T.depth_parent v hv'.1
    simp only [g] at huv
    by_cases huS : u ∈ S <;> by_cases hvS : v ∈ S <;>
      simp only [huS, hvS, ↓reduceIte, Prod.mk.injEq] at huv
    · exact huv.1
    · obtain ⟨h1, h2⟩ := huv
      rw [← h1] at dv; rw [h2] at du; omega
    · obtain ⟨h1, h2⟩ := huv
      rw [h1] at du; rw [← h2] at dv; omega
    · exact huv.2

end
end SpanTree
end CutQueryComplexity
