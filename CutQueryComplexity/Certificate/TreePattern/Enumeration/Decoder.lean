import CutQueryComplexity.Certificate.TreePattern.Enumeration.Basic

set_option autoImplicit false

namespace CutQueryComplexity.Certificate.TreePattern

open Finset SimpleGraph
open scoped Classical
noncomputable section

namespace Prufer

variable {α : Type} [Fintype α] [LinearOrder α]

def clique (S : Finset α) : SimpleGraph α where
  Adj x y := x ∈ S ∧ y ∈ S ∧ x ≠ y
  symm := ⟨by intro x y h; exact ⟨h.2.1, h.1, h.2.2.symm⟩⟩
  loopless := ⟨by intro x h; exact h.2.2 rfl⟩

theorem clique_pair {x y : α} (hxy : x ≠ y) : clique {x, y} = edge x y := by
  ext u v
  simp only [clique, edge_adj, mem_insert, mem_singleton]
  aesop

theorem TreeOn.singleton (x : α) : TreeOn {x} (⊥ : SimpleGraph α) := by
  refine ⟨⟨x, mem_singleton_self _⟩, ?_, isAcyclic_bot, ?_⟩
  · intro u v h; exact False.elim h
  · intro u hu v hv
    have hu' := mem_singleton.mp hu
    have hv' := mem_singleton.mp hv
    subst u; subst v
    exact Reachable.rfl

theorem clique_tree_of_card_two {S : Finset α} (hS : S.card = 2) :
    TreeOn S (clique S) := by
  obtain ⟨x, y, hxy, rfl⟩ := card_eq_two.mp hS
  rw [clique_pair hxy]
  simpa using (TreeOn.singleton y).attach_leaf (by simpa using hxy) (mem_singleton_self y)

/-- Graph equality preserves degree even when neighbor finiteness was obtained
through different instances. -/
theorem degree_congr_graph {G H : SimpleGraph α} (h : G = H) (x : α)
    [Fintype (G.neighborSet x)] [Fintype (H.neighborSet x)] :
    G.degree x = H.degree x := by
  calc
    G.degree x = (G.neighborSet x).ncard := (G.ncard_neighborSet x).symm
    _ = (H.neighborSet x).ncard := by rw [h]
    _ = H.degree x := H.ncard_neighborSet x

theorem attach_degree_new {S : Finset α} {G : SimpleGraph α}
    (hsupp : ∀ {u w}, G.Adj u w → u ∈ S ∧ w ∈ S)
    {v a : α} (hv : v ∉ S) (ha : a ∈ S) : (G ⊔ edge v a).degree v = 1 := by
  have hva : v ≠ a := fun he => hv (he.symm ▸ ha)
  apply degree_eq_one_iff_existsUnique_adj.mpr
  refine ⟨a, Or.inr ((edge_adj _ _ _ _).mpr ⟨Or.inl ⟨rfl, rfl⟩, hva⟩), ?_⟩
  intro x hx
  rcases hx with hx | hx
  · exact False.elim (hv (hsupp hx).1)
  · rcases (edge_adj _ _ _ _).mp hx with ⟨hx, _⟩
    rcases hx with ⟨_, hx⟩ | ⟨he, _⟩
    · exact hx
    · exact False.elim (hva he)

theorem attach_degree_old {S : Finset α} {G : SimpleGraph α}
    (hsupp : ∀ {u w}, G.Adj u w → u ∈ S ∧ w ∈ S)
    {v a x : α} (hv : v ∉ S) (ha : a ∈ S) (hx : x ∈ S) :
    (G ⊔ edge v a).degree x = G.degree x + if x = a then 1 else 0 := by
  have hxv : x ≠ v := fun he => hv (he ▸ hx)
  have hva : v ≠ a := fun he => hv (he.symm ▸ ha)
  have hnot : v ∉ G.neighborFinset x := by
    intro hh
    exact hv (hsupp ((mem_neighborFinset _ _ _).mp hh)).2
  have he : (G ⊔ edge v a).neighborFinset x =
      if x = a then insert v (G.neighborFinset x) else G.neighborFinset x := by
    ext y
    by_cases hxa : x = a <;> by_cases hyv : y = v <;>
      simp_all [mem_neighborFinset, mem_insert, sup_adj, edge_adj]
  change ((G ⊔ edge v a).neighborFinset x).card = _
  rw [he]
  by_cases hxa : x = a <;>
    simp [hxa, hnot, card_neighborFinset_eq_degree, Nat.add_comm]

theorem clique_degree_of_card_two {S : Finset α} (hS : S.card = 2)
    {x : α} (hx : x ∈ S) : (clique S).degree x = 1 := by
  obtain ⟨u, v, huv, rfl⟩ := card_eq_two.mp hS
  apply degree_eq_one_iff_existsUnique_adj.mpr
  rcases mem_insert.mp hx with hxu | hx
  · subst x
    refine ⟨v, ⟨by simp, by simp, huv⟩, ?_⟩
    intro y hy
    rcases mem_insert.mp hy.2.1 with hyu | hyv
    · exact False.elim (hy.2.2 hyu.symm)
    · exact mem_singleton.mp hyv
  · have hxv := mem_singleton.mp hx
    subst x
    refine ⟨u, ⟨by simp, by simp, huv.symm⟩, ?_⟩
    intro y hy
    rcases mem_insert.mp hy.2.1 with hyu | hyv
    · exact hyu
    · exact False.elim (hy.2.2 (mem_singleton.mp hyv).symm)

def Valid (S : Finset α) (c : List α) : Prop :=
  c.length + 2 = S.card ∧ ∀ x ∈ c, x ∈ S

theorem Valid.available_nonempty {S : Finset α} {c : List α} (h : Valid S c) :
    (S \ c.toFinset).Nonempty := by
  have hc := c.toFinset_card_le
  have hs : S.card ≤ (S \ c.toFinset).card + c.toFinset.card :=
    card_le_card_sdiff_add_card
  apply card_pos.mp
  have hl := h.1
  omega

theorem Valid.tail_erase {S : Finset α} {a v : α} {c : List α}
    (h : Valid S (a :: c)) (hv : v ∈ S) (hnot : v ∉ a :: c) :
    Valid (S.erase v) c := by
  refine ⟨?_, ?_⟩
  · rw [card_erase_of_mem hv]
    have hl := h.1
    simp only [List.length_cons] at hl
    omega
  · intro x hx
    refine mem_erase.mpr ⟨?_, h.2 x (List.mem_cons_of_mem a hx)⟩
    intro he
    exact hnot (he ▸ List.mem_cons_of_mem a hx)

/-- Standard least-absent-label Prüfer decoder. The fallback branch only
serves malformed inputs; Valid excludes it. -/
def decode (S : Finset α) : List α → SimpleGraph α
  | [] => clique S
  | a :: c =>
      if h : (S \ (a :: c).toFinset).Nonempty then
        let v := (S \ (a :: c).toFinset).min' h
        decode (S.erase v) c ⊔ edge v a
      else ⊥

theorem decode_spec (c : List α) : ∀ S, Valid S c →
    TreeOn S (decode S c) ∧ ∀ x ∈ S, (decode S c).degree x = c.count x + 1 := by
  induction c with
  | nil =>
      intro S h
      have hS : S.card = 2 := by simpa using h.1.symm
      refine ⟨clique_tree_of_card_two hS, ?_⟩
      intro x hx
      simp only [List.count_nil, Nat.zero_add]
      apply degree_eq_one_iff_existsUnique_adj.mpr
      exact degree_eq_one_iff_existsUnique_adj.mp (clique_degree_of_card_two hS hx)
  | cons a c ih =>
      intro S h
      have hne := h.available_nonempty
      let v := (S \ (a :: c).toFinset).min' hne
      have hv : v ∈ S ∧ v ∉ a :: c := by
        have hm := min'_mem (S \ (a :: c).toFinset) hne
        simpa only [mem_sdiff, List.mem_toFinset] using hm
      have ha : a ∈ S.erase v := by
        refine mem_erase.mpr ⟨?_, h.2 a (by simp)⟩
        intro he
        exact hv.2 (List.mem_cons.mpr (Or.inl he.symm))
      obtain ⟨htree, hdegree⟩ := ih (S.erase v) (h.tail_erase hv.1 hv.2)
      have he : decode S (a :: c) = decode (S.erase v) c ⊔ edge v a := by
        simp only [decode, dif_pos hne, v]
      refine ⟨?_, ?_⟩
      · rw [he]
        have hh := htree.attach_leaf (notMem_erase v S) ha
        rwa [insert_erase hv.1] at hh
      · intro x hx
        rw [degree_congr_graph he x]
        by_cases hxv : x = v
        · subst x
          rw [attach_degree_new htree.supported (notMem_erase v S) ha]
          have hc : (a :: c).count v = 0 := List.count_eq_zero.mpr hv.2
          simp [hc]
        · rw [attach_degree_old htree.supported (notMem_erase v S) ha
            (mem_erase.mpr ⟨hxv, hx⟩), hdegree x (mem_erase.mpr ⟨hxv, hx⟩)]
          by_cases hxa : x = a
          · subst x
            rw [if_pos rfl, List.count_cons_self]
          · rw [if_neg hxa, List.count_cons_of_ne (Ne.symm hxa), Nat.add_zero]

theorem decode_tree {S : Finset α} {c : List α} (h : Valid S c) :
    TreeOn S (decode S c) := (decode_spec c S h).1

theorem decode_degree {S : Finset α} {c : List α} (h : Valid S c)
    {x : α} (hx : x ∈ S) : (decode S c).degree x = c.count x + 1 :=
  (decode_spec c S h).2 x hx

theorem available_eq_leaves {S : Finset α} {c : List α} {G : SimpleGraph α}
    (hdegree : ∀ x ∈ S, G.degree x = c.count x + 1) :
    S \ c.toFinset = S.filter (fun x => G.degree x = 1) := by
  ext x
  by_cases hx : x ∈ S
  · simp [hx, hdegree x hx, List.count_eq_zero]
  · simp [hx]

end Prufer
end
end CutQueryComplexity.Certificate.TreePattern

#print axioms CutQueryComplexity.Certificate.TreePattern.Prufer.clique_tree_of_card_two
#print axioms CutQueryComplexity.Certificate.TreePattern.Prufer.degree_congr_graph
#print axioms CutQueryComplexity.Certificate.TreePattern.Prufer.attach_degree_new
#print axioms CutQueryComplexity.Certificate.TreePattern.Prufer.attach_degree_old
#print axioms CutQueryComplexity.Certificate.TreePattern.Prufer.decode_spec
#print axioms CutQueryComplexity.Certificate.TreePattern.Prufer.decode_tree
#print axioms CutQueryComplexity.Certificate.TreePattern.Prufer.decode_degree
#print axioms CutQueryComplexity.Certificate.TreePattern.Prufer.available_eq_leaves
