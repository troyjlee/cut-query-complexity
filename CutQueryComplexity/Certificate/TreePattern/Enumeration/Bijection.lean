import CutQueryComplexity.Certificate.TreePattern.Enumeration.Decoder

set_option autoImplicit false

namespace CutQueryComplexity.Certificate.TreePattern

open Finset SimpleGraph
open scoped Classical
noncomputable section

namespace Prufer

variable {α : Type} [Fintype α] [LinearOrder α]

private theorem min'_eq_of_set_eq {s t : Finset α} (hst : s = t)
    (hs : s.Nonempty) (ht : t.Nonempty) : s.min' hs = t.min' ht := by
  cases hst
  rfl

theorem decode_injective (c : List α) : ∀ (S : Finset α) (d : List α),
    Valid S c → Valid S d → decode S c = decode S d → c = d := by
  induction c with
  | nil =>
      intro S d hc hd _
      have hlen : d.length = 0 := by have h₁ := hc.1; have h₂ := hd.1; simp at h₁; omega
      exact (List.length_eq_zero_iff.mp hlen).symm
  | cons a c ih =>
      intro S d hc hd heq
      cases d with
      | nil =>
          have h₁ := hc.1
          have h₂ := hd.1
          simp only [List.length_cons, List.length_nil] at h₁ h₂
          omega
      | cons b d =>
          have hcN := hc.available_nonempty
          have hdN := hd.available_nonempty
          have hsets : S \ (a :: c).toFinset = S \ (b :: d).toFinset := by
            rw [available_eq_leaves (decode_spec (a :: c) S hc).2,
              available_eq_leaves (decode_spec (b :: d) S hd).2]
            apply filter_congr
            intro x _
            rw [degree_congr_graph heq x]
          let v := (S \ (a :: c).toFinset).min' hcN
          have hv : v ∈ S ∧ v ∉ a :: c := by
            simpa only [mem_sdiff, List.mem_toFinset] using
              min'_mem (S \ (a :: c).toFinset) hcN
          have hv' : v ∈ S ∧ v ∉ b :: d := by
            have hm : v ∈ S \ (b :: d).toFinset :=
              hsets ▸ min'_mem (S \ (a :: c).toFinset) hcN
            simpa only [mem_sdiff, List.mem_toFinset] using hm
          have hmin : (S \ (b :: d).toFinset).min' hdN = v := by
            exact min'_eq_of_set_eq hsets.symm hdN hcN
          have hca : decode S (a :: c) = decode (S.erase v) c ⊔ edge v a := by
            simp only [decode, dif_pos hcN, v]
          have hdb : decode S (b :: d) = decode (S.erase v) d ⊔ edge v b := by
            simp only [decode, dif_pos hdN, hmin]
          have hva : v ≠ a := fun hh => hv.2 (List.mem_cons.mpr (Or.inl hh))
          have hvb : v ≠ b := fun hh => hv'.2 (List.mem_cons.mpr (Or.inl hh))
          have ha : (decode S (a :: c)).Adj v a := by
            rw [hca]
            exact Or.inr ((edge_adj _ _ _ _).mpr ⟨Or.inl ⟨rfl, rfl⟩, hva⟩)
          have hb : (decode S (a :: c)).Adj v b := by
            rw [heq, hdb]
            exact Or.inr ((edge_adj _ _ _ _).mpr ⟨Or.inl ⟨rfl, rfl⟩, hvb⟩)
          have hdeg : (decode S (a :: c)).degree v = 1 := by
            rw [decode_degree hc hv.1, List.count_eq_zero.mpr hv.2]
          obtain ⟨w, _, hw⟩ := degree_eq_one_iff_existsUnique_adj.mp hdeg
          have hab : a = b := (hw a ha).trans (hw b hb).symm
          have hct := hc.tail_erase hv.1 hv.2
          have hdt := hd.tail_erase hv'.1 hv'.2
          have ht := congrArg (fun H => eraseVertex H v) heq
          rw [hca, hdb, eraseVertex_attach (decode_tree hct).supported (notMem_erase v S),
            eraseVertex_attach (decode_tree hdt).supported (notMem_erase v S)] at ht
          exact congrArg₂ List.cons hab (ih (S.erase v) d hct hdt ht)

theorem TreeOn.eq_clique_of_card_two {S : Finset α} {G : SimpleGraph α}
    (h : TreeOn S G) (hS : S.card = 2) : G = clique S := by
  obtain ⟨x, y, hxy, rfl⟩ := card_eq_two.mp hS
  have hxyG : G.Adj x y := by
    obtain ⟨z, hz⟩ := (h.reachable x (by simp) y (by simp)).nonempty_neighborSet_left hxy
    have hzS := (h.supported hz).2
    rcases mem_insert.mp hzS with rfl | hzS
    · exact False.elim (G.irrefl hz)
    · simpa only [mem_singleton.mp hzS, mem_neighborSet] using hz
  rw [clique_pair hxy]
  ext u v
  rw [edge_adj]
  constructor
  · intro huv
    have hu := (h.supported huv).1
    have hv := (h.supported huv).2
    simp only [mem_insert, mem_singleton] at hu hv
    aesop
  · rintro ⟨(⟨rfl, rfl⟩ | ⟨rfl, rfl⟩), _⟩
    · exact hxyG
    · exact hxyG.symm

/-- The standard least-leaf encoder. The fuel is the number of leaf deletions;
for a tree on S the valid fuel is S.card - 2. Fallbacks only serve malformed
inputs, and are excluded in encode_spec. -/
def encode (S : Finset α) (G : SimpleGraph α) : ℕ → List α
  | 0 => []
  | k + 1 =>
      if h : (S.filter (fun x => G.degree x = 1)).Nonempty then
        let v := (S.filter (fun x => G.degree x = 1)).min' h
        if ha : (G.neighborFinset v).Nonempty then
          let a := (G.neighborFinset v).min' ha
          a :: encode (S.erase v) (eraseVertex G v) k
        else []
      else []

theorem encode_spec (k : ℕ) : ∀ (S : Finset α) (G : SimpleGraph α),
    TreeOn S G → S.card = k + 2 →
      Valid S (encode S G k) ∧ decode S (encode S G k) = G := by
  induction k with
  | zero =>
      intro S G htree hcard
      simp only [encode]
      refine ⟨⟨by simpa using hcard.symm, by simp⟩, ?_⟩
      exact (htree.eq_clique_of_card_two hcard).symm
  | succ k ih =>
      intro S G htree hcard
      let leaves := S.filter (fun x => G.degree x = 1)
      have hleaves : leaves.Nonempty := by
        obtain ⟨v, hv, hd⟩ := htree.exists_leaf (by omega)
        exact ⟨v, mem_filter.mpr ⟨hv, hd⟩⟩
      let v := leaves.min' hleaves
      have hv : v ∈ S ∧ G.degree v = 1 :=
        mem_filter.mp (min'_mem leaves hleaves)
      have hneigh : (G.neighborFinset v).Nonempty := by
        apply card_pos.mp
        rw [card_neighborFinset_eq_degree, hv.2]
        omega
      let a := (G.neighborFinset v).min' hneigh
      have ha : G.Adj v a := (mem_neighborFinset _ _ _).mp (min'_mem _ hneigh)
      have hunique : ∀ x, G.Adj v x → x = a := by
        obtain ⟨w, _, hw⟩ := degree_eq_one_iff_existsUnique_adj.mp hv.2
        intro x hx
        exact (hw x hx).trans (hw a ha).symm
      have haS : a ∈ S.erase v := mem_erase.mpr ⟨ha.ne', (htree.supported ha).2⟩
      have hsmall : (S.erase v).card = k + 2 := by
        rw [card_erase_of_mem hv.1, hcard]
        omega
      have hsmallTree := htree.erase_leaf hv.1 hv.2
      let c := encode (S.erase v) (eraseVertex G v) k
      have hc : Valid (S.erase v) c :=
        (ih (S.erase v) (eraseVertex G v) hsmallTree hsmall).1
      have hdecode : decode (S.erase v) c = eraseVertex G v :=
        (ih (S.erase v) (eraseVertex G v) hsmallTree hsmall).2
      have hencode : encode S G (k + 1) = a :: c := by
        have hL : (S.filter (fun x => G.degree x = 1)).Nonempty := hleaves
        have hN : (G.neighborFinset
            ((S.filter (fun x => G.degree x = 1)).min' hL)).Nonempty := hneigh
        simp only [encode, dif_pos hL, dif_pos hN, a, c, v, leaves]
      rw [hencode]
      have hvc : v ∉ a :: c := by
        intro hh
        rcases List.mem_cons.mp hh with hh | hh
        · exact (mem_erase.mp haS).1 hh.symm
        · exact notMem_erase v S (hc.2 v hh)
      have hvalid : Valid S (a :: c) := by
        refine ⟨?_, ?_⟩
        · have hh := hc.1
          simp only [List.length_cons]
          omega
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact (htree.supported ha).2
          · exact mem_of_mem_erase (hc.2 x hx)
      have hdegree : ∀ x ∈ S, G.degree x = (a :: c).count x + 1 := by
        intro x hx
        by_cases hxv : x = v
        · subst x
          rw [hv.2, List.count_eq_zero.mpr hvc]
        · have hx' : x ∈ S.erase v := mem_erase.mpr ⟨hxv, hx⟩
          rw [degree_congr_graph (reconstruct_leaf ha hunique).symm x,
            attach_degree_old hsmallTree.supported (notMem_erase v S) haS hx',
            degree_congr_graph hdecode.symm x, decode_degree hc hx']
          by_cases hxa : x = a
          · subst x
            rw [if_pos rfl, List.count_cons_self]
          · rw [if_neg hxa, List.count_cons_of_ne (Ne.symm hxa), Nat.add_zero]
      have havail : S \ (a :: c).toFinset = leaves := available_eq_leaves hdegree
      have hn := hvalid.available_nonempty
      have hmin : (S \ (a :: c).toFinset).min' hn = v := by
        exact min'_eq_of_set_eq havail hn hleaves
      refine ⟨hvalid, ?_⟩
      simp only [decode, dif_pos hn, hmin]
      rw [hdecode]
      exact reconstruct_leaf ha hunique

theorem decode_encode {S : Finset α} {G : SimpleGraph α}
    (h : TreeOn S G) (hS : 2 ≤ S.card) :
    decode S (encode S G (S.card - 2)) = G :=
  (encode_spec (S.card - 2) S G h (by omega)).2

theorem encode_decode {S : Finset α} {c : List α} (h : Valid S c) :
    encode S (decode S c) c.length = c := by
  have hs := encode_spec c.length S (decode S c) (decode_tree h) h.1.symm
  exact decode_injective _ S c hs.1 h hs.2

theorem decode_surjective_aux (m : ℕ) :
    ∀ (S : Finset α), S.card = m → ∀ (G : SimpleGraph α), TreeOn S G → 2 ≤ m →
      ∃ c : List α, Valid S c ∧ decode S c = G := by
  intro S hcard G htree hm
  exact ⟨encode S G (m - 2), encode_spec (m - 2) S G htree (by omega)⟩

theorem decode_surjective {S : Finset α} {G : SimpleGraph α}
    (h : TreeOn S G) (hS : 2 ≤ S.card) :
    ∃ c : List α, Valid S c ∧ decode S c = G :=
  decode_surjective_aux S.card S rfl G h hS

end Prufer
end
end CutQueryComplexity.Certificate.TreePattern

#print axioms CutQueryComplexity.Certificate.TreePattern.Prufer.decode_injective
#print axioms CutQueryComplexity.Certificate.TreePattern.Prufer.TreeOn.eq_clique_of_card_two
#print axioms CutQueryComplexity.Certificate.TreePattern.Prufer.encode_spec
#print axioms CutQueryComplexity.Certificate.TreePattern.Prufer.decode_encode
#print axioms CutQueryComplexity.Certificate.TreePattern.Prufer.encode_decode
#print axioms CutQueryComplexity.Certificate.TreePattern.Prufer.decode_surjective
