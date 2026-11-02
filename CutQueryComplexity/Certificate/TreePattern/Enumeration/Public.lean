import CutQueryComplexity.Certificate.TreePattern.Enumeration.Bijection
import Mathlib.Data.Vector.Basic

set_option autoImplicit false

namespace CutQueryComplexity.Certificate.TreePattern

open Finset SimpleGraph
open scoped Classical
noncomputable section

private def pruferList {n : ℕ} (c : PruferCode n) : List.Vector (Fin n) (n - 2) :=
  (Equiv.vectorEquivFin (Fin n) (n - 2)).symm c

private theorem pruferList_val {n : ℕ} (c : PruferCode n) :
    (pruferList c).val = List.ofFn c := List.Vector.toList_ofFn c

private theorem pruferList_valid {n : ℕ} (hn : 2 ≤ n) (c : PruferCode n) :
    Prufer.Valid univ (pruferList c).val := by
  refine ⟨?_, fun _ _ => mem_univ _⟩
  rw [(pruferList c).property, card_univ, Fintype.card_fin]
  omega

/-- The usual least-absent-label decoder, proved to return a labelled tree. -/
def pruferDecode {n : ℕ} (hn : 2 ≤ n) (c : PruferCode n) :
    {T : SimpleGraph (Fin n) // T.IsTree} :=
  ⟨Prufer.decode univ (pruferList c).val,
    (Prufer.TreeOn.univ_iff _).mp (Prufer.decode_tree (pruferList_valid hn c))⟩

theorem pruferDecode_injective {n : ℕ} (hn : 2 ≤ n) :
    Function.Injective (pruferDecode hn) := by
  intro c d h
  have hl : (pruferList c).val = (pruferList d).val :=
    Prufer.decode_injective _ _ _ (pruferList_valid hn c) (pruferList_valid hn d)
      (congrArg Subtype.val h)
  exact (Equiv.vectorEquivFin (Fin n) (n - 2)).symm.injective (Subtype.ext hl)

theorem pruferDecode_surjective {n : ℕ} (hn : 2 ≤ n) :
    Function.Surjective (pruferDecode hn) := by
  intro T
  obtain ⟨l, hl, hdecode⟩ := Prufer.decode_surjective
    ((Prufer.TreeOn.univ_iff T.val).mpr T.property) (by simpa using hn)
  have hlen : l.length = n - 2 := by
    have hh := hl.1
    simp only [card_univ, Fintype.card_fin] at hh
    omega
  let v : List.Vector (Fin n) (n - 2) := ⟨l, hlen⟩
  refine ⟨(Equiv.vectorEquivFin (Fin n) (n - 2)) v, ?_⟩
  apply Subtype.ext
  change Prufer.decode univ
    ((Equiv.vectorEquivFin (Fin n) (n - 2)).symm
      ((Equiv.vectorEquivFin (Fin n) (n - 2)) v)).val = T.val
  rw [Equiv.symm_apply_apply]
  exact hdecode

private theorem pruferEncoded_spec {n : ℕ} (hn : 2 ≤ n)
    (T : {T : SimpleGraph (Fin n) // T.IsTree}) :
    Prufer.Valid univ (Prufer.encode univ T.val (n - 2)) ∧
      Prufer.decode univ (Prufer.encode univ T.val (n - 2)) = T.val :=
  Prufer.encode_spec (n - 2) univ T.val
    ((Prufer.TreeOn.univ_iff T.val).mpr T.property) (by
      simp only [card_univ, Fintype.card_fin]
      omega)

private def pruferEncodedList {n : ℕ} (hn : 2 ≤ n)
    (T : {T : SimpleGraph (Fin n) // T.IsTree}) : List.Vector (Fin n) (n - 2) :=
  ⟨Prufer.encode univ T.val (n - 2), by
    have h := (pruferEncoded_spec hn T).1.1
    simp only [card_univ, Fintype.card_fin] at h
    omega⟩

/-- The standard recursive least-leaf Prüfer encoder. -/
def pruferEncode {n : ℕ} (hn : 2 ≤ n)
    (T : {T : SimpleGraph (Fin n) // T.IsTree}) : PruferCode n :=
  (Equiv.vectorEquivFin (Fin n) (n - 2)) (pruferEncodedList hn T)

theorem pruferDecode_encode {n : ℕ} (hn : 2 ≤ n)
    (T : {T : SimpleGraph (Fin n) // T.IsTree}) :
    pruferDecode hn (pruferEncode hn T) = T := by
  apply Subtype.ext
  change Prufer.decode univ
    ((Equiv.vectorEquivFin (Fin n) (n - 2)).symm
      ((Equiv.vectorEquivFin (Fin n) (n - 2)) (pruferEncodedList hn T))).val = T.val
  rw [Equiv.symm_apply_apply]
  exact (pruferEncoded_spec hn T).2

theorem pruferEncode_decode {n : ℕ} (hn : 2 ≤ n) (c : PruferCode n) :
    pruferEncode hn (pruferDecode hn c) = c := by
  apply pruferDecode_injective hn
  exact pruferDecode_encode hn (pruferDecode hn c)

/-- The actual Prüfer equivalence between the explicit recursive encoder and
decoder. Neither construction uses a count or bijection oracle. -/
def pruferEquiv {n : ℕ} (hn : 2 ≤ n) :
    {T : SimpleGraph (Fin n) // T.IsTree} ≃ PruferCode n where
  toFun := pruferEncode hn
  invFun := pruferDecode hn
  left_inv := pruferDecode_encode hn
  right_inv := pruferEncode_decode hn

/-- The inverse is the usual Prüfer code: every label occurs degree minus one
times, as proved from the explicit decoder's leaf-attachment invariant. -/
theorem pruferEncode_degree {n : ℕ} (hn : 2 ≤ n)
    (T : {T : SimpleGraph (Fin n) // T.IsTree}) (v : Fin n) :
    T.val.degree v = (List.ofFn (pruferEncode hn T)).count v + 1 := by
  have hd := Prufer.decode_degree (pruferList_valid hn (pruferEncode hn T)) (mem_univ v)
  have hi := congrArg Subtype.val (pruferDecode_encode hn T)
  change Prufer.decode univ (pruferList (pruferEncode hn T)).val = T.val at hi
  rwa [Prufer.degree_congr_graph hi v, pruferList_val] at hd

theorem labelledTree_card {n : ℕ} (hn : 2 ≤ n) :
    Fintype.card {T : SimpleGraph (Fin n) // T.IsTree} = n ^ (n - 2) := by
  calc
    Fintype.card {T : SimpleGraph (Fin n) // T.IsTree} =
        Fintype.card (PruferCode n) := Fintype.card_congr (pruferEquiv hn)
    _ = n ^ (n - 2) := by simp [PruferCode]

theorem labelledTrees_card {n : ℕ} (hn : 2 ≤ n) :
    (labelledTrees n).card = n ^ (n - 2) := by
  simpa only [labelledTrees, Fintype.card_subtype] using labelledTree_card hn

end
end CutQueryComplexity.Certificate.TreePattern

#print axioms CutQueryComplexity.Certificate.TreePattern.pruferDecode_injective
#print axioms CutQueryComplexity.Certificate.TreePattern.pruferDecode_surjective
#print axioms CutQueryComplexity.Certificate.TreePattern.pruferDecode_encode
#print axioms CutQueryComplexity.Certificate.TreePattern.pruferEncode_decode
#print axioms CutQueryComplexity.Certificate.TreePattern.pruferEncode_degree
#print axioms CutQueryComplexity.Certificate.TreePattern.labelledTree_card
#print axioms CutQueryComplexity.Certificate.TreePattern.labelledTrees_card
