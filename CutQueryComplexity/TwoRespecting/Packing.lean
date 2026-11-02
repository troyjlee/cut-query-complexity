import CutQueryComplexity.TwoRespecting.BFSTree
import CutQueryComplexity.Problem.Basic

/-! # A light spanning edge set for any length function

If every proper cut of `H` has weight at least `λ > 0`, then for every length
function `ℓ` that is nonnegative on positive-weight pairs there is a spanning edge
set `E` of positive-weight pairs with

`∑ e ∈ E, ℓ e ≤ (∑ a, ∑ b, w a b * ℓ a b) / λ`.

This is the minimum-spanning-tree inequality behind fractional tree packing
(Karger; Lemma 12 of the deterministic mincut paper). The proof contracts a
shortest positive crossing pair and inducts on the number of blocks: each step adds
one pair of length `ℓ₀` and lowers every other crossing length by `ℓ₀`, while the
total crossing weight of `k` blocks is at least `kλ`. No linear programming or
minimax theorem is needed.
-/

namespace CutQueryComplexity
namespace TwoRespecting

open WeightedGraph

variable {V : Type} [Fintype V] [DecidableEq V]

/-- `S` is a union of blocks of the labelling `π`. -/
def Respects (π : V → V) (S : Finset V) : Prop := ∀ x y, π x = π y → (x ∈ S ↔ y ∈ S)

/-- Crossing `ℓ`-weighted mass of the partition `π` (ordered pairs). -/
def crossMass (H : WeightedGraph V) (π : V → V) (ℓ : V → V → ℝ) : ℝ :=
  ∑ a, ∑ b, if π a ≠ π b then H.w a b * ℓ a b else 0

/-- `E` crosses every proper union of blocks of `π`. -/
def Connects (E : Finset (V × V)) (π : V → V) : Prop :=
  ∀ S : Finset V, S.Nonempty → S ≠ Finset.univ → Respects π S → ∃ e ∈ E, CrossesPair S e

/-- The total crossing weight is the sum of the block cuts. -/
theorem sum_block_cuts (H : WeightedGraph V) (π : V → V) :
    (∑ a, ∑ b, if π a ≠ π b then H.w a b else 0) =
      ∑ c ∈ Finset.univ.image π, H.cut (Finset.univ.filter fun x => π x = c) := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := π) (t := Finset.univ.image π)
    (fun a _ => Finset.mem_image_of_mem π (Finset.mem_univ a))]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [cut]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [Finset.mem_filter] at ha
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext b
  simp [ha.2, eq_comm]

theorem block_proper {π : V → V} {c d : V} (hc : c ∈ Finset.univ.image π)
    (hd : d ∈ Finset.univ.image π) (hcd : c ≠ d) :
    (Finset.univ.filter fun x => π x = c).Nonempty ∧
      (Finset.univ.filter fun x => π x = c) ≠ Finset.univ ∧
      Respects π (Finset.univ.filter fun x => π x = c) := by
  obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hc
  obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hd
  refine ⟨⟨x, by simp⟩, fun h => hcd ?_, fun a b hab => by simp [hab]⟩
  have : y ∈ Finset.univ.filter fun z => π z = π x := by rw [h]; exact Finset.mem_univ y
  exact (Finset.mem_filter.mp this).2.symm

/-- The induction on the number of blocks. -/
theorem exists_light_connecting (H : WeightedGraph V) {lam : ℝ} (hlam : 0 < lam) :
    ∀ (k : ℕ) (π : V → V) (ℓ : V → V → ℝ), (Finset.univ.image π).card = k + 1 →
      (∀ S : Finset V, S.Nonempty → S ≠ Finset.univ → Respects π S → lam ≤ H.cut S) →
      (∀ a b, π a ≠ π b → 0 < H.w a b → 0 ≤ ℓ a b) →
      ∃ E : Finset (V × V), E.card ≤ k ∧ Connects E π ∧
        (∀ e ∈ E, 0 < H.w e.1 e.2) ∧ (∑ e ∈ E, ℓ e.1 e.2) * lam ≤ crossMass H π ℓ
  | 0, π, ℓ, hk, _, _ => by
      -- one block: nothing to connect, and nothing crosses
      obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hk
      have hall : ∀ x, π x = c := fun x => by
        have : π x ∈ Finset.univ.image π := Finset.mem_image_of_mem π (Finset.mem_univ x)
        rw [hc] at this; exact Finset.mem_singleton.mp this
      refine ⟨∅, by simp, fun S hS hS' hR => ?_, by simp, ?_⟩
      · exfalso
        obtain ⟨x, hx⟩ := hS
        exact hS' (Finset.eq_univ_of_forall fun y => (hR x y ((hall x).trans (hall y).symm)).mp hx)
      · simp [crossMass, hall]
  | k + 1, π, ℓ, hk, hcut, hsign => by
      classical
      -- a positive crossing pair exists
      obtain ⟨c, hc⟩ : (Finset.univ.image π).Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨d, hd, hcd⟩ : ∃ d ∈ Finset.univ.image π, d ≠ c := by
        by_contra h
        push Not at h
        have : Finset.univ.image π ⊆ {c} := fun x hx => Finset.mem_singleton.mpr (h x hx)
        have := Finset.card_le_card this
        simp at this; omega
      obtain ⟨hB1, hB2, hB3⟩ := block_proper hc hd (Ne.symm hcd)
      have hBcut := hcut _ hB1 hB2 hB3
      set P := (Finset.univ : Finset (V × V)).filter fun p => π p.1 ≠ π p.2 ∧ 0 < H.w p.1 p.2
      have hPne : P.Nonempty := by
        by_contra hP
        rw [Finset.not_nonempty_iff_eq_empty] at hP
        have hzero : H.cut (Finset.univ.filter fun x => π x = c) = 0 := by
          rw [cut]
          refine Finset.sum_eq_zero fun a ha => Finset.sum_eq_zero fun b hb => ?_
          rw [Finset.mem_filter] at ha
          rw [Finset.mem_compl, Finset.mem_filter] at hb
          by_contra hw
          have hpos : 0 < H.w a b := lt_of_le_of_ne (H.nonneg a b) (Ne.symm hw)
          have : (a, b) ∈ P := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
            rw [ha.2]; exact fun h => hb (by simp [h]), hpos⟩
          rw [hP] at this; simp at this
        linarith
      obtain ⟨⟨u, v⟩, huv, hmin⟩ := P.exists_min_image (fun p => ℓ p.1 p.2) hPne
      rw [Finset.mem_filter] at huv
      obtain ⟨-, hπuv, hwuv⟩ := huv
      set ℓ₀ := ℓ u v
      have hℓ₀ : 0 ≤ ℓ₀ := hsign u v hπuv hwuv
      -- merge the blocks of `u` and `v`
      let π' : V → V := fun x => if π x = π v then π u else π x
      have hπ'π : ∀ x y, π x = π y → π' x = π' y := fun x y h => by simp only [π', h]
      have himage : Finset.univ.image π' = (Finset.univ.image π).erase (π v) := by
        ext c'
        simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_erase, π']
        constructor
        · rintro ⟨x, rfl⟩
          split_ifs with h
          · exact ⟨hπuv, u, rfl⟩
          · exact ⟨h, x, rfl⟩
        · rintro ⟨hne, x, rfl⟩
          exact ⟨x, by simp [hne]⟩
      have hk' : (Finset.univ.image π').card = k + 1 := by
        rw [himage, Finset.card_erase_of_mem (Finset.mem_image_of_mem π (Finset.mem_univ v))]
        omega
      have hcut' : ∀ S : Finset V, S.Nonempty → S ≠ Finset.univ → Respects π' S →
          lam ≤ H.cut S := fun S h1 h2 h3 => hcut S h1 h2 fun x y hxy => h3 x y (hπ'π x y hxy)
      let ℓ' : V → V → ℝ := fun a b => ℓ a b - ℓ₀
      have hsign' : ∀ a b, π' a ≠ π' b → 0 < H.w a b → 0 ≤ ℓ' a b := by
        intro a b hab hw
        have hπab : π a ≠ π b := fun h => hab (hπ'π a b h)
        have := hmin (a, b) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hπab, hw⟩)
        simp only [ℓ']; linarith
      obtain ⟨E', hcard, hconn, hpos, hbound⟩ :=
        exists_light_connecting H hlam k π' ℓ' hk' hcut' hsign'
      refine ⟨insert (u, v) E', ?_, ?_, ?_, ?_⟩
      · exact (Finset.card_insert_le _ _).trans (by omega)
      · intro S hS hS' hR
        by_cases hsame : u ∈ S ↔ v ∈ S
        · obtain ⟨e, he, hce⟩ := hconn S hS hS' fun x y hxy => by
            simp only [π'] at hxy
            split_ifs at hxy with hx hy hy
            · exact (hR x v hx).trans (hR y v hy).symm
            · exact (hR x v hx).trans (hsame.symm.trans (hR u y hxy))
            · exact (hR x u hxy).trans (hsame.trans (hR v y hy.symm))
            · exact hR x y hxy
          exact ⟨e, Finset.mem_insert_of_mem he, hce⟩
        · refine ⟨(u, v), Finset.mem_insert_self _ _, ?_⟩
          unfold CrossesPair; simp only; tauto
      · intro e he
        rcases Finset.mem_insert.mp he with rfl | he
        · exact hwuv
        · exact hpos e he
      · -- bound the new sum
        have hsumE : ∑ e ∈ insert (u, v) E', ℓ e.1 e.2 ≤ ℓ₀ + ∑ e ∈ E', ℓ e.1 e.2 := by
          by_cases hmem : (u, v) ∈ E'
          · rw [Finset.insert_eq_of_mem hmem]; linarith
          · rw [Finset.sum_insert hmem]
        have hshift : ∑ e ∈ E', ℓ e.1 e.2 = ∑ e ∈ E', ℓ' e.1 e.2 + E'.card * ℓ₀ := by
          simp only [ℓ', Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]; ring
        have hcardR : (E'.card : ℝ) ≤ k := by exact_mod_cast hcard
        -- crossing mass: shift by `ℓ₀`, then drop the merged pairs
        have hW : ((k + 2 : ℕ) : ℝ) * lam ≤ ∑ a, ∑ b, if π a ≠ π b then H.w a b else 0 := by
          rw [sum_block_cuts, ← hk]
          have := Finset.card_nsmul_le_sum (Finset.univ.image π)
            (fun c => H.cut (Finset.univ.filter fun x => π x = c)) lam fun c' hc' => by
              obtain ⟨d', hd', hcd'⟩ : ∃ d' ∈ Finset.univ.image π, d' ≠ c' := by
                by_contra h
                push Not at h
                have : Finset.univ.image π ⊆ {c'} := fun x hx => Finset.mem_singleton.mpr (h x hx)
                have := Finset.card_le_card this
                simp at this; omega
              obtain ⟨h1, h2, h3⟩ := block_proper hc' hd' (Ne.symm hcd')
              exact hcut _ h1 h2 h3
          simpa using this
        have hsplit : crossMass H π ℓ =
            crossMass H π ℓ' + ℓ₀ * ∑ a, ∑ b, if π a ≠ π b then H.w a b else 0 := by
          simp only [crossMass, ℓ', Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
          split_ifs <;> ring
        have hmono : crossMass H π' ℓ' ≤ crossMass H π ℓ' := by
          unfold crossMass
          refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
          have hX : π a ≠ π b → 0 ≤ H.w a b * ℓ' a b := by
            intro h
            rcases (H.nonneg a b).lt_or_eq with hw | hw
            · have := hmin (a, b) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h, hw⟩)
              exact mul_nonneg (H.nonneg a b) (by simp only [ℓ']; linarith)
            · rw [← hw]; simp
          by_cases h1 : π a = π b
          · simp [h1, hπ'π a b h1]
          · by_cases h2 : π' a = π' b
            · simp only [h1, h2, ne_eq, not_true_eq_false, not_false_eq_true, ite_false, ite_true]
              exact hX h1
            · simp [h1, h2]
        have hk2 : ((k + 2 : ℕ) : ℝ) = k + 2 := by push_cast; ring
        rw [hk2] at hW
        have hW' : ℓ₀ * ((k + 2) * lam) ≤
            ℓ₀ * ∑ a, ∑ b, if π a ≠ π b then H.w a b else 0 :=
          mul_le_mul_of_nonneg_left hW hℓ₀
        have hEk : (E'.card : ℝ) * ℓ₀ ≤ k * ℓ₀ := mul_le_mul_of_nonneg_right hcardR hℓ₀
        set A := ∑ e ∈ E', ℓ' e.1 e.2 with hA
        have h1 : ∑ e ∈ insert (u, v) E', ℓ e.1 e.2 ≤ A + (k + 1) * ℓ₀ := by linarith
        have h2 : (∑ e ∈ insert (u, v) E', ℓ e.1 e.2) * lam ≤ (A + (k + 1) * ℓ₀) * lam :=
          mul_le_mul_of_nonneg_right h1 hlam.le
        have h3 : 0 ≤ ℓ₀ * lam := mul_nonneg hℓ₀ hlam.le
        have h4 : (A + (k + 1) * ℓ₀) * lam = A * lam + ℓ₀ * ((k + 2) * lam) - ℓ₀ * lam := by ring
        linarith

/-- **Light spanning edge sets.** If every proper cut of `H` weighs at least `λ > 0`,
then for every length function nonnegative on positive pairs there is a spanning edge
set of positive pairs whose total length is at most `(∑ w ℓ) / λ`. -/
theorem exists_light_spanning (H : WeightedGraph V) {lam : ℝ} (hlam : 0 < lam)
    (hcut : ∀ S : Finset V, S.Nonempty → S ≠ Finset.univ → lam ≤ H.cut S)
    (ℓ : V → V → ℝ) (hℓ : ∀ a b, 0 ≤ ℓ a b) (hV : Nonempty V) :
    ∃ E : Finset (V × V), Spans E ∧ (∀ e ∈ E, 0 < H.w e.1 e.2) ∧
      (∑ e ∈ E, ℓ e.1 e.2) * lam ≤ ∑ a, ∑ b, H.w a b * ℓ a b := by
  have hcard : (Finset.univ.image (id : V → V)).card = (Fintype.card V - 1) + 1 := by
    rw [Finset.image_id, Finset.card_univ]
    have := Fintype.card_pos (α := V); omega
  obtain ⟨E, -, hconn, hpos, hbound⟩ := exists_light_connecting H hlam _ id ℓ hcard
    (fun S h1 h2 _ => hcut S h1 h2) (fun a b _ _ => hℓ a b)
  refine ⟨E, fun S h1 h2 => hconn S h1 h2 fun x y hxy => by simp [show x = y from hxy],
    hpos, hbound.trans (le_of_eq ?_)⟩
  unfold crossMass
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  by_cases hab : a = b
  · subst hab; simp [H.diag]
  · simp [hab]

end TwoRespecting
end CutQueryComplexity
