import CutQueryComplexity.DirectedUnitST.SparseBand.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Algebra.Order.Floor.Ring

/-! # Reduction of every real potential to the finite expanded grid

The graph in this proof is the public active-pair relation of an arbitrary
potential. Component translation is used only in the soundness proof.
-/

set_option autoImplicit false

namespace CutQueryComplexity.DirectedUnitST.SparseBand

open Finset

theorem abs_sub_le_walk_length {V : Type*} {G : SimpleGraph V}
    (r : V → ℝ) {B : ℝ} (hB : ∀ u v, G.Adj u v → |r u - r v| ≤ B)
    {u v : V} (p : G.Walk u v) : |r u - r v| ≤ p.length * B := by
  induction p with
  | nil => simp
  | @cons u v w huv p ih =>
      have ht := abs_add_le (r u - r v) (r v - r w)
      have he := hB u v huv
      simp only [SimpleGraph.Walk.length_cons, Nat.cast_add, Nat.cast_one]
      have hh : r u - r v + (r v - r w) = r u - r w := by ring
      rw [hh] at ht
      nlinarith

/-- Component translations keep every edge difference and put all potentials
inside a bounded interval. Isolated vertices are included. -/
theorem exists_component_translate {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (r : V → ℝ) {B : ℝ} (hB₀ : 0 ≤ B)
    (hB : ∀ u v, G.Adj u v → |r u - r v| ≤ B) :
    ∃ t : V → ℝ,
      (∀ v, 0 ≤ t v ∧ t v ≤ (Fintype.card V : ℝ) * B) ∧
      ∀ u v, G.Adj u v → t u - t v = r u - r v := by
  classical
  let s (v : V) : Finset V := univ.filter (G.Reachable v)
  have hv (v : V) : v ∈ s v := by simp [s]
  have hs (v : V) : (s v).Nonempty := ⟨v, hv v⟩
  let a (v : V) : ℝ := (s v).inf' (hs v) r
  refine ⟨fun v => r v - a v, ?_, ?_⟩
  · intro v
    have hav : a v ≤ r v := Finset.inf'_le r (hv v)
    refine ⟨sub_nonneg.mpr hav, ?_⟩
    obtain ⟨u, hu, hmin⟩ := Finset.exists_mem_eq_inf' (hs v) r
    have hreach : G.Reachable v u := (Finset.mem_filter.mp hu).2
    obtain ⟨p, hp⟩ := hreach.exists_isPath
    have hlen : (p.length : ℝ) ≤ Fintype.card V := by
      exact_mod_cast hp.length_lt.le
    have hdist := abs_sub_le_walk_length r hB p
    have hmul := mul_le_mul_of_nonneg_right hlen hB₀
    change r v - (s v).inf' (hs v) r ≤ _
    rw [hmin]
    exact (le_abs_self _).trans (hdist.trans hmul)
  · intro u v huv
    have heq : s u = s v := by
      ext w
      simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun huw => huv.reachable.symm.trans huw,
        fun hvw => huv.reachable.trans hvw⟩
    have ha : a u = a v := by simp only [a, heq]
    change (r u - a u) - (r v - a v) = r u - r v
    rw [ha]
    ring

noncomputable def activeGraph {n k : ℕ} (c : OffsetTable n k)
    (r : Fin n → ℝ) : SimpleGraph (Fin n) where
  Adj u v := (∃ h : u < v, Active c r ⟨(u, v), h⟩) ∨
    (∃ h : v < u, Active c r ⟨(v, u), h⟩)
  symm := ⟨fun _ _ => Or.symm⟩
  loopless := ⟨fun u => by simp⟩

theorem activeGraph_adj {n k : ℕ} (c : OffsetTable n k) (r : Fin n → ℝ)
    (e : Pair n) (he : Active c r e) :
    (activeGraph c r).Adj e.val.1 e.val.2 := Or.inl ⟨e.property, he⟩

theorem exists_bounded_potential {n k : ℕ} (hk : 0 < k)
    (c : OffsetTable n k) (r : Fin n → ℝ) :
    ∃ t : Fin n → ℝ, (∀ v, 0 ≤ t v ∧ t v ≤ 2 * n) ∧
      ∀ e : Pair n, Active c r e → Active c t e := by
  have hedge : ∀ u v, (activeGraph c r).Adj u v → |r u - r v| ≤ (2 : ℝ) := by
    intro u v huv
    rcases huv with ⟨h, he⟩ | ⟨h, he⟩
    · exact (active_abs_sub_lt_two hk c r ⟨(u, v), h⟩ he).le
    · rw [abs_sub_comm]
      exact (active_abs_sub_lt_two hk c r ⟨(v, u), h⟩ he).le
  obtain ⟨t, ht, heq⟩ := exists_component_translate (activeGraph c r) r (by norm_num) hedge
  refine ⟨t, ?_, ?_⟩
  · simpa [Fintype.card_fin, mul_comm] using ht
  · intro e he
    dsimp [Active] at he ⊢
    rw [heq _ _ (activeGraph_adj c r e he)]
    exact he

/-- Flooring a bounded real potential gives a finite integer grid point whose
expanded band contains every originally active pair. -/
theorem exists_grid_cover {n k : ℕ} (hk : 0 < k)
    (c : OffsetTable n k) (r : Fin n → ℝ) :
    ∃ g : GridPoint n k, ∀ e : Pair n, Active c r e → GridActive c g e := by
  obtain ⟨t, ht, hactive⟩ := exists_bounded_potential hk c r
  have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have ht₀ (v : Fin n) : 0 ≤ (4 : ℝ) * k * t v :=
    mul_nonneg (by positivity) (ht v).1
  have hf (v : Fin n) : ⌊(4 : ℝ) * k * t v⌋₊ < 8 * n * k + 1 := by
    apply (Nat.floor_lt (ht₀ v)).mpr
    push_cast
    nlinarith [(ht v).2]
  let g : GridPoint n k := fun v => ⟨⌊(4 : ℝ) * k * t v⌋₊, hf v⟩
  refine ⟨g, ?_⟩
  intro e he
  have ha := hactive e he
  rw [Active, offsetRat_cast] at ha
  have hscale : |4 * (k : ℝ) * (t e.val.1 - t e.val.2) -
      4 * (offsetInt (c e) : ℝ)| < 4 := by
    calc
      _ = |(4 * (k : ℝ)) *
          (t e.val.1 - t e.val.2 - (offsetInt (c e) : ℝ) / k)| := by
        congr 1
        field_simp [ne_of_gt hkR]
      _ = (4 * (k : ℝ)) *
          |t e.val.1 - t e.val.2 - (offsetInt (c e) : ℝ) / k| := by
        rw [abs_mul, abs_of_pos (show (0 : ℝ) < 4 * k by positivity)]
      _ < (4 * (k : ℝ)) * (1 / k) :=
        mul_lt_mul_of_pos_left ha (by positivity)
      _ = 4 := by field_simp [ne_of_gt hkR]
  have h₁ := Nat.floor_le (ht₀ e.val.1)
  have h₂ := Nat.floor_le (ht₀ e.val.2)
  have h₃ := Nat.lt_floor_add_one ((4 : ℝ) * k * t e.val.1)
  have h₄ := Nat.lt_floor_add_one ((4 : ℝ) * k * t e.val.2)
  have hreal : |(g e.val.1 : ℝ) - (g e.val.2 : ℝ) -
      4 * (offsetInt (c e) : ℝ)| ≤ 8 := by
    rcases abs_lt.mp hscale with ⟨hl, hu⟩
    apply abs_le.mpr
    dsimp [g]
    constructor <;> nlinarith
  change |(g e.val.1 : ℤ) - (g e.val.2 : ℤ) - 4 * offsetInt (c e)| ≤ 8
  exact_mod_cast hreal

/-- The finite checker controls all real potentials, including potentials
chosen adaptively after arbitrary query answers. -/
theorem gridAccept_bandGood {n k : ℕ} (hk : 0 < k)
    (c : OffsetTable n k) (hc : GridAccept c) : BandGood c := by
  classical
  intro r
  obtain ⟨g, hg⟩ := exists_grid_cover hk c r
  calc
    (activePairs c r).card ≤ (gridActivePairs c g).card := by
      apply Finset.card_le_card
      intro e he
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hg e (Finset.mem_filter.mp he).2⟩
    _ ≤ bandBudget n k := hc g

end CutQueryComplexity.DirectedUnitST.SparseBand
