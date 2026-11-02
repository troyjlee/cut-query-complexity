import CutQueryComplexity.Graph.ContractionCounting
import Mathlib.Data.Nat.Choose.Bounds

/-! # Counting small cuts in nonnegative weighted graphs

For an integer `k ≥ 1`, the number of proper shores of weight at most `k κ`
is at most `2^(2k) * choose(n,2k)` when `n ≥ 2k`. Below that threshold the
powerset bound applies. Both complementary shores are counted. The proof
uses a positive lower bound `κ` on all proper cuts, not integer edge weights.
-/

namespace CutQueryComplexity
noncomputable section
open scoped Classical
open WeightedGraph
variable {V B : Type} [Fintype V] [DecidableEq V] [Fintype B] [DecidableEq B]

def contractionCountBound (n t : ℕ) : ℕ := 2 ^ min n t * n.choose (min n t)

theorem contractionCountBound_step {n t : ℕ} (ht : t < n) :
    (n - t) * contractionCountBound n t = n * contractionCountBound (n - 1) t := by
  have ht' : t ≤ n - 1 := by omega
  have hn : n - 1 + 1 = n := by omega
  have he := Nat.choose_mul_succ_eq (n - 1) t
  rw [hn] at he
  simp only [contractionCountBound, min_eq_right ht.le, min_eq_right ht']
  calc
    _ = 2 ^ t * (n.choose t * (n - t)) := by ring
    _ = 2 ^ t * ((n - 1).choose t * n) := by rw [← he]
    _ = _ := by ring

theorem contractionCountBound_le_pow {n : ℕ} (hn : 1 ≤ n) (t : ℕ) :
    contractionCountBound n t ≤ (2 * n) ^ t := by
  by_cases h : n ≤ t
  · simp only [contractionCountBound, min_eq_left h, Nat.choose_self, mul_one]
    exact (Nat.pow_le_pow_left (by omega : 2 ≤ 2 * n) n).trans
      (Nat.pow_le_pow_right (by omega : 0 < 2 * n) h)
  · have ht : t ≤ n := by omega
    simp only [contractionCountBound, min_eq_right ht, mul_pow]
    exact Nat.mul_le_mul_left _ (Nat.choose_le_pow n t)

def smallShoreFamily (G : WeightedGraph V) (π : V → B) (L : ℝ) : Finset (Finset V) :=
  (properShores V).filter (fun S => RespectsBlocks π S ∧ G.cut S ≤ L)

@[simp] theorem mem_smallShoreFamily (G : WeightedGraph V) (π : V → B) (L : ℝ)
    (S : Finset V) : S ∈ smallShoreFamily G π L ↔
      ProperShore S ∧ RespectsBlocks π S ∧ G.cut S ≤ L := by
  simp only [smallShoreFamily, Finset.mem_filter, mem_properShores]

theorem survivingShores_subset_smallShoreFamily (G : WeightedGraph V) (π : V → B)
    (L : ℝ) (a b : B) :
    survivingShores π (smallShoreFamily G π L) a b ⊆
      smallShoreFamily G (mergeBlocks π {a, b} a) L := by
  intro S hS
  obtain ⟨hS, hab⟩ := Finset.mem_filter.mp hS
  obtain ⟨hp, hr, hc⟩ := (mem_smallShoreFamily _ _ _ _).mp hS
  exact (mem_smallShoreFamily _ _ _ _).mpr ⟨hp, hr.merge_pair hab, hc⟩

/-- The cut-counting induction applies to every intermediate block map. -/
theorem smallShoreFamily_card_le (G : WeightedGraph V) {κ : ℝ} (hκ : 0 < κ)
    (hmin : ∀ S, ProperShore S → κ ≤ G.cut S) (k : ℕ) (hk : 1 ≤ k) (π : V → B) :
    (smallShoreFamily G π (k * κ)).card ≤ contractionCountBound (liveBlocks π).card (2 * k) := by
  suffices ∀ n (π : V → B), (liveBlocks π).card = n →
      (smallShoreFamily G π (k * κ)).card ≤ contractionCountBound n (2 * k) from
    this _ π rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro π hn
    by_cases hsmall : n ≤ 2 * k
    · have hb := card_respecting_le π (smallShoreFamily G π (k * κ))
        (fun S hS => ((mem_smallShoreFamily _ _ _ _).mp hS).2.1)
      simpa only [hn, contractionCountBound, min_eq_left hsmall, Nat.choose_self, mul_one] using hb
    · have ht : 2 * k < n := by omega
      have hn2 : 2 ≤ (liveBlocks π).card := by omega
      have hsurv (a b : B) (hp : 0 < (G.contract π).w a b) :
          ((survivingShores π (smallShoreFamily G π (k * κ)) a b).card : ℝ) ≤
            contractionCountBound (n - 1) (2 * k) := by
        obtain ⟨ha, hb, hne⟩ := G.contract_weight_pos_labels π hp
        have hcard := liveBlocks_merge_pair_card π ha hb hne
        rw [hn] at hcard
        have hb' := ih (n - 1) (by omega) (mergeBlocks π {a, b} a) hcard
        exact_mod_cast (Finset.card_le_card
          (survivingShores_subset_smallShoreFamily G π (k * κ) a b)).trans hb'
      have hstep := contraction_count_step G π (smallShoreFamily G π (k * κ)) hκ
        (Nat.cast_nonneg k) hmin hn2
        (fun S hS => ((mem_smallShoreFamily _ _ _ _).mp hS).2.1)
        (fun S hS => ((mem_smallShoreFamily _ _ _ _).mp hS).2.2) hsurv
      rw [hn] at hstep
      have hrec := congrArg (fun m : ℕ => (m : ℝ)) (contractionCountBound_step ht)
      simp only [Nat.cast_mul, Nat.cast_sub ht.le, Nat.cast_ofNat] at hrec
      have hp : (0 : ℝ) < n - 2 * (k : ℝ) := by
        apply sub_pos.mpr
        exact_mod_cast ht
      have hb : ((smallShoreFamily G π (k * κ)).card : ℝ) ≤ contractionCountBound n (2 * k) := by
        apply (mul_le_mul_iff_right₀ hp).mp
        nlinarith [hrec, hstep]
      exact_mod_cast hb

namespace WeightedGraph

/-- Proper shores of weight at most an integer multiple of a positive cut lower bound. -/
def nearMinShores (G : WeightedGraph V) (κ : ℝ) (k : ℕ) : Finset (Finset V) :=
  (properShores V).filter (fun S => G.cut S ≤ k * κ)

theorem nearMinShores_card_le (G : WeightedGraph V) {κ : ℝ} (hκ : 0 < κ)
    (hmin : ∀ S, ProperShore S → κ ≤ G.cut S) (k : ℕ) (hk : 1 ≤ k) :
    (G.nearMinShores κ k).card ≤ contractionCountBound (Fintype.card V) (2 * k) := by
  simpa [nearMinShores, smallShoreFamily, liveBlocks] using
    smallShoreFamily_card_le G hκ hmin k hk (id : V → V)

theorem nearMinShores_card_le_pow (G : WeightedGraph V) {κ : ℝ} (hκ : 0 < κ)
    (hmin : ∀ S, ProperShore S → κ ≤ G.cut S) (hn : 1 ≤ Fintype.card V)
    (k : ℕ) (hk : 1 ≤ k) : (G.nearMinShores κ k).card ≤ (2 * Fintype.card V) ^ (2 * k) :=
  (G.nearMinShores_card_le hκ hmin k hk).trans (contractionCountBound_le_pow hn (2 * k))

end WeightedGraph
end
end CutQueryComplexity
