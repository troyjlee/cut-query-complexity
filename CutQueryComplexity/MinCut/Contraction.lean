import CutQueryComplexity.Problem.Basic

/-! # The contraction bound

Let every proper cut of `H` weigh at least `λ > 0`, and let `ℓ` be symmetric edge
lengths, nonnegative on positive edges. Then some set `F` of positive edges crosses
every proper cut and satisfies

  `λ · ℓ(F) ≤ Σ_{u,v} w(u,v) ℓ(u,v)`.

The right side counts each undirected edge twice, so this is `ℓ(F) ≤ (2/λ) Σ_e w_e ℓ_e`.
It replaces Karger's greedy packing lemma in the existence of a good tree
distribution.

The proof runs on a partition into blocks, given by a labelling `c : V → V`, with
`k` blocks. Every block is a proper cut when `k ≥ 2`, so the crossing weight is at
least `kλ` (counted in both directions). Merge the blocks of a shortest crossing
positive edge `e₀`, of length `m`, and recurse with lengths `ℓ − m`. The recursive
set has at most `k − 2` edges, so adding `e₀` costs at most `(k − 1)m`, which the
`kλ·m` saved on the crossing weight pays for.
-/

namespace CutQueryComplexity
namespace Contraction

noncomputable section
open scoped Classical
variable {V : Type} [Fintype V]

/-- Number of blocks of a labelling. -/
def nblocks (c : V → V) : ℕ := (Finset.univ.image c).card

/-- Unions of blocks. -/
def IsUnion (c : V → V) (S : Finset V) : Prop := ∀ u v, c u = c v → (u ∈ S ↔ v ∈ S)

/-- `F` crosses every proper union of blocks. -/
def Connects (c : V → V) (F : Finset (V × V)) : Prop :=
  ∀ S, IsUnion c S → ProperShore S → ∃ e ∈ F, (e.1 ∈ S ↔ e.2 ∉ S)

/-- Weighted length crossing the partition, counted in both directions. -/
def crossW (H : WeightedGraph V) (c : V → V) (ℓ : V → V → ℝ) : ℝ :=
  ∑ u, ∑ v, if c u ≠ c v then H.w u v * ℓ u v else 0

def lenF (ℓ : V → V → ℝ) (F : Finset (V × V)) : ℝ := ∑ e ∈ F, ℓ e.1 e.2

/-- The blocks' cuts add up to the crossing weight. -/
theorem sum_block_cuts (H : WeightedGraph V) (c : V → V) :
    ∑ y ∈ Finset.univ.image c, H.cut (Finset.univ.filter fun x => c x = y) =
      ∑ u, ∑ v, if c u ≠ c v then H.w u v else 0 := by
  have hfib := Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ.image c)
    (g := c) (fun x _ => Finset.mem_image_of_mem c (Finset.mem_univ x))
    (fun u => ∑ v, if c u ≠ c v then H.w u v else 0)
  rw [← hfib]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [WeightedGraph.cut]
  refine Finset.sum_congr rfl fun u hu => ?_
  have hcu : c u = y := (Finset.mem_filter.mp hu).2
  rw [← Finset.sum_filter]
  congr 1
  ext v
  simp [hcu, eq_comm]

theorem nblocks_le_one {c : V → V} (hk : nblocks c ≤ 1) (u v : V) : c u = c v :=
  Finset.card_le_one.mp hk _ (Finset.mem_image_of_mem c (Finset.mem_univ u)) _
    (Finset.mem_image_of_mem c (Finset.mem_univ v))

/-- With at least two blocks, the crossing weight is at least `kλ`. -/
theorem crossing_ge (H : WeightedGraph V) {lam : ℝ}
    (hcut : ∀ S, ProperShore S → lam ≤ H.cut S) {c : V → V} (hk : 2 ≤ nblocks c) :
    nblocks c * lam ≤ ∑ u, ∑ v, if c u ≠ c v then H.w u v else 0 := by
  rw [← sum_block_cuts]
  have : ∑ _y ∈ Finset.univ.image c, lam ≤
      ∑ y ∈ Finset.univ.image c, H.cut (Finset.univ.filter fun x => c x = y) := by
    refine Finset.sum_le_sum fun y hy => hcut _ ⟨?_, ?_⟩
    · obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hy
      exact ⟨x, by simp⟩
    · intro h
      obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hy
      have : ¬ nblocks c ≤ 1 := by omega
      apply this
      refine Finset.card_le_one.mpr fun a ha b hb => ?_
      obtain ⟨a', _, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨b', _, rfl⟩ := Finset.mem_image.mp hb
      have ha' : a' ∈ Finset.univ.filter fun x => c x = y := by rw [h]; exact Finset.mem_univ a'
      have hb' : b' ∈ Finset.univ.filter fun x => c x = y := by rw [h]; exact Finset.mem_univ b'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha' hb'
      rw [ha', hb']
  simpa [nblocks] using this

theorem crossW_nonneg (H : WeightedGraph V) {c : V → V} {ℓ : V → V → ℝ}
    (hℓ : ∀ u v, c u ≠ c v → 0 < H.w u v → 0 ≤ ℓ u v) : 0 ≤ crossW H c ℓ := by
  refine Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun v _ => ?_
  split_ifs with h
  · rcases (H.nonneg u v).eq_or_lt with h0 | h0
    · rw [← h0, zero_mul]
    · exact mul_nonneg h0.le (hℓ u v h h0)
  · exact le_rfl

/-- Merge the block of `b` into the block of `a`. -/
def merge (c : V → V) (a b : V) (x : V) : V := if c x = c b then c a else c x

omit [Fintype V] in
theorem merge_eq_iff {c : V → V} {a b : V} (x y : V) :
    merge c a b x = merge c a b y ↔
      c x = c y ∨ ((c x = c a ∨ c x = c b) ∧ (c y = c a ∨ c y = c b)) := by
  unfold merge
  by_cases hx : c x = c b <;> by_cases hy : c y = c b <;> simp only [hx, hy, ↓reduceIte] <;>
    constructor <;> intro h <;> first | tauto | (rcases h with h | ⟨h1 | h1, h2 | h2⟩ <;> simp_all)

theorem image_merge {c : V → V} {a b : V} (hab : c a ≠ c b) :
    Finset.univ.image (merge c a b) = (Finset.univ.image c).erase (c b) := by
  ext y
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_erase, merge]
  constructor
  · rintro ⟨x, rfl⟩
    by_cases hx : c x = c b
    · simp only [hx, ↓reduceIte]; exact ⟨hab, a, rfl⟩
    · simp only [hx, ↓reduceIte]; exact ⟨hx, x, rfl⟩
  · rintro ⟨hy, x, rfl⟩
    exact ⟨x, by simp [hy]⟩

theorem nblocks_merge {c : V → V} {a b : V} (hab : c a ≠ c b) :
    nblocks (merge c a b) = nblocks c - 1 := by
  rw [nblocks, image_merge hab, Finset.card_erase_of_mem (Finset.mem_image_of_mem c
    (Finset.mem_univ b)), nblocks]

/-- **Contraction bound on a partition.** -/
theorem contraction_blocks (H : WeightedGraph V) {lam : ℝ} (hlam : 0 < lam)
    (hcut : ∀ S, ProperShore S → lam ≤ H.cut S) :
    ∀ k (c : V → V) (ℓ : V → V → ℝ), nblocks c = k → (∀ u v, ℓ u v = ℓ v u) →
      (∀ u v, c u ≠ c v → 0 < H.w u v → 0 ≤ ℓ u v) →
      ∃ F : Finset (V × V), F.card ≤ k - 1 ∧
        (∀ e ∈ F, 0 < H.w e.1 e.2 ∧ c e.1 ≠ c e.2) ∧ Connects c F ∧
        lam * lenF ℓ F ≤ crossW H c ℓ := by
  intro k
  induction k with
  | zero =>
      intro c ℓ hk _ hℓ
      refine ⟨∅, by simp, by simp, ?_, by simpa [lenF] using crossW_nonneg H hℓ⟩
      intro S _ hS
      obtain ⟨u, hu⟩ := hS.1
      have := Finset.card_pos.mpr ⟨c u, Finset.mem_image_of_mem c (Finset.mem_univ u)⟩
      unfold nblocks at hk
      omega
  | succ k ih =>
  intro c ℓ hk hsym hℓ
  by_cases hk1 : k = 0
  · subst hk1
    refine ⟨∅, by simp, by simp, ?_, by simpa [lenF] using crossW_nonneg H hℓ⟩
    intro S hU hS
    obtain ⟨u, hu⟩ := hS.1
    obtain ⟨v, hv⟩ : ∃ v, v ∉ S := by
      by_contra h
      push Not at h
      exact hS.2 (Finset.eq_univ_of_forall h)
    exact (hv ((hU u v (nblocks_le_one (by omega) u v)).mp hu)).elim
  -- At least two blocks: a positive crossing edge exists.
  have hk2 : 2 ≤ nblocks c := by omega
  set P := Finset.univ.filter fun e : V × V => c e.1 ≠ c e.2 ∧ 0 < H.w e.1 e.2
  have hP : P.Nonempty := by
    have h := crossing_ge H hcut hk2
    have hpos : 0 < ∑ u, ∑ v, if c u ≠ c v then H.w u v else 0 := by
      have : (0 : ℝ) < nblocks c * lam := mul_pos (by exact_mod_cast (by omega : 0 < nblocks c)) hlam
      linarith
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    have : ∑ u, ∑ v, (if c u ≠ c v then H.w u v else 0) = 0 := by
      refine Finset.sum_eq_zero fun u _ => Finset.sum_eq_zero fun v _ => ?_
      split_ifs with h
      · rcases (H.nonneg u v).eq_or_lt with h0 | h0
        · exact h0.symm
        · have : (u, v) ∈ P := by simp [P, h, h0]
          simp [hne] at this
      · rfl
    linarith
  obtain ⟨e₀, he₀, hmin⟩ := Finset.exists_min_image P (fun e => ℓ e.1 e.2) hP
  obtain ⟨a, b⟩ := e₀
  simp only [P, Finset.mem_filter, Finset.mem_univ, true_and] at he₀
  obtain ⟨hab, hwab⟩ := he₀
  set m := ℓ a b
  have hm0 : 0 ≤ m := hℓ a b hab hwab
  have hmle : ∀ u v, c u ≠ c v → 0 < H.w u v → m ≤ ℓ u v := fun u v h1 h2 =>
    hmin (u, v) (by simp [P, h1, h2])
  set c' := merge c a b
  have hcross' : ∀ u v, c' u ≠ c' v → c u ≠ c v := fun u v h h' =>
    h ((merge_eq_iff u v).mpr (Or.inl h'))
  obtain ⟨F', hcard, hedge, hconn, hbound⟩ := ih c' (fun u v => ℓ u v - m)
    (by rw [nblocks_merge hab, hk]; rfl) (fun u v => by rw [hsym])
    (fun u v h hw => sub_nonneg.mpr (hmle u v (hcross' u v h) hw))
  refine ⟨insert (a, b) F', ?_, ?_, ?_, ?_⟩
  · exact (Finset.card_insert_le _ _).trans (by omega)
  · intro e he
    rcases Finset.mem_insert.mp he with rfl | he
    · exact ⟨hwab, hab⟩
    · exact ⟨(hedge e he).1, hcross' _ _ (hedge e he).2⟩
  · intro S hU hS
    by_cases hsplit : (a ∈ S ↔ b ∈ S)
    · have hU' : IsUnion c' S := by
        intro u v huv
        rcases (merge_eq_iff u v).mp huv with h | ⟨h1 | h1, h2 | h2⟩
        · exact hU u v h
        · exact (hU u a h1).trans (hU a v h2.symm)
        · exact (hU u a h1).trans (hsplit.trans (hU b v h2.symm))
        · exact (hU u b h1).trans (hsplit.symm.trans (hU a v h2.symm))
        · exact (hU u b h1).trans (hU b v h2.symm)
      obtain ⟨e, he, hcr⟩ := hconn S hU' hS
      exact ⟨e, Finset.mem_insert_of_mem he, hcr⟩
    · exact ⟨(a, b), Finset.mem_insert_self _ _, by simp only; tauto⟩
  · -- The length bound.
    have hins : lenF ℓ (insert (a, b) F') ≤ m + lenF ℓ F' := by
      unfold lenF
      by_cases hmem : (a, b) ∈ F'
      · rw [Finset.insert_eq_of_mem hmem]; linarith
      · rw [Finset.sum_insert hmem]
    have hsub : lenF ℓ F' = lenF (fun u v => ℓ u v - m) F' + F'.card * m := by
      unfold lenF
      rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
      ring
    have hcardR : (F'.card : ℝ) ≤ (k : ℝ) - 1 := by
      have : F'.card + 1 ≤ k := by omega
      have : (F'.card : ℝ) + 1 ≤ k := by exact_mod_cast this
      linarith
    -- Crossing weight split.
    have hW : crossW H c' (fun u v => ℓ u v - m) + m * ((k + 1 : ℕ) * lam) ≤ crossW H c ℓ := by
      have hge := crossing_ge H hcut hk2
      rw [hk] at hge
      have h1 : crossW H c' (fun u v => ℓ u v - m) ≤
          ∑ u, ∑ v, (if c u ≠ c v then H.w u v * (ℓ u v - m) else 0) := by
        refine Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => ?_
        by_cases h' : c' u ≠ c' v
        · simp [h', hcross' u v h']
        · simp only [h', ↓reduceIte]
          split_ifs with h
          · rcases (H.nonneg u v).eq_or_lt with h0 | h0
            · rw [← h0, zero_mul]
            · exact mul_nonneg h0.le (sub_nonneg.mpr (hmle u v h h0))
          · exact le_rfl
      have h2 : ∑ u, ∑ v, (if c u ≠ c v then H.w u v * (ℓ u v - m) else 0) +
          m * ∑ u, ∑ v, (if c u ≠ c v then H.w u v else 0) = crossW H c ℓ := by
        unfold crossW
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun v _ => ?_
        split_ifs <;> ring
      nlinarith
    have hkR : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    rw [hkR] at hW
    calc lam * lenF ℓ (insert (a, b) F')
        ≤ lam * (m + lenF (fun u v => ℓ u v - m) F' + F'.card * m) := by
          rw [hsub] at hins; nlinarith
      _ ≤ crossW H c' (fun u v => ℓ u v - m) + lam * (m + ((k : ℝ) - 1) * m) := by
          have : lam * (F'.card * m) ≤ lam * (((k : ℝ) - 1) * m) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcardR hm0) hlam.le
          linarith
      _ ≤ crossW H c ℓ := by
          have : 0 ≤ lam * m := mul_nonneg hlam.le hm0
          have e : lam * (m + ((k : ℝ) - 1) * m) + lam * m = m * (((k : ℝ) + 1) * lam) := by ring
          linarith

/-- **Contraction bound.** Some set of positive edges crosses every proper cut and has
`λ·ℓ(F) ≤ Σ_{u,v} w(u,v) ℓ(u,v)`. -/
theorem exists_connector (H : WeightedGraph V) {lam : ℝ} (hlam : 0 < lam)
    (hcut : ∀ S, ProperShore S → lam ≤ H.cut S) (ℓ : V → V → ℝ) (hsym : ∀ u v, ℓ u v = ℓ v u)
    (hℓ : ∀ u v, 0 < H.w u v → 0 ≤ ℓ u v) :
    ∃ F : Finset (V × V), (∀ e ∈ F, 0 < H.w e.1 e.2) ∧
      (∀ S, ProperShore S → ∃ e ∈ F, (e.1 ∈ S ↔ e.2 ∉ S)) ∧
      lam * lenF ℓ F ≤ ∑ u, ∑ v, H.w u v * ℓ u v := by
  obtain ⟨F, -, hedge, hconn, hb⟩ := contraction_blocks H hlam hcut _ id ℓ rfl hsym
    (fun u v _ hw => hℓ u v hw)
  refine ⟨F, fun e he => (hedge e he).1, fun S hS => hconn S (fun u v h => by
    simp only [id] at h; rw [h]) hS, hb.trans (le_of_eq ?_)⟩
  unfold crossW
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
  by_cases h : u = v
  · subst h; simp [H.diag]
  · simp [h]

end
end Contraction
end CutQueryComplexity
