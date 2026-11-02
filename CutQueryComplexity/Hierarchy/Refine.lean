import CutQueryComplexity.Hierarchy.Guard

/-! # Hierarchy refinement (Lemmas 22–23, Theorem 24)

The deferred external input is `HierarchyBound a h` (Lemma 21 in cut form): every explicit
graph `J` on `r` vertices has a hierarchy with at most `2r + 1` nodes, childless leaf nodes,
height at most `h r`, and canonical representation cost at most `a r` times every cut.

One refinement round runs the skeleton program of Theorem 15 with guard weight `γ` and
completion parameter `q ≥ 2B/γ`, giving an explicit graph `H₀ = F + γJ`. A hierarchy of
`H₀` is chosen offline, and its canonical capacities for `G` give the new hierarchy.

* `transfer_cut`: `c_G(S) ≤ c_{H₀}(S) + η c_{H₀}(S)² / (γ² λ)` (Lemma 22, cut form).
* `transfer_rep`: the same inequality for representation costs of any hierarchy, with
  no factor depending on its size or depth (Lemma 22, tree form).
* `round_promise`: with `γ = 1/(100 a² ρ²)` and `γB ≥ 1`, the promise `R(S*) ≤ Bλ`
  becomes `R_new(S*) ≤ (B/2) λ` for the same minimum cut (Lemma 23).
* `refine_weakSkeleton`: iterating rounds while `γB ≥ 1` and finishing with Theorem 15
  gives a weak skeleton with `O(M a² ρ⁴ B log n)` queries for hierarchies with at most `M`
  nodes (Theorem 24 with the elementary guard of quality `ρ`).
-/

namespace CutQueryComplexity
namespace Hierarchy

open TwoRespecting WeightedGraph Search Search.Comp Discovery Finset

variable {V : Type} [Fintype V] [DecidableEq V]

namespace Hier

variable {N : Type} [Fintype N] [DecidableEq N]

/-- The height of a hierarchy. -/
def height (H : Hier V N) : ℕ := univ.sup H.T.depth

omit [Fintype V] [DecidableEq V] [DecidableEq N] in
theorem depth_le_height (H : Hier V N) (x : N) : H.T.depth x ≤ H.height :=
  le_sup (f := H.T.depth) (mem_univ x)

/-- Guards of lower quality are guards of higher quality. -/
theorem GuardFor.mono [LinearOrder N] {H : Hier V N} {ρ ρ' : ℝ} (hg : H.GuardFor ρ)
    (hρ : ρ ≤ ρ') : H.GuardFor ρ' := by
  intro cap hcap hsub
  obtain ⟨J, hJ⟩ := hg cap hcap hsub
  refine ⟨J, fun S => ⟨(hJ S).1, (hJ S).2.trans ?_⟩⟩
  exact mul_le_mul_of_nonneg_right hρ (H.rep_nonneg hcap S)

/-- The star-mesh guard of quality `ρ` for a hierarchy of height at most `ρ / 2`. -/
theorem guardFor_of_height [LinearOrder N] {H : Hier V N} (hlc : H.LeafChildless) {ρ : ℝ}
    (hρ : 2 * (H.height : ℝ) ≤ ρ) : H.GuardFor ρ :=
  guardFor_of_leafChildless hlc hρ

end Hier

/-- **Lemma 21 as a hypothesis.** Every explicit graph on `r` vertices has a hierarchy with
at most `2r + 1` nodes, childless leaf nodes, height at most `h r`, and canonical
representation cost at most `a r` times every cut. -/
def HierarchyBound (a : ℕ → ℝ) (h : ℕ → ℕ) : Prop :=
  ∀ (W : Type) [Fintype W] [DecidableEq W] (J : WeightedGraph W),
    ∃ m : ℕ, ∃ H : Hier W (Fin m), m ≤ 2 * Fintype.card W + 1 ∧ H.LeafChildless ∧
      H.height ≤ h (Fintype.card W) ∧ ∀ S, H.rep (H.canon J) S ≤ a (Fintype.card W) * J.cut S

/-- A hierarchy whose node type is `Fin m`. -/
structure Pkg (V : Type) where
  m : ℕ
  H : Hier V (Fin m)

/-- The hierarchy of an explicit graph supplied by `HierarchyBound`, chosen offline. -/
noncomputable def hbPkg {a : ℕ → ℝ} {h : ℕ → ℕ} (hb : HierarchyBound a h)
    (J : WeightedGraph V) : Pkg V :=
  ⟨Classical.choose (hb V J), Classical.choose (Classical.choose_spec (hb V J))⟩

theorem hbPkg_spec {a : ℕ → ℝ} {h : ℕ → ℕ} (hb : HierarchyBound a h) (J : WeightedGraph V) :
    (hbPkg hb J).m ≤ 2 * Fintype.card V + 1 ∧ (hbPkg hb J).H.LeafChildless ∧
      (hbPkg hb J).H.height ≤ h (Fintype.card V) ∧
      ∀ S, (hbPkg hb J).H.rep ((hbPkg hb J).H.canon J) S ≤ a (Fintype.card V) * J.cut S :=
  Classical.choose_spec (Classical.choose_spec (hb V J))

namespace Hier

variable {N : Type} [Fintype N] [DecidableEq N]

/-- **Lemma 22, tree form.** If every cut of `G` is at most `c + κ c²` in terms of the
corresponding cut `c` of `H₀`, the same holds for the canonical representation costs of
any hierarchy. -/
theorem transfer_rep (H' : Hier V N) (G H0 : WeightedGraph V) {κ : ℝ} (hκ : 0 ≤ κ)
    (hcut : ∀ S, G.cut S ≤ H0.cut S + κ * H0.cut S ^ 2) (S : Finset V) :
    H'.rep (H'.canon G) S ≤ H'.rep (H'.canon H0) S + κ * H'.rep (H'.canon H0) S ^ 2 := by
  obtain ⟨ℓ, hℓ, heq⟩ := H'.exists_rep_eq (H'.canon H0) S
  set δ : N → ℝ := fun x => |toReal ℓ x - toReal ℓ (H'.T.parent x)|
  have hδ0 : ∀ x, 0 ≤ δ x := fun x => abs_nonneg _
  have hδ1 : ∀ x, δ x * δ x = δ x := fun x => by
    simp only [δ, toReal]; split_ifs <;> norm_num
  set y : N → ℝ := fun x => H'.canon H0 x * δ x
  have hy0 : ∀ x, 0 ≤ y x := fun x => mul_nonneg (H0.cut_nonneg _) (hδ0 x)
  have hR : H'.rep (H'.canon H0) S = ∑ x ∈ H'.edges, y x := by
    rw [heq]; rfl
  have hsq : ∑ x ∈ H'.edges, y x ^ 2 ≤ (∑ x ∈ H'.edges, y x) ^ 2 := by
    rw [sq, sum_mul]
    refine sum_le_sum fun x hx => ?_
    rw [sq]
    exact mul_le_mul_of_nonneg_left (single_le_sum (fun z _ => hy0 z) hx) (hy0 x)
  calc H'.rep (H'.canon G) S ≤ H'.labelCost (H'.canon G) (toReal ℓ) := H'.rep_le _ hℓ
    _ = ∑ x ∈ H'.edges, G.cut (H'.cluster x) * δ x := rfl
    _ ≤ ∑ x ∈ H'.edges, (y x + κ * y x ^ 2) := by
        refine sum_le_sum fun x _ => ?_
        have h1 := mul_le_mul_of_nonneg_right (hcut (H'.cluster x)) (hδ0 x)
        have h2 : (H0.cut (H'.cluster x) + κ * H0.cut (H'.cluster x) ^ 2) * δ x =
            y x + κ * y x ^ 2 := by
          simp only [y, canon]
          have := hδ1 x
          rw [mul_pow, sq (δ x), this]; ring
        linarith
    _ = ∑ x ∈ H'.edges, y x + κ * ∑ x ∈ H'.edges, y x ^ 2 := by
        rw [sum_add_distrib, mul_sum]
    _ ≤ ∑ x ∈ H'.edges, y x + κ * (∑ x ∈ H'.edges, y x) ^ 2 := by
        gcongr
    _ = _ := by rw [hR]

variable [LinearOrder N] {H : Hier V N}

/-- The completion and guard parts of the skeleton program on the genuine oracle. -/
theorem supplied_parts (G : WeightedGraph V) {ρ : ℝ} (hg : H.GuardFor ρ) {s : ℝ} (hs : 0 ≤ s)
    (q : ℕ) :
    ∃ J : WeightedGraph V,
      (∀ S, (∃ a, H.ExtendsR S a ∧ H.labelCost (H.canon G) a ≤ J.cut S) ∧
        J.cut S ≤ ρ * H.rep (H.canon G) S) ∧
      ∀ S, ((H.supplied hg s hs q).eval G.cut).cut S =
        ((H.completion q).eval G.cut).cut S + s * J.cut S := by
  obtain ⟨cap, hcap, hcapeq, hsub, heval⟩ := supplied_eval (H := H) G hg hs q
  refine ⟨guardOf hg cap hcap, fun S => ?_, fun S => ?_⟩
  · obtain ⟨⟨a, ha, hle⟩, hup⟩ := guardOf_spec hg cap hcap hsub S
    refine ⟨⟨a, ha, ?_⟩, ?_⟩
    · rwa [labelCost_congr hcapeq] at hle
    · rwa [rep_congr hcapeq] at hup
  · rw [heval, cut_add, cut_scale]

/-- **Lemma 22, cut form.** -/
theorem transfer_cut (G : WeightedGraph V) {ρ : ℝ} (hg : H.GuardFor ρ) {γ : ℝ} (hγ : 0 < γ)
    {q : ℕ} (hq : 1 ≤ q) {η : ℝ} (hqη : 2 / (q : ℝ) ≤ η) (hlam : 0 < mincutValue G)
    (S : Finset V) :
    G.cut S ≤ ((H.supplied hg γ hγ.le q).eval G.cut).cut S +
      η / (γ ^ 2 * mincutValue G) * ((H.supplied hg γ hγ.le q).eval G.cut).cut S ^ 2 := by
  obtain ⟨J, hJ, hsum⟩ := supplied_parts (H := H) G hg hγ.le q
  rw [hsum]
  obtain ⟨⟨a, ha, hL⟩, -⟩ := hJ S
  set L := H.labelCost (H.canon G) a
  set F := (H.completion q).eval G.cut
  have hF := (completion_close (H := H) G hq hqη hlam ha).1
  have hFnn := F.cut_nonneg S
  have hL0 : 0 ≤ L := H.labelCost_nonneg (fun x => G.cut_nonneg _) a
  have hη : 0 ≤ η := le_trans (by positivity) hqη
  set c := F.cut S + γ * J.cut S
  have hγL : γ * L ≤ c := by
    have := mul_le_mul_of_nonneg_left hL hγ.le; linarith
  have hc0 : 0 ≤ c := le_trans (mul_nonneg hγ.le hL0) hγL
  have hL2 : L ^ 2 ≤ c ^ 2 / γ ^ 2 := by
    rw [le_div_iff₀ (by positivity), ← mul_pow, mul_comm]
    exact pow_le_pow_left₀ (mul_nonneg hγ.le hL0) hγL 2
  have h1 : η * L ^ 2 / mincutValue G ≤ η / (γ ^ 2 * mincutValue G) * c ^ 2 := by
    rw [div_le_iff₀ hlam]
    calc η * L ^ 2 ≤ η * (c ^ 2 / γ ^ 2) := mul_le_mul_of_nonneg_left hL2 hη
      _ = η / (γ ^ 2 * mincutValue G) * c ^ 2 * mincutValue G := by
          field_simp
  have hJnn := J.cut_nonneg S
  nlinarith

/-- **Lemma 23.** One refinement round halves the promise for the same minimum cut. -/
theorem round_promise (G : WeightedGraph V) {ρ : ℝ} (hρ : 1 ≤ ρ) (hg : H.GuardFor ρ)
    {a γ B : ℝ} (ha : 1 ≤ a) (hγ : 0 < γ) (hγdef : 100 * a ^ 2 * ρ ^ 2 * γ ≤ 1)
    (hγB : 1 ≤ γ * B) {q : ℕ} (hq : 1 ≤ q) (hqη : 2 / (q : ℝ) ≤ γ / B)
    (hlam : 0 < mincutValue G) {S : Finset V} (hSmin : G.cut S = mincutValue G)
    (hRS : H.rep (H.canon G) S ≤ B * mincutValue G)
    {M : Type} [Fintype M] [DecidableEq M] (H' : Hier V M)
    (hH' : ∀ T, H'.rep (H'.canon ((H.supplied hg γ hγ.le q).eval G.cut)) T ≤
      a * ((H.supplied hg γ hγ.le q).eval G.cut).cut T) :
    H'.rep (H'.canon G) S ≤ B / 2 * mincutValue G := by
  set lam := mincutValue G
  set H0 := (H.supplied hg γ hγ.le q).eval G.cut
  have hB : 0 < B := by
    by_contra hB; push Not at hB; nlinarith
  set η := γ / B
  have hη : 0 < η := div_pos hγ hB
  -- the cut of `H₀` at the optimum
  obtain ⟨J, hJ, hsum⟩ := supplied_parts (H := H) G hg hγ.le q
  set R := H.rep (H.canon G) S
  have hR0 : 0 ≤ R := le_trans (G.cut_nonneg S) (cut_le_rep G S)
  obtain ⟨ℓ, hℓ, hRℓ⟩ := H.exists_rep_eq (H.canon G) S
  have hF := (completion_close (H := H) G hq hqη hlam (extendsR_toReal hℓ)).2
  rw [← hRℓ, hSmin] at hF
  have hJS := (hJ S).2
  have hRB2 : R ^ 2 ≤ (B * lam) ^ 2 := pow_le_pow_left₀ hR0 hRS 2
  have hFS : ((H.completion q).eval G.cut).cut S ≤ lam * (1 + γ * B) := by
    have : η * R ^ 2 / lam ≤ γ * B * lam := by
      rw [div_le_iff₀ hlam]
      calc η * R ^ 2 ≤ η * (B * lam) ^ 2 := mul_le_mul_of_nonneg_left hRB2 hη.le
        _ = γ * B * lam * lam := by simp only [η]; field_simp
    linarith
  have hH0S : H0.cut S ≤ lam * (3 * ρ * (γ * B)) := by
    rw [hsum]
    have h1 : γ * J.cut S ≤ γ * (ρ * (B * lam)) :=
      mul_le_mul_of_nonneg_left (hJS.trans (mul_le_mul_of_nonneg_left hRS (by linarith))) hγ.le
    have hργB : 1 ≤ ρ * (γ * B) := by nlinarith
    have hγBρ : γ * B ≤ ρ * (γ * B) := by nlinarith
    have e1 : γ * (ρ * (B * lam)) = lam * (ρ * (γ * B)) := by ring
    have e2 : lam * 1 ≤ lam * (ρ * (γ * B)) := mul_le_mul_of_nonneg_left hργB hlam.le
    have e3 : lam * (γ * B) ≤ lam * (ρ * (γ * B)) := mul_le_mul_of_nonneg_left hγBρ hlam.le
    nlinarith
  -- the hierarchy of `H₀` at the optimum
  set x := 3 * a * ρ * (γ * B)
  have hRH : H'.rep (H'.canon H0) S ≤ x * lam := by
    calc _ ≤ a * H0.cut S := hH' S
      _ ≤ a * (lam * (3 * ρ * (γ * B))) := mul_le_mul_of_nonneg_left hH0S (by linarith)
      _ = x * lam := by simp only [x]; ring
  have hRH0 : 0 ≤ H'.rep (H'.canon H0) S := H'.rep_nonneg (fun _ => H0.cut_nonneg _) S
  have hcut : ∀ T, G.cut T ≤ H0.cut T + η / (γ ^ 2 * lam) * H0.cut T ^ 2 :=
    fun T => transfer_cut (H := H) G hg hγ hq hqη hlam T
  have hκ : 0 ≤ η / (γ ^ 2 * lam) := by positivity
  have htr := transfer_rep H' G H0 hκ hcut S
  have hsq : H'.rep (H'.canon H0) S ^ 2 ≤ (x * lam) ^ 2 := pow_le_pow_left₀ hRH0 hRH 2
  have hx2 : η / (γ ^ 2 * lam) * (x * lam) ^ 2 = x ^ 2 / (γ * B) * lam := by
    simp only [η]; field_simp
  have hfin : x + x ^ 2 / (γ * B) ≤ B / 2 := by
    have hγB0 : 0 < γ * B := by linarith
    have hx : x ^ 2 / (γ * B) = 9 * a ^ 2 * ρ ^ 2 * (γ * B) := by
      simp only [x]; field_simp; norm_num
    rw [hx]
    have haρ : 1 ≤ a * ρ := one_le_mul_of_one_le_of_one_le ha hρ
    have hap : a * ρ ≤ a ^ 2 * ρ ^ 2 := by
      calc a * ρ ≤ (a * ρ) * (a * ρ) := le_mul_of_one_le_right (by linarith) haρ
        _ = a ^ 2 * ρ ^ 2 := by ring
    have h12 : x + 9 * a ^ 2 * ρ ^ 2 * (γ * B) ≤ 12 * (a ^ 2 * ρ ^ 2 * γ) * B := by
      have := mul_le_mul_of_nonneg_right hap hγB0.le
      simp only [x]; nlinarith
    nlinarith
  calc H'.rep (H'.canon G) S
      ≤ H'.rep (H'.canon H0) S + η / (γ ^ 2 * lam) * H'.rep (H'.canon H0) S ^ 2 := htr
    _ ≤ x * lam + η / (γ ^ 2 * lam) * (x * lam) ^ 2 := by gcongr
    _ = (x + x ^ 2 / (γ * B)) * lam := by rw [hx2]; ring
    _ ≤ B / 2 * lam := mul_le_mul_of_nonneg_right hfin hlam.le

end Hier

/-! ## The refinement program -/

section Program

variable {a : ℕ → ℝ} {h : ℕ → ℕ}

/-- The completion parameter of a round with promise `B`. -/
noncomputable def roundQ (γ B : ℝ) : ℕ := ⌈2 * B / γ⌉₊

/-- The completion parameter of the final skeleton with promise `B`. -/
noncomputable def finalQ (ρ B : ℝ) : ℕ := ⌈200 * ρ ^ 2 * B ^ 2⌉₊

open Classical in
/-- Theorem 15 on a package, with the star-mesh guard of quality `ρ` when it applies. -/
noncomputable def finalProg (ρ B : ℝ) (hρB : 0 ≤ 1 / (10 * ρ * B)) (P : Pkg V) :
    Comp (Finset V) ℝ (WeightedGraph V) :=
  if hg : P.H.GuardFor ρ then P.H.supplied hg (1 / (10 * ρ * B)) hρB (finalQ ρ B) else .pure 0

open Classical in
/-- One refinement round: the explicit graph `H₀`. -/
noncomputable def roundProg (ρ γ : ℝ) (hγ : 0 ≤ γ) (B : ℝ) (P : Pkg V) :
    Comp (Finset V) ℝ (WeightedGraph V) :=
  if hg : P.H.GuardFor ρ then P.H.supplied hg γ hγ (roundQ γ B) else .pure 0

/-- **Theorem 24 as a program.** Refine while `γB ≥ 1`, then build the skeleton. -/
noncomputable def refine (hb : HierarchyBound a h) (ρ γ : ℝ) (hγ : 0 ≤ γ)
    (hfin : ∀ B : ℝ, 0 < B → 0 ≤ 1 / (10 * ρ * B)) :
    ℕ → ℝ → Pkg V → Comp (Finset V) ℝ (WeightedGraph V)
  | 0, B, P => if hB : 0 < B then finalProg ρ B (hfin B hB) P else .pure 0
  | fuel + 1, B, P =>
      if γ * B < 1 then (if hB : 0 < B then finalProg ρ B (hfin B hB) P else .pure 0)
      else (roundProg ρ γ hγ B P).bind fun H0 => refine hb ρ γ hγ hfin fuel (B / 2) (hbPkg hb H0)

/-- Real form of the cost of Theorem 15 on a package with at most `M` nodes. -/
theorem supplied_cost_real (G : WeightedGraph V) (P : Pkg V) {ρ s : ℝ} (hg : P.H.GuardFor ρ)
    (hs : 0 ≤ s) {q : ℕ} (hq : 1 ≤ q) {M : ℕ} (hM : P.m ≤ M) {x : ℝ} (hx : (q : ℝ) - 1 ≤ x) :
    ((P.H.supplied hg s hs q).cost G.cut : ℝ) ≤
      M * (1 + 4 * x * ((Nat.log 2 (Fintype.card V) : ℝ) + 3)) := by
  have h := Hier.supplied_cost (H := P.H) G hg hs hq
  have hE : P.H.edges.card ≤ M := by
    refine le_trans ?_ hM
    simp only [Hier.edges]
    exact (card_erase_le).trans (by simp)
  have hq1 : ((q - 1 : ℕ) : ℝ) ≤ x := by
    rw [Nat.cast_sub hq]; simpa using hx
  have hx0 : 0 ≤ x := le_trans (Nat.cast_nonneg _) hq1
  calc ((P.H.supplied hg s hs q).cost G.cut : ℝ)
      ≤ ((P.H.edges.card * (1 + 4 * ((q - 1) * (Nat.log 2 (Fintype.card V) + 3))) : ℕ) : ℝ) := by
        exact_mod_cast h
    _ = (P.H.edges.card : ℝ) * (1 + 4 * (((q - 1 : ℕ) : ℝ) *
          ((Nat.log 2 (Fintype.card V) : ℝ) + 3))) := by push_cast; ring
    _ ≤ M * (1 + 4 * x * ((Nat.log 2 (Fintype.card V) : ℝ) + 3)) := by
        have hL : (0 : ℝ) ≤ (Nat.log 2 (Fintype.card V) : ℝ) + 3 := by positivity
        have h1 : (1 : ℝ) + 4 * (((q - 1 : ℕ) : ℝ) * ((Nat.log 2 (Fintype.card V) : ℝ) + 3)) ≤
            1 + 4 * x * ((Nat.log 2 (Fintype.card V) : ℝ) + 3) := by
          have := mul_le_mul_of_nonneg_right hq1 hL; nlinarith
        have hEr : (P.H.edges.card : ℝ) ≤ M := by exact_mod_cast hE
        have h0 : (0 : ℝ) ≤ 1 + 4 * (((q - 1 : ℕ) : ℝ) * ((Nat.log 2 (Fintype.card V) : ℝ) + 3)) :=
          by positivity
        nlinarith

/-- **Theorem 24, for any guard regime.** `Good` packages have guards of quality `ρ`, and every
package chosen by `HierarchyBound` is good. Every hierarchy has at most `M` nodes;
`L = ⌊log₂ n⌋ + 3`. The query cost is at most
`M (fuel + 1) + M L (16 + 800 ρ²) B / γ`. -/
theorem refine_spec_of_good (hb : HierarchyBound a h) (G : WeightedGraph V)
    (hn : 2 ≤ Fintype.card V)
    (hlam : 0 < mincutValue G) {ρ γ : ℝ} (hρ : 1 ≤ ρ) (hγ : 0 < γ)
    (hγdef : 100 * a (Fintype.card V) ^ 2 * ρ ^ 2 * γ ≤ 1) (ha : 1 ≤ a (Fintype.card V))
    (Good : Pkg V → Prop) (hgood : ∀ P, Good P → P.H.GuardFor ρ)
    (hsel : ∀ J : WeightedGraph V, Good (hbPkg hb J)) {M : ℕ} (hM : 2 * Fintype.card V + 1 ≤ M)
    (hfin : ∀ B : ℝ, 0 < B → 0 ≤ 1 / (10 * ρ * B)) :
    ∀ (fuel : ℕ) (B : ℝ) (P : Pkg V), 1 ≤ B → γ * B < 2 ^ fuel → Good P → P.m ≤ M →
      (∃ S, IsMinCut G S ∧ P.H.rep (P.H.canon G) S ≤ B * mincutValue G) →
      IsWeakSkeleton G ((refine hb ρ γ hγ.le hfin fuel B P).eval G.cut) ∧
      ((refine hb ρ γ hγ.le hfin fuel B P).cost G.cut : ℝ) ≤
        M * (fuel + 1) + M * ((Nat.log 2 (Fintype.card V) : ℝ) + 3) * (16 + 800 * ρ ^ 2) * B / γ := by
  set L : ℝ := (Nat.log 2 (Fintype.card V) : ℝ) + 3
  have hL : 0 ≤ L := by positivity
  have hγ100 : 100 * γ ≤ 1 := by
    have h1 : 1 ≤ a (Fintype.card V) ^ 2 * ρ ^ 2 := by
      have := one_le_mul_of_one_le_of_one_le ha hρ; nlinarith
    nlinarith
  -- the final application of Theorem 15
  have hfinal : ∀ (B : ℝ) (P : Pkg V) (hB0 : 0 < B), 1 ≤ B → γ * B < 1 → Good P → P.m ≤ M →
      (∃ S, IsMinCut G S ∧ P.H.rep (P.H.canon G) S ≤ B * mincutValue G) →
      IsWeakSkeleton G ((finalProg ρ B (hfin B hB0) P).eval G.cut) ∧
      ((finalProg ρ B (hfin B hB0) P).cost G.cut : ℝ) ≤ M * (1 + 800 * ρ ^ 2 * B / γ * L) := by
    intro B P hB0 hB hγB hP hm hprom
    have hg : P.H.GuardFor ρ := hgood P hP
    have hsk := Hier.supplied_weakSkeleton (H := P.H) G hn hρ hB hg hlam hprom
    simp only [finalProg, dite_eq_left hg]
    refine ⟨hsk.1, ?_⟩
    have hq1 : 1 ≤ finalQ ρ B := by
      unfold finalQ; exact Nat.one_le_iff_ne_zero.mpr (by positivity)
    have hx : (finalQ ρ B : ℝ) - 1 ≤ 200 * ρ ^ 2 * B / γ := by
      have h1 : (finalQ ρ B : ℝ) < 200 * ρ ^ 2 * B ^ 2 + 1 := Nat.ceil_lt_add_one (by positivity)
      have h2 : B ^ 2 ≤ B / γ := by
        rw [le_div_iff₀ hγ, sq, mul_assoc]
        have : B * γ ≤ 1 := by linarith
        nlinarith
      have h3 : 200 * ρ ^ 2 * B ^ 2 ≤ 200 * ρ ^ 2 * B / γ := by
        rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_left h2 (by positivity)
      linarith
    have := supplied_cost_real G P hg (hfin B hB0) hq1 hm hx
    calc _ ≤ _ := this
      _ = M * (1 + 800 * ρ ^ 2 * B / γ * L) := by simp only [L]; ring
  intro fuel
  induction fuel with
  | zero =>
      intro B P hB hγB hP hm hprom
      have hB0 : 0 < B := by linarith
      simp only [refine, dite_eq_left hB0]
      obtain ⟨h1, h2⟩ := hfinal B P hB0 hB (by simpa using hγB) hP hm hprom
      refine ⟨h1, h2.trans ?_⟩
      have h0 : 0 ≤ (M : ℝ) * L * (16 * B / γ) := by positivity
      have e : (M : ℝ) * (1 + 800 * ρ ^ 2 * B / γ * L) + M * L * (16 * B / γ) =
          M * 1 + M * L * (16 + 800 * ρ ^ 2) * B / γ := by ring
      push_cast
      linarith
  | succ fuel ih =>
      intro B P hB hγB hP hm hprom
      have hB0 : 0 < B := by linarith
      by_cases hsmall : γ * B < 1
      · simp only [refine, ite_eq_left hsmall, dite_eq_left hB0]
        obtain ⟨h1, h2⟩ := hfinal B P hB0 hB hsmall hP hm hprom
        refine ⟨h1, h2.trans ?_⟩
        have h0 : 0 ≤ (M : ℝ) * L * (16 * B / γ) := by positivity
        have h0' : (0 : ℝ) ≤ M * fuel := by positivity
        have e : (M : ℝ) * (1 + 800 * ρ ^ 2 * B / γ * L) + M * L * (16 * B / γ) + M * fuel =
            M * (fuel + 1) + M * L * (16 + 800 * ρ ^ 2) * B / γ := by ring
        push_cast
        linarith
      · push Not at hsmall
        have hg : P.H.GuardFor ρ := hgood P hP
        simp only [refine, ite_eq_right (not_lt.mpr hsmall), roundProg, dite_eq_left hg, eval_bind,
          cost_bind]
        set q := roundQ γ B
        set H0 := (P.H.supplied hg γ hγ.le q).eval G.cut
        have hqge : 2 * B / γ ≤ q := Nat.le_ceil _
        have hqpos : (0 : ℝ) < q := lt_of_lt_of_le (by positivity) hqge
        have hq : 1 ≤ q := by exact_mod_cast hqpos
        have hqη : 2 / (q : ℝ) ≤ γ / B := by
          rw [div_le_div_iff₀ hqpos hB0]
          rw [div_le_iff₀ hγ] at hqge; linarith
        obtain ⟨hm', -, -, hdist⟩ := hbPkg_spec hb H0
        obtain ⟨S, hS, hRS⟩ := hprom
        have hSval : G.cut S = mincutValue G :=
          le_antisymm (le_mincutValue G hn hS.2) (mincutValue_le G hS.1)
        have hnew := Hier.round_promise (H := P.H) G hρ hg ha hγ hγdef hsmall hq hqη hlam hSval
          hRS (hbPkg hb H0).H hdist
        have hB2 : 1 ≤ B / 2 := by
          have : 1 / γ ≤ B := by rw [div_le_iff₀ hγ]; linarith
          have : 100 ≤ 1 / γ := by rw [le_div_iff₀ hγ]; linarith
          linarith
        have hγB2 : γ * (B / 2) < 2 ^ fuel := by
          rw [pow_succ] at hγB; linarith
        obtain ⟨hsk, hcost⟩ := ih (B / 2) (hbPkg hb H0) hB2 hγB2 (hsel H0) (hm'.trans hM)
          ⟨S, hS, hnew⟩
        refine ⟨hsk, ?_⟩
        have hx : (q : ℝ) - 1 ≤ 2 * B / γ := by
          have : (q : ℝ) < 2 * B / γ + 1 := Nat.ceil_lt_add_one (by positivity)
          linarith
        have hround : ((P.H.supplied hg γ hγ.le q).cost G.cut : ℝ) ≤
            M * (1 + 4 * (2 * B / γ) * L) := supplied_cost_real G P hg hγ.le hq hm hx
        have hcost' : ((refine hb ρ γ hγ.le hfin fuel (B / 2) (hbPkg hb H0)).cost G.cut : ℝ) ≤
            M * (fuel + 1) + M * L * (16 + 800 * ρ ^ 2) * (B / 2) / γ := hcost
        push_cast
        have e : (M : ℝ) * (1 + 4 * (2 * B / γ) * L) +
            (M * (fuel + 1) + M * L * (16 + 800 * ρ ^ 2) * (B / 2) / γ) +
            M * L * (400 * ρ ^ 2) * B / γ =
            M * (fuel + 1 + 1) + M * L * (16 + 800 * ρ ^ 2) * B / γ := by ring
        have hpos : 0 ≤ (M : ℝ) * L * (400 * ρ ^ 2) * B / γ := by positivity
        linarith

/-- **Theorem 24 for any guard regime, packaged.** -/
theorem refine_weakSkeleton_of_good (hb : HierarchyBound a h) (G : WeightedGraph V)
    (hn : 2 ≤ Fintype.card V) (hlam : 0 < mincutValue G) {ρ γ : ℝ} (hρ : 1 ≤ ρ) (hγ : 0 < γ)
    (hγdef : 100 * a (Fintype.card V) ^ 2 * ρ ^ 2 * γ ≤ 1) (ha : 1 ≤ a (Fintype.card V))
    (Good : Pkg V → Prop) (hgood : ∀ P, Good P → P.H.GuardFor ρ)
    (hsel : ∀ J : WeightedGraph V, Good (hbPkg hb J)) {M : ℕ} (hM : 2 * Fintype.card V + 1 ≤ M)
    (hfin : ∀ B : ℝ, 0 < B → 0 ≤ 1 / (10 * ρ * B)) {B : ℝ} (hB : 1 ≤ B) (P : Pkg V)
    (hP : Good P) (hm : P.m ≤ M)
    (hprom : ∃ S, IsMinCut G S ∧ P.H.rep (P.H.canon G) S ≤ B * mincutValue G) :
    IsWeakSkeleton G ((refine hb ρ γ hγ.le hfin ⌈γ * B⌉₊ B P).eval G.cut) ∧
      ((refine hb ρ γ hγ.le hfin ⌈γ * B⌉₊ B P).cost G.cut : ℝ) ≤
        M * (⌈γ * B⌉₊ + 1) +
          M * ((Nat.log 2 (Fintype.card V) : ℝ) + 3) * (16 + 800 * ρ ^ 2) * B / γ := by
  have hlt : γ * B < 2 ^ ⌈γ * B⌉₊ := by
    calc γ * B ≤ ⌈γ * B⌉₊ := Nat.le_ceil _
      _ < 2 ^ ⌈γ * B⌉₊ := by exact_mod_cast Nat.lt_two_pow_self
  exact refine_spec_of_good hb G hn hlam hρ hγ hγdef ha Good hgood hsel hM hfin _ B P hB hlt hP hm
    hprom


/-- **Theorem 24 with the height-based star-mesh guard.** -/
theorem refine_spec (hb : HierarchyBound a h) (G : WeightedGraph V) (hn : 2 ≤ Fintype.card V)
    (hlam : 0 < mincutValue G) {ρ γ : ℝ} (hρ : 1 ≤ ρ) (hγ : 0 < γ)
    (hγdef : 100 * a (Fintype.card V) ^ 2 * ρ ^ 2 * γ ≤ 1) (ha : 1 ≤ a (Fintype.card V))
    (hρh : 2 * (h (Fintype.card V) : ℝ) ≤ ρ) {M : ℕ} (hM : 2 * Fintype.card V + 1 ≤ M)
    (hfin : ∀ B : ℝ, 0 < B → 0 ≤ 1 / (10 * ρ * B)) :
    ∀ (fuel : ℕ) (B : ℝ) (P : Pkg V), 1 ≤ B → γ * B < 2 ^ fuel → P.H.LeafChildless →
      2 * (P.H.height : ℝ) ≤ ρ → P.m ≤ M →
      (∃ S, IsMinCut G S ∧ P.H.rep (P.H.canon G) S ≤ B * mincutValue G) →
      IsWeakSkeleton G ((refine hb ρ γ hγ.le hfin fuel B P).eval G.cut) ∧
      ((refine hb ρ γ hγ.le hfin fuel B P).cost G.cut : ℝ) ≤
        M * (fuel + 1) + M * ((Nat.log 2 (Fintype.card V) : ℝ) + 3) * (16 + 800 * ρ ^ 2) * B / γ :=
  fun fuel B P hB hγB hlc hht hm hprom =>
    refine_spec_of_good hb G hn hlam hρ hγ hγdef ha
      (fun P => P.H.LeafChildless ∧ 2 * (P.H.height : ℝ) ≤ ρ)
      (fun P hP => Hier.guardFor_of_height hP.1 hP.2)
      (fun J => ⟨(hbPkg_spec hb J).2.1, by
        have : ((hbPkg hb J).H.height : ℝ) ≤ h (Fintype.card V) := by
          exact_mod_cast (hbPkg_spec hb J).2.2.1
        linarith⟩) hM hfin fuel B P hB hγB ⟨hlc, hht⟩ hm hprom

/-- **Theorem 24, packaged.** Start from any hierarchy with promise `B ≥ 1`. -/
theorem refine_weakSkeleton (hb : HierarchyBound a h) (G : WeightedGraph V)
    (hn : 2 ≤ Fintype.card V) (hlam : 0 < mincutValue G) {ρ γ : ℝ} (hρ : 1 ≤ ρ) (hγ : 0 < γ)
    (hγdef : 100 * a (Fintype.card V) ^ 2 * ρ ^ 2 * γ ≤ 1) (ha : 1 ≤ a (Fintype.card V))
    (hρh : 2 * (h (Fintype.card V) : ℝ) ≤ ρ) {M : ℕ} (hM : 2 * Fintype.card V + 1 ≤ M)
    (hfin : ∀ B : ℝ, 0 < B → 0 ≤ 1 / (10 * ρ * B)) {B : ℝ} (hB : 1 ≤ B) (P : Pkg V)
    (hlc : P.H.LeafChildless) (hht : 2 * (P.H.height : ℝ) ≤ ρ) (hm : P.m ≤ M)
    (hprom : ∃ S, IsMinCut G S ∧ P.H.rep (P.H.canon G) S ≤ B * mincutValue G) :
    IsWeakSkeleton G ((refine hb ρ γ hγ.le hfin ⌈γ * B⌉₊ B P).eval G.cut) ∧
      ((refine hb ρ γ hγ.le hfin ⌈γ * B⌉₊ B P).cost G.cut : ℝ) ≤
        M * (⌈γ * B⌉₊ + 1) +
          M * ((Nat.log 2 (Fintype.card V) : ℝ) + 3) * (16 + 800 * ρ ^ 2) * B / γ := by
  have hlt : γ * B < 2 ^ ⌈γ * B⌉₊ := by
    calc γ * B ≤ ⌈γ * B⌉₊ := Nat.le_ceil _
      _ < 2 ^ ⌈γ * B⌉₊ := by exact_mod_cast Nat.lt_two_pow_self
  exact refine_spec hb G hn hlam hρ hγ hγdef ha hρh hM hfin _ B P hB hlt hlc hht hm hprom

end Program

end Hierarchy
end CutQueryComplexity
