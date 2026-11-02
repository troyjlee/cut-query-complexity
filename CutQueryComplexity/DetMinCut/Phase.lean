import CutQueryComplexity.Hierarchy.Initial
import CutQueryComplexity.Discovery.ResidualPreparation
import CutQueryComplexity.Discovery.CenterSelection

/-! # One discovery phase (Lemmas 29–32)

On a normalized graph (`d_v ≤ (N − 1) U` for all `v`, `U > 0`), a phase

1. learns an explicit subgraph `K` by residual preparation (Lemma 29),
2. selects centers and learns their residual rows (Lemma 30),
3. rounds by a hierarchy of the explicit graph `H = K + H_C^R`, compressed to the terminals
   `C ∪ {v₀}` (eq. (H-rounding)), and learns the quotient by the resulting partition,
4. forms the auxiliary graph `J` and its minimum terminal-separating value `μ` (Lemma 31),
5. if `μ ≥ 4Nt`, reads a hierarchy of `J` on the original vertices and refines it into a
   weak skeleton (Lemma 32 and Theorem 24); otherwise queries the cut `S_J` and returns it as
   a new witness with value below `U / (4N)` (Lemma 32).

Every graph built from query answers is total: inconsistent transcripts give some valid
graph, and on the genuine oracle the graph is the intended one (`learnContract_eval`,
`centerOf_eq`, `auxOf_eq`).
-/

namespace CutQueryComplexity
namespace DetMinCut

open TwoRespecting WeightedGraph Search Search.Comp Discovery Hierarchy Finset

variable {W : Type} [Fintype W] [DecidableEq W]

/-! ## Graphs built from transcripts -/

section Builders

variable {ι : Type} [Fintype ι] [DecidableEq ι] [LinearOrder ι]

/-- Decode a contracted graph from the cuts of single parts and of ordered pairs of parts
in `img`. -/
noncomputable def decodeQ (img : Finset ι) (s : ι → Option ℝ) (pr : ι × ι → Option ℝ) : WeightedGraph ι where
  w i j := if i ∈ img ∧ j ∈ img ∧ i ≠ j then
      max 0 (((s i).getD 0 + (s j).getD 0 - (pr (min i j, max i j)).getD 0) / 2) else 0
  symm i j := by
    by_cases h : i ∈ img ∧ j ∈ img ∧ i ≠ j
    · have h' : j ∈ img ∧ i ∈ img ∧ j ≠ i := ⟨h.2.1, h.1, Ne.symm h.2.2⟩
      rw [ite_eq_left h, ite_eq_left h', min_comm j i, max_comm j i, add_comm ((s j).getD 0)]
    · have h' : ¬ (j ∈ img ∧ i ∈ img ∧ j ≠ i) := fun h' => h ⟨h'.2.1, h'.1, Ne.symm h'.2.2⟩
      rw [ite_eq_right h, ite_eq_right h']
  nonneg i j := by split <;> simp
  diag i := by simp

/-- Learn the contraction of the oracle graph along `π`, querying only parts in `img`. -/
noncomputable def learnContract (π : W → ι) (img : Finset ι) :
    Comp (Finset W) ℝ (WeightedGraph ι) :=
  (tabulate (fun i => ask (pull π {i})) img.toList).bind fun s =>
    (tabulate (fun p : ι × ι => ask (pull π {p.1, p.2}))
      (img.offDiag.filter fun p => p.1 < p.2).toList).map fun pr => decodeQ img s pr

theorem learnContract_eval (G : WeightedGraph W) (π : W → ι) {img : Finset ι}
    (himg : ∀ v, π v ∈ img) : (learnContract π img).eval G.cut = G.contract π := by
  ext i j
  simp only [learnContract, eval_bind, eval_map, eval_tabulate, eval_ask, decodeQ,
    mem_toList]
  by_cases hij : i ∈ img ∧ j ∈ img ∧ i ≠ j
  · rw [ite_eq_left hij]
    obtain ⟨hi, hj, hne⟩ := hij
    have hp : (min i j, max i j) ∈ img.offDiag.filter fun p => p.1 < p.2 := by
      simp only [mem_filter, mem_offDiag]
      refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
      · rcases min_choice i j with h | h <;> rw [h] <;> assumption
      · rcases max_choice i j with h | h <;> rw [h] <;> assumption
      · exact (min_lt_max.mpr hne).ne
      · exact min_lt_max.mpr hne
    have hpair : ({min i j, max i j} : Finset ι) = {i, j} := by
      rcases le_total i j with h | h
      · rw [min_eq_left h, max_eq_right h]
      · rw [min_eq_right h, max_eq_left h, pair_comm]
    simp only [ite_eq_left hi, ite_eq_left hj, ite_eq_left hp, Option.getD_some, hpair]
    rw [(G.contract π).edge_eq_three_cuts hne, cut_contract, cut_contract, cut_contract]
    exact max_eq_right (by
      rw [← cut_contract, ← cut_contract, ← cut_contract, ← (G.contract π).edge_eq_three_cuts hne]
      exact (G.contract π).nonneg i j)
  · rw [ite_eq_right hij]
    by_cases hne : i = j
    · subst hne; exact ((G.contract π).diag i).symm
    · have hfib : ∀ b, b ∉ img → fiber π b = ∅ := fun b hb => by
        ext v; simp only [mem_fiber, Finset.notMem_empty, iff_false]
        exact fun h => hb (by rw [← h]; exact himg v)
      simp only [contract, ite_eq_right hne]
      have : i ∉ img ∨ j ∉ img := by tauto
      rcases this with h | h
      · rw [hfib i h]; simp [cross]
      · rw [hfib j h]; simp [cross]

omit [Fintype ι] in
theorem learnContract_cost (G : WeightedGraph W) (π : W → ι) (img : Finset ι) :
    (learnContract π img).cost G.cut ≤ img.card + img.card * img.card := by
  simp only [learnContract, cost_bind, cost_map, cost_tabulate, cost_ask, List.map_const',
    List.sum_replicate, smul_eq_mul, mul_one, length_toList]
  have : (img.offDiag.filter fun p => p.1 < p.2).card ≤ img.card * img.card := by
    refine (card_filter_le _ _).trans ?_
    rw [offDiag_card]; exact Nat.sub_le _ _
  omega

end Builders

/-- The graph of center rows, symmetrized and clipped so that it is valid on every transcript. -/
noncomputable def centerOf (C : Finset W) (rows : W → W → ℝ) : WeightedGraph W where
  w a b := if a = b then 0 else if a ∈ C ∧ b ∈ C then (max 0 (rows a b) + max 0 (rows b a)) / 2
    else if a ∈ C then max 0 (rows a b) else if b ∈ C then max 0 (rows b a) else 0
  symm a b := by
    by_cases hab : a = b
    · subst hab; rfl
    · rw [ite_eq_right hab, ite_eq_right (Ne.symm hab)]
      by_cases ha : a ∈ C <;> by_cases hb : b ∈ C <;> simp [ha, hb, add_comm]
  nonneg a b := by
    split_ifs <;> first | exact le_rfl | positivity
  diag a := by simp

omit [Fintype W] in
theorem centerOf_eq (R : WeightedGraph W) {C : Finset W} {rows : W → W → ℝ}
    (hrows : ∀ c ∈ C, ∀ x, rows c x = R.w c x) : centerOf C rows = centerGraph R C := by
  ext a b
  simp only [centerOf, centerGraph]
  by_cases hab : a = b
  · subst hab; simp [R.diag]
  rw [ite_eq_right hab]
  by_cases ha : a ∈ C <;> by_cases hb : b ∈ C
  · simp only [ha, hb, and_self, ite_true, or_self, hrows a ha, hrows b hb, R.symm b a,
      max_eq_right (R.nonneg a b)]
    ring
  · simp [ha, hb, hrows a ha, max_eq_right (R.nonneg a b)]
  · simp [ha, hb, hrows b hb, R.symm b a, max_eq_right (R.nonneg a b)]
  · simp [ha, hb]

section Aux

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The auxiliary graph from a learned quotient `Q`, the explicit graph `K`, and residual
degrees `r` (clipped at zero). -/
noncomputable def auxOf (Q : WeightedGraph ι) (K : WeightedGraph W) (r : W → ℝ) (π : W → ι) :
    WeightedGraph (W ⊕ ι) where
  w
    | .inl a, .inl b => K.w a b
    | .inr i, .inr j => Q.w i j
    | .inl a, .inr i => if π a = i then max 0 (r a) else 0
    | .inr i, .inl a => if π a = i then max 0 (r a) else 0
  symm x y := by
    rcases x with a | i <;> rcases y with b | j
    · exact K.symm a b
    · rfl
    · rfl
    · exact Q.symm i j
  nonneg x y := by
    rcases x with a | i <;> rcases y with b | j
    · exact K.nonneg a b
    · dsimp only; split <;> simp
    · dsimp only; split <;> simp
    · exact Q.nonneg i j
  diag x := by
    rcases x with a | i
    · exact K.diag a
    · exact Q.diag i

omit [DecidableEq W] in
theorem degree_subtract (G K : WeightedGraph W) (hKG : ∀ u v, K.w u v ≤ G.w u v) (a : W) :
    (G.subtract K).degree a = G.degree a - K.degree a := by
  simp only [degree, subtract, max_eq_right (sub_nonneg.mpr (hKG _ _)), sum_sub_distrib]

omit [Fintype ι] in
theorem auxOf_eq (G K : WeightedGraph W) (hKG : ∀ u v, K.w u v ≤ G.w u v) (π : W → ι) :
    auxOf (G.contract π) K (fun a => G.degree a - K.degree a) π = auxGraph G K π := by
  have hr : ∀ a, max 0 (G.degree a - K.degree a) = (G.subtract K).degree a := fun a => by
    rw [degree_subtract G K hKG, max_eq_right]
    rw [← degree_subtract G K hKG]
    exact sum_nonneg fun _ _ => (G.subtract K).nonneg _ _
  ext x y
  rcases x with a | i <;> rcases y with b | j <;> simp [auxOf, auxGraph, hr]

end Aux

/-! ## The minimum terminal-separating cut of an explicit auxiliary graph -/

section Psi

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Minimum terminal-extension cut of an explicit graph on `W ⊕ ι`. -/
noncomputable def psiOf (J : WeightedGraph (W ⊕ ι)) (S : Finset W) : ℝ :=
  (univ : Finset (Finset ι)).inf' univ_nonempty fun T => J.cut (S.disjSum T)

open Classical in
/-- A proper shore minimizing `psiOf`, chosen offline (`∅` if there is none). -/
noncomputable def bestShore (J : WeightedGraph (W ⊕ ι)) : Finset W :=
  if h : (properShores W).Nonempty then
    Classical.choose (exists_mem_eq_inf' h (psiOf J)) else ∅

theorem bestShore_spec (J : WeightedGraph (W ⊕ ι)) (h : (properShores W).Nonempty) :
    ProperShore (bestShore J) ∧ ∀ S, ProperShore S → psiOf J (bestShore J) ≤ psiOf J S := by
  classical
  have hs := Classical.choose_spec (exists_mem_eq_inf' h (psiOf J))
  simp only [bestShore, dite_eq_left h]
  refine ⟨(mem_properShores _).mp hs.1, fun S hS => ?_⟩
  rw [← hs.2]
  exact inf'_le _ ((mem_properShores S).mpr hS)

theorem psiOf_auxGraph (G K : WeightedGraph W) (π : W → ι) (S : Finset W) :
    psiOf (auxGraph G K π) S = psi G K π S := by
  rw [psi_eq_auxGraph]; rfl

end Psi

/-! ## The phase program -/

section Phase

variable {a : ℕ → ℝ} {h : ℕ → ℕ}

/-- The residual-degree floor `t = U / (16 N²)`. -/
noncomputable def floorT (N : ℕ) (U : ℝ) : ℝ := U / (16 * (N : ℝ) ^ 2)

/-- The scan bound of residual preparation. -/
def prepS (N : ℕ) : ℕ := 4 + 3 * Nat.clog 2 N

/-- Guard quality covering every hierarchy used in a phase on `N` vertices. -/
noncomputable def rhoOf (h : ℕ → ℕ) (N : ℕ) : ℝ := max 1 (2 * (h (3 * N + 1) : ℝ))

/-- The refinement guard weight `γ = 1 / (100 a(N)² ρ²)` for a guard quality `ρ = ρf N`. -/
noncomputable def gammaR (a : ℕ → ℝ) (ρf : ℕ → ℝ) (N : ℕ) : ℝ :=
  1 / (100 * a N ^ 2 * ρf N ^ 2)

/-- The refinement guard weight for the height-based guard. -/
noncomputable def gammaOf (a : ℕ → ℝ) (h : ℕ → ℕ) (N : ℕ) : ℝ := gammaR a (rhoOf h) N

/-- The promise `B = 2 β A` with `β = a(N + m)` and `A = (1 + a(N))(2k + 1)`. -/
noncomputable def promiseB (a : ℕ → ℝ) (N m k : ℕ) : ℝ :=
  2 * a (N + m) * ((1 + a N) * (2 * k + 1))

theorem one_le_rhoOf (h : ℕ → ℕ) (N : ℕ) : 1 ≤ rhoOf h N := le_max_left _ _

theorem rhoOf_pos (h : ℕ → ℕ) (N : ℕ) : 0 < rhoOf h N := lt_of_lt_of_le one_pos (one_le_rhoOf h N)

theorem gammaR_pos (ha : ∀ r, 1 ≤ a r) {ρf : ℕ → ℝ} (hρf : ∀ N, 1 ≤ ρf N) (N : ℕ) :
    0 < gammaR a ρf N := by
  have := ha N; have : 0 < ρf N := lt_of_lt_of_le one_pos (hρf N)
  unfold gammaR; positivity

theorem gammaOf_pos (ha : ∀ r, 1 ≤ a r) (h : ℕ → ℕ) (N : ℕ) : 0 < gammaOf a h N :=
  gammaR_pos ha (one_le_rhoOf h) N

theorem hfinR {ρf : ℕ → ℝ} (hρf : ∀ N, 1 ≤ ρf N) (N : ℕ) :
    ∀ B : ℝ, 0 < B → 0 ≤ 1 / (10 * ρf N * B) :=
  fun B hB => by have : 0 < ρf N := lt_of_lt_of_le one_pos (hρf N); positivity

theorem hfin_of_rho (h : ℕ → ℕ) (N : ℕ) : ∀ B : ℝ, 0 < B → 0 ≤ 1 / (10 * rhoOf h N * B) :=
  fun B hB => by have := rhoOf_pos h N; positivity

/-- The outcome of a phase. -/
inductive PhaseOut (W : Type)
  | skel (H : WeightedGraph W)
  | halve (S : Finset W) (val : ℝ)

/-- What a phase guarantees on the genuine oracle. -/
def PhaseOK (G : WeightedGraph W) (U : ℝ) : PhaseOut W → Prop
  | .skel H => IsWeakSkeleton G H
  | .halve S val => ProperShore S ∧ val = G.cut S ∧ val < U / (4 * Fintype.card W)

/-- **One phase, with guard quality `ρf N`.** `d` are the known degrees, `U` the witnessed
bound, `k` the center parameter, and `v₀` an extra terminal. -/
noncomputable def phaseG (hb : HierarchyBound a h) (ha : ∀ r, 1 ≤ a r) (ρf : ℕ → ℝ)
    (hρf : ∀ N, 1 ≤ ρf N) (d : W → ℝ) (U : ℝ) (k : ℕ) (v0 : W) :
    Comp (Finset W) ℝ (PhaseOut W) :=
  (residualPrep d (floorT (Fintype.card W) U) k (prepS (Fintype.card W))).bind fun K =>
  (centerSelection d K (floorT (Fintype.card W) U) k).bind fun cs =>
  let Hx := K.add (centerOf cs.C cs.rows)
  let P := hbPkg hb Hx
  let πp := P.H.part (P.H.canon Hx) (fun _ => Hx.cut_nonneg _) (cs.C ∪ {v0})
  (learnContract πp (univ.image πp)).bind fun Q =>
  let J := auxOf Q K (fun x => d x - K.degree x) πp
  if 4 * Fintype.card W * floorT (Fintype.card W) U ≤ psiOf J (bestShore J) then
    let PJ := hbPkg hb J
    let γ := gammaR a ρf (Fintype.card W)
    let B := promiseB a (Fintype.card W) P.m k
    (refine hb (ρf (Fintype.card W)) γ (gammaR_pos ha hρf _).le
      (hfinR hρf (Fintype.card W)) ⌈γ * B⌉₊ B ⟨PJ.m, PJ.H.restrictInl⟩).map PhaseOut.skel
  else (ask (bestShore J)).map (PhaseOut.halve (bestShore J))

/-- **One phase** with the height-based guard. -/
noncomputable def phase (hb : HierarchyBound a h) (ha : ∀ r, 1 ≤ a r) (d : W → ℝ) (U : ℝ)
    (k : ℕ) (v0 : W) : Comp (Finset W) ℝ (PhaseOut W) :=
  phaseG hb ha (rhoOf h) (one_le_rhoOf h) d U k v0

/-- The certification branch of a phase (Lemma 32 with Theorem 24), for any guard quality. -/
theorem certify_branchG (hb : HierarchyBound a h) (ha : ∀ r, 1 ≤ a r) {ρf : ℕ → ℝ}
    (hρf : ∀ N, 1 ≤ ρf N) {cap : ℕ} (hcapN : h (Fintype.card W) ≤ cap)
    (hguard : ∀ P : Pkg W, P.H.LeafChildless → P.H.height ≤ cap →
      P.H.GuardFor (ρf (Fintype.card W)))
    (G : WeightedGraph W) (hN : 2 ≤ Fintype.card W) {K : WeightedGraph W}
    (hKG : ∀ u v, K.w u v ≤ G.w u v) {m : ℕ} (π : W → Fin m)
    (hm : m ≤ 2 * Fintype.card W + 1) (hcapm : h (Fintype.card W + m) ≤ cap)
    {k : ℕ} {e : ℝ} (he : 0 < e)
    (hup : ∀ S, psi G K π S ≤ (1 + a (Fintype.card W)) * (2 * k + 1) * G.cut S + e)
    (hμ : 2 * e ≤ psiOf (auxGraph G K π) (bestShore (auxGraph G K π))) :
    let PJ := hbPkg hb (auxGraph G K π)
    let γ := gammaR a ρf (Fintype.card W)
    let B := promiseB a (Fintype.card W) m k
    let R := refine hb (ρf (Fintype.card W)) γ (gammaR_pos ha hρf _).le
      (hfinR hρf (Fintype.card W)) ⌈γ * B⌉₊ B ⟨PJ.m, PJ.H.restrictInl⟩
    IsWeakSkeleton G (R.eval G.cut) ∧
      (R.cost G.cut : ℝ) ≤ (6 * Fintype.card W + 3) * (⌈γ * B⌉₊ + 1) +
        (6 * Fintype.card W + 3) * ((Nat.log 2 (Fintype.card W) : ℝ) + 3) *
          (16 + 800 * ρf (Fintype.card W) ^ 2) * B / γ := by
  intro PJ γ B R
  set N := Fintype.card W
  set J := auxGraph G K π
  have hne : (properShores W).Nonempty := by
    obtain ⟨v⟩ := Fintype.card_pos_iff.mp (show 0 < N by omega)
    exact ⟨{v}, (mem_properShores _).mpr (properShore_singleton v hN)⟩
  obtain ⟨-, hbest⟩ := bestShore_spec J hne
  have hμS : ∀ S, ProperShore S → 2 * e ≤ psi G K π S := fun S hS => by
    rw [← psiOf_auxGraph]; exact hμ.trans (hbest S hS)
  -- the minimum cut is positive
  obtain ⟨Smin, hSmin⟩ : ∃ S, IsMinCut G S := by
    obtain ⟨S, hS, heq⟩ := exists_mem_eq_inf' hne G.cut
    exact ⟨S, (mem_properShores _).mp hS, fun T hT => by
      rw [← heq]; exact inf'_le _ ((mem_properShores _).mpr hT)⟩
  have hSval : G.cut Smin = mincutValue G :=
    le_antisymm (le_mincutValue G hN hSmin.2) (mincutValue_le G hSmin.1)
  have hA : 1 ≤ (1 + a N) * (2 * k + 1) := by
    have := ha N; nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hlam : 0 < mincutValue G := by
    have h1 := hup Smin; have h2 := hμS Smin hSmin.1
    rw [hSval] at h1
    by_contra hneg; push Not at hneg
    have : (1 + a N) * (2 * k + 1) * mincutValue G ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) hneg
    linarith
  -- the hierarchy of `J`
  obtain ⟨hmJ, hlcJ, hhtJ, hdistJ⟩ := hbPkg_spec hb J
  have hcardJ : Fintype.card (W ⊕ Fin m) = N + m := by simp [N]
  rw [hcardJ] at hhtJ hdistJ
  have hmJ' : PJ.m ≤ 2 * (N + m) + 1 := by simpa [hcardJ] using hmJ
  have hprom := Hier.restrictInl_promise G K hKG π PJ.H (by linarith [ha (N + m)]) hdistJ hup
    hμS hSmin
  have hρ := hρf N
  have hγ := gammaR_pos ha hρf N
  have hB : 1 ≤ B := by
    have := ha (N + m); simp only [B, promiseB]; nlinarith
  have hγdef : 100 * a N ^ 2 * ρf N ^ 2 * γ ≤ 1 := by
    have : 0 < 100 * a N ^ 2 * ρf N ^ 2 := by have := ha N; positivity
    simp only [γ, gammaR]; rw [mul_one_div_cancel this.ne']
  have hrefine := refine_weakSkeleton_of_good hb G hN hlam hρ hγ hγdef (ha N)
    (fun P => P.H.LeafChildless ∧ P.H.height ≤ cap) (fun P hP => hguard P hP.1 hP.2)
    (fun J => ⟨(hbPkg_spec hb J).2.1, (hbPkg_spec hb J).2.2.1.trans hcapN⟩)
    (M := 6 * N + 3) (by omega) (hfinR hρf N) hB ⟨PJ.m, PJ.H.restrictInl⟩
    ⟨Hier.restrictInl_leafChildless hlcJ, by rw [Hier.restrictInl_height]; exact hhtJ.trans hcapm⟩
    (show PJ.m ≤ 6 * N + 3 by omega)
    ⟨Smin, hSmin, by
      have := hprom
      calc _ ≤ 2 * a (N + m) * ((1 + a N) * (2 * k + 1)) * mincutValue G := by linarith
        _ = B * mincutValue G := rfl⟩
  refine ⟨hrefine.1, hrefine.2.trans (le_of_eq ?_)⟩
  push_cast; ring

/-- The certification branch of a phase (Lemma 32 with Theorem 24). -/
theorem certify_branch (hb : HierarchyBound a h) (ha : ∀ r, 1 ≤ a r) (hh : Monotone h)
    (G : WeightedGraph W) (hN : 2 ≤ Fintype.card W) {K : WeightedGraph W}
    (hKG : ∀ u v, K.w u v ≤ G.w u v) {m : ℕ} (π : W → Fin m) (hm : m ≤ 2 * Fintype.card W + 1)
    {k : ℕ} {e : ℝ} (he : 0 < e)
    (hup : ∀ S, psi G K π S ≤ (1 + a (Fintype.card W)) * (2 * k + 1) * G.cut S + e)
    (hμ : 2 * e ≤ psiOf (auxGraph G K π) (bestShore (auxGraph G K π))) :
    let PJ := hbPkg hb (auxGraph G K π)
    let γ := gammaOf a h (Fintype.card W)
    let B := promiseB a (Fintype.card W) m k
    let R := refine hb (rhoOf h (Fintype.card W)) γ (gammaOf_pos ha h _).le
      (hfin_of_rho h (Fintype.card W)) ⌈γ * B⌉₊ B ⟨PJ.m, PJ.H.restrictInl⟩
    IsWeakSkeleton G (R.eval G.cut) ∧
      (R.cost G.cut : ℝ) ≤ (6 * Fintype.card W + 3) * (⌈γ * B⌉₊ + 1) +
        (6 * Fintype.card W + 3) * ((Nat.log 2 (Fintype.card W) : ℝ) + 3) *
          (16 + 800 * rhoOf h (Fintype.card W) ^ 2) * B / γ :=
  certify_branchG hb ha (one_le_rhoOf h) (cap := h (3 * Fintype.card W + 1)) (hh (by omega))
    (fun P hlc hht => Hier.guardFor_of_height hlc (by
      have : (P.H.height : ℝ) ≤ h (3 * Fintype.card W + 1) := by exact_mod_cast hht
      exact (by linarith : 2 * (P.H.height : ℝ) ≤ 2 * (h (3 * Fintype.card W + 1) : ℝ)).trans
        (le_max_right _ _)))
    G hN hKG π hm (hh (by omega)) he hup hμ

/-- The query bound of a phase on `N` vertices with parameter `k` and guard quality `ρf N`. -/
noncomputable def phaseBoundR (a : ℕ → ℝ) (ρf : ℕ → ℝ) (N k : ℕ) : ℝ :=
  let p := 2 * (selectionBudget N k + 1)
  let Bs := 2 * a (3 * N + 1) * ((1 + a N) * (2 * k + 1))
  let γ := gammaR a ρf N
  (N * prepS N * (4 * k * Nat.clog 2 (N - 1)) +
      selectionBudget N k * (6 * (6 + 3 * Nat.clog 2 N) * (Nat.clog 2 N + 1) + (N - 1)) +
      (p + p * p) : ℕ) +
    ((6 * N + 3) * (γ * Bs + 2) +
      (6 * N + 3) * ((Nat.log 2 N : ℝ) + 3) * (16 + 800 * ρf N ^ 2) * Bs / γ + 1)

/-- The query bound of a phase with the height-based guard. -/
noncomputable def phaseBound (a : ℕ → ℝ) (h : ℕ → ℕ) (N k : ℕ) : ℝ := phaseBoundR a (rhoOf h) N k

/-- **One phase (Lemmas 29–32), for any guard quality.** On a normalized graph a phase either
returns a weak skeleton or a proper shore whose cut is below `U / (4N)`, within `phaseBoundR`. -/
theorem phase_specG (hb : HierarchyBound a h) (ha : ∀ r, 1 ≤ a r) (hma : Monotone a)
    {ρf : ℕ → ℝ} (hρf : ∀ N, 1 ≤ ρf N) {cap : ℕ} (hcapN : h (Fintype.card W) ≤ cap)
    (hcapm : ∀ m ≤ 2 * Fintype.card W + 1, h (Fintype.card W + m) ≤ cap)
    (hguard : ∀ P : Pkg W, P.H.LeafChildless → P.H.height ≤ cap →
      P.H.GuardFor (ρf (Fintype.card W)))
    (G : WeightedGraph W) (hN : 3 ≤ Fintype.card W) {U : ℝ} (hU : 0 < U)
    (hdeg : ∀ v, G.degree v ≤ ((Fintype.card W : ℝ) - 1) * U) {k : ℕ} (hk2 : 2 ≤ k)
    (hkN : k ≤ 8 * Fintype.card W) (v0 : W) :
    PhaseOK G U ((phaseG hb ha ρf hρf G.degree U k v0).eval G.cut) ∧
      ((phaseG hb ha ρf hρf G.degree U k v0).cost G.cut : ℝ) ≤
        phaseBoundR a ρf (Fintype.card W) k := by
  have : Nonempty W := ⟨v0⟩
  have hk0 : 0 < k := by omega
  obtain ⟨hKex, hlight, hKcost⟩ := residualPrep_normalized G hU hk0 hdeg
  simp only [phaseG, floorT, prepS, eval_bind, cost_bind]
  set N := Fintype.card W with hNdef
  set t := U / (16 * (N : ℝ) ^ 2) with htdef
  set K := (residualPrep G.degree t k (4 + 3 * Nat.clog 2 N)).eval G.cut with hKdef
  have hKG : ∀ u v, K.w u v ≤ G.w u v := fun u v => by
    rcases hKex u v with h0 | h0 <;> rw [h0]; exact G.nonneg u v
  obtain ⟨hCcard, hrows, hcov, hCcost⟩ := centerSelection_normalized G K hKG hU hk2 hkN hdeg hlight
  simp only [← hNdef] at hCcard hrows hcov hCcost
  simp only [← htdef] at hCcard hrows hcov hCcost
  set cs := (centerSelection G.degree K t k).eval G.cut with hcsdef
  set Hx := K.add (centerOf cs.C cs.rows) with hHxdef
  have hHx : Hx = K.add (centerGraph (G.subtract K) cs.C) := by rw [hHxdef, centerOf_eq _ hrows]
  obtain ⟨hPm, -, -, hPdist⟩ := hbPkg_spec hb Hx
  simp only [← hNdef] at hPm hPdist
  set P := hbPkg hb Hx with hPdef
  set C0 := cs.C ∪ {v0} with hC0
  set πp := P.H.part (P.H.canon Hx) (fun _ => Hx.cut_nonneg _) C0 with hπp
  have hQ := learnContract_eval G πp (img := univ.image πp)
    (fun v => mem_image_of_mem _ (mem_univ v))
  set Q := (learnContract πp (univ.image πp)).eval G.cut with hQdef
  have hJ : auxOf Q K (fun x => G.degree x - K.degree x) πp = auxGraph G K πp := by
    rw [hQ]; exact auxOf_eq G K hKG πp
  have ht0 : 0 ≤ t := by positivity
  have hup : ∀ S, psi G K πp S ≤ (1 + a N) * (2 * k + 1) * G.cut S + 2 * N * t := by
    intro S
    obtain ⟨T, hagree, hround0⟩ := Hier.exists_rounding P.H Hx hPdist C0 S
    have hround1 : Hx.cut (pull πp T) ≤ a N * Hx.cut S := hround0
    have hround : (K.add (centerGraph (G.subtract K) cs.C)).cut (pull πp T) ≤
        a N * (K.add (centerGraph (G.subtract K) cs.C)).cut S := by
      rw [← hHx]; exact hround1
    have hagree' : pull πp T ∩ cs.C = S ∩ cs.C := by
      have hsub : cs.C ⊆ C0 := subset_union_left
      calc pull πp T ∩ cs.C = (pull πp T ∩ C0) ∩ cs.C := by rw [inter_assoc, inter_eq_right.mpr hsub]
        _ = (S ∩ C0) ∩ cs.C := by rw [hagree]
        _ = S ∩ cs.C := by rw [inter_assoc, inter_eq_right.mpr hsub]
    have hα : 0 ≤ a N := by linarith [ha N]
    have hcov' : ∀ v ∉ cs.C, (G.subtract K).degree v ≤ t ∨
        (G.subtract K).degree v / k ≤ ∑ c ∈ cs.C, (G.subtract K).w v c := hcov
    have := psi_upper (ι := Fin P.m) G K hKG πp (C := cs.C) (S := S) (T := T) hagree' (t := t)
      ht0 (k := k) hk0 hcov' (α := a N) hα hround
    exact this
  rw [hJ]
  simp only [← hNdef, ← htdef]
  -- the query cost before the test
  have hne : (properShores W).Nonempty := by
    exact ⟨{v0}, (mem_properShores _).mpr (properShore_singleton v0 (by omega))⟩
  have himg : (univ.image πp).card ≤ 2 * (selectionBudget N k + 1) := by
    have h1 := Hier.card_image_part_le P.H (P.H.canon Hx) (fun _ => Hx.cut_nonneg _) C0
    have h2 : C0.card ≤ cs.C.card + 1 := (card_union_le _ _).trans (by simp)
    have h3 : max 1 (2 * C0.card - 2) ≤ 2 * (selectionBudget N k + 1) :=
      max_le (by omega) (by omega)
    exact h1.trans h3
  have hlearn := learnContract_cost G πp (univ.image πp)
  set nb : ℕ := N * prepS N * (4 * k * Nat.clog 2 (N - 1)) +
      selectionBudget N k * (6 * (6 + 3 * Nat.clog 2 N) * (Nat.clog 2 N + 1) + (N - 1)) +
      (2 * (selectionBudget N k + 1) + 2 * (selectionBudget N k + 1) *
        (2 * (selectionBudget N k + 1))) with hnb
  have hpre : (residualPrep G.degree t k (4 + 3 * Nat.clog 2 N)).cost G.cut +
      ((centerSelection G.degree K t k).cost G.cut +
        (learnContract πp (univ.image πp)).cost G.cut) ≤ nb := by
    have := Nat.mul_le_mul himg himg
    simp only [hnb, prepS]
    omega
  have hpreR : ((residualPrep G.degree t k (4 + 3 * Nat.clog 2 N)).cost G.cut : ℝ) +
      ((centerSelection G.degree K t k).cost G.cut +
        (learnContract πp (univ.image πp)).cost G.cut) ≤ (nb : ℝ) := by
    exact_mod_cast hpre
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have h4Nt : 4 * (N : ℝ) * t = U / (4 * N) := by
    simp only [htdef]; field_simp; ring
  set Bs := 2 * a (3 * N + 1) * ((1 + a N) * (2 * k + 1)) with hBs
  set γ := gammaR a ρf N with hγdef
  have hγ := gammaR_pos ha hρf N
  have hρ := hρf N
  have hcertpos : (0 : ℝ) ≤ (6 * N + 3) * (γ * Bs + 2) +
      (6 * N + 3) * ((Nat.log 2 N : ℝ) + 3) * (16 + 800 * ρf N ^ 2) * Bs / γ := by
    have := ha (3 * N + 1); have := ha N; positivity
  by_cases hc : 4 * (N : ℝ) * t ≤ psiOf (auxGraph G K πp) (bestShore (auxGraph G K πp))
  · rw [ite_eq_left hc]
    simp only [eval_map, cost_map, PhaseOK]
    have he : (0 : ℝ) < 2 * N * t := by positivity
    obtain ⟨hsk, hcost⟩ := certify_branchG hb ha hρf hcapN hguard G (by omega) hKG πp hPm
      (hcapm _ hPm) (k := k) he hup
      (by linarith)
    refine ⟨hsk, ?_⟩
    -- the refinement cost is at most the certification part of `phaseBound`
    have hBle : promiseB a N P.m k ≤ Bs := by
      simp only [promiseB, hBs]
      have hm3 : N + P.m ≤ 3 * N + 1 := by omega
      have := hma hm3
      have hA : 0 ≤ (1 + a N) * (2 * k + 1) := by have := ha N; positivity
      nlinarith
    have hB0 : 0 ≤ promiseB a N P.m k := by
      have := ha (N + P.m); have := ha N; simp only [promiseB]; positivity
    have hceil : (⌈γ * promiseB a N P.m k⌉₊ : ℝ) + 1 ≤ γ * Bs + 2 := by
      have := Nat.ceil_lt_add_one (show 0 ≤ γ * promiseB a N P.m k by positivity)
      have := mul_le_mul_of_nonneg_left hBle hγ.le
      linarith
    have hL : (0 : ℝ) ≤ ((Nat.log 2 N : ℝ) + 3) * (16 + 800 * ρf N ^ 2) := by positivity
    have hterm : (6 * (N : ℝ) + 3) * ((Nat.log 2 N : ℝ) + 3) * (16 + 800 * ρf N ^ 2) *
        promiseB a N P.m k / γ ≤
        (6 * N + 3) * ((Nat.log 2 N : ℝ) + 3) * (16 + 800 * ρf N ^ 2) * Bs / γ := by
      apply div_le_div_of_nonneg_right _ hγ.le
      exact mul_le_mul_of_nonneg_left hBle (by positivity)
    have hfirst : (6 * (N : ℝ) + 3) * ((⌈γ * promiseB a N P.m k⌉₊ : ℝ) + 1) ≤
        (6 * N + 3) * (γ * Bs + 2) := mul_le_mul_of_nonneg_left hceil (by positivity)
    have hpb : phaseBoundR a ρf N k = (nb : ℝ) + ((6 * N + 3) * (γ * Bs + 2) +
        (6 * N + 3) * ((Nat.log 2 N : ℝ) + 3) * (16 + 800 * ρf N ^ 2) * Bs / γ + 1) := rfl
    rw [hpb]
    push_cast
    linarith
  · rw [ite_eq_right hc]
    simp only [eval_map, cost_map, eval_ask, cost_ask, PhaseOK]
    obtain ⟨hprop, -⟩ := bestShore_spec (auxGraph G K πp) hne
    refine ⟨⟨hprop, by simp, ?_⟩, ?_⟩
    · push Not at hc
      have h1 := psi_lower G K hKG πp (bestShore (auxGraph G K πp))
      rw [← psiOf_auxGraph] at h1
      rw [← h4Nt]; exact lt_of_le_of_lt h1 hc
    · have hpb : phaseBoundR a ρf N k = (nb : ℝ) + ((6 * N + 3) * (γ * Bs + 2) +
          (6 * N + 3) * ((Nat.log 2 N : ℝ) + 3) * (16 + 800 * ρf N ^ 2) * Bs / γ + 1) := rfl
      rw [hpb]
      push_cast
      linarith

/-- **One phase (Lemmas 29–32).** On a normalized graph a phase either returns a weak
skeleton or a proper shore whose cut is below `U / (4N)`, within `phaseBound`. -/
theorem phase_spec (hb : HierarchyBound a h) (ha : ∀ r, 1 ≤ a r) (hma : Monotone a)
    (hh : Monotone h) (G : WeightedGraph W) (hN : 3 ≤ Fintype.card W) {U : ℝ} (hU : 0 < U)
    (hdeg : ∀ v, G.degree v ≤ ((Fintype.card W : ℝ) - 1) * U) {k : ℕ} (hk2 : 2 ≤ k)
    (hkN : k ≤ 8 * Fintype.card W) (v0 : W) :
    PhaseOK G U ((phase hb ha G.degree U k v0).eval G.cut) ∧
      ((phase hb ha G.degree U k v0).cost G.cut : ℝ) ≤ phaseBound a h (Fintype.card W) k :=
  phase_specG hb ha hma (one_le_rhoOf h) (cap := h (3 * Fintype.card W + 1)) (hh (by omega))
    (fun m hm => hh (by omega))
    (fun P hlc hht => Hier.guardFor_of_height hlc (by
      have : (P.H.height : ℝ) ≤ h (3 * Fintype.card W + 1) := by exact_mod_cast hht
      exact (by linarith : 2 * (P.H.height : ℝ) ≤ 2 * (h (3 * Fintype.card W + 1) : ℝ)).trans
        (le_max_right _ _)))
    G hN hU hdeg hk2 hkN v0

end Phase

end DetMinCut
end CutQueryComplexity
