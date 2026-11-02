import CutQueryComplexity.BoundedFlowMinCut.Incidence
import CutQueryComplexity.Primitive.HeavySearch
import CutQueryComplexity.Primitive.CrossSearch
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! # A dominating set and the small-cut separation lemma (M2)

**Separation.** In a unit graph of minimum degree at least `δ`, every proper
shore `S` of cut value below `δ` meets every dominating set `R`, and so does its
complement. If `S` missed `R`, each vertex of `S` would have a neighbour in
`R ⊆ Sᶜ`, so `cut S ≥ |S|`; and each vertex of `S` has at least `δ + 1 - |S|`
neighbours outside `S`, so `cut S ≥ |S| (δ + 1 - |S|)`. For `1 ≤ |S| ≤ δ - 1` the
second bound is at least `δ`. (This is Lemma 5.3 of Anand–Saranurak–Wang, as
used by Kenneth-Mordoch, Lemma 2.2.)

**Construction.** A greedy covering, implemented directly (in place of
ASW Theorem 5.4). The undominated vertices `U` start as all of `V`. Each round
searches for a vertex `v` whose closed-neighbourhood score
`w_U(v) = [v ∈ U] + Σ_{u ∈ U} G.w v u` is at least its average, which is at
least `(δ+1)|U|/n`; the subset sums of `w_U` come from the incidence oracle
(seven queries) and the public count `|A ∩ U|`. The neighbours of `v` in `U`
are then enumerated one by one, and `v` joins `R` while its closed
neighbourhood leaves `U`.

On a unit graph each round removes `w_U(v) ≥ (δ+1)|U|/n` vertices, so the
potential `Φ(a) = (n/(δ+1)) log a + 1` drops by one per round, and
`(δ+1)|R| ≤ n log n + δ + 1`. Each round costs at most a constant times
`L` per removed vertex, so the whole construction costs `O(n L)` queries.
-/

set_option autoImplicit false

namespace CutQueryComplexity.BoundedFlowMinCut
noncomputable section
open scoped Classical
open WeightedGraph GHReduction

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ### Separation -/

/-- Every vertex is in `R` or adjacent to `R`. -/
def Dominates (G : WeightedGraph V) (R : Finset V) : Prop :=
  ∀ v, v ∈ R ∨ ∃ r ∈ R, 0 < G.w v r

/-- A shore whose vertices all have a neighbour outside it cuts at least its size. -/
theorem card_le_cut_of_missing {G : WeightedGraph V} (hG : AllPairsAudit.Unweighted G)
    {R S : Finset V} (hR : Dominates G R) (hSR : Disjoint S R) : (S.card : ℝ) ≤ G.cut S := by
  rw [WeightedGraph.cut, Finset.card_eq_sum_ones, Nat.cast_sum]
  apply Finset.sum_le_sum
  intro v hv
  rcases hR v with h | ⟨r, hr, hvr⟩
  · exact absurd h (Finset.disjoint_left.mp hSR hv)
  · have hrS : r ∈ Sᶜ := Finset.mem_compl.mpr (Finset.disjoint_right.mp hSR hr)
    have h1 : G.w v r = 1 := by rcases hG v r with h | h <;> simp_all
    calc
      ((1 : ℕ) : ℝ) = G.w v r := by simp [h1]
      _ ≤ _ := Finset.single_le_sum (fun u _ => G.nonneg v u) hrS

/-- Every vertex of `S` has at least `δ + 1 - |S|` neighbours outside `S`. -/
theorem card_mul_le_cut {G : WeightedGraph V} (hG : AllPairsAudit.Unweighted G) {δ : ℕ}
    (hδ : ∀ v, δ ≤ natDegree G v) (S : Finset V) :
    (S.card : ℝ) * ((δ : ℝ) + 1 - S.card) ≤ G.cut S := by
  rw [WeightedGraph.cut, ← nsmul_eq_mul, ← Finset.sum_const]
  apply Finset.sum_le_sum
  intro v hv
  rw [unit_sum_eq_card hG]
  have hsplit : (nbrs G v ∩ Sᶜ).card + (nbrs G v ∩ S).card = natDegree G v := by
    rw [← Finset.sdiff_eq_inter_compl, add_comm, Finset.card_inter_add_card_sdiff]
    rfl
  have hin : (nbrs G v ∩ S).card + 1 ≤ S.card := by
    have : nbrs G v ∩ S ⊆ S.erase v := fun u hu => Finset.mem_erase.mpr
      ⟨fun he => not_mem_nbrs_self G v (he ▸ (Finset.mem_inter.mp hu).1),
        (Finset.mem_inter.mp hu).2⟩
    have hc := Finset.card_le_card this
    rw [Finset.card_erase_of_mem hv] at hc
    have := Finset.card_pos.mpr ⟨v, hv⟩
    omega
  have := hδ v
  have hreal : ((nbrs G v ∩ Sᶜ).card : ℝ) + (nbrs G v ∩ S).card = natDegree G v := by
    exact_mod_cast hsplit
  have hreal2 : ((nbrs G v ∩ S).card : ℝ) + 1 ≤ S.card := by exact_mod_cast hin
  have hreal3 : (δ : ℝ) ≤ natDegree G v := by exact_mod_cast this
  linarith

/-- A side of a cut of value below `δ` contains a vertex of every dominating set. -/
theorem meets_dominating_of_cut_lt {G : WeightedGraph V} (hG : AllPairsAudit.Unweighted G)
    {δ : ℕ} (hδ : ∀ v, δ ≤ natDegree G v) {R S : Finset V} (hR : Dominates G R)
    (hS : S.Nonempty) (hcut : G.cut S < δ) : (S ∩ R).Nonempty := by
  by_contra hne
  have hdisj : Disjoint S R := Finset.disjoint_iff_inter_eq_empty.mpr
    (Finset.not_nonempty_iff_eq_empty.mp hne)
  have h1 := card_le_cut_of_missing hG hR hdisj
  have h2 := card_mul_le_cut hG hδ S
  have hk : (1 : ℝ) ≤ S.card := by exact_mod_cast Finset.card_pos.mpr hS
  have hkδ : (S.card : ℝ) ≤ δ - 1 := by
    have hlt : (S.card : ℝ) < δ := lt_of_le_of_lt h1 hcut
    have : S.card < δ := by exact_mod_cast hlt
    have : S.card ≤ δ - 1 := by omega
    have hδ1 : 1 ≤ δ := by omega
    calc (S.card : ℝ) ≤ ((δ - 1 : ℕ) : ℝ) := by exact_mod_cast this
      _ = δ - 1 := by push_cast [Nat.cast_sub hδ1]; ring
  nlinarith

/-- **Separation lemma.** A proper shore of cut value below the minimum degree
meets every dominating set on both sides. -/
theorem small_cut_meets_dominating (G : WeightedGraph V) (hG : AllPairsAudit.Unweighted G)
    {δ : ℕ} (hδ : ∀ v, δ ≤ natDegree G v) {R : Finset V} (hR : Dominates G R)
    {S : Finset V} (hS : ProperShore S) (hcut : G.cut S < δ) :
    (S ∩ R).Nonempty ∧ (Sᶜ ∩ R).Nonempty := by
  refine ⟨meets_dominating_of_cut_lt hG hδ hR hS.1 hcut, ?_⟩
  have hc : Sᶜ.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    exact hS.2 (by simpa using congrArg (·ᶜ) h)
  exact meets_dominating_of_cut_lt hG hδ hR hc (by rwa [G.cut_compl])

/-! ### Enumerating neighbours -/

/-- Enumerate the neighbours of `v` in `T`, one logarithmic search each. -/
def enumNeighbors (v : V) : (fuel : ℕ) → Finset V → Prog (Finset V) ℝ (Finset V)
  | 0, _ => .pure ∅
  | fuel + 1, T => (liftDTree (findNeighbor (searchDepth V) v T)).bind fun o => match o with
      | none => .pure ∅
      | some u => (enumNeighbors v fuel (T.erase u)).map (insert u)

theorem enumNeighbors_spec (G : WeightedGraph V) (v : V)
    (fuel : ℕ) (T : Finset V) (hfuel : (nbrs G v ∩ T).card < fuel) :
    Prog.eval G.cut (enumNeighbors v fuel T) = nbrs G v ∩ T ∧
      Prog.cost G.cut (enumNeighbors v fuel T) ≤
        ((nbrs G v ∩ T).card + 1) * (3 * (searchDepth V + 1)) := by
  induction fuel generalizing T with
  | zero => omega
  | succ fuel ih =>
      have hres := findNeighbor_correct G (searchDepth V) v T
        (card_le_pow_searchDepth Finset.univ)
      have hcost := liftDTree_cost_le (findNeighbor (searchDepth V) v T) G.cut
      cases ho : (findNeighbor (searchDepth V) v T).eval G.cut with
      | none =>
          rw [ho] at hres
          have hempty : nbrs G v ∩ T = ∅ := by
            ext u
            simp only [Finset.mem_inter, mem_nbrs, Finset.notMem_empty, iff_false, not_and]
            intro hpos huT
            have := hres u (Finset.mem_univ u)
            simp [restrictWeight, huT] at this
            linarith
          simp only [enumNeighbors, Prog.eval_bind, Prog.cost_bind, liftDTree_eval, ho,
            Prog.eval_pure, Prog.cost_pure, hempty]
          refine ⟨by simp, ?_⟩
          simp only [Finset.card_empty, zero_add, one_mul, add_zero]
          exact hcost.trans (by ring_nf; omega)
      | some u =>
          rw [ho] at hres
          obtain ⟨-, hu⟩ := hres
          have hu' := (restrictWeight_pos _ T u).mp hu
          have hmem : u ∈ nbrs G v ∩ T := Finset.mem_inter.mpr ⟨(mem_nbrs G v u).mpr hu'.2, hu'.1⟩
          have herase : nbrs G v ∩ T.erase u = (nbrs G v ∩ T).erase u := by
            ext x
            simp only [Finset.mem_inter, Finset.mem_erase]
            tauto
          have hcard : (nbrs G v ∩ T.erase u).card + 1 = (nbrs G v ∩ T).card := by
            rw [herase, Finset.card_erase_of_mem hmem]
            have := Finset.card_pos.mpr ⟨u, hmem⟩
            omega
          obtain ⟨heval, hcost'⟩ := ih (T.erase u) (by omega)
          simp only [enumNeighbors, Prog.eval_bind, Prog.cost_bind, liftDTree_eval, ho,
            Prog.eval_map, Prog.cost_map, heval]
          refine ⟨by rw [herase, Finset.insert_erase hmem], ?_⟩
          calc
            _ ≤ 3 * (searchDepth V + 1) +
                ((nbrs G v ∩ T.erase u).card + 1) * (3 * (searchDepth V + 1)) := by
              omega
            _ = _ := by rw [← hcard]; ring

/-! ### One greedy round -/

/-- The closed-neighbourhood score of `v` against the undominated set `U`. -/
def closedScore (G : WeightedGraph V) (U : Finset V) (v : V) : ℝ :=
  (if v ∈ U then 1 else 0) + ∑ u ∈ U, G.w v u

/-- The vertices of `U` dominated by `v`. -/
def closedNbhd (G : WeightedGraph V) (v : V) (U : Finset V) : Finset V :=
  if v ∈ U then insert v (nbrs G v ∩ U) else nbrs G v ∩ U

/-- Subset sums of the score: the incidence oracle plus a public count. -/
def scoreQuery (deg : V → ℕ) (U A : Finset V) : DTree (Finset V) ℝ ℝ 7 :=
  (incidenceTree 0 (fun v => (deg v : ℝ)) U A).map (fun x => x + ((A ∩ U).card : ℝ))

/-- The average score, computed from the cached degrees. -/
def roundTarget (deg : V → ℕ) (U : Finset V) : ℝ :=
  ((U.card : ℝ) + ∑ u ∈ U, (deg u : ℝ)) / Fintype.card V

/-- Search a vertex whose score is at least the average. -/
def centerTree (deg : V → ℕ) (U : Finset V) :
    DTree (Finset V) ℝ (Option V) (searchDepth V * 7) :=
  (searchAverage (searchDepth V) Finset.univ (roundTarget deg U)).substitute (scoreQuery deg U)

/-- One round: a centre and the undominated vertices it dominates. -/
def domRound (deg : V → ℕ) (U : Finset V) : Prog (Finset V) ℝ (Option (V × Finset V)) :=
  (liftDTree (centerTree deg U)).bind fun o => match o with
    | none => .pure none
    | some v => (enumNeighbors v (Fintype.card V) U).map
        (fun N => some (v, if v ∈ U then insert v N else N))

omit [Fintype V] [DecidableEq V] in
theorem subtract_zero_w (G : WeightedGraph V) (u v : V) : (G.subtract 0).w u v = G.w u v := by
  simp [subtract, G.nonneg]

theorem scoreQuery_eval (G : WeightedGraph V) {deg : V → ℕ}
    (hdeg : ∀ v, (deg v : ℝ) = G.degree v) (U A : Finset V) :
    (scoreQuery deg U A).eval G.cut = subsetSum (closedScore G U) A := by
  rw [scoreQuery, DTree.eval_map, incidenceTree_eval G 0 (fun u v => G.nonneg u v) _ hdeg]
  simp only [subtract_zero_w, subsetSum, closedScore, Finset.sum_add_distrib, Finset.sum_ite_mem,
    Finset.sum_const, nsmul_eq_mul, mul_one]
  ring

theorem sum_closedScore {G : WeightedGraph V} (hG : AllPairsAudit.Unweighted G) (U : Finset V) :
    subsetSum (closedScore G U) Finset.univ = (U.card : ℝ) + ∑ u ∈ U, (natDegree G u : ℝ) := by
  simp only [subsetSum, closedScore, Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.univ_inter,
    Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro u _
  rw [← degree_eq_natDegree hG]
  exact Finset.sum_congr rfl (fun v _ => G.symm v u)

theorem closedScore_eq_card {G : WeightedGraph V} (hG : AllPairsAudit.Unweighted G)
    (U : Finset V) (v : V) : closedScore G U v = (closedNbhd G v U).card := by
  rw [closedScore, unit_sum_eq_card hG, closedNbhd]
  by_cases hv : v ∈ U
  · have hn : v ∉ nbrs G v ∩ U := fun h => not_mem_nbrs_self G v (Finset.mem_inter.mp h).1
    simp [hv, Finset.card_insert_of_notMem hn, add_comm]
  · simp [hv]

theorem closedNbhd_subset (G : WeightedGraph V) (v : V) (U : Finset V) : closedNbhd G v U ⊆ U := by
  unfold closedNbhd
  split
  · exact Finset.insert_subset (by assumption) Finset.inter_subset_right
  · exact Finset.inter_subset_right

/-- On a unit graph with the true degrees, a round returns a centre `v` of score at
least the average, and exactly the vertices of `U` it dominates. -/
theorem domRound_spec {G : WeightedGraph V} (hG : AllPairsAudit.Unweighted G) {deg : V → ℕ}
    (hdeg : ∀ v, deg v = natDegree G v) {U : Finset V} (hU : U.Nonempty) :
    ∃ v, Prog.eval G.cut (domRound deg U) = some (v, closedNbhd G v U) ∧
      roundTarget deg U ≤ (closedNbhd G v U).card ∧
      Prog.cost G.cut (domRound deg U) ≤
        searchDepth V * 7 + ((nbrs G v ∩ U).card + 1) * (3 * (searchDepth V + 1)) := by
  have hdegR : ∀ v, (deg v : ℝ) = G.degree v := fun v => by
    rw [hdeg, degree_eq_natDegree hG]
  have : Nonempty V := ⟨hU.choose⟩
  have hn : 0 < Fintype.card V := Fintype.card_pos
  have hav : roundTarget deg U * (Finset.univ : Finset V).card ≤
      subsetSum (closedScore G U) Finset.univ := by
    rw [sum_closedScore hG, roundTarget, Finset.card_univ, div_mul_cancel₀ _ (by positivity)]
    simp only [hdeg, le_refl]
  obtain ⟨v, hv, -, hscore⟩ := searchAverage_correct (closedScore G U) (searchDepth V)
    Finset.univ (roundTarget deg U) (card_le_pow_searchDepth _) Finset.univ_nonempty hav
  have hcenter : (centerTree deg U).eval G.cut = some v := by
    rw [centerTree, DTree.eval_substitute]
    have hread : (fun A => (scoreQuery deg U A).eval G.cut) = subsetSum (closedScore G U) :=
      funext (scoreQuery_eval G hdegR U)
    rw [hread, hv]
  obtain ⟨henum, hcost⟩ := enumNeighbors_spec G v (Fintype.card V) U
    (lt_of_le_of_lt (Finset.card_le_card Finset.inter_subset_left)
      (lt_of_le_of_lt (natDegree_le G v) (by omega)))
  refine ⟨v, ?_, by rw [← closedScore_eq_card hG]; exact hscore, ?_⟩
  · simp only [domRound, Prog.eval_bind, liftDTree_eval, hcenter, Prog.eval_map, henum,
      closedNbhd]
  · simp only [domRound, Prog.cost_bind, liftDTree_eval, hcenter, Prog.cost_map]
    have := liftDTree_cost_le (centerTree deg U) G.cut
    omega

/-! ### The greedy loop -/

/-- Rounds until every vertex is dominated, within public fuel. -/
def domLoop (deg : V → ℕ) : (fuel : ℕ) → Finset V → Finset V → Prog (Finset V) ℝ (Finset V)
  | 0, R, _ => .pure R
  | fuel + 1, R, U =>
      if U = ∅ then .pure R else
        (domRound deg U).bind fun o => match o with
          | none => .pure R
          | some (v, N) => domLoop deg fuel (insert v R) (U \ N)

/-- The dominating-set program, on the cached degree vector. -/
def dominatingProg (deg : V → ℕ) : Prog (Finset V) ℝ (Finset V) :=
  domLoop deg (Fintype.card V) ∅ Finset.univ

/-- The potential `Φ(a) = (n/d) log a + 1`, with `Φ(0) = 0`. -/
def domPotential (n d a : ℕ) : ℝ := if a = 0 then 0 else (n : ℝ) / d * Real.log a + 1

theorem domPotential_nonneg (n d a : ℕ) : 0 ≤ domPotential n d a := by
  unfold domPotential
  split
  · exact le_rfl
  · have : 0 ≤ Real.log a := Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr ‹_›)
    positivity

/-- One round that keeps at most a `1 - d/n` fraction lowers the potential by one. -/
theorem domPotential_step {n d a a' : ℕ} (hd : 0 < d) (ha : 0 < a)
    (h : (n : ℝ) * a' ≤ ((n : ℝ) - d) * a) :
    domPotential n d a' + 1 ≤ domPotential n d a := by
  have hloga : 0 ≤ Real.log a := Real.log_nonneg (by exact_mod_cast ha)
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  unfold domPotential
  rw [ite_eq_right_iff.mpr (fun h => absurd h (by omega : a ≠ 0))]
  split_ifs with ha'
  · have : 0 ≤ (n : ℝ) / d * Real.log a := by positivity
    linarith
  · have ha'R : (1 : ℝ) ≤ a' := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr ha'
    have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha
    have hnpos : (0 : ℝ) < n := by
      by_contra hn
      have hn0 : (n : ℝ) = 0 := le_antisymm (not_lt.mp hn) (Nat.cast_nonneg n)
      rw [hn0] at h
      nlinarith
    have hfrac : (a' : ℝ) ≤ a * (1 - d / n) := by
      rw [show (a : ℝ) * (1 - d / n) = ((n : ℝ) - d) * a / n by field_simp,
        le_div_iff₀ hnpos]
      linarith
    have hpos : 0 < 1 - (d : ℝ) / n := by
      by_contra hc
      have : (a : ℝ) * (1 - d / n) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) (not_lt.mp hc)
      linarith
    have hlog : Real.log a' ≤ Real.log a - d / n := by
      have h1 := Real.log_le_log (by linarith) hfrac
      rw [Real.log_mul (by linarith) hpos.ne'] at h1
      have h2 := Real.log_le_sub_one_of_pos hpos
      linarith
    have hkey : (1 : ℝ) ≤ n / d * (Real.log a - Real.log a') := by
      calc (1 : ℝ) = n / d * (d / n) := by field_simp
        _ ≤ n / d * (Real.log a - Real.log a') := by
          apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    nlinarith

/-- The per-round query charge, per dominated vertex. -/
def roundCharge (V : Type) [Fintype V] : ℕ := 7 * searchDepth V + 6 * (searchDepth V + 1)

theorem domLoop_spec {G : WeightedGraph V} (hG : AllPairsAudit.Unweighted G) {deg : V → ℕ}
    (hdeg : ∀ v, deg v = natDegree G v) {δ : ℕ} (hδ : ∀ v, δ ≤ natDegree G v)
    (fuel : ℕ) (R U : Finset V) (hfuel : U.card ≤ fuel)
    (hdom : ∀ v, v ∉ U → v ∈ R ∨ ∃ r ∈ R, 0 < G.w v r) :
    Dominates G (Prog.eval G.cut (domLoop deg fuel R U)) ∧
      ((Prog.eval G.cut (domLoop deg fuel R U)).card : ℝ) ≤
        R.card + domPotential (Fintype.card V) (δ + 1) U.card ∧
      Prog.cost G.cut (domLoop deg fuel R U) ≤ roundCharge V * U.card := by
  induction fuel generalizing R U with
  | zero =>
      have hU : U = ∅ := Finset.card_eq_zero.mp (by omega)
      subst hU
      refine ⟨fun v => hdom v (Finset.notMem_empty v), ?_, by simp [domLoop]⟩
      simp [domLoop, domPotential]
  | succ fuel ih =>
      by_cases hU : U = ∅
      · subst hU
        refine ⟨fun v => hdom v (Finset.notMem_empty v), ?_, by simp [domLoop]⟩
        simp [domLoop, domPotential]
      · have hne : U.Nonempty := Finset.nonempty_iff_ne_empty.mpr hU
        obtain ⟨v, hround, htarget, hcost⟩ := domRound_spec hG hdeg hne
        set N := closedNbhd G v U
        have hNU : N ⊆ U := closedNbhd_subset G v U
        have hn : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨hne.choose⟩
        -- the round removes at least `(δ+1)|U|/n` vertices
        have hlower : ((δ + 1 : ℕ) : ℝ) * U.card ≤ (Fintype.card V : ℝ) * N.card := by
          have h1 : ((δ + 1 : ℕ) : ℝ) * U.card ≤ (U.card : ℝ) + ∑ u ∈ U, (deg u : ℝ) := by
            have : ∑ u ∈ U, (δ : ℝ) ≤ ∑ u ∈ U, (deg u : ℝ) :=
              Finset.sum_le_sum (fun u _ => by rw [hdeg]; exact_mod_cast hδ u)
            simp only [Finset.sum_const, nsmul_eq_mul] at this
            push_cast
            linarith
          have h2 : (U.card : ℝ) + ∑ u ∈ U, (deg u : ℝ) ≤ Fintype.card V * N.card := by
            unfold roundTarget at htarget
            have := (div_le_iff₀ (by exact_mod_cast hn : (0 : ℝ) < Fintype.card V)).mp htarget
            linarith
          linarith
        have hNpos : 0 < N.card := by
          by_contra h0
          have h0' : (N.card : ℝ) = 0 := by exact_mod_cast Nat.eq_zero_of_not_pos h0
          rw [h0', mul_zero] at hlower
          have : (0 : ℝ) < ((δ + 1 : ℕ) : ℝ) * U.card := by
            have := Finset.card_pos.mpr hne
            positivity
          linarith
        have hcard' : (U \ N).card + N.card = U.card := Finset.card_sdiff_add_card_eq_card hNU
        obtain ⟨hD, hC, hK⟩ := ih (insert v R) (U \ N) (by omega) (by
          intro x hx
          by_cases hxU : x ∈ U
          · have hxN : x ∈ N := by
              by_contra h
              exact hx (Finset.mem_sdiff.mpr ⟨hxU, h⟩)
            simp only [N, closedNbhd] at hxN
            split_ifs at hxN with hvU
            · rcases Finset.mem_insert.mp hxN with h | h
              · exact Or.inl (h ▸ Finset.mem_insert_self v R)
              · exact Or.inr ⟨v, Finset.mem_insert_self v R,
                  by rw [G.symm]; exact (mem_nbrs G v x).mp (Finset.mem_inter.mp h).1⟩
            · exact Or.inr ⟨v, Finset.mem_insert_self v R,
                by rw [G.symm]; exact (mem_nbrs G v x).mp (Finset.mem_inter.mp hxN).1⟩
          · rcases hdom x hxU with h | ⟨r, hr, hxr⟩
            · exact Or.inl (Finset.mem_insert_of_mem h)
            · exact Or.inr ⟨r, Finset.mem_insert_of_mem hr, hxr⟩)
        have heval : Prog.eval G.cut (domLoop deg (fuel + 1) R U) =
            Prog.eval G.cut (domLoop deg fuel (insert v R) (U \ N)) := by
          simp only [domLoop, hU, ite_false, Prog.eval_bind, hround]
        have hcostEq : Prog.cost G.cut (domLoop deg (fuel + 1) R U) =
            Prog.cost G.cut (domRound deg U) +
              Prog.cost G.cut (domLoop deg fuel (insert v R) (U \ N)) := by
          simp only [domLoop, hU, ite_false, Prog.cost_bind, hround]
        refine ⟨heval ▸ hD, ?_, ?_⟩
        · rw [heval]
          have hstep := domPotential_step (n := Fintype.card V) (d := δ + 1) (a := U.card)
            (a' := (U \ N).card) (by omega) (Finset.card_pos.mpr hne) (by
              have : ((U \ N).card : ℝ) = U.card - N.card := by
                rw [← hcard']; push_cast; ring
              rw [this]
              push_cast at hlower ⊢
              nlinarith)
          have hins : ((insert v R).card : ℝ) ≤ R.card + 1 := by
            exact_mod_cast Finset.card_insert_le v R
          linarith
        · rw [hcostEq]
          have hnb : (nbrs G v ∩ U).card ≤ N.card := by
            apply Finset.card_le_card
            simp only [N, closedNbhd]
            split
            · exact Finset.subset_insert _ _
            · exact le_rfl
          have hround' : Prog.cost G.cut (domRound deg U) ≤ roundCharge V * N.card := by
            unfold roundCharge
            calc
              _ ≤ searchDepth V * 7 + ((nbrs G v ∩ U).card + 1) * (3 * (searchDepth V + 1)) := hcost
              _ ≤ 7 * searchDepth V * N.card + (2 * N.card) * (3 * (searchDepth V + 1)) := by
                have h1 : searchDepth V * 7 ≤ 7 * searchDepth V * N.card := by
                  nlinarith
                have h2 : (nbrs G v ∩ U).card + 1 ≤ 2 * N.card := by omega
                have h3 := Nat.mul_le_mul_right (3 * (searchDepth V + 1)) h2
                omega
              _ = _ := by ring
          calc
            _ ≤ roundCharge V * N.card + roundCharge V * (U \ N).card := Nat.add_le_add hround' hK
            _ = _ := by rw [← Nat.mul_add, add_comm, hcard']

theorem real_log_le_clog (n : ℕ) : Real.log n ≤ Nat.clog 2 n := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h
    simp
  · have hp : (n : ℝ) ≤ (2 : ℝ) ^ Nat.clog 2 n := by
      exact_mod_cast Nat.le_pow_clog (by norm_num : 1 < (2 : ℕ)) n
    have hl := Real.log_le_log (Nat.cast_pos.mpr h) hp
    rw [Real.log_pow] at hl
    have htwo : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    nlinarith [Nat.cast_nonneg (α := ℝ) (Nat.clog 2 n)]

/-- **The dominating set.** On a unit graph, given its true degrees, the program
returns a dominating set `R` with `(δ + 1) |R| ≤ n L(n)` whenever every degree is at
least `δ`, using at most `13 n L(n)` queries. -/
theorem dominating_correct (G : WeightedGraph V) (hG : AllPairsAudit.Unweighted G)
    (deg : V → ℕ) (hdeg : ∀ v, deg v = natDegree G v) {δ : ℕ} (hδ : ∀ v, δ ≤ natDegree G v) :
    Dominates G (Prog.eval G.cut (dominatingProg deg)) ∧
      (δ + 1) * (Prog.eval G.cut (dominatingProg deg)).card ≤
        Fintype.card V * logFactor (Fintype.card V) ∧
      Prog.cost G.cut (dominatingProg deg) ≤ 13 * Fintype.card V * logFactor (Fintype.card V) := by
  obtain ⟨hD, hC, hK⟩ := domLoop_spec hG hdeg hδ (Fintype.card V) ∅ Finset.univ
    (by simp) (fun v hv => absurd (Finset.mem_univ v) hv)
  unfold dominatingProg
  refine ⟨hD, ?_, ?_⟩
  · set R := Prog.eval G.cut (domLoop deg (Fintype.card V) ∅ Finset.univ)
    rcases Nat.eq_zero_or_pos (Fintype.card V) with hn | hn
    · have : R.card = 0 := by
        have := Finset.card_le_univ R
        omega
      simp [this]
    · have hδn : δ + 1 ≤ Fintype.card V := by
        obtain ⟨v⟩ := Fintype.card_pos_iff.mp hn
        have := (hδ v).trans (natDegree_le G v)
        omega
      have hlog := real_log_le_clog (Fintype.card V)
      have hL := clog_add_one_le_logFactor (Fintype.card V)
      simp only [Finset.card_empty, Nat.cast_zero, zero_add, Finset.card_univ, domPotential,
        Nat.pos_iff_ne_zero.mp hn, ite_false] at hC
      have hδpos : (0 : ℝ) < ((δ + 1 : ℕ) : ℝ) := by positivity
      have hmul : ((δ + 1 : ℕ) : ℝ) * R.card ≤
          (Fintype.card V : ℝ) * Real.log (Fintype.card V) + (δ + 1 : ℕ) := by
        have h := mul_le_mul_of_nonneg_left hC hδpos.le
        calc _ ≤ _ := h
          _ = _ := by field_simp
      have hreal : (((δ + 1) * R.card : ℕ) : ℝ) ≤
          ((Fintype.card V * logFactor (Fintype.card V) : ℕ) : ℝ) := by
        push_cast
        have hnR : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
        have hLR : ((Nat.clog 2 (Fintype.card V) : ℕ) : ℝ) + 1 ≤ logFactor (Fintype.card V) := by
          exact_mod_cast hL
        have hδnR : ((δ + 1 : ℕ) : ℝ) ≤ Fintype.card V := by exact_mod_cast hδn
        push_cast at hmul hδnR
        nlinarith
      exact_mod_cast hreal
  · calc
      _ ≤ roundCharge V * (Finset.univ : Finset V).card := hK
      _ ≤ 13 * Fintype.card V * logFactor (Fintype.card V) := by
        rw [Finset.card_univ]
        have hL := searchDepth_add_one_le_logFactor (V := V)
        unfold roundCharge
        nlinarith

end
end CutQueryComplexity.BoundedFlowMinCut
