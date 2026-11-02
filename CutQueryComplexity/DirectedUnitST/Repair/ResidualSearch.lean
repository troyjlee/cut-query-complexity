import CutQueryComplexity.DirectedUnitST.Repair.Basic
import CutQueryComplexity.DirectedCertificate.Basic
import CutQueryComplexity.Model.Prog
import CutQueryComplexity.Discovery.Normalization

/-! # Outgoing-cut programs for residual stars

The programs take only public sets and learned constants.  Unknown pairs are
pure in the public direction; learned pairs (including splits and reverse
residual arcs) are accounted for explicitly.  These are actual `Prog`
programs against the original outgoing-cut oracle.
-/

set_option autoImplicit false

namespace CutQueryComplexity.DirectedUnitST.Repair

open Finset Certificate DirectedCertificate Prog
open scoped Classical

noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V]

/-- A symmetrized partial star after the singleton value has been learned.
The empty star makes no oracle call. -/
def starProg (v : V) (singletonValue : ℝ) (A : Finset V) : Prog (Finset V) ℝ ℝ :=
  if A.erase v = ∅ then .pure 0 else
    (Prog.ask (A.erase v)).bind fun a =>
    (Prog.ask (insert v A)).bind fun b =>
    .pure (singletonValue + a - b)

theorem starProg_eval (G : WeightedDiGraph V) (v : V) (A : Finset V) :
    (starProg v (G.out {v}) A).eval G.out = G.symStar v A := by
  unfold starProg
  split_ifs with h
  · simp only [Prog.eval_pure]
    have hstar : G.symStar v A = G.symStar v (A.erase v) := by
      unfold WeightedDiGraph.symStar
      symm
      apply sum_subset (erase_subset v A)
      intro w hw hw'
      have : w = v := by simpa [hw] using hw'
      subst w
      simp [WeightedDiGraph.sym_w, G.diag]
    rw [hstar, h]
    simp [WeightedDiGraph.symStar]
  · simp only [Prog.eval_bind, Prog.eval_ask, Prog.eval_pure]
    exact (G.symStar_eq_erase v A).symm

omit [Fintype V] in
theorem starProg_cost (read : Finset V → ℝ) (v : V) (singletonValue : ℝ)
    (A : Finset V) : (starProg v singletonValue A).cost read ≤ 2 := by
  unfold starProg
  split_ifs <;> simp

omit [Fintype V] in
@[simp] theorem starProg_empty (v : V) (singletonValue : ℝ) :
    starProg v singletonValue ∅ = (.pure 0 : Prog (Finset V) ℝ ℝ) := by
  simp [starProg]

/-- Search only unknown pairs whose public direction points out of `v`.
All eligible known residual capacities are summed without queries. -/
def residualStarProg (v : V) (singletonValue : ℝ) (eligible known outward : Finset V)
    (knownResidual : V → ℝ) : Prog (Finset V) ℝ ℝ :=
  (starProg v singletonValue ((eligible \ known) ∩ outward)).map fun unknownMass =>
    (∑ w ∈ eligible ∩ known, knownResidual w) + unknownMass

/-- The representation premise is pointwise capacity data, not a search or
query-complexity assumption.  Unknown reverse directions have zero capacity. -/
theorem residualStarProg_eval (G : WeightedDiGraph V) (v : V)
    (eligible known outward : Finset V) (knownResidual residualCap : V → ℝ)
    (hknown : ∀ w ∈ eligible ∩ known, residualCap w = knownResidual w)
    (hunknown : ∀ w ∈ eligible \ known,
      residualCap w = if w ∈ outward then G.sym.w v w else 0) :
    (residualStarProg v (G.out {v}) eligible known outward knownResidual).eval G.out =
      ∑ w ∈ eligible, residualCap w := by
  simp only [residualStarProg, Prog.eval_map, starProg_eval, WeightedDiGraph.symStar]
  rw [← sum_inter_add_sum_sdiff eligible known]
  congr 1
  · exact sum_congr rfl fun w hw => (hknown w hw).symm
  · rw [← filter_mem_eq_inter, sum_filter]
    exact sum_congr rfl fun w hw => (hunknown w hw).symm

omit [Fintype V] in
theorem residualStarProg_cost (read : Finset V → ℝ) (v : V) (singletonValue : ℝ)
    (eligible known outward : Finset V) (knownResidual : V → ℝ) :
    (residualStarProg v singletonValue eligible known outward knownResidual).cost read ≤ 2 := by
  simp only [residualStarProg, Prog.cost_map]
  exact starProg_cost read v singletonValue _

/-- Binary search for a positive pair in a public candidate list of known
mass.  The singleton case already knows the pair capacity from that mass. -/
def findPositiveProg (v : V) (singletonValue : ℝ) (W : List V) (mass : ℝ) :
    Prog (Finset V) ℝ (Option V) :=
  if mass ≤ 0 then .pure none else
  if W.length ≤ 1 then .pure W.head? else
    (starProg v singletonValue (W.take (W.length / 2)).toFinset).bind fun a =>
      if 0 < a then findPositiveProg v singletonValue (W.take (W.length / 2)) a
      else findPositiveProg v singletonValue (W.drop (W.length / 2)) (mass - a)
termination_by W.length
decreasing_by all_goals simp only [List.length_take, List.length_drop]; omega

omit [Fintype V] in
/-- A public worst-case logarithmic query cap, valid even for arbitrary
oracle answers. -/
theorem findPositiveProg_cost (read : Finset V → ℝ) (v : V) (singletonValue : ℝ) :
    ∀ (n : ℕ) (W : List V) (mass : ℝ), W.length ≤ n →
      (findPositiveProg v singletonValue W mass).cost read ≤ 2 * Nat.clog 2 W.length := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro W mass hn
    rw [findPositiveProg]
    split_ifs with hm hW
    · simp
    · simp
    · simp only [Prog.cost_bind]
      have hleft : (W.take (W.length / 2)).length < n := by simp; omega
      have hright : (W.drop (W.length / 2)).length < n := by simp; omega
      have hleftLog := Discovery.clog_half_succ_le (L := W.length)
        (l := (W.take (W.length / 2)).length) (by omega) (by simp; omega)
      have hrightLog := Discovery.clog_half_succ_le (L := W.length)
        (l := (W.drop (W.length / 2)).length) (by omega) (by simp; omega)
      have hc := starProg_cost read v singletonValue (W.take (W.length / 2)).toFinset
      split_ifs
      · have h := ih _ hleft (W.take (W.length / 2))
          ((starProg v singletonValue (W.take (W.length / 2)).toFinset).eval read) le_rfl
        omega
      · have h := ih _ hright (W.drop (W.length / 2))
          (mass - (starProg v singletonValue (W.take (W.length / 2)).toFinset).eval read) le_rfl
        omega

/-- Every positive-mass invocation actually returns a positive-capacity
pair from the eligible public list. -/
theorem findPositiveProg_spec (G : WeightedDiGraph V) (v : V) :
    ∀ (n : ℕ) (W : List V) (mass : ℝ), W.length ≤ n → W.Nodup →
      mass = G.symStar v W.toFinset → 0 < mass →
      ∃ w ∈ W, 0 < G.sym.w v w ∧
        (findPositiveProg v (G.out {v}) W mass).eval G.out = some w := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro W mass hn hnd hmass hpos
    rw [findPositiveProg]
    simp only [not_le.mpr hpos, ↓reduceIte]
    by_cases hW : W.length ≤ 1
    · simp only [hW, ↓reduceIte, Prog.eval_pure]
      cases W with
      | nil => simp [WeightedDiGraph.symStar] at hmass; linarith
      | cons w W =>
        have hnil : W = [] := by
          apply List.eq_nil_of_length_eq_zero
          have hlen : (w :: W).length = W.length + 1 := rfl
          omega
        subst W
        simp only [List.toFinset_cons, List.toFinset_nil, insert_empty_eq,
          WeightedDiGraph.symStar, sum_singleton] at hmass
        exact ⟨w, by simp, by linarith, rfl⟩
    · simp only [hW, ↓reduceIte, Prog.eval_bind, starProg_eval]
      let W₁ := W.take (W.length / 2)
      let W₂ := W.drop (W.length / 2)
      have hsplit : W = W₁ ++ W₂ := (List.take_append_drop _ _).symm
      have hnd' := hsplit ▸ hnd
      rw [List.nodup_append] at hnd'
      have hdisj : Disjoint W₁.toFinset W₂.toFinset :=
        List.disjoint_toFinset_iff_disjoint.mpr fun a h₁ h₂ => hnd'.2.2 a h₁ a h₂ rfl
      have hmass₂ : mass - G.symStar v W₁.toFinset = G.symStar v W₂.toFinset := by
        rw [hmass, hsplit, List.toFinset_append, WeightedDiGraph.symStar,
          sum_union hdisj]
        unfold WeightedDiGraph.symStar
        ring
      by_cases ha : 0 < G.symStar v W₁.toFinset
      · dsimp [W₁] at ha
        simp only [ha, ↓reduceIte]
        obtain ⟨w, hw, hp, he⟩ := ih W₁.length (by dsimp [W₁]; simp; omega)
          W₁ _ le_rfl hnd'.1 rfl ha
        exact ⟨w, List.mem_of_mem_take hw, hp, he⟩
      · dsimp [W₁] at ha
        simp only [ha, ↓reduceIte]
        have hpos₂ : 0 < mass - G.symStar v W₁.toFinset := by linarith
        obtain ⟨w, hw, hp, he⟩ := ih W₂.length (by dsimp [W₂]; simp; omega)
          W₂ _ le_rfl hnd'.2.1 hmass₂ hpos₂
        exact ⟨w, List.mem_of_mem_drop hw, hp, he⟩

/-- Learn a positive pair and its full capacity.  This uses the original
outgoing-cut oracle throughout. -/
def discoverPairProg (v : V) (singletonValue : ℝ) (W : List V) (mass : ℝ) :
    Prog (Finset V) ℝ (Option (V × ℝ)) :=
  (findPositiveProg v singletonValue W mass).bind fun result =>
    match result with
    | none => .pure none
    | some w => (starProg v singletonValue {w}).map fun capacity => some (w, capacity)

omit [Fintype V] in
theorem discoverPairProg_cost (read : Finset V → ℝ) (v : V) (singletonValue : ℝ)
    (W : List V) (mass : ℝ) :
    (discoverPairProg v singletonValue W mass).cost read ≤ 2 * Nat.clog 2 W.length + 2 := by
  have hfind := findPositiveProg_cost read v singletonValue W.length W mass le_rfl
  simp only [discoverPairProg, Prog.cost_bind]
  cases h : (findPositiveProg v singletonValue W mass).eval read with
  | none => simp only [Prog.cost_pure]; omega
  | some w =>
    simp only [Prog.cost_map]
    have hstar := starProg_cost read v singletonValue {w}
    omega

theorem discoverPairProg_spec (G : WeightedDiGraph V) (v : V) (W : List V)
    (hW : W.Nodup) (mass : ℝ) (hmass : mass = G.symStar v W.toFinset) (hpos : 0 < mass) :
    ∃ w ∈ W, 0 < G.sym.w v w ∧
      (discoverPairProg v (G.out {v}) W mass).eval G.out = some (w, G.sym.w v w) := by
  obtain ⟨w, hw, hp, he⟩ := findPositiveProg_spec G v W.length W mass le_rfl hW hmass hpos
  refine ⟨w, hw, hp, ?_⟩
  simp only [discoverPairProg, Prog.eval_bind, he, Prog.eval_map, starProg_eval,
    WeightedDiGraph.symStar, sum_singleton]

omit [Fintype V] in
theorem discoverPairProg_cost_of_nonpositive (read : Finset V → ℝ) (v : V)
    (singletonValue : ℝ) (W : List V) (mass : ℝ) (hm : mass ≤ 0) :
    (discoverPairProg v singletonValue W mass).cost read = 0 := by
  simp [discoverPairProg, findPositiveProg, hm]

/-- Find a positive residual neighbor. Known positive entries are selected
offline from public data; otherwise query only eligible unknown forward
pairs. No hidden graph or hidden capacity function is an input. -/
def residualEdgeProg (v : V) (singletonValue : ℝ) (eligible known outward : Finset V)
    (knownResidual : V → ℝ) : Prog (Finset V) ℝ (Option (V × ℝ)) :=
  if h : ∃ w ∈ eligible ∩ known, 0 < knownResidual w then
    .pure (some (Classical.choose h, knownResidual (Classical.choose h)))
  else
    let U := (eligible \ known) ∩ outward
    (starProg v singletonValue U).bind fun mass =>
      discoverPairProg v singletonValue U.toList mass

omit [Fintype V] in
/-- Reusing a known positive residual entry makes no input query. -/
theorem residualEdgeProg_cost_of_known (read : Finset V → ℝ) (v : V)
    (singletonValue : ℝ) (eligible known outward : Finset V) (knownResidual : V → ℝ)
    (h : ∃ w ∈ eligible ∩ known, 0 < knownResidual w) :
    (residualEdgeProg v singletonValue eligible known outward knownResidual).cost read = 0 := by
  rw [residualEdgeProg, dite_eq_left h]
  rfl

omit [Fintype V] in
/-- A nonpositive unknown-mass answer ends the row test after at most the
two star queries. This is independent of the oracle's correctness. -/
theorem residualEdgeProg_cost_of_nonpositive (read : Finset V → ℝ) (v : V)
    (singletonValue : ℝ) (eligible known outward : Finset V) (knownResidual : V → ℝ)
    (hm : (starProg v singletonValue ((eligible \ known) ∩ outward)).eval read ≤ 0) :
    (residualEdgeProg v singletonValue eligible known outward knownResidual).cost read ≤ 2 := by
  unfold residualEdgeProg
  split_ifs
  · simp
  · simp only [Prog.cost_bind, discoverPairProg_cost_of_nonpositive read v singletonValue _ _ hm,
      Nat.add_zero]
    exact starProg_cost read v singletonValue _

omit [Fintype V] in
/-- The complete residual-neighbor routine has a public logarithmic cap
for arbitrary oracle answers, including its initial unknown-mass query. -/
theorem residualEdgeProg_cost (read : Finset V → ℝ) (v : V) (singletonValue : ℝ)
    (eligible known outward : Finset V) (knownResidual : V → ℝ) :
    (residualEdgeProg v singletonValue eligible known outward knownResidual).cost read ≤
      2 * Nat.clog 2 eligible.card + 4 := by
  unfold residualEdgeProg
  split_ifs with h
  · simp
  · simp only [Prog.cost_bind]
    have hs := starProg_cost read v singletonValue ((eligible \ known) ∩ outward)
    have hd := discoverPairProg_cost read v singletonValue
      ((eligible \ known) ∩ outward).toList
      ((starProg v singletonValue ((eligible \ known) ∩ outward)).eval read)
    simp only [length_toList] at hd
    have hc : ((eligible \ known) ∩ outward).card ≤ eligible.card :=
      card_le_card (fun w hw => (mem_sdiff.mp (mem_inter.mp hw).1).1)
    have hl := Nat.clog_mono_right 2 hc
    omega

/-- Exact positive-neighbor discovery in the represented residual graph,
including both known split pairs and unknown pure pairs. -/
theorem residualEdgeProg_spec (G : WeightedDiGraph V) (v : V)
    (eligible known outward : Finset V) (knownResidual residualCap : V → ℝ)
    (hknown : ∀ w ∈ eligible ∩ known, residualCap w = knownResidual w)
    (hunknown : ∀ w ∈ eligible \ known,
      residualCap w = if w ∈ outward then G.sym.w v w else 0)
    (hpos : ∃ w ∈ eligible, 0 < residualCap w) :
    ∃ w ∈ eligible, 0 < residualCap w ∧
      (residualEdgeProg v (G.out {v}) eligible known outward knownResidual).eval G.out =
        some (w, residualCap w) := by
  unfold residualEdgeProg
  split_ifs with h
  · have hc := Classical.choose_spec h
    have hcap := hknown (Classical.choose h) hc.1
    refine ⟨Classical.choose h, (mem_inter.mp hc.1).1, ?_, ?_⟩
    · rw [hcap]
      exact hc.2
    · simp only [Prog.eval_pure, hcap]
  · let U := (eligible \ known) ∩ outward
    obtain ⟨x, hx, hpx⟩ := hpos
    have hxknown : x ∉ known := by
      intro hxk
      apply h
      refine ⟨x, mem_inter.mpr ⟨hx, hxk⟩, ?_⟩
      rwa [← hknown x (mem_inter.mpr ⟨hx, hxk⟩)]
    have hxsd : x ∈ eligible \ known := mem_sdiff.mpr ⟨hx, hxknown⟩
    have hxout : x ∈ outward := by
      by_contra hxo
      have hc := hunknown x hxsd
      simp only [hxo, ↓reduceIte] at hc
      linarith
    have hxU : x ∈ U := mem_inter.mpr ⟨hxsd, hxout⟩
    have hxcap : residualCap x = G.sym.w v x := by
      simpa only [hxout, ↓reduceIte] using hunknown x hxsd
    have hmass : 0 < G.symStar v U := by
      apply sum_pos' (fun w _ => G.sym.nonneg v w)
      exact ⟨x, hxU, by rwa [← hxcap]⟩
    obtain ⟨w, hw, hp, he⟩ := discoverPairProg_spec G v U.toList
      (nodup_toList U) (G.symStar v U) (by simp) hmass
    have hwU : w ∈ U := mem_toList.mp hw
    have hwE : w ∈ eligible := (mem_sdiff.mp (mem_inter.mp hwU).1).1
    have hcap : residualCap w = G.sym.w v w := by
      simpa only [(mem_inter.mp hwU).2, ↓reduceIte] using
        hunknown w (mem_inter.mp hwU).1
    refine ⟨w, hwE, by rwa [hcap], ?_⟩
    simp only [Prog.eval_bind, starProg_eval]
    simpa only [hcap] using he

/-- An empty result is an exact residual-row certificate: every eligible
entry is nonpositive. For nonnegative residual capacities this says zero. -/
theorem residualEdgeProg_none_iff (G : WeightedDiGraph V) (v : V)
    (eligible known outward : Finset V) (knownResidual residualCap : V → ℝ)
    (hknown : ∀ w ∈ eligible ∩ known, residualCap w = knownResidual w)
    (hunknown : ∀ w ∈ eligible \ known,
      residualCap w = if w ∈ outward then G.sym.w v w else 0) :
    (residualEdgeProg v (G.out {v}) eligible known outward knownResidual).eval G.out = none ↔
      ∀ w ∈ eligible, residualCap w ≤ 0 := by
  constructor
  · intro hnone w hw
    by_contra hp
    obtain ⟨x, _, _, hx⟩ := residualEdgeProg_spec G v eligible known outward knownResidual
      residualCap hknown hunknown ⟨w, hw, lt_of_not_ge hp⟩
    rw [hnone] at hx
    contradiction
  · intro hzero
    have hknownzero : ¬ ∃ w ∈ eligible ∩ known, 0 < knownResidual w := by
      rintro ⟨w, hw, hp⟩
      have hz := hzero w (mem_inter.mp hw).1
      rw [hknown w hw] at hz
      linarith
    have hmass : G.symStar v ((eligible \ known) ∩ outward) = 0 := by
      apply sum_eq_zero
      intro w hw
      have hsd := (mem_inter.mp hw).1
      have hcap : residualCap w = G.sym.w v w := by
        simpa only [(mem_inter.mp hw).2, ↓reduceIte] using hunknown w hsd
      have hz := hzero w (mem_sdiff.mp hsd).1
      rw [hcap] at hz
      exact le_antisymm hz (G.sym.nonneg v w)
    rw [residualEdgeProg, dite_eq_right hknownzero]
    simp only [Prog.eval_bind, starProg_eval, hmass]
    rw [discoverPairProg, Prog.eval_bind, findPositiveProg, ite_eq_left (le_refl (0 : ℝ))]
    rfl

end
end CutQueryComplexity.DirectedUnitST.Repair

#print axioms CutQueryComplexity.DirectedUnitST.Repair.starProg_eval
#print axioms CutQueryComplexity.DirectedUnitST.Repair.residualStarProg_eval
#print axioms CutQueryComplexity.DirectedUnitST.Repair.residualStarProg_cost
#print axioms CutQueryComplexity.DirectedUnitST.Repair.findPositiveProg_cost
#print axioms CutQueryComplexity.DirectedUnitST.Repair.findPositiveProg_spec
#print axioms CutQueryComplexity.DirectedUnitST.Repair.discoverPairProg_cost
#print axioms CutQueryComplexity.DirectedUnitST.Repair.discoverPairProg_spec
#print axioms CutQueryComplexity.DirectedUnitST.Repair.residualEdgeProg_cost
#print axioms CutQueryComplexity.DirectedUnitST.Repair.residualEdgeProg_spec
#print axioms CutQueryComplexity.DirectedUnitST.Repair.residualEdgeProg_none_iff
