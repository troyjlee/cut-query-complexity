import CutQueryComplexity.Sparsification.EstimationCost

/-! # Charging the estimation work

Two charges are read off the call log.

* **Draw charge.** A call at scale `κ` charges `1/κ` to every vertex pair inside
  its region whose blocks differ. Scales at least halve between batches, and the
  regions of one batch are disjoint. So a pair in different blocks has charge at
  most `2/κ`, and at most `1/κ` while it waits in a pending region. When a call
  merges it, its strength is below `2κ`, so its final charge is below `4/k`.
* **Call charge.** Every call has a forest edge `f` in its region whose blocks
  differ and with `2κ ≤ n⁴w_f`. Such an edge is charged at most once per batch,
  and the invariant `2^{d_f}·κ ≤ n⁴k_f` bounds its total charge `d_f` by
  `log₂(2n⁴)` once it is merged.

`ChargeGood` packages these facts together with the exact caches of logged calls
and the equality between logged groups and recorded events. It follows
deterministically from `Good` along supported steps.
-/

namespace CutQueryComplexity.WeightedGraph
noncomputable section
open scoped Classical
open Probability
variable {V : Type} [Fintype V]

/-- The pair lies in the call's region and its blocks differ. -/
def InCall (c : CallRecord V) (u v : V) : Prop := c.π u ∈ c.T ∧ c.π v ∈ c.T ∧ c.π u ≠ c.π v

/-- The forest edge `(a, b)` is charged by the call. -/
def ForestCharged (H : WeightedGraph V) (c : CallRecord V) (a b : V) : Prop :=
  InCall c a b ∧ 0 < H.w a b ∧ 2 * c.κ ≤ (Fintype.card V : ℝ) ^ 4 * H.w a b

def chargeW (calls : List (CallRecord V)) (u v : V) : ℝ :=
  (calls.map (fun c => if InCall c u v then 1 / c.κ else 0)).sum

def chargeN (H : WeightedGraph V) (calls : List (CallRecord V)) (a b : V) : ℕ :=
  calls.countP (fun c => decide (ForestCharged H c a b))

omit [Fintype V] in
theorem chargeW_append (calls : List (CallRecord V)) (c : CallRecord V) (u v : V) :
    chargeW (calls ++ [c]) u v = chargeW calls u v + if InCall c u v then 1 / c.κ else 0 := by
  simp [chargeW]

theorem chargeN_append (H : WeightedGraph V) (calls : List (CallRecord V)) (c : CallRecord V)
    (a b : V) : chargeN H (calls ++ [c]) a b =
      chargeN H calls a b + if ForestCharged H c a b then 1 else 0 := by
  simp only [chargeN, List.countP_append, List.countP_cons, List.countP_nil]
  split_ifs <;> simp_all

abbrev nPow4 (V : Type) [Fintype V] : ℝ := (Fintype.card V : ℝ) ^ 4

structure ChargeGood (G H : WeightedGraph V) (s : EstState V) : Prop where
  records : ∀ c ∈ s.calls, (∀ b, c.cache b = G.cut (fiber c.π b)) ∧ 0 < c.κ ∧
    (∃ a b, ForestCharged H c a b)
  pendingEdge : ∀ S ∈ s.pending, ∃ a b, a ∈ S ∧ b ∈ S ∧ s.π a ≠ s.π b ∧ 0 < H.w a b ∧
    2 * s.κ ≤ nPow4 V * H.w a b
  w1 : ∀ u v, s.π u ≠ s.π v → chargeW s.calls u v ≤ 2 / s.κ ∧
    ((∃ S ∈ s.pending, u ∈ S ∧ v ∈ S) → chargeW s.calls u v ≤ 1 / s.κ)
  w2 : ∀ u v, u ≠ v → s.π u = s.π v → chargeW s.calls u v ≤ 4 / G.strength u v
  n1 : ∀ a b, 0 < H.w a b → s.π a ≠ s.π b → chargeN H s.calls a b = 0 ∨
    ((2 : ℝ) ^ chargeN H s.calls a b * s.κ ≤ nPow4 V * G.strength a b ∧
      ((∃ S ∈ s.pending, a ∈ S ∧ b ∈ S) →
        (2 : ℝ) ^ (chargeN H s.calls a b + 1) * s.κ ≤ nPow4 V * G.strength a b))
  n2 : ∀ a b, 0 < H.w a b → s.π a = s.π b → (2 : ℝ) ^ chargeN H s.calls a b ≤ 2 * nPow4 V
  groups : (s.calls.map CallRecord.groups).sum = s.events.length

/-! ### Initial state and batch boundary -/

theorem initState_charge (G H : WeightedGraph V) (cache : V → ℝ) :
    ChargeGood G H (initState H cache) := by
  refine ⟨by simp [initState], by simp [initState], ?_, ?_, ?_, ?_, by simp [initState]⟩
  · intro u v _
    simp only [initState, chargeW, List.map_nil, List.sum_nil]
    refine ⟨by have := initScale_pos H; positivity, fun h => ?_⟩
    simp at h
  · intro u v huv h
    exact (huv h).elim
  · intro a b _ _
    left
    simp [initState, chargeN]
  · intro a b hab h
    simp only [initState, id] at h
    subst h
    simp [H.diag] at hab

omit [Fintype V] in
/-- A walk inside a forest component crossing blocks has a crossing edge. -/
theorem exists_crossing_edge {F : SimpleGraph V} {π : V → V} {w u v : V}
    (hu : F.Reachable w u) (p : F.Walk u v) (hne : π u ≠ π v) :
    ∃ a b, F.Reachable w a ∧ F.Reachable w b ∧ π a ≠ π b ∧ F.Adj a b := by
  induction p with
  | nil => exact (hne rfl).elim
  | @cons x y z hxy p ih =>
      by_cases h : π x = π y
      · exact ih (hu.trans (SimpleGraph.Adj.reachable hxy)) (h ▸ hne)
      · exact ⟨x, y, hu, hu.trans (SimpleGraph.Adj.reachable hxy), h, hxy⟩

theorem activeRegion_edge {H : WeightedGraph V} {π : V → V} {t : ℝ} {S : Finset V}
    (hS : S ∈ activeRegions H π t) :
    ∃ a b, a ∈ S ∧ b ∈ S ∧ π a ≠ π b ∧ 0 < H.w a b ∧ t ≤ H.w a b := by
  obtain ⟨hS, u, hu, v, hv, hne⟩ := Finset.mem_filter.mp hS
  obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp hS
  obtain ⟨p⟩ := (mem_forestRegion.mp hu).symm.trans (mem_forestRegion.mp hv)
  obtain ⟨a, b, ha, hb, hab, hadj⟩ := exists_crossing_edge (mem_forestRegion.mp hu) p hne
  exact ⟨a, b, mem_forestRegion.mpr ha, mem_forestRegion.mpr hb, hab, hadj.1, hadj.2⟩

theorem boundary_charge {G H : WeightedGraph V} {s : EstState V} (hs : Good G H s)
    (hc : ChargeGood G H s) (hpend : s.pending = []) :
    ChargeGood G H (boundary H s) := by
  unfold boundary
  split_ifs with hrem
  · set D := topLevel H s.π
    set κ' := min (s.κ / 2) ((Fintype.card V : ℝ) ^ 2 / 2 * D)
    have hD := topLevel_pos H s.π hrem
    have hn : 0 < Fintype.card V := by
      obtain ⟨p, _⟩ := hrem
      exact Fintype.card_pos_iff.mpr ⟨p.1⟩
    have hnR : (0 : ℝ) < (Fintype.card V : ℝ) := by exact_mod_cast hn
    have hκ' : 0 < κ' := lt_min (by linarith [hs.pos]) (by positivity)
    have hhalf : κ' ≤ s.κ / 2 := min_le_left _ _
    have hle2 : 2 / s.κ ≤ 1 / κ' := by
      rw [div_le_div_iff₀ hs.pos hκ']
      linarith
    refine ⟨hc.records, ?_, ?_, hc.w2, ?_, hc.n2, hc.groups⟩
    · intro S hS
      obtain ⟨a, b, ha, hb, hab, hpos, ht⟩ := activeRegion_edge (Finset.mem_toList.mp hS)
      refine ⟨a, b, ha, hb, hab, hpos, ?_⟩
      have hκD : κ' ≤ (Fintype.card V : ℝ) ^ 2 / 2 * D := min_le_right _ _
      have hn2 : (0 : ℝ) < (Fintype.card V : ℝ) ^ 2 := by positivity
      have : (Fintype.card V : ℝ) ^ 2 * (D / (Fintype.card V : ℝ) ^ 2) = D := by field_simp
      have ht' : D ≤ (Fintype.card V : ℝ) ^ 2 * H.w a b := by
        calc D = (Fintype.card V : ℝ) ^ 2 * (D / (Fintype.card V : ℝ) ^ 2) := this.symm
          _ ≤ _ := mul_le_mul_of_nonneg_left ht hn2.le
      simp only [nPow4]
      nlinarith
    · intro u v hne
      have h := (hc.w1 u v hne).1
      exact ⟨h.trans (hle2.trans (by rw [div_le_div_iff₀ hκ' hκ']; linarith)),
        fun _ => h.trans hle2⟩
    · intro a b hab hne
      rcases hc.n1 a b hab hne with h | ⟨h1, _⟩
      · exact Or.inl h
      · right
        have hk : (2 : ℝ) ^ chargeN H s.calls a b * (2 * κ') ≤ nPow4 V * G.strength a b := by
          refine le_trans ?_ h1
          apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        refine ⟨le_trans ?_ hk, fun _ => ?_⟩
        · apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        · rw [pow_succ]
          linarith
  · exact ⟨hc.records, by simp [hpend], fun u v hne => ⟨(hc.w1 u v hne).1, by simp [hpend]⟩,
      hc.w2, fun a b hab hne => by
        rcases hc.n1 a b hab hne with h | ⟨h1, _⟩
        · exact Or.inl h
        · exact Or.inr ⟨h1, by simp [hpend]⟩, hc.n2, hc.groups⟩


/-! ### The region step -/

/-- **A good call keeps the charging invariant.** -/
theorem afterCall_charge {G H : WeightedGraph V} (hH : IsApproxKruskalForest G H)
    {s : EstState V} (hs : Good G H s)
    (hc : ChargeGood G H s) {S : Finset V} {rest : List (Finset V)}
    (hpend : s.pending = S :: rest) {X : WeightedGraph V} (hX : X.induce (S.image s.π) = X)
    {ans : Finset V → ℝ} (hs' : Good G H (afterCall s S rest X ans)) :
    ChargeGood G H (afterCall s S rest X ans) := by
  have hSmem : S ∈ s.pending := by rw [hpend]; exact List.mem_cons_self
  have hSclosed := hs.closed S hSmem
  have hdisj := hs.disjoint
  rw [hpend] at hdisj
  have hκ := hs.pos
  have hθ : 0 < 3 * s.κ / 4 := by positivity
  -- Region membership through labels.
  have hmemT {u : V} : s.π u ∈ S.image s.π ↔ u ∈ S := by
    constructor
    · intro h
      obtain ⟨w, hw, hwu⟩ := Finset.mem_image.mp h
      exact hSclosed w hw u hwu.symm
    · exact fun h => Finset.mem_image_of_mem _ h
  have hnotS {S' : Finset V} (hS' : S' ∈ rest) {u : V} (hu : u ∈ S') : u ∉ S := fun h =>
    Finset.disjoint_left.mp ((List.pairwise_cons.mp hdisj).1 S' hS') h hu
  have heq := merge_eq_iff (π := s.π) hX hθ
  have hmerged {u v : V} (hm : mergeMap s.π (S.image s.π) X (3 * s.κ / 4) u =
      mergeMap s.π (S.image s.π) X (3 * s.κ / 4) v) (hne : s.π u ≠ s.π v) : u ∈ S ∧ v ∈ S := by
    rcases (heq u v).mp hm with h | ⟨huT, hr⟩
    · exact (hne h).elim
    · exact ⟨hmemT.mp huT, hmemT.mp (component_subset hX hθ huT
        ((X.mem_strongComponent _ _ _).mpr hr))⟩
  have hcoarse {u v : V} (hne : mergeMap s.π (S.image s.π) X (3 * s.κ / 4) u ≠
      mergeMap s.π (S.image s.π) X (3 * s.κ / 4) v) : s.π u ≠ s.π v :=
    fun h => hne (mergeMap_coarsens hX hθ h)
  have hstay {x : V} (hx : x ∉ S) : mergeMap s.π (S.image s.π) X (3 * s.κ / 4) x = s.π x :=
    mergeMap_of_not_mem (fun h => hx (hmemT.mp h))
  have hn : (1 : ℝ) ≤ nPow4 V := by
    obtain ⟨a, b, ha, -⟩ := hc.pendingEdge S hSmem
    have : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨a⟩
    simp only [nPow4]
    exact one_le_pow₀ (by exact_mod_cast this)
  dsimp only [afterCall]
  set c₀ : CallRecord V := ⟨s.π, s.cache, S.image s.π, s.κ,
    (nontrivialGroups (S.image s.π) X (3 * s.κ / 4)).card⟩ with hc₀
  have hIn {u v : V} : InCall c₀ u v ↔ u ∈ S ∧ v ∈ S ∧ s.π u ≠ s.π v := by
    simp only [InCall, c₀, hmemT]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> dsimp only
  · intro c hcm
    rcases List.mem_append.mp hcm with h | h
    · exact hc.records c h
    · rw [List.mem_singleton.mp h]
      obtain ⟨a, b, ha, hb, hab, hpos, hw⟩ := hc.pendingEdge S hSmem
      exact ⟨hs.cache, hκ, a, b, hIn.mpr ⟨ha, hb, hab⟩, hpos, hw⟩
  · intro S' hS'
    obtain ⟨a, b, ha, hb, hab, hpos, hw⟩ :=
      hc.pendingEdge S' (by rw [hpend]; exact List.mem_cons_of_mem _ hS')
    refine ⟨a, b, ha, hb, ?_, hpos, hw⟩
    rw [hstay (hnotS hS' ha), hstay (hnotS hS' hb)]
    exact hab
  · intro u v hne
    have hne' := hcoarse hne
    rw [chargeW_append]
    by_cases huv : u ∈ S ∧ v ∈ S
    · have hin : InCall c₀ u v := hIn.mpr ⟨huv.1, huv.2, hne'⟩
      simp only [hin, ↓reduceIte]
      have h1 := (hc.w1 u v hne').2 ⟨S, hSmem, huv.1, huv.2⟩
      refine ⟨by simp only [c₀]; rw [show (2 : ℝ) / s.κ = 1 / s.κ + 1 / s.κ by ring]; linarith,
        fun ⟨S', hS', hu, _⟩ => (hnotS hS' hu huv.1).elim⟩
    · have hin : ¬InCall c₀ u v := fun h => huv ⟨(hIn.mp h).1, (hIn.mp h).2.1⟩
      simp only [hin, ↓reduceIte, _root_.add_zero]
      exact ⟨(hc.w1 u v hne').1, fun ⟨S', hS', hu, hv⟩ => (hc.w1 u v hne').2
        ⟨S', by rw [hpend]; exact List.mem_cons_of_mem _ hS', hu, hv⟩⟩
  · intro u v huv hm
    rw [chargeW_append]
    by_cases hπ : s.π u = s.π v
    · have hin : ¬InCall c₀ u v := fun h => (hIn.mp h).2.2 hπ
      simp only [hin, ↓reduceIte, _root_.add_zero]
      exact hc.w2 u v huv hπ
    · obtain ⟨hu, hv⟩ := hmerged hm hπ
      simp only [hIn.mpr ⟨hu, hv, hπ⟩, ↓reduceIte]
      have h1 := (hc.w1 u v hπ).2 ⟨S, hSmem, hu, hv⟩
      have hk : s.κ / 2 ≤ G.strength u v := (G.le_strength_iff huv _).mpr (hs'.refines u v hm)
      have hk2 := hs.sep u v hπ
      have hkpos : 0 < G.strength u v := by linarith
      simp only [c₀]
      have : 1 / s.κ + 1 / s.κ ≤ 4 / G.strength u v := by
        rw [show 1 / s.κ + 1 / s.κ = 2 / s.κ by ring, div_le_div_iff₀ hκ hkpos]
        linarith
      linarith
  · intro a b hab hne
    have hne' := hcoarse hne
    rw [chargeN_append]
    by_cases hfc : ForestCharged H c₀ a b
    · simp only [hfc, ↓reduceIte]
      obtain ⟨hin, -, hw⟩ := hfc
      obtain ⟨ha, hb, -⟩ := hIn.mp hin
      have hwk := G.weight_le_strength a b
      have hHG : H.w a b ≤ G.w a b := hH.original.subgraph a b
      right
      refine ⟨?_, fun ⟨S', hS', ha', _⟩ => (hnotS hS' ha' ha).elim⟩
      rcases hc.n1 a b hab hne' with h0 | ⟨_, hpend'⟩
      · rw [h0, _root_.zero_add, pow_one]
        simp only [c₀] at hw
        have : nPow4 V * H.w a b ≤ nPow4 V * G.strength a b :=
          mul_le_mul_of_nonneg_left (hHG.trans hwk) (by positivity)
        linarith
      · exact hpend' ⟨S, hSmem, ha, hb⟩
    · simp only [hfc, ↓reduceIte, _root_.add_zero]
      rcases hc.n1 a b hab hne' with h0 | ⟨h1, hpend'⟩
      · exact Or.inl h0
      · exact Or.inr ⟨h1, fun ⟨S', hS', ha', hb'⟩ =>
          hpend' ⟨S', by rw [hpend]; exact List.mem_cons_of_mem _ hS', ha', hb'⟩⟩
  · intro a b hab hm
    rw [chargeN_append]
    by_cases hπ : s.π a = s.π b
    · have hfc : ¬ForestCharged H c₀ a b := fun h => (hIn.mp h.1).2.2 hπ
      simp only [hfc, ↓reduceIte, _root_.add_zero]
      exact hc.n2 a b hab hπ
    · obtain ⟨ha, hb⟩ := hmerged hm hπ
      have hk2 := hs.sep a b hπ
      have hpow : ∀ d : ℕ, (2 : ℝ) ^ chargeN H s.calls a b ≤ 2 ^ d →
          (2 : ℝ) ^ (chargeN H s.calls a b + if ForestCharged H c₀ a b then 1 else 0) ≤
            2 ^ (d + 1) := by
        intro d hd
        split_ifs
        · rw [pow_succ, pow_succ]
          linarith
        · rw [_root_.add_zero, pow_succ]
          linarith [pow_pos (by norm_num : (0 : ℝ) < 2) d]
      rcases hc.n1 a b hab hπ with h0 | ⟨_, hpend'⟩
      · have := hpow 0 (by rw [h0])
        simp only [_root_.zero_add, pow_one] at this
        linarith
      · have h := hpend' ⟨S, hSmem, ha, hb⟩
        have hlt : (2 : ℝ) ^ (chargeN H s.calls a b + 1) < 2 * nPow4 V := by
          have : nPow4 V * G.strength a b < nPow4 V * (2 * s.κ) :=
            mul_lt_mul_of_pos_left hk2 (by linarith)
          by_contra hge
          push Not at hge
          nlinarith
        have := hpow (chargeN H s.calls a b) le_rfl
        linarith
  · simp only [List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
      List.sum_nil, _root_.add_zero, List.length_append, List.length_map, Finset.length_toList,
      hc.groups]
    rfl


/-! ### Along the run -/

theorem estStep_charge {G H : WeightedGraph V} (hH : IsApproxKruskalForest G H) {ρ : ℝ}
    (hρ : 0 < ρ) {R : ℕ} {s s' : EstState V} (hs : Good G H s) (hc : ChargeGood G H s)
    (hs' : Good G H s') (hmem : s' ∈ ((estStep H ρ R s).eval G.cut).support) :
    ChargeGood G H s' := by
  unfold estStep at hmem
  rcases hst : s.status with _ | _ | _ <;> rw [hst] at hmem
  · rcases hp : s.pending with _ | ⟨S, rest⟩ <;> rw [hp] at hmem
    · simp only [RTree.eval_pure, PMF.mem_support_pure_iff] at hmem
      subst hmem
      exact boundary_charge hs hc hp
    · simp only [hs.pos, ↓reduceDIte] at hmem
      rw [regionStep_eval] at hmem
      obtain ⟨o, ho, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hmem
      cases o with
      | none => exact absurd rfl hs'.notFailed
      | some X =>
          have hB : Fintype.card V ≤ 2 ^ searchDepth V := Nat.le_pow_clog (by decide) _
          exact afterCall_charge hH hs hc hp
            (estimateCall_support G (searchDepth V) (searchDepth V) s.π s.cache hs.cache _
              hB hB hs.pos hρ R ho) hs'
  · simp only [RTree.eval_pure, PMF.mem_support_pure_iff] at hmem
    subst hmem
    exact hc
  · exact absurd hst hs.notFailed

/-- The fuel-indexed invariant with events and charges. -/
def RunInv3 (G H : WeightedGraph V) (N : ℕ) (s : EstState V) : Prop :=
  RunInv2 G H N s ∧ ChargeGood G H s

theorem estStep_failure3 {G H : WeightedGraph V} (hH : IsApproxKruskalForest G H) {ρ : ℝ}
    (hρ : 0 < ρ) {R : ℕ} (hR : ρ * (Fintype.card V : ℝ) ^ 2 ≤ R) {δ₀ : ℝ} (hδ : 0 ≤ δ₀)
    (hδ2 : δ₀ ≤ 2)
    (hexp : ((2 * Fintype.card V : ℕ) : ℝ) ^ 2 * Real.exp (-(ρ / 128)) ≤ δ₀ / 4)
    (N : ℕ) (s : EstState V) (hs : RunInv3 G H (N + 1) s) :
    Probability.mass ((estStep H ρ R s).eval G.cut) (fun s' => ¬RunInv3 G H N s') ≤
      callFailure V ρ δ₀ := by
  refine le_trans (mass_mono_on_support _ (fun s' hs' hbad => ?_))
    (estStep_failure2 hH hρ hR hδ hδ2 hexp N s hs.1)
  intro hinv
  exact hbad ⟨hinv, estStep_charge hH hρ hs.1.1.1 hs.2 hinv.1.1 hs'⟩

/-- Successful finished state with charges. -/
def EstSuccess' (G H : WeightedGraph V) (s : EstState V) : Prop :=
  EstSuccess G H s ∧ ChargeGood G H s

theorem estRun_correct' {G H : WeightedGraph V} (hH : IsApproxKruskalForest G H) {ρ : ℝ}
    (hρ : 0 < ρ) {R : ℕ} (hR : ρ * (Fintype.card V : ℝ) ^ 2 ≤ R) {δ₀ : ℝ} (hδ : 0 ≤ δ₀)
    (hδ2 : δ₀ ≤ 2)
    (hexp : ((2 * Fintype.card V : ℕ) : ℝ) ^ 2 * Real.exp (-(ρ / 128)) ≤ δ₀ / 4)
    {cache : V → ℝ} (hc : ∀ b, cache b = G.cut (fiber (id : V → V) b)) {N : ℕ}
    (hN : runPot H (initState H cache) ≤ N) :
    Probability.mass ((estRun H ρ R N (initState H cache)).eval G.cut)
      (fun s => ¬EstSuccess' G H s) ≤ N * callFailure V ρ δ₀ := by
  have h := RTree.iterate_failure_le (estStep H ρ R) G.cut (RunInv3 G H) (callFailure V ρ δ₀)
    (estStep_failure3 hH hρ hR hδ hδ2 hexp) N (initState H cache)
    ⟨⟨⟨initState_good hH hc, hN⟩, initState_events G H cache⟩, initState_charge G H cache⟩
  unfold estRun
  refine le_trans (mass_mono _ ?_) h
  intro s hbad hinv
  apply hbad
  obtain ⟨⟨⟨hg, hpot⟩, hev⟩, hch⟩ := hinv
  refine ⟨⟨hg, hev, ?_⟩, hch⟩
  rcases hst : s.status with _ | _ | _
  · simp [runPot, hst] at hpot
  · rfl
  · exact absurd hst hg.notFailed

end
end CutQueryComplexity.WeightedGraph
