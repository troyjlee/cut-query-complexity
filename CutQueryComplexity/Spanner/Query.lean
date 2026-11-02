import CutQueryComplexity.Spanner.Random
import CutQueryComplexity.Primitive.OrderedSearch

/-! # Query implementation of a spanner trial (D3; source `lem:search`, `lem:spanner`)

The algorithm state is public (`PubState`): a residual predicate on all potential pairs, cluster
labels, and the explicit selected pairs. The hidden residual is
`semOf G ps = {e : e is an actual pair ∧ res e}`. Every search list is public: candidates are
filtered by public predicates and sorted by key (`sortKey`), and the ordered search
(`firstNbr`) returns the first actual pair.

For one vertex `a` (`vertexQ`):

* sampled vertices keep their label and search nothing;
* otherwise, search `f_a` among residual pairs into sampled clusters, then repeatedly search the
  minimum residual pair with key at most `σ = key f_a` into a cluster not yet reported
  (`reportLoop`). Its endpoint names the next reported cluster, which is then excluded.

`vertexQ_correct`: the reported clusters, selected pairs, and new label are exactly those of the
semantic phase (`Spanner.step`). A search hit is the minimum-key eligible actual pair, because
the list is sorted and keys are injective. The report loop keeps every found cluster reported;
when the search fails, no reported cluster is left.
-/

namespace CutQueryComplexity
namespace Spanner

open Finset

noncomputable section

attribute [local instance 10] Classical.propDecidable

variable {V : Type} [Fintype V] [DecidableEq V] {κ : Type} [LinearOrder κ]

/-! ## Sorted search lists -/

variable (key : Sym2 V → κ)

/-- Candidates sorted by the key of their pair with `a`. -/
def sortKey (a : V) (s : Finset V) : List V :=
  s.toList.mergeSort fun x y => decide (key s(a, x) ≤ key s(a, y))

variable {key}

omit [Fintype V] [DecidableEq V] in
theorem mem_sortKey {a x : V} {s : Finset V} : x ∈ sortKey key a s ↔ x ∈ s := by
  rw [sortKey, List.mem_mergeSort, mem_toList]

omit [Fintype V] [DecidableEq V] in
theorem sortKey_nodup (a : V) (s : Finset V) : (sortKey key a s).Nodup :=
  (List.mergeSort_perm _ _).nodup_iff.mpr (nodup_toList s)

omit [Fintype V] [DecidableEq V] in
theorem sortKey_pairwise (a : V) (s : Finset V) :
    (sortKey key a s).Pairwise fun x y => decide (key s(a, x) ≤ key s(a, y)) = true :=
  List.pairwise_mergeSort (fun x y z hxy hyz => by simp at *; exact hxy.trans hyz)
    (fun x y => by simp [le_total]) _

omit [Fintype V] [DecidableEq V] in
theorem length_sortKey (a : V) (s : Finset V) : (sortKey key a s).length = s.card := by
  rw [sortKey, (List.mergeSort_perm _ _).length_eq, length_toList]

omit [Fintype V] [DecidableEq V] in
/-- The first hit of a key-sorted list has the minimum key among hits. -/
theorem find_min {g : V → κ} {p : V → Bool} :
    ∀ {L : List V}, L.Pairwise (fun x y => decide (g x ≤ g y) = true) →
      ∀ {y}, L.find? p = some y → ∀ x ∈ L, p x = true → g y ≤ g x
  | [], _, _, h, _, _, _ => by simp at h
  | z :: L, hL, y, h, x, hx, hpx => by
      rw [List.find?_cons] at h
      rw [List.pairwise_cons] at hL
      cases hz : p z
      · rw [hz] at h
        rcases List.mem_cons.mp hx with rfl | hx
        · rw [hz] at hpx; cases hpx
        · exact find_min hL.2 h x hx hpx
      · rw [hz] at h; cases h
        rcases List.mem_cons.mp hx with rfl | hx
        · exact le_rfl
        · simpa using hL.1 x hx

/-! ## Public state -/

/-- The pair multiplicity of an unordered pair. -/
def symS (G : DiGraph V) : Sym2 V → ℕ := Sym2.lift ⟨G.sym, G.sym_comm⟩

omit [Fintype V] [DecidableEq V] in
@[simp] theorem symS_mk (G : DiGraph V) (u v : V) : symS G s(u, v) = G.sym u v := rfl

/-- The public algorithm state. -/
structure PubState (V : Type) where
  res : Sym2 V → Bool
  lab : V → Option V
  H : Finset (Sym2 V)

/-- The hidden residual described by a public state. -/
def semOf (G : DiGraph V) (ps : PubState V) : State V :=
  ⟨univ.filter fun e => 0 < symS G e ∧ ps.res e = true, ps.lab, ps.H⟩

omit [DecidableEq V] in
theorem mem_semOf_E {G : DiGraph V} {ps : PubState V} {a u : V} :
    s(a, u) ∈ (semOf G ps).E ↔ 0 < G.sym a u ∧ ps.res s(a, u) = true := by
  simp [semOf]

/-! ## One vertex -/

/-- Public candidates for `f_a`: residual pairs into sampled clusters. -/
def sampCand (coin : V → Bool) (ps : PubState V) (a : V) : Finset V :=
  univ.filter fun u => u ≠ a ∧ ps.res s(a, u) = true ∧ ∃ c, ps.lab u = some c ∧ coin c = true

variable (key)

/-- Public candidates for the next report: residual pairs with key at most `σ` into a cluster not
yet reported. -/
def repCand (ps : PubState V) (a : V) (σ : Option V) (X : Finset V) : Finset V :=
  univ.filter fun u => u ≠ a ∧ ps.res s(a, u) = true ∧ (∃ D, ps.lab u = some D ∧ D ∉ X) ∧
    ∀ z, σ = some z → key s(a, u) ≤ key s(a, z)

/-- The report loop with `fuel` searches; it returns the reported clusters and selected pairs. -/
def reportLoop (ps : PubState V) (a : V) (σ : Option V) (k : ℕ) :
    (fuel : ℕ) → Finset V → Finset (Sym2 V) →
      DTree (Finset V) ℕ (Finset V × Finset (Sym2 V)) (fuel * (3 + 3 * k))
  | 0, X, sel => DTree.pure (X, sel)
  | fuel + 1, X, sel =>
      ((firstNbr a k (sortKey key a (repCand key ps a σ X))).bind fun r =>
        match r with
        | none => DTree.pure (X, sel)
        | some (u, _) => reportLoop ps a σ k fuel (insert ((ps.lab u).getD u) X)
            (insert s(a, u) sel)).cast (by ring)

/-- One vertex: reported clusters, selected pairs, and new label. -/
def vertexQ (coin : V → Bool) (ps : PubState V) (a : V) (k : ℕ) :
    DTree (Finset V) ℕ (Finset V × Finset (Sym2 V) × Option V)
      ((Fintype.card V + 1) * (3 + 3 * k)) :=
  if ∃ c, ps.lab a = some c ∧ coin c = true then DTree.pure (∅, ∅, ps.lab a)
  else ((firstNbr a k (sortKey key a (sampCand coin ps a))).bind fun r =>
    (reportLoop key ps a (r.map Prod.fst) k (Fintype.card V) ∅ ∅).map fun xs =>
      (xs.1, xs.2, (r.map Prod.fst).bind ps.lab)).cast (by ring)

/-- The selected pairs of `a` in the semantic phase. -/
def selOf (coin : V → Bool) (st : State V) (a : V) : Finset (Sym2 V) :=
  univ.filter fun f => ∃ D y, Reported key coin st a D ∧ minNbr key a (toClus st a D) = some y ∧
    f = s(a, y)

/-! ## Correctness of one vertex -/

variable {key}

omit [Fintype V] [DecidableEq V] in
theorem minNbr_eq_of_min (hinj : Function.Injective key) {a : V} {U : Finset V} {y : V}
    (hy : y ∈ U) (hmin : ∀ u ∈ U, key s(a, y) ≤ key s(a, u)) : minNbr key a U = some y := by
  obtain ⟨y', hy'⟩ := exists_minNbr key ⟨y, hy⟩ (a := a)
  obtain ⟨hy'U, hy'min⟩ := minNbr_some key hy'
  have heq : key s(a, y') = key s(a, y) := le_antisymm (hy'min y hy) (hmin y' hy'U)
  have hp := hinj heq
  rw [hy']
  rcases Sym2.eq_iff.mp hp with ⟨-, h⟩ | ⟨h1, h2⟩
  · rw [h]
  · rw [← h1, h2]

/-- The specification of an ordered search on a key-sorted candidate list. -/
theorem firstNbr_sortKey (G : DiGraph V) {a : V} {s : Finset V} (ha : a ∉ s) {k : ℕ}
    (hk : Fintype.card V ≤ 2 ^ k) :
    ((firstNbr a k (sortKey key a s)).eval G.out = none ↔ ∀ u ∈ s, G.sym a u = 0) ∧
      ∀ y m, (firstNbr a k (sortKey key a s)).eval G.out = some (y, m) →
        y ∈ s ∧ 0 < G.sym a y ∧ m = G.sym a y ∧
          ∀ u ∈ s, 0 < G.sym a u → key s(a, y) ≤ key s(a, u) := by
  have hnd := sortKey_nodup (key := key) a s
  have hna : a ∉ sortKey key a s := fun h => ha (mem_sortKey.mp h)
  have hlen : (sortKey key a s).length ≤ 2 ^ k := by
    rw [length_sortKey]; exact (card_le_univ s).trans hk
  rw [firstNbr_correct G a k hnd hna hlen]
  constructor
  · unfold firstPos
    rw [Option.map_eq_none_iff, List.find?_eq_none]
    constructor
    · intro h u hu
      have := h u (mem_sortKey.mpr hu); simpa using this
    · intro h u hu; simp [h u (mem_sortKey.mp hu)]
  · intro y m h
    unfold firstPos at h
    cases hf : (sortKey key a s).find? (fun x => decide (0 < G.sym a x)) with
    | none => rw [hf] at h; cases h
    | some y' =>
        rw [hf] at h; simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨mem_sortKey.mp (List.mem_of_find?_eq_some hf), by simpa using List.find?_some hf,
          rfl, fun u hu hpos => ?_⟩
        exact find_min (g := fun x => key s(a, x)) (sortKey_pairwise a s) hf u
          (mem_sortKey.mpr hu) (by simpa using hpos)

variable {G : DiGraph V}

theorem mem_toSamp_semOf {coin : V → Bool} {ps : PubState V} {a u : V} :
    u ∈ toSamp coin (semOf G ps) a ↔ u ∈ sampCand coin ps a ∧ 0 < G.sym a u := by
  rw [mem_toSamp, mem_semOf_E]
  simp only [sampCand, mem_filter, mem_univ, true_and, Samp, semOf]
  constructor
  · rintro ⟨⟨hpos, hres⟩, hs⟩
    refine ⟨⟨fun h => ?_, hres, hs⟩, hpos⟩
    subst h; simp at hpos
  · rintro ⟨⟨-, hres, hs⟩, hpos⟩; exact ⟨⟨hpos, hres⟩, hs⟩

theorem mem_toClus_semOf {ps : PubState V} {a D u : V} :
    u ∈ toClus (semOf G ps) a D ↔ 0 < G.sym a u ∧ ps.res s(a, u) = true ∧ ps.lab u = some D := by
  rw [mem_toClus, mem_semOf_E]; simp [semOf, and_assoc]

/-- The selected pairs of a set of reported clusters. -/
def selX (st : State V) (a : V) (X : Finset V) : Finset (Sym2 V) :=
  univ.filter fun f => ∃ D ∈ X, ∃ y, minNbr key a (toClus st a D) = some y ∧ f = s(a, y)

theorem selOf_eq_selX (coin : V → Bool) (st : State V) (a : V) :
    selOf key coin st a = selX (key := key) st a (reportsOf key coin st a) := by
  ext f
  simp only [selOf, selX, reportsOf, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨D, y, hr, hy, rfl⟩; exact ⟨D, hr, y, hy, rfl⟩
  · rintro ⟨D, hr, y, hy, rfl⟩; exact ⟨D, y, hr, hy, rfl⟩

/-- **The report loop finds exactly the reported clusters.** -/
theorem reportLoop_correct (hinj : Function.Injective key) (coin : V → Bool) (ps : PubState V)
    {a : V} (hns : ¬ ∃ c, ps.lab a = some c ∧ coin c = true) {k : ℕ}
    (hk : Fintype.card V ≤ 2 ^ k) :
    ∀ (fuel : ℕ) (X : Finset V), X ⊆ reportsOf key coin (semOf G ps) a →
      (reportsOf key coin (semOf G ps) a).card ≤ fuel + X.card →
      (reportLoop key ps a ((minNbr key a (toSamp coin (semOf G ps) a))) k fuel X
        (selX (key := key) (semOf G ps) a X)).eval G.out =
        (reportsOf key coin (semOf G ps) a, selOf key coin (semOf G ps) a) := by
  set st := semOf G ps
  set R := reportsOf key coin st a
  set σ := minNbr key a (toSamp coin st a)
  intro fuel
  induction fuel with
  | zero =>
      intro X hX hcard
      have : X = R := eq_of_subset_of_card_le hX (by omega)
      subst this
      simp only [reportLoop, DTree.eval_pure, selOf_eq_selX]
      rfl
  | succ fuel ih =>
      intro X hX hcard
      have haX : a ∉ repCand key ps a σ X := by simp [repCand]
      obtain ⟨hnone, hsome⟩ := firstNbr_sortKey (key := key) G haX hk
      simp only [reportLoop, DTree.eval_cast, DTree.eval_bind]
      cases hr : (firstNbr a k (sortKey key a (repCand key ps a σ X))).eval G.out with
      | none =>
          -- no eligible pair: every reported cluster is already in `X`
          simp only [DTree.eval_pure]
          have hRX : R ⊆ X := by
            intro D hD
            by_contra hDX
            obtain ⟨-, y, hy, hmin⟩ := (mem_filter.mp hD).2
            obtain ⟨hyC, -⟩ := minNbr_some key hy
            obtain ⟨hpos, hres, hlab⟩ := mem_toClus_semOf.mp hyC
            have hyc : y ∈ repCand key ps a σ X := by
              simp only [repCand, mem_filter, mem_univ, true_and]
              refine ⟨fun h => ?_, hres, ⟨D, hlab, hDX⟩, fun z hz => hmin z hz⟩
              subst h; simp at hpos
            have := (hnone.mp hr) y hyc
            omega
          have hXR : X = R := le_antisymm hX hRX
          subst hXR
          rw [selOf_eq_selX]
      | some r =>
          obtain ⟨u, m⟩ := r
          simp only
          obtain ⟨huc, hpos, -, hmin⟩ := hsome u m hr
          simp only [repCand, mem_filter, mem_univ, true_and] at huc
          obtain ⟨-, hres, ⟨D, hlab, hDX⟩, hσ⟩ := huc
          have hgetD : (ps.lab u).getD u = D := by rw [hlab]; rfl
          -- `u` is the minimum pair into `D`
          have huD : u ∈ toClus st a D := mem_toClus_semOf.mpr ⟨hpos, hres, hlab⟩
          have hminD : minNbr key a (toClus st a D) = some u := by
            refine minNbr_eq_of_min hinj huD fun v hv => ?_
            by_contra hlt
            push Not at hlt
            obtain ⟨hvpos, hvres, hvlab⟩ := mem_toClus_semOf.mp hv
            have hvc : v ∈ repCand key ps a σ X := by
              simp only [repCand, mem_filter, mem_univ, true_and]
              refine ⟨fun h => ?_, hvres, ⟨D, hvlab, hDX⟩, fun z hz => (hlt.le.trans (hσ z hz))⟩
              subst h; simp at hvpos
            exact absurd (hmin v hvc hvpos) (not_le.mpr hlt)
          have hDR : D ∈ R := by
            refine mem_filter.mpr ⟨mem_univ _, ?_⟩
            exact ⟨fun ⟨c, hc, hcoin⟩ => hns ⟨c, hc, hcoin⟩, u, hminD, fun z hz => hσ z hz⟩
          rw [hgetD]
          have hsel : insert s(a, u) (selX (key := key) st a X) =
              selX (key := key) st a (insert D X) := by
            ext f
            simp only [selX, mem_insert, mem_filter, mem_univ, true_and]
            constructor
            · rintro (rfl | ⟨D', hD', y, hy, rfl⟩)
              · exact ⟨D, Or.inl rfl, u, hminD, rfl⟩
              · exact ⟨D', Or.inr hD', y, hy, rfl⟩
            · rintro ⟨D', rfl | hD', y, hy, rfl⟩
              · rw [hminD] at hy; cases hy; exact Or.inl rfl
              · exact Or.inr ⟨D', hD', y, hy, rfl⟩
          rw [hsel]
          exact ih (insert D X) (insert_subset hDR hX) (by rw [card_insert_of_notMem hDX]; omega)

/-- **One vertex is implemented exactly.** -/
theorem vertexQ_correct (hinj : Function.Injective key) (coin : V → Bool) (ps : PubState V)
    (a : V) {k : ℕ} (hk : Fintype.card V ≤ 2 ^ k) :
    (vertexQ key coin ps a k).eval G.out =
      (reportsOf key coin (semOf G ps) a, selOf key coin (semOf G ps) a,
        newLab key coin (semOf G ps) a) := by
  set st := semOf G ps
  unfold vertexQ
  split_ifs with hs
  · -- a sampled vertex reports nothing
    have hR : reportsOf key coin st a = ∅ := by
      ext D; simp only [reportsOf, mem_filter, mem_univ, true_and, Finset.notMem_empty,
        iff_false]
      rintro ⟨hns, -⟩; exact hns (by simpa [Samp, st, semOf] using hs)
    have hsel : selOf key coin st a = ∅ := by
      ext f; simp only [selOf, mem_filter, mem_univ, true_and, Finset.notMem_empty, iff_false]
      rintro ⟨D, y, ⟨hns, -⟩, -⟩; exact hns (by simpa [Samp, st, semOf] using hs)
    have hlab : newLab key coin st a = ps.lab a := by
      simp [newLab, Samp, st, semOf, hs]
    simp [hR, hsel, hlab]
  · have hna : a ∉ sampCand coin ps a := by simp [sampCand]
    obtain ⟨hnone, hsome⟩ := firstNbr_sortKey (key := key) G hna hk
    -- the search for `f_a` returns the semantic minimum
    have hfa : ((firstNbr a k (sortKey key a (sampCand coin ps a))).eval G.out).map Prod.fst =
        minNbr key a (toSamp coin st a) := by
      cases hr : (firstNbr a k (sortKey key a (sampCand coin ps a))).eval G.out with
      | none =>
          have hemp : toSamp coin st a = ∅ := by
            ext u
            simp only [Finset.notMem_empty, iff_false]
            intro hu
            obtain ⟨huc, hpos⟩ := mem_toSamp_semOf.mp hu
            have := (hnone.mp hr) u huc; omega
          rw [hemp, minNbr_eq_none key rfl]; rfl
      | some r =>
          obtain ⟨z, m⟩ := r
          obtain ⟨hzc, hzpos, -, hzmin⟩ := hsome z m hr
          symm
          refine minNbr_eq_of_min hinj (mem_toSamp_semOf.mpr ⟨hzc, hzpos⟩) fun u hu => ?_
          obtain ⟨huc, hupos⟩ := mem_toSamp_semOf.mp hu
          exact hzmin u huc hupos
    simp only [DTree.eval_cast, DTree.eval_bind, DTree.eval_map, hfa]
    have hsel0 : (∅ : Finset (Sym2 V)) = selX (key := key) st a ∅ := by
      ext f; simp [selX]
    rw [hsel0, reportLoop_correct hinj coin ps hs hk (Fintype.card V) ∅ (empty_subset _)
      (by simpa using card_le_univ _)]
    simp [newLab, Samp, st, semOf, hs]

/-! ## One phase and the trial -/

/-- The per-vertex results of a phase. -/
abbrev VRes (V : Type) := Finset V × Finset (Sym2 V) × Option V

variable (key)

/-- The query budget of one vertex. -/
abbrev vBudget (V : Type) [Fintype V] (k : ℕ) : ℕ := (Fintype.card V + 1) * (3 + 3 * k)

/-- Process listed vertices against the frozen old state. -/
def phaseLoop (coin : V → Bool) (ps : PubState V) (k : ℕ) :
    (vs : List V) → DTree (Finset V) ℕ (V → VRes V) (vs.length * vBudget V k)
  | [] => DTree.pure fun _ => (∅, ∅, none)
  | a :: vs => ((vertexQ key coin ps a k).bind fun r =>
      (phaseLoop coin ps k vs).map fun m => Function.update m a r).cast
        (by simp only [List.length_cons]; ring)

/-- The public update after all reports. -/
def nextPub (ps : PubState V) (m : V → VRes V) : PubState V where
  res e := decide (ps.res e = true ∧ ¬ (∃ a b D, e = s(a, b) ∧ ps.lab b = some D ∧ D ∈ (m a).1) ∧
    ¬ ∃ a b, e = s(a, b) ∧ (m a).2.2 = (m b).2.2)
  lab a := (m a).2.2
  H := ps.H ∪ univ.biUnion fun a => (m a).2.1

/-- The query budget of one phase. -/
abbrev phBudget (V : Type) [Fintype V] (k : ℕ) : ℕ := Fintype.card V * vBudget V k

/-- **One phase.** -/
def phaseQ (coin : V → Bool) (ps : PubState V) (k : ℕ) :
    DTree (Finset V) ℕ (PubState V) (phBudget V k) :=
  ((phaseLoop key coin ps k (univ : Finset V).toList).map (nextPub ps)).cast
    (by rw [length_toList, card_univ])

variable {key}

theorem phaseLoop_correct (hinj : Function.Injective key) (coin : V → Bool) (ps : PubState V)
    {k : ℕ} (hk : Fintype.card V ≤ 2 ^ k) (vs : List V) {a : V} (ha : a ∈ vs) :
    (phaseLoop key coin ps k vs).eval G.out a =
      (reportsOf key coin (semOf G ps) a, selOf key coin (semOf G ps) a,
        newLab key coin (semOf G ps) a) := by
  induction vs with
  | nil => simp at ha
  | cons b vs ih =>
      simp only [phaseLoop, DTree.eval_cast, DTree.eval_bind, DTree.eval_map]
      by_cases hab : a = b
      · subst hab; rw [Function.update_self, vertexQ_correct hinj coin ps a hk]
      · rw [Function.update_of_ne hab]; exact ih ((List.mem_cons.mp ha).resolve_left hab)

/-- **One phase is implemented exactly.** -/
theorem phaseQ_correct (hinj : Function.Injective key) (coin : V → Bool) (ps : PubState V)
    {k : ℕ} (hk : Fintype.card V ≤ 2 ^ k) :
    semOf G ((phaseQ key coin ps k).eval G.out) = step key coin (semOf G ps) := by
  set m := (phaseLoop key coin ps k (univ : Finset V).toList).eval G.out
  have hm : ∀ a, m a = (reportsOf key coin (semOf G ps) a, selOf key coin (semOf G ps) a,
      newLab key coin (semOf G ps) a) := fun a =>
    phaseLoop_correct hinj coin ps hk _ (mem_toList.mpr (mem_univ a))
  have heval : (phaseQ key coin ps k).eval G.out = nextPub ps m := by
    simp [phaseQ, m]
  rw [heval]
  set st := semOf G ps
  have hDel : ∀ e, (∃ a b D, e = s(a, b) ∧ ps.lab b = some D ∧ D ∈ (m a).1) ↔
      Del key coin st e := fun e => by
    simp only [hm, Del, reportsOf, mem_filter, mem_univ, true_and]; rfl
  have hSame : ∀ e, (∃ a b, e = s(a, b) ∧ (m a).2.2 = (m b).2.2) ↔ SameNew key coin st e :=
    fun e => by simp only [hm, SameNew]
  show State.mk _ _ _ = State.mk _ _ _
  congr 1
  · ext e
    simp only [semOf, nextPub, mem_filter, mem_univ, true_and, decide_eq_true_eq, hDel, hSame, st]
    tauto
  · funext a; simp [nextPub, hm]
  · simp only [nextPub, selected]
    congr 1
    ext f
    simp only [mem_biUnion, mem_univ, true_and, hm, selOf, mem_filter]

variable (key)

/-- The first `j` phases. -/
def phasesQ (coins : ℕ → V → Bool) (k : ℕ) (ps0 : PubState V) :
    (j : ℕ) → DTree (Finset V) ℕ (PubState V) (j * phBudget V k)
  | 0 => DTree.pure ps0
  | j + 1 => ((phasesQ coins k ps0 j).bind fun ps => phaseQ key (coins j) ps k).cast (by ring)

/-- The initial public state for a public support predicate `P`. -/
def ps0 (P : Sym2 V → Bool) : PubState V := ⟨P, some, ∅⟩

/-- The original support: actual pairs satisfying `P`. -/
def support (G : DiGraph V) (P : Sym2 V → Bool) : Finset (Sym2 V) :=
  univ.filter fun e => 0 < symS G e ∧ P e = true

/-- **A full trial**: `K` sampled phases, then the final phase; returns the selected pairs. -/
def trialQ {K : ℕ} (cs : Fin K → V → Bool) (k : ℕ) (P : Sym2 V → Bool) :
    DTree (Finset V) ℕ (Finset (Sym2 V)) (K * phBudget V k + phBudget V k) :=
  (phasesQ key (extCoins cs) k (ps0 P) K).bind fun ps =>
    (phaseQ key (fun _ => false) ps k).map PubState.H

variable {key}

theorem phasesQ_correct (hinj : Function.Injective key) (coins : ℕ → V → Bool) {k : ℕ}
    (hk : Fintype.card V ≤ 2 ^ k) (P : Sym2 V → Bool) :
    ∀ j, semOf G ((phasesQ key coins k (ps0 P) j).eval G.out) =
      runPhases key coins (support G P) j
  | 0 => by simp [phasesQ, runPhases, semOf, ps0, init, support]
  | j + 1 => by
      simp only [phasesQ, DTree.eval_cast, DTree.eval_bind, runPhases]
      rw [phaseQ_correct hinj _ _ hk, phasesQ_correct hinj coins hk P j]

/-- **A full trial is implemented exactly**: its output is the semantic trial's spanner. -/
theorem trialQ_correct (hinj : Function.Injective key) {K : ℕ} (cs : Fin K → V → Bool) {k : ℕ}
    (hk : Fintype.card V ≤ 2 ^ k) (P : Sym2 V → Bool) :
    (trialQ key cs k P).eval G.out = (trial key (extCoins cs) (support G P) (K + 1)).H := by
  simp only [trialQ, DTree.eval_bind, DTree.eval_map, trial, Nat.add_sub_cancel]
  rw [← phasesQ_correct hinj (extCoins cs) hk P K, ← phaseQ_correct hinj _ _ hk]
  rfl

/-! ## Query cost -/

section Cost

variable {I A O P : Type} {q r : ℕ}

theorem dcost_bind (T : DTree I A O q) (f : O → DTree I A P r) (read : I → A) :
    (T.bind f).cost read = T.cost read + (f (T.eval read)).cost read := by
  simp [DTree.cost, DTree.run_bind]

theorem dcost_map (f : O → P) (T : DTree I A O q) (read : I → A) :
    (T.map f).cost read = T.cost read := by simp [DTree.cost]

theorem dcost_cast (h : q = r) (T : DTree I A O q) (read : I → A) :
    (T.cast h).cost read = T.cost read := by simp [DTree.cost]

@[simp] theorem dcost_pure (o : O) (read : I → A) : (DTree.pure (q := q) o : DTree I A O q).cost read = 0 := by
  simp [DTree.cost]

end Cost

omit [Fintype V] in
theorem cost_firstNbr_le (a : V) (k : ℕ) (L : List V) (read : Finset V → ℕ) :
    (firstNbr a k L).cost read ≤ 3 + 3 * k := DTree.cost_le _ _

/-- The report loop costs one search per new report, plus one. -/
theorem reportLoop_cost (hinj : Function.Injective key) (coin : V → Bool) (ps : PubState V)
    {a : V} (hns : ¬ ∃ c, ps.lab a = some c ∧ coin c = true) {k : ℕ}
    (hk : Fintype.card V ≤ 2 ^ k) :
    ∀ (fuel : ℕ) (X : Finset V), X ⊆ reportsOf key coin (semOf G ps) a →
      (reportLoop key ps a ((minNbr key a (toSamp coin (semOf G ps) a))) k fuel X
        (selX (key := key) (semOf G ps) a X)).cost G.out ≤
        (3 + 3 * k) * ((reportsOf key coin (semOf G ps) a).card - X.card + 1) := by
  set st := semOf G ps
  set R := reportsOf key coin st a
  set σ := minNbr key a (toSamp coin st a)
  intro fuel
  induction fuel with
  | zero => intro X _; simp [reportLoop]
  | succ fuel ih =>
      intro X hX
      have haX : a ∉ repCand key ps a σ X := by simp [repCand]
      obtain ⟨-, hsome⟩ := firstNbr_sortKey (key := key) G haX hk
      simp only [reportLoop, dcost_cast, dcost_bind]
      have hc := cost_firstNbr_le a k (sortKey key a (repCand key ps a σ X)) G.out
      cases hr : (firstNbr a k (sortKey key a (repCand key ps a σ X))).eval G.out with
      | none =>
          simp only [dcost_pure, add_zero]
          exact hc.trans (Nat.le_mul_of_pos_right _ (by omega))
      | some r =>
          obtain ⟨u, m⟩ := r
          simp only
          obtain ⟨huc, hpos, -, hmin⟩ := hsome u m hr
          simp only [repCand, mem_filter, mem_univ, true_and] at huc
          obtain ⟨-, hres, ⟨D, hlab, hDX⟩, hσ⟩ := huc
          have hgetD : (ps.lab u).getD u = D := by rw [hlab]; rfl
          have huD : u ∈ toClus st a D := mem_toClus_semOf.mpr ⟨hpos, hres, hlab⟩
          have hminD : minNbr key a (toClus st a D) = some u := by
            refine minNbr_eq_of_min hinj huD fun v hv => ?_
            by_contra hlt
            push Not at hlt
            obtain ⟨hvpos, hvres, hvlab⟩ := mem_toClus_semOf.mp hv
            have hvc : v ∈ repCand key ps a σ X := by
              simp only [repCand, mem_filter, mem_univ, true_and]
              refine ⟨fun h => ?_, hvres, ⟨D, hvlab, hDX⟩, fun z hz => (hlt.le.trans (hσ z hz))⟩
              subst h; simp at hvpos
            exact absurd (hmin v hvc hvpos) (not_le.mpr hlt)
          have hDR : D ∈ R :=
            mem_filter.mpr ⟨mem_univ _, fun ⟨c, hc, hcoin⟩ => hns ⟨c, hc, hcoin⟩, u, hminD,
              fun z hz => hσ z hz⟩
          rw [hgetD]
          have hsel : insert s(a, u) (selX (key := key) st a X) =
              selX (key := key) st a (insert D X) := by
            ext f
            simp only [selX, mem_insert, mem_filter, mem_univ, true_and]
            constructor
            · rintro (rfl | ⟨D', hD', y, hy, rfl⟩)
              · exact ⟨D, Or.inl rfl, u, hminD, rfl⟩
              · exact ⟨D', Or.inr hD', y, hy, rfl⟩
            · rintro ⟨D', rfl | hD', y, hy, rfl⟩
              · rw [hminD] at hy; cases hy; exact Or.inl rfl
              · exact Or.inr ⟨D', hD', y, hy, rfl⟩
          rw [hsel]
          have hrec := ih (insert D X) (insert_subset hDR hX)
          rw [card_insert_of_notMem hDX] at hrec
          have hXR : X.card + 1 ≤ R.card := by
            have := card_lt_card (ssubset_of_subset_of_ne hX fun h => hDX (h ▸ hDR))
            omega
          calc _ ≤ (3 + 3 * k) + (3 + 3 * k) * (R.card - (X.card + 1) + 1) := add_le_add hc hrec
            _ = (3 + 3 * k) * (R.card - X.card + 1) := by
                rw [show R.card - X.card + 1 = (R.card - (X.card + 1) + 1) + 1 by omega]; ring

/-- **One vertex costs at most `(3 + 3k)(reports + 2)` queries.** -/
theorem vertexQ_cost (hinj : Function.Injective key) (coin : V → Bool) (ps : PubState V)
    (a : V) {k : ℕ} (hk : Fintype.card V ≤ 2 ^ k) :
    (vertexQ key coin ps a k).cost G.out ≤
      (3 + 3 * k) * ((reportsOf key coin (semOf G ps) a).card + 2) := by
  unfold vertexQ
  split_ifs with hs
  · simp
  · have hna : a ∉ sampCand coin ps a := by simp [sampCand]
    obtain ⟨hnone, hsome⟩ := firstNbr_sortKey (key := key) G hna hk
    have hfa : ((firstNbr a k (sortKey key a (sampCand coin ps a))).eval G.out).map Prod.fst =
        minNbr key a (toSamp coin (semOf G ps) a) := by
      cases hr : (firstNbr a k (sortKey key a (sampCand coin ps a))).eval G.out with
      | none =>
          have hemp : toSamp coin (semOf G ps) a = ∅ := by
            ext u
            simp only [Finset.notMem_empty, iff_false]
            intro hu
            obtain ⟨huc, hpos⟩ := mem_toSamp_semOf.mp hu
            have := (hnone.mp hr) u huc; omega
          rw [hemp, minNbr_eq_none key rfl]; rfl
      | some r =>
          obtain ⟨z, m⟩ := r
          obtain ⟨hzc, hzpos, -, hzmin⟩ := hsome z m hr
          symm
          refine minNbr_eq_of_min hinj (mem_toSamp_semOf.mpr ⟨hzc, hzpos⟩) fun u hu => ?_
          obtain ⟨huc, hupos⟩ := mem_toSamp_semOf.mp hu
          exact hzmin u huc hupos
    simp only [dcost_cast, dcost_bind, dcost_map, hfa]
    have hsel0 : (∅ : Finset (Sym2 V)) = selX (key := key) (semOf G ps) a ∅ := by
      ext f; simp [selX]
    rw [hsel0]
    have h1 := cost_firstNbr_le a k (sortKey key a (sampCand coin ps a)) G.out
    have h2 := reportLoop_cost (G := G) hinj coin ps hs hk (Fintype.card V) ∅ (empty_subset _)
    simp only [card_empty, Nat.sub_zero] at h2
    calc _ ≤ (3 + 3 * k) + (3 + 3 * k) * ((reportsOf key coin (semOf G ps) a).card + 1) :=
          add_le_add h1 h2
      _ = _ := by ring

theorem phaseLoop_cost (hinj : Function.Injective key) (coin : V → Bool) (ps : PubState V)
    {k : ℕ} (hk : Fintype.card V ≤ 2 ^ k) (vs : List V) :
    (phaseLoop key coin ps k vs).cost G.out ≤
      (3 + 3 * k) * (vs.map fun a => (reportsOf key coin (semOf G ps) a).card + 2).sum := by
  induction vs with
  | nil => simp [phaseLoop]
  | cons a vs ih =>
      simp only [phaseLoop, dcost_cast, dcost_bind, dcost_map, List.map_cons, List.sum_cons]
      have := vertexQ_cost (G := G) hinj coin ps a hk
      calc _ ≤ (3 + 3 * k) * ((reportsOf key coin (semOf G ps) a).card + 2) +
            (3 + 3 * k) * (vs.map fun a => (reportsOf key coin (semOf G ps) a).card + 2).sum :=
            add_le_add this ih
        _ = _ := by ring

/-- **One phase costs at most `(3 + 3k)(reports + 2n)` queries.** -/
theorem phaseQ_cost (hinj : Function.Injective key) (coin : V → Bool) (ps : PubState V)
    {k : ℕ} (hk : Fintype.card V ≤ 2 ^ k) :
    (phaseQ key coin ps k).cost G.out ≤
      (3 + 3 * k) * (totalReports key coin (semOf G ps) + 2 * Fintype.card V) := by
  simp only [phaseQ, dcost_cast, dcost_map]
  refine (phaseLoop_cost hinj coin ps hk _).trans (Nat.mul_le_mul_left _ (le_of_eq ?_))
  rw [List.sum_map_add, totalReports]
  rw [Finset.sum_map_toList, Finset.sum_map_toList]
  simp [mul_comm]

/-- The first `j` phases cost at most `(3 + 3k)` per search. -/
theorem phasesQ_cost (hinj : Function.Injective key) (coins : ℕ → V → Bool) {k : ℕ}
    (hk : Fintype.card V ≤ 2 ^ k) (P : Sym2 V → Bool) :
    ∀ j, (phasesQ key coins k (ps0 P) j).cost G.out ≤
      (3 + 3 * k) * (∑ i ∈ range j, totalReports key (coins i)
        (runPhases key coins (support G P) i) + j * (2 * Fintype.card V))
  | 0 => by simp [phasesQ]
  | j + 1 => by
      simp only [phasesQ, dcost_cast, dcost_bind]
      have h1 := phasesQ_cost hinj coins hk P j
      have h2 := phaseQ_cost (G := G) hinj (coins j)
        ((phasesQ key coins k (ps0 P) j).eval G.out) hk
      rw [phasesQ_correct hinj coins hk P j] at h2
      rw [sum_range_succ]
      calc _ ≤ _ := add_le_add h1 h2
        _ = _ := by ring

/-- **A trial costs at most `(3 + 3k)(trial reports + 2n(K + 1))` queries.** -/
theorem trialQ_cost (hinj : Function.Injective key) {K : ℕ} (cs : Fin K → V → Bool) {k : ℕ}
    (hk : Fintype.card V ≤ 2 ^ k) (P : Sym2 V → Bool) :
    (trialQ key cs k P).cost G.out ≤
      (3 + 3 * k) * (trialReports key (support G P) cs + 2 * Fintype.card V * (K + 1)) := by
  simp only [trialQ, dcost_bind, dcost_map]
  have h1 := phasesQ_cost (G := G) hinj (extCoins cs) hk P K
  have h2 := phaseQ_cost (G := G) hinj (fun _ => false)
    ((phasesQ key (extCoins cs) k (ps0 P) K).eval G.out) hk
  rw [phasesQ_correct hinj (extCoins cs) hk P K] at h2
  have hsum : ∑ i ∈ range K, totalReports key (extCoins cs i)
      (runPhases key (extCoins cs) (support G P) i) =
      ∑ j : Fin K, totalReports key (extCoins cs j) (runPhases key (extCoins cs) (support G P) j) :=
    (Fin.sum_univ_eq_sum_range (fun i => totalReports key (extCoins cs i)
      (runPhases key (extCoins cs) (support G P) i)) K).symm
  rw [hsum] at h1
  calc _ ≤ _ := add_le_add h1 h2
    _ = _ := by simp only [trialReports]; ring

end

end Spanner
end CutQueryComplexity
