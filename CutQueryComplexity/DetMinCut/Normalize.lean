import CutQueryComplexity.Discovery.Normalization
import CutQueryComplexity.Problem.Basic
import CutQueryComplexity.Search.BinarySearch

/-! # The current quotient and degree normalization (Lemma 27)

The current quotient of the input is kept as a representative map `r : V → V` on the
original vertices. Its classes are the image of `r` (`Cls r`), and `proj r` sends a vertex to
its class. A query to the quotient `G.contract (proj r)` is one original query on a union of
classes.

The normalization state also records the known class degrees `deg`, a witnessed bound `U`,
and its witness shore `wit`. The invariant `Inv` says that the degrees are exact, the witness
is a proper union of classes with value `U`, `U` is at most every class degree, and some
minimum cut of `G` is a union of classes.

`normalize` repeatedly finds, for a class `v` with `d_v > (N − 1) U`, a neighbor class `u`
with `w(u, v) > U` (`heavyNeighbor`, at most `2⌈log₂(N − 1)⌉` queries), queries the cut of
`u ∪ v` (one query), and merges `u` into `v`. No cut of value at most `U` separates them, so
the invariant survives. `normalize_spec` proves that at the end `U ≤ 0` or every class degree
is at most `(N' − 1) U'`, with at most `(2⌈log₂ n⌉ + 1)(N − N')` queries.
-/

namespace CutQueryComplexity
namespace DetMinCut

open WeightedGraph Search Search.Comp Discovery Finset

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ## Classes of a representative map -/

/-- The classes of `r`: its image. -/
abbrev Cls (r : V → V) := {c : V // c ∈ univ.image r}

/-- The class of a vertex. -/
def proj (r : V → V) (x : V) : Cls r := ⟨r x, mem_image_of_mem r (mem_univ x)⟩

theorem proj_surjective (r : V → V) : Function.Surjective (proj r) := by
  rintro ⟨c, hc⟩
  obtain ⟨x, -, rfl⟩ := mem_image.mp hc
  exact ⟨x, rfl⟩

theorem proj_eq_iff {r : V → V} {x y : V} : proj r x = proj r y ↔ r x = r y := by
  simp [proj, Subtype.ext_iff]

theorem card_cls (r : V → V) : Fintype.card (Cls r) = (univ.image r).card :=
  Fintype.card_coe _

/-- The vertices of a class. -/
theorem fiber_proj (r : V → V) (c : Cls r) :
    fiber (proj r) c = univ.filter fun x => r x = c.val := by
  ext x; simp [proj, Subtype.ext_iff]

/-- A shore is a union of classes. -/
def Sat (r : V → V) (S : Finset V) : Prop := ∀ x y, r x = r y → (x ∈ S ↔ y ∈ S)

theorem sat_pull (r : V → V) (T : Finset (Cls r)) : Sat r (pull (proj r) T) := by
  intro x y hxy
  simp only [mem_pull, proj_eq_iff.mpr hxy]

theorem pull_image_of_sat {r : V → V} {S : Finset V} (hS : Sat r S) :
    pull (proj r) (S.image (proj r)) = S :=
  pull_image_of_saturated (proj r) fun x y h => hS x y (proj_eq_iff.mp h)

/-- The quotient graph. -/
abbrev quot (G : WeightedGraph V) (r : V → V) : WeightedGraph (Cls r) := G.contract (proj r)

theorem quot_degree (G : WeightedGraph V) (r : V → V) (c : Cls r) :
    (quot G r).degree c = G.cut (univ.filter fun x => r x = c.val) := by
  rw [contract_degree, fiber_proj]

/-- A proper union of classes forces at least two classes. -/
theorem two_le_card_cls {r : V → V} {S : Finset V} (hS : Sat r S) (hp : ProperShore S) :
    2 ≤ Fintype.card (Cls r) := by
  obtain ⟨x, hx⟩ := hp.1
  obtain ⟨y, hy⟩ : ∃ y, y ∉ S := by
    by_contra h; push Not at h; exact hp.2 (eq_univ_of_forall h)
  have hne : proj r x ≠ proj r y := fun h => hy ((hS x y (proj_eq_iff.mp h)).mp hx)
  exact Fintype.one_lt_card_iff.mpr ⟨_, _, hne⟩

/-! ## Merging two classes -/

/-- Merge the class `u` into the class `v`. -/
def mergeR (r : V → V) (u v : V) : V → V := fun x => if r x = u then v else r x

omit [Fintype V] in
theorem mergeR_of_eq {r : V → V} {u v : V} {x y : V} (h : r x = r y) :
    mergeR r u v x = mergeR r u v y := by
  simp only [mergeR, h]

omit [Fintype V] in
/-- A union of classes that does not separate `u` from `v` is a union of merged classes. -/
theorem sat_mergeR {r : V → V} {u v : V} {S : Finset V} (hS : Sat r S)
    (huv : ∀ x y, r x = u → r y = v → (x ∈ S ↔ y ∈ S)) : Sat (mergeR r u v) S := by
  intro x y hxy
  simp only [mergeR] at hxy
  by_cases hx : r x = u <;> by_cases hy : r y = u <;> simp only [hx, hy, ite_true, ite_false] at hxy
  · exact hS x y (hx.trans hy.symm)
  · exact huv x y hx hxy.symm
  · exact (huv y x hy hxy).symm
  · exact hS x y hxy

theorem image_mergeR {r : V → V} {u v : V} (_hu : u ∈ univ.image r) (hv : v ∈ univ.image r)
    (huv : u ≠ v) : univ.image (mergeR r u v) = (univ.image r).erase u := by
  ext c
  simp only [mem_image, mem_univ, true_and, mem_erase, mergeR]
  constructor
  · rintro ⟨x, rfl⟩
    by_cases hx : r x = u
    · simp only [hx, ite_true]; exact ⟨Ne.symm huv, by simpa using hv⟩
    · simp only [hx, ite_false]; exact ⟨hx, x, rfl⟩
  · rintro ⟨hcu, x, rfl⟩
    exact ⟨x, by simp [hcu]⟩

theorem card_cls_mergeR {r : V → V} {u v : V} (hu : u ∈ univ.image r) (hv : v ∈ univ.image r)
    (huv : u ≠ v) : Fintype.card (Cls (mergeR r u v)) = Fintype.card (Cls r) - 1 := by
  rw [card_cls, card_cls, image_mergeR hu hv huv, card_erase_of_mem hu]

theorem filter_mergeR_v {r : V → V} {u v : V} :
    (univ.filter fun x => mergeR r u v x = v) =
      univ.filter fun x => r x = u ∨ r x = v := by
  ext x; simp only [mem_filter, mem_univ, true_and, mergeR]
  by_cases hx : r x = u <;> simp [hx]

theorem filter_mergeR_ne {r : V → V} {u v c : V} (hcu : c ≠ u) (hcv : c ≠ v) :
    (univ.filter fun x => mergeR r u v x = c) = univ.filter fun x => r x = c := by
  ext x
  rw [Finset.mem_filter, Finset.mem_filter]
  simp only [mem_univ, true_and, mergeR]
  by_cases hx : r x = u
  · rw [ite_eq_left hx]
    exact ⟨fun h => absurd h.symm hcv, fun h => absurd (h.symm.trans hx) hcu⟩
  · rw [ite_eq_right hx]

/-! ## The normalization state and its invariant -/

/-- A normalization state. -/
structure St (V : Type) where
  r : V → V
  deg : V → ℝ
  U : ℝ
  wit : Finset V

/-- The invariant of the current quotient on the genuine graph `G`. -/
structure Inv (G : WeightedGraph V) (st : St V) : Prop where
  deg : ∀ c : Cls st.r, st.deg c.val = G.cut (univ.filter fun x => st.r x = c.val)
  wit_sat : Sat st.r st.wit
  wit_proper : ProperShore st.wit
  wit_val : G.cut st.wit = st.U
  U_le : ∀ c : Cls st.r, st.U ≤ st.deg c.val
  opt : ∃ S, IsMinCut G S ∧ Sat st.r S

theorem Inv.quot_degree {G : WeightedGraph V} {st : St V} (h : Inv G st) :
    (fun c : Cls st.r => st.deg c.val) = (quot G st.r).degree := by
  funext c; rw [h.deg c, DetMinCut.quot_degree]

theorem Inv.two_le {G : WeightedGraph V} {st : St V} (h : Inv G st) :
    2 ≤ Fintype.card (Cls st.r) := two_le_card_cls h.wit_sat h.wit_proper

theorem Inv.lam_le {G : WeightedGraph V} {st : St V} (h : Inv G st) :
    mincutValue G ≤ st.U := h.wit_val ▸ mincutValue_le G h.wit_proper

/-! ## The normalization program -/

/-- The state after merging the class `u` into `v`, with `duv` the cut of their union. -/
noncomputable def mergeSt (st : St V) (u v : Cls st.r) (duv : ℝ) : St V :=
  ⟨mergeR st.r u.val v.val, Function.update st.deg v.val duv, min st.U duv,
    if duv < st.U then pull (proj st.r) {u, v} else st.wit⟩


/-- **Degree normalization.** -/
noncomputable def normalize : ℕ → St V → Comp (Finset V) ℝ (St V)
  | 0, st => .pure st
  | fuel + 1, st =>
    if hc : 0 < st.U ∧ ∃ c : Cls st.r, ((Fintype.card (Cls st.r) : ℝ) - 1) * st.U < st.deg c.val
    then
      (mapQ (pull (proj st.r)) (heavyNeighbor (Classical.choose hc.2)
          (st.deg (Classical.choose hc.2).val))).bind fun u =>
        if u = Classical.choose hc.2 then .pure st else
        (ask (pull (proj st.r) {u, Classical.choose hc.2})).bind fun duv =>
          normalize fuel (mergeSt st u (Classical.choose hc.2) duv)
    else .pure st

/-- The stopping condition of normalization. -/
def Stopped (st : St V) : Prop :=
  st.U ≤ 0 ∨ ∀ c : Cls st.r, st.deg c.val ≤ ((Fintype.card (Cls st.r) : ℝ) - 1) * st.U

/-- Two classes joined by an edge heavier than `U` are not separated by any union of classes
of value at most `U`. -/
theorem not_separated_cls (G : WeightedGraph V) {r : V → V} {u v : Cls r} {U : ℝ}
    (hheavy : U < (quot G r).w v u) {S : Finset V} (hS : Sat r S) (hSU : G.cut S ≤ U) :
    ∀ x y, r x = u.val → r y = v.val → (x ∈ S ↔ y ∈ S) := by
  intro x y hx hy
  set T := S.image (proj r)
  have hT : pull (proj r) T = S := pull_image_of_sat hS
  have hcut : (quot G r).cut T ≤ U := by rw [cut_contract, hT]; exact hSU
  have key := not_separated_of_heavy (quot G r) hcut hheavy
  have hpx : proj r x = u := Subtype.ext hx
  have hpy : proj r y = v := Subtype.ext hy
  rw [← hT, mem_pull, mem_pull, hpx, hpy]
  exact key.symm

theorem pull_pair_eq (r : V → V) (u v : Cls r) :
    pull (proj r) {u, v} = univ.filter fun x => r x = u.val ∨ r x = v.val := by
  ext x
  simp only [mem_pull, mem_insert, mem_singleton, mem_filter, mem_univ, true_and, Subtype.ext_iff]
  exact Iff.rfl

/-- One merge preserves the invariant. -/
theorem inv_merge (G : WeightedGraph V) {st : St V} (hI : Inv G st) {u v : Cls st.r}
    (huv : u ≠ v) (hheavy : st.U < (quot G st.r).w v u) :
    Inv G (mergeSt st u v (G.cut (pull (proj st.r) {u, v}))) := by
  have huv' : u.val ≠ v.val := fun h => huv (Subtype.ext h)
  have hns : ∀ {S : Finset V}, Sat st.r S → G.cut S ≤ st.U →
      ∀ x y, st.r x = u.val → st.r y = v.val → (x ∈ S ↔ y ∈ S) :=
    fun hS hSU => not_separated_cls G hheavy hS hSU
  have hwitM : Sat (mergeR st.r u.val v.val) st.wit :=
    sat_mergeR hI.wit_sat (hns hI.wit_sat (le_of_eq hI.wit_val))
  have hmemP : ∀ x, x ∈ pull (proj st.r) {u, v} ↔ mergeR st.r u.val v.val x = v.val := by
    intro x
    rw [pull_pair_eq]
    simp only [mem_filter, mem_univ, true_and, mergeR]
    by_cases hx : st.r x = u.val
    · simp [hx]
    · rw [ite_eq_right hx]; simp [hx]
  have hPsat : Sat (mergeR st.r u.val v.val) (pull (proj st.r) {u, v}) := by
    intro x y hxy; rw [hmemP, hmemP, hxy]
  have himg := image_mergeR u.2 v.2 huv' (r := st.r)
  unfold mergeSt
  constructor
  · -- exact degrees
    rintro ⟨c, hc⟩
    dsimp only
    rw [himg, mem_erase] at hc
    by_cases hcv : c = v.val
    · subst hcv
      rw [Function.update_self, filter_mergeR_v, pull_pair_eq]
    · rw [Function.update_of_ne hcv, filter_mergeR_ne hc.1 hcv]
      exact hI.deg ⟨c, hc.2⟩
  · -- the witness is a union of classes
    dsimp only
    split_ifs
    · exact hPsat
    · exact hwitM
  · -- the witness is proper
    dsimp only
    split_ifs
    · refine ⟨?_, ?_⟩
      · obtain ⟨x, -, hx⟩ := mem_image.mp u.2
        exact ⟨x, by rw [pull_pair_eq]; simp [hx]⟩
      · intro hall
        obtain ⟨a, ha⟩ := hI.wit_proper.1
        obtain ⟨b, hb⟩ : ∃ b, b ∉ st.wit := by
          by_contra h; push Not at h; exact hI.wit_proper.2 (eq_univ_of_forall h)
        have hab : mergeR st.r u.val v.val a ≠ mergeR st.r u.val v.val b :=
          fun h => hb ((hwitM a b h).mp ha)
        have h1 := (hmemP a).mp (by rw [hall]; exact mem_univ a)
        have h2 := (hmemP b).mp (by rw [hall]; exact mem_univ b)
        exact hab (h1.trans h2.symm)
    · exact hI.wit_proper
  · -- the witnessed value
    dsimp only
    split_ifs with h
    · exact (min_eq_right h.le).symm
    · rw [hI.wit_val]; exact (min_eq_left (not_lt.mp h)).symm
  · -- the bound is at most every degree
    rintro ⟨c, hc⟩
    dsimp only
    rw [himg, mem_erase] at hc
    by_cases hcv : c = v.val
    · subst hcv; rw [Function.update_self]; exact min_le_right _ _
    · rw [Function.update_of_ne hcv]
      exact (min_le_left _ _).trans (hI.U_le ⟨c, hc.2⟩)
  · -- some minimum cut survives
    obtain ⟨S, hS, hSsat⟩ := hI.opt
    have hSU : G.cut S ≤ st.U := by
      have : G.cut S ≤ mincutValue G := by
        rw [mincutValue, dite_eq_left ⟨S, (mem_properShores S).mpr hS.1⟩]
        exact le_inf' _ _ fun T hT => hS.2 T ((mem_properShores T).mp hT)
      exact this.trans hI.lam_le
    exact ⟨S, hS, sat_mergeR hSsat (hns hSsat hSU)⟩

/-- **Lemma 27.** Normalization keeps the invariant, never increases the bound, refines the
classes, and stops with `U ≤ 0` or all class degrees at most `(N' − 1) U'`. With
`c = 2⌈log₂ n⌉ + 1`, its cost plus `c N'` is at most `c N`. -/
theorem normalize_spec (G : WeightedGraph V) :
    ∀ (fuel : ℕ) (st : St V), Inv G st → Fintype.card (Cls st.r) ≤ fuel + 1 →
      Inv G ((normalize fuel st).eval G.cut) ∧ ((normalize fuel st).eval G.cut).U ≤ st.U ∧
      Stopped ((normalize fuel st).eval G.cut) ∧
      (∀ x y, st.r x = st.r y →
        ((normalize fuel st).eval G.cut).r x = ((normalize fuel st).eval G.cut).r y) ∧
      Fintype.card (Cls ((normalize fuel st).eval G.cut).r) ≤ Fintype.card (Cls st.r) ∧
      (normalize fuel st).cost G.cut +
          (2 * Nat.clog 2 (Fintype.card V) + 1) *
            Fintype.card (Cls ((normalize fuel st).eval G.cut).r) ≤
        (2 * Nat.clog 2 (Fintype.card V) + 1) * Fintype.card (Cls st.r) := by
  intro fuel
  induction fuel with
  | zero =>
      intro st hI hN
      have := hI.two_le; omega
  | succ fuel ih =>
      intro st hI hN
      by_cases hc : 0 < st.U ∧
          ∃ c : Cls st.r, ((Fintype.card (Cls st.r) : ℝ) - 1) * st.U < st.deg c.val
      swap
      · simp only [normalize, dite_eq_right hc, eval_pure, cost_pure, zero_add]
        refine ⟨hI, le_rfl, ?_, fun _ _ h => h, le_rfl, le_rfl⟩
        unfold Stopped
        by_contra hst; push Not at hst
        obtain ⟨h1, c, hcU⟩ := hst
        exact hc ⟨h1, c, hcU⟩
      set v := Classical.choose hc.2 with hvdef
      have hv : ((Fintype.card (Cls st.r) : ℝ) - 1) * st.U < st.deg v.val :=
        Classical.choose_spec hc.2
      have hdeg : st.deg v.val = (quot G st.r).degree v := congrFun hI.quot_degree v
      have hcutq : G.cut ∘ pull (proj st.r) = (quot G st.r).cut := by
        funext T; exact (cut_contract G (proj st.r) T).symm
      obtain ⟨hne, hheavy, hcost⟩ := heavyNeighbor_spec (quot G st.r) v (U := st.U)
        (by rw [← hdeg]; exact hv)
      simp only [normalize, dite_eq_left hc, ← hvdef, eval_bind, cost_bind, eval_mapQ,
        cost_mapQ, hcutq, hdeg]
      set u := (heavyNeighbor v ((quot G st.r).degree v)).eval (quot G st.r).cut
      rw [ite_eq_right hne]
      simp only [eval_bind, cost_bind, eval_ask, cost_ask]
      have huv : u ≠ v := hne
      have huv' : u.val ≠ v.val := fun h => huv (Subtype.ext h)
      have hI1 := inv_merge G hI huv hheavy
      have hN1 : Fintype.card (Cls (mergeSt st u v (G.cut (pull (proj st.r) {u, v}))).r) =
          Fintype.card (Cls st.r) - 1 := card_cls_mergeR u.2 v.2 huv'
      have h2 := hI.two_le
      obtain ⟨hI', hU', hst', href', hcard', hcost'⟩ := ih _ hI1 (le_of_eq_of_le hN1 (by omega))
      have hcard'' := hcard'.trans (le_of_eq hN1)
      have hcost'' := hcost'.trans (le_of_eq (congrArg (fun x => (2 * Nat.clog 2 (Fintype.card V) + 1) * x) hN1))
      refine ⟨hI', hU'.trans (by simp only [mergeSt]; exact min_le_left _ _), hst', fun x y h => href' x y (mergeR_of_eq (u := u.val) (v := v.val) h), ?_, ?_⟩
      · omega
      · have hlog : Nat.clog 2 (Fintype.card (Cls st.r) - 1) ≤ Nat.clog 2 (Fintype.card V) := by
          apply Nat.clog_mono_right
          have : Fintype.card (Cls st.r) ≤ Fintype.card V := by
            rw [card_cls]; exact card_image_le.trans (by simp)
          omega
        have : (Fintype.card (Cls st.r) - 1) + 1 = Fintype.card (Cls st.r) := by omega
        have e : (2 * Nat.clog 2 (Fintype.card V) + 1) * Fintype.card (Cls st.r) =
            (2 * Nat.clog 2 (Fintype.card V) + 1) * (Fintype.card (Cls st.r) - 1) +
              (2 * Nat.clog 2 (Fintype.card V) + 1) := by
          rw [← Nat.mul_succ, Nat.succ_eq_add_one, this]
        omega

end DetMinCut
end CutQueryComplexity
