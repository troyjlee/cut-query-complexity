import CutQueryComplexity.Discovery.Centers
import CutQueryComplexity.Search.Combinators

/-! # Bucketed center selection: the adaptive program (Lemma 30)

The residual `R = G - K` is fixed, with `K ≤ G` explicit and the degrees `d_v` of `G`
known, so the residual degrees `r_v = d_v - deg_K(v)` are known (`knownDeg`). The state
holds the center set `C` and the learned residual rows of the centers. Every quantity
that decides the active set and the buckets reads only `w_R(v, c)` for `c ∈ C`
(`active_congr`, `bucket_congr`, ...), so the program computes them from the learned rows.

One selection (`selectStep`) evaluates surrogate group totals by `eq:bucketed-score` and
`overlapMass` (`groupScore`, six queries per bucket), runs `avgSearch` over `V \ C`, and
learns the chosen row with `N - 1` queries (`learnRow`). `selectStep_spec` shows that the
new center `u ∉ C` has `k Φ ≤ 8 N σ(u)`, hence `Φ` shrinks by the factor `1 - k/(8N)`.

`centerSelection_spec` is Lemma 30: after at most `F = ⌈(8N/k) ln (2N)⌉` selections
(`F < (8N/k) ln (2N) + 1`) no vertex is active, which is the coverage property
`eq:center-coverage`, using at most `F (6 (M + 1)(⌈log₂ N⌉ + 1) + N - 1)` cut queries,
where `M + 1` bounds the number of buckets (`2 D ≤ t 2^M`, all `r_v ≤ D`).
`centerSelection_normalized` takes `D = (N - 1) U`, `t = U / (16 N²)` and
`M = 5 + 3 ⌈log₂ N⌉`, giving `O((N² / k) log (2N))`.
-/

namespace CutQueryComplexity
namespace Discovery

open Search Search.Comp WeightedGraph Finset

variable {V : Type} [Fintype V] [DecidableEq V]

section Congr

variable {t : ℝ} {k : ℕ} {r : V → ℝ} {ω ω' : V → V → ℝ} {C : Finset V}

omit [Fintype V] [DecidableEq V] in
theorem pot_congr (h : ∀ v, ∀ c ∈ C, ω v c = ω' v c) (v : V) :
    pot k r ω C v = pot k r ω' C v :=
  prod_congr rfl fun c hc => by simp [coef, h v c hc]

omit [Fintype V] [DecidableEq V] in
theorem bmass_congr (h : ∀ v, ∀ c ∈ C, ω v c = ω' v c) (v : V) :
    bmass ω C v = bmass ω' C v :=
  sum_congr rfl fun c hc => h v c hc

omit [DecidableEq V] in
theorem active_congr (h : ∀ v, ∀ c ∈ C, ω v c = ω' v c) :
    active t k r ω C = active t k r ω' C := by
  ext v; simp [mem_active, IsActive, bmass_congr h]

omit [Fintype V] [DecidableEq V] in
theorem bucketOf_congr (h : ∀ v, ∀ c ∈ C, ω v c = ω' v c) (v : V) :
    bucketOf k r ω C v = bucketOf k r ω' C v := by
  simp [bucketOf, theta, pot_congr h]

omit [DecidableEq V] in
theorem buckets_congr (h : ∀ v, ∀ c ∈ C, ω v c = ω' v c) :
    buckets t k r ω C = buckets t k r ω' C := by
  simp only [buckets, active_congr h, funext (bucketOf_congr h)]

omit [DecidableEq V] in
theorem bucket_congr (h : ∀ v, ∀ c ∈ C, ω v c = ω' v c) (j : ℤ) :
    bucket t k r ω C j = bucket t k r ω' C j := by
  simp only [bucket, active_congr h, funext (bucketOf_congr h)]

end Congr

/-- The state: centers and their learned residual rows. -/
structure CenterState (V : Type) where
  C : Finset V
  rows : V → V → ℝ

/-- The known row weights `w(v, c) = rows c v`; only `c ∈ C` is ever used. -/
def knownW (st : CenterState V) : V → V → ℝ := fun v c => st.rows c v

/-- The known residual degrees. -/
noncomputable def knownDeg (d : V → ℝ) (K : WeightedGraph V) (v : V) : ℝ := d v - K.degree v

/-- The surrogate total `∑_{u ∈ W} σ̃(u)`, by `eq:bucketed-score` and six queries per bucket. -/
noncomputable def groupScore (d : V → ℝ) (K : WeightedGraph V) (t : ℝ) (k : ℕ)
    (st : CenterState V) (W : Finset V) : Comp (Finset V) ℝ ℝ :=
  (mapList (fun j => (overlapMass (knownDeg d K) K
      (bucket t k (knownDeg d K) (knownW st) st.C j) W).map fun x => (2 : ℝ) ^ j * x)
    (buckets t k (knownDeg d K) (knownW st) st.C).toList).map fun xs => k / 2 * xs.sum

/-- Learn the residual weights from `u` to the listed vertices, one query each. -/
noncomputable def learnRow (d : V → ℝ) (K : WeightedGraph V) (u : V) :
    List V → Comp (Finset V) ℝ (V → ℝ)
  | [] => Comp.pure 0
  | x :: xs => (ask {u, x}).bind fun a => (learnRow d K u xs).map fun g y =>
      if y = x then (d u + d x - a) / 2 - K.w u x else g y

/-- One selection: a vertex of above-average surrogate score becomes a center. -/
noncomputable def selectStep (d : V → ℝ) (K : WeightedGraph V) (t : ℝ) (k : ℕ) (v₀ : V)
    (st : CenterState V) : Comp (Finset V) ℝ (CenterState V) :=
  (groupScore d K t k st st.Cᶜ).bind fun m =>
    (avgSearch (groupScore d K t k st) v₀ (st.Cᶜ).toList m).bind fun u =>
      (learnRow d K u (univ.erase u).toList).map fun row =>
        { C := insert u st.C, rows := Function.update st.rows u row }

open scoped Classical in
/-- Select centers while some vertex is active, for at most `fuel` selections. -/
noncomputable def centerLoop (d : V → ℝ) (K : WeightedGraph V) (t : ℝ) (k : ℕ) :
    ℕ → CenterState V → Comp (Finset V) ℝ (CenterState V)
  | 0, st => Comp.pure st
  | fuel + 1, st =>
      if h : (active t k (knownDeg d K) (knownW st) st.C).Nonempty then
        (selectStep d K t k h.choose st).bind (centerLoop d K t k fuel)
      else Comp.pure st

/-- The selection budget `F = ⌈(8N/k) ln (2N)⌉`. -/
noncomputable def selectionBudget (N k : ℕ) : ℕ := ⌈8 * N / k * Real.log (2 * N)⌉₊

/-- Bucketed center selection. -/
noncomputable def centerSelection (d : V → ℝ) (K : WeightedGraph V) (t : ℝ) (k : ℕ) :
    Comp (Finset V) ℝ (CenterState V) :=
  centerLoop d K t k (selectionBudget (Fintype.card V) k) ⟨∅, fun _ _ => 0⟩

section Proofs

variable (G K : WeightedGraph V) (hKG : ∀ u v, K.w u v ≤ G.w u v)
include hKG

theorem knownDeg_eq (v : V) : knownDeg G.degree K v = (G.subtract K).degree v := by
  rw [degree_subtract G K hKG]; rfl

theorem groupScore_spec {t : ℝ} {k : ℕ} {st : CenterState V}
    (hrows : ∀ c ∈ st.C, ∀ x, st.rows c x = (G.subtract K).w c x) (W : Finset V) :
    (groupScore G.degree K t k st W).eval G.cut =
        ∑ u ∈ W, rscore t k (G.subtract K).degree (G.subtract K).w st.C u ∧
      (groupScore G.degree K t k st W).cost G.cut ≤
        6 * (buckets t k (G.subtract K).degree (G.subtract K).w st.C).card := by
  set R := G.subtract K
  have hr : knownDeg G.degree K = R.degree := funext (knownDeg_eq G K hKG)
  have hω : ∀ v, ∀ c ∈ st.C, knownW st v c = R.w v c := fun v c hc => by
    simp [knownW, hrows c hc v, R.symm c v]
  have hom : ∀ A W', (overlapMass R.degree K A W').eval G.cut = R.cross A W' ∧
      (overlapMass R.degree K A W').cost G.cut = 6 := by
    rw [← hr]; exact overlapMass_spec G K hKG (fun v => (knownDeg_eq G K hKG v))
  simp only [groupScore, eval_map, eval_mapList, cost_map, hr, buckets_congr hω,
    bucket_congr hω]
  refine ⟨?_, ?_⟩
  · rw [sum_rscore, Finset.sum_map_toList]
    congr 1
    exact sum_congr rfl fun j _ => by rw [(hom _ W).1]; rfl
  · calc _ ≤ 6 * (buckets t k R.degree R.w st.C).toList.length :=
          cost_mapList_le _ _ _ fun j _ => by rw [cost_map, (hom _ W).2]
      _ = _ := by rw [length_toList]

theorem learnRow_spec (u : V) :
    ∀ L : List V, L.Nodup → u ∉ L →
      (learnRow G.degree K u L).eval G.cut =
          (fun y => if y ∈ L then (G.subtract K).w u y else 0) ∧
        (learnRow G.degree K u L).cost G.cut = L.length
  | [], _, _ => by simp [learnRow]; rfl
  | x :: xs, hnd, hu => by
      have hux : u ≠ x := fun h => hu (h ▸ List.mem_cons_self)
      obtain ⟨he, hc⟩ := learnRow_spec u xs (List.nodup_cons.mp hnd).2
        (fun h => hu (List.mem_cons_of_mem _ h))
      simp only [learnRow, eval_bind, eval_ask, eval_map, cost_bind, cost_ask, cost_map, he, hc,
        List.length_cons]
      refine ⟨funext fun y => ?_, by omega⟩
      by_cases hy : y = x
      · subst hy
        simp only [↓reduceIte, List.mem_cons, true_or, subtract_w]
        rw [max_eq_right (sub_nonneg.mpr (hKG u y)), G.edge_eq_three_cuts hux,
          cut_singleton, cut_singleton]
      · simp [hy]

/-- One selection: the new center `u ∉ C` has `k Φ ≤ 8 N σ(u)`, all learned rows stay
exact, and at most `6B + 6B ⌈log₂ N⌉ + (N - 1)` queries are used, `B` the number of
buckets. -/
theorem selectStep_spec {t : ℝ} {k : ℕ} (ht : 0 ≤ t) (hk2 : 2 ≤ k)
    (hlight : ∀ v, (G.subtract K).degree v ≤ t ∨
      ∀ u, (G.subtract K).w v u ≤ (G.subtract K).degree v / k)
    {st : CenterState V} (hrows : ∀ c ∈ st.C, ∀ x, st.rows c x = (G.subtract K).w c x)
    {v₀ : V} (hv₀ : v₀ ∈ active t k (G.subtract K).degree (G.subtract K).w st.C) :
    ∃ u ∉ st.C, ((selectStep G.degree K t k v₀ st).eval G.cut).C = insert u st.C ∧
      (∀ c ∈ ((selectStep G.degree K t k v₀ st).eval G.cut).C, ∀ x,
        ((selectStep G.degree K t k v₀ st).eval G.cut).rows c x = (G.subtract K).w c x) ∧
      k * Phi t k (G.subtract K).degree (G.subtract K).w st.C ≤
        8 * Fintype.card V * score t k (G.subtract K).degree (G.subtract K).w st.C u ∧
      (selectStep G.degree K t k v₀ st).cost G.cut ≤
        6 * (buckets t k (G.subtract K).degree (G.subtract K).w st.C).card *
          (Nat.clog 2 (Fintype.card V) + 1) + (Fintype.card V - 1) := by
  have hgs := groupScore_spec G K hKG (t := t) (k := k) hrows
  set R := G.subtract K
  set B := (buckets t k R.degree R.w st.C).card
  have hk : 0 < k := by omega
  simp only [selectStep, eval_bind, cost_bind, eval_map, cost_map, (hgs _).1]
  set m := ∑ x ∈ st.Cᶜ, rscore t k R.degree R.w st.C x
  have hW : st.Cᶜ.toList ≠ [] := by
    intro h
    have : v₀ ∈ st.Cᶜ := mem_compl.mpr (mem_active.mp hv₀).1
    rw [← mem_toList, h] at this
    simp at this
  have hlen : (st.Cᶜ.toList.length : ℝ) = (st.Cᶜ.card : ℝ) := by rw [length_toList]
  have hcard : (0 : ℝ) < st.Cᶜ.card := by
    rw [← hlen]; exact_mod_cast List.length_pos_iff.mpr hW
  obtain ⟨hmem, hτ, hcs⟩ := avgSearch_spec G.cut (groupScore G.degree K t k st) v₀
    (rscore t k R.degree R.w st.C) (c := 6 * B) (fun X => (hgs X).1) (fun X => (hgs X).2)
    (m / st.Cᶜ.card) _ _ m le_rfl (nodup_toList _) hW (by rw [toList_toFinset])
    (by rw [hlen, div_mul_cancel₀ _ hcard.ne'])
  set u := (avgSearch (groupScore G.degree K t k st) v₀ st.Cᶜ.toList m).eval G.cut
  have hu : u ∉ st.C := mem_compl.mp (mem_toList.mp hmem)
  obtain ⟨hrow, hrc⟩ := learnRow_spec G K hKG u (univ.erase u).toList (nodup_toList _)
    (by simp)
  have hrow' : (learnRow G.degree K u (univ.erase u).toList).eval G.cut = R.w u := by
    rw [hrow]; funext y
    by_cases hy : y = u
    · subst hy; simp [R.diag]
    · simp [hy, R]
  refine ⟨u, hu, rfl, ?_, ?_, ?_⟩
  · intro c hc x
    rw [hrow']
    by_cases hcu : c = u
    · subst hcu; simp
    · simp only [Function.update_of_ne hcu]
      exact hrows c ((mem_insert.mp hc).resolve_left hcu) x
  · refine select_bound (fun a b => R.nonneg a b) hlight ht hk hk2 (fun v => rfl) ?_
    rw [div_le_iff₀ hcard] at hτ
    exact hτ
  · rw [hrc, length_toList, card_erase_of_mem (mem_univ u), card_univ]
    have h1 := (hgs st.Cᶜ).2
    have h2 : st.Cᶜ.toList.length ≤ Fintype.card V := by
      rw [length_toList]; exact card_le_univ _
    have h3 := Nat.clog_mono_right 2 h2
    have h4 : 6 * B * Nat.clog 2 st.Cᶜ.toList.length ≤ 6 * B * Nat.clog 2 (Fintype.card V) :=
      Nat.mul_le_mul_left _ h3
    have h5 : 6 * B * (Nat.clog 2 (Fintype.card V) + 1) =
        6 * B * Nat.clog 2 (Fintype.card V) + 6 * B := by ring
    omega

/-- The selection loop: with a potential bound matching the remaining fuel, it ends with no
active vertex, exact rows, at most `fuel` new centers, and `fuel` selection costs. -/
theorem centerLoop_spec {t : ℝ} {k : ℕ} (ht : 0 < t) (hk2 : 2 ≤ k)
    (hkN : k ≤ 8 * Fintype.card V)
    (hlight : ∀ v, (G.subtract K).degree v ≤ t ∨
      ∀ u, (G.subtract K).w v u ≤ (G.subtract K).degree v / k)
    {D : ℝ} {M : ℕ} (hD : ∀ v, (G.subtract K).degree v ≤ D) (hM : 2 * D ≤ t * 2 ^ M)
    {F : ℕ} (hF : (Fintype.card V : ℝ) * (1 - k / (8 * Fintype.card V)) ^ F ≤ 1 / 2) :
    ∀ (fuel : ℕ) (st : CenterState V), (∀ c ∈ st.C, ∀ x, st.rows c x = (G.subtract K).w c x) →
      fuel ≤ F →
      Phi t k (G.subtract K).degree (G.subtract K).w st.C ≤
        Fintype.card V * (1 - k / (8 * Fintype.card V)) ^ (F - fuel) →
      (∀ c ∈ ((centerLoop G.degree K t k fuel st).eval G.cut).C, ∀ x,
          ((centerLoop G.degree K t k fuel st).eval G.cut).rows c x = (G.subtract K).w c x) ∧
        active t k (G.subtract K).degree (G.subtract K).w
          ((centerLoop G.degree K t k fuel st).eval G.cut).C = ∅ ∧
        ((centerLoop G.degree K t k fuel st).eval G.cut).C.card ≤ st.C.card + fuel ∧
        (centerLoop G.degree K t k fuel st).cost G.cut ≤
          fuel * (6 * (M + 1) * (Nat.clog 2 (Fintype.card V) + 1) + (Fintype.card V - 1)) := by
  set R := G.subtract K
  have hk : 0 < k := by omega
  have hω0 : ∀ a b, 0 ≤ R.w a b := fun a b => R.nonneg a b
  have hr : knownDeg G.degree K = R.degree := funext (knownDeg_eq G K hKG)
  have hcongr : ∀ st : CenterState V, (∀ c ∈ st.C, ∀ x, st.rows c x = R.w c x) →
      active t k (knownDeg G.degree K) (knownW st) st.C = active t k R.degree R.w st.C := by
    intro st hrows
    rw [hr]
    exact active_congr fun v c hc => by simp [knownW, hrows c hc v, R.symm c v]
  have hempty : ∀ C : Finset V, Phi t k R.degree R.w C ≤ 1 / 2 →
      active t k R.degree R.w C = ∅ := by
    intro C hC
    by_contra hne
    have := Phi_gt_half hω0 hlight ht.le hk (Finset.nonempty_iff_ne_empty.mpr hne)
    linarith
  intro fuel
  induction fuel with
  | zero =>
    intro st hrows _ hΦ
    simp only [centerLoop, eval_pure, cost_pure, Nat.sub_zero] at hΦ ⊢
    exact ⟨hrows, hempty _ (hΦ.trans hF), by omega, Nat.zero_le _⟩
  | succ fuel ih =>
    intro st hrows hfuel hΦ
    by_cases h : (active t k (knownDeg G.degree K) (knownW st) st.C).Nonempty
    · have hv₀ : h.choose ∈ active t k R.degree R.w st.C := by
        rw [← hcongr st hrows]; exact h.choose_spec
      simp only [centerLoop, h, ↓reduceDIte, eval_bind, cost_bind]
      obtain ⟨u, hu, hC, hrows', hsel, hcost⟩ := selectStep_spec G K hKG ht.le hk2 hlight hrows hv₀
      set st' := (selectStep G.degree K t k h.choose st).eval G.cut
      have hN : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos_iff.mpr ⟨u⟩
      set x : ℝ := k / (8 * Fintype.card V)
      have hx1 : 0 ≤ 1 - x := by
        have : x ≤ 1 := by
          rw [div_le_one (by positivity)]; exact_mod_cast hkN
        linarith
      have hΦ' : Phi t k R.degree R.w st'.C ≤
          Fintype.card V * (1 - x) ^ (F - fuel) := by
        rw [hC]
        have h1 := Phi_insert_le hω0 hlight ht.le hk hu
        have h2 : x * Phi t k R.degree R.w st.C ≤ score t k R.degree R.w st.C u := by
          simp only [x]
          rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
          linarith
        have h3 : F - fuel = (F - (fuel + 1)) + 1 := by omega
        rw [h3, pow_succ]
        nlinarith [mul_le_mul_of_nonneg_left hΦ hx1]
      obtain ⟨h1, h2, h3, h4⟩ := ih st' hrows' (by omega) hΦ'
      refine ⟨h1, h2, ?_, ?_⟩
      · rw [hC] at h3
        have := card_insert_of_notMem hu
        omega
      · have hB := card_buckets_le hω0 hlight ht hk hD hM st.C
        have hsel : (selectStep G.degree K t k h.choose st).cost G.cut ≤
            6 * (M + 1) * (Nat.clog 2 (Fintype.card V) + 1) + (Fintype.card V - 1) := by
          refine hcost.trans (Nat.add_le_add_right ?_ _)
          exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hB)
        rw [Nat.succ_mul]
        omega
    · simp only [centerLoop, h, ↓reduceDIte, eval_pure, cost_pure, zero_le, and_true]
      rw [hcongr st hrows, Finset.not_nonempty_iff_eq_empty] at h
      exact ⟨hrows, h, by omega⟩

/-- **Lemma 30 (bucketed center selection).** For a residual `R = G - K` satisfying
`eq:residual-light`, with `2 ≤ k ≤ 8N`, `t > 0`, residual degrees at most `D` and
`2D ≤ t 2^M`, `centerSelection` learns the exact rows of a set `C` of at most
`F = ⌈(8N/k) ln (2N)⌉` centers such that `eq:center-coverage` holds, using at most
`F (6 (M + 1)(⌈log₂ N⌉ + 1) + N - 1)` cut queries. -/
theorem centerSelection_spec [Nonempty V] {t : ℝ} {k : ℕ} (ht : 0 < t) (hk2 : 2 ≤ k)
    (hkN : k ≤ 8 * Fintype.card V)
    (hlight : ∀ v, (G.subtract K).degree v ≤ t ∨
      ∀ u, (G.subtract K).w v u ≤ (G.subtract K).degree v / k)
    {D : ℝ} {M : ℕ} (hD : ∀ v, (G.subtract K).degree v ≤ D) (hM : 2 * D ≤ t * 2 ^ M) :
    ((centerSelection G.degree K t k).eval G.cut).C.card ≤
        selectionBudget (Fintype.card V) k ∧
      (∀ c ∈ ((centerSelection G.degree K t k).eval G.cut).C, ∀ x,
        ((centerSelection G.degree K t k).eval G.cut).rows c x = (G.subtract K).w c x) ∧
      (∀ v ∉ ((centerSelection G.degree K t k).eval G.cut).C,
        (G.subtract K).degree v ≤ t ∨
        (G.subtract K).degree v / k ≤
          ∑ c ∈ ((centerSelection G.degree K t k).eval G.cut).C, (G.subtract K).w v c) ∧
      (centerSelection G.degree K t k).cost G.cut ≤
        selectionBudget (Fintype.card V) k *
          (6 * (M + 1) * (Nat.clog 2 (Fintype.card V) + 1) + (Fintype.card V - 1)) := by
  have hk : 0 < k := by omega
  have hF := pow_fuel_le (N := Fintype.card V) Fintype.card_pos hk hkN
  have hΦ0 : Phi t k (G.subtract K).degree (G.subtract K).w ∅ ≤
      Fintype.card V * (1 - k / (8 * Fintype.card V)) ^
        (selectionBudget (Fintype.card V) k - selectionBudget (Fintype.card V) k) := by
    rw [Nat.sub_self, pow_zero, mul_one]
    exact Phi_le_card (fun a b => (G.subtract K).nonneg a b) hlight ht.le hk ∅
  obtain ⟨h1, h2, h3, h4⟩ := centerLoop_spec G K hKG ht hk2 hkN hlight hD hM hF
    (selectionBudget (Fintype.card V) k) ⟨∅, fun _ _ => 0⟩ (by simp) le_rfl hΦ0
  refine ⟨by simpa [centerSelection] using h3, h1, fun v hv => ?_, h4⟩
  have : v ∉ active t k (G.subtract K).degree (G.subtract K).w
      ((centerSelection G.degree K t k).eval G.cut).C := by
    unfold centerSelection; rw [h2]; simp
  rw [mem_active] at this
  unfold IsActive bmass at this
  by_contra hcon
  push Not at hcon
  exact this ⟨hv, hcon.1, hcon.2⟩

/-- Lemma 30 under the normalization `d_v ≤ (N - 1) U`, `t = U / (16 N²)`, with
`M = 5 + 3 ⌈log₂ N⌉`: at most `F (6 (6 + 3 ⌈log₂ N⌉)(⌈log₂ N⌉ + 1) + N - 1)` queries,
`F = ⌈(8N/k) ln (2N)⌉ < (8N/k) ln (2N) + 1`. -/
theorem centerSelection_normalized [Nonempty V] {U : ℝ} (hU : 0 < U) {k : ℕ} (hk2 : 2 ≤ k)
    (hkN : k ≤ 8 * Fintype.card V)
    (hdeg : ∀ v, G.degree v ≤ ((Fintype.card V : ℝ) - 1) * U)
    (hlight : ∀ v, (G.subtract K).degree v ≤ U / (16 * (Fintype.card V : ℝ) ^ 2) ∨
      ∀ u, (G.subtract K).w v u ≤ (G.subtract K).degree v / k) :
    ((centerSelection G.degree K (U / (16 * (Fintype.card V : ℝ) ^ 2)) k).eval G.cut).C.card ≤
        selectionBudget (Fintype.card V) k ∧
      (∀ c ∈ ((centerSelection G.degree K (U / (16 * (Fintype.card V : ℝ) ^ 2)) k).eval
          G.cut).C, ∀ x,
        ((centerSelection G.degree K (U / (16 * (Fintype.card V : ℝ) ^ 2)) k).eval
          G.cut).rows c x = (G.subtract K).w c x) ∧
      (∀ v ∉ ((centerSelection G.degree K (U / (16 * (Fintype.card V : ℝ) ^ 2)) k).eval
          G.cut).C,
        (G.subtract K).degree v ≤ U / (16 * (Fintype.card V : ℝ) ^ 2) ∨
        (G.subtract K).degree v / k ≤
          ∑ c ∈ ((centerSelection G.degree K (U / (16 * (Fintype.card V : ℝ) ^ 2)) k).eval
            G.cut).C, (G.subtract K).w v c) ∧
      (centerSelection G.degree K (U / (16 * (Fintype.card V : ℝ) ^ 2)) k).cost G.cut ≤
        selectionBudget (Fintype.card V) k *
          (6 * (6 + 3 * Nat.clog 2 (Fintype.card V)) * (Nat.clog 2 (Fintype.card V) + 1) +
            (Fintype.card V - 1)) := by
  have hN : (1 : ℝ) ≤ Fintype.card V := by exact_mod_cast Fintype.card_pos
  have hD : ∀ v, (G.subtract K).degree v ≤ ((Fintype.card V : ℝ) - 1) * U := fun v => by
    rw [degree_subtract G K hKG]; linarith [degree_nonneg K v, hdeg v]
  have hM : 2 * (((Fintype.card V : ℝ) - 1) * U) ≤
      U / (16 * (Fintype.card V : ℝ) ^ 2) * 2 ^ (5 + 3 * Nat.clog 2 (Fintype.card V)) := by
    have hc0 : Fintype.card V ≤ 2 ^ Nat.clog 2 (Fintype.card V) :=
      Nat.le_pow_clog one_lt_two _
    have hc : (Fintype.card V : ℝ) ≤ (2 : ℝ) ^ Nat.clog 2 (Fintype.card V) := by
      exact_mod_cast hc0
    generalize (Fintype.card V : ℝ) = n at hN hc ⊢
    generalize Nat.clog 2 (Fintype.card V) = m at hc ⊢
    have h1 : n ^ 3 ≤ ((2 : ℝ) ^ m) ^ 3 := pow_le_pow_left₀ (by positivity) hc 3
    rw [pow_add, mul_comm 3 m, pow_mul, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    have h2 : (n - 1) * n ^ 2 ≤ ((2 : ℝ) ^ m) ^ 3 := by nlinarith
    have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 32 * U)
    norm_num
    nlinarith
  have := centerSelection_spec G K hKG (by positivity) hk2 hkN hlight hD hM
  refine ⟨this.1, this.2.1, this.2.2.1, this.2.2.2.trans (le_of_eq ?_)⟩
  ring

end Proofs

end Discovery
end CutQueryComplexity
