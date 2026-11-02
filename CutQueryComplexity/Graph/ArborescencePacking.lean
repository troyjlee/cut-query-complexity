import CutQueryComplexity.Graph.WeightedDirected
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Sequences
import Mathlib.Topology.Order.Compact
import Mathlib.Algebra.BigOperators.Field

/-! # Real arborescence packing (W3)

Spanning in-arborescences rooted at `r` are parent maps `p : V → Option V` (arcs `v → p v`,
oriented toward the root).  The set of all of them is one fixed finite set `inArbs r`.

* `edmonds_int` : integral Edmonds (rooted, in-version) for `ℕ` capacities, by Lovász's
  growing argument with submodularity of the outgoing cut.
* `exists_inArb_packing` : real version, by rounding `N·c` down, packing integrally,
  dividing by `N`, and passing to a convergent subsequence of coefficient vectors over
  the fixed finite index type `InArb r`.
* `cut_of_inArb_packing` : the converse.
* `exists_outArb_packing`, `cut_of_outArb_packing` : out-arborescence versions via `rev`.
-/

namespace CutQueryComplexity.DirectedCertificate

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## In-arborescences as parent maps -/

/-- One step of the walk toward the root. -/
def parentStep (p : V → Option V) (o : Option V) : Option V := o.bind p

/-- `p` is a spanning in-arborescence of `V` rooted at `r` (arcs `v → p v`). -/
structure IsInArb (r : V) (p : V → Option V) : Prop where
  root : p r = none
  nonroot : ∀ v, v ≠ r → p v ≠ none
  irrefl : ∀ v, p v ≠ some v
  acyclic : ∀ v, ∃ n : ℕ, (parentStep p)^[n] (some v) = none

/-- The fixed finite set of all spanning in-arborescences rooted at `r`. -/
noncomputable def inArbs (r : V) : Finset (V → Option V) := by
  classical exact Finset.univ.filter (IsInArb r)

theorem mem_inArbs {r : V} {p : V → Option V} : p ∈ inArbs r ↔ IsInArb r p := by
  unfold inArbs; simp

/-- The finite index type of in-arborescences rooted at `r`. -/
abbrev InArb (r : V) := {p : V → Option V // p ∈ inArbs r}

/-- Weighted arc load `Σ_T a T · [T u = some v]`. -/
noncomputable def load {r : V} (a : InArb r → ℝ) (u v : V) : ℝ :=
  ∑ T : InArb r, a T * if T.1 u = some v then 1 else 0

/-! ## Integer capacities -/

/-- Outgoing cut for `ℕ` capacities. -/
def outN (c : V → V → ℕ) (S : Finset V) : ℕ := ∑ u ∈ S, ∑ v ∈ Sᶜ, c u v

/-- Arc indicator of a parent map. -/
def arcInd (p : V → Option V) (u v : V) : ℕ := if p u = some v then 1 else 0

/-- Every nonempty set avoiding `r` has outgoing capacity at least `k`. -/
def CutCondN (c : V → V → ℕ) (r : V) (k : ℕ) : Prop :=
  ∀ S : Finset V, S.Nonempty → r ∉ S → k ≤ outN c S

theorem outN_add (c d : V → V → ℕ) (S : Finset V) :
    outN (fun a b => c a b + d a b) S = outN c S + outN d S := by
  simp only [outN, Finset.sum_add_distrib]

theorem outN_single (u v : V) (S : Finset V) :
    outN (fun a b => if a = u ∧ b = v then 1 else 0) S = if u ∈ S ∧ v ∉ S then 1 else 0 := by
  simp only [outN, ite_and]
  have h : ∀ x, (∑ y ∈ Sᶜ, if x = u then (if y = v then (1 : ℕ) else 0) else 0) =
      if x = u then (if v ∈ Sᶜ then 1 else 0) else 0 := by
    intro x; split_ifs <;> simp_all
  rw [Finset.sum_congr rfl fun x _ => h x, Finset.sum_ite_eq']
  split_ifs <;> simp_all

theorem outN_univ (c : V → V → ℕ) (S : Finset V) :
    outN c S = ∑ a, ∑ b, if a ∈ S ∧ b ∉ S then c a b else 0 := by
  have hu : ∀ (T : Finset V) (f : V → ℕ), ∑ x ∈ T, f x = ∑ x, if x ∈ T then f x else 0 := by
    intro T f; rw [Finset.sum_ite_mem, Finset.univ_inter]
  simp only [outN, ite_and]
  rw [hu S]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs
  · rw [hu Sᶜ]; simp only [Finset.mem_compl]
  · simp

/-- Submodularity of the outgoing cut. -/
theorem outN_submod (c : V → V → ℕ) (X Y : Finset V) :
    outN c (X ∩ Y) + outN c (X ∪ Y) ≤ outN c X + outN c Y := by
  rw [outN_univ, outN_univ, outN_univ c X, outN_univ c Y, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun b _ => ?_
  by_cases ha : a ∈ X <;> by_cases hb : a ∈ Y <;> by_cases hc : b ∈ X <;> by_cases hd : b ∈ Y <;>
    simp [ha, hb, hc, hd]

/-! ## Lovász's growing argument -/

/-- Invariant of the partially grown arborescence on `R` with residual capacity `c'`. -/
structure GrowState (c : V → V → ℕ) (r : V) (k : ℕ) (R : Finset V) (p : V → Option V)
    (ht : V → ℕ) (c' : V → V → ℕ) : Prop where
  root_mem : r ∈ R
  root : p r = none
  parent : ∀ v ∈ R, v ≠ r → ∃ w ∈ R, p v = some w ∧ ht w < ht v
  outside : ∀ v, v ∉ R → p v = none
  split : ∀ a b, c' a b + arcInd p a b = c a b
  cut : CutCondN c' r k

variable {c : V → V → ℕ} {r : V} {k : ℕ} {R : Finset V} {p : V → Option V} {ht : V → ℕ}
  {c' : V → V → ℕ}

theorem GrowState.outN_outside (hs : GrowState c r k R p ht c') {X : Finset V}
    (hX : ∀ x ∈ X, x ∉ R) : outN c' X = outN c X := by
  have hcs : c = fun a b => c' a b + arcInd p a b := funext fun a => funext fun b => (hs.split a b).symm
  rw [hcs, outN_add]
  have : outN (arcInd p) X = 0 := by
    refine Finset.sum_eq_zero fun a ha => Finset.sum_eq_zero fun b _ => ?_
    simp [arcInd, hs.outside a (hX a ha)]
  omega

theorem grow_extend (hs : GrowState c r k R p ht c') {u v : V} (hu : u ∉ R) (hv : v ∈ R)
    (huv : 1 ≤ c' u v)
    (hcrit : ∀ Y : Finset V, Y.Nonempty → r ∉ Y → outN c' Y = k → u ∈ Y → v ∉ Y → False) :
    GrowState c r k (insert u R) (Function.update p u (some v))
      (Function.update ht u (ht v + 1)) (fun a b => c' a b - if a = u ∧ b = v then 1 else 0) := by
  have hur : u ≠ r := fun h => hu (h ▸ hs.root_mem)
  have hvu : v ≠ u := fun h => hu (h ▸ hv)
  refine ⟨mem_insert_of_mem hs.root_mem, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Function.update_of_ne hur.symm]; exact hs.root
  · intro w hw hwr
    by_cases hwu : w = u
    · subst hwu
      exact ⟨v, mem_insert_of_mem hv, by simp, by simp [Function.update_of_ne hvu]⟩
    · have hwR : w ∈ R := (mem_insert.1 hw).resolve_left hwu
      obtain ⟨x, hx, hpx, hlt⟩ := hs.parent w hwR hwr
      have hxu : x ≠ u := fun h => hu (h ▸ hx)
      refine ⟨x, mem_insert_of_mem hx, by rw [Function.update_of_ne hwu]; exact hpx, ?_⟩
      rw [Function.update_of_ne hxu, Function.update_of_ne hwu]; exact hlt
  · intro w hw
    have hwu : w ≠ u := fun h => hw (h ▸ mem_insert_self _ _)
    rw [Function.update_of_ne hwu]
    exact hs.outside w fun h => hw (mem_insert_of_mem h)
  · intro a b
    have h0 := hs.split a b
    by_cases ha : a = u
    · subst ha
      have hpu := hs.outside a hu
      by_cases hb : b = v
      · subst hb; simp [arcInd, hpu] at h0 ⊢; omega
      · simp [arcInd, hpu, hb, Ne.symm hb] at h0 ⊢; omega
    · have h1 : arcInd (Function.update p u (some v)) a b = arcInd p a b := by
        simp only [arcInd, Function.update_of_ne ha]
      rw [h1]; simp only [ha, false_and, ite_false, Nat.sub_zero]; omega
  · intro Y hY hrY
    have hcs : c' = fun a b => (c' a b - if a = u ∧ b = v then 1 else 0) +
        (if a = u ∧ b = v then 1 else 0) := by
      funext a b
      by_cases h : a = u ∧ b = v
      · obtain ⟨rfl, rfl⟩ := h; simp; omega
      · simp [h]
    have heq : outN c' Y = outN (fun a b => (c' a b - if a = u ∧ b = v then 1 else 0) +
        (if a = u ∧ b = v then 1 else 0)) Y := by
      conv_lhs => rw [hcs]
    rw [outN_add, outN_single] at heq
    have hk := hs.cut Y hY hrY
    by_cases h : u ∈ Y ∧ v ∉ Y
    · rw [ite_eq_left h] at heq
      have hne : outN c' Y ≠ k := fun h' => hcrit Y hY hrY h' h.1 h.2
      omega
    · rw [ite_eq_right h] at heq
      omega

theorem grow_step (hc : CutCondN c r (k + 1)) (hs : GrowState c r k R p ht c')
    (hR : R ≠ Finset.univ) :
    ∃ u ∉ R, ∃ p' ht' c'', GrowState c r k (insert u R) p' ht' c'' := by
  classical
  let crit : Finset V → Prop := fun Y => Y.Nonempty ∧ r ∉ Y ∧ outN c' Y = k ∧ ¬ Y ⊆ R
  by_cases hF : ∃ Y, crit Y
  · obtain ⟨X, hXF, hXmin⟩ := Finset.exists_min_image (Finset.univ.filter crit) Finset.card
      (by obtain ⟨Y, hY⟩ := hF; exact ⟨Y, by simp [hY]⟩)
    have hX : crit X := (Finset.mem_filter.1 hXF).2
    obtain ⟨hXne, hrX, hXk, hXR⟩ := hX
    have hXmin' : ∀ Y, crit Y → X.card ≤ Y.card := fun Y hY => hXmin Y (by simp [hY])
    -- an arc from `X \ R` into `X ∩ R`
    have harc : ∃ u ∈ X, u ∉ R ∧ ∃ v ∈ X, v ∈ R ∧ 1 ≤ c' u v := by
      by_contra hno
      push Not at hno
      obtain ⟨x, hxX, hxR⟩ := Finset.not_subset.1 hXR
      have h1 : k + 1 ≤ outN c' (X \ R) := by
        rw [hs.outN_outside (fun y hy => (Finset.mem_sdiff.1 hy).2)]
        exact hc _ ⟨x, Finset.mem_sdiff.2 ⟨hxX, hxR⟩⟩
          (fun h => hrX (Finset.mem_sdiff.1 h).1)
      have h2 : outN c' (X \ R) ≤ outN c' X := by
        unfold outN
        calc ∑ a ∈ X \ R, ∑ b ∈ (X \ R)ᶜ, c' a b = ∑ a ∈ X \ R, ∑ b ∈ Xᶜ, c' a b := by
              refine Finset.sum_congr rfl fun a ha => ?_
              obtain ⟨haX, haR⟩ := Finset.mem_sdiff.1 ha
              refine (Finset.sum_subset (Finset.compl_subset_compl.2 Finset.sdiff_subset)
                fun b hb hb' => ?_).symm
              have hbX : b ∈ X := by simpa using hb'
              have hbR : b ∈ R := by
                by_contra hbR; exact (Finset.mem_compl.1 hb) (Finset.mem_sdiff.2 ⟨hbX, hbR⟩)
              have := hno a haX haR b hbX hbR
              omega
          _ ≤ ∑ a ∈ X, ∑ b ∈ Xᶜ, c' a b :=
              Finset.sum_le_sum_of_subset Finset.sdiff_subset
      omega
    obtain ⟨u, huX, huR, v, hvX, hvR, huv⟩ := harc
    refine ⟨u, huR, _, _, _, grow_extend hs huR hvR huv ?_⟩
    intro Y hY hrY hYk huY hvY
    have hsub := outN_submod c' X Y
    have hI := hs.cut (X ∩ Y) ⟨u, Finset.mem_inter.2 ⟨huX, huY⟩⟩
      (fun h => hrX (Finset.mem_inter.1 h).1)
    have hU := hs.cut (X ∪ Y) (hXne.mono Finset.subset_union_left)
      (fun h => (Finset.mem_union.1 h).elim hrX hrY)
    have hIk : outN c' (X ∩ Y) = k := by omega
    have hcI : crit (X ∩ Y) := ⟨⟨u, Finset.mem_inter.2 ⟨huX, huY⟩⟩,
      fun h => hrX (Finset.mem_inter.1 h).1, hIk,
      fun h => huR (h (Finset.mem_inter.2 ⟨huX, huY⟩))⟩
    have hlt : (X ∩ Y).card < X.card := Finset.card_lt_card
      ⟨Finset.inter_subset_left, fun h => hvY (Finset.mem_inter.1 (h hvX)).2⟩
    exact absurd (hXmin' _ hcI) (by omega)
  · push Not at hF
    have harc : ∃ u ∉ R, ∃ v ∈ R, 1 ≤ c' u v := by
      by_contra hno
      push Not at hno
      obtain ⟨x, hx⟩ : ∃ x, x ∉ R := by
        by_contra h; push Not at h; exact hR (Finset.eq_univ_iff_forall.2 h)
      have h1 : k + 1 ≤ outN c' Rᶜ := by
        rw [hs.outN_outside (fun y hy => Finset.mem_compl.1 hy)]
        exact hc _ ⟨x, Finset.mem_compl.2 hx⟩ (fun h => Finset.mem_compl.1 h hs.root_mem)
      have h2 : outN c' Rᶜ = 0 := by
        refine Finset.sum_eq_zero fun a ha => Finset.sum_eq_zero fun b hb => ?_
        have := hno a (Finset.mem_compl.1 ha) b (by simpa using hb)
        omega
      omega
    obtain ⟨u, huR, v, hvR, huv⟩ := harc
    refine ⟨u, huR, _, _, _, grow_extend hs huR hvR huv ?_⟩
    intro Y hY hrY hYk huY _
    exact hF Y ⟨hY, hrY, hYk, fun h => huR (h huY)⟩

theorem grow_full (hc : CutCondN c r (k + 1)) :
    ∀ n : ℕ, ∀ (R : Finset V) (p : V → Option V) (ht : V → ℕ) (c' : V → V → ℕ),
      GrowState c r k R p ht c' → Rᶜ.card = n →
      ∃ p ht c', GrowState c r k Finset.univ p ht c' := by
  intro n
  induction n with
  | zero =>
    intro R p ht c' hs hn
    have : R = Finset.univ := by
      rw [Finset.card_eq_zero, Finset.compl_eq_empty_iff] at hn; exact hn
    subst this; exact ⟨p, ht, c', hs⟩
  | succ n ih =>
    intro R p ht c' hs hn
    have hR : R ≠ Finset.univ := by
      rintro rfl; simp at hn
    obtain ⟨u, hu, p', ht', c'', hs'⟩ := grow_step hc hs hR
    refine ih _ p' ht' c'' hs' ?_
    rw [Finset.compl_insert, Finset.card_erase_of_mem (Finset.mem_compl.2 hu), hn]
    rfl

theorem GrowState.isInArb (hs : GrowState c r k Finset.univ p ht c') : IsInArb r p := by
  refine ⟨hs.root, ?_, ?_, ?_⟩
  · intro v hv h
    obtain ⟨w, _, hw, _⟩ := hs.parent v (mem_univ _) hv
    rw [h] at hw; simp at hw
  · intro v h
    have hv : v ≠ r := by rintro rfl; rw [hs.root] at h; simp at h
    obtain ⟨w, _, hw, hlt⟩ := hs.parent v (mem_univ _) hv
    rw [h] at hw; cases hw; omega
  · have key : ∀ n : ℕ, ∀ v, ht v < n → ∃ m : ℕ, (parentStep p)^[m] (some v) = none := by
      intro n
      induction n with
      | zero => intro v h; omega
      | succ n ih =>
        intro v hvn
        by_cases hv : v = r
        · subst hv; exact ⟨1, by simp [parentStep, hs.root]⟩
        · obtain ⟨w, _, hw, hlt⟩ := hs.parent v (mem_univ _) hv
          obtain ⟨m, hm⟩ := ih w (by omega)
          refine ⟨m + 1, ?_⟩
          rw [Function.iterate_succ_apply]
          simpa [parentStep, hw] using hm
    intro v
    exact key (ht v + 1) v (Nat.lt_succ_self _)

/-- One Lovász step: from the `(k+1)`-cut condition, a spanning in-arborescence using only
arcs of positive capacity whose removal leaves the `k`-cut condition. -/
theorem edmonds_step (hc : CutCondN c r (k + 1)) :
    ∃ p, IsInArb r p ∧ ∃ c' : V → V → ℕ, (∀ a b, c' a b + arcInd p a b = c a b) ∧
      CutCondN c' r k := by
  have h0 : GrowState c r k {r} (fun _ => none) (fun _ => 0) c := by
    refine ⟨mem_singleton_self r, rfl, ?_, fun _ _ => rfl, fun a b => by simp [arcInd], ?_⟩
    · intro v hv hvr; exact absurd (mem_singleton.1 hv) hvr
    · intro S hS hr; exact le_trans (Nat.le_succ k) (hc S hS hr)
  obtain ⟨p, ht, c', hs⟩ := grow_full hc _ _ _ _ _ h0 rfl
  exact ⟨p, hs.isInArb, c', hs.split, hs.cut⟩

/-- Integral Edmonds theorem (rooted, in-arborescences): `k` in-arborescences with arc loads
bounded by `ℕ` capacities whenever every nonempty set avoiding `r` has out-capacity `≥ k`. -/
theorem edmonds_int (r : V) :
    ∀ (k : ℕ) (c : V → V → ℕ), CutCondN c r k →
      ∃ b : InArb r → ℕ, ∑ T, b T = k ∧ ∀ u v, ∑ T, b T * arcInd T.1 u v ≤ c u v := by
  intro k
  induction k with
  | zero => intro c _; exact ⟨0, by simp, fun u v => by simp⟩
  | succ k ih =>
    intro c hc
    obtain ⟨p, hp, c', hsplit, hc'⟩ := edmonds_step hc
    obtain ⟨b, hb, hbl⟩ := ih c' hc'
    refine ⟨fun T => b T + if T = ⟨p, mem_inArbs.2 hp⟩ then 1 else 0, ?_, ?_⟩
    · rw [Finset.sum_add_distrib, hb, Finset.sum_ite_eq']; simp
    · intro u v
      simp only [add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul,
        Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      have := hbl u v
      have := hsplit u v
      omega

/-! ## Real capacities -/

open Filter Topology

omit [Fintype V] in
theorem arcInd_cast (p : V → Option V) (u v : V) :
    ((arcInd p u v : ℕ) : ℝ) = if p u = some v then 1 else 0 := by
  unfold arcInd; split_ifs <;> simp

/-- Rounding `N·c` down loses less than `|V|²` on every cut. -/
theorem cutCondN_floor (G : WeightedDiGraph V) (r : V) (lam : ℝ)
    (hcut : ∀ S : Finset V, S.Nonempty → r ∉ S → lam ≤ G.out S) (N : ℝ) (hN : 0 ≤ N) :
    CutCondN (fun u v => ⌊N * G.c u v⌋₊) r ⌊N * lam - (Fintype.card V : ℝ) ^ 2⌋₊ := by
  intro S hS hr
  by_cases h0 : N * lam - (Fintype.card V : ℝ) ^ 2 < 0
  · rw [Nat.floor_eq_zero.2 (by linarith)]; exact Nat.zero_le _
  push Not at h0
  have h1 : ((⌊N * lam - (Fintype.card V : ℝ) ^ 2⌋₊ : ℕ) : ℝ) ≤
      N * lam - (Fintype.card V : ℝ) ^ 2 := Nat.floor_le h0
  have h2 : N * G.out S - (S.card : ℝ) * (Sᶜ.card : ℝ) ≤
      ((outN (fun u v => ⌊N * G.c u v⌋₊) S : ℕ) : ℝ) := by
    unfold outN WeightedDiGraph.out
    push_cast
    have : N * (∑ u ∈ S, ∑ v ∈ Sᶜ, G.c u v) - (S.card : ℝ) * (Sᶜ.card : ℝ) =
        ∑ u ∈ S, ∑ v ∈ Sᶜ, (N * G.c u v - 1) := by
      simp [Finset.sum_sub_distrib, Finset.mul_sum]
    rw [this]
    refine Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => ?_
    have := Nat.lt_floor_add_one (N * G.c u v)
    linarith
  have h3 : (S.card : ℝ) * (Sᶜ.card : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 := by
    have a1 : (S.card : ℝ) ≤ Fintype.card V := by exact_mod_cast Finset.card_le_univ S
    have a2 : (Sᶜ.card : ℝ) ≤ Fintype.card V := by exact_mod_cast Finset.card_le_univ Sᶜ
    rw [sq]; exact mul_le_mul a1 a2 (by positivity) (by positivity)
  have h4 : N * lam ≤ N * G.out S := mul_le_mul_of_nonneg_left (hcut S hS hr) hN
  have : ((⌊N * lam - (Fintype.card V : ℝ) ^ 2⌋₊ : ℕ) : ℝ) ≤
      ((outN (fun u v => ⌊N * G.c u v⌋₊) S : ℕ) : ℝ) := by linarith
  exact_mod_cast this

/-- **Real rooted arborescence packing.** If every nonempty set avoiding `r` has outgoing
capacity at least `lam`, there are coefficients on the fixed finite set of in-arborescences
rooted at `r` with total `lam` and arc loads bounded by the capacities. -/
theorem exists_inArb_packing (G : WeightedDiGraph V) (r : V) (lam : ℝ) (hlam : 0 ≤ lam)
    (hcut : ∀ S : Finset V, S.Nonempty → r ∉ S → lam ≤ G.out S) :
    ∃ a : InArb r → ℝ, (∀ T, 0 ≤ a T) ∧ (∑ T, a T = lam) ∧ ∀ u v, load a u v ≤ G.c u v := by
  set M : ℝ := (Fintype.card V : ℝ) ^ 2 with hM
  have hM0 : 0 ≤ M := by positivity
  have hint : ∀ n : ℕ, ∃ b : InArb r → ℕ, ∑ T, b T = ⌊((n : ℝ) + 1) * lam - M⌋₊ ∧
      ∀ u v, ∑ T, b T * arcInd T.1 u v ≤ ⌊((n : ℝ) + 1) * G.c u v⌋₊ := fun n =>
    edmonds_int r _ _ (cutCondN_floor G r lam hcut _ (by positivity))
  choose b hbsum hbload using hint
  let x : ℕ → InArb r → ℝ := fun n T => (b n T : ℝ) / ((n : ℝ) + 1)
  have hNpos : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 1 := fun n => by positivity
  have hxsum : ∀ n, ∑ T, x n T = (⌊((n : ℝ) + 1) * lam - M⌋₊ : ℝ) / ((n : ℝ) + 1) := by
    intro n; simp only [x]; rw [← Finset.sum_div]; congr 1; exact_mod_cast hbsum n
  have hkle : ∀ n : ℕ, (⌊((n : ℝ) + 1) * lam - M⌋₊ : ℝ) ≤ ((n : ℝ) + 1) * lam := by
    intro n
    by_cases h0 : ((n : ℝ) + 1) * lam - M < 0
    · rw [Nat.floor_eq_zero.2 (by linarith)]; simp only [Nat.cast_zero]
      exact mul_nonneg (hNpos n).le hlam
    · have := Nat.floor_le (not_lt.1 h0); linarith
  have hsum_le : ∀ n, ∑ T, x n T ≤ lam := by
    intro n; rw [hxsum, div_le_iff₀ (hNpos n)]; linarith [hkle n]
  have hsum_ge : ∀ n : ℕ, lam - (M + 1) * (1 / ((n : ℝ) + 1)) ≤ ∑ T, x n T := by
    intro n; rw [hxsum]
    have h1 := Nat.sub_one_lt_floor (((n : ℝ) + 1) * lam - M)
    rw [le_div_iff₀ (hNpos n)]
    have h2 : (lam - (M + 1) * (1 / ((n : ℝ) + 1))) * ((n : ℝ) + 1) =
        ((n : ℝ) + 1) * lam - (M + 1) := by
      field_simp
    linarith
  have hx0 : ∀ n T, 0 ≤ x n T := fun n T => by positivity
  have hxle : ∀ n T, x n T ≤ lam := fun n T =>
    le_trans (Finset.single_le_sum (fun T _ => hx0 n T) (Finset.mem_univ T)) (hsum_le n)
  have hxload : ∀ n u v, load (x n) u v ≤ G.c u v := by
    intro n u v
    have h1 : load (x n) u v =
        ((∑ T, b n T * arcInd T.1 u v : ℕ) : ℝ) / ((n : ℝ) + 1) := by
      simp only [load, x]; push_cast; rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun T _ => ?_
      rw [arcInd_cast]; ring
    rw [h1, div_le_iff₀ (hNpos n)]
    have h2 : ((∑ T, b n T * arcInd T.1 u v : ℕ) : ℝ) ≤ (⌊((n : ℝ) + 1) * G.c u v⌋₊ : ℝ) := by
      exact_mod_cast hbload n u v
    have h3 := Nat.floor_le (mul_nonneg (hNpos n).le (G.nonneg u v))
    linarith
  -- compactness of the coefficient box over the fixed finite set of arborescences
  have hmem : ∀ n, x n ∈ Set.Icc (0 : InArb r → ℝ) (fun _ => lam) := fun n =>
    ⟨fun T => hx0 n T, fun T => hxle n T⟩
  obtain ⟨a, ha, φ, hφ, hlim⟩ := isCompact_Icc.tendsto_subseq hmem
  have hcoord : ∀ T, Tendsto (fun n => x (φ n) T) atTop (𝓝 (a T)) := tendsto_pi_nhds.1 hlim
  refine ⟨a, fun T => ha.1 T, ?_, ?_⟩
  · have hA : Tendsto (fun n => ∑ T, x (φ n) T) atTop (𝓝 (∑ T, a T)) :=
      tendsto_finsetSum _ fun T _ => hcoord T
    have hB : Tendsto (fun n => ∑ T, x n T) atTop (𝓝 lam) := by
      have hlow : Tendsto (fun n : ℕ => lam - (M + 1) * (1 / ((n : ℝ) + 1))) atTop (𝓝 lam) := by
        have := ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (M + 1)).const_sub lam
        simpa using this
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds hsum_ge hsum_le
    exact tendsto_nhds_unique hA (hB.comp hφ.tendsto_atTop)
  · intro u v
    have hA : Tendsto (fun n => load (x (φ n)) u v) atTop (𝓝 (load a u v)) :=
      tendsto_finsetSum _ fun T _ => (hcoord T).mul_const _
    exact le_of_tendsto' hA fun n => hxload (φ n) u v

omit [Fintype V] in
/-- Every in-arborescence toward `r` has an arc leaving each nonempty `S ∌ r`. -/
theorem IsInArb.exists_leaving {r : V} {p : V → Option V} (hp : IsInArb r p) {S : Finset V}
    (hS : S.Nonempty) (hr : r ∉ S) : ∃ u ∈ S, ∃ w ∉ S, p u = some w := by
  obtain ⟨v, hv⟩ := hS
  obtain ⟨n, hn⟩ := hp.acyclic v
  induction n generalizing v with
  | zero => simp at hn
  | succ n ih =>
    rw [Function.iterate_succ_apply] at hn
    cases hpv : p v with
    | none =>
      have : v = r := by by_contra h; exact hp.nonroot v h hpv
      exact absurd (this ▸ hv) hr
    | some w =>
      by_cases hw : w ∈ S
      · have hstep : parentStep p (some v) = some w := by simp [parentStep, hpv]
        rw [hstep] at hn
        exact ih w hw hn
      · exact ⟨v, hv, w, hw, hpv⟩

/-- Converse: a packing of total `lam` under the capacities forces the cut condition. -/
theorem cut_of_inArb_packing (G : WeightedDiGraph V) (r : V) (lam : ℝ) (a : InArb r → ℝ)
    (ha : ∀ T, 0 ≤ a T) (hsum : ∑ T, a T = lam) (hload : ∀ u v, load a u v ≤ G.c u v) :
    ∀ S : Finset V, S.Nonempty → r ∉ S → lam ≤ G.out S := by
  intro S hS hr
  have hind : ∀ (T : InArb r) u v, (0 : ℝ) ≤ if T.1 u = some v then 1 else 0 :=
    fun T u v => by split_ifs <;> norm_num
  have hT : ∀ T : InArb r, (1 : ℝ) ≤ ∑ u ∈ S, ∑ v ∈ Sᶜ, if T.1 u = some v then 1 else 0 := by
    intro T
    obtain ⟨u, hu, w, hw, huw⟩ := (mem_inArbs.1 T.2).exists_leaving hS hr
    calc (1 : ℝ) = if T.1 u = some w then 1 else 0 := by rw [ite_eq_left huw]
      _ ≤ ∑ v ∈ Sᶜ, if T.1 u = some v then 1 else 0 :=
          Finset.single_le_sum (f := fun v => if T.1 u = some v then (1 : ℝ) else 0)
            (fun v _ => hind T u v) (Finset.mem_compl.2 hw)
      _ ≤ _ := Finset.single_le_sum
          (f := fun u => ∑ v ∈ Sᶜ, if T.1 u = some v then (1 : ℝ) else 0)
          (fun u _ => Finset.sum_nonneg fun v _ => hind T u v) hu
  calc lam = ∑ T, a T * 1 := by simp only [mul_one, hsum]
    _ ≤ ∑ T, a T * ∑ u ∈ S, ∑ v ∈ Sᶜ, (if T.1 u = some v then 1 else 0) :=
        Finset.sum_le_sum fun T _ => mul_le_mul_of_nonneg_left (hT T) (ha T)
    _ = ∑ u ∈ S, ∑ v ∈ Sᶜ, load a u v := by
        simp only [load, Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun u _ => Finset.sum_comm
    _ ≤ G.out S := Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => hload u v

/-- Packing characterization for in-arborescences rooted at `r`. -/
theorem inArb_packing_iff (G : WeightedDiGraph V) (r : V) (lam : ℝ) (hlam : 0 ≤ lam) :
    (∃ a : InArb r → ℝ, (∀ T, 0 ≤ a T) ∧ (∑ T, a T = lam) ∧ ∀ u v, load a u v ≤ G.c u v) ↔
      ∀ S : Finset V, S.Nonempty → r ∉ S → lam ≤ G.out S :=
  ⟨fun ⟨a, h0, hs, hl⟩ => cut_of_inArb_packing G r lam a h0 hs hl,
    exists_inArb_packing G r lam hlam⟩

/-! ## Out-arborescences by reversal

An out-arborescence from `r` is the same parent map read with arcs `p v → v`. -/

/-- Weighted arc load of out-arborescences: `Σ_T a T · [T v = some u]` on the arc `u → v`. -/
noncomputable def outLoad {r : V} (a : InArb r → ℝ) (u v : V) : ℝ :=
  ∑ T : InArb r, a T * if T.1 v = some u then 1 else 0

theorem outLoad_eq_load {r : V} (a : InArb r → ℝ) (u v : V) : outLoad a u v = load a v u := rfl

/-- Out-arborescences packed under `G` are exactly in-arborescences packed under `G.rev`. -/
theorem outLoad_le_iff (G : WeightedDiGraph V) {r : V} (a : InArb r → ℝ) :
    (∀ u v, outLoad a u v ≤ G.c u v) ↔ ∀ u v, load a u v ≤ G.rev.c u v :=
  ⟨fun h u v => h v u, fun h u v => h v u⟩

/-- **Real out-arborescence packing** from `r`: cut condition on capacity into each `S ∌ r`. -/
theorem exists_outArb_packing (G : WeightedDiGraph V) (r : V) (lam : ℝ) (hlam : 0 ≤ lam)
    (hcut : ∀ S : Finset V, S.Nonempty → r ∉ S → lam ≤ G.out Sᶜ) :
    ∃ a : InArb r → ℝ, (∀ T, 0 ≤ a T) ∧ (∑ T, a T = lam) ∧ ∀ u v, outLoad a u v ≤ G.c u v := by
  obtain ⟨a, h0, hs, hl⟩ := exists_inArb_packing G.rev r lam hlam
    (fun S hS hr => by rw [G.rev_out]; exact hcut S hS hr)
  exact ⟨a, h0, hs, (outLoad_le_iff G a).2 hl⟩

theorem cut_of_outArb_packing (G : WeightedDiGraph V) (r : V) (lam : ℝ) (a : InArb r → ℝ)
    (ha : ∀ T, 0 ≤ a T) (hsum : ∑ T, a T = lam) (hload : ∀ u v, outLoad a u v ≤ G.c u v) :
    ∀ S : Finset V, S.Nonempty → r ∉ S → lam ≤ G.out Sᶜ := by
  intro S hS hr
  rw [← G.rev_out]
  exact cut_of_inArb_packing G.rev r lam a ha hsum ((outLoad_le_iff G a).1 hload) S hS hr

theorem outArb_packing_iff (G : WeightedDiGraph V) (r : V) (lam : ℝ) (hlam : 0 ≤ lam) :
    (∃ a : InArb r → ℝ, (∀ T, 0 ≤ a T) ∧ (∑ T, a T = lam) ∧ ∀ u v, outLoad a u v ≤ G.c u v) ↔
      ∀ S : Finset V, S.Nonempty → r ∉ S → lam ≤ G.out Sᶜ :=
  ⟨fun ⟨a, h0, hs, hl⟩ => cut_of_outArb_packing G r lam a h0 hs hl,
    exists_outArb_packing G r lam hlam⟩

end CutQueryComplexity.DirectedCertificate
