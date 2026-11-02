import CutQueryComplexity.TwoRespecting.Tree
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.Linarith

/-! # Terminal compression of a tree (Lemma 26)

A tree is a `RootedTree V`; the edge above a non-root vertex `v` has capacity
`c v ≥ 0`. The cost of a labeling `f : V → Bool` is the capacity of the edges it
cuts. A contraction is described by a set `K` of kept vertices containing the
root: every vertex maps to its nearest ancestor in `K` (`rep T K`). Thus the edge
above `v` is contracted exactly when `v ∉ K`, the fibers are connected, and the
quotient tree has vertex set `K`.

`tree_compression` proves Lemma 26: for every terminal set `C` there is such a
`K` with `|K| ≤ max 1 (2|C| - 2)`, injective on `C`, such that every labeling of
`C` has a minimum-cost extension constant on each fiber. The proof repeatedly
merges a terminal-free quotient vertex `x` of degree at most two along its
heaviest incident quotient edge, relabeling the class of `x` (`relabel`). This
covers both pruning non-terminal leaves and shortening degree-two paths, and
does not need `C` to consist of leaves. The size bound is a degree count
(`card_le_of_final`).
-/

namespace CutQueryComplexity
namespace Discovery

open TwoRespecting RootedTree Finset

variable {V : Type} [Fintype V] [DecidableEq V] (T : RootedTree V)

/-- The nearest ancestor of `v` in `K`, or the root if there is none. -/
def rep (K : Finset V) (v : V) : V :=
  if _h : v ∈ K ∨ v = T.root then v else rep K (T.parent v)
termination_by T.depth v
decreasing_by
  have := T.depth_parent v (fun e => _h (Or.inr e))
  omega

/-- Capacity of the tree edges cut by a labeling. -/
def cost (c : V → ℝ) (f : V → Bool) : ℝ :=
  ∑ v ∈ univ.erase T.root, if f v = f (T.parent v) then 0 else c v

/-- The quotient edges incident to `x`, named by their child endpoints. -/
def inc (K : Finset V) (x : V) : Finset V :=
  (K.erase T.root).filter fun j => j = x ∨ rep T K (T.parent j) = x

/-- For every labeling, some labeling constant on the fibers of `rep T K` agrees with it on
the terminals and costs no more. -/
def Good (c : V → ℝ) (C K : Finset V) : Prop :=
  ∀ g : V → Bool, ∃ f : V → Bool, (∀ t ∈ C, f t = g t) ∧ (∀ v, f v = f (rep T K v)) ∧
    cost T c f ≤ cost T c g

variable {T}

section Rep

variable {K : Finset V}

omit [Fintype V] in
theorem rep_of_mem {v : V} (h : v ∈ K) : rep T K v = v := by
  rw [rep]; simp [h]

omit [Fintype V] in
theorem rep_root : rep T K T.root = T.root := by
  rw [rep]; simp

omit [Fintype V] in
theorem rep_of_not_mem {v : V} (h : v ∉ K) (hr : v ≠ T.root) :
    rep T K v = rep T K (T.parent v) := by
  rw [rep]; simp [h, hr]

omit [Fintype V] in
/-- Each vertex is mapped to one of its ancestors, so fibers are connected. -/
theorem rep_isAnc (K : Finset V) (v : V) : T.IsAnc (rep T K v) v := by
  induction hd : T.depth v using Nat.strong_induction_on generalizing v with
  | _ n ih =>
    by_cases hv : v ∈ K
    · rw [rep_of_mem hv]
    by_cases hr : v = T.root
    · subst hr; rw [rep_root]
    rw [rep_of_not_mem hv hr]
    exact isAnc_trans (ih _ (by have := T.depth_parent v hr; omega) _ rfl) (isAnc_parent v)

omit [Fintype V] in
theorem rep_mem (hroot : T.root ∈ K) (v : V) : rep T K v ∈ K := by
  induction hd : T.depth v using Nat.strong_induction_on generalizing v with
  | _ n ih =>
    by_cases hv : v ∈ K
    · rw [rep_of_mem hv]; exact hv
    by_cases hr : v = T.root
    · subst hr; rw [rep_root]; exact hroot
    rw [rep_of_not_mem hv hr]
    exact ih _ (by have := T.depth_parent v hr; omega) _ rfl

omit [Fintype V] in
theorem rep_rep (hroot : T.root ∈ K) (v : V) : rep T K (rep T K v) = rep T K v :=
  rep_of_mem (rep_mem hroot v)

omit [Fintype V] in
/-- The quotient parent of a non-root vertex is a different vertex. -/
theorem rep_parent_ne {j : V} (hj : j ≠ T.root) : rep T K (T.parent j) ≠ j := by
  intro h
  have h1 := (rep_isAnc (T := T) K (T.parent j)).depth_le
  have h2 := T.depth_parent j hj
  rw [h] at h1
  omega

omit [Fintype V] in
/-- Removing `k` from `K` merges the class of `k` into the class of its quotient parent. -/
theorem rep_erase {k : V} (hk : k ∈ K) (hkr : k ≠ T.root) (v : V) :
    rep T (K.erase k) v = if rep T K v = k then rep T K (T.parent k) else rep T K v := by
  induction hd : T.depth v using Nat.strong_induction_on generalizing v with
  | _ n ih =>
    by_cases hr : v = T.root
    · subst hr; simp [rep_root, Ne.symm hkr]
    by_cases hvk : v = k
    · subst hvk
      rw [rep_of_not_mem (by simp) hr, ih _ (by have := T.depth_parent v hr; omega) _ rfl,
        rep_of_mem hk]
      simp [rep_parent_ne hr]
    by_cases hv : v ∈ K
    · rw [rep_of_mem (Finset.mem_erase.mpr ⟨hvk, hv⟩), rep_of_mem hv]; simp [hvk]
    · rw [rep_of_not_mem (fun h => hv (Finset.mem_of_mem_erase h)) hr,
        ih _ (by have := T.depth_parent v hr; omega) _ rfl, rep_of_not_mem hv hr]

end Rep

section Cost

variable {K : Finset V} {c : V → ℝ}

/-- For a labeling constant on fibers, only the kept edges contribute. -/
theorem cost_eq_quotient {f : V → Bool} (hf : ∀ v, f v = f (rep T K v)) :
    cost T c f = ∑ j ∈ K.erase T.root, if f j = f (rep T K (T.parent j)) then 0 else c j := by
  have hK : K.erase T.root = (univ.erase T.root).filter (· ∈ K) := by
    ext v; simp [and_comm]
  rw [hK, Finset.sum_filter, cost]
  refine Finset.sum_congr rfl fun v hv => ?_
  have hr : v ≠ T.root := (Finset.mem_erase.mp hv).1
  by_cases hvK : v ∈ K
  · simp [hvK, ← hf (T.parent v)]
  · have : f v = f (T.parent v) := by rw [hf v, hf (T.parent v), rep_of_not_mem hvK hr]
    simp [hvK, this]

/-- Relabel the class of `x` with the label of its neighbor across the quotient edge `k`.
The result is constant on the classes after merging along `k`, and costs no more when the
other edges at `x` have total capacity at most `c k`. -/
theorem relabel (hroot : T.root ∈ K) (hc : ∀ v, 0 ≤ c v) {f : V → Bool}
    (hf : ∀ v, f v = f (rep T K v)) {x k : V} (hk : k ∈ K) (hkr : k ≠ T.root)
    (hx : x = k ∨ x = rep T K (T.parent k)) (hsum : ∑ j ∈ (inc T K x).erase k, c j ≤ c k) :
    let t := if x = k then rep T K (T.parent k) else k
    let f' := fun v => if rep T K v = x then f t else f v
    (∀ v, f' v = f' (rep T (K.erase k) v)) ∧ cost T c f' ≤ cost T c f := by
  intro t f'
  have hqk : rep T K (T.parent k) ≠ k := rep_parent_ne hkr
  have hqkK : rep T K (T.parent k) ∈ K := rep_mem hroot _
  have hrr : ∀ v, rep T K (rep T K v) = rep T K v := rep_rep hroot
  -- `f'` is constant on the classes of `K`.
  have hf'K : ∀ v, f' v = f' (rep T K v) := by
    intro v
    simp only [f', hrr]
    split
    · rfl
    · exact hf v
  -- The two endpoints of the merged edge receive the same label.
  have hedge : f' k = f' (rep T K (T.parent k)) := by
    simp only [f', t, rep_of_mem hk, hrr]
    rcases hx with rfl | rfl
    · simp [hqk]
    · simp [hqk]
  refine ⟨fun v => ?_, ?_⟩
  · rw [rep_erase hk hkr v]
    split
    · rename_i hv
      rw [hf'K v, hv, hedge]
    · exact hf'K v
  -- Cost comparison on the quotient.
  by_cases hft : f x = f t
  · have : f' = f := by
      funext v
      simp only [f']
      split
      · rename_i hv; rw [← hft, ← hv, ← hf v]
      · rfl
    rw [this]
  have hcut : f k ≠ f (rep T K (T.parent k)) := by
    rcases hx with rfl | rfl
    · simpa [t] using hft
    · simp only [t, hqk, ite_false] at hft; exact Ne.symm hft
  rw [cost_eq_quotient hf'K, cost_eq_quotient hf]
  set S := K.erase T.root
  have hkS : k ∈ S := Finset.mem_erase.mpr ⟨hkr, hk⟩
  -- A termwise bound with a correction supported on the edges at `x`.
  have hterm : ∀ j ∈ S,
      (if f' j = f' (rep T K (T.parent j)) then 0 else c j) ≤
        (if f j = f (rep T K (T.parent j)) then 0 else c j) +
          ((if j = k then -c k else 0) + (if j ≠ k ∧ j ∈ inc T K x then c j else 0)) := by
    intro j hj
    have hjK : j ∈ K := Finset.mem_of_mem_erase hj
    by_cases hjk : j = k
    · subst hjk
      simp [hedge, hcut]
    by_cases hji : j ∈ inc T K x
    · simp only [hjk, hji, ite_false, ne_eq, not_false_eq_true, and_self, ite_true,
        zero_add]
      have := hc j
      split <;> split <;> linarith
    · have hjx : j ≠ x ∧ rep T K (T.parent j) ≠ x := by
        simp only [inc, Finset.mem_filter, not_and, not_or] at hji
        exact hji hj
      have h1 : f' j = f j := by simp [f', rep_of_mem hjK, hjx.1]
      have h2 : f' (rep T K (T.parent j)) = f (rep T K (T.parent j)) := by
        simp [f', hrr, hjx.2]
      simp [h1, h2, hjk, hji]
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq' S k,
    ← Finset.sum_filter]
  simp only [hkS, ite_true]
  have hfilt : S.filter (fun j => j ≠ k ∧ j ∈ inc T K x) = (inc T K x).erase k := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_erase, inc, S]
    tauto
  rw [hfilt]
  linarith

end Cost

section Count

variable {K : Finset V}

omit [Fintype V] in
/-- In a quotient with at least two vertices, every vertex has an incident edge. -/
theorem inc_nonempty (hroot : T.root ∈ K) (hK : 2 ≤ K.card) {x : V} (hx : x ∈ K) :
    (inc T K x).Nonempty := by
  by_cases hxr : x = T.root
  · subst hxr
    have hne : (K.erase T.root).Nonempty := by
      rw [← Finset.card_pos, Finset.card_erase_of_mem hroot]; omega
    obtain ⟨j, hj, hmin⟩ := (K.erase T.root).exists_min_image T.depth hne
    have hjr := (Finset.mem_erase.mp hj).1
    refine ⟨j, Finset.mem_filter.mpr ⟨hj, Or.inr ?_⟩⟩
    by_contra hq
    have hmem : rep T K (T.parent j) ∈ K.erase T.root :=
      Finset.mem_erase.mpr ⟨hq, rep_mem hroot _⟩
    have h1 := hmin _ hmem
    have h2 := (rep_isAnc (T := T) K (T.parent j)).depth_le
    have h3 := T.depth_parent j hjr
    omega
  · exact ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hxr, hx⟩, Or.inl rfl⟩⟩

omit [Fintype V] in
/-- Handshake identity for the quotient tree on `K`. -/
theorem sum_card_inc (hroot : T.root ∈ K) :
    ∑ x ∈ K, (inc T K x).card = 2 * (K.card - 1) := by
  set S := K.erase T.root
  have hsplit : ∀ x, (inc T K x).card =
      (S.filter fun j => j = x).card + (S.filter fun j => rep T K (T.parent j) = x).card := by
    intro x
    rw [inc, Finset.filter_or, Finset.card_union_of_disjoint]
    rw [Finset.disjoint_filter]
    intro j hj h1 h2
    exact rep_parent_ne (Finset.mem_erase.mp hj).1 (h2.trans h1.symm)
  have h1 : S.card = ∑ x ∈ K, (S.filter fun j => j = x).card :=
    Finset.card_eq_sum_card_fiberwise (f := fun j => j) fun j hj =>
      Finset.mem_of_mem_erase hj
  have h2 : S.card = ∑ x ∈ K, (S.filter fun j => rep T K (T.parent j) = x).card :=
    Finset.card_eq_sum_card_fiberwise fun j _ => rep_mem hroot _
  have hS : S.card = K.card - 1 := Finset.card_erase_of_mem hroot
  simp only [hsplit, Finset.sum_add_distrib, ← h1, ← h2, hS]
  omega

omit [Fintype V] in
/-- The size bound: if every terminal-free class has quotient degree at least three, then
`|K| ≤ 2|C| - 2`. -/
theorem card_le_of_final (hroot : T.root ∈ K) {C : Finset V} (hinj : Set.InjOn (rep T K) C)
    (hK : 2 ≤ K.card)
    (hfin : ∀ x ∈ K, (∀ t ∈ C, rep T K t ≠ x) → 3 ≤ (inc T K x).card) :
    K.card ≤ 2 * C.card - 2 := by
  set TC := C.image (rep T K)
  have hTC : TC ⊆ K := fun x hx => by
    obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp hx
    exact rep_mem hroot t
  have hcard : TC.card = C.card := Finset.card_image_of_injOn hinj
  have hlow1 : TC.card • 1 ≤ ∑ x ∈ TC, (inc T K x).card :=
    Finset.card_nsmul_le_sum _ _ _ fun x hx =>
      Finset.card_pos.mpr (inc_nonempty hroot hK (hTC hx))
  have hlow3 : (K \ TC).card • 3 ≤ ∑ x ∈ K \ TC, (inc T K x).card :=
    Finset.card_nsmul_le_sum _ _ _ fun x hx => by
      obtain ⟨hxK, hxT⟩ := Finset.mem_sdiff.mp hx
      exact hfin x hxK fun t ht h => hxT (Finset.mem_image.mpr ⟨t, ht, h⟩)
  have hsum := Finset.sum_sdiff hTC (f := fun x => (inc T K x).card)
  rw [sum_card_inc hroot] at hsum
  have hsd : (K \ TC).card = K.card - TC.card := Finset.card_sdiff_of_subset hTC
  have hle : TC.card ≤ K.card := Finset.card_le_card hTC
  simp only [smul_eq_mul] at hlow1 hlow3
  omega

end Count

section Main

variable {c : V → ℝ} {C : Finset V}

/-- The invariant of the compression loop. -/
def Inv (T : RootedTree V) (c : V → ℝ) (C K : Finset V) : Prop :=
  T.root ∈ K ∧ Set.InjOn (rep T K) C ∧ Good T c C K

omit [Fintype V] [DecidableEq V] in
theorem sum_le_of_card_le_one {s : Finset V} (hs : s.card ≤ 1) {a : ℝ} (ha : 0 ≤ a)
    (h : ∀ j ∈ s, c j ≤ a) : ∑ j ∈ s, c j ≤ a := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hs with h0 | h1
  · rw [Finset.card_eq_zero.mp h0, Finset.sum_empty]; exact ha
  · obtain ⟨j, rfl⟩ := Finset.card_eq_one.mp h1
    simpa using h j (Finset.mem_singleton_self j)

/-- One compression step: merge a terminal-free class of degree at most two along its
heaviest incident edge. -/
theorem step (hc : ∀ v, 0 ≤ c v) {K : Finset V} (hI : Inv T c C K) (hK : 2 ≤ K.card) {x : V}
    (hxK : x ∈ K) (hxC : ∀ t ∈ C, rep T K t ≠ x) (hdeg : (inc T K x).card ≤ 2) :
    ∃ k ∈ K, Inv T c C (K.erase k) := by
  obtain ⟨hroot, hinj, hgood⟩ := hI
  obtain ⟨k, hkinc, hkmax⟩ := (inc T K x).exists_max_image c (inc_nonempty hroot hK hxK)
  obtain ⟨hkS, hkx⟩ := Finset.mem_filter.mp hkinc
  obtain ⟨hkr, hk⟩ := Finset.mem_erase.mp hkS
  have hx : x = k ∨ x = rep T K (T.parent k) := hkx.imp Eq.symm Eq.symm
  have hsum : ∑ j ∈ (inc T K x).erase k, c j ≤ c k :=
    sum_le_of_card_le_one (by rw [Finset.card_erase_of_mem hkinc]; omega) (hc k)
      fun j hj => hkmax j (Finset.mem_of_mem_erase hj)
  refine ⟨k, hk, Finset.mem_erase.mpr ⟨Ne.symm hkr, hroot⟩, ?_, ?_⟩
  · -- The merged classes are `x`, which has no terminal, and its neighbor.
    intro t₁ h₁ t₂ h₂ heq
    simp only [rep_erase hk hkr] at heq
    have hx₁ := hxC t₁ h₁
    have hx₂ := hxC t₂ h₂
    split at heq <;> split at heq
    · exact hinj h₁ h₂ (by simp_all)
    · rename_i ha hb
      exfalso
      rcases hx with rfl | rfl
      · exact hx₁ ha
      · exact hx₂ heq.symm
    · rename_i ha hb
      exfalso
      rcases hx with rfl | rfl
      · exact hx₂ hb
      · exact hx₁ heq
    · exact hinj h₁ h₂ heq
  · intro g
    obtain ⟨f, hfC, hfK, hfg⟩ := hgood g
    obtain ⟨hf'K, hf'c⟩ := relabel hroot hc hfK hk hkr hx hsum
    refine ⟨_, fun t ht => ?_, hf'K, le_trans hf'c hfg⟩
    simp [hxC t ht, hfC t ht]

/-- Iterating `step` reaches a quotient in which no step applies. -/
theorem exists_final (hc : ∀ v, 0 ≤ c v) :
    ∀ (n : ℕ) (K : Finset V), K.card ≤ n → Inv T c C K →
      ∃ K', Inv T c C K' ∧ (K'.card ≤ 1 ∨
        ∀ x ∈ K', (∀ t ∈ C, rep T K' t ≠ x) → 3 ≤ (inc T K' x).card) := by
  intro n
  induction n with
  | zero => intro K hK hI; exact ⟨K, hI, Or.inl (by omega)⟩
  | succ n ih =>
    intro K hK hI
    by_cases hfin : K.card ≤ 1 ∨ ∀ x ∈ K, (∀ t ∈ C, rep T K t ≠ x) → 3 ≤ (inc T K x).card
    · exact ⟨K, hI, hfin⟩
    push Not at hfin
    obtain ⟨h2, x, hxK, hxC, hdeg⟩ := hfin
    obtain ⟨k, hk, hI'⟩ := step hc hI h2 hxK hxC (by omega)
    exact ih _ (by rw [Finset.card_erase_of_mem hk]; omega) hI'

omit [Fintype V] in
theorem rep_univ [Fintype V] (v : V) : rep T univ v = v := rep_of_mem (Finset.mem_univ v)

/-- Lemma 26. For a rooted tree with nonnegative capacities and any terminal set `C`, there is
a contraction `rep T K` (each vertex goes to its nearest ancestor in `K`) onto at most
`max 1 (2|C| - 2)` vertices, injective on `C`, such that every labeling `ℓ` of `C` has a
minimum-cost extension constant on each fiber. -/
theorem tree_compression (hc : ∀ v, 0 ≤ c v) (C : Finset V) :
    ∃ K : Finset V, T.root ∈ K ∧ (∀ v, rep T K v ∈ K) ∧ K.card ≤ max 1 (2 * C.card - 2) ∧
      Set.InjOn (rep T K) C ∧
      ∀ ℓ : V → Bool, ∃ f : V → Bool, (∀ t ∈ C, f t = ℓ t) ∧ (∀ v, f v = f (rep T K v)) ∧
        ∀ g : V → Bool, (∀ t ∈ C, g t = ℓ t) → cost T c f ≤ cost T c g := by
  have hI : Inv T c C univ :=
    ⟨Finset.mem_univ _, fun a _ b _ h => by simpa [rep_univ] using h,
      fun g => ⟨g, fun _ _ => rfl, fun v => by rw [rep_univ], le_rfl⟩⟩
  obtain ⟨K, ⟨hroot, hinj, hgood⟩, hfin⟩ := exists_final hc _ univ le_rfl hI
  refine ⟨K, hroot, rep_mem hroot, ?_, hinj, fun ℓ => ?_⟩
  · rcases hfin with h | h
    · exact le_trans h (le_max_left _ _)
    · by_cases hK : K.card ≤ 1
      · exact le_trans hK (le_max_left _ _)
      · exact le_trans (card_le_of_final hroot hinj (by omega) h) (le_max_right _ _)
  -- Take a minimum-cost extension, then a fiber-constant one that is no worse.
  obtain ⟨g₀, hg₀, hmin⟩ := (univ.filter fun g : V → Bool => ∀ t ∈ C, g t = ℓ t).exists_min_image
    (cost T c) ⟨ℓ, by simp⟩
  obtain ⟨f, hfC, hfK, hfg⟩ := hgood g₀
  have hg₀C := (Finset.mem_filter.mp hg₀).2
  refine ⟨f, fun t ht => (hfC t ht).trans (hg₀C t ht), hfK, fun g hg => ?_⟩
  exact le_trans hfg (hmin g (by simpa using hg))

end Main

end Discovery
end CutQueryComplexity
