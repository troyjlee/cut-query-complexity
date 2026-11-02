import CutQueryComplexity.Spanner.Reach

/-! # One spanner trial and its stretch (D2; source `lem:stretch`)

Pairs are ordered by an injective key (length, then a unique ID); lengths are monotone in the key
(`hmono`). A phase acts on a frozen old state `State` (residual pairs `E`, cluster labels `lab`
naming the cluster center, selected pairs `H`) and the old-cluster coins `coin`.

* A vertex in a sampled old cluster keeps its label and reports nothing.
* Another vertex `a` finds `f_a`, its minimum-key residual pair into a sampled cluster
  (`toSamp`), and for each old cluster `D` its minimum-key pair `f(a, D)` into `D` (`toClus`).
  It reports `D` when `key f(a, D) ≤ key f_a` (all adjacent clusters when `f_a` is absent).
* Each report selects `f(a, D)` and deletes the entire old block of residual pairs from `a`
  into `D` (`Del`). `a` takes the label of `f_a`'s endpoint, or becomes inactive.
* After all reports, the block deletions and new labels are applied together, and pairs with
  equal new labels are removed (`step`).

`Inv m` is the source invariant. Every residual pair has active endpoints with distinct labels,
and each endpoint reaches its center through at most `m` selected pairs, each no longer than the
residual pair (`Inv.path`). Every original pair is still residual or already has a replacement
of at most `α` pairs, each no longer than it (`Inv.done`). `inv_step` proves one phase, for every
choice of coins. The final phase has no sampled cluster, so it deletes every residual pair
(`step_E_eq_empty`).

`trial_stretch`: for every coin sequence, the completed `k`-phase trial is an `α = 2k − 1`
spanner of the original support. `trial_path` gives the path form with total length at most
`(2k − 1) ℓ_e`.
-/

namespace CutQueryComplexity
namespace Spanner

open Finset

noncomputable section
open Classical

variable {V : Type} [Fintype V] [DecidableEq V] {κ : Type} [LinearOrder κ]

/-- The frozen state at the start of a phase. -/
structure State (V : Type) where
  E : Finset (Sym2 V)
  lab : V → Option V
  H : Finset (Sym2 V)

variable (key : Sym2 V → κ)

/-- The minimum-key pair from `a` into `U`, named by its other endpoint. -/
def minNbr (a : V) (U : Finset V) : Option V :=
  if h : U.Nonempty then some (Classical.choose (U.exists_min_image (fun u => key s(a, u)) h))
  else none

omit [Fintype V] [DecidableEq V] in
theorem minNbr_some {a : V} {U : Finset V} {y : V} (h : minNbr key a U = some y) :
    y ∈ U ∧ ∀ u ∈ U, key s(a, y) ≤ key s(a, u) := by
  unfold minNbr at h
  split_ifs at h with hU
  · cases h
    exact Classical.choose_spec (U.exists_min_image (fun u => key s(a, u)) hU)

omit [Fintype V] [DecidableEq V] in
theorem exists_minNbr {a : V} {U : Finset V} (h : U.Nonempty) : ∃ y, minNbr key a U = some y := by
  unfold minNbr; simp only [h, ↓reduceDIte]; exact ⟨_, rfl⟩

omit [Fintype V] [DecidableEq V] in
theorem minNbr_eq_none {a : V} {U : Finset V} (h : U = ∅) : minNbr key a U = none := by
  unfold minNbr; simp [h]

variable (coin : V → Bool) (st : State V)

/-- `a` lies in a sampled old cluster. -/
def Samp (a : V) : Prop := ∃ c, st.lab a = some c ∧ coin c = true

/-- Residual neighbors of `a` in sampled old clusters. -/
def toSamp (a : V) : Finset V := univ.filter fun u => s(a, u) ∈ st.E ∧ Samp coin st u

/-- Residual neighbors of `a` in the old cluster `D`. -/
def toClus (a D : V) : Finset V := univ.filter fun u => s(a, u) ∈ st.E ∧ st.lab u = some D

/-- `a` reports the old cluster `D`. -/
def Reported (a D : V) : Prop :=
  ¬ Samp coin st a ∧ ∃ y, minNbr key a (toClus st a D) = some y ∧
    ∀ z, minNbr key a (toSamp coin st a) = some z → key s(a, y) ≤ key s(a, z)

/-- The new label. -/
def newLab (a : V) : Option V :=
  if Samp coin st a then st.lab a else (minNbr key a (toSamp coin st a)).bind st.lab

/-- The residual pair lies in a reported old block. -/
def Del (e : Sym2 V) : Prop :=
  ∃ a b D, e = s(a, b) ∧ st.lab b = some D ∧ Reported key coin st a D

/-- The endpoints receive equal new labels. -/
def SameNew (e : Sym2 V) : Prop :=
  ∃ a b, e = s(a, b) ∧ newLab key coin st a = newLab key coin st b

/-- The selected pairs `f(a, D)` of all reports. -/
def selected : Finset (Sym2 V) :=
  univ.filter fun f => ∃ a D y, Reported key coin st a D ∧
    minNbr key a (toClus st a D) = some y ∧ f = s(a, y)

/-- **One phase.** -/
def step : State V where
  E := st.E.filter fun e => ¬ Del key coin st e ∧ ¬ SameNew key coin st e
  lab := newLab key coin st
  H := st.H ∪ selected key coin st

variable (ℓ : Sym2 V → ℝ)

/-- **The phase invariant** after `m` phases, with stretch target `α`. -/
structure Inv (E0 : Finset (Sym2 V)) (α m : ℕ) (st : State V) : Prop where
  sub : st.E ⊆ E0
  Hsub : st.H ⊆ E0
  edge : ∀ a b, s(a, b) ∈ st.E →
    a ≠ b ∧ (∃ c, st.lab a = some c) ∧ (∃ c, st.lab b = some c) ∧ st.lab a ≠ st.lab b
  path : ∀ a b, s(a, b) ∈ st.E → ∀ c, st.lab a = some c → Reach ℓ st.H (ℓ s(a, b)) m a c
  done : ∀ a b, s(a, b) ∈ E0 → s(a, b) ∈ st.E ∨ Reach ℓ st.H (ℓ s(a, b)) α a b

variable {key coin st ℓ}

theorem mem_toClus {a D u : V} : u ∈ toClus st a D ↔ s(a, u) ∈ st.E ∧ st.lab u = some D := by
  simp [toClus]

theorem mem_toSamp {a u : V} : u ∈ toSamp coin st a ↔ s(a, u) ∈ st.E ∧ Samp coin st u := by
  simp [toSamp]

theorem selected_mem {a D y : V} (hr : Reported key coin st a D)
    (hy : minNbr key a (toClus st a D) = some y) : s(a, y) ∈ (step key coin st).H :=
  mem_union_right _ (mem_filter.mpr ⟨mem_univ _, a, D, y, hr, hy, rfl⟩)

theorem H_subset_step : st.H ⊆ (step key coin st).H := subset_union_left

section Phase

variable (hinj : Function.Injective key) (hmono : ∀ e f, key f ≤ key e → ℓ f ≤ ℓ e)
variable {E0 : Finset (Sym2 V)} {α m : ℕ}
include hinj hmono

/-- An endpoint of a pair that its block deletions spare gets a new label and a center path. -/
theorem survivor (hI : Inv ℓ E0 α m st) {a b : V} (he : s(a, b) ∈ st.E)
    (hnd : ¬ ∃ D, st.lab b = some D ∧ Reported key coin st a D) :
    ∃ c, newLab key coin st a = some c ∧
      Reach ℓ (step key coin st).H (ℓ s(a, b)) (m + 1) a c := by
  by_cases hs : Samp coin st a
  · obtain ⟨c, hc, -⟩ := id hs
    refine ⟨c, by simp [newLab, hs, hc], ?_⟩
    exact (hI.path a b he c hc).mono (H_subset_step (key := key) (coin := coin) (st := st)) le_rfl (Nat.le_succ m)
  · obtain ⟨-, -, ⟨D, hD⟩, -⟩ := hI.edge a b he
    have hbD : b ∈ toClus st a D := mem_toClus.mpr ⟨he, hD⟩
    obtain ⟨y0, hy0⟩ := exists_minNbr key ⟨b, hbD⟩ (a := a)
    have hy0le := (minNbr_some key hy0).2 b hbD
    -- not reported: some sampled pair is strictly smaller
    have hnr : ¬ Reported key coin st a D := fun hr => hnd ⟨D, hD, hr⟩
    simp only [Reported, not_and, not_exists, not_forall] at hnr
    obtain ⟨z, hz, hlt⟩ := hnr hs y0 hy0
    have hlt' : key s(a, z) < key s(a, y0) := lt_of_not_ge hlt
    obtain ⟨hzS, hzmin⟩ := minNbr_some key hz
    obtain ⟨hzE, c', hzc, hcoin⟩ := mem_toSamp.mp hzS
    refine ⟨c', by simp [newLab, hs, hz, hzc], ?_⟩
    -- the pair `f_a = s(a, z)` was selected
    have hzC : z ∈ toClus st a c' := mem_toClus.mpr ⟨hzE, hzc⟩
    obtain ⟨z', hz'⟩ := exists_minNbr key ⟨z, hzC⟩ (a := a)
    obtain ⟨hz'C, hz'min⟩ := minNbr_some key hz'
    obtain ⟨hz'E, hz'c⟩ := mem_toClus.mp hz'C
    have hz'S : z' ∈ toSamp coin st a := mem_toSamp.mpr ⟨hz'E, c', hz'c, hcoin⟩
    have hkey : key s(a, z') = key s(a, z) :=
      le_antisymm (hz'min z hzC) (hzmin z' hz'S)
    have hsame : s(a, z') = s(a, z) := hinj hkey
    have hrep : Reported key coin st a c' := ⟨hs, z', hz', fun w hw => by
      rw [hz] at hw; cases hw; exact le_of_eq hkey⟩
    have hsel : s(a, z) ∈ (step key coin st).H := hsame ▸ selected_mem hrep hz'
    have hne : a ≠ z := (hI.edge a z hzE).1
    have hlen : ℓ s(a, z) ≤ ℓ s(a, b) := hmono _ _ (hlt'.le.trans hy0le)
    have hzpath := hI.path z a (by rwa [Sym2.eq_swap]) c' hzc
    rw [Sym2.eq_swap] at hzpath
    exact Reach.step hne hsel hlen (hzpath.mono (H_subset_step (key := key) (coin := coin) (st := st)) hlen le_rfl)

omit hinj in
/-- A pair deleted through a reported block has a replacement of `2m + 1` pairs. -/
theorem blocked (hI : Inv ℓ E0 α m st) {a b D : V} (he : s(a, b) ∈ st.E)
    (hD : st.lab b = some D) (hr : Reported key coin st a D) :
    Reach ℓ (step key coin st).H (ℓ s(a, b)) (2 * m + 1) a b := by
  obtain ⟨-, y, hy, -⟩ := id hr
  obtain ⟨hyC, hymin⟩ := minNbr_some key hy
  obtain ⟨hyE, hyD⟩ := mem_toClus.mp hyC
  have hlen : ℓ s(a, y) ≤ ℓ s(a, b) := hmono _ _ (hymin b (mem_toClus.mpr ⟨he, hD⟩))
  have hsel := selected_mem hr hy
  have hne : a ≠ y := (hI.edge a y hyE).1
  have p1 := hI.path y a (by rwa [Sym2.eq_swap]) D hyD
  rw [Sym2.eq_swap] at p1
  have p2 := hI.path b a (by rwa [Sym2.eq_swap]) D hD
  rw [Sym2.eq_swap] at p2
  have q1 := p1.mono (H_subset_step (key := key) (coin := coin) (st := st)) hlen le_rfl
  have q2 := (p2.mono (H_subset_step (key := key) (coin := coin) (st := st)) le_rfl le_rfl).symm
  have := (Reach.single hne hsel hlen).trans (q1.trans q2)
  exact this.mono subset_rfl le_rfl (by omega)

omit hinj hmono in
/-- With no sampled cluster, every residual pair lies in a reported block. -/
theorem del_of_final (hI : Inv ℓ E0 α m st) (hcoin : ∀ c, coin c = false) {a b : V}
    (he : s(a, b) ∈ st.E) : Del key coin st s(a, b) := by
  obtain ⟨-, -, ⟨D, hD⟩, -⟩ := hI.edge a b he
  have hns : ∀ u, ¬ Samp coin st u := fun u ⟨c, _, hc⟩ => by simp [hcoin c] at hc
  have hbD : b ∈ toClus st a D := mem_toClus.mpr ⟨he, hD⟩
  obtain ⟨y, hy⟩ := exists_minNbr key ⟨b, hbD⟩ (a := a)
  have hS : toSamp coin st a = ∅ := by
    ext u; simp [mem_toSamp, hns u]
  refine ⟨a, b, D, rfl, hD, hns a, y, hy, fun z hz => ?_⟩
  rw [minNbr_eq_none key hS] at hz; cases hz

omit hinj hmono in
/-- The final phase deletes every residual pair. -/
theorem step_E_eq_empty (hI : Inv ℓ E0 α m st) (hcoin : ∀ c, coin c = false) :
    (step key coin st).E = ∅ := by
  ext e
  simp only [step, mem_filter, Finset.notMem_empty, iff_false, not_and, not_not]
  intro he
  induction e using Sym2.ind with
  | h a b => exact fun hnd => absurd (del_of_final hI hcoin he) hnd

/-- **One phase preserves the invariant**, for every choice of coins. -/
theorem inv_step (hI : Inv ℓ E0 α m st) (h1 : 2 * m + 1 ≤ α)
    (h2 : 2 * (m + 1) ≤ α ∨ ∀ c, coin c = false) :
    Inv ℓ E0 α (m + 1) (step key coin st) := by
  have hnotDel : ∀ a b, ¬ Del key coin st s(a, b) →
      ¬ ∃ D, st.lab b = some D ∧ Reported key coin st a D :=
    fun a b hnd ⟨D, hD, hr⟩ => hnd ⟨a, b, D, rfl, hD, hr⟩
  have hnotDel' : ∀ a b, ¬ Del key coin st s(a, b) →
      ¬ ∃ D, st.lab a = some D ∧ Reported key coin st b D :=
    fun a b hnd ⟨D, hD, hr⟩ => hnd ⟨b, a, D, Sym2.eq_swap, hD, hr⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (filter_subset _ _).trans hI.sub
  · intro f hf
    rcases mem_union.mp hf with hf | hf
    · exact hI.Hsub hf
    · obtain ⟨-, a, D, y, -, hy, rfl⟩ := mem_filter.mp hf
      exact hI.sub (mem_toClus.mp (minNbr_some key hy).1).1
  · intro a b he
    obtain ⟨heE, hnd, hns⟩ := mem_filter.mp he
    obtain ⟨ca, hca, -⟩ := survivor hinj hmono hI heE (hnotDel a b hnd)
    obtain ⟨cb, hcb, -⟩ := survivor hinj hmono hI (by rwa [Sym2.eq_swap]) (hnotDel' a b hnd)
    refine ⟨(hI.edge a b heE).1, ⟨ca, hca⟩, ⟨cb, hcb⟩, fun heq => hns ⟨a, b, rfl, heq⟩⟩
  · intro a b he c hc
    obtain ⟨heE, hnd, -⟩ := mem_filter.mp he
    obtain ⟨c', hc', hp⟩ := survivor hinj hmono hI heE (hnotDel a b hnd)
    have : c = c' := by
      have h := hc.symm.trans hc'
      exact Option.some_injective _ h
    subst this; exact hp
  · intro a b he0
    rcases hI.done a b he0 with he | hp
    · by_cases hdel : Del key coin st s(a, b)
      · right
        obtain ⟨a', b', D, heq, hD, hr⟩ := hdel
        have he' : s(a', b') ∈ st.E := heq ▸ he
        have hb := (blocked hmono hI he' hD hr).mono subset_rfl le_rfl h1
        rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hb
        · rw [Sym2.eq_swap]; exact hb.symm
      · by_cases hsame : SameNew key coin st s(a, b)
        · right
          obtain ⟨a', b', heq, hlab⟩ := hsame
          have hnd' : ¬ Del key coin st s(a', b') := heq ▸ hdel
          have he' : s(a', b') ∈ st.E := heq ▸ he
          obtain ⟨ca, hca, pa⟩ := survivor hinj hmono hI he' (hnotDel a' b' hnd')
          obtain ⟨cb, hcb, pb⟩ := survivor hinj hmono hI (by rwa [Sym2.eq_swap])
            (hnotDel' a' b' hnd')
          rw [Sym2.eq_swap] at pb
          have hcc : ca = cb := Option.some_injective _ (hca.symm.trans (hlab.trans hcb))
          subst hcc
          have h2' : 2 * (m + 1) ≤ α := by
            rcases h2 with h2 | hcoin
            · exact h2
            · exact absurd (del_of_final hI hcoin he') hnd'
          have hb : Reach ℓ (step key coin st).H (ℓ s(a', b')) α a' b' :=
            (pa.trans pb.symm).mono subset_rfl le_rfl (by omega)
          rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact hb
          · rw [Sym2.eq_swap]; exact hb.symm
        · left; exact mem_filter.mpr ⟨he, hdel, hsame⟩
    · right; exact hp.mono (H_subset_step (key := key) (coin := coin) (st := st)) le_rfl le_rfl

end Phase

/-! ## The completed trial -/

variable (key)

/-- The initial state: the original support, singleton clusters, nothing selected. -/
def init (E0 : Finset (Sym2 V)) : State V := ⟨E0, some, ∅⟩

/-- The nonfinal phases, with coins `coins j` in phase `j + 1`. -/
def runPhases (coins : ℕ → V → Bool) (E0 : Finset (Sym2 V)) : ℕ → State V
  | 0 => init E0
  | j + 1 => step key (coins j) (runPhases coins E0 j)

/-- A trial of `k` phases: `k − 1` sampled phases, then the final phase with no sampled cluster. -/
def trial (coins : ℕ → V → Bool) (E0 : Finset (Sym2 V)) (k : ℕ) : State V :=
  step key (fun _ => false) (runPhases key coins E0 (k - 1))

variable {key}

omit [Fintype V] [DecidableEq V] in
theorem inv_init {E0 : Finset (Sym2 V)} (hE0 : ∀ a b, s(a, b) ∈ E0 → a ≠ b) (α : ℕ) :
    Inv ℓ E0 α 0 (init E0) where
  sub := subset_rfl
  Hsub := by simp [init]
  edge a b he := ⟨hE0 a b he, ⟨a, rfl⟩, ⟨b, rfl⟩, by simpa [init] using hE0 a b he⟩
  path a b _ c hc := by
    simp only [init, Option.some.injEq] at hc
    subst hc; exact Reach.refl 0 a
  done a b he := Or.inl he

/-- **Stretch for every completed trial** (source `lem:stretch`). For every coin sequence, every
original pair `ab` is joined in the output by at most `2k − 1` selected pairs, each no longer
than `ab`; the output is supported in the original pairs. -/
theorem trial_stretch (hinj : Function.Injective key) (hmono : ∀ e f, key f ≤ key e → ℓ f ≤ ℓ e)
    {E0 : Finset (Sym2 V)} (hE0 : ∀ a b, s(a, b) ∈ E0 → a ≠ b) (coins : ℕ → V → Bool)
    {k : ℕ} (hk : 1 ≤ k) :
    (trial key coins E0 k).H ⊆ E0 ∧ (trial key coins E0 k).E = ∅ ∧
      ∀ a b, s(a, b) ∈ E0 →
        Reach ℓ (trial key coins E0 k).H (ℓ s(a, b)) (2 * k - 1) a b := by
  have hrun : ∀ j, j ≤ k - 1 → Inv ℓ E0 (2 * k - 1) j (runPhases key coins E0 j) := by
    intro j
    induction j with
    | zero => intro _; exact inv_init hE0 _
    | succ j ih =>
        intro hj
        exact inv_step hinj hmono (ih (by omega)) (by omega) (Or.inl (by omega))
  have hfin := inv_step hinj hmono (hrun (k - 1) le_rfl) (by omega) (Or.inr fun _ => rfl)
  refine ⟨hfin.Hsub, step_E_eq_empty (hrun (k - 1) le_rfl) (fun _ => rfl), ?_⟩
  intro a b he
  rcases hfin.done a b he with h | h
  · rw [step_E_eq_empty (hrun (k - 1) le_rfl) (fun _ => rfl)] at h
    exact absurd h (Finset.notMem_empty _)
  · exact h

/-- **The path form**: total length at most `(2k − 1) ℓ_{ab}` for nonnegative lengths. -/
theorem trial_path (hinj : Function.Injective key) (hmono : ∀ e f, key f ≤ key e → ℓ f ≤ ℓ e)
    (hℓ : ∀ e, 0 ≤ ℓ e) {E0 : Finset (Sym2 V)} (hE0 : ∀ a b, s(a, b) ∈ E0 → a ≠ b)
    (coins : ℕ → V → Bool) {k : ℕ} (hk : 1 ≤ k) {a b : V} (he : s(a, b) ∈ E0) :
    ∃ p : (Spectral.pairGraph (trial key coins E0 k).H).Walk a b,
      p.IsPath ∧ (p.edges.map ℓ).sum ≤ (2 * k - 1 : ℕ) * ℓ s(a, b) :=
  ((trial_stretch hinj hmono hE0 coins hk).2.2 a b he).exists_path (hℓ _)

end

end Spanner
end CutQueryComplexity
