import CutQueryComplexity.DirectedCertificate.Basic
import CutQueryComplexity.AllPairs.Representation

/-! Public cut-equivalent data and finite offline minimization for directed cuts.
The constructors below receive only reconstructed public data, never an input graph. -/
namespace CutQueryComplexity.Reconstruction

open Finset DirectedCertificate
open scoped Classical
noncomputable section

/-- The outgoing-cut function is determined by these two public fields. -/
structure DirectedData (V : Type) where
  sym : WeightedGraph V
  imbalance : V → ℝ

namespace DirectedData
variable {V : Type} [Fintype V] [DecidableEq V]

/-- Evaluated without further queries to the input. -/
def cut (D : DirectedData V) (S : Finset V) : ℝ :=
  (D.sym.cut S + ∑ v ∈ S, D.imbalance v) / 2

@[simp] theorem cut_empty (D : DirectedData V) : D.cut ∅ = 0 := by
  simp [cut, WeightedGraph.cut]

theorem cut_correct (D : DirectedData V) (G : WeightedDiGraph V)
    (hs : D.sym = G.sym) (hb : D.imbalance = G.imbalance) (S : Finset V) :
    D.cut S = G.out S := by
  rw [cut, hs, hb, ← G.two_mul_out S]
  ring

/-- Total finite minimization, with the empty shore for an empty feasible domain. -/
def minimize (D : DirectedData V) (Q : Finset (Finset V)) : Finset V :=
  if h : Q.Nonempty then Classical.choose (Finset.exists_mem_eq_inf' h D.cut) else ∅

theorem minimize_spec (D : DirectedData V) (Q : Finset (Finset V))
    (h : Q.Nonempty) : D.minimize Q ∈ Q ∧ ∀ T ∈ Q, D.cut (D.minimize Q) ≤ D.cut T := by
  have he := Classical.choose_spec (Finset.exists_mem_eq_inf' h D.cut)
  simp only [minimize, dite_eq_left h]
  exact ⟨he.1, fun T hT => by rw [← he.2]; exact Finset.inf'_le _ hT⟩

def terminalShores (s t : V) : Finset (Finset V) :=
  Finset.univ.filter fun S => s ∈ S ∧ t ∉ S

def offlineST (D : DirectedData V) (s t : V) : Finset V :=
  D.minimize (terminalShores s t)

def terminalAnswer (D : DirectedData V) (s t : V) : AllPairs.STAnswer V :=
  ⟨D.offlineST s t, D.cut (D.offlineST s t)⟩

def allPairsAnswers (D : DirectedData V) : AllPairs.Answers V := D.terminalAnswer

def offlineGlobal (D : DirectedData V) : Finset V := D.minimize (properShores V)

def globalAnswer (D : DirectedData V) : AllPairs.STAnswer V :=
  ⟨D.offlineGlobal, D.cut D.offlineGlobal⟩

@[simp] theorem terminalAnswer_self (D : DirectedData V) (s : V) :
    D.terminalAnswer s s = ⟨∅, 0⟩ := by
  have h : terminalShores s s = ∅ := by ext S; simp [terminalShores]
  simp [terminalAnswer, offlineST, h, minimize]

theorem globalAnswer_tiny (D : DirectedData V) (hn : Fintype.card V < 2) :
    D.globalAnswer = ⟨∅, 0⟩ := by
  have h : properShores V = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro S hS
    have hp := (mem_properShores S).mp hS
    have hcard : S.card < Fintype.card V := by
      exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, hp.2⟩)
    have hpos := Finset.card_pos.mpr hp.1
    omega
  simp [globalAnswer, offlineGlobal, h, minimize]

theorem terminalAnswer_correct (D : DirectedData V) (G : WeightedDiGraph V)
    (hs : D.sym = G.sym) (hb : D.imbalance = G.imbalance)
    {s t : V} (hst : s ≠ t) :
    s ∈ (D.terminalAnswer s t).shore ∧ t ∉ (D.terminalAnswer s t).shore ∧
      (D.terminalAnswer s t).value = G.out (D.terminalAnswer s t).shore ∧
      ∀ T, s ∈ T → t ∉ T →
        G.out (D.terminalAnswer s t).shore ≤ G.out T := by
  have hn : (terminalShores s t).Nonempty := ⟨{s}, by simp [terminalShores, Ne.symm hst]⟩
  obtain ⟨hm, hl⟩ := D.minimize_spec (terminalShores s t) hn
  have hm' : s ∈ D.offlineST s t ∧ t ∉ D.offlineST s t := by
    simpa [offlineST, terminalShores] using hm
  refine ⟨hm'.1, hm'.2, D.cut_correct G hs hb _, fun T hsT htT => ?_⟩
  have h := hl T (by simp [terminalShores, hsT, htT])
  simpa only [terminalAnswer, offlineST, cut_correct D G hs hb] using h

theorem allPairsAnswers_correct (D : DirectedData V) (G : WeightedDiGraph V)
    (hs : D.sym = G.sym) (hb : D.imbalance = G.imbalance) :
    ∀ s t, s ≠ t →
      s ∈ (D.allPairsAnswers s t).shore ∧ t ∉ (D.allPairsAnswers s t).shore ∧
      (D.allPairsAnswers s t).value = G.out (D.allPairsAnswers s t).shore ∧
      ∀ T, s ∈ T → t ∉ T → G.out (D.allPairsAnswers s t).shore ≤ G.out T :=
  fun _ _ hst => D.terminalAnswer_correct G hs hb hst

theorem globalAnswer_correct (D : DirectedData V) (G : WeightedDiGraph V)
    (hs : D.sym = G.sym) (hb : D.imbalance = G.imbalance)
    (hn : 2 ≤ Fintype.card V) :
    IsGlobalMinCut G D.globalAnswer.shore ∧
      D.globalAnswer.value = G.out D.globalAnswer.shore ∧
      D.globalAnswer.value = G.minValue := by
  obtain ⟨v⟩ := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card V)
  have hne : (properShores V).Nonempty :=
    ⟨{v}, (mem_properShores _).mpr (properShore_singleton v hn)⟩
  obtain ⟨hm, hl⟩ := D.minimize_spec (properShores V) hne
  have hg : IsGlobalMinCut G D.globalAnswer.shore := by
    refine ⟨(mem_properShores _).mp hm, fun T hT => ?_⟩
    have h := hl T ((mem_properShores _).mpr hT)
    simpa only [globalAnswer, offlineGlobal, cut_correct D G hs hb] using h
  have hv : D.globalAnswer.value = G.out D.globalAnswer.shore := D.cut_correct G hs hb _
  exact ⟨hg, hv, hv.trans hg.out_eq_minValue⟩

end DirectedData
end
end CutQueryComplexity.Reconstruction
