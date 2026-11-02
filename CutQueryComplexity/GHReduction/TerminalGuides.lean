import CutQueryComplexity.Certificate.SplittingOff
import CutQueryComplexity.Graph.VertexRestriction
import CutQueryComplexity.MinCut.TreePacking

/-! # Public terminal guide distributions

The graph `K` in the definitions below is explicit public data. Splitting off
nonterminals and then packing trees on the actual subtype `U` gives abstract
guide trees. Their edges need not be edges of `K` or of a hidden input graph.

No single-source solver or Gomory-Hu reduction is assumed here. This module
constructs only the guide distribution, including the finite minimum used to
choose its connectivity parameter from `K`.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction

noncomputable section
open scoped Classical
open WeightedGraph Certificate

variable {V : Type} [Fintype V] [DecidableEq V]

/-- A proper shore inside `U` also separates the ambient terminal set. -/
theorem localShore_separates {U S : Finset V} (h : LocalShore U S) :
    Separates U S := by
  obtain ⟨hsub, ⟨a, ha⟩, ⟨b, hb⟩⟩ := h
  refine ⟨⟨a, Finset.mem_inter.mpr ⟨ha, hsub ha⟩⟩, ?_⟩
  intro hall
  exact (Finset.mem_sdiff.mp hb).2 (hall (Finset.mem_sdiff.mp hb).1)

/-- All ambient shores separating at least two terminals. Nonterminals remain
available on either side; this is not the induced minimum cut on `U`. -/
def terminalShores (U : Finset V) : Finset (Finset V) :=
  Finset.univ.filter (Separates U)

@[simp] theorem mem_terminalShores (U S : Finset V) :
    S ∈ terminalShores U ↔ Separates U S := by
  simp [terminalShores]

theorem terminalShores_nonempty {U : Finset V} (hU : 2 ≤ U.card) :
    (terminalShores U).Nonempty := by
  obtain ⟨S, hS⟩ := (localShores_nonempty_iff U).mpr hU
  exact ⟨S, (mem_terminalShores U S).mpr
    (localShore_separates ((mem_localShores U S).mp hS))⟩

/-- The explicit graph's terminal connectivity, with zero when there is no
terminal-separating shore. -/
def terminalMin (K : WeightedGraph V) (U : Finset V) : ℝ :=
  if h : (terminalShores U).Nonempty then (terminalShores U).inf' h K.cut else 0

theorem terminalMin_nonneg (K : WeightedGraph V) (U : Finset V) :
    0 ≤ terminalMin K U := by
  unfold terminalMin
  split
  · exact Finset.le_inf' _ _ (fun S _ => K.cut_nonneg S)
  · exact le_rfl

theorem terminalMin_le (K : WeightedGraph V) {U S : Finset V}
    (hS : Separates U S) : terminalMin K U ≤ K.cut S := by
  have hm := (mem_terminalShores U S).mpr hS
  rw [terminalMin, dite_eq_left ⟨S, hm⟩]
  exact Finset.inf'_le _ hm

theorem le_terminalMin (K : WeightedGraph V) {U : Finset V} (hU : 2 ≤ U.card)
    {lam : ℝ} (hcut : ∀ S, Separates U S → lam ≤ K.cut S) :
    lam ≤ terminalMin K U := by
  rw [terminalMin, dite_eq_left (terminalShores_nonempty hU)]
  exact Finset.le_inf' _ _ (fun S hS => hcut S ((mem_terminalShores U S).mp hS))

theorem exists_terminalMin (K : WeightedGraph V) {U : Finset V}
    (hU : 2 ≤ U.card) :
    ∃ S, Separates U S ∧ K.cut S = terminalMin K U := by
  have hne := terminalShores_nonempty hU
  obtain ⟨S, hS, he⟩ := Finset.exists_mem_eq_inf' hne K.cut
  refine ⟨S, (mem_terminalShores U S).mp hS, ?_⟩
  rw [terminalMin, dite_eq_left hne, he]

/-- Restriction removes isolated outside labels without changing any cut. -/
theorem onVertices_cut_eq_of_support (J : WeightedGraph V) (U : Finset V)
    (hJ : ∀ x y, x ∉ U → J.w x y = 0) (S : Finset V) :
    (J.onVertices U).cut (projectShore U S) = J.cut S := by
  have hind : J.induce U = J := by
    ext x y
    by_cases hx : x ∈ U
    · by_cases hy : y ∈ U
      · simp [WeightedGraph.induce, hx, hy]
      · have hz : J.w x y = 0 := by
          rw [J.symm]
          exact hJ y x hy
        simp [WeightedGraph.induce, hx, hy, hz]
    · simp [WeightedGraph.induce, hx, hJ x y hx]
  rw [J.onVertices_cut_project, localCut_eq_cut_induce, hind]

/-- Splitting-off followed by global tree packing on the actual terminal type.
The same distribution satisfies the bound for every ambient shore. -/
theorem exists_terminalGuide_pmf (K : WeightedGraph V) (U : Finset V)
    {lam : ℝ} (hlam : 0 < lam) (hU : 2 ≤ U.card)
    (hcut : ∀ S, Separates U S → lam ≤ K.cut S) :
    ∃ P : PMF (RootedTree U), ∀ S : Finset V,
      Probability.mass P (fun T => 3 ≤ (T.crossSet (projectShore U S)).card) ≤
        ENNReal.ofReal (2 * K.cut S / (3 * lam)) := by
  obtain ⟨J, hJ, hJK, hconn⟩ := Certificate.exists_splitOff K U lam hcut
  have hrestricted : ∀ S : Finset U, ProperShore S → lam ≤ (J.onVertices U).cut S := by
    intro S hS
    have he := onVertices_cut_eq_of_support J U hJ (liftShore U S)
    rw [project_liftShore] at he
    rw [he]
    exact hconn _ (localShore_separates (localShore_lift hS))
  obtain ⟨a, ha⟩ : U.Nonempty := Finset.card_pos.mp (by omega)
  have hdec : (fun x y : U => Classical.propDecidable (x = y)) =
      (inferInstance : DecidableEq U) := Subsingleton.elim _ _
  have hcutPacking (S : Finset U) :
      @WeightedGraph.cut U (Finset.Subtype.fintype U)
        (fun x y => Classical.propDecidable (x = y)) (J.onVertices U) S =
          (J.onVertices U).cut S := by rw [hdec]
  obtain ⟨P, hP⟩ := @TreePacking.exists_tree_pmf U (Finset.Subtype.fintype U)
    (J.onVertices U) lam hlam (fun S hS => by
      rw [hcutPacking]
      exact hrestricted S hS)
    (show Nonempty U from ⟨⟨a, ha⟩⟩)
  refine ⟨P, fun S => ?_⟩
  calc
    _ ≤ ENNReal.ofReal (2 * (J.onVertices U).cut (projectShore U S) / (3 * lam)) :=
      by simpa only [hcutPacking] using hP (projectShore U S)
    _ = ENNReal.ofReal (2 * J.cut S / (3 * lam)) := by
      rw [onVertices_cut_eq_of_support J U hJ]
    _ ≤ ENNReal.ofReal (2 * K.cut S / (3 * lam)) := by
      apply ENNReal.ofReal_le_ofReal
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hJK S) (by norm_num))
        (by positivity)

/-- Select a distribution using only the explicit graph and public terminals.
The remaining arguments are properties of this explicit data. -/
def terminalGuidePMF (K : WeightedGraph V) (U : Finset V) (hU : 2 ≤ U.card)
    (hpos : 0 < terminalMin K U) : PMF (RootedTree U) :=
  Classical.choose (exists_terminalGuide_pmf K U hpos hU
    (fun _ hS => terminalMin_le K hS))

theorem terminalGuidePMF_spec (K : WeightedGraph V) (U : Finset V)
    (hU : 2 ≤ U.card) (hpos : 0 < terminalMin K U) (S : Finset V) :
    Probability.mass (terminalGuidePMF K U hU hpos)
      (fun T => 3 ≤ (T.crossSet (projectShore U S)).card) ≤
        ENNReal.ofReal (2 * K.cut S / (3 * terminalMin K U)) :=
  Classical.choose_spec (exists_terminalGuide_pmf K U hpos hU
    (fun _ hS => terminalMin_le K hS)) S

/-- Multiplicative lower bounds pass to terminal connectivity. This is a
deterministic statement, so it also applies to adaptively chosen terminal sets. -/
theorem terminalMin_lower_of_cut_lower (F K : WeightedGraph V) {U : Finset V}
    (hU : 2 ≤ U.card) {c : ℝ} (hc : 0 ≤ c)
    (hcut : ∀ S, c * F.cut S ≤ K.cut S) :
    c * terminalMin F U ≤ terminalMin K U := by
  apply le_terminalMin K hU
  intro S hS
  exact (mul_le_mul_of_nonneg_left (terminalMin_le F hS) hc).trans (hcut S)

theorem terminalMin_pos_of_approx (F K : WeightedGraph V) {U : Finset V}
    (hU : 2 ≤ U.card) (hpos : 0 < terminalMin F U)
    (hcut : ∀ S, (99 / 100 : ℝ) * F.cut S ≤ K.cut S) :
    0 < terminalMin K U := by
  exact lt_of_lt_of_le (mul_pos (by norm_num) hpos)
    (terminalMin_lower_of_cut_lower F K hU (by norm_num) hcut)

/-- A true cut within `11/10` of terminal connectivity is missed with probability
at most `3/4`. Its optimality, if needed, is a separate semantic hypothesis;
the distribution does not use the hidden graph `F` or the shore `S`. -/
theorem terminalGuidePMF_failure_le (F K : WeightedGraph V) (U : Finset V)
    (hU : 2 ≤ U.card) (hposK : 0 < terminalMin K U)
    (happrox : ∀ S, (99 / 100 : ℝ) * F.cut S ≤ K.cut S ∧
      K.cut S ≤ (101 / 100 : ℝ) * F.cut S)
    (S : Finset V) (hsmall : F.cut S ≤ (11 / 10 : ℝ) * terminalMin F U) :
    Probability.mass (terminalGuidePMF K U hU hposK)
      (fun T => 3 ≤ (T.crossSet (projectShore U S)).card) ≤
        ENNReal.ofReal (3 / 4 : ℝ) := by
  refine (terminalGuidePMF_spec K U hU hposK S).trans ?_
  apply ENNReal.ofReal_le_ofReal
  rw [div_le_iff₀ (by positivity : 0 < 3 * terminalMin K U)]
  have hmin := terminalMin_lower_of_cut_lower F K hU (by norm_num : (0 : ℝ) ≤ 99 / 100)
    (fun A => (happrox A).1)
  have hupper := (happrox S).2
  have hnonneg := terminalMin_nonneg F U
  nlinarith

end
end CutQueryComplexity.GHReduction
