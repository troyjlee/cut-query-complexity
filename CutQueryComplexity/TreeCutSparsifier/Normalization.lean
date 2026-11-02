import CutQueryComplexity.DetMinCut.SafePartition
import CutQueryComplexity.DetMinCut.Main

/-! # Preservation of every minimum cut during degree normalization -/

set_option autoImplicit false

namespace CutQueryComplexity.TreeCutSparsifier

open WeightedGraph Search Search.Comp Discovery DetMinCut Finset

variable {V : Type} [Fintype V] [DecidableEq V]

def SafeInv (G : WeightedGraph V) (st : St V) : Prop :=
  Inv G st ∧ SafePartition G st.r

theorem safePartition_merge (G : WeightedGraph V) {st : St V} (hI : Inv G st)
    (hs : SafePartition G st.r) {u v : Cls st.r}
    (hheavy : st.U < (quot G st.r).w v u) :
    SafePartition G (mergeSt st u v (G.cut (pull (proj st.r) {u, v}))).r := by
  intro S hS
  exact sat_mergeR (hs S hS) (not_separated_cls G hheavy (hs S hS)
    (by rw [isMinCut_of_sat hS]; exact hI.lam_le))

theorem normalize_safe (G : WeightedGraph V) :
    ∀ (fuel : ℕ) (st : St V), Inv G st → SafePartition G st.r →
      SafePartition G ((DetMinCut.normalize fuel st).eval G.cut).r := by
  intro fuel
  induction fuel with
  | zero =>
      intro st hI hs
      exact hs
  | succ fuel ih =>
      intro st hI hs
      by_cases hc : 0 < st.U ∧
          ∃ c : Cls st.r, ((Fintype.card (Cls st.r) : ℝ) - 1) * st.U < st.deg c.val
      swap
      · simp only [DetMinCut.normalize, dite_eq_right hc, eval_pure]
        exact hs
      set v := Classical.choose hc.2 with hvdef
      have hv : ((Fintype.card (Cls st.r) : ℝ) - 1) * st.U < st.deg v.val :=
        Classical.choose_spec hc.2
      have hdeg : st.deg v.val = (quot G st.r).degree v := congrFun hI.quot_degree v
      have hcutq : G.cut ∘ pull (proj st.r) = (quot G st.r).cut := by
        funext T; exact (cut_contract G (proj st.r) T).symm
      obtain ⟨hne, hheavy, hcost⟩ := heavyNeighbor_spec (quot G st.r) v (U := st.U)
        (by rw [← hdeg]; exact hv)
      simp only [DetMinCut.normalize, dite_eq_left hc, ← hvdef, eval_bind, eval_mapQ, hcutq, hdeg]
      set u := (heavyNeighbor v ((quot G st.r).degree v)).eval (quot G st.r).cut
      rw [ite_eq_right hne]
      simp only [eval_bind, eval_ask]
      have huv : u ≠ v := hne
      have huv' : u.val ≠ v.val := fun h => huv (Subtype.ext h)
      have hI1 := inv_merge G hI huv hheavy
      exact ih _ hI1 (safePartition_merge G hI hs hheavy)

theorem SafeInv.U_pos {G : WeightedGraph V} {st : St V} (h : SafeInv G st)
    (hpos : 0 < mincutValue G) : 0 < st.U := hpos.trans_le h.1.lam_le

theorem safePartition_two_le_card (G : WeightedGraph V) (hn : 2 ≤ Fintype.card V)
    {r : V → V} (hs : SafePartition G r) : 2 ≤ Fintype.card (Cls r) := by
  obtain ⟨S, hS⟩ := exists_isMinCut_of_two_le_card G hn
  exact two_le_card_cls (hs S hS) hS.1

/-- A safe quotient has the same minimum-cut value as the original graph. -/
theorem safePartition_mincutValue (G : WeightedGraph V) (hn : 2 ≤ Fintype.card V)
    {r : V → V} (hs : SafePartition G r) : mincutValue (quot G r) = mincutValue G := by
  obtain ⟨S, hS⟩ := exists_isMinCut_of_two_le_card G hn
  obtain ⟨T, hpull, hval⟩ := hs.exists_quotient_cut hS
  have hT : ProperShore T := by
    constructor
    · obtain ⟨x, hx⟩ := hS.1.1
      exact ⟨proj r x, by rw [← hpull] at hx; exact (mem_pull _ _ _).mp hx⟩
    · intro heq
      apply hS.1.2
      rw [← hpull, heq]
      ext x; simp
  have hupper := mincutValue_le (quot G r) hT
  rw [hval, isMinCut_of_sat hS] at hupper
  obtain ⟨Tmin, hmin⟩ := exists_isMinCut_of_two_le_card (quot G r) (safePartition_two_le_card G hn hs)
  have hlower := mincutValue_le G (properShore_pull (proj r) (proj_surjective r) hmin.1)
  rw [← cut_contract, isMinCut_of_sat hmin] at hlower
  exact le_antisymm hupper hlower

theorem safePartition_quotient_positive (G : WeightedGraph V) (hn : 2 ≤ Fintype.card V)
    {r : V → V} (hs : SafePartition G r) (hpos : 0 < mincutValue G) :
    0 < mincutValue (quot G r) := by
  rw [safePartition_mincutValue G hn hs]
  exact hpos

end CutQueryComplexity.TreeCutSparsifier
