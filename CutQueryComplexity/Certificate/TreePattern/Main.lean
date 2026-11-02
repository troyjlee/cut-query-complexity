import CutQueryComplexity.Certificate.TreePattern.NormalForm
import Mathlib.Data.Finset.Interval

/-!
# Terminal cut certificates from the public tree verifier

A tree and queried terminal shore are fixed before every weighted competitor.
The matching flow is constructed by max-flow/min-cut and the proved public
normal form. Verification uses at most 4n original undirected cut queries.
-/

set_option autoImplicit false

namespace CutQueryComplexity.Certificate.TreePattern

open Finset WeightedGraph
open scoped Classical
noncomputable section

variable {n : ℕ}

/-- The same public family serves all graphs and all divergence vectors. -/
def flowPatternFamily (hn : 2 ≤ n) : Finset (Finset (Finset (Fin n))) :=
  univ.image (flowQueries hn)

theorem flowPatternFamily_card_le (hn : 2 ≤ n) :
    (flowPatternFamily hn).card ≤ Fintype.card (LabelledTree n) := by
  simpa [flowPatternFamily] using
    (card_image_le (s := (univ : Finset (LabelledTree n))) (f := flowQueries hn))

/-- Soundness and completeness refer to the same concrete public verifier. -/
theorem verifyFlow_exists_iff (hn : 2 ≤ n) (G : WeightedGraph (Fin n)) (b : Fin n → ℝ) :
    (∃ T : LabelledTree n, (verifyFlow hn T b).eval G.cut = true) ↔
      ∃ f, Feasible G f ∧ ∀ v, netOut f v = b v := by
  constructor
  · rintro ⟨T, hT⟩
    exact accepts_sound hn T G b ((verifyFlow_eval hn T b G).mp hT)
  · intro hf
    obtain ⟨T, hT⟩ := exists_accepting_tree hn G b hf
    exact ⟨T, (verifyFlow_eval hn T b G).mpr hT⟩

/-- A successful verifier transfers to every consistent weighted competitor. -/
theorem verifyFlow_transfer (hn : 2 ≤ n) (T : LabelledTree n) (b : Fin n → ℝ)
    (G : WeightedGraph (Fin n)) (hT : (verifyFlow hn T b).eval G.cut = true) :
    ∀ H : WeightedGraph (Fin n), Consistent G H (flowQueries hn T) →
      ∃ f, Feasible H f ∧ ∀ v, netOut f v = b v := by
  intro H hH
  exact accepts_transfer hn T G H b ((verifyFlow_eval hn T b G).mp hT) hH

/-- Literal public-family quantifier order: the family is fixed before both
the hidden graph and its requested feasible divergence. -/
theorem public_flow_patterns (hn : 2 ≤ n) :
    ∃ Q : Finset (Finset (Finset (Fin n))),
      Q.card ≤ Fintype.card (LabelledTree n) ∧
      (∀ q ∈ Q, q.card ≤ 4 * n - 1) ∧
      ∀ G : WeightedGraph (Fin n), ∀ b : Fin n → ℝ,
        (∃ f, Feasible G f ∧ ∀ v, netOut f v = b v) →
        ∃ T : LabelledTree n, flowQueries hn T ∈ Q ∧
          (verifyFlow hn T b).eval G.cut = true ∧
          (∀ answer, (verifyFlow hn T b).cost answer ≤ 4 * n - 1) ∧
          ∀ H : WeightedGraph (Fin n), Consistent G H (flowQueries hn T) →
            ∃ f, Feasible H f ∧ ∀ v, netOut f v = b v := by
  refine ⟨flowPatternFamily hn, flowPatternFamily_card_le hn, ?_, ?_⟩
  · intro q hq
    obtain ⟨T, _, rfl⟩ := mem_image.mp hq
    exact flowQueries_card_le hn T
  · intro G b hf
    obtain ⟨T, hT⟩ := (verifyFlow_exists_iff hn G b).mpr hf
    exact ⟨T, mem_image_of_mem _ (mem_univ _), hT, verifyFlow_cost hn T b,
      verifyFlow_transfer hn T b G hT⟩

/-- Exactly the shores containing s and avoiding t, enumerated publicly. -/
def terminalShores (s t : Fin n) : Finset (Finset (Fin n)) := Icc {s} {t}ᶜ

@[simp] theorem mem_terminalShores (s t : Fin n) (S : Finset (Fin n)) :
    S ∈ terminalShores s t ↔ s ∈ S ∧ t ∉ S := by
  simp [terminalShores]

theorem terminalShores_card (s t : Fin n) (hst : s ≠ t) :
    (terminalShores s t).card = 2 ^ (n - 2) := by
  have hsub : ({s} : Finset (Fin n)) ⊆ {t}ᶜ := by simp [hst.symm]
  rw [terminalShores, card_Icc_finset hsub]
  simp only [card_compl, Fintype.card_fin, card_singleton]
  congr 1

/-- A description consists only of a tree and a terminal shore. Its size
will be specialized by the independent proved Prüfer enumeration. -/
def terminalDescriptions (s t : Fin n) : Finset (LabelledTree n × Finset (Fin n)) :=
  univ ×ˢ terminalShores s t

theorem terminalDescriptions_card (s t : Fin n) (hst : s ≠ t) :
    (terminalDescriptions s t).card =
      Fintype.card (LabelledTree n) * 2 ^ (n - 2) := by
  simp [terminalDescriptions, terminalShores_card s t hst]

def terminalDemand (s t : Fin n) (value : ℝ) (v : Fin n) : ℝ :=
  (if v = s then value else 0) - (if v = t then value else 0)

theorem sum_terminalDemand (s t : Fin n) (value : ℝ) {S : Finset (Fin n)}
    (hs : s ∈ S) (ht : t ∉ S) : ∑ v ∈ S, terminalDemand s t value v = value := by
  simp [terminalDemand, sum_sub_distrib, hs, ht]

/-- An actual maximum flow and its matching terminal cut, over arbitrary
nonnegative real capacities. -/
theorem exists_matching_terminal_flow (G : WeightedGraph (Fin n)) (s t : Fin n)
    (hst : s ≠ t) : ∃ S : Finset (Fin n), ∃ f : Fin n → Fin n → ℝ,
      s ∈ S ∧ t ∉ S ∧ Feasible G f ∧
      (∀ v, netOut f v = terminalDemand s t (G.cut S) v) := by
  have hdis : Disjoint ({s} : Finset (Fin n)) {t} := disjoint_singleton.mpr hst
  obtain ⟨f, S₀, hf, hcons, _, _, hS₀, hval⟩ :=
    exists_maxFlow G {s} {t} hdis G.degree
      (fun v => sum_nonneg fun u _ => G.nonneg v u)
  let S := S₀ ∪ {s}
  have hs : s ∈ S := mem_union_right _ (mem_singleton_self _)
  have ht : t ∉ S := by
    intro htS
    rcases mem_union.mp htS with ht₀ | hts
    · exact disjoint_left.mp hS₀ ht₀ (mem_singleton_self _)
    · exact hst (mem_singleton.mp hts).symm
  have hsum : ∑ v ∈ S, netOut f v = netOut f s := by
    rw [sum_eq_single s]
    · intro v hv hvs
      exact hcons v (by simpa using hvs) (by
        intro hvt
        exact ht ((mem_singleton.mp hvt) ▸ hv))
    · exact fun h => (h hs).elim
  have hcut : G.cut S = netOut f s := by
    apply le_antisymm
    · have hupper := cut_union_le G S₀ {s}
      simp only [sum_singleton] at hval
      exact hupper.trans_eq hval.symm
    · rw [← hsum]
      exact sum_netOut_le_cut hf S
  have hother : ∀ v, v ≠ s → v ≠ t → netOut f v = 0 := by
    intro v hvs hvt
    exact hcons v (by simpa using hvs) (by simpa using hvt)
  have hall : ∑ v, netOut f v = netOut f s + netOut f t := by
    calc
      ∑ v, netOut f v = ∑ v, ((if v = s then netOut f s else 0) +
          (if v = t then netOut f t else 0)) := by
        apply sum_congr rfl
        intro v _
        by_cases hvs : v = s
        · subst v
          simp [hst]
        · by_cases hvt : v = t
          · subst v
            simp [hst.symm]
          · simp [hvs, hvt, hother v hvs hvt]
      _ = _ := by simp [sum_add_distrib]
  have hzero : ∑ v, netOut f v = 0 := hf.1.sum_sum_eq_zero univ
  have hdivt : netOut f t = -netOut f s := by linarith
  refine ⟨S, f, hs, ht, hf, fun v => ?_⟩
  by_cases hvs : v = s
  · subst v
    simp [terminalDemand, hst, hcut]
  · by_cases hvt : v = t
    · subst v
      simp [terminalDemand, hst.symm, hcut, hdivt]
    · simp [terminalDemand, hvs, hvt, hother v hvs hvt]

def terminalQueries (hn : 2 ≤ n) (T : LabelledTree n) (S : Finset (Fin n)) :
    Finset (Finset (Fin n)) := insert S (flowQueries hn T)

theorem terminalQueries_card_le (hn : 2 ≤ n) (T : LabelledTree n) (S : Finset (Fin n)) :
    (terminalQueries hn T S).card ≤ 4 * n := by
  have hi := card_insert_le S (flowQueries hn T)
  have hf := flowQueries_card_le hn T
  unfold terminalQueries
  omega

theorem terminal_certificate_of_accepts (hn : 2 ≤ n) (T : LabelledTree n)
    (G : WeightedGraph (Fin n)) (s t : Fin n) (S : Finset (Fin n))
    (hs : s ∈ S) (ht : t ∉ S)
    (hacc : accepts hn T (terminalDemand s t (G.cut S)) G.cut) :
    ∀ H : WeightedGraph (Fin n), Consistent G H (terminalQueries hn T S) →
      IsSTMinCut H s t S ∧ H.cut S = G.cut S := by
  intro H hH
  have hvalue : H.cut S = G.cut S := hH S (mem_insert_self _ _)
  obtain ⟨f, hf, hdiv⟩ := accepts_transfer hn T G H _ hacc
    (hH.mono (subset_insert _ _))
  refine ⟨⟨hs, ht, fun U hsU htU => ?_⟩, hvalue⟩
  have hweak := sum_netOut_le_cut hf U
  rw [sum_congr rfl (fun v _ => hdiv v), sum_terminalDemand s t (G.cut S) hsU htU] at hweak
  rw [hvalue]
  exact hweak

/-- The queried shore and tree are selected once before all unrestricted
weighted competitors, including those whose support differs from G. -/
theorem exists_terminal_tree_certificate (hn : 2 ≤ n) (G : WeightedGraph (Fin n))
    (s t : Fin n) (hst : s ≠ t) :
    ∃ T : LabelledTree n, ∃ S : Finset (Fin n),
      (terminalQueries hn T S).card ≤ 4 * n ∧ S ∈ terminalQueries hn T S ∧
      IsSTMinCut G s t S ∧
      ∀ H : WeightedGraph (Fin n), Consistent G H (terminalQueries hn T S) →
        IsSTMinCut H s t S ∧ H.cut S = G.cut S := by
  obtain ⟨S, f, hs, ht, hf, hdiv⟩ := exists_matching_terminal_flow G s t hst
  obtain ⟨T, hacc⟩ := exists_accepting_tree hn G (terminalDemand s t (G.cut S)) ⟨f, hf, hdiv⟩
  have hcert := terminal_certificate_of_accepts hn T G s t S hs ht hacc
  exact ⟨T, S, terminalQueries_card_le hn T S, mem_insert_self _ _,
    (hcert G (fun _ _ => rfl)).1, hcert⟩

/-- Public verification takes a tree and shore, then measures its own target
value. No optimum value or hidden graph is supplied to the program. -/
def verifyTerminal (hn : 2 ≤ n) (s t : Fin n) (T : LabelledTree n) (S : Finset (Fin n)) :
    DTree (Finset (Fin n)) ℝ Bool (4 * n) :=
  if s ∈ S ∧ t ∉ S then
    (DTree.query S fun value => verifyFlow hn T (terminalDemand s t value)).cast (by omega)
  else DTree.pure false

theorem verifyTerminal_eval (hn : 2 ≤ n) (s t : Fin n) (T : LabelledTree n)
    (S : Finset (Fin n)) (G : WeightedGraph (Fin n)) :
    (verifyTerminal hn s t T S).eval G.cut = true ↔
      s ∈ S ∧ t ∉ S ∧ accepts hn T (terminalDemand s t (G.cut S)) G.cut := by
  by_cases h : s ∈ S ∧ t ∉ S
  · simp only [verifyTerminal, ite_eq_left h, DTree.eval, DTree.run_cast, DTree.run_query]
    change (verifyFlow hn T (terminalDemand s t (G.cut S))).eval G.cut = true ↔ _
    rw [verifyFlow_eval]
    exact ⟨fun ha => ⟨h.1, h.2, ha⟩, fun ha => ha.2.2⟩
  · have hfalse : ¬(s ∈ S ∧ t ∉ S ∧
        accepts hn T (terminalDemand s t (G.cut S)) G.cut) :=
      fun ha => h ⟨ha.1, ha.2.1⟩
    simp [verifyTerminal, h, hfalse]

theorem verifyTerminal_cost (hn : 2 ≤ n) (s t : Fin n) (T : LabelledTree n)
    (S : Finset (Fin n)) (answer : Finset (Fin n) → ℝ) :
    (verifyTerminal hn s t T S).cost answer ≤ 4 * n := DTree.cost_le _ _

theorem verifyTerminal_sound (hn : 2 ≤ n) (s t : Fin n) (T : LabelledTree n)
    (S : Finset (Fin n)) (G : WeightedGraph (Fin n))
    (hcheck : (verifyTerminal hn s t T S).eval G.cut = true) :
    ∀ H : WeightedGraph (Fin n), Consistent G H (terminalQueries hn T S) →
      IsSTMinCut H s t S ∧ H.cut S = G.cut S := by
  obtain ⟨hs, ht, hacc⟩ := (verifyTerminal_eval hn s t T S G).mp hcheck
  exact terminal_certificate_of_accepts hn T G s t S hs ht hacc

/-- The finite public description family contains a successful certificate
for every weighted input. The same actual verifier has a cap on every oracle
and certifies the queried optimum shore and value against every competitor. -/
theorem exists_verified_terminal_certificate (hn : 2 ≤ n) (s t : Fin n)
    (hst : s ≠ t) (G : WeightedGraph (Fin n)) :
    ∃ T : LabelledTree n, ∃ S : Finset (Fin n),
      (T, S) ∈ terminalDescriptions s t ∧
      (verifyTerminal hn s t T S).eval G.cut = true ∧
      (∀ answer, (verifyTerminal hn s t T S).cost answer ≤ 4 * n) ∧
      (terminalQueries hn T S).card ≤ 4 * n ∧ S ∈ terminalQueries hn T S ∧
      ∀ H : WeightedGraph (Fin n), Consistent G H (terminalQueries hn T S) →
        IsSTMinCut H s t S ∧ H.cut S = G.cut S := by
  obtain ⟨S, f, hs, ht, hf, hdiv⟩ := exists_matching_terminal_flow G s t hst
  obtain ⟨T, hacc⟩ := exists_accepting_tree hn G (terminalDemand s t (G.cut S)) ⟨f, hf, hdiv⟩
  have hcheck := (verifyTerminal_eval hn s t T S G).mpr ⟨hs, ht, hacc⟩
  refine ⟨T, S, ?_, hcheck, verifyTerminal_cost hn s t T S,
    terminalQueries_card_le hn T S, mem_insert_self _ _,
    verifyTerminal_sound hn s t T S G hcheck⟩
  exact mem_product.mpr ⟨mem_univ _, (mem_terminalShores s t S).mpr ⟨hs, ht⟩⟩

/-- The entire finite description family is fixed before the graph. Every
description has the same unconditional query cap, and every weighted input
has a successful description certifying its queried minimum shore and value
against every consistent nonnegative weighted competitor. -/
theorem public_terminal_certificates (hn : 2 ≤ n) (s t : Fin n) (hst : s ≠ t) :
    ∃ D : Finset (LabelledTree n × Finset (Fin n)),
      D.card = Fintype.card (LabelledTree n) * 2 ^ (n - 2) ∧
      (∀ d ∈ D, (terminalQueries hn d.1 d.2).card ≤ 4 * n ∧
        ∀ answer, (verifyTerminal hn s t d.1 d.2).cost answer ≤ 4 * n) ∧
      ∀ G : WeightedGraph (Fin n), ∃ d ∈ D,
        (verifyTerminal hn s t d.1 d.2).eval G.cut = true ∧
        d.2 ∈ terminalQueries hn d.1 d.2 ∧
        ∀ H : WeightedGraph (Fin n), Consistent G H (terminalQueries hn d.1 d.2) →
          IsSTMinCut H s t d.2 ∧ H.cut d.2 = G.cut d.2 := by
  refine ⟨terminalDescriptions s t, terminalDescriptions_card s t hst, ?_, ?_⟩
  · intro d _
    exact ⟨terminalQueries_card_le hn d.1 d.2, verifyTerminal_cost hn s t d.1 d.2⟩
  · intro G
    obtain ⟨T, S, hmem, hcheck, _, _, hqueried, hcert⟩ :=
      exists_verified_terminal_certificate hn s t hst G
    exact ⟨(T, S), hmem, hcheck, hqueried, hcert⟩

end
end CutQueryComplexity.Certificate.TreePattern

#print axioms CutQueryComplexity.Certificate.TreePattern.exists_matching_terminal_flow
#print axioms CutQueryComplexity.Certificate.TreePattern.verifyFlow_exists_iff
#print axioms CutQueryComplexity.Certificate.TreePattern.public_flow_patterns
#print axioms CutQueryComplexity.Certificate.TreePattern.terminalShores_card
#print axioms CutQueryComplexity.Certificate.TreePattern.terminalDescriptions_card
#print axioms CutQueryComplexity.Certificate.TreePattern.terminal_certificate_of_accepts
#print axioms CutQueryComplexity.Certificate.TreePattern.exists_terminal_tree_certificate
#print axioms CutQueryComplexity.Certificate.TreePattern.verifyTerminal_eval
#print axioms CutQueryComplexity.Certificate.TreePattern.verifyTerminal_cost
#print axioms CutQueryComplexity.Certificate.TreePattern.verifyTerminal_sound
#print axioms CutQueryComplexity.Certificate.TreePattern.exists_verified_terminal_certificate
#print axioms CutQueryComplexity.Certificate.TreePattern.public_terminal_certificates
