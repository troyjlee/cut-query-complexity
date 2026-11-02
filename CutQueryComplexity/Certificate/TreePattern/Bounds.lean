import CutQueryComplexity.Certificate.TreePattern.Main
import CutQueryComplexity.Certificate.TreePattern.Enumeration

/-!
# Numerical bounds for the public tree-pattern certificates

The actual Prüfer bijection counts the public labelled trees. The normal-form
and verifier constructions supply completeness and soundness for the same
fixed query families, including against competitors with changed support.
-/

set_option autoImplicit false

namespace CutQueryComplexity.Certificate.TreePattern

open Finset
open scoped Classical
noncomputable section

variable {n : ℕ}

theorem flowPatternFamily_card_le_cayley (hn : 2 ≤ n) :
    (flowPatternFamily hn).card ≤ n ^ (n - 2) := by
  calc
    (flowPatternFamily hn).card ≤ Fintype.card (LabelledTree n) :=
      flowPatternFamily_card_le hn
    _ = n ^ (n - 2) := labelledTree_card hn

theorem terminalDescriptions_card_cayley (hn : 2 ≤ n)
    (s t : Fin n) (hst : s ≠ t) :
    (terminalDescriptions s t).card = 2 ^ (n - 2) * n ^ (n - 2) := by
  calc
    (terminalDescriptions s t).card = Fintype.card (LabelledTree n) * 2 ^ (n - 2) :=
      terminalDescriptions_card s t hst
    _ = n ^ (n - 2) * 2 ^ (n - 2) :=
      congrArg (fun a : ℕ => a * 2 ^ (n - 2)) (labelledTree_card hn)
    _ = 2 ^ (n - 2) * n ^ (n - 2) := Nat.mul_comm _ _

/-- At most n^(n-2) fixed public query patterns suffice simultaneously for
every nonnegative weighted graph and every feasible divergence. The same
concrete verifier uses at most 4n-1 queries on every real answer sequence. -/
theorem public_flow_patterns_cayley (hn : 2 ≤ n) :
    ∃ Q : Finset (Finset (Finset (Fin n))),
      Q.card ≤ n ^ (n - 2) ∧
      (∀ q ∈ Q, q.card ≤ 4 * n - 1) ∧
      ∀ G : WeightedGraph (Fin n), ∀ b : Fin n → ℝ,
        (∃ f, Feasible G f ∧ ∀ v, netOut f v = b v) →
        ∃ T : LabelledTree n, flowQueries hn T ∈ Q ∧
          (verifyFlow hn T b).eval G.cut = true ∧
          (∀ answer, (verifyFlow hn T b).cost answer ≤ 4 * n - 1) ∧
          ∀ H : WeightedGraph (Fin n), Consistent G H (flowQueries hn T) →
            ∃ f, Feasible H f ∧ ∀ v, netOut f v = b v := by
  obtain ⟨Q, hQ, hsize, hcomplete⟩ := public_flow_patterns hn
  exact ⟨Q, hQ.trans_eq (labelledTree_card hn), hsize, hcomplete⟩

/-- For fixed distinct terminals, exactly 2^(n-2)n^(n-2) public descriptions
contain a successful certificate for every input. Its queried shore is an
actual minimum cut, its value is preserved for every consistent competitor,
and its public verifier has an unconditional 4n query cap. -/
theorem public_terminal_certificates_cayley (hn : 2 ≤ n) (s t : Fin n) (hst : s ≠ t) :
    ∃ D : Finset (LabelledTree n × Finset (Fin n)),
      D.card = 2 ^ (n - 2) * n ^ (n - 2) ∧
      (∀ d ∈ D, (terminalQueries hn d.1 d.2).card ≤ 4 * n ∧
        ∀ answer, (verifyTerminal hn s t d.1 d.2).cost answer ≤ 4 * n) ∧
      ∀ G : WeightedGraph (Fin n), ∃ d ∈ D,
        (verifyTerminal hn s t d.1 d.2).eval G.cut = true ∧
        d.2 ∈ terminalQueries hn d.1 d.2 ∧
        IsSTMinCut G s t d.2 ∧
        ∀ H : WeightedGraph (Fin n), Consistent G H (terminalQueries hn d.1 d.2) →
          IsSTMinCut H s t d.2 ∧ H.cut d.2 = G.cut d.2 := by
  obtain ⟨D, hD, hcost, hcomplete⟩ := public_terminal_certificates hn s t hst
  refine ⟨D, ?_, hcost, ?_⟩
  · calc
      D.card = Fintype.card (LabelledTree n) * 2 ^ (n - 2) := hD
      _ = n ^ (n - 2) * 2 ^ (n - 2) :=
        congrArg (fun a : ℕ => a * 2 ^ (n - 2)) (labelledTree_card hn)
      _ = 2 ^ (n - 2) * n ^ (n - 2) := Nat.mul_comm _ _
  · intro G
    obtain ⟨d, hd, hcheck, hqueried, hcert⟩ := hcomplete G
    exact ⟨d, hd, hcheck, hqueried, (hcert G (fun _ _ => rfl)).1, hcert⟩

end
end CutQueryComplexity.Certificate.TreePattern

#print axioms CutQueryComplexity.Certificate.TreePattern.flowPatternFamily_card_le_cayley
#print axioms CutQueryComplexity.Certificate.TreePattern.terminalDescriptions_card_cayley
#print axioms CutQueryComplexity.Certificate.TreePattern.public_flow_patterns_cayley
#print axioms CutQueryComplexity.Certificate.TreePattern.public_terminal_certificates_cayley
