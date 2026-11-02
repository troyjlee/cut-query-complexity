import CutQueryComplexity.DirectedCertificate.Basic
import CutQueryComplexity.DirectedCertificate.Flow
import CutQueryComplexity.Certificate.FlowCert

/-! # Directed flow certificates (W5; `lem:flow`)

* `lem:flow` (`exists_flowCert_directed`): for a feasible directed signed flow `f` in `G`,
  at most `18 n` outgoing-cut queries certify `Σ_{v ∈ S} netOut f v ≤ F_{G'}(S)` for every
  shore `S` in every consistent nonnegative `G'` (arbitrary support). The stronger transfer
  form is `exists_flowTransfer_directed`.
* The orientation of `lem:orientation` is in `DirectedCertificate.Orientation`.

Route. `z = a − aᵀ − 2f` is a signed flow feasible in `u = sym G` with divergence `β − 2d`.
The undirected flow certificate for `G.sym` is compiled into directed queries `{S, Sᶜ}`
(`sym_cut`), and `degreeQueries` fix `β`.
-/

namespace CutQueryComplexity.DirectedCertificate

open Finset WeightedDiGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Compiling undirected symmetrized cuts -/

/-- Each undirected query `S` of the symmetrization becomes the directed queries `S`, `Sᶜ`. -/
def symQueries (Q : Finset (Finset V)) : Finset (Finset V) := Q ∪ Q.image compl

theorem symQueries_card (Q : Finset (Finset V)) : (symQueries Q).card ≤ 2 * Q.card := by
  unfold symQueries
  have := Finset.card_union_le Q (Q.image compl)
  have := Finset.card_image_le (s := Q) (f := compl)
  omega

/-- Directed consistency on `symQueries Q` gives undirected consistency of the
symmetrizations on `Q`. -/
theorem Consistent.sym {G G' : WeightedDiGraph V} {Q : Finset (Finset V)}
    (h : Consistent G G' (symQueries Q)) : Certificate.Consistent G.sym G'.sym Q := by
  intro S hS
  rw [sym_cut, sym_cut, h S (Finset.mem_union_left _ hS),
    h Sᶜ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hS))]

/-- Two digraphs with the same symmetrization and the same imbalance have the same
outgoing-cut function (`eq:cut-identity`). -/
theorem out_eq_of_sym_imbalance {H G' : WeightedDiGraph V}
    (hs : ∀ u v, H.sym.w u v = G'.sym.w u v) (hb : ∀ v, H.imbalance v = G'.imbalance v)
    (S : Finset V) : H.out S = G'.out S := by
  have e : H.sym = G'.sym := WeightedGraph.ext (funext fun u => funext fun v => hs u v)
  have h1 := H.two_mul_out S
  have h2 := G'.two_mul_out S
  rw [e, Finset.sum_congr rfl fun v _ => hb v] at h1
  linarith

/-! ## The shifted flow `z = a − aᵀ − 2f` -/

/-- `z_{vw} = a_{vw} − a_{wv} − 2 f_{vw}`. -/
def flowShift (G : WeightedDiGraph V) (f : V → V → ℝ) : V → V → ℝ :=
  fun v w => G.c v w - G.c w v - 2 * f v w

omit [Fintype V] [DecidableEq V] in
theorem feasible_flowShift {G : WeightedDiGraph V} {f : V → V → ℝ} (hf : G.Feasible f) :
    Certificate.Feasible G.sym (flowShift G f) := by
  refine ⟨fun u v => ?_, fun u v => ?_⟩
  · simp only [flowShift]; rw [hf.1 u v]; ring
  · have h1 := hf.2 u v
    have h2 := hf.2 v u
    rw [hf.1 u v] at h2
    rw [sym_w, abs_le]; simp only [flowShift]; constructor <;> linarith

omit [DecidableEq V] in
theorem netOut_flowShift (G : WeightedDiGraph V) (f : V → V → ℝ) (v : V) :
    Certificate.netOut (flowShift G f) v = G.imbalance v - 2 * Certificate.netOut f v := by
  simp only [Certificate.netOut, flowShift, imbalance, outdeg, indeg, Finset.sum_sub_distrib,
    Finset.mul_sum]

/-! ## `lem:flow` -/

/-- Degree queries in a query set fix the imbalance. -/
theorem consistent_imbalance {G G' : WeightedDiGraph V} {Q : Finset (Finset V)}
    (h : Consistent G G' (Q ∪ degreeQueries V)) (v : V) :
    G'.imbalance v = G.imbalance v :=
  (degrees_eq_of_consistent (h.mono Finset.subset_union_right) v).2.2

/-- `lem:flow`, transfer form: `18 n` queries; every consistent `G'` carries a signed flow
feasible in `G'.sym` with divergence `β − 2d`, and has the imbalance `β` of `G`. -/
theorem exists_flowTransfer_directed (G : WeightedDiGraph V) {f : V → V → ℝ}
    (hf : G.Feasible f) :
    ∃ Q : Finset (Finset V), Q.card ≤ 18 * Fintype.card V ∧ ∀ G' : WeightedDiGraph V,
      Consistent G G' Q →
        (∃ z', Certificate.Feasible G'.sym z' ∧
          ∀ x, Certificate.netOut z' x = G.imbalance x - 2 * Certificate.netOut f x) ∧
        ∀ x, G'.imbalance x = G.imbalance x := by
  obtain ⟨Q₀, hQ₀, hcert⟩ := Certificate.exists_flowCert G.sym Finset.univ (feasible_flowShift hf)
  refine ⟨symQueries Q₀ ∪ degreeQueries V, ?_, fun G' hG' => ⟨?_, consistent_imbalance hG'⟩⟩
  · have := symQueries_card Q₀
    have := degreeQueries_card (V := V)
    have := Finset.card_union_le (symQueries Q₀) (degreeQueries V)
    rw [Finset.card_univ] at hQ₀
    omega
  · obtain ⟨z', hz', hnet⟩ := hcert G'.sym (Consistent.sym (hG'.mono Finset.subset_union_left))
    exact ⟨z', hz', fun x => by rw [hnet x (Finset.mem_univ x), netOut_flowShift]⟩

/-- **`lem:flow`** (directed, real capacities): if `f` is feasible in `G`, then at most
`18 n` outgoing-cut queries certify `d(S) ≤ F_{G'}(S)` for every shore `S`, where
`d = netOut f`, in every consistent nonnegative weighted digraph `G'`. -/
theorem exists_flowCert_directed (G : WeightedDiGraph V) {f : V → V → ℝ}
    (hf : G.Feasible f) :
    ∃ Q : Finset (Finset V), Q.card ≤ 18 * Fintype.card V ∧ ∀ G' : WeightedDiGraph V,
      Consistent G G' Q → ∀ S : Finset V, ∑ v ∈ S, Certificate.netOut f v ≤ G'.out S := by
  obtain ⟨Q, hQ, hT⟩ := exists_flowTransfer_directed G hf
  refine ⟨Q, hQ, fun G' hG' S => ?_⟩
  obtain ⟨⟨z', hz', hnet⟩, himb⟩ := hT G' hG'
  have hc := Certificate.sum_netOut_le_cut hz' Sᶜ
  rw [WeightedGraph.cut_compl] at hc
  have h0 := WeightedDiGraph.sum_univ_netOut hz'.1
  rw [← Finset.sum_add_sum_compl S] at h0
  have h2 := G'.two_mul_out S
  rw [Finset.sum_congr rfl fun v _ => himb v] at h2
  have h3 : ∑ v ∈ S, Certificate.netOut z' v =
      ∑ v ∈ S, G.imbalance v - 2 * ∑ v ∈ S, Certificate.netOut f v := by
    rw [Finset.sum_congr rfl fun v _ => hnet v, Finset.sum_sub_distrib, Finset.mul_sum]
  linarith

end CutQueryComplexity.DirectedCertificate
