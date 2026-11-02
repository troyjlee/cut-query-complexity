import CutQueryComplexity.Graph.Weighted
import CutQueryComplexity.Graph.WeightedDirected
import CutQueryComplexity.Problem.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Directed weighted global-mincut certificates: W0 contract and W1 cut algebra

Formalization of milestones W0 and the cut-algebra/measurement part of
W1 of the directed weighted certificate development.
Source: the model and statements of paper P3 (`papers/P3/directed-cut-certificates.pdf`),
and its equations (3) and (4).

* W0: `Consistent`, `IsGlobalMinCut`, `minValue`, value and witness
  certificates, monotonicity/union of consistency, witness ⇒ value, the
  one-query zero-optimum certificate, and the budget-free and budgeted
  endpoint statements as `def`s of propositions.
* W1: symmetrization `sym : WeightedGraph V`, directed degrees and
  imbalance, `c_U(S) = F(S) + F(Sᶜ)`, `2F(S) = c_U(S) + β(S)`, the
  partial-star identity, `2n` degree queries, and a compiled measurement
  language with union cost bounds.
-/

namespace CutQueryComplexity.DirectedCertificate

/-! ## W0: the certificate contract -/

namespace WeightedDiGraph
variable {V : Type*} [Fintype V] [DecidableEq V] (G : WeightedDiGraph V)

theorem out_nonneg (S : Finset V) : 0 ≤ G.out S :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => G.nonneg _ _

@[simp] theorem out_empty : G.out ∅ = 0 := by simp [out]

@[simp] theorem out_univ : G.out Finset.univ = 0 := by simp [out]

/-- The global minimum of the outgoing cut over proper shores (zero if none exist). -/
noncomputable def minValue : ℝ :=
  if h : (properShores V).Nonempty then (properShores V).inf' h G.out else 0

theorem minValue_le {S : Finset V} (hS : ProperShore S) : G.minValue ≤ G.out S := by
  have hm := (mem_properShores S).mpr hS
  rw [minValue, dite_eq_left ⟨S, hm⟩]
  exact Finset.inf'_le _ hm

end WeightedDiGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

open WeightedDiGraph

/-- The competitor `G'` answers every outgoing-cut query in `Q` as `G` does. -/
def Consistent (G G' : WeightedDiGraph V) (Q : Finset (Finset V)) : Prop :=
  ∀ S ∈ Q, G'.out S = G.out S

/-- `S` is a proper shore minimizing the outgoing cut of `G`. -/
def IsGlobalMinCut (G : WeightedDiGraph V) (S : Finset V) : Prop :=
  ProperShore S ∧ ∀ T, ProperShore T → G.out S ≤ G.out T

/-- The queries `Q` force the global minimum outgoing-cut value. -/
def IsMinCutValueCertificate (G : WeightedDiGraph V) (Q : Finset (Finset V)) : Prop :=
  ∀ G' : WeightedDiGraph V, Consistent G G' Q → G'.minValue = G.minValue

/-- `Q` contains a shore `S` that is a global minimum cut of every consistent
nonnegative competitor (competitors may have arbitrary support). -/
def IsMinCutWitnessCertificate (G : WeightedDiGraph V) (Q : Finset (Finset V))
    (S : Finset V) : Prop :=
  S ∈ Q ∧ ∀ G' : WeightedDiGraph V, Consistent G G' Q → IsGlobalMinCut G' S

theorem Consistent.refl (G : WeightedDiGraph V) (Q : Finset (Finset V)) :
    Consistent G G Q := fun _ _ => rfl

theorem Consistent.symm {G G' : WeightedDiGraph V} {Q : Finset (Finset V)}
    (h : Consistent G G' Q) : Consistent G' G Q := fun S hS => (h S hS).symm

theorem Consistent.trans {G G' G'' : WeightedDiGraph V} {Q : Finset (Finset V)}
    (h : Consistent G G' Q) (h' : Consistent G' G'' Q) : Consistent G G'' Q :=
  fun S hS => (h' S hS).trans (h S hS)

/-- Consistency is inherited by sub-query-sets (restriction). -/
theorem Consistent.mono {G G' : WeightedDiGraph V} {Q Q' : Finset (Finset V)}
    (h : Consistent G G' Q') (hQ : Q ⊆ Q') : Consistent G G' Q :=
  fun S hS => h S (hQ hS)

theorem consistent_union {G G' : WeightedDiGraph V} {Q Q' : Finset (Finset V)} :
    Consistent G G' (Q ∪ Q') ↔ Consistent G G' Q ∧ Consistent G G' Q' := by
  simp only [Consistent, Finset.mem_union]
  exact ⟨fun h => ⟨fun S hS => h S (Or.inl hS), fun S hS => h S (Or.inr hS)⟩,
    fun h S hS => hS.elim (h.1 S) (h.2 S)⟩

theorem consistent_biUnion {ι : Type*} {G G' : WeightedDiGraph V} {s : Finset ι}
    {Q : ι → Finset (Finset V)} :
    Consistent G G' (s.biUnion Q) ↔ ∀ i ∈ s, Consistent G G' (Q i) := by
  simp only [Consistent, Finset.mem_biUnion]
  exact ⟨fun h i hi S hS => h S ⟨i, hi, hS⟩, fun h S ⟨i, hi, hS⟩ => h i hi S hS⟩

/-- On a global minimum cut the minimum value is attained. -/
theorem IsGlobalMinCut.out_eq_minValue {G : WeightedDiGraph V} {S : Finset V}
    (h : IsGlobalMinCut G S) : G.out S = G.minValue := by
  refine le_antisymm ?_ (G.minValue_le h.1)
  have hne : (properShores V).Nonempty := ⟨S, (mem_properShores S).mpr h.1⟩
  obtain ⟨T, hT, hTv⟩ := Finset.exists_mem_eq_inf' hne G.out
  rw [minValue, dite_eq_left hne, hTv]
  exact h.2 T ((mem_properShores T).mp hT)

theorem exists_isGlobalMinCut (G : WeightedDiGraph V) (hn : 2 ≤ Fintype.card V) :
    ∃ S, IsGlobalMinCut G S := by
  have hpos : 0 < Fintype.card V := by omega
  obtain ⟨v⟩ := Fintype.card_pos_iff.mp hpos
  have hne : (properShores V).Nonempty :=
    ⟨{v}, (mem_properShores _).mpr (properShore_singleton v hn)⟩
  obtain ⟨S, hS, hmin⟩ := Finset.exists_mem_eq_inf' hne G.out
  refine ⟨S, (mem_properShores S).mp hS, fun T hT => ?_⟩
  rw [← hmin]
  exact Finset.inf'_le _ ((mem_properShores T).mpr hT)

/-- A witness certificate's shore is optimal in the input itself. -/
theorem IsMinCutWitnessCertificate.isGlobalMinCut {G : WeightedDiGraph V}
    {Q : Finset (Finset V)} {S : Finset V} (h : IsMinCutWitnessCertificate G Q S) :
    IsGlobalMinCut G S :=
  h.2 G (Consistent.refl G Q)

/-- A witness certificate is a value certificate. -/
theorem IsMinCutWitnessCertificate.isValueCertificate {G : WeightedDiGraph V}
    {Q : Finset (Finset V)} {S : Finset V} (h : IsMinCutWitnessCertificate G Q S) :
    IsMinCutValueCertificate G Q := by
  intro G' hG'
  rw [← (h.2 G' hG').out_eq_minValue, ← h.isGlobalMinCut.out_eq_minValue, hG' S h.1]

/-- Adding queries preserves a witness certificate. -/
theorem IsMinCutWitnessCertificate.mono {G : WeightedDiGraph V}
    {Q Q' : Finset (Finset V)} {S : Finset V} (h : IsMinCutWitnessCertificate G Q S)
    (hQ : Q ⊆ Q') : IsMinCutWitnessCertificate G Q' S :=
  ⟨hQ h.1, fun G' hG' => h.2 G' (hG'.mono hQ)⟩

/-- Zero optimum: a single query on a zero-capacity proper shore is a witness
certificate against every nonnegative competitor. -/
theorem zero_witnessCertificate (G : WeightedDiGraph V) {S : Finset V}
    (hS : ProperShore S) (h0 : G.out S = 0) :
    IsMinCutWitnessCertificate G {S} S := by
  refine ⟨Finset.mem_singleton_self S, fun G' hG' => ⟨hS, fun T _ => ?_⟩⟩
  rw [hG' S (Finset.mem_singleton_self S), h0]
  exact G'.out_nonneg T

/-- If the minimum value is zero (and `n ≥ 2`), one query suffices. -/
theorem exists_zero_witnessCertificate (G : WeightedDiGraph V)
    (hn : 2 ≤ Fintype.card V) (h0 : G.minValue = 0) :
    ∃ S, (({S} : Finset (Finset V)).card ≤ 1) ∧ IsMinCutWitnessCertificate G {S} S := by
  obtain ⟨S, hS⟩ := exists_isGlobalMinCut G hn
  exact ⟨S, by simp, zero_witnessCertificate G hS.1 (hS.out_eq_minValue.trans h0)⟩

/-- Sanity (non-vacuity): querying every shore is always a witness certificate. -/
theorem all_shores_witnessCertificate (G : WeightedDiGraph V)
    (hn : 2 ≤ Fintype.card V) : ∃ S, IsMinCutWitnessCertificate G Finset.univ S := by
  obtain ⟨S, hS⟩ := exists_isGlobalMinCut G hn
  refine ⟨S, Finset.mem_univ S, fun G' hG' => ⟨hS.1, fun T hT => ?_⟩⟩
  rw [hG' S (Finset.mem_univ _), hG' T (Finset.mem_univ _)]
  exact hS.2 T hT

/-! ### Endpoint statements (targets only; not proved here) -/

/-- `A(n,k) = ⌈n/k⌉` with natural division. -/
def ceilDiv (n k : ℕ) : ℕ := (n + k - 1) / k

/-- `L(n) = ⌈log₂(2n)⌉`. -/
def logL (n : ℕ) : ℕ := Nat.clog 2 (2 * n)

/-- The plan's natural budget `B_C(n,k) = C (n k² + n k L(n)² + n (A(n,k)+1))`. -/
def budget (C n k : ℕ) : ℕ := C * (n * k ^ 2 + n * k * logL n ^ 2 + n * (ceilDiv n k + 1))

/-- The parameterized endpoint `thm:uniform-certificate`, all quantifiers explicit:
competitors range over every nonnegative real directed graph on `Fin n`, with
arbitrary support. -/
def UniformCertificateTarget : Prop :=
  ∃ C : ℕ, ∀ n : ℕ, ∀ G : WeightedDiGraph (Fin n), ∀ k : ℕ,
    2 ≤ n → 1 ≤ k → k < n →
    ∃ Q : Finset (Finset (Fin n)), ∃ S : Finset (Fin n),
      Q.card ≤ budget C n k ∧ S ∈ Q ∧
      ∀ G' : WeightedDiGraph (Fin n), (∀ T ∈ Q, G'.out T = G.out T) →
        ProperShore S ∧ ∀ T : Finset (Fin n), ProperShore T → G'.out S ≤ G'.out T

/-- The headline `O(n^{5/3})` endpoint, with a real constant. -/
def HeadlineCertificateTarget : Prop :=
  ∃ C : ℝ, ∀ n : ℕ, ∀ G : WeightedDiGraph (Fin n), 2 ≤ n →
    ∃ Q : Finset (Finset (Fin n)), ∃ S : Finset (Fin n),
      (Q.card : ℝ) ≤ C * (n : ℝ) ^ ((5 : ℝ) / 3) ∧ S ∈ Q ∧
      ∀ G' : WeightedDiGraph (Fin n), (∀ T ∈ Q, G'.out T = G.out T) →
        ProperShore S ∧ ∀ T : Finset (Fin n), ProperShore T → G'.out S ≤ G'.out T

/-- Budget-free endpoint: existence of some witness certificate. -/
def BudgetFreeCertificateTarget : Prop :=
  ∀ n : ℕ, ∀ G : WeightedDiGraph (Fin n), 2 ≤ n →
    ∃ Q : Finset (Finset (Fin n)), ∃ S : Finset (Fin n), S ∈ Q ∧
      ∀ G' : WeightedDiGraph (Fin n), (∀ T ∈ Q, G'.out T = G.out T) →
        ProperShore S ∧ ∀ T : Finset (Fin n), ProperShore T → G'.out S ≤ G'.out T

/-- The explicit targets are literally the packaged certificate predicates. -/
theorem uniformCertificateTarget_iff : UniformCertificateTarget ↔
    ∃ C : ℕ, ∀ n : ℕ, ∀ G : WeightedDiGraph (Fin n), ∀ k : ℕ,
      2 ≤ n → 1 ≤ k → k < n →
      ∃ Q S, Q.card ≤ budget C n k ∧ IsMinCutWitnessCertificate G Q S :=
  Iff.rfl

theorem headlineCertificateTarget_iff : HeadlineCertificateTarget ↔
    ∃ C : ℝ, ∀ n : ℕ, ∀ G : WeightedDiGraph (Fin n), 2 ≤ n →
      ∃ Q S, (Q.card : ℝ) ≤ C * (n : ℝ) ^ ((5 : ℝ) / 3) ∧
        IsMinCutWitnessCertificate G Q S :=
  Iff.rfl

/-- The budget-free endpoint holds (trivially, by querying every shore). -/
theorem budgetFreeCertificateTarget : BudgetFreeCertificateTarget := by
  intro n G hn
  obtain ⟨S, hS⟩ := all_shores_witnessCertificate G (by simpa using hn)
  exact ⟨_, S, hS.1, hS.2⟩

/-! ## W1: cut algebra with real capacities -/

namespace WeightedDiGraph
variable (G : WeightedDiGraph V)

/-- Symmetrization `u_{vw} = c v w + c w v`, as an undirected weighted graph. -/
def sym : WeightedGraph V where
  w v w := G.c v w + G.c w v
  symm u v := add_comm _ _
  nonneg u v := add_nonneg (G.nonneg u v) (G.nonneg v u)
  diag v := by simp [G.diag]

omit [Fintype V] [DecidableEq V] in
@[simp] theorem sym_w (v w : V) : G.sym.w v w = G.c v w + G.c w v := rfl

/-- Out-degree `d⁺(v)`. -/
def outdeg (v : V) : ℝ := ∑ w, G.c v w

/-- In-degree `d⁻(v)`. -/
def indeg (v : V) : ℝ := ∑ w, G.c w v

/-- Degree imbalance `β_v = d⁺(v) − d⁻(v)`. -/
def imbalance (v : V) : ℝ := G.outdeg v - G.indeg v

/-- Internal arc mass `Σ_{u,v ∈ S} c u v`. -/
def internal (S : Finset V) : ℝ := ∑ u ∈ S, ∑ v ∈ S, G.c u v

/-- Symmetrized partial star `u(v,T) = Σ_{w ∈ T} u_{vw}`. -/
def symStar (v : V) (T : Finset V) : ℝ := ∑ w ∈ T, G.sym.w v w

theorem out_eq_sum_outdeg_sub_internal (S : Finset V) :
    G.out S = ∑ u ∈ S, G.outdeg u - G.internal S := by
  rw [out, internal, eq_sub_iff_add_eq, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [add_comm, outdeg]
  exact Finset.sum_add_sum_compl S (fun v => G.c u v)

theorem out_compl_eq_sum_indeg_sub_internal (S : Finset V) :
    G.out Sᶜ = ∑ u ∈ S, G.indeg u - G.internal S := by
  rw [out, compl_compl, Finset.sum_comm, internal, Finset.sum_comm (s := S) (t := S),
    eq_sub_iff_add_eq, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [add_comm, indeg]
  exact Finset.sum_add_sum_compl S (fun u => G.c u v)

/-- `c_U(S) = F(S) + F(Sᶜ)`. -/
theorem sym_cut (S : Finset V) : G.sym.cut S = G.out S + G.out Sᶜ := by
  simp only [WeightedGraph.cut, sym_w, Finset.sum_add_distrib, out, compl_compl]
  congr 1
  exact Finset.sum_comm

/-- `β(S) = F(S) − F(Sᶜ)`. -/
theorem sum_imbalance (S : Finset V) :
    ∑ v ∈ S, G.imbalance v = G.out S - G.out Sᶜ := by
  simp only [imbalance, Finset.sum_sub_distrib]
  rw [G.out_eq_sum_outdeg_sub_internal, G.out_compl_eq_sum_indeg_sub_internal]
  ring

/-- `eq:cut-identity`: `2F(S) = c_U(S) + β(S)`. -/
theorem two_mul_out (S : Finset V) :
    2 * G.out S = G.sym.cut S + ∑ v ∈ S, G.imbalance v := by
  rw [sym_cut, sum_imbalance]; ring

theorem out_singleton (v : V) : G.out {v} = G.outdeg v := by
  rw [out_eq_sum_outdeg_sub_internal]; simp [internal, G.diag]

theorem out_compl_singleton (v : V) : G.out ({v}ᶜ) = G.indeg v := by
  rw [out_compl_eq_sum_indeg_sub_internal]; simp [internal, G.diag]

omit [Fintype V] in
theorem internal_insert {v : V} {T : Finset V} (hv : v ∉ T) :
    G.internal (insert v T) =
      G.internal T + ∑ w ∈ T, G.c v w + ∑ w ∈ T, G.c w v := by
  simp only [internal, Finset.sum_insert hv, G.diag, Finset.sum_add_distrib]
  ring

/-- `eq:star`: for `v ∉ T`, `u(v,T) = F({v}) + F(T) − F(T ∪ {v})` (no factor 1/2). -/
theorem symStar_eq {v : V} {T : Finset V} (hv : v ∉ T) :
    G.symStar v T = G.out {v} + G.out T - G.out (insert v T) := by
  rw [out_singleton, out_eq_sum_outdeg_sub_internal, out_eq_sum_outdeg_sub_internal,
    Finset.sum_insert hv, internal_insert G hv, symStar]
  simp only [sym_w, Finset.sum_add_distrib]
  ring

/-- The star identity without the side condition, using `T.erase v`. -/
theorem symStar_eq_erase (v : V) (T : Finset V) :
    G.symStar v T = G.out {v} + G.out (T.erase v) - G.out (insert v T) := by
  have h : G.symStar v T = G.symStar v (T.erase v) := by
    by_cases hv : v ∈ T
    · rw [symStar, symStar, ← Finset.add_sum_erase T _ hv]; simp [G.diag]
    · rw [Finset.erase_eq_of_notMem hv]
  rw [h, symStar_eq G (Finset.notMem_erase v T), Finset.insert_erase_eq_insert]

/-- Pair identity: `u(v,w) = F({v}) + F({w}) − F({v,w})` for `v ≠ w` (no factor 1/2). -/
theorem sym_w_eq_three_outs {v w : V} (hvw : v ≠ w) :
    G.sym.w v w = G.out {v} + G.out {w} - G.out {v, w} := by
  have h := G.symStar_eq (v := v) (T := {w}) (by simpa using hvw)
  simpa [symStar] using h

end WeightedDiGraph

/-- The `≤ 2n` singleton and complementary-singleton queries. -/
def degreeQueries (V : Type*) [Fintype V] [DecidableEq V] : Finset (Finset V) :=
  Finset.univ.image (fun v : V => ({v} : Finset V)) ∪
    Finset.univ.image (fun v : V => ({v}ᶜ : Finset V))

theorem degreeQueries_card : (degreeQueries V).card ≤ 2 * Fintype.card V := by
  unfold degreeQueries
  refine (Finset.card_union_le _ _).trans ?_
  have h1 := Finset.card_image_le (s := (Finset.univ : Finset V))
    (f := fun v : V => ({v} : Finset V))
  have h2 := Finset.card_image_le (s := (Finset.univ : Finset V))
    (f := fun v : V => ({v}ᶜ : Finset V))
  rw [Finset.card_univ] at h1 h2
  omega

theorem Consistent.outdeg_eq {G G' : WeightedDiGraph V} {Q : Finset (Finset V)}
    (h : Consistent G G' Q) {v : V} (hv : {v} ∈ Q) : G'.outdeg v = G.outdeg v := by
  rw [← G.out_singleton, ← G'.out_singleton, h _ hv]

theorem Consistent.indeg_eq {G G' : WeightedDiGraph V} {Q : Finset (Finset V)}
    (h : Consistent G G' Q) {v : V} (hv : {v}ᶜ ∈ Q) : G'.indeg v = G.indeg v := by
  rw [← G.out_compl_singleton, ← G'.out_compl_singleton, h _ hv]

/-- Singleton and complement-singleton queries fix both degree vectors and `β`. -/
theorem degrees_eq_of_consistent {G G' : WeightedDiGraph V}
    (h : Consistent G G' (degreeQueries V)) (v : V) :
    G'.outdeg v = G.outdeg v ∧ G'.indeg v = G.indeg v ∧
      G'.imbalance v = G.imbalance v := by
  have h1 : G'.outdeg v = G.outdeg v :=
    h.outdeg_eq (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ v)))
  have h2 : G'.indeg v = G.indeg v :=
    h.indeg_eq (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ v)))
  exact ⟨h1, h2, by rw [WeightedDiGraph.imbalance, WeightedDiGraph.imbalance, h1, h2]⟩

/-! ## W1: reversal -/

namespace WeightedDiGraph
variable (G : WeightedDiGraph V)

omit [Fintype V] [DecidableEq V] in
theorem rev_sym_w (v w : V) : G.rev.sym.w v w = G.sym.w v w := add_comm _ _

end WeightedDiGraph

/-- Consistency of reversals: complemented queries. -/
theorem Consistent.rev {G G' : WeightedDiGraph V} {Q : Finset (Finset V)}
    (h : Consistent G G' (Q.image compl)) : Consistent G.rev G'.rev Q := by
  intro S hS
  rw [WeightedDiGraph.rev_out, WeightedDiGraph.rev_out]
  exact h _ (Finset.mem_image_of_mem _ hS)

/-! ## W1: compiled measurements -/

/-- A real functional of competitor graphs whose value on every competitor consistent
with `G` is fixed by the finite set `shores` of original outgoing-cut queries. -/
structure Compiled (G : WeightedDiGraph V) (f : WeightedDiGraph V → ℝ) where
  shores : Finset (Finset V)
  fixes : ∀ G' : WeightedDiGraph V, Consistent G G' shores → f G' = f G

namespace Compiled
variable {G : WeightedDiGraph V} {f f₁ f₂ g : WeightedDiGraph V → ℝ}

/-- Query cost of a compiled measurement. -/
def cost (m : Compiled G f) : ℕ := m.shores.card

/-- Public constants cost zero. -/
def const (G : WeightedDiGraph V) (r : ℝ) : Compiled G (fun _ => r) := ⟨∅, fun _ _ => rfl⟩

@[simp] theorem const_cost (r : ℝ) : (const G r).cost = 0 := rfl

/-- A single original query. -/
def query (G : WeightedDiGraph V) (S : Finset V) : Compiled G (fun H => H.out S) :=
  ⟨{S}, fun _ h => h S (Finset.mem_singleton_self S)⟩

theorem query_cost (S : Finset V) : (query G S).cost = 1 := Finset.card_singleton S

/-- Transport along a pointwise identity of functionals. -/
def congr (m : Compiled G f) (h : ∀ H, f H = g H) : Compiled G g :=
  ⟨m.shores, fun G' hG' => by rw [← h, ← h, m.fixes G' hG']⟩

@[simp] theorem congr_cost (m : Compiled G f) (h : ∀ H, f H = g H) :
    (m.congr h).cost = m.cost := rfl

/-- Post-composition with any public function. -/
def map (op : ℝ → ℝ) (m : Compiled G f) : Compiled G (fun H => op (f H)) :=
  ⟨m.shores, fun G' hG' => by simp only [m.fixes G' hG']⟩

@[simp] theorem map_cost (op : ℝ → ℝ) (m : Compiled G f) : (m.map op).cost = m.cost := rfl

/-- Combination of two compiled measurements (shore union). -/
def map₂ (op : ℝ → ℝ → ℝ) (m₁ : Compiled G f₁) (m₂ : Compiled G f₂) :
    Compiled G (fun H => op (f₁ H) (f₂ H)) :=
  ⟨m₁.shores ∪ m₂.shores, fun G' hG' => by
    rw [consistent_union] at hG'
    simp only [m₁.fixes G' hG'.1, m₂.fixes G' hG'.2]⟩

theorem map₂_cost_le (op : ℝ → ℝ → ℝ) (m₁ : Compiled G f₁) (m₂ : Compiled G f₂) :
    (map₂ op m₁ m₂).cost ≤ m₁.cost + m₂.cost := Finset.card_union_le _ _

end Compiled

/-- A family of functionals, indexed by `s`, all fixed by one shore set. -/
structure CompiledFamily (G : WeightedDiGraph V) {ι : Type*} (s : Finset ι)
    (f : ι → WeightedDiGraph V → ℝ) where
  shores : Finset (Finset V)
  fixes : ∀ G' : WeightedDiGraph V, Consistent G G' shores → ∀ i ∈ s, f i G' = f i G

/-- Compile a family by the union of the individual shore sets. -/
def Compiled.family {G : WeightedDiGraph V} {ι : Type*} (s : Finset ι)
    {f : ι → WeightedDiGraph V → ℝ} (m : ∀ i, Compiled G (f i)) : CompiledFamily G s f :=
  ⟨s.biUnion fun i => (m i).shores, fun G' h i hi =>
    (m i).fixes G' (consistent_biUnion.mp h i hi)⟩

/-- The cost of a compiled family is at most the sum of the costs. -/
theorem Compiled.family_card_le {G : WeightedDiGraph V} {ι : Type*} (s : Finset ι)
    {f : ι → WeightedDiGraph V → ℝ} (m : ∀ i, Compiled G (f i)) :
    (Compiled.family s m).shores.card ≤ ∑ i ∈ s, (m i).cost :=
  Finset.card_biUnion_le

/-- Union of two compiled families, indexed by the disjoint sum. -/
def CompiledFamily.union {G : WeightedDiGraph V} {ι κ : Type*} {s : Finset ι} {t : Finset κ}
    {f : ι → WeightedDiGraph V → ℝ} {g : κ → WeightedDiGraph V → ℝ}
    (F₁ : CompiledFamily G s f) (F₂ : CompiledFamily G t g) :
    CompiledFamily G (s.disjSum t) (Sum.elim f g) :=
  ⟨F₁.shores ∪ F₂.shores, fun G' h i hi => by
    rw [consistent_union] at h
    cases i with
    | inl i => exact F₁.fixes G' h.1 i (Finset.inl_mem_disjSum.mp hi)
    | inr i => exact F₂.fixes G' h.2 i (Finset.inr_mem_disjSum.mp hi)⟩

theorem CompiledFamily.union_card_le {G : WeightedDiGraph V} {ι κ : Type*}
    {s : Finset ι} {t : Finset κ}
    {f : ι → WeightedDiGraph V → ℝ} {g : κ → WeightedDiGraph V → ℝ}
    (F₁ : CompiledFamily G s f) (F₂ : CompiledFamily G t g) :
    (F₁.union F₂).shores.card ≤ F₁.shores.card + F₂.shores.card :=
  Finset.card_union_le _ _

/-! ### The measurement language for the original graph -/

/-- Measurements of a directed graph that its outgoing-cut function determines.
Directed arcs and directed partial stars are deliberately absent: they are not
functions of the cut function (`directed_arc_not_determined`). -/
inductive Measurement (V : Type*)
  /-- symmetrized pair capacity `u(v,w)` -/
  | pair (v w : V)
  /-- symmetrized partial star `u(v,T)` -/
  | star (v : V) (T : Finset V)
  /-- out-degree `d⁺(v)` -/
  | outdeg (v : V)
  /-- in-degree `d⁻(v)` -/
  | indeg (v : V)
  /-- imbalance `β_v` -/
  | imbalance (v : V)
  /-- a public constant -/
  | const (r : ℝ)

namespace Measurement

/-- Semantics of a measurement on a graph. -/
def eval : Measurement V → WeightedDiGraph V → ℝ
  | pair v w, H => H.sym.w v w
  | star v T, H => H.symStar v T
  | outdeg v, H => H.outdeg v
  | indeg v, H => H.indeg v
  | imbalance v, H => H.imbalance v
  | const r, _ => r

/-- The explicit original shores queried for a measurement. -/
def shores : Measurement V → Finset (Finset V)
  | pair v w => {{v}, ({w} : Finset V).erase v, {v, w}}
  | star v T => {{v}, T.erase v, insert v T}
  | outdeg v => {{v}}
  | indeg v => {{v}ᶜ}
  | imbalance v => {{v}, {v}ᶜ}
  | const _ => ∅

/-- Declared query cost. -/
def cost : Measurement V → ℕ
  | pair _ _ => 3
  | star _ _ => 3
  | outdeg _ => 1
  | indeg _ => 1
  | imbalance _ => 2
  | const _ => 0

theorem card_shores_le (m : Measurement V) : m.shores.card ≤ m.cost := by
  cases m <;> simp only [shores, cost]
  · exact Finset.card_le_three
  · exact Finset.card_le_three
  · simp
  · simp
  · exact Finset.card_le_two
  · simp

/-- Each measurement is an explicit linear combination of its own shore queries. -/
theorem eval_formula (H : WeightedDiGraph V) : ∀ m : Measurement V,
    m.eval H =
      match m with
      | pair v w => H.out {v} + H.out (({w} : Finset V).erase v) - H.out {v, w}
      | star v T => H.out {v} + H.out (T.erase v) - H.out (insert v T)
      | outdeg v => H.out {v}
      | indeg v => H.out {v}ᶜ
      | imbalance v => H.out {v} - H.out {v}ᶜ
      | const r => r
  | pair v w => by
      have := H.symStar_eq_erase v {w}
      simpa [eval, WeightedDiGraph.symStar] using this
  | star v T => H.symStar_eq_erase v T
  | outdeg v => (H.out_singleton v).symm
  | indeg v => (H.out_compl_singleton v).symm
  | imbalance v => by
      simp [eval, WeightedDiGraph.imbalance, H.out_singleton, H.out_compl_singleton]
  | const r => rfl

/-- Agreement on a measurement's shores fixes its value (for any two graphs). -/
theorem eval_eq_of_agree (m : Measurement V) {H H' : WeightedDiGraph V}
    (h : ∀ S ∈ m.shores, H'.out S = H.out S) : m.eval H' = m.eval H := by
  rw [eval_formula H', eval_formula H]
  cases m <;> simp only [shores, Finset.mem_insert, Finset.mem_singleton,
    forall_eq_or_imp, forall_eq] at h ⊢
  · rw [h.1, h.2.1, h.2.2]
  · rw [h.1, h.2.1, h.2.2]
  · rw [h]
  · rw [h]
  · rw [h.1, h.2]

/-- Compilation of a measurement of the original graph. -/
def compile (G : WeightedDiGraph V) (m : Measurement V) : Compiled G m.eval :=
  ⟨m.shores, fun _ h => eval_eq_of_agree m h⟩

theorem compile_cost_le (G : WeightedDiGraph V) (m : Measurement V) :
    (compile G m).cost ≤ m.cost := card_shores_le m

/-- Compiling a finite family of measurements costs at most the sum of the costs. -/
theorem compileAll_card_le (G : WeightedDiGraph V) {ι : Type*} (s : Finset ι)
    (m : ι → Measurement V) :
    (Compiled.family s (fun i => compile G (m i))).shores.card ≤ ∑ i ∈ s, (m i).cost :=
  (Compiled.family_card_le s _).trans (Finset.sum_le_sum fun i _ => compile_cost_le G (m i))

end Measurement

/-- Exact transfer of symmetrized pairs, including originally zero pairs: a consistent
competitor cannot add capacity on a measured pair. -/
theorem Consistent.sym_w_eq {G G' : WeightedDiGraph V} {v w : V}
    (h : Consistent G G' (Measurement.pair v w).shores) : G'.sym.w v w = G.sym.w v w :=
  Measurement.eval_eq_of_agree (Measurement.pair v w) h

theorem Consistent.symStar_eq {G G' : WeightedDiGraph V} {v : V} {T : Finset V}
    (h : Consistent G G' (Measurement.star v T).shores) :
    G'.symStar v T = G.symStar v T :=
  Measurement.eval_eq_of_agree (Measurement.star v T) h

/-! ### Directed arcs are not determined by the cut function -/

/-- The directed 3-cycle `0 → 1 → 2 → 0`. -/
def cycle3 : WeightedDiGraph (Fin 3) where
  c u v := if v = u + 1 then 1 else 0
  nonneg u v := by split_ifs <;> norm_num
  diag v := by simp

/-- The reversed 3-cycle. -/
def cycle3rev : WeightedDiGraph (Fin 3) := cycle3.rev

/-- The two orientations of a triangle have identical outgoing-cut functions, but
different directed arcs: individual arcs (and directed partial stars) are not
determined by any set of outgoing-cut queries. -/
theorem directed_arc_not_determined :
    (∀ S, cycle3rev.out S = cycle3.out S) ∧ cycle3rev.c 0 1 ≠ cycle3.c 0 1 := by
  refine ⟨fun S => ?_, by simp [cycle3rev, cycle3, WeightedDiGraph.rev]⟩
  have key : ∀ S : Finset (Fin 3),
      (∑ u ∈ S, ∑ v ∈ Sᶜ, if u = v + 1 then 1 else 0 : ℕ) =
        ∑ u ∈ S, ∑ v ∈ Sᶜ, if v = u + 1 then 1 else 0 := by decide
  have h := congrArg (fun n : ℕ => (n : ℝ)) (key S)
  simpa [cycle3rev, cycle3, WeightedDiGraph.rev, WeightedDiGraph.out, Nat.cast_sum,
    Nat.cast_ite] using h

end CutQueryComplexity.DirectedCertificate
