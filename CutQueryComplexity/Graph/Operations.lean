import CutQueryComplexity.Problem.Basic

/-! # Cross weights, induced graphs, known deletions, and contractions -/

namespace CutQueryComplexity
namespace WeightedGraph

variable {V B : Type*} [Fintype V] [DecidableEq V]

/-- Total weight between two specified sets. Disjointness is imposed when needed. -/
def cross (G : WeightedGraph V) (S T : Finset V) : ℝ :=
  ∑ u ∈ S, ∑ v ∈ T, G.w u v

theorem cross_nonneg (G : WeightedGraph V) (S T : Finset V) : 0 ≤ G.cross S T :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => G.nonneg _ _

@[simp] theorem cross_empty_left (G : WeightedGraph V) (T : Finset V) :
    G.cross ∅ T = 0 := by simp [cross]

@[simp] theorem cross_empty_right (G : WeightedGraph V) (S : Finset V) :
    G.cross S ∅ = 0 := by simp [cross]

theorem cross_comm (G : WeightedGraph V) (S T : Finset V) :
    G.cross S T = G.cross T S := by
  rw [cross, cross, Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => G.symm _ _

@[simp] theorem cross_compl (G : WeightedGraph V) (S : Finset V) :
    G.cross S Sᶜ = G.cut S := rfl

theorem cross_union_left (G : WeightedGraph V) (S T U : Finset V) (h : Disjoint S T) :
    G.cross (S ∪ T) U = G.cross S U + G.cross T U := by
  exact Finset.sum_union h

theorem cross_union_right (G : WeightedGraph V) (S T U : Finset V) (h : Disjoint T U) :
    G.cross S (T ∪ U) = G.cross S T + G.cross S U := by
  simp only [cross, Finset.sum_union h, Finset.sum_add_distrib]

theorem cross_eq_sum_ite (G : WeightedGraph V) (S T : Finset V) :
    G.cross S T = ∑ u, ∑ v, if u ∈ S ∧ v ∈ T then G.w u v else 0 := by
  classical
  simp only [cross, ite_and, Finset.sum_ite_irrel]
  simp

/-- Three cuts determine the weight between disjoint shores. -/
theorem cross_eq_three_cuts (G : WeightedGraph V) {S T : Finset V}
    (hST : Disjoint S T) : G.cross S T = (G.cut S + G.cut T - G.cut (S ∪ T)) / 2 := by
  have h : G.cut (S ∪ T) + G.cross S T + G.cross T S = G.cut S + G.cut T := by
    simp only [cut_eq_sum_ite, cross_eq_sum_ite, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro v _
    have hu : u ∈ S → u ∉ T := fun h => Finset.disjoint_left.mp hST h
    have hv : v ∈ S → v ∉ T := fun h => Finset.disjoint_left.mp hST h
    by_cases huS : u ∈ S <;> by_cases huT : u ∈ T <;>
      by_cases hvS : v ∈ S <;> by_cases hvT : v ∈ T <;> simp_all
  rw [G.cross_comm T S] at h
  linarith

/-- Positive cross weight is equivalent to the presence of a positive edge. -/
theorem cross_pos_iff (G : WeightedGraph V) (S T : Finset V) :
    0 < G.cross S T ↔ ∃ u ∈ S, ∃ v ∈ T, 0 < G.w u v := by
  rw [cross, Finset.sum_pos_iff_of_nonneg (fun u _ =>
    Finset.sum_nonneg (fun v _ => G.nonneg u v))]
  simp_rw [Finset.sum_pos_iff_of_nonneg (fun v _ => G.nonneg _ v)]

/-- Induce on `U`, retaining isolated vertices outside `U` in the public vertex type. -/
def induce (G : WeightedGraph V) (U : Finset V) : WeightedGraph V where
  w u v := if u ∈ U ∧ v ∈ U then G.w u v else 0
  symm u v := by simp [and_comm, G.symm u v]
  nonneg u v := by split <;> simp_all [G.nonneg]
  diag v := by simp [G.diag]

theorem cut_induce (G : WeightedGraph V) (U S : Finset V) :
    (G.induce U).cut S = G.cross (S ∩ U) (U \ S) := by
  simp only [cut_eq_sum_ite, cross_eq_sum_ite, induce]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  by_cases huS : u ∈ S <;> by_cases huU : u ∈ U <;>
    by_cases hvS : v ∈ S <;> by_cases hvU : v ∈ U <;> simp [huS, huU, hvS, hvU]

/-- Subtract an explicitly known graph, clipping inconsistent transcripts at zero. -/
def subtract (G K : WeightedGraph V) : WeightedGraph V where
  w u v := max 0 (G.w u v - K.w u v)
  symm u v := by rw [G.symm, K.symm]
  nonneg _ _ := le_max_left _ _
  diag v := by simp [G.diag, K.diag]

theorem cut_subtract (G K : WeightedGraph V) (h : ∀ u v, K.w u v ≤ G.w u v)
    (S : Finset V) : (G.subtract K).cut S = G.cut S - K.cut S := by
  simp only [cut, subtract, max_eq_right (sub_nonneg.mpr (h _ _)), Finset.sum_sub_distrib]

variable [Fintype B] [DecidableEq B]

/-- Pull a public quotient shore back to the original vertices. -/
def pull (π : V → B) (T : Finset B) : Finset V := Finset.univ.filter (fun v => π v ∈ T)

@[simp] theorem mem_pull (π : V → B) (T : Finset B) (v : V) :
    v ∈ pull π T ↔ π v ∈ T := by simp [pull]

@[simp] theorem pull_compl (π : V → B) (T : Finset B) : pull π Tᶜ = (pull π T)ᶜ := by
  ext; simp

/-- The vertices in a public contraction block. -/
def fiber (π : V → B) (b : B) : Finset V := pull π {b}

@[simp] theorem mem_fiber (π : V → B) (b : B) (v : V) :
    v ∈ fiber π b ↔ π v = b := by simp [fiber]

theorem cross_fibers (G : WeightedGraph V) (π : V → B) (S T : Finset B) :
    (∑ b ∈ S, ∑ c ∈ T, G.cross (fiber π b) (fiber π c)) =
      G.cross (pull π S) (pull π T) := by
  simp only [cross_eq_sum_ite, mem_fiber]
  calc
    _ = ∑ b ∈ S, ∑ u, ∑ v, ∑ c ∈ T,
        if π u = b ∧ π v = c then G.w u v else 0 := by
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro u _
      rw [Finset.sum_comm]
    _ = ∑ u, ∑ v, ∑ b ∈ S, ∑ c ∈ T,
        if π u = b ∧ π v = c then G.w u v else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro u _
      rw [Finset.sum_comm]
    _ = _ := by simp [ite_and, Finset.sum_ite_irrel]

/-- Contract along a known block map and discard loops. Surjectivity is only needed
when lifting a proper quotient shore to a proper original shore. -/
def contract (G : WeightedGraph V) (π : V → B) : WeightedGraph B where
  w b c := if b = c then 0 else G.cross (fiber π b) (fiber π c)
  symm b c := by
    by_cases h : b = c
    · subst c; rfl
    · simp [h, Ne.symm h, G.cross_comm]
  nonneg b c := by split <;> simp_all [G.cross_nonneg]
  diag b := by simp

/-- A contraction cut is exactly one original cut query. -/
theorem cut_contract (G : WeightedGraph V) (π : V → B) (T : Finset B) :
    (G.contract π).cut T = G.cut (pull π T) := by
  calc
    _ = ∑ b ∈ T, ∑ c ∈ Tᶜ, G.cross (fiber π b) (fiber π c) := by
      apply Finset.sum_congr rfl
      intro b hb
      apply Finset.sum_congr rfl
      intro c hc
      have hbc : b ≠ c := by intro h; subst c; simpa [hb] using hc
      simp [contract, hbc]
    _ = _ := by rw [cross_fibers, pull_compl, cross_compl]

theorem properShore_pull (π : V → B) (hπ : Function.Surjective π) {T : Finset B}
    (hT : ProperShore T) : ProperShore (pull π T) := by
  constructor
  · obtain ⟨b, hb⟩ := hT.1
    obtain ⟨v, rfl⟩ := hπ b
    exact ⟨v, (mem_pull _ _ _).mpr hb⟩
  · intro h
    apply hT.2
    apply Finset.eq_univ_of_forall
    intro b
    obtain ⟨v, rfl⟩ := hπ b
    have : v ∈ pull π T := by rw [h]; simp
    simpa using this

end WeightedGraph
end CutQueryComplexity
