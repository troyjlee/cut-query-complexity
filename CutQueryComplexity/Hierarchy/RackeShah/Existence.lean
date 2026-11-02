import CutQueryComplexity.Hierarchy.RackeShah.Construction
import CutQueryComplexity.Hierarchy.Laminar
import CutQueryComplexity.Hierarchy.Existence

/-! # The `O(log n log log n)` hierarchy bound (Räcke–Shah, M6)

The certified root decomposition of M5 is a laminar cover of the vertex set; its laminar
hierarchy has childless singleton leaves, at most `2n − 1` nodes and depth less than `L(n)`
(halving), and by the weighted-majority bound (M1) its canonical representation cost of every
shore is at most `2 · loadBound n (2n) n ≤ 268 L(n) K(n)` times the cut.

`exists_hierarchyBound_log_mul_loglog` packages this as `HierarchyBound` with distortion
`268 L(n) L(L(n))` and height `2 L(n)`, for every finite vertex type and every nonnegative real
weighted graph, with the one-root convention on the empty vertex set. The quadratic-distortion
theorem `exists_hierarchyBound_sq` is unchanged.
-/

namespace CutQueryComplexity
namespace Hierarchy
namespace RackeShah

open WeightedGraph Finset Certificate DetMinCut

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The distortion constant `2 (2κ + 6)`. -/
def rsConstant : ℝ := 268

/-! ## Logarithms against `L(n)` -/

theorem lg_two_mul_le_logL (n : ℕ) : lg (2 * n) ≤ logL n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [lg, Real.logb_zero]
  · have h1 : ((2 * n : ℕ) : ℝ) ≤ (2 : ℝ) ^ Nat.clog 2 (2 * n) := by
      exact_mod_cast Nat.le_pow_clog one_lt_two (2 * n)
    have h2 : lg (2 * n) ≤ Nat.clog 2 (2 * n) := by
      unfold lg
      calc Real.logb 2 ((2 * n : ℕ) : ℝ) ≤ Real.logb 2 ((2 : ℝ) ^ Nat.clog 2 (2 * n)) :=
            (Real.logb_le_logb one_lt_two (by positivity) (by positivity)).mpr h1
        _ = Nat.clog 2 (2 * n) := by
            rw [Real.logb_pow, Real.logb_self_eq_one one_lt_two, mul_one]
    have h3 : (Nat.clog 2 (2 * n) : ℝ) ≤ logL n := by exact_mod_cast clog_le_logL' n
    exact h2.trans h3

theorem lg_le_logL (n : ℕ) : lg n ≤ logL n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [lg, Real.logb_zero]
  · exact (lg_mono hn (by omega)).trans (lg_two_mul_le_logL n)

/-- The root load bound in terms of `L(n) K(n)`. -/
theorem loadBound_root_le (n : ℕ) :
    2 * loadBound n (2 * n) n ≤ rsConstant * logL n * KK n := by
  unfold loadBound rsConstant
  have h1 := lg_two_mul_le_logL n
  have h2 := lg_le_logL n
  have hL : (1 : ℝ) ≤ logL n := by exact_mod_cast one_le_logL' n
  have hK : (1 : ℝ) ≤ KK n := by exact_mod_cast one_le_KK n
  have hκ : kappa = 64 := rfl
  rw [hκ]
  nlinarith

/-! ## The laminar hierarchy of a root decomposition -/

theorem isLaminarCover_of_dec [Nonempty V] {G : WeightedGraph V}
    {Q : Finset V → WeightedGraph V} {F : Finset (Finset V)} (h : Dec G Q univ F) :
    IsLaminarCover F :=
  ⟨h.nonempty_mem, h.laminar, h.mem_self, fun v => h.singleton_mem v (mem_univ v)⟩

theorem childParts_eq_parts {F : Finset (Finset V)} (hF : IsLaminarCover F) (x : LNode F) :
    childParts (laminarHier F hF) x = parts F x.1 := by
  ext C
  rw [childParts, mem_image, mem_parts]
  constructor
  · rintro ⟨c, hc, rfl⟩
    rw [laminarHier_cluster_eq]
    exact ⟨c.2, (mem_children_iff_maximal hF).mp hc⟩
  · rintro ⟨hC, hCx, hmax⟩
    exact ⟨⟨C, hC⟩, (mem_children_iff_maximal hF).mpr ⟨hCx, hmax⟩, laminarHier_cluster_eq hF _⟩

/-- The representation-cost bound of a certified decomposition with load bound `D`. -/
theorem rep_le_of_certified [Nonempty V] (G : WeightedGraph V) {Q : Finset V → WeightedGraph V}
    {F : Finset (Finset V)} (hDec : Dec G Q univ F) (hF : IsLaminarCover F) {D : ℝ}
    (hload : ∀ u v, ∑ S ∈ F, (Q S).w u v ≤ D * G.w u v) (A : Finset V) :
    (laminarHier F hF).rep ((laminarHier F hF).canon G) A ≤ 2 * (D * G.cut A) := by
  set H := laminarHier F hF
  have hlc := leafChildless hF
  have hne : ∀ x : LNode F, (H.cluster x).Nonempty := fun x => by
    rw [laminarHier_cluster_eq]; exact hDec.nonempty_mem x.1 x.2
  have hloc : ∀ x, ¬ H.IsLeaf x → Local G (H.cluster x) (childParts H x) (Q x.1) := by
    intro x hx
    rw [laminarHier_cluster_eq, childParts_eq_parts]
    have h2 : 2 ≤ x.1.card := by
      rcases Nat.lt_or_ge x.1.card 2 with h | h
      · exfalso
        have h1 : x.1.card = 1 := by have := (hDec.nonempty_mem x.1 x.2).card_pos; omega
        obtain ⟨v, hv⟩ := card_eq_one.mp h1
        exact hx ((isLeaf_iff hF x).mpr ⟨v, hv⟩)
      · exact h
    exact hDec.parts_local x.1 x.2 h2
  refine (rep_le_two_mul_sum_cut H hlc G (fun x => Q x.1) hne hloc A).trans ?_
  have hsum : ∑ x : LNode F, (Q x.1).cut A = ∑ S ∈ F, (Q S).cut A :=
    Finset.sum_coe_sort F fun S => (Q S).cut A
  rw [hsum]
  gcongr
  calc ∑ S ∈ F, (Q S).cut A = ∑ u ∈ A, ∑ v ∈ Aᶜ, ∑ S ∈ F, (Q S).w u v := by
        simp only [cut]
        rw [sum_comm]
        exact sum_congr rfl fun u _ => sum_comm
    _ ≤ ∑ u ∈ A, ∑ v ∈ Aᶜ, D * G.w u v :=
        sum_le_sum fun u _ => sum_le_sum fun v _ => hload u v
    _ = D * G.cut A := by rw [cut, mul_sum]; exact sum_congr rfl fun u _ => (mul_sum _ _ _).symm

/-- Depths are below `L(n)`. -/
theorem depth_lt_logL [Nonempty V] {G : WeightedGraph V} {Q : Finset V → WeightedGraph V}
    {F : Finset (Finset V)} (hDec : Dec G Q univ F) (hF : IsLaminarCover F) (x : LNode F) :
    (laminarHier F hF).T.depth x < logL (Fintype.card V) := by
  show depthL F x < _
  rw [depthL_eq_card_filter]
  have h1 := hDec.halving x.1 x.2
  rw [card_univ] at h1
  have h2 : 1 ≤ x.1.card := (hDec.nonempty_mem x.1 x.2).card_pos
  have h3 : 2 ^ (F.filter fun T => x.1 ⊂ T).card < 2 ^ logL (Fintype.card V) :=
    calc 2 ^ (F.filter fun T => x.1 ⊂ T).card
        ≤ 2 ^ (F.filter fun T => x.1 ⊂ T).card * x.1.card := Nat.le_mul_of_pos_right _ h2
      _ ≤ Fintype.card V := h1
      _ < 2 * Fintype.card V := by have := Fintype.card_pos (α := V); omega
      _ ≤ 2 ^ logL (Fintype.card V) := le_two_pow_logL _
  exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp h3

/-! ## The endpoint -/

/-- **Räcke–Shah, offline, with the explicit constant.** Every nonnegative real-weighted graph
on `n` vertices has a hierarchy with at most `2n + 1` nodes, childless terminal nodes, height at
most `2 L(n)`, and canonical representation cost at most `268 L(n) L(L(n))` times every cut. -/
theorem rackeShah_hierarchyBound :
    HierarchyBound (fun n => rsConstant * (logL n : ℝ) * (logL (logL n) : ℝ))
      (fun n => 2 * logL n) := by
  intro W _ _ J
  rcases isEmpty_or_nonempty W with hW | hW
  · refine ⟨1, trivHier W, by omega, fun v => isEmptyElim v, ?_, fun S => ?_⟩
    · exact Finset.sup_le fun _ _ => by simp [trivHier, trivTree]
    · have hext : (trivHier W).Extends S (fun _ => false) := fun v => isEmptyElim v
      refine ((trivHier W).rep_le _ hext).trans ?_
      have h0 : (trivHier W).edges = ∅ := by
        ext x; simp only [Hier.mem_edges, Finset.notMem_empty, iff_false, not_not]
        exact Subsingleton.elim x _
      rw [Hier.labelCost, h0, sum_empty]
      have hL : (0 : ℝ) ≤ logL (Fintype.card W) := Nat.cast_nonneg _
      have hK : (0 : ℝ) ≤ logL (logL (Fintype.card W)) := Nat.cast_nonneg _
      have := J.cut_nonneg S
      have : (0 : ℝ) ≤ rsConstant := by norm_num [rsConstant]
      positivity
  · obtain ⟨Q, F, hDec, hload, -⟩ := exists_certified_univ J
    have hF := isLaminarCover_of_dec hDec
    set H := laminarHier F hF
    set e := Fintype.equivFin (LNode F)
    refine ⟨Fintype.card (LNode F), H.transfer e, ?_, ?_, ?_, fun S => ?_⟩
    · have := card_node_le hF; omega
    · exact Hier.leafChildless_transfer (leafChildless hF) e
    · refine Hier.height_transfer_le (fun x => ?_) e
      exact le_trans (depth_lt_logL hDec hF x).le
        (by omega : logL (Fintype.card W) ≤ 2 * logL (Fintype.card W))
    · refine (Hier.rep_transfer_le H e J S).trans ?_
      have hload' : ∀ u v, ∑ T ∈ F, (Q T).w u v ≤
          loadBound (Fintype.card W) (2 * Fintype.card W) (Fintype.card W) * J.w u v := by
        intro u v
        have := hload u v (mem_univ u) (mem_univ v)
        rwa [card_univ] at this
      refine (rep_le_of_certified J hDec hF hload' S).trans ?_
      have h1 := loadBound_root_le (Fintype.card W)
      have h2 := J.cut_nonneg S
      show 2 * (loadBound (Fintype.card W) (2 * Fintype.card W) (Fintype.card W) * J.cut S) ≤
        rsConstant * logL (Fintype.card W) * (logL (logL (Fintype.card W)) : ℝ) * J.cut S
      have hK : (KK (Fintype.card W) : ℝ) = logL (logL (Fintype.card W)) := rfl
      rw [← hK]
      nlinarith

/-- **Räcke–Shah, offline.** -/
theorem exists_hierarchyBound_log_mul_loglog :
    ∃ C : ℝ, 1 ≤ C ∧
      HierarchyBound (fun n => C * (logL n : ℝ) * (logL (logL n) : ℝ)) (fun n => 2 * logL n) :=
  ⟨rsConstant, by norm_num [rsConstant], rackeShah_hierarchyBound⟩

end RackeShah
end Hierarchy
end CutQueryComplexity
