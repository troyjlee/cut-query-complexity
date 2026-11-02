import CutQueryComplexity.Hierarchy.Existence.Tree
import CutQueryComplexity.Hierarchy.Refine
import CutQueryComplexity.DetMinCut.Parameters

/-! # Hierarchy existence (hierarchy plan, Milestones 5–6)

`exists_hierarchyBound_sq`: every explicit graph on `n` vertices has a hierarchy with at most
`2n + 1` nodes, childless leaves, height at most `4 L(n)`, and canonical representation cost at
most `1690 L(n)²` times every cut, where `L(n) = max 1 ⌈log₂ 2n⌉`. That is,

  `HierarchyBound (fun n => 1690 L(n)²) (fun n => 4 L(n))`,

with no assumption. The construction is the recursive balanced bandwidth partition with
`λ = 12 L(n) + 1` (Milestones 3–4), turned into a hierarchy whose clusters shrink by `5/6` per
level, and bounded by the majority labelling (Milestone 1). The cubic form required by the
log-seven plan is `exists_polylog_hierarchyBound`.
-/

namespace CutQueryComplexity
namespace Hierarchy

open WeightedGraph Finset TwoRespecting DetMinCut

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ## Transport along an equivalence of node types -/

namespace Hier

variable {N M : Type} [Fintype N] [DecidableEq N] [Fintype M] [DecidableEq M]

/-- The rooted tree transported along `e`. -/
def transferTree (T : RootedTree N) (e : N ≃ M) : RootedTree M where
  root := e T.root
  parent x := e (T.parent (e.symm x))
  depth x := T.depth (e.symm x)
  parent_root := by simp [T.parent_root]
  depth_root := by simp [T.depth_root]
  depth_parent v hv := by
    have := T.depth_parent (e.symm v) fun h => hv (by rw [← h]; simp)
    simpa using this

/-- The hierarchy transported along `e`. -/
def transfer (H : Hier V N) (e : N ≃ M) : Hier V M :=
  ⟨transferTree H.T e, fun v => e (H.leaf v), e.injective.comp H.leaf_inj⟩

omit [Fintype N] [DecidableEq N] [Fintype M] [DecidableEq M] in
theorem iterate_transfer (T : RootedTree N) (e : N ≃ M) (k : ℕ) (y : N) :
    (transferTree T e).parent^[k] (e y) = e (T.parent^[k] y) := by
  induction k generalizing y with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
      show (transferTree T e).parent^[k] (e (T.parent (e.symm (e y)))) = _
      rw [e.symm_apply_apply, ih]

omit [Fintype N] [DecidableEq N] [Fintype M] [DecidableEq M] in
theorem isAnc_transfer (T : RootedTree N) (e : N ≃ M) (x y : N) :
    (transferTree T e).IsAnc (e x) (e y) ↔ T.IsAnc x y := by
  constructor
  · rintro ⟨k, hk⟩
    rw [iterate_transfer] at hk
    exact ⟨k, e.injective hk⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, by rw [iterate_transfer, hk]⟩

omit [DecidableEq V] [Fintype N] [Fintype M] in
theorem cluster_transfer (H : Hier V N) (e : N ≃ M) (x : N) :
    (H.transfer e).cluster (e x) = H.cluster x := by
  ext v
  rw [mem_cluster, mem_cluster]
  exact isAnc_transfer H.T e x (H.leaf v)

omit [Fintype V] [DecidableEq V] in
theorem edges_transfer (H : Hier V N) (e : N ≃ M) :
    (H.transfer e).edges = H.edges.map e.toEmbedding := by
  ext x'
  simp only [mem_edges, mem_map_equiv]
  show x' ≠ e H.T.root ↔ e.symm x' ≠ H.T.root
  constructor
  · intro h h'; exact h (by rw [← h']; simp)
  · intro h h'; exact h (by rw [h']; simp)

omit [Fintype V] [DecidableEq V] in
theorem children_transfer (H : Hier V N) (e : N ≃ M) (x : N) :
    (H.transfer e).children (e x) = (H.children x).map e.toEmbedding := by
  ext c'
  rw [mem_children, mem_map_equiv, mem_children]
  show c' ≠ e H.T.root ∧ e (H.T.parent (e.symm c')) = e x ↔ _
  rw [e.apply_eq_iff_eq]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨fun h => h1 (by rw [← h]; simp), h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨fun h => h1 (by rw [h]; simp), h2⟩

omit [Fintype V] [DecidableEq V] in
theorem leafChildless_transfer {H : Hier V N} (hlc : H.LeafChildless) (e : N ≃ M) :
    (H.transfer e).LeafChildless := by
  intro v
  show (H.transfer e).children (e (H.leaf v)) = ∅
  rw [children_transfer, hlc v, map_empty]

omit [Fintype V] [DecidableEq V] [Fintype N] [DecidableEq N] [DecidableEq M] in
theorem height_transfer_le {H : Hier V N} {D : ℕ} (hD : ∀ x, H.T.depth x ≤ D) (e : N ≃ M) :
    (H.transfer e).height ≤ D :=
  Finset.sup_le fun x' _ => hD (e.symm x')

/-- Transport does not increase the representation cost. -/
theorem rep_transfer_le (H : Hier V N) (e : N ≃ M) (J : WeightedGraph V) (S : Finset V) :
    (H.transfer e).rep ((H.transfer e).canon J) S ≤ H.rep (H.canon J) S := by
  obtain ⟨ℓ, hℓ, hR⟩ := H.exists_rep_eq (H.canon J) S
  have hext : (H.transfer e).Extends S (ℓ ∘ e.symm) := by
    intro v; show ℓ (e.symm (e (H.leaf v))) = _; rw [e.symm_apply_apply]; exact hℓ v
  refine ((H.transfer e).rep_le _ hext).trans (le_of_eq ?_)
  rw [hR]
  unfold labelCost
  rw [edges_transfer, sum_map]
  refine sum_congr rfl fun x _ => ?_
  show J.cut ((H.transfer e).cluster (e x)) * |toReal (ℓ ∘ e.symm) (e x) -
    toReal (ℓ ∘ e.symm) (e (H.T.parent (e.symm (e x))))| = _
  rw [cluster_transfer]
  simp only [toReal, Function.comp, e.symm_apply_apply]
  rfl

end Hier

/-! ## The parameters -/

theorem beta_le_logL (n : ℕ) : beta n ≤ 3 * (logL n : ℝ) := by
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0; simp [beta]
  unfold beta
  have hl := log43_pos
  rw [div_le_iff₀ hl]
  have h1 : Real.log n ≤ logL n * Real.log 2 := by
    have : (n : ℝ) ≤ 2 ^ logL n := by
      have := le_two_pow_logL n
      exact_mod_cast (show n ≤ 2 ^ logL n by omega)
    calc Real.log n ≤ Real.log (2 ^ logL n) := Real.log_le_log (by exact_mod_cast hpos) this
      _ = logL n * Real.log 2 := by rw [Real.log_pow]
  have h2 : Real.log 2 ≤ 3 * Real.log (4 / 3) := by
    have : Real.log 2 ≤ Real.log ((4 / 3 : ℝ) ^ 3) := Real.log_le_log (by norm_num) (by norm_num)
    rwa [Real.log_pow, Nat.cast_ofNat] at this
  have hL : (0 : ℝ) ≤ logL n := Nat.cast_nonneg _
  nlinarith

/-- The fixed bandwidth parameter `λ = 12 L(n) + 1`. -/
noncomputable def lamH (V : Type) [Fintype V] : ℝ := 12 * (logL (Fintype.card V) : ℝ) + 1

omit [DecidableEq V] in
theorem one_le_lamH : 1 ≤ lamH V := by
  unfold lamH; have : (0 : ℝ) ≤ logL (Fintype.card V) := Nat.cast_nonneg _; linarith

omit [DecidableEq V] in
theorem beta_le_lamH : 4 * beta (Fintype.card V) ≤ lamH V := by
  unfold lamH; have := beta_le_logL (Fintype.card V); linarith

/-! ## Depth -/

/-- Depths are at most `4 L(n)`. -/
theorem depthN_le [Nonempty V] (J : WeightedGraph V) (X : Node J (one_le_lamH (V := V))
    (beta_le_lamH (V := V))) :
    depthN J (one_le_lamH (V := V)) (beta_le_lamH (V := V)) X ≤ 4 * logL (Fintype.card V) := by
  have hn : Fintype.card V ≤ 2 ^ logL (Fintype.card V) := by
    have := le_two_pow_logL (Fintype.card V); omega
  set d := depthN J (one_le_lamH (V := V)) (beta_le_lamH (V := V)) X
  set L := logL (Fintype.card V)
  have hp := pow_card_le J (one_le_lamH (V := V)) (beta_le_lamH (V := V)) X
  have hX := (node_good J (one_le_lamH (V := V)) (beta_le_lamH (V := V)) X).1.card_pos
  by_contra hlt
  push Not at hlt
  -- `6^d ≤ 5^d n ≤ 5^d 2^L`, but `6^(4L) ≥ 2^L 5^(4L)` and `6 > 5`
  have h1 : 6 ^ d ≤ 5 ^ d * 2 ^ L := by
    calc 6 ^ d ≤ 6 ^ d * X.1.card := Nat.le_mul_of_pos_right _ hX
      _ ≤ 5 ^ d * Fintype.card V := hp
      _ ≤ 5 ^ d * 2 ^ L := Nat.mul_le_mul_left _ hn
  have h2 : 2 ^ L * 5 ^ (4 * L) ≤ 6 ^ (4 * L) := by
    rw [pow_mul, pow_mul, ← mul_pow]
    exact Nat.pow_le_pow_left (by norm_num) L
  obtain ⟨k, hk⟩ : ∃ k, d = 4 * L + (k + 1) := ⟨d - 4 * L - 1, by omega⟩
  have h3 : 5 ^ (k + 1) < 6 ^ (k + 1) := Nat.pow_lt_pow_left (by norm_num) (by omega)
  rw [hk, pow_add 6 (4 * L) (k + 1), pow_add 5 (4 * L) (k + 1)] at h1
  have h4 : 2 ^ L * 5 ^ (4 * L) * 5 ^ (k + 1) < 6 ^ (4 * L) * 6 ^ (k + 1) := by
    calc 2 ^ L * 5 ^ (4 * L) * 5 ^ (k + 1) ≤ 6 ^ (4 * L) * 5 ^ (k + 1) :=
          Nat.mul_le_mul_right _ h2
      _ < 6 ^ (4 * L) * 6 ^ (k + 1) := Nat.mul_lt_mul_of_pos_left h3 (by positivity)
  have e : 5 ^ (4 * L) * 5 ^ (k + 1) * 2 ^ L = 2 ^ L * 5 ^ (4 * L) * 5 ^ (k + 1) := by ring
  rw [e] at h1
  exact absurd h1 (not_le.mpr h4)

/-! ## Hierarchy existence -/

/-- The one-node tree. -/
def trivTree : RootedTree (Fin 1) where
  root := 0
  parent _ := 0
  depth _ := 0
  parent_root := rfl
  depth_root := rfl
  depth_parent v hv := absurd (Subsingleton.elim v 0) hv

/-- The hierarchy on no vertices. -/
def trivHier (W : Type) [IsEmpty W] : Hier W (Fin 1) :=
  ⟨trivTree, fun v => isEmptyElim v, fun v => isEmptyElim v⟩

/-- The distortion constant: `26 λ (4L + 1) ≤ 1690 L²`. -/
theorem distortion_le (n : ℕ) :
    26 * (12 * (logL n : ℝ) + 1) * ((4 * logL n : ℕ) + 1) ≤ 1690 * (logL n : ℝ) ^ 2 := by
  have hL : (1 : ℝ) ≤ logL n := by exact_mod_cast one_le_logL' n
  push_cast
  nlinarith

/-- **Hierarchy existence, quadratic form.** -/
theorem exists_hierarchyBound_sq :
    HierarchyBound (fun n => 1690 * (logL n : ℝ) ^ 2) (fun n => 4 * logL n) := by
  intro W _ _ J
  rcases isEmpty_or_nonempty W with hW | hW
  · -- no vertices: a single root
    refine ⟨1, trivHier W, by omega, fun v => isEmptyElim v, ?_, fun S => ?_⟩
    · exact Finset.sup_le fun _ _ => by simp [trivHier, trivTree]
    · have hext : (trivHier W).Extends S (fun _ => false) := fun v => isEmptyElim v
      refine ((trivHier W).rep_le _ hext).trans ?_
      have h0 : (trivHier W).edges = ∅ := by
        ext x; simp only [Hier.mem_edges, Finset.notMem_empty, iff_false, not_not]
        exact Subsingleton.elim x _
      rw [Hier.labelCost, h0, sum_empty]
      exact mul_nonneg (by positivity) (J.cut_nonneg S)
  · set hl1 := one_le_lamH (V := W)
    set hlB := beta_le_lamH (V := W)
    set H := clusterHier J hl1 hlB
    set e := Fintype.equivFin (Node J hl1 hlB)
    refine ⟨Fintype.card (Node J hl1 hlB), H.transfer e, ?_, ?_, ?_, fun S => ?_⟩
    · have := card_clusters_le J hl1 hlB univ (good_univ J hl1)
      rw [card_univ] at this
      rw [Fintype.card_coe]
      omega
    · apply Hier.leafChildless_transfer
      intro v
      ext C
      simp only [Finset.notMem_empty, iff_false]
      intro hC
      have hmem := (mem_children_iff J hl1 hlB _ C).mp hC
      have hlt : C.1.card < ({v} : Finset W).card := bpart_card_lt J hl1 hlB hmem
      rw [card_singleton] at hlt
      have := (node_good J hl1 hlB C).1.card_pos
      omega
    · exact Hier.height_transfer_le (fun X => depthN_le J X) e
    · refine (Hier.rep_transfer_le H e J S).trans ?_
      refine (rep_le_clusterHier J hl1 hlB (D := 4 * logL (Fintype.card W))
        (fun X => depthN_le J X) S).trans ?_
      have hd := distortion_le (Fintype.card W)
      have hc := J.cut_nonneg S
      show 26 * lamH W * (((4 * logL (Fintype.card W) : ℕ) : ℝ) + 1) * J.cut S ≤ _
      unfold lamH
      exact mul_le_mul_of_nonneg_right hd hc

/-- `HierarchyBound` is monotone in the distortion. -/
theorem HierarchyBound.mono {a a' : ℕ → ℝ} {h : ℕ → ℕ} (hb : HierarchyBound a h)
    (ha : ∀ r, a r ≤ a' r) : HierarchyBound a' h := by
  intro W _ _ J
  obtain ⟨m, H, hm, hlc, hht, hdist⟩ := hb W J
  exact ⟨m, H, hm, hlc, hht, fun S =>
    (hdist S).trans (mul_le_mul_of_nonneg_right (ha _) (J.cut_nonneg S))⟩

/-- **Hierarchy existence, the cubic form of the plan.** -/
theorem exists_polylog_hierarchyBound :
    ∃ A : ℝ, ∃ K : ℕ, 1 ≤ A ∧ 1 ≤ K ∧
      HierarchyBound (fun n => A * (logL n : ℝ) ^ 3) (fun n => K * logL n) := by
  refine ⟨1690, 4, by norm_num, by norm_num, exists_hierarchyBound_sq.mono fun r => ?_⟩
  have hL : (1 : ℝ) ≤ logL r := by exact_mod_cast one_le_logL' r
  have : (logL r : ℝ) ^ 2 ≤ (logL r : ℝ) ^ 3 := pow_le_pow_right₀ hL (by norm_num)
  linarith

end Hierarchy
end CutQueryComplexity
