import CutQueryComplexity.Hierarchy.Supplied
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-! # An elementary guard graph (Lemma 19 for hierarchies of bounded height)

For nonnegative capacities `cap` on the tree edges, each node `x` spreads a unit of
mass over the vertices below it: at every node the mass is split among the children in
proportion to their capacities. Write `π_x` for the resulting distribution and
`W_u = ∑_{c child of u} cap c`. The guard graph is the star-mesh graph

  `J = ∑_u ∑_{c ≠ c' children of u} (cap c · cap c' / W_u) · π_c ⊗ π_{c'}`,

so `c_J(S) = ∑_u ∑_{c ≠ c'} (cap c · cap c' / W_u) π_c(S) π_{c'}(Sᶜ)`.

* **Lower bound** (`guard_lower`): the real labelling `x ↦ π_x(S)` extends `S` and costs
  at most `2 c_J(S)`. At each node, `|p_c − p̄| ≤ ∑_{c'} (cap c'/W) |p_c − p_{c'}|` and
  `|p − p'| ≤ p(1−p') + p'(1−p)` on `[0,1]`.
* **Upper bound** (`guard_upper`): if the capacities are subadditive over children
  (canonical capacities are), then `c_J(S) ≤ D · cost(ℓ)` for every binary extension
  `ℓ`, where `D` is the height of the tree. The star at `u` costs at most the
  capacity-weighted mass disagreeing with `ℓ u` among the children, and that
  disagreement is charged to the label changes below `u`.

So `2J` is a guard of quality `2D` (`guardFor_of_leafChildless`). This replaces the
flow-sparsifier citation of Lemma 19 and the flow-decomposition argument of Remark 20.
-/

namespace CutQueryComplexity
namespace Hierarchy

open TwoRespecting WeightedGraph Finset

variable {V : Type} [Fintype V] [DecidableEq V]

theorem sum_swap21 {α β γ : Type} (A : Finset α) (B : Finset β) (C : Finset γ)
    (f : α → β → γ → ℝ) :
    ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, f a b c = ∑ c ∈ C, ∑ a ∈ A, ∑ b ∈ B, f a b c := by
  calc ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, f a b c = ∑ a ∈ A, ∑ c ∈ C, ∑ b ∈ B, f a b c :=
        sum_congr rfl fun a _ => sum_comm
    _ = _ := sum_comm

theorem sum_swap22 {α β γ δ : Type} (A : Finset α) (B : Finset β) (C : Finset γ) (D : Finset δ)
    (f : α → β → γ → δ → ℝ) :
    ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, ∑ d ∈ D, f a b c d =
      ∑ c ∈ C, ∑ d ∈ D, ∑ a ∈ A, ∑ b ∈ B, f a b c d := by
  rw [sum_swap21 A B C]
  exact sum_congr rfl fun c _ => sum_swap21 A B D _

namespace Hier

variable {N : Type} [Fintype N] [DecidableEq N] (H : Hier V N) (cap : N → ℝ)

/-- Total capacity of the children. -/
def W (x : N) : ℝ := ∑ c ∈ H.children x, cap c

/-- Proper descendants of `x` on the way to the leaf of `v`. -/
def pathSet (x : N) (v : V) : Finset N :=
  univ.filter fun y => H.T.IsAnc x y ∧ y ≠ x ∧ H.T.IsAnc y (H.leaf v)

/-- The mass distribution of `x` over the vertices. -/
noncomputable def pi (x : N) (v : V) : ℝ :=
  if H.T.IsAnc x (H.leaf v) then ∏ y ∈ H.pathSet x v, cap y / H.W cap (H.T.parent y) else 0

/-- Mass of `x` on a vertex set. -/
noncomputable def pmass (S : Finset V) (x : N) : ℝ := ∑ v ∈ S, H.pi cap x v

/-- Star-mesh weight of a pair of children of `u`. -/
noncomputable def kw (u c c' : N) : ℝ := if c = c' then 0 else cap c * cap c' / H.W cap u

variable {H cap}

/-! ### Basic facts about the distributions -/

omit [Fintype V] [DecidableEq V] in
theorem W_nonneg (hcap : ∀ x, 0 ≤ cap x) (x : N) : 0 ≤ H.W cap x :=
  sum_nonneg fun c _ => hcap c

omit [Fintype V] [DecidableEq V] in
theorem pi_nonneg (hcap : ∀ x, 0 ≤ cap x) (x : N) (v : V) : 0 ≤ H.pi cap x v := by
  unfold pi
  split_ifs
  · exact Finset.prod_nonneg fun y _ => div_nonneg (hcap y) (W_nonneg hcap _)
  · exact le_rfl

omit [Fintype V] [DecidableEq V] in
theorem pi_of_not {x : N} {v : V} (h : ¬ H.T.IsAnc x (H.leaf v)) : H.pi cap x v = 0 := by
  simp [pi, h]

omit [Fintype V] [DecidableEq V] in
theorem isAnc_of_pi_ne {x : N} {v : V} (h : H.pi cap x v ≠ 0) : H.T.IsAnc x (H.leaf v) := by
  by_contra h'; exact h (pi_of_not h')

omit [Fintype V] [DecidableEq V] in
theorem kw_nonneg (hcap : ∀ x, 0 ≤ cap x) (u c c' : N) : 0 ≤ H.kw cap u c c' := by
  unfold kw
  split_ifs
  · exact le_rfl
  · exact div_nonneg (mul_nonneg (hcap c) (hcap c')) (W_nonneg hcap u)

omit [Fintype V] [DecidableEq V] in
theorem kw_symm (u c c' : N) : H.kw cap u c c' = H.kw cap u c' c := by
  unfold kw
  by_cases h : c = c'
  · subst h; rfl
  · rw [ite_eq_right h, ite_eq_right (Ne.symm h), mul_comm (cap c)]

omit [Fintype V] [DecidableEq V] in
theorem kw_le (hcap : ∀ x, 0 ≤ cap x) (u c c' : N) :
    H.kw cap u c c' ≤ cap c * cap c' / H.W cap u := by
  unfold kw
  split_ifs
  · exact div_nonneg (mul_nonneg (hcap c) (hcap c')) (W_nonneg hcap u)
  · exact le_rfl

omit [Fintype V] [DecidableEq V] in
/-- The capacity fractions of the children sum to at most one. -/
theorem sum_ratio_le_one (x : N) :
    ∑ c ∈ H.children x, cap c / H.W cap x ≤ 1 := by
  simp only [div_eq_mul_inv, ← sum_mul]
  change H.W cap x * (H.W cap x)⁻¹ ≤ 1
  by_cases h : H.W cap x = 0
  · rw [h]; norm_num
  · rw [mul_inv_cancel₀ h]

omit [Fintype V] [DecidableEq V] in
theorem sum_ratio_eq_one {x : N} (h : H.W cap x ≠ 0) :
    ∑ c ∈ H.children x, cap c / H.W cap x = 1 := by
  simp only [div_eq_mul_inv, ← sum_mul]
  exact mul_inv_cancel₀ h

omit [Fintype V] [DecidableEq V] in
theorem pathSet_insert {x c0 : N} {v : V} (hc0 : c0 ∈ H.children x)
    (h0 : H.T.IsAnc c0 (H.leaf v)) : H.pathSet x v = insert c0 (H.pathSet c0 v) := by
  ext y
  simp only [pathSet, mem_filter, mem_univ, true_and, mem_insert]
  constructor
  · rintro ⟨hxy, hyx, hyl⟩
    rcases RootedTree.isAnc_total_of_common hyl h0 with h1 | h1
    · left
      have hdx : H.T.depth x < H.T.depth y := by
        rcases lt_or_eq_of_le hxy.depth_le with hl | he
        · exact hl
        · exact absurd (RootedTree.eq_of_isAnc_of_depth_eq hxy he).symm hyx
      have hdc := depth_child hc0
      have := h1.depth_le
      exact RootedTree.eq_of_isAnc_of_depth_eq h1 (by omega)
    · by_cases hyc : y = c0
      · exact Or.inl hyc
      · exact Or.inr ⟨h1, hyc, hyl⟩
  · rintro (rfl | ⟨h1, h2, h3⟩)
    · exact ⟨isAnc_of_mem_children hc0 (RootedTree.isAnc_refl _),
        (ne_of_mem_children hc0 (RootedTree.isAnc_refl _)).symm, h0⟩
    · exact ⟨isAnc_of_mem_children hc0 h1, (ne_of_mem_children hc0 h1).symm, h3⟩

omit [Fintype V] [DecidableEq V] in
/-- Away from leaf nodes, a node's mass is split among its children. -/
theorem pi_rec {x : N} (hx : ¬ H.IsLeaf x) (v : V) :
    H.pi cap x v = ∑ c ∈ H.children x, cap c / H.W cap x * H.pi cap c v := by
  by_cases h : H.T.IsAnc x (H.leaf v)
  · have hne : x ≠ H.leaf v := fun he => hx ⟨v, he.symm⟩
    obtain ⟨c0, hc0, h0⟩ := exists_child (H := H) h hne
    rw [sum_eq_single c0 (fun c hc hcne => by
      rw [pi_of_not fun h' => hcne (child_unique hc hc0 h' h0), mul_zero])
      (fun h' => absurd hc0 h')]
    have hnot : c0 ∉ H.pathSet c0 v := by simp [pathSet]
    unfold pi
    rw [ite_eq_left h, ite_eq_left h0, pathSet_insert hc0 h0, prod_insert hnot,
      (mem_children.mp hc0).2]
  · rw [pi_of_not h]
    exact (sum_eq_zero fun c hc => by
      rw [pi_of_not fun h' => h (isAnc_of_mem_children hc h'), mul_zero]).symm

omit [Fintype V] in
theorem pi_leaf (hlc : H.LeafChildless) (v w : V) :
    H.pi cap (H.leaf v) w = if w = v then 1 else 0 := by
  by_cases hw : w = v
  · subst hw
    have hempty : H.pathSet (H.leaf w) w = ∅ := by
      ext y
      simp only [pathSet, mem_filter, mem_univ, true_and, Finset.notMem_empty, iff_false]
      rintro ⟨h1, h2, h3⟩
      exact h2 (RootedTree.isAnc_antisymm h3 h1)
    simp [pi, hempty, RootedTree.isAnc_refl]
  · rw [ite_eq_right hw, pi_of_not]
    intro h
    have hne : H.leaf v ≠ H.leaf w := fun he => hw (H.leaf_inj he).symm
    obtain ⟨c, hc, -⟩ := exists_child (H := H) h hne
    rw [hlc v] at hc
    exact Finset.notMem_empty c hc

omit [Fintype V] [DecidableEq V] in
theorem pmass_rec {x : N} (hx : ¬ H.IsLeaf x) (S : Finset V) :
    H.pmass cap S x = ∑ c ∈ H.children x, cap c / H.W cap x * H.pmass cap S c := by
  unfold pmass
  simp only [pi_rec hx, mul_sum]
  exact sum_comm

omit [Fintype V] in
theorem pmass_leaf (hlc : H.LeafChildless) (S : Finset V) (v : V) :
    H.pmass cap S (H.leaf v) = ind S v := by
  simp [pmass, pi_leaf hlc, ind]

omit [Fintype V] [DecidableEq V] in
theorem pmass_nonneg (hcap : ∀ x, 0 ≤ cap x) (S : Finset V) (x : N) : 0 ≤ H.pmass cap S x :=
  sum_nonneg fun v _ => pi_nonneg hcap x v

theorem pmass_add_compl (S : Finset V) (x : N) :
    H.pmass cap S x + H.pmass cap Sᶜ x = H.pmass cap univ x :=
  sum_add_sum_compl S _

theorem pmass_univ_le_one (hcap : ∀ x, 0 ≤ cap x) (hlc : H.LeafChildless) (x : N) :
    H.pmass cap univ x ≤ 1 := by
  induction x using H.induction_up with
  | h x ih =>
    by_cases hx : H.IsLeaf x
    · obtain ⟨v, rfl⟩ := hx
      rw [pmass_leaf hlc]; simp [ind]
    · rw [pmass_rec hx]
      calc ∑ c ∈ H.children x, cap c / H.W cap x * H.pmass cap univ c
          ≤ ∑ c ∈ H.children x, cap c / H.W cap x * 1 :=
            sum_le_sum fun c hc => mul_le_mul_of_nonneg_left (ih c hc)
              (div_nonneg (hcap c) (W_nonneg hcap x))
        _ ≤ 1 := by simpa using sum_ratio_le_one x

theorem pmass_le_one (hcap : ∀ x, 0 ≤ cap x) (hlc : H.LeafChildless) (S : Finset V) (x : N) :
    H.pmass cap S x ≤ 1 := by
  have := pmass_add_compl (H := H) (cap := cap) S x
  have := pmass_nonneg (H := H) hcap Sᶜ x
  have := pmass_univ_le_one hcap hlc x
  linarith

/-- With subadditive capacities, every node of positive capacity carries a full unit. -/
theorem pmass_univ_eq_one (hcap : ∀ x, 0 ≤ cap x) (hlc : H.LeafChildless) (hsub : H.Subadd cap)
    (x : N) : (H.IsLeaf x ∨ 0 < H.W cap x) → H.pmass cap univ x = 1 := by
  induction x using H.induction_up with
  | h x ih =>
    rintro (hx | hW)
    · obtain ⟨v, rfl⟩ := hx
      rw [pmass_leaf hlc]; simp [ind]
    · by_cases hx : H.IsLeaf x
      · obtain ⟨v, rfl⟩ := hx
        rw [pmass_leaf hlc]; simp [ind]
      rw [pmass_rec hx]
      calc ∑ c ∈ H.children x, cap c / H.W cap x * H.pmass cap univ c
          = ∑ c ∈ H.children x, cap c / H.W cap x := by
            refine sum_congr rfl fun c hc => ?_
            rcases (hcap c).lt_or_eq with hpos | hzero
            · have hce : c ∈ H.edges := (mem_filter.mp hc).1
              have : H.IsLeaf c ∨ 0 < H.W cap c := by
                by_cases hl : H.IsLeaf c
                · exact Or.inl hl
                · exact Or.inr (lt_of_lt_of_le hpos (hsub c hce hl))
              rw [ih c hc this, mul_one]
            · rw [← hzero]; simp
        _ = 1 := sum_ratio_eq_one hW.ne'

theorem pmass_univ_eq_one_of_pos (hcap : ∀ x, 0 ≤ cap x) (hlc : H.LeafChildless)
    (hsub : H.Subadd cap) {c : N} (hc : c ∈ H.edges) (hpos : 0 < cap c) :
    H.pmass cap univ c = 1 := by
  refine pmass_univ_eq_one hcap hlc hsub c ?_
  by_cases hl : H.IsLeaf c
  · exact Or.inl hl
  · exact Or.inr (lt_of_lt_of_le hpos (hsub c hc hl))

/-! ### The guard graph -/

variable (H cap) in
/-- Weights of the star-mesh guard graph. -/
noncomputable def guardW (v w : V) : ℝ :=
  ∑ u, ∑ c ∈ H.children u, ∑ c' ∈ H.children u, H.kw cap u c c' * (H.pi cap c v * H.pi cap c' w)

variable (H) in
/-- **The star-mesh guard graph.** -/
noncomputable def guardGraph (hcap : ∀ x, 0 ≤ cap x) : WeightedGraph V where
  w := H.guardW cap
  symm v w := by
    unfold guardW
    refine sum_congr rfl fun u _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun c _ => sum_congr rfl fun c' _ => ?_
    rw [kw_symm]; ring
  nonneg v w := sum_nonneg fun u _ => sum_nonneg fun c _ => sum_nonneg fun c' _ =>
    mul_nonneg (kw_nonneg hcap u c c') (mul_nonneg (pi_nonneg hcap c v) (pi_nonneg hcap c' w))
  diag v := by
    refine sum_eq_zero fun u _ => sum_eq_zero fun c hc => sum_eq_zero fun c' hc' => ?_
    by_cases hcc : c = c'
    · simp [kw, hcc]
    · by_cases h1 : H.pi cap c v = 0
      · simp [h1]
      · have h2 : H.pi cap c' v = 0 := by
          by_contra h2
          exact hcc (child_unique hc hc' (isAnc_of_pi_ne h1) (isAnc_of_pi_ne h2))
        simp [h2]

theorem guardGraph_cut (hcap : ∀ x, 0 ≤ cap x) (S : Finset V) :
    (H.guardGraph hcap).cut S = ∑ u, ∑ c ∈ H.children u, ∑ c' ∈ H.children u,
      H.kw cap u c c' * (H.pmass cap S c * H.pmass cap Sᶜ c') := by
  have hR : ∀ u, ∀ c c' : N, H.kw cap u c c' * (H.pmass cap S c * H.pmass cap Sᶜ c') =
      ∑ v ∈ S, ∑ w ∈ Sᶜ, H.kw cap u c c' * (H.pi cap c v * H.pi cap c' w) := by
    intro u c c'
    rw [pmass, pmass, sum_mul_sum, mul_sum]
    exact sum_congr rfl fun v _ => by rw [mul_sum]
  simp only [hR]
  change ∑ v ∈ S, ∑ w ∈ Sᶜ, H.guardW cap v w = _
  unfold guardW
  rw [sum_swap21 S Sᶜ univ]
  exact sum_congr rfl fun u _ => sum_swap22 S Sᶜ (H.children u) (H.children u) _

/-! ### Lower bound -/

theorem abs_sub_le_cross {p p' q q' : ℝ} (hp : 0 ≤ p) (hp' : 0 ≤ p') (hq : 0 ≤ q) (hq' : 0 ≤ q')
    (h1 : p + q = 1) (h2 : p' + q' = 1) : |p - p'| ≤ p * q' + p' * q := by
  rw [abs_le]
  constructor <;> nlinarith

theorem star_lower (hcap : ∀ x, 0 ≤ cap x) (hlc : H.LeafChildless) (hsub : H.Subadd cap)
    (S : Finset V) (u : N) :
    ∑ c ∈ H.children u, cap c * |H.pmass cap S c - H.pmass cap S u| ≤
      2 * ∑ c ∈ H.children u, ∑ c' ∈ H.children u,
        H.kw cap u c c' * (H.pmass cap S c * H.pmass cap Sᶜ c') := by
  set a := H.pmass cap S
  set b := H.pmass cap Sᶜ
  have hRnn : 0 ≤ ∑ c ∈ H.children u, ∑ c' ∈ H.children u, H.kw cap u c c' * (a c * b c') :=
    sum_nonneg fun c _ => sum_nonneg fun c' _ => mul_nonneg (kw_nonneg hcap u c c')
      (mul_nonneg (pmass_nonneg hcap S c) (pmass_nonneg hcap Sᶜ c'))
  by_cases hl : H.IsLeaf u
  · obtain ⟨v, rfl⟩ := hl
    rw [hlc v]; simp
  by_cases hW : H.W cap u = 0
  · have hz : ∀ c ∈ H.children u, cap c = 0 :=
      (sum_eq_zero_iff_of_nonneg fun c _ => hcap c).mp hW
    rw [sum_eq_zero fun c hc => by rw [hz c hc, zero_mul]]
    linarith
  have hWpos : 0 < H.W cap u := lt_of_le_of_ne (W_nonneg hcap u) (Ne.symm hW)
  have hau : a u = ∑ c' ∈ H.children u, cap c' / H.W cap u * a c' := pmass_rec hl S
  have hone := sum_ratio_eq_one (H := H) hW
  -- each child against the average
  have hstep : ∀ c ∈ H.children u, cap c * |a c - a u| ≤
      ∑ c' ∈ H.children u, H.kw cap u c c' * (a c * b c' + a c' * b c) := by
    intro c hc
    have hdiff : a c - a u = ∑ c' ∈ H.children u, cap c' / H.W cap u * (a c - a c') := by
      rw [hau]
      simp only [mul_sub, sum_sub_distrib, ← sum_mul, hone, one_mul]
    rw [hdiff]
    calc cap c * |∑ c' ∈ H.children u, cap c' / H.W cap u * (a c - a c')|
        ≤ cap c * ∑ c' ∈ H.children u, |cap c' / H.W cap u * (a c - a c')| :=
          mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs _ _) (hcap c)
      _ = ∑ c' ∈ H.children u, cap c * cap c' / H.W cap u * |a c - a c'| := by
          rw [mul_sum]
          refine sum_congr rfl fun c' _ => ?_
          rw [abs_mul, abs_of_nonneg (div_nonneg (hcap c') hWpos.le)]
          ring
      _ ≤ _ := by
          refine sum_le_sum fun c' hc' => ?_
          by_cases hcc : c = c'
          · subst hcc; simp [kw]
          rw [show H.kw cap u c c' = cap c * cap c' / H.W cap u by simp [kw, hcc]]
          rcases (hcap c).lt_or_eq with hp | hp
          · rcases (hcap c').lt_or_eq with hp' | hp'
            · apply mul_le_mul_of_nonneg_left _ (div_nonneg (mul_nonneg (hcap c) (hcap c'))
                hWpos.le)
              have m1 := pmass_univ_eq_one_of_pos hcap hlc hsub (mem_filter.mp hc).1 hp
              have m2 := pmass_univ_eq_one_of_pos hcap hlc hsub (mem_filter.mp hc').1 hp'
              rw [← pmass_add_compl S] at m1 m2
              exact abs_sub_le_cross (pmass_nonneg hcap S c) (pmass_nonneg hcap S c')
                (pmass_nonneg hcap Sᶜ c) (pmass_nonneg hcap Sᶜ c') m1 m2
            · rw [← hp']; simp
          · rw [← hp]; simp
  calc ∑ c ∈ H.children u, cap c * |a c - a u|
      ≤ ∑ c ∈ H.children u, ∑ c' ∈ H.children u, H.kw cap u c c' * (a c * b c' + a c' * b c) :=
        sum_le_sum hstep
    _ = ∑ c ∈ H.children u, ∑ c' ∈ H.children u, H.kw cap u c c' * (a c * b c') +
        ∑ c ∈ H.children u, ∑ c' ∈ H.children u, H.kw cap u c c' * (a c' * b c) := by
        rw [← sum_add_distrib]
        exact sum_congr rfl fun c _ => by rw [← sum_add_distrib]; simp only [mul_add]
    _ = 2 * ∑ c ∈ H.children u, ∑ c' ∈ H.children u, H.kw cap u c c' * (a c * b c') := by
        have : ∑ c ∈ H.children u, ∑ c' ∈ H.children u, H.kw cap u c c' * (a c' * b c) =
            ∑ c ∈ H.children u, ∑ c' ∈ H.children u, H.kw cap u c c' * (a c * b c') := by
          rw [sum_comm]
          exact sum_congr rfl fun c _ => sum_congr rfl fun c' _ => by rw [kw_symm]
        rw [this]; ring

/-- **Lower bound.** The labelling by masses extends `S` and costs at most `2 c_J(S)`. -/
theorem guard_lower (hcap : ∀ x, 0 ≤ cap x) (hlc : H.LeafChildless) (hsub : H.Subadd cap)
    (S : Finset V) :
    H.ExtendsR S (H.pmass cap S) ∧
      H.labelCost cap (H.pmass cap S) ≤ 2 * (H.guardGraph hcap).cut S := by
  refine ⟨fun v => pmass_leaf hlc S v, ?_⟩
  rw [guardGraph_cut, mul_sum, labelCost, sum_edges_eq_sum_children]
  refine sum_le_sum fun u _ => ?_
  calc ∑ c ∈ H.children u, cap c * |H.pmass cap S c - H.pmass cap S (H.T.parent c)|
      = ∑ c ∈ H.children u, cap c * |H.pmass cap S c - H.pmass cap S u| :=
        sum_congr rfl fun c hc => by rw [(mem_children.mp hc).2]
    _ ≤ _ := star_lower hcap hlc hsub S u

/-! ### Upper bound -/

section Upper

variable (S : Finset V) (ℓ : N → Bool)

variable (H cap) in
/-- Mass of `x` disagreeing with the label `t`. -/
noncomputable def dis (x : N) (t : Bool) : ℝ := if t then H.pmass cap Sᶜ x else H.pmass cap S x

variable (H cap) in
/-- Cost of the label change on the edge above `y`. -/
noncomputable def fchg (y : N) : ℝ := cap y * |toReal ℓ y - toReal ℓ (H.T.parent y)|

variable (H cap) in
/-- Label-change cost strictly below `x`. -/
noncomputable def below (x : N) : ℝ :=
  ∑ y ∈ H.edges, if H.T.IsAnc x y ∧ x ≠ y then H.fchg cap ℓ y else 0

variable (H cap) in
/-- Capacity-weighted disagreement of the children of `x` with the label of `x`. -/
noncomputable def disagree (x : N) : ℝ := ∑ c ∈ H.children x, cap c * H.dis cap S c (ℓ x)

variable {S ℓ}

theorem dis_nonneg (hcap : ∀ x, 0 ≤ cap x) (x : N) (t : Bool) : 0 ≤ H.dis cap S x t := by
  unfold dis; split_ifs <;> exact pmass_nonneg hcap _ x

theorem dis_le_one (hcap : ∀ x, 0 ≤ cap x) (hlc : H.LeafChildless) (x : N) (t : Bool) :
    H.dis cap S x t ≤ 1 := by
  unfold dis; split_ifs <;> exact pmass_le_one hcap hlc _ x

omit [Fintype V] [DecidableEq V] [Fintype N] [DecidableEq N] in
theorem fchg_nonneg (hcap : ∀ x, 0 ≤ cap x) (y : N) : 0 ≤ H.fchg cap ℓ y :=
  mul_nonneg (hcap y) (abs_nonneg _)

theorem dis_rec {x : N} (hx : ¬ H.IsLeaf x) (t : Bool) :
    H.dis cap S x t = ∑ c ∈ H.children x, cap c / H.W cap x * H.dis cap S c t := by
  unfold dis
  cases t <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> exact pmass_rec hx _

theorem disagree_nonneg (hcap : ∀ x, 0 ≤ cap x) (x : N) : 0 ≤ H.disagree cap S ℓ x :=
  sum_nonneg fun c _ => mul_nonneg (hcap c) (dis_nonneg hcap c _)

/-- The star at `u` costs at most the disagreement of its children with `ℓ u`. -/
theorem star_upper (hcap : ∀ x, 0 ≤ cap x) (hlc : H.LeafChildless) (u : N) :
    ∑ c ∈ H.children u, ∑ c' ∈ H.children u,
        H.kw cap u c c' * (H.pmass cap S c * H.pmass cap Sᶜ c') ≤ H.disagree cap S ℓ u := by
  have hr := sum_ratio_le_one (H := H) (cap := cap) u
  have hW := W_nonneg (H := H) hcap u
  unfold disagree dis
  cases ℓ u
  · simp only [Bool.false_eq_true, ite_false]
    calc _ ≤ ∑ c ∈ H.children u, ∑ c' ∈ H.children u,
            cap c * H.pmass cap S c * (cap c' / H.W cap u) := by
          refine sum_le_sum fun c _ => sum_le_sum fun c' _ => ?_
          calc H.kw cap u c c' * (H.pmass cap S c * H.pmass cap Sᶜ c')
              ≤ cap c * cap c' / H.W cap u * (H.pmass cap S c * 1) := by
                apply mul_le_mul (kw_le hcap u c c') _ (mul_nonneg (pmass_nonneg hcap _ _)
                  (pmass_nonneg hcap _ _)) (div_nonneg (mul_nonneg (hcap c) (hcap c')) hW)
                exact mul_le_mul_of_nonneg_left (pmass_le_one hcap hlc _ _)
                  (pmass_nonneg hcap _ _)
            _ = _ := by ring
      _ = ∑ c ∈ H.children u, cap c * H.pmass cap S c *
            ∑ c' ∈ H.children u, cap c' / H.W cap u :=
          sum_congr rfl fun c _ => (mul_sum _ _ _).symm
      _ ≤ _ := sum_le_sum fun c _ => by
          have := mul_le_mul_of_nonneg_left hr
            (mul_nonneg (hcap c) (pmass_nonneg (H := H) hcap S c))
          linarith
  · simp only [ite_true]
    calc _ ≤ ∑ c ∈ H.children u, ∑ c' ∈ H.children u,
            cap c' * H.pmass cap Sᶜ c' * (cap c / H.W cap u) := by
          refine sum_le_sum fun c _ => sum_le_sum fun c' _ => ?_
          calc H.kw cap u c c' * (H.pmass cap S c * H.pmass cap Sᶜ c')
              ≤ cap c * cap c' / H.W cap u * (1 * H.pmass cap Sᶜ c') := by
                apply mul_le_mul (kw_le hcap u c c') _ (mul_nonneg (pmass_nonneg hcap _ _)
                  (pmass_nonneg hcap _ _)) (div_nonneg (mul_nonneg (hcap c) (hcap c')) hW)
                exact mul_le_mul_of_nonneg_right (pmass_le_one hcap hlc _ _)
                  (pmass_nonneg hcap _ _)
            _ = _ := by ring
      _ = ∑ c' ∈ H.children u, cap c' * H.pmass cap Sᶜ c' *
            ∑ c ∈ H.children u, cap c / H.W cap u := by
          rw [sum_comm]
          exact sum_congr rfl fun c' _ => (mul_sum _ _ _).symm
      _ ≤ _ := sum_le_sum fun c _ => by
          have := mul_le_mul_of_nonneg_left hr
            (mul_nonneg (hcap c) (pmass_nonneg (H := H) hcap Sᶜ c))
          linarith

/-- Disagreement with the parent's label: own disagreement plus the edge's change. -/
theorem dis_step (hcap : ∀ x, 0 ≤ cap x) (hlc : H.LeafChildless) {x c : N}
    (hc : c ∈ H.children x) :
    cap c * H.dis cap S c (ℓ x) ≤ H.fchg cap ℓ c + cap c * H.dis cap S c (ℓ c) := by
  have hp := (mem_children.mp hc).2
  by_cases he : ℓ c = ℓ x
  · rw [he]; linarith [fchg_nonneg (H := H) (ℓ := ℓ) hcap c]
  · have hf : H.fchg cap ℓ c = cap c := by
      unfold fchg toReal; rw [hp]
      cases hc' : ℓ c <;> cases hx' : ℓ x <;> simp_all
    rw [hf]
    have := mul_le_mul_of_nonneg_left (dis_le_one (S := S) hcap hlc c (ℓ x)) (hcap c)
    have := mul_nonneg (hcap c) (dis_nonneg (H := H) (S := S) hcap c (ℓ c))
    linarith

/-- A node's own disagreement is at most that of its children (subadditivity). -/
theorem own_le_disagree (hcap : ∀ x, 0 ≤ cap x) (hlc : H.LeafChildless) (hsub : H.Subadd cap)
    (hℓ : H.Extends S ℓ) {c : N} (hc : c ∈ H.edges) :
    cap c * H.dis cap S c (ℓ c) ≤ H.disagree cap S ℓ c := by
  by_cases hl : H.IsLeaf c
  · obtain ⟨v, rfl⟩ := hl
    have : H.dis cap S (H.leaf v) (ℓ (H.leaf v)) = 0 := by
      unfold dis
      rw [hℓ v, pmass_leaf hlc, pmass_leaf hlc]
      by_cases hv : v ∈ S <;> simp [hv, ind]
    rw [this, mul_zero]
    exact disagree_nonneg hcap _
  · rw [dis_rec hl, mul_sum]
    refine sum_le_sum fun c' _ => ?_
    have hle : cap c * (cap c' / H.W cap c) ≤ cap c' := by
      by_cases hW : H.W cap c = 0
      · rw [hW, div_zero, mul_zero]; exact hcap c'
      · have hWpos : 0 < H.W cap c := lt_of_le_of_ne (W_nonneg hcap c) (Ne.symm hW)
        rw [mul_div_assoc', div_le_iff₀ hWpos]
        exact mul_le_mul_of_nonneg_right (hsub c hc hl) (hcap c') |>.trans_eq (mul_comm _ _)
    calc cap c * (cap c' / H.W cap c * H.dis cap S c' (ℓ c))
        = cap c * (cap c' / H.W cap c) * H.dis cap S c' (ℓ c) := by ring
      _ ≤ cap c' * H.dis cap S c' (ℓ c) :=
          mul_le_mul_of_nonneg_right hle (dis_nonneg hcap c' _)

omit [Fintype V] [DecidableEq V] in
theorem below_child (hcap : ∀ x, 0 ≤ cap x) (x : N) :
    ∑ c ∈ H.children x, (H.fchg cap ℓ c + H.below cap ℓ c) ≤ H.below cap ℓ x := by
  have hincl : ∀ c ∈ H.children x, H.fchg cap ℓ c + H.below cap ℓ c =
      ∑ y ∈ H.edges, if H.T.IsAnc c y then H.fchg cap ℓ y else 0 := by
    intro c hc
    have hce : c ∈ H.edges := (mem_filter.mp hc).1
    have h1 : (∑ y ∈ H.edges, if c = y then H.fchg cap ℓ y else 0) = H.fchg cap ℓ c := by
      simp [hce]
    rw [below, ← h1, ← sum_add_distrib]
    refine sum_congr rfl fun y _ => ?_
    by_cases hcy : c = y
    · subst hcy; simp [RootedTree.isAnc_refl]
    · simp [hcy]
  rw [sum_congr rfl hincl, sum_comm, below]
  refine sum_le_sum fun y _ => ?_
  by_cases h : ∃ c0 ∈ H.children x, H.T.IsAnc c0 y
  · obtain ⟨c0, hc0, h0⟩ := h
    rw [sum_eq_single c0 (fun c hc hne => ite_eq_right fun h' => hne (child_unique hc hc0 h' h0))
      (fun h' => absurd hc0 h'), ite_eq_left h0,
      ite_eq_left ⟨isAnc_of_mem_children hc0 h0, ne_of_mem_children hc0 h0⟩]
  · push Not at h
    rw [sum_eq_zero fun c hc => ite_eq_right (h c hc)]
    split_ifs
    · exact fchg_nonneg hcap y
    · exact le_rfl

theorem disagree_le_below (hcap : ∀ x, 0 ≤ cap x) (hlc : H.LeafChildless) (hsub : H.Subadd cap)
    (hℓ : H.Extends S ℓ) (x : N) : H.disagree cap S ℓ x ≤ H.below cap ℓ x := by
  induction x using H.induction_up with
  | h x ih =>
    calc H.disagree cap S ℓ x
        ≤ ∑ c ∈ H.children x, (H.fchg cap ℓ c + cap c * H.dis cap S c (ℓ c)) :=
          sum_le_sum fun c hc => dis_step hcap hlc hc
      _ ≤ ∑ c ∈ H.children x, (H.fchg cap ℓ c + H.below cap ℓ c) := by
          refine sum_le_sum fun c hc => ?_
          have h1 := own_le_disagree hcap hlc hsub hℓ (mem_filter.mp hc).1
          have h2 := ih c hc
          linarith
      _ ≤ H.below cap ℓ x := below_child hcap x

/-- **Upper bound.** With subadditive capacities, `c_J(S) ≤ D · cost(ℓ)` for every binary
extension `ℓ` of `S`, where `D` is the height of the tree. -/
theorem guard_upper (hcap : ∀ x, 0 ≤ cap x) (hlc : H.LeafChildless) (hsub : H.Subadd cap)
    (hℓ : H.Extends S ℓ) :
    (H.guardGraph hcap).cut S ≤
      (univ.sup H.T.depth : ℕ) * H.labelCost cap (toReal ℓ) := by
  set D := univ.sup H.T.depth
  rw [guardGraph_cut]
  calc _ ≤ ∑ u, H.below cap ℓ u := sum_le_sum fun u _ =>
        (star_upper hcap hlc u).trans (disagree_le_below hcap hlc hsub hℓ u)
    _ = ∑ y ∈ H.edges, ((univ.filter fun u => H.T.IsAnc u y ∧ u ≠ y).card : ℝ) *
          H.fchg cap ℓ y := by
        unfold below
        rw [sum_comm]
        refine sum_congr rfl fun y _ => ?_
        rw [← sum_filter, sum_const, nsmul_eq_mul]
    _ ≤ ∑ y ∈ H.edges, (D : ℝ) * H.fchg cap ℓ y := by
        refine sum_le_sum fun y _ => mul_le_mul_of_nonneg_right ?_ (fchg_nonneg hcap y)
        exact_mod_cast (card_strictAnc_le y).trans (le_sup (f := H.T.depth) (mem_univ y))
    _ = _ := by rw [← mul_sum]; rfl

end Upper

/-- **Lemma 19 for bounded height.** If leaf nodes have no children, twice the
star-mesh graph is a guard of quality `2D`, where `D` is the height of the tree. -/
theorem guardFor_of_leafChildless (hlc : H.LeafChildless) {ρ : ℝ}
    (hρ : 2 * (univ.sup H.T.depth : ℕ) ≤ ρ) : H.GuardFor ρ := by
  intro cap hcap hsub
  refine ⟨(H.guardGraph hcap).scale 2 (by norm_num), fun S => ⟨?_, ?_⟩⟩
  · obtain ⟨hext, hle⟩ := guard_lower hcap hlc hsub S
    exact ⟨_, hext, by rw [cut_scale]; exact hle⟩
  · obtain ⟨ℓ, hℓ, hR⟩ := H.exists_rep_eq cap S
    rw [cut_scale, hR]
    have h := guard_upper hcap hlc hsub hℓ
    have h0 := H.labelCost_nonneg hcap (toReal ℓ)
    nlinarith

variable [LinearOrder N]

/-- **Theorem 15 for hierarchies whose leaf nodes are childless.** If some minimum cut
has representation cost at most `B λ`, the skeleton program with the star-mesh guard
(`ρ = max 1 (2D)`, `D` the height) outputs a weak skeleton, using
`|edges| (1 + 4 (q − 1)(⌊log₂ n⌋ + 3))` queries for `q = ⌈200 ρ² B²⌉`. -/
theorem supplied_weakSkeleton_of_leafChildless (G : WeightedGraph V)
    (hn : 2 ≤ Fintype.card V) (hlc : H.LeafChildless) {B : ℝ} (hB : 1 ≤ B)
    (hlam : 0 < mincutValue G)
    (hprom : ∃ S, IsMinCut G S ∧ H.rep (H.canon G) S ≤ B * mincutValue G) :
    let ρ : ℝ := max 1 (2 * (univ.sup H.T.depth : ℕ))
    let hg : H.GuardFor ρ := guardFor_of_leafChildless hlc (le_max_right _ _)
    let q := ⌈200 * ρ ^ 2 * B ^ 2⌉₊
    IsWeakSkeleton G ((H.supplied hg (1 / (10 * ρ * B))
        (div_nonneg zero_le_one (by positivity)) q).eval G.cut) ∧
      (H.supplied hg (1 / (10 * ρ * B)) (div_nonneg zero_le_one (by positivity)) q).cost G.cut ≤
        H.edges.card * (1 + 4 * ((q - 1) * (Nat.log 2 (Fintype.card V) + 3))) :=
  supplied_weakSkeleton G hn (le_max_left _ _) hB _ hlam hprom

end Hier
end Hierarchy
end CutQueryComplexity
