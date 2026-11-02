import CutQueryComplexity.CanonicalST.Witness.Count
import CutQueryComplexity.Graph.EdgeSum

/-!
# Exact padding loss and witness marginals

The conditional calculation counts missing padding pairs in each actual
shore fiber. The marginal estimate then uses the finite padded-witness
distribution, retaining all multiplicities. Adding a learned edge filters
this same witness family and never changes the fixed shore representatives.
-/

set_option autoImplicit false

namespace CutQueryComplexity.CanonicalST.Witness

open Finset WeightedGraph
open scoped Classical
noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V]

theorem padding_missing_card {α : Type*} [DecidableEq α] (U K : Finset α) (b : ℕ)
    (hKU : K ⊆ U) (hKb : K.card ≤ b) {e : α} (heU : e ∈ U) (heK : e ∉ K) :
    ((U.powersetCard b).filter fun Y => K ⊆ Y ∧ e ∉ Y).card =
      (U.card - K.card - 1).choose (b - K.card) := by
  have hKe : K ⊆ U.erase e := by
    intro x hx
    exact mem_erase.mpr ⟨fun h => heK (h ▸ hx), hKU hx⟩
  have he : (U.powersetCard b).filter (fun Y => K ⊆ Y ∧ e ∉ Y) =
      ((U.erase e).powersetCard b).filter (K ⊆ ·) := by
    ext Y
    simp only [mem_filter, mem_powersetCard]
    constructor
    · rintro ⟨⟨hYU, hcard⟩, hKY, hnot⟩
      refine ⟨⟨?_, hcard⟩, hKY⟩
      intro x hx
      exact mem_erase.mpr ⟨fun h => hnot (h ▸ hx), hYU hx⟩
    · rintro ⟨⟨hYU, hcard⟩, hKY⟩
      refine ⟨⟨hYU.trans (erase_subset _ _), hcard⟩, hKY, ?_⟩
      intro heY
      exact (mem_erase.mp (hYU heY)).1 rfl
  rw [he, card_filter_powersetCard_subset K (U.erase e) b hKe hKb,
    card_erase_of_mem heU]
  congr 1
  omega

/-- Cross-multiplied hypergeometric exclusion probability, proved by the
binomial coefficient identity rather than a probabilistic assumption. -/
theorem padding_missing_mul {α : Type*} [DecidableEq α] (U K : Finset α) (b : ℕ)
    (hKU : K ⊆ U) (hKb : K.card ≤ b) {e : α} (heU : e ∈ U) (heK : e ∉ K) :
    (U.card - K.card) * ((U.powersetCard b).filter fun Y => K ⊆ Y ∧ e ∉ Y).card =
      (U.card - b) * ((U.powersetCard b).filter (K ⊆ ·)).card := by
  have hlt : K.card < U.card := by
    apply card_lt_card
    refine Finset.ssubset_iff_subset_ne.mpr ⟨hKU, ?_⟩
    intro he
    exact heK (he.symm ▸ heU)
  rw [padding_missing_card U K b hKU hKb heU heK,
    card_filter_powersetCard_subset K U b hKU hKb]
  have h₁ : U.card - K.card - 1 + 1 = U.card - K.card := by omega
  have h₂ : U.card - K.card - (b - K.card) = U.card - b := by omega
  have hc := Nat.choose_mul_succ_eq (U.card - K.card - 1) (b - K.card)
  rw [h₁, h₂] at hc
  simpa only [mul_comm] using hc

theorem phase_loss_ratio {M h f k : ℕ} (hk : 1 ≤ k) (hkf : k ≤ f)
    (hfM : f ≤ M) (hlower : f - k ≤ h) (hupper : h ≤ f - k / 2 - 1) :
    (k / 2 + 1) * (M - h) ≤ k * (M - (f - k / 2 - 1)) := by
  have hc : k / 2 + 1 ≤ k := by omega
  have hfh : f - h ≤ k := by omega
  have hsplit : M - h = (M - f) + (f - h) := by omega
  have hbudget : M - (f - k / 2 - 1) = (M - f) + (k / 2 + 1) := by omega
  rw [hsplit, hbudget, Nat.mul_add, Nat.mul_add]
  calc
    (k / 2 + 1) * (M - f) + (k / 2 + 1) * (f - h) ≤
        k * (M - f) + (k / 2 + 1) * k :=
      Nat.add_le_add (Nat.mul_le_mul_right _ hc) (Nat.mul_le_mul_left _ hfh)
    _ = k * (M - f) + k * (k / 2 + 1) := by rw [Nat.mul_comm (k / 2 + 1) k]

/-- For a separated shore, at least (floor(k/2)+1)/k of its padding
sets omit the unknown pair. This is the exact conditional counting step. -/
theorem phase_padding_missing {α : Type*} [DecidableEq α] (U K : Finset α)
    {f k : ℕ} (hKU : K ⊆ U) (hk : 1 ≤ k) (hkf : k ≤ f)
    (hfU : f ≤ U.card) (hlower : f - k ≤ K.card)
    (hupper : K.card ≤ f - k / 2 - 1) {e : α} (heU : e ∈ U) (heK : e ∉ K) :
    (k / 2 + 1) * ((U.powersetCard (f - k / 2 - 1)).filter (K ⊆ ·)).card ≤
      k * ((U.powersetCard (f - k / 2 - 1)).filter fun Y => K ⊆ Y ∧ e ∉ Y).card := by
  let total : ℕ := ((U.powersetCard (f - k / 2 - 1)).filter (K ⊆ ·)).card
  let missing : ℕ :=
    ((U.powersetCard (f - k / 2 - 1)).filter fun Y => K ⊆ Y ∧ e ∉ Y).card
  have hm : (U.card - K.card) * missing = (U.card - (f - k / 2 - 1)) * total :=
    padding_missing_mul U K (f - k / 2 - 1) hKU hupper heU heK
  have hr := phase_loss_ratio hk hkf hfU hlower hupper
  have hp := Nat.mul_le_mul_right total hr
  have hlt : K.card < U.card := by
    apply card_lt_card
    refine Finset.ssubset_iff_subset_ne.mpr ⟨hKU, ?_⟩
    intro he
    exact heK (he.symm ▸ heU)
  have hpositive : 0 < U.card - K.card := by omega
  change (k / 2 + 1) * total ≤ k * missing
  refine Nat.le_of_mul_le_mul_left ?_ hpositive
  calc
    (U.card - K.card) * ((k / 2 + 1) * total) =
        ((k / 2 + 1) * (U.card - K.card)) * total := by ac_rfl
    _ ≤ (k * (U.card - (f - k / 2 - 1))) * total := hp
    _ = k * ((U.card - (f - k / 2 - 1)) * total) := by ac_rfl
    _ = k * ((U.card - K.card) * missing) := by rw [← hm]
    _ = (U.card - K.card) * (k * missing) := by ac_rfl

def Separates (u v : V) (S : Finset V) : Prop :=
  (u ∈ S ∧ v ∉ S) ∨ (v ∈ S ∧ u ∉ S)

def separatedWitnesses (A : Finset (Finset V)) (H : WeightedGraph V)
    (b : ℕ) (u v : V) : Finset (Finset V × Finset (V × V)) :=
  (paddedWitnesses A H b).filter fun w => Separates u v w.1

theorem marginal_count_difference (W : Finset (Finset V × Finset (V × V))) (u v : V) :
    |((W.filter fun w => u ∈ w.1).card : ℚ) -
      ((W.filter fun w => v ∈ w.1).card : ℚ)| ≤
      ((W.filter fun w => Separates u v w.1).card : ℚ) := by
  have hcast (z : V) : ((W.filter fun w => z ∈ w.1).card : ℚ) =
      ∑ w ∈ W, if z ∈ w.1 then (1 : ℚ) else 0 := by
    simp only [card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [hcast u, hcast v, ← sum_sub_distrib]
  calc
    |∑ w ∈ W, ((if u ∈ w.1 then (1 : ℚ) else 0) -
        (if v ∈ w.1 then (1 : ℚ) else 0))| ≤
        ∑ w ∈ W, |(if u ∈ w.1 then (1 : ℚ) else 0) -
          (if v ∈ w.1 then (1 : ℚ) else 0)| := abs_sum_le_sum_abs _ _
    _ = ∑ w ∈ W, if Separates u v w.1 then (1 : ℚ) else 0 := by
      apply sum_congr rfl
      intro w _
      by_cases hu : u ∈ w.1 <;> by_cases hv : v ∈ w.1 <;> simp [Separates, hu, hv]
    _ = _ := by
      simp only [card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

/-- Jensen's separation inequality for the actual finite witness distribution. -/
theorem potential_separation (A : Finset (Finset V)) (H : WeightedGraph V) (b : ℕ)
    (u v : V) (hne : (paddedWitnesses A H b).Nonempty) :
    |potential A H b u - potential A H b v| * (paddedWitnesses A H b).card ≤
      (separatedWitnesses A H b u v).card := by
  let W := paddedWitnesses A H b
  have hpos : (0 : ℚ) < W.card := by exact_mod_cast (card_pos.mpr hne)
  have hmul (z : V) : potential A H b z * W.card =
      ((W.filter fun w => z ∈ w.1).card : ℚ) := by
    exact div_mul_cancel₀ _ hpos.ne'
  calc
    |potential A H b u - potential A H b v| * W.card =
        |(potential A H b u - potential A H b v) * W.card| := by
          rw [abs_mul, abs_of_pos hpos]
    _ = |((W.filter fun w => u ∈ w.1).card : ℚ) -
        ((W.filter fun w => v ∈ w.1).card : ℚ)| := by rw [sub_mul, hmul u, hmul v]
    _ ≤ ((W.filter fun w => Separates u v w.1).card : ℚ) := marginal_count_difference W u v

def addEdge (H : WeightedGraph V) (e : EdgeIndex V) : WeightedGraph V :=
  H.add (edgeGraph e 1 (by norm_num))

theorem edgeGraph_one_w (e : EdgeIndex V) (u v : V) :
    (edgeGraph e 1 (by norm_num)).w u v =
      if (u, v) = e.val ∨ (v, u) = e.val then 1 else 0 := by
  have hn : ¬ ((u, v) = e.val ∧ (v, u) = e.val) := by
    rintro ⟨h₁, h₂⟩
    apply e.property
    exact (congrArg Prod.fst h₁).symm.trans (congrArg Prod.snd h₂)
  by_cases h₁ : (u, v) = e.val <;> by_cases h₂ : (v, u) = e.val <;>
    simp_all [edgeGraph]

theorem addEdge_positive (H : WeightedGraph V) (e : EdgeIndex V) (x y : V) :
    0 < (addEdge H e).w x y ↔ 0 < H.w x y ∨ (x, y) = e.val ∨ (y, x) = e.val := by
  change 0 < H.w x y + (edgeGraph e 1 (by norm_num)).w x y ↔ _
  rw [edgeGraph_one_w]
  by_cases hm : (x, y) = e.val ∨ (y, x) = e.val
  · rw [ite_eq_left hm]
    constructor
    · intro _
      exact Or.inr hm
    · intro _
      linarith [H.nonneg x y]
  · rw [ite_eq_right hm, _root_.add_zero]
    exact ⟨Or.inl, fun h => h.resolve_right hm⟩

def KilledBy (e : EdgeIndex V) (w : Finset V × Finset (V × V)) : Prop :=
  (e.val.1 ∈ w.1 ∧ e.val.2 ∉ w.1 ∧ e.val ∉ w.2) ∨
    (e.val.2 ∈ w.1 ∧ e.val.1 ∉ w.1 ∧ (e.val.2, e.val.1) ∉ w.2)

theorem paddedWitnesses_addEdge (A : Finset (Finset V)) (H : WeightedGraph V)
    (b : ℕ) (e : EdgeIndex V) :
    paddedWitnesses A (addEdge H e) b =
      (paddedWitnesses A H b).filter fun w => ¬ KilledBy e w := by
  ext ⟨S, Y⟩
  simp only [mem_filter, mem_paddedWitnesses, mem_paddingFamily]
  constructor
  · rintro ⟨hS, hYU, hcard, hnew⟩
    refine ⟨⟨hS, hYU, hcard, ?_⟩, ?_⟩
    · intro z hz
      obtain ⟨hzU, hzpos⟩ := mem_filter.mp hz
      exact hnew (mem_filter.mpr ⟨hzU, (addEdge_positive H e z.1 z.2).mpr (Or.inl hzpos)⟩)
    · rintro (⟨hu, hv, hnot⟩ | ⟨hv, hu, hnot⟩)
      · exact hnot (hnew ((mem_knownPairs _ _ _ _).mpr
          ⟨hu, hv, (addEdge_positive H e _ _).mpr (Or.inr (Or.inl rfl))⟩))
      · exact hnot (hnew ((mem_knownPairs _ _ _ _).mpr
          ⟨hv, hu, (addEdge_positive H e _ _).mpr (Or.inr (Or.inr rfl))⟩))
  · rintro ⟨⟨hS, hYU, hcard, hold⟩, hkill⟩
    refine ⟨hS, hYU, hcard, ?_⟩
    rintro ⟨x, y⟩ hz
    obtain ⟨hx, hy, hp⟩ := (mem_knownPairs _ _ _ _).mp hz
    rcases (addEdge_positive H e x y).mp hp with hp | hp | hp
    · exact hold ((mem_knownPairs _ _ _ _).mpr ⟨hx, hy, hp⟩)
    · by_contra hnot
      apply hkill
      left
      have hx' : x = e.val.1 := congrArg Prod.fst hp
      have hy' : y = e.val.2 := congrArg Prod.snd hp
      simpa only [hx', hy'] using And.intro hx (And.intro hy hnot)
    · by_contra hnot
      apply hkill
      right
      have hy' : y = e.val.1 := congrArg Prod.fst hp
      have hx' : x = e.val.2 := congrArg Prod.snd hp
      simpa only [hx', hy'] using And.intro hx (And.intro hy hnot)

theorem paddedWitnesses_addEdge_subset (A : Finset (Finset V)) (H : WeightedGraph V)
    (b : ℕ) (e : EdgeIndex V) : paddedWitnesses A (addEdge H e) b ⊆ paddedWitnesses A H b := by
  rw [paddedWitnesses_addEdge]
  exact filter_subset _ _

theorem filtered_paddedWitnesses_card (A : Finset (Finset V)) (H : WeightedGraph V)
    (b : ℕ) (P : Finset V × Finset (V × V) → Prop) :
    ((paddedWitnesses A H b).filter P).card =
      ∑ S ∈ A, ((paddingFamily H S b).filter fun Y => P (S, Y)).card := by
  have he : (paddedWitnesses A H b).filter P =
      A.biUnion (fun S => ((paddingFamily H S b).filter fun Y => P (S, Y)).image
        fun Y => (S, Y)) := by
    ext ⟨S, Y⟩
    simp [paddedWitnesses, and_assoc]
  rw [he, card_biUnion]
  · apply sum_congr rfl
    intro S _
    exact card_image_of_injective _ (fun Y Z h => (Prod.mk.inj h).2)
  · intro S _ T _ hST
    apply disjoint_left.mpr
    intro w hwS hwT
    obtain ⟨Y, _, heS⟩ := mem_image.mp hwS
    obtain ⟨Z, _, heT⟩ := mem_image.mp hwT
    exact hST (congrArg Prod.fst (heS.trans heT.symm))

/-- Sum the conditional calculation over its true shore fibers. -/
theorem phase_witness_loss_count (A : Finset (Finset V)) (H : WeightedGraph V)
    (e : EdgeIndex V) {f k : ℕ} (hk : 1 ≤ k) (hkf : k ≤ f)
    (hpossible : ∀ S ∈ A, f ≤ (possiblePairs S).card)
    (hlower : ∀ S ∈ A, f - k ≤ (knownPairs H S).card)
    (hunknown : H.w e.val.1 e.val.2 = 0) :
    (k / 2 + 1) * (separatedWitnesses A H (f - k / 2 - 1) e.val.1 e.val.2).card ≤
      k * ((paddedWitnesses A H (f - k / 2 - 1)).filter (KilledBy e)).card := by
  unfold separatedWitnesses
  rw [filtered_paddedWitnesses_card, filtered_paddedWitnesses_card, mul_sum, mul_sum]
  apply sum_le_sum
  intro S hS
  by_cases hsep : Separates e.val.1 e.val.2 S
  · by_cases hupper : (knownPairs H S).card ≤ f - k / 2 - 1
    · rcases hsep with ⟨hu, hv⟩ | ⟨hv, hu⟩
      · have heU : e.val ∈ possiblePairs S := (mem_possiblePairs _ _ _).mpr ⟨hu, hv⟩
        have heK : e.val ∉ knownPairs H S := by
          intro he
          have hp := ((mem_knownPairs H S e.val.1 e.val.2).mp he).2.2
          rw [hunknown] at hp
          exact (lt_irrefl (0 : ℝ)) hp
        have h := phase_padding_missing (possiblePairs S) (knownPairs H S)
          (knownPairs_subset H S) hk hkf (hpossible S hS) (hlower S hS) hupper heU heK
        simpa only [paddingFamily, filter_filter, KilledBy, Separates, hu, hv,
          not_false_eq_true, not_true_eq_false, and_true, true_and, and_false,
          false_and, or_false, false_or, filter_true] using h
      · have heU : (e.val.2, e.val.1) ∈ possiblePairs S :=
          (mem_possiblePairs _ _ _).mpr ⟨hv, hu⟩
        have heK : (e.val.2, e.val.1) ∉ knownPairs H S := by
          simp [H.symm e.val.2 e.val.1, hunknown]
        have h := phase_padding_missing (possiblePairs S) (knownPairs H S)
          (knownPairs_subset H S) hk hkf (hpossible S hS) (hlower S hS) hupper heU heK
        simpa only [paddingFamily, filter_filter, KilledBy, Separates, hu, hv,
          not_false_eq_true, not_true_eq_false, and_true, true_and, and_false,
          false_and, or_false, false_or, filter_true] using h
    · simp [paddingFamily_empty_of_lt H S (by omega : f - k / 2 - 1 <
        (knownPairs H S).card)]
  · simp [hsep]

theorem witness_loss_card_identity (A : Finset (Finset V)) (H : WeightedGraph V)
    (b : ℕ) (e : EdgeIndex V) :
    (paddedWitnesses A (addEdge H e) b).card +
      ((paddedWitnesses A H b).filter (KilledBy e)).card = (paddedWitnesses A H b).card := by
  rw [paddedWitnesses_addEdge, add_comm]
  exact card_filter_add_card_filter_not (KilledBy e)

/-- The loss bound for the actual padded-witness potential, before dividing
by the positive current witness count. -/
theorem phase_witness_loss (A : Finset (Finset V)) (H : WeightedGraph V)
    (e : EdgeIndex V) {f k : ℕ} (hk : 1 ≤ k) (hkf : k ≤ f)
    (hpossible : ∀ S ∈ A, f ≤ (possiblePairs S).card)
    (hlower : ∀ S ∈ A, f - k ≤ (knownPairs H S).card)
    (hunknown : H.w e.val.1 e.val.2 = 0)
    (hne : (paddedWitnesses A H (f - k / 2 - 1)).Nonempty) :
    ((k / 2 + 1 : ℕ) : ℚ) *
        |potential A H (f - k / 2 - 1) e.val.1 -
          potential A H (f - k / 2 - 1) e.val.2| *
        (paddedWitnesses A H (f - k / 2 - 1)).card ≤
      (k : ℚ) * ((paddedWitnesses A H (f - k / 2 - 1)).card -
        (paddedWitnesses A (addEdge H e) (f - k / 2 - 1)).card) := by
  have hcount := phase_witness_loss_count A H e hk hkf hpossible hlower hunknown
  have hcountQ : ((k / 2 + 1 : ℕ) : ℚ) *
      (separatedWitnesses A H (f - k / 2 - 1) e.val.1 e.val.2).card ≤
      (k : ℚ) * ((paddedWitnesses A H (f - k / 2 - 1)).filter (KilledBy e)).card := by
    exact_mod_cast hcount
  have hsep := potential_separation A H (f - k / 2 - 1) e.val.1 e.val.2 hne
  have hm := mul_le_mul_of_nonneg_left hsep (Nat.cast_nonneg (α := ℚ) (k / 2 + 1))
  have hcard := witness_loss_card_identity A H (f - k / 2 - 1) e
  have hcardQ : ((paddedWitnesses A (addEdge H e) (f - k / 2 - 1)).card : ℚ) +
      ((paddedWitnesses A H (f - k / 2 - 1)).filter (KilledBy e)).card =
      (paddedWitnesses A H (f - k / 2 - 1)).card := by exact_mod_cast hcard
  calc
    ((k / 2 + 1 : ℕ) : ℚ) *
        |potential A H (f - k / 2 - 1) e.val.1 -
          potential A H (f - k / 2 - 1) e.val.2| *
        (paddedWitnesses A H (f - k / 2 - 1)).card =
      ((k / 2 + 1 : ℕ) : ℚ) *
        (|potential A H (f - k / 2 - 1) e.val.1 -
          potential A H (f - k / 2 - 1) e.val.2| *
          (paddedWitnesses A H (f - k / 2 - 1)).card) := by ring
    _ ≤ ((k / 2 + 1 : ℕ) : ℚ) *
        (separatedWitnesses A H (f - k / 2 - 1) e.val.1 e.val.2).card := hm
    _ ≤ (k : ℚ) * ((paddedWitnesses A H (f - k / 2 - 1)).filter (KilledBy e)).card := hcountQ
    _ = (k : ℚ) * ((paddedWitnesses A H (f - k / 2 - 1)).card -
        (paddedWitnesses A (addEdge H e) (f - k / 2 - 1)).card) := by
      congr 1
      linarith only [hcardQ]

/-- The edge found at half the search threshold contracts the actual finite
witness family. No uniform distribution on distinct shores is substituted. -/
theorem phase_witness_contraction (A : Finset (Finset V)) (H : WeightedGraph V)
    (e : EdgeIndex V) {f k : ℕ} (hk : 1 ≤ k) (hkf : k ≤ f)
    (hpossible : ∀ S ∈ A, f ≤ (possiblePairs S).card)
    (hlower : ∀ S ∈ A, f - k ≤ (knownPairs H S).card)
    (hunknown : H.w e.val.1 e.val.2 = 0)
    (hne : (paddedWitnesses A H (f - k / 2 - 1)).Nonempty)
    {δ : ℚ} (hδ : 0 ≤ δ)
    (hlength : δ / 2 ≤ |potential A H (f - k / 2 - 1) e.val.1 -
      potential A H (f - k / 2 - 1) e.val.2|) :
    ((paddedWitnesses A (addEdge H e) (f - k / 2 - 1)).card : ℚ) ≤
      (1 - δ / 4) * (paddedWitnesses A H (f - k / 2 - 1)).card := by
  have h := phase_witness_loss A H e hk hkf hpossible hlower hunknown hne
  have hkQ : (0 : ℚ) < k := by exact_mod_cast (show 0 < k by omega)
  have hc : (k : ℚ) ≤ 2 * ((k / 2 + 1 : ℕ) : ℚ) := by
    exact_mod_cast (show k ≤ 2 * (k / 2 + 1) by omega)
  have hfactor : (k : ℚ) * δ / 4 ≤ ((k / 2 + 1 : ℕ) : ℚ) *
      |potential A H (f - k / 2 - 1) e.val.1 -
        potential A H (f - k / 2 - 1) e.val.2| := by
    have h₁ := mul_le_mul_of_nonneg_right hc hδ
    have h₂ := mul_le_mul_of_nonneg_left hlength
      (Nat.cast_nonneg (α := ℚ) (k / 2 + 1))
    nlinarith
  have hm := mul_le_mul_of_nonneg_right hfactor
    (Nat.cast_nonneg (α := ℚ) (paddedWitnesses A H (f - k / 2 - 1)).card)
  apply (mul_le_mul_iff_right₀ hkQ).mp
  nlinarith

theorem addEdge_mono (H : WeightedGraph V) (e : EdgeIndex V) :
    H.IsSubgraph (addEdge H e) := by
  intro u v
  change H.w u v ≤ H.w u v + (edgeGraph e 1 (by norm_num)).w u v
  exact le_add_of_nonneg_right ((edgeGraph e 1 (by norm_num)).nonneg u v)

/-- Updating the learned core graph preserves the fixed outside graph. -/
theorem addEdge_add_left (K L : WeightedGraph V) (e : EdgeIndex V) :
    K.add (addEdge L e) = addEdge (K.add L) e := by
  ext u v
  simp only [addEdge, add_w, _root_.add_assoc]

private theorem weight_of_match (H : WeightedGraph V) (e : EdgeIndex V) {u v : V}
    (h : (u, v) = e.val ∨ (v, u) = e.val) : H.w u v = H.w e.val.1 e.val.2 := by
  rcases h with h | h
  · exact congrArg (fun p : V × V => H.w p.1 p.2) h
  · exact (H.symm u v).trans (congrArg (fun p : V × V => H.w p.1 p.2) h)

theorem addEdge_unit {H : WeightedGraph V} (hH : AllPairsAudit.Unweighted H)
    (e : EdgeIndex V) (hunknown : H.w e.val.1 e.val.2 = 0) :
    AllPairsAudit.Unweighted (addEdge H e) := by
  intro u v
  change H.w u v + (edgeGraph e 1 (by norm_num)).w u v = 0 ∨
    H.w u v + (edgeGraph e 1 (by norm_num)).w u v = 1
  rw [edgeGraph_one_w]
  by_cases hm : (u, v) = e.val ∨ (v, u) = e.val
  · rw [ite_eq_left hm, weight_of_match H e hm, hunknown]
    simp
  · simpa only [ite_eq_right hm, _root_.add_zero] using hH u v

theorem addEdge_le {H G : WeightedGraph V} (hHG : H.IsSubgraph G)
    (e : EdgeIndex V) (hunknown : H.w e.val.1 e.val.2 = 0)
    (hactual : G.w e.val.1 e.val.2 = 1) : (addEdge H e).IsSubgraph G := by
  intro u v
  change H.w u v + (edgeGraph e 1 (by norm_num)).w u v ≤ G.w u v
  rw [edgeGraph_one_w]
  by_cases hm : (u, v) = e.val ∨ (v, u) = e.val
  · rw [ite_eq_left hm, weight_of_match H e hm, weight_of_match G e hm,
      hunknown, hactual]
    norm_num
  · simpa only [ite_eq_right hm, _root_.add_zero] using hHG u v

theorem addEdge_supported (C : Finset V) (L : WeightedGraph V)
    (hL : ∀ u v, u ∉ C ∨ v ∉ C → L.w u v = 0)
    (e : EdgeIndex V) (hu : e.val.1 ∈ C) (hv : e.val.2 ∈ C) :
    ∀ x y, x ∉ C ∨ y ∉ C → (addEdge L e).w x y = 0 := by
  intro x y hxy
  have hm : ¬ ((x, y) = e.val ∨ (y, x) = e.val) := by
    intro he
    rcases he with he | he
    · have hx : x ∈ C := (show x = e.val.1 from congrArg Prod.fst he).symm ▸ hu
      have hy : y ∈ C := (show y = e.val.2 from congrArg Prod.snd he).symm ▸ hv
      exact hxy.elim (fun h => h hx) (fun h => h hy)
    · have hy : y ∈ C := (show y = e.val.1 from congrArg Prod.fst he).symm ▸ hu
      have hx : x ∈ C := (show x = e.val.2 from congrArg Prod.snd he).symm ▸ hv
      exact hxy.elim (fun h => h hx) (fun h => h hy)
  change L.w x y + (edgeGraph e 1 (by norm_num)).w x y = 0
  rw [hL x y hxy, edgeGraph_one_w, ite_eq_right hm]
  norm_num

end
end CutQueryComplexity.CanonicalST.Witness

#print axioms CutQueryComplexity.CanonicalST.Witness.padding_missing_card
#print axioms CutQueryComplexity.CanonicalST.Witness.padding_missing_mul
#print axioms CutQueryComplexity.CanonicalST.Witness.phase_padding_missing
#print axioms CutQueryComplexity.CanonicalST.Witness.potential_separation
#print axioms CutQueryComplexity.CanonicalST.Witness.paddedWitnesses_addEdge
#print axioms CutQueryComplexity.CanonicalST.Witness.phase_witness_loss_count
#print axioms CutQueryComplexity.CanonicalST.Witness.phase_witness_loss

#print axioms CutQueryComplexity.CanonicalST.Witness.phase_witness_contraction
#print axioms CutQueryComplexity.CanonicalST.Witness.addEdge_unit
#print axioms CutQueryComplexity.CanonicalST.Witness.addEdge_le
#print axioms CutQueryComplexity.CanonicalST.Witness.addEdge_supported
