import CutQueryComplexity.StarContraction2022.Contraction.Joint.Avoidance

/-! Part of the actual contraction proof: attachment traces, labels, and the public quotient. -/

set_option autoImplicit false

namespace CutQueryComplexity.StarContraction2022.Contraction.Joint

open Finset LearnSubgraph
open CutQueryComplexity.Probability
open scoped Classical ENNReal
noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V]

private theorem attachment_mass_bind_ge {T U : Type*} (p : PMF T) (next : T → PMF U)
    (Good : T → Prop) (Success : U → Prop) (c : ℝ≥0∞)
    (h : ∀ t ∈ p.support, Good t → c ≤ mass (next t) Success) :
    mass p Good * c ≤ mass (p.bind next) Success := by
  rw [mass_eq_tsum, mass_bind, ← ENNReal.tsum_mul_right]
  apply ENNReal.tsum_le_tsum
  intro t
  by_cases ht : Good t
  · simp only [ht, ite_true]
    by_cases hs : t ∈ p.support
    · exact mul_le_mul le_rfl (h t hs ht) (by positivity) (by positivity)
    · have hz : p t = 0 := by simpa only [PMF.mem_support_iff, not_not] using hs
      simp [hz]
  · simp [ht]

private theorem attachment_crossingRatio_eq_inter {A : Type} [Fintype A] [DecidableEq A]
    (C N : Finset A) : Probability.crossingRatio C N = ((C ∩ N).card : ℝ) / N.card := by
  unfold Probability.crossingRatio
  apply congrArg (fun F : Finset A => (F.card : ℝ) / N.card)
  ext w
  simp only [mem_inter]

namespace CenterAttachment

/-! The last quotient is formed on original vertices. Its public labels are
the actual center-component labels plus one label for each unattached outside
vertex. In particular, empty labels are never introduced, and no optimum of
an induced graph is needed for original-cut preservation. -/

variable {Q : Type} [Fintype Q] [DecidableEq Q]

def trace (R S : Finset V) : Finset R :=
  univ.filter fun v => v.val ∈ S

@[simp] theorem mem_trace (R S : Finset V) (v : R) :
    v ∈ trace R S ↔ v.val ∈ S := by simp [trace]

def unattached (R : Finset V) (attach : V → Option R) : Finset V :=
  univ.filter fun v => v ∉ R ∧ attach v = none

/-- All inputs are public: centers, their quotient, and the sampled outside
attachments. The hidden graph and target shore do not occur in the map. -/
def label (R : Finset V) (π : PublicQuotient R Q) (attach : V → Option R)
    (v : V) : Q ⊕ unattached R attach :=
  if hv : v ∈ R then Sum.inl (π.map ⟨v,hv⟩)
  else match ha : attach v with
    | none => Sum.inr ⟨v, by simp [unattached,hv,ha]⟩
    | some u => Sum.inl (π.map u)

@[simp] theorem label_center (R : Finset V) (π : PublicQuotient R Q)
    (attach : V → Option R) (v : R) : label R π attach v.val = Sum.inl (π.map v) := by
  simp [label,v.property]

theorem label_attached (R : Finset V) (π : PublicQuotient R Q)
    (attach : V → Option R) {v : V} (hv : v ∉ R) {u : R}
    (ha : attach v = some u) : label R π attach v = Sum.inl (π.map u) := by
  unfold label
  rw [dif_neg hv]
  split
  · rename_i he
    cases he.symm.trans ha
  · rename_i w he
    have hw : w = u := Option.some.inj (he.symm.trans ha)
    subst w
    rfl

@[simp] theorem label_unattached (R : Finset V) (π : PublicQuotient R Q)
    (attach : V → Option R) (v : unattached R attach) :
    label R π attach v.val = Sum.inr v := by
  have hv := (mem_filter.mp v.property).2
  unfold label
  rw [dif_neg hv.1]
  split
  · rfl
  · rename_i w he
    cases hv.2.symm.trans he

def quotient (R : Finset V) (π : PublicQuotient R Q) (attach : V → Option R) :
    PublicQuotient V (Q ⊕ unattached R attach) where
  map := label R π attach
  onto := by
    intro q
    cases q with
    | inl q =>
      obtain ⟨v,hv⟩ := π.onto q
      exact ⟨v.val, (label_center R π attach v).trans (congrArg Sum.inl hv)⟩
    | inr v => exact ⟨v.val, label_unattached R π attach v⟩

theorem label_inl_witness (R : Finset V) (π : PublicQuotient R Q)
    (attach : V → Option R) {v : V} {q : Q} (he : label R π attach v = Sum.inl q) :
    ∃ u : R, π.map u = q ∧ (v = u.val ∨ (v ∉ R ∧ attach v = some u)) := by
  by_cases hv : v ∈ R
  · refine ⟨⟨v,hv⟩, ?_, Or.inl rfl⟩
    simpa [label,hv] using he
  · cases ha : attach v with
    | none =>
      have hu : v ∈ unattached R attach := by simp [unattached, hv, ha]
      have hl := label_unattached R π attach ⟨v, hu⟩
      cases hl.symm.trans he
    | some u =>
      refine ⟨u, ?_, Or.inr ⟨hv,rfl⟩⟩
      exact Sum.inl.inj ((label_attached R π attach hv ha).symm.trans he)

theorem label_inr_value (R : Finset V) (π : PublicQuotient R Q)
    (attach : V → Option R) {v : V} {u : unattached R attach}
    (he : label R π attach v = Sum.inr u) : v = u.val := by
  by_cases hv : v ∈ R
  · simp [label,hv] at he
  · cases ha : attach v with
    | none =>
      have hu : v ∈ unattached R attach := by simp [unattached, hv, ha]
      have hl := label_unattached R π attach ⟨v, hu⟩
      exact congrArg Subtype.val (Sum.inr.inj (hl.symm.trans he))
    | some w =>
      cases (label_attached R π attach hv ha).symm.trans he

theorem respects (R S : Finset V) (π : PublicQuotient R Q)
    (attach : V → Option R)
    (hcore : RespectsBlocks π.map (trace R S))
    (hout : ∀ v, v ∉ R → ∀ u, attach v = some u → (v ∈ S ↔ u.val ∈ S)) :
    RespectsBlocks (quotient R π attach).map S := by
  intro v w hmap
  change label R π attach v = label R π attach w at hmap
  cases he : label R π attach v with
  | inl q =>
    obtain ⟨a,ha,hva⟩ := label_inl_witness R π attach he
    obtain ⟨b,hb,hwb⟩ := label_inl_witness R π attach (hmap.symm.trans he)
    have hab : a.val ∈ S ↔ b.val ∈ S := by
      simpa only [mem_trace] using hcore a b (ha.trans hb.symm)
    have hvs : v ∈ S ↔ a.val ∈ S := by
      rcases hva with hva | ⟨hv,hva⟩
      · rw [hva]
      · exact hout v hv a hva
    have hws : w ∈ S ↔ b.val ∈ S := by
      rcases hwb with hwb | ⟨hw,hwb⟩
      · rw [hwb]
      · exact hout w hw b hwb
    exact hvs.trans (hab.trans hws.symm)
  | inr a =>
    have hv := label_inr_value R π attach he
    have hw := label_inr_value R π attach (hmap.symm.trans he)
    rw [hv,hw]

theorem card_labels (R : Finset V) (attach : V → Option R) :
    Fintype.card (Q ⊕ unattached R attach) = Fintype.card Q + (unattached R attach).card := by
  simp

theorem unattached_card_le (R B : Finset V) (attach : V → Option R)
    (hout : ∀ v, v ∉ R → attach v = none → v ∈ B) :
    (unattached R attach).card ≤ (B \ R).card := by
  apply card_le_card
  intro v hv
  have hh := (mem_filter.mp hv).2
  exact mem_sdiff.mpr ⟨hout v hh.1 hh.2, hh.1⟩

/-- This is the joint bad-set accounting: the center bound charges B∩R,
whereas unattached outside vertices charge B\R. Their sum is |B|. -/
theorem card_labels_le (R B : Finset V) (attach : V → Option R) (cost : ℝ)
    (hcore : (Fintype.card Q : ℝ) ≤ (B ∩ R).card + cost)
    (hout : ∀ v, v ∉ R → attach v = none → v ∈ B) :
    (Fintype.card (Q ⊕ unattached R attach) : ℝ) ≤ B.card + cost := by
  have ho : ((unattached R attach).card : ℝ) ≤ (B \ R).card := by
    exact_mod_cast unattached_card_le R B attach hout
  have hs : ((B \ R).card : ℝ) + (B ∩ R).card = B.card := by
    exact_mod_cast badSet_split B R
  rw [card_labels, Nat.cast_add]
  linarith

/-- Original shore and exact minimum value are transferred only after the
full original-vertex quotient is constructed. No induced-minimum premise. -/
theorem preserves_minimum (R S : Finset V) (π : PublicQuotient R Q)
    (attach : V → Option R) (G : WeightedGraph V) (hS : IsMinCut G S)
    (hcore : RespectsBlocks π.map (trace R S))
    (hout : ∀ v, v ∉ R → ∀ u, attach v = some u → (v ∈ S ↔ u.val ∈ S)) :
    IsMinCut ((quotient R π attach).graph G) (S.image (quotient R π attach).map) ∧
      mincutValue ((quotient R π attach).graph G) = mincutValue G ∧
      2 ≤ Fintype.card (Q ⊕ unattached R attach) := by
  have hr := respects R S π attach hcore hout
  exact ⟨(quotient R π attach).project_minimum hS hr,
    (quotient R π attach).mincut_eq hS hr,
    (quotient R π attach).two_le_card_of_survives hr hS.1⟩

/-! Fresh outside draws are constructed from the complete public learned row
table. The source set and center set can be different types of vertices; no
independence of the earlier recovery rows is used. -/

def extendOutside (E R : Finset V) (draws : E → Option R) : V → Option R :=
  fun v => if hv : v ∈ E then draws ⟨v,hv⟩ else none

@[simp] theorem extendOutside_source (E R : Finset V) (draws : E → Option R) (u : E) :
    extendOutside E R draws u.val = draws u := by
  simp [extendOutside,u.property]

@[simp] theorem extendOutside_other (E R : Finset V) (draws : E → Option R)
    (v : V) (hv : v ∉ E) : extendOutside E R draws v = none := by
  simp [extendOutside,hv]

/-- One independent uniform replacement draw per eligible row, with none for
empty rows. Sampling itself takes no hidden graph or shore. -/
def outsideDraws (E R : Finset V) (N : E → Finset R) : PMF (V → Option R) :=
  (Probability.product fun u : E => Probability.neighborDraw (N u)).map
    (extendOutside E R)

def outsideDrawsProgram (E R : Finset V) (N : E → Finset R) :
    RTree (Finset V) ℝ (V → Option R) 0 := RTree.pure (outsideDraws E R N)

@[simp] theorem outsideDrawsProgram_eval (E R : Finset V) (N : E → Finset R)
    (read : Finset V → ℝ) :
    (outsideDrawsProgram E R N).eval read = outsideDraws E R N := by
  exact RTree.eval_pure _ _

def OutsideAvoidance (S R : Finset V) (attach : V → Option R) : Prop :=
  ∀ v, (attach v).elim True (fun w => v ∈ S ↔ w.val ∈ S)

def crossingColumns (R S : Finset V) (v : V) : Finset R :=
  univ.filter fun w => ¬ (v ∈ S ↔ w.val ∈ S)

@[simp] theorem mem_crossingColumns (R S : Finset V) (v : V) (w : R) :
    w ∈ crossingColumns R S v ↔ w.val ∈ crossingSet S v := by
  by_cases hv : v ∈ S <;> simp [crossingColumns,crossingSet,hv]

def outsideRatio (E R S : Finset V) (N : E → Finset R) (u : E) : ℝ :=
  Probability.crossingRatio (crossingColumns R S u.val) (N u)

/-- Recovery's proof-only crossing columns are restricted to the true row.
For any learned subrow, that restriction leaves its ratio unchanged. -/
theorem outsideRatio_true_subrow (E R S : Finset V) (N F : E → Finset R)
    (hNF : ∀ u, N u ⊆ F u) (u : E) :
    outsideRatio E R S N u =
      Probability.crossingRatio ((F u).filter (fun w => w.val ∈ crossingSet S u.val)) (N u) := by
  have he : crossingColumns R S u.val ∩ N u =
      (F u).filter (fun w => w.val ∈ crossingSet S u.val) ∩ N u := by
    ext w
    constructor
    · intro hw
      have hh := mem_inter.mp hw
      exact mem_inter.mpr ⟨mem_filter.mpr
        ⟨hNF u hh.2,(mem_crossingColumns R S u.val w).mp hh.1⟩,hh.2⟩
    · intro hw
      have hh := mem_inter.mp hw
      exact mem_inter.mpr
        ⟨(mem_crossingColumns R S u.val w).mpr (mem_filter.mp hh.1).2,hh.2⟩
  simp only [outsideRatio,attachment_crossingRatio_eq_inter,he]

theorem extendOutside_avoidance_iff (E R S : Finset V) (draws : E → Option R) :
    OutsideAvoidance S R (extendOutside E R draws) ↔
      ∀ u : E, (draws u).elim True (fun w => u.val ∈ S ↔ w.val ∈ S) := by
  constructor
  · intro h u
    simpa only [extendOutside_source] using h u.val
  · intro h v
    by_cases hv : v ∈ E
    · simpa only [extendOutside, dif_pos hv] using h ⟨v,hv⟩
    · simp [extendOutside,hv]

theorem list_survival_factor {A : Type} [Fintype A] [DecidableEq A]
    (N Z : Finset A) :
    mass (Probability.neighborDraw N) (fun o => o.elim True (fun v => v ∉ Z)) =
      ENNReal.ofReal (1 - Probability.crossingRatio Z N) := by
  rw [Probability.mass_neighborDraw]
  by_cases hN : N.Nonempty
  · have hd : (0 : ℝ) < N.card := by exact_mod_cast card_pos.mpr hN
    have hc : ((N \ Z).card : ℝ) + ((Z ∩ N).card : ℝ) = N.card := by
      exact_mod_cast (by simpa only [inter_comm] using card_sdiff_add_card_inter N Z)
    have he : ((N \ Z).card : ℝ) / N.card = 1 - Probability.crossingRatio Z N := by
      rw [attachment_crossingRatio_eq_inter]
      apply (div_eq_iff hd.ne').mpr
      field_simp [hd.ne']
      linarith
    rw [if_pos hN]
    calc
      _ = ((N \ Z).card : ℝ≥0∞) / (N.card : ℝ≥0∞) := by
        apply congrArg (fun F : Finset A => (F.card : ℝ≥0∞) / (N.card : ℝ≥0∞))
        ext v
        simp only [mem_filter, mem_sdiff]
      _ = _ := by
        rw [← he, ENNReal.ofReal_div_of_pos hd,
          ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
  · have he : N = ∅ := not_nonempty_iff_eq_empty.mp hN
    simp [hN,he,Probability.crossingRatio]

/-- Exact product probability, proved for the constructed public sampler. -/
theorem outsideDraws_avoidance_mass (E R S : Finset V) (N : E → Finset R) :
    mass (outsideDraws E R N) (OutsideAvoidance S R) =
      ENNReal.ofReal (∏ u : E, (1 - outsideRatio E R S N u)) := by
  rw [outsideDraws,mass_map]
  simp_rw [extendOutside_avoidance_iff]
  rw [Probability.mass_product (fun u : E => Probability.neighborDraw (N u))
    (fun u o => o.elim True (fun w => u.val ∈ S ↔ w.val ∈ S))]
  have hrow (u : E) :
      mass (Probability.neighborDraw (N u))
          (fun o => o.elim True (fun w => u.val ∈ S ↔ w.val ∈ S)) =
        ENNReal.ofReal (1 - outsideRatio E R S N u) := by
    simpa only [outsideRatio,crossingColumns,mem_filter,mem_univ,true_and,not_not] using
      list_survival_factor (N u) (crossingColumns R S u.val)
  simp_rw [hrow]
  exact (ENNReal.ofReal_prod_of_nonneg (fun u _ =>
    sub_nonneg.mpr (Probability.crossingRatio_le_one _ _))).symm

theorem outsideDraws_avoidance_lower (E R S : Finset V) (N : E → Finset R)
    (alpha beta : ℝ) (ha0 : 0 < alpha) (ha1 : alpha < 1)
    (hmax : ∀ u, outsideRatio E R S N u ≤ alpha)
    (hsum : (∑ u, outsideRatio E R S N u) ≤ beta) :
    ENNReal.ofReal ((1 - alpha) ^ Nat.ceil (beta / alpha)) ≤
      mass (outsideDraws E R N) (OutsideAvoidance S R) := by
  rw [outsideDraws_avoidance_mass]
  apply ENNReal.ofReal_le_ofReal
  exact product_survival_lower (outsideRatio E R S N) alpha beta ha0 ha1
    (fun u => Probability.crossingRatio_nonneg _ _) hmax hsum

/-- A supported attachment is an actual member of its learned list; an
ineligible vertex has no outgoing attachment. -/
theorem outsideDraws_support (E R : Finset V) (N : E → Finset R)
    (attach : V → Option R) (ha : attach ∈ (outsideDraws E R N).support) :
    (∀ u : E, match attach u.val with
      | none => N u = ∅
      | some w => w ∈ N u) ∧ (∀ v, v ∉ E → attach v = none) := by
  obtain ⟨draws,hd,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp ha
  have hs := (Probability.mem_support_product _ _).mp hd
  constructor
  · intro u
    have hu := (Probability.mem_support_neighborDraw (N u) (draws u)).mp (hs u)
    rw [extendOutside_source]
    cases he : draws u with
    | none => simpa only [he] using hu
    | some w => simpa only [he] using hu
  · exact extendOutside_other E R draws

/-- Every eligible nonempty row attaches. Therefore the only remaining
outside singleton labels belong to the shared measured bad set. -/
theorem outsideDraws_unattached (R B : Finset V)
    (N : (univ \ (R ∪ B) : Finset V) → Finset R)
    (hN : ∀ u, (N u).Nonempty) (attach : V → Option R)
    (ha : attach ∈ (outsideDraws (univ \ (R ∪ B)) R N).support) :
    ∀ v, v ∉ R → attach v = none → v ∈ B := by
  intro v hvR hv
  by_contra hvB
  have hvE : v ∈ (univ \ (R ∪ B) : Finset V) := by simp [hvR,hvB]
  have hs := (outsideDraws_support _ _ N attach ha).1 ⟨v,hvE⟩
  have hz : N ⟨v,hvE⟩ = ∅ := by simpa only [hv] using hs
  exact (hN ⟨v,hvE⟩).ne_empty hz

theorem outsideDraws_ratio_avoidance (E R S : Finset V) (N : E → Finset R)
    (hmax : ∀ u, outsideRatio E R S N u ≤ 7 / 10)
    (hsum : (∑ u, outsideRatio E R S N u) ≤ 80) :
    ENNReal.ofReal ((3 / 10 : ℝ) ^ 115) ≤
      mass (outsideDraws E R N) (OutsideAvoidance S R) := by
  have he : Nat.ceil ((80 : ℝ) / (7 / 10)) = 115 := by
    rw [Nat.ceil_eq_iff (by norm_num : (115 : ℕ) ≠ 0)]
    norm_num
  simpa only [he,show (1 : ℝ) - 7 / 10 = 3 / 10 by norm_num] using
    outsideDraws_avoidance_lower E R S N (7 / 10) 80 (by norm_num) (by norm_num) hmax hsum

theorem outsideDraws_avoidance_complete (R B S : Finset V)
    (N : (univ \ (R ∪ B) : Finset V) → Finset R)
    (hN : ∀ u, (N u).Nonempty)
    (hmax : ∀ u, outsideRatio (univ \ (R ∪ B)) R S N u ≤ 7 / 10)
    (hsum : (∑ u, outsideRatio (univ \ (R ∪ B)) R S N u) ≤ 80) :
    ENNReal.ofReal ((3 / 10 : ℝ) ^ 115) ≤
      mass (outsideDraws (univ \ (R ∪ B)) R N) (fun attach =>
        OutsideAvoidance S R attach ∧ ∀ v, v ∉ R → attach v = none → v ∈ B) := by
  apply (outsideDraws_ratio_avoidance _ R S N hmax hsum).trans
  apply mass_mono_on_support
  intro attach ha hav
  exact ⟨hav,outsideDraws_unattached R B N hN attach ha⟩

theorem outsideDraws_edges (E R : Finset V) (N : E → Finset R)
    (Edge : V → R → Prop) (htrue : ∀ u : E, ∀ w ∈ N u, Edge u.val w)
    (attach : V → Option R) (ha : attach ∈ (outsideDraws E R N).support) :
    ∀ v w, attach v = some w → Edge v w := by
  intro v w he
  have hs := outsideDraws_support E R N attach ha
  by_cases hv : v ∈ E
  · have hw : w ∈ N ⟨v,hv⟩ := by simpa only [he] using hs.1 ⟨v,hv⟩
    exact htrue ⟨v,hv⟩ w hw
  · have hh := hs.2 v hv
    rw [he] at hh
    cases hh

/-- The complete recovery transcript is retained before fresh replacement
draws. This is a bind of the actual previous law, not a law conditioned on
global recovery success. -/
def afterOutsideTranscript {T : Type} (μ : PMF T) (E R : Finset V)
    (rows : T → E → Finset R) : PMF (T × (V → Option R)) :=
  μ.bind fun t => (outsideDraws E R (rows t)).map fun attach => (t,attach)

theorem afterOutsideTranscript_avoidance {T : Type} (μ : PMF T) (E R S : Finset V)
    (rows : T → E → Finset R) (Good : T → Prop)
    (hgood : ∀ t ∈ μ.support, Good t →
      (∀ u, outsideRatio E R S (rows t) u ≤ 7 / 10) ∧
        (∑ u, outsideRatio E R S (rows t) u) ≤ 80) :
    mass μ Good * ENNReal.ofReal ((3 / 10 : ℝ) ^ 115) ≤
      mass (afterOutsideTranscript μ E R rows)
        (fun out => Good out.1 ∧ OutsideAvoidance S R out.2) := by
  apply attachment_mass_bind_ge μ
    (fun t => (outsideDraws E R (rows t)).map fun attach => (t,attach)) Good _ _
  intro t ht hg
  rw [mass_map]
  simp only [hg,true_and]
  exact outsideDraws_ratio_avoidance E R S (rows t) (hgood t ht hg).1 (hgood t ht hg).2

theorem afterOutsideTranscript_complete {T : Type} (μ : PMF T) (R B S : Finset V)
    (rows : T → (univ \ (R ∪ B) : Finset V) → Finset R) (Good : T → Prop)
    (hgood : ∀ t ∈ μ.support, Good t →
      (∀ u, (rows t u).Nonempty) ∧
      (∀ u, outsideRatio (univ \ (R ∪ B)) R S (rows t) u ≤ 7 / 10) ∧
        (∑ u, outsideRatio (univ \ (R ∪ B)) R S (rows t) u) ≤ 80) :
    mass μ Good * ENNReal.ofReal ((3 / 10 : ℝ) ^ 115) ≤
      mass (afterOutsideTranscript μ (univ \ (R ∪ B)) R rows) (fun out =>
        Good out.1 ∧ OutsideAvoidance S R out.2 ∧
          ∀ v, v ∉ R → out.2 v = none → v ∈ B) := by
  apply attachment_mass_bind_ge μ
    (fun t => (outsideDraws (univ \ (R ∪ B)) R (rows t)).map fun attach => (t,attach)) Good _ _
  intro t ht hg
  rw [mass_map]
  simp only [hg,true_and]
  exact outsideDraws_avoidance_complete R B S (rows t)
    (hgood t ht hg).1 (hgood t ht hg).2.1 (hgood t ht hg).2.2

end CenterAttachment

section ComposedTwoOut

variable [LinearOrder V]

/-- Concrete public composition of the sampled center components and the
outside one-out attachments, retaining every original vertex. -/
def composedQuotient (R : Finset V) (tape : TwoOut.Tape R) (attach : V → Option R) :
    PublicQuotient V
      ((TwoOut.selectedGraph tape).ConnectedComponent ⊕ CenterAttachment.unattached R attach) :=
  CenterAttachment.quotient R (TwoOut.publicQuotient tape) attach

theorem composedQuotient_preserves (R S : Finset V) (tape : TwoOut.Tape R)
    (attach : V → Option R) (G : WeightedGraph V) (hS : IsMinCut G S)
    (hcore : Avoidance (CenterAttachment.trace R S) tape)
    (hout : ∀ v, v ∉ R → ∀ u, attach v = some u → (v ∈ S ↔ u.val ∈ S)) :
    IsMinCut ((composedQuotient R tape attach).graph G)
        (S.image (composedQuotient R tape attach).map) ∧
      mincutValue ((composedQuotient R tape attach).graph G) = mincutValue G ∧
      2 ≤ Fintype.card
        ((TwoOut.selectedGraph tape).ConnectedComponent ⊕ CenterAttachment.unattached R attach) := by
  exact CenterAttachment.preserves_minimum R S (TwoOut.publicQuotient tape) attach G hS
    (TwoOut.publicQuotient_respects (avoidance_twoOut _ _ hcore)) hout

theorem composedQuotient_card_le (R B : Finset V) (tape : TwoOut.Tape R)
    (attach : V → Option R) (cost : ℝ)
    (hcore : (TwoOut.componentCount tape : ℝ) ≤ (B ∩ R).card + cost)
    (hout : ∀ v, v ∉ R → attach v = none → v ∈ B) :
    (Fintype.card
      ((TwoOut.selectedGraph tape).ConnectedComponent ⊕ CenterAttachment.unattached R attach) : ℝ) ≤
        B.card + cost := by
  apply CenterAttachment.card_labels_le R B attach cost
  · simpa only [TwoOut.componentCount, Fintype.card_eq_nat_card] using hcore
  · exact hout

/-- The proved component event passes the literal public middle-degree
guard, after charging the common bad set once. -/
theorem composedQuotient_guard (R B : Finset V) (d : ℕ) (tape : TwoOut.Tape R)
    (attach : V → Option R) (hd : Schedule.degreeCutoff ≤ d)
    (hc : Schedule.CenterGuard (Fintype.card V) d R.card)
    (hb : Schedule.BadGuard (Fintype.card V) d B.card)
    (hcore : (TwoOut.componentCount tape : ℝ) ≤ (B ∩ R).card +
      (R.card : ℝ) / Schedule.height d +
        (8 * Real.exp 1 ^ 3 + 1) * R.card / (Schedule.height d / 5 : ℕ))
    (hout : ∀ v, v ∉ R → attach v = none → v ∈ B) :
    Fintype.card
      ((TwoOut.selectedGraph tape).ConnectedComponent ⊕ CenterAttachment.unattached R attach) * d ≤
        80000 * Fintype.card V := by
  have he := Schedule.twoOut_degree_envelope d hd
  have hh := Schedule.height_ge d hd
  have hh0 : (0 : ℝ) < Schedule.height d := by exact_mod_cast (by omega : 0 < Schedule.height d)
  have he0 : (0 : ℝ) < (Schedule.height d / 5 : ℕ) := by
    exact_mod_cast (by omega : 0 < Schedule.height d / 5)
  have hhe : (Schedule.height d : ℝ) ≤ 6 * (Schedule.height d / 5 : ℕ) := by
    exact_mod_cast he.2
  have hratio : (R.card : ℝ) / (Schedule.height d / 5 : ℕ) ≤
      6 * ((R.card : ℝ) / Schedule.height d) := by
    apply (div_le_iff₀ he0).mpr
    calc
      (R.card : ℝ) = ((R.card : ℝ) / Schedule.height d) * Schedule.height d := by
        field_simp [hh0.ne']
      _ ≤ ((R.card : ℝ) / Schedule.height d) * (6 * (Schedule.height d / 5 : ℕ)) :=
        mul_le_mul_of_nonneg_left hhe (by positivity)
      _ = _ := by ring
  have hcomponent : (TwoOut.componentCount tape : ℝ) ≤ (B ∩ R).card +
      (7 + 48 * Real.exp 1 ^ 3) * ((R.card : ℝ) / Schedule.height d) := by
    calc
      _ ≤ (B ∩ R).card + (R.card : ℝ) / Schedule.height d +
          (8 * Real.exp 1 ^ 3 + 1) * ((R.card : ℝ) / (Schedule.height d / 5 : ℕ)) := by
        simpa only [mul_div_assoc] using hcore
      _ ≤ (B ∩ R).card + (R.card : ℝ) / Schedule.height d +
          (8 * Real.exp 1 ^ 3 + 1) * (6 * ((R.card : ℝ) / Schedule.height d)) := by
        gcongr
      _ = _ := by ring
  exact Schedule.middle_component_guard (Fintype.card V) d R.card B.card _ hd hc hb
    (composedQuotient_card_le R B tape attach _ hcomponent hout)

/-- The center event keeps the original shore's trace and its actual
component count. It makes no minimum-cut assertion about the induced graph. -/
def CenterDrawsGood (R B S : Finset V) (d : ℕ) (tape : TwoOut.Tape R) : Prop :=
  Avoidance (CenterAttachment.trace R S) tape ∧
    (TwoOut.componentCount tape : ℝ) ≤ (B ∩ R).card +
      (R.card : ℝ) / Schedule.height d +
        (8 * Real.exp 1 ^ 3 + 1) * R.card / (Schedule.height d / 5 : ℕ)

/-- Literal center parameters, obtained from the joint conditioned-exposure
theorem and the genuine learned-row deficiency bound. -/
theorem centerDraws_good (R B S : Finset V) (d : ℕ) (N : R → Finset R)
    (hd : Schedule.degreeCutoff ≤ d)
    (hgood : GoodRows (4 / 5) 800 N (CenterAttachment.trace R S))
    (hdegree : ∀ v, N v ≠ ∅ → Schedule.height d ≤ (N v).card)
    (hzero : ((zeroSources N).card : ℝ) ≤ (B ∩ R).card + (R.card : ℝ) / Schedule.height d)
    (hloop : ∀ v, v ∉ N v) :
    ENNReal.ofReal ((1 / 5 : ℝ) ^ 2000) * ENNReal.ofReal (199 / 200 : ℝ) ≤
      mass (Probability.neighborTape N 2) (CenterDrawsGood R B S d) := by
  have hdeg : ∀ v, v ∉ zeroSources N → Schedule.height d ≤ (N v).card := by
    intro v hv
    apply hdegree v
    simpa only [zeroSources,mem_filter,mem_univ,true_and] using hv
  have hdiv : 5 * (Schedule.height d / 5) ≤ Schedule.height d := by omega
  have hell : ((Schedule.height d / 5 : ℕ) : ℝ) ≤
      (1 - (4 / 5 : ℝ)) * Schedule.height d := by
    have hr : (5 : ℝ) * (Schedule.height d / 5 : ℕ) ≤ (Schedule.height d : ℝ) := by
      exact_mod_cast hdiv
    linarith
  have hceil : Nat.ceil ((800 : ℝ) / (4 / 5)) = 1000 := by norm_num
  have hbase : ENNReal.ofReal ((1 / 5 : ℝ) ^ 2000) * ENNReal.ofReal (199 / 200 : ℝ) ≤
      mass (Probability.neighborTape N 2) (fun tape =>
        Avoidance (CenterAttachment.trace R S) tape ∧
          (TwoOut.componentCount tape : ℝ) ≤ (zeroSources N).card +
            (8 * Real.exp 1 ^ 3 + 1) * R.card / (Schedule.height d / 5 : ℕ)) := by
    simpa only [hceil,Fintype.card_coe,
      show (1 : ℝ) - 4 / 5 = 1 / 5 by norm_num,show 2 * 1000 = 2000 by omega] using
      twoOut_joint_good N (CenterAttachment.trace R S) (zeroSources N) (4 / 5) 800
        (Schedule.height d) (Schedule.height d / 5) (by norm_num) (by norm_num)
        hgood hdeg hloop (Schedule.twoOut_degree_envelope d hd).1 hell
  apply hbase.trans
  apply mass_mono
  intro tape ht
  exact ⟨ht.1,ht.2.trans (add_le_add hzero le_rfl)⟩

/-- Both sets of replacement draws are taken after the public learned rows
are fixed. Earlier row correlations are unrestricted. -/
def componentAttachmentDraws (R B : Finset V) (inside : R → Finset R)
    (outside : (univ \ (R ∪ B) : Finset V) → Finset R) :
    PMF (TwoOut.Tape R × (V → Option R)) :=
  (Probability.neighborTape inside 2).bind fun tape =>
    (CenterAttachment.outsideDraws (univ \ (R ∪ B)) R outside).map fun attach => (tape,attach)

def componentAttachmentProgram (R B : Finset V) (inside : R → Finset R)
    (outside : (univ \ (R ∪ B) : Finset V) → Finset R) :
    RTree (Finset V) ℝ (TwoOut.Tape R × (V → Option R)) 0 :=
  RTree.pure (componentAttachmentDraws R B inside outside)

/-- The actual fixed-transcript draws preserve a fixed original optimum,
its exact minimum value and the public middle-degree size guard together.
The center trace is never assumed to be an induced-graph optimum. -/
theorem componentAttachmentDraws_success (R B S : Finset V) (d : ℕ)
    (inside : R → Finset R) (outside : (univ \ (R ∪ B) : Finset V) → Finset R)
    (G : WeightedGraph V) (hS : IsMinCut G S) (hd : Schedule.degreeCutoff ≤ d)
    (hc : Schedule.CenterGuard (Fintype.card V) d R.card)
    (hb : Schedule.BadGuard (Fintype.card V) d B.card)
    (hgood : GoodRows (4 / 5) 800 inside (CenterAttachment.trace R S))
    (hdegree : ∀ v, inside v ≠ ∅ → Schedule.height d ≤ (inside v).card)
    (hzero : ((zeroSources inside).card : ℝ) ≤
      (B ∩ R).card + (R.card : ℝ) / Schedule.height d)
    (hloop : ∀ v, v ∉ inside v)
    (hout : ∀ u, (outside u).Nonempty)
    (homax : ∀ u, CenterAttachment.outsideRatio (univ \ (R ∪ B)) R S outside u ≤ 7 / 10)
    (hosum : (∑ u, CenterAttachment.outsideRatio (univ \ (R ∪ B)) R S outside u) ≤ 80) :
    (ENNReal.ofReal ((1 / 5 : ℝ) ^ 2000) * ENNReal.ofReal (199 / 200 : ℝ)) *
        ENNReal.ofReal ((3 / 10 : ℝ) ^ 115) ≤
      mass (componentAttachmentDraws R B inside outside) (fun out =>
        IsMinCut ((composedQuotient R out.1 out.2).graph G)
          (S.image (composedQuotient R out.1 out.2).map) ∧
        mincutValue ((composedQuotient R out.1 out.2).graph G) = mincutValue G ∧
        2 ≤ Fintype.card
          ((TwoOut.selectedGraph out.1).ConnectedComponent ⊕ CenterAttachment.unattached R out.2) ∧
        Fintype.card
          ((TwoOut.selectedGraph out.1).ConnectedComponent ⊕ CenterAttachment.unattached R out.2) * d ≤
            80000 * Fintype.card V) := by
  have hcore := centerDraws_good R B S d inside hd hgood hdegree hzero hloop
  apply (mul_le_mul hcore le_rfl (by positivity) (by positivity)).trans
  apply Probability.mass_bind_ge (Probability.neighborTape inside 2)
    (fun tape => (CenterAttachment.outsideDraws (univ \ (R ∪ B)) R outside).map
      fun attach => (tape,attach)) (CenterDrawsGood R B S d) _ _
  intro tape _ ht
  rw [mass_map]
  apply (CenterAttachment.outsideDraws_avoidance_complete R B S outside hout homax hosum).trans
  apply mass_mono
  intro attach ha
  have havoid : ∀ v, v ∉ R → ∀ u, attach v = some u → (v ∈ S ↔ u.val ∈ S) := by
    intro v _ u hu
    have hv := ha.1 v
    simpa only [hu,Option.elim_some] using hv
  have hpres := composedQuotient_preserves R S tape attach G hS ht.1 havoid
  exact ⟨hpres.1,hpres.2.1,hpres.2.2,
    composedQuotient_guard R B d tape attach hd hc hb ht.2 ha.2⟩

/-- Append fresh center and outside draws to an actual public query program.
The complete earlier transcript is returned and the advertised query budget
is unchanged. Neither the hidden graph nor a good-event predicate is an input. -/
def componentAttachmentAfter {T : Type} {q : ℕ}
    (before : RTree (Finset V) ℝ T q) (R B : Finset V)
    (inside : T → R → Finset R)
    (outside : T → (univ \ (R ∪ B) : Finset V) → Finset R) :
    RTree (Finset V) ℝ (T × (TwoOut.Tape R × (V → Option R))) q :=
  (before.bind fun transcript =>
    RTree.map (fun out => (transcript,out))
      (componentAttachmentProgram R B (inside transcript) (outside transcript))).cast
        (Nat.add_zero q)

theorem componentAttachmentAfter_eval {T : Type} {q : ℕ}
    (before : RTree (Finset V) ℝ T q) (R B : Finset V)
    (inside : T → R → Finset R)
    (outside : T → (univ \ (R ∪ B) : Finset V) → Finset R)
    (read : Finset V → ℝ) :
    (componentAttachmentAfter before R B inside outside).eval read =
      (before.eval read).bind fun transcript =>
        (componentAttachmentDraws R B (inside transcript) (outside transcript)).map
          fun out => (transcript,out) := by
  simp only [componentAttachmentAfter, RTree.eval_cast, RTree.eval_bind,
    RTree.eval_map, componentAttachmentProgram, RTree.eval_pure]

/-- Integrate the concrete fixed-transcript theorem through the actual
preceding program. Only learned-row properties are required on its good
outcomes, and their possibly correlated joint law is left intact. -/
theorem componentAttachmentAfter_success {T : Type} {q : ℕ}
    (before : RTree (Finset V) ℝ T q) (R B S : Finset V) (d : ℕ)
    (inside : T → R → Finset R)
    (outside : T → (univ \ (R ∪ B) : Finset V) → Finset R)
    (G : WeightedGraph V) (hS : IsMinCut G S) (hd : Schedule.degreeCutoff ≤ d)
    (hc : Schedule.CenterGuard (Fintype.card V) d R.card)
    (hb : Schedule.BadGuard (Fintype.card V) d B.card) (Good : T → Prop)
    (hgood : ∀ t ∈ (before.eval G.cut).support, Good t →
      GoodRows (4 / 5) 800 (inside t) (CenterAttachment.trace R S) ∧
      (∀ v, inside t v ≠ ∅ → Schedule.height d ≤ (inside t v).card) ∧
      (((zeroSources (inside t)).card : ℝ) ≤
        (B ∩ R).card + (R.card : ℝ) / Schedule.height d) ∧
      (∀ v, v ∉ inside t v) ∧
      (∀ u, (outside t u).Nonempty) ∧
      (∀ u, CenterAttachment.outsideRatio (univ \ (R ∪ B)) R S (outside t) u ≤ 7 / 10) ∧
      (∑ u, CenterAttachment.outsideRatio (univ \ (R ∪ B)) R S (outside t) u) ≤ 80) :
    mass (before.eval G.cut) Good *
        ((ENNReal.ofReal ((1 / 5 : ℝ) ^ 2000) * ENNReal.ofReal (199 / 200 : ℝ)) *
          ENNReal.ofReal ((3 / 10 : ℝ) ^ 115)) ≤
      mass ((componentAttachmentAfter before R B inside outside).eval G.cut) (fun out =>
        Good out.1 ∧
        IsMinCut ((composedQuotient R out.2.1 out.2.2).graph G)
          (S.image (composedQuotient R out.2.1 out.2.2).map) ∧
        mincutValue ((composedQuotient R out.2.1 out.2.2).graph G) = mincutValue G ∧
        2 ≤ Fintype.card
          ((TwoOut.selectedGraph out.2.1).ConnectedComponent ⊕ CenterAttachment.unattached R out.2.2) ∧
        Fintype.card
          ((TwoOut.selectedGraph out.2.1).ConnectedComponent ⊕ CenterAttachment.unattached R out.2.2) * d ≤
            80000 * Fintype.card V) := by
  rw [componentAttachmentAfter_eval]
  apply attachment_mass_bind_ge (before.eval G.cut)
    (fun t => (componentAttachmentDraws R B (inside t) (outside t)).map fun out => (t,out))
    Good _ _
  intro t ht hg
  rcases hgood t ht hg with ⟨hr, hdegree, hzero, hloop, hout, hmax, hsum⟩
  rw [mass_map]
  apply (componentAttachmentDraws_success R B S d (inside t) (outside t)
    G hS hd hc hb hr hdegree hzero hloop hout hmax hsum).trans
  apply mass_mono
  exact fun out ho => ⟨hg,ho⟩

end ComposedTwoOut

/-- The high-degree branch keeps each center separate and uses only outside
attachments. This is another instance of the same surjective public map. -/
def outsideQuotient (R : Finset V) (attach : V → Option R) :
    PublicQuotient V (R ⊕ CenterAttachment.unattached R attach) :=
  CenterAttachment.quotient R PublicQuotient.identity attach

theorem outsideQuotient_preserves (R S : Finset V) (attach : V → Option R)
    (G : WeightedGraph V) (hS : IsMinCut G S)
    (hout : ∀ v, v ∉ R → ∀ u, attach v = some u → (v ∈ S ↔ u.val ∈ S)) :
    IsMinCut ((outsideQuotient R attach).graph G) (S.image (outsideQuotient R attach).map) ∧
      mincutValue ((outsideQuotient R attach).graph G) = mincutValue G ∧
      2 ≤ Fintype.card (R ⊕ CenterAttachment.unattached R attach) := by
  apply CenterAttachment.preserves_minimum R S PublicQuotient.identity attach G hS _ hout
  intro u v huv
  change u = v at huv
  rw [huv]

theorem outsideQuotient_card_le (R B : Finset V) (attach : V → Option R)
    (hout : ∀ v, v ∉ R → attach v = none → v ∈ B) :
    Fintype.card (R ⊕ CenterAttachment.unattached R attach) ≤ R.card + B.card := by
  rw [CenterAttachment.card_labels, Fintype.card_coe]
  exact Nat.add_le_add_left ((CenterAttachment.unattached_card_le R B attach hout).trans
    (card_le_card sdiff_subset)) _

theorem outsideQuotient_guard (R B : Finset V) (d : ℕ) (attach : V → Option R)
    (hd : Schedule.degreeCutoff ≤ d)
    (hc : Schedule.CenterGuard (Fintype.card V) d R.card)
    (hb : Schedule.BadGuard (Fintype.card V) d B.card)
    (hout : ∀ v, v ∉ R → attach v = none → v ∈ B) :
    (Fintype.card (R ⊕ CenterAttachment.unattached R attach) : ℝ) * d ≤
      300001 * Fintype.card V * Real.log d :=
  Schedule.high_component_guard (Fintype.card V) d R.card B.card _ hd hc hb
    (outsideQuotient_card_le R B attach hout)

/-- The high-degree branch's actual public one-out sampler preserves the
original optimum and passes the literal quotient-size guard on one event. -/
theorem outsideDraws_quotient_success (R B S : Finset V) (d : ℕ)
    (N : (univ \ (R ∪ B) : Finset V) → Finset R)
    (G : WeightedGraph V) (hS : IsMinCut G S) (hd : Schedule.degreeCutoff ≤ d)
    (hc : Schedule.CenterGuard (Fintype.card V) d R.card)
    (hb : Schedule.BadGuard (Fintype.card V) d B.card)
    (hN : ∀ u, (N u).Nonempty)
    (hmax : ∀ u, CenterAttachment.outsideRatio (univ \ (R ∪ B)) R S N u ≤ 7 / 10)
    (hsum : (∑ u, CenterAttachment.outsideRatio (univ \ (R ∪ B)) R S N u) ≤ 80) :
    ENNReal.ofReal ((3 / 10 : ℝ) ^ 115) ≤
      mass (CenterAttachment.outsideDraws (univ \ (R ∪ B)) R N) (fun attach =>
        IsMinCut ((outsideQuotient R attach).graph G) (S.image (outsideQuotient R attach).map) ∧
        mincutValue ((outsideQuotient R attach).graph G) = mincutValue G ∧
        2 ≤ Fintype.card (R ⊕ CenterAttachment.unattached R attach) ∧
        (Fintype.card (R ⊕ CenterAttachment.unattached R attach) : ℝ) * d ≤
          300001 * Fintype.card V * Real.log d) := by
  apply (CenterAttachment.outsideDraws_avoidance_complete R B S N hN hmax hsum).trans
  apply mass_mono
  intro attach ha
  have havoid : ∀ v, v ∉ R → ∀ u, attach v = some u → (v ∈ S ↔ u.val ∈ S) := by
    intro v _ u hu
    have hv := ha.1 v
    simpa only [hu,Option.elim_some] using hv
  have hpres := outsideQuotient_preserves R S attach G hS havoid
  exact ⟨hpres.1,hpres.2.1,hpres.2.2,outsideQuotient_guard R B d attach hd hc hb ha.2⟩

/-- The high-degree public continuation samples outside attachments after
the complete learned transcript and preserves the prefix query budget. -/
def outsideAttachmentAfter {T : Type} {q : ℕ}
    (before : RTree (Finset V) ℝ T q) (R B : Finset V)
    (rows : T → (univ \ (R ∪ B) : Finset V) → Finset R) :
    RTree (Finset V) ℝ (T × (V → Option R)) q :=
  (before.bind fun transcript =>
    RTree.map (fun attach => (transcript,attach))
      (CenterAttachment.outsideDrawsProgram (univ \ (R ∪ B)) R (rows transcript))).cast
        (Nat.add_zero q)

theorem outsideAttachmentAfter_eval {T : Type} {q : ℕ}
    (before : RTree (Finset V) ℝ T q) (R B : Finset V)
    (rows : T → (univ \ (R ∪ B) : Finset V) → Finset R)
    (read : Finset V → ℝ) :
    (outsideAttachmentAfter before R B rows).eval read =
      (before.eval read).bind fun transcript =>
        (CenterAttachment.outsideDraws (univ \ (R ∪ B)) R (rows transcript)).map
          fun attach => (transcript,attach) := by
  simp only [outsideAttachmentAfter, RTree.eval_cast, RTree.eval_bind,
    RTree.eval_map, CenterAttachment.outsideDrawsProgram_eval]

/-- High-degree success is integrated over the actual prefix law. No
conditioning on a global recovery cap or independence of learned rows occurs. -/
theorem outsideAttachmentAfter_success {T : Type} {q : ℕ}
    (before : RTree (Finset V) ℝ T q) (R B S : Finset V) (d : ℕ)
    (rows : T → (univ \ (R ∪ B) : Finset V) → Finset R)
    (G : WeightedGraph V) (hS : IsMinCut G S) (hd : Schedule.degreeCutoff ≤ d)
    (hc : Schedule.CenterGuard (Fintype.card V) d R.card)
    (hb : Schedule.BadGuard (Fintype.card V) d B.card) (Good : T → Prop)
    (hgood : ∀ t ∈ (before.eval G.cut).support, Good t →
      (∀ u, (rows t u).Nonempty) ∧
      (∀ u, CenterAttachment.outsideRatio (univ \ (R ∪ B)) R S (rows t) u ≤ 7 / 10) ∧
      (∑ u, CenterAttachment.outsideRatio (univ \ (R ∪ B)) R S (rows t) u) ≤ 80) :
    mass (before.eval G.cut) Good * ENNReal.ofReal ((3 / 10 : ℝ) ^ 115) ≤
      mass ((outsideAttachmentAfter before R B rows).eval G.cut) (fun out =>
        Good out.1 ∧
        IsMinCut ((outsideQuotient R out.2).graph G) (S.image (outsideQuotient R out.2).map) ∧
        mincutValue ((outsideQuotient R out.2).graph G) = mincutValue G ∧
        2 ≤ Fintype.card (R ⊕ CenterAttachment.unattached R out.2) ∧
        (Fintype.card (R ⊕ CenterAttachment.unattached R out.2) : ℝ) * d ≤
          300001 * Fintype.card V * Real.log d) := by
  rw [outsideAttachmentAfter_eval]
  apply attachment_mass_bind_ge (before.eval G.cut)
    (fun t => (CenterAttachment.outsideDraws (univ \ (R ∪ B)) R (rows t)).map
      fun attach => (t,attach)) Good _ _
  intro t ht hg
  rcases hgood t ht hg with ⟨hN,hmax,hsum⟩
  rw [mass_map]
  apply (outsideDraws_quotient_success R B S d (rows t) G hS hd hc hb hN hmax hsum).trans
  apply mass_mono
  exact fun attach ha => ⟨hg,ha⟩


#print axioms CenterAttachment.quotient
#print axioms CenterAttachment.respects
#print axioms CenterAttachment.card_labels_le
#print axioms CenterAttachment.preserves_minimum
#print axioms CenterAttachment.outsideDraws_avoidance_mass
#print axioms CenterAttachment.outsideRatio_true_subrow
#print axioms CenterAttachment.outsideDrawsProgram_eval
#print axioms CenterAttachment.outsideDraws_avoidance_lower
#print axioms CenterAttachment.outsideDraws_support
#print axioms CenterAttachment.outsideDraws_unattached
#print axioms CenterAttachment.outsideDraws_ratio_avoidance
#print axioms CenterAttachment.outsideDraws_avoidance_complete
#print axioms CenterAttachment.outsideDraws_edges
#print axioms CenterAttachment.afterOutsideTranscript_avoidance
#print axioms CenterAttachment.afterOutsideTranscript_complete
#print axioms composedQuotient_preserves
#print axioms composedQuotient_card_le
#print axioms composedQuotient_guard
#print axioms centerDraws_good
#print axioms componentAttachmentDraws_success
#print axioms componentAttachmentAfter_eval
#print axioms componentAttachmentAfter_success
#print axioms outsideQuotient_preserves
#print axioms outsideQuotient_card_le
#print axioms outsideQuotient_guard
#print axioms outsideDraws_quotient_success
#print axioms outsideAttachmentAfter_eval
#print axioms outsideAttachmentAfter_success

end
end CutQueryComplexity.StarContraction2022.Contraction.Joint
