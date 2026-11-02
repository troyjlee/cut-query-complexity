import CutQueryComplexity.StarContraction2022.Certificates.ParallelState
import CutQueryComplexity.StarContraction2022.Probability.Product
import CutQueryComplexity.StarContraction2022.Recovery.Decode
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Actual star-batch insertion and component progress

A round learns at most one outgoing edge from each red finest component, with
the other endpoint blue. We prove that the implemented first-available-layer
insertion accepts every such edge, even while all layers are changing. This is
the combinatorial part of the progress analysis, not an assumed drift bound.
-/

set_option autoImplicit false

namespace CutQueryComplexity.StarContraction2022.Certificates

noncomputable section
open scoped Classical ENNReal

variable {V Q : Type} [Fintype V] [DecidableEq V] [Fintype Q] [DecidableEq Q]
variable {π : PublicQuotient V Q} {r : ℕ}

/-- A public set is closed under the actual graph edges. -/
def Closed (F : _root_.SimpleGraph Q) (A : Finset Q) : Prop :=
  ∀ u ∈ A, ∀ v, F.Adj u v → v ∈ A

theorem forestBlock_closed (F : _root_.SimpleGraph Q) (a : Q) :
    Closed F (forestBlock F a) := by
  intro u hu v huv
  exact (mem_forestBlock _ _ _).mpr (((mem_forestBlock _ _ _).mp hu).trans huv.reachable)

theorem Closed.not_reachable {F : _root_.SimpleGraph Q} {A : Finset Q}
    (h : Closed F A) {u v : Q} (hu : u ∈ A) (hv : v ∉ A) : ¬F.Reachable u v := by
  intro hr
  exact hv (reachable_mem_of_closed F A h hu hr)

theorem Closed.sup_edge {F : _root_.SimpleGraph Q} {A : Finset Q} (h : Closed F A)
    {a b : Q} (ha : a ∉ A) (hb : b ∉ A) :
    Closed (F ⊔ _root_.SimpleGraph.edge a b) A := by
  intro u hu v huv
  rcases huv with hf | he
  · exact h u hu v hf
  · rcases (_root_.SimpleGraph.edge_adj ..).mp he with ⟨hh | hh, _⟩
    · exact (ha (hh.1 ▸ hu)).elim
    · exact (hb (hh.1 ▸ hu)).elim

private theorem forestSum_connected (Fs : List (_root_.SimpleGraph Q))
    (F : _root_.SimpleGraph Q)
    (h : ∀ H ∈ Fs, ∀ u v, H.Reachable u v → F.Reachable u v)
    {u v : Q} (hp : 0 < (forestSum Fs).w u v) : F.Reachable u v := by
  induction Fs with
  | nil => simp at hp
  | cons H Fs ih =>
      by_cases hadj : H.Adj u v
      · exact h H (by simp) u v hadj.reachable
      · have ht : 0 < (forestSum Fs).w u v := by
          simpa only [forestSum_cons, WeightedGraph.add_w, SimpleGraph.toWeighted_w,
            hadj, ite_false, zero_add] using hp
        exact ih (fun K hK => h K (by simp [hK])) ht

private theorem reachable_of_positive (G : WeightedGraph Q) (F : _root_.SimpleGraph Q)
    (h : ∀ u v, 0 < G.w u v → F.Reachable u v) {u v : Q}
    (huv : G.support.Reachable u v) : F.Reachable u v := by
  obtain ⟨p⟩ := huv
  induction p with
  | nil => exact .rfl
  | @cons u w v huw p ih =>
      exact (h u w (lt_of_le_of_ne (G.nonneg u w) (Ne.symm huw))).trans ih

/-- Laminar forests that exhaust all crossing residual edges are actually a
sequence of residual spanning forests. Later assigned edges are included in
the argument, so this does not confuse the final residual with each prefix. -/
theorem residualForestChain_of_closed (G : WeightedGraph Q)
    (Fs : List (_root_.SimpleGraph Q))
    (hacyclic : ∀ F ∈ Fs, F.IsAcyclic)
    (hlaminar : Fs.Pairwise (fun F H => ∀ u v, H.Reachable u v → F.Reachable u v))
    (hsub : (forestSum Fs).IsSubgraph G)
    (hclosed : ∀ F ∈ Fs, ∀ u v,
      0 < (G.subtract (forestSum Fs)).w u v → F.Reachable u v) :
    ResidualForestChain G Fs := by
  induction Fs generalizing G with
  | nil => trivial
  | cons F Fs ih =>
      obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hlaminar
      let K := SimpleGraph.toWeighted F
      have hK : K.IsSubgraph G := by
        intro u v
        have hh := hsub u v
        change K.w u v + (forestSum Fs).w u v ≤ G.w u v at hh
        linarith [(forestSum Fs).nonneg u v]
      have hs : (forestSum Fs).IsSubgraph (G.subtract K) := by
        intro u v
        have hh := hsub u v
        change K.w u v + (forestSum Fs).w u v ≤ G.w u v at hh
        change (forestSum Fs).w u v ≤ max 0 (G.w u v - K.w u v)
        exact (show (forestSum Fs).w u v ≤ G.w u v - K.w u v by linarith).trans
          (le_max_right _ _)
      have hres : (G.subtract K).subtract (forestSum Fs) =
          G.subtract (forestSum (F :: Fs)) := by
        ext u v
        have hh := hsub u v
        change K.w u v + (forestSum Fs).w u v ≤ G.w u v at hh
        have hk := hK u v
        change max 0 (max 0 (G.w u v - K.w u v) - (forestSum Fs).w u v) =
          max 0 (G.w u v - (K.w u v + (forestSum Fs).w u v))
        rw [max_eq_right (by linarith : 0 ≤ G.w u v - K.w u v)]
        congr 1
        ring
      have hconn : ∀ u v, 0 < G.w u v → F.Reachable u v := by
        intro u v hp
        by_cases hsum : 0 < (forestSum (F :: Fs)).w u v
        · apply forestSum_connected (F :: Fs) F ?_ hsum
          intro H hH a b hab
          rcases List.mem_cons.mp hH with rfl | hH
          · exact hab
          · exact hhead H hH a b hab
        · have hz : (forestSum (F :: Fs)).w u v = 0 :=
            le_antisymm (le_of_not_gt hsum) ((forestSum (F :: Fs)).nonneg u v)
          apply hclosed F (by simp) u v
          change 0 < max 0 (G.w u v - (forestSum (F :: Fs)).w u v)
          rw [hz, sub_zero, max_eq_right (G.nonneg u v)]
          exact hp
      refine ⟨⟨?_, hacyclic F (by simp), ?_⟩, ?_⟩
      · intro u v huv
        have hh := hK u v
        have hw : K.w u v = 1 := by simp [K, SimpleGraph.toWeighted_w, huv]
        change G.w u v ≠ 0
        rw [hw] at hh
        linarith
      · intro u v huv
        exact reachable_of_positive G F hconn huv
      · apply ih (G.subtract K) (fun H hH => hacyclic H (by simp [hH])) htail hs
        intro H hH u v hp
        rw [hres] at hp
        exact hclosed H (by simp [hH]) u v hp

namespace ParallelState

/-- Remaining original edges stay inside the finest current component. -/
def ResidualClosed (s : ParallelState π r) (hr : 0 < r) (G : WeightedGraph V) : Prop :=
  ∀ u v, 0 < (G.subtract s.usedGraph).w u v →
    (s.forests (lastIndex hr)).quotient.Reachable (π.map u) (π.map v)

theorem residualClosed_of_retired (s : ParallelState π r) (hr : 0 < r)
    (G : WeightedGraph V) (hi : s.InactiveSound hr G) (hall : s.inactive = Finset.univ) :
    s.ResidualClosed hr G := by
  intro u v hp
  by_contra hnot
  have hu : u ∈ s.inactive := by rw [hall]; exact Finset.mem_univ u
  have hz := hi u hu v (by simpa only [mem_lastBlock] using hnot)
  linarith

theorem residual_contract (s : ParallelState π r) (G : WeightedGraph V)
    (hsub : s.usedGraph.IsSubgraph G) :
    π.graph (G.subtract s.usedGraph) = (π.graph G).subtract s.quotientGraph := by
  have hquot := s.quotientGraph_subgraph G hsub
  have hcuts (S : Finset Q) : (π.graph (G.subtract s.usedGraph)).cut S =
      ((π.graph G).subtract s.quotientGraph).cut S := by
    rw [π.cut_graph, G.cut_subtract s.usedGraph hsub,
      (π.graph G).cut_subtract s.quotientGraph hquot, π.cut_graph,
      ← s.usedGraph_contract, π.cut_graph]
  ext u v
  by_cases huv : u = v
  · subst v
    simp [WeightedGraph.diag]
  · have hd : Disjoint ({u} : Finset Q) {v} := by simpa using huv
    have ha := (π.graph (G.subtract s.usedGraph)).cross_eq_three_cuts hd
    have hb := ((π.graph G).subtract s.quotientGraph).cross_eq_three_cuts hd
    simp only [WeightedGraph.cross, Finset.sum_singleton] at ha hb
    rw [hcuts {u}, hcuts {v}, hcuts ({u} ∪ {v})] at ha
    exact ha.trans hb.symm

/-- Closure of the original residual supplies the actual prefix-spanning
condition for every layer. No residual-spanning certificate is assumed. -/
theorem complete_of_residualClosed (s : ParallelState π r) (hr : 0 < r)
    (G : WeightedGraph V) (hsub : s.usedGraph.IsSubgraph G) (hl : s.Laminar)
    (hc : s.ResidualClosed hr G) : s.Complete G := by
  apply residualForestChain_of_closed (π.graph G) s.layerList
  · rw [layerList, List.forall_mem_ofFn_iff]
    exact fun i => (s.forests i).acyclic
  · rw [layerList, List.pairwise_ofFn]
    intro i j hij u v huv
    exact hl i j (le_of_lt hij) u v huv
  · rw [← s.quotientGraph_eq_forestSum]
    exact s.quotientGraph_subgraph G hsub
  · rw [layerList, List.forall_mem_ofFn_iff]
    intro i u v hp
    change 0 < ((π.graph G).subtract (forestSum s.layerList)).w u v at hp
    rw [← s.quotientGraph_eq_forestSum, ← s.residual_contract G hsub] at hp
    have huv : u ≠ v := by
      intro he
      subst v
      simpa only [WeightedGraph.diag, lt_self_iff_false] using hp
    change 0 < (if u = v then 0 else
      (G.subtract s.usedGraph).cross (WeightedGraph.fiber π.map u)
        (WeightedGraph.fiber π.map v)) at hp
    rw [if_neg huv] at hp
    obtain ⟨a, ha, b, hb, hab⟩ := ((G.subtract s.usedGraph).cross_pos_iff _ _).mp hp
    have hai : π.map a = u := (WeightedGraph.mem_fiber _ _ _).mp ha
    have hbi : π.map b = v := (WeightedGraph.mem_fiber _ _ _).mp hb
    have hilast : i ≤ lastIndex hr := by
      change i.val ≤ r - 1
      omega
    simpa only [hai, hbi] using hl i (lastIndex hr) hilast _ _ (hc a b hab)

theorem certificate_of_retired (s : ParallelState π r) (hr : 0 < r)
    (G : WeightedGraph V) (hG : G.IsIntegral) (hsub : s.usedGraph.IsSubgraph G)
    (hl : s.Laminar) (hi : s.InactiveSound hr G) (hall : s.inactive = Finset.univ) :
    IsThresholdCertificate r (π.graph G) s.quotientGraph :=
  s.complete_certificate G hG (s.complete_of_residualClosed hr G hsub hl
    (s.residualClosed_of_retired hr G hi hall))

/-- Actual original-vertex blocks of one quotient forest. -/
def blocks (s : ParallelState π r) (i : Fin r) : Finset (Finset V) :=
  Finset.univ.image (fun q => π.lift (forestBlock (s.forests i).quotient q))

def block (s : ParallelState π r) (i : Fin r) (v : V) : Finset V :=
  π.lift (forestBlock (s.forests i).quotient (π.map v))

/-- Only blocks containing a nonretired original vertex enter the progress potential. -/
def liveBlocks (s : ParallelState π r) (i : Fin r) : Finset (Finset V) :=
  (s.blocks i).filter (fun B => ∃ v ∈ B, v ∉ s.inactive)

theorem liveBlocks_card_le (s : ParallelState π r) (i : Fin r) :
    (s.liveBlocks i).card ≤ Fintype.card Q := by
  exact (Finset.card_filter_le _ _).trans
    ((Finset.card_image_le).trans_eq (Finset.card_univ))

@[simp] theorem mem_block (s : ParallelState π r) (i : Fin r) (v w : V) :
    w ∈ s.block i v ↔ (s.forests i).quotient.Reachable (π.map v) (π.map w) := by
  simp [block]

theorem block_mem_live (s : ParallelState π r) (i : Fin r) {v : V}
    (hv : v ∉ s.inactive) : s.block i v ∈ s.liveBlocks i := by
  apply Finset.mem_filter.mpr
  refine ⟨?_, ⟨v, by simp, hv⟩⟩
  exact Finset.mem_image.mpr ⟨π.map v, Finset.mem_univ _, rfl⟩

theorem block_eq_of_mem (s : ParallelState π r) (i : Fin r) {B : Finset V}
    (hB : B ∈ s.blocks i) {v : V} (hv : v ∈ B) : s.block i v = B := by
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hB
  have hqv : (s.forests i).quotient.Reachable q (π.map v) := by simpa using hv
  ext w
  simp only [mem_block, PublicQuotient.mem_lift, mem_forestBlock]
  exact ⟨fun h => hqv.trans h, fun h => hqv.symm.trans h⟩

theorem block_eq_of_reachable (s : ParallelState π r) (i : Fin r) {v w : V}
    (h : (s.forests i).quotient.Reachable (π.map v) (π.map w)) :
    s.block i v = s.block i w := by
  ext u
  simp only [mem_block]
  exact ⟨fun hu => h.symm.trans hu, fun hu => h.trans hu⟩

/-- Laminarity bounds the actual live component count of every earlier layer
by that of a later layer. Inactive components are not counted as live. -/
theorem liveBlocks_card_mono (s : ParallelState π r) (hs : s.Laminar)
    (i j : Fin r) (hij : i ≤ j) : (s.liveBlocks i).card ≤ (s.liveBlocks j).card := by
  let left := {B : Finset V // B ∈ s.liveBlocks i}
  let right := {B : Finset V // B ∈ s.liveBlocks j}
  have chooseVertex (k : Fin r) (B : {B : Finset V // B ∈ s.liveBlocks k}) :
      ∃ v, v ∈ B.val ∧ v ∉ s.inactive := (Finset.mem_filter.mp B.property).2
  let representative (k : Fin r) (B : {B : Finset V // B ∈ s.liveBlocks k}) : V :=
    Classical.choose (chooseVertex k B)
  have rep_mem (k : Fin r) (B : {B : Finset V // B ∈ s.liveBlocks k}) :
      representative k B ∈ B.val ∧ representative k B ∉ s.inactive :=
    Classical.choose_spec (chooseVertex k B)
  let f : right → left := fun B =>
    ⟨s.block i (representative j B), s.block_mem_live i (rep_mem j B).2⟩
  have hf : Function.Surjective f := by
    intro B
    let v := representative i B
    let A : right := ⟨s.block j v, s.block_mem_live j (rep_mem i B).2⟩
    refine ⟨A, ?_⟩
    apply Subtype.ext
    have hvw : (s.forests j).quotient.Reachable (π.map v) (π.map (representative j A)) :=
      (s.mem_block j v _).mp (rep_mem j A).1
    have he : s.block i v = s.block i (representative j A) :=
      s.block_eq_of_reachable i (hs i j hij _ _ hvw)
    have hb : s.block i v = B.val :=
      s.block_eq_of_mem i (Finset.mem_filter.mp B.property).1 (rep_mem i B).1
    exact he.symm.trans hb
  simpa only [left, right, Fintype.card_coe] using Fintype.card_le_of_surjective f hf

def livePotential (s : ParallelState π r) : ℕ := ∑ i, (s.liveBlocks i).card

theorem livePotential_le (s : ParallelState π r) (hr : 0 < r) (hs : s.Laminar) :
    s.livePotential ≤ r * (s.liveBlocks (lastIndex hr)).card := by
  calc
    s.livePotential ≤ ∑ _i : Fin r, (s.liveBlocks (lastIndex hr)).card := by
      apply Finset.sum_le_sum
      intro i hi
      apply s.liveBlocks_card_mono hs i (lastIndex hr)
      change i.val ≤ r - 1
      omega
    _ = _ := by simp

/-- A representative is chosen from the actual public live block. Its choice
uses neither residual capacities nor any hidden graph. -/
def liveRepresentative (s : ParallelState π r) (i : Fin r)
    (B : {B : Finset V // B ∈ s.liveBlocks i}) : V :=
  Classical.choose ((Finset.mem_filter.mp B.property).2)

theorem liveRepresentative_spec (s : ParallelState π r) (i : Fin r)
    (B : {B : Finset V // B ∈ s.liveBlocks i}) :
    s.liveRepresentative i B ∈ B.val ∧ s.liveRepresentative i B ∉ s.inactive :=
  Classical.choose_spec ((Finset.mem_filter.mp B.property).2)

theorem block_representative (s : ParallelState π r) (i : Fin r)
    (B : {B : Finset V // B ∈ s.liveBlocks i}) :
    s.block i (s.liveRepresentative i B) = B.val :=
  s.block_eq_of_mem i (Finset.mem_filter.mp B.property).1
    (s.liveRepresentative_spec i B).1

theorem block_eq_iff (s : ParallelState π r) (i : Fin r) (u v : V) :
    s.block i u = s.block i v ↔
      (s.forests i).quotient.Reachable (π.map u) (π.map v) := by
  refine ⟨?_, s.block_eq_of_reachable i⟩
  intro he
  have hv : v ∈ s.block i u := by rw [he]; simp
  exact (s.mem_block i u v).mp hv

/-- Merging components or retiring vertices cannot create additional live
blocks. The proof injects each new live block into an old one. -/
theorem liveBlocks_card_mono_of (s t : ParallelState π r) (i : Fin r)
    (hi : s.inactive ⊆ t.inactive)
    (hr : ∀ u v, (s.forests i).quotient.Reachable u v →
      (t.forests i).quotient.Reachable u v) :
    (t.liveBlocks i).card ≤ (s.liveBlocks i).card := by
  let f : {B : Finset V // B ∈ t.liveBlocks i} →
      {B : Finset V // B ∈ s.liveBlocks i} := fun B =>
    ⟨s.block i (t.liveRepresentative i B),
      s.block_mem_live i (fun h => (t.liveRepresentative_spec i B).2 (hi h))⟩
  have hf : Function.Injective f := by
    intro A B hab
    have hh : s.block i (t.liveRepresentative i A) =
        s.block i (t.liveRepresentative i B) := congrArg Subtype.val hab
    have hconn := hr _ _ ((s.block_eq_iff i _ _).mp hh)
    have he := t.block_eq_of_reachable i hconn
    rw [t.block_representative i A, t.block_representative i B] at he
    exact Subtype.ext he
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hf

/-- A genuine merge of two distinct live components strictly decreases the
live count. Isolated components do not enter either side of this estimate. -/
theorem liveBlocks_card_lt_of_merge (s t : ParallelState π r) (i : Fin r)
    (hi : t.inactive = s.inactive)
    (hr : ∀ u v, (s.forests i).quotient.Reachable u v →
      (t.forests i).quotient.Reachable u v)
    {u v : V} (hu : u ∉ s.inactive) (hv : v ∉ s.inactive)
    (hold : ¬(s.forests i).quotient.Reachable (π.map u) (π.map v))
    (hnew : (t.forests i).quotient.Reachable (π.map u) (π.map v)) :
    (t.liveBlocks i).card < (s.liveBlocks i).card := by
  let f : {B : Finset V // B ∈ s.liveBlocks i} →
      {B : Finset V // B ∈ t.liveBlocks i} := fun B =>
    ⟨t.block i (s.liveRepresentative i B),
      t.block_mem_live i (by simpa only [hi] using (s.liveRepresentative_spec i B).2)⟩
  have hmap (B : {B : Finset V // B ∈ s.liveBlocks i}) {w : V}
      (hw : w ∈ B.val) : (f B).val = t.block i w := by
    have hB := s.block_representative i B
    have hw' : w ∈ s.block i (s.liveRepresentative i B) := hB.symm ▸ hw
    exact t.block_eq_of_reachable i (hr _ _ ((s.mem_block i _ w).mp hw'))
  have hsurj : Function.Surjective f := by
    intro B
    let w := t.liveRepresentative i B
    have hw : w ∉ s.inactive := by simpa only [hi] using (t.liveRepresentative_spec i B).2
    let A : {B : Finset V // B ∈ s.liveBlocks i} :=
      ⟨s.block i w, s.block_mem_live i hw⟩
    refine ⟨A, Subtype.ext ?_⟩
    calc
      (f A).val = t.block i w := hmap A (by simp [A])
      _ = B.val := t.block_representative i B
  have hnotinj : ¬Function.Injective f := by
    intro hinj
    let A : {B : Finset V // B ∈ s.liveBlocks i} :=
      ⟨s.block i u, s.block_mem_live i hu⟩
    let B : {B : Finset V // B ∈ s.liveBlocks i} :=
      ⟨s.block i v, s.block_mem_live i hv⟩
    have he : f A = f B := by
      apply Subtype.ext
      rw [hmap A (w := u) (by simp [A]), hmap B (w := v) (by simp [B])]
      exact t.block_eq_of_reachable i hnew
    have hab : s.block i u = s.block i v := congrArg Subtype.val (hinj he)
    exact hold ((s.block_eq_iff i u v).mp hab)
  simpa only [Fintype.card_coe] using Fintype.card_lt_of_surjective_not_injective f hsurj hnotinj

/-- Both endpoints of a positive residual edge crossing the finest component
are active. This is derived from honest retirement, not a discovery premise. -/
theorem positive_endpoints_active (s : ParallelState π r) (hr : 0 < r)
    (G : WeightedGraph V) (hi : s.InactiveSound hr G) {u v : V}
    (hcross : ¬(s.forests (lastIndex hr)).quotient.Reachable (π.map u) (π.map v))
    (hp : 0 < (G.subtract s.usedGraph).w u v) :
    u ∉ s.inactive ∧ v ∉ s.inactive := by
  refine ⟨?_, ?_⟩
  · intro hu
    have hz := hi u hu v (by simpa only [mem_lastBlock] using hcross)
    linarith
  · intro hv
    have hz := hi v hv u (by
      simp only [mem_lastBlock]
      exact fun h => hcross h.symm)
    rw [WeightedGraph.symm] at hz
    linarith

theorem insertAt_livePotential (s : ParallelState π r) (i : Fin r)
    (e : OriginalEdge π) (hn)
    (hu : e.val.1 ∉ s.inactive) (hv : e.val.2 ∉ s.inactive) :
    (s.insertAt i e hn).livePotential + 1 ≤ s.livePotential := by
  have hstrict : ((s.insertAt i e hn).liveBlocks i).card < (s.liveBlocks i).card := by
    apply s.liveBlocks_card_lt_of_merge (s.insertAt i e hn) i rfl
      (fun _ _ h => s.insertAt_reachable i e hn i h) hu hv hn
    have he : (_root_.SimpleGraph.edge (π.map e.val.1) (π.map e.val.2)).Adj
        (π.map e.val.1) (π.map e.val.2) :=
      (_root_.SimpleGraph.edge_adj ..).mpr ⟨Or.inl ⟨rfl, rfl⟩, e.property⟩
    simpa only [insertAt, Function.update_self, EndpointForest.extend_quotient,
      OriginalEdge.quotientGraph] using
      he.reachable.mono (show _root_.SimpleGraph.edge (π.map e.val.1) (π.map e.val.2) ≤
        (s.forests i).quotient ⊔ _root_.SimpleGraph.edge (π.map e.val.1) (π.map e.val.2)
        from le_sup_right)
  apply Nat.succ_le_of_lt
  apply Finset.sum_lt_sum
  · intro j hj
    exact s.liveBlocks_card_mono_of (s.insertAt i e hn) j (fun _ h => h)
      (fun _ _ h => s.insertAt_reachable i e hn j h)
  · exact ⟨i, Finset.mem_univ i, hstrict⟩

theorem insertFirst_livePotential (s : ParallelState π r) (e : OriginalEdge π)
    {t : ParallelState π r} (ht : s.insertFirst e = some t)
    (hu : e.val.1 ∉ s.inactive) (hv : e.val.2 ∉ s.inactive) :
    t.livePotential + 1 ≤ s.livePotential := by
  unfold insertFirst at ht
  split at ht
  next h =>
    cases Option.some.inj ht
    exact s.insertAt_livePotential _ e _ hu hv
  next h => cases ht

theorem retire_livePotential (s : ParallelState π r) (v : V) :
    (s.retire v).livePotential ≤ s.livePotential := by
  apply Finset.sum_le_sum
  intro i hi
  exact s.liveBlocks_card_mono_of (s.retire v) i (s.retire_mono v) (fun _ _ h => h)

theorem insertFirst_exists (s : ParallelState π r) (e : OriginalEdge π)
    (i : Fin r)
    (hi : ¬(s.forests i).quotient.Reachable (π.map e.val.1) (π.map e.val.2)) :
    ∃ t, s.insertFirst e = some t := by
  have hne : (s.available e).Nonempty := ⟨i, by simp [available, hi]⟩
  refine ⟨s.insertAt (s.firstIndex e hne) e (s.firstIndex_available e hne), ?_⟩
  simp only [insertFirst, dif_pos hne]

theorem insertAt_closed (s : ParallelState π r) (i j : Fin r) (e : OriginalEdge π) (hn)
    {A : Finset Q} (hA : Closed (s.forests j).quotient A)
    (hsrc : π.map e.val.1 ∉ A) (hdst : π.map e.val.2 ∉ A) :
    Closed ((s.insertAt i e hn).forests j).quotient A := by
  by_cases hji : j = i
  · subst j
    simpa [insertAt, OriginalEdge.quotientGraph] using hA.sup_edge hsrc hdst
  · simpa [insertAt, hji] using hA

theorem insertFirst_closed (s : ParallelState π r) (e : OriginalEdge π)
    {t : ParallelState π r} (ht : s.insertFirst e = some t) (j : Fin r)
    {A : Finset Q} (hA : Closed (s.forests j).quotient A)
    (hsrc : π.map e.val.1 ∉ A) (hdst : π.map e.val.2 ∉ A) :
    Closed (t.forests j).quotient A := by
  unfold insertFirst at ht
  split at ht
  next h =>
    cases Option.some.inj ht
    exact s.insertAt_closed _ j e _ hA hsrc hdst
  next h => cases ht

/-- Process the actual learned list; each edge is placed in its least legal layer. -/
def insertBatch (s : ParallelState π r) : List (OriginalEdge π) → Option (ParallelState π r)
  | [] => some s
  | e :: es => (s.insertFirst e).bind fun t => t.insertBatch es

theorem insertFirst_inactive (s : ParallelState π r) (e : OriginalEdge π)
    {t : ParallelState π r} (ht : s.insertFirst e = some t) : t.inactive = s.inactive := by
  unfold insertFirst at ht
  split at ht
  next h => cases Option.some.inj ht; rfl
  next h => cases ht

theorem insertFirst_failed (s : ParallelState π r) (e : OriginalEdge π)
    {t : ParallelState π r} (ht : s.insertFirst e = some t) : t.failed = s.failed := by
  unfold insertFirst at ht
  split at ht
  next h => cases Option.some.inj ht; rfl
  next h => cases ht

theorem insertBatch_inactive (s : ParallelState π r) (es : List (OriginalEdge π))
    {t : ParallelState π r} (ht : s.insertBatch es = some t) : t.inactive = s.inactive := by
  induction es generalizing s with
  | nil => exact congrArg ParallelState.inactive (Option.some.inj ht).symm
  | cons e es ih =>
      cases he : s.insertFirst e with
      | none => simp [insertBatch, he] at ht
      | some u =>
          have htail : u.insertBatch es = some t := by simpa [insertBatch, he] using ht
          exact (ih u htail).trans (s.insertFirst_inactive e he)

theorem insertFirst_usedGraph (s : ParallelState π r) (e : OriginalEdge π)
    {t : ParallelState π r} (ht : s.insertFirst e = some t) :
    t.usedGraph = s.usedGraph.add e.graph := by
  unfold insertFirst at ht
  split at ht
  next h => cases Option.some.inj ht; exact s.insertAt_usedGraph _ e _
  next h => cases ht

theorem insertFirst_honest (s : ParallelState π r) (e : OriginalEdge π)
    {t : ParallelState π r} (ht : s.insertFirst e = some t)
    (G : SimpleInput V) (hs : s.usedGraph.IsSubgraph G.toWeighted)
    (hp : 0 < (G.toWeighted.subtract s.usedGraph).w e.val.1 e.val.2) :
    t.usedGraph.IsSubgraph G.toWeighted := by
  unfold insertFirst at ht
  split at ht
  next h => cases Option.some.inj ht; exact s.insertAt_honest _ e _ G hs hp
  next h => cases ht

theorem insertFirst_inactiveSound (s : ParallelState π r) (e : OriginalEdge π)
    {t : ParallelState π r} (ht : s.insertFirst e = some t)
    (hr : 0 < r) (G : WeightedGraph V) (hi : s.InactiveSound hr G) :
    t.InactiveSound hr G := by
  unfold insertFirst at ht
  split at ht
  next h => cases Option.some.inj ht; exact s.insertAt_inactiveSound _ e _ hr G hi
  next h => cases ht

theorem insertBatch_inactiveSound (s : ParallelState π r) (es : List (OriginalEdge π))
    {t : ParallelState π r} (ht : s.insertBatch es = some t)
    (hr : 0 < r) (G : WeightedGraph V) (hi : s.InactiveSound hr G) :
    t.InactiveSound hr G := by
  induction es generalizing s with
  | nil => exact (Option.some.inj ht) ▸ hi
  | cons e es ih =>
      cases he : s.insertFirst e with
      | none => simp [insertBatch, he] at ht
      | some u =>
          have htail : u.insertBatch es = some t := by simpa [insertBatch, he] using ht
          exact ih u htail (s.insertFirst_inactiveSound e he hr G hi)

/-- Earlier red sources and their blue destinations cannot be a later red
source. Thus the next edge is still available in the original residual. -/
theorem insertBatch_honest (s : ParallelState π r) (es : List (OriginalEdge π))
    {t : ParallelState π r} (ht : s.insertBatch es = some t)
    (G : SimpleInput V) (hs : s.usedGraph.IsSubgraph G.toWeighted)
    (hp : ∀ e ∈ es, 0 < (G.toWeighted.subtract s.usedGraph).w e.val.1 e.val.2)
    (hd : es.Pairwise (fun e f => e.val.1 ≠ f.val.1 ∧ e.val.2 ≠ f.val.1)) :
    t.usedGraph.IsSubgraph G.toWeighted := by
  induction es generalizing s with
  | nil => exact (Option.some.inj ht) ▸ hs
  | cons e es ih =>
      cases he : s.insertFirst e with
      | none => simp [insertBatch, he] at ht
      | some u =>
          have htail : u.insertBatch es = some t := by simpa [insertBatch, he] using ht
          have hs' := s.insertFirst_honest e he G hs (hp e (by simp))
          obtain ⟨hhead, htaild⟩ := List.pairwise_cons.mp hd
          apply ih u htail hs' ?_ htaild
          intro f hf
          obtain ⟨he1, he2⟩ := hhead f hf
          have hfwd : (f.val.1, f.val.2) ≠ e.val := by
            intro hh
            exact he1 (congrArg Prod.fst hh).symm
          have hrev : (f.val.2, f.val.1) ≠ e.val := by
            intro hh
            exact he2 (congrArg Prod.snd hh).symm
          have hz : e.graph.w f.val.1 f.val.2 = 0 := by
            simp [OriginalEdge.graph, OriginalEdge.originalIndex, WeightedGraph.edgeGraph,
              hfwd, hrev]
          rw [s.insertFirst_usedGraph e he]
          change 0 < max 0 (G.toWeighted.w f.val.1 f.val.2 -
            (s.usedGraph.w f.val.1 f.val.2 + e.graph.w f.val.1 f.val.2))
          have hpf := hp f (by simp [hf])
          change 0 < max 0 (G.toWeighted.w f.val.1 f.val.2 -
            s.usedGraph.w f.val.1 f.val.2) at hpf
          simpa only [hz, add_zero] using hpf

/-- Every accepted edge spends one unit of the live-component potential.
Retirement is handled separately and only decreases this potential. -/
theorem insertBatch_livePotential (s : ParallelState π r) (es : List (OriginalEdge π))
    {t : ParallelState π r} (ht : s.insertBatch es = some t)
    (hactive : ∀ e ∈ es, e.val.1 ∉ s.inactive ∧ e.val.2 ∉ s.inactive) :
    t.livePotential + es.length ≤ s.livePotential := by
  induction es generalizing s with
  | nil =>
      have he : s = t := Option.some.inj ht
      simp [← he]
  | cons e es ih =>
      cases he : s.insertFirst e with
      | none => simp [insertBatch, he] at ht
      | some u =>
          have htail : u.insertBatch es = some t := by simpa [insertBatch, he] using ht
          have hhead := hactive e (by simp)
          have hstep := s.insertFirst_livePotential e he hhead.1 hhead.2
          have hi := s.insertFirst_inactive e he
          have htailactive : ∀ f ∈ es, f.val.1 ∉ u.inactive ∧ f.val.2 ∉ u.inactive := by
            intro f hf
            simpa only [hi] using hactive f (by simp [hf])
          have hh := ih u htail htailactive
          simp only [List.length_cons]
          omega

theorem insertBatch_laminar (s : ParallelState π r) (hs : s.Laminar)
    (es : List (OriginalEdge π)) {t : ParallelState π r}
    (ht : s.insertBatch es = some t) : t.Laminar := by
  induction es generalizing s with
  | nil => simpa [insertBatch] using (Option.some.inj ht ▸ hs)
  | cons e es ih =>
      cases he : s.insertFirst e with
      | none => simp [insertBatch, he] at ht
      | some u =>
          have htail : u.insertBatch es = some t := by simpa [insertBatch, he] using ht
          exact ih u (s.insertFirst_laminar hs e he) htail

theorem insertBatch_edgeCount (s : ParallelState π r) (es : List (OriginalEdge π))
    {t : ParallelState π r} (ht : s.insertBatch es = some t) :
    t.edgeCount = s.edgeCount + es.length := by
  induction es generalizing s with
  | nil =>
      have he : s = t := Option.some.inj ht
      simp [← he]
  | cons e es ih =>
      cases he : s.insertFirst e with
      | none => simp [insertBatch, he] at ht
      | some u =>
          have htail : u.insertBatch es = some t := by simpa [insertBatch, he] using ht
          rw [ih u htail, s.insertFirst_edgeCount e he, List.length_cons]
          omega

/-- A sequence of separating shores protects each unprocessed source component.
The shores are proof-side witnesses, not inputs to the insertion algorithm. -/
theorem insertBatch_complete (s : ParallelState π r) (es : List (OriginalEdge π))
    (hr : 0 < r) (A : OriginalEdge π → Finset Q)
    (hclosed : ∀ e ∈ es, Closed (s.forests (lastIndex hr)).quotient (A e))
    (hcross : ∀ e ∈ es, π.map e.val.1 ∈ A e ∧ π.map e.val.2 ∉ A e)
    (havoid : es.Pairwise (fun e f => π.map e.val.1 ∉ A f ∧ π.map e.val.2 ∉ A f)) :
    ∃ t, s.insertBatch es = some t := by
  induction es generalizing s with
  | nil => exact ⟨s, rfl⟩
  | cons e es ih =>
      have hc := hcross e (by simp)
      have hn := (hclosed e (by simp)).not_reachable hc.1 hc.2
      obtain ⟨u, hu⟩ := s.insertFirst_exists e (lastIndex hr) hn
      obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp havoid
      have hclosed' : ∀ f ∈ es, Closed (u.forests (lastIndex hr)).quotient (A f) := by
        intro f hf
        obtain ⟨hsf, htf⟩ := hhead f hf
        exact s.insertFirst_closed e hu _ (hclosed f (by simp [hf])) hsf htf
      obtain ⟨t, ht⟩ := ih u hclosed'
        (fun f hf => hcross f (by simp [hf])) htail
      exact ⟨t, by simp [insertBatch, hu, ht]⟩

/-- Each original learned source is red and its chosen neighbor is blue.
The colors are constant on the initial finest connected components. -/
def StarBatch (s : ParallelState π r) (hr : 0 < r) (color : Q → Bool)
    (es : List (OriginalEdge π)) : Prop :=
  (∀ u v, (s.forests (lastIndex hr)).quotient.Reachable u v → color u = color v) ∧
  (∀ e ∈ es, color (π.map e.val.1) = true ∧ color (π.map e.val.2) = false) ∧
  es.Pairwise (fun e f =>
    ¬(s.forests (lastIndex hr)).quotient.Reachable (π.map e.val.1) (π.map f.val.1))

/-- Every learned red-to-blue edge is inserted, with no losses to cycles,
while preserving the actual nested component partitions. -/
theorem insertStarBatch_complete (s : ParallelState π r) (hr : 0 < r)
    (hs : s.Laminar) (color : Q → Bool) (es : List (OriginalEdge π))
    (hstar : s.StarBatch hr color es) :
    ∃ t, s.insertBatch es = some t ∧ t.Laminar ∧
      t.edgeCount = s.edgeCount + es.length := by
  obtain ⟨hcolor, hdir, hdistinct⟩ := hstar
  let F := (s.forests (lastIndex hr)).quotient
  let A : OriginalEdge π → Finset Q := fun e => forestBlock F (π.map e.val.1)
  have htarget (e f : OriginalEdge π) (he : e ∈ es) (hf : f ∈ es) :
      π.map e.val.2 ∉ A f := by
    intro hm
    have hh := hcolor _ _ ((mem_forestBlock _ _ _).mp hm)
    rw [(hdir f hf).1, (hdir e he).2] at hh
    cases hh
  have hc : ∀ e ∈ es, Closed F (A e) := fun e _ => forestBlock_closed F _
  have hx : ∀ e ∈ es, π.map e.val.1 ∈ A e ∧ π.map e.val.2 ∉ A e := by
    intro e he
    exact ⟨root_mem_forestBlock F _, htarget e e he he⟩
  have hav : es.Pairwise (fun e f => π.map e.val.1 ∉ A f ∧ π.map e.val.2 ∉ A f) := by
    apply List.pairwise_iff_getElem.mpr
    intro i j hi hj hij
    have he : es[i] ∈ es := List.getElem_mem hi
    have hf : es[j] ∈ es := List.getElem_mem hj
    have hd := List.pairwise_iff_getElem.mp hdistinct i j hi hj hij
    refine ⟨?_, htarget _ _ he hf⟩
    intro hm
    exact hd ((mem_forestBlock _ _ _).mp hm).symm
  obtain ⟨t, ht⟩ := s.insertBatch_complete es hr A hc hx hav
  exact ⟨t, ht, s.insertBatch_laminar hs es ht, s.insertBatch_edgeCount es ht⟩

/-- The full deterministic transition for an honestly learned star batch:
all edges enter, no original unit capacity is reused, retirement remains sound,
and every learned edge decreases the live-component potential. -/
theorem insertStarBatch_honest (s : ParallelState π r) (hr : 0 < r)
    (hs : s.Laminar) (G : SimpleInput V) (hsub : s.usedGraph.IsSubgraph G.toWeighted)
    (hi : s.InactiveSound hr G.toWeighted) (color : Q → Bool)
    (es : List (OriginalEdge π)) (hstar : s.StarBatch hr color es)
    (hp : ∀ e ∈ es, 0 < (G.toWeighted.subtract s.usedGraph).w e.val.1 e.val.2) :
    ∃ t, s.insertBatch es = some t ∧ t.Laminar ∧
      t.usedGraph.IsSubgraph G.toWeighted ∧ t.InactiveSound hr G.toWeighted ∧
      t.edgeCount = s.edgeCount + es.length ∧
      t.livePotential + es.length ≤ s.livePotential := by
  obtain ⟨t, ht, hl, hc⟩ := s.insertStarBatch_complete hr hs color es hstar
  obtain ⟨hcolor, hdir, hdistinct⟩ := hstar
  have hactive : ∀ e ∈ es, e.val.1 ∉ s.inactive ∧ e.val.2 ∉ s.inactive := by
    intro e he
    apply s.positive_endpoints_active hr G.toWeighted hi ?_ (hp e he)
    intro hh
    have heq := hcolor _ _ hh
    rw [(hdir e he).1, (hdir e he).2] at heq
    cases heq
  have hd : es.Pairwise (fun e f => e.val.1 ≠ f.val.1 ∧ e.val.2 ≠ f.val.1) := by
    apply List.pairwise_iff_getElem.mpr
    intro i j hi hj hij
    have he := List.getElem_mem hi
    have hf := List.getElem_mem hj
    have hn := List.pairwise_iff_getElem.mp hdistinct i j hi hj hij
    refine ⟨?_, ?_⟩
    · intro hh
      apply hn
      rw [hh]
    · intro hh
      have heq := congrArg (fun v => color (π.map v)) hh
      rw [(hdir _ he).2, (hdir _ hf).1] at heq
      cases heq
  exact ⟨t, ht, hl, s.insertBatch_honest es ht G hsub hp hd,
    s.insertBatch_inactiveSound es ht hr G.toWeighted hi, hc,
    s.insertBatch_livePotential es ht hactive⟩

/-- A checkable public neighbor table. Positivity in the hidden residual is
deliberately absent from this validator and is proved from the decoder. -/
def NeighborTable (color : Q → Bool) (sources : Finset V) (next : V → Option V) : Prop :=
  ∀ u ∈ sources, ∃ v, next u = some v ∧
    color (π.map u) = true ∧ color (π.map v) = false

def tableNeighbor (color : Q → Bool) (sources : Finset V) (next : V → Option V)
    (h : NeighborTable (π := π) color sources next) (u : sources) : V :=
  Classical.choose (h u.val u.property)

theorem tableNeighbor_spec (color : Q → Bool) (sources : Finset V) (next : V → Option V)
    (h : NeighborTable (π := π) color sources next) (u : sources) :
    next u.val = some (tableNeighbor color sources next h u) ∧
      color (π.map u.val) = true ∧
      color (π.map (tableNeighbor color sources next h u)) = false :=
  Classical.choose_spec (h u.val u.property)

def tableEdge (color : Q → Bool) (sources : Finset V) (next : V → Option V)
    (h : NeighborTable (π := π) color sources next) (u : sources) : OriginalEdge π :=
  ⟨(u.val, tableNeighbor color sources next h u), by
    have hc := tableNeighbor_spec color sources next h u
    intro he
    have hh := congrArg color he
    rw [hc.2.1, hc.2.2] at hh
    cases hh⟩

/-- One original edge for each recovered row, ordered only by public labels. -/
def tableEdges (color : Q → Bool) (sources : Finset V) (next : V → Option V)
    (h : NeighborTable (π := π) color sources next) : List (OriginalEdge π) :=
  (Finset.univ.toList : List sources).map (tableEdge color sources next h)

theorem tableEdges_length (color : Q → Bool) (sources : Finset V) (next : V → Option V)
    (h : NeighborTable (π := π) color sources next) :
    (tableEdges color sources next h).length = sources.card := by
  simp [tableEdges]

theorem tableEdges_star (s : ParallelState π r) (hr : 0 < r) (color : Q → Bool)
    (sources : Finset V) (next : V → Option V)
    (h : NeighborTable (π := π) color sources next)
    (hcolor : ∀ u v, (s.forests (lastIndex hr)).quotient.Reachable u v → color u = color v)
    (hsep : ∀ u ∈ sources, ∀ v ∈ sources, u ≠ v →
      ¬(s.forests (lastIndex hr)).quotient.Reachable (π.map u) (π.map v)) :
    s.StarBatch hr color (tableEdges color sources next h) := by
  refine ⟨hcolor, ?_, ?_⟩
  · intro e he
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp he
    exact (tableNeighbor_spec color sources next h u).2
  · unfold tableEdges
    rw [List.pairwise_map]
    apply (Finset.nodup_toList (Finset.univ : Finset sources)).pairwise_of_forall_ne
    intro u hu v hv hne
    apply hsep u.val u.property v.val v.property
    intro he
    exact hne (Subtype.ext he)

/-- Validate the queried table and perform the implemented least-layer batch
update. The constructor uses no graph, divergence, or certificate oracle. -/
def assembleNeighbors (s : ParallelState π r) (color : Q → Bool)
    (sources : Finset V) (next : V → Option V) : Option (ParallelState π r) :=
  if h : NeighborTable (π := π) color sources next then
    s.insertBatch (tableEdges color sources next h)
  else none

theorem assembleNeighbors_honest (s : ParallelState π r) (hr : 0 < r)
    (hl : s.Laminar) (color : Q → Bool) (sources : Finset V) (next : V → Option V)
    (h : NeighborTable (π := π) color sources next)
    (hcolor : ∀ u v, (s.forests (lastIndex hr)).quotient.Reachable u v → color u = color v)
    (hsep : ∀ u ∈ sources, ∀ v ∈ sources, u ≠ v →
      ¬(s.forests (lastIndex hr)).quotient.Reachable (π.map u) (π.map v))
    (G : SimpleInput V) (hs : s.usedGraph.IsSubgraph G.toWeighted)
    (hi : s.InactiveSound hr G.toWeighted)
    (hp : ∀ u ∈ sources, ∀ v, next u = some v →
      0 < (G.toWeighted.subtract s.usedGraph).w u v) :
    ∃ t, s.assembleNeighbors color sources next = some t ∧ t.Laminar ∧
      t.usedGraph.IsSubgraph G.toWeighted ∧ t.InactiveSound hr G.toWeighted ∧
      t.edgeCount = s.edgeCount + sources.card ∧
      t.livePotential + sources.card ≤ s.livePotential := by
  have hstar := s.tableEdges_star hr color sources next h hcolor hsep
  have hpos : ∀ e ∈ tableEdges color sources next h,
      0 < (G.toWeighted.subtract s.usedGraph).w e.val.1 e.val.2 := by
    intro e he
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp he
    exact hp u.val u.property _ (tableNeighbor_spec color sources next h u).1
  obtain ⟨t, ht, htl, hts, hti, hcount, hpotential⟩ :=
    s.insertStarBatch_honest hr hl G hs hi color _ hstar hpos
  rw [tableEdges_length] at hcount hpotential
  exact ⟨t, by simpa only [assembleNeighbors, dif_pos h] using ht,
    htl, hts, hti, hcount, hpotential⟩

end ParallelState

/-- The finite public source of independent colors. Unused subset labels cost
no queries; actual component labels are read from this tape. -/
def componentBits : PMF (Finset Q → Bool) :=
  Probability.product (fun _ : Finset Q =>
    PMF.uniformOfFinset (Finset.univ : Finset Bool) Finset.univ_nonempty)

private theorem fairBit_mass (b : Bool) :
    CutQueryComplexity.Probability.mass
      (PMF.uniformOfFinset (Finset.univ : Finset Bool) Finset.univ_nonempty)
      (fun c => c = b) = (2 : ℝ≥0∞)⁻¹ := by
  change (PMF.uniformOfFinset (Finset.univ : Finset Bool)
    Finset.univ_nonempty).toOuterMeasure ({b} : Set Bool) = _
  rw [PMF.toOuterMeasure_apply_singleton,
    PMF.uniformOfFinset_apply_of_mem Finset.univ_nonempty (Finset.mem_univ b)]
  norm_num

theorem componentBits_two (A B : Finset Q) (hAB : A ≠ B) :
    CutQueryComplexity.Probability.mass (componentBits (Q := Q))
      (fun tape => tape A = true ∧ tape B = false) = (4 : ℝ≥0∞)⁻¹ := by
  let P : Finset Q → Bool → Prop := fun I b =>
    (I = A → b = true) ∧ (I = B → b = false)
  have he : (fun tape : Finset Q → Bool => tape A = true ∧ tape B = false) =
      (fun tape => ∀ I, P I (tape I)) := by
    funext tape
    apply propext
    constructor
    · intro h I
      exact ⟨fun hh => hh.symm ▸ h.1, fun hh => hh.symm ▸ h.2⟩
    · intro h
      exact ⟨(h A).1 rfl, (h B).2 rfl⟩
  rw [he, componentBits, Probability.mass_product]
  have hf (I : Finset Q) :
      CutQueryComplexity.Probability.mass
        (PMF.uniformOfFinset (Finset.univ : Finset Bool) Finset.univ_nonempty) (P I) =
      (if I = A then (2 : ℝ≥0∞)⁻¹ else 1) *
        (if I = B then (2 : ℝ≥0∞)⁻¹ else 1) := by
    by_cases hIA : I = A
    · subst I
      simpa [P, hAB] using fairBit_mass true
    · by_cases hIB : I = B
      · subst I
        simpa [P, Ne.symm hAB] using fairBit_mass false
      · simp [P, hIA, hIB]
  simp_rw [hf]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_ite_eq', Finset.mem_univ, ite_true]
  rw [← ENNReal.mul_inv (a := 2) (b := 2) (Or.inl (by norm_num)) (Or.inl (by simp))]
  norm_num

def componentColor (F : _root_.SimpleGraph Q) (tape : Finset Q → Bool) : Q → Bool :=
  fun q => tape (forestBlock F q)

theorem componentColor_constant (F : _root_.SimpleGraph Q) (tape : Finset Q → Bool)
    {u v : Q} (h : F.Reachable u v) : componentColor F tape u = componentColor F tape v := by
  have he : forestBlock F u = forestBlock F v := by
    ext w
    simp only [mem_forestBlock]
    exact ⟨fun hw => h.symm.trans hw, fun hw => h.trans hw⟩
  exact congrArg tape he

theorem componentColor_red_blue (F : _root_.SimpleGraph Q) {u v : Q}
    (h : ¬F.Reachable u v) :
    CutQueryComplexity.Probability.mass (componentBits (Q := Q))
      (fun tape => componentColor F tape u = true ∧ componentColor F tape v = false) =
        (4 : ℝ≥0∞)⁻¹ := by
  apply componentBits_two
  intro he
  have hv : v ∈ forestBlock F u := by rw [he]; exact root_mem_forestBlock F v
  exact h ((mem_forestBlock F u v).mp hv)

namespace ParallelState

/-- Exactly those representatives whose queried blue residual row is positive. -/
def favorableRepresentatives (s : ParallelState π r) (hr : 0 < r)
    (G : WeightedGraph V) (reps : Finset V) (tape : Finset Q → Bool) : Finset V :=
  reps.filter fun u =>
    componentColor (s.forests (lastIndex hr)).quotient tape (π.map u) = true ∧
    ∃ v, 0 < (G.subtract s.usedGraph).w u v ∧
      componentColor (s.forests (lastIndex hr)).quotient tape (π.map v) = false

/-- A particular positive outgoing neighbor gives probability 1/4; no
independence between different representatives is asserted or needed. -/
theorem favorableRepresentative_mass (s : ParallelState π r) (hr : 0 < r)
    (G : WeightedGraph V) (reps : Finset V) {u v : V} (hu : u ∈ reps)
    (hcross : ¬(s.forests (lastIndex hr)).quotient.Reachable (π.map u) (π.map v))
    (hp : 0 < (G.subtract s.usedGraph).w u v) :
    (4 : ℝ≥0∞)⁻¹ ≤ CutQueryComplexity.Probability.mass (componentBits (Q := Q))
      (fun tape => u ∈ s.favorableRepresentatives hr G reps tape) := by
  rw [← componentColor_red_blue _ hcross]
  apply CutQueryComplexity.Probability.mass_mono
  intro tape ht
  exact Finset.mem_filter.mpr ⟨hu, ht.1, v, hp, ht.2⟩

/-- Linearity of expectation converts the actual component-color experiment
to the quarter-of-representatives bound used by the parallel phase. -/
theorem favorableRepresentatives_expect (s : ParallelState π r) (hr : 0 < r)
    (G : WeightedGraph V) (reps : Finset V)
    (hrep : ∀ u ∈ reps, ∃ v,
      ¬(s.forests (lastIndex hr)).quotient.Reachable (π.map u) (π.map v) ∧
        0 < (G.subtract s.usedGraph).w u v) :
    (reps.card : ℝ≥0∞) / 4 ≤ CutQueryComplexity.Probability.expect (componentBits (Q := Q))
      (fun tape => ((s.favorableRepresentatives hr G reps tape).card : ℝ≥0∞)) := by
  have hcount (tape : Finset Q → Bool) :
      ((s.favorableRepresentatives hr G reps tape).card : ℝ≥0∞) =
        ∑ u ∈ reps, if u ∈ s.favorableRepresentatives hr G reps tape then 1 else 0 := by
    rw [favorableRepresentatives, Finset.card_filter]
    push_cast
    apply Finset.sum_congr rfl
    intro u hu
    simp only [favorableRepresentatives, Finset.mem_filter, hu, true_and]
  simp_rw [hcount]
  rw [CutQueryComplexity.Probability.expect_sum]
  calc
    (reps.card : ℝ≥0∞) / 4 = ∑ _u ∈ reps, (4 : ℝ≥0∞)⁻¹ := by
      simp [div_eq_mul_inv, nsmul_eq_mul]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro u hu
      obtain ⟨v, hcross, hp⟩ := hrep u hu
      have hind : CutQueryComplexity.Probability.expect (componentBits (Q := Q))
          (fun tape => if u ∈ s.favorableRepresentatives hr G reps tape then 1 else 0) =
          CutQueryComplexity.Probability.mass (componentBits (Q := Q))
            (fun tape => u ∈ s.favorableRepresentatives hr G reps tape) := by
        rw [CutQueryComplexity.Probability.expect, CutQueryComplexity.Probability.mass_eq_tsum]
        apply tsum_congr
        intro tape
        by_cases hh : u ∈ s.favorableRepresentatives hr G reps tape
        · simp only [if_pos hh, mul_one]
        · simp only [if_neg hh, mul_zero]
      rw [hind]
      exact s.favorableRepresentative_mass hr G reps hu hcross hp

/-- An invalid public table flags failure. Every valid table is processed by
the actual first-fit update, rather than a graph-dependent chosen forest. -/
def assembleOrFail (s : ParallelState π r) (color : Q → Bool)
    (sources : Finset V) (next : V → Option V) : ParallelState π r :=
  (s.assembleNeighbors color sources next).getD {s with failed := true}

/-- The quarter-progress bound is linked to the implemented batch update.
The recovery premise describes its returned actual neighbor names, not a
potential drop, progress probability, certificate, or query-cost promise. -/
theorem assemble_favorable_expect (s : ParallelState π r) (hr : 0 < r)
    (hl : s.Laminar) (G : SimpleInput V) (hs : s.usedGraph.IsSubgraph G.toWeighted)
    (hi : s.InactiveSound hr G.toWeighted) (reps : Finset V)
    (hsep : ∀ u ∈ reps, ∀ v ∈ reps, u ≠ v →
      ¬(s.forests (lastIndex hr)).quotient.Reachable (π.map u) (π.map v))
    (hpositive : ∀ u ∈ reps, ∃ v,
      ¬(s.forests (lastIndex hr)).quotient.Reachable (π.map u) (π.map v) ∧
        0 < (G.toWeighted.subtract s.usedGraph).w u v)
    (next : (Finset Q → Bool) → V → Option V)
    (hnext : ∀ tape, ∀ u ∈ s.favorableRepresentatives hr G.toWeighted reps tape,
      ∃ v, next tape u = some v ∧
        0 < (G.toWeighted.subtract s.usedGraph).w u v ∧
        componentColor (s.forests (lastIndex hr)).quotient tape (π.map v) = false) :
    CutQueryComplexity.Probability.expect (componentBits (Q := Q))
      (fun tape => ((s.assembleOrFail
        (componentColor (s.forests (lastIndex hr)).quotient tape)
        (s.favorableRepresentatives hr G.toWeighted reps tape) (next tape)).livePotential : ℝ≥0∞)) +
      (reps.card : ℝ≥0∞) / 4 ≤ (s.livePotential : ℝ≥0∞) := by
  let F := (s.forests (lastIndex hr)).quotient
  let A := fun tape => s.favorableRepresentatives hr G.toWeighted reps tape
  let T := fun tape => s.assembleOrFail (componentColor F tape) (A tape) (next tape)
  have hstep (tape : Finset Q → Bool) : (T tape).livePotential + (A tape).card ≤ s.livePotential := by
    have htab : NeighborTable (π := π) (componentColor F tape) (A tape) (next tape) := by
      intro u hu
      obtain ⟨v, hv, hp, hb⟩ := hnext tape u hu
      have hred := (Finset.mem_filter.mp hu).2.1
      exact ⟨v, hv, hred, hb⟩
    have hsep' : ∀ u ∈ A tape, ∀ v ∈ A tape, u ≠ v →
        ¬F.Reachable (π.map u) (π.map v) := by
      intro u hu v hv hne
      exact hsep u (Finset.mem_filter.mp hu).1 v (Finset.mem_filter.mp hv).1 hne
    have hp : ∀ u ∈ A tape, ∀ v, next tape u = some v →
        0 < (G.toWeighted.subtract s.usedGraph).w u v := by
      intro u hu v hv
      obtain ⟨w, hw, hpw, hb⟩ := hnext tape u hu
      have he : w = v := Option.some.inj (hw.symm.trans hv)
      simpa only [he] using hpw
    obtain ⟨t, ht, _, _, _, _, hpot⟩ :=
      s.assembleNeighbors_honest hr hl (componentColor F tape) (A tape) (next tape)
        htab (fun u v huv => componentColor_constant F tape huv) hsep' G hs hi hp
    simpa only [T, assembleOrFail, ht, Option.getD_some] using hpot
  have he : CutQueryComplexity.Probability.expect (componentBits (Q := Q))
      (fun tape => ((T tape).livePotential : ℝ≥0∞)) +
      CutQueryComplexity.Probability.expect (componentBits (Q := Q))
        (fun tape => ((A tape).card : ℝ≥0∞)) ≤ (s.livePotential : ℝ≥0∞) := by
    rw [← CutQueryComplexity.Probability.expect_add]
    apply CutQueryComplexity.Probability.expect_le_of_le_on_support
    intro tape htape
    exact_mod_cast hstep tape
  have hcount := s.favorableRepresentatives_expect hr G.toWeighted reps hpositive
  exact (add_le_add (le_refl _) hcount).trans he

end ParallelState

namespace FiniteProgress

open CutQueryComplexity.Probability

variable {α : Type}

/-- Finite composition of transition laws. This is a proof-side law; the
operational parallel program must be connected to it separately. -/
def steps (next : α → PMF α) : ℕ → α → PMF α
  | 0, s => PMF.pure s
  | T + 1, s => (next s).bind (steps next T)

/-- Once a process leaves its active region, it cannot re-enter. The lemma
propagates an actual one-step support property through finite composition. -/
theorem steps_active_back (next : α → PMF α) (active : α → Prop)
    (hback : ∀ s t, t ∈ (next s).support → active t → active s)
    (T : ℕ) (s t : α) (ht : t ∈ (steps next T s).support) (ha : active t) : active s := by
  induction T generalizing s t with
  | zero =>
      have he : t = s := by simpa only [steps, PMF.mem_support_pure_iff] using ht
      exact he ▸ ha
  | succ T ih =>
      obtain ⟨u, hu, htu⟩ := (PMF.mem_support_bind_iff _ _ _).mp ht
      exact hback s u hu (ih u t htu ha)

theorem steps_tail_le_active (next : α → PMF α) (active : α → Prop)
    (hback : ∀ s t, t ∈ (next s).support → active t → active s)
    (T : ℕ) (s : α) : mass (steps next T s) active ≤ if active s then 1 else 0 := by
  rw [← one_mul (mass (steps next T s) active), ← expect_indicator]
  apply expect_le_of_le_on_support
  intro t ht
  by_cases ha : active t
  · have hs := steps_active_back next active hback T s t ht ha
    simp only [if_pos ha, if_pos hs, le_refl]
  · simp only [if_neg ha]
    exact bot_le

/-- A finite additive-drift calculation, retaining the terminal potential.
No infinite Las Vegas program or termination oracle is assumed. The concrete
parallel program must discharge `hback` and `hdrop` from its implemented
transition; this generic lemma is not the parallel progress endpoint. -/
theorem steps_potential_tail (next : α → PMF α) (active : α → Prop)
    (potential : α → ℝ≥0∞) (delta : ℝ≥0∞)
    (hback : ∀ s t, t ∈ (next s).support → active t → active s)
    (hdrop : ∀ s, expect (next s) potential + delta * (if active s then 1 else 0) ≤
      potential s) (T : ℕ) (s : α) :
    expect (steps next T s) potential +
      delta * T * mass (steps next T s) active ≤ potential s := by
  induction T generalizing s with
  | zero => simp only [steps, expect_pure, Nat.cast_zero, mul_zero, zero_mul, add_zero, le_refl]
  | succ T ih =>
      have hh : expect (next s) (fun t =>
          expect (steps next T t) potential + delta * T * mass (steps next T t) active) ≤
          expect (next s) potential :=
        expect_mono_on_support _ (fun t _ => ih t)
      rw [expect_add, expect_const_mul] at hh
      have hiter : expect (steps next (T + 1) s) potential +
          delta * T * mass (steps next (T + 1) s) active ≤ expect (next s) potential := by
        rw [steps, expect_bind, mass_bind]
        exact hh
      have hmass := steps_tail_le_active next active hback (T + 1) s
      calc
        expect (steps next (T + 1) s) potential +
            delta * ((T + 1 : ℕ) : ℝ≥0∞) * mass (steps next (T + 1) s) active =
            (expect (steps next (T + 1) s) potential +
              delta * T * mass (steps next (T + 1) s) active) +
              delta * mass (steps next (T + 1) s) active := by
          simp only [Nat.cast_add, Nat.cast_one, mul_add, mul_one, add_mul]
          exact (add_assoc _ _ _).symm
        _ ≤ expect (next s) potential + delta * (if active s then 1 else 0) :=
          add_le_add hiter (mul_le_mul le_rfl hmass (by positivity) (by positivity))
        _ ≤ potential s := hdrop s

theorem steps_weighted_tail (next : α → PMF α) (active : α → Prop)
    (potential : α → ℝ≥0∞) (delta : ℝ≥0∞)
    (hback : ∀ s t, t ∈ (next s).support → active t → active s)
    (hdrop : ∀ s, expect (next s) potential + delta * (if active s then 1 else 0) ≤
      potential s) (T : ℕ) (s : α) :
    delta * T * mass (steps next T s) active ≤ potential s := by
  exact (le_add_of_nonneg_left (show (0 : ℝ≥0∞) ≤ expect (steps next T s) potential from bot_le)).trans
    (steps_potential_tail next active potential delta hback hdrop T s)

/-- Expected active rounds in a finite execution, by the law of total
expectation. No infinite stopping time is introduced. -/
def activeVisits (next : α → PMF α) (active : α → Prop) : ℕ → α → ℝ≥0∞
  | 0, _ => 0
  | T + 1, s => (if active s then 1 else 0) +
      expect (next s) (activeVisits next active T)

/-- The same one-step inequality bounds all active-round charges uniformly
in the horizon, not merely the tail at its last round. This is the finite
telescoping estimate needed for expected query cost in a phase. -/
theorem steps_potential_visits (next : α → PMF α) (active : α → Prop)
    (potential : α → ℝ≥0∞) (delta : ℝ≥0∞)
    (hdrop : ∀ s, expect (next s) potential + delta * (if active s then 1 else 0) ≤
      potential s) (T : ℕ) (s : α) :
    expect (steps next T s) potential + delta * activeVisits next active T s ≤
      potential s := by
  induction T generalizing s with
  | zero => simp only [steps, activeVisits, expect_pure, mul_zero, add_zero, le_refl]
  | succ T ih =>
      have hh : expect (next s) (fun t => expect (steps next T t) potential +
          delta * activeVisits next active T t) ≤ expect (next s) potential :=
        expect_mono_on_support _ (fun t _ => ih t)
      rw [expect_add, expect_const_mul] at hh
      calc
        expect (steps next (T + 1) s) potential +
            delta * activeVisits next active (T + 1) s =
            (expect (next s) (fun t => expect (steps next T t) potential) +
              delta * expect (next s) (activeVisits next active T)) +
              delta * (if active s then 1 else 0) := by
          simp only [steps, expect_bind, activeVisits, mul_add]
          ac_rfl
        _ ≤ expect (next s) potential + delta * (if active s then 1 else 0) :=
          add_le_add hh (le_refl _)
        _ ≤ potential s := hdrop s

theorem activeVisits_bound (next : α → PMF α) (active : α → Prop)
    (potential : α → ℝ≥0∞) (delta : ℝ≥0∞)
    (hdrop : ∀ s, expect (next s) potential + delta * (if active s then 1 else 0) ≤
      potential s) (T : ℕ) (s : α) :
    delta * activeVisits next active T s ≤ potential s := by
  exact (le_add_of_nonneg_left (show (0 : ℝ≥0∞) ≤ expect (steps next T s) potential from bot_le)).trans
    (steps_potential_visits next active potential delta hdrop T s)

end FiniteProgress

/-- Round padding has the same numerical envelope as the parallel cost term.
This bounds the new charge before any uniform constant is fixed. -/
theorem roundPadding_envelope (n q r : ℕ) (hq : 2 ≤ q) (hqn : q ≤ n) :
    (r : ℝ) * (1 + Real.log q) ≤ (r : ℝ) * q * Real.log n / Real.log q := by
  have hq1 : (1 : ℝ) < q := by exact_mod_cast (show 1 < q by omega)
  have hq0 : (0 : ℝ) < q := by linarith
  have hlog : 0 < Real.log (q : ℝ) := Real.log_pos hq1
  have hln : Real.log (q : ℝ) ≤ Real.log (n : ℝ) :=
    Real.log_le_log hq0 (by exact_mod_cast hqn)
  have hsum : 1 + Real.log (q : ℝ) ≤ q := by
    linarith [Real.log_le_sub_one_of_pos hq0]
  have hratio : 1 ≤ Real.log (n : ℝ) / Real.log q := by
    apply (le_div_iff₀ hlog).mpr
    simpa using hln
  calc
    (r : ℝ) * (1 + Real.log q) ≤ (r : ℝ) * q :=
      mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg r)
    _ ≤ (r : ℝ) * q * (Real.log n / Real.log q) :=
      le_mul_of_one_le_right (by positivity) hratio
    _ = _ := by ring

/-- The denominator is retained above the parallel stopping scale. The public
power-size guard supplies `5*log(log n) <= 2*log q`; small sizes are separate. -/
theorem phase_denominator (q l t : ℝ) (hq : 0 < q) (hl : 0 < l)
    (ht : q / l ≤ t) (hpower : 5 * Real.log l ≤ 2 * Real.log q) :
    Real.log q / 5 ≤ Real.log (2 * t / l) := by
  have ht0 : 0 < t := (div_pos hq hl).trans_le ht
  have hbase : 0 < 2 * (q / l) / l := by positivity
  have hle : 2 * (q / l) / l ≤ 2 * t / l :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left ht (by norm_num)) hl.le
  have he : Real.log (2 * (q / l) / l) =
      Real.log 2 + Real.log q - 2 * Real.log l := by
    rw [Real.log_div (by positivity) (ne_of_gt hl),
      Real.log_mul (by norm_num) (ne_of_gt (div_pos hq hl)),
      Real.log_div (ne_of_gt hq) (ne_of_gt hl)]
    ring
  have hmono := Real.log_le_log hbase hle
  have htwo : 0 ≤ Real.log (2 : ℝ) := (Real.log_pos (by norm_num)).le
  rw [he] at hmono
  linarith

/-- The actual public power-size guard implies the logarithmic inequality
used above. Natural logarithms are smaller than base-two logarithms here. -/
theorem parallel_power_logs (n q : ℕ) (hn : 2 ≤ n)
    (hpower : (Real.log (n : ℝ) / Real.log 2) ^ ((5 : ℝ) / 2) ≤ (q : ℝ)) :
    5 * Real.log (Real.log (n : ℝ)) ≤ 2 * Real.log (q : ℝ) := by
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hln : 0 < Real.log (n : ℝ) := Real.log_pos hn1
  have htwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have htwo_le : Real.log (2 : ℝ) ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hbase : Real.log (n : ℝ) ≤ Real.log (n : ℝ) / Real.log 2 := by
    apply (le_div_iff₀ htwo).mpr
    exact mul_le_of_le_one_right hln.le htwo_le
  have hpow : (Real.log (n : ℝ)) ^ ((5 : ℝ) / 2) ≤ (q : ℝ) :=
    (Real.rpow_le_rpow hln.le hbase (by norm_num)).trans hpower
  have hlog := Real.log_le_log (Real.rpow_pos_of_pos hln _) hpow
  rw [Real.log_rpow hln] at hlog
  linarith

theorem phase_denominator_of_guard (n q : ℕ) (hn : 2 ≤ n) (hq : 0 < q)
    (hpower : (Real.log (n : ℝ) / Real.log 2) ^ ((5 : ℝ) / 2) ≤ (q : ℝ))
    (t : ℝ) (ht : (q : ℝ) / Real.log n ≤ t) :
    Real.log (q : ℝ) / 5 ≤ Real.log (2 * t / Real.log n) := by
  apply phase_denominator (q : ℝ) (Real.log n) t (by exact_mod_cast hq)
    (Real.log_pos (by exact_mod_cast (show 1 < n by omega))) ht
  exact parallel_power_logs n q hn hpower

/-- The actual degree-bucket count has a constant-factor logarithmic
overhead. Keeping that factor costs another factor two in the denominator;
it must not be silently replaced by exactly `log n`. -/
theorem phase_denominator_slots (q l t J : ℝ) (hq : 0 < q) (hl : 0 < l)
    (hJ : 0 < J) (hslots : J ≤ 3 * l) (ht : q / l ≤ t)
    (hpower : 5 * Real.log l ≤ 2 * Real.log q)
    (hlarge : 10 * Real.log 3 ≤ Real.log q) :
    Real.log q / 10 ≤ Real.log (2 * t / J) := by
  have ht0 : 0 < t := (div_pos hq hl).trans_le ht
  have hbase : 0 < 2 * t / (3 * l) := by positivity
  have hratio : 2 * t / (3 * l) ≤ 2 * t / J :=
    div_le_div_of_nonneg_left (by positivity) hJ hslots
  have hlog := Real.log_le_log hbase hratio
  have he : Real.log (2 * t / (3 * l)) = Real.log (2 * t / l) - Real.log 3 := by
    have hdiv : 2 * t / (3 * l) = (2 * t / l) / 3 := by ring
    rw [hdiv, Real.log_div (ne_of_gt (by positivity : 0 < 2 * t / l)) (by norm_num)]
  rw [he] at hlog
  have hfirst := phase_denominator q l t hq hl ht hpower
  linarith

/-- The large-input guard supplies the explicit constant-log reserve used
when the true number of buckets replaces the idealized logarithmic scale. -/
theorem parallel_guard_log_reserve (n q : ℕ) (hln : 1000 ≤ Real.log (n : ℝ))
    (hpower : (Real.log (n : ℝ) / Real.log 2) ^ ((5 : ℝ) / 2) ≤ (q : ℝ)) :
    10 * Real.log 3 ≤ Real.log (q : ℝ) := by
  have htwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have htwo_le : Real.log (2 : ℝ) ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hbase : 1000 ≤ Real.log (n : ℝ) / Real.log 2 := by
    apply (le_div_iff₀ htwo).mpr
    nlinarith
  have hsq : (1000 : ℝ) ^ 2 ≤ (Real.log (n : ℝ) / Real.log 2) ^ 2 := by
    nlinarith [sq_nonneg (Real.log (n : ℝ) / Real.log 2 - 1000)]
  have hrpow : (Real.log (n : ℝ) / Real.log 2) ^ (2 : ℕ) ≤
      (Real.log (n : ℝ) / Real.log 2) ^ ((5 : ℝ) / 2) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have hq := (hsq.trans hrpow).trans hpower
  have hthree : (3 : ℝ) ^ 10 ≤ (q : ℝ) := by norm_num at *; linarith
  have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 3 ^ 10) hthree
  simpa only [Real.log_pow, Nat.cast_ofNat] using hh

/-- The finite charge over geometrically shrinking component scales is
uniform in the number of phases; no infinite execution is assumed. -/
theorem geometric_phase_charge (q : ℝ) (hq : 0 ≤ q) (phases : ℕ) :
    (∑ j ∈ Finset.range phases, q / (2 : ℝ) ^ j) ≤ 2 * q := by
  calc
    (∑ j ∈ Finset.range phases, q / (2 : ℝ) ^ j) =
        q * ∑ j ∈ Finset.range phases, (1 / (2 : ℝ)) ^ j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      simp only [one_div, inv_pow, div_eq_mul_inv, one_mul]
    _ ≤ q * 2 := mul_le_mul_of_nonneg_left (sum_geometric_two_le phases) hq
    _ = 2 * q := mul_comm _ _

/-- Zero-row buckets make no calls; positive rows retain the sparse-decoder
denominator, including singleton buckets. -/
def parallelRowWeight (b : ℕ) : ℝ :=
  if b = 0 then 0 else (b : ℝ) / Real.log (2 * (b : ℝ))

/-- A uniform elementary affine bound replaces an asymptotic bucket-sum
claim. Its baseline is the current representative scale, not hidden degrees. -/
theorem parallelRowWeight_affine (b : ℕ) (s : ℝ) (hs : 1 ≤ s) :
    parallelRowWeight b ≤ 2 * ((b : ℝ) + s) / Real.log (2 * s) := by
  have hs0 : 0 < s := by linarith
  have hd : 0 < Real.log (2 * s) := Real.log_pos (by linarith)
  by_cases hb : b = 0
  · simp only [parallelRowWeight, hb, ite_true, Nat.cast_zero, zero_add]
    positivity
  · have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast (show 1 ≤ b by omega)
    have hb0 : (0 : ℝ) < b := by linarith
    have hdb : 0 < Real.log (2 * (b : ℝ)) := Real.log_pos (by linarith)
    rw [parallelRowWeight, if_neg hb]
    by_cases hbs : (b : ℝ) ≤ s
    · have hdb1 : 0 < Real.log ((b : ℝ) + 1) := Real.log_pos (by linarith)
      have hds1 : 0 < Real.log (s + 1) := Real.log_pos (by linarith)
      have hlogb : Real.log ((b : ℝ) + 1) ≤ Real.log (2 * (b : ℝ)) :=
        Real.log_le_log (by linarith) (by linarith)
      have hsmall : (b : ℝ) / Real.log ((b : ℝ) + 1) ≤ s / Real.log (s + 1) :=
        (div_le_div_iff₀ hdb1 hds1).mpr (Recovery.log_one_add_ratio hb0.le hbs)
      have hslog : Real.log (2 * s) ≤ 2 * Real.log (s + 1) := by
        have hsq : 2 * s ≤ (s + 1) ^ 2 := by nlinarith [sq_nonneg s]
        have hh := Real.log_le_log (by positivity : (0 : ℝ) < 2 * s) hsq
        simpa only [Real.log_pow, Nat.cast_ofNat] using hh
      calc
        (b : ℝ) / Real.log (2 * (b : ℝ)) ≤ (b : ℝ) / Real.log ((b : ℝ) + 1) :=
          div_le_div_of_nonneg_left hb0.le hdb1 hlogb
        _ ≤ s / Real.log (s + 1) := hsmall
        _ ≤ 2 * s / Real.log (2 * s) := by
          apply (div_le_div_iff₀ hds1 hd).mpr
          nlinarith [mul_le_mul_of_nonneg_left hslog hs0.le]
        _ ≤ _ := (div_le_div_iff_of_pos_right hd).mpr (by linarith)
    · have hsb : s ≤ (b : ℝ) := (lt_of_not_ge hbs).le
      have hlog : Real.log (2 * s) ≤ Real.log (2 * (b : ℝ)) :=
        Real.log_le_log (by positivity) (by linarith)
      calc
        (b : ℝ) / Real.log (2 * (b : ℝ)) ≤ (b : ℝ) / Real.log (2 * s) :=
          div_le_div_of_nonneg_left hb0.le hd hlog
        _ ≤ _ := (div_le_div_iff_of_pos_right hd).mpr (by linarith)

/-- Actual degree-bucket sizes are charged jointly. In applications choose
`s = t/J`, where t is the current number of representatives and J is the
public number of degree buckets. Empty and very small favorable sets satisfy
the same estimate; no replacement by the coarse m+n recovery bound occurs. -/
theorem parallelRowWeight_sum {I : Type} [Fintype I] (sizes : I → ℕ)
    (t s : ℝ) (hs : 1 ≤ s) (hm : (∑ i, (sizes i : ℝ)) ≤ t)
    (hslots : (Fintype.card I : ℝ) * s ≤ t) :
    (∑ i, parallelRowWeight (sizes i)) ≤ 4 * t / Real.log (2 * s) := by
  have hd : 0 < Real.log (2 * s) := Real.log_pos (by linarith)
  calc
    (∑ i, parallelRowWeight (sizes i)) ≤
        ∑ i, 2 * ((sizes i : ℝ) + s) / Real.log (2 * s) :=
      Finset.sum_le_sum (fun i _ => parallelRowWeight_affine (sizes i) s hs)
    _ = 2 * ((∑ i, (sizes i : ℝ)) + (Fintype.card I : ℝ) * s) /
        Real.log (2 * s) := by
      rw [← Finset.sum_div, ← Finset.mul_sum, Finset.sum_add_distrib]
      simp
    _ ≤ _ := (div_le_div_iff_of_pos_right hd).mpr (by linarith)

theorem parallelBucketWeight_sum (J : ℕ) (sizes : Fin J → ℕ) (t : ℝ)
    (hJ : 1 ≤ J) (ht : (J : ℝ) ≤ t) (hm : (∑ i, (sizes i : ℝ)) ≤ t) :
    (∑ i, parallelRowWeight (sizes i)) ≤ 4 * t / Real.log (2 * t / J) := by
  have hJ0 : (0 : ℝ) < J := by exact_mod_cast (show 0 < J by omega)
  have hs : 1 ≤ t / J := (le_div_iff₀ hJ0).mpr (by simpa using ht)
  have hslots : (Fintype.card (Fin J) : ℝ) * (t / J) ≤ t := by
    simp only [Fintype.card_fin]
    have he : (J : ℝ) * (t / J) = t := by field_simp
    rw [he]
  have hh := parallelRowWeight_sum sizes t (t / J) hs hm hslots
  simpa only [mul_div_assoc] using hh

#print axioms Closed.sup_edge
#print axioms residualForestChain_of_closed
#print axioms ParallelState.residual_contract
#print axioms ParallelState.complete_of_residualClosed
#print axioms ParallelState.certificate_of_retired
#print axioms ParallelState.liveBlocks_card_mono
#print axioms ParallelState.livePotential_le
#print axioms ParallelState.liveBlocks_card_mono_of
#print axioms ParallelState.liveBlocks_card_lt_of_merge
#print axioms ParallelState.positive_endpoints_active
#print axioms ParallelState.insertAt_livePotential
#print axioms ParallelState.retire_livePotential
#print axioms ParallelState.insertBatch_complete
#print axioms ParallelState.insertBatch_laminar
#print axioms ParallelState.insertBatch_edgeCount
#print axioms ParallelState.insertStarBatch_complete
#print axioms ParallelState.insertBatch_honest
#print axioms ParallelState.insertBatch_livePotential
#print axioms ParallelState.insertStarBatch_honest
#print axioms ParallelState.tableEdges_star
#print axioms ParallelState.tableEdges_length
#print axioms ParallelState.assembleNeighbors_honest
#print axioms componentBits_two
#print axioms componentColor_constant
#print axioms componentColor_red_blue
#print axioms ParallelState.favorableRepresentatives_expect
#print axioms ParallelState.assemble_favorable_expect
#print axioms FiniteProgress.steps_active_back
#print axioms FiniteProgress.steps_tail_le_active
#print axioms FiniteProgress.steps_potential_tail
#print axioms FiniteProgress.steps_weighted_tail
#print axioms FiniteProgress.steps_potential_visits
#print axioms FiniteProgress.activeVisits_bound
#print axioms roundPadding_envelope
#print axioms phase_denominator
#print axioms parallel_power_logs
#print axioms phase_denominator_of_guard
#print axioms phase_denominator_slots
#print axioms parallel_guard_log_reserve
#print axioms geometric_phase_charge
#print axioms parallelRowWeight_affine
#print axioms parallelRowWeight_sum
#print axioms parallelBucketWeight_sum

end
end CutQueryComplexity.StarContraction2022.Certificates
