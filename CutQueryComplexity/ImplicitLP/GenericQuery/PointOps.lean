import CutQueryComplexity.ImplicitLP.GenericQuery.Query
import CutQueryComplexity.ImplicitLP.BatchProg

/-! # Public coordinate operations used throughout the general run

All operations are functions on a fixed public index type. Their interpretation
commutes with coordinate arithmetic, independently of multiplicity and query
success. No graph-dependent list is used in an executable formula.
-/

set_option autoImplicit false
namespace CutQueryComplexity.ImplicitLP.GenericQuery
open Matrix Finset Real
noncomputable section
variable {n me : ℕ}

def mapPt (f : ℝ → ℝ) (x : Point n me) : Point n me := fun i => f (x i)
def map2Pt (f : ℝ → ℝ → ℝ) (x y : Point n me) : Point n me := fun i => f (x i) (y i)
def map3Pt (f : ℝ → ℝ → ℝ → ℝ) (x y z : Point n me) : Point n me :=
  fun i => f (x i) (y i) (z i)
def zeroPt : Point n me := 0

theorem pairOf_mapPt (f : ℝ → ℝ) (pt : Point n me) (e : Sym2 (Fin n)) :
    pairOf (mapPt f pt).pair e = f (pairOf pt.pair e) := pairOf_map f pt.pair e
theorem pairOf_map2Pt (f : ℝ → ℝ → ℝ) (p₁ p₂ : Point n me) (e : Sym2 (Fin n)) :
    pairOf (map2Pt f p₁ p₂).pair e = f (pairOf p₁.pair e) (pairOf p₂.pair e) :=
  pairOf_map2 f p₁.pair p₂.pair e

def wPt (X : Point n me) : Point n me := mapPt exp X
def gradPt (μ : ℝ) (X z : Point n me) : Point n me :=
  map2Pt (fun a b => 2 * μ * sinh (μ * (a - b))) X z
def clipQPt (Q : ℝ) (q : Point n me) : Point n me := mapPt (clipTo (-Q) Q) q
def clipWPt (wmin : ℝ) (w : Point n me) : Point n me := mapPt (max wmin) w
def barSPt (κ m x : Point n me) : Point n me :=
  map3Pt (fun k mm xx => k / cos (k * (xx - mm))) κ m x
def barDphiPt (κ m x : Point n me) : Point n me :=
  map3Pt (fun k mm xx => k * tan (k * (xx - mm))) κ m x
def normDPt (κ m x X : Point n me) : Point n me :=
  map2Pt (fun a b => 1 / (exp a * b ^ 2)) X (barSPt κ m x)
def normQPt (t : ℝ) (κ m c x X : Point n me) : Point n me :=
  map3Pt (fun cc a d => t * cc + exp a * d) c X (barDphiPt κ m x)
def addPt (x y : Point n me) : Point n me := x + y
def obsPt (c₀ : ℝ) (y : Point n me) : Point n me := mapPt (fun u => log (exp u + c₀)) y
def chasePt (ξ : ℝ) (X v : Point n me) : Point n me := X - (1 + ξ) • v
def invSlackPt (κ m x : Point n me) : Point n me :=
  map3Pt (fun k mm xx => cos (k * (xx - mm)) / k) κ m x

variable (G : DiGraph (Fin n))

theorem vec_mapPt (f : ℝ → ℝ) (x : Point n me) (i : Fin (rowCount G me)) :
    vec G (mapPt f x) i = f (vec G x i) := rfl
theorem vec_map2Pt (f : ℝ → ℝ → ℝ) (x y : Point n me) (i : Fin (rowCount G me)) :
    vec G (map2Pt f x y) i = f (vec G x i) (vec G y i) := rfl
theorem vec_map3Pt (f : ℝ → ℝ → ℝ → ℝ) (x y z : Point n me) (i : Fin (rowCount G me)) :
    vec G (map3Pt f x y z) i = f (vec G x i) (vec G y i) (vec G z i) := rfl
theorem vec_zeroPt : vec G (zeroPt : Point n me) = 0 := rfl
theorem vec_wPt (X : Point n me) : vec G (wPt X) = fun i => exp (vec G X i) := rfl
theorem vec_gradPt (μ : ℝ) (X z : Point n me) :
    vec G (gradPt μ X z) = potGrad μ (vec G X - vec G z) := rfl

theorem vec_clipQPt {Q : ℝ} (q : Point n me) (h : ∀ i, |vec G q i| ≤ Q) :
    vec G (clipQPt Q q) = vec G q := by
  funext i
  exact clipTo_of_mem (abs_le.mp (h i)).1 (abs_le.mp (h i)).2
theorem vec_clipWPt {wmin : ℝ} (w : Point n me) (h : ∀ i, wmin ≤ vec G w i) :
    vec G (clipWPt wmin w) = vec G w := by
  funext i
  exact max_eq_right (h i)

theorem vec_eq_weights (x : Point n me) :
    vec G x = vec G (weights (pairOf x.pair) x.explicit) := by
  funext i
  simp only [vec]
  generalize (rowEquiv G me).symm i = r
  rcases r with ⟨p, k⟩ | j
  · exact (pairOf_mk_lt x.pair p.2).symm
  · rfl

theorem vec_barSPt (κ m x : Point n me) :
    vec G (barSPt κ m x) = barS (vec G κ) (vec G m) (vec G x) := rfl
theorem vec_barDphiPt (κ m x : Point n me) :
    vec G (barDphiPt κ m x) = barDphi (vec G κ) (vec G m) (vec G x) := rfl
theorem vec_normDPt (κ m x X : Point n me) :
    vec G (normDPt κ m x X) =
      normD (fun i => exp (vec G X i)) (barS (vec G κ) (vec G m) (vec G x)) := rfl
theorem vec_normQPt (t : ℝ) (κ m c x X : Point n me) :
    vec G (normQPt t κ m c x X) = normQ t (vec G c) (fun i => exp (vec G X i))
      (barDphi (vec G κ) (vec G m) (vec G x)) := rfl
theorem vec_addPt (x y : Point n me) : vec G (addPt x y) = vec G x + vec G y := rfl
theorem vec_obsPt (c₀ : ℝ) (y : Point n me) :
    vec G (obsPt c₀ y) = fun i => log (exp (vec G y i) + c₀) := rfl
theorem vec_chasePt (ξ : ℝ) (X v : Point n me) :
    vec G (chasePt ξ X v) = vec G X - (1 + ξ) • vec G v := rfl

theorem vec_invSlackPt {κ m x : Fin (rowCount G me) → ℝ} (hκ : ∀ i, 0 < κ i)
    (hx : Interior κ m x) {κp mp xp : Point n me} (hκp : vec G κp = κ)
    (hmp : vec G mp = m) (hxp : vec G xp = x) :
    vec G (invSlackPt κp mp xp) = fun i => exp (sfun κ m x i) := by
  funext i
  rw [invSlackPt, vec_map3Pt, hκp, hmp, hxp, sfun,
    exp_log (div_pos (cos_theta_pos hx i) (hκ i))]
  rfl

#print axioms vec_eq_weights
#print axioms vec_clipQPt
#print axioms vec_normDPt
#print axioms vec_normQPt
#print axioms vec_invSlackPt

end
end CutQueryComplexity.ImplicitLP.GenericQuery
