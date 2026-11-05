import Mathlib
import MarkovTriple.BGL.Instances.SphereN.Atlas.Chart3

/-!
# Chartwise `Γ`, `L` of the stereographic charts equal the extrinsic `ΓS`, `LS` (Round 29, stream R, R1)

For `f ∈ 𝒜₀(Sph 3)` with `E = ext f`, `P = Pc b`: `∂ᵢ(E∘P) = Σ_a ∂_aE(P) ∂ᵢP_a`; the chart Gram matrix is the tangent projector,
`((1+r²)/2)² Σᵢ ∂ᵢP_a ∂ᵢP_c = δ_{ac} - P_aP_c` (`R27.Gch_coord`), `L P_a = -2P_a` (`R27.Lch_coord`), and Euler's relations
for degree-0 homogeneity kill the radial parts.
-/

open MeasureTheory Filter Topology
open MarkovTriple.BGL (pderiv)

namespace MarkovTriple.BGL.SphereN.Atlas

open MarkovTriple.BGL.Instances.Riemannian.R27
open LebesgueRd

lemma T_id (b : Bool) (a c : Fin 3) (y : Ev 2) :
    ((1 + r2 y) / 2) ^ 2 * ∑ k, dd k (fun z => Pc b z a) y * dd k (fun z => Pc b z c) y =
      (if a = c then 1 else 0) - Pc b y a * Pc b y c := by
  have h := Gch_coord b a c y
  rw [Gch_conformal] at h
  exact h

lemma Lap_id (b : Bool) (a : Fin 3) (y : Ev 2) :
    ((1 + r2 y) / 2) ^ 2 * ∑ k, dd k (dd k (fun z => Pc b z a)) y = -2 * Pc b y a := by
  have h := Lch_coord b a y
  rw [Lch_conformal, wS_inv] at h
  exact h

lemma pc_eq (b : Bool) (y : Ev 2) : cv ((eS2 (ptS b y) : Sph 3) : Ee 3) = Pc b y := rfl

lemma comp_eq (f : Sph 3 → ℝ) (b : Bool) : (fun y => f (eS2 (ptS b y))) = fun y => ext f (Pc b y) := by
  funext y
  rw [← pc_eq, ext_cv]

lemma euler1 {f : Sph 3 → ℝ} (hf : f ∈ A₀S 3) {x : Fin 3 → ℝ} (hx : x ≠ 0) :
    ∑ a, x a * dd a (ext f) x = 0 := by
  have := euler (show SmO (ext f) from hf) (hom_ext f) hx
  simpa using this

lemma euler2 {f : Sph 3 → ℝ} (hf : f ∈ A₀S 3) {x : Fin 3 → ℝ} (hx : x ≠ 0) (a : Fin 3) :
    ∑ c, x c * dd c (dd a (ext f)) x = - dd a (ext f) x := by
  have hE : SmO (ext f) := hf
  have := euler (hE.ddO a) (hom_dd hE (hom_ext f) a) hx
  simpa using this

lemma dd_chart {f : Sph 3 → ℝ} (hf : f ∈ A₀S 3) (b : Bool) (k : Fin 2) (y : Ev 2) :
    dd k (fun z => f (eS2 (ptS b z))) y = ∑ a, dd a (ext f) (Pc b y) * dd k (fun z => Pc b z a) y := by
  rw [comp_eq]
  exact dd_comp_O (show SmO (ext f) from hf) (fun a => diff_Pc b a y) (Pc_ne b y) k

lemma gram3 (c : ℝ) (e h : Fin 3 → ℝ) (p : Fin 3 → Fin 2 → ℝ) :
    c * ∑ k, (∑ a, e a * p a k) * (∑ d, h d * p d k) =
      ∑ a, ∑ d, e a * h d * (c * ∑ k, p a k * p d k) := by
  simp only [Fin.sum_univ_three, Fin.sum_univ_two]
  ring

theorem chart_Γ_eq {f h : Sph 3 → ℝ} (hf : f ∈ A₀S 3) (hh : h ∈ A₀S 3) (b : Bool) (y : Ev 2) :
    Gch gS (fun y => f (eS2 (ptS b y))) (fun y => h (eS2 (ptS b y))) y = ΓS f h (eS2 (ptS b y)) := by
  rw [Gch_conformal]
  have e1 : ∀ k, pderiv (fun y => f (eS2 (ptS b y))) k y =
      ∑ a, dd a (ext f) (Pc b y) * dd k (fun z => Pc b z a) y := fun k => dd_chart hf b k y
  have e2 : ∀ k, pderiv (fun y => h (eS2 (ptS b y))) k y =
      ∑ a, dd a (ext h) (Pc b y) * dd k (fun z => Pc b z a) y := fun k => dd_chart hh b k y
  simp only [e1, e2]
  rw [gram3]
  simp only [T_id]
  have hx := Pc_ne b y
  have h1 := euler1 hf hx
  have h2 := euler1 hh hx
  unfold ΓS Gf
  rw [pc_eq]
  simp only [Fin.sum_univ_three] at h1 h2 ⊢
  simp only [Fin.isValue, ↓reduceIte, Fin.reduceEq]
  linear_combination (dd 0 (ext h) (Pc b y) * Pc b y 0 + dd 1 (ext h) (Pc b y) * Pc b y 1 +
    dd 2 (ext h) (Pc b y) * Pc b y 2) * (- h1)

lemma dd_sum_mul {m : ℕ} (G H : Fin 3 → (Fin m → ℝ) → ℝ) {y : Fin m → ℝ}
    (hG : ∀ a, DifferentiableAt ℝ (G a) y) (hH : ∀ a, DifferentiableAt ℝ (H a) y) (k : Fin m) :
    dd k (fun z => ∑ a, G a z * H a z) y = ∑ a, (G a y * dd k (H a) y + H a y * dd k (G a) y) := by
  have h : HasFDerivAt (fun z => ∑ a, G a z * H a z)
      (∑ a, (G a y • fderiv ℝ (H a) y + H a y • fderiv ℝ (G a) y)) y :=
    HasFDerivAt.fun_sum fun a _ => (hG a).hasFDerivAt.mul (hH a).hasFDerivAt
  unfold dd
  rw [h.fderiv]
  simp

lemma lap3 (C : ℝ) (e : Fin 3 → ℝ) (E2 : Fin 3 → Fin 3 → ℝ) (p q : Fin 3 → Fin 2 → ℝ) :
    C * ∑ k, ∑ a, (e a * q a k + p a k * ∑ c, E2 a c * p c k) =
      ∑ a, e a * (C * ∑ k, q a k) + ∑ a, ∑ c, E2 a c * (C * ∑ k, p a k * p c k) := by
  simp only [Fin.sum_univ_three, Fin.sum_univ_two]
  ring

lemma diff_Pvec (b : Bool) (y : Ev 2) : DifferentiableAt ℝ (fun z => Pc b z) y :=
  differentiableAt_pi.2 fun a => diff_Pc b a y

lemma diff_ddE {f : Sph 3 → ℝ} (hf : f ∈ A₀S 3) (b : Bool) (a : Fin 3) (y : Ev 2) :
    DifferentiableAt ℝ (fun z => dd a (ext f) (Pc b z)) y := by
  have hE : SmO (ext f) := hf
  exact ((hE.ddO a).differentiableAt (Pc_ne b y)).comp y (diff_Pvec b y)

theorem chart_L_eq {f : Sph 3 → ℝ} (hf : f ∈ A₀S 3) (b : Bool) (y : Ev 2) :
    Lch gS wS (fun y => f (eS2 (ptS b y))) y = LS f (eS2 (ptS b y)) := by
  have hE : SmO (ext f) := hf
  have hx := Pc_ne b y
  rw [Lch_conformal, wS_inv]
  have e0 : ∀ k : Fin 2, pderiv (pderiv (fun y => f (eS2 (ptS b y))) k) k y =
      ∑ a, (dd a (ext f) (Pc b y) * dd k (dd k (fun z => Pc b z a)) y +
        dd k (fun z => Pc b z a) y * ∑ c, dd c (dd a (ext f)) (Pc b y) * dd k (fun z => Pc b z c) y) := by
    intro k
    have e1 : pderiv (fun y => f (eS2 (ptS b y))) k =
        fun z => ∑ a, dd a (ext f) (Pc b z) * dd k (fun w => Pc b w a) z := funext fun z => dd_chart hf b k z
    show dd k (pderiv (fun y => f (eS2 (ptS b y))) k) y = _
    have : dd k (pderiv (fun y => f (eS2 (ptS b y))) k) y =
        dd k (fun z => ∑ a, dd a (ext f) (Pc b z) * dd k (fun w => Pc b w a) z) y := by rw [e1]
    rw [this, dd_sum_mul (fun a z => dd a (ext f) (Pc b z)) (fun a z => dd k (fun w => Pc b w a) z)
      (fun a => diff_ddE hf b a y) (fun a => diff_dd_Pc b a k y) k]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [dd_comp_O (hE.ddO a) (fun c => diff_Pc b c y) hx k]
  simp only [e0]
  rw [lap3]
  simp only [T_id, Lap_id]
  have h1 := euler1 hf hx
  have h2 := fun a => euler2 hf hx a
  unfold LS Lf
  rw [pc_eq]
  simp only [Fin.sum_univ_three] at h1 h2 ⊢
  simp only [Fin.isValue, ↓reduceIte, Fin.reduceEq]
  linear_combination (-(Pc b y 0)) * (h2 0) - (Pc b y 1) * (h2 1) - (Pc b y 2) * (h2 2) - h1

end MarkovTriple.BGL.SphereN.Atlas
