import Mathlib
import MarkovTriple.BGL.Instances.Riemannian.R27.Sphere2
import MarkovTriple.BGL.Instances.Riemannian.R27.Sphere2Lap
import MarkovTriple.BGL.Instances.Riemannian.R27.Piola

/-!
# Chartwise `Γ`, `L`, `Γ₂` of the coordinate functions of `S²`, glued by the atlas

`coordFn a p = p_a`.  In every chart `b`, `coordFn a ∘ pt_b = ±Fc a`, so `L = -2 ·`, `Γ(p_a, p_b) = δ_{ab} - p_a p_b`
(`Lch_Fc`, `Gch_Fc`), independently of the chart.  `Γ₂(p_a) = ½ L Γ(p_a) - Γ(p_a, L p_a) = 1 + p_a²`, i.e. `CD(1,2)`
holds with equality on the coordinate functions.
-/

open MarkovTriple.BGL (pderiv)
open Filter Topology

namespace MarkovTriple.BGL.Instances.Riemannian.R27

/-- the coordinate functions of `S² ⊂ ℝ³` -/
def coordFn (a : Fin 3) (p : S2) : ℝ := p.1 a

theorem sphereAtlas_overlap_ne :
    (sphereAtlas.chart true).overlap (sphereAtlas.chart false) = {x | x ≠ 0} := by
  show (sph true).overlap (sph false) = _
  rw [sph_overlap]; simp

theorem sphereAtlas_τ {x : Ev 2} (_hx : x ≠ 0) :
    sphereAtlas.τ true false x = fun i => x i / (x 0 ^ 2 + x 1 ^ 2) := by
  show τS true false x = _
  rw [τS_ne (by decide)]
  rfl

/-! ### smoothness of the coordinate functions -/

lemma contDiff_qf (n : WithTop ℕ∞) : ContDiff ℝ n qf := by
  unfold qf r2
  exact ContDiff.inv (by fun_prop) fun y => one_add_r2_ne y

lemma contDiff_Fc (n : WithTop ℕ∞) (a : Fin 3) : ContDiff ℝ n (Fc a) := by
  have hq := contDiff_qf n
  have c3 : ∀ a : Fin 3, a = 0 ∨ a = 1 ∨ a = 2 := by decide
  rcases c3 a with rfl | rfl | rfl
  · show ContDiff ℝ n fun y : Ev 2 => 2 * y 0 * qf y
    exact (contDiff_const.mul (contDiff_apply ℝ ℝ 0)).mul hq
  · show ContDiff ℝ n fun y : Ev 2 => 2 * y 1 * qf y
    exact (contDiff_const.mul (contDiff_apply ℝ ℝ 1)).mul hq
  · show ContDiff ℝ n fun y : Ev 2 => 1 - 2 * qf y
    exact contDiff_const.sub (contDiff_const.mul hq)

/-- the sign by which `coordFn a ∘ pt_b` differs from `Fc a` -/
def csign (b : Bool) (a : Fin 3) : ℝ := if a = 2 then sgn b else 1

lemma csign_sq (b : Bool) (a : Fin 3) : csign b a ^ 2 = 1 := by
  unfold csign; split_ifs
  · exact sgn_sq b
  · norm_num

lemma coord_pt (b : Bool) (a : Fin 3) (y : Ev 2) : coordFn a (ptS b y) = csign b a * Fc a y := by
  have c3 : ∀ a : Fin 3, a = 0 ∨ a = 1 ∨ a = 2 := by decide
  rcases c3 a with rfl | rfl | rfl
  · simp [csign, coordFn, ptS_val0]
  · simp [csign, coordFn, ptS_val1]
  · simp [csign, coordFn, ptS_val2]

theorem coordFn_smooth (a : Fin 3) (k : ℕ) : sphereAtlas.Smooth k (coordFn a) := by
  intro b
  show ContDiffOn ℝ k (coordFn a ∘ ptS b) Set.univ
  have : coordFn a ∘ ptS b = fun y => csign b a * Fc a y := funext fun y => coord_pt b a y
  rw [this]
  exact (contDiff_const.mul (contDiff_Fc k a)).contDiffOn

/-! ### scalar multiples -/

section scalar
variable {g : Fin 2 → Fin 2 → Ev 2 → ℝ} {w : Ev 2 → ℝ} {F H : Ev 2 → ℝ} {x : Ev 2}

lemma Lch_const_mul (c : ℝ) : Lch g w (fun y => c * F y) x = c * Lch g w F x := by
  unfold Lch
  simp only [pderiv_const_mul]
  have e : ∀ i : Fin 2, (fun y => w y * ∑ j, g i j y * (c * pderiv F j y)) =
      fun y => c * (w y * ∑ j, g i j y * pderiv F j y) := fun i => funext fun y => by
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  simp only [e, pderiv_const_mul]
  rw [← Finset.mul_sum]
  ring

lemma Gch_const_mul (c d : ℝ) : Gch g (fun y => c * F y) (fun y => d * H y) x = c * d * Gch g F H x := by
  unfold Gch
  simp only [pderiv_const_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

end scalar

lemma Lch_coord (b : Bool) (a : Fin 3) (y : Ev 2) :
    Lch gS wS (coordFn a ∘ ptS b) y = -2 * coordFn a (ptS b y) := by
  have : coordFn a ∘ ptS b = fun y => csign b a * Fc a y := funext fun y => coord_pt b a y
  rw [this, Lch_const_mul, Lch_Fc, coord_pt]
  ring

lemma Gch_coord (b : Bool) (a a' : Fin 3) (y : Ev 2) :
    Gch gS (coordFn a ∘ ptS b) (coordFn a' ∘ ptS b) y =
      (if a = a' then 1 else 0) - coordFn a (ptS b y) * coordFn a' (ptS b y) := by
  have e : ∀ a : Fin 3, coordFn a ∘ ptS b = fun y => csign b a * Fc a y := fun a =>
    funext fun y => coord_pt b a y
  rw [e a, e a', Gch_const_mul, Gch_Fc, coord_pt, coord_pt]
  by_cases h : a = a'
  · subst h
    have := csign_sq b a
    simp only [ite_true]
    nlinarith [this]
  · simp [h]; ring

/-! ### gluing -/

theorem sphere_glueL_coord (a : Fin 3) :
    sphereAtlas.glueL (coordFn a) = fun p => -2 * coordFn a p := by
  funext p
  have h := Lch_coord (sphereAtlas.idx p) a (sphereAtlas.pos p)
  have hp := sphereAtlas.pt_pos p
  change ((sph (sphereAtlas.idx p)).pt (sphereAtlas.pos p)) = p at hp
  show Lch gS wS (coordFn a ∘ ptS (sphereAtlas.idx p)) (sphereAtlas.pos p) = _
  rw [h]
  change -2 * coordFn a ((sph (sphereAtlas.idx p)).pt (sphereAtlas.pos p)) = _
  rw [hp]

theorem sphere_glueΓ_coord (a a' : Fin 3) :
    sphereAtlas.glueΓ (coordFn a) (coordFn a') =
      fun p => (if a = a' then 1 else 0) - coordFn a p * coordFn a' p := by
  funext p
  have h := Gch_coord (sphereAtlas.idx p) a a' (sphereAtlas.pos p)
  have hp := sphereAtlas.pt_pos p
  change ((sph (sphereAtlas.idx p)).pt (sphereAtlas.pos p)) = p at hp
  show Gch gS (coordFn a ∘ ptS (sphereAtlas.idx p)) (coordFn a' ∘ ptS (sphereAtlas.idx p))
    (sphereAtlas.pos p) = _
  rw [h]
  change (if a = a' then 1 else 0) - coordFn a ((sph (sphereAtlas.idx p)).pt (sphereAtlas.pos p)) *
    coordFn a' ((sph (sphereAtlas.idx p)).pt (sphereAtlas.pos p)) = _
  rw [hp]

/-! ### `Γ₂` -/

lemma wS_inv (x : Ev 2) : (wS x)⁻¹ = ((1 + r2 x) / 2) ^ 2 := by
  have := one_add_r2_ne x
  unfold wS
  field_simp
  norm_num

/-- `L (1 - F²) = -(2 F L F + 2 Γ(F,F))` in the conformal chart (a product-rule instance) -/
lemma Lch_one_sub_sq {F : Ev 2 → ℝ} (hF : ContDiff ℝ 2 F) (x : Ev 2) :
    Lch gS wS (fun y => 1 - F y * F y) x = -(2 * F x * Lch gS wS F x + 2 * Gch gS F F x) := by
  have hd : ∀ y, DifferentiableAt ℝ F y := fun y => (hF.differentiable (by norm_num)) y
  have hpd : ∀ k y, DifferentiableAt ℝ (pderiv F k) y := fun k y =>
    (contDiffAt_pderiv hF.contDiffAt k).differentiableAt (by norm_num)
  have e : ∀ k : Fin 2, pderiv (fun y => 1 - F y * F y) k =
      fun y => -(F y * pderiv F k y + F y * pderiv F k y) := fun k => funext fun y => by
    rw [pderiv_sub (f := fun _ => (1 : ℝ)) (g := fun y => F y * F y) (differentiableAt_const _) ((hd y).mul (hd y)),
      pderiv_const,
      pderiv_mul (hd y) (hd y)]
    ring
  rw [Lch_conformal, Lch_conformal, Gch_conformal, wS_inv]
  simp only [e]
  have h2 : ∀ k : Fin 2, pderiv (fun y => -(F y * pderiv F k y + F y * pderiv F k y)) k x =
      -(2 * (pderiv F k x * pderiv F k x + F x * pderiv (pderiv F k) k x)) := fun k => by
    rw [pderiv_neg, pderiv_add (f := fun y => F y * pderiv F k y) (g := fun y => F y * pderiv F k y)
      ((hd x).mul (hpd k x)) ((hd x).mul (hpd k x)),
      pderiv_mul (hd x) (hpd k x)]
    ring
  simp only [h2, Finset.sum_neg_distrib, ← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

theorem sphere_glueΓ₂_coord (a : Fin 3) :
    sphereAtlas.glueΓ₂ (coordFn a) = fun p => 1 + coordFn a p ^ 2 := by
  funext p
  unfold Atlas.glueΓ₂
  rw [sphere_glueΓ_coord a a, sphere_glueL_coord a]
  set b : Bool := sphereAtlas.idx p with hb
  set y := sphereAtlas.pos p with hy
  have hp : (sph b).pt y = p := sphereAtlas.pt_pos p
  have hF : ContDiff ℝ 2 (Fc a) := contDiff_Fc 2 a
  have hc := csign_sq b a
  have h1 : sphereAtlas.glueL (fun p => (if a = a then 1 else 0) - coordFn a p * coordFn a p) p =
      6 * Fc a y ^ 2 - 2 := by
    show Lch gS wS ((fun p => (if a = a then (1 : ℝ) else 0) - coordFn a p * coordFn a p) ∘ ptS b) y = _
    have : ((fun p => (if a = a then (1 : ℝ) else 0) - coordFn a p * coordFn a p) ∘ ptS b) =
        fun y => 1 - Fc a y * Fc a y := funext fun y => by
      simp only [Function.comp_apply, coord_pt, ↓reduceIte]
      nlinarith [hc]
    rw [this, Lch_one_sub_sq hF, Lch_Fc, Gch_Fc]
    simp only [ite_true]
    ring
  have h2 : sphereAtlas.glueΓ (coordFn a) (fun p => -2 * coordFn a p) p = -2 * (1 - Fc a y ^ 2) := by
    show Gch gS (coordFn a ∘ ptS b) ((fun p => -2 * coordFn a p) ∘ ptS b) y = _
    have e1 : coordFn a ∘ ptS b = fun y => csign b a * Fc a y := funext fun y => coord_pt b a y
    have e2 : (fun p => -2 * coordFn a p) ∘ ptS b = fun y => (-2 * csign b a) * Fc a y :=
      funext fun y => by simp only [Function.comp_apply, coord_pt]; ring
    rw [e1, e2, Gch_const_mul, Gch_Fc]
    simp only [ite_true]
    nlinarith [hc]
  rw [h1, h2]
  have h3 : coordFn a p = csign b a * Fc a y := by rw [← hp]; exact coord_pt b a y
  rw [h3]
  nlinarith [hc]

theorem sphere_CD12_coord_eq (a : Fin 3) (p : S2) :
    sphereAtlas.glueΓ (coordFn a) (coordFn a) p + (1 / 2) * sphereAtlas.glueL (coordFn a) p ^ 2 =
      sphereAtlas.glueΓ₂ (coordFn a) p := by
  rw [sphere_glueΓ₂_coord, sphere_glueΓ_coord, sphere_glueL_coord]
  simp only [ite_true]
  ring

end MarkovTriple.BGL.Instances.Riemannian.R27
