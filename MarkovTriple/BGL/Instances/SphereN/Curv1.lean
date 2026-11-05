import Mathlib
import MarkovTriple.BGL.Instances.SphereN.Triple
import MarkovTriple.BGL.Instances.LebesgueRd.Gamma2

/-!
# Local calculus at a point of the sphere (Round 28, stream L, group L3)

Product rule `L(fg) = f Lg + g Lf + 2Γ(f,g)` for the intrinsic operators and `ΓA = Γ`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace MarkovTriple.BGL.SphereN

open LebesgueRd

variable {n : ℕ}

lemma dd_ev {F G : (Fin n → ℝ) → ℝ} {y : Fin n → ℝ} (h : F =ᶠ[𝓝 y] G) (i : Fin n) :
    dd i F =ᶠ[𝓝 y] dd i G := by
  filter_upwards [h.eventuallyEq_nhds] with z hz using dd_congr hz i

lemma Lf_ev {F G : (Fin n → ℝ) → ℝ} {y : Fin n → ℝ} (h : F =ᶠ[𝓝 y] G) :
    Lf F =ᶠ[𝓝 y] Lf G := by
  have : ∀ i, dd i (dd i F) =ᶠ[𝓝 y] dd i (dd i G) := fun i => by
    have h1 := dd_ev h i
    filter_upwards [h1.eventuallyEq_nhds] with z hz using dd_congr hz i
  filter_upwards [eventually_all.2 this] with z hz
  exact Finset.sum_congr rfl fun i _ => hz i

lemma Gf_ev {F G F' G' : (Fin n → ℝ) → ℝ} {y : Fin n → ℝ} (h : F =ᶠ[𝓝 y] F') (h' : G =ᶠ[𝓝 y] G') :
    Gf F G =ᶠ[𝓝 y] Gf F' G' := by
  filter_upwards [eventually_all.2 (dd_ev h), eventually_all.2 (dd_ev h')] with z hz hz'
  exact Finset.sum_congr rfl fun i _ => by rw [hz i, hz' i]

lemma Lf_congr {F G : (Fin n → ℝ) → ℝ} {y : Fin n → ℝ} (h : F =ᶠ[𝓝 y] G) : Lf F y = Lf G y :=
  (Lf_ev h).self_of_nhds

lemma Gf_congr {F G F' G' : (Fin n → ℝ) → ℝ} {y : Fin n → ℝ} (h : F =ᶠ[𝓝 y] F') (h' : G =ᶠ[𝓝 y] G') :
    Gf F G y = Gf F' G' y :=
  (Gf_ev h h').self_of_nhds

/-- at a point `y` with `|y| > 3/10`, the cut-off agrees with `F` near `y`. -/
lemma hat_ev {F : (Fin n → ℝ) → ℝ} {y : Fin n → ℝ} (hy : 3 / 10 < nrm y) : hat F =ᶠ[𝓝 y] F :=
  hat_eventuallyEq hy

lemma sphere_far (x : Sph n) : 3 / 10 < nrm (cv (x : Ee n)) := by
  rw [nrm_cv_sph]; norm_num

/-- the intrinsic product rule. -/
theorem LS_mul {f g : Sph n → ℝ} (hf : f ∈ A₀S n) (hg : g ∈ A₀S n) (x : Sph n) :
    LS (f * g) x = f x * LS g x + g x * LS f x + 2 * ΓS f g x := by
  have hfar := sphere_far x
  set y := cv (x : Ee n) with hy
  have e1 : ext (f * g) =ᶠ[𝓝 y] hat (ext f) * hat (ext g) := by
    rw [ext_mul]
    filter_upwards [hat_ev (F := ext f) hfar, hat_ev (F := ext g) hfar] with z h1 h2
    simp [h1, h2]
  have hF : Sm (hat (ext f)) := Sm_hat hf
  have hG : Sm (hat (ext g)) := Sm_hat hg
  have key := Lf_mul hF hG y
  show Lf (ext (f * g)) y = _
  rw [Lf_congr e1, key]
  have v1 : hat (ext f) y = f x := by
    rw [(hat_ev hfar).self_of_nhds, hy, ext_cv]
  have v2 : hat (ext g) y = g x := by
    rw [(hat_ev hfar).self_of_nhds, hy, ext_cv]
  rw [v1, v2]
  have l1 : Lf (hat (ext g)) y = LS g x := Lf_congr (hat_ev hfar)
  have l2 : Lf (hat (ext f)) y = LS f x := Lf_congr (hat_ev hfar)
  have l3 : Gf (hat (ext f)) (hat (ext g)) y = ΓS f g x := Gf_congr (hat_ev hfar) (hat_ev hfar)
  rw [l1, l2, l3]

/-- `ΓA = Γ` for the intrinsic operators (the book's formula `Γ = ½(L(fg) − fLg − gLf)`). -/
theorem ΓA_eq_ΓS (hn : 2 ≤ n) {f g : Sph n → ℝ} (hf : f ∈ A₀S n) (hg : g ∈ A₀S n) :
    (sphereDiffusion n hn).ΓA f g = ΓS f g := by
  funext x
  show (LS (f * g) x - f x * LS g x - g x * LS f x) / 2 = _
  rw [LS_mul hf hg]
  ring

end MarkovTriple.BGL.SphereN
