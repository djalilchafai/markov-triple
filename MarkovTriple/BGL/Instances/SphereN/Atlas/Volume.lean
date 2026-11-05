import Mathlib
import MarkovTriple.BGL.Instances.SphereN.Atlas.Vol3
import MarkovTriple.BGL.Instances.SphereN.Atlas.Norm

/-!
# The chart integral on `S²` (Round 29, stream R, R2)

Change of variables for the cone map `Φ_b(y,r) = r P_b(y)` (`|det DΦ_b| = r² w_S(y)`) against the polar decomposition of `σ0`
(`polar_gauss`): `∫_{ℝ²} f(P_b(y)) w_S(y) dy = ∫ f dσ0`, whence `∫ (f∘e∘pt_b) w_S = (∫ w_S) ∫ f dσ`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal Real

namespace MarkovTriple.BGL.SphereN.Atlas

open MarkovTriple.BGL.Instances.Riemannian.R27

lemma nrm_Φ (b : Bool) {v : Fin 3 → ℝ} (hv : v ∈ Hs) : nrm (Φ b v) = v 2 := by
  have h : nrm (Φ b v) ^ 2 = v 2 ^ 2 := by
    rw [nrm_sq]
    simpa [LebesgueRd.sq] using nrm_sq_Φ b v
  exact (sq_eq_sq₀ (nrm_nonneg _) (le_of_lt hv)).1 h

lemma ext_Φ (f : Sph 3 → ℝ) (b : Bool) {v : Fin 3 → ℝ} (hv : v ∈ Hs) :
    ext f (Φ b v) = f (eS2 (ptS b (yv v))) := by
  have h : Φ b v = v 2 • Pc b (yv v) := rfl
  rw [h, ext_smul f hv]
  have := congrFun (comp_eq f b) (yv v)
  simpa using this.symm

lemma step1 (b : Bool) (f : Sph 3 → ℝ) :
    ∫ z : Fin 3 → ℝ, Real.exp (-(nrm z) ^ 2) * ext f z =
      ∫ v in Hs, (v 2 ^ 2 * Real.exp (-(v 2) ^ 2)) * (wS (yv v) * f (eS2 (ptS b (yv v)))) := by
  have hHs : MeasurableSet Hs := isOpen_lt continuous_const (continuous_apply 2) |>.measurableSet
  have hae : ∀ᵐ z ∂(volume : Measure (Fin 3 → ℝ)), z ∈ Φ b '' Hs := by
    rw [ae_iff]
    refine measure_mono_null (fun z hz => ?_) axis_null
    by_contra hc
    exact hz (surj_Φ b hc)
  have h1 : ∫ z : Fin 3 → ℝ, Real.exp (-(nrm z) ^ 2) * ext f z =
      ∫ z in Φ b '' Hs, Real.exp (-(nrm z) ^ 2) * ext f z := by
    rw [Measure.restrict_eq_self_of_ae_mem hae]
  rw [h1, integral_image_eq_integral_abs_det_fderiv_smul volume hHs
    (fun v _ => (hasFDerivAt_Φ b v).hasFDerivWithinAt) (injOn_Φ b)]
  refine setIntegral_congr_fun hHs fun v hv => ?_
  simp only [smul_eq_mul, det_Ljac, abs_det_Mjac, nrm_Φ b hv, ext_Φ f b hv]
  ring

lemma step2 (b : Bool) (f : Sph 3 → ℝ) :
    ∫ v in Hs, (v 2 ^ 2 * Real.exp (-(v 2) ^ 2)) * (wS (yv v) * f (eS2 (ptS b (yv v)))) =
      Jn 3 * ∫ y : Ev 2, wS y * f (eS2 (ptS b y)) := by
  have hHs : MeasurableSet Hs := isOpen_lt continuous_const (continuous_apply 2) |>.measurableSet
  rw [← integral_indicator hHs]
  have hp := volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) (Fin.last 2)
  have e1 : ∀ v : Fin 3 → ℝ, Hs.indicator (fun v => (v 2 ^ 2 * Real.exp (-(v 2) ^ 2)) *
      (wS (yv v) * f (eS2 (ptS b (yv v))))) v =
      (fun p : ℝ × (Fin 2 → ℝ) => (Ioi (0 : ℝ)).indicator (fun r => r ^ 2 * Real.exp (-r ^ 2)) p.1 *
        (wS p.2 * f (eS2 (ptS b p.2)))) (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) (Fin.last 2) v) := by
    intro v
    have hev : MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) (Fin.last 2) v = (v 2, yv v) :=
      Prod.ext rfl (funext fun j => by
        show v ((Fin.last 2).succAbove j) = v j.castSucc
        rw [Fin.succAbove_last])
    rw [hev]
    beta_reduce
    by_cases hv : 0 < v 2
    · rw [Set.indicator_of_mem (show v ∈ Hs from hv), Set.indicator_of_mem (show v 2 ∈ Ioi (0 : ℝ) from hv)]
    · rw [Set.indicator_of_notMem (show v ∉ Hs from hv),
        Set.indicator_of_notMem (show v 2 ∉ Ioi (0 : ℝ) from hv)]
      simp
  simp only [e1]
  rw [hp.integral_comp' (g := fun p : ℝ × (Fin 2 → ℝ) =>
    (Ioi (0 : ℝ)).indicator (fun r => r ^ 2 * Real.exp (-r ^ 2)) p.1 * (wS p.2 * f (eS2 (ptS b p.2))))]
  rw [Measure.volume_eq_prod, integral_prod_mul
    (fun r : ℝ => (Ioi (0 : ℝ)).indicator (fun r => r ^ 2 * Real.exp (-r ^ 2)) r)
    (fun y : Ev 2 => wS y * f (eS2 (ptS b y)))]
  congr 1
  rw [integral_indicator measurableSet_Ioi]
  unfold Jn
  simp

theorem chart_polar (b : Bool) (f : Sph 3 → ℝ) :
    ∫ y : Ev 2, wS y * f (eS2 (ptS b y)) = ∫ z, f z ∂σ0 3 := by
  have h := polar_gauss (n := 3) (by norm_num) f
  rw [step1 b f, step2 b f] at h
  have hJ := Jn_pos 3
  have : (Jn 3) * (∫ y : Ev 2, wS y * f (eS2 (ptS b y))) = (Jn 3) * ∫ z, f z ∂σ0 3 := by
    rw [h]; ring
  exact mul_left_cancel₀ hJ.ne' this

theorem chart_integral {f : Sph 3 → ℝ} (_hf : f ∈ A₀S 3) (b : Bool) :
    ∫ y : Ev 2, f (eS2 (ptS b y)) * wS y = (∫ y : Ev 2, wS y) * ∫ x, f x ∂σ 3 := by
  have h1 : ∫ y : Ev 2, wS y = (σ0 3 Set.univ).toReal := by
    have := chart_polar b (fun _ => (1 : ℝ))
    simp only [mul_one] at this
    rw [this]
    simp [Measure.real]
  have hne : (σ0 3 Set.univ).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.2 ⟨σ0_univ_ne_zero (by norm_num), σ0_univ_ne_top 3⟩
  have e : ∀ y : Ev 2, f (eS2 (ptS b y)) * wS y = wS y * f (eS2 (ptS b y)) := fun y => mul_comm _ _
  simp only [e]
  rw [chart_polar, h1, integral_σ]
  field_simp

lemma σ0_three : (σ0 3 Set.univ).toReal = 4 * π := by
  unfold σ0
  rw [Measure.toSphere_apply_univ, EuclideanSpace.volume_ball]
  have hΓ : Real.Gamma (((Fintype.card (Fin 3) : ℕ) : ℝ) / 2 + 1) = 3 / 4 * √π := by
    have h := Real.Gamma_nat_add_half 2
    have e : (((Fintype.card (Fin 3) : ℕ) : ℝ) / 2 + 1) = (2 : ℕ) + 1 / 2 := by
      simp; norm_num
    rw [e, h]
    simp
    ring
  rw [hΓ]
  simp only [Fintype.card_fin, finrank_euclideanSpace]
  have hπ : 0 < √π := Real.sqrt_pos.2 Real.pi_pos
  have hval : √π ^ 3 / (3 / 4 * √π) = 4 / 3 * π := by
    have h2 : √π ^ 2 = π := Real.sq_sqrt Real.pi_pos.le
    field_simp
    nlinarith [h2]
  rw [hval]
  simp only [ENNReal.ofReal_one, one_pow, one_mul]
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
  simp
  ring

/-- bonus: the total mass of `w_S dy` is the area `4π` of the unit 2-sphere -/
theorem integral_wS : ∫ y : Ev 2, wS y = 4 * π := by
  have := chart_polar true (fun _ => (1 : ℝ))
  simp only [mul_one] at this
  rw [this, ← σ0_three]
  simp [Measure.real]

end MarkovTriple.BGL.SphereN.Atlas
