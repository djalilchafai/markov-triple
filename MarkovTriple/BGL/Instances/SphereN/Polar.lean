import Mathlib
import MarkovTriple.BGL.Instances.SphereN.Meas

/-!
# Polar coordinates for the Lebesgue integral (Round 28, stream L)

`∫_{ℝ^n} φ(|y|) h̃(y) dy = (∫_{S^{n-1}} h dσ0) · ∫_0^∞ r^{n-1} φ(r) dr`, from Mathlib's
`Measure.measurePreserving_homeomorphUnitSphereProd` (cone/radial construction of the surface measure).
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace MarkovTriple.BGL.SphereN

open LebesgueRd

variable {n : ℕ}

lemma ext_ofLp (h : Sph n → ℝ) {x : Ee n} (hx : x ≠ 0) :
    ext h (WithLp.ofLp x) = h ((homeomorphUnitSphereProd (Ee n) ⟨x, hx⟩).1) := by
  have hy : (WithLp.ofLp x : Fin n → ℝ) ≠ 0 := by
    intro h0; apply hx; simpa using congrArg (WithLp.toLp 2) h0
  rw [ext_of_ne h hy]
  congr 1
  apply Subtype.ext
  ext i
  rw [proj_coe_apply, homeomorphUnitSphereProd_apply_fst_coe]
  simp [nrm]

lemma polar_E (hn : 1 ≤ n) (φ : ℝ → ℝ) (h : Sph n → ℝ) :
    ∫ x : Ee n, φ ‖x‖ * ext h (WithLp.ofLp x) = (∫ z, h z ∂σ0 n) * ∫ y in Ioi (0 : ℝ), y ^ (n - 1) * φ y := by
  have : Nontrivial (Ee n) := by
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    infer_instance
  have hdim : Module.finrank ℝ (Ee n) = n := finrank_euclideanSpace_fin
  calc ∫ x : Ee n, φ ‖x‖ * ext h (WithLp.ofLp x)
      = ∫ x : ({0}ᶜ : Set (Ee n)), φ ‖x.1‖ * ext h (WithLp.ofLp x.1)
          ∂(Measure.comap Subtype.val (volume : Measure (Ee n))) := by
        rw [integral_subtype_comap (measurableSet_singleton _).compl
          (fun x : Ee n => φ ‖x‖ * ext h (WithLp.ofLp x)), restrict_compl_singleton]
    _ = ∫ x : ({0}ᶜ : Set (Ee n)),
          (fun z : Sph n × Ioi (0 : ℝ) => h z.1 * φ z.2) (homeomorphUnitSphereProd (Ee n) x)
          ∂(Measure.comap Subtype.val (volume : Measure (Ee n))) := by
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        simp only [homeomorphUnitSphereProd_apply_snd_coe]
        rw [ext_ofLp h x.2, mul_comm]
    _ = ∫ z : Sph n × Ioi (0 : ℝ), h z.1 * φ z.2
          ∂((volume : Measure (Ee n)).toSphere.prod (Measure.volumeIoiPow (Module.finrank ℝ (Ee n) - 1))) :=
        (Measure.measurePreserving_homeomorphUnitSphereProd (volume : Measure (Ee n))).integral_comp
          (Homeomorph.measurableEmbedding _) (fun z : Sph n × Ioi (0 : ℝ) => h z.1 * φ z.2)
    _ = (∫ z, h z ∂σ0 n) * ∫ r : Ioi (0 : ℝ), φ r ∂(Measure.volumeIoiPow (n - 1)) := by
        rw [integral_prod_mul (fun z : Sph n => h z) (fun r : Ioi (0 : ℝ) => φ r), hdim]
        rfl
    _ = _ := by
        congr 1
        simp only [Measure.volumeIoiPow, ENNReal.ofReal]
        rw [integral_withDensity_eq_integral_smul,
          integral_subtype_comap measurableSet_Ioi fun a => Real.toNNReal (a ^ (n - 1)) • φ a,
          setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_]
        · rw [NNReal.smul_def, Real.coe_toNNReal _ (pow_nonneg hx.out.le _), smul_eq_mul]
        · exact (measurable_subtype_coe.pow_const _).real_toNNReal

lemma polar (hn : 1 ≤ n) (φ : ℝ → ℝ) (h : Sph n → ℝ) :
    ∫ y : Fin n → ℝ, φ (nrm y) * ext h y = (∫ z, h z ∂σ0 n) * ∫ y in Ioi (0 : ℝ), y ^ (n - 1) * φ y := by
  rw [← polar_E hn φ h]
  exact ((PiLp.volume_preserving_ofLp (Fin n)).integral_comp
    (MeasurableEquiv.toLp 2 (Fin n → ℝ)).symm.measurableEmbedding
    (fun y : Fin n → ℝ => φ (nrm y) * ext h y)).symm

end MarkovTriple.BGL.SphereN
