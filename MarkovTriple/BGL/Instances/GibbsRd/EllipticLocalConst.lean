import Mathlib
import MarkovTriple.BGL.Instances.GibbsRd.EllipticE2Pre

/-!
# Local constants of an `EllData d` (R16, elliptic half; glue items)

* `EllData.exists_dens_lower`: `dens ≥ m > 0` on every compact set;
* `EllData.locL2_of_memLp`: `MemLp f 2 E.μ ⇒ LocL2 f` (Lebesgue `L²_loc`), since `μ = Z⁻¹ w dx` with `w` continuous positive;
* `EllData.local_ellipticity`: for `K` compact there is `λ > 0` with `Σ aᵢⱼ ξᵢ ξⱼ ≥ λ Σ ξᵢ²` on `K` (uniform ellipticity on compacts).
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace MarkovTriple.BGL.Instances.GibbsRd

open Elliptic

variable {d : ℕ}

namespace EllData
variable (E : EllData d)

lemma exists_dens_lower {K : Set (Rd d)} (hK : IsCompact K) :
    ∃ m : ℝ, 0 < m ∧ ∀ x ∈ K, m ≤ E.dens x := by
  by_cases hne : K.Nonempty
  · obtain ⟨x0, hx0, hmin⟩ := hK.exists_isMinOn hne E.dens_smooth.continuous.continuousOn
    exact ⟨E.dens x0, E.dens_pos x0, fun x hx => hmin hx⟩
  · exact ⟨1, one_pos, fun x hx => absurd ⟨x, hx⟩ hne⟩

/-- `L²(μ)` implies `L²_loc` for Lebesgue measure -/
theorem locL2_of_memLp {f : Rd d → ℝ} (hf : MemLp f 2 E.μ) : LocL2 f := by
  intro K hK
  obtain ⟨m, hm, hmK⟩ := E.exists_dens_lower hK
  have hle : volume.restrict K ≤ (ENNReal.ofReal (1 / m)) • E.μ := by
    refine Measure.le_iff.2 fun A hA => ?_
    rw [Measure.restrict_apply hA, Measure.smul_apply, smul_eq_mul]
    unfold EllData.μ
    rw [withDensity_apply _ hA]
    have h1 : ∫⁻ x in A ∩ K, ENNReal.ofReal m ≤ ∫⁻ x in A, ENNReal.ofReal (E.dens x) := by
      calc ∫⁻ x in A ∩ K, ENNReal.ofReal m ≤ ∫⁻ x in A ∩ K, ENNReal.ofReal (E.dens x) :=
            setLIntegral_mono' (hA.inter hK.measurableSet) fun x hx => ENNReal.ofReal_le_ofReal (hmK x hx.2)
        _ ≤ ∫⁻ x in A, ENNReal.ofReal (E.dens x) := lintegral_mono_set Set.inter_subset_left
    rw [setLIntegral_const] at h1
    have : volume (A ∩ K) = ENNReal.ofReal (1 / m) * (ENNReal.ofReal m * volume (A ∩ K)) := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), one_div, inv_mul_cancel₀ hm.ne']
      simp
    rw [this]
    exact mul_le_mul_right h1 _
  have : Fact (ENNReal.ofReal (1 / m) ≠ ⊤) := ⟨ENNReal.ofReal_ne_top⟩
  exact (hf.smul_measure ENNReal.ofReal_ne_top).mono_measure hle

/-- **Uniform ellipticity on compacts** -/
theorem local_ellipticity {K : Set (Rd d)} (hK : IsCompact K) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ x ∈ K, ∀ ξ : Rd d, lam * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, E.a i j x * ξ i * ξ j := by
  classical
  by_cases hd : d = 0
  · subst hd; exact ⟨1, one_pos, fun x _ ξ => by simp⟩
  set Sph : Set (Rd d) := Metric.sphere 0 1 with hSph
  have hSc : IsCompact Sph := isCompact_sphere 0 1
  have hcont : Continuous (fun p : Rd d × Rd d => ∑ i, ∑ j, E.a i j p.1 * p.2 i * p.2 j) := by
    refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
    exact (((E.a_smooth i j).continuous.comp continuous_fst).mul ((continuous_apply i).comp continuous_snd)).mul
      ((continuous_apply j).comp continuous_snd)
  by_cases hne : K.Nonempty
  · have hne2 : Sph.Nonempty := by
      have : Nonempty (Fin d) := ⟨⟨0, Nat.pos_of_ne_zero hd⟩⟩
      exact NormedSpace.sphere_nonempty.2 zero_le_one
    obtain ⟨p0, hp0, hmin⟩ := (hK.prod hSc).exists_isMinOn (hne.prod hne2) hcont.continuousOn
    set lam0 := ∑ i, ∑ j, E.a i j p0.1 * p0.2 i * p0.2 j with hlam0
    have hξ0 : p0.2 ≠ 0 := by
      intro h0
      have : ‖p0.2‖ = 1 := by simpa [hSph] using hp0.2
      rw [h0] at this; simp at this
    have hpos : 0 < lam0 := E.a_pos p0.1 p0.2 hξ0
    refine ⟨lam0 / d, by positivity, fun x hx ξ => ?_⟩
    by_cases hξ : ξ = 0
    · simp [hξ]
    · have hn : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
      set η : Rd d := ‖ξ‖⁻¹ • ξ with hη
      have hηs : η ∈ Sph := by
        simp [hSph, hη, norm_smul, hn.ne']
      have hmin' := hmin (show (x, η) ∈ K ×ˢ Sph from ⟨hx, hηs⟩)
      have hscale : ∑ i, ∑ j, E.a i j x * ξ i * ξ j = ‖ξ‖ ^ 2 * ∑ i, ∑ j, E.a i j x * η i * η j := by
        simp only [hη, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        field_simp
      have hsq : ∑ i, ξ i ^ 2 ≤ d * ‖ξ‖ ^ 2 := by
        calc ∑ i, ξ i ^ 2 ≤ ∑ _i : Fin d, ‖ξ‖ ^ 2 := Finset.sum_le_sum fun i _ => by
              have := norm_le_pi_norm ξ i
              rw [Real.norm_eq_abs] at this
              nlinarith [abs_nonneg (ξ i), sq_abs (ξ i)]
          _ = d * ‖ξ‖ ^ 2 := by simp
      rw [hscale]
      have hdpos : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd
      calc lam0 / d * ∑ i, ξ i ^ 2 ≤ lam0 / d * (d * ‖ξ‖ ^ 2) :=
            mul_le_mul_of_nonneg_left hsq (by positivity)
        _ = lam0 * ‖ξ‖ ^ 2 := by field_simp
        _ ≤ ‖ξ‖ ^ 2 * ∑ i, ∑ j, E.a i j x * η i * η j := by
            have h3 : lam0 ≤ ∑ i, ∑ j, E.a i j x * η i * η j := hmin'
            calc lam0 * ‖ξ‖ ^ 2 = ‖ξ‖ ^ 2 * lam0 := by ring
              _ ≤ _ := mul_le_mul_of_nonneg_left h3 (sq_nonneg _)
  · exact ⟨1, one_pos, fun x hx => absurd ⟨x, hx⟩ hne⟩

/-- **local upper bound** of the co-metric on compact sets (automatic from continuity; replaces the former global
bound `a ≤ Λ`): for `K` compact there is `Λ` with `Σ aᵢⱼ vᵢ vⱼ ≤ Λ Σ vᵢ²` on `K`. -/
theorem local_upper {K : Set (Rd d)} (hK : IsCompact K) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ x ∈ K, ∀ v : Rd d, ∑ i, ∑ j, E.a i j x * v i * v j ≤ Λ * ∑ i, v i ^ 2 := by
  classical
  have hb : ∀ i j : Fin d, ∃ Bij : ℝ, ∀ x ∈ K, ‖E.a i j x‖ ≤ Bij := fun i j =>
    hK.exists_bound_of_continuousOn (E.a_smooth i j).continuous.continuousOn
  choose Bij hBij using hb
  set B : ℝ := ∑ i, ∑ j, |Bij i j| with hB
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hab : ∀ x ∈ K, ∀ i j, |E.a i j x| ≤ B := by
    intro x hx i j
    have h1 : |E.a i j x| ≤ |Bij i j| := by
      have := hBij i j x hx
      rw [Real.norm_eq_abs] at this
      exact this.trans (le_abs_self _)
    refine h1.trans ?_
    have h2 : |Bij i j| ≤ ∑ j, |Bij i j| :=
      Finset.single_le_sum (f := fun j => |Bij i j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
    have h3 : ∑ j, |Bij i j| ≤ B :=
      Finset.single_le_sum (f := fun i => ∑ j, |Bij i j|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)
    linarith
  refine ⟨B * d, by positivity, fun x hx v => ?_⟩
  calc ∑ i, ∑ j, E.a i j x * v i * v j ≤ ∑ i, ∑ j, B * (|v i| * |v j|) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by
          calc E.a i j x * v i * v j ≤ |E.a i j x * v i * v j| := le_abs_self _
            _ = |E.a i j x| * (|v i| * |v j|) := by rw [abs_mul, abs_mul]; ring
            _ ≤ B * (|v i| * |v j|) :=
              mul_le_mul_of_nonneg_right (hab x hx i j) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = B * (∑ i, |v i|) ^ 2 := by
        rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]
    _ ≤ B * (d * ∑ i, |v i| ^ 2) := by
        refine mul_le_mul_of_nonneg_left ?_ hB0
        have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin d))) (f := fun i => |v i|)
        simpa using this
    _ = B * d * ∑ i, v i ^ 2 := by
        simp only [sq_abs]; ring

end EllData

end MarkovTriple.BGL.Instances.GibbsRd
