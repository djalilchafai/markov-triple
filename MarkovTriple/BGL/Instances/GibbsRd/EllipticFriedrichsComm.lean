import Mathlib
import MarkovTriple.BGL.Instances.GibbsRd.EllipticFriedrichsYoung

/-!
# The Friedrichs commutator formula (R16, Friedrichs step)

Statement C1 of `STATEMENTS_R16_Friedrichs.md`: for `Pop b φ = Σᵢ ∂ᵢ(Σⱼ bᵢⱼ ∂ⱼ φ)` and a mollifier `ρ`,
`ρ ⋆ Pop b φ − Pop b (ρ ⋆ φ)` is an explicit sum of first-order commutator integrals (Friedrichs 1944, Lemma 1;
the second-order commutator reduces to the first-order one because `∂ᵢ (ρ ⋆ f) = (∂ᵢρ) ⋆ f`).
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace MarkovTriple.BGL.Instances.GibbsRd.Elliptic

open MarkovTriple.BGL (pderiv)

variable {d : ℕ}

/-- the divergence-form operator `Pop b φ = Σᵢ ∂ᵢ (Σⱼ bᵢⱼ ∂ⱼ φ)` -/
noncomputable def Pop (b : Fin d → Fin d → (Fin d → ℝ) → ℝ) (φ : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : ℝ :=
  ∑ i, pderiv (fun y => ∑ j, b i j y * pderiv φ j y) i x

section
variable {b : Fin d → Fin d → (Fin d → ℝ) → ℝ} {ρ H φ : (Fin d → ℝ) → ℝ}

lemma sm_Pop (hb : ∀ i j, Sm (b i j)) (hφ : Sm φ) : Sm (Pop b φ) :=
  ContDiff.sum fun i _ => by
    have : Sm (fun y => ∑ j, b i j y * pderiv φ j y) := ContDiff.sum fun j _ => (hb i j).mul (hφ.pderiv j)
    exact this.pderiv i

/-- `∂ᵢ (ρ ⋆ H) = (∂ᵢρ) ⋆ H` for a smooth compactly supported `H` -/
lemma pderiv_moll_ker (hρ : Sm ρ) (hH : Sm H) (hHc : HasCompactSupport H) (i : Fin d) (x : Fin d → ℝ) :
    pderiv (moll ρ H) i x = ∫ y, pderiv ρ i (x - y) * H y := by
  have hcomm : moll ρ H = moll H ρ := by
    funext z
    rw [moll_eq]; unfold moll
    exact integral_congr_ae (Eventually.of_forall fun y => by ring)
  rw [hcomm, pderiv_moll hH hHc (weakDeriv_of_smooth hρ i) x]
  unfold moll
  exact integral_congr_ae (Eventually.of_forall fun y => mul_comm _ _)

lemma integrable_ker {D c : (Fin d → ℝ) → ℝ} (hD : Continuous D) (hc : Continuous c) (hcs : HasCompactSupport c)
    (x : Fin d → ℝ) : Integrable (fun y => D (x - y) * c y) :=
  ((hD.comp (continuous_const.sub continuous_id)).mul hc).integrable_of_hasCompactSupport hcs.mul_left

lemma moll_finset_sum {ι : Type*} (s : Finset ι) {F : ι → (Fin d → ℝ) → ℝ} (hρ : Sm ρ)
    (hρc : HasCompactSupport ρ) (hF : ∀ k, Continuous (F k)) (x : Fin d → ℝ) :
    moll ρ (fun y => ∑ k ∈ s, F k y) x = ∑ k ∈ s, moll ρ (F k) x := by
  unfold moll
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum]
  intro k _
  exact hρc.convolutionExists_left (ContinuousLinearMap.mul ℝ ℝ) hρ.continuous (hF k).locallyIntegrable x

lemma hcs_of_tsupport {f : (Fin d → ℝ) → ℝ} {K : Set (Fin d → ℝ)} (hK : IsCompact K) (h : ∀ x, x ∉ K → f x = 0) :
    HasCompactSupport f := HasCompactSupport.intro hK h

/-- **C1** the Friedrichs commutator formula -/
theorem comm_formula (hb : ∀ i j, Sm (b i j)) (hρ : Sm ρ) (hρc : HasCompactSupport ρ) (hφ : Sm φ)
    (hφc : HasCompactSupport φ) (x : Fin d → ℝ) :
    moll ρ (Pop b φ) x - Pop b (moll ρ φ) x =
      ∑ i, ∑ j, ((∫ y, pderiv ρ i (x - y) * (b i j y * pderiv φ j y))
        - pderiv (b i j) i x * moll ρ (pderiv φ j) x
        - b i j x * ∫ y, pderiv ρ i (x - y) * pderiv φ j y) := by
  have hg : ∀ j, Sm (pderiv φ j) := fun j => hφ.pderiv j
  have hgc : ∀ j, HasCompactSupport (pderiv φ j) := fun j => hφc.fderiv_apply ℝ (Pi.single j 1)
  have hHi : ∀ i, Sm (fun y => ∑ j, b i j y * pderiv φ j y) := fun i =>
    ContDiff.sum fun j _ => (hb i j).mul (hg j)
  have hHc : ∀ i, HasCompactSupport (fun y => ∑ j, b i j y * pderiv φ j y) := fun i =>
    hcs_of_tsupport (hφc : IsCompact (tsupport φ)) fun y hy => by
      refine Finset.sum_eq_zero fun j _ => ?_
      have : pderiv φ j y = 0 := by
        by_contra hne
        exact hy (support_fderiv_subset ℝ (show fderiv ℝ φ y ≠ 0 from fun h0 => hne (by simp [pderiv, h0])))
      simp [this]
  -- the moll side
  have e1 : moll ρ (Pop b φ) x = ∑ i, ∑ j, ∫ y, pderiv ρ i (x - y) * (b i j y * pderiv φ j y) := by
    unfold Pop
    rw [moll_finset_sum _ hρ hρc (fun i => ((hHi i).pderiv i).continuous)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← pderiv_moll hρ hρc (weakDeriv_of_smooth (hHi i) i) x,
      pderiv_moll_ker hρ (hHi i) (hHc i) i x]
    simp_rw [Finset.mul_sum]
    rw [integral_finsetSum]
    intro j _
    exact integrable_ker (hρ.pderiv i).continuous ((hb i j).continuous.mul (hg j).continuous)
      ((hgc j).mul_left) x
  -- the `Pop b (moll ρ φ)` side
  have e2 : ∀ j, pderiv (moll ρ φ) j = moll ρ (pderiv φ j) := fun j => by
    funext z; exact pderiv_moll hρ hρc (weakDeriv_of_smooth hφ j) z
  have hmg : ∀ j, Sm (moll ρ (pderiv φ j)) := fun j =>
    moll_contDiff hρ hρc (hg j).continuous.locallyIntegrable
  have e3 : Pop b (moll ρ φ) x = ∑ i, ∑ j, (pderiv (b i j) i x * moll ρ (pderiv φ j) x +
      b i j x * ∫ y, pderiv ρ i (x - y) * pderiv φ j y) := by
    unfold Pop
    refine Finset.sum_congr rfl fun i _ => ?_
    simp_rw [e2]
    rw [pderiv_sum _ (fun j => (hb i j).mul (hmg j)) i x]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [pderiv_mul' (hb i j) (hmg j), pderiv_moll_ker hρ (hg j) (hgc j) i x]
  rw [e1, e3, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

end

end MarkovTriple.BGL.Instances.GibbsRd.Elliptic
