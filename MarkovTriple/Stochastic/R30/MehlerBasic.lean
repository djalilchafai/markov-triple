import Mathlib
import MarkovTriple.Stochastic.R29.GaussRd
import MarkovTriple.BGL.Instances.LebesgueRd.Full.HeatDerivAux5
import MarkovTriple.BGL.Instances.LebesgueRd.Full.HeatDerivAux4
import MarkovTriple.BGL.Instances.LebesgueRd.Full.HeatAPI

/-!
# Round 30 (S), part 2: the Mehler average `Mh a c φ (x) = ∫ φ(a x + c z) dγ(z)` on `ℝ^d` for `φ ∈ C_c^∞`

`Mh a c φ x = heatRd (-c) φ (a x)`, so smoothness and derivatives come from the heat-flow API of Round 24.
The Ornstein-Uhlenbeck generator `Lou g x = Σ ∂ᵢ∂ᵢ g - Σ xᵢ ∂ᵢ g` satisfies
`Lou (Mh a c φ) = a² Mh a c (Δφ) - a Σ xᵢ Mh a c (∂ᵢ φ)`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace MarkovTriple.Stochastic.R30

open MarkovTriple.BGL.LebesgueRd

variable {d : ℕ} {φ : (Fin d → ℝ) → ℝ}

/-- the Mehler average -/
noncomputable def Mh (a c : ℝ) (φ : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : ℝ :=
  ∫ z, φ (a • x + c • z) ∂(gam d)

/-- the Ornstein-Uhlenbeck generator on smooth functions: `Δ g - x·∇ g` -/
noncomputable def Lou (g : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : ℝ :=
  ∑ i, dd i (dd i g) x - ∑ i, x i * dd i g x

lemma Mh_eq_heat (a c : ℝ) (φ : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) :
    Mh a c φ x = heatRd (-c) φ (a • x) := by
  simp [Mh, heatRd]

lemma Mh_smooth (hφ : φ ∈ A₀ d) (a c : ℝ) : Sm (Mh a c φ) := by
  have : Mh a c φ = fun x => heatRd (-c) φ (a • x) := funext (Mh_eq_heat a c φ)
  rw [this]
  exact (heatRd_smooth hφ (-c)).comp (by fun_prop)

lemma dd_Mh (hφ : φ ∈ A₀ d) (a c : ℝ) (i : Fin d) :
    dd i (Mh a c φ) = fun x => a * Mh a c (dd i φ) x := by
  funext x
  have h1 : Mh a c φ = fun x => heatRd (-c) φ (a • x) := funext (Mh_eq_heat a c φ)
  have hd := (hasFDerivAt_of (heatRd_smooth hφ (-c)) (a • x)).comp x
    ((hasFDerivAt_id x).const_smul a)
  unfold dd
  rw [h1]
  have := hd.fderiv
  rw [show (fun x => heatRd (-c) φ (a • x)) = heatRd (-c) φ ∘ (fun x => a • x) from rfl, this]
  simp only [ContinuousLinearMap.comp_apply, smul_apply, ContinuousLinearMap.id_apply]
  have h2 : fderiv ℝ (heatRd (-c) φ) (a • x) (Pi.single i 1) = heatRd (-c) (dd i φ) (a • x) :=
    congrFun (dd_heatRd hφ (-c) i) (a • x)
  rw [map_smul, smul_eq_mul, h2, Mh_eq_heat]
  rfl

lemma dd_dd_Mh (hφ : φ ∈ A₀ d) (a c : ℝ) (i : Fin d) :
    dd i (dd i (Mh a c φ)) = fun x => a ^ 2 * Mh a c (dd i (dd i φ)) x := by
  rw [dd_Mh hφ a c i]
  have : dd i (fun x => a * Mh a c (dd i φ) x) = fun x => a * dd i (Mh a c (dd i φ)) x := by
    funext x
    have := dd_smul a (Mh_smooth (dd_mem hφ i) a c) i
    exact congrFun this x
  rw [this, dd_Mh (dd_mem hφ i) a c i]
  funext x; ring

lemma abs_Mh_le {C : ℝ} (hC : ∀ x, |φ x| ≤ C) (a c : ℝ) (x : Fin d → ℝ) :
    |Mh a c φ x| ≤ C := by
  rw [Mh_eq_heat]; exact abs_heatRd_le hC _ _

lemma integrable_comp_Mh {ψ : (Fin d → ℝ) → ℝ} (hψ : ψ ∈ A₀ d) (a c : ℝ) (x : Fin d → ℝ) :
    Integrable (fun z => ψ (a • x + c • z)) (gam d) := by
  have := integrable_comp_gam_A0 hψ (-c) x
  have := integrable_comp_gam_A0 hψ (-c) (a • x)
  simpa using this

/-- Lou of the Mehler average -/
lemma Lou_Mh (hφ : φ ∈ A₀ d) (a c : ℝ) (x : Fin d → ℝ) :
    Lou (Mh a c φ) x = a ^ 2 * Mh a c (Lf φ) x - a * ∑ i, x i * Mh a c (dd i φ) x := by
  unfold Lou
  simp_rw [dd_dd_Mh hφ a c, dd_Mh hφ a c]
  have : ∑ i, a ^ 2 * Mh a c (dd i (dd i φ)) x = a ^ 2 * Mh a c (Lf φ) x := by
    rw [← Finset.mul_sum]
    congr 1
    unfold Mh Lf
    exact (integral_finsetSum (μ := gam d) Finset.univ
      (f := fun i z => dd i (dd i φ) (a • x + c • z))
      (fun i _ => integrable_comp_Mh (dd_mem (dd_mem hφ i) i) a c x)).symm
  rw [this, Finset.mul_sum]
  simp only [sub_right_inj]
  refine Finset.sum_congr rfl fun i _ => by ring

end MarkovTriple.Stochastic.R30
