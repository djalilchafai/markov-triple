import Mathlib
import MarkovTriple.BGL.Theory.LSToPI
import MarkovTriple.BGL.Instances.Sphere.LogSobolevDim

/-!
# Optimality of the log-Sobolev constant `1/3` on the zonal `S³` (BGL p. 272)

Source: Bakry-Gentil-Ledoux, p. 272, the paragraph after the proof of Thm 5.7.4: "Theorem 5.7.4 applies to the sphere `Sⁿ`
... the lower bound `ρn/(n-1)` of the logarithmic Sobolev constant being optimal since these two models both satisfy a
curvature-dimension condition `CD(n-1, n)` and their Poincaré constant (equal to `1/n`) is already optimal."
The mechanism is Prop. 5.1.3 (first assertion, p. 238): `LS(C) ⟹ P(C)` (`DiffusionTriple.PI_of_LS`, `CompactTriple.PI_of_LS`).

On the zonal `S³` (`n = 3`, `CD(2,3)`, `ρ n/(n-1) = 3`): the Poincaré constant is `1/3`, attained by the first eigenfunction
`U₁(x) = 2x` (`L U₁ = -3 U₁`, `U₁ = UZ 1`, `‖U₁‖₂ = 1`, `∫ U₁ = 0`).  Hence `P(c)` fails for `c < 1/3`
(`DiffusionTriple.not_PI_of_eigen`), hence `LS(c, 0)` fails for `c < 1/3`, so `sphere_LS_dim : LS (1/3) 0` is optimal.
-/

open MeasureTheory Set Real
open scoped ENNReal

namespace MarkovTriple.BGL.Instances.Sphere

/-- `∫ U₁² dμ = 1` (orthonormality of the zonal eigenbasis, `inner_eZ`). -/
lemma UZ_one_sq : ∫ x, UZ 1 x ^ 2 ∂μZ = 1 := by
  have h : inner ℝ (eZ 1) (eZ 1) = (1 : ℝ) := by simpa using inner_eZ 1 1
  rw [MeasureTheory.L2.inner_def] at h
  have e : ∀ᵐ x ∂μZ, inner ℝ ((eZ 1 : Lp ℝ 2 μZ) x) ((eZ 1 : Lp ℝ 2 μZ) x) = UZ 1 x ^ 2 := by
    filter_upwards [(memLp_of_mem (UZ_mem 1) 2).coeFn_toLp] with x hx
    simp only [eZ]
    rw [hx]; simp [sq]
  rwa [integral_congr_ae e] at h

/-- The first eigenfunction of the zonal `S³`: `L U₁ = -3 U₁`. -/
lemma sphere_L_UZ_one (x : Zon) : sCompact.toDiffusionTriple.L (UZ 1) x = -3 * UZ 1 x := by
  show LZ (UZ 1) x = _
  rw [LZ_UZ]; norm_num

/-- **The Poincaré constant `1/3` of the zonal `S³` is sharp**: `P(c)` fails for every `c < 1/3`
(eigenfunction `U₁`, `λ₁ = 3`). -/
theorem sphere_not_PI_lt {c : ℝ} (hc : c < 1 / 3) : ¬ sCompact.toDiffusionTriple.PI c :=
  DiffusionTriple.not_PI_of_eigen sCompact.toDiffusionTriple (f := UZ 1) (UZ_mem 1) (lam := 3)
    (by norm_num) (Filter.Eventually.of_forall sphere_L_UZ_one) UZ_one_sq hc

/-- **Optimality of the log-Sobolev constant on `S³`** (BGL p. 272): `LS(c, 0)` fails for every `c < 1/3`.
Proof: `LS(c) ⟹ P(c)` (BGL Prop. 5.1.3) and `P(c)` fails (`sphere_not_PI_lt`). -/
theorem sphere_not_LS_lt {c : ℝ} (hc : c < 1 / 3) : ¬ sCompact.toDiffusionTriple.LS c 0 :=
  fun h => sphere_not_PI_lt hc (sCompact.PI_of_LS h)

/-- **Thm 5.7.4 on the zonal `S³` is sharp**: `LS(1/3, 0)` holds (`sphere_LS_dim`, `(n-1)/(ρ n) = 1/3`, `CD(2,3)`), and `LS(c, 0)`
fails for every `c < 1/3`.  Likewise the Poincaré constant `1/3` is optimal (`sphere_PI'`, `sphere_not_PI_lt`). -/
theorem sphere_LS_dim_optimal :
    sCompact.toDiffusionTriple.LS (1 / 3) 0 ∧ ∀ c : ℝ, c < 1 / 3 → ¬ sCompact.toDiffusionTriple.LS c 0 :=
  ⟨sphere_LS_dim, fun _ hc => sphere_not_LS_lt hc⟩

theorem sphere_PI_optimal :
    sCompact.toDiffusionTriple.PI (1 / 3) ∧ ∀ c : ℝ, c < 1 / 3 → ¬ sCompact.toDiffusionTriple.PI c :=
  ⟨sphere_PI', fun _ hc => sphere_not_PI_lt hc⟩

end MarkovTriple.BGL.Instances.Sphere

#print axioms MarkovTriple.BGL.Instances.Sphere.sphere_not_PI_lt
#print axioms MarkovTriple.BGL.Instances.Sphere.sphere_LS_dim_optimal
#print axioms MarkovTriple.BGL.Instances.Sphere.sphere_PI_optimal
