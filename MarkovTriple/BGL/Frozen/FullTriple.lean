import Mathlib
import MarkovTriple.BGL.Frozen.StandardTriple
import MarkovTriple.BGL.Frozen.GammaA

/-!
# Full Markov Triples (BGL Definitions 3.3.1, 3.3.7, 3.3.25; hypotheses F1–F10)
-/

open MeasureTheory Filter
open scoped NNReal ENNReal Topology LinearPMap

namespace MarkovTriple.BGL

/-- A **Full Markov Triple** (BGL Def. 3.3.25, §3.4.3): a Standard Markov Triple with an
**extended algebra** `𝒜 ⊃ 𝒜₀` (Def. 3.3.1) satisfying F1–F8, plus connexity F9 (Def. 3.3.7) and ESA
F10 (Def. 3.1.10).  Labels are the book's.

`𝒜` is a unital `Subalgebra` (it contains the constants), consisting of measurable functions, with no
integrability.  `L : 𝒜 → 𝒜` is the same function `L` as in the diffusion triple (so "extends `L` on
`𝒜₀`" holds by construction); `Γ` on `𝒜` is *defined* by the formula (`DiffusionTriple.ΓA`, F4), it
is not a separate field.  Equalities between functions are a.e. (book convention).
Not fields because derivable: `ΓA(f,g) ∈ 𝒜` (F4; algebra closure), a.e.-linearity of `L` and
bilinearity/symmetry of `ΓA` on `𝒜` (from F6 and the formula), `ΓA(f,h) ∈ 𝒜₀` for `h ∈ 𝒜₀` (from
F1), integrability of the three terms in F7 (from F1 and `memLp`), `L 1 = 0`, `ΓA(1,·) = 0` (from F6
with `k = 0`). -/
structure FullTriple (E : Type*) [MeasurableSpace E] extends StandardTriple E where
  /-- the extended algebra `𝒜` (Def. 3.3.1). -/
  A : Subalgebra ℝ (E → ℝ)
  /-- `𝒜₀ ⊂ 𝒜`. -/
  A₀_le : ∀ f ∈ A₀, f ∈ A
  /-- elements of `𝒜` are measurable. -/
  A_measurable : ∀ f ∈ A, Measurable f
  /-- F1, ideal property: `f ∈ 𝒜`, `h ∈ 𝒜₀` ⇒ `h f ∈ 𝒜₀`. -/
  ideal : ∀ f ∈ A, ∀ h ∈ A₀, h * f ∈ A₀
  /-- F2, positivity detection: `f ∈ 𝒜` with `∫ h f dμ ≥ 0` for every positive `h ∈ 𝒜₀` is `≥ 0`
  (a.e.). -/
  pos_detect : ∀ f ∈ A, (∀ h ∈ A₀, 0 ≤ᵐ[μ] h → 0 ≤ ∫ x, h x * f x ∂μ) → 0 ≤ᵐ[μ] f
  /-- F3: `𝒜` is stable under composition with every smooth `ψ : ℝᵏ → ℝ`. -/
  A_comp : ∀ (k : ℕ) (ψ : (Fin k → ℝ) → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ →
    ∀ f : Fin k → (E → ℝ), (∀ i, f i ∈ A) → (fun x => ψ (fun i => f i x)) ∈ A
  /-- F4: `L : 𝒜 → 𝒜` (an extension of `L` on `𝒜₀`; `Γ` on `𝒜` is `ΓA`). -/
  L_mem_A : ∀ f ∈ A, L f ∈ A
  /-- F5: `Γ(f) ≥ 0` on `𝒜` (a.e.). -/
  ΓA_nonneg : ∀ f ∈ A, 0 ≤ᵐ[μ] toStandardTriple.toDiffusionTriple.ΓA f f
  /-- F6, change of variables formula (3.1.2) for `Γ` on `𝒜`, for all smooth `ψ`. -/
  diffusion_Γ_A : ∀ (k : ℕ) (ψ : (Fin k → ℝ) → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ →
    ∀ f : Fin k → (E → ℝ), (∀ i, f i ∈ A) → ∀ g ∈ A,
      toStandardTriple.toDiffusionTriple.ΓA (fun x => ψ (fun i => f i x)) g =ᵐ[μ]
        fun x => ∑ i, pderiv ψ i (fun j => f j x) *
          toStandardTriple.toDiffusionTriple.ΓA (f i) g x
  /-- F6, change of variables formula (3.1.8) for `L` on `𝒜`, for all smooth `ψ`. -/
  diffusion_L_A : ∀ (k : ℕ) (ψ : (Fin k → ℝ) → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ →
    ∀ f : Fin k → (E → ℝ), (∀ i, f i ∈ A) →
      L (fun x => ψ (fun i => f i x)) =ᵐ[μ]
        fun x => ∑ i, pderiv ψ i (fun j => f j x) * L (f i) x +
          ∑ i, ∑ j, pderiv₂ ψ i j (fun l => f l x) *
            toStandardTriple.toDiffusionTriple.ΓA (f i) (f j) x
  /-- F7: for `f ∈ 𝒜`, `g ∈ 𝒜₀`: `∫ Γ(f,g) dμ = −∫ g Lf dμ = −∫ f Lg dμ`. -/
  ibp_A : ∀ f ∈ A, ∀ g ∈ A₀,
    ∫ x, toStandardTriple.toDiffusionTriple.ΓA f g x ∂μ = -∫ x, g x * L f x ∂μ ∧
    ∫ x, toStandardTriple.toDiffusionTriple.ΓA f g x ∂μ = -∫ x, f x * L g x ∂μ
  /-- F8: `P_t f ∈ 𝒜` for `f ∈ 𝒜₀`, `t ≥ 0` (as an `L²`-class: it has a representative in `𝒜`). -/
  semigroup_A : ∀ (t : ℝ≥0) (f : A₀), ∃ g ∈ A,
    (toStandardTriple.toDiffusionTriple.semigroup t
      (toStandardTriple.toDiffusionTriple.cls f) : E → ℝ) =ᵐ[μ] g
  /-- F9, connexity (Def. 3.3.7): `f ∈ 𝒜`, `Γ(f) = 0` ⇒ `f` constant (both a.e.). -/
  connected : ∀ f ∈ A, toStandardTriple.toDiffusionTriple.ΓA f f =ᵐ[μ] 0 →
    ∃ c : ℝ, f =ᵐ[μ] fun _ => c
  /-- F10, ESA (Def. 3.1.10), in its "core" form: `𝒜₀` is dense in `𝒟(L)` for the graph norm,
  i.e. every `u ∈ 𝒟(L)` is the `L²`-limit of classes `a_n ∈ 𝒜₀` with `L a_n → L u` in `L²`. -/
  esa : ∀ (u : Lp ℝ 2 μ) (hu : u ∈ toStandardTriple.toDiffusionTriple.generator.domain),
    ∃ a : ℕ → A₀, Tendsto (fun n => toStandardTriple.toDiffusionTriple.cls (a n)) atTop (𝓝 u) ∧
      Tendsto (fun n => toStandardTriple.toDiffusionTriple.Lcls (a n)) atTop
        (𝓝 (toStandardTriple.toDiffusionTriple.generator ⟨u, hu⟩))

end MarkovTriple.BGL
