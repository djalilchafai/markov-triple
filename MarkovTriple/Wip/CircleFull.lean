import MarkovTriple.Sanity.Circle
/-! # Round-3 audit (G3): the circle as a `FullMarkovTriple`, with `Γ ≠ 0`.

Every field of `FullMarkovTriple` is PROVED except the two analytic ones, `esa` and
`semigroup_stable`, which are `sorry`ed on purpose (marked `OBSTACLE`); see `AUDIT_FROZEN3.md` §G3 for
the exact obstacles and the proof route.  This file is an audit artefact: not imported by the root. -/
open MeasureTheory
open scoped ENNReal NNReal
namespace Frozen3Audit
open MarkovTriple.Sanity.Circle

/-- `𝒜 := C^∞(𝕋)`, as a unital subalgebra (same carrier as `A₀`; it contains the constants). -/
def Afull : Subalgebra ℝ (𝕋 → ℝ) where
  carrier := (MarkovTriple.Sanity.Circle.A₀ : Set (𝕋 → ℝ))
  add_mem' := fun {_ _} hf hg => MarkovTriple.Sanity.Circle.A₀.add_mem hf hg
  mul_mem' := fun {_ _} hf hg => MarkovTriple.Sanity.Circle.A₀.mul_mem hf hg
  algebraMap_mem' := fun r => by
    show _ ∈ MarkovTriple.Sanity.Circle.A₀
    rw [mem_A₀]; exact contDiff_const

lemma mem_Afull {f : 𝕋 → ℝ} : f ∈ Afull ↔ f ∈ MarkovTriple.Sanity.Circle.A₀ := Iff.rfl

noncomputable def circleFull : FullMarkovTriple 𝕋 where
  toMarkovTriple := circleTriple
  A := Afull
  A₀_le := fun f hf => mem_Afull.2 hf
  A_measurable := fun f hf => (A₀_prop (mem_Afull.1 hf)).2.2.measurable
  A_comp := fun k ψ hψ f hf => by
    rw [mem_Afull, mem_A₀]
    exact hψ.comp (contDiff_pi.2 fun i => mem_A₀.1 (mem_Afull.1 (hf i)))
  L_mem_A := fun f hf => mem_Afull.2 (circleTriple.L_mem f (mem_Afull.1 hf))
  Γ_mem_A := fun f hf g hg => mem_Afull.2 (circleTriple.Γ_mem f (mem_Afull.1 hf) g (mem_Afull.1 hg))
  Γ_symm_A := fun f hf g hg => circleTriple.Γ_symm f (mem_Afull.1 hf) g (mem_Afull.1 hg)
  Γ_add_A := fun f hf f' hf' g hg => circleTriple.Γ_add f (mem_Afull.1 hf) f' (mem_Afull.1 hf') g (mem_Afull.1 hg)
  Γ_smul_A := fun c f hf g hg => circleTriple.Γ_smul c f (mem_Afull.1 hf) g (mem_Afull.1 hg)
  Γ_nonneg_A := fun f hf x => circleTriple.Γ_nonneg f (mem_Afull.1 hf) x
  L_add_A := fun f hf g hg => circleTriple.L_add f (mem_Afull.1 hf) g (mem_Afull.1 hg)
  L_smul_A := fun c f hf => circleTriple.L_smul c f (mem_Afull.1 hf)
  carre_du_champ_A := fun f hf g hg x => circleTriple.carre_du_champ f (mem_Afull.1 hf) g (mem_Afull.1 hg) x
  diffusion_A := fun k ψ hψ f hf =>
    ⟨fun g hg => (diffusion_c k ψ hψ f (fun i => mem_Afull.1 (hf i))).1 g (mem_Afull.1 hg),
      (diffusion_c k ψ hψ f (fun i => mem_Afull.1 (hf i))).2⟩
  -- OBSTACLE 1 (range criterion): `(1 - L) C^∞(𝕋)` dense in `L²`.  Needs trig-polynomial filtration
  -- (or Fourier basis) + injectivity of `1 - L` on finite-dimensional `L`-invariant subspaces.
  esa := sorry
  ibp_A := fun f hf _ _ g hg => ⟨integrable_of_cont
      (A₀_prop (circleTriple.Γ_mem f (mem_Afull.1 hf) g hg)).2.2, ibp_c (mem_Afull.1 hf) hg⟩
  ibp_A_symm := fun f hf _ _ g hg => by
    have h := ibp_c (f := g) (g := f) hg (mem_Afull.1 hf)
    have e : ∫ x, f x * Lc g x ∂μ₀ = -∫ x, Gc g f x ∂μ₀ := h
    have e2 : Gc g f = Gc f g := by funext x; simp [Gc, mul_comm]
    rw [e2] at e
    exact e
  -- OBSTACLE 2: every `IsSemigroupOf` witness is `e^{tL̄}`, and `e^{tL̄}` maps `C^∞(𝕋)` to `C^∞(𝕋)`.
  -- Needs (a) uniqueness of the semigroup from the generator clause, (b) Fourier-multiplier
  -- description `e^{-4π²n²t}` and smoothness of a rapidly-decaying Fourier series.
  semigroup_stable := sorry

/-- Non-triviality: this full triple really has `Γ ≠ 0`. -/
theorem circleFull_Γ_ne_zero : circleFull.Γ ⇑cC ⇑cC ≠ 0 := circle_Γ_ne_zero
  -- (defeq: `circleFull.Γ = Gc`)

/-- ... and `L 1 = 0`, `1 ∈ 𝒜 \ ` (circle: `1 ∈ 𝒜₀` as well). -/
example : (1 : 𝕋 → ℝ) ∈ circleFull.A := circleFull.A.one_mem
end Frozen3Audit
