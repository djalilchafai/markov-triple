import Mathlib
import MarkovTriple.BGL.Instances.GibbsRd.EllFull
import MarkovTriple.BGL.Theory.Strong.Main

/-!
# Weighted elliptic triples on `ℝ^d`: ESA, ergodicity, integrated `Γ₂`, Poincaré, Standard/Full triple

Mirrors `Instances/Gibbs/FunctPI.lean` and `FunctFull.lean`.

* `WeakHypo` (BGL Def. 3.3.8) and `F8` (Def. 3.3.1 (viii)) are *named hypotheses*; `Curv ρ` is the curvature
  condition `CD(ρ,∞)` of Def. 3.3.14 on smooth functions.
* `integral_Γ₂` (BGL (3.3.8)) and `integrated_CD` are unconditional/under `Curv ρ`.
* `ell_poincare` (BGL Cor. 4.8.2 / Prop. 4.8.3 route), `ell_spectralGap`, `ell_expDecay`: `Curv ρ` + `WeakHypo`.
* `standard`, `full`, `full_CD`, `full_poincare`, `full_logSobolev`, `full_gradient_bound`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace

namespace MarkovTriple.BGL.Instances.GibbsRd

open MarkovTriple.BGL (pderiv pderiv₂ DiffusionTriple PreFull FullTriple StandardTriple)

variable {d : ℕ}

namespace EllData
variable (E : EllData d)

/-- **Weak hypo-ellipticity** (BGL Def. 3.3.8) with `𝒜 = C^∞(ℝ^d)`: elliptic regularity of weak solutions of
`L f = λ f` (quoted, not proved, by the book; Sect. 1.12).  Named hypothesis. -/
def WeakHypo : Prop := E.diff.WeakHypoElliptic (Afull d)

/-- **F8** (BGL Def. 3.3.1 (viii)): `P_t f ∈ 𝒜 = C^∞` (has a smooth representative) for `f ∈ 𝒜₀`.  Named hypothesis. -/
def F8 : Prop :=
  ∀ (t : ℝ≥0) (f : E.diff.A₀), ∃ g ∈ Afull d,
    (E.diff.semigroup t (E.diff.cls f) : Rd d → ℝ) =ᵐ[E.μ] g

/-- **Curvature `CD(ρ,∞)`** (BGL Def. 3.3.14, `n = ∞`) on smooth functions, for the formula-defined
`Γ₂ = ½(L Γ − Γ(·,L·) − Γ(L·,·))` (Def. 3.3.12): `ρ Γ(f) ≤ Γ₂(f)` everywhere. -/
def Curv (ρ : ℝ) : Prop := ∀ f : Rd d → ℝ, Sm f → ∀ x, ρ * E.diff.ΓA f f x ≤ E.diff.Γ₂ f f x

/-- **ESA (F10)**, BGL Prop. 3.3.11, from `preFull`, completeness and `WeakHypo`. -/
theorem diff_esaProp (hH : E.WeakHypo) : E.diff.ESAProp :=
  DiffusionTriple.ESAProp_of_weakHypo E.diff E.preFull E.diff_isComplete hH

/-- **Ergodicity (S10)**, BGL Prop. 3.3.10 (with the deviation documented in `Gibbs/FunctESA.lean`). -/
theorem diff_ergodic (hH : E.WeakHypo) :
    ∀ (u : Lp ℝ 2 E.diff.μ) (hu : u ∈ E.diff.generator.domain),
      E.diff.generator ⟨u, hu⟩ = 0 → ∃ c : ℝ, (u : Rd d → ℝ) =ᵐ[E.diff.μ] fun _ => c :=
  DiffusionTriple.ergodic_of_weakHypo E.diff E.preFull E.diff_isComplete hH

/-- `Γ₂` on a test function as the explicit combination of coordinate expressions. -/
lemma Γ₂_eq_comb {f : Rd d → ℝ} (hf : Sm f) :
    E.diff.Γ₂ f f = fun x => (E.L (E.Γ f f) x - E.Γ f (E.L f) x - E.Γ (E.L f) f x) / 2 := by
  funext x
  have e1 : E.diff.ΓA f f = E.Γ f f := E.ΓA_eq hf hf
  have e2 : E.diff.ΓA f (E.L f) = E.Γ f (E.L f) := E.ΓA_eq hf (E.sm_L hf)
  have e3 : E.diff.ΓA (E.L f) f = E.Γ (E.L f) f := E.ΓA_eq (E.sm_L hf) hf
  show (E.L (E.diff.ΓA f f) x - E.diff.ΓA f (E.L f) x - E.diff.ΓA (E.L f) f x) / 2 = _
  rw [e1, e2, e3]

/-- **BGL (3.3.8) on test functions**: `∫ Γ₂(f) dμ = ∫ (L f)² dμ`. -/
theorem integral_Γ₂ {f : Rd d → ℝ} (hf : f ∈ A₀ d) :
    ∫ x, E.diff.Γ₂ f f x ∂E.μ = ∫ x, E.L f x * E.L f x ∂E.μ := by
  have hLf : E.L f ∈ A₀ d := E.L_mem hf
  have m1 : E.L (E.Γ f f) ∈ A₀ d := E.L_mem (E.Γ_mem hf hf)
  have m2 : E.Γ f (E.L f) ∈ A₀ d := E.Γ_mem hf hLf
  have m3 : E.Γ (E.L f) f ∈ A₀ d := E.Γ_mem hLf hf
  have i1 : Integrable (E.L (E.Γ f f)) E.μ := E.diff.integrable_of_mem m1
  have i2 : Integrable (E.Γ f (E.L f)) E.μ := E.diff.integrable_of_mem m2
  have i3 : Integrable (E.Γ (E.L f) f) E.μ := E.diff.integrable_of_mem m3
  have h0 : ∫ x, E.L (E.Γ f f) x ∂E.μ = 0 := E.integral_L_zero (E.Γ_mem hf hf)
  have hib := E.ibp_sm (f := f) (g := E.L f) hf.1 hLf.1 (Or.inr hf.2)
  have h3 : ∫ x, E.Γ (E.L f) f x ∂E.μ = ∫ x, E.Γ f (E.L f) x ∂E.μ := by
    rw [E.Γ_symm]
  have h2 : ∫ x, E.Γ f (E.L f) x ∂E.μ = -∫ x, E.L f x * E.L f x ∂E.μ := by
    rw [← h3]; linarith
  rw [E.Γ₂_eq_comb hf.1]
  have i12 : Integrable (fun x => E.L (E.Γ f f) x - E.Γ f (E.L f) x) E.μ := i1.sub i2
  rw [integral_div, integral_sub i12 i3, integral_sub i1 i2, h0, h3, h2]
  ring

/-- **Integrated curvature on `𝒜₀`** under `Curv ρ`: `ρ ∫ Γ(f) dμ ≤ ∫ (L f)² dμ`. -/
theorem integrated_CD {ρ : ℝ} (hρ : E.Curv ρ) {f : Rd d → ℝ} (hf : f ∈ A₀ d) :
    ρ * ∫ x, E.Γ f f x ∂E.μ ≤ ∫ x, E.L f x * E.L f x ∂E.μ := by
  have hLf : E.L f ∈ A₀ d := E.L_mem hf
  have m1 : E.L (E.Γ f f) ∈ A₀ d := E.L_mem (E.Γ_mem hf hf)
  have m2 : E.Γ f (E.L f) ∈ A₀ d := E.Γ_mem hf hLf
  have m3 : E.Γ (E.L f) f ∈ A₀ d := E.Γ_mem hLf hf
  have iΓ : Integrable (E.Γ f f) E.μ := E.diff.integrable_of_mem (E.Γ_mem hf hf)
  have iΓ₂ : Integrable (E.diff.Γ₂ f f) E.μ := by
    rw [E.Γ₂_eq_comb hf.1]
    exact (((E.diff.integrable_of_mem m1).sub (E.diff.integrable_of_mem m2)).sub
      (E.diff.integrable_of_mem m3)).div_const 2
  rw [← E.integral_Γ₂ hf, ← integral_const_mul]
  refine integral_mono_ae (iΓ.const_mul ρ) iΓ₂ (Eventually.of_forall fun x => ?_)
  have := hρ f hf.1 x
  rw [E.ΓA_eq hf.1 hf.1] at this
  exact this

/-- the integrated curvature inequality in the `L²` language of `DiffusionTriple.rho_var_le_of`. -/
theorem integrated_CD_cls {ρ : ℝ} (hρ : E.Curv ρ) (a : E.diff.A₀) :
    ρ * (-inner ℝ (E.diff.Lcls a) (E.diff.cls a)) ≤ ‖E.diff.Lcls a‖ ^ 2 := by
  have h := E.integrated_CD hρ a.2
  have e1 : -inner ℝ (E.diff.Lcls a) (E.diff.cls a) = ∫ x, E.Γ a.1 a.1 x ∂E.μ := by
    rw [DiffusionTriple.inner_Lcls_cls, neg_neg]; rfl
  have e2 : ‖E.diff.Lcls a‖ ^ 2 = ∫ x, E.L a.1 x * E.L a.1 x ∂E.μ := by
    rw [← real_inner_self_eq_norm_sq, L2_inner_eq]
    refine integral_congr_ae ?_
    filter_upwards [DiffusionTriple.coeFn_Lcls E.diff a] with x hx
    rw [hx]; rfl
  rw [e1, e2]
  exact h

/-- **Poincaré inequality with constant `1/ρ`** (BGL Cor. 4.8.2 / Prop. 4.8.3 route): from integrated `Γ₂`,
`Curv ρ` (Def. 3.3.14), ESA and ergodicity (both from `WeakHypo`, Defs. 3.3.8–3.3.11).  No F8, no gradient
bound. -/
theorem ell_poincare {ρ : ℝ} (hρpos : 0 < ρ) (hρ : E.Curv ρ) (hH : E.WeakHypo) :
    E.diff.PI (1 / ρ) := by
  refine ⟨(inferInstance : IsProbabilityMeasure E.diff.μ), by positivity, fun f hf => ?_⟩
  have h := DiffusionTriple.rho_var_le_of E.diff (E.diff_esaProp hH) (E.diff_ergodic hH)
    (fun a => E.integrated_CD_cls hρ a) hf
  show ProbabilityTheory.variance f E.diff.μ ≤ 1 / ρ * ∫ x, E.diff.Γ f f x ∂E.diff.μ
  rw [one_div, inv_mul_eq_div, le_div_iff₀ hρpos]
  linarith

/-- spectral gap `ρ` of the Friedrichs semigroup. -/
theorem ell_spectralGap {ρ : ℝ} (hρpos : 0 < ρ) (hρ : E.Curv ρ) (hH : E.WeakHypo) :
    (DiffusionTriple.formData E.diff).HasSpectralGap ρ := by
  have := DiffusionTriple.hasSpectralGap_of_PI E.diff (E.diff_esaProp hH)
    (E.ell_poincare hρpos hρ hH)
  simpa using this

/-- `L²` exponential decay `‖P_t u‖ ≤ e^{-ρ t}‖u‖` for `u ⟂ 1`. -/
theorem ell_expDecay {ρ : ℝ} (hρpos : 0 < ρ) (hρ : E.Curv ρ) (hH : E.WeakHypo) :
    (DiffusionTriple.formData E.diff).HasExpDecay ρ := by
  have := DiffusionTriple.expDecay_of_PI E.diff (E.diff_esaProp hH)
    (E.ell_poincare hρpos hρ hH)
  simpa using this

/-! ### Standard and Full Markov Triples -/

/-- **Standard Markov Triple** (S10 from Prop. 3.3.10; S11 from ESA, finite measure). -/
noncomputable def standard (hH : E.WeakHypo) : StandardTriple (Rd d) where
  toDiffusionTriple := E.diff
  ergodic := E.diff_ergodic hH
  conservative := fun _ hu _ t =>
    DiffusionTriple.conservative_of_esa (T := E.diff) (E.diff_esaProp hH) hu t

/-- **Full Markov Triple** (BGL Def. 3.3.25), under `WeakHypo` and `F8`. -/
noncomputable def full (hH : E.WeakHypo) (h8 : E.F8) : FullTriple (Rd d) where
  toStandardTriple := E.standard hH
  A := Afull d
  A₀_le := E.preFull.A₀_le
  A_measurable := E.preFull.A_measurable
  ideal := E.preFull.ideal
  pos_detect := E.preFull.pos_detect
  A_comp := fun k ψ hψ f hf => sm_comp k ψ hψ f hf
  L_mem_A := E.preFull.L_mem_A
  ΓA_nonneg := E.preFull.ΓA_nonneg
  diffusion_Γ_A := E.preFull.diffusion_Γ_A
  diffusion_L_A := fun k ψ hψ f hf => Eventually.of_forall fun x => by
    have hf' : ∀ i, Sm (f i) := fun i => hf i
    have key : ∀ i j, E.diff.ΓA (f i) (f j) = E.Γ (f i) (f j) :=
      fun i j => E.ΓA_eq (hf' i) (hf' j)
    have := E.L_comp ψ hψ f hf' x
    refine this.trans ?_
    congr 1
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
      show _ = _ * E.diff.ΓA (f i) (f j) x
      rw [key i j]
  ibp_A := E.preFull.ibp_A
  semigroup_A := h8
  connected := E.preFull.connected
  esa := E.diff_esaProp hH

/-- **`CD(ρ,∞)` for the Full triple** from `Curv ρ`. -/
theorem full_CD (hH : E.WeakHypo) (h8 : E.F8) {ρ : ℝ} (hρ : E.Curv ρ) : (E.full hH h8).CD ρ ∞ :=
  ⟨le_top, fun f hf => Eventually.of_forall fun x => by
    have := hρ f hf x
    simp only [ENNReal.inv_top, ENNReal.toReal_zero, zero_mul, add_zero]
    exact this⟩

/-- Poincaré through the Full triple (`poincare_of_CD_infty`; same statement as `ell_poincare`). -/
theorem full_poincare (hH : E.WeakHypo) (h8 : E.F8) {ρ : ℝ} (hρpos : 0 < ρ) (hρ : E.Curv ρ) :
    (E.full hH h8).toDiffusionTriple.PI (1 / ρ) :=
  haveI : IsProbabilityMeasure (E.full hH h8).μ := (inferInstance : IsProbabilityMeasure E.μ)
  FullTriple.poincare_of_CD_infty _ hρpos (E.full_CD hH h8 hρ)

/-- **Log-Sobolev** `Ent(f²) ≤ (2/ρ)∫Γ(f)dμ` (BGL Prop. 5.7.1 route), conditional on `EntropyInterpolation`. -/
theorem full_logSobolev (hH : E.WeakHypo) (h8 : E.F8) {ρ : ℝ} (hρpos : 0 < ρ) (hρ : E.Curv ρ)
    (hE : (E.full hH h8).EntropyInterpolation) :
    (E.full hH h8).toDiffusionTriple.LS (1 / ρ) 0 :=
  haveI : IsProbabilityMeasure (E.full hH h8).μ := (inferInstance : IsProbabilityMeasure E.μ)
  FullTriple.logSobolev_of_CD_infty _ hE hρpos (E.full_CD hH h8 hρ)

/-- **Gradient bound** `Γ(P_t f) ≤ e^{-2ρt} P_t Γ(f)` (BGL Cor. 3.3.19), conditional on
`GradientInterpolation`. -/
theorem full_gradient_bound (hH : E.WeakHypo) (h8 : E.F8) {ρ : ℝ} (hρ : E.Curv ρ)
    (hG : (E.full hH h8).GradientInterpolation) (f : (E.full hH h8).A₀) (t : ℝ≥0) :
    (E.full hH h8).toDiffusionTriple.ΓA ((E.full hH h8).Pt t f) ((E.full hH h8).Pt t f) ≤ᵐ[E.μ]
      fun x => Real.exp (-2 * ρ * t) * ((E.full hH h8).toDiffusionTriple.semigroup t
        ((E.full hH h8).toDiffusionTriple.cls
          ⟨(E.full hH h8).toDiffusionTriple.ΓA f.1 f.1,
            (E.full hH h8).ΓA_self_mem_A₀ f.2⟩) : Lp ℝ 2 E.μ) x :=
  FullTriple.gradient_bound _ (E.full_CD hH h8 hρ) hG f t

end EllData

end MarkovTriple.BGL.Instances.GibbsRd
