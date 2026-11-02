import Mathlib
import MarkovTriple.BGL.Instances.Gibbs.FunctPI
import MarkovTriple.BGL.Frozen.FullTriple
import MarkovTriple.BGL.Frozen.CD
import MarkovTriple.BGL.Theory.LogSobolevMain
import MarkovTriple.BGL.Theory.GradientBound
import MarkovTriple.BGL.Theory.Strong.Main

/-!
# Gibbs measures: the Full Markov Triple, conditionally on exactly three analytic inputs

BGL Def. 3.3.25 (F1–F10, S10, S11) for `μ = Z⁻¹e^{-V}dx`, `𝒜₀ = C_c^∞(ℝ)`, `𝒜 = C^∞(ℝ)`.

Everything except the three semigroup-dependent items is proved here:
F1 (ideal), F2 (positivity detection), F3, F4, F5, F6, F7, F9 (connexity) are elementary calculus
(`Gibbs/FunctIBP`, `Calculus`); S11 follows from ESA for the finite measure (`conservative_of_esa`).
The remaining inputs are

* `WeakHypoEllipticAt 1`, `WeakHypoEllipticAt 0` (BGL Def. 3.3.8; with completeness they give F10 = ESA,
  Prop. 3.2.1/3.3.11, and S10 = ergodicity, Prop. 3.3.10);
* `GibbsData.F8`: `P_t f ∈ 𝒜` for `f ∈ 𝒜₀` (BGL Def. 3.3.1 (viii) / F8), i.e. the Friedrichs semigroup maps
  test functions to smooth functions.

Under these `gibbsFull : FullTriple ℝ` exists, `FullTriple.CD ρ ∞` holds when `V'' ≥ ρ`
(`gibbsFull_CD`), and the book's consequences follow, the last two still conditional on the named
regularity structures of `Theory/` (not derived for non-compact triples):
Poincaré (unconditionally in the structure, `gibbsFull_poincare`), log-Sobolev (`EntropyInterpolation`),
gradient bounds (`GradientInterpolation`, `StrongInterpolation`).
-/

open MeasureTheory Filter Topology
open scoped NNReal ENNReal
open MarkovTriple.Sanity.OU hiding A₀ γ φ

local notation "OA₀" => MarkovTriple.Sanity.OU.A₀

namespace MarkovTriple.BGL.Instances.Gibbs

namespace GibbsData
variable (G : GibbsData)

/-- F2 for the Gibbs measure (positivity detection on continuous functions, via a bump function). -/
lemma pos_detect_aux {f : ℝ → ℝ} (hf : Sm f)
    (h : ∀ g ∈ OA₀, 0 ≤ᵐ[G.μ] g → 0 ≤ ∫ x, g x * f x ∂G.μ) : ∀ x, 0 ≤ f x := by
  by_contra hcon
  push Not at hcon
  obtain ⟨x0, hx0⟩ := hcon
  have hnhds : ∀ᶠ y in 𝓝 x0, f y < 0 := hf.continuous.continuousAt.eventually_lt
    continuousAt_const hx0
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.1 hnhds
  let b : ContDiffBump x0 := ⟨r / 2, r, half_pos hr, half_lt_self hr⟩
  have hb_mem : (fun y => b y) ∈ OA₀ := ⟨b.contDiff, b.hasCompactSupport⟩
  have hnn : 0 ≤ᵐ[G.μ] fun y => b y := Eventually.of_forall fun y => b.nonneg
  have h1 := h _ hb_mem hnn
  have hle : ∀ y, 0 ≤ -(b y * f y) := by
    intro y
    by_cases hy : dist y x0 < r
    · have := hball hy
      have hby : 0 ≤ b y := b.nonneg
      have := mul_nonneg hby (neg_nonneg.2 this.le)
      linarith
    · have : b y = 0 := b.zero_of_le_dist (by simpa [b] using not_lt.1 hy)
      simp [this]
  have hcont : Continuous fun y => -(b y * f y) := (b.continuous.mul hf.continuous).neg
  have hcs : HasCompactSupport fun y => -(b y * f y) :=
    (b.hasCompactSupport.mul_right (f' := f)).neg
  have hne : (fun y => -(b y * f y)) x0 ≠ 0 := by
    have : b x0 = 1 := b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)
    simp only [this, one_mul, neg_ne_zero]
    exact hx0.ne
  have hpos := hcont.integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := G.μ) hcs hle hne
  rw [integral_neg] at hpos
  linarith

/-- **F8 for the Gibbs triple**: `P_t f ∈ 𝒜 = C^∞(ℝ)` (as an `L²`-class, it has a smooth representative)
for `f ∈ 𝒜₀` (BGL Def. 3.3.1 (viii)).  Not proved here: regularity of the Friedrichs semigroup. -/
def F8 : Prop :=
  ∀ (t : ℝ≥0) (f : G.gibbsDiff.A₀), ∃ g ∈ Afull,
    (G.gibbsDiff.semigroup t (G.gibbsDiff.cls f) : ℝ → ℝ) =ᵐ[G.μ] g

/-- The Gibbs **Standard Markov Triple** (S10 from `WeakHypoEllipticAt 0`; S11 from ESA, finite measure). -/
noncomputable def gibbsStandard (h1 : G.WeakHypoEllipticAt 1) (h0 : G.WeakHypoEllipticAt 0) :
    StandardTriple ℝ where
  toDiffusionTriple := G.gibbsDiff
  ergodic := G.gibbsDiff_ergodic h0
  conservative := fun _ hu _ t =>
    DiffusionTriple.conservative_of_esa G.gibbsDiff (G.gibbsDiff_esaProp h1) hu t

/-- The Gibbs **Full Markov Triple** (BGL Def. 3.3.25), conditional on `WeakHypoEllipticAt 1`,
`WeakHypoEllipticAt 0` and `F8` (see the module docstring). -/
noncomputable def gibbsFull (h1 : G.WeakHypoEllipticAt 1) (h0 : G.WeakHypoEllipticAt 0)
    (h8 : G.F8) : FullTriple ℝ where
  toStandardTriple := G.gibbsStandard h1 h0
  A := Afull
  A₀_le := fun f hf => hf.1
  A_measurable := fun f hf => (show Sm f from hf).continuous.measurable
  ideal := fun f hf h hh => ⟨(hh.1).mul (show Sm f from hf), hh.2.mul_right⟩
  pos_detect := fun f hf h =>
    Eventually.of_forall (G.pos_detect_aux (show Sm f from hf) h)
  A_comp := fun k ψ hψ f hf => sm_comp k ψ hψ f hf
  L_mem_A := fun f hf => sm_Lg G.smooth (show Sm f from hf)
  ΓA_nonneg := fun f hf => Eventually.of_forall fun x => by
    have := congrFun (G.gibbsDiff_ΓA (show Sm f from hf) (show Sm f from hf)) x
    show 0 ≤ G.gibbsDiff.ΓA f f x
    rw [this]
    simpa [Go] using mul_self_nonneg (deriv f x)
  diffusion_Γ_A := fun k ψ hψ f hf g hg => Eventually.of_forall fun x => by
    have hf' : ∀ i, Sm (f i) := fun i => hf i
    have hg' : Sm g := hg
    have key : ∀ i, G.gibbsDiff.ΓA (f i) g = Go (f i) g := fun i => G.gibbsDiff_ΓA (hf' i) hg'
    show G.gibbsDiff.ΓA (fun x => ψ (fun i => f i x)) g x = _
    rw [G.gibbsDiff_ΓA (sm_comp k ψ hψ f hf') hg']
    have := congrFun ((diffusion_s k ψ hψ f hf').1 g hg') x
    refine this.trans ?_
    exact Finset.sum_congr rfl fun i _ => by
      show _ = _ * G.gibbsDiff.ΓA (f i) g x
      rw [key i]
  diffusion_L_A := fun k ψ hψ f hf => Eventually.of_forall fun x => by
    have hf' : ∀ i, Sm (f i) := fun i => hf i
    have key : ∀ i j, G.gibbsDiff.ΓA (f i) (f j) = Go (f i) (f j) :=
      fun i j => G.gibbsDiff_ΓA (hf' i) (hf' j)
    have := congrFun (diffusion_g G.V k ψ hψ f hf') x
    refine this.trans ?_
    congr 1
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
      show _ = _ * G.gibbsDiff.ΓA (f i) (f j) x
      rw [key i j]
  ibp_A := fun f hf g hg => by
    have hf' : Sm f := hf
    have e : G.gibbsDiff.ΓA f g = Go f g := G.gibbsDiff_ΓA hf' hg.1
    refine ⟨?_, ?_⟩
    · show ∫ x, G.gibbsDiff.ΓA f g x ∂G.μ = -∫ x, g x * Lg G.V f x ∂G.μ
      rw [G.ibp_sm hf' hg.1 (Or.inl hg.2), neg_neg, e]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp [Go, mul_comm]
    · show ∫ x, G.gibbsDiff.ΓA f g x ∂G.μ = -∫ x, f x * Lg G.V g x ∂G.μ
      rw [G.ibp_sm hg.1 hf' (Or.inr hg.2), neg_neg, e]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp [Go]
  semigroup_A := h8
  connected := fun f hf h => by
    have hf' : Sm f := hf
    have h1 : G.gibbsDiff.ΓA f f =ᵐ[G.μ] 0 := h
    rw [G.gibbsDiff_ΓA hf' hf'] at h1
    have h2 : deriv f =ᵐ[G.μ] 0 := by
      filter_upwards [h1] with x hx
      have : deriv f x * deriv f x = 0 := hx
      simpa using this
    have h3 : deriv f = 0 :=
      (Continuous.ae_eq_iff_eq G.μ hf'.deriv'.continuous continuous_const).1 h2
    have h4 : ∀ x, deriv f x = 0 := fun x => congrFun h3 x
    have h5 := is_const_of_deriv_eq_zero (hf'.differentiable (by simp)) h4
    exact ⟨f 0, Eventually.of_forall fun x => h5 x 0⟩
  esa := fun u hu => G.gibbsDiff_esaProp h1 u hu

/-- **`CD(ρ, ∞)` of the Gibbs Full Markov Triple** (BGL Def. 3.3.14, on all of `𝒜`), for `V'' ≥ ρ`. -/
theorem gibbsFull_CD (h1 : G.WeakHypoEllipticAt 1) (h0 : G.WeakHypoEllipticAt 0) (h8 : G.F8)
    {ρ : ℝ} (hρ : ∀ x, ρ ≤ deriv (deriv G.V) x) : (G.gibbsFull h1 h0 h8).CD ρ ∞ := by
  refine ⟨le_top, fun f hf => Eventually.of_forall fun x => ?_⟩
  have hf' : Sm f := hf
  have := G.gibbsDiff_Γ₂_ge hρ hf' x
  show ρ * G.gibbsDiff.ΓA f f x + ((∞ : ℝ≥0∞)⁻¹).toReal * (Lg G.V f x) ^ 2 ≤ G.gibbsDiff.Γ₂ f f x
  simpa using this

/-- **Poincaré for Gibbs through the Full triple** (`poincare_of_CD_infty`; same statement as
`gibbs_poincare`, which does not need F8). -/
theorem gibbsFull_poincare (h1 : G.WeakHypoEllipticAt 1) (h0 : G.WeakHypoEllipticAt 0) (h8 : G.F8)
    {ρ : ℝ} (hρpos : 0 < ρ) (hρ : ∀ x, ρ ≤ deriv (deriv G.V) x) :
    (G.gibbsFull h1 h0 h8).toDiffusionTriple.PI (1 / ρ) :=
  haveI : IsProbabilityMeasure (G.gibbsFull h1 h0 h8).μ :=
    (inferInstance : IsProbabilityMeasure G.μ)
  FullTriple.poincare_of_CD_infty _ hρpos (G.gibbsFull_CD h1 h0 h8 hρ)

/-- **Log-Sobolev for Gibbs** (`Ent(f²) ≤ (2/ρ) ∫ f'² dμ`, BGL Prop. 5.7.1 / Thm 5.7.4 route),
conditional on the named structure `EntropyInterpolation` of the Gibbs Full triple. -/
theorem gibbsFull_logSobolev (h1 : G.WeakHypoEllipticAt 1) (h0 : G.WeakHypoEllipticAt 0) (h8 : G.F8)
    {ρ : ℝ} (hρpos : 0 < ρ) (hρ : ∀ x, ρ ≤ deriv (deriv G.V) x)
    (hE : (G.gibbsFull h1 h0 h8).EntropyInterpolation) :
    (G.gibbsFull h1 h0 h8).toDiffusionTriple.LS (1 / ρ) 0 :=
  haveI : IsProbabilityMeasure (G.gibbsFull h1 h0 h8).μ :=
    (inferInstance : IsProbabilityMeasure G.μ)
  FullTriple.logSobolev_of_CD_infty _ hE hρpos (G.gibbsFull_CD h1 h0 h8 hρ)

/-- **Gradient bound for Gibbs** (`Γ(P_t f) ≤ e^{-2ρt} P_t Γ(f)`, BGL Cor. 3.3.19), conditional on
`GradientInterpolation` of the Gibbs Full triple. -/
theorem gibbsFull_gradient_bound (h1 : G.WeakHypoEllipticAt 1) (h0 : G.WeakHypoEllipticAt 0)
    (h8 : G.F8) {ρ : ℝ} (hρ : ∀ x, ρ ≤ deriv (deriv G.V) x)
    (hG : (G.gibbsFull h1 h0 h8).GradientInterpolation) (f : (G.gibbsFull h1 h0 h8).A₀) (t : ℝ≥0) :
    (G.gibbsFull h1 h0 h8).toDiffusionTriple.ΓA ((G.gibbsFull h1 h0 h8).Pt t f)
        ((G.gibbsFull h1 h0 h8).Pt t f) ≤ᵐ[G.μ] fun x =>
      Real.exp (-2 * ρ * t) * ((G.gibbsFull h1 h0 h8).toDiffusionTriple.semigroup t
        ((G.gibbsFull h1 h0 h8).toDiffusionTriple.cls
          ⟨(G.gibbsFull h1 h0 h8).toDiffusionTriple.ΓA f.1 f.1,
            (G.gibbsFull h1 h0 h8).ΓA_self_mem_A₀ f.2⟩) : Lp ℝ 2 G.μ) x :=
  FullTriple.gradient_bound _ (G.gibbsFull_CD h1 h0 h8 hρ) hG f t

end GibbsData

end MarkovTriple.BGL.Instances.Gibbs
