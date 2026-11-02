import Mathlib
import MarkovTriple.BGL.Instances.Gibbs.Calculus
import MarkovTriple.BGL.Frozen.DiffusionTriple
import MarkovTriple.BGL.Frozen.GammaA
import MarkovTriple.BGL.Frozen.Gamma2
import MarkovTriple.BGL.Theory.Complete.Real

/-!
# Gibbs measures `e^{-V} dx` on `ℝ` as BGL `DiffusionTriple`s (D1–D8), completeness, `CD(ρ,∞)`-curvature

For `V : ℝ → ℝ` smooth with `e^{-V}` integrable, `μ = Z⁻¹ e^{-V} dx`, `𝒜₀ = C_c^∞(ℝ)`,
`L f = f'' − V' f'`, `Γ(f,g) = f' g'`.  `V = x²/2` is the Ornstein–Uhlenbeck triple (`Instances.OU`).

Proved here (unconditionally): `gibbsDiff : DiffusionTriple ℝ` (all of D1–D8; `ibp`, `integral_L` by
integrating the compactly supported derivative `(g f' e^{-V})'`), `gibbsDiff_isComplete` (Def. 3.3.9) and the
curvature inequality `Γ₂ ≥ ρ Γ` on smooth functions for `V'' ≥ ρ` (`gibbsDiff_Γ₂_ge`, in terms of the frozen
`DiffusionTriple.Γ₂`/`ΓA`).

NOT done: the Standard/Full/Compact structures.  S10, S11, F8 (`P_t` maps `𝒜₀` into `𝒜`) and F10 (ESA) need
control of the Friedrichs semigroup of a general uniformly convex `V`, which has no closed form (the OU instance
uses the Hermite basis and Mehler's formula).  Hence no `CD(ρ,∞)` in the sense of `FullTriple.CD` yet, only
its pointwise content `gibbsDiff_Γ₂_ge`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal
open MarkovTriple.Sanity.OU hiding A₀ γ φ

open MarkovTriple.BGL.Instances.OU (expo expo_sm expo_cs expo_mono expo_tendsto A₀_bounded)

local notation "OA₀" => MarkovTriple.Sanity.OU.A₀

namespace MarkovTriple.BGL.Instances.Gibbs

/-- Data of a Gibbs measure on `ℝ`: a smooth potential with integrable `e^{-V}`. -/
structure GibbsData where
  /-- the potential -/
  V : ℝ → ℝ
  /-- smooth -/
  smooth : Sm V
  /-- `e^{-V}` is integrable -/
  integrable : Integrable (fun x => Real.exp (-V x))

namespace GibbsData
variable (G : GibbsData)

lemma continuous_exp : Continuous (fun x => Real.exp (-G.V x)) :=
  Real.continuous_exp.comp G.smooth.continuous.neg

/-- the normalising constant -/
noncomputable def Z : ℝ := ∫ x, Real.exp (-G.V x)

lemma Z_pos : 0 < G.Z := by
  unfold Z
  refine (integral_pos_iff_support_of_nonneg (fun x => (Real.exp_pos _).le) G.integrable).2 ?_
  have : Function.support (fun x => Real.exp (-G.V x)) = Set.univ :=
    Set.eq_univ_of_forall fun x => (Real.exp_pos _).ne'
  rw [this]; simp

/-- the normalised density -/
noncomputable def w (x : ℝ) : ℝ := Real.exp (-G.V x) / G.Z

lemma w_pos (x : ℝ) : 0 < G.w x := div_pos (Real.exp_pos _) G.Z_pos

lemma w_integrable : Integrable G.w volume := G.integrable.div_const _

lemma integral_w : ∫ x, G.w x = 1 := by
  unfold w
  rw [integral_div]
  exact div_self G.Z_pos.ne'

lemma w_smooth : Sm G.w :=
  (Real.contDiff_exp.comp G.smooth.neg).div_const _

lemma hasDerivAt_w (x : ℝ) : HasDerivAt G.w (-(deriv G.V x) * G.w x) x := by
  have h := ((G.smooth.hasDerivAt x).neg.exp).div_const G.Z
  refine h.congr_deriv ?_
  unfold w
  simp only [Pi.neg_apply]
  ring

/-- the Gibbs probability measure -/
noncomputable def μ : Measure ℝ := volume.withDensity (fun x => ENNReal.ofReal (G.w x))

instance : IsProbabilityMeasure G.μ := by
  refine ⟨?_⟩
  unfold μ
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal G.w_integrable (Filter.Eventually.of_forall fun x => (G.w_pos x).le),
    integral_w]
  simp

lemma integral_μ (F : ℝ → ℝ) : ∫ x, F x ∂G.μ = ∫ x, G.w x * F x := by
  unfold μ
  rw [integral_withDensity_eq_integral_toReal_smul (f := fun x => ENNReal.ofReal (G.w x))
    (ENNReal.measurable_ofReal.comp G.w_smooth.continuous.measurable)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [ENNReal.toReal_ofReal (G.w_pos x).le]

/-- `μ` charges nonempty open sets and is absolutely continuous (as `w > 0`) -/
instance : G.μ.IsOpenPosMeasure := by
  refine ⟨fun U hU hne h0 => ?_⟩
  unfold μ at h0
  rw [withDensity_apply _ hU.measurableSet] at h0
  have h1 := (lintegral_eq_zero_iff (ENNReal.measurable_ofReal.comp
    G.w_smooth.continuous.measurable)).1 (by simpa using h0 : ∫⁻ x in U, ENNReal.ofReal (G.w x) ∂volume = 0)
  have h2 : ∀ᵐ x ∂(volume.restrict U), False := by
    filter_upwards [h1] with x hx
    simp [ENNReal.ofReal_eq_zero, not_le.2 (G.w_pos x)] at hx
  have := (ae_restrict_iff' hU.measurableSet).1 h2
  have h3 : volume U = 0 := by
    have : ∀ᵐ x ∂volume, x ∉ U := by
      filter_upwards [this] with x hx hxU using hx hxU
    simpa [ae_iff] using this
  exact hU.measure_ne_zero volume hne h3

/-! ### Integration by parts -/

/-- master integration by parts: `∫ (g L f + g' f') w = 0` when `g f'` has compact support. -/
lemma ibp_master {f g : ℝ → ℝ} (hf : Sm f) (hg : Sm g)
    (hc : HasCompactSupport (fun x => g x * deriv f x)) :
    ∫ x, G.w x * (g x * Lg G.V f x + deriv g x * deriv f x) = 0 := by
  set H : ℝ → ℝ := fun x => g x * deriv f x * G.w x with hH
  set F : ℝ → ℝ := fun x => G.w x * (g x * Lg G.V f x + deriv g x * deriv f x) with hF
  have hder : ∀ x, HasDerivAt H (F x) x := by
    intro x
    have h1 := (hg.hasDerivAt x).mul (hf.deriv'.hasDerivAt x)
    have := h1.mul (G.hasDerivAt_w x)
    refine this.congr_deriv ?_
    simp only [hF, Lg, Pi.mul_apply]
    ring
  have hHs : Sm H := (hg.mul hf.deriv').mul G.w_smooth
  have hHc : HasCompactSupport H := hc.mul_right
  have hFd : F = deriv H := funext fun x => (hder x).deriv.symm
  have hFc : HasCompactSupport F := by rw [hFd]; exact hHc.deriv
  have hFcont : Continuous F := by rw [hFd]; exact hHs.deriv'.continuous
  exact integral_eq_zero_of_hasDerivAt_of_integrable hder (hFcont.integrable_of_hasCompactSupport hFc)
    (hHs.continuous.integrable_of_hasCompactSupport hHc)

lemma integrable_cs {h : ℝ → ℝ} (hcont : Continuous h) (hc : HasCompactSupport h) :
    Integrable (fun x => G.w x * h x) volume :=
  (G.w_smooth.continuous.mul hcont).integrable_of_hasCompactSupport hc.mul_left

lemma Lg_mem {f : ℝ → ℝ} (hf : f ∈ OA₀) : Lg G.V f ∈ OA₀ := by
  have h1 := A₀.deriv_mem (A₀.deriv_mem hf)
  have h2 : (fun x : ℝ => deriv G.V x * deriv f x) ∈ OA₀ :=
    ⟨G.smooth.deriv'.mul hf.1.deriv', (A₀.deriv_mem hf).2.mul_left⟩
  exact sub_mem h1 h2

lemma integral_L_zero {f : ℝ → ℝ} (hf : f ∈ OA₀) : ∫ x, Lg G.V f x ∂G.μ = 0 := by
  have := G.ibp_master (f := f) (g := fun _ => (1 : ℝ)) hf.1 contDiff_const (by simpa using hf.2.deriv)
  rw [integral_μ]
  simpa using this

lemma ibp_A₀ {f g : ℝ → ℝ} (hf : f ∈ OA₀) (hg : g ∈ OA₀) :
    ∫ x, g x * Lg G.V f x ∂G.μ = -∫ x, deriv f x * deriv g x ∂G.μ := by
  have hm := G.ibp_master hf.1 hg.1 (by exact hg.2.mul_right)
  have hg' := A₀.deriv_mem hg
  have i1 : Integrable (fun x => G.w x * (g x * Lg G.V f x)) volume :=
    G.integrable_cs ((hg.1.continuous.mul (sm_Lg G.smooth hf.1).continuous))
      (by exact hg.2.mul_right)
  have i2 : Integrable (fun x => G.w x * (deriv g x * deriv f x)) volume :=
    G.integrable_cs (hg'.1.continuous.mul hf.1.deriv'.continuous) (by exact hg'.2.mul_right)
  simp only [mul_add] at hm
  rw [integral_add i1 i2] at hm
  rw [integral_μ, integral_μ]
  have : ∫ x, G.w x * (deriv f x * deriv g x) = ∫ x, G.w x * (deriv g x * deriv f x) :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
  rw [this]
  linarith

/-- **The Gibbs `DiffusionTriple`** (D1–D8) for `μ = Z⁻¹ e^{-V} dx`, `𝒜₀ = C_c^∞`, `L f = f'' − V' f'`. -/
noncomputable def gibbsDiff : DiffusionTriple ℝ where
  μ := G.μ
  sigmaFinite := inferInstance
  finite_prob := fun _ => inferInstance
  A₀ := OA₀
  measurable := fun f hf => hf.1.continuous.measurable
  bounded := fun f hf => A₀_bounded hf
  memLp := fun f hf p _ _ => hf.1.continuous.memLp_of_hasCompactSupport hf.2
  dense := fun p hp hp' => by
    have := hp
    refine (Lp.dense_hasCompactSupport_contDiff (F := ℝ) (μ := G.μ) hp').mono ?_
    rintro u ⟨g, hug, hcs, hcd⟩
    exact ⟨g, ⟨hcd, hcs⟩, hug⟩
  comp_mem := fun k ψ hψ h0 f hf => comp_mem_A₀ k ψ hψ h0 f hf
  exhaustion := ⟨expo, fun n => ⟨expo_sm n, expo_cs n⟩,
    fun n => Eventually.of_forall fun x => expo_mono x (Nat.le_succ n),
    Eventually.of_forall expo_tendsto⟩
  Γ := Go
  L := Lg G.V
  Γ_mem := fun f hf g hg => A₀.Go_mem hf hg
  L_mem := fun f hf => G.Lg_mem hf
  Γ_symm := fun f _ g _ => Eventually.of_forall fun x => by simp [Go, mul_comm]
  Γ_add := fun f hf f' hf' g _ => Eventually.of_forall fun x => by
    simp [Go, deriv_add_s hf.1 hf'.1, add_mul]
  Γ_smul := fun c f hf g _ => Eventually.of_forall fun x => by
    simp [Go, deriv_smul_s c hf.1, mul_assoc]
  Γ_nonneg := fun f _ => Eventually.of_forall fun x => by
    simpa [Go] using mul_self_nonneg (deriv f x)
  diffusion := fun k ψ hψ _ f hf g hg => Eventually.of_forall fun x =>
    congrFun ((diffusion_s k ψ hψ f (fun i => (hf i).1)).1 g hg.1) x
  ibp := fun f hf g hg => by
    rw [G.ibp_A₀ hf hg]
    simp only [Go]
  integral_L := fun f hf => G.integral_L_zero hf

/-- On smooth functions the formula-defined `ΓA` of the Gibbs triple is `f' g'`. -/
lemma gibbsDiff_ΓA {f g : ℝ → ℝ} (hf : Sm f) (hg : Sm g) : G.gibbsDiff.ΓA f g = Go f g := by
  funext x
  have e : G.gibbsDiff.ΓA f g x = (Lg G.V (f * g) x - f x * Lg G.V g x - g x * Lg G.V f x) / 2 := rfl
  rw [e, Lg_mul hf hg x]; simp only [Go]; ring

/-- **Completeness** (BGL Def. 3.3.9) of every Gibbs triple (genuine cutoffs). -/
theorem gibbsDiff_isComplete : G.gibbsDiff.IsComplete :=
  Complete.isComplete_of_real _ (fun _ hf hc => ⟨hf, hc⟩)
    (fun _ _ => Filter.Eventually.of_forall fun _ => rfl)

/-- **Curvature of the Gibbs triple.**  If `V'' ≥ ρ` then the frozen `Γ₂` satisfies
`Γ₂(f) ≥ ρ Γ(f)` (everywhere, on smooth `f`), i.e. the pointwise content of `CD(ρ,∞)`. -/
theorem gibbsDiff_Γ₂_ge {ρ : ℝ} (hρ : ∀ x, ρ ≤ deriv (deriv G.V) x) {f : ℝ → ℝ} (hf : Sm f) (x : ℝ) :
    ρ * G.gibbsDiff.ΓA f f x ≤ G.gibbsDiff.Γ₂ f f x := by
  have e1 : G.gibbsDiff.ΓA f f = Go f f := G.gibbsDiff_ΓA hf hf
  have e2 : G.gibbsDiff.ΓA f (Lg G.V f) = Go f (Lg G.V f) := G.gibbsDiff_ΓA hf (sm_Lg G.smooth hf)
  have e3 : G.gibbsDiff.ΓA (Lg G.V f) f = Go (Lg G.V f) f := G.gibbsDiff_ΓA (sm_Lg G.smooth hf) hf
  have key := Γ₂_ge G.smooth hρ hf x
  have e : G.gibbsDiff.Γ₂ f f x = (Lg G.V (Go f f) x - 2 * Go f (Lg G.V f) x) / 2 := by
    show (Lg G.V (G.gibbsDiff.ΓA f f) x - G.gibbsDiff.ΓA f (Lg G.V f) x - G.gibbsDiff.ΓA (Lg G.V f) f x) / 2 = _
    rw [e1, e2, e3]
    simp only [Go]; ring
  rw [e, e1]
  exact key

end GibbsData

end MarkovTriple.BGL.Instances.Gibbs
