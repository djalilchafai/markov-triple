import Mathlib
import MarkovTriple.BGL.Instances.Gibbs.FunctIBP
import MarkovTriple.BGL.Instances.Gibbs.FunctESA

/-!
# The Gibbs extended algebra `𝒜 = C^∞(ℝ)` (BGL Def. 3.3.1 (i)-(vii), Def. 3.3.7) and its curvature

For `G : GibbsData` this proves, with no hypothesis on the semigroup, that `𝒜 = C^∞(ℝ)` satisfies all the
semigroup-free axioms of an extended algebra (`gibbs_preFull : PreFull G.gibbsDiff Afull`: F1, F2, F4-F7, F9),
that the triple is complete (Def. 3.3.9, `gibbsDiff_isComplete`), and the pointwise curvature inequality
`Γ₂ ≥ ρ Γ` on all of `𝒜` for `V'' ≥ ρ` (`gibbs_CD_pointwise`, the content of BGL Def. 3.3.14 for `n = ∞`).
It then specialises the general Props. 3.3.10/3.3.11 (`FunctESA.lean`) to the Gibbs triple (`gibbsDiff_esaProp`,
`gibbsDiff_ergodic`).  The two regularity statements weak hypo-ellipticity (`WeakHypo`, Def. 3.3.8) and F8
(`P_t 𝒜₀ ⊂ 𝒜`, Def. 3.3.1 (viii)) are defined here as `Prop`s; they are PROVED for every `GibbsData` in
`RegHypo.lean` (`GibbsData.weakHypo`) and `RegSemigroup.lean` (`GibbsData.f8`) (round 15), and the unconditional
corollaries are in `RegMain.lean`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal
open MarkovTriple.Sanity.OU hiding A₀ γ φ

local notation "OA₀" => MarkovTriple.Sanity.OU.A₀

namespace MarkovTriple.BGL.Instances.Gibbs

namespace GibbsData
variable (G : GibbsData)

/-- positivity detection (F2, BGL Def. 3.3.1 (ii)) for smooth functions (via a bump function). -/
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

/-- **Weak hypo-ellipticity** (BGL Def. 3.3.8) of the Gibbs triple with `𝒜 = C^∞(ℝ)`: every `f ∈ 𝒟(L*)`
with `L* f = λ f` (Def. 3.1.9), for any `λ ∈ ℝ`, belongs to `𝒜`.  This is classical elliptic regularity for
`f'' - V' f' = λ f` which the book quotes (Sect. 1.12) and does not prove; proved in `RegHypo.lean`
(`GibbsData.weakHypo`), so it is no longer a hypothesis. -/
def WeakHypo : Prop := G.gibbsDiff.WeakHypoElliptic Afull

/-- **F8 for the Gibbs triple** (BGL Def. 3.3.1 (viii)): `P_t f ∈ 𝒜 = C^∞(ℝ)` (as an `L²`-class it has a smooth
representative) for `f ∈ 𝒜₀`.  Regularity of the Friedrichs semigroup; quoted, not proved, by the book
(hypo-elliptic case, Sect. 1.12, p. 49); proved in `RegSemigroup.lean` (`GibbsData.f8`). -/
def F8 : Prop :=
  ∀ (t : ℝ≥0) (f : G.gibbsDiff.A₀), ∃ g ∈ Afull,
    (G.gibbsDiff.semigroup t (G.gibbsDiff.cls f) : ℝ → ℝ) =ᵐ[G.μ] g

instance : IsProbabilityMeasure G.gibbsDiff.μ := inferInstanceAs (IsProbabilityMeasure G.μ)

/-- **The semigroup-free axioms of the extended algebra `𝒜 = C^∞(ℝ)` for the Gibbs triple.** -/
theorem gibbs_preFull : PreFull G.gibbsDiff Afull where
  A₀_le := fun f hf => hf.1
  A_measurable := fun f hf => (show Sm f from hf).continuous.measurable
  ideal := fun f hf h hh => ⟨(hh.1).mul (show Sm f from hf), hh.2.mul_right⟩
  pos_detect := fun f hf h =>
    Eventually.of_forall (G.pos_detect_aux (show Sm f from hf) h)
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
  ibp_A := fun f hf g hg => by
    have hf' : Sm f := hf
    have e : G.gibbsDiff.ΓA f g = Go f g := G.gibbsDiff_ΓA hf' hg.1
    refine ⟨?_, ?_⟩
    · show ∫ x, G.gibbsDiff.ΓA f g x ∂G.μ = -∫ x, g x * Lg G.V f x ∂G.μ
      rw [e, G.ibp_sm hf' hg.1 (Or.inl hg.2), neg_neg]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp [Go, mul_comm]
    · show ∫ x, G.gibbsDiff.ΓA f g x ∂G.μ = -∫ x, f x * Lg G.V g x ∂G.μ
      rw [e, G.ibp_sm hg.1 hf' (Or.inr hg.2)]
      simp [Go]
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

/-- **`CD(ρ,∞)` content on the whole extended algebra**: for `V'' ≥ ρ`, every `f ∈ 𝒜 = C^∞(ℝ)` satisfies
`ρ Γ(f) ≤ Γ₂(f)` everywhere (BGL Def. 3.3.14 with `n = ∞`). -/
theorem gibbs_CD_pointwise {ρ : ℝ} (hρ : ∀ x, ρ ≤ deriv (deriv G.V) x) :
    ∀ f ∈ Afull, ∀ x, ρ * G.gibbsDiff.ΓA f f x + ((∞ : ℝ≥0∞)⁻¹).toReal * (Lg G.V f x) ^ 2 ≤
      G.gibbsDiff.Γ₂ f f x := fun f hf x => by
  simpa using G.gibbsDiff_Γ₂_ge hρ (show Sm f from hf) x

/-- **ESA (F10) for the Gibbs triple**, BGL Prop. 3.3.11 (connexity + weak hypo-ellipticity + completeness)
applied to `gibbs_preFull` (F1, F2, F4-F7, F9) and `gibbsDiff_isComplete` (Def. 3.3.9). -/
theorem gibbsDiff_esaProp (hH : G.WeakHypo) : G.gibbsDiff.ESAProp :=
  DiffusionTriple.ESAProp_of_weakHypo G.gibbsDiff G.gibbs_preFull G.gibbsDiff_isComplete hH

/-- **Ergodicity (S10) for the Gibbs triple**, BGL Prop. 3.3.10 applied to `gibbs_preFull` (see the status
note on `DiffusionTriple.ergodic_of_weakHypo` in `FunctESA.lean`: the integration by parts of the book's proof
is replaced by the cut-off computation of Prop. 3.2.1, using completeness). -/
theorem gibbsDiff_ergodic (hH : G.WeakHypo) :
    ∀ (u : Lp ℝ 2 G.gibbsDiff.μ) (hu : u ∈ G.gibbsDiff.generator.domain),
      G.gibbsDiff.generator ⟨u, hu⟩ = 0 → ∃ c : ℝ, (u : ℝ → ℝ) =ᵐ[G.gibbsDiff.μ] fun _ => c :=
  DiffusionTriple.ergodic_of_weakHypo G.gibbsDiff G.gibbs_preFull G.gibbsDiff_isComplete hH

end GibbsData

end MarkovTriple.BGL.Instances.Gibbs
