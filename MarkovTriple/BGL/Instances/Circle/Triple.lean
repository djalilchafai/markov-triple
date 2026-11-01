import Mathlib
import MarkovTriple.BGL.Instances.Circle.Ergodic
import MarkovTriple.BGL.Instances.Circle.PosDetect
import MarkovTriple.BGL.Frozen.CompactTriple
import MarkovTriple.BGL.Frozen.CD
import MarkovTriple.BGL.Semigroup.ESA
import MarkovTriple.BGL.Semigroup.Characterization
import MarkovTriple.BGL.Consistency

/-!
# The circle as a complete Compact (hence Full, Standard) Markov Triple with `Γ ≠ 0` (not frozen)

`E = 𝕋 = ℝ/ℤ`, `μ` the Haar probability measure, `𝒜₀ = 𝒜 = C^∞(𝕋)`, `L f = f''`, `Γ(f,g) = f' g'`.
D1–D8: `Sanity.circleDiffusion`.  Here:
* S10 `circle_ergodic`, S11 (`P_t 1 = 1`, via the eigenfunction `n = 0`) — `circleStandard`;
* F1–F10 — `circleFull`: F2 by `ae_nonneg_of_pairing`; F8 by the smoothing theorem (the Friedrichs semigroup
  acts by `e^{-(2πn)² t}` on Fourier modes); F9 from S10; F10 by `core_of_invariant` from F8
  (the invariance of the classes of `𝒜₀` under `P_t`);
* `circleCompact : CompactTriple 𝕋` (`𝒜 = 𝒜₀`);
* `circle_CD`: `CD(ρ, n)` for all `ρ ≤ 0`, `n ∈ [1, ∞]`, in particular `circle_CD_zero_top` (`CD(0,∞)`)
  and `circle_CD_zero_one` (`CD(0,1)`), in the sense of `FullTriple.CD` (all of `𝒜`).
-/

namespace MarkovTriple.BGL.Circle
open MeasureTheory AddCircle Filter Topology
open scoped ENNReal NNReal Real InnerProductSpace
open MarkovTriple.Sanity.Circle
local notation "𝒜c" => MarkovTriple.Sanity.Circle.A₀

/-- `Γ(f,g) = f' g'` pointwise on `𝒜₀`: the formula-defined `ΓA` of `cT` is `Gc`. -/
lemma ΓA_eq_Gc {f g : 𝕋 → ℝ} (hf : f ∈ 𝒜c) (hg : g ∈ 𝒜c) : cT.ΓA f g = Gc f g := by
  funext x
  have := Lc_mul hf hg x
  show (Lc (f * g) x - f x * Lc g x - g x * Lc f x) / 2 = Gc f g x
  rw [this]; simp only [Gc]; ring

/-- `𝒜 := C^∞(𝕋)`, as a unital subalgebra (same carrier as `A₀`; it contains the constants). -/
def Afull : Subalgebra ℝ (𝕋 → ℝ) where
  carrier := (𝒜c : Set (𝕋 → ℝ))
  add_mem' := fun {_ _} hf hg => add_mem hf hg
  mul_mem' := fun {_ _} hf hg => mul_mem hf hg
  algebraMap_mem' := fun r => by
    show _ ∈ 𝒜c
    rw [mem_A₀]; exact contDiff_const

lemma mem_Afull {f : 𝕋 → ℝ} : f ∈ Afull ↔ f ∈ 𝒜c := Iff.rfl

/-- `P_t` maps classes of test functions to classes of test functions (F8, and the hypothesis of
`core_of_invariant`). -/
theorem semigroup_cls_mem (t : ℝ≥0) (f : cT.A₀) :
    ∃ g ∈ 𝒜c, (cT.semigroup t (cT.cls f) : 𝕋 → ℝ) =ᵐ[cT.μ] g := by
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t) with h | ht
  · subst h
    refine ⟨f.1, f.2, ?_⟩
    rw [DiffusionTriple.semigroup_zero]
    exact DiffusionTriple.coeFn_cls cT f
  · exact smoothing ht (cT.cls f)

theorem semigroup_invariant (t : ℝ≥0) (f : cT.A₀) :
    ∃ g : cT.A₀, cT.semigroup t (cT.cls f) = cT.cls g := by
  obtain ⟨g, hg, hae⟩ := semigroup_cls_mem t f
  exact ⟨⟨g, hg⟩, Lp.ext (hae.trans (DiffusionTriple.coeFn_cls cT ⟨g, hg⟩).symm)⟩

/-- The circle as a Standard Markov Triple (S10, S11). -/
noncomputable def circleStandard : StandardTriple 𝕋 where
  toDiffusionTriple := cT
  ergodic := fun u hu h => circle_ergodic u hu h
  conservative := fun _ hu _ t =>
    DiffusionTriple.conservative_of_semigroup_one cT hu t (semigroup_one t)

/-- The circle as a Full Markov Triple (F1–F10) with `𝒜 = 𝒜₀ = C^∞(𝕋)`. -/
noncomputable def circleFull : FullTriple 𝕋 where
  toStandardTriple := circleStandard
  A := Afull
  A₀_le := fun f hf => mem_Afull.2 hf
  A_measurable := fun f hf => (A₀_prop (mem_Afull.1 hf)).2.2.measurable
  ideal := fun f hf h hh => mul_mem hh (mem_Afull.1 hf)
  pos_detect := fun f hf h => ae_nonneg_of_pairing (mem_Afull.1 hf) h
  A_comp := fun k ψ hψ f hf => by
    rw [mem_Afull, mem_A₀]
    exact hψ.comp (contDiff_pi.2 fun i => mem_A₀.1 (mem_Afull.1 (hf i)))
  L_mem_A := fun f hf => mem_Afull.2 (Lc_mem (mem_Afull.1 hf))
  ΓA_nonneg := fun f hf => Eventually.of_forall fun x => by
    have hf' := mem_Afull.1 hf
    show 0 ≤ cT.ΓA f f x
    rw [ΓA_eq_Gc hf' hf']
    exact mul_self_nonneg _
  diffusion_Γ_A := fun k ψ hψ f hf g hg => Eventually.of_forall fun x => by
    have hf' : ∀ i, f i ∈ 𝒜c := fun i => mem_Afull.1 (hf i)
    have hg' := mem_Afull.1 hg
    have hcomp : (fun x => ψ (fun i => f i x)) ∈ 𝒜c := by
      rw [mem_A₀]; exact hψ.comp (contDiff_pi.2 fun i => mem_A₀.1 (hf' i))
    show cT.ΓA (fun x => ψ (fun i => f i x)) g x =
      ∑ i, pderiv ψ i (fun j => f j x) * cT.ΓA (f i) g x
    rw [ΓA_eq_Gc hcomp hg']
    simp only [ΓA_eq_Gc (hf' _) hg']
    exact congrFun ((diffusion_c k ψ hψ f hf').1 g hg') x
  diffusion_L_A := fun k ψ hψ f hf => Eventually.of_forall fun x => by
    have hf' : ∀ i, f i ∈ 𝒜c := fun i => mem_Afull.1 (hf i)
    show Lc (fun x => ψ (fun i => f i x)) x = ∑ i, pderiv ψ i (fun j => f j x) * Lc (f i) x +
      ∑ i, ∑ j, pderiv₂ ψ i j (fun l => f l x) * cT.ΓA (f i) (f j) x
    simp only [ΓA_eq_Gc (hf' _) (hf' _)]
    exact congrFun ((diffusion_c k ψ hψ f hf').2) x
  ibp_A := fun f hf g hg => by
    have hf' := mem_Afull.1 hf
    have hg' : g ∈ 𝒜c := hg
    have e := ΓA_eq_Gc hf' hg'
    show (∫ x, cT.ΓA f g x ∂μ₀ = -∫ x, g x * Lc f x ∂μ₀) ∧
      (∫ x, cT.ΓA f g x ∂μ₀ = -∫ x, f x * Lc g x ∂μ₀)
    rw [e]
    have e2 : Gc g f = Gc f g := by funext x; simp [Gc, mul_comm]
    have h1 := ibp_c hf' hg'
    have h2 := ibp_c hg' hf'
    rw [e2] at h2
    exact ⟨by linarith, by linarith⟩
  semigroup_A := fun t f => by
    obtain ⟨g, hg, hae⟩ := semigroup_cls_mem t f
    exact ⟨g, mem_Afull.2 hg, hae⟩
  connected := fun f hf hΓ => by
    have hf' := mem_Afull.1 hf
    have e := ΓA_eq_Gc hf' hf'
    let F : cT.A₀ := ⟨f, hf'⟩
    have hΓ0 : cT.Γ f f =ᵐ[cT.μ] 0 := by
      have : cT.Γ f f = cT.ΓA f f := by rw [e]; rfl
      rw [this]; exact hΓ
    have hE : circleStandard.toDiffusionTriple.closedForm
        ⟨cT.cls F, (DiffusionTriple.formData cT).emb_mem_Q ⟨DiffusionTriple.clsₗ cT F, ⟨F, rfl⟩⟩⟩
        ⟨cT.cls F, (DiffusionTriple.formData cT).emb_mem_Q ⟨DiffusionTriple.clsₗ cT F, ⟨F, rfl⟩⟩⟩
        = 0 := by
      exact (DiffusionTriple.closedForm_cls cT F F).trans
        ((DiffusionTriple.energy_zero_iff cT F).2 hΓ0)
    obtain ⟨c, hc⟩ := StandardTriple.energy_zero_const circleStandard
      ⟨cT.cls F, (DiffusionTriple.formData cT).emb_mem_Q ⟨DiffusionTriple.clsₗ cT F, ⟨F, rfl⟩⟩⟩ hE
    exact ⟨c, (DiffusionTriple.coeFn_cls cT F).symm.trans hc⟩
  esa := fun u hu => DiffusionTriple.core_of_invariant cT semigroup_invariant u hu

/-- The circle as a Compact Markov Triple (`𝒜 = 𝒜₀`).  The ESA field `esa` of `circleFull` was
proved directly (`core_of_invariant`), and agrees with `CompactTriple.esa_auto`. -/
noncomputable def circleCompact : CompactTriple 𝕋 where
  toFullTriple := circleFull
  A_eq := fun _ => Iff.rfl

/-- Non-triviality: `Γ(cos 2π·, cos 2π·) ≠ 0`. -/
theorem circleCompact_Γ_ne_zero : circleCompact.Γ ⇑cC ⇑cC ≠ 0 := circle_Γ_ne_zero

/-- `Γ₂(f) = (L f)²` on the circle, `f ∈ 𝒜₀` (flat, one-dimensional), with the formula-defined `ΓA`. -/
theorem circle_Γ₂ {f : 𝕋 → ℝ} (hf : f ∈ 𝒜c) (x : 𝕋) : cT.Γ₂ f f x = (Lc f x) ^ 2 := by
  have h1 : cT.ΓA f f = D f * D f := by rw [ΓA_eq_Gc hf hf]; rfl
  have h2 := ΓA_eq_Gc hf (Lc_mem hf)
  have h3 := ΓA_eq_Gc (Lc_mem hf) hf
  have h4 := Lc_mul (D_mem hf) (D_mem hf) x
  show (Lc (cT.ΓA f f) x - cT.ΓA f (Lc f) x - cT.ΓA (Lc f) f x) / 2 = (Lc f x) ^ 2
  rw [h1, h2, h3, h4]
  simp only [Gc, Lc]
  ring

/-- **`CD(ρ, n)` for all `ρ ≤ 0` and `n ∈ [1, ∞]`** on the circle (BGL Def. 3.3.14, on all of `𝒜`). -/
theorem circle_CD {ρ : ℝ} (hρ : ρ ≤ 0) {n : ℝ≥0∞} (hn : 1 ≤ n) : circleCompact.toFullTriple.CD ρ n := by
  refine ⟨hn, fun f hf => Eventually.of_forall fun x => ?_⟩
  have hf' := mem_Afull.1 hf
  show ρ * cT.ΓA f f x + (n⁻¹).toReal * (Lc f x) ^ 2 ≤ cT.Γ₂ f f x
  rw [circle_Γ₂ hf' x, ΓA_eq_Gc hf' hf']
  have h1 : (n⁻¹).toReal ≤ 1 := by
    have : n⁻¹ ≤ 1 := ENNReal.inv_le_one.2 hn
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top this
  have h2 : ρ * Gc f f x ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hρ (mul_self_nonneg _)
  have h3 : (n⁻¹).toReal * (Lc f x) ^ 2 ≤ (Lc f x) ^ 2 := by
    nlinarith [sq_nonneg (Lc f x)]
  linarith

/-- `CD(0, ∞)` on the circle. -/
theorem circle_CD_zero_top : circleCompact.toFullTriple.CD 0 ⊤ := circle_CD le_rfl le_top

/-- `CD(0, 1)` on the circle. -/
theorem circle_CD_zero_one : circleCompact.toFullTriple.CD 0 1 := circle_CD le_rfl le_rfl

/-- `circle_CD_zero`: the circle satisfies both `CD(0,∞)` and `CD(0,1)`. -/
theorem circle_CD_zero :
    circleCompact.toFullTriple.CD 0 ⊤ ∧ circleCompact.toFullTriple.CD 0 1 :=
  ⟨circle_CD_zero_top, circle_CD_zero_one⟩

end MarkovTriple.BGL.Circle
