import Mathlib
import MarkovTriple.Frozen.CDFull
import MarkovTriple.FunctionalInequalities.BEChain
import MarkovTriple.FunctionalInequalities.BEBdd

/-! # Bakry–Émery (Phase 4b), part 2: the `Γ`-calculus step `e'' = 2 ∫ G Γ₂(log G) ≥ 2ρ I`

Pure `Γ`-calculus on `𝒜` (no semigroup): for `u ∈ 𝒜` with the regularity `BEReg` and `G = exp ∘ u`,
`CDFull ρ ∞` gives
`2 ρ ∫ G Γ(u) ≤ ∫ (LG)²/G + ∫ u · L(LG)`.
The proof uses only the mixed integration by parts `ibp_AA` and the chain rule `diffusion_A`. -/

open MeasureTheory
open scoped ENNReal

namespace MarkovTriple.BE

variable {E : Type*} [MeasurableSpace E] (F : FullMarkovTriple E)

/-- **Regularity of a function in the Bakry–Émery computation** (finite `μ`): `f`, `Lf`, `Γ(f,f)` are
essentially bounded and `L(Lf)`, `L Γ(f,f)` are in `L²`.  This is what the integrations by parts
of the Bakry–Émery computation need on `u = log P_t h`. -/
structure BEReg (f : E → ℝ) : Prop where
  bdd : MemLp f ∞ F.μ
  Lbdd : MemLp (F.L f) ∞ F.μ
  Γbdd : MemLp (F.Γ f f) ∞ F.μ
  LL : MemLp (F.L (F.L f)) 2 F.μ
  LΓ : MemLp (F.L (F.Γ f f)) 2 F.μ

lemma exp_comp_mem {u : E → ℝ} (hu : u ∈ F.A) : (fun x => Real.exp (u x)) ∈ F.A :=
  comp_mem_A F Real.contDiff_exp hu

lemma L_exp_comp {u : E → ℝ} (hu : u ∈ F.A) :
    F.L (fun x => Real.exp (u x)) =
      fun x => Real.exp (u x) * F.L u x + Real.exp (u x) * F.Γ u u x := by
  have h := L_comp F Real.contDiff_exp hu
  rw [h]
  funext x
  simp [Real.deriv_exp]

lemma Γ_exp_comp {u : E → ℝ} (hu : u ∈ F.A) {g : E → ℝ} (hg : g ∈ F.A) :
    F.Γ (fun x => Real.exp (u x)) g = fun x => Real.exp (u x) * F.Γ u g x := by
  have h := Γ_comp F Real.contDiff_exp hu hg
  rw [h]
  funext x
  simp [Real.deriv_exp]

lemma memLp_exp_top [IsFiniteMeasure F.μ] {u : E → ℝ} (hu : u ∈ F.A) (hb : MemLp u ∞ F.μ) :
    MemLp (fun x => Real.exp (u x)) ∞ F.μ := by
  obtain ⟨C, hC⟩ := bd_of_memLp_top hb
  refine memLp_top_of_bd (C := Real.exp C)
    (Real.continuous_exp.measurable.comp (F.A_measurable u hu)).aestronglyMeasurable ?_
  filter_upwards [hC] with x hx
  rw [abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.2 ((le_abs_self _).trans hx)

lemma memLp_LG_top [IsFiniteMeasure F.μ] {u : E → ℝ} (hu : u ∈ F.A) (hr : BEReg F u) :
    MemLp (F.L (fun x => Real.exp (u x))) ∞ F.μ := by
  rw [L_exp_comp F hu]
  have hGb := memLp_exp_top F hu hr.bdd
  exact memLp_top_add (memLp_top_mul hGb hr.Lbdd) (memLp_top_mul hGb hr.Γbdd)

theorem alg [IsFiniteMeasure F.μ] {ρ : ℝ} (hCD : F.CDFull ρ ∞) {u : E → ℝ} (hu : u ∈ F.A)
    (hr : BEReg F u) (hLLG : MemLp (F.L (F.L (fun x => Real.exp (u x)))) 2 F.μ) :
    2 * ρ * ∫ x, Real.exp (u x) * F.Γ u u x ∂F.μ ≤
      (∫ x, (F.L (fun y => Real.exp (u y)) x) ^ 2 / Real.exp (u x) ∂F.μ) +
        ∫ x, u x * F.L (F.L (fun y => Real.exp (u y))) x ∂F.μ := by
  set G : E → ℝ := fun x => Real.exp (u x) with hG
  set a : E → ℝ := F.L u with ha
  set w : E → ℝ := F.Γ u u with hw
  have hGA : G ∈ F.A := exp_comp_mem F hu
  have haA : a ∈ F.A := F.L_mem_A u hu
  have hwA : w ∈ F.A := F.Γ_mem_A u hu u hu
  have hLGe : F.L G = fun x => G x * a x + G x * w x := L_exp_comp F hu
  have hGb : MemLp G ∞ F.μ := memLp_exp_top F hu hr.bdd
  have hab : MemLp a ∞ F.μ := hr.Lbdd
  have hwb : MemLp w ∞ F.μ := hr.Γbdd
  have hLGb : MemLp (F.L G) ∞ F.μ := by
    rw [hLGe]
    exact memLp_top_add (memLp_top_mul hGb hab) (memLp_top_mul hGb hwb)
  have hLGA : F.L G ∈ F.A := F.L_mem_A G hGA
  have two : ∀ {f : E → ℝ}, MemLp f ∞ F.μ → MemLp f 2 F.μ := fun h => memLp_of_memLp_top h 2
  have iint : ∀ {f g : E → ℝ}, MemLp f ∞ F.μ → MemLp g ∞ F.μ →
      Integrable (fun x => f x * g x) F.μ := fun hf hg => integrable_top_mul_two hf (two hg)
  -- the three integrations by parts
  have I1 := F.ibp_AA G hGA a haA (two hGb) (two hLGb) (two hab) hr.LL hab
  have I2 := F.ibp_AA G hGA w hwA (two hGb) (two hLGb) (two hwb) hr.LΓ hwb
  have I3 := F.ibp_AA w hwA G hGA (two hwb) hr.LΓ (two hGb) (two hLGb) hGb
  have I4 := F.ibp_AA (F.L G) hLGA u hu (two hLGb) hLLG (two hr.bdd) (two hab) hr.bdd
  have I5 := F.ibp_AA u hu (F.L G) hLGA (two hr.bdd) (two hab) (two hLGb) hLLG hLGb
  have eΓa : F.Γ G a = fun x => G x * F.Γ u a x := Γ_exp_comp F hu haA
  have eΓw : F.Γ G w = fun x => G x * F.Γ u w x := Γ_exp_comp F hu hwA
  have sw : F.Γ w G = F.Γ G w := F.Γ_symm_A w hwA G hGA
  have su : F.Γ u (F.L G) = F.Γ (F.L G) u := F.Γ_symm_A u hu _ hLGA
  -- the identities
  have J1 : ∫ x, a x * F.L G x ∂F.μ = -∫ x, G x * F.Γ u a x ∂F.μ := by
    have := I1.2; rw [eΓa] at this; exact this
  have J2 : ∫ x, w x * F.L G x ∂F.μ = -∫ x, G x * F.Γ u w x ∂F.μ := by
    have := I2.2; rw [eΓw] at this; exact this
  have J3 : ∫ x, G x * F.L w x ∂F.μ = -∫ x, G x * F.Γ u w x ∂F.μ := by
    have := I3.2; rw [sw, eΓw] at this; exact this
  have J4 : ∫ x, u x * F.L (F.L G) x ∂F.μ = ∫ x, a x * F.L G x ∂F.μ := by
    have h4 := I4.2
    have h5 := I5.2
    have e : ∫ x, F.L G x * F.L u x ∂F.μ = ∫ x, a x * F.L G x ∂F.μ := by
      congr 1; funext x; ring
    rw [su] at h5
    rw [← e, h5, ← h4]
  -- integrability
  have iGΓua : Integrable (fun x => G x * F.Γ u a x) F.μ := by
    have := I1.1; rw [eΓa] at this; exact this
  have iGΓuw : Integrable (fun x => G x * F.Γ u w x) F.μ := by
    have := I2.1; rw [eΓw] at this; exact this
  have iGLw : Integrable (fun x => G x * F.L w x) F.μ := integrable_top_mul_two hGb hr.LΓ
  have iaLG : Integrable (fun x => a x * F.L G x) F.μ := iint hab hLGb
  have iwLG : Integrable (fun x => w x * F.L G x) F.μ := iint hwb hLGb
  have iGw : Integrable (fun x => G x * w x) F.μ := iint hGb hwb
  -- curvature
  have hcd : ∀ᵐ x ∂F.μ, G x * (ρ * w x) ≤ G x * ((F.L w x - 2 * F.Γ u a x) / 2) := by
    filter_upwards [(hCD.2 u hu)] with x hx
    have hGx : 0 < G x := Real.exp_pos _
    have hx' : ρ * w x ≤ (F.L w x - 2 * F.Γ u a x) / 2 := by
      have : ρ * F.Γ u u x + ((∞ : ℝ≥0∞)⁻¹).toReal * (F.L u x) ^ 2 ≤ F.toMarkovTriple.Γ₂ u x := hx
      simpa [MarkovTriple.Γ₂, ENNReal.inv_top] using this
    exact mul_le_mul_of_nonneg_left hx' hGx.le
  have iR : Integrable (fun x => G x * ((F.L w x - 2 * F.Γ u a x) / 2)) F.μ := by
    have : (fun x => G x * ((F.L w x - 2 * F.Γ u a x) / 2)) =
        fun x => (1 / 2 : ℝ) * (G x * F.L w x) - G x * F.Γ u a x := by
      funext x; ring
    rw [this]
    exact (iGLw.const_mul _).sub iGΓua
  have hmono := integral_mono_ae (iGw.const_mul ρ |>.congr (Filter.Eventually.of_forall
    fun x => by simp only []; ring)) iR hcd
  have hL1 : ∫ x, G x * (ρ * w x) ∂F.μ = ρ * ∫ x, G x * w x ∂F.μ := by
    rw [← integral_const_mul]; congr 1; funext x; ring
  have hR1 : ∫ x, G x * ((F.L w x - 2 * F.Γ u a x) / 2) ∂F.μ =
      (1 / 2 : ℝ) * (∫ x, G x * F.L w x ∂F.μ) - ∫ x, G x * F.Γ u a x ∂F.μ := by
    have : (fun x => G x * ((F.L w x - 2 * F.Γ u a x) / 2)) =
        fun x => (1 / 2 : ℝ) * (G x * F.L w x) - G x * F.Γ u a x := by
      funext x; ring
    rw [this, integral_sub (iGLw.const_mul _) iGΓua, integral_const_mul]
  have hq : (fun x => (F.L G x) ^ 2 / G x) = fun x => a x * F.L G x + w x * F.L G x := by
    funext x
    have hGx : 0 < G x := Real.exp_pos _
    simp only [hLGe]
    field_simp
  rw [hL1, hR1] at hmono
  rw [hq, integral_add iaLG iwLG, J4]
  have hGLw : ∫ x, G x * F.L w x ∂F.μ = ∫ x, w x * F.L G x ∂F.μ := by rw [J3, J2]
  rw [hGLw] at hmono
  have e1 : ∫ x, G x * F.Γ u a x ∂F.μ = -∫ x, a x * F.L G x ∂F.μ := by linarith [J1]
  rw [e1] at hmono
  linarith

end MarkovTriple.BE
