import Mathlib
import MarkovTriple.BGL.Instances.LebesgueRd.Full.Identify
import MarkovTriple.BGL.Instances.LebesgueRd.Full.Ergodic
import MarkovTriple.BGL.Instances.LebesgueRd.Full.Esa
import MarkovTriple.BGL.Instances.LebesgueRd.Full.DomainAPI
import MarkovTriple.BGL.Instances.LebesgueRd.FullEasy
import MarkovTriple.BGL.Frozen.FullTriple
import MarkovTriple.BGL.Frozen.CD
import MarkovTriple.BGL.Semigroup.Conservative

/-!
# The Brownian full triple on `(ℝ^d, Lebesgue)` (BGL Def. 3.3.25), and `CD(0, d)` (Round 24, stream A)

`lebesgueRdFull d hd : FullTriple (Fin d → ℝ)` with `𝒜₀ = C_c^∞`, `𝒜 = C^∞`, `L = Δ`, `Γ = ∇f·∇g`
(infinite measure; `FullTriple` does not force a probability measure).  Fields F1–F7, F9 from `FullEasy`
(through `preFull_lebesgueRd`), F10 from `Esa.lean`, S10 from `Ergodic.lean`, F8 and S11 from the
Duhamel identification `Identify.lean`.  `lebesgueRdFull_CD_iff`: `CD(ρ, n)` holds iff `ρ ≤ 0` and `d ≤ n`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal LinearPMap InnerProductSpace

namespace MarkovTriple.BGL.LebesgueRd

open MarkovTriple.BGL

variable {d : ℕ}

lemma semigroup_ae_heatRd (hd : 1 ≤ d) {f : (Fin d → ℝ) → ℝ} (hf : f ∈ A₀ d) (t : ℝ≥0) :
    ((lebesgueRdDiffusion d hd).semigroup t ((lebesgueRdDiffusion d hd).cls ⟨f, hf⟩) :
        (Fin d → ℝ) → ℝ) =ᵐ[volume] heatRd (Real.sqrt (2 * t)) f := by
  rw [semigroup_eq_heatRd hd hf t]
  exact coeFn_heatL2 hf _

/-- **S11** for `(ℝ^d, Lebesgue)`. -/
theorem conservative_lebesgueRd (hd : 1 ≤ d) (u : ℕ → (Fin d → ℝ) → ℝ)
    (hu : IsExhaustion (lebesgueRdDiffusion d hd).μ (lebesgueRdDiffusion d hd).A₀ u)
    (hnn : ∀ n, 0 ≤ᵐ[(lebesgueRdDiffusion d hd).μ] u n) (t : ℝ≥0) :
    ∀ᵐ x ∂(lebesgueRdDiffusion d hd).μ, Tendsto (fun n => ((lebesgueRdDiffusion d hd).semigroup t
      ((lebesgueRdDiffusion d hd).cls ⟨u n, hu.1 n⟩) : (Fin d → ℝ) → ℝ) x) atTop (𝓝 1) := by
  have hae : ∀ᵐ x ∂(volume : Measure (Fin d → ℝ)), ∀ n, ((lebesgueRdDiffusion d hd).semigroup t
      ((lebesgueRdDiffusion d hd).cls ⟨u n, hu.1 n⟩) : (Fin d → ℝ) → ℝ) x =
        heatRd (Real.sqrt (2 * t)) (u n) x :=
    ae_all_iff.2 fun n => semigroup_ae_heatRd hd (hu.1 n) t
  rcases (zero_le : (0 : ℝ≥0) ≤ t).eq_or_lt with h0 | hpos
  · subst h0
    have e : DiffusionTriple.semigroup (lebesgueRdDiffusion d hd) 0 = 1 :=
      (DiffusionTriple.formData (lebesgueRdDiffusion d hd)).semigroup_zero
    have hc : ∀ᵐ x ∂(volume : Measure (Fin d → ℝ)), ∀ n,
        ((lebesgueRdDiffusion d hd).cls ⟨u n, hu.1 n⟩ : (Fin d → ℝ) → ℝ) x = u n x :=
      ae_all_iff.2 fun n => (lebesgueRdDiffusion d hd).coeFn_cls ⟨u n, hu.1 n⟩
    filter_upwards [hc, hu.2.2] with x h1 h2
    simp only [e, one_apply_eq_self]
    exact h2.congr (fun n => (h1 n).symm)
  · have ha : Real.sqrt (2 * (t : ℝ)) ≠ 0 := by
      have : (0 : ℝ) < t := by exact_mod_cast hpos
      exact (Real.sqrt_pos.2 (by linarith)).ne'
    have hle : ∀ n, ∀ᵐ y ∂(volume : Measure (Fin d → ℝ)), |u n y| ≤ 1 := by
      intro n
      filter_upwards [hu.le_one_ae, hnn n] with y h1 h2
      rw [abs_of_nonneg h2]; exact h1 n
    filter_upwards [hae] with x hx
    have := heatRd_tendsto_one ha (fun n => (smooth (hu.1 n)).continuous.measurable) hle hu.2.2 x
    exact this.congr (fun n => (hx n).symm)

/-- **F8** for `(ℝ^d, Lebesgue)`. -/
theorem semigroup_A (hd : 1 ≤ d) (t : ℝ≥0) (f : (lebesgueRdDiffusion d hd).A₀) :
    ∃ g ∈ A d, ((lebesgueRdDiffusion d hd).semigroup t ((lebesgueRdDiffusion d hd).cls f) :
      (Fin d → ℝ) → ℝ) =ᵐ[volume] g :=
  ⟨heatRd (Real.sqrt (2 * t)) f.1, mem_A.2 (heatRd_smooth f.2 _), semigroup_ae_heatRd hd f.2 t⟩

/-- **The Brownian full triple on `(ℝ^d, Lebesgue)`.** -/
noncomputable def lebesgueRdFull (d : ℕ) (hd : 1 ≤ d) : FullTriple (Fin d → ℝ) where
  toStandardTriple :=
    { toDiffusionTriple := lebesgueRdDiffusion d hd
      ergodic := fun u hu h => ergodic_lebesgueRd hd u hu h
      conservative := fun u hu hnn t => conservative_lebesgueRd hd u hu hnn t }
  A := A d
  A₀_le := (preFull_lebesgueRd hd).A₀_le
  A_measurable := (preFull_lebesgueRd hd).A_measurable
  ideal := (preFull_lebesgueRd hd).ideal
  pos_detect := (preFull_lebesgueRd hd).pos_detect
  A_comp := fun _ ψ hψ f hf => A_comp ψ hψ f hf
  L_mem_A := (preFull_lebesgueRd hd).L_mem_A
  ΓA_nonneg := (preFull_lebesgueRd hd).ΓA_nonneg
  diffusion_Γ_A := (preFull_lebesgueRd hd).diffusion_Γ_A
  diffusion_L_A := fun k ψ hψ f hf => F6L hd k ψ hψ f hf
  ibp_A := (preFull_lebesgueRd hd).ibp_A
  semigroup_A := fun t f => semigroup_A hd t f
  connected := (preFull_lebesgueRd hd).connected
  esa := fun u hu => esa_lebesgueRd hd u hu

theorem lebesgueRdFull_toDiffusionTriple (hd : 1 ≤ d) :
    (lebesgueRdFull d hd).toDiffusionTriple = lebesgueRdDiffusion d hd := rfl

theorem lebesgueRdFull_A (hd : 1 ≤ d) : (lebesgueRdFull d hd).A = A d := rfl

/-! ### Curvature-dimension: `CD(ρ, n) ↔ ρ ≤ 0 ∧ d ≤ n` -/

lemma continuous_Gf {f : (Fin d → ℝ) → ℝ} (hf : Sm f) : Continuous (Gf f f) := by
  have : Gf f f = fun y => ∑ i, dd i f y * dd i f y := rfl
  rw [this]
  exact continuous_finsetSum _ fun i _ => (hf.dd i).continuous.mul (hf.dd i).continuous

lemma continuous_Lf {f : (Fin d → ℝ) → ℝ} (hf : Sm f) : Continuous (Lf f) := by
  have : Lf f = fun y => ∑ i, dd i (dd i f) y := rfl
  rw [this]
  exact continuous_finsetSum _ fun i _ => ((hf.dd i).dd i).continuous

lemma continuous_Γ₂ (hd : 1 ≤ d) {f : (Fin d → ℝ) → ℝ} (hf : Sm f) :
    Continuous (fun x => (lebesgueRdDiffusion d hd).Γ₂ f f x) := by
  have : (fun x => (lebesgueRdDiffusion d hd).Γ₂ f f x) =
      fun x => ∑ i, ∑ j, (dd i (dd j f) x) ^ 2 := funext (Γ₂_eq hd hf)
  rw [this]
  exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    (((hf.dd j).dd i).continuous).pow 2

lemma le_of_ae_le_continuous {F G : (Fin d → ℝ) → ℝ} (hF : Continuous F) (hG : Continuous G)
    (h : F ≤ᵐ[volume] G) : ∀ x, F x ≤ G x := by
  by_contra hx
  push Not at hx
  obtain ⟨x, hx⟩ := hx
  have hpos : 0 < (volume : Measure (Fin d → ℝ)) {y | G y < F y} :=
    (isOpen_lt hG hF).measure_pos volume ⟨x, hx⟩
  have h0 : (volume : Measure (Fin d → ℝ)) {y | G y < F y} = 0 :=
    measure_mono_null (fun y hy => not_le.2 hy) (ae_iff.1 h)
  exact hpos.ne' h0

theorem lebesgueRdFull_CD_iff (hd : 1 ≤ d) (ρ : ℝ) (n : ℝ≥0∞) :
    (lebesgueRdFull d hd).CD ρ n ↔ ρ ≤ 0 ∧ (d : ℝ≥0∞) ≤ n := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hΓ₂nn : ∀ {f : (Fin d → ℝ) → ℝ}, Sm f → ∀ x,
      0 ≤ (lebesgueRdDiffusion d hd).Γ₂ f f x := fun {f} hf x => by
    rw [Γ₂_eq hd hf x]
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  have hGnn : ∀ (f : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ), 0 ≤ Gf f f x := fun f x =>
    Finset.sum_nonneg fun i _ => mul_self_nonneg _
  show (1 ≤ n ∧ ∀ f ∈ A d, ∀ᵐ x ∂(volume : Measure (Fin d → ℝ)),
      ρ * (lebesgueRdDiffusion d hd).ΓA f f x + (n⁻¹).toReal * (Lf f x) ^ 2 ≤
        (lebesgueRdDiffusion d hd).Γ₂ f f x) ↔ _
  constructor
  · rintro ⟨h1, h⟩
    have hall : ∀ f : (Fin d → ℝ) → ℝ, Sm f → ∀ x, ρ * Gf f f x + (n⁻¹).toReal * (Lf f x) ^ 2 ≤
        (lebesgueRdDiffusion d hd).Γ₂ f f x := by
      intro f hf
      refine le_of_ae_le_continuous (((continuous_Gf hf).const_smul ρ).add
        ((continuous_Lf hf).pow 2 |>.const_smul (n⁻¹).toReal)) (continuous_Γ₂ hd hf) ?_
      filter_upwards [h f (mem_A.2 hf)] with x hx
      rw [ΓA_eq_Gf hd hf hf] at hx
      simpa using hx
    by_cases hn : n = ⊤
    · subst hn
      have := hall _ (contDiff_apply ℝ ℝ (⟨0, hd⟩ : Fin d)) 0
      rw [Gf_coord hd, Lf_coord hd, Γ₂_coord hd] at this
      refine ⟨by simpa using this, le_top⟩
    · have hn1 : (1 : ℝ) ≤ n.toReal := by
        simpa using ENNReal.toReal_mono hn h1
      have hnpos : 0 < n.toReal := by linarith
      have hall' : ∀ f : (Fin d → ℝ) → ℝ, Sm f → ∀ x, ρ * Gf f f x + (1 / n.toReal) * (Lf f x) ^ 2 ≤
          (lebesgueRdDiffusion d hd).Γ₂ f f x := by
        intro f hf x
        have := hall f hf x
        rwa [ENNReal.toReal_inv, ← one_div] at this
      obtain ⟨hρ, hdn⟩ := (bochner_Rd_iff hd hnpos).1 hall'
      refine ⟨hρ, ?_⟩
      exact (ENNReal.toReal_le_toReal (ENNReal.natCast_ne_top d) hn).1 (by simpa using hdn)
  · rintro ⟨hρ, hdn⟩
    have h1 : 1 ≤ n := le_trans (by exact_mod_cast hd) hdn
    refine ⟨h1, fun f hf => Filter.Eventually.of_forall fun x => ?_⟩
    have hf' : Sm f := mem_A.1 hf
    rw [ΓA_eq_Gf hd hf' hf']
    by_cases hn : n = ⊤
    · subst hn
      simp only [ENNReal.inv_top, ENNReal.toReal_zero, zero_mul, add_zero]
      nlinarith [hΓ₂nn hf' x, hGnn f x, mul_nonpos_of_nonpos_of_nonneg hρ (hGnn f x)]
    · have hn1 : (1 : ℝ) ≤ n.toReal := by
        simpa using ENNReal.toReal_mono hn h1
      have hnpos : 0 < n.toReal := by linarith
      have hdn' : (d : ℝ) ≤ n.toReal := by simpa using ENNReal.toReal_mono hn hdn
      have := (bochner_Rd_iff hd hnpos).2 ⟨hρ, hdn'⟩ f hf' x
      rwa [ENNReal.toReal_inv, ← one_div]

end MarkovTriple.BGL.LebesgueRd
