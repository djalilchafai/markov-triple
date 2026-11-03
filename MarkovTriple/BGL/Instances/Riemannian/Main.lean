import Mathlib
import MarkovTriple.BGL.Instances.Riemannian.Data

/-!
# Weighted Riemannian charts: Markov-triple layers, and a non-flat example

For `R : RiemData d` (`Riemannian/Data.lean`) the generic theory of `GibbsRd/Ell*.lean` applied to `R.toEll`:

* unconditional: `R.riemDiff : DiffusionTriple (Rd d)` (D1–D8) with `L = Δ_g − ∇W·∇` (`riem_L_eq`), completeness
  (`riemDiff_isComplete`), `riemPreFull` (F1, F2, F4–F7, F9 on `𝒜 = C^∞`), the integrated identity (3.3.8);
* under the named hypothesis `WeakHypo` (Def. 3.3.8): ESA (F10, Prop. 3.3.11), ergodicity (S10, Prop. 3.3.10);
* under `WeakHypo` and the curvature hypothesis `Curv ρ` (Def. 3.3.14 with `n = ∞`, a pointwise inequality for the
  formula-defined `Γ₂`): Poincaré, spectral gap, `L²` decay; with `F8` additionally the Full triple and `CD(ρ,∞)`.

NOT proved (see `STATEMENTS_R15_Riem.md`): the identification `Γ₂(f) = |∇∇f|² + (Ric_g + ∇∇W)(∇f,∇f)` (BGL (1.16.4),
Thm C.3.3) for a variable co-metric, hence the equivalence of `Curv ρ` with `Ric_g + ∇∇W ≥ ρ g` (1.16.8).  Mathlib (this
version) has the Levi-Civita connection and the Riemannian distance on manifolds, but no Riemann/Ricci curvature
tensor, no Hessian, no Laplace–Beltrami operator and no Riemannian volume measure.
-/

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace MarkovTriple.BGL.Instances.Riemannian

open MarkovTriple.BGL.Instances.GibbsRd
open MarkovTriple.BGL (pderiv pderiv₂ DiffusionTriple FullTriple PreFull)

variable {d : ℕ}

namespace RiemData
variable (R : RiemData d)

/-- `Γ(f,g) = Σ g^{ij} ∂ᵢf ∂ⱼg` is the carré du champ defined from `L` by `½(L(fg) − fLg − gLf)` (Def. 3.3.1 (iv)). -/
theorem riem_ΓA_eq {f h : Rd d → ℝ} (hf : Sm f) (hh : Sm h) :
    R.riemDiff.ΓA f h = R.Γ f h := R.toEll.ΓA_eq hf hh

/-- the semigroup-free extended-algebra axioms on `𝒜 = C^∞(ℝ^d)` -/
theorem riemPreFull : PreFull R.riemDiff (Afull d) := R.toEll.preFull

/-- **Weak hypo-ellipticity** (Def. 3.3.8), named hypothesis -/
abbrev WeakHypo : Prop := R.toEll.WeakHypo

/-- **F8** (Def. 3.3.1 (viii)), named hypothesis -/
abbrev F8 : Prop := R.toEll.F8

/-- **Curvature `CD(ρ,∞)`** (Def. 3.3.14) on smooth functions for the formula-defined `Γ₂` of Def. 3.3.12,
named hypothesis (the book's geometric reading is `Ric_g + ∇∇W ≥ ρ g`, (1.16.8); not formalised for variable `g`). -/
abbrev Curv (ρ : ℝ) : Prop := R.toEll.Curv ρ

/-- ESA (F10, BGL Prop. 3.3.11) -/
theorem riem_esaProp (hH : R.WeakHypo) : R.riemDiff.ESAProp := R.toEll.diff_esaProp hH

/-- Ergodicity (S10, BGL Prop. 3.3.10) -/
theorem riem_ergodic (hH : R.WeakHypo) :
    ∀ (u : MeasureTheory.Lp ℝ 2 R.riemDiff.μ) (hu : u ∈ R.riemDiff.generator.domain),
      R.riemDiff.generator ⟨u, hu⟩ = 0 → ∃ c : ℝ, (u : Rd d → ℝ) =ᵐ[R.riemDiff.μ] fun _ => c :=
  R.toEll.diff_ergodic hH

/-- integrated `Γ₂` (3.3.8) on test functions -/
theorem riem_integral_Γ₂ {f : Rd d → ℝ} (hf : f ∈ A₀ d) :
    ∫ x, R.riemDiff.Γ₂ f f x ∂(R.toEll.μ) = ∫ x, R.toEll.L f x * R.toEll.L f x ∂(R.toEll.μ) :=
  R.toEll.integral_Γ₂ hf

/-- **Poincaré** `Var_μ(f) ≤ ρ⁻¹ ∫ Γ(f) dμ` for the weighted Riemannian chart under `Curv ρ`, `WeakHypo`. -/
theorem riem_poincare {ρ : ℝ} (hρpos : 0 < ρ) (hρ : R.Curv ρ) (hH : R.WeakHypo) :
    R.riemDiff.PI (1 / ρ) := R.toEll.ell_poincare hρpos hρ hH

theorem riem_spectralGap {ρ : ℝ} (hρpos : 0 < ρ) (hρ : R.Curv ρ) (hH : R.WeakHypo) :
    (DiffusionTriple.formData R.riemDiff).HasSpectralGap ρ := R.toEll.ell_spectralGap hρpos hρ hH

theorem riem_expDecay {ρ : ℝ} (hρpos : 0 < ρ) (hρ : R.Curv ρ) (hH : R.WeakHypo) :
    (DiffusionTriple.formData R.riemDiff).HasExpDecay ρ := R.toEll.ell_expDecay hρpos hρ hH

/-- **The Riemannian Full Markov Triple** (Def. 3.3.25) under `WeakHypo`, `F8`. -/
noncomputable def riemFull (hH : R.WeakHypo) (h8 : R.F8) : FullTriple (Rd d) := R.toEll.full hH h8

theorem riemFull_CD (hH : R.WeakHypo) (h8 : R.F8) {ρ : ℝ} (hρ : R.Curv ρ) :
    (R.riemFull hH h8).CD ρ ∞ := R.toEll.full_CD hH h8 hρ

theorem riemFull_logSobolev (hH : R.WeakHypo) (h8 : R.F8) {ρ : ℝ} (hρpos : 0 < ρ) (hρ : R.Curv ρ)
    (hE : (R.riemFull hH h8).EntropyInterpolation) :
    (R.riemFull hH h8).toDiffusionTriple.LS (1 / ρ) 0 :=
  R.toEll.full_logSobolev hH h8 hρpos hρ hE

end RiemData

/-! ### A non-flat, non-Euclidean example: the diagonal co-metric `g^{ii} = 2 + sin xᵢ` with Gaussian weight -/

/-- the diagonal co-metric `g^{ij}(x) = δᵢⱼ (2 + sin xᵢ)` -/
noncomputable def diagCoMetric (i j : Fin d) (x : Rd d) : ℝ := if i = j then 2 + Real.sin (x i) else 0

/-- Riemannian datum with variable co-metric `diag(2 + sin xᵢ)` and weight `W = |x|²/2`: all fields proved,
so `RiemData` is not vacuous beyond the flat case. -/
noncomputable def diagRiem (d : ℕ) : RiemData d where
  g := diagCoMetric
  W := fun x => qd x / 2
  g_smooth := fun i j => by
    unfold diagCoMetric
    by_cases h : i = j
    · simp only [h, ite_true]
      exact contDiff_const.add (Real.contDiff_sin.comp (contDiff_apply ℝ ℝ j))
    · simp only [h, ite_false]; exact contDiff_const
  g_symm := fun i j x => by
    unfold diagCoMetric
    by_cases h : i = j
    · subst h; rfl
    · simp [h, Ne.symm h]
  g_posDef := fun x => by
    have : (Matrix.of fun i j : Fin d => diagCoMetric i j x) =
        Matrix.diagonal (fun i => 2 + Real.sin (x i)) := by
      ext i j
      by_cases h : i = j
      · subst h; simp [diagCoMetric]
      · simp [diagCoMetric, h]
    rw [this, Matrix.posDef_diagonal_iff]
    intro i
    have := Real.neg_one_le_sin (x i)
    linarith
  g_bdd := ⟨3, fun x v => by
    have : ∑ i, ∑ j, diagCoMetric i j x * v i * v j = ∑ i, (2 + Real.sin (x i)) * v i ^ 2 := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_eq_single i]
      · simp [diagCoMetric]; ring
      · intro j _ hji; simp [diagCoMetric, Ne.symm hji]
      · simp
    rw [this, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have := Real.sin_le_one (x i)
    nlinarith [sq_nonneg (v i)]⟩
  W_smooth := sm_qd.div_const 2
  integrable := by
    have hdet : ∀ x : Rd d, 1 ≤ (Matrix.det (Matrix.of fun i j : Fin d => diagCoMetric i j x)) := by
      intro x
      have : (Matrix.of fun i j : Fin d => diagCoMetric i j x) =
          Matrix.diagonal (fun i => 2 + Real.sin (x i)) := by
        ext i j
        by_cases h : i = j
        · subst h; simp [diagCoMetric]
        · simp [diagCoMetric, h]
      rw [this, Matrix.det_diagonal]
      exact Finset.one_le_prod₀ fun i _ => by
        have := Real.neg_one_le_sin (x i); linarith
    have hcont : Continuous (fun x : Rd d => Real.exp (-(qd x / 2)) *
        (Matrix.det (Matrix.of fun i j : Fin d => diagCoMetric i j x)) ^ (-(1 / 2 : ℝ))) := by
      have hc : Continuous (fun x : Rd d => Matrix.det (Matrix.of fun i j : Fin d => diagCoMetric i j x)) := by
        have : (fun x : Rd d => Matrix.det (Matrix.of fun i j : Fin d => diagCoMetric i j x)) =
            fun x => ∏ i, (2 + Real.sin (x i)) := by
          funext x
          have : (Matrix.of fun i j : Fin d => diagCoMetric i j x) =
              Matrix.diagonal (fun i => 2 + Real.sin (x i)) := by
            ext i j
            by_cases h : i = j
            · subst h; simp [diagCoMetric]
            · simp [diagCoMetric, h]
          rw [this, Matrix.det_diagonal]
        rw [this]
        exact continuous_finsetProd _ fun i _ =>
          continuous_const.add (Real.continuous_sin.comp (continuous_apply i))
      exact (Real.continuous_exp.comp (sm_qd.continuous.div_const 2).neg).mul
        (hc.rpow_const fun x => Or.inl (lt_of_lt_of_le one_pos (hdet x)).ne')
    refine Integrable.mono' (g := fun x : Rd d => Real.exp (-(qd x / 2)))
      (integrable_of_convex_rd (V := fun x : Rd d => qd x / 2) (sm_qd.div_const 2) one_pos hessGe_gauss)
      hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
    have h1 : (Matrix.det (Matrix.of fun i j : Fin d => diagCoMetric i j x)) ^ (-(1 / 2 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (hdet x) (by norm_num)
    have h0 : 0 ≤ (Matrix.det (Matrix.of fun i j : Fin d => diagCoMetric i j x)) ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_nonneg (by linarith [hdet x]) _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le h0)]
    calc _ ≤ Real.exp (-(qd x / 2)) * 1 := mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
      _ = _ := mul_one _

end MarkovTriple.BGL.Instances.Riemannian
