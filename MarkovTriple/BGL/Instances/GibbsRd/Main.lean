import Mathlib
import MarkovTriple.BGL.Instances.GibbsRd.Convex

/-!
# Gibbs measures on `ℝ^d`: the book's weighted `ℝ^n` example (BGL Sect. 1.16, (1.16.5)) as a Markov triple

Summary of the theorems for `G : GibbsRdData d` (`μ = Z⁻¹ e^{-V} dx`, `L = Δ − ∇V·∇`, `𝒜₀ = C_c^∞(ℝ^d)`):

* `G.gibbsRdDiff : DiffusionTriple (Rd d)` (D1–D8), `gibbsRdDiff_isComplete` (Def. 3.3.9) — unconditional;
* `gibbsRd_Γ₂_eq` (Bochner, (1.16.5)) and `gibbsRd_curv : Hess V ≥ ρ → Curv ρ` — unconditional;
* `gibbsRd_integral_Γ₂` (3.3.8), `gibbsRd_integrated_CD` — unconditional (the latter under `Hess V ≥ ρ`);
* under the named hypothesis `WeakHypo` (Def. 3.3.8): ESA (F10), ergodicity (S10), `gibbsRd_poincare`, spectral gap,
  `L²` decay; under `WeakHypo` and `F8`: `gibbsRdFull`, `gibbsRdFull_CD`, `gibbsRdFull_poincare`; LSI and gradient
  bound conditional on `EntropyInterpolation` / `GradientInterpolation` (as in dimension one).
* `GibbsRdData.ofConvex`, `gaussData`: non-vacuity (uniformly convex `V`, standard Gaussian `V = |x|²/2`).
-/

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace MarkovTriple.BGL.Instances.GibbsRd

open MarkovTriple.BGL (pderiv pderiv₂ DiffusionTriple FullTriple)

variable {d : ℕ}

namespace GibbsRdData
variable (G : GibbsRdData d)

/-- **Hessian curvature ⇒ `CD(ρ,∞)` pointwise** (BGL (1.16.5), (1.16.8) with `Ric = 0`): `Hess V ≥ ρ` implies
`ρ Γ(f) ≤ Γ₂(f)` for every `C^∞` `f`, everywhere. -/
theorem gibbsRd_curv {ρ : ℝ} (hρ : HessGe G.V ρ) : G.toEll.Curv ρ := by
  intro f hf x
  have hΓ : G.toEll.diff.ΓA f f x = ∑ i, pderiv f i x * pderiv f i x := by
    rw [G.toEll.ΓA_eq hf hf, G.toEll_Γ]; rfl
  have hB := G.gibbsRd_Γ₂_eq hf x
  have hsq : ∑ i, pderiv f i x * pderiv f i x = ∑ i, pderiv f i x ^ 2 :=
    Finset.sum_congr rfl fun i _ => by ring
  have h1 := hρ x (fun i => pderiv f i x)
  have h2 : 0 ≤ ∑ i, ∑ j, pderiv (pderiv f i) j x ^ 2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  have : G.toEll.diff.Γ₂ f f x = G.gibbsRdDiff.Γ₂ f f x := rfl
  rw [this, hB, hΓ, hsq]
  linarith

/-- `μ`-integrated `Γ₂` identity (3.3.8): `∫ Γ₂(f) dμ = ∫ (L f)² dμ` for `f ∈ C_c^∞(ℝ^d)`. -/
theorem gibbsRd_integral_Γ₂ {f : Rd d → ℝ} (hf : f ∈ A₀ d) :
    ∫ x, G.gibbsRdDiff.Γ₂ f f x ∂G.toEll.μ = ∫ x, Lr G.V f x * Lr G.V f x ∂G.toEll.μ := by
  have := G.toEll.integral_Γ₂ hf
  rw [show G.gibbsRdDiff.Γ₂ f f = G.toEll.diff.Γ₂ f f from rfl, this]
  simp only [G.toEll_L hf.1]

/-- integrated curvature on test functions: `ρ ∫ |∇f|² dμ ≤ ∫ (L f)² dμ`. -/
theorem gibbsRd_integrated_CD {ρ : ℝ} (hρ : HessGe G.V ρ) {f : Rd d → ℝ} (hf : f ∈ A₀ d) :
    ρ * ∫ x, Gr f f x ∂G.toEll.μ ≤ ∫ x, Lr G.V f x * Lr G.V f x ∂G.toEll.μ := by
  have := G.toEll.integrated_CD (G.gibbsRd_curv hρ) hf
  simp only [G.toEll_Γ, G.toEll_L hf.1] at this
  exact this

/-- **Weak hypo-ellipticity** (Def. 3.3.8) of the Gibbs triple on `ℝ^d`: a named hypothesis. -/
abbrev WeakHypo : Prop := G.toEll.WeakHypo

/-- **F8** (Def. 3.3.1 (viii)): a named hypothesis. -/
abbrev F8 : Prop := G.toEll.F8

/-- **ESA (F10)** under `WeakHypo` (BGL Prop. 3.3.11). -/
theorem gibbsRdDiff_esaProp (hH : G.WeakHypo) : G.gibbsRdDiff.ESAProp := G.toEll.diff_esaProp hH

/-- **Poincaré** for the Gibbs measure `e^{-V}dx` on `ℝ^d`, `Hess V ≥ ρ > 0`: `Var_μ(f) ≤ ρ⁻¹ ∫ |∇f|² dμ` for
`f ∈ C_c^∞(ℝ^d)`; hypotheses: `WeakHypo` only (no F8, no gradient bound). -/
theorem gibbsRd_poincare {ρ : ℝ} (hρpos : 0 < ρ) (hρ : HessGe G.V ρ) (hH : G.WeakHypo) :
    G.gibbsRdDiff.PI (1 / ρ) := G.toEll.ell_poincare hρpos (G.gibbsRd_curv hρ) hH

/-- spectral gap `ρ`. -/
theorem gibbsRd_spectralGap {ρ : ℝ} (hρpos : 0 < ρ) (hρ : HessGe G.V ρ) (hH : G.WeakHypo) :
    (DiffusionTriple.formData G.gibbsRdDiff).HasSpectralGap ρ :=
  G.toEll.ell_spectralGap hρpos (G.gibbsRd_curv hρ) hH

/-- `L²` exponential decay. -/
theorem gibbsRd_expDecay {ρ : ℝ} (hρpos : 0 < ρ) (hρ : HessGe G.V ρ) (hH : G.WeakHypo) :
    (DiffusionTriple.formData G.gibbsRdDiff).HasExpDecay ρ :=
  G.toEll.ell_expDecay hρpos (G.gibbsRd_curv hρ) hH

/-- **The Gibbs Full Markov Triple on `ℝ^d`** (BGL Def. 3.3.25), under `WeakHypo` and `F8`. -/
noncomputable def gibbsRdFull (hH : G.WeakHypo) (h8 : G.F8) : FullTriple (Rd d) := G.toEll.full hH h8

/-- **`CD(ρ,∞)`** (Def. 3.3.14) for the Full triple, from `Hess V ≥ ρ`. -/
theorem gibbsRdFull_CD (hH : G.WeakHypo) (h8 : G.F8) {ρ : ℝ} (hρ : HessGe G.V ρ) :
    (G.gibbsRdFull hH h8).CD ρ ∞ := G.toEll.full_CD hH h8 (G.gibbsRd_curv hρ)

/-- Poincaré through the Full triple. -/
theorem gibbsRdFull_poincare (hH : G.WeakHypo) (h8 : G.F8) {ρ : ℝ} (hρpos : 0 < ρ)
    (hρ : HessGe G.V ρ) : (G.gibbsRdFull hH h8).toDiffusionTriple.PI (1 / ρ) :=
  G.toEll.full_poincare hH h8 hρpos (G.gibbsRd_curv hρ)

/-- Log-Sobolev, conditional on `EntropyInterpolation` (as for the 1-D Gibbs triple). -/
theorem gibbsRdFull_logSobolev (hH : G.WeakHypo) (h8 : G.F8) {ρ : ℝ} (hρpos : 0 < ρ)
    (hρ : HessGe G.V ρ) (hE : (G.gibbsRdFull hH h8).EntropyInterpolation) :
    (G.gibbsRdFull hH h8).toDiffusionTriple.LS (1 / ρ) 0 :=
  G.toEll.full_logSobolev hH h8 hρpos (G.gibbsRd_curv hρ) hE

/-- Gradient bound, conditional on `GradientInterpolation`. -/
theorem gibbsRdFull_gradient_bound (hH : G.WeakHypo) (h8 : G.F8) {ρ : ℝ} (hρ : HessGe G.V ρ)
    (hG : (G.gibbsRdFull hH h8).GradientInterpolation) (f : (G.gibbsRdFull hH h8).A₀) (t : ℝ≥0) :
    (G.gibbsRdFull hH h8).toDiffusionTriple.ΓA ((G.gibbsRdFull hH h8).Pt t f)
        ((G.gibbsRdFull hH h8).Pt t f) ≤ᵐ[G.toEll.μ] fun x =>
      Real.exp (-2 * ρ * t) * ((G.gibbsRdFull hH h8).toDiffusionTriple.semigroup t
        ((G.gibbsRdFull hH h8).toDiffusionTriple.cls
          ⟨(G.gibbsRdFull hH h8).toDiffusionTriple.ΓA f.1 f.1,
            (G.gibbsRdFull hH h8).ΓA_self_mem_A₀ f.2⟩) : Lp ℝ 2 G.toEll.μ) x :=
  G.toEll.full_gradient_bound hH h8 (G.gibbsRd_curv hρ) hG f t

end GibbsRdData

/-- Gibbs data from a uniformly convex smooth potential (`Hess V ≥ ρ > 0`). -/
noncomputable def GibbsRdData.ofConvex {V : Rd d → ℝ} (hV : Sm V) {ρ : ℝ} (hρpos : 0 < ρ)
    (hρ : HessGe V ρ) : GibbsRdData d :=
  ⟨V, hV, integrable_of_convex_rd hV hρpos hρ⟩

/-- the Hessian of `V(x) = |x|²/2` is the identity: `∂ⱼ∂ᵢ V = δᵢⱼ`. -/
lemma hess_gauss (i j : Fin d) (x : Rd d) :
    pderiv (pderiv (fun y : Rd d => qd y / 2) i) j x = if j = i then 1 else 0 := by
  have h1 : pderiv (fun y : Rd d => qd y / 2) i = fun y => y i := by
    funext y
    have := pderiv_qd i y
    unfold pderiv at this ⊢
    have hd : HasFDerivAt (qd : Rd d → ℝ) (fderiv ℝ qd y) y := (sm_qd.differentiableAt y).hasFDerivAt
    rw [show (fun y : Rd d => qd y / 2) = fun y => (2 : ℝ)⁻¹ * qd y from by
      funext z; simp [div_eq_inv_mul], (hd.const_mul (2 : ℝ)⁻¹).fderiv]
    simp [this]
  rw [h1]
  exact pderiv_coord i j x

/-- the standard Gaussian potential `V(x) = |x|²/2` on `ℝ^d`: `Hess V = I`. -/
lemma hessGe_gauss : HessGe (fun x : Rd d => qd x / 2) 1 := by
  intro x v
  simp only [hess_gauss]
  have : ∑ i, ∑ j, (if j = i then (1 : ℝ) else 0) * v i * v j = ∑ i, v i ^ 2 := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [sq]
  rw [this]; simp

/-- the standard Gaussian Gibbs data on `ℝ^d` (informally `Z = (2π)^{d/2}`, `μ = N(0,I_d)`; not proved here), with `Hess V = I`. -/
noncomputable def gaussData (d : ℕ) : GibbsRdData d :=
  GibbsRdData.ofConvex (V := fun x : Rd d => qd x / 2) (sm_qd.div_const 2) one_pos hessGe_gauss

/-- the standard Gaussian on `ℝ^d` satisfies the pointwise `CD(1,∞)`: `Γ₂(f) ≥ Γ(f)` for all `C^∞` `f`. -/
theorem gaussData_curv (d : ℕ) : (gaussData d).toEll.Curv 1 :=
  (gaussData d).gibbsRd_curv hessGe_gauss

end MarkovTriple.BGL.Instances.GibbsRd
