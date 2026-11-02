import Mathlib
import MarkovTriple.BGL.Theory.Strong.Reinforced
import MarkovTriple.BGL.Theory.Strong.Psi
import MarkovTriple.BGL.Theory.GradientBound

/-!
# The semigroup interpolation for the strong gradient bound (BGL Lemmas 3.3.20–3.3.21, Thm 3.3.18)

For `f, h ∈ 𝒜₀`, `h ≥ 0`, `ε > 0`, `t ≥ 0`, put `k_s = P_s h`, `g_s = P_{t-s} f`, `u_s = Γ(g_s)` and
`Φ_ε(s) = ∫ k_s ψ_ε(u_s) dμ` (the function `Φ` of the book's proof, with `ψ_ε(r) = √(r+ε²) − ε`).

`StrongInterpolation T` isolates the *analytic* regularity (continuity, differentiability and the
derivative formula `Φ_ε'(s) = ∫ k_s (L(ψ_ε∘u_s) − 2ψ_ε'(u_s) Γ(g_s, L g_s))`, the latter obtained from
`∂_s u_s = −2Γ(g_s, L g_s)` and `∫ L k_s · ψ_ε(u_s) = ∫ k_s L(ψ_ε∘u_s)`); everything else is proved here:
the pointwise inequality (using the reinforced curvature inequality `reinforced_cd`), the Gronwall step, end
points, positivity detection and the `ε → 0` limit (`Strong/Main.lean`).
-/

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

namespace MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E]

/-- **Key real inequality.**  `u ≥ 0`, `ρ ≥ 0`, `ρ u ≤ a` (CD), `Y ≤ 4 (a − ρu) u` (reinforced CD) ⇒
`ρ ψ_ε(u) ≤ 2ψ_ε'(u) a + ψ_ε''(u) Y`. -/
lemma key_ineq {ε ρ u a Y : ℝ} (hε : 0 < ε) (hρ : 0 ≤ ρ) (hu : 0 ≤ u) (hK : ρ * u ≤ a)
    (hY : Y ≤ 4 * (a - ρ * u) * u) :
    ρ * (Real.sqrt (u + ε ^ 2) - ε) ≤
      2 * (1 / (2 * Real.sqrt (u + ε ^ 2))) * a + (-1 / (4 * Real.sqrt (u + ε ^ 2) ^ 3)) * Y := by
  set S := Real.sqrt (u + ε ^ 2) with hS
  have hpos : 0 < u + ε ^ 2 := by nlinarith [sq_pos_of_pos hε]
  have hSpos : 0 < S := Real.sqrt_pos.2 hpos
  have hS2 : S ^ 2 = u + ε ^ 2 := Real.sq_sqrt hpos.le
  have hSε : ε ≤ S := by
    rw [hS]; apply Real.le_sqrt_of_sq_le; nlinarith
  have ha : 0 ≤ a := le_trans (mul_nonneg hρ hu) hK
  -- step 1:  -Y/(4 S^3) ≥ -(a - ρu) u / S^3
  have h1 : (-1 / (4 * S ^ 3)) * Y ≥ (-1 / (4 * S ^ 3)) * (4 * (a - ρ * u) * u) := by
    apply mul_le_mul_of_nonpos_left hY
    have : 0 < 4 * S ^ 3 := by positivity
    exact (div_nonpos_iff.2 (Or.inr ⟨by norm_num, this.le⟩))
  have h2 : (-1 / (4 * S ^ 3)) * (4 * (a - ρ * u) * u) = -((a - ρ * u) * u) / S ^ 3 := by
    field_simp
  -- step 2
  have h3 : 2 * (1 / (2 * S)) * a - ((a - ρ * u) * u) / S ^ 3 = (a * ε ^ 2 + ρ * u ^ 2) / S ^ 3 := by
    field_simp
    nlinarith [hS2]
  have h4 : ρ * u / S ≤ (a * ε ^ 2 + ρ * u ^ 2) / S ^ 3 := by
    rw [div_le_div_iff₀ hSpos (by positivity)]
    have : S ^ 3 = S * S ^ 2 := by ring
    rw [this, hS2]
    have : ρ * u * (u + ε ^ 2) ≤ a * ε ^ 2 + ρ * u ^ 2 := by nlinarith [mul_nonneg ha (sq_nonneg ε)]
    nlinarith [this, hSpos]
  have h5 : ρ * (S - ε) ≤ ρ * u / S := by
    rw [le_div_iff₀ hSpos]
    have : (S - ε) * S ≤ u := by nlinarith [hS2]
    nlinarith [mul_le_mul_of_nonneg_left this hρ]
  calc ρ * (S - ε) ≤ ρ * u / S := h5
    _ ≤ (a * ε ^ 2 + ρ * u ^ 2) / S ^ 3 := h4
    _ = 2 * (1 / (2 * S)) * a - ((a - ρ * u) * u) / S ^ 3 := h3.symm
    _ = 2 * (1 / (2 * S)) * a + (-1 / (4 * S ^ 3)) * (4 * (a - ρ * u) * u) := by rw [h2]; ring
    _ ≤ _ := by linarith [h1]

namespace FullTriple

variable (T : FullTriple E)

lemma pderiv2_comp_eval (ψ : ℝ → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (z : Fin 1 → ℝ) :
    pderiv₂ (fun z : Fin 1 → ℝ => ψ (z 0)) 0 0 z = deriv (deriv ψ) (z 0) := by
  unfold pderiv₂
  have e : (fun y : Fin 1 → ℝ => pderiv (fun z : Fin 1 → ℝ => ψ (z 0)) 0 y) =
      fun y => deriv ψ (y 0) := by
    funext y; exact pderiv_comp_eval ψ (hψ.differentiable (by simp)) y
  rw [e]
  have h1 : Differentiable ℝ (deriv ψ) :=
    ((contDiff_infty_iff_deriv.1 hψ).2).differentiable (by simp)
  have hd : HasFDerivAt (fun y : Fin 1 → ℝ => deriv ψ (y 0))
      (deriv (deriv ψ) (z 0) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0) z := by
    have h2 : HasDerivAt (deriv ψ) (deriv (deriv ψ) (z 0)) (z 0) := (h1 (z 0)).hasDerivAt
    exact h2.comp_hasFDerivAt z (hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 1) z)
  rw [hd.fderiv]
  simp

/-- `L(ψ∘u) = ψ'(u) L u + ψ''(u) Γ(u)` a.e. for smooth `ψ`, `u ∈ 𝒜`. -/
theorem L_comp {ψ : ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) {u : E → ℝ} (hu : u ∈ T.A) :
    T.L (fun x => ψ (u x)) =ᵐ[T.μ] fun x =>
      deriv ψ (u x) * T.L u x + deriv (deriv ψ) (u x) * T.toDiffusionTriple.ΓA u u x := by
  have hψ' : ContDiff ℝ (⊤ : ℕ∞) (fun z : Fin 1 → ℝ => ψ (z 0)) :=
    hψ.comp (contDiff_apply ℝ ℝ 0)
  have key := T.diffusion_L_A 1 (fun z => ψ (z 0)) hψ' ![u]
    (by intro i; fin_cases i; simpa using hu)
  filter_upwards [key] with x hx
  refine hx.trans ?_
  simp [Fin.sum_univ_one, pderiv_comp_eval ψ (hψ.differentiable (by simp)),
    pderiv2_comp_eval ψ hψ]

/-- the exact identity `L(Γ(g)) = 2Γ₂(g) + 2Γ(g, L g)`. -/
lemma L_G_self (g : E → ℝ) (x : E) :
    T.L (G T g g) x = 2 * T.toDiffusionTriple.Γ₂ g g x + 2 * G T g (T.L g) x := by
  rw [Γ₂_eq, G_comm (T.L g) g]; ring

/-- `s ↦` the integrand of the derivative: `L(ψ_ε ∘ Γ g) − 2 ψ_ε'(Γ g) Γ(g, L g)`. -/
noncomputable def strongD (ε : ℝ) (g : E → ℝ) : E → ℝ := fun x =>
  T.L (fun y => psiS ε (G T g g y)) x - 2 * deriv (psiS ε) (G T g g x) * G T g (T.L g) x

/-- **Pointwise inequality (Lemma 3.3.21)**: `ρ ψ_ε(Γ g) ≤ L(ψ_ε∘Γg) − 2ψ_ε'(Γ g)Γ(g,Lg)` a.e. -/
theorem strongD_ge {ρ : ℝ} {n : ℝ≥0∞} (hCD : T.CD ρ n) (hρ : 0 ≤ ρ) {ε : ℝ} (hε : 0 < ε)
    {g : E → ℝ} (hg : g ∈ T.A) :
    ∀ᵐ x ∂T.μ, ρ * psiS ε (G T g g x) ≤ T.strongD ε g x := by
  have hu : G T g g ∈ T.A := G_mem hg hg
  have a1 := L_comp T (psiS_smooth hε) hu
  have a2 := reinforced_cd hCD hg
  have a3 := hCD.2 g hg
  have a4 := T.ΓA_nonneg g hg
  filter_upwards [a1, a2, a3, a4] with x e1 e2 e3 e4
  have hu0 : 0 ≤ G T g g x := e4
  have hK : ρ * G T g g x ≤ T.toDiffusionTriple.Γ₂ g g x := by
    have : 0 ≤ (n⁻¹).toReal * (T.L g x) ^ 2 := mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _)
    show ρ * T.toDiffusionTriple.ΓA g g x ≤ _
    linarith
  have := key_ineq hε hρ hu0 hK e2
  unfold strongD
  rw [e1, L_G_self T g x, deriv_psiS hε hu0, deriv2_psiS hε hu0, psiS_eq hε (by nlinarith [sq_pos_of_pos hε])]
  nlinarith [this]

end FullTriple

end MarkovTriple.BGL
