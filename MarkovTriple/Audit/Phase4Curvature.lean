import Mathlib
import MarkovTriple.Frozen.Gamma2

/-! # Phase-4 audit (1b): machine-checked *pointwise* curvature of two nondegenerate candidates
(`Γ ≠ 0`, `ρ > 0`); NOT full Markov triples (no esa / semigroup_stable here).

* OU on `ℝ`: `L f = f'' − x f'`, `Γ(f,g) = f' g'`.  `Γ₂(f) = f''² + f'²`, i.e. `CD(1,∞)` on every
  smooth `f` (in particular on `C_c^∞` and on `C^∞`), with equality `Γ₂ = Γ + f''²`.
* Legendre (zonal `S²` / Jacobi) on `[-1,1]`: `L f = (1−x²) f'' − 2x f'`, `Γ(f,g) = (1−x²) f' g'`.
  `Γ₂(f) = Γ(f) + ((1−x²)f'' − x f')² + x² f'²`, whence `CD(1,2)` pointwise:
  `Γ₂ ≥ Γ + (Lf)²/2` (Lichnerowicz constant ρn/(n−1) = 2 = λ₁(S²), sharp). -/

open scoped ENNReal

namespace MarkovTriple.Audit

section Calc
variable {f : ℝ → ℝ}

lemma sm_deriv (hf : ContDiff ℝ (⊤ : ℕ∞) f) : ContDiff ℝ (⊤ : ℕ∞) (deriv f) :=
  (contDiff_infty_iff_deriv.1 hf).2

lemma sm_diff (hf : ContDiff ℝ (⊤ : ℕ∞) f) : Differentiable ℝ f :=
  (contDiff_infty_iff_deriv.1 hf).1

/-- derivative of `x ↦ p(x) * (deriv f x)^2` style products are handled by `HasDerivAt`. -/
lemma hasDerivAt_d (hf : ContDiff ℝ (⊤ : ℕ∞) f) (x : ℝ) : HasDerivAt f (deriv f x) x :=
  (sm_diff hf x).hasDerivAt
lemma hasDerivAt_dd (hf : ContDiff ℝ (⊤ : ℕ∞) f) (x : ℝ) :
    HasDerivAt (deriv f) (deriv (deriv f) x) x := hasDerivAt_d (sm_deriv hf) x
lemma hasDerivAt_ddd (hf : ContDiff ℝ (⊤ : ℕ∞) f) (x : ℝ) :
    HasDerivAt (deriv (deriv f)) (deriv (deriv (deriv f)) x) x := hasDerivAt_d (sm_deriv (sm_deriv hf)) x
end Calc

/-! ### OU -/
noncomputable def ouL (f : ℝ → ℝ) : ℝ → ℝ := fun x => deriv (deriv f) x - x * deriv f x
noncomputable def ouΓ (f g : ℝ → ℝ) : ℝ → ℝ := fun x => deriv f x * deriv g x
noncomputable def ouΓ₂ (f : ℝ → ℝ) : ℝ → ℝ := fun x => (ouL (ouΓ f f) x - 2 * ouΓ f (ouL f) x) / 2

theorem ou_Gamma2 {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (x : ℝ) :
    ouΓ₂ f x = deriv (deriv f) x ^ 2 + ouΓ f f x := by
  have hF : ∀ y, HasDerivAt (ouΓ f f)
      (deriv (deriv f) y * deriv f y + deriv f y * deriv (deriv f) y) y := fun y =>
    (hasDerivAt_dd hf y).mul (hasDerivAt_dd hf y)
  have h1 : deriv (ouΓ f f) = fun y =>
      deriv (deriv f) y * deriv f y + deriv f y * deriv (deriv f) y :=
    funext fun y => (hF y).deriv
  have hF2 : HasDerivAt (deriv (ouΓ f f))
      (deriv (deriv (deriv f)) x * deriv f x + deriv (deriv f) x * deriv (deriv f) x +
        (deriv (deriv f) x * deriv (deriv f) x + deriv f x * deriv (deriv (deriv f)) x)) x := by
    rw [h1]
    exact ((hasDerivAt_ddd hf x).mul (hasDerivAt_dd hf x)).add
      ((hasDerivAt_dd hf x).mul (hasDerivAt_ddd hf x))
  have hL : HasDerivAt (ouL f)
      (deriv (deriv (deriv f)) x - (deriv f x + x * deriv (deriv f) x)) x := by
    unfold ouL
    exact (hasDerivAt_ddd hf x).sub ((hasDerivAt_id x).mul (hasDerivAt_dd hf x) |>.congr_deriv (by simp))
  have e1 : ouL (ouΓ f f) x = deriv (deriv (ouΓ f f)) x - x * deriv (ouΓ f f) x := rfl
  have e2 : ouΓ f (ouL f) x = deriv f x * deriv (ouL f) x := rfl
  unfold ouΓ₂
  rw [e1, e2, hF2.deriv, hL.deriv, h1]
  unfold ouΓ
  ring

/-- `CD(1,∞)` for OU, pointwise on every smooth `f`. -/
theorem ou_CD_infty {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (x : ℝ) :
    1 * ouΓ f f x + ((∞ : ENNReal)⁻¹).toReal * (ouL f x) ^ 2 ≤ ouΓ₂ f x := by
  rw [ou_Gamma2 hf]; simp; nlinarith [sq_nonneg (deriv (deriv f) x)]

/-! ### Legendre -/
noncomputable def lgL (f : ℝ → ℝ) : ℝ → ℝ := fun x => (1 - x ^ 2) * deriv (deriv f) x - 2 * x * deriv f x
noncomputable def lgΓ (f g : ℝ → ℝ) : ℝ → ℝ := fun x => (1 - x ^ 2) * (deriv f x * deriv g x)
noncomputable def lgΓ₂ (f : ℝ → ℝ) : ℝ → ℝ := fun x => (lgL (lgΓ f f) x - 2 * lgΓ f (lgL f) x) / 2

theorem lg_Gamma2 {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (x : ℝ) :
    lgΓ₂ f x = lgΓ f f x + ((1 - x ^ 2) * deriv (deriv f) x - x * deriv f x) ^ 2
      + x ^ 2 * deriv f x ^ 2 := by
  have hq : ∀ y, HasDerivAt (fun y : ℝ => 1 - y ^ 2) (-(2 * y)) y := fun y => by
    simpa using ((hasDerivAt_id y).pow 2).const_sub 1
  have hF : ∀ y, HasDerivAt (lgΓ f f)
      (-(2 * y) * (deriv f y * deriv f y) + (1 - y ^ 2) *
        (deriv (deriv f) y * deriv f y + deriv f y * deriv (deriv f) y)) y := fun y =>
    (hq y).mul ((hasDerivAt_dd hf y).mul (hasDerivAt_dd hf y))
  have h1 : deriv (lgΓ f f) = fun y => -(2 * y) * (deriv f y * deriv f y) + (1 - y ^ 2) *
        (deriv (deriv f) y * deriv f y + deriv f y * deriv (deriv f) y) :=
    funext fun y => (hF y).deriv
  have hF2 : HasDerivAt (deriv (lgΓ f f))
      (-(2:ℝ) * (deriv f x * deriv f x) - 2 * x * (deriv (deriv f) x * deriv f x + deriv f x * deriv (deriv f) x)
        - 2 * x * (deriv (deriv f) x * deriv f x + deriv f x * deriv (deriv f) x)
        + (1 - x ^ 2) * ((deriv (deriv (deriv f)) x * deriv f x + deriv (deriv f) x * deriv (deriv f) x)
          + (deriv (deriv f) x * deriv (deriv f) x + deriv f x * deriv (deriv (deriv f)) x))) x := by
    have h := (((hasDerivAt_id' x).const_mul 2).neg.mul ((hasDerivAt_dd hf x).mul (hasDerivAt_dd hf x))).add
      ((hq x).mul (((hasDerivAt_ddd hf x).mul (hasDerivAt_dd hf x)).add
        ((hasDerivAt_dd hf x).mul (hasDerivAt_ddd hf x))))
    rw [h1]
    convert h using 1
    simp only [Pi.mul_apply, Pi.add_apply, Pi.neg_apply]
    ring
  have hL : HasDerivAt (lgL f)
      (-(2 * x) * deriv (deriv f) x + (1 - x ^ 2) * deriv (deriv (deriv f)) x
        - (2 * deriv f x + 2 * x * deriv (deriv f) x)) x := by
    have h := ((hq x).mul (hasDerivAt_ddd hf x)).sub
      (((hasDerivAt_id' x).const_mul 2).mul (hasDerivAt_dd hf x))
    convert h using 1
    · funext y; simp [lgL]
    · simp
  have e1 : lgL (lgΓ f f) x = (1 - x ^ 2) * deriv (deriv (lgΓ f f)) x - 2 * x * deriv (lgΓ f f) x := rfl
  have e2 : lgΓ f (lgL f) x = (1 - x ^ 2) * (deriv f x * deriv (lgL f) x) := rfl
  unfold lgΓ₂
  rw [e1, e2, hF2.deriv, hL.deriv, h1]
  unfold lgΓ
  ring

/-- `CD(1,2)` for the Legendre operator (zonal `S²`, `ρ = 1`, `n = 2`), pointwise (for all `x`: the
identity `lg_Gamma2` is algebraic; for `|x| > 1` the weight is negative, which matters for
`Γ_nonneg`, see AUDIT_PHASE4.md I-3). -/
theorem lg_CD_two {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (x : ℝ) :
    1 * lgΓ f f x + (((2 : ℝ≥0∞))⁻¹).toReal * (lgL f x) ^ 2 ≤ lgΓ₂ f x := by
  rw [lg_Gamma2 hf]
  have h2 : (((2 : ℝ≥0∞))⁻¹).toReal = 1 / 2 := by
    rw [ENNReal.toReal_inv]; norm_num
  rw [h2]
  unfold lgL
  nlinarith [sq_nonneg ((1 - x ^ 2) * deriv (deriv f) x - x * deriv f x + x * deriv f x)]

end MarkovTriple.Audit
#print axioms MarkovTriple.Audit.ou_CD_infty
#print axioms MarkovTriple.Audit.lg_CD_two
