import Mathlib
import MarkovTriple.BGL.Basic
import MarkovTriple.BGL.Frozen.GammaA

/-!
# Consistency of the formula-defined carré du champ with `Γ` on `𝒜₀` (not frozen)

BGL (3.1.6) and its polarisation: for `f, g ∈ 𝒜₀`, `L(fg) = f Lg + g Lf + 2Γ(f,g)` a.e. (a
consequence of D3, D5, D6).  Hence `ΓA = Γ` a.e. on `𝒜₀`, so that the extension of `Γ` to `𝒜` by the
formula (F4) is an honest extension.
-/

open MeasureTheory

namespace MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E] (T : DiffusionTriple E)

namespace DiffusionTriple

lemma pderiv_mul_zero (z : Fin 2 → ℝ) :
    pderiv (fun z : Fin 2 → ℝ => z 0 * z 1) 0 z = z 1 := by
  have hd : HasFDerivAt (fun z : Fin 2 → ℝ => z 0 * z 1)
      (z 0 • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1 +
        z 1 • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0) z :=
    (hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 2) z).mul (hasFDerivAt_apply (1 : Fin 2) z)
  unfold pderiv
  rw [hd.fderiv]
  simp

lemma pderiv_mul_one (z : Fin 2 → ℝ) :
    pderiv (fun z : Fin 2 → ℝ => z 0 * z 1) 1 z = z 0 := by
  have hd : HasFDerivAt (fun z : Fin 2 → ℝ => z 0 * z 1)
      (z 0 • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1 +
        z 1 • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0) z :=
    (hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 2) z).mul (hasFDerivAt_apply (1 : Fin 2) z)
  unfold pderiv
  rw [hd.fderiv]
  simp

/-- Leibniz rule for `Γ` (case `ψ(x,y) = xy` of the diffusion property). -/
theorem Γ_mul_left {f g h : E → ℝ} (hf : f ∈ T.A₀) (hg : g ∈ T.A₀) (hh : h ∈ T.A₀) :
    T.Γ (f * g) h =ᵐ[T.μ] f * T.Γ g h + g * T.Γ f h := by
  have hψ : ContDiff ℝ (⊤ : ℕ∞) (fun z : Fin 2 → ℝ => z 0 * z 1) :=
    (contDiff_apply ℝ ℝ 0).mul (contDiff_apply ℝ ℝ 1)
  have key := T.diffusion 2 (fun z : Fin 2 → ℝ => z 0 * z 1) hψ (by simp) ![f, g]
    (by intro i; fin_cases i <;> simpa) h hh
  have e : (fun x => (fun z : Fin 2 → ℝ => z 0 * z 1) (fun i => (![f, g] : Fin 2 → E → ℝ) i x)) =
      f * g := by
    funext x; simp
  rw [e] at key
  filter_upwards [key] with x hx
  rw [hx]
  simp [Fin.sum_univ_two, pderiv_mul_zero, pderiv_mul_one]
  ring

/-- **BGL (3.1.6), polarised**: `L(fg) = f Lg + g Lf + 2 Γ(f,g)` a.e. on `𝒜₀`. -/
theorem L_mul_ae {f g : E → ℝ} (hf : f ∈ T.A₀) (hg : g ∈ T.A₀) :
    T.L (f * g) =ᵐ[T.μ] f * T.L g + g * T.L f + (2 : ℝ) • T.Γ f g := by
  have hfg : f * g ∈ T.A₀ := T.A₀.mul_mem hf hg
  have hd : T.L (f * g) - f * T.L g - g * T.L f - (2 : ℝ) • T.Γ f g ∈ T.A₀ :=
    T.A₀.sub_mem (T.A₀.sub_mem (T.A₀.sub_mem (T.L_mem _ hfg) (T.A₀.mul_mem hf (T.L_mem _ hg)))
      (T.A₀.mul_mem hg (T.L_mem _ hf))) (T.A₀.smul_mem _ (T.Γ_mem _ hf _ hg))
  have hI : ∀ a ∈ T.A₀, ∀ b ∈ T.A₀, Integrable (T.Γ a b) T.μ :=
    fun a ha b hb => integrable_of_mem T (T.Γ_mem a ha b hb)
  have key := ae_zero_of_orth T hd (fun h hh => by
    have hhf : h * f ∈ T.A₀ := T.A₀.mul_mem hh hf
    have hhg : h * g ∈ T.A₀ := T.A₀.mul_mem hh hg
    have i1 := integrable_of_mem T (T.A₀.mul_mem hh (T.L_mem _ hfg))
    have i2 := integrable_of_mem T (T.A₀.mul_mem hhf (T.L_mem _ hg))
    have i3 := integrable_of_mem T (T.A₀.mul_mem hhg (T.L_mem _ hf))
    have i4 := integrable_of_mem T (T.A₀.mul_mem hh (T.Γ_mem _ hf _ hg))
    have e1 : (fun x => h x * (T.L (f * g) - f * T.L g - g * T.L f - (2 : ℝ) • T.Γ f g) x) =
        fun x => h x * T.L (f * g) x - (h * f) x * T.L g x - (h * g) x * T.L f x -
          2 * (h x * T.Γ f g x) := by
      funext x; simp only [Pi.sub_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]; ring
    have s1 : ∫ x, (h x * T.L (f * g) x - (h * f) x * T.L g x - (h * g) x * T.L f x -
          2 * (h x * T.Γ f g x)) ∂T.μ =
        ∫ x, h x * T.L (f * g) x ∂T.μ - ∫ x, (h * f) x * T.L g x ∂T.μ -
          ∫ x, (h * g) x * T.L f x ∂T.μ - 2 * ∫ x, h x * T.Γ f g x ∂T.μ := by
      rw [integral_sub (f := fun x => h x * T.L (f * g) x - (h * f) x * T.L g x -
          (h * g) x * T.L f x) (g := fun x => 2 * (h x * T.Γ f g x))
          ((i1.sub i2).sub i3) (i4.const_mul 2),
        integral_sub (f := fun x => h x * T.L (f * g) x - (h * f) x * T.L g x)
          (g := fun x => (h * g) x * T.L f x) (i1.sub i2) i3,
        integral_sub (f := fun x => h x * T.L (f * g) x) (g := fun x => (h * f) x * T.L g x) i1 i2,
        integral_const_mul]
    rw [e1, s1, T.ibp _ hfg _ hh, T.ibp _ hg _ hhf, T.ibp _ hf _ hhg]
    have j1 := hI _ hfg _ hh
    have j2 := hI _ hg _ hhf
    have j3 := hI _ hf _ hhg
    have j4 := integrable_of_mem T (T.A₀.mul_mem hh (T.Γ_mem _ hf _ hg))
    have hz : ∫ x, (-T.Γ (f * g) h x + T.Γ g (h * f) x + T.Γ f (h * g) x -
        2 * (h x * T.Γ f g x)) ∂T.μ = 0 := by
      have hae : (fun x => -T.Γ (f * g) h x + T.Γ g (h * f) x + T.Γ f (h * g) x -
          2 * (h x * T.Γ f g x)) =ᵐ[T.μ] 0 := by
        filter_upwards [Γ_mul_left T hf hg hh, T.Γ_symm g hg (h * f) hhf,
          Γ_mul_left T hh hf hg, T.Γ_symm f hf (h * g) hhg, Γ_mul_left T hh hg hf,
          T.Γ_symm g hg h hh, T.Γ_symm f hf h hh, T.Γ_symm g hg f hf] with x a1 a2 a3 a4 a5 a6 a7 a8
        simp only [Pi.add_apply, Pi.mul_apply] at a1 a3 a5
        simp only [Pi.zero_apply]
        rw [a1, a2, a3, a4, a5, a6, a7, a8]; ring
      rw [integral_congr_ae hae]; simp
    have t1 := integral_add (f := fun x => -T.Γ (f * g) h x) (g := fun x => T.Γ g (h * f) x)
      j1.neg j2
    have t2 := integral_add (f := fun x => -T.Γ (f * g) h x + T.Γ g (h * f) x)
      (g := fun x => T.Γ f (h * g) x) (j1.neg.add j2) j3
    have t3 := integral_sub
      (f := fun x => -T.Γ (f * g) h x + T.Γ g (h * f) x + T.Γ f (h * g) x)
      (g := fun x => 2 * (h x * T.Γ f g x)) ((j1.neg.add j2).add j3) (j4.const_mul 2)
    have t4 : ∫ x, -T.Γ (f * g) h x ∂T.μ = -∫ x, T.Γ (f * g) h x ∂T.μ := integral_neg _
    have t5 := integral_const_mul (μ := T.μ) 2 (fun x => h x * T.Γ f g x)
    beta_reduce at t1 t2 t3 t5
    linarith [hz, t1, t2, t3, t4, t5])
  filter_upwards [key] with x hx
  simp only [Pi.sub_apply, Pi.zero_apply, Pi.add_apply, Pi.mul_apply, Pi.smul_apply,
    smul_eq_mul] at hx ⊢
  linarith

/-- The formula-defined carré du champ `ΓA` agrees with `Γ` a.e. on `𝒜₀`. -/
theorem ΓA_ae_eq {f g : E → ℝ} (hf : f ∈ T.A₀) (hg : g ∈ T.A₀) : T.ΓA f g =ᵐ[T.μ] T.Γ f g := by
  filter_upwards [L_mul_ae T hf hg] with x hx
  simp only [Pi.add_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul] at hx
  simp only [ΓA]
  rw [hx]; ring

end DiffusionTriple

end MarkovTriple.BGL
