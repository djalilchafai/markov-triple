import Mathlib
import MarkovTriple.BGL.Frozen.FullTriple
import MarkovTriple.BGL.Theory.GammaCalculus

/-!
# The part of the extended-algebra axioms F1–F8 used by the mass-conservation theorem

BGL Thm 3.3.23 is stated for a *Diffusion Markov Triple* with extended algebra `𝒜` and does not assume
S11 (conservativeness) nor S10: in the frozen surface, `FullTriple` extends `StandardTriple`, so S11 is
one of its fields and the theorem would be vacuous there.  We therefore isolate, as a `Prop`-valued
structure over a bare `DiffusionTriple D` and a subalgebra `𝒜`, exactly the extended-algebra axioms the
proof uses (F5, F6 for `Γ`, the second equality of F7, F8, `𝒜₀ ⊂ 𝒜`).  Every `FullTriple` provides one
(`FullTriple.extendedAlgebra`).

Also: the Cauchy–Schwarz inequality for `ΓA` on `𝒜` (from F5, F6) and the elementary bound
`|Γ(f, η²)| ≤ √B (η² + Γ(η))` when `Γ(f) ≤ B`.
-/

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

namespace MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E]

/-- The extended-algebra axioms used by Thm 3.3.23 (a sub-list of F1–F8, over a bare diffusion triple). -/
structure ExtendedAlgebra (D : DiffusionTriple E) (A : Subalgebra ℝ (E → ℝ)) : Prop where
  /-- `𝒜₀ ⊂ 𝒜`. -/
  A₀_le : ∀ f ∈ D.A₀, f ∈ A
  /-- F5. -/
  ΓA_nonneg : ∀ f ∈ A, 0 ≤ᵐ[D.μ] D.ΓA f f
  /-- F6, change of variables formula for `Γ` on `𝒜`. -/
  diffusion_Γ_A : ∀ (k : ℕ) (ψ : (Fin k → ℝ) → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ →
    ∀ f : Fin k → (E → ℝ), (∀ i, f i ∈ A) → ∀ g ∈ A,
      D.ΓA (fun x => ψ (fun i => f i x)) g =ᵐ[D.μ]
        fun x => ∑ i, pderiv ψ i (fun j => f j x) * D.ΓA (f i) g x
  /-- F7 (second equality). -/
  ibp_A : ∀ f ∈ A, ∀ g ∈ D.A₀, ∫ x, D.ΓA f g x ∂D.μ = -∫ x, f x * D.L g x ∂D.μ
  /-- F8. -/
  semigroup_A : ∀ (t : ℝ≥0) (f : D.A₀), ∃ g ∈ A,
    (D.semigroup t (D.cls f) : E → ℝ) =ᵐ[D.μ] g

/-- Every full triple has the extended-algebra axioms used by Thm 3.3.23. -/
theorem FullTriple.extendedAlgebra (T : FullTriple E) :
    ExtendedAlgebra T.toDiffusionTriple T.A :=
  ⟨T.A₀_le, T.ΓA_nonneg, T.diffusion_Γ_A, fun f hf g hg => (T.ibp_A f hf g hg).2, T.semigroup_A⟩

namespace ExtendedAlgebra

variable {D : DiffusionTriple E} {A : Subalgebra ℝ (E → ℝ)} (h : ExtendedAlgebra D A)
include h

omit [MeasurableSpace E] h in
lemma pderiv_lin_zero (s : ℝ) (z : Fin 2 → ℝ) :
    pderiv (fun z : Fin 2 → ℝ => z 0 + s * z 1) 0 z = 1 := by
  have hd : HasFDerivAt (fun z : Fin 2 → ℝ => z 0 + s * z 1)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0 +
        s • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1) z :=
    (hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 2) z).add
      ((hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 2) z).const_mul s)
  unfold pderiv
  rw [hd.fderiv]
  simp

omit [MeasurableSpace E] h in
lemma pderiv_lin_one (s : ℝ) (z : Fin 2 → ℝ) :
    pderiv (fun z : Fin 2 → ℝ => z 0 + s * z 1) 1 z = s := by
  have hd : HasFDerivAt (fun z : Fin 2 → ℝ => z 0 + s * z 1)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0 +
        s • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1) z :=
    (hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 2) z).add
      ((hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 2) z).const_mul s)
  unfold pderiv
  rw [hd.fderiv]
  simp

/-- Linearity of `ΓA` in the first variable on `𝒜` (F6 with a linear `ψ`). -/
theorem ΓA_lin_left {f g : E → ℝ} (hf : f ∈ A) (hg : g ∈ A) (s : ℝ) {k : E → ℝ} (hk : k ∈ A) :
    D.ΓA (fun x => f x + s * g x) k =ᵐ[D.μ] fun x => D.ΓA f k x + s * D.ΓA g k x := by
  have hψ : ContDiff ℝ (⊤ : ℕ∞) (fun z : Fin 2 → ℝ => z 0 + s * z 1) :=
    (contDiff_apply ℝ ℝ 0).add (contDiff_const.mul (contDiff_apply ℝ ℝ 1))
  have key := h.diffusion_Γ_A 2 (fun z : Fin 2 → ℝ => z 0 + s * z 1) hψ ![f, g]
    (by intro i; fin_cases i <;> simpa) k hk
  have e : (fun x => (fun z : Fin 2 → ℝ => z 0 + s * z 1) (fun i => (![f, g] : Fin 2 → E → ℝ) i x))
      = fun x => f x + s * g x := by
    funext x; simp
  rw [e] at key
  filter_upwards [key] with x hx
  rw [hx]
  simp [Fin.sum_univ_two, pderiv_lin_zero, pderiv_lin_one]

/-- **Cauchy–Schwarz for `ΓA` on `𝒜`**: `Γ(f,g)² ≤ Γ(f) Γ(g)` a.e. -/
theorem ΓA_cs {f g : E → ℝ} (hf : f ∈ A) (hg : g ∈ A) :
    ∀ᵐ x ∂D.μ, D.ΓA f g x ^ 2 ≤ D.ΓA f f x * D.ΓA g g x := by
  have key : ∀ s : ℝ, ∀ᵐ x ∂D.μ,
      0 ≤ D.ΓA f f x + 2 * s * D.ΓA f g x + s ^ 2 * D.ΓA g g x := by
    intro s
    have hs : (fun x => f x + s * g x) ∈ A := by
      have : (fun x => f x + s * g x) = f + s • g := by funext x; simp
      rw [this]; exact A.add_mem hf (A.smul_mem hg s)
    have e1 := ΓA_lin_left h hf hg s hs
    have e2 := ΓA_lin_left h hf hg s hf
    have e3 := ΓA_lin_left h hf hg s hg
    have hn := h.ΓA_nonneg _ hs
    filter_upwards [e1, e2, e3, hn] with x h1 h2 h3 h4
    have c1 : D.ΓA f (fun x => f x + s * g x) x = D.ΓA (fun x => f x + s * g x) f x :=
      congrFun (DiffusionTriple.ΓA_comm D f _) x
    have c2 : D.ΓA g (fun x => f x + s * g x) x = D.ΓA (fun x => f x + s * g x) g x :=
      congrFun (DiffusionTriple.ΓA_comm D g _) x
    have c3 : D.ΓA g f x = D.ΓA f g x := congrFun (DiffusionTriple.ΓA_comm D g f) x
    have step : D.ΓA (fun x => f x + s * g x) (fun x => f x + s * g x) x =
        D.ΓA f f x + 2 * s * D.ΓA f g x + s ^ 2 * D.ΓA g g x := by
      have e1' : D.ΓA (fun x => f x + s * g x) (fun x => f x + s * g x) x =
          D.ΓA f (fun x => f x + s * g x) x + s * D.ΓA g (fun x => f x + s * g x) x := h1
      rw [e1', c1, c2, h2, h3]
      have h2' : D.ΓA f g x = D.ΓA f g x := rfl
      rw [c3]; ring
    rw [← step]; exact h4
  have keyq := ae_all_iff.2 (fun q : ℚ => key (q : ℝ))
  filter_upwards [keyq] with x hx
  have hall : ∀ s : ℝ, 0 ≤ D.ΓA g g x * (s * s) + (2 * D.ΓA f g x) * s + D.ΓA f f x := by
    intro s
    have : 0 ≤ D.ΓA f f x + 2 * s * D.ΓA f g x + s ^ 2 * D.ΓA g g x := by
      refine Rat.denseRange_cast.induction_on s
        (isClosed_le continuous_const (by fun_prop)) (fun q => hx q)
    nlinarith [this]
  have hd := discrim_le_zero hall
  unfold discrim at hd
  nlinarith [hd]

/-- `Γ(f, η²) = 2 η Γ(η, f)`-type bound: if `Γ(f) ≤ B` (`B ≥ 0`) then
`|Γ(f, η²)| ≤ √B (η² + Γ(η))` a.e. -/
theorem ΓA_sq_bound {f η : E → ℝ} (hf : f ∈ A) (hη : η ∈ A) {B : ℝ} (_hB0 : 0 ≤ B)
    (hB : D.ΓA f f ≤ᵐ[D.μ] fun _ => B) :
    ∀ᵐ x ∂D.μ, |D.ΓA f (fun x => η x ^ 2) x| ≤
      Real.sqrt B * (η x ^ 2 + D.ΓA η η x) := by
  have hψ : ContDiff ℝ (⊤ : ℕ∞) (fun r : ℝ => r ^ 2) := contDiff_id.pow 2
  have hψ' : ContDiff ℝ (⊤ : ℕ∞) (fun z : Fin 1 → ℝ => (fun r : ℝ => r ^ 2) (z 0)) :=
    hψ.comp (contDiff_apply ℝ ℝ 0)
  have key := h.diffusion_Γ_A 1 (fun z : Fin 1 → ℝ => (fun r : ℝ => r ^ 2) (z 0)) hψ' ![η]
    (by intro i; fin_cases i; simpa using hη) f hf
  have hcs := ΓA_cs h hη hf
  have hn := h.ΓA_nonneg η hη
  filter_upwards [key, hcs, hn, hB] with x hx hc hn' hb
  simp only [Fin.sum_univ_one] at hx
  have hx' : D.ΓA (fun x => η x ^ 2) f x =
      (pderiv (fun z : Fin 1 → ℝ => (fun r : ℝ => r ^ 2) (z 0)) 0
        fun j => (![η] : Fin 1 → E → ℝ) j x) * D.ΓA η f x := hx
  have hder : pderiv (fun z : Fin 1 → ℝ => (fun r : ℝ => r ^ 2) (z 0)) 0
      (fun j => (![η] : Fin 1 → E → ℝ) j x) = 2 * η x := by
    rw [pderiv_comp_eval (fun r : ℝ => r ^ 2) (hψ.differentiable (by simp))]
    simp
  have comm : D.ΓA f (fun x => η x ^ 2) x = D.ΓA (fun x => η x ^ 2) f x :=
    congrFun (DiffusionTriple.ΓA_comm D f _) x
  rw [comm, hx', hder]
  have c1 : D.ΓA η f x = D.ΓA f η x := congrFun (DiffusionTriple.ΓA_comm D η f) x
  have hle : |D.ΓA η f x| ≤ Real.sqrt (D.ΓA η η x) * Real.sqrt B := by
    rw [← Real.sqrt_mul hn']
    refine Real.abs_le_sqrt ?_
    exact hc.trans (mul_le_mul_of_nonneg_left hb hn')
  have hsq : Real.sqrt (D.ΓA η η x) ^ 2 = D.ΓA η η x := Real.sq_sqrt hn'
  have hab : 2 * |η x| * Real.sqrt (D.ΓA η η x) ≤ η x ^ 2 + D.ΓA η η x := by
    nlinarith [sq_nonneg (|η x| - Real.sqrt (D.ΓA η η x)), sq_abs (η x)]
  have hsB := Real.sqrt_nonneg B
  calc |2 * η x * D.ΓA η f x| = 2 * |η x| * |D.ΓA η f x| := by
        rw [abs_mul, abs_mul]; simp
    _ ≤ 2 * |η x| * (Real.sqrt (D.ΓA η η x) * Real.sqrt B) :=
        mul_le_mul_of_nonneg_left hle (by positivity)
    _ = Real.sqrt B * (2 * |η x| * Real.sqrt (D.ΓA η η x)) := by ring
    _ ≤ Real.sqrt B * (η x ^ 2 + D.ΓA η η x) := mul_le_mul_of_nonneg_left hab hsB

end ExtendedAlgebra

end MarkovTriple.BGL
