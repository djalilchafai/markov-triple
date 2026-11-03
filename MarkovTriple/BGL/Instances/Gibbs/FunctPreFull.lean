import Mathlib
import MarkovTriple.BGL.Frozen.Complete
import MarkovTriple.BGL.Frozen.GammaA
import MarkovTriple.BGL.Theory.Gamma2Integral
import MarkovTriple.BGL.Consistency

/-!
# The semigroup-free part of the Full Markov Triple axioms, and the cut-off argument of BGL Prop. 3.2.1 / 3.3.11

`PreFull D A` bundles the fields of `FullTriple` (BGL Def. 3.3.1 (i)-(vii), Def. 3.3.7) that do not mention
the semigroup: ideal property F1, positivity detection F2, `L : 𝒜 → 𝒜` F4, `Γ ≥ 0` F5, change of variables
F6, integration by parts F7, connexity F9 (BGL Def. 3.3.7).  It is a `Prop` (never an axiom).

The main result, `PreFull.gradient_eq_zero`, is the computation inside the proof of BGL Prop. 3.2.1 (repeated
for the abstract setting in the paragraph after Prop. 3.3.10, "the proof of Proposition 3.2.1 immediately
extends"): for `w ∈ 𝒜 ∩ L²` with `w L w ≥ 0` and a complete triple (Def. 3.3.9), `Γ(w) = 0`.
-/

open MeasureTheory Filter Topology

namespace MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E]

/-- The axioms of the extended algebra (BGL Def. 3.3.1 (i)-(vii)) and connexity (Def. 3.3.7) that do not
involve the semigroup. -/
structure PreFull (D : DiffusionTriple E) (A : Subalgebra ℝ (E → ℝ)) : Prop where
  /-- `𝒜₀ ⊂ 𝒜` -/
  A₀_le : ∀ f ∈ D.A₀, f ∈ A
  /-- elements of `𝒜` are measurable -/
  A_measurable : ∀ f ∈ A, Measurable f
  /-- F1 -/
  ideal : ∀ f ∈ A, ∀ h ∈ D.A₀, h * f ∈ D.A₀
  /-- F2 -/
  pos_detect : ∀ f ∈ A, (∀ h ∈ D.A₀, 0 ≤ᵐ[D.μ] h → 0 ≤ ∫ x, h x * f x ∂D.μ) → 0 ≤ᵐ[D.μ] f
  /-- F4 -/
  L_mem_A : ∀ f ∈ A, D.L f ∈ A
  /-- F5 -/
  ΓA_nonneg : ∀ f ∈ A, 0 ≤ᵐ[D.μ] D.ΓA f f
  /-- F6 -/
  diffusion_Γ_A : ∀ (k : ℕ) (ψ : (Fin k → ℝ) → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ →
    ∀ f : Fin k → (E → ℝ), (∀ i, f i ∈ A) → ∀ g ∈ A,
      D.ΓA (fun x => ψ (fun i => f i x)) g =ᵐ[D.μ]
        fun x => ∑ i, pderiv ψ i (fun j => f j x) * D.ΓA (f i) g x
  /-- F7 -/
  ibp_A : ∀ f ∈ A, ∀ g ∈ D.A₀,
    ∫ x, D.ΓA f g x ∂D.μ = -∫ x, g x * D.L f x ∂D.μ ∧
    ∫ x, D.ΓA f g x ∂D.μ = -∫ x, f x * D.L g x ∂D.μ
  /-- F9 -/
  connected : ∀ f ∈ A, D.ΓA f f =ᵐ[D.μ] 0 → ∃ c : ℝ, f =ᵐ[D.μ] fun _ => c

namespace PreFull

variable {D : DiffusionTriple E} {A : Subalgebra ℝ (E → ℝ)} (h : PreFull D A)
include h

omit h in
lemma pderiv_mul_zero (z : Fin 2 → ℝ) : pderiv (fun z : Fin 2 → ℝ => z 0 * z 1) 0 z = z 1 := by
  have hd : HasFDerivAt (fun z : Fin 2 → ℝ => z 0 * z 1)
      (z 0 • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1 +
        z 1 • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0) z :=
    (hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 2) z).mul (hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 2) z)
  unfold pderiv
  rw [hd.fderiv]
  simp

omit h in
lemma pderiv_mul_one (z : Fin 2 → ℝ) : pderiv (fun z : Fin 2 → ℝ => z 0 * z 1) 1 z = z 0 := by
  have hd : HasFDerivAt (fun z : Fin 2 → ℝ => z 0 * z 1)
      (z 0 • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1 +
        z 1 • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0) z :=
    (hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 2) z).mul (hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 2) z)
  unfold pderiv
  rw [hd.fderiv]
  simp

omit h in
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

omit h in
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

/-- `Γ(f g, k) = f Γ(g,k) + g Γ(f,k)` on `𝒜` (F6 with `ψ(a,b) = ab`). -/
theorem ΓA_mul_left {f g k : E → ℝ} (hf : f ∈ A) (hg : g ∈ A) (hk : k ∈ A) :
    D.ΓA (f * g) k =ᵐ[D.μ] fun x => f x * D.ΓA g k x + g x * D.ΓA f k x := by
  have hψ : ContDiff ℝ (⊤ : ℕ∞) (fun z : Fin 2 → ℝ => z 0 * z 1) :=
    (contDiff_apply ℝ ℝ 0).mul (contDiff_apply ℝ ℝ 1)
  have key := h.diffusion_Γ_A 2 (fun z : Fin 2 → ℝ => z 0 * z 1) hψ ![f, g]
    (by intro i; fin_cases i <;> simpa) k hk
  have e : (fun x => (fun z : Fin 2 → ℝ => z 0 * z 1) (fun i => (![f, g] : Fin 2 → E → ℝ) i x))
      = f * g := by
    funext x; simp
  rw [e] at key
  filter_upwards [key] with x hx
  rw [hx]
  simp [Fin.sum_univ_two, pderiv_mul_zero, pderiv_mul_one]
  ring

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

/-- `Γ(f,g) ∈ 𝒜` for `f, g ∈ 𝒜` (F4). -/
theorem ΓA_mem_A {f g : E → ℝ} (hf : f ∈ A) (hg : g ∈ A) : D.ΓA f g ∈ A := by
  have e : D.ΓA f g = (1 / 2 : ℝ) • (D.L (f * g) - f * D.L g - g * D.L f) := by
    funext x
    simp only [DiffusionTriple.ΓA, Pi.smul_apply, Pi.sub_apply, Pi.mul_apply, smul_eq_mul]
    ring
  rw [e]
  exact A.smul_mem (A.sub_mem (A.sub_mem (h.L_mem_A _ (A.mul_mem hf hg))
    (A.mul_mem hf (h.L_mem_A _ hg))) (A.mul_mem hg (h.L_mem_A _ hf))) _

/-- `Γ(f,η) ∈ 𝒜₀` for `f ∈ 𝒜`, `η ∈ 𝒜₀` (remark after BGL Def. 3.3.1). -/
theorem ΓA_mem_A₀ {f η : E → ℝ} (hf : f ∈ A) (hη : η ∈ D.A₀) : D.ΓA f η ∈ D.A₀ := by
  have e : D.ΓA f η = (1 / 2 : ℝ) • (D.L (f * η) - f * D.L η - η * D.L f) := by
    funext x
    simp only [DiffusionTriple.ΓA, Pi.smul_apply, Pi.sub_apply, Pi.mul_apply, smul_eq_mul]
    ring
  rw [e]
  have h1 : f * η ∈ D.A₀ := by rw [mul_comm]; exact h.ideal f hf η hη
  have h2 : f * D.L η ∈ D.A₀ := by rw [mul_comm]; exact h.ideal f hf _ (D.L_mem _ hη)
  have h3 : η * D.L f ∈ D.A₀ := h.ideal _ (h.L_mem_A f hf) η hη
  exact D.A₀.smul_mem _ (D.A₀.sub_mem (D.A₀.sub_mem (D.L_mem _ h1) h2) h3)

end PreFull

end MarkovTriple.BGL
