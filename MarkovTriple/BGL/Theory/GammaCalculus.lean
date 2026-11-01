import Mathlib
import MarkovTriple.BGL.Theory.ALevel

/-!
# One-variable chain rules for `Γ` on the extended algebra `𝒜` (from F3, F6)

For `ψ : ℝ → ℝ` smooth and `g, h ∈ 𝒜`: `Γ(ψ∘g, h) = ψ'(g) Γ(g, h)` a.e.  (`ΓA_comp_left`), hence
`Γ(ψ∘g, ψ∘g) = ψ'(g)² Γ(g,g)` (`ΓA_comp_comp`).  Special cases: translation `ε + g`
(`ΓA_shift`) and the square (`ΓA_sq`).
-/

open MeasureTheory Filter Topology Set

namespace MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E]

lemma pderiv_comp_eval (ψ : ℝ → ℝ) (hψ : Differentiable ℝ ψ) (z : Fin 1 → ℝ) :
    pderiv (fun z : Fin 1 → ℝ => ψ (z 0)) 0 z = deriv ψ (z 0) := by
  have hd : HasFDerivAt (fun z : Fin 1 → ℝ => ψ (z 0))
      (deriv ψ (z 0) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0) z := by
    have h1 : HasDerivAt ψ (deriv ψ (z 0)) (z 0) := (hψ (z 0)).hasDerivAt
    have h2 := h1.comp_hasFDerivAt z (hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 1) z)
    exact h2
  unfold pderiv
  rw [hd.fderiv]
  simp

namespace FullTriple

variable (T : FullTriple E)

lemma const_mem_A (c : ℝ) : (fun _ : E => c) ∈ T.A := T.A.algebraMap_mem c

lemma comp_mem_A {ψ : ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) {g : E → ℝ} (hg : g ∈ T.A) :
    (fun x => ψ (g x)) ∈ T.A := by
  have hψ' : ContDiff ℝ (⊤ : ℕ∞) (fun z : Fin 1 → ℝ => ψ (z 0)) :=
    hψ.comp (contDiff_apply ℝ ℝ 0)
  exact T.A_comp 1 (fun z => ψ (z 0)) hψ' ![g] (by intro i; fin_cases i; simpa using hg)

/-- `Γ(ψ∘g, h) = ψ'(g) Γ(g,h)` a.e., for `g, h ∈ 𝒜` (F6, `k = 1`). -/
theorem ΓA_comp_left {ψ : ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) {g h : E → ℝ} (hg : g ∈ T.A)
    (hh : h ∈ T.A) :
    T.toDiffusionTriple.ΓA (fun x => ψ (g x)) h =ᵐ[T.μ]
      fun x => deriv ψ (g x) * T.toDiffusionTriple.ΓA g h x := by
  have hψ' : ContDiff ℝ (⊤ : ℕ∞) (fun z : Fin 1 → ℝ => ψ (z 0)) :=
    hψ.comp (contDiff_apply ℝ ℝ 0)
  have key := T.diffusion_Γ_A 1 (fun z => ψ (z 0)) hψ' ![g]
    (by intro i; fin_cases i; simpa using hg) h hh
  filter_upwards [key] with x hx
  simp only [Fin.sum_univ_one] at hx
  have hx' : T.toDiffusionTriple.ΓA (fun x => ψ (g x)) h x =
      (pderiv (fun z : Fin 1 → ℝ => ψ (z 0)) 0 fun j => (![g] : Fin 1 → E → ℝ) j x) *
        T.toDiffusionTriple.ΓA g h x := hx
  rw [hx', pderiv_comp_eval ψ (hψ.differentiable (by simp))]
  rfl

/-- `Γ(ψ∘g, ψ∘g) = ψ'(g)² Γ(g,g)` a.e. -/
theorem ΓA_comp_comp {ψ : ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) {g : E → ℝ} (hg : g ∈ T.A) :
    T.toDiffusionTriple.ΓA (fun x => ψ (g x)) (fun x => ψ (g x)) =ᵐ[T.μ]
      fun x => deriv ψ (g x) ^ 2 * T.toDiffusionTriple.ΓA g g x := by
  have hc := comp_mem_A T hψ hg
  have h1 := ΓA_comp_left T hψ hg hc
  have h2 := ΓA_comp_left T hψ hg hg
  filter_upwards [h1, h2] with x hx1 hx2
  have : T.toDiffusionTriple.ΓA g (fun x => ψ (g x)) x =
      T.toDiffusionTriple.ΓA (fun x => ψ (g x)) g x :=
    congrFun (DiffusionTriple.ΓA_comm T.toDiffusionTriple g _) x
  rw [hx1, this, hx2]; ring

/-- Translation: `Γ(ε + g, ε + g) = Γ(g,g)` a.e. -/
theorem ΓA_shift (ε : ℝ) {g : E → ℝ} (hg : g ∈ T.A) :
    T.toDiffusionTriple.ΓA (fun x => ε + g x) (fun x => ε + g x) =ᵐ[T.μ]
      T.toDiffusionTriple.ΓA g g := by
  have hψ : ContDiff ℝ (⊤ : ℕ∞) (fun r : ℝ => ε + r) := contDiff_const.add contDiff_id
  filter_upwards [ΓA_comp_comp T hψ hg] with x hx
  rw [hx]
  have : deriv (fun r : ℝ => ε + r) (g x) = 1 := by simp
  rw [this]; ring

/-- `Γ(f², f²) = 4 f² Γ(f,f)` a.e. -/
theorem ΓA_sq {f : E → ℝ} (hf : f ∈ T.A) :
    T.toDiffusionTriple.ΓA (fun x => f x ^ 2) (fun x => f x ^ 2) =ᵐ[T.μ]
      fun x => 4 * f x ^ 2 * T.toDiffusionTriple.ΓA f f x := by
  have hψ : ContDiff ℝ (⊤ : ℕ∞) (fun r : ℝ => r ^ 2) := contDiff_id.pow 2
  filter_upwards [ΓA_comp_comp T hψ hf] with x hx
  rw [hx]
  have : deriv (fun r : ℝ => r ^ 2) (f x) = 2 * f x := by simp
  rw [this]; ring

end FullTriple

end MarkovTriple.BGL
