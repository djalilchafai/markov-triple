import Mathlib
import MarkovTriple.BGL.Instances.Gibbs.FunctPreFull

/-!
# The cut-off estimate of BGL Prop. 3.2.1 (extended in the paragraph after Prop. 3.3.10)

Inside the proof of Prop. 3.2.1 the book multiplies `f L f = f²` (there `Lf = f`) by `ζ²`, integrates by parts
against `f ζ² ∈ 𝒜₀` and applies the chain rule to get
`∫ ζ² Γ(f) ≤ 2 ∫ |f ζ| Γ(f)^{1/2} Γ(ζ)^{1/2}`, then Cauchy–Schwarz with `Γ(ζ) ≤ ε`, giving
`∫ ζ² Γ(f) ≤ 4 ε ‖f‖₂²`.  Letting `ζ = ζ_k` (completeness, Def. 3.3.9) yields `Γ(f) = 0`.
Here the pointwise AM-GM `2|fζ||Γ(ζ,f)| ≤ ½ζ²Γ(f) + 2ε²f²` replaces the integral Cauchy–Schwarz.
-/

open MeasureTheory Filter Topology

namespace MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E]

namespace PreFull

variable {D : DiffusionTriple E} {A : Subalgebra ℝ (E → ℝ)} (h : PreFull D A)
include h

/-- **The quantitative cut-off estimate** (BGL Prop. 3.2.1, proof): for `w ∈ 𝒜 ∩ L²` with `w L w ≥ 0`
and any `η ∈ 𝒜₀` with `Γ(η) ≤ ε²`:  `∫ η² Γ(w) ≤ 4 ε² ∫ w²`. -/
theorem cutoff_estimate {w η : E → ℝ} (hw : w ∈ A) (hw2 : MemLp w 2 D.μ)
    (hsign : ∀ᵐ x ∂D.μ, 0 ≤ w x * D.L w x) (hη : η ∈ D.A₀) {ε : ℝ} (hε : 0 < ε)
    (hΓη : D.ΓA η η ≤ᵐ[D.μ] fun _ => ε ^ 2) :
    ∫ x, (η x * η x) * D.ΓA w w x ∂D.μ ≤ 4 * ε ^ 2 * ∫ x, w x ^ 2 ∂D.μ := by
  have hηA : η ∈ A := h.A₀_le η hη
  have hηη : η * η ∈ D.A₀ := D.A₀.mul_mem hη hη
  have hηηA : η * η ∈ A := h.A₀_le _ hηη
  set g : E → ℝ := (η * η) * w with hg
  have hgA₀ : g ∈ D.A₀ := h.ideal w hw (η * η) hηη
  have hΓww : D.ΓA w w ∈ A := h.ΓA_mem_A hw hw
  have hF7 := (h.ibp_A w hw g hgA₀).1
  -- the identity `Γ(w, g) = η² Γ(w) + 2 w η Γ(η, w)`
  have hcomm : D.ΓA w g = D.ΓA g w := DiffusionTriple.ΓA_comm D w g
  have m1 := h.ΓA_mul_left hηηA hw hw
  have m2 := h.ΓA_mul_left hηA hηA hw
  have hid : ∀ᵐ x ∂D.μ, D.ΓA w g x = (η x * η x) * D.ΓA w w x +
      2 * (w x * η x * D.ΓA η w x) := by
    filter_upwards [m1, m2] with x a b
    rw [hcomm]
    have : D.ΓA g w x = (η * η) x * D.ΓA w w x + w x * D.ΓA (η * η) w x := a
    rw [this, b]
    simp only [Pi.mul_apply]
    ring
  -- integrability
  have hI1 : Integrable (fun x => (η x * η x) * D.ΓA w w x) D.μ := by
    have : (η * D.ΓA w w ∘ id) = η * D.ΓA w w := rfl
    exact DiffusionTriple.integrable_of_mem D (h.ideal _ hΓww (η * η) hηη)
  have hI2 : Integrable (D.ΓA w g) D.μ := DiffusionTriple.integrable_of_mem D (h.ΓA_mem_A₀ hw hgA₀)
  have hI3 : Integrable (fun x => w x ^ 2) D.μ := hw2.integrable_sq
  -- the sign
  have hsgn : ∫ x, D.ΓA w g x ∂D.μ ≤ 0 := by
    rw [hF7, neg_nonpos]
    refine integral_nonneg_of_ae ?_
    filter_upwards [hsign] with x hx
    show 0 ≤ (η x * η x * w x) * D.L w x
    have : (η x * η x * w x) * D.L w x = (η x * η x) * (w x * D.L w x) := by ring
    rw [this]
    exact mul_nonneg (mul_self_nonneg _) hx
  -- pointwise bound
  have hpt : ∀ᵐ x ∂D.μ, (1 / 2) * ((η x * η x) * D.ΓA w w x) ≤
      D.ΓA w g x + 2 * ε ^ 2 * w x ^ 2 := by
    filter_upwards [hid, ΓA_cs h hηA hw, h.ΓA_nonneg w hw, hΓη] with x a b c d
    simp only [Pi.zero_apply] at c
    set G := D.ΓA w w x
    set c' := D.ΓA η w x
    have hc2 : c' ^ 2 ≤ ε ^ 2 * G := by
      calc c' ^ 2 ≤ D.ΓA η η x * G := b
        _ ≤ ε ^ 2 * G := mul_le_mul_of_nonneg_right d c
    -- `-2 w η c' ≤ a w² + (η c')²/a`, `a = 2 ε²`
    have ha : 0 < 2 * ε ^ 2 := by positivity
    have k1 : -2 * (w x * (η x * c')) * (2 * ε ^ 2) ≤
        (2 * ε ^ 2) * (2 * ε ^ 2) * w x ^ 2 + (η x * c') ^ 2 := by
      nlinarith [sq_nonneg ((2 * ε ^ 2) * w x + η x * c')]
    have k2 : (η x * c') ^ 2 ≤ η x ^ 2 * (ε ^ 2 * G) := by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_left hc2 (sq_nonneg _)
    have k3 : -2 * (w x * η x * c') ≤ 2 * ε ^ 2 * w x ^ 2 + (1 / 2) * (η x * η x * G) := by
      have : -2 * (w x * η x * c') * (2 * ε ^ 2) ≤
          (2 * ε ^ 2) * (2 * ε ^ 2 * w x ^ 2 + (1 / 2) * (η x * η x * G)) := by
        nlinarith [k1, k2]
      have hε2 : 0 < 2 * ε ^ 2 := ha
      exact le_of_mul_le_mul_right (by linarith) hε2
    linarith
  have hI4 : Integrable (fun x => D.ΓA w g x + 2 * ε ^ 2 * w x ^ 2) D.μ :=
    hI2.add (hI3.const_mul (2 * ε ^ 2))
  have hint := integral_mono_ae (hI1.const_mul (1 / 2)) hI4 hpt
  have e1 : ∫ x, (1 / 2) * ((η x * η x) * D.ΓA w w x) ∂D.μ =
      (1 / 2) * ∫ x, (η x * η x) * D.ΓA w w x ∂D.μ := integral_const_mul _ _
  have e2 : ∫ x, (D.ΓA w g x + 2 * ε ^ 2 * w x ^ 2) ∂D.μ =
      ∫ x, D.ΓA w g x ∂D.μ + 2 * ε ^ 2 * ∫ x, w x ^ 2 ∂D.μ := by
    rw [integral_add hI2 (hI3.const_mul _), integral_const_mul]
  rw [e1, e2] at hint
  nlinarith [hint, hsgn]


/-- **`Γ(w) = 0` for `w ∈ 𝒜 ∩ L²` with `w L w ≥ 0`, on a complete triple** (BGL Prop. 3.2.1 proof, Def. 3.3.9). -/
theorem gradient_eq_zero (hC : D.IsComplete) {w : E → ℝ} (hw : w ∈ A) (hw2 : MemLp w 2 D.μ)
    (hsign : ∀ᵐ x ∂D.μ, 0 ≤ w x * D.L w x) : D.ΓA w w =ᵐ[D.μ] 0 := by
  obtain ⟨ζ, hζA, hζ0, hmono, hlim, hΓ⟩ := hC
  have hG0 := h.ΓA_nonneg w hw
  have hΓww : D.ΓA w w ∈ A := h.ΓA_mem_A hw hw
  have hI : ∀ k, Integrable (fun x => (ζ k x * ζ k x) * D.ΓA w w x) D.μ := fun k =>
    DiffusionTriple.integrable_of_mem D (h.ideal _ hΓww (ζ k * ζ k) (D.A₀.mul_mem (hζA k) (hζA k)))
  set C : ℝ := ∫ x, w x ^ 2 ∂D.μ with hC
  have est : ∀ k : ℕ, ∫ x, (ζ k x * ζ k x) * D.ΓA w w x ∂D.μ ≤ 4 * (1 / ((k : ℝ) + 1)) ^ 2 * C := by
    intro k
    refine h.cutoff_estimate hw hw2 hsign (hζA k) (by positivity) ?_
    filter_upwards [DiffusionTriple.ΓA_ae_eq D (hζA k) (hζA k), hΓ k] with x a b
    rw [a]; exact b
  have hmon : ∀ᵐ x ∂D.μ, ∀ k, ζ k x ≤ ζ (k + 1) x := ae_all_iff.2 hmono
  have hpos : ∀ᵐ x ∂D.μ, ∀ k, 0 ≤ ζ k x := ae_all_iff.2 hζ0
  have hJmono : ∀ j k, j ≤ k → ∫ x, (ζ j x * ζ j x) * D.ΓA w w x ∂D.μ ≤
      ∫ x, (ζ k x * ζ k x) * D.ΓA w w x ∂D.μ := by
    intro j k hjk
    refine integral_mono_ae (hI j) (hI k) ?_
    filter_upwards [hmon, hpos, hG0] with x a b c
    simp only [Pi.zero_apply] at c
    have hm : Monotone fun n => ζ n x := monotone_nat_of_le_succ a
    have := hm hjk
    exact mul_le_mul_of_nonneg_right (by nlinarith [b j, b k]) c
  have hzero : ∀ j, (fun x => (ζ j x * ζ j x) * D.ΓA w w x) =ᵐ[D.μ] 0 := by
    intro j
    have hnn : 0 ≤ᵐ[D.μ] fun x => (ζ j x * ζ j x) * D.ΓA w w x := by
      filter_upwards [hG0] with x c
      simp only [Pi.zero_apply] at c ⊢
      exact mul_nonneg (mul_self_nonneg _) c
    have hle : ∫ x, (ζ j x * ζ j x) * D.ΓA w w x ∂D.μ ≤ 0 := by
      have ht : Tendsto (fun k : ℕ => 4 * (1 / ((k : ℝ) + 1)) ^ 2 * C) atTop (𝓝 0) := by
        have h1 := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).pow 2
        have h2 := (h1.const_mul 4).mul_const C
        simpa using h2
      exact ge_of_tendsto ht (eventually_atTop.2 ⟨j, fun k hk => (hJmono j k hk).trans (est k)⟩)
    have h0 : ∫ x, (ζ j x * ζ j x) * D.ΓA w w x ∂D.μ = 0 :=
      le_antisymm hle (integral_nonneg_of_ae hnn)
    exact (integral_eq_zero_iff_of_nonneg_ae hnn (hI j)).1 h0
  have hall : ∀ᵐ x ∂D.μ, ∀ j, (ζ j x * ζ j x) * D.ΓA w w x = 0 := ae_all_iff.2 hzero
  filter_upwards [hall, hlim] with x hx hl
  obtain ⟨j, hj⟩ := (hl.eventually_ne (one_ne_zero : (1 : ℝ) ≠ 0)).exists
  have := hx j
  simp only [Pi.zero_apply]
  rcases mul_eq_zero.1 this with h1 | h1
  · exact absurd (mul_self_eq_zero.1 h1) hj
  · exact h1

end PreFull

end MarkovTriple.BGL
