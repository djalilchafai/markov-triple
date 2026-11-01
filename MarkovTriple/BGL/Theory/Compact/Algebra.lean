import Mathlib
import MarkovTriple.BGL.Theory.Compact.Flow

/-!
# Pure `𝒜₀`-algebra on a compact triple: symmetric integration by parts and `Γ₂`
-/

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

namespace MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E]

namespace CompactTriple

variable (C : CompactTriple E)

lemma ib {f : E → ℝ} (hf : f ∈ C.A₀) : Integrable f C.μ :=
  DiffusionTriple.integrable_of_mem C.toDiffusionTriple hf

lemma Lm {f : E → ℝ} (hf : f ∈ C.A₀) : C.L f ∈ C.A₀ := C.toDiffusionTriple.L_mem f hf

lemma i2 {f g : E → ℝ} (hf : f ∈ C.A₀) (hg : g ∈ C.A₀) :
    Integrable (fun x => f x * g x) C.μ := C.ib (C.A₀.mul_mem hf hg)

lemma i3 {f g h : E → ℝ} (hf : f ∈ C.A₀) (hg : g ∈ C.A₀) (hh : h ∈ C.A₀) :
    Integrable (fun x => f x * g x * h x) C.μ := C.ib (C.A₀.mul_mem (C.A₀.mul_mem hf hg) hh)

/-- symmetry of `L` on `𝒜₀`: `∫ u L v = ∫ v L u`. -/
lemma sym {u v : E → ℝ} (hu : u ∈ C.A₀) (hv : v ∈ C.A₀) :
    ∫ x, u x * C.L v x ∂C.μ = ∫ x, v x * C.L u x ∂C.μ := by
  have h := C.ibp_A u (C.A₀_le u hu) v hv
  linarith [h.1, h.2]

/-- the algebraic form of `2 ∫ k Γ₂(g)`. -/
theorem two_int_Γ₂ {k g : E → ℝ} (hk : k ∈ C.A₀) (hg : g ∈ C.A₀) :
    2 * ∫ x, k x * C.toDiffusionTriple.Γ₂ g g x ∂C.μ =
      (1 / 2) * ∫ x, C.L (C.L k) x * g x * g x ∂C.μ
        - 2 * ∫ x, C.L k x * g x * C.L g x ∂C.μ
        + ∫ x, k x * C.L g x * C.L g x ∂C.μ
        + ∫ x, k x * g x * C.L (C.L g) x ∂C.μ := by
  have hLk := C.Lm hk
  have hLg := C.Lm hg
  have hLLk := C.Lm hLk
  have hLLg := C.Lm hLg
  have hX : C.toDiffusionTriple.ΓA g g ∈ C.A₀ := C.ΓA_self_mem_A₀ hg
  have hgg : g * g ∈ C.A₀ := C.A₀.mul_mem hg hg
  have hgLg : g * C.L g ∈ C.A₀ := C.A₀.mul_mem hg hLg
  have hLX := C.Lm hX
  have hLgg := C.Lm hgg
  have hLgLg := C.Lm hgLg
  -- pointwise expression
  have hpt : ∀ x, 2 * (k x * C.toDiffusionTriple.Γ₂ g g x) =
      k x * C.L (C.toDiffusionTriple.ΓA g g) x - k x * C.L (g * C.L g) x +
        k x * g x * C.L (C.L g) x + k x * C.L g x * C.L g x := by
    intro x
    simp only [DiffusionTriple.Γ₂, DiffusionTriple.ΓA]
    rw [mul_comm (C.L g) g]
    ring
  have e1 : 2 * ∫ x, k x * C.toDiffusionTriple.Γ₂ g g x ∂C.μ =
      ∫ x, (k x * C.L (C.toDiffusionTriple.ΓA g g) x - k x * C.L (g * C.L g) x +
        k x * g x * C.L (C.L g) x + k x * C.L g x * C.L g x) ∂C.μ := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall hpt)
  have j1 := C.i2 hk hLX
  have j2 := C.i2 hk hLgLg
  have j3 := C.i3 hk hg hLLg
  have j4 := C.i3 hk hLg hLg
  have j12 : Integrable (fun x => k x * C.L (C.toDiffusionTriple.ΓA g g) x -
      k x * C.L (g * C.L g) x) C.μ := j1.sub j2
  have j123 : Integrable (fun x => k x * C.L (C.toDiffusionTriple.ΓA g g) x -
      k x * C.L (g * C.L g) x + k x * g x * C.L (C.L g) x) C.μ := j12.add j3
  rw [e1, integral_add j123 j4, integral_add j12 j3, integral_sub j1 j2]
  -- symmetric integration by parts
  have s1 : ∫ x, k x * C.L (C.toDiffusionTriple.ΓA g g) x ∂C.μ =
      ∫ x, C.toDiffusionTriple.ΓA g g x * C.L k x ∂C.μ := C.sym hk hX
  have s3 : ∫ x, k x * C.L (g * C.L g) x ∂C.μ = ∫ x, (g * C.L g) x * C.L k x ∂C.μ :=
    C.sym hk hgLg
  have s2 : ∫ x, C.L k x * C.L (g * g) x ∂C.μ = ∫ x, (g * g) x * C.L (C.L k) x ∂C.μ :=
    C.sym hLk hgg
  have e2 : ∫ x, C.toDiffusionTriple.ΓA g g x * C.L k x ∂C.μ =
      (1 / 2) * ∫ x, C.L (C.L k) x * g x * g x ∂C.μ -
        ∫ x, C.L k x * g x * C.L g x ∂C.μ := by
    have p : ∀ x, C.toDiffusionTriple.ΓA g g x * C.L k x =
        (1 / 2) * (C.L k x * C.L (g * g) x) - C.L k x * g x * C.L g x := by
      intro x; simp only [DiffusionTriple.ΓA]; ring
    have q1 := C.i2 hLk hLgg
    have q2 := C.i3 hLk hg hLg
    rw [integral_congr_ae (Eventually.of_forall p), integral_sub (q1.const_mul _) q2,
      integral_const_mul, s2]
    congr 2
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [Pi.mul_apply]; ring
  have e3 : ∫ x, (g * C.L g) x * C.L k x ∂C.μ = ∫ x, C.L k x * g x * C.L g x ∂C.μ :=
    integral_congr_ae (Eventually.of_forall fun x => by simp only [Pi.mul_apply]; ring)
  rw [s1, s3, e2, e3]
  ring

end CompactTriple

end MarkovTriple.BGL
