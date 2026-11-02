import Mathlib
import MarkovTriple.BGL.Theory.Strong.Energy

/-!
# Bilinear expansion of `Γ` on `𝒜` (a.e.)
-/

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

namespace MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E]

namespace FullTriple

variable {T : FullTriple E}

lemma memA_comb {x y z : E → ℝ} (hx : x ∈ T.A) (hy : y ∈ T.A) (hz : z ∈ T.A) (a : ℝ) :
    (fun w => x w + a * y w + z w) ∈ T.A := by
  have : (fun w => x w + a * y w + z w) = x + a • y + z := by funext w; simp
  rw [this]; exact T.A.add_mem (T.A.add_mem hx (T.A.smul_mem hy a)) hz

/-- `Γ(x + a y + z, k) = Γ(x,k) + aΓ(y,k) + Γ(z,k)`. -/
lemma G_expand_left {x y z k : E → ℝ} (hx : x ∈ T.A) (hy : y ∈ T.A) (hz : z ∈ T.A) (hk : k ∈ T.A)
    (a : ℝ) : G T (fun w => x w + a * y w + z w) k =ᵐ[T.μ]
      fun w => G T x k w + a * G T y k w + G T z k w := by
  have hxy : (fun w => x w + a * y w) ∈ T.A := by
    have : (fun w => x w + a * y w) = x + a • y := by funext w; simp
    rw [this]; exact T.A.add_mem hx (T.A.smul_mem hy a)
  have e : (fun w => x w + a * y w + z w) = fun w => (fun w => x w + a * y w) w + 1 * z w := by
    funext w; ring
  rw [e]
  filter_upwards [G_lin_left hxy hz 1 hk, G_lin_left hx hy a hk] with w h1 h2
  rw [h1, h2]; ring

lemma G_expand_right {x y z k : E → ℝ} (hx : x ∈ T.A) (hy : y ∈ T.A) (hz : z ∈ T.A) (hk : k ∈ T.A)
    (a : ℝ) : G T k (fun w => x w + a * y w + z w) =ᵐ[T.μ]
      fun w => G T k x w + a * G T k y w + G T k z w := by
  rw [G_comm k]
  filter_upwards [G_expand_left hx hy hz hk a] with w h
  rw [h, G_comm x k, G_comm y k, G_comm z k]

end FullTriple

end MarkovTriple.BGL
