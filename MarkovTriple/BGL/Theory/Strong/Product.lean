import Mathlib
import MarkovTriple.BGL.Theory.Strong.Hessian

/-!
# `Γ₂` of a product of two elements of `𝒜` and shift invariance (a.e. identities on `𝒜`)
-/

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

namespace MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E]

namespace FullTriple

variable {T : FullTriple E}

lemma G_mul_right {h k g : E → ℝ} (hh : h ∈ T.A) (hk : k ∈ T.A) (hg : g ∈ T.A) :
    G T g (h * k) =ᵐ[T.μ] fun x => h x * G T g k x + k x * G T g h x := by
  rw [G_comm g (h * k)]
  filter_upwards [G_mul_left hh hk hg] with x hx
  rw [hx, G_comm k g, G_comm h g]

lemma const_memA (c : ℝ) : (fun _ : E => c) ∈ T.A := T.A.algebraMap_mem c

lemma Γ₂_const_left {k : E → ℝ} (hk : k ∈ T.A) (c : ℝ) :
    T.toDiffusionTriple.Γ₂ (fun _ => c) k =ᵐ[T.μ] 0 := by
  have hc : (fun _ : E => c) ∈ T.A := const_memA c
  have h0 : (fun _ : E => (0 : ℝ)) ∈ T.A := const_memA 0
  have a1 : G T (fun _ => c) k =ᵐ[T.μ] (fun _ => (0 : ℝ)) := G_const_left c hk
  have a2 : T.L (G T (fun _ => c) k) =ᵐ[T.μ] T.L (fun _ => (0 : ℝ)) :=
    L_congr_A T (G_mem hc hk) h0 a1
  have a3 : T.L (fun _ => (0 : ℝ)) =ᵐ[T.μ] 0 := L_const 0
  have a4 : G T (fun _ => c) (T.L k) =ᵐ[T.μ] 0 := G_const_left c (L_memA hk)
  have a5 : T.L (fun _ => c) =ᵐ[T.μ] (fun _ => (0 : ℝ)) := L_const c
  have a6 : G T (T.L fun _ => c) k =ᵐ[T.μ] G T (fun _ => (0 : ℝ)) k :=
    G_congr_left (L_memA hc) h0 hk a5
  have a7 : G T (fun _ => (0 : ℝ)) k =ᵐ[T.μ] 0 := G_const_left 0 hk
  filter_upwards [a2, a3, a4, a6, a7] with x b2 b3 b4 b6 b7
  rw [Γ₂_eq, b2, b3, b4, b6, b7]; simp

section shift

variable {f : E → ℝ} (hf : f ∈ T.A) (a : ℝ)

omit [MeasurableSpace E] in
lemma shift_eq : (fun x => f x - a) = fun x => f x + (-a) * (fun _ : E => (1 : ℝ)) x := by
  funext x; ring

include hf in
lemma shift_memA : (fun x => f x - a) ∈ T.A := by
  rw [shift_eq]
  have : (fun x => f x + (-a) * (fun _ : E => (1 : ℝ)) x) = f + (-a) • (fun _ : E => (1 : ℝ)) := by
    funext x; simp
  rw [this]; exact T.A.add_mem hf (T.A.smul_mem (const_memA 1) _)

include hf in
lemma shift_G {k : E → ℝ} (hk : k ∈ T.A) : G T (fun x => f x - a) k =ᵐ[T.μ] G T f k := by
  rw [shift_eq]
  filter_upwards [G_lin_left hf (const_memA (T := T) 1) (-a) hk, G_const_left (T := T) 1 hk] with x h1 h2
  rw [h1]; simp only [Pi.zero_apply] at h2; rw [h2]; ring

include hf in
lemma shift_L : T.L (fun x => f x - a) =ᵐ[T.μ] T.L f := by
  rw [shift_eq]
  filter_upwards [L_lin hf (const_memA (T := T) 1) (-a), L_const (T := T) 1] with x h1 h2
  rw [h1]; simp only [Pi.zero_apply] at h2; rw [h2]; ring

include hf in
lemma shift_Γ₂ {k : E → ℝ} (hk : k ∈ T.A) :
    T.toDiffusionTriple.Γ₂ (fun x => f x - a) k =ᵐ[T.μ] T.toDiffusionTriple.Γ₂ f k := by
  rw [shift_eq]
  filter_upwards [Γ₂_lin_left hf (const_memA (T := T) 1) hk (-a), Γ₂_const_left (T := T) hk 1] with x h1 h2
  rw [h1]; simp only [Pi.zero_apply] at h2; rw [h2]; ring

end shift

/-- **`Γ₂(uv, uv)`**. -/
theorem Γ₂_mul_self {u v : E → ℝ} (hu : u ∈ T.A) (hv : v ∈ T.A) :
    T.toDiffusionTriple.Γ₂ (u * v) (u * v) =ᵐ[T.μ] fun x =>
      u x ^ 2 * T.toDiffusionTriple.Γ₂ v v x + v x ^ 2 * T.toDiffusionTriple.Γ₂ u u x +
        2 * u x * v x * T.toDiffusionTriple.Γ₂ u v x + 2 * u x * G T u (G T v v) x +
        2 * v x * G T v (G T u u) x + 2 * G T u u x * G T v v x + 2 * G T u v x ^ 2 := by
  have huv : u * v ∈ T.A := T.A.mul_mem hu hv
  have Guv := G_mem (T := T) hu hv
  have Gvv := G_mem (T := T) hv hv
  have Guu := G_mem (T := T) hu hu
  -- PR with g = uv
  have r1 := Γ₂_mul_left hu hv huv
  -- Γ₂(v, uv) and Γ₂(u, uv)
  have r2 := Γ₂_mul_left hu hv hv
  have r3 := Γ₂_mul_left hu hv hu
  -- G(v, uv), G(u, uv)
  have w1 : G T v (u * v) =ᵐ[T.μ] u * G T v v + v * G T u v := by
    filter_upwards [G_mul_right hu hv hv] with x hx
    have : G T v u x = G T u v x := by rw [G_comm]
    simp only [Pi.add_apply, Pi.mul_apply]; rw [hx, this]
  have w2 : G T u (u * v) =ᵐ[T.μ] u * G T u v + v * G T u u := by
    filter_upwards [G_mul_right hu hv hu] with x hx; simpa using hx
  have p1 : u * G T v v + v * G T u v ∈ T.A :=
    T.A.add_mem (T.A.mul_mem hu Gvv) (T.A.mul_mem hv Guv)
  have p2 : u * G T u v + v * G T u u ∈ T.A :=
    T.A.add_mem (T.A.mul_mem hu Guv) (T.A.mul_mem hv Guu)
  have z1 : G T u (G T v (u * v)) =ᵐ[T.μ] G T u (u * G T v v + v * G T u v) :=
    G_congr_right hu (G_mem hv huv) p1 w1
  have z2 : G T v (G T u (u * v)) =ᵐ[T.μ] G T v (u * G T u v + v * G T u u) :=
    G_congr_right hv (G_mem hu huv) p2 w2
  have y1 : G T (u * G T v v + v * G T u v) u =ᵐ[T.μ]
      fun x => G T (u * G T v v) u x + G T (v * G T u v) u x :=
    G_add_left (T.A.mul_mem hu Gvv) (T.A.mul_mem hv Guv) hu
  have y2 : G T (u * G T v v) u =ᵐ[T.μ] fun x => u x * G T (G T v v) u x + G T v v x * G T u u x :=
    G_mul_left hu Gvv hu
  have y3 : G T (v * G T u v) u =ᵐ[T.μ] fun x => v x * G T (G T u v) u x + G T u v x * G T v u x :=
    G_mul_left hv Guv hu
  have y4 : G T (u * G T u v + v * G T u u) v =ᵐ[T.μ]
      fun x => G T (u * G T u v) v x + G T (v * G T u u) v x :=
    G_add_left (T.A.mul_mem hu Guv) (T.A.mul_mem hv Guu) hv
  have y5 : G T (u * G T u v) v =ᵐ[T.μ] fun x => u x * G T (G T u v) v x + G T u v x * G T u v x :=
    G_mul_left hu Guv hv
  have y6 : G T (v * G T u u) v =ᵐ[T.μ] fun x => v x * G T (G T u u) v x + G T u u x * G T v v x :=
    G_mul_left hv Guu hv
  have y7 : G T (u * v) (G T u v) =ᵐ[T.μ] fun x => u x * G T v (G T u v) x + v x * G T u (G T u v) x :=
    by
    filter_upwards [G_mul_left hu hv Guv] with x hx; exact hx
  have y8 := z1
  -- G(u, p1) = G(p1, u)
  have c1 : G T u (u * G T v v + v * G T u v) = G T (u * G T v v + v * G T u v) u := G_comm _ _
  have c2 : G T v (u * G T u v + v * G T u u) = G T (u * G T u v + v * G T u u) v := G_comm _ _
  have y9 : G T v (u * v) = G T (u * v) v := G_comm _ _
  have y10 : G T u (u * v) = G T (u * v) u := G_comm _ _
  -- Γ₂(v,uv) = Γ₂(uv,v), Γ₂(u,uv) = Γ₂(uv,u)
  have q1 : T.toDiffusionTriple.Γ₂ v (u * v) = T.toDiffusionTriple.Γ₂ (u * v) v := Γ₂_comm _ _
  have q2 : T.toDiffusionTriple.Γ₂ u (u * v) = T.toDiffusionTriple.Γ₂ (u * v) u := Γ₂_comm _ _
  filter_upwards [r1, r2, r3, z1, z2, y1, y2, y3, y4, y5, y6, y7] with x s1 s2 s3 t1 t2 t3 t4 t5 t6 t7 t8 t9
  rw [s1, q1, q2, s2, s3]
  have e1 : G T u (G T v (u * v)) x = G T u (u * G T v v + v * G T u v) x := t1
  have e2 : G T v (G T u (u * v)) x = G T v (u * G T u v + v * G T u u) x := t2
  rw [e1, e2, c1, c2, t3, t4, t5, t6, t7, t8]
  rw [t9]
  have g1 : G T v u x = G T u v x := by rw [G_comm]
  have g2 : G T (G T v v) u x = G T u (G T v v) x := by rw [G_comm]
  have g3 : G T (G T u u) v x = G T v (G T u u) x := by rw [G_comm]
  have g4 : G T (G T u v) u x = G T u (G T u v) x := by rw [G_comm]
  have g5 : G T (G T u v) v x = G T v (G T u v) x := by rw [G_comm]
  have g6 : G T (u * v) v x = G T v (u * v) x := by rw [G_comm]
  have g7 : T.toDiffusionTriple.Γ₂ v u x = T.toDiffusionTriple.Γ₂ u v x := by rw [Γ₂_comm]
  rw [g1, g2, g3, g4, g5, g7, G_comm v u]
  ring

end FullTriple

end MarkovTriple.BGL
