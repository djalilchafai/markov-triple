import Mathlib
import MarkovTriple.BGL.Theory.Extension.Hessian

/-!
# Algebra of the Hessian on `𝒜`: linearity, first-order property (BGL p. 158, after Def. 3.3.13)

* `Hess_lin_left`, `Hess_lin_mid`, `Hess_lin_right`: `H(f)(g,h)` is a.e. linear in each slot;
* `Hess_mul_mid`: `H(f)(kg,h) = k H(f)(g,h) + g H(f)(k,h)` (first order operator in `g`);
* `Hess_memA₀`: `H(f)(g,h) ∈ 𝒜₀` when `f,g ∈ 𝒜`, `h ∈ 𝒜₀`.
-/

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

namespace MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E]

namespace FullTriple

variable {T : FullTriple E}

lemma lin_memA {f g : E → ℝ} (hf : f ∈ T.A) (hg : g ∈ T.A) (s : ℝ) :
    (fun x => f x + s * g x) ∈ T.A := by
  have : (fun x => f x + s * g x) = f + s • g := by funext x; simp
  rw [this]; exact T.A.add_mem hf (T.A.smul_mem hg s)

/-- right-slot linearity transported along an a.e. identity. -/
lemma G_lin_right_ae {p k1 k2 K : E → ℝ} (hp : p ∈ T.A) (h1 : k1 ∈ T.A) (h2 : k2 ∈ T.A) (hK : K ∈ T.A)
    (s : ℝ) (hKe : K =ᵐ[T.μ] fun x => k1 x + s * k2 x) :
    G T p K =ᵐ[T.μ] fun x => G T p k1 x + s * G T p k2 x := by
  have hl := lin_memA h1 h2 s
  have c := G_congr_right hp hK hl hKe
  have l := G_lin_left h1 h2 s hp
  filter_upwards [c, l] with x hc hl'
  rw [hc, G_comm p (fun x => k1 x + s * k2 x)]
  rw [show G T (fun x => k1 x + s * k2 x) p x = G T k1 p x + s * G T k2 p x from hl', G_comm k1 p,
    G_comm k2 p]

/-- linearity of `H(f)(g,h)` in `f`. -/
theorem Hess_lin_left {f1 f2 g h : E → ℝ} (h1 : f1 ∈ T.A) (h2 : f2 ∈ T.A) (hg : g ∈ T.A)
    (hh : h ∈ T.A) (s : ℝ) :
    Hess T (fun x => f1 x + s * f2 x) g h =ᵐ[T.μ] fun x => Hess T f1 g h x + s * Hess T f2 g h x := by
  have hF := lin_memA h1 h2 s
  have a1 := G_lin_left h1 h2 s hh
  have a2 := G_lin_left h1 h2 s hg
  have a3 := G_lin_left h1 h2 s (G_mem hg hh)
  have m1 := lin_memA (G_mem h1 hh) (G_mem h2 hh) s
  have m2 := lin_memA (G_mem h1 hg) (G_mem h2 hg) s
  have t1 := G_lin_right_ae hg (G_mem h1 hh) (G_mem h2 hh) (G_mem hF hh) s a1
  have t2 := G_lin_right_ae hh (G_mem h1 hg) (G_mem h2 hg) (G_mem hF hg) s a2
  filter_upwards [t1, t2, a3] with x e1 e2 e3
  simp only [Hess]
  rw [e1, e2, e3]
  ring

/-- linearity of `H(f)(g,h)` in `g`. -/
theorem Hess_lin_mid {f g1 g2 h : E → ℝ} (hf : f ∈ T.A) (h1 : g1 ∈ T.A) (h2 : g2 ∈ T.A)
    (hh : h ∈ T.A) (s : ℝ) :
    Hess T f (fun x => g1 x + s * g2 x) h =ᵐ[T.μ] fun x => Hess T f g1 h x + s * Hess T f g2 h x := by
  have hF := lin_memA h1 h2 s
  have a1 := G_lin_left h1 h2 s (G_mem hf hh)
  have a2 : G T f (fun x => g1 x + s * g2 x) =ᵐ[T.μ] fun x => G T f g1 x + s * G T f g2 x := by
    have := G_lin_left h1 h2 s hf
    filter_upwards [this] with x hx
    rw [G_comm f, hx, G_comm g1 f, G_comm g2 f]
  have a3 := G_lin_left h1 h2 s hh
  have m2 := lin_memA (G_mem hf h1) (G_mem hf h2) s
  have t2 := G_lin_right_ae hh (G_mem hf h1) (G_mem hf h2) (G_mem hf hF) s a2
  have t3 := G_lin_right_ae hf (G_mem h1 hh) (G_mem h2 hh) (G_mem hF hh) s a3
  filter_upwards [a1, t2, t3] with x e1 e2 e3
  simp only [Hess]
  rw [e1, e2, e3]
  ring

theorem Hess_lin_right {f g h1 h2 : E → ℝ} (hf : f ∈ T.A) (hg : g ∈ T.A) (e1 : h1 ∈ T.A)
    (e2 : h2 ∈ T.A) (s : ℝ) :
    Hess T f g (fun x => h1 x + s * h2 x) =ᵐ[T.μ] fun x => Hess T f g h1 x + s * Hess T f g h2 x := by
  rw [Hess_symm]
  filter_upwards [Hess_lin_mid hf e1 e2 hg s] with x hx
  rw [hx, Hess_symm f g h1, Hess_symm f g h2]

/-- `H(f)(g,h) ∈ 𝒜` for `f,g,h ∈ 𝒜`. -/
lemma Hess_memA {f g h : E → ℝ} (hf : f ∈ T.A) (hg : g ∈ T.A) (hh : h ∈ T.A) :
    Hess T f g h ∈ T.A := by
  have : Hess T f g h = (1 / 2 : ℝ) • (G T g (G T f h) + G T h (G T f g) - G T f (G T g h)) := by
    funext x; simp only [Hess, Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]; ring
  rw [this]
  exact T.A.smul_mem (T.A.sub_mem (T.A.add_mem (G_mem hg (G_mem hf hh)) (G_mem hh (G_mem hf hg)))
    (G_mem hf (G_mem hg hh))) _

/-- `H(f)(g,h) ∈ 𝒜₀` for `f, g ∈ 𝒜` and `h ∈ 𝒜₀`. -/
lemma Hess_memA₀ {f g h : E → ℝ} (hf : f ∈ T.A) (hg : g ∈ T.A) (hh : h ∈ T.A₀) :
    Hess T f g h ∈ T.A₀ := by
  have hhA := T.A₀_le _ hh
  have : Hess T f g h = (1 / 2 : ℝ) • (G T g (G T f h) + G T (G T f g) h - G T f (G T g h)) := by
    funext x
    simp only [Hess, Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
    rw [G_comm h (G T f g)]; ring
  rw [this]
  exact T.A₀.smul_mem _ (T.A₀.sub_mem (T.A₀.add_mem (ΓA_mem_A₀ T hg (ΓA_mem_A₀ T hf hh))
    (ΓA_mem_A₀ T (G_mem hf hg) hh)) (ΓA_mem_A₀ T hf (ΓA_mem_A₀ T hg hh)))

lemma G_right_two_mul {p a u b v : E → ℝ} (hp : p ∈ T.A) (ha : a ∈ T.A) (hu : u ∈ T.A) (hb : b ∈ T.A)
    (hv : v ∈ T.A) :
    G T p (fun x => a x * u x + b x * v x) =ᵐ[T.μ] fun x =>
      a x * G T p u x + u x * G T p a x + (b x * G T p v x + v x * G T p b x) := by
  have hau : a * u ∈ T.A := T.A.mul_mem ha hu
  have hbv : b * v ∈ T.A := T.A.mul_mem hb hv
  have hs : (fun x => a x * u x + b x * v x) ∈ T.A := by
    have : (fun x => a x * u x + b x * v x) = a * u + b * v := by funext x; simp
    rw [this]; exact T.A.add_mem hau hbv
  have e1 := G_lin_right_ae (K := fun x => a x * u x + b x * v x) hp hau hbv hs 1
    (Eventually.of_forall fun x => by simp)
  have e2 := G_mul_right ha hu hp
  have e3 := G_mul_right hb hv hp
  filter_upwards [e1, e2, e3] with x h1 h2 h3
  rw [h1]
  rw [h2, h3]; ring

/-- BGL (p. 158): `H(f)(kg,h) = k H(f)(g,h) + g H(f)(k,h)` (first order in the middle slot). -/
theorem Hess_mul_mid {f g k h : E → ℝ} (hf : f ∈ T.A) (hg : g ∈ T.A) (hk : k ∈ T.A) (hh : h ∈ T.A) :
    Hess T f (k * g) h =ᵐ[T.μ] fun x => k x * Hess T f g h x + g x * Hess T f k h x := by
  have hkg : k * g ∈ T.A := T.A.mul_mem hk hg
  have e1 := G_mul_left hk hg (G_mem hf hh)
  have e2 : G T f (k * g) =ᵐ[T.μ] fun x => k x * G T g f x + g x * G T k f x := by
    have := G_mul_left hk hg hf
    filter_upwards [this] with x hx
    rw [G_comm f (k * g)]; exact hx
  have e3 : G T (k * g) h =ᵐ[T.μ] fun x => k x * G T g h x + g x * G T k h x := G_mul_left hk hg hh
  have mA : (fun x => k x * G T g f x + g x * G T k f x) ∈ T.A := by
    have : (fun x => k x * G T g f x + g x * G T k f x) = k * G T g f + g * G T k f := by
      funext x; simp
    rw [this]; exact T.A.add_mem (T.A.mul_mem hk (G_mem hg hf)) (T.A.mul_mem hg (G_mem hk hf))
  have nA : (fun x => k x * G T g h x + g x * G T k h x) ∈ T.A := by
    have : (fun x => k x * G T g h x + g x * G T k h x) = k * G T g h + g * G T k h := by
      funext x; simp
    rw [this]; exact T.A.add_mem (T.A.mul_mem hk (G_mem hg hh)) (T.A.mul_mem hg (G_mem hk hh))
  have t2 := G_congr_right hh (G_mem hf hkg) mA e2
  have t2' := G_right_two_mul hh hk (G_mem hg hf) hg (G_mem hk hf)
  have t3 := G_congr_right hf (G_mem hkg hh) nA e3
  have t3' := G_right_two_mul hf hk (G_mem hg hh) hg (G_mem hk hh)
  have m1 := Hess_memA hf hg hh
  filter_upwards [e1, t2, t2', t3, t3'] with x a1 a2 a3 a4 a5
  simp only [Hess]
  rw [a1, a2, a3, a4, a5]
  simp only [G_comm g f, G_comm k f, G_comm h g, G_comm h k]
  ring

end FullTriple

end MarkovTriple.BGL
