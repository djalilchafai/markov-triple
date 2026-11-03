import Mathlib
import MarkovTriple.BGL.Theory.Strong.Interpolation
import MarkovTriple.BGL.Theory.Strong.Hessian
import MarkovTriple.BGL.Theory.Gamma2Integral
import MarkovTriple.BGL.Theory.GammaCalculus

/-!
# The chain rule for `Γ₂` along `e^{ag}` (BGL (5.7.6)) and its integrated consequence (BGL (5.7.10)-(5.7.12))

Source: Bakry-Gentil-Ledoux, proof of Thm 5.7.4, pp. 270-272.

* `Γ₂_exp` (BGL (5.7.6), p. 270): for `g ∈ 𝒜`, `a ∈ ℝ`:
  `Γ₂(e^{ag}) = a² e^{2ag} (Γ₂(g) + a Γ(g, Γ(g)) + a² Γ(g)²)` a.e.
  (The book obtains it from the chain rule (3.3.2) for `Γ₂`; here it is computed from the definition
  `Γ₂(f) = ½ L Γ(f) − Γ(f, L f)` and the chain rules F6 for `L`, `Γ`.)
* `integral_exp_Γ₂_ge` (BGL (5.7.11), (5.7.12), p. 271-272): for `g ∈ 𝒜₀` with `e^{g/2} ∈ 𝒜₀` (the case where
  the book's Prop. 3.3.17 identification `∫Γ₂(f) = ∫(Lf)²` is available, as it is on compact triples) and `CD(ρ,n)`,
  `1 < n < ∞`:
  `ρ n/(n-1) ∫ e^g Γ(g) + (4n-1)/(4(n+2)²) ∫ e^g Γ(g)² ≤ ∫ e^g Γ₂(g)`.
-/

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

namespace MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E]

namespace FullTriple

variable (T : FullTriple E)

lemma contDiff_kexp (k c : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (fun r : ℝ => k * Real.exp (c * r)) :=
  contDiff_const.mul (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id))

lemma deriv_kexp (k c r : ℝ) :
    deriv (fun r : ℝ => k * Real.exp (c * r)) r = k * c * Real.exp (c * r) := by
  have h : HasDerivAt (fun r : ℝ => k * Real.exp (c * r)) (k * (Real.exp (c * r) * c)) r := by
    have h1 : HasDerivAt (fun r : ℝ => c * r) c r := by
      simpa using (hasDerivAt_id r).const_mul c
    exact (h1.exp).const_mul k
  rw [h.deriv]; ring

lemma deriv_deriv_kexp (k c r : ℝ) :
    deriv (deriv (fun r : ℝ => k * Real.exp (c * r))) r = k * c * c * Real.exp (c * r) := by
  have : deriv (fun r : ℝ => k * Real.exp (c * r)) = fun r => (k * c) * Real.exp (c * r) := by
    funext r; rw [deriv_kexp]
  rw [this, deriv_kexp]

/-- `x ↦ k e^{c g(x)}`. -/
noncomputable def Pw (g : E → ℝ) (k c : ℝ) : E → ℝ := fun x => k * Real.exp (c * g x)

variable {T}
variable {g : E → ℝ}

lemma Pw_mem (hg : g ∈ T.A) (k c : ℝ) : Pw g k c ∈ T.A :=
  comp_mem_A T (contDiff_kexp k c) hg

lemma L_Pw (hg : g ∈ T.A) (k c : ℝ) :
    T.L (Pw g k c) =ᵐ[T.μ] fun x =>
      k * c * Real.exp (c * g x) * T.L g x +
        k * c * c * Real.exp (c * g x) * T.toDiffusionTriple.ΓA g g x := by
  filter_upwards [L_comp T (contDiff_kexp k c) hg] with x hx
  have hx' : T.L (Pw g k c) x = _ := hx
  rw [hx', deriv_kexp, deriv_deriv_kexp]

lemma G_Pw (hg : g ∈ T.A) (k c : ℝ) {h : E → ℝ} (hh : h ∈ T.A) :
    G T (Pw g k c) h =ᵐ[T.μ] fun x => k * c * Real.exp (c * g x) * G T g h x := by
  filter_upwards [ΓA_comp_left T (contDiff_kexp k c) hg hh] with x hx
  have hx' : G T (Pw g k c) h x = _ := hx
  rw [hx', deriv_kexp]

/-- `Γ₂(e^{ag})` for the representative `Pw g 1 a` (computation behind `Γ₂_exp`). -/
theorem Γ₂_Pw (hg : g ∈ T.A) (a : ℝ) :
    T.toDiffusionTriple.Γ₂ (Pw g 1 a) (Pw g 1 a) =ᵐ[T.μ]
      fun x => a ^ 2 * Real.exp (2 * a * g x) *
        (T.toDiffusionTriple.Γ₂ g g x + a * G T g (G T g g) x + a ^ 2 * (G T g g x) ^ 2) := by
  have huA : G T g g ∈ T.A := G_mem hg hg
  have hlA : T.L g ∈ T.A := L_memA hg
  have hEA : Pw g 1 a ∈ T.A := Pw_mem hg 1 a
  have i1 : G T (Pw g 1 a) (Pw g 1 a) =ᵐ[T.μ] Pw g (a ^ 2) (2 * a) * G T g g := by
    have := ΓA_comp_comp T (contDiff_kexp 1 a) hg
    filter_upwards [this] with x hx
    have hx' : G T (Pw g 1 a) (Pw g 1 a) x = _ := hx
    rw [hx', deriv_kexp]
    simp only [Pw, Pi.mul_apply]
    have : Real.exp (a * g x) ^ 2 = Real.exp (2 * a * g x) := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [show (1 * a * Real.exp (a * g x)) ^ 2 = a ^ 2 * Real.exp (a * g x) ^ 2 by ring, this]
  have hPA : Pw g (a ^ 2) (2 * a) ∈ T.A := Pw_mem hg _ _
  have i2 : T.L (G T (Pw g 1 a) (Pw g 1 a)) =ᵐ[T.μ] T.L (Pw g (a ^ 2) (2 * a) * G T g g) :=
    L_congr_A T (G_mem hEA hEA) (T.A.mul_mem hPA huA) i1
  have i3 := L_Pw hg (a ^ 2) (2 * a)
  have i4 := G_Pw hg (a ^ 2) (2 * a) huA
  have hrP : (fun x => a * Real.exp (a * g x) * T.L g x + a ^ 2 * Real.exp (a * g x) * G T g g x)
      = Pw g a a * T.L g + Pw g (a ^ 2) a * G T g g := by
    funext x; simp [Pw]
  have hrA : (fun x => a * Real.exp (a * g x) * T.L g x + a ^ 2 * Real.exp (a * g x) * G T g g x)
      ∈ T.A := by
    rw [hrP]
    exact T.A.add_mem (T.A.mul_mem (Pw_mem hg _ _) hlA) (T.A.mul_mem (Pw_mem hg _ _) huA)
  have ii1 : T.L (Pw g 1 a) =ᵐ[T.μ]
      fun x => a * Real.exp (a * g x) * T.L g x + a ^ 2 * Real.exp (a * g x) * G T g g x := by
    filter_upwards [L_Pw hg 1 a] with x hx
    rw [hx]; simp only [DiffusionTriple.ΓA]; ring
  have ii2 := G_congr_right hEA (L_memA hEA) hrA ii1
  have ii3 := G_Pw hg 1 a hrA
  have ii4 : G T (fun x => a * Real.exp (a * g x) * T.L g x +
      a ^ 2 * Real.exp (a * g x) * G T g g x) g =ᵐ[T.μ] fun x =>
      (Pw g a a x * G T (T.L g) g x + T.L g x * G T (Pw g a a) g x) +
      (Pw g (a ^ 2) a x * G T (G T g g) g x + G T g g x * G T (Pw g (a ^ 2) a) g x) := by
    rw [hrP]
    have hA1 : Pw g a a * T.L g ∈ T.A := T.A.mul_mem (Pw_mem hg _ _) hlA
    have hA2 : Pw g (a ^ 2) a * G T g g ∈ T.A := T.A.mul_mem (Pw_mem hg _ _) huA
    filter_upwards [G_add_left hA1 hA2 hg, G_mul_left (Pw_mem hg a a) hlA hg,
      G_mul_left (Pw_mem hg (a ^ 2) a) huA hg] with x e1 e2 e3
    rw [e1, e2, e3]
  have ii5 := G_Pw hg a a hg
  have ii6 := G_Pw hg (a ^ 2) a hg
  filter_upwards [i2, i3, i4, ii2, ii3, ii4, ii5, ii6] with x e2 e3 e4 f2 f3 f4 f5 f6
  have c1 := L_mul_eq (T := T) (Pw g (a ^ 2) (2 * a)) (G T g g) x
  have g1 : G T g (fun x => a * Real.exp (a * g x) * T.L g x +
      a ^ 2 * Real.exp (a * g x) * G T g g x) x = G T (fun x => a * Real.exp (a * g x) * T.L g x +
      a ^ 2 * Real.exp (a * g x) * G T g g x) g x := congrFun (G_comm (T := T) _ _) x
  have g2 : G T (T.L (Pw g 1 a)) (Pw g 1 a) x = G T (Pw g 1 a) (T.L (Pw g 1 a)) x :=
    congrFun (G_comm (T := T) _ _) x
  have g3 : G T g (G T g g) x = G T (G T g g) g x := congrFun (G_comm (T := T) _ _) x
  have g4 : G T (T.L g) g x = G T g (T.L g) x := congrFun (G_comm (T := T) _ _) x
  have hex : Real.exp (2 * a * g x) = Real.exp (a * g x) ^ 2 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [Γ₂_eq, Γ₂_eq, g2, e2, c1, e3, e4, f2, f3, g1, f4, f5, f6, g3, g4]
  simp only [Pw]
  rw [hex]
  ring

/-- **BGL (5.7.6)** (p. 270): `Γ₂(e^{ag}) = a² e^{2ag}(Γ₂(g) + a Γ(g,Γ(g)) + a² Γ(g)²)` a.e., `g ∈ 𝒜`. -/
theorem Γ₂_exp (hg : g ∈ T.A) (a : ℝ) :
    T.toDiffusionTriple.Γ₂ (fun x => Real.exp (a * g x)) (fun x => Real.exp (a * g x)) =ᵐ[T.μ]
      fun x => a ^ 2 * Real.exp (2 * a * g x) *
        (T.toDiffusionTriple.Γ₂ g g x + a * G T g (G T g g) x + a ^ 2 * (G T g g x) ^ 2) := by
  have hE : (fun x => Real.exp (a * g x)) = Pw g 1 a := by funext x; simp [Pw]
  rw [hE]; exact Γ₂_Pw hg a

/-! ### The integrated inequality (5.7.7)-(5.7.12) for `g ∈ 𝒜₀` -/

section Integrated

variable (hg0 : g ∈ T.A₀)
include hg0

lemma expg_mem : (fun x => Real.exp (g x)) ∈ T.A := comp_mem_A T Real.contDiff_exp (T.A₀_le g hg0)

/-- `∫ e^g h` is finite for `h ∈ 𝒜₀` (F1: `𝒜₀ · 𝒜 ⊂ 𝒜₀`). -/
lemma intW {h : E → ℝ} (hh : h ∈ T.A₀) :
    Integrable (fun x => Real.exp (g x) * h x) T.μ := by
  have := DiffusionTriple.integrable_of_mem T.toDiffusionTriple (T.ideal _ (expg_mem hg0) h hh)
  exact this.congr (Eventually.of_forall fun x => by simp [mul_comm])

lemma G2_mem : T.toDiffusionTriple.Γ₂ g g ∈ T.A₀ := by
  have hgA := T.A₀_le g hg0
  have hu := ΓA_self_mem_A₀ T hg0
  have hl := T.L_mem g hg0
  have h1 : T.L (G T g g) ∈ T.A₀ := T.L_mem _ hu
  have h2 : G T g (T.L g) ∈ T.A₀ := ΓA_mem_A₀ T hgA hl
  have h3 : G T (T.L g) g ∈ T.A₀ := ΓA_mem_A₀ T (L_memA hgA) hg0
  have : T.toDiffusionTriple.Γ₂ g g = (1 / 2 : ℝ) • (T.L (G T g g) - G T g (T.L g) - G T (T.L g) g) := by
    funext x
    simp only [DiffusionTriple.Γ₂, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring
  rw [this]
  exact T.A₀.smul_mem _ (T.A₀.sub_mem (T.A₀.sub_mem h1 h2) h3)

/-- the six `𝒜₀` functions of the computation. -/
lemma mem_comb (c0 c1 c2 c3 c4 c5 : ℝ) : (fun x => c0 * T.toDiffusionTriple.Γ₂ g g x +
    c1 * G T g (G T g g) x + c2 * (G T g g x) ^ 2 + c3 * (T.L g x) ^ 2 +
    c4 * (T.L g x * G T g g x) + c5 * G T g g x) ∈ T.A₀ := by
  have hgA := T.A₀_le g hg0
  have hu := ΓA_self_mem_A₀ T hg0
  have hl := T.L_mem g hg0
  have hv : G T g (G T g g) ∈ T.A₀ := ΓA_mem_A₀ T hgA hu
  have hu2 : (fun x => (G T g g x) ^ 2) ∈ T.A₀ := by
    have : (fun x => (G T g g x) ^ 2) = G T g g * G T g g := by funext x; simp [sq]
    rw [this]; exact T.A₀.mul_mem hu hu
  have hl2 : (fun x => (T.L g x) ^ 2) ∈ T.A₀ := by
    have : (fun x => (T.L g x) ^ 2) = T.L g * T.L g := by funext x; simp [sq]
    rw [this]; exact T.A₀.mul_mem hl hl
  have hlu : (fun x => T.L g x * G T g g x) ∈ T.A₀ := T.A₀.mul_mem hl hu
  have := T.A₀.add_mem (T.A₀.add_mem (T.A₀.add_mem (T.A₀.add_mem (T.A₀.add_mem
    (T.A₀.smul_mem c0 (G2_mem hg0)) (T.A₀.smul_mem c1 hv)) (T.A₀.smul_mem c2 hu2))
    (T.A₀.smul_mem c3 hl2)) (T.A₀.smul_mem c4 hlu)) (T.A₀.smul_mem c5 hu)
  convert this using 1

/-- the weighted moment of the combination. -/
lemma M_comb (c0 c1 c2 c3 c4 c5 : ℝ) :
    ∫ x, Real.exp (g x) * (c0 * T.toDiffusionTriple.Γ₂ g g x +
      c1 * G T g (G T g g) x + c2 * (G T g g x) ^ 2 + c3 * (T.L g x) ^ 2 +
      c4 * (T.L g x * G T g g x) + c5 * G T g g x) ∂T.μ =
    c0 * (∫ x, Real.exp (g x) * T.toDiffusionTriple.Γ₂ g g x ∂T.μ) +
    c1 * (∫ x, Real.exp (g x) * G T g (G T g g) x ∂T.μ) +
    c2 * (∫ x, Real.exp (g x) * (G T g g x) ^ 2 ∂T.μ) +
    c3 * (∫ x, Real.exp (g x) * (T.L g x) ^ 2 ∂T.μ) +
    c4 * (∫ x, Real.exp (g x) * (T.L g x * G T g g x) ∂T.μ) +
    c5 * (∫ x, Real.exp (g x) * G T g g x ∂T.μ) := by
  have hgA := T.A₀_le g hg0
  have hu := ΓA_self_mem_A₀ T hg0
  have hl := T.L_mem g hg0
  have hv : G T g (G T g g) ∈ T.A₀ := ΓA_mem_A₀ T hgA hu
  have hu2 : (fun x => (G T g g x) ^ 2) ∈ T.A₀ := by
    have : (fun x => (G T g g x) ^ 2) = G T g g * G T g g := by funext x; simp [sq]
    rw [this]; exact T.A₀.mul_mem hu hu
  have hl2 : (fun x => (T.L g x) ^ 2) ∈ T.A₀ := by
    have : (fun x => (T.L g x) ^ 2) = T.L g * T.L g := by funext x; simp [sq]
    rw [this]; exact T.A₀.mul_mem hl hl
  have hlu : (fun x => T.L g x * G T g g x) ∈ T.A₀ := T.A₀.mul_mem hl hu
  have i0 := intW hg0 (G2_mem hg0)
  have i1 := intW hg0 hv
  have i2 := intW hg0 hu2
  have i3 := intW hg0 hl2
  have i4 := intW hg0 hlu
  have i5 := intW hg0 hu
  have e : (fun x => Real.exp (g x) * (c0 * T.toDiffusionTriple.Γ₂ g g x +
      c1 * G T g (G T g g) x + c2 * (G T g g x) ^ 2 + c3 * (T.L g x) ^ 2 +
      c4 * (T.L g x * G T g g x) + c5 * G T g g x)) = fun x =>
      c0 * (Real.exp (g x) * T.toDiffusionTriple.Γ₂ g g x) +
      c1 * (Real.exp (g x) * G T g (G T g g) x) + c2 * (Real.exp (g x) * (G T g g x) ^ 2) +
      c3 * (Real.exp (g x) * (T.L g x) ^ 2) +
      c4 * (Real.exp (g x) * (T.L g x * G T g g x)) + c5 * (Real.exp (g x) * G T g g x) := by
    funext x; ring
  rw [e, integral_add, integral_add, integral_add, integral_add, integral_add,
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
    integral_const_mul, integral_const_mul]
  all_goals first
    | exact (((((i0.const_mul _).add (i1.const_mul _)).add (i2.const_mul _)).add
        (i3.const_mul _)).add (i4.const_mul _))
    | exact ((((i0.const_mul _).add (i1.const_mul _)).add (i2.const_mul _)).add (i3.const_mul _))
    | exact (((i0.const_mul _).add (i1.const_mul _)).add (i2.const_mul _))
    | exact ((i0.const_mul _).add (i1.const_mul _))
    | exact (i0.const_mul _)
    | exact (i1.const_mul _) | exact (i2.const_mul _) | exact (i3.const_mul _)
    | exact (i4.const_mul _) | exact (i5.const_mul _)

lemma int_comb (c0 c1 c2 c3 c4 c5 : ℝ) :
    Integrable (fun x => Real.exp (g x) * (c0 * T.toDiffusionTriple.Γ₂ g g x +
      c1 * G T g (G T g g) x + c2 * (G T g g x) ^ 2 + c3 * (T.L g x) ^ 2 +
      c4 * (T.L g x * G T g g x) + c5 * G T g g x)) T.μ :=
  intW hg0 (mem_comb hg0 c0 c1 c2 c3 c4 c5)

end Integrated


section Main

variable {ρ : ℝ} {n : ℝ≥0∞}

lemma sq_mem {h : E → ℝ} (hh : h ∈ T.A₀) : (fun x => (h x) ^ 2) ∈ T.A₀ := by
  have : (fun x => (h x) ^ 2) = h * h := by funext x; simp [sq]
  rw [this]; exact T.A₀.mul_mem hh hh

/-- **(5.7.7)**: `∫ e^g Lg Γ(g) = -∫ e^g Γ(g,Γ(g)) - ∫ e^g Γ(g)²`, `g ∈ 𝒜₀` (BGL p. 271). -/
theorem integral_exp_L_Γ (hg0 : g ∈ T.A₀) :
    ∫ x, Real.exp (g x) * (T.L g x * G T g g x) ∂T.μ =
      -(∫ x, Real.exp (g x) * G T g (G T g g) x ∂T.μ) -
        ∫ x, Real.exp (g x) * (G T g g x) ^ 2 ∂T.μ := by
  have hgA := T.A₀_le g hg0
  have hu := ΓA_self_mem_A₀ T hg0
  have hv : G T g (G T g g) ∈ T.A₀ := ΓA_mem_A₀ T hgA hu
  have hk : G T g g * (fun x => Real.exp (g x)) ∈ T.A₀ := T.ideal _ (expg_mem hg0) _ hu
  have ib := (T.ibp_A g hgA _ hk).1
  have a1 := G_mul_left (T := T) (T.A₀_le _ hu) (expg_mem hg0) hgA
  have a2 := ΓA_comp_left T Real.contDiff_exp hgA hgA
  have e1 : ∫ x, G T g (G T g g * fun x => Real.exp (g x)) x ∂T.μ =
      ∫ x, (Real.exp (g x) * G T g (G T g g) x + Real.exp (g x) * (G T g g x) ^ 2) ∂T.μ := by
    refine integral_congr_ae ?_
    filter_upwards [a1, a2] with x h1 h2
    rw [congrFun (G_comm (T := T) g _) x, h1]
    have h3 : G T (fun x => Real.exp (g x)) g x = Real.exp (g x) * G T g g x := by
      have h2' := h2
      rw [Real.deriv_exp] at h2'
      exact h2'
    rw [h3, congrFun (G_comm (T := T) (G T g g) g) x]; ring
  have e2 : ∫ x, (Real.exp (g x) * G T g (G T g g) x + Real.exp (g x) * (G T g g x) ^ 2) ∂T.μ
      = (∫ x, Real.exp (g x) * G T g (G T g g) x ∂T.μ) +
        ∫ x, Real.exp (g x) * (G T g g x) ^ 2 ∂T.μ := by
    rw [integral_add (intW hg0 hv) (intW hg0 (sq_mem hu))]
  have e3 : ∫ x, (G T g g * fun x => Real.exp (g x)) x * T.L g x ∂T.μ =
      ∫ x, Real.exp (g x) * (T.L g x * G T g g x) ∂T.μ := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [Pi.mul_apply]; ring
  rw [e1, e2, e3] at ib
  linarith

/-- **(5.7.8) at `a = 1/2`**: `∫ e^g (Lg)² = ∫ e^g Γ₂(g) + 3/2 ∫ e^g Γ(g,Γ(g)) + ∫ e^g Γ(g)²`
for `g ∈ 𝒜₀` with `e^{g/2} ∈ 𝒜₀` (BGL p. 271: `∫Γ₂(e^{ag}) = ∫(Le^{ag})²`, here (3.3.8) `integral_Γ₂`). -/
theorem integral_exp_sq_L (hg0 : g ∈ T.A₀) (he : (fun x => Real.exp (g x / 2)) ∈ T.A₀) :
    ∫ x, Real.exp (g x) * (T.L g x) ^ 2 ∂T.μ =
      (∫ x, Real.exp (g x) * T.toDiffusionTriple.Γ₂ g g x ∂T.μ) +
      3 / 2 * (∫ x, Real.exp (g x) * G T g (G T g g) x ∂T.μ) +
        ∫ x, Real.exp (g x) * (G T g g x) ^ 2 ∂T.μ := by
  have hgA := T.A₀_le g hg0
  have hMc := M_comb hg0
  have hibp := integral_exp_L_Γ hg0
  have hf : (fun x => Real.exp (g x / 2)) = Pw g 1 (1 / 2) := by
    funext x; simp [Pw]; ring_nf
  rw [hf] at he
  have h338 := integral_Γ₂ T he
  have a1 := Γ₂_Pw hgA (1 / 2)
  have a2 := L_Pw hgA 1 (1 / 2)
  have l1 : ∫ x, T.toDiffusionTriple.Γ₂ (Pw g 1 (1 / 2)) (Pw g 1 (1 / 2)) x ∂T.μ =
      ∫ x, Real.exp (g x) * ((1 / 4) * T.toDiffusionTriple.Γ₂ g g x +
        (1 / 8) * G T g (G T g g) x + (1 / 16) * (G T g g x) ^ 2 + 0 * (T.L g x) ^ 2 +
        0 * (T.L g x * G T g g x) + 0 * G T g g x) ∂T.μ := by
    refine integral_congr_ae ?_
    filter_upwards [a1] with x hx
    rw [hx]
    have : 2 * (1 / 2 : ℝ) * g x = g x := by ring
    rw [this]; ring
  have l2 : ∫ x, T.L (Pw g 1 (1 / 2)) x * T.L (Pw g 1 (1 / 2)) x ∂T.μ =
      ∫ x, Real.exp (g x) * (0 * T.toDiffusionTriple.Γ₂ g g x +
        0 * G T g (G T g g) x + (1 / 16) * (G T g g x) ^ 2 + (1 / 4) * (T.L g x) ^ 2 +
        (1 / 4) * (T.L g x * G T g g x) + 0 * G T g g x) ∂T.μ := by
    refine integral_congr_ae ?_
    filter_upwards [a2] with x hx
    rw [hx]
    have h1 : Real.exp (1 / 2 * g x) * Real.exp (1 / 2 * g x) = Real.exp (g x) := by
      rw [← Real.exp_add]; congr 1; ring
    calc _ = (Real.exp (1 / 2 * g x) * Real.exp (1 / 2 * g x)) *
          ((1 / 4) * (T.L g x) ^ 2 + (1 / 4) * (T.L g x * G T g g x) +
          (1 / 16) * (G T g g x) ^ 2) := by
            show (1 * (1 / 2 : ℝ) * Real.exp (1 / 2 * g x) * T.L g x +
              1 * (1 / 2) * (1 / 2) * Real.exp (1 / 2 * g x) * G T g g x) *
              (1 * (1 / 2 : ℝ) * Real.exp (1 / 2 * g x) * T.L g x +
              1 * (1 / 2) * (1 / 2) * Real.exp (1 / 2 * g x) * G T g g x) = _
            ring
      _ = _ := by rw [h1]; ring
  rw [l1, l2, hMc, hMc] at h338
  linarith

/-- **BGL (5.7.10)-(5.7.11)** (pp. 271-272) for `g ∈ 𝒜₀`, `CD(ρ,n)`, `1 < n < ∞`, `m = n`:
`ρ n/(n-1) ∫ e^g Γ(g) + (4n-1)/(4(n+2)²) ∫ e^g Γ(g)² ≤ ∫ e^g Γ₂(g)`.
The hypothesis `he` (`e^{g/2} ∈ 𝒜₀`) is what the book's Prop. 3.3.17 provides for `e^{ag}`, `g ∈ 𝒜₀`
(`∫Γ₂(e^{g/2}) = ∫(L e^{g/2})²`, here `integral_Γ₂`); on compact triples it is automatic. -/
theorem integral_exp_Γ₂_ge (hCD : T.CD ρ n) (hn1 : 1 < n) (hn : n ≠ ⊤) (hg0 : g ∈ T.A₀)
    (he : (fun x => Real.exp (g x / 2)) ∈ T.A₀) :
    ρ * (n.toReal / (n.toReal - 1)) * ∫ x, Real.exp (g x) * G T g g x ∂T.μ +
      (4 * n.toReal - 1) / (4 * (n.toReal + 2) ^ 2) *
        ∫ x, Real.exp (g x) * (G T g g x) ^ 2 ∂T.μ ≤
      ∫ x, Real.exp (g x) * T.toDiffusionTriple.Γ₂ g g x ∂T.μ := by
  have hgA := T.A₀_le g hg0
  have hm1 : 1 < n.toReal := by
    have := (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hn).2 hn1
    simpa using this
  have hn' : (n⁻¹).toReal = (n.toReal)⁻¹ := ENNReal.toReal_inv n
  generalize hm : n.toReal = m at hm1 hn' ⊢
  have hMc := M_comb hg0
  have hibp := integral_exp_L_Γ hg0
  have hW := integral_exp_sq_L hg0 he
  have hmpos : 0 < m := by linarith
  -- the parameter a
  obtain ⟨a, ha_def⟩ : ∃ a : ℝ, a = 3 / (2 * (m + 2)) := ⟨_, rfl⟩
  have hapos : 0 < a := by rw [ha_def]; positivity
  have ha : a * (m + 2) = 3 / 2 := by rw [ha_def]; field_simp
  -- pointwise curvature inequality for e^{ag}
  have hfA : Pw g 1 a ∈ T.A := Pw_mem hgA 1 a
  have q0 := hCD.2 _ hfA
  have q1 := ΓA_comp_comp T (contDiff_kexp 1 a) hgA
  have q2 := L_Pw hgA 1 a
  have q3 := Γ₂_Pw hgA a
  have hpt : ∀ᵐ x ∂T.μ, Real.exp (g x) * (0 * T.toDiffusionTriple.Γ₂ g g x +
        0 * G T g (G T g g) x + a ^ 2 * (G T g g x) ^ 2 + 1 * (T.L g x) ^ 2 +
        (2 * a) * (T.L g x * G T g g x) + (m * ρ) * G T g g x) ≤
      Real.exp (g x) * (m * T.toDiffusionTriple.Γ₂ g g x +
        (m * a) * G T g (G T g g) x + (m * a ^ 2) * (G T g g x) ^ 2 + 0 * (T.L g x) ^ 2 +
        0 * (T.L g x * G T g g x) + 0 * G T g g x) := by
    filter_upwards [q0, q1, q2, q3] with x h0 h1 h2 h3
    have h1' : G T (Pw g 1 a) (Pw g 1 a) x = (1 * a * Real.exp (a * g x)) ^ 2 * G T g g x := by
      have := h1
      simp only [deriv_kexp] at this
      exact this
    have hΓ : T.toDiffusionTriple.ΓA (Pw g 1 a) (Pw g 1 a) x =
        (1 * a * Real.exp (a * g x)) ^ 2 * G T g g x := h1'
    rw [hΓ, hn', h2, h3] at h0
    have hex : Real.exp (2 * a * g x) = Real.exp (a * g x) ^ 2 := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [hex] at h0
    have hK : 0 < a ^ 2 * Real.exp (a * g x) ^ 2 := by positivity
    have h4 := mul_le_mul_of_nonneg_left h0 hmpos.le
    have h5 : m * (ρ * ((1 * a * Real.exp (a * g x)) ^ 2 * G T g g x) + m⁻¹ *
        (1 * a * Real.exp (a * g x) * T.L g x +
          1 * a * a * Real.exp (a * g x) * T.toDiffusionTriple.ΓA g g x) ^ 2) =
        a ^ 2 * Real.exp (a * g x) ^ 2 * (m * ρ * G T g g x +
          (T.L g x + a * G T g g x) ^ 2) := by
      have : m * m⁻¹ = 1 := mul_inv_cancel₀ hmpos.ne'
      calc _ = m * ρ * ((1 * a * Real.exp (a * g x)) ^ 2 * G T g g x) +
            (m * m⁻¹) * (1 * a * Real.exp (a * g x) * T.L g x +
          1 * a * a * Real.exp (a * g x) * G T g g x) ^ 2 := by
              show m * (ρ * _ + m⁻¹ * (_ + _ * G T g g x) ^ 2) = _; ring
        _ = _ := by rw [this]; ring
    have h6 : m * (a ^ 2 * Real.exp (a * g x) ^ 2 * (T.toDiffusionTriple.Γ₂ g g x +
        a * G T g (G T g g) x + a ^ 2 * (G T g g x) ^ 2)) =
        a ^ 2 * Real.exp (a * g x) ^ 2 * (m * T.toDiffusionTriple.Γ₂ g g x +
        (m * a) * G T g (G T g g) x + (m * a ^ 2) * (G T g g x) ^ 2) := by ring
    rw [h5, h6] at h4
    have h7 : m * ρ * G T g g x + (T.L g x + a * G T g g x) ^ 2 ≤
        m * T.toDiffusionTriple.Γ₂ g g x + (m * a) * G T g (G T g g) x +
          (m * a ^ 2) * (G T g g x) ^ 2 := le_of_mul_le_mul_left h4 hK
    have h8 := mul_le_mul_of_nonneg_left h7 (Real.exp_pos (g x)).le
    refine le_trans (le_of_eq ?_) (le_trans h8 (le_of_eq ?_)) <;> ring
  have hint := integral_mono_ae (int_comb hg0 0 0 (a ^ 2) 1 (2 * a) (m * ρ))
    (int_comb hg0 m (m * a) (m * a ^ 2) 0 0 0) hpt
  rw [hMc, hMc] at hint
  -- algebra
  have t1 : (3 / 2 - (m + 2) * a) * (∫ x, Real.exp (g x) * G T g (G T g g) x ∂T.μ) = 0 := by
    rw [show 3 / 2 - (m + 2) * a = 0 by linarith, zero_mul]
  have t2 : a * (∫ x, Real.exp (g x) * (T.L g x * G T g g x) ∂T.μ) =
      a * (-(∫ x, Real.exp (g x) * G T g (G T g g) x ∂T.μ) -
        ∫ x, Real.exp (g x) * (G T g g x) ^ 2 ∂T.μ) := by rw [hibp]
  have key : (m - 1) * (∫ x, Real.exp (g x) * T.toDiffusionTriple.Γ₂ g g x ∂T.μ) ≥
      m * ρ * (∫ x, Real.exp (g x) * G T g g x ∂T.μ) +
        ((1 - a) ^ 2 - m * a ^ 2) * ∫ x, Real.exp (g x) * (G T g g x) ^ 2 ∂T.μ := by
    nlinarith [hint, t1, t2, hW, hibp]
  have hm1pos : 0 < m - 1 := by linarith
  have hZc : (4 * m - 1) / (4 * (m + 2) ^ 2) * (m - 1) = (1 - a) ^ 2 - m * a ^ 2 := by
    rw [ha_def]; field_simp; ring
  rw [← mul_le_mul_iff_right₀ hm1pos]
  have e : (m - 1) * (ρ * (m / (m - 1)) * (∫ x, Real.exp (g x) * G T g g x ∂T.μ) +
      (4 * m - 1) / (4 * (m + 2) ^ 2) * ∫ x, Real.exp (g x) * (G T g g x) ^ 2 ∂T.μ) =
      m * ρ * (∫ x, Real.exp (g x) * G T g g x ∂T.μ) +
        ((4 * m - 1) / (4 * (m + 2) ^ 2) * (m - 1)) *
          ∫ x, Real.exp (g x) * (G T g g x) ^ 2 ∂T.μ := by
    field_simp
  rw [e, hZc]
  linarith [key]

/-- **BGL (5.7.12)** (p. 272): `ρ n/(n-1) ∫ e^g Γ(g) ≤ ∫ e^g Γ₂(g)`. -/
theorem integral_exp_Γ₂_ge' (hCD : T.CD ρ n) (hn1 : 1 < n) (hn : n ≠ ⊤) (hg0 : g ∈ T.A₀)
    (he : (fun x => Real.exp (g x / 2)) ∈ T.A₀) :
    ρ * (n.toReal / (n.toReal - 1)) * ∫ x, Real.exp (g x) * G T g g x ∂T.μ ≤
      ∫ x, Real.exp (g x) * T.toDiffusionTriple.Γ₂ g g x ∂T.μ := by
  have h := integral_exp_Γ₂_ge hCD hn1 hn hg0 he
  have hm1 : 1 < n.toReal := by
    have := (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hn).2 hn1
    simpa using this
  have hZ : 0 ≤ (4 * n.toReal - 1) / (4 * (n.toReal + 2) ^ 2) *
      ∫ x, Real.exp (g x) * (G T g g x) ^ 2 ∂T.μ := by
    refine mul_nonneg (div_nonneg (by linarith) (by positivity)) ?_
    exact integral_nonneg fun x => mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
  linarith

end Main

end FullTriple

end MarkovTriple.BGL
