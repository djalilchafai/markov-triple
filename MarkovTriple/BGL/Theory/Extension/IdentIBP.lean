import Mathlib
import MarkovTriple.BGL.Theory.Extension.HessLin
import MarkovTriple.BGL.Theory.Extension.ClosedDetect

/-!
# Integration by parts for Hessians (BGL (3.3.5), used in the proof of Prop. 3.3.17, p. 161)

For `f ∈ 𝒜` (not only `𝒜₀`) and test functions `g, h, k ∈ 𝒜₀`:
`∫ k H(f)(g,h) dμ = ½ ∫ f · E(g,h,k) dμ`, with `E(g,h,k) ∈ 𝒜₀` explicit.  This is the book's "reduced to an
integral of the form `∫ f E(g,h,k)` where `E(g,h,k)` (even if tedious to write down explicitly) belongs to `𝒜₀`"; we
write it down.  Only F1 (ideal property), F6 (chain rule in the form `G_mul_left`) and F7 (integration by parts) are
used.
-/

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal InnerProductSpace

namespace MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E]

namespace FullTriple

variable {T : FullTriple E}

lemma mulA₀ {u v : E → ℝ} (hu : u ∈ T.A) (hv : v ∈ T.A₀) : (fun x => u x * v x) ∈ T.A₀ := by
  have := T.ideal u hu v hv
  have e : (fun x => u x * v x) = v * u := by funext x; simp [mul_comm]
  rw [e]; exact this

lemma mulA₀' {u v : E → ℝ} (hu : u ∈ T.A₀) (hv : v ∈ T.A₀) : (fun x => u x * v x) ∈ T.A₀ :=
  T.A₀.mul_mem hu hv

lemma intA₀ {u : E → ℝ} (hu : u ∈ T.A₀) : Integrable u T.μ := integrable_A₀ hu

lemma G_memA₀ {f h : E → ℝ} (hf : f ∈ T.A) (hh : h ∈ T.A₀) : G T f h ∈ T.A₀ := ΓA_mem_A₀ T hf hh

lemma G_memA₀' {f h : E → ℝ} (hf : f ∈ T.A₀) (hh : h ∈ T.A) : G T f h ∈ T.A₀ := by
  rw [G_comm]; exact ΓA_mem_A₀ T hh hf

lemma L_memA₀ {f : E → ℝ} (hf : f ∈ T.A₀) : T.L f ∈ T.A₀ := T.L_mem f hf

/-- **Basic integration by parts.**  For `f ∈ 𝒜`, `a, b ∈ 𝒜₀`:
`∫ a Γ(f,b) = −∫ f (a L b + Γ(a,b))`. -/
lemma int_mul_G {f a b : E → ℝ} (hf : f ∈ T.A) (ha : a ∈ T.A₀) (hb : b ∈ T.A₀) :
    ∫ x, a x * G T f b x ∂T.μ = -∫ x, f x * (a x * T.L b x + G T a b x) ∂T.μ := by
  have haA := A₀_memA ha
  have hq : a * f ∈ T.A₀ := T.ideal f hf a ha
  have e1 := G_mul_left haA hf (A₀_memA hb)
  have h7 := (T.ibp_A (a * f) (A₀_memA hq) b hb).2
  have i1 : Integrable (fun x => a x * G T f b x) T.μ := intA₀ (mulA₀' ha (G_memA₀ hf hb))
  have i2 : Integrable (fun x => f x * G T a b x) T.μ := intA₀ (mulA₀ hf (G_memA₀ haA hb))
  have i3 : Integrable (fun x => f x * (a x * T.L b x)) T.μ :=
    intA₀ (mulA₀ hf (mulA₀' ha (L_memA₀ hb)))
  have e2 : ∫ x, G T (a * f) b x ∂T.μ = ∫ x, a x * G T f b x ∂T.μ + ∫ x, f x * G T a b x ∂T.μ := by
    rw [← integral_add i1 i2]
    exact integral_congr_ae e1
  have e3 : ∫ x, (a * f) x * T.L b x ∂T.μ = ∫ x, f x * (a x * T.L b x) ∂T.μ :=
    integral_congr_ae (Eventually.of_forall fun x => by simp only [Pi.mul_apply]; ring)
  have e4 : ∫ x, f x * (a x * T.L b x + G T a b x) ∂T.μ =
      ∫ x, f x * (a x * T.L b x) ∂T.μ + ∫ x, f x * G T a b x ∂T.μ := by
    rw [← integral_add i3 i2]
    exact integral_congr_ae (Eventually.of_forall fun x => by ring)
  rw [e4]
  linarith [e2, h7, e3]

/-- `c₁ = k L g + Γ(k,g)`. -/
noncomputable def cc (T : FullTriple E) (g k : E → ℝ) : E → ℝ := fun x => k x * T.L g x + G T k g x

lemma cc_memA₀ {g k : E → ℝ} (hg : g ∈ T.A₀) (hk : k ∈ T.A₀) : cc T g k ∈ T.A₀ := by
  unfold cc
  have : (fun x => k x * T.L g x + G T k g x) = (fun x => k x * T.L g x) + G T k g := by
    funext x; simp
  rw [this]
  exact T.A₀.add_mem (mulA₀' hk (L_memA₀ hg)) (G_memA₀ (A₀_memA hk) hg)

/-- `∫ k Γ(g, Γ(f,h)) = ∫ f · (c₁ L h + Γ(c₁,h))`, `c₁ = k L g + Γ(k,g)`. -/
lemma int_k_GG {f g h k : E → ℝ} (hf : f ∈ T.A) (hg : g ∈ T.A₀) (hh : h ∈ T.A₀) (hk : k ∈ T.A₀) :
    ∫ x, k x * G T g (G T f h) x ∂T.μ =
      ∫ x, f x * (cc T g k x * T.L h x + G T (cc T g k) h x) ∂T.μ := by
  have hw : G T f h ∈ T.A₀ := G_memA₀ hf hh
  have hc := cc_memA₀ hg hk
  have s1 := int_mul_G (A₀_memA hw) hk hg
  have s2 := int_mul_G hf hc hh
  calc ∫ x, k x * G T g (G T f h) x ∂T.μ = ∫ x, k x * G T (G T f h) g x ∂T.μ := by
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        rw [G_comm g (G T f h)]
    _ = -∫ x, G T f h x * (k x * T.L g x + G T k g x) ∂T.μ := s1
    _ = -∫ x, cc T g k x * G T f h x ∂T.μ := by
        congr 1
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        simp only [cc]; ring
    _ = ∫ x, f x * (cc T g k x * T.L h x + G T (cc T g k) h x) ∂T.μ := by
        rw [s2, neg_neg]

/-- the test function `E(g,h,k)` of BGL p. 161 (explicit). -/
noncomputable def E3 (T : FullTriple E) (g h k : E → ℝ) : E → ℝ := fun x =>
  (cc T g k x * T.L h x + G T (cc T g k) h x) + (cc T h k x * T.L g x + G T (cc T h k) g x) +
    (k x * T.L (G T g h) x + G T k (G T g h) x)

lemma E3_memA₀ {g h k : E → ℝ} (hg : g ∈ T.A₀) (hh : h ∈ T.A₀) (hk : k ∈ T.A₀) : E3 T g h k ∈ T.A₀ := by
  have hm : G T g h ∈ T.A₀ := G_memA₀ (A₀_memA hg) hh
  have c1 := cc_memA₀ hg hk
  have c2 := cc_memA₀ hh hk
  have t1 : (fun x => cc T g k x * T.L h x + G T (cc T g k) h x) ∈ T.A₀ :=
    T.A₀.add_mem (mulA₀' c1 (L_memA₀ hh)) (G_memA₀ (A₀_memA c1) hh)
  have t2 : (fun x => cc T h k x * T.L g x + G T (cc T h k) g x) ∈ T.A₀ :=
    T.A₀.add_mem (mulA₀' c2 (L_memA₀ hg)) (G_memA₀ (A₀_memA c2) hg)
  have t3 : (fun x => k x * T.L (G T g h) x + G T k (G T g h) x) ∈ T.A₀ :=
    T.A₀.add_mem (mulA₀' hk (L_memA₀ hm)) (G_memA₀ (A₀_memA hk) hm)
  exact T.A₀.add_mem (T.A₀.add_mem t1 t2) t3

/-- **BGL (3.3.5), extended to `f ∈ 𝒜`**: `∫ k H(f)(g,h) = ½ ∫ f E(g,h,k)` for `g,h,k ∈ 𝒜₀`. -/
theorem int_mul_Hess {f g h k : E → ℝ} (hf : f ∈ T.A) (hg : g ∈ T.A₀) (hh : h ∈ T.A₀)
    (hk : k ∈ T.A₀) :
    ∫ x, k x * Hess T f g h x ∂T.μ = (1 / 2 : ℝ) * ∫ x, f x * E3 T g h k x ∂T.μ := by
  have hm : G T g h ∈ T.A₀ := G_memA₀ (A₀_memA hg) hh
  have hfg : G T f g ∈ T.A₀ := G_memA₀ hf hg
  have hfh : G T f h ∈ T.A₀ := G_memA₀ hf hh
  have A1 := int_k_GG hf hg hh hk
  have B1 := int_k_GG hf hh hg hk
  have C1 := int_mul_G hf hk hm
  have j1 : Integrable (fun x => k x * G T g (G T f h) x) T.μ :=
    intA₀ (mulA₀' hk (G_memA₀ (A₀_memA hg) hfh))
  have j2 : Integrable (fun x => k x * G T h (G T f g) x) T.μ :=
    intA₀ (mulA₀' hk (G_memA₀ (A₀_memA hh) hfg))
  have j3 : Integrable (fun x => k x * G T f (G T g h) x) T.μ :=
    intA₀ (mulA₀' hk (G_memA₀ hf hm))
  have c1 := cc_memA₀ hg hk
  have c2 := cc_memA₀ hh hk
  have u1 : Integrable (fun x => f x * (cc T g k x * T.L h x + G T (cc T g k) h x)) T.μ :=
    intA₀ (mulA₀ hf (T.A₀.add_mem (mulA₀' c1 (L_memA₀ hh)) (G_memA₀ (A₀_memA c1) hh)))
  have u2 : Integrable (fun x => f x * (cc T h k x * T.L g x + G T (cc T h k) g x)) T.μ :=
    intA₀ (mulA₀ hf (T.A₀.add_mem (mulA₀' c2 (L_memA₀ hg)) (G_memA₀ (A₀_memA c2) hg)))
  have u3 : Integrable (fun x => f x * (k x * T.L (G T g h) x + G T k (G T g h) x)) T.μ :=
    intA₀ (mulA₀ hf (T.A₀.add_mem (mulA₀' hk (L_memA₀ hm)) (G_memA₀ (A₀_memA hk) hm)))
  have lhs : ∫ x, k x * Hess T f g h x ∂T.μ = (1 / 2 : ℝ) *
      (∫ x, k x * G T g (G T f h) x ∂T.μ + ∫ x, k x * G T h (G T f g) x ∂T.μ -
        ∫ x, k x * G T f (G T g h) x ∂T.μ) := by
    have j12 : Integrable (fun x => k x * G T g (G T f h) x + k x * G T h (G T f g) x) T.μ := j1.add j2
    rw [← integral_add j1 j2, ← integral_sub j12 j3, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [Hess]; ring
  have rhs : ∫ x, f x * E3 T g h k x ∂T.μ =
      ∫ x, f x * (cc T g k x * T.L h x + G T (cc T g k) h x) ∂T.μ +
        ∫ x, f x * (cc T h k x * T.L g x + G T (cc T h k) g x) ∂T.μ +
        ∫ x, f x * (k x * T.L (G T g h) x + G T k (G T g h) x) ∂T.μ := by
    have u12 : Integrable (fun x => f x * (cc T g k x * T.L h x + G T (cc T g k) h x) +
        f x * (cc T h k x * T.L g x + G T (cc T h k) g x)) T.μ := u1.add u2
    rw [← integral_add u1 u2, ← integral_add u12 u3]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [E3]; ring
  rw [lhs, rhs, A1, B1]
  have : ∫ x, k x * G T f (G T g h) x ∂T.μ =
      -∫ x, f x * (k x * T.L (G T g h) x + G T k (G T g h) x) ∂T.μ := C1
  rw [this]
  ring

end FullTriple

end MarkovTriple.BGL
