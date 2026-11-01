import Mathlib
import MarkovTriple.BGL.Theory.Compact.Algebra

/-!
# `GradientInterpolation` for every compact triple (BGL Lemmas 3.3.20–3.3.21 for `𝒜 = 𝒜₀`)

For `f, h ∈ 𝒜₀` and `G_s = P_{t-s}[f]`, `K_s = P_s[h]` (so `K_s, G_s ∈ 𝒜₀` and all integrations by
parts are the D5/F7 ones with test functions), integrating by parts once gives
`Φ(s) = ∫ K_s Γ(G_s) = ½ ∫ L K_s · G_s² − ∫ K_s G_s L G_s`, a combination of triple products of
`L²`-differentiable, uniformly bounded curves; the Leibniz rule `Compact.tri_hasDerivAt` and the algebra
of `Algebra.lean` give `Φ' = 2 ∫ K_s Γ₂(G_s)`.
-/

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal
open MarkovTriple.BGL.Compact

namespace MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E]

namespace CompactTriple

variable (C : CompactTriple E)

/-- `L (L (P_s ψ)) = P_s (L Lψ)`. -/
lemma L_Pt2 (ψ : C.A₀) (s : ℝ) :
    C.L (C.L (C.Pt s.toNNReal ψ)) =ᵐ[C.μ] (C.orb (C.Lt (C.Lt ψ)) s : E → ℝ) := by
  have h1 := C.L_Pt ψ s
  have h2 : C.L (C.L (C.Pt s.toNNReal ψ)) =ᵐ[C.μ] C.L (C.Pt s.toNNReal (C.Lt ψ)) := by
    refine C.L_congr_A (C.L_mem_A _ (C.Pt_mem_A _ ψ)) (C.Pt_mem_A _ _) ?_
    exact h1.trans (C.orb_ae (C.Lt ψ) s)
  exact h2.trans (C.L_Pt (C.Lt ψ) s)

/-- the expression of `Φ` in terms of triple products. -/
theorem gradPhi_eq (f h : C.A₀) (t : ℝ≥0) (s : ℝ) :
    C.gradPhi f h t s = (1 / 2) * tri (C.orb (C.Lt h) s) (C.orb f (t - s)) (C.orb f (t - s)) -
      tri (C.orb h s) (C.orb f (t - s)) (C.orb (C.Lt f) (t - s)) := by
  set k := C.Pt s.toNNReal h with hk
  set g := C.Pt ((t : ℝ) - s).toNNReal f with hg
  have hk0 : k ∈ C.A₀ := C.Pt_mem _ h
  have hg0 : g ∈ C.A₀ := C.Pt_mem _ f
  have hLk := C.Lm hk0
  have hLg := C.Lm hg0
  have hgg : g * g ∈ C.A₀ := C.A₀.mul_mem hg0 hg0
  have e1 : tri (C.orb (C.Lt h) s) (C.orb f (t - s)) (C.orb f (t - s)) =
      ∫ x, C.L k x * g x * g x ∂C.μ :=
    tri_ae ((C.L_Pt h s).symm) (C.orb_ae f _) (C.orb_ae f _)
  have e2 : tri (C.orb h s) (C.orb f (t - s)) (C.orb (C.Lt f) (t - s)) =
      ∫ x, k x * g x * C.L g x ∂C.μ :=
    tri_ae (C.orb_ae h _) (C.orb_ae f _) ((C.L_Pt f _).symm)
  rw [e1, e2]
  unfold FullTriple.gradPhi
  have p : ∀ x, k x * C.toDiffusionTriple.ΓA g g x =
      (1 / 2) * (k x * C.L (g * g) x) - k x * g x * C.L g x := by
    intro x; simp only [DiffusionTriple.ΓA]; ring
  have q1 := C.i2 hk0 (C.Lm hgg)
  have q2 := C.i3 hk0 hg0 hLg
  have s1 : ∫ x, k x * C.L (g * g) x ∂C.μ = ∫ x, C.L k x * g x * g x ∂C.μ := by
    rw [C.sym hk0 hgg]
    exact integral_congr_ae (Eventually.of_forall fun x => by simp only [Pi.mul_apply]; ring)
  show ∫ x, k x * C.toDiffusionTriple.ΓA g g x ∂C.μ = _
  rw [integral_congr_ae (Eventually.of_forall p), integral_sub (q1.const_mul _) q2,
    integral_const_mul, s1]

lemma hasDerivAt_orb_comp (χ : C.A₀) (t : ℝ) {s : ℝ} (hs : 0 < t - s) :
    HasDerivAt (fun r => C.orb χ (t - r)) (-(C.orb (C.Lt χ) (t - s))) s := by
  have h := (C.hasDerivAt_orb χ hs).scomp s ((hasDerivAt_id s).const_sub t)
  convert h using 1
  · rfl
  · exact (neg_one_smul ℝ _).symm

lemma orb_bdd' (ψ : C.A₀) : ∃ c : ℝ, 0 < c ∧ ∀ s, Bdd c (C.orb ψ s) := by
  obtain ⟨c, hc, h⟩ := C.exists_bound ψ
  exact ⟨c, hc, fun s => C.orb_bdd hc h s⟩

/-- **The derivative of `Φ`**, for `0 < s < t`. -/
theorem hasDerivAt_gradPhi (f h : C.A₀) (t : ℝ≥0) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) (t : ℝ)) :
    HasDerivAt (C.gradPhi f h t) (2 * ∫ x, C.Pt s.toNNReal h x *
      C.toDiffusionTriple.Γ₂ (C.Pt ((t : ℝ) - s).toNNReal f) (C.Pt ((t : ℝ) - s).toNNReal f) x
        ∂C.μ) s := by
  have hts : 0 < (t : ℝ) - s := by linarith [hs.2]
  obtain ⟨c1, hc1, b1⟩ := C.orb_bdd' h
  obtain ⟨c2, hc2, b2⟩ := C.orb_bdd' (C.Lt h)
  obtain ⟨c3, hc3, b3⟩ := C.orb_bdd' f
  obtain ⟨c4, hc4, b4⟩ := C.orb_bdd' (C.Lt f)
  set M := c1 + c2 + c3 + c4 with hM
  have hM0 : 0 ≤ M := by positivity
  have mono : ∀ {c : ℝ} {u : Lp ℝ 2 C.μ}, Bdd c u → c ≤ M → Bdd M u := fun hu hc =>
    hu.mono fun x hx => hx.trans hc
  have B1 : ∀ r, Bdd M (C.orb h r) := fun r => mono (b1 r) (by linarith)
  have B2 : ∀ r, Bdd M (C.orb (C.Lt h) r) := fun r => mono (b2 r) (by linarith)
  have B3 : ∀ r, Bdd M (C.orb f (t - r)) := fun r => mono (b3 _) (by linarith)
  have B4 : ∀ r, Bdd M (C.orb (C.Lt f) (t - r)) := fun r => mono (b4 _) (by linarith)
  have dK := C.hasDerivAt_orb h hs.1
  have dLK := C.hasDerivAt_orb (C.Lt h) hs.1
  have dG := C.hasDerivAt_orb_comp f t hts
  have dLG := C.hasDerivAt_orb_comp (C.Lt f) t hts
  have d1 := tri_hasDerivAt hM0 dLK dG dG B2 B3 B3
  have d2 := tri_hasDerivAt hM0 dK dG dLG B1 B3 B4
  have hfun : C.gradPhi f h t = fun r => (1 / 2) * tri (C.orb (C.Lt h) r) (C.orb f (t - r))
      (C.orb f (t - r)) - tri (C.orb h r) (C.orb f (t - r)) (C.orb (C.Lt f) (t - r)) :=
    funext fun r => C.gradPhi_eq f h t r
  rw [hfun]
  refine ((d1.const_mul (1 / 2)).sub d2).congr_deriv ?_
  -- identification of the derivative
  set k := C.Pt s.toNNReal h with hk
  set g := C.Pt ((t : ℝ) - s).toNNReal f with hg
  have hk0 : k ∈ C.A₀ := C.Pt_mem _ h
  have hg0 : g ∈ C.A₀ := C.Pt_mem _ f
  have a0 : (C.orb (C.Lt (C.Lt h)) s : E → ℝ) =ᵐ[C.μ] C.L (C.L k) := (C.L_Pt2 h s).symm
  have a1 : (C.orb (C.Lt h) s : E → ℝ) =ᵐ[C.μ] C.L k := (C.L_Pt h s).symm
  have a2 : (C.orb h s : E → ℝ) =ᵐ[C.μ] k := C.orb_ae h s
  have b0 : (C.orb f (t - s) : E → ℝ) =ᵐ[C.μ] g := C.orb_ae f _
  have b1' : (C.orb (C.Lt f) (t - s) : E → ℝ) =ᵐ[C.μ] C.L g := (C.L_Pt f _).symm
  have b2' : (C.orb (C.Lt (C.Lt f)) (t - s) : E → ℝ) =ᵐ[C.μ] C.L (C.L g) :=
    (C.L_Pt2 f _).symm
  have T1 := tri_ae a0 b0 b0
  have T2 : tri (C.orb (C.Lt h) s) (-(C.orb (C.Lt f) (t - s))) (C.orb f (t - s)) =
      -∫ x, C.L k x * C.L g x * g x ∂C.μ := by
    rw [tri_neg_mid, tri_ae a1 b1' b0]
  have T3 : tri (C.orb (C.Lt h) s) (C.orb f (t - s)) (-(C.orb (C.Lt f) (t - s))) =
      -∫ x, C.L k x * g x * C.L g x ∂C.μ := by
    rw [tri_neg_right, tri_ae a1 b0 b1']
  have T4 := tri_ae a1 b0 b1'
  have T5 : tri (C.orb h s) (-(C.orb (C.Lt f) (t - s))) (C.orb (C.Lt f) (t - s)) =
      -∫ x, k x * C.L g x * C.L g x ∂C.μ := by
    rw [tri_neg_mid, tri_ae a2 b1' b1']
  have T6 : tri (C.orb h s) (C.orb f (t - s)) (-(C.orb (C.Lt (C.Lt f)) (t - s))) =
      -∫ x, k x * g x * C.L (C.L g) x ∂C.μ := by
    rw [tri_neg_right, tri_ae a2 b0 b2']
  have q : ∫ x, C.L k x * C.L g x * g x ∂C.μ = ∫ x, C.L k x * g x * C.L g x ∂C.μ :=
    integral_congr_ae (Eventually.of_forall fun x => by ring)
  have alg := C.two_int_Γ₂ hk0 hg0
  rw [T2, T3, T5, T6] at *
  simp only [T1, T4] at *
  linarith

lemma Γ₂_mem {g : E → ℝ} (hg : g ∈ C.A₀) : C.toDiffusionTriple.Γ₂ g g ∈ C.A₀ := by
  have h1 := C.Lm (C.ΓA_self_mem_A₀ hg)
  have h2 := C.ΓA_mem_A₀ (C.A₀_le g hg) (C.Lm hg)
  have h3 := C.ΓA_mem_A₀ (C.A₀_le _ (C.Lm hg)) hg
  have : C.toDiffusionTriple.Γ₂ g g = (1 / 2 : ℝ) • (C.L (C.toDiffusionTriple.ΓA g g) -
      C.toDiffusionTriple.ΓA g (C.L g) - C.toDiffusionTriple.ΓA (C.L g) g) := by
    funext x
    simp only [DiffusionTriple.Γ₂, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  rw [this]
  exact C.A₀.smul_mem _ (C.A₀.sub_mem (C.A₀.sub_mem h1 h2) h3)

lemma continuous_gradPhi (f h : C.A₀) (t : ℝ≥0) : Continuous (C.gradPhi f h t) := by
  obtain ⟨c1, hc1, b1⟩ := C.orb_bdd' h
  obtain ⟨c2, hc2, b2⟩ := C.orb_bdd' (C.Lt h)
  obtain ⟨c3, hc3, b3⟩ := C.orb_bdd' f
  obtain ⟨c4, hc4, b4⟩ := C.orb_bdd' (C.Lt f)
  set M := c1 + c2 + c3 + c4 with hM
  have hM0 : 0 ≤ M := by positivity
  have mono : ∀ {c : ℝ} {u : Lp ℝ 2 C.μ}, Bdd c u → c ≤ M → Bdd M u := fun hu hc =>
    hu.mono fun x hx => hx.trans hc
  have hfun : C.gradPhi f h t = fun r => (1 / 2) * tri (C.orb (C.Lt h) r) (C.orb f (t - r))
      (C.orb f (t - r)) - tri (C.orb h r) (C.orb f (t - r)) (C.orb (C.Lt f) (t - r)) :=
    funext fun r => C.gradPhi_eq f h t r
  rw [hfun, continuous_iff_continuousAt]
  intro s
  have cG : ContinuousAt (fun r : ℝ => C.orb f (t - r)) s :=
    ((C.continuous_orb f).comp (continuous_const.sub continuous_id)).continuousAt
  have cLG : ContinuousAt (fun r : ℝ => C.orb (C.Lt f) (t - r)) s :=
    ((C.continuous_orb (C.Lt f)).comp (continuous_const.sub continuous_id)).continuousAt
  have c1' := tri_continuousAt hM0 (C.continuous_orb (C.Lt h)).continuousAt cG cG
    (fun r => mono (b3 _) (by linarith)) (fun r => mono (b3 _) (by linarith))
  have c2' := tri_continuousAt hM0 (C.continuous_orb h).continuousAt cG cLG
    (fun r => mono (b3 _) (by linarith)) (fun r => mono (b4 _) (by linarith))
  exact (c1'.const_mul (1 / 2)).sub c2'

/-- **`GradientInterpolation` holds for every compact triple.** -/
theorem gradientInterpolation : C.toFullTriple.GradientInterpolation where
  continuousOn := fun f h _ t => (C.continuous_gradPhi f h t).continuousOn
  hasDerivAt := fun f h _ t s hs => by
    have hk0 : C.Pt s.toNNReal h ∈ C.A₀ := C.Pt_mem _ h
    have hg0 : C.Pt ((t : ℝ) - s).toNNReal f ∈ C.A₀ := C.Pt_mem _ f
    refine ⟨C.i2 hk0 (C.ΓA_self_mem_A₀ hg0), C.i2 hk0 (C.Γ₂_mem hg0),
      C.hasDerivAt_gradPhi f h t hs⟩

end CompactTriple

/-- Compact triples satisfy the regularity hypothesis `GradientInterpolation` (G1 of `GAPS.md`). -/
theorem compact_gradientInterpolation (C : CompactTriple E) :
    C.toFullTriple.GradientInterpolation := C.gradientInterpolation

/-- **Gradient bound on a compact triple, unconditionally** (BGL Cor. 3.3.19 for `𝒜 = 𝒜₀`):
`CD(ρ,n)` implies `Γ(P_t f) ≤ e^{-2ρt} P_t(Γ f)` a.e., `f ∈ 𝒜₀`, `t ≥ 0`. -/
theorem compact_gradient_bound (C : CompactTriple E) {ρ : ℝ} {n : ℝ≥0∞}
    (hCD : C.toFullTriple.CD ρ n) (f : C.A₀) (t : ℝ≥0) :
    C.toDiffusionTriple.ΓA (C.Pt t f) (C.Pt t f) ≤ᵐ[C.μ] fun x =>
      Real.exp (-2 * ρ * t) * (C.toDiffusionTriple.semigroup t (C.toDiffusionTriple.cls
        ⟨C.toDiffusionTriple.ΓA f.1 f.1, C.ΓA_self_mem_A₀ f.2⟩) : Lp ℝ 2 C.μ) x :=
  C.toFullTriple.gradient_bound hCD C.gradientInterpolation f t

end MarkovTriple.BGL
