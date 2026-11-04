import Mathlib
import MarkovTriple.BGL.Instances.GibbsRd.Core2RdEnergy

/-!
# Gibbs on `ℝ^d`: `L f ∈ L²(μ)` from `Γ(f), Γ₂(f) ∈ L¹(μ)` and `Hess V ≥ ρ` (R20, Stream D1)

Statements: `Instances/Gibbs/STATEMENTS_R20_Direct.md` (D1-4).

## DIFFERENCE FROM BGL

BGL's proof of the converse of Prop. 3.3.17 (p. 161-162) goes through the density of `(L²+Id)𝒜₀` (the hypothesis `Core2`, ERRATA R15-1).
Here `L²` is never touched.  For `f ∈ C^∞ ∩ L²(μ)` with `Γ(f), Γ₂(f) ∈ L¹` we prove `L f ∈ L²(μ)` by a cut-off (Caccioppoli) estimate in the
spirit of BGL Prop. 3.2.1 (p. 142), applied to `Γ₂` instead of `Γ`: for a cut-off `χ` (two integrations by parts, F7, and the definition
`Γ₂ = ½(LΓ(f) − 2Γ(f,Lf))`)
`∫χ²(Lf)² = ∫χ²Γ₂(f) + ∫χ Γ(χ,Γf) − 2∫χ (Lf) Γ(χ,f)`,
where `Γ(χ,Γf) = 2 Hess f(∇χ,∇f)` is controlled by Cauchy-Schwarz `2|Hess f(a,b)| ≤ |a|²|b|² + |Hess f|²` and
`|Hess f|² = Γ₂(f) − Hess V(∇f,∇f) ≤ Γ₂(f) + |ρ|Γ(f)`.  `|∇χ_n|² ≤ 8C²` uniformly, `χ_n → 1`.  Only `Hess V ≥ ρ` (any sign) is used:
no growth condition on `∇V, Hess V, ∇³V`, and neither `Core2` nor the commutators of `L²` with cut-offs.
-/

open MeasureTheory Filter Topology Set

namespace MarkovTriple.BGL.Instances.GibbsRd

open MarkovTriple.BGL (pderiv)

variable {d : ℕ}

/-- the real-number part of the cut-off estimate. -/
lemma rd_pt {c u S s q Q0 H2 Γ ρ X : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hs : 0 ≤ s) (hq0 : 0 ≤ q)
    (hq : q ≤ Q0) (hS : S ^ 2 ≤ q * s) (hH0 : 0 ≤ H2) (hH : H2 ≤ |Γ| + |ρ| * s)
    (hX : X ≤ c * (q * s + H2)) :
    -(2 * c * u * S) + X + c ^ 2 * Γ ≤
      1 / 2 * (c * c * u * u) + (2 * Q0 * s + (Q0 * s + (|Γ| + |ρ| * s)) + |Γ|) := by
  have h1 : -(2 * c * u * S) ≤ 1 / 2 * (c * c * u * u) + 2 * S ^ 2 := by
    nlinarith [sq_nonneg (c * u + 2 * S)]
  have h2 : S ^ 2 ≤ Q0 * s := hS.trans (mul_le_mul_of_nonneg_right hq hs)
  have h3 : X ≤ Q0 * s + (|Γ| + |ρ| * s) := by
    have a : 0 ≤ q * s + H2 := by positivity
    have b : c * (q * s + H2) ≤ q * s + H2 := mul_le_of_le_one_left a hc1
    have c' : q * s ≤ Q0 * s := mul_le_mul_of_nonneg_right hq hs
    linarith
  have h4 : c ^ 2 * Γ ≤ |Γ| := by
    have : c ^ 2 ≤ 1 := by nlinarith
    calc c ^ 2 * Γ ≤ c ^ 2 * |Γ| := mul_le_mul_of_nonneg_left (le_abs_self _) (sq_nonneg _)
      _ ≤ 1 * |Γ| := mul_le_mul_of_nonneg_right this (abs_nonneg _)
      _ = |Γ| := one_mul _
  linarith

/-- Cauchy-Schwarz for a Hessian: `2 Σ_k Σ_j a_k b_j H_jk ≤ |a|²|b|² + |H|²`. -/
lemma sum_cross (a b : Fin d → ℝ) (H : Fin d → Fin d → ℝ) :
    2 * ∑ k, ∑ j, a k * b j * H j k ≤
      (∑ k, a k * a k) * (∑ j, b j * b j) + ∑ j, ∑ k, H j k ^ 2 := by
  have e1 : (∑ k, a k * a k) * (∑ j, b j * b j) = ∑ k, ∑ j, (a k * a k) * (b j * b j) :=
    Finset.sum_mul_sum _ _ _ _
  have e2 : ∑ j, ∑ k, H j k ^ 2 = ∑ k, ∑ j, H j k ^ 2 := Finset.sum_comm
  rw [e1, e2, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun k _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun j _ => ?_
  nlinarith [sq_nonneg (a k * b j - H j k)]

lemma gr_sm {f g : Rd d → ℝ} (hf : Sm f) (hg : Sm g) :
    Sm (Gr f g) := ContDiff.sum fun k _ => (hf.pderiv k).mul (hg.pderiv k)

namespace GibbsRdData

/-- the cut-off cross term: `½Γ(χ², Γf) = χ · 2 Σ_k Σ_j ∂ₖχ ∂ⱼf ∂ₖ∂ⱼ f`. -/
lemma cross_formula {χ f : Rd d → ℝ} (hχ : Sm χ) (hf : Sm f) (x : Rd d) :
    Gr (fun y => χ y * χ y) (Gr f f) x / 2 =
      χ x * (2 * ∑ k, ∑ j, pderiv χ k x * pderiv f j x * pderiv (pderiv f j) k x) := by
  have h : ∀ k, pderiv (fun y => χ y * χ y) k x * pderiv (Gr f f) k x =
      ∑ j, 4 * χ x * (pderiv χ k x * pderiv f j x * pderiv (pderiv f j) k x) := by
    intro k
    rw [pderiv_mul' hχ hχ k x, pderiv_Gr hf k x, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have : Gr (fun y => χ y * χ y) (Gr f f) x = ∑ k, ∑ j, 4 * χ x *
      (pderiv χ k x * pderiv f j x * pderiv (pderiv f j) k x) := by
    unfold Gr
    exact Finset.sum_congr rfl fun k _ => h k
  rw [this]
  simp only [Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring

/-- **D1-4.**  `f ∈ C^∞ ∩ L²(μ)`, `Γ(f) ∈ L¹(μ)`, `Γ₂(f) = ‖Hess f‖² + Hess V(∇f,∇f) ∈ L¹(μ)` and `Hess V ≥ ρ` (any sign of `ρ`)
give `L f ∈ L²(μ)`.  No growth condition on `V`. -/
theorem memLp_Lr_of_Γ₂ (G : GibbsRdData d) {ρ : ℝ} (hρ : HessGe G.V ρ) {f : Rd d → ℝ} (hf : Sm f)
    (hG : Integrable (Gr f f) G.toEll.μ)
    (hG2 : Integrable (fun x => ∑ i, ∑ j, pderiv (pderiv f i) j x ^ 2 +
      ∑ i, ∑ j, pderiv (pderiv G.V i) j x * pderiv f i x * pderiv f j x) G.toEll.μ) :
    MemLp (Lr G.V f) 2 G.toEll.μ := by
  obtain ⟨C, hC0, hC⟩ := sT_deriv_bound
  set μ := G.toEll.μ with hμ
  have hu : Sm (Lr G.V f) := sm_Lr G.smooth hf
  have hP : Sm (Gr f f) := sm_Gr hf
  have hV2 : ∀ i j, Sm (pderiv (pderiv G.V i) j) := fun i j => (G.smooth.pderiv i).pderiv j
  have hfi : ∀ i, Sm (pderiv f i) := fun i => hf.pderiv i
  have hH2c : Continuous (fun x => ∑ i, ∑ j, pderiv (pderiv f i) j x ^ 2) :=
    continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
      ((hf.pderiv i).pderiv j).continuous.pow 2
  have hQc : Continuous (fun x => ∑ i, ∑ j, pderiv (pderiv G.V i) j x * pderiv f i x * pderiv f j x) :=
    continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
      ((hV2 i j).continuous.mul (hfi i).continuous).mul (hfi j).continuous
  set Γ : Rd d → ℝ := fun x => ∑ i, ∑ j, pderiv (pderiv f i) j x ^ 2 +
      ∑ i, ∑ j, pderiv (pderiv G.V i) j x * pderiv f i x * pderiv f j x with hΓ
  have hΓc : Continuous Γ := hH2c.add hQc
  set W : Rd d → ℝ := fun x => 2 * (8 * C ^ 2) * Gr f f x + ((8 * C ^ 2) * Gr f f x +
      (|Γ x| + |ρ| * Gr f f x)) + |Γ x| with hW
  have iW : Integrable W μ := by
    have i1 := hG2.abs
    have i2 := hG.const_mul |ρ|
    have i3 := (hG.const_mul (2 * (8 * C ^ 2))).add
      (((hG.const_mul (8 * C ^ 2)).add (i1.add i2)).add i1)
    refine i3.congr (Eventually.of_forall fun x => ?_)
    simp only [hW, Pi.add_apply]
    ring
  refine memLp_two_of_cut (B := 2 * ∫ x, W x ∂μ) hu.continuous (fun n => ?_)
  set R : ℝ := (n : ℝ) + 1 with hR
  have hRpos : 0 < R := by positivity
  have hR1 : 1 ≤ R := by rw [hR]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  set χ : Rd d → ℝ := cut R with hχdef
  have hχ : Sm χ := sm_cut R
  have hχc : HasCompactSupport χ := hcs_cut hRpos
  have hχ0 : ∀ x, 0 ≤ χ x := fun x => cut_nonneg R x
  have hχ1 : ∀ x, χ x ≤ 1 := fun x => cut_le_one R x
  have hq : ∀ x, Gr χ χ x ≤ 8 * C ^ 2 := fun x => by
    have := (sum_sq_pderiv_cut_le hRpos hC x).trans (div_le_self (by positivity) (one_le_pow₀ hR1))
    simpa [Gr, sq] using this
  have hχχ : Sm (fun x => χ x * χ x) := hχ.mul hχ
  have hχχc : HasCompactSupport (fun x => χ x * χ x) := hχc.mul_right
  have intc : ∀ {φ : Rd d → ℝ}, Continuous φ → HasCompactSupport φ → Integrable φ μ :=
    fun hc hs => G.int_cs hc hs
  -- the two integrations by parts
  set g : Rd d → ℝ := fun x => χ x * χ x * Lr G.V f x with hg
  have hgS : Sm g := hχχ.mul hu
  have hgc : HasCompactSupport g := hχχc.mul_right
  have e1 := G.ibp_Lr hf hgS (Or.inl hgc)
  have e2 := G.ibp_Lr hP hχχ (Or.inl hχχc)
  set a1 : Rd d → ℝ := fun x => χ x * (2 * Lr G.V f x * Gr χ f x) with ha1
  set a2 : Rd d → ℝ := fun x => χ x * χ x * Gr (Lr G.V f) f x with ha2
  set a3 : Rd d → ℝ := fun x => χ x * χ x * Lr G.V (Gr f f) x with ha3
  set a4 : Rd d → ℝ := fun x => Gr (fun y => χ y * χ y) (Gr f f) x with ha4
  set a5 : Rd d → ℝ := fun x => χ x * χ x * Γ x with ha5
  have ia1 : Integrable a1 μ := intc
    (hχ.continuous.mul ((continuous_const.mul hu.continuous).mul (gr_sm hχ hf).continuous))
    hχc.mul_right
  have ia2 : Integrable a2 μ := intc
    (hχχ.continuous.mul (gr_sm hu hf).continuous) hχχc.mul_right
  have ia3 : Integrable a3 μ := intc
    (hχχ.continuous.mul (sm_Lr G.smooth hP).continuous) hχχc.mul_right
  have ia4 : Integrable a4 μ := intc (gr_sm hχχ hP).continuous (G.hcs_Gr_left hχχc)
  have ia5 : Integrable a5 μ := intc (hχχ.continuous.mul hΓc) hχχc.mul_right
  set T : Rd d → ℝ := fun x => χ x * χ x * Lr G.V f x * Lr G.V f x with hT
  have iT : Integrable T μ := intc
    ((hχχ.continuous.mul hu.continuous).mul hu.continuous) (hχχc.mul_right.mul_right)
  -- first identity: ∫ T = -(∫ a1 + ∫ a2)
  have hGg : ∀ x, Gr g f x = a1 x + a2 x := by
    intro x
    have hpg : ∀ k, pderiv g k x = (pderiv χ k x * χ x + χ x * pderiv χ k x) * Lr G.V f x +
        χ x * χ x * pderiv (Lr G.V f) k x := by
      intro k
      have h1 : pderiv g k x = pderiv (fun y => χ y * χ y) k x * Lr G.V f x +
          (χ x * χ x) * pderiv (Lr G.V f) k x := pderiv_mul' hχχ hu k x
      have h2 : pderiv (fun y => χ y * χ y) k x = pderiv χ k x * χ x + χ x * pderiv χ k x :=
        pderiv_mul' hχ hχ k x
      rw [h1, h2]
    simp only [ha1, ha2, Gr, Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hpg k]
    ring
  have eT : ∫ x, T x ∂μ = -(∫ x, a1 x ∂μ + ∫ x, a2 x ∂μ) := by
    have : ∫ x, T x ∂μ = -∫ x, (a1 x + a2 x) ∂μ := by
      have hT' : ∫ x, T x ∂μ = ∫ x, g x * Lr G.V f x ∂μ :=
        integral_congr_ae (Eventually.of_forall fun x => by simp only [hT, hg])
      have hR' : ∫ x, Gr g f x ∂μ = ∫ x, (a1 x + a2 x) ∂μ :=
        integral_congr_ae (Eventually.of_forall hGg)
      rw [hT', e1, hR']
    rw [this, integral_add ia1 ia2]
  -- second identity: ∫ a3 = -∫ a4
  have e3 : ∫ x, a3 x ∂μ = -∫ x, a4 x ∂μ := e2
  -- pointwise Bochner: a2 = a3/2 - a5
  have hpt : ∀ x, a2 x = a3 x / 2 - a5 x := by
    intro x
    have hb := G.bochner_pt hf x
    have hcm : Gr (Lr G.V f) f x = Gr f (Lr G.V f) x := congrFun (gr_comm _ _) x
    simp only [ha2, ha3, ha5, hΓ]
    rw [hb, hcm]
    ring
  have ea2 : ∫ x, a2 x ∂μ = (∫ x, a3 x ∂μ) / 2 - ∫ x, a5 x ∂μ := by
    rw [← integral_div, ← integral_sub (ia3.div_const 2) ia5]
    exact integral_congr_ae (Eventually.of_forall hpt)
  -- hence ∫ T = ∫ (-a1 + a4/2 + a5)
  have eT2 : ∫ x, T x ∂μ = ∫ x, (-(a1 x) + a4 x / 2 + a5 x) ∂μ := by
    have h1 : ∫ x, (-(a1 x) + a4 x / 2 + a5 x) ∂μ =
        ∫ x, (-(a1 x) + a4 x / 2) ∂μ + ∫ x, a5 x ∂μ :=
      integral_add (ia1.neg.add (ia4.div_const 2)) ia5
    have h2 : ∫ x, (-(a1 x) + a4 x / 2) ∂μ = ∫ x, -(a1 x) ∂μ + ∫ x, a4 x / 2 ∂μ :=
      integral_add ia1.neg (ia4.div_const 2)
    have h3 : ∫ x, -(a1 x) ∂μ = -∫ x, a1 x ∂μ := integral_neg _
    rw [h1, h2, h3, integral_div, eT, ea2, e3]
    ring
  -- pointwise bound
  have hbd : ∀ x, -(a1 x) + a4 x / 2 + a5 x ≤ 1 / 2 * T x + W x := by
    intro x
    have hs0 : 0 ≤ Gr f f x := Finset.sum_nonneg fun k _ => mul_self_nonneg _
    have hq0 : 0 ≤ Gr χ χ x := Finset.sum_nonneg fun k _ => mul_self_nonneg _
    have hH0 : 0 ≤ ∑ i, ∑ j, pderiv (pderiv f i) j x ^ 2 :=
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
    have hS : Gr χ f x ^ 2 ≤ Gr χ χ x * Gr f f x := by
      have := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin d))
        (fun k => pderiv χ k x) (fun k => pderiv f k x)
      simpa [Gr, sq] using this
    have hHess : ∑ i, ∑ j, pderiv (pderiv f i) j x ^ 2 ≤ |Γ x| + |ρ| * Gr f f x := by
      have hQ : ρ * Gr f f x ≤ ∑ i, ∑ j, pderiv (pderiv G.V i) j x * pderiv f i x * pderiv f j x := by
        have := hρ x (fun k => pderiv f k x)
        simpa [Gr, sq] using this
      have h1 := le_abs_self (Γ x)
      have h2 : -(|ρ| * Gr f f x) ≤ ρ * Gr f f x := by
        nlinarith [neg_abs_le ρ, hs0]
      simp only [hΓ] at h1 ⊢
      linarith
    have hX : a4 x / 2 ≤ χ x * (Gr χ χ x * Gr f f x + ∑ i, ∑ j, pderiv (pderiv f i) j x ^ 2) := by
      have hc := cross_formula hχ hf x
      have hcs := sum_cross (fun k => pderiv χ k x) (fun j => pderiv f j x)
        (fun j k => pderiv (pderiv f j) k x)
      simp only [ha4]
      rw [hc]
      refine mul_le_mul_of_nonneg_left ?_ (hχ0 x)
      simpa [Gr] using hcs
    have key := rd_pt (c := χ x) (u := Lr G.V f x) (S := Gr χ f x) (s := Gr f f x) (q := Gr χ χ x)
      (Q0 := 8 * C ^ 2) (H2 := ∑ i, ∑ j, pderiv (pderiv f i) j x ^ 2) (Γ := Γ x) (ρ := ρ)
      (X := a4 x / 2) (hχ0 x) (hχ1 x) hs0 hq0 (hq x) hS hH0 hHess hX
    simp only [ha1, ha5, hT, hW]
    nlinarith [key]
  have hint : ∫ x, T x ∂μ ≤ 1 / 2 * ∫ x, T x ∂μ + ∫ x, W x ∂μ := by
    calc ∫ x, T x ∂μ = ∫ x, (-(a1 x) + a4 x / 2 + a5 x) ∂μ := eT2
      _ ≤ ∫ x, (1 / 2 * T x + W x) ∂μ :=
          integral_mono ((ia1.neg.add (ia4.div_const 2)).add ia5) ((iT.const_mul _).add iW) hbd
      _ = 1 / 2 * ∫ x, T x ∂μ + ∫ x, W x ∂μ := by
          rw [integral_add (iT.const_mul _) iW, integral_const_mul]
  have hfin : ∫ x, (χ x * Lr G.V f x) ^ 2 ∂μ = ∫ x, T x ∂μ :=
    integral_congr_ae (Eventually.of_forall fun x => by simp only [hT]; ring)
  rw [hfin]
  linarith

end GibbsRdData

end MarkovTriple.BGL.Instances.GibbsRd
