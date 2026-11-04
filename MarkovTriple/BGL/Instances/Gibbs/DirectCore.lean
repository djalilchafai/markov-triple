import Mathlib
import MarkovTriple.BGL.Instances.Gibbs.Core2Resolvent
import MarkovTriple.BGL.Instances.Gibbs.FunctIBP

/-!
# Gibbs on `ℝ`: `L f ∈ L²(μ)` from `Γ(f), Γ₂(f) ∈ L¹(μ)` and `V'' ≥ ρ` (R20, Stream D1)

Statements: `STATEMENTS_R20_Direct.md` (D1-2).

## DIFFERENCE FROM BGL

BGL's proof of the converse of Prop. 3.3.17 (p. 161-162) goes through the density of `(L²+Id)𝒜₀` (the hypothesis `Core2`, ERRATA R15-1).
Here we do not touch `L²`.  We prove `L f ∈ L²(μ)` for smooth `f ∈ L²` with `Γ(f), Γ₂(f) ∈ L¹` by a cut-off (Caccioppoli) estimate in
the spirit of BGL Prop. 3.2.1 (p. 142), applied to `Γ₂` instead of `Γ`: for `χ ∈ C_c^∞` (two integrations by parts, F7, and the definition
`Γ₂ = ½(LΓ(f) − 2Γ(f,Lf))`),
`∫χ²(Lf)² = ∫χ²Γ₂(f) + ∫χ Γ(χ,Γf) − 2∫χ (Lf) Γ(χ,f)`,
with `Γ(χ,Γ f) = 2χ'f'f''`, `f''² = Γ₂(f) − V'' f'² ≤ Γ₂(f) + |ρ|f'²`.  Nothing on `V` (growth of `V'`, `V'''`) is used; only `V'' ≥ ρ`.
The step "`f ∈ 𝒜 ∩ L²`, `L f ∈ L²` ⇒ `f ∈ 𝒟(L̄)`" is BGL Prop. 3.3.6 (i) (`FullTriple.mem_domain_of_ESA`, essential self-adjointness of `L`).
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal
open MarkovTriple.Sanity.OU (Sm)
open MarkovTriple.Sanity.OU hiding A₀ γ φ
open MarkovTriple.BGL.Lebesgue (chiR Rn Rn_pos chiR_smooth chiR_cs)

namespace MarkovTriple.BGL.Instances.Gibbs

/-- the real-number part of the cut-off estimate. -/
lemma direct_pt {c c' u s t Γ ρ K : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hK : |c'| ≤ K)
    (ht : t ^ 2 ≤ |Γ| + |ρ| * s ^ 2) :
    -(2 * c * c' * u * s) + 2 * c * c' * s * t + c ^ 2 * Γ ≤
      1 / 2 * (c * c * u * u) + (2 * K ^ 2 * s ^ 2 + K * (s ^ 2 + (|Γ| + |ρ| * s ^ 2)) + |Γ|) := by
  have hK0 : 0 ≤ K := (abs_nonneg _).trans hK
  have hc'2 : c' ^ 2 ≤ K ^ 2 := by nlinarith [abs_nonneg c', sq_abs c']
  have h1 : -(2 * c * c' * u * s) ≤ 1 / 2 * (c * c * u * u) + 2 * c' ^ 2 * s ^ 2 := by
    nlinarith [sq_nonneg (c * u + 2 * c' * s)]
  have h1' : 2 * c' ^ 2 * s ^ 2 ≤ 2 * K ^ 2 * s ^ 2 := by nlinarith [sq_nonneg s]
  have hm : |c * c'| ≤ K := by
    rw [abs_mul, abs_of_nonneg hc0]
    exact (mul_le_of_le_one_left (abs_nonneg _) hc1).trans hK
  have h2 : 2 * c * c' * s * t ≤ K * (s ^ 2 + t ^ 2) := by
    have e : 2 * c * c' * s * t = 2 * (c * c') * (s * t) := by ring
    rw [e]
    have a1 : 2 * (c * c') * (s * t) ≤ 2 * |c * c'| * |s * t| := by
      have := le_abs_self ((c * c') * (s * t))
      rw [abs_mul] at this
      linarith
    have a2 : 2 * |c * c'| * |s * t| ≤ 2 * K * |s * t| :=
      mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
    have a3 : 2 * |s * t| ≤ s ^ 2 + t ^ 2 := by
      rw [abs_mul]
      nlinarith [sq_nonneg (|s| - |t|), sq_abs s, sq_abs t]
    nlinarith [mul_le_mul_of_nonneg_left a3 hK0]
  have h3 : c ^ 2 * Γ ≤ |Γ| := by
    have : c ^ 2 ≤ 1 := by nlinarith
    calc c ^ 2 * Γ ≤ c ^ 2 * |Γ| := mul_le_mul_of_nonneg_left (le_abs_self _) (sq_nonneg _)
      _ ≤ 1 * |Γ| := mul_le_mul_of_nonneg_right this (abs_nonneg _)
      _ = |Γ| := one_mul _
  nlinarith [mul_le_mul_of_nonneg_left ht hK0]

namespace GibbsData
variable (G : GibbsData)

/-- **D1-2.**  `f ∈ C^∞ ∩ L²(μ)`, `Γ(f) = f'²`, `Γ₂(f) = f''² + V''f'² ∈ L¹(μ)` and `V'' ≥ ρ` give `L f ∈ L²(μ)`.
No growth condition on `V`. -/
theorem memLp_Lg_of_Γ₂ {ρ : ℝ} (hρ : ∀ x, ρ ≤ deriv (deriv G.V) x) {f : ℝ → ℝ} (hf : Sm f)
    (hG : Integrable (fun x => deriv f x * deriv f x) G.μ)
    (hG2 : Integrable (fun x => deriv (deriv f) x ^ 2 + deriv (deriv G.V) x * deriv f x ^ 2) G.μ) :
    MemLp (Lg G.V f) 2 G.μ := by
  obtain ⟨K, hK1, hK⟩ := chiR_iter_bound
  have hu : Sm (Lg G.V f) := sm_Lg G.smooth hf
  have hf1 : Sm (deriv f) := hf.deriv'
  have hf2 : Sm (deriv (deriv f)) := hf1.deriv'
  have hu1 : Sm (deriv (Lg G.V f)) := hu.deriv'
  have hP : Sm (Go f f) := hf1.mul hf1
  have hV2 : Sm (deriv (deriv G.V)) := G.smooth.deriv'.deriv'
  set W : ℝ → ℝ := fun x => 2 * K ^ 2 * (deriv f x * deriv f x) + K * ((deriv f x * deriv f x) +
      (|deriv (deriv f) x ^ 2 + deriv (deriv G.V) x * deriv f x ^ 2| +
        |ρ| * (deriv f x * deriv f x))) +
      |deriv (deriv f) x ^ 2 + deriv (deriv G.V) x * deriv f x ^ 2| with hW
  have iW : Integrable W G.μ := by
    have i1 := hG2.abs
    have i2 := hG.const_mul |ρ|
    have i3 := (hG.const_mul (2 * K ^ 2)).add (((hG.add (i1.add i2)).const_mul K).add i1)
    refine i3.congr (Eventually.of_forall fun x => ?_)
    simp only [hW, Pi.add_apply]
    ring
  refine memLp_two_of_cutoff (B := 2 * ∫ x, W x ∂G.μ) hu.continuous (fun n => ?_)
  set χ : ℝ → ℝ := chiR (Rn n) with hχdef
  have hχ : Sm χ := chiR_smooth _
  have hχc : HasCompactSupport χ := chiR_cs (Rn_pos n).ne'
  have hχ0 : ∀ x, 0 ≤ χ x := fun x => chiR_nonneg' _ x
  have hχ1 : ∀ x, χ x ≤ 1 := fun x => chiR_le_one' _ x
  have hχ' : ∀ x, |deriv χ x| ≤ K := fun x => by simpa using hK 1 (by norm_num) n x
  have hχ1s : Sm (deriv χ) := hχ.deriv'
  have hχχ : Sm (fun x => χ x * χ x) := hχ.mul hχ
  have hχχc : HasCompactSupport (fun x => χ x * χ x) := hχc.mul_right
  have intc : ∀ {φ : ℝ → ℝ}, Continuous φ → HasCompactSupport φ → Integrable φ G.μ :=
    fun hc hs => hc.integrable_of_hasCompactSupport hs
  -- the two integrations by parts
  set g : ℝ → ℝ := fun x => χ x * χ x * Lg G.V f x with hg
  have hgS : Sm g := hχχ.mul hu
  have hgc : HasCompactSupport g := hχχc.mul_right
  have hdg : ∀ x, deriv g x = (deriv χ x * χ x + χ x * deriv χ x) * Lg G.V f x +
      χ x * χ x * deriv (Lg G.V f) x := fun x =>
    (((hχ.hasDerivAt x).mul (hχ.hasDerivAt x)).mul (hu.hasDerivAt x)).deriv
  have e1 := G.ibp_sm hf hgS (Or.inl hgc)
  have hdP : ∀ x, deriv (Go f f) x = deriv (deriv f) x * deriv f x + deriv f x * deriv (deriv f) x :=
    fun x => ((hf1.hasDerivAt x).mul (hf1.hasDerivAt x)).deriv
  have hdχχ : ∀ x, deriv (fun x => χ x * χ x) x = deriv χ x * χ x + χ x * deriv χ x := fun x =>
    ((hχ.hasDerivAt x).mul (hχ.hasDerivAt x)).deriv
  have e2 := G.ibp_sm hP hχχ (Or.inl hχχc)
  -- the five integrands
  set a1 : ℝ → ℝ := fun x => χ x * (2 * deriv χ x * Lg G.V f x * deriv f x) with ha1
  set a2 : ℝ → ℝ := fun x => χ x * χ x * (deriv (Lg G.V f) x * deriv f x) with ha2
  set a3 : ℝ → ℝ := fun x => χ x * χ x * Lg G.V (Go f f) x with ha3
  set a4 : ℝ → ℝ := fun x => χ x * (4 * deriv χ x * deriv f x * deriv (deriv f) x) with ha4
  set a5 : ℝ → ℝ := fun x => χ x * χ x *
    (deriv (deriv f) x ^ 2 + deriv (deriv G.V) x * deriv f x ^ 2) with ha5
  have ia1 : Integrable a1 G.μ := intc
    (hχ.continuous.mul ((continuous_const.mul hχ1s.continuous |>.mul hu.continuous).mul hf1.continuous))
    hχc.mul_right
  have ia2 : Integrable a2 G.μ := intc
    (hχχ.continuous.mul (hu1.continuous.mul hf1.continuous)) hχχc.mul_right
  have ia3 : Integrable a3 G.μ := intc
    (hχχ.continuous.mul (sm_Lg G.smooth hP).continuous) hχχc.mul_right
  have ia4 : Integrable a4 G.μ := intc
    (hχ.continuous.mul (((continuous_const.mul hχ1s.continuous).mul hf1.continuous).mul hf2.continuous))
    hχc.mul_right
  have ia5 : Integrable a5 G.μ := intc
    (hχχ.continuous.mul ((hf2.continuous.pow 2).add (hV2.continuous.mul (hf1.continuous.pow 2))))
    hχχc.mul_right
  set T : ℝ → ℝ := fun x => χ x * χ x * Lg G.V f x * Lg G.V f x with hT
  have iT : Integrable T G.μ := intc
    ((hχχ.continuous.mul hu.continuous).mul hu.continuous) (hχχc.mul_right.mul_right)
  -- first identity: ∫ T = -(∫ a1 + ∫ a2)
  have eT : ∫ x, T x ∂G.μ = -(∫ x, a1 x ∂G.μ + ∫ x, a2 x ∂G.μ) := by
    have : ∫ x, T x ∂G.μ = -∫ x, (a1 x + a2 x) ∂G.μ := by
      refine e1.trans ?_
      congr 1
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [hdg, ha1, ha2]
      ring
    rw [this, integral_add ia1 ia2]
  -- second identity: ∫ a3 = -∫ a4
  have e3 : ∫ x, a3 x ∂G.μ = -∫ x, a4 x ∂G.μ := by
    refine e2.trans ?_
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [hdχχ, hdP, ha4]
    ring
  -- pointwise Bochner: a2 = a3/2 - a5
  have hpt : ∀ x, a2 x = a3 x / 2 - a5 x := by
    intro x
    have hb := Γ₂_eq G.smooth hf x
    have e : Go f (Lg G.V f) x = deriv f x * deriv (Lg G.V f) x := rfl
    simp only [ha2, ha3, ha5]
    rw [← hb, e]
    ring
  have ea2 : ∫ x, a2 x ∂G.μ = (∫ x, a3 x ∂G.μ) / 2 - ∫ x, a5 x ∂G.μ := by
    rw [← integral_div, ← integral_sub (ia3.div_const 2) ia5]
    exact integral_congr_ae (Eventually.of_forall hpt)
  -- hence ∫ T = ∫ (-a1 + a4/2 + a5)
  have eT2 : ∫ x, T x ∂G.μ = ∫ x, (-(a1 x) + a4 x / 2 + a5 x) ∂G.μ := by
    have h1 : ∫ x, (-(a1 x) + a4 x / 2 + a5 x) ∂G.μ =
        ∫ x, (-(a1 x) + a4 x / 2) ∂G.μ + ∫ x, a5 x ∂G.μ :=
      integral_add (ia1.neg.add (ia4.div_const 2)) ia5
    have h2 : ∫ x, (-(a1 x) + a4 x / 2) ∂G.μ = ∫ x, -(a1 x) ∂G.μ + ∫ x, a4 x / 2 ∂G.μ :=
      integral_add ia1.neg (ia4.div_const 2)
    have h3 : ∫ x, -(a1 x) ∂G.μ = -∫ x, a1 x ∂G.μ := integral_neg _
    rw [h1, h2, h3, integral_div, eT, ea2, e3]
    ring
  -- pointwise bound
  have hbd : ∀ x, -(a1 x) + a4 x / 2 + a5 x ≤ 1 / 2 * T x + W x := by
    intro x
    have ht : deriv (deriv f) x ^ 2 ≤
        |deriv (deriv f) x ^ 2 + deriv (deriv G.V) x * deriv f x ^ 2| + |ρ| * (deriv f x * deriv f x) := by
      have h1 : ρ * deriv f x ^ 2 ≤ deriv (deriv G.V) x * deriv f x ^ 2 :=
        mul_le_mul_of_nonneg_right (hρ x) (sq_nonneg _)
      have h2 : -(|ρ| * deriv f x ^ 2) ≤ ρ * deriv f x ^ 2 := by
        nlinarith [neg_abs_le ρ, sq_nonneg (deriv f x)]
      have h3 := le_abs_self (deriv (deriv f) x ^ 2 + deriv (deriv G.V) x * deriv f x ^ 2)
      nlinarith [sq_nonneg (deriv f x)]
    have key := direct_pt (c := χ x) (c' := deriv χ x) (u := Lg G.V f x) (s := deriv f x)
      (t := deriv (deriv f) x) (Γ := deriv (deriv f) x ^ 2 + deriv (deriv G.V) x * deriv f x ^ 2)
      (ρ := ρ) (K := K) (hχ0 x) (hχ1 x) (hχ' x) (by simpa only [sq] using ht)
    simp only [ha1, ha4, ha5, hT, hW]
    nlinarith [key]
  have hint : ∫ x, T x ∂G.μ ≤ 1 / 2 * ∫ x, T x ∂G.μ + ∫ x, W x ∂G.μ := by
    calc ∫ x, T x ∂G.μ = ∫ x, (-(a1 x) + a4 x / 2 + a5 x) ∂G.μ := eT2
      _ ≤ ∫ x, (1 / 2 * T x + W x) ∂G.μ :=
          integral_mono ((ia1.neg.add (ia4.div_const 2)).add ia5) ((iT.const_mul _).add iW) hbd
      _ = 1 / 2 * ∫ x, T x ∂G.μ + ∫ x, W x ∂G.μ := by
          rw [integral_add (iT.const_mul _) iW, integral_const_mul]
  have hfin : ∫ x, (χ x * Lg G.V f x) ^ 2 ∂G.μ = ∫ x, T x ∂G.μ :=
    integral_congr_ae (Eventually.of_forall fun x => by simp only [hT]; ring)
  rw [hfin]
  linarith

end GibbsData

end MarkovTriple.BGL.Instances.Gibbs
