import Mathlib
import MarkovTriple.BGL.Theory.Extension.Converse
import MarkovTriple.BGL.Theory.Extension.Hessian
import MarkovTriple.BGL.Frozen.Complete

/-!
# Direct converse of BGL Prop. 3.3.17 without `Core2` (Round 20, Stream D3)

Statements: `Extension/STATEMENTS_R20_ConverseDirect.md`.

## DIFFERENCE FROM BGL

* **What BGL does** (Prop. 3.3.17, p. 161-162, converse): proves `|∫ f L h| ≤ C ‖h‖` on `(L² + Id)𝒜₀` from
  `K(f,h)² ≤ K(f) K(h)`, then *extends* the functional to all of `L²` using that `𝒜₀` is a core for `L²` (together with
  ergodicity).  This `L²`-core step is tacit in the book (ERRATA R15-1; formal name `FullTriple.Core2`, used by
  `FullTriple.mem_domain_of_Γ₂`), and is hard (only proved under growth hypotheses, Rounds 17-19).
* **What we do instead**: we never use `Core2`.  We show `L f ∈ L²` *directly* by the cut-off technique of BGL Prop. 3.2.1
  (p. 142, essential self-adjointness) applied to `Γ₂`: for the completeness cut-offs `χ = ζ_k ∈ 𝒜₀` (Def. 3.3.9),
  `∫ χ² (Lf)² = ∫ χ² Γ₂(f) + ∫ χ Γ(Γf, χ) − 2 ∫ χ Lf Γ(f, χ)` (`cutoff_Γ₂_identity`, F7 only); the cross term is bounded by
  the Hessian Cauchy-Schwarz `Γ(χ,Γf)² ≤ 4 (Γ₂(f) − ρΓ(f)) Γ(χ) Γ(f)` (`hessCS`, a *consequence* of BGL (3.3.7) =
  `hessian_general_ineq`, since `Γ(χ,Γf) = 2 H(f)(χ,f)`), and `Γ(f,χ)² ≤ Γ(f)Γ(χ)`; Fatou as `k → ∞` gives
  `L f ∈ L²` (`memLp_L_of_Γ₂`).  Then ESA (F10) puts `f` in `𝒟(L̄)` via the maximal-domain lemma (`mem_domain_of_maximal`,
  BGL Prop. 3.3.6 (i)), whence `mem_domain_of_Γ₂_direct`.
* **Why**: the converse only needs `L f ∈ L²`, which is what the cut-off argument gives; `Core2` is much stronger.
* **Hypotheses that differ**: BGL: ESA, `CD(ρ,∞)`, ergodicity (and tacitly the `L²`-core step).  Here: ESA (field F10),
  completeness `IsComplete` (Def. 3.3.9), `CD(ρ,n)` for any `n`.  **`Core2` is NOT needed**; neither is ergodicity, nor any
  growth/Hessian-boundedness hypothesis, nor a separate "HessCS" hypothesis (it is a theorem here).  Completeness is a new
  hypothesis relative to `mem_domain_of_Γ₂`; the two results are therefore incomparable.
-/

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

namespace MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E]

namespace FullTriple

variable {T : FullTriple E}

/-- **Maximal-domain lemma** (BGL Prop. 3.3.6 (i), under ESA/F10): `f ∈ 𝒜 ∩ L²` with `Lf ∈ L²` has `[f] ∈ 𝒟(L̄)` and
`L̄[f] = [Lf]`.  Abstract version (= `mem_domain_of_ESA`; proof via `𝒟(L̄*) = 𝒟(L̄)`, F10 and symmetry F7). -/
theorem mem_domain_of_maximal {f : E → ℝ} (hf : f ∈ T.A) (hf2 : MemLp f 2 T.μ)
    (hLf2 : MemLp (T.L f) 2 T.μ) :
    ∃ hF : hf2.toLp f ∈ T.toDiffusionTriple.generator.domain,
      T.toDiffusionTriple.generator ⟨hf2.toLp f, hF⟩ = hLf2.toLp (T.L f) :=
  mem_domain_of_ESA hf hf2 hLf2

/-- **Hessian Cauchy-Schwarz** (BGL (3.3.7) specialised; DERIVED, not a hypothesis): under `CD(ρ,n)`,
`Γ(χ, Γ f)² ≤ 4 (Γ₂(f) − ρΓ(f)) Γ(χ) Γ(f)` a.e. (`Γ(χ,Γf) = 2 H(f)(χ,f)`). -/
theorem hessCS {ρ : ℝ} {n : ℝ≥0∞} (hCD : T.CD ρ n) {f χ : E → ℝ} (hf : f ∈ T.A) (hχ : χ ∈ T.A) :
    ∀ᵐ x ∂T.μ, G T χ (G T f f) x ^ 2 ≤
      4 * (T.toDiffusionTriple.Γ₂ f f x - ρ * G T f f x) * (G T χ χ x * G T f f x) := by
  filter_upwards [hessian_general_ineq hCD hf hχ hf] with x hx
  have e : Hess T f χ f x = G T χ (G T f f) x / 2 := by
    simp only [Hess]; rw [G_comm f χ]; ring
  rw [e] at hx
  simp only [Kf] at hx
  nlinarith [hx]

/-- **Cut-off `Γ₂` identity** (only F7, F1): for `χ ∈ 𝒜₀`, `f ∈ 𝒜`,
`∫ χ² (Lf)² = ∫ χ² Γ₂(f) + ∫ χ Γ(Γf, χ) − 2 ∫ χ Lf Γ(f, χ)`. -/
theorem cutoff_Γ₂_identity {χ f : E → ℝ} (hχ : χ ∈ T.A₀) (hf : f ∈ T.A) :
    ∫ x, χ x ^ 2 * T.L f x ^ 2 ∂T.μ =
      ∫ x, χ x ^ 2 * T.toDiffusionTriple.Γ₂ f f x ∂T.μ + ∫ x, χ x * G T (G T f f) χ x ∂T.μ -
        2 * ∫ x, χ x * T.L f x * G T f χ x ∂T.μ := by
  have hχA := A₀_memA hχ
  have hp : G T f f ∈ T.A := G_mem hf hf
  have hSA₀ : χ * χ ∈ T.A₀ := T.A₀.mul_mem hχ hχ
  have hSA : χ * χ ∈ T.A := A₀_memA hSA₀
  have hLf := L_memA hf
  have hLp := L_memA hp
  have hI : ∀ u : E → ℝ, u ∈ T.A → Integrable (fun x => χ x ^ 2 * u x) T.μ := by
    intro u hu
    refine (intA₀ (mulA₀ hu hSA₀)).congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.mul_apply]; ring
  -- (b) F7 for p against χ*χ
  have b1 := (T.ibp_A (G T f f) hp (χ * χ) hSA₀).1
  have c1 := G_mul_right hχA hχA hp
  have i1 : Integrable (fun x => χ x * G T (G T f f) χ x) T.μ :=
    intA₀ (mulA₀' hχ (G_memA₀ hp hχ))
  have b2 : ∫ x, G T (G T f f) (χ * χ) x ∂T.μ = 2 * ∫ x, χ x * G T (G T f f) χ x ∂T.μ := by
    rw [integral_congr_ae c1, ← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun x => by ring)
  have b3 : ∫ x, (χ * χ) x * T.L (G T f f) x ∂T.μ = ∫ x, χ x ^ 2 * T.L (G T f f) x ∂T.μ :=
    integral_congr_ae (Eventually.of_forall fun x => by simp only [Pi.mul_apply]; ring)
  -- (d) F7 for f against (χ*χ) L f
  have hg2 : (χ * χ) * T.L f ∈ T.A₀ := T.ideal (T.L f) hLf (χ * χ) hSA₀
  have d1 := (T.ibp_A f hf ((χ * χ) * T.L f) hg2).1
  have e1 := G_mul_right hSA hLf hf
  have e2 := G_mul_right hχA hχA hf
  have iB := hI (G T f (T.L f)) (G_mem hf hLf)
  have i3 : Integrable (fun x => χ x * T.L f x * G T f χ x) T.μ :=
    (intA₀ (mulA₀' hχ (mulA₀ hLf (G_memA₀ hf hχ)))).congr
      (Eventually.of_forall fun x => by ring)
  have d2 : ∫ x, G T f ((χ * χ) * T.L f) x ∂T.μ =
      ∫ x, χ x ^ 2 * G T f (T.L f) x ∂T.μ + 2 * ∫ x, χ x * T.L f x * G T f χ x ∂T.μ := by
    rw [← integral_const_mul, ← integral_add iB (i3.const_mul 2)]
    refine integral_congr_ae ?_
    filter_upwards [e1, e2] with x h1 h2
    rw [h1, h2]; simp only [Pi.mul_apply]; ring
  have d3 : ∫ x, ((χ * χ) * T.L f) x * T.L f x ∂T.μ = ∫ x, χ x ^ 2 * T.L f x ^ 2 ∂T.μ :=
    integral_congr_ae (Eventually.of_forall fun x => by simp only [Pi.mul_apply]; ring)
  -- (f) Γ₂ f f
  have iA1 := hI (T.L (G T f f)) hLp
  have f1 : ∫ x, χ x ^ 2 * T.toDiffusionTriple.Γ₂ f f x ∂T.μ =
      (∫ x, χ x ^ 2 * T.L (G T f f) x ∂T.μ) / 2 - ∫ x, χ x ^ 2 * G T f (T.L f) x ∂T.μ := by
    rw [← integral_div, ← integral_sub (iA1.div_const 2) iB]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    show χ x ^ 2 * T.toDiffusionTriple.Γ₂ f f x = _
    rw [Γ₂_eq, G_comm (T.L f) f]; ring
  have iL2 := hI (fun x => T.L f x ^ 2) (by
    have : (fun x => T.L f x ^ 2) = T.L f * T.L f := by funext x; simp [sq]
    rw [this]; exact T.A.mul_mem hLf hLf)
  rw [b3] at b1
  have d4 : ∫ x, χ x ^ 2 * T.L f x ^ 2 ∂T.μ = - ∫ x, G T f ((χ * χ) * T.L f) x ∂T.μ := by
    rw [d1, ← d3]; ring
  rw [d2] at d4
  linarith

/-- **Cut-off bound**: for `χ ∈ 𝒜₀` with `0 ≤ χ ≤ 1`, `Γ(χ) ≤ 1` (a.e.), `f ∈ 𝒜` with `Γ(f), Γ₂(f) ∈ L¹`, under
`CD(ρ,n)`: `∫ χ² (Lf)² ≤ 4 ∫ (Γ₂(f) − ρΓ(f)) + 2 (|ρ| + 3) ∫ Γ(f)`, uniformly in `χ`. -/
theorem cutoff_bound {ρ : ℝ} {n : ℝ≥0∞} (hCD : T.CD ρ n) {χ f : E → ℝ} (hχ : χ ∈ T.A₀)
    (h0 : 0 ≤ᵐ[T.μ] χ) (h1 : χ ≤ᵐ[T.μ] fun _ => (1 : ℝ)) (hΓχ : G T χ χ ≤ᵐ[T.μ] fun _ => (1 : ℝ))
    (hf : f ∈ T.A) (hG : Integrable (G T f f) T.μ) (hG2 : Integrable (T.toDiffusionTriple.Γ₂ f f) T.μ) :
    ∫ x, χ x ^ 2 * T.L f x ^ 2 ∂T.μ ≤
      4 * ∫ x, (T.toDiffusionTriple.Γ₂ f f x - ρ * G T f f x) ∂T.μ +
        2 * (|ρ| + 3) * ∫ x, G T f f x ∂T.μ := by
  have hχA := A₀_memA hχ
  have hLf := L_memA hf
  have hSA₀ : χ * χ ∈ T.A₀ := T.A₀.mul_mem hχ hχ
  have iK : Integrable (fun x => T.toDiffusionTriple.Γ₂ f f x - ρ * G T f f x) T.μ :=
    hG2.sub (hG.const_mul ρ)
  have hK := K_nonneg hCD hf
  have ha := T.ΓA_nonneg f hf
  have hI : ∀ u : E → ℝ, u ∈ T.A → Integrable (fun x => χ x ^ 2 * u x) T.μ := by
    intro u hu
    refine (intA₀ (mulA₀ hu hSA₀)).congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.mul_apply]; ring
  have iX : Integrable (fun x => χ x ^ 2 * T.L f x ^ 2) T.μ := by
    have : (fun x => T.L f x ^ 2) = T.L f * T.L f := by funext x; simp [sq]
    exact hI (fun x => T.L f x ^ 2) (this ▸ T.A.mul_mem hLf hLf)
  have hp := G_mem hf hf
  have iJ : Integrable (fun x => χ x * G T (G T f f) χ x) T.μ :=
    intA₀ (mulA₀' hχ (G_memA₀ hp hχ))
  have i3 : Integrable (fun x => χ x * T.L f x * G T f χ x) T.μ :=
    (intA₀ (mulA₀' hχ (mulA₀ hLf (G_memA₀ hf hχ)))).congr
      (Eventually.of_forall fun x => by ring)
  have iR : Integrable (fun x => χ x ^ 2 * T.toDiffusionTriple.Γ₂ f f x) T.μ :=
    (hI _ (by
      have : T.toDiffusionTriple.Γ₂ f f = fun x => (T.L (G T f f) x - G T f (T.L f) x - G T (T.L f) f x) / 2 := by
        funext x; exact Γ₂_eq f f x
      rw [this]
      have e : (fun x => (T.L (G T f f) x - G T f (T.L f) x - G T (T.L f) f x) / 2) =
          (1 / 2 : ℝ) • (T.L (G T f f) - G T f (T.L f) - G T (T.L f) f) := by
        funext x; simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring
      rw [e]
      exact T.A.smul_mem (T.A.sub_mem (T.A.sub_mem (L_memA hp) (G_mem hf hLf)) (G_mem hLf hf)) _))
  have iA : Integrable (fun x => G T f f x) T.μ := hG
  have idn := cutoff_Γ₂_identity hχ hf
  -- bound for R1
  have m1 : ∫ x, χ x ^ 2 * T.toDiffusionTriple.Γ₂ f f x ∂T.μ ≤
      ∫ x, (T.toDiffusionTriple.Γ₂ f f x - ρ * G T f f x) ∂T.μ + |ρ| * ∫ x, G T f f x ∂T.μ := by
    rw [← integral_const_mul, ← integral_add iK (hG.const_mul _)]
    refine integral_mono_ae iR (iK.add (hG.const_mul _)) ?_
    filter_upwards [hK, ha, h0, h1] with x k a c1 c2
    have c1' : 0 ≤ χ x := c1
    have c2' : χ x ≤ 1 := c2
    have a' : 0 ≤ G T f f x := a
    have hc : χ x ^ 2 ≤ 1 := by nlinarith
    have hc0 : 0 ≤ χ x ^ 2 := sq_nonneg _
    have t1 : χ x ^ 2 * (T.toDiffusionTriple.Γ₂ f f x - ρ * G T f f x) ≤
        T.toDiffusionTriple.Γ₂ f f x - ρ * G T f f x := by nlinarith
    have t2 : ρ * (χ x ^ 2 * G T f f x) ≤ |ρ| * G T f f x := by
      calc ρ * (χ x ^ 2 * G T f f x) ≤ |ρ| * (χ x ^ 2 * G T f f x) :=
            mul_le_mul_of_nonneg_right (le_abs_self ρ) (mul_nonneg hc0 a')
        _ ≤ |ρ| * G T f f x := mul_le_mul_of_nonneg_left (by nlinarith) (abs_nonneg ρ)
    have e : χ x ^ 2 * T.toDiffusionTriple.Γ₂ f f x =
        χ x ^ 2 * (T.toDiffusionTriple.Γ₂ f f x - ρ * G T f f x) + ρ * (χ x ^ 2 * G T f f x) := by ring
    show χ x ^ 2 * T.toDiffusionTriple.Γ₂ f f x ≤ _
    linarith
  -- bound for J (Hessian Cauchy-Schwarz)
  have m2 : ∫ x, χ x * G T (G T f f) χ x ∂T.μ ≤
      ∫ x, (T.toDiffusionTriple.Γ₂ f f x - ρ * G T f f x) ∂T.μ + ∫ x, G T f f x ∂T.μ := by
    rw [← integral_add iK hG]
    refine integral_mono_ae iJ (iK.add hG) ?_
    filter_upwards [hessCS hCD hf hχA, hK, ha, h0, h1, hΓχ, T.ΓA_nonneg χ hχA] with x hs k a c1 c2 g1 g0
    have c1' : 0 ≤ χ x := c1
    have c2' : χ x ≤ 1 := c2
    have a' : 0 ≤ G T f f x := a
    have g1' : G T χ χ x ≤ 1 := g1
    have hs' : G T (G T f f) χ x ^ 2 ≤ 4 * (T.toDiffusionTriple.Γ₂ f f x - ρ * G T f f x) *
        (G T χ χ x * G T f f x) := by rw [G_comm (G T f f) χ]; exact hs
    have g0' : 0 ≤ G T χ χ x := g0
    set h := G T (G T f f) χ x with hh
    set K := T.toDiffusionTriple.Γ₂ f f x - ρ * G T f f x with hKdef
    have hKa : 0 ≤ K * G T f f x := mul_nonneg k a'
    have h2 : (χ x * h) ^ 2 ≤ (K + G T f f x) ^ 2 := by
      have e1 : (χ x * h) ^ 2 = χ x ^ 2 * h ^ 2 := by ring
      have e2 : χ x ^ 2 ≤ 1 := by nlinarith
      have e3 : h ^ 2 ≤ 4 * K * G T f f x := by
        have : 4 * K * (G T χ χ x * G T f f x) ≤ 4 * K * G T f f x := by
          have : G T χ χ x * G T f f x ≤ G T f f x := by nlinarith
          nlinarith
        linarith
      have e4 : χ x ^ 2 * h ^ 2 ≤ h ^ 2 := by nlinarith [sq_nonneg h]
      nlinarith [sq_nonneg (K - G T f f x)]
    have h3 := abs_le_of_sq_le_sq h2 (add_nonneg k a')
    exact (le_abs_self _).trans h3
  -- bound for the last term
  have m3 : -(2 * ∫ x, χ x * T.L f x * G T f χ x ∂T.μ) ≤
      (1 / 2) * ∫ x, χ x ^ 2 * T.L f x ^ 2 ∂T.μ + 2 * ∫ x, G T f f x ∂T.μ := by
    have : -(2 * ∫ x, χ x * T.L f x * G T f χ x ∂T.μ) = ∫ x, -(2 * (χ x * T.L f x * G T f χ x)) ∂T.μ := by
      rw [integral_neg, integral_const_mul]
    rw [this, ← integral_const_mul, ← integral_const_mul, ← integral_add (iX.const_mul _) (hG.const_mul _)]
    refine integral_mono_ae (i3.const_mul 2 |>.neg |>.congr (Eventually.of_forall fun x => by simp)) ?_ ?_
    · exact (iX.const_mul _).add (hG.const_mul _)
    · filter_upwards [ExtendedAlgebra.ΓA_cs T.extendedAlgebra hf hχA, ha, hΓχ] with x hs a g1
      have a' : 0 ≤ G T f f x := a
      have g1' : G T χ χ x ≤ 1 := g1
      have hs' : G T f χ x ^ 2 ≤ G T f f x * G T χ χ x := hs
      have : G T f χ x ^ 2 ≤ G T f f x := by nlinarith
      show -(2 * (χ x * T.L f x * G T f χ x)) ≤ _
      nlinarith [sq_nonneg (χ x * T.L f x + 2 * G T f χ x)]
  linarith
/-- **`L f ∈ L²` from the cut-off `Γ₂` argument** (BGL Prop. 3.2.1-style cut-offs, Def. 3.3.9, applied to `Γ₂`).
Hypotheses: completeness (cut-offs `ζ_k`), `CD(ρ,n)`, `f ∈ 𝒜`, `Γ(f), Γ₂(f) ∈ L¹`.  No `Core2`, no `f ∈ L²`.
Moreover `‖Lf‖₂² ≤ 4 ∫ (Γ₂(f) − ρΓ(f)) + 2 (|ρ|+3) ∫ Γ(f)` (see `cutoff_bound`). -/
theorem memLp_L_of_Γ₂ {ρ : ℝ} {n : ℝ≥0∞} (hC : T.toDiffusionTriple.IsComplete) (hCD : T.CD ρ n)
    {f : E → ℝ} (hf : f ∈ T.A) (hG : Integrable (G T f f) T.μ)
    (hG2 : Integrable (T.toDiffusionTriple.Γ₂ f f) T.μ) : MemLp (T.L f) 2 T.μ := by
  obtain ⟨ζ, hζ0, hζpos, hζmono, hζlim, hζΓ⟩ := hC
  set C : ℝ := 4 * ∫ x, (T.toDiffusionTriple.Γ₂ f f x - ρ * G T f f x) ∂T.μ +
    2 * (|ρ| + 3) * ∫ x, G T f f x ∂T.μ with hCdef
  have hLf := L_memA hf
  have hmeas : Measurable (T.L f) := T.A_measurable _ hLf
  -- ζ k ≤ 1
  have hle1 : ∀ᵐ x ∂T.μ, ∀ k, ζ k x ≤ 1 := by
    have hm := ae_all_iff.2 (fun k => hζmono k)
    filter_upwards [hm, hζlim] with x hx hl k
    have : Monotone (fun k => ζ k x) := monotone_nat_of_le_succ (fun k => hx k)
    exact this.ge_of_tendsto hl k
  have hbd : ∀ k, ∫ x, ζ k x ^ 2 * T.L f x ^ 2 ∂T.μ ≤ C := by
    intro k
    have hk1 : ζ k ≤ᵐ[T.μ] fun _ => (1 : ℝ) := by
      filter_upwards [hle1] with x hx using hx k
    have hk2 : G T (ζ k) (ζ k) ≤ᵐ[T.μ] fun _ => (1 : ℝ) := by
      filter_upwards [DiffusionTriple.ΓA_ae_eq T.toDiffusionTriple (hζ0 k) (hζ0 k), hζΓ k] with x a b
      rw [show G T (ζ k) (ζ k) x = T.toDiffusionTriple.ΓA (ζ k) (ζ k) x from rfl, a]
      refine b.trans ?_
      have : (1 : ℝ) / ((k : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
      have h0 : 0 ≤ (1 : ℝ) / ((k : ℝ) + 1) := by positivity
      nlinarith
    exact cutoff_bound hCD (hζ0 k) (hζpos k) hk1 hk2 hf hG hG2
  -- Fatou
  have hnn : ∀ k, 0 ≤ᵐ[T.μ] fun x => ζ k x ^ 2 * T.L f x ^ 2 :=
    fun k => Eventually.of_forall fun x => by positivity
  have hmeasζ : ∀ k, Measurable (ζ k) := fun k => T.A_measurable _ (A₀_memA (hζ0 k))
  have hint : ∀ k, Integrable (fun x => ζ k x ^ 2 * T.L f x ^ 2) T.μ := by
    intro k
    have hSA₀ : ζ k * ζ k ∈ T.A₀ := T.A₀.mul_mem (hζ0 k) (hζ0 k)
    have : (fun x => T.L f x ^ 2) = T.L f * T.L f := by funext x; simp [sq]
    have hL2 : (T.L f * T.L f) ∈ T.A := T.A.mul_mem hLf hLf
    refine (intA₀ (mulA₀ hL2 hSA₀)).congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.mul_apply]; ring
  have hF : ∫⁻ x, ENNReal.ofReal (T.L f x ^ 2) ∂T.μ ≤ ENNReal.ofReal C := by
    calc ∫⁻ x, ENNReal.ofReal (T.L f x ^ 2) ∂T.μ
        = ∫⁻ x, liminf (fun k => ENNReal.ofReal (ζ k x ^ 2 * T.L f x ^ 2)) atTop ∂T.μ := by
          refine lintegral_congr_ae ?_
          filter_upwards [hζlim] with x hx
          have : Tendsto (fun k => ENNReal.ofReal (ζ k x ^ 2 * T.L f x ^ 2)) atTop
              (𝓝 (ENNReal.ofReal (T.L f x ^ 2))) := by
            have h1 : Tendsto (fun k => ζ k x ^ 2 * T.L f x ^ 2) atTop (𝓝 (1 ^ 2 * T.L f x ^ 2)) :=
              (hx.pow 2).mul_const _
            rw [one_pow, one_mul] at h1
            exact (ENNReal.continuous_ofReal.tendsto _).comp h1
          exact this.liminf_eq.symm
      _ ≤ liminf (fun k => ∫⁻ x, ENNReal.ofReal (ζ k x ^ 2 * T.L f x ^ 2) ∂T.μ) atTop :=
          lintegral_liminf_le (fun k => (((hmeasζ k).pow_const 2).mul (hmeas.pow_const 2)).ennreal_ofReal)
      _ ≤ ENNReal.ofReal C := by
          refine Filter.liminf_le_of_frequently_le' (Eventually.of_forall fun k => ?_).frequently
          rw [← ofReal_integral_eq_lintegral_ofReal (hint k) (hnn k)]
          exact ENNReal.ofReal_le_ofReal (hbd k)
  have hgi : Integrable (fun x => T.L f x ^ 2) T.μ := by
    refine (lintegral_ofReal_ne_top_iff_integrable (hmeas.pow_const 2).aestronglyMeasurable
      (Eventually.of_forall fun x => by positivity)).1 ?_
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hF
  exact (memLp_two_iff_integrable_sq hmeas.aestronglyMeasurable).2 hgi

/-- **Direct converse of BGL Prop. 3.3.17, without `Core2`** (Round 20, D3; see the module docstring, DIFFERENCE FROM BGL).
`f ∈ 𝒜 ∩ L²`, `Γ(f), Γ₂(f) ∈ L¹`, `CD(ρ,n)`, completeness and ESA (field F10) ⇒ `[f] ∈ 𝒟(L̄)`, `L̄[f] = [Lf]`.  Same conclusion as
`mem_domain_of_Γ₂`, with `Core2` replaced by completeness (Def. 3.3.9).  Ergodicity is not used. -/
theorem mem_domain_of_Γ₂_direct {ρ : ℝ} {n : ℝ≥0∞} (hC : T.toDiffusionTriple.IsComplete) (hCD : T.CD ρ n)
    {f : E → ℝ} (hf : f ∈ T.A) (hf2 : MemLp f 2 T.μ) (hG : Integrable (G T f f) T.μ)
    (hG2 : Integrable (T.toDiffusionTriple.Γ₂ f f) T.μ) :
    ∃ hF : hf2.toLp f ∈ T.toDiffusionTriple.generator.domain,
      ((T.toDiffusionTriple.generator ⟨hf2.toLp f, hF⟩ : Lp ℝ 2 T.μ) : E → ℝ) =ᵐ[T.μ] T.L f := by
  have hLf2 := memLp_L_of_Γ₂ hC hCD hf hG hG2
  obtain ⟨hF, hFe⟩ := mem_domain_of_maximal hf hf2 hLf2
  refine ⟨hF, ?_⟩
  rw [hFe]
  exact hLf2.coeFn_toLp

end FullTriple

end MarkovTriple.BGL
