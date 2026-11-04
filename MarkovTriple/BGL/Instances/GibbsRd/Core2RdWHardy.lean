import Mathlib
import MarkovTriple.BGL.Instances.GibbsRd.Core2RdEnergy
import MarkovTriple.BGL.Instances.GibbsRd.Core2RdWDefs

/-!
# The `ℝ^d` Hardy estimate: `f, ∇f ∈ L²(μ) ⇒ ∂ₖV f ∈ L²(μ)` (R19, Stream A5, target C2)

Statements: `STATEMENTS_R19_Core2Rd.md` (C2).  `d`-dimensional version of the 1-D `memLp_of_hardy` (R18, Stream A2), under
`Σ ∂ᵢ∂ᵢV ≤ |∇V|²/4 + B`.  The exact IBP is `ibp_Lr` with the test function `V`:
`∫ g (ΔV − |∇V|²) dμ = −∫ Γ(g, V) dμ`, `g = η² f²`; Young's inequality and the cut-off `η = cut R`
(`Σ |∂ᵢη|² ≤ 8C²`) absorb every term (BGL Prop. 3.2.1: Caccioppoli with cut-offs).
-/

open MeasureTheory Filter Topology

namespace MarkovTriple.BGL.Instances.GibbsRd

open MarkovTriple.BGL (pderiv)

variable {d : ℕ}

/-- the real-number part of the Hardy estimate. -/
lemma hardy_pt {ψ f Δ B Q F : ℝ} {q w u : Fin d → ℝ} (h0 : 0 ≤ ψ) (h1 : ψ ≤ 1)
    (hq : ∑ i, q i * q i ≤ Q) (hB : 0 ≤ B) (hΔ : Δ ≤ (∑ i, u i * u i) / 4 + B)
    (hF : F = ψ * ψ * (f * f) * (Δ - ∑ i, u i * u i) +
      ∑ i, ((q i * ψ + ψ * q i) * (f * f) + ψ * ψ * (w i * f + f * w i)) * u i) :
    ψ * ψ * (f * f) * ∑ i, u i * u i ≤ 4 * B * (f * f) + 16 * Q * (f * f) + 16 * ∑ i, w i * w i - 4 * F := by
  have hψ2 : ψ * ψ ≤ 1 := by nlinarith
  have hψ20 : 0 ≤ ψ * ψ := mul_self_nonneg _
  have hff : 0 ≤ f * f := mul_self_nonneg _
  have hg0 : 0 ≤ ψ * ψ * (f * f) := mul_nonneg hψ20 hff
  have hgf : ψ * ψ * (f * f) ≤ f * f := mul_le_of_le_one_left hff hψ2
  have hN0 : 0 ≤ ∑ i, u i * u i := Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have key : ∀ i, ((q i * ψ + ψ * q i) * (f * f) + ψ * ψ * (w i * f + f * w i)) * u i ≤
      1 / 2 * (ψ * ψ * (f * f) * (u i * u i)) + 4 * ((f * f) * (q i * q i)) + 4 * (w i * w i) := by
    intro i
    have h3 : ψ * ψ * (w i * w i) ≤ w i * w i := mul_le_of_le_one_left (mul_self_nonneg _) hψ2
    nlinarith [sq_nonneg (ψ * f * u i / 2 - 2 * f * q i), sq_nonneg (ψ * f * u i / 2 - 2 * ψ * w i)]
  have hS : ∑ i, ((q i * ψ + ψ * q i) * (f * f) + ψ * ψ * (w i * f + f * w i)) * u i ≤
      1 / 2 * (ψ * ψ * (f * f) * ∑ i, u i * u i) + 4 * Q * (f * f) + 4 * ∑ i, w i * w i := by
    refine (Finset.sum_le_sum fun i _ => key i).trans ?_
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    have : 4 * ((f * f) * ∑ i, q i * q i) ≤ 4 * ((f * f) * Q) := by
      have := mul_le_mul_of_nonneg_left hq hff
      linarith
    nlinarith
  have hgΔ : ψ * ψ * (f * f) * Δ ≤ ψ * ψ * (f * f) * ((∑ i, u i * u i) / 4 + B) :=
    mul_le_mul_of_nonneg_left hΔ hg0
  have hgB : ψ * ψ * (f * f) * B ≤ (f * f) * B := mul_le_mul_of_nonneg_right hgf hB
  have hF' : F = ψ * ψ * (f * f) * Δ - ψ * ψ * (f * f) * ∑ i, u i * u i +
      ∑ i, ((q i * ψ + ψ * q i) * (f * f) + ψ * ψ * (w i * f + f * w i)) * u i := by
    rw [hF]; ring
  nlinarith

namespace GibbsRdData

/-- integral form of the Hardy estimate. -/
theorem hardy_bound (G : GibbsRdData d) {f : Rd d → ℝ} (hf : Sm f) (hf2 : MemLp f 2 G.toEll.μ)
    (hf1 : ∀ i, MemLp (pderiv f i) 2 G.toEll.μ) {B : ℝ}
    (hB : ∀ x, ∑ i, pderiv (pderiv G.V i) i x ≤ Gr G.V G.V x / 4 + B) :
    ∃ M : ℝ, ∀ n : ℕ, ∫ x, cut ((n : ℝ) + 1) x ^ 2 * (f x * f x) * Gr G.V G.V x ∂G.toEll.μ ≤ M := by
  obtain ⟨C, hC0, hC⟩ := sT_deriv_bound
  set μ := G.toEll.μ with hμ
  set B' : ℝ := max B 0 with hB'
  have hB'0 : 0 ≤ B' := le_max_right _ _
  have iff2 : Integrable (fun x => f x * f x) μ := by simpa [sq] using hf2.integrable_sq
  have iGff : Integrable (Gr f f) μ := by
    have h1 : ∀ i ∈ (Finset.univ : Finset (Fin d)),
        Integrable (fun x => pderiv f i x * pderiv f i x) μ := fun i _ => by
      simpa [sq] using (hf1 i).integrable_sq
    exact integrable_finsetSum _ h1
  refine ⟨4 * B' * ∫ x, f x * f x ∂μ + 16 * (8 * C ^ 2) * ∫ x, f x * f x ∂μ + 16 * ∫ x, Gr f f x ∂μ,
    fun n => ?_⟩
  set R : ℝ := (n : ℝ) + 1 with hR
  have hRpos : 0 < R := by positivity
  have hR1 : 1 ≤ R := by rw [hR]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  set ψ : Rd d → ℝ := cut R with hψdef
  have hψ : Sm ψ := sm_cut R
  have hψc : HasCompactSupport ψ := hcs_cut hRpos
  have hq : ∀ x, ∑ i, pderiv ψ i x * pderiv ψ i x ≤ 8 * C ^ 2 := fun x => by
    have := (sum_sq_pderiv_cut_le hRpos hC x).trans (div_le_self (by positivity) (one_le_pow₀ hR1))
    simpa [sq] using this
  have hg : Sm (ψ * ψ * (f * f)) := (hψ.mul hψ).mul (hf.mul hf)
  have hgc : HasCompactSupport (ψ * ψ * (f * f)) := hψc.mul_right.mul_right
  have hI := G.ibp_Lr G.smooth hg (Or.inl hgc)
  have iA : Integrable (fun x => (ψ * ψ * (f * f)) x * Lr G.V G.V x) μ :=
    G.int_cs (hg.continuous.mul (sm_Lr G.smooth G.smooth).continuous) hgc.mul_right
  have iBb : Integrable (fun x => Gr (ψ * ψ * (f * f)) G.V x) μ :=
    G.int_cs (G.sm_Gr' hg G.smooth).continuous (G.hcs_Gr_left hgc)
  have hzero : ∫ x, ((ψ * ψ * (f * f)) x * Lr G.V G.V x + Gr (ψ * ψ * (f * f)) G.V x) ∂μ = 0 := by
    rw [integral_add iA iBb]; linarith
  have iF : Integrable (fun x => (ψ * ψ * (f * f)) x * Lr G.V G.V x +
      Gr (ψ * ψ * (f * f)) G.V x) μ := iA.add iBb
  have iL : Integrable (fun x => ψ x ^ 2 * (f x * f x) * Gr G.V G.V x) μ := by
    have hc : Continuous (fun x => ψ x ^ 2 * (f x * f x) * Gr G.V G.V x) :=
      ((hψ.continuous.pow 2).mul (hf.continuous.mul hf.continuous)).mul (G.sm_Gr' G.smooth G.smooth).continuous
    have hs : HasCompactSupport (fun x => ψ x ^ 2 * (f x * f x) * Gr G.V G.V x) :=
      ((hψc.comp_left (g := fun y : ℝ => y ^ 2) (by simp)).mul_right).mul_right
    exact G.int_cs hc hs
  set c0 : ℝ := 4 * B' + 16 * (8 * C ^ 2) with hc0
  set Fx : Rd d → ℝ := fun x => (ψ * ψ * (f * f)) x * Lr G.V G.V x + Gr (ψ * ψ * (f * f)) G.V x with hFx
  have hpt : ∀ x, ψ x ^ 2 * (f x * f x) * Gr G.V G.V x ≤ c0 * (f x * f x) + 16 * Gr f f x - 4 * Fx x := by
    intro x
    have e : ∀ i, pderiv (ψ * ψ * (f * f)) i x =
        (pderiv ψ i x * ψ x + ψ x * pderiv ψ i x) * (f x * f x) +
          ψ x * ψ x * (pderiv f i x * f x + f x * pderiv f i x) := fun i => by
      rw [pderiv_mul (f := ψ * ψ) (g := f * f) (hψ.mul hψ) (hf.mul hf), pderiv_mul (f := ψ) (g := ψ) hψ hψ,
        pderiv_mul (f := f) (g := f) hf hf]
      rfl
    have key := hardy_pt (ψ := ψ x) (f := f x) (Δ := ∑ i, pderiv (pderiv G.V i) i x) (B := B')
      (Q := 8 * C ^ 2) (F := Fx x)
      (q := fun i => pderiv ψ i x) (w := fun i => pderiv f i x) (u := fun i => pderiv G.V i x)
      (cut_nonneg R x) (cut_le_one R x) (hq x) hB'0
      (by have := hB x; unfold Gr at this; have h2 := le_max_left B 0; linarith)
      (by
        have e2 : Lr G.V G.V x = ∑ i, pderiv (pderiv G.V i) i x - ∑ i, pderiv G.V i x * pderiv G.V i x := by
          unfold Lr; rw [Finset.sum_sub_distrib]
        simp only [hFx, Gr, e, e2, Pi.mul_apply])
    have k2 : ψ x ^ 2 * (f x * f x) * Gr G.V G.V x ≤
        4 * B' * (f x * f x) + 16 * (8 * C ^ 2) * (f x * f x) + 16 * Gr f f x - 4 * Fx x := by
      simpa [Gr, sq, Pi.mul_apply, mul_assoc] using key
    rw [hc0]; linarith
  have h1 : Integrable (fun x => c0 * (f x * f x)) μ := iff2.const_mul _
  have h2 : Integrable (fun x => 16 * Gr f f x) μ := iGff.const_mul _
  have h3 : Integrable (fun x => 4 * Fx x) μ := iF.const_mul _
  have iR : Integrable (fun x => c0 * (f x * f x) + 16 * Gr f f x - 4 * Fx x) μ := (h1.add h2).sub h3
  have hmono := integral_mono iL iR hpt
  have hRint : ∫ x, (c0 * (f x * f x) + 16 * Gr f f x - 4 * Fx x) ∂μ =
      c0 * ∫ x, f x * f x ∂μ + 16 * ∫ x, Gr f f x ∂μ := by
    have e1 : ∫ x, (c0 * (f x * f x) + 16 * Gr f f x - 4 * Fx x) ∂μ =
        ∫ x, (c0 * (f x * f x) + 16 * Gr f f x) ∂μ - ∫ x, 4 * Fx x ∂μ := integral_sub (h1.add h2) h3
    have e2 : ∫ x, (c0 * (f x * f x) + 16 * Gr f f x) ∂μ =
        ∫ x, c0 * (f x * f x) ∂μ + ∫ x, 16 * Gr f f x ∂μ := integral_add h1 h2
    rw [e1, e2, integral_const_mul, integral_const_mul, integral_const_mul]
    have hz : ∫ x, Fx x ∂μ = 0 := hzero
    rw [hz]; ring
  rw [hRint] at hmono
  have : ∫ x, ψ x ^ 2 * (f x * f x) * Gr G.V G.V x ∂μ =
      ∫ x, cut ((n : ℝ) + 1) x ^ 2 * (f x * f x) * Gr G.V G.V x ∂μ := rfl
  rw [hc0] at hmono
  linarith

/-- **C2 (Hardy)**: `f ∈ L²`, `∇f ∈ L²`, `ΔV ≤ |∇V|²/4 + B` imply `∂ₖV · f ∈ L²(μ)`. -/
theorem memLp_V_mul_of_hardy (G : GibbsRdData d) {f : Rd d → ℝ} (hf : Sm f) (hf2 : MemLp f 2 G.toEll.μ)
    (hf1 : ∀ i, MemLp (pderiv f i) 2 G.toEll.μ) {B : ℝ}
    (hB : ∀ x, ∑ i, pderiv (pderiv G.V i) i x ≤ Gr G.V G.V x / 4 + B) (k : Fin d) :
    MemLp (fun x => pderiv G.V k x * f x) 2 G.toEll.μ := by
  obtain ⟨M, hM⟩ := G.hardy_bound hf hf2 hf1 hB
  refine memLp_two_of_cut ((G.smooth.pderiv k).continuous.mul hf.continuous) (B := M) (fun n => ?_)
  refine le_trans ?_ (hM n)
  have hψ : Sm (cut ((n : ℝ) + 1) : Rd d → ℝ) := sm_cut _
  have hψc := hcs_cut (d := d) (by positivity : (0 : ℝ) < (n : ℝ) + 1)
  have i1 : Integrable (fun x => (cut ((n : ℝ) + 1) x * (pderiv G.V k x * f x)) ^ 2) G.toEll.μ :=
    G.int_cs ((hψ.continuous.mul ((G.smooth.pderiv k).continuous.mul hf.continuous)).pow 2)
      ((hψc.mul_right).comp_left (g := fun y : ℝ => y ^ 2) (by simp))
  have i2 : Integrable (fun x => cut ((n : ℝ) + 1) x ^ 2 * (f x * f x) * Gr G.V G.V x) G.toEll.μ :=
    G.int_cs (((hψ.continuous.pow 2).mul (hf.continuous.mul hf.continuous)).mul
      (G.sm_Gr' G.smooth G.smooth).continuous)
      (((hψc.comp_left (g := fun y : ℝ => y ^ 2) (by simp)).mul_right).mul_right)
  refine integral_mono i1 i2 fun x => ?_
  have h1 : pderiv G.V k x * pderiv G.V k x ≤ Gr G.V G.V x :=
    Finset.single_le_sum (f := fun j => pderiv G.V j x * pderiv G.V j x) (fun j _ => mul_self_nonneg _)
      (Finset.mem_univ k)
  have h0 : 0 ≤ cut ((n : ℝ) + 1) x ^ 2 * (f x * f x) := mul_nonneg (sq_nonneg _) (mul_self_nonneg _)
  show (cut ((n : ℝ) + 1) x * (pderiv G.V k x * f x)) ^ 2 ≤ _
  nlinarith

end GibbsRdData

end MarkovTriple.BGL.Instances.GibbsRd
