import Mathlib
import MarkovTriple.BGL.Instances.GibbsRd.Core2RdEnergy

/-!
# `Hess v ∈ L²(μ)` for the resolvent solution WITHOUT a bound on `L(cut R)` (R19, Stream A5, target C1)

Statements: `STATEMENTS_R19_Core2Rd.md` (C1).  R18 (`hess_bound`) integrated `∫ φ LΓ(v) = ∫ Γ(v) Lφ` and needed `|L(cut R)| ≤ K`
(bounded `Hess V`, `∇³V`).  Here `∫ φ LΓ(v) = −∫ Γ(φ, Γ v)` and Young's inequality
`−2ψ q_k h_{lk} a_l ≤ ¼ ψ² h_{lk}² + 4 q_k² a_l²` absorb `∇φ ∇Γ(v) = 4ψ Σ q_k a_l h_{lk}` into `∫ φ ‖Hess v‖²`;
only `Σ|∂ₖ cut|² ≤ 8C²` is used, and `Hess V ≥ ρ` (`ρ` of any sign) enters through the Bochner formula `Γ₂ ≥ ρΓ` (BGL Sect. 3.2-3.3).
-/

open MeasureTheory Filter Topology

namespace MarkovTriple.BGL.Instances.GibbsRd

open MarkovTriple.BGL (pderiv)

variable {d : ℕ}

/-- Young step for `−½ ∇φ·∇Γ(v)`. -/
lemma hessIBP_pt {ψ Q : ℝ} {q a : Fin d → ℝ} {h : Fin d → Fin d → ℝ} (hq : ∑ k, q k * q k ≤ Q) :
    -(∑ k, (q k * ψ + ψ * q k) * ∑ l, (h l k * a l + a l * h l k)) / 2 ≤
      1 / 4 * (ψ * ψ * ∑ l, ∑ k, h l k ^ 2) + 4 * Q * ∑ l, a l * a l := by
  have term : ∀ k l, -((q k * ψ + ψ * q k) * (h l k * a l + a l * h l k)) / 2 ≤
      1 / 4 * (ψ * ψ * h l k ^ 2) + 4 * (q k * q k * (a l * a l)) := by
    intro k l
    nlinarith [sq_nonneg (ψ * h l k / 2 + 2 * q k * a l)]
  have eL : -(∑ k, (q k * ψ + ψ * q k) * ∑ l, (h l k * a l + a l * h l k)) / 2 =
      ∑ k, ∑ l, (-((q k * ψ + ψ * q k) * (h l k * a l + a l * h l k)) / 2) := by
    simp only [Finset.mul_sum, Finset.sum_div, neg_div, Finset.sum_neg_distrib]
  rw [eL]
  refine (Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ => term k l).trans ?_
  have e1 : ∑ k : Fin d, ∑ l : Fin d, (1 / 4 * (ψ * ψ * h l k ^ 2) + 4 * (q k * q k * (a l * a l))) =
      1 / 4 * (ψ * ψ * ∑ l, ∑ k, h l k ^ 2) + 4 * ((∑ k, q k * q k) * ∑ l, a l * a l) := by
    simp only [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
    congr 1 <;> exact Finset.sum_comm
  rw [e1]
  have h0 : 0 ≤ ∑ l, a l * a l := Finset.sum_nonneg fun _ _ => mul_self_nonneg _
  nlinarith [mul_le_mul_of_nonneg_right hq h0]

namespace GibbsRdData

/-- Hessian estimate, integral form, no bound on `L(cut R)`. -/
theorem hess_bound_free (G : GibbsRdData d) {v a : Rd d → ℝ} (hv : Sm v) (ha : a ∈ A₀ d)
    (hv2 : MemLp v 2 G.toEll.μ) (hL : ∀ x, Lr G.V v x = v x - a x) {ρ : ℝ} (hρ : HessGe G.V ρ) :
    ∃ B : ℝ, ∀ (n : ℕ) (i j : Fin d),
      ∫ x, (cut ((n : ℝ) + 1) x * pderiv (pderiv v i) j x) ^ 2 ∂G.toEll.μ ≤ B := by
  obtain ⟨C, hC0, hC⟩ := sT_deriv_bound
  set μ := G.toEll.μ with hμ
  have hgrad : ∀ i, MemLp (pderiv v i) 2 μ := G.memLp_grad_resolvent hv ha hv2 hL
  have iGvv : Integrable (Gr v v) μ := by
    have h1 : ∀ i ∈ (Finset.univ : Finset (Fin d)),
        Integrable (fun x => pderiv v i x * pderiv v i x) μ := fun i _ => by
      simpa [sq] using (hgrad i).integrable_sq
    exact integrable_finsetSum _ h1
  have iGaa : Integrable (Gr a a) μ := G.int_cs (G.sm_Gr' ha.1 ha.1).continuous (G.hcs_Gr_left ha.2)
  set W : Rd d → ℝ := fun x => 1 / 2 * (Gr v v x + Gr a a x) + |ρ| * Gr v v x with hW
  have iW : Integrable W μ := ((iGvv.add iGaa).const_mul (1 / 2)).add (iGvv.const_mul |ρ|)
  refine ⟨4 / 3 * (4 * (8 * C ^ 2) * ∫ x, Gr v v x ∂μ + ∫ x, W x ∂μ), fun n i j => ?_⟩
  set R : ℝ := (n : ℝ) + 1 with hR
  have hRpos : 0 < R := by positivity
  have hR1 : 1 ≤ R := by rw [hR]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  set ψ : Rd d → ℝ := cut R with hψdef
  have hψ : Sm ψ := sm_cut R
  have hψc : HasCompactSupport ψ := hcs_cut hRpos
  have hq : ∀ x, ∑ k, pderiv ψ k x * pderiv ψ k x ≤ 8 * C ^ 2 := fun x => by
    have := (sum_sq_pderiv_cut_le hRpos hC x).trans (div_le_self (by positivity) (one_le_pow₀ hR1))
    simpa [sq] using this
  have hφ : Sm (ψ * ψ) := hψ.mul hψ
  have hφc : HasCompactSupport (ψ * ψ) := hψc.mul_right
  have hΓ : Sm (Gr v v) := G.sm_Gr' hv hv
  have iA : Integrable (fun x => (ψ * ψ) x * Lr G.V (Gr v v) x) μ :=
    G.int_cs (hφ.continuous.mul (sm_Lr G.smooth hΓ).continuous) hφc.mul_right
  have iT : Integrable (fun x => Gr (ψ * ψ) (Gr v v) x) μ :=
    G.int_cs (G.sm_Gr' hφ hΓ).continuous (G.hcs_Gr_left hφc)
  have hA : ∫ x, (ψ * ψ) x * Lr G.V (Gr v v) x ∂μ = -∫ x, Gr (ψ * ψ) (Gr v v) x ∂μ :=
    G.ibp_Lr hΓ hφ (Or.inl hφc)
  have hHv : Continuous (fun x => ∑ k, ∑ l, pderiv (pderiv v k) l x ^ 2) :=
    continuous_finsetSum _ fun k _ => continuous_finsetSum _ fun l _ =>
      ((hv.pderiv k).pderiv l).continuous.pow 2
  have iHv : Integrable (fun x => (ψ * ψ) x * ∑ k, ∑ l, pderiv (pderiv v k) l x ^ 2) μ :=
    G.int_cs (hφ.continuous.mul hHv) hφc.mul_right
  have hpt : ∀ x, (ψ * ψ) x * ∑ k, ∑ l, pderiv (pderiv v k) l x ^ 2 ≤
      (ψ * ψ) x * Lr G.V (Gr v v) x / 2 + W x := by
    intro x
    have hb := G.bochner_pt hv x
    have hgs := G.gr_sub hv ha.1 hL x
    have hcm : Gr (Lr G.V v) v x = Gr v (Lr G.V v) x := congrFun (gr_comm _ _) x
    have hQ : ρ * Gr v v x ≤ ∑ k, ∑ l, pderiv (pderiv G.V k) l x * pderiv v k x * pderiv v l x := by
      have := hρ x (fun k => pderiv v k x)
      simpa [Gr, sq] using this
    have ht : Gr v a x ≤ (Gr v v x + Gr a a x) / 2 := by
      unfold Gr
      rw [← Finset.sum_add_distrib, Finset.sum_div]
      exact Finset.sum_le_sum fun k _ => by nlinarith [sq_nonneg (pderiv v k x - pderiv a k x)]
    have hs0 : 0 ≤ Gr v v x := Finset.sum_nonneg fun k _ => mul_self_nonneg _
    have hr0 : 0 ≤ Gr a a x := Finset.sum_nonneg fun k _ => mul_self_nonneg _
    have key := hess_pt (φ := (ψ * ψ) x) (s := Gr v v x) (t := Gr v a x) (r := Gr a a x)
      (Q := ∑ k, ∑ l, pderiv (pderiv G.V k) l x * pderiv v k x * pderiv v l x) (ρ := ρ)
      (Hv := ∑ k, ∑ l, pderiv (pderiv v k) l x ^ 2) (X := (ψ * ψ) x * Lr G.V (Gr v v) x)
      (mul_self_nonneg _) (by have := cut_le_one R x; have := cut_nonneg R x; simp only [Pi.mul_apply]
                              nlinarith) hs0 hr0 ht hQ (by
        have e : ∑ k, ∑ l, pderiv (pderiv v k) l x ^ 2 =
            (Lr G.V (Gr v v) x - Gr v (Lr G.V v) x - Gr (Lr G.V v) v x) / 2 -
            ∑ k, ∑ l, pderiv (pderiv G.V k) l x * pderiv v k x * pderiv v l x := by
          linarith
        rw [e, hcm, hgs]; ring)
    simpa only [hW] using key
  -- the IBP term, pointwise
  have hTpt : ∀ x, -(Gr (ψ * ψ) (Gr v v) x) / 2 ≤
      1 / 4 * ((ψ * ψ) x * ∑ k, ∑ l, pderiv (pderiv v k) l x ^ 2) + 4 * (8 * C ^ 2) * Gr v v x := by
    intro x
    have e1 : ∀ k, pderiv (ψ * ψ) k x = pderiv ψ k x * ψ x + ψ x * pderiv ψ k x := fun k => by
      rw [pderiv_mul (f := ψ) (g := ψ) hψ hψ]
    have key := hessIBP_pt (ψ := ψ x) (Q := 8 * C ^ 2) (q := fun k => pderiv ψ k x)
      (a := fun l => pderiv v l x) (h := fun l k => pderiv (pderiv v l) k x) (hq x)
    have e2 : Gr (ψ * ψ) (Gr v v) x = ∑ k, (pderiv ψ k x * ψ x + ψ x * pderiv ψ k x) *
        ∑ l, (pderiv (pderiv v l) k x * pderiv v l x + pderiv v l x * pderiv (pderiv v l) k x) := by
      rw [show Gr (ψ * ψ) (Gr v v) x = ∑ k, pderiv (ψ * ψ) k x * pderiv (Gr v v) k x from rfl]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [e1 k, pderiv_Gr hv k x]
    rw [e2]
    simpa [Gr, Pi.mul_apply] using key
  have iR : Integrable (fun x => (ψ * ψ) x * Lr G.V (Gr v v) x / 2 + W x) μ := (iA.div_const 2).add iW
  have hmono := integral_mono iHv iR hpt
  rw [integral_add (iA.div_const 2) iW, integral_div, hA] at hmono
  have iR2 : Integrable (fun x => 1 / 4 * ((ψ * ψ) x * ∑ k, ∑ l, pderiv (pderiv v k) l x ^ 2) +
      4 * (8 * C ^ 2) * Gr v v x) μ := (iHv.const_mul (1 / 4)).add (iGvv.const_mul (4 * (8 * C ^ 2)))
  have iT2 : Integrable (fun x => -Gr (ψ * ψ) (Gr v v) x / 2) μ := iT.neg.div_const 2
  have hT := integral_mono iT2 iR2 hTpt
  have eT : ∫ x, -Gr (ψ * ψ) (Gr v v) x / 2 ∂μ = -(∫ x, Gr (ψ * ψ) (Gr v v) x ∂μ) / 2 := by
    rw [integral_div, integral_neg]
  rw [integral_add (iHv.const_mul (1 / 4)) (iGvv.const_mul (4 * (8 * C ^ 2))), integral_const_mul,
    integral_const_mul, eT] at hT
  -- the single entry
  have i1 : Integrable (fun x => (ψ x * pderiv (pderiv v i) j x) ^ 2) μ :=
    G.int_cs ((hψ.continuous.mul ((hv.pderiv i).pderiv j).continuous).pow 2)
      ((hψc.mul_right).comp_left (g := fun y : ℝ => y ^ 2) (by simp))
  have hle : ∫ x, (ψ x * pderiv (pderiv v i) j x) ^ 2 ∂μ ≤
      ∫ x, (ψ * ψ) x * ∑ k, ∑ l, pderiv (pderiv v k) l x ^ 2 ∂μ := by
    refine integral_mono i1 iHv fun x => ?_
    have : pderiv (pderiv v i) j x ^ 2 ≤ ∑ k, ∑ l, pderiv (pderiv v k) l x ^ 2 :=
      (Finset.single_le_sum (f := fun l => pderiv (pderiv v i) l x ^ 2) (fun l _ => sq_nonneg _)
        (Finset.mem_univ j)).trans
        (Finset.single_le_sum (f := fun k => ∑ l, pderiv (pderiv v k) l x ^ 2)
          (fun k _ => Finset.sum_nonneg fun l _ => sq_nonneg _) (Finset.mem_univ i))
    have h0 := mul_self_nonneg (ψ x)
    show (ψ x * pderiv (pderiv v i) j x) ^ 2 ≤ (ψ x * ψ x) * _
    nlinarith
  linarith

/-- **C1**: `Hess v ∈ L²(μ)` under `Hess V ≥ ρ` (`ρ` of any sign) ONLY (no bound on `L(cut R)`, no growth of `V`). -/
theorem memLp_hess_resolvent_free (G : GibbsRdData d) {v a : Rd d → ℝ} (hv : Sm v) (ha : a ∈ A₀ d)
    (hv2 : MemLp v 2 G.toEll.μ) (hL : ∀ x, Lr G.V v x = v x - a x) {ρ : ℝ} (hρ : HessGe G.V ρ)
    (i j : Fin d) : MemLp (pderiv (pderiv v i) j) 2 G.toEll.μ := by
  obtain ⟨B, hB⟩ := hess_bound_free G hv ha hv2 hL hρ
  exact memLp_two_of_cut ((hv.pderiv i).pderiv j).continuous (fun n => hB n i j)

end GibbsRdData

end MarkovTriple.BGL.Instances.GibbsRd
