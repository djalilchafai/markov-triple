import Mathlib
import MarkovTriple.BGL.Instances.GibbsRd.EllipticLocalConst
import MarkovTriple.BGL.Instances.GibbsRd.EllipticCaccioppoli

/-!
# E1: the weak Caccioppoli inequality for `H¹_loc` weak solutions (R16, elliptic half)

Statement: `STATEMENTS_R16_E2.md`, E1.  Textbook: Evans PDE §6.3.1 Thm 1, Step 1 (with the test function `v = ζ²u ∈ H¹_0`,
admissible by `weakForm_extend`); Gilbarg–Trudinger (8.28).
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace MarkovTriple.BGL.Instances.GibbsRd

open MarkovTriple.BGL (pderiv)
open Elliptic

variable {d : ℕ}

/-- `c · F · G` is integrable for `F, G ∈ L²_loc` and `c` continuous with compact support. -/
lemma integrable_cs_mul_mul {F G c : Rd d → ℝ} (hF : LocL2 F) (hG : LocL2 G) (hc : Continuous c)
    (hs : HasCompactSupport c) : Integrable (fun x => c x * (F x * G x)) := by
  have h1 : LocL2 (fun x => c x * F x) := hF.mul_continuous hc
  have h2 : HasCompactSupport (fun x => c x * F x) := hs.mul_right
  have h3 := integrable_locL2_mul_cs hG (memLp_of_locL2_cs h1 h2) h2
  refine h3.congr (Eventually.of_forall fun x => ?_)
  ring

namespace EllData
variable (E : EllData d)

lemma integrable_quad {F G : Fin d → Rd d → ℝ} (hF : ∀ i, LocL2 (F i)) (hG : ∀ i, LocL2 (G i)) {c : Rd d → ℝ}
    (hc : Continuous c) (hs : HasCompactSupport c) :
    Integrable (fun x => c x * ∑ i, ∑ j, E.a i j x * F i x * G j x) := by
  have : ∀ x, c x * ∑ i, ∑ j, E.a i j x * F i x * G j x =
      ∑ i, ∑ j, (c x * E.a i j x) * (F i x * G j x) := by
    intro x
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  simp_rw [this]
  exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    integrable_cs_mul_mul (hF i) (hG j) (hc.mul (E.a_smooth i j).continuous) (hs.mul_right)

/-- pointwise Young bound for the quadratic form (vector `ζ g + 2 u ∇ζ`) -/
lemma quad_young (g ζ' : Fin d → ℝ) (x : Rd d) (z u : ℝ) :
    -(4 * z * u * ∑ i, ∑ j, E.a i j x * g i * ζ' j) ≤
      z ^ 2 * (∑ i, ∑ j, E.a i j x * g i * g j) + 4 * u ^ 2 * (∑ i, ∑ j, E.a i j x * ζ' i * ζ' j) := by
  have hq := E.quad_nonneg (fun i => z * g i + 2 * u * ζ' i) x
  have hexp : ∑ i, ∑ j, E.a i j x * (z * g i + 2 * u * ζ' i) * (z * g j + 2 * u * ζ' j) =
      z ^ 2 * (∑ i, ∑ j, E.a i j x * g i * g j) + 2 * (2 * z * u * ∑ i, ∑ j, E.a i j x * g i * ζ' j)
        + 4 * u ^ 2 * (∑ i, ∑ j, E.a i j x * ζ' i * ζ' j) := by
    have hsym : ∑ i, ∑ j, E.a i j x * ζ' i * g j = ∑ i, ∑ j, E.a i j x * g i * ζ' j := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
      rw [E.a_symm j i x]; ring
    have e1 : ∑ i, ∑ j, E.a i j x * (z * g i + 2 * u * ζ' i) * (z * g j + 2 * u * ζ' j) =
        z ^ 2 * (∑ i, ∑ j, E.a i j x * g i * g j) + 2 * z * u * (∑ i, ∑ j, E.a i j x * g i * ζ' j)
          + 2 * z * u * (∑ i, ∑ j, E.a i j x * ζ' i * g j)
          + 4 * u ^ 2 * (∑ i, ∑ j, E.a i j x * ζ' i * ζ' j) := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [e1, hsym]; ring
  rw [hexp] at hq
  linarith

/-- **E1** the weak Caccioppoli inequality (Evans §6.3.1 Thm 1 Step 1): for `u ∈ H¹_loc` with `L u = h` weakly,
`∫ w ζ² Γ(∇u) ≤ −2 ∫ h ζ² u w + 4 ∫ w u² Γ(ζ,ζ)`. -/
theorem weak_caccioppoli {u h : Rd d → ℝ} {g : Fin d → Rd d → ℝ} (hu : LocL2 u)
    (hg : ∀ i, WeakDeriv u (g i) i) (hgL : ∀ i, LocL2 (g i)) (hh : LocL2 h) (hW : E.VeryWeakSol u h)
    {ζ : Rd d → ℝ} (hζ : Sm ζ) (hc : HasCompactSupport ζ) :
    ∫ x, E.w x * (ζ x ^ 2 * ∑ i, ∑ j, E.a i j x * g i x * g j x) ≤
      -2 * (∫ x, h x * (ζ x ^ 2 * u x) * E.w x) + 4 * ∫ x, E.w x * (u x ^ 2 * E.Γ ζ ζ x) := by
  have hcw : Continuous E.w := E.w_smooth.continuous
  have hζc : Continuous ζ := hζ.continuous
  set ψ : Rd d → ℝ := ζ * ζ with hψ
  have hψS : Sm ψ := hζ.mul hζ
  have hψc : HasCompactSupport ψ := hc.mul_right
  have hψx : ∀ x, ψ x = ζ x * ζ x := fun x => rfl
  have hψd : ∀ j x, pderiv ψ j x = 2 * ζ x * pderiv ζ j x := fun j x => by
    rw [hψ, pderiv_mul hζ hζ]; ring
  set v : Rd d → ℝ := fun x => ψ x * u x with hv
  set vj : Fin d → Rd d → ℝ := fun j x => ψ x * g j x + pderiv ψ j x * u x with hvj
  have hvmem : MemLp v 2 volume :=
    memLp_of_locL2_cs (hu.mul_continuous hψS.continuous) hψc.mul_right
  have hvc : HasCompactSupport v := hψc.mul_right
  have hvjmem : ∀ j, MemLp (vj j) 2 volume := fun j => by
    refine memLp_of_locL2_cs (((hgL j).mul_continuous hψS.continuous).add
      (hu.mul_continuous (hψS.pderiv j).continuous)) ?_
    have h1 : HasCompactSupport (fun x => ψ x * g j x) := hψc.mul_right
    have h2 : HasCompactSupport (fun x => pderiv ψ j x * u x) :=
      (hψc.fderiv_apply ℝ (Pi.single j 1)).mul_right
    exact h1.add h2
  have key := E.weakForm_extend hu hg hgL hh hW hvmem hvc (fun j => (hg j).smooth_mul hψS) hvjmem
  have hζd : ∀ j, HasCompactSupport (pderiv ζ j) := fun j => hc.fderiv_apply ℝ (Pi.single j 1)
  have hζdc : ∀ j, Continuous (pderiv ζ j) := fun j => (hζ.pderiv j).continuous
  set Q : Rd d → ℝ := fun x => ∑ i, ∑ j, E.a i j x * g i x * g j x with hQ
  set Cc : Rd d → ℝ := fun x => ∑ i, ∑ j, E.a i j x * g i x * pderiv ζ j x with hC
  set I : Rd d → ℝ := fun x => E.w x * (ζ x ^ 2 * Q x) with hI
  set J : Rd d → ℝ := fun x => 2 * (E.w x * (ζ x * u x * Cc x)) with hJ
  set Zt : Rd d → ℝ := fun x => E.w x * (u x ^ 2 * E.Γ ζ ζ x) with hZ
  have hIint : Integrable I := by
    have := E.integrable_quad hgL hgL (c := fun x => E.w x * ζ x ^ 2) (hcw.mul (hζc.pow 2))
      (hcs_of_factor hc fun x hx => by simp [hx])
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp only [hI, hQ]; ring
  have hJint : Integrable J := by
    have h1 : ∀ i j, Integrable (fun x => (E.w x * ζ x * E.a i j x * pderiv ζ j x) * (u x * g i x)) := fun i j =>
      (integrable_cs_mul_mul hu (hgL i) (((hcw.mul hζc).mul (E.a_smooth i j).continuous).mul (hζdc j))
        (hζd j |>.mul_left)).congr (Eventually.of_forall fun x => by simp only [Pi.mul_apply])
    have h2 := (integrable_finsetSum Finset.univ fun i _ => integrable_finsetSum Finset.univ fun j _ => h1 i j).const_mul 2
    refine h2.congr (Eventually.of_forall fun x => ?_)
    simp only [hJ, hC, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hZint : Integrable Zt := by
    have h1 : ∀ i j, Integrable (fun x => (E.w x * E.a i j x * pderiv ζ i x * pderiv ζ j x) * (u x * u x)) := fun i j =>
      integrable_cs_mul_mul hu hu ((((hcw.mul (E.a_smooth i j).continuous).mul (hζdc i)).mul (hζdc j)))
        (hζd j |>.mul_left)
    have h2 := integrable_finsetSum Finset.univ fun i _ => integrable_finsetSum Finset.univ fun j _ => h1 i j
    refine h2.congr (Eventually.of_forall fun x => ?_)
    simp only [hZ, EllData.Γ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  -- the identity from the weak form
  have hpt : ∀ x, E.w x * ∑ i, ∑ j, E.a i j x * g i x * (ψ x * g j x + pderiv ψ j x * u x) = I x + J x := by
    intro x
    simp only [hI, hJ, hQ, hC, hψd, hψx, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hB : ∫ x, (I x + J x) = -∫ x, h x * (ζ x ^ 2 * u x) * E.w x := by
    have := key
    unfold Bf at this
    simp_rw [hpt] at this
    rw [this]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [hv, hψx]; ring
  have hmono : ∫ x, -J x ≤ ∫ x, ((1 / 2) * I x + 2 * Zt x) := by
    refine integral_mono hJint.neg ((hIint.const_mul _).add (hZint.const_mul _)) fun x => ?_
    have := E.quad_young (fun i => g i x) (fun j => pderiv ζ j x) x (ζ x) (u x)
    have hw := (E.w_pos x).le
    have h3 := mul_le_mul_of_nonneg_left this hw
    have e : E.Γ ζ ζ x = ∑ i, ∑ j, E.a i j x * pderiv ζ i x * pderiv ζ j x := rfl
    simp only [hJ, hI, hQ, hC, hZ, e]
    nlinarith [h3]
  rw [integral_neg, integral_add (hIint.const_mul _) (hZint.const_mul _), integral_const_mul (1 / 2 : ℝ) I,
    integral_const_mul (2 : ℝ) Zt] at hmono
  rw [integral_add hIint hJint] at hB
  have : ∫ x, E.w x * (ζ x ^ 2 * Q x) = ∫ x, I x := rfl
  show ∫ x, I x ≤ _
  linarith

end EllData

end MarkovTriple.BGL.Instances.GibbsRd
