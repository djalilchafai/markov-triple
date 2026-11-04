import Mathlib
import MarkovTriple.BGL.Instances.Riemannian.BochnerRiem
import MarkovTriple.BGL.Instances.Riemannian.BochnerConverse
import MarkovTriple.BGL.Instances.Riemannian.BochnerCrit
import MarkovTriple.BGL.Instances.GibbsRd.DirectEllCore

/-!
# Direct converse of BGL Prop. 3.3.17: the Hessian Cauchy–Schwarz for a weighted Riemannian chart (R20, Stream D2)

Statements: `STATEMENTS_R20_DirectEll.md` (D3).

## DIFFERENCE FROM BGL

*BGL* (Prop. 3.3.17, p. 161-162) needs `Core2` (ERRATA R15-1) for the converse; R19 proved it under `CoreCut`, which needs
bounded `Γ₂(χ_n)`, `Lχ_n`, ... for the cut-offs and FAILS for the hyperbolic plane.  *Here* the cut-off argument of
`GibbsRd/DirectEllCore.lean` (BGL Prop. 3.2.1 technique applied to `Γ₂`) needs, besides `Γ(χ) ≤ 1`, only the pointwise estimate
for the cross term `Γ(χ, Γ f) = 2 Hess f(∇χ, ∇f)`:

`Γ(u, Γ f)² ≤ 4 Γ(u) Γ(f) (Γ₂(f) − ρΓ(f))`        (`RiemData.riem_hessCS`).

Proof (Bochner, BGL (1.16.4), Thm C.3.3, in the global chart): `Γ₂(f) = ‖Hess f‖²_g + (Ric + ∇∇W)(∇f,∇f)` (`riem_bochner`),
`Ric + ∇∇W ≥ ρ g` (`riem_ricci_of_curv`, from `Curv ρ`) give `‖Hess f‖²_g ≤ Γ₂(f) − ρΓ(f)`; and
`Γ(u,Γf) = 2⟨Hess f, du ⊗ df⟩_g` (`pderiv_GamF_self`) with the Cauchy–Schwarz inequality for the semi-definite form
`⟨A,B⟩_g = Σ g^{ik} g^{jl} A_{ij} B_{kl}` (`hess_cs`; semi-definiteness is `hessNorm_nonneg`).  Hypotheses: `Curv ρ` only (`ρ` of any sign).
-/

open MeasureTheory Filter Topology

namespace MarkovTriple.BGL.Instances.Riemannian

open MarkovTriple.BGL.Instances.GibbsRd
open MarkovTriple.BGL (pderiv pderiv₂ DiffusionTriple)

variable {d : ℕ}

namespace RiemData
variable (R : RiemData d)

/-- **Cauchy–Schwarz for the Hessian form**: `⟨H, q⊗p⟩² ≤ ⟨H,H⟩ ⟨q,q⟩⟨p,p⟩` for `⟨A,B⟩ = Σ g^{ik} g^{jl} A_{ij} B_{kl}`. -/
lemma hess_cs (x : Rd d) (H : Fin d → Fin d → ℝ) (q p : Fin d → ℝ) :
    (∑ i, ∑ j, ∑ k, ∑ l, R.g i k x * R.g j l x * H i j * (q k * p l)) ^ 2 ≤
      (∑ i, ∑ j, ∑ k, ∑ l, R.g i k x * R.g j l x * H i j * H k l) *
        ((∑ i, ∑ j, R.g i j x * q i * q j) * (∑ i, ∑ j, R.g i j x * p i * p j)) := by
  set A := ∑ i, ∑ j, ∑ k, ∑ l, R.g i k x * R.g j l x * H i j * H k l with hA
  set X := ∑ i, ∑ j, ∑ k, ∑ l, R.g i k x * R.g j l x * H i j * (q k * p l) with hX
  set Y := (∑ i, ∑ j, R.g i j x * q i * q j) * (∑ i, ∑ j, R.g i j x * p i * p j) with hY
  have hX2 : ∑ i, ∑ j, ∑ k, ∑ l, R.g i k x * R.g j l x * H k l * (q i * p j) = X := by
    rw [hX]
    sums4s [fun i j => R.g_symm i j x]
  have hY' : ∑ i, ∑ j, ∑ k, ∑ l, R.g i k x * R.g j l x * (q i * p j) * (q k * p l) = Y := by
    rw [hY, Finset.sum_mul_sum]
    simp only [Finset.mul_sum, Finset.sum_mul]
    sums4
  refine cs_of_nonneg_quad (A := A) (B := X) (C := Y) fun t => ?_
  have h := R.hessNorm_nonneg (fun i j => H i j + t * (q i * p j)) x
  have e : ∑ i, ∑ j, ∑ k, ∑ l, R.g i k x * R.g j l x * (H i j + t * (q i * p j)) *
      (H k l + t * (q k * p l)) =
      A + t * X + t * (∑ i, ∑ j, ∑ k, ∑ l, R.g i k x * R.g j l x * H k l * (q i * p j)) +
        t ^ 2 * (∑ i, ∑ j, ∑ k, ∑ l, R.g i k x * R.g j l x * (q i * p j) * (q k * p l)) := by
    simp only [hA, hX, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  rw [e, hX2, hY'] at h
  linarith

/-- `‖Hess f‖²_g ≤ Γ₂(f) − ρΓ(f)` pointwise, from Bochner's formula and `Curv ρ` -/
lemma hessNorm_le_G2' {ρ : ℝ} (hρ : R.Curv ρ) {f : Rd d → ℝ} (hf : Sm f) (x : Rd d) :
    ∑ i, ∑ j, ∑ k, ∑ l, R.g i k x * R.g j l x * R.hess f i j x * R.hess f k l x ≤
      R.toEll.G2' ρ f f x := by
  have h0 := R.riem_bochner hf x
  have h1 := congrFun (R.toEll.Γ₂_eq_comb hf) x
  have h2 : R.riemDiff.Γ₂ f f x = R.toEll.G2 f f x := by
    show R.toEll.diff.Γ₂ f f x = _
    rw [h1]
    unfold EllData.G2
    rw [R.toEll.Γ_symm_apply f (R.toEll.L f) x]
  have hric := R.riem_ricci_of_curv hρ x (fun i => R.grad f i x)
  have hΓ := R.Gam_eq_gl_grad f x
  have hΓ' : R.toEll.Γ f f x = R.GamF f f x := rfl
  unfold EllData.G2'
  rw [← h2, h0, hΓ', hΓ]
  linarith

/-- **D3: the Hessian Cauchy–Schwarz** `Γ(u,Γf)² ≤ 4Γ(u)Γ(f)(Γ₂(f) − ρΓ(f))` for a weighted Riemannian chart with `Curv ρ`. -/
theorem riem_hessCS {ρ : ℝ} (hρ : R.Curv ρ) : R.toEll.HessCS ρ := by
  intro f u hf hu x
  have e1 : R.toEll.Γ u (R.toEll.Γ f f) x =
      2 * ∑ i, ∑ j, ∑ k, ∑ l, R.g i k x * R.g j l x * R.hess f i j x * (pderiv u k x * pderiv f l x) := by
    show ∑ k, ∑ l, R.g k l x * pderiv u k x * pderiv (R.GamF f f) l x = _
    simp only [R.pderiv_GamF_self hf, Finset.mul_sum]
    sums4s [fun i j => R.g_symm i j x]
  have hcs := R.hess_cs x (fun i j => R.hess f i j x) (fun i => pderiv u i x) (fun i => pderiv f i x)
  have hHN := R.hessNorm_le_G2' hρ hf x
  have hQu : R.toEll.Γ u u x = ∑ i, ∑ j, R.g i j x * pderiv u i x * pderiv u j x := rfl
  have hQf : R.toEll.Γ f f x = ∑ i, ∑ j, R.g i j x * pderiv f i x * pderiv f j x := rfl
  have h0u := R.toEll.Γ_nonneg u x
  have h0f := R.toEll.Γ_nonneg f x
  rw [e1]
  rw [hQu, hQf] at *
  have hm := mul_le_mul_of_nonneg_right hHN (mul_nonneg h0u h0f)
  nlinarith [hcs, hm]

end RiemData

end MarkovTriple.BGL.Instances.Riemannian
