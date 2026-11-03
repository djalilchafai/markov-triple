import Mathlib
import MarkovTriple.BGL.Instances.Riemannian.BochnerRiem

/-!
# The curvature criterion `Ric_g + ∇∇W ≥ ρ g ⇒ Curv ρ` (BGL (1.16.8))

* `hessNorm_nonneg`: `‖H‖²_HS = Σ g^{ik} g^{jl} H_{ij} H_{kl} ≥ 0` for every array `H` (positive definiteness of `g^{ij}`:
  Gram decomposition `g^{ik} = Σ_s S_{si} S_{sk}` through the matrix square root);
* `riem_curv_of_ricci`: if `ρ Σ g_{ij} ξ^iξ^j ≤ Σ (Ric + ∇∇W)_{ij} ξ^iξ^j` for all `x` and `ξ ∈ ℝ^d`, then `R.Curv ρ`,
  i.e. `CD(ρ,∞)` on smooth functions (Def. 3.3.14) for the formula-defined `Γ₂`.
-/

open MeasureTheory Filter Topology

namespace MarkovTriple.BGL.Instances.Riemannian

open MarkovTriple.BGL.Instances.GibbsRd
open MarkovTriple.BGL (pderiv pderiv₂ DiffusionTriple)

variable {d : ℕ}

open scoped MatrixOrder in
/-- Gram decomposition of a positive semidefinite real matrix through its square root -/
lemma gram_decomp (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.PosSemidef) :
    ∃ S : Matrix (Fin d) (Fin d) ℝ, ∀ i k, A i k = ∑ s, S s i * S s k := by
  have h0 : 0 ≤ A := Matrix.nonneg_iff_posSemidef.2 hA
  refine ⟨CFC.sqrt A, fun i k => ?_⟩
  have h1 : CFC.sqrt A * CFC.sqrt A = A := CFC.sqrt_mul_sqrt_self A h0
  have h2 : IsSelfAdjoint (CFC.sqrt A) := (CFC.sqrt_nonneg A).isSelfAdjoint
  have h3 : Matrix.transpose (CFC.sqrt A) = CFC.sqrt A := by
    have := h2.star_eq
    simpa [Matrix.star_eq_conjTranspose] using this
  have := congrFun (congrFun h1 i) k
  rw [← this, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun s _ => ?_
  have := congrFun (congrFun h3 s) i
  simp only [Matrix.transpose_apply] at this
  rw [this]

lemma p5s (F : Fin d → Fin d → Fin d → Fin d → Fin d → ℝ) :
    ∑ a, ∑ b, ∑ c, ∑ e, ∑ f, F a b c e f = ∑ f, ∑ a, ∑ b, ∑ c, ∑ e, F a b c e f := by
  calc ∑ a, ∑ b, ∑ c, ∑ e, ∑ f, F a b c e f = ∑ a, ∑ b, ∑ c, ∑ f, ∑ e, F a b c e f :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
          Finset.sum_comm
    _ = ∑ a, ∑ b, ∑ f, ∑ c, ∑ e, F a b c e f :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ a, ∑ f, ∑ b, ∑ c, ∑ e, F a b c e f :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = _ := Finset.sum_comm

lemma alg_hessnorm (g S H : Fin d → Fin d → ℝ) (hS : ∀ i k, g i k = ∑ s, S s i * S s k) :
    ∑ i, ∑ j, ∑ k, ∑ l, g i k * g j l * H i j * H k l =
      ∑ s, ∑ j, ∑ l, g j l * ((∑ i, S s i * H i j) * (∑ k, S s k * H k l)) := by
  have e : ∀ i j k l, g i k * g j l * H i j * H k l =
      (∑ s, S s i * S s k) * g j l * H i j * H k l := fun i j k l => by rw [hS i k]
  simp only [e, Finset.sum_mul, Finset.mul_sum]
  rw [p5s]
  refine Finset.sum_congr rfl fun s _ => ?_
  sums4

namespace RiemData
variable (R : RiemData d)

lemma quad_nonneg (x v : Rd d) : 0 ≤ ∑ i, ∑ j, R.g i j x * v i * v j := by
  by_cases hv : v = 0
  · subst hv; simp
  · exact (R.quad_pos x v hv).le

/-- `‖H‖²_HS ≥ 0` -/
lemma hessNorm_nonneg (H : Fin d → Fin d → ℝ) (x : Rd d) :
    0 ≤ ∑ i, ∑ j, ∑ k, ∑ l, R.g i k x * R.g j l x * H i j * H k l := by
  obtain ⟨S, hS⟩ := gram_decomp (R.mat x) (R.g_posDef x).posSemidef
  rw [alg_hessnorm (fun i j => R.g i j x) S H hS]
  refine Finset.sum_nonneg fun s _ => ?_
  have := R.quad_nonneg x (fun j => ∑ i, S s i * H i j)
  refine le_of_le_of_eq this ?_
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by ring

/-- `Γ(f,f) = Σ g_{ij} ∇^if ∇^jf` -/
lemma Gam_eq_gl_grad (f : Rd d → ℝ) (x : Rd d) :
    R.GamF f f x = ∑ i, ∑ j, R.gl i j x * R.grad f i x * R.grad f j x := by
  have h : ∀ i, pderiv f i x = ∑ s, R.gl i s x * R.grad f s x := fun i => R.pderiv_eq_gl_grad f i x
  have e : R.GamF f f x = ∑ i, R.grad f i x * pderiv f i x := by
    unfold GamF grad
    simp only [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [e]
  simp only [h, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- **Criterion (BGL (1.16.8))**: if `Ric_g + ∇∇W ≥ ρ g` (as quadratic forms at every point), then `Curv ρ`
(`CD(ρ,∞)` on smooth functions). -/
theorem riem_curv_of_ricci {ρ : ℝ}
    (h : ∀ (x ξ : Rd d), ρ * ∑ i, ∑ j, R.gl i j x * ξ i * ξ j ≤
      ∑ i, ∑ j, R.beRicci i j x * ξ i * ξ j) : R.Curv ρ := by
  intro f hf x
  have h1 : R.toEll.diff.ΓA f f x = R.GamF f f x := by rw [R.toEll.ΓA_eq hf hf]; rfl
  have h3 : R.toEll.diff.Γ₂ f f x = _ := R.riem_bochner hf x
  rw [h1, h3, R.Gam_eq_gl_grad f x]
  have := R.hessNorm_nonneg (fun i j => R.hess f i j x) x
  have h2 := h x (fun i => R.grad f i x)
  linarith

end RiemData

end MarkovTriple.BGL.Instances.Riemannian
