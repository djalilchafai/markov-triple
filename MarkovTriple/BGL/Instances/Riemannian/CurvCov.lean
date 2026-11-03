import Mathlib
import MarkovTriple.BGL.Instances.Riemannian.CurvLap
import MarkovTriple.BGL.Instances.Riemannian.CurvAlg

/-!
# Covariant calculus on `C^∞` functions in a Riemannian chart (BGL App. C.3)

For `R : RiemData d` and `u, v` of class `C^∞`:

* `GamF u v = Σ g^{ij} ∂_iu ∂_jv` (the carré du champ), `pderiv_GamF`:
  `∂_k Γ(u,v) = Σ g^{ij}(∇_k∇_i u ∂_jv + ∂_iu ∇_k∇_j v)` (metric compatibility, Thm C.3.2);
* the third covariant derivative `cov3 f i j a = ∇_i H_{ja}` with `H = ∇∇f`;
* `hess_GamF`: `∇_i∇_j Γ(f) = 2 g^{ab} ∇_iH_{ja} f_b + 2 g^{ab} H_{ja} H_{ib}`;
* `pderiv_L`: `∂_l(Lf) = Σ g^{ij}∇_lH_{ij} − Σ g^{ij}(∇_l∇_iW f_j + ∂_iW H_{lj})`;
* the Ricci identity `cov3_ricci`: `∇_iH_{aj} − ∇_aH_{ij} = − R_{ia}{}^p{}_j ∂_pf` (App. C.3, p. 507).
-/

open MeasureTheory Filter Topology

namespace MarkovTriple.BGL.Instances.Riemannian

open MarkovTriple.BGL.Instances.GibbsRd
open MarkovTriple.BGL (pderiv pderiv₂ DiffusionTriple)

variable {d : ℕ}

namespace RiemData
variable (R : RiemData d)

section
variable {u v f : Rd d → ℝ}

lemma sm_hess (hu : Sm u) (i j : Fin d) : Sm (fun x => R.hess u i j x) := by
  unfold hess
  exact ((hu.pderiv j).pderiv i).sub (ContDiff.sum fun k _ => (R.sm_chr k i j).mul (hu.pderiv k))

lemma hess_symm (hu : Sm u) (i j : Fin d) (x : Rd d) : R.hess u i j x = R.hess u j i x := by
  unfold hess
  rw [pderiv_symm (hu) j i x]
  exact congrArg _ (Finset.sum_congr rfl fun k _ => by rw [R.chr_symm k i j x])

/-- `∂_i H_{ja}` in terms of the third derivatives -/
lemma pderiv_hess (hu : Sm u) (i j a : Fin d) (x : Rd d) :
    pderiv (fun y => R.hess u j a y) i x = pderiv (pderiv (pderiv u a) j) i x -
      ∑ p, (pderiv (R.chr p j a) i x * pderiv u p x + R.chr p j a x * pderiv (pderiv u p) i x) := by
  unfold hess
  rw [pderiv_sub' ((hu.pderiv a).pderiv j) (ContDiff.sum fun k _ => (R.sm_chr k j a).mul (hu.pderiv k)) i x,
    pderiv_sum _ (fun k => (R.sm_chr k j a).mul (hu.pderiv k)) i x]
  congr 1
  exact Finset.sum_congr rfl fun p _ => pderiv_mul' (R.sm_chr p j a) (hu.pderiv p) i x

/-- the carré du champ `Γ(u,v) = Σ g^{ij} ∂_iu ∂_jv` -/
noncomputable def GamF (u v : Rd d → ℝ) : Rd d → ℝ :=
  fun x => ∑ i, ∑ j, R.g i j x * pderiv u i x * pderiv v j x

lemma toEll_Γ_eq (u v : Rd d → ℝ) : R.toEll.Γ u v = R.GamF u v := rfl

lemma sm_GamF (hu : Sm u) (hv : Sm v) : Sm (R.GamF u v) :=
  ContDiff.sum fun i _ => ContDiff.sum fun j _ => ((R.g_smooth i j).mul (hu.pderiv i)).mul (hv.pderiv j)

/-- **Metric compatibility**: `∂_k Γ(u,v) = Σ g^{ij}(∇_k∇_iu ∂_jv + ∂_iu ∇_k∇_jv)` -/
lemma pderiv_GamF (hu : Sm u) (hv : Sm v) (k : Fin d) (x : Rd d) :
    pderiv (R.GamF u v) k x = ∑ i, ∑ j, R.g i j x *
      (R.hess u k i x * pderiv v j x + pderiv u i x * R.hess v k j x) := by
  have h1 : pderiv (R.GamF u v) k x = ∑ i, ∑ j, (((-∑ m, (R.chr i k m x * R.g m j x +
      R.chr j k m x * R.g i m x)) * pderiv u i x * pderiv v j x) +
      R.g i j x * (pderiv (pderiv u i) k x * pderiv v j x + pderiv u i x * pderiv (pderiv v j) k x)) := by
    unfold GamF
    rw [pderiv_sum _ (fun i => ContDiff.sum fun j _ =>
      ((R.g_smooth i j).mul (hu.pderiv i)).mul (hv.pderiv j)) k x]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [pderiv_sum _ (fun j => ((R.g_smooth i j).mul (hu.pderiv i)).mul (hv.pderiv j)) k x]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [pderiv_mul' ((R.g_smooth i j).mul (hu.pderiv i)) (hv.pderiv j) k x,
      pderiv_mul' (R.g_smooth i j) (hu.pderiv i) k x, R.pderiv_g_chr k i j x]
    ring
  rw [h1]
  have := alg_G1 (fun i j => R.g i j x) (fun m k' i => R.chr m k' i x) (fun i => pderiv u i x)
    (fun j => pderiv v j x) (fun i => pderiv (pderiv u i) k x) (fun j => pderiv (pderiv v j) k x) k
  simp only [Finset.sum_add_distrib]
  simp only [Finset.sum_add_distrib] at this
  rw [this]
  unfold hess
  rfl

lemma pderiv_GamF_self (hf : Sm f) (k : Fin d) (x : Rd d) :
    pderiv (R.GamF f f) k x = 2 * ∑ i, ∑ j, R.g i j x * R.hess f k i x * pderiv f j x := by
  rw [R.pderiv_GamF hf hf k x]
  have h2 : ∑ i, ∑ j, R.g i j x * (pderiv f i x * R.hess f k j x) =
      ∑ i, ∑ j, R.g i j x * R.hess f k i x * pderiv f j x := by
    sums2s [fun i j => R.g_symm i j x]
  simp only [mul_add, Finset.sum_add_distrib, ← mul_assoc] at h2 ⊢
  rw [two_mul]
  simp only [mul_assoc] at h2 ⊢
  rw [h2]

/-- the third covariant derivative `∇_i H_{ja}` of the Hessian `H = ∇∇f` -/
noncomputable def cov3 (f : Rd d → ℝ) (i j a : Fin d) (x : Rd d) : ℝ :=
  pderiv (fun y => R.hess f j a y) i x - ∑ m, R.chr m i j x * R.hess f m a x -
    ∑ m, R.chr m i a x * R.hess f j m x

/-- `∇_i∇_j Γ(f) = 2 g^{ab} ∇_iH_{ja} f_b + 2 g^{ab} H_{ja} H_{ib}` -/
lemma hess_GamF (hf : Sm f) (i j : Fin d) (x : Rd d) :
    R.hess (R.GamF f f) i j x = 2 * ∑ a, ∑ b, R.g a b x * R.cov3 f i j a x * pderiv f b x +
      2 * ∑ a, ∑ b, R.g a b x * R.hess f j a x * R.hess f i b x := by
  have hfun : pderiv (R.GamF f f) j = fun y => 2 * ∑ a, ∑ b, R.g a b y * R.hess f j a y *
      pderiv f b y := funext fun y => R.pderiv_GamF_self hf j y
  have hsm : ∀ a, Sm (fun y => ∑ b, R.g a b y * R.hess f j a y * pderiv f b y) := fun a =>
    ContDiff.sum fun b _ => ((R.g_smooth a b).mul (R.sm_hess hf j a)).mul (hf.pderiv b)
  have hd : pderiv (pderiv (R.GamF f f) j) i x = 2 * ∑ a, ∑ b, ((pderiv (R.g a b) i x *
      R.hess f j a x + R.g a b x * pderiv (fun y => R.hess f j a y) i x) * pderiv f b x +
      R.g a b x * R.hess f j a x * pderiv (pderiv f b) i x) := by
    rw [hfun, pderiv_mul' contDiff_const (ContDiff.sum fun a _ => hsm a) i x, pderiv_const, zero_mul,
      zero_add, pderiv_sum _ hsm i x]
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [pderiv_sum _ (fun b => ((R.g_smooth a b).mul (R.sm_hess hf j a)).mul (hf.pderiv b)) i x]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [pderiv_mul' ((R.g_smooth a b).mul (R.sm_hess hf j a)) (hf.pderiv b) i x,
      pderiv_mul' (R.g_smooth a b) (R.sm_hess hf j a) i x]
  have := alg_C2 (fun a b => R.g a b x) (fun m k' i' => R.chr m k' i' x)
    (fun a b => pderiv (R.g a b) i x) (fun a b => R.hess f a b x)
    (fun a => pderiv (fun y => R.hess f j a y) i x) (fun b => pderiv (pderiv f b) i x)
    (fun b => pderiv f b x) i j (fun a b => R.pderiv_g_chr i a b x) (fun b => rfl)
  beta_reduce at this
  have hH : R.hess (R.GamF f f) i j x = pderiv (pderiv (R.GamF f f) j) i x -
      ∑ m, R.chr m i j x * pderiv (R.GamF f f) m x := rfl
  rw [hH, hd]
  simp only [R.pderiv_GamF_self hf]
  unfold cov3
  exact this

lemma cov3_symm (hf : Sm f) (i j a : Fin d) (x : Rd d) : R.cov3 f i j a x = R.cov3 f i a j x := by
  unfold cov3
  have h : (fun y => R.hess f j a y) = fun y => R.hess f a j y :=
    funext fun y => R.hess_symm hf j a y
  rw [h]
  have e1 : ∑ m, R.chr m i j x * R.hess f m a x = ∑ m, R.chr m i j x * R.hess f a m x :=
    Finset.sum_congr rfl fun m _ => by rw [R.hess_symm hf m a x]
  have e2 : ∑ m, R.chr m i a x * R.hess f j m x = ∑ m, R.chr m i a x * R.hess f m j x :=
    Finset.sum_congr rfl fun m _ => by rw [R.hess_symm hf j m x]
  rw [e1, e2]
  ring

/-- `∂_l (L f) = Σ g^{ij} ∇_lH_{ij} − Σ g^{ij}(∇_l∇_iW f_j + ∂_iW H_{lj})` -/
lemma pderiv_L (hf : Sm f) (l : Fin d) (x : Rd d) :
    pderiv (R.toEll.L f) l x = ∑ i, ∑ j, R.g i j x * R.cov3 f l i j x -
      ∑ i, ∑ j, R.g i j x * (R.hess R.W l i x * pderiv f j x + pderiv R.W i x * R.hess f l j x) := by
  have hfun : R.toEll.L f = fun y => ∑ i, ∑ j, R.g i j y * R.hess f i j y -
      R.GamF R.W f y := funext fun y => R.L_eq_hess hf y
  have hsm1 : ∀ i, Sm (fun y => ∑ j, R.g i j y * R.hess f i j y) := fun i =>
    ContDiff.sum fun j _ => (R.g_smooth i j).mul (R.sm_hess hf i j)
  have hsm2 : Sm (fun y => ∑ i, ∑ j, R.g i j y * R.hess f i j y) :=
    ContDiff.sum fun i _ => hsm1 i
  rw [hfun, pderiv_sub' hsm2 (R.sm_GamF R.W_smooth hf) l x, pderiv_sum _ hsm1 l x,
    R.pderiv_GamF R.W_smooth hf l x]
  congr 1
  have h1 : ∀ i, pderiv (fun y => ∑ j, R.g i j y * R.hess f i j y) l x =
      ∑ j, (pderiv (R.g i j) l x * R.hess f i j x +
        R.g i j x * pderiv (fun y => R.hess f i j y) l x) := by
    intro i
    rw [pderiv_sum _ (fun j => (R.g_smooth i j).mul (R.sm_hess hf i j)) l x]
    exact Finset.sum_congr rfl fun j _ => pderiv_mul' (R.g_smooth i j) (R.sm_hess hf i j) l x
  simp only [h1]
  have := alg_G3 (fun i j => R.g i j x) (fun m k' i => R.chr m k' i x) (fun i j => pderiv (R.g i j) l x)
    (fun i j => R.hess f i j x) (fun i j => pderiv (fun y => R.hess f i j y) l x) l
    (fun i j => R.pderiv_g_chr l i j x)
  beta_reduce at this
  rw [this]
  rfl

/-- **Ricci identity** (App. C.3): `∇_iH_{aj} − ∇_aH_{ij} = − Σ_p R_{ia}{}^p{}_j ∂_pf` -/
lemma cov3_ricci (hf : Sm f) (i a j : Fin d) (x : Rd d) :
    R.cov3 f i a j x - R.cov3 f a i j x = -∑ p, R.riem i a p j x * pderiv f p x := by
  have := alg_D (fun m i' a' => R.chr m i' a' x) (fun i' p a' j' => pderiv (R.chr p a' j') i' x)
    (fun i' j' => pderiv (pderiv f j') i' x) (fun i' j' => R.hess f i' j' x) (fun p => pderiv f p x)
    (fun i' a' j' => pderiv (pderiv (pderiv f j') a') i' x)
    (fun i' j' a' => pderiv (fun y => R.hess f j' a' y) i' x)
    (fun m i' a' => R.chr_symm m i' a' x)
    (fun i' a' j' => pderiv_symm (hf.pderiv j') a' i' x)
    (fun i' j' => rfl)
    (fun i' j' a' => R.pderiv_hess hf i' j' a' x) i a j
  beta_reduce at this
  unfold cov3 riem
  rw [this]

end

end RiemData

end MarkovTriple.BGL.Instances.Riemannian
