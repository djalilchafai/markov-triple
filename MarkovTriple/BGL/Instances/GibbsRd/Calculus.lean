import Mathlib
import MarkovTriple.BGL.Frozen.PartialDeriv
import MarkovTriple.BGL.Analysis.OU.Basic

/-!
# Calculus on `ℝ^d = Fin d → ℝ`: partial derivatives, chain rule, symmetry of the Hessian, `C_c^∞`, integration by parts

Measure-free calculus shared by the Euclidean weighted (Gibbs) triples and the weighted Riemannian triples of
coordinates (`GibbsRd/Ell*`, `Riemannian/*`).  Partial derivatives are the frozen `BGL.pderiv`
(`∂ᵢ f(x) = Df(x)(eᵢ)`); `pderiv (pderiv f i) j = ∂ⱼ∂ᵢ f`.

* `Sm f`: `f` is `C^∞`.  `A₀ d` = `C_c^∞(ℝ^d)` (non-unital algebra), `Afull d` = `C^∞(ℝ^d)` (unital algebra).
* first-order calculus of `∂ᵢ`: `pderiv_add`, `pderiv_mul`, `pderiv_smul`, `pderiv_sum`, chain rule `pderiv_comp`;
* `pderiv_symm`: `∂ⱼ∂ᵢ f = ∂ᵢ∂ⱼ f` for `C^∞` `f` (Mathlib's `ContDiffAt.isSymmSndFDerivAt`);
* `integral_pderiv_eq_zero`: `∫ ∂ᵢ H dx = 0` for `H ∈ C_c^∞` (Mathlib's integration by parts for Fréchet derivatives).
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace MarkovTriple.BGL.Instances.GibbsRd

open MarkovTriple.BGL (pderiv pderiv₂)

variable {d : ℕ}

/-- Euclidean space `ℝ^d`, as `Fin d → ℝ` (Lebesgue measure = product measure). -/
abbrev Rd (d : ℕ) := Fin d → ℝ

/-- `C^∞`. -/
abbrev Sm (f : Rd d → ℝ) : Prop := ContDiff ℝ (⊤ : ℕ∞) f

section algebra

/-- `C_c^∞(ℝ^d)` as a non-unital subalgebra of `ℝ^d → ℝ`. -/
def A₀ (d : ℕ) : NonUnitalSubalgebra ℝ (Rd d → ℝ) where
  carrier := {f | Sm f ∧ HasCompactSupport f}
  add_mem' := fun {f g} (hf : Sm f ∧ HasCompactSupport f) (hg : Sm g ∧ HasCompactSupport g) =>
    ⟨hf.1.add hg.1, hf.2.add hg.2⟩
  zero_mem' := (⟨contDiff_const, HasCompactSupport.zero⟩ :
    Sm (0 : Rd d → ℝ) ∧ HasCompactSupport (0 : Rd d → ℝ))
  mul_mem' := fun {f g} (hf : Sm f ∧ HasCompactSupport f) (hg : Sm g ∧ HasCompactSupport g) =>
    ⟨hf.1.mul hg.1, hf.2.mul_right⟩
  smul_mem' := fun c {f} (hf : Sm f ∧ HasCompactSupport f) => ⟨hf.1.const_smul c, hf.2.smul_left⟩

/-- `C^∞(ℝ^d)` as a unital subalgebra. -/
def Afull (d : ℕ) : Subalgebra ℝ (Rd d → ℝ) where
  carrier := {f | Sm f}
  add_mem' := fun {f g} (hf : Sm f) (hg : Sm g) => hf.add hg
  zero_mem' := (contDiff_const : Sm (0 : Rd d → ℝ))
  mul_mem' := fun {f g} (hf : Sm f) (hg : Sm g) => hf.mul hg
  one_mem' := (contDiff_const : Sm (1 : Rd d → ℝ))
  algebraMap_mem' := fun r => (contDiff_const : Sm (fun _ : Rd d => r))

lemma mem_A₀ {f : Rd d → ℝ} : f ∈ A₀ d ↔ Sm f ∧ HasCompactSupport f := Iff.rfl
lemma mem_Afull {f : Rd d → ℝ} : f ∈ Afull d ↔ Sm f := Iff.rfl

end algebra

variable {f g : Rd d → ℝ}

lemma Sm.pderiv (hf : Sm f) (i : Fin d) : Sm (pderiv f i) :=
  MarkovTriple.Sanity.OU.contDiff_pderiv f hf i

lemma Sm.differentiableAt (hf : Sm f) (x : Rd d) : DifferentiableAt ℝ f x :=
  (hf.differentiable (by simp)) x

lemma Sm.hasFDerivAt' (hf : Sm f) (x : Rd d) : HasFDerivAt f (fderiv ℝ f x) x :=
  (hf.differentiableAt x).hasFDerivAt

lemma A₀.pderiv_mem (hf : f ∈ A₀ d) (i : Fin d) : pderiv f i ∈ A₀ d :=
  ⟨hf.1.pderiv i, hf.2.fderiv_apply ℝ (Pi.single i 1)⟩

lemma A₀.le (hf : f ∈ A₀ d) : f ∈ Afull d := hf.1

/-! ### First-order calculus -/

lemma pderiv_add (hf : Sm f) (hg : Sm g) (i : Fin d) (x : Rd d) :
    pderiv (f + g) i x = pderiv f i x + pderiv g i x := by
  unfold pderiv
  rw [fderiv_add (hf.differentiableAt x) (hg.differentiableAt x)]
  rfl

lemma pderiv_sub (hf : Sm f) (hg : Sm g) (i : Fin d) (x : Rd d) :
    pderiv (f - g) i x = pderiv f i x - pderiv g i x := by
  unfold pderiv
  rw [fderiv_sub (hf.differentiableAt x) (hg.differentiableAt x)]
  rfl

lemma pderiv_mul (hf : Sm f) (hg : Sm g) (i : Fin d) (x : Rd d) :
    pderiv (f * g) i x = pderiv f i x * g x + f x * pderiv g i x := by
  unfold pderiv
  rw [fderiv_mul (hf.differentiableAt x) (hg.differentiableAt x)]
  simp
  ring

lemma pderiv_smul (c : ℝ) (hf : Sm f) (i : Fin d) (x : Rd d) :
    pderiv (c • f) i x = c * pderiv f i x := by
  unfold pderiv
  rw [fderiv_const_smul (hf.differentiableAt x)]
  simp

lemma pderiv_add' (hf : Sm f) (hg : Sm g) (i : Fin d) (x : Rd d) :
    pderiv (fun y => f y + g y) i x = pderiv f i x + pderiv g i x := pderiv_add hf hg i x

lemma pderiv_mul' (hf : Sm f) (hg : Sm g) (i : Fin d) (x : Rd d) :
    pderiv (fun y => f y * g y) i x = pderiv f i x * g x + f x * pderiv g i x := pderiv_mul hf hg i x

lemma pderiv_sub' (hf : Sm f) (hg : Sm g) (i : Fin d) (x : Rd d) :
    pderiv (fun y => f y - g y) i x = pderiv f i x - pderiv g i x := pderiv_sub hf hg i x

lemma pderiv_const (c : ℝ) (i : Fin d) (x : Rd d) : pderiv (fun _ : Rd d => c) i x = 0 := by
  simp [pderiv]

lemma pderiv_sum {ι : Type*} (s : Finset ι) {F : ι → Rd d → ℝ} (hF : ∀ j, Sm (F j)) (i : Fin d)
    (x : Rd d) :
    pderiv (fun y => ∑ j ∈ s, F j y) i x = ∑ j ∈ s, pderiv (F j) i x := by
  unfold pderiv
  rw [fderiv_fun_sum (fun j _ => (hF j).differentiableAt x)]
  simp

lemma pderiv_comp {k : ℕ} (ψ : (Fin k → ℝ) → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (F : Fin k → Rd d → ℝ) (hF : ∀ j, Sm (F j)) (i : Fin d) (x : Rd d) :
    pderiv (fun y => ψ (fun j => F j y)) i x =
      ∑ l, pderiv ψ l (fun j => F j x) * pderiv (F l) i x := by
  have hFd : HasFDerivAt (fun y : Rd d => fun j => F j y)
      (ContinuousLinearMap.pi (fun j => fderiv ℝ (F j) x)) x :=
    hasFDerivAt_pi.2 (fun j => (hF j).hasFDerivAt' x)
  have hψd : HasFDerivAt ψ (fderiv ℝ ψ (fun j => F j x)) (fun j => F j x) :=
    ((hψ.differentiable (by simp)) _).hasFDerivAt
  have := hψd.comp x hFd
  unfold pderiv
  rw [show (fun y : Rd d => ψ fun j => F j y) = ψ ∘ fun y : Rd d => fun j => F j y from rfl,
    this.fderiv]
  simp only [ContinuousLinearMap.comp_apply]
  rw [MarkovTriple.Sanity.OU.clm_pi_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp [mul_comm]

/-- composition `ψ(f₁,…,f_k)` of `C^∞` functions is `C^∞`. -/
lemma sm_comp (k : ℕ) (ψ : (Fin k → ℝ) → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (F : Fin k → Rd d → ℝ) (hF : ∀ i, Sm (F i)) : Sm (fun x => ψ (fun i => F i x)) :=
  hψ.comp (contDiff_pi.2 hF)

lemma comp_mem_A₀ (k : ℕ) (ψ : (Fin k → ℝ) → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (h0 : ψ 0 = 0)
    (F : Fin k → Rd d → ℝ) (hF : ∀ i, F i ∈ A₀ d) : (fun x => ψ (fun i => F i x)) ∈ A₀ d := by
  refine ⟨sm_comp k ψ hψ F fun i => (hF i).1, ?_⟩
  refine HasCompactSupport.intro (K := ⋃ i, tsupport (F i))
    (isCompact_iUnion fun i => (hF i).2) fun x hx => ?_
  have : ∀ i, F i x = 0 := fun i =>
    image_eq_zero_of_notMem_tsupport (fun h => hx (Set.mem_iUnion.2 ⟨i, h⟩))
  have e : (fun i => F i x) = 0 := funext this
  simp only [e, h0]

/-! ### Symmetry of the Hessian -/

/-- `∂ⱼ(∂ᵢ f) x = D²f(x)(eⱼ, eᵢ)`. -/
lemma pderiv_pderiv_eq (hf : Sm f) (i j : Fin d) (x : Rd d) :
    pderiv (pderiv f i) j x = fderiv ℝ (fderiv ℝ f) x (Pi.single j 1) (Pi.single i 1) := by
  have hfd : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ f) := hf.fderiv_right (by simp)
  have hdf : Differentiable ℝ (fderiv ℝ f) := hfd.differentiable (by simp)
  have h := (hdf x).hasFDerivAt.clm_apply (hasFDerivAt_const (Pi.single i (1 : ℝ) : Rd d) x)
  unfold pderiv
  have e : (fun y => fderiv ℝ f y (Pi.single i 1 : Rd d)) =
      fun y => (fderiv ℝ f y) (Pi.single i 1 : Rd d) := rfl
  have := h.fderiv
  simp only [ContinuousLinearMap.comp_zero, zero_add] at this
  rw [show (fun y => fderiv ℝ f y (Pi.single i 1 : Rd d)) = _ from e, this]
  rfl

/-- **Symmetry of the Hessian** `∂ⱼ∂ᵢ f = ∂ᵢ∂ⱼ f` for `C^∞` functions. -/
lemma pderiv_symm (hf : Sm f) (i j : Fin d) (x : Rd d) :
    pderiv (pderiv f i) j x = pderiv (pderiv f j) i x := by
  rw [pderiv_pderiv_eq hf, pderiv_pderiv_eq hf]
  have hs : IsSymmSndFDerivAt ℝ f x :=
    (hf.contDiffAt).isSymmSndFDerivAt (by simp)
  exact hs _ _

lemma pderiv_symm_fun (hf : Sm f) (i j : Fin d) : pderiv (pderiv f i) j = pderiv (pderiv f j) i :=
  funext fun x => pderiv_symm hf i j x

/-! ### Integration by parts in `ℝ^d` -/

/-- `∫ ∂ᵢ H dx = 0` for `H ∈ C_c^∞(ℝ^d)` (Lebesgue measure). -/
lemma integral_pderiv_eq_zero (hH : Sm f) (hc : HasCompactSupport f) (i : Fin d) :
    ∫ x, pderiv f i x = 0 := by
  have hc' : HasCompactSupport (fun x => pderiv f i x) := hc.fderiv_apply ℝ (Pi.single i 1)
  have i1 : Integrable (fun x => pderiv f i x) volume :=
    ((hH.pderiv i).continuous).integrable_of_hasCompactSupport hc'
  have i2 : Integrable (fun x => (1 : ℝ) * f x) volume := by
    simpa using hH.continuous.integrable_of_hasCompactSupport hc
  have key := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := (volume : Measure (Rd d)))
    (f := fun _ => (1 : ℝ)) (g := f) (v := (Pi.single i 1 : Rd d))
    (by simp) (by simpa [pderiv] using i1) i2 (fun _ _ => differentiableAt_const _)
    (fun x _ => hH.differentiableAt x)
  simpa [pderiv] using key

end MarkovTriple.BGL.Instances.GibbsRd
