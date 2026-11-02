import Mathlib
import MarkovTriple.BGL.Frozen.StandardTriple
import MarkovTriple.BGL.SemigroupLemmas

/-!
# No nontrivial finite-state Markov triple: the diffusion property kills discrete generators

BGL's Markov triples are *diffusion* triples: the change-of-variables formula (D3, (3.1.2)) makes
`Γ(·, g)` a first-order derivation.  On a finite state space every test function takes finitely many
values, and then the diffusion property forces `Γ = 0`:

* `finite_Γ_ae_zero`: if `E` is finite, every `DiffusionTriple E` has `Γ f g = 0` a.e. on `𝒜₀`.
  (Take `ψ` a polynomial vanishing on the finite value set of `f` and on `0`, with simple roots; then
  `ψ ∘ f = 0`, so `0 = Γ(ψ ∘ f, g) = ψ'(f) Γ(f, g)` with `ψ'(f) ≠ 0`.)
* `finite_L_ae_zero`: hence `L f = 0` a.e. (integration by parts with `g = L f`).
* `finite_standard_const`: for a `StandardTriple` on a finite space (S10), every test function is a.e.
  constant: the only finite-state Standard Markov Triples are the trivial one-atom ones
  (`Sanity/Trivial.lean`).

So a two-point chain or any finite reversible Markov chain with nonzero generator is NOT a BGL
`DiffusionTriple` (they satisfy the Γ-calculus only with the discrete, non-diffusion `Γ`); no such
instance can be built without changing the frozen `diffusion` field.
-/

open MeasureTheory Polynomial
open scoped NNReal

namespace MarkovTriple.BGL.Instances.Discrete

variable {E : Type*} [MeasurableSpace E]

/-- the one-variable polynomial `ψ(v) = p(v 0)` is smooth with `∂₀ψ(v) = p'(v 0)`. -/
lemma pderiv_poly (p : ℝ[X]) (v : Fin 1 → ℝ) :
    pderiv (fun w : Fin 1 → ℝ => p.eval (w 0)) 0 v = p.derivative.eval (v 0) := by
  unfold pderiv
  have h1 : HasFDerivAt (fun w : Fin 1 → ℝ => w 0) (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0) v :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).hasFDerivAt
  have h2 := (p.hasDerivAt (v 0)).comp_hasFDerivAt v h1
  have e : (fun w : Fin 1 → ℝ => p.eval (w 0)) = (fun x => p.eval x) ∘ fun w => w 0 := rfl
  rw [e, h2.fderiv]
  simp

lemma contDiff_poly (p : ℝ[X]) : ContDiff ℝ (⊤ : ℕ∞) (fun w : Fin 1 → ℝ => p.eval (w 0)) :=
  have h : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => p.eval x) := by
    simpa using Polynomial.contDiff_aeval (𝕜 := ℝ) p (⊤ : ℕ∞)
  h.comp (contDiff_apply ℝ ℝ 0)

/-- **On a finite state space `Γ = 0`** (a.e., on test functions). -/
theorem finite_Γ_ae_zero [Finite E] (T : DiffusionTriple E) {f : E → ℝ} (hf : f ∈ T.A₀)
    {g : E → ℝ} (hg : g ∈ T.A₀) : T.Γ f g =ᵐ[T.μ] 0 := by
  classical
  have := Fintype.ofFinite E
  set P : Finset ℝ := insert 0 (Finset.univ.image f) with hP
  set p : ℝ[X] := ∏ b ∈ P, (X - C b) with hp
  have hroot : ∀ x, p.eval (f x) = 0 := fun x => by
    rw [hp, eval_prod]
    exact Finset.prod_eq_zero (i := f x) (by simp [hP]) (by simp)
  have hp0 : p.eval 0 = 0 := by
    rw [hp, eval_prod]
    exact Finset.prod_eq_zero (i := 0) (by simp [hP]) (by simp)
  have hsimple : ∀ x, p.derivative.eval (f x) ≠ 0 := fun x => by
    have := Lagrange.eval_nodal_derivative_eval_node_eq (s := P) (v := (id : ℝ → ℝ)) (i := f x)
      (by simp [hP])
    have e : Lagrange.nodal P (id : ℝ → ℝ) = p := by
      simp [Lagrange.nodal, hp]
    rw [e] at this
    simp only [id] at this
    rw [this]
    simp only [Lagrange.nodal, eval_prod, eval_sub, eval_X, eval_C, id]
    refine Finset.prod_ne_zero_iff.2 (fun j hj => ?_ : ∀ j ∈ P.erase (f x), (f x - j : ℝ) ≠ 0)
    exact sub_ne_zero.2 fun h => (Finset.mem_erase.1 hj).1 h.symm
  have key := T.diffusion 1 (fun w : Fin 1 → ℝ => p.eval (w 0)) (contDiff_poly p)
    (by simpa using hp0) (fun _ => f) (fun _ => hf) g hg
  have hz : (fun x => p.eval (f x)) = (0 : ℝ) • f := by
    funext x; simpa using hroot x
  have h0 : T.Γ (fun x => (fun w : Fin 1 → ℝ => p.eval (w 0)) (fun _ => f x)) g =ᵐ[T.μ] 0 := by
    have e : (fun x => (fun w : Fin 1 → ℝ => p.eval (w 0)) (fun _ => f x)) = (0 : ℝ) • f := hz
    rw [e]
    filter_upwards [T.Γ_smul 0 f hf g hg] with x hx
    simpa using hx
  filter_upwards [key, h0] with x h1 h2
  rw [h2] at h1
  simp only [Fin.sum_univ_one, pderiv_poly] at h1
  have := h1.symm
  rcases mul_eq_zero.1 this with h | h
  · exact absurd h (hsimple x)
  · simpa using h

/-- **On a finite state space `L = 0`** (a.e., on test functions). -/
theorem finite_L_ae_zero [Finite E] (T : DiffusionTriple E) {f : E → ℝ} (hf : f ∈ T.A₀) :
    T.L f =ᵐ[T.μ] 0 := by
  have hLf := T.L_mem f hf
  have h := T.ibp f hf (T.L f) hLf
  have hG : ∫ x, T.Γ f (T.L f) x ∂T.μ = 0 := by
    rw [integral_congr_ae (finite_Γ_ae_zero T hf hLf)]; simp
  rw [hG, neg_zero] at h
  have hint : Integrable (fun x => T.L f x * T.L f x) T.μ := by
    simpa [sq] using (T.memLp _ hLf 2 (by norm_num) (by simp)).integrable_sq
  have h0 := (integral_eq_zero_iff_of_nonneg (fun x => mul_self_nonneg (T.L f x)) hint).1 h
  filter_upwards [h0] with x hx
  simpa using hx

/-- **Finite-state Standard Markov Triples are trivial**: by S10 every test function is a.e. constant. -/
theorem finite_standard_const [Finite E] (T : StandardTriple E) {f : E → ℝ} (hf : f ∈ T.A₀) :
    ∃ c : ℝ, f =ᵐ[T.μ] fun _ => c := by
  have hd := T.toDiffusionTriple.cls_mem_generator_domain ⟨f, hf⟩
  have hG := T.toDiffusionTriple.generator_cls ⟨f, hf⟩ hd
  have hL : T.toDiffusionTriple.Lcls ⟨f, hf⟩ = 0 := by
    refine Lp.ext ?_
    filter_upwards [DiffusionTriple.coeFn_Lcls T.toDiffusionTriple ⟨f, hf⟩, Lp.coeFn_zero ℝ 2 T.μ,
      finite_L_ae_zero T.toDiffusionTriple hf] with x h1 h2 h3
    rw [h1, h2]; exact h3
  obtain ⟨c, hc⟩ := T.ergodic _ hd (by rw [hG, hL])
  refine ⟨c, ?_⟩
  filter_upwards [hc, DiffusionTriple.coeFn_cls T.toDiffusionTriple ⟨f, hf⟩] with x h1 h2
  rw [← h2]; exact h1

end MarkovTriple.BGL.Instances.Discrete
