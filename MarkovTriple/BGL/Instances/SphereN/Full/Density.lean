import Mathlib
import MarkovTriple.BGL.Instances.SphereN.Triple
import MarkovTriple.BGL.Frozen.Classes
import MarkovTriple.BGL.Basic
import MarkovTriple.BGL.Instances.SphereN.Full.Harm

/-!
# Density of harmonic polynomials in `L²(σ)` (Round 29, stream N, group N2)

Stone-Weierstrass (polynomials in the coordinates separate the points of `S^{n-1}`) gives density in `C(S^{n-1})`,
hence in `L²(σ)`; the Fischer decomposition (`Fischer.lean`) reduces polynomials to harmonic ones, which are
eigenfunctions of `L` (`LS_restr_harm`).
-/

open MvPolynomial MeasureTheory

namespace MarkovTriple.BGL.SphereN

variable {n : ℕ}

/-- A linear map defined on polynomials sends `Σ |x|^{2j} h` into any subspace containing the images of
the harmonic pieces. -/
lemma map_mem_of_harm {M : Type*} [AddCommGroup M] [Module ℝ M] (hn : 0 < n) (Φ : Pn n →ₗ[ℝ] M)
    (T : Submodule ℝ M) (hΦ : ∀ (j k : ℕ) (h : Pn n), IsHarm k h → Φ (rsq ^ j * h) ∈ T) (p : Pn n) :
    Φ p ∈ T := by
  have hW : ∀ d, Wsp n d ≤ T.comap Φ := by
    intro d
    rw [Wsp, Submodule.span_le]
    rintro _ ⟨j, k, h, hh, _, rfl⟩
    exact hΦ j k h hh
  have hp := MvPolynomial.sum_homogeneousComponent p
  have : Φ p = ∑ i ∈ Finset.range (p.totalDegree + 1), Φ (homogeneousComponent i p) := by
    rw [← map_sum, hp]
  rw [this]
  exact Submodule.sum_mem _ fun i _ => hW i (fischer hn i (homogeneousComponent_isHomogeneous i p))

lemma restr_pow_rsq_mul (j : ℕ) (q : Pn n) : restr ((rsq : Pn n) ^ j * q) = restr q := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', mul_assoc, restr_rsq_mul, ih]

noncomputable def restrL : Pn n →ₗ[ℝ] (Sph n → ℝ) where
  toFun := restr
  map_add' p q := by funext x; simp [restr]
  map_smul' c p := by funext x; simp [restr]

/-- **Every polynomial restricted to the sphere is a finite combination of restrictions of harmonic
homogeneous polynomials.** -/
theorem restr_mem_span_harm (hn : 0 < n) (p : Pn n) :
    restr p ∈ Submodule.span ℝ {f : Sph n → ℝ | ∃ (k : ℕ) (h : Pn n), IsHarm k h ∧ f = restr h} := by
  refine map_mem_of_harm hn restrL _ (fun j k h hh => ?_) p
  show restr (rsq ^ j * h) ∈ _
  rw [restr_pow_rsq_mul]
  exact Submodule.subset_span ⟨k, h, hh, rfl⟩

lemma continuous_coord (i : Fin n) : Continuous fun x : Sph n => cv (x : Ee n) i :=
  (continuous_apply i).comp continuous_cv

/-- the polynomial restriction as an algebra homomorphism into `C(S^{n-1})`. -/
noncomputable def restrA : Pn n →ₐ[ℝ] C(Sph n, ℝ) :=
  MvPolynomial.aeval fun i => ⟨fun x => cv (x : Ee n) i, continuous_coord i⟩

lemma restrA_apply (p : Pn n) (x : Sph n) : restrA p x = restr p x := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [restrA, restr]
  | add p q hp hq => simp only [map_add, ContinuousMap.add_apply, hp, hq, restr]
  | mul_X p i hp =>
    simp only [map_mul, ContinuousMap.mul_apply, hp]
    simp [restrA, restr]

lemma restrA_sep : (restrA (n := n)).range.SeparatesPoints := by
  intro x y hxy
  have hxy' : cv (x : Ee n) ≠ cv (y : Ee n) := by
    intro h
    apply hxy
    apply Subtype.ext
    ext i
    exact congrFun h i
  obtain ⟨i, hi⟩ : ∃ i, cv (x : Ee n) i ≠ cv (y : Ee n) i := by
    by_contra hcon
    apply hxy'
    funext j
    by_contra hj
    exact hcon ⟨j, hj⟩
  refine ⟨_, ⟨restrA (X i), ⟨X i, rfl⟩, rfl⟩, ?_⟩
  show restrA (X i) x ≠ restrA (X i) y
  rw [restrA_apply, restrA_apply]
  simpa [restr] using hi

lemma restrA_top : (restrA (n := n)).range.topologicalClosure = ⊤ :=
  ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints _ restrA_sep

/-- the set of harmonic eigenfunctions in `𝒜₀`. -/
def harmSet (n : ℕ) (hn : 2 ≤ n) : Set (sphereDiffusion n hn).A₀ :=
  {f | ∃ (k : ℕ) (h : Pn n), IsHarm k h ∧ f.1 = restr h}

lemma restr_mem_A₀ (hn : 2 ≤ n) (p : Pn n) : restr p ∈ (sphereDiffusion n hn).A₀ := restr_mem p

lemma cls_restr (hn : 2 ≤ n) (p : Pn n) :
    (sphereDiffusion n hn).cls ⟨restr p, restr_mem p⟩ =
      ContinuousMap.toLp (E := ℝ) 2 (σ n) ℝ (restrA p) := by
  refine Lp.ext ?_
  filter_upwards [DiffusionTriple.coeFn_cls (sphereDiffusion n hn) ⟨restr p, restr_mem p⟩,
    ContinuousMap.coeFn_toLp (E := ℝ) (p := 2) (μ := σ n) (𝕜 := ℝ) (restrA p)] with x h1 h2
  rw [h1, h2]
  exact (restrA_apply p x).symm

/-- **Density of the harmonic eigenfunctions in `L²(σ)`.** -/
theorem dense_span_harm (hn : 2 ≤ n) :
    (Submodule.span ℝ ((sphereDiffusion n hn).cls '' harmSet n hn)).topologicalClosure = ⊤ := by
  set T := Submodule.span ℝ ((sphereDiffusion n hn).cls '' harmSet n hn) with hT
  let Φ : Pn n →ₗ[ℝ] Lp ℝ 2 (σ n) :=
    (ContinuousMap.toLp (E := ℝ) 2 (σ n) ℝ).toLinearMap.comp restrA.toLinearMap
  have hΦ : ∀ p, Φ p ∈ T := by
    intro p
    refine map_mem_of_harm (by omega) Φ T (fun j k h hh => ?_) p
    have e : restrA ((rsq : Pn n) ^ j * h) = restrA h := by
      ext x
      rw [restrA_apply, restrA_apply, restr_pow_rsq_mul]
    show ContinuousMap.toLp (E := ℝ) 2 (σ n) ℝ (restrA ((rsq : Pn n) ^ j * h)) ∈ T
    rw [e, ← cls_restr hn h]
    exact Submodule.subset_span ⟨⟨restr h, restr_mem h⟩, ⟨k, h, hh, rfl⟩, rfl⟩
  have h1 : DenseRange (ContinuousMap.toLp (E := ℝ) 2 (σ n) ℝ : C(Sph n, ℝ) →L[ℝ] Lp ℝ 2 (σ n)) :=
    ContinuousMap.toLp_denseRange ℝ (σ n) ℝ (by norm_num)
  have h2 : Dense ((restrA (n := n)).range : Set C(Sph n, ℝ)) := by
    rw [dense_iff_closure_eq, ← Subalgebra.topologicalClosure_coe, restrA_top]; rfl
  have h3 := h1.dense_image (ContinuousMap.toLp (E := ℝ) 2 (σ n) ℝ).continuous h2
  have h4 : Dense (T : Set (Lp ℝ 2 (σ n))) := by
    refine h3.mono ?_
    rintro _ ⟨F, ⟨p, rfl⟩, rfl⟩
    exact hΦ p
  exact Submodule.dense_iff_topologicalClosure_eq_top.1 h4

end MarkovTriple.BGL.SphereN
