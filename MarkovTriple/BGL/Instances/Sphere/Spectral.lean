import Mathlib
import MarkovTriple.BGL.Instances.Sphere.Ops

/-!
# Integration by parts and the eigenbasis `U_k` of the zonal sphere `S³`

* `ibpZ`: `∫ g · L f dμ = -∫ Γ(f,g) dμ` for `f, g ∈ 𝒜`;
* `UZ k = U_k(cos θ)` (second-kind Chebyshev polynomials `U_k(x)`), `L U_k = -k(k+2) U_k` exactly
  (also at the endpoints);
* `(U_k)` is an orthonormal basis of `L²(μ)` (`hilbertBasisZ`).
-/

open MeasureTheory Real Set Filter Topology
open scoped ENNReal NNReal InnerProductSpace
open MarkovTriple.Sanity.OU (Sm deriv_comp1 contDiff_pderiv)

namespace MarkovTriple.BGL.Instances.Sphere

/-! ### integration by parts -/

lemma integral_ibp_theta {F G : ℝ → ℝ} (hF : Sm F) (hG : Sm G) (eF : EP F) :
    ∫ θ in (0 : ℝ)..π, 2 / π * sin θ ^ 2 * (G θ * dL F θ) =
      -∫ θ in (0 : ℝ)..π, 2 / π * sin θ ^ 2 * dG F G θ := by
  have hv : ∀ θ, HasDerivAt (fun θ => sin θ ^ 2 * deriv F θ)
      (2 * sin θ * cos θ * deriv F θ + sin θ ^ 2 * deriv (deriv F) θ) θ := by
    intro θ
    have h1 : HasDerivAt (fun θ => sin θ ^ 2) (2 * sin θ * cos θ) θ := by
      have := (hasDerivAt_sin θ).fun_pow 2
      simpa using this
    exact h1.mul (hF.deriv'.hasDerivAt θ) |>.congr_deriv (by ring)
  have hpart := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := 0) (b := π)
    (u := G) (u' := deriv G) (v := fun θ => sin θ ^ 2 * deriv F θ)
    (v' := fun θ => 2 * sin θ * cos θ * deriv F θ + sin θ ^ 2 * deriv (deriv F) θ)
    (fun θ _ => hG.hasDerivAt θ) (fun θ _ => hv θ)
    (hG.deriv'.continuous.intervalIntegrable _ _)
    (by
      refine Continuous.intervalIntegrable ?_ _ _
      have := hF.deriv'.continuous
      have := hF.deriv'.deriv'.continuous
      fun_prop)
  have hident : ∀ θ, sin θ ^ 2 * dL F θ =
      2 * sin θ * cos θ * deriv F θ + sin θ ^ 2 * deriv (deriv F) θ := by
    intro θ
    unfold dL
    have := sin_mul_Dq (hF0 hF eF) θ
    calc sin θ ^ 2 * (deriv (deriv F) θ + 2 * (cos θ * Dq F θ))
        = sin θ ^ 2 * deriv (deriv F) θ + 2 * sin θ * cos θ * (sin θ * Dq F θ) := by ring
      _ = _ := by rw [this]; ring
  have e1 : ∫ θ in (0 : ℝ)..π, 2 / π * sin θ ^ 2 * (G θ * dL F θ) =
      2 / π * ∫ θ in (0 : ℝ)..π, G θ * (2 * sin θ * cos θ * deriv F θ + sin θ ^ 2 * deriv (deriv F) θ) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    show 2 / π * sin θ ^ 2 * (G θ * dL F θ) = 2 / π * (G θ * _)
    rw [← hident θ]; ring
  have e2 : ∫ θ in (0 : ℝ)..π, 2 / π * sin θ ^ 2 * dG F G θ =
      2 / π * ∫ θ in (0 : ℝ)..π, deriv G θ * (sin θ ^ 2 * deriv F θ) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    simp only [dG]; ring
  rw [e1, e2, hpart]
  simp

lemma ae_eq_on_Icc_of_cos {φ ψ : ℝ → ℝ} (h : ∀ θ ∈ Icc 0 π, φ θ = ψ θ) :
    ∫ θ in (0 : ℝ)..π, φ θ = ∫ θ in (0 : ℝ)..π, ψ θ := by
  refine intervalIntegral.integral_congr fun θ hθ => ?_
  rw [uIcc_of_le pi_pos.le] at hθ
  exact h θ hθ

lemma mk_cosZ {H : ℝ → ℝ} {θ : ℝ} (h : θ ∈ Icc 0 π) : mk H (cosZ θ) = H θ := by
  simp [mk, arc_cosZ h]

lemma ibpZ {f g : Zon → ℝ} (hf : f ∈ AZ) (hg : g ∈ AZ) :
    ∫ x, g x * LZ f x ∂μZ = -∫ x, GZ f g x ∂μZ := by
  have c1 : Continuous fun x => g x * LZ f x :=
    (continuous_of_mem hg).mul (continuous_of_mem (LZ_mem hf))
  have c2 : Continuous (GZ f g) := continuous_of_mem (GZ_mem hf hg)
  rw [integral_μZ c1, integral_μZ c2]
  have hF : Sm (ext f) := hf
  have hG : Sm (ext g) := hg
  have h2 : ∀ θ ∈ Icc 0 π, LZ f (cosZ θ) = dL (ext f) θ := fun θ hθ => by
    show mk (dL (ext f)) (cosZ θ) = _
    exact mk_cosZ hθ
  have h3 : ∀ θ ∈ Icc 0 π, GZ f g (cosZ θ) = dG (ext f) (ext g) θ := fun θ hθ => by
    show mk (dG (ext f) (ext g)) (cosZ θ) = _
    exact mk_cosZ hθ
  calc ∫ θ in (0 : ℝ)..π, 2 / π * sin θ ^ 2 * (g (cosZ θ) * LZ f (cosZ θ))
      = ∫ θ in (0 : ℝ)..π, 2 / π * sin θ ^ 2 * (ext g θ * dL (ext f) θ) := by
        refine ae_eq_on_Icc_of_cos fun θ hθ => ?_
        rw [h2 θ hθ]; rfl
    _ = -∫ θ in (0 : ℝ)..π, 2 / π * sin θ ^ 2 * dG (ext f) (ext g) θ :=
        integral_ibp_theta hF hG (ep_ext f)
    _ = _ := by
        congr 1
        refine ae_eq_on_Icc_of_cos fun θ hθ => ?_
        rw [h3 θ hθ]

/-! ### eigenfunctions -/

/-- the `k`-th zonal eigenfunction `U_k(x)`, `x = cos θ`. -/
noncomputable def UZ (k : ℕ) : Zon → ℝ := mk (Utheta k)

lemma ep_Utheta (k : ℕ) : EP (Utheta k) := ⟨fun θ => Utheta_neg k θ, fun θ => Utheta_add_two_pi k θ⟩

lemma ext_UZ (k : ℕ) : ext (UZ k) = Utheta k := ext_mk (fun θ => Utheta_neg k θ) (fun θ => Utheta_add_two_pi k θ)

lemma UZ_mem (k : ℕ) : UZ k ∈ AZ := mk_mem (contDiff_Utheta k) (fun θ => Utheta_neg k θ) (fun θ => Utheta_add_two_pi k θ)

lemma UZ_cosZ (k : ℕ) {θ : ℝ} (h : θ ∈ Icc 0 π) : UZ k (cosZ θ) = Utheta k θ := mk_cosZ h

lemma dL_Utheta (k : ℕ) (θ : ℝ) : dL (Utheta k) θ = -((k : ℝ) * (k + 2)) * Utheta k θ := by
  have e : dL (Utheta k) = fun θ => -((k : ℝ) * (k + 2)) * Utheta k θ := by
    refine eq_of_sin_mul_eq (sm_dL (contDiff_Utheta k) (ep_Utheta k)).continuous
      (continuous_const.mul (continuous_Utheta k)) fun θ => ?_
    by_cases hs : sin θ = 0
    · simp [hs]
    · congr 1
      have := Utheta_eigen_aux k θ hs
      unfold dL Dq
      rw [if_neg hs]
      exact this
  exact congrFun e θ

lemma LZ_UZ (k : ℕ) (x : Zon) : LZ (UZ k) x = -((k : ℝ) * (k + 2)) * UZ k x := by
  rw [LZ_apply, ext_UZ, dL_Utheta]
  rfl

/-! ### orthonormal basis -/

/-- the class of `U_k` in `L²(μ)`. -/
noncomputable def eZ (k : ℕ) : Lp ℝ 2 μZ := (memLp_of_mem (UZ_mem k) 2).toLp (UZ k)

lemma inner_eZ (j k : ℕ) : inner ℝ (eZ j) (eZ k) = if j = k then (1 : ℝ) else 0 := by
  rw [MeasureTheory.L2.inner_def]
  have : ∀ᵐ x ∂μZ, inner ℝ ((eZ j : Lp ℝ 2 μZ) x) ((eZ k : Lp ℝ 2 μZ) x) = UZ j x * UZ k x := by
    filter_upwards [(memLp_of_mem (UZ_mem j) 2).coeFn_toLp, (memLp_of_mem (UZ_mem k) 2).coeFn_toLp]
      with x h1 h2
    simp only [eZ]
    rw [h1, h2]; simp [mul_comm]
  rw [integral_congr_ae this]
  rw [integral_μZ (φ := fun x => UZ j x * UZ k x)
    ((continuous_of_mem (UZ_mem j)).mul (continuous_of_mem (UZ_mem k)))]
  rw [← integral_Utheta_mul j k]
  refine ae_eq_on_Icc_of_cos fun θ hθ => ?_
  simp only [UZ_cosZ _ hθ]

lemma orthonormal_eZ : Orthonormal ℝ eZ := by
  rw [orthonormal_iff_ite]
  intro j k
  rw [inner_eZ]

lemma x_eq_cos (x : Zon) : x.1 = cos (arc x) := by simp [arc, Real.cos_arccos x.2.1 x.2.2]

lemma rec_succ (k : ℕ) (x : Zon) : 2 * x.1 * UZ (k + 1) x = UZ (k + 2) x + UZ k x := by
  have := recurrence_succ k (arc x)
  simp only [UZ, mk]
  rw [x_eq_cos x]; exact this

lemma rec_zero (x : Zon) : 2 * x.1 * UZ 0 x = UZ 1 x := by
  have := recurrence_zero (arc x)
  simp only [UZ, mk]
  rw [x_eq_cos x]; exact this

/-- every power of `x` is a combination of the `U_k`. -/
lemma xU_mem (k : ℕ) : (fun x : Zon => x.1 * UZ k x) ∈ Submodule.span ℝ (Set.range UZ) := by
  rcases k with _ | k
  · have : (fun x : Zon => x.1 * UZ 0 x) = (1 / 2 : ℝ) • UZ 1 := by
      funext x
      have := rec_zero x
      simp only [Pi.smul_apply, smul_eq_mul]
      linarith
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩)
  · have : (fun x : Zon => x.1 * UZ (k + 1) x) = (1 / 2 : ℝ) • (UZ (k + 2) + UZ k) := by
      funext x
      have := rec_succ k x
      simp only [Pi.smul_apply, smul_eq_mul, Pi.add_apply]
      linarith
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.add_mem _ (Submodule.subset_span ⟨k + 2, rfl⟩)
      (Submodule.subset_span ⟨k, rfl⟩))

/-- the span of `U_k` (as functions) is stable under multiplication by `x`. -/
lemma span_mul_x (g : Zon → ℝ) (hg : g ∈ Submodule.span ℝ (Set.range UZ)) :
    (fun x : Zon => x.1 * g x) ∈ Submodule.span ℝ (Set.range UZ) := by
  induction hg using Submodule.span_induction with
  | mem g hg => obtain ⟨k, rfl⟩ := hg; exact xU_mem k
  | zero =>
    have : (fun x : Zon => x.1 * (0 : Zon → ℝ) x) = 0 := by funext x; simp
    rw [this]; exact Submodule.zero_mem _
  | add a b _ _ ha hb =>
    have : (fun x : Zon => x.1 * (a + b) x) = (fun x : Zon => x.1 * a x) + fun x : Zon => x.1 * b x := by
      funext x; simp [mul_add]
    rw [this]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha =>
    have : (fun x : Zon => x.1 * (c • a) x) = c • fun x : Zon => x.1 * a x := by
      funext x; simp [mul_left_comm]
    rw [this]; exact Submodule.smul_mem _ _ ha

lemma pow_mem_span (n : ℕ) : (fun x : Zon => x.1 ^ n) ∈ Submodule.span ℝ (Set.range UZ) := by
  induction n with
  | zero =>
    have : (fun x : Zon => x.1 ^ 0) = UZ 0 := by
      funext x
      simp [UZ, mk, Utheta]
    rw [this]; exact Submodule.subset_span ⟨0, rfl⟩
  | succ n ih =>
    have := span_mul_x _ ih
    convert this using 2 with x
    ring

lemma poly_mem_span (p : Polynomial ℝ) :
    (fun x : Zon => p.eval x.1) ∈ Submodule.span ℝ (Set.range UZ) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    have : (fun x : Zon => (p + q).eval x.1) = (fun x : Zon => p.eval x.1) + fun x : Zon => q.eval x.1 := by
      funext x; simp
    rw [this]; exact Submodule.add_mem _ hp hq
  | monomial n a =>
    have : (fun x : Zon => (Polynomial.monomial n a).eval x.1) = a • fun x : Zon => x.1 ^ n := by
      funext x; simp
    rw [this]; exact Submodule.smul_mem _ _ (pow_mem_span n)

lemma toLp_mem_span (g : Zon → ℝ) (hg : g ∈ Submodule.span ℝ (Set.range UZ)) :
    ∃ h : MemLp g 2 μZ, h.toLp g ∈ Submodule.span ℝ (Set.range eZ) := by
  induction hg using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨k, rfl⟩ := hg
    exact ⟨memLp_of_mem (UZ_mem k) 2, Submodule.subset_span ⟨k, rfl⟩⟩
  | zero =>
    have hz : MemLp (0 : Zon → ℝ) 2 μZ := MemLp.zero
    refine ⟨hz, ?_⟩
    have : (hz.toLp (0 : Zon → ℝ) : Lp ℝ 2 μZ) = 0 := MemLp.toLp_zero hz
    rw [this]; exact Submodule.zero_mem _
  | add a b _ _ ha hb =>
    obtain ⟨h1, h1'⟩ := ha
    obtain ⟨h2, h2'⟩ := hb
    refine ⟨h1.add h2, ?_⟩
    rw [MemLp.toLp_add h1 h2]
    exact Submodule.add_mem _ h1' h2'
  | smul c a _ ha =>
    obtain ⟨h1, h1'⟩ := ha
    refine ⟨h1.const_smul c, ?_⟩
    rw [MemLp.toLp_const_smul c h1]
    exact Submodule.smul_mem _ _ h1'

/-- the classes `e_k` span a dense subspace of `L²(μ)`. -/
lemma dense_span_eZ : ⊤ ≤ (Submodule.span ℝ (Set.range eZ)).topologicalClosure := by
  intro u _
  set S := Submodule.span ℝ (Set.range eZ) with hS
  have h1 : DenseRange (ContinuousMap.toLp (E := ℝ) 2 μZ ℝ : C(Zon, ℝ) →L[ℝ] Lp ℝ 2 μZ) :=
    ContinuousMap.toLp_denseRange ℝ μZ ℝ (by norm_num)
  have hTc : IsClosed (S.topologicalClosure : Set (Lp ℝ 2 μZ)) :=
    Submodule.isClosed_topologicalClosure _
  have hpoly : ∀ c : C(Zon, ℝ), ContinuousMap.toLp (E := ℝ) 2 μZ ℝ c ∈
      (S.topologicalClosure : Set (Lp ℝ 2 μZ)) := by
    intro c
    have hc : c ∈ closure ((polynomialFunctions (Set.Icc (-1 : ℝ) 1) : Subalgebra ℝ C(Zon, ℝ)) :
        Set C(Zon, ℝ)) := by
      rw [← Subalgebra.topologicalClosure_coe, polynomialFunctions_closure_eq_top]; trivial
    have := map_mem_closure (t := (S : Set (Lp ℝ 2 μZ)))
      (ContinuousMap.toLp (E := ℝ) 2 μZ ℝ).continuous hc (by
        rintro q ⟨p, -, rfl⟩
        obtain ⟨h, hmem⟩ := toLp_mem_span (fun x : Zon => p.eval x.1) (poly_mem_span p)
        show ContinuousMap.toLp (E := ℝ) 2 μZ ℝ (Polynomial.toContinuousMapOn p (Set.Icc (-1 : ℝ) 1)) ∈ _
        have e : ContinuousMap.toLp (E := ℝ) 2 μZ ℝ (Polynomial.toContinuousMapOn p (Set.Icc (-1 : ℝ) 1)) =
            h.toLp (fun x : Zon => p.eval x.1) := by
          refine Lp.ext ?_
          filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (μ := μZ) (𝕜 := ℝ)
            (Polynomial.toContinuousMapOn p (Set.Icc (-1 : ℝ) 1)), h.coeFn_toLp] with x h1 h2
          rw [h1, h2]; simp
        rw [e]; exact hmem)
    rw [Submodule.topologicalClosure_coe]; exact this
  have : closure (Set.range (ContinuousMap.toLp (E := ℝ) 2 μZ ℝ : C(Zon, ℝ) →L[ℝ] Lp ℝ 2 μZ)) ⊆
      (S.topologicalClosure : Set (Lp ℝ 2 μZ)) :=
    closure_minimal (by rintro _ ⟨c, rfl⟩; exact hpoly c) hTc
  rw [h1.closure_range] at this
  exact this (mem_univ u)

end MarkovTriple.BGL.Instances.Sphere
