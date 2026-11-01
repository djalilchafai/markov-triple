import Mathlib
import MarkovTriple.Hilbert.Complexify

/-!
# Abstract Hilbert lemma behind Lichnerowicz / Bakry–Émery

Let `R` be a self-adjoint operator with `0 ≤ R ≤ 1` (`UnitOp R`; `R = (1 + B)⁻¹` for a
non-negative self-adjoint `B`).  Writing `u = R w`, `B u = w - R w`.  The *squared* inequality
`‖B u‖² ≥ ρ ⟪B u, u⟫` (the integrated `Γ₂ ≥ ρ Γ`) implies the *gap* `⟪B u, u⟫ ≥ ρ ‖u‖²`
on the orthogonal complement of the fixed space `{n | R n = n} = ker B`.

Proof (no spectral measure, only the continuous functional calculus): put `V = R(1-R)`,
`U = √V` (functional calculus), `W = (1-R)²`.  Applying the hypothesis to `w = U z` gives
`ρ ⟪V V z, z⟫ ≤ ⟪W V z, z⟫`, which is the conclusion for `y = (1-R) z`; the set of `y`
satisfying the conclusion is closed and `range (1-R)` is dense in `(ker (1-R))^⊥`.
-/

open scoped InnerProductSpace

namespace MarkovTriple.Hilbert

open Cx

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

lemma sa_inner {X : H →L[ℝ] H} (hX : IsSelfAdjoint X) (u v : H) :
    inner ℝ (X u) v = inner ℝ u (X v) :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hX u v

/-- Key step: the conclusion for vectors of the form `(1 - R) z`. -/
lemma gap_of_square_range {R : H →L[ℝ] H} (hR : UnitOp R) (ρ : ℝ)
    (h : ∀ w : H, ρ * inner ℝ (w - R w) (R w) ≤ ‖w - R w‖ ^ 2) (z : H) :
    ρ * ‖R (z - R z)‖ ^ 2 ≤ inner ℝ ((z - R z) - R (z - R z)) (R (z - R z)) := by
  have hRsa := hR.selfAdjoint
  set s : ℝ → ℝ := fun x => Real.sqrt (x * (1 - x)) with hs
  have hscont : ContinuousOn s (Set.Icc 0 1) := by
    apply Continuous.continuousOn
    exact Real.continuous_sqrt.comp (by fun_prop)
  set U : H →L[ℝ] H := rcfc s R with hU
  have hUsa : IsSelfAdjoint U := hR.isSelfAdjoint_rcfc s
  have hUR : Commute R U := by
    have := hR.commute_rcfc id s
    rw [hR.rcfc_id] at this
    exact this
  -- `U * U = R * (1 - R)`
  have hid : ContinuousOn (fun x : ℝ => x) (Set.Icc 0 1) := continuousOn_id
  have h1x : ContinuousOn (fun x : ℝ => 1 - x) (Set.Icc 0 1) := by
    apply Continuous.continuousOn; fun_prop
  have hone_sub : rcfc (fun x : ℝ => 1 - x) R = 1 - R := by
    rw [hR.rcfc_sub (f := fun _ => (1 : ℝ)) (g := fun x => x) continuousOn_const hid,
      hR.rcfc_one]
    congr 1
    exact hR.rcfc_id
  have hV : rcfc (fun x : ℝ => x * (1 - x)) R = R * (1 - R) := by
    rw [hR.rcfc_mul hid h1x, hone_sub]
    congr 1
    exact hR.rcfc_id
  have hUU : U * U = R * (1 - R) := by
    have h2 : rcfc (fun x => s x * s x) R = U * U := hR.rcfc_mul hscont hscont
    rw [← h2, ← hV]
    apply hR.rcfc_congr
    intro x hx
    simp only [hs]
    exact Real.mul_self_sqrt (mul_nonneg hx.1 (by linarith [hx.2]))
  -- operators
  set V : H →L[ℝ] H := R * (1 - R) with hVdef
  set W : H →L[ℝ] H := (1 - R) * (1 - R) with hWdef
  have h1Rsa : IsSelfAdjoint (1 - R) := (IsSelfAdjoint.one _).sub hRsa
  have hc1R : Commute R (1 - R) := (Commute.one_right R).sub_right (Commute.refl R)
  have hVsa : IsSelfAdjoint V := (IsSelfAdjoint.commute_iff hRsa h1Rsa).mp hc1R
  have hUV : Commute U V := by
    have : Commute U R := hUR.symm
    exact this.mul_right ((Commute.one_right U).sub_right hUR.symm)
  have hUW : Commute U W := by
    have h' : Commute U (1 - R) := (Commute.one_right U).sub_right hUR.symm
    exact h'.mul_right h'
  have hVW : Commute V W := by
    have h' : Commute V (1 - R) := hc1R.mul_left (Commute.refl _)
    exact h'.mul_right h'
  -- `⟪X (U z), U z⟫ = ⟪(X * V) z, z⟫` for `X` commuting with `U`
  have key : ∀ X : H →L[ℝ] H, Commute U X →
      inner ℝ (X (U z)) (U z) = inner ℝ ((X * V) z) z := by
    intro X hX
    have e1 : inner ℝ (X (U z)) (U z) = inner ℝ (U (X (U z))) z := by
      rw [sa_inner hUsa]
    rw [e1]
    congr 1
    have : U * X * U = X * (U * U) := by
      rw [hX.eq, mul_assoc]
    rw [hUU] at this
    exact congrArg (fun T : H →L[ℝ] H => T z) this
  have hh := h (U z)
  have a1 : inner ℝ (U z - R (U z)) (R (U z)) = inner ℝ (V (U z)) (U z) := by
    have : inner ℝ (U z - R (U z)) (R (U z)) = inner ℝ (R (U z - R (U z))) (U z) := by
      rw [sa_inner hRsa]
    rw [this]; rfl
  have a2 : ‖U z - R (U z)‖ ^ 2 = inner ℝ (W (U z)) (U z) := by
    rw [← real_inner_self_eq_norm_sq]
    have : inner ℝ (U z - R (U z)) (U z - R (U z)) =
        inner ℝ ((1 - R) (U z - R (U z))) (U z) := by
      rw [sa_inner h1Rsa]
      rfl
    rw [this]; rfl
  rw [a1, a2, key V hUV, key W hUW] at hh
  -- goal
  have b1 : ‖R (z - R z)‖ ^ 2 = inner ℝ ((V * V) z) z := by
    have : R (z - R z) = V z := rfl
    rw [this, ← real_inner_self_eq_norm_sq, ← sa_inner hVsa]; rfl
  have b2 : inner ℝ ((z - R z) - R (z - R z)) (R (z - R z)) = inner ℝ ((V * W) z) z := by
    have e : (z - R z) - R (z - R z) = W z := by
      simp only [hWdef, ContinuousLinearMap.mul_apply, ContinuousLinearMap.sub_apply,
        ContinuousLinearMap.one_apply]
    have e' : R (z - R z) = V z := rfl
    rw [e, e', ← sa_inner hVsa]; rfl
  rw [b1, b2]
  have : W * V = V * W := hVW.symm.eq
  rw [this] at hh
  exact hh

/-- **Gap from the squared inequality.** -/
theorem gap_of_square {R : H →L[ℝ] H} (hR : UnitOp R) (ρ : ℝ)
    (h : ∀ w : H, ρ * inner ℝ (w - R w) (R w) ≤ ‖w - R w‖ ^ 2)
    {w : H} (hw : ∀ n : H, R n = n → inner ℝ w n = 0) :
    ρ * ‖R w‖ ^ 2 ≤ inner ℝ (w - R w) (R w) := by
  have hRsa := hR.selfAdjoint
  set K : Submodule ℝ H := LinearMap.range ((1 - R : H →L[ℝ] H) : H →ₗ[ℝ] H) with hK
  have hwK : w ∈ K.topologicalClosure := by
    rw [← Submodule.orthogonal_orthogonal_eq_closure]
    intro n hn
    rw [real_inner_comm]
    have hn' : ∀ z, inner ℝ n ((1 - R) z) = 0 := fun z =>
      hn _ ⟨z, rfl⟩ |> fun h0 => by rw [real_inner_comm]; exact h0
    have h1Rsa : IsSelfAdjoint (1 - R) := (IsSelfAdjoint.one _).sub hRsa
    have hz : (1 - R) n = 0 := by
      have : inner ℝ ((1 - R) n) ((1 - R) n) = 0 := by
        rw [← sa_inner h1Rsa]; exact (sa_inner h1Rsa _ _).symm ▸ by
          rw [sa_inner h1Rsa]; exact hn' _
      exact inner_self_eq_zero.mp this
    have : R n = n := by
      have : n - R n = 0 := hz
      exact (sub_eq_zero.mp this).symm
    exact hw n this
  have hclosed : IsClosed {y : H | ρ * ‖R y‖ ^ 2 ≤ inner ℝ (y - R y) (R y)} := by
    apply isClosed_le <;> fun_prop
  have hsub : (K : Set H) ⊆ {y : H | ρ * ‖R y‖ ^ 2 ≤ inner ℝ (y - R y) (R y)} := by
    rintro _ ⟨z, rfl⟩
    exact gap_of_square_range hR ρ h z
  have := closure_minimal hsub hclosed (by rw [← Submodule.topologicalClosure_coe]; exact hwK)
  exact this

end MarkovTriple.Hilbert
