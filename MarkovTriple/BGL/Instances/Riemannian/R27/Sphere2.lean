import Mathlib
import MarkovTriple.BGL.Instances.Riemannian.R27.Sphere2Chart

/-!
# The atlas of `S²` with two stereographic charts (BGL Appendix C.3, Sect. 2.2 example)

Charts `ptS b : ℝ² → S²` (`b : Bool`), co-metric `gS = ((1+|y|²)/2)² δ`, density `wS = 4/(1+|y|²)²`; transition
`y ↦ y/|y|²` on `{y ≠ 0}`.  `sphereAtlas : Atlas S2 2` carries the verified pushforward laws `g_b ∘ τ = J g_a Jᵀ`,
`w_a = (w_b ∘ τ)|det J|` (here `det J = -|y|⁻⁴`).
-/

open MarkovTriple.BGL (pderiv)
open Filter Topology

namespace MarkovTriple.BGL.Instances.Riemannian.R27

lemma pderiv_invS {x : Ev 2} (hx : x ≠ 0) (i k : Fin 2) :
    pderiv (fun y => invS y i) k x = ((if i = k then 1 else 0) * r2 x - x i * (2 * x k)) / r2 x ^ 2 := by
  have h := r2_ne_zero hx
  have hr : DifferentiableAt ℝ r2 x := r2_diff x
  have e : (fun y => invS y i) = fun y => y i * (r2 y)⁻¹ := funext fun y => by simp [invS, div_eq_mul_inv]
  rw [e, pderiv_mul (f := fun y => y i) (g := fun y => (r2 y)⁻¹) (differentiableAt_apply i x) (hr.inv h),
    pderiv_inv hr h, pderiv_r2, pderiv_coord]
  field_simp
  ring

lemma contDiffOn_gS (i j : Fin 2) : ContDiff ℝ (⊤ : ℕ∞) (gS i j) := by
  by_cases h : i = j
  · have : gS i j = fun y => ((1 + r2 y) / 2) ^ 2 := funext fun y => by simp [gS, h]
    rw [this]; unfold r2; fun_prop
  · have : gS i j = fun _ => 0 := funext fun y => by simp [gS, h]
    rw [this]; exact contDiff_const

lemma contDiff_wS : ContDiff ℝ (⊤ : ℕ∞) wS := by
  unfold wS
  refine contDiff_const.div ?_ fun y => by have := one_add_r2_pos y; positivity
  unfold r2; fun_prop

/-- the stereographic chart `b` -/
noncomputable def sph (b : Bool) : Chart S2 2 where
  U := Set.univ
  isOpen := isOpen_univ
  pt := ptS b
  injOn := (ptS_inj b).injOn
  g := gS
  w := wS
  g_smooth := fun i j => (contDiffOn_gS i j).contDiffOn
  w_smooth := contDiff_wS.contDiffOn
  w_pos := fun x _ => wS_pos x

/-- the transition maps -/
noncomputable def τS (a b : Bool) : Ev 2 → Ev 2 := if a = b then fun x => x else invS

lemma τS_same (a : Bool) : τS a a = fun x => x := by simp [τS]
lemma τS_ne {a b : Bool} (h : a ≠ b) : τS a b = invS := by simp [τS, h]

lemma sph_overlap (a b : Bool) : (sph a).overlap (sph b) = {x | a = b ∨ x ≠ 0} := by
  ext x
  constructor
  · rintro ⟨-, y, -, hy⟩
    by_cases hab : a = b
    · exact Or.inl hab
    · refine Or.inr fun hx0 => ?_
      have h2 : sgn b * Fc 2 y = sgn a * Fc 2 x := congrArg (fun p : S2 => p.1 2) hy
      have hs : sgn b = - sgn a := by cases a <;> cases b <;> simp_all [sgn]
      subst hx0
      have hF : Fc 2 (0 : Ev 2) = -1 := by simp [Fc, qf, r2]; norm_num
      rw [hs, hF] at h2
      have hsa := sgn_ne a
      have : Fc 2 y = 1 - 0 := by
        have h3 : Fc 2 y = 1 := by
          have := mul_left_cancel₀ hsa (by linarith : sgn a * Fc 2 y = sgn a * 1)
          exact this
        simpa using h3
      have hq := qf_pos y
      simp only [Fc] at this
      linarith
  · rintro (hab | hx)
    · subst hab
      exact ⟨Set.mem_univ _, x, Set.mem_univ _, rfl⟩
    · by_cases hab : a = b
      · subst hab
        exact ⟨Set.mem_univ _, x, Set.mem_univ _, rfl⟩
      · exact ⟨Set.mem_univ _, invS x, Set.mem_univ _, ptS_invS hab hx⟩

lemma sph_overlap_mem {a b : Bool} {x : Ev 2} (hx : x ∈ (sph a).overlap (sph b)) : a = b ∨ x ≠ 0 := by
  rwa [sph_overlap] at hx

lemma jac_id (x : Ev 2) (i k : Fin 2) : jac (fun x : Ev 2 => x) x i k = if i = k then 1 else 0 := by
  simp only [jac]; exact pderiv_coord i k x

lemma jac_invS {x : Ev 2} (hx : x ≠ 0) (i k : Fin 2) :
    jac invS x i k = ((if i = k then 1 else 0) * r2 x - x i * (2 * x k)) / r2 x ^ 2 := by
  simp only [jac]; exact pderiv_invS hx i k

lemma det_jac_invS {x : Ev 2} (hx : x ≠ 0) : (jac invS x).det = -(r2 x ^ 2)⁻¹ := by
  have h := r2_ne_zero hx
  have e : r2 x = x 0 ^ 2 + x 1 ^ 2 := rfl
  rw [Matrix.det_fin_two]
  simp only [jac_invS hx]
  simp
  rw [e] at h ⊢
  field_simp
  ring

/-- the atlas of `S²` by two stereographic charts -/
noncomputable def sphereAtlas : Atlas S2 2 where
  ι := Bool
  chart := sph
  cover := by
    intro p
    by_cases hp : p.1 2 = 1
    · refine ⟨false, 0, Set.mem_univ _, ?_⟩
      have h0 : p.1 0 = 0 := by
        have := p.2; rw [hp] at this; nlinarith [sq_nonneg (p.1 0), sq_nonneg (p.1 1)]
      have h1 : p.1 1 = 0 := by
        have := p.2; rw [hp] at this; nlinarith [sq_nonneg (p.1 0), sq_nonneg (p.1 1)]
      apply Subtype.ext
      funext i
      have c3 : ∀ i : Fin 3, i = 0 ∨ i = 1 ∨ i = 2 := by decide
      rcases c3 i with rfl | rfl | rfl
      · show Fc 0 (0 : Ev 2) = p.1 0
        simp [Fc, h0]
      · show Fc 1 (0 : Ev 2) = p.1 1
        simp [Fc, h1]
      · show sgn false * Fc 2 (0 : Ev 2) = p.1 2
        simp [Fc, qf, r2, sgn, hp]; norm_num
    · have hlt : p.1 2 < 1 := by
        have := p.2
        have : p.1 2 ^ 2 ≤ 1 := by nlinarith [sq_nonneg (p.1 0), sq_nonneg (p.1 1)]
        have h' : p.1 2 ≤ 1 := by nlinarith
        exact lt_of_le_of_ne h' hp
      have hne : 1 - p.1 2 ≠ 0 := by linarith
      set y : Ev 2 := fun i => if i = 0 then p.1 0 / (1 - p.1 2) else p.1 1 / (1 - p.1 2) with hydef
      refine ⟨true, y, Set.mem_univ _, ?_⟩
      have hc := p.2
      have hr : 1 + r2 y = 2 / (1 - p.1 2) := by
        simp only [r2, hydef]
        simp
        field_simp
        nlinarith [hc]
      have hq : qf y = (1 - p.1 2) / 2 := by
        unfold qf; rw [hr]; field_simp
      apply Subtype.ext
      funext i
      have c3 : ∀ i : Fin 3, i = 0 ∨ i = 1 ∨ i = 2 := by decide
      rcases c3 i with rfl | rfl | rfl
      · show Fc 0 y = p.1 0
        simp only [Fc, hq]; simp only [hydef]; simp; field_simp
      · show Fc 1 y = p.1 1
        simp only [Fc, hq]; simp only [hydef]; simp; field_simp
      · show sgn true * Fc 2 y = p.1 2
        simp only [Fc, hq, sgn]; simp; ring
  τ := τS
  overlap_open := by
    intro a b
    rw [sph_overlap]
    by_cases hab : a = b
    · simp [hab]
    · simp only [hab, false_or]
      exact isOpen_ne
  τ_mem := by
    intro a b x hx
    refine ⟨Set.mem_univ _, ?_⟩
    rcases sph_overlap_mem hx with hab | hx0
    · subst hab; rw [τS_same]
    · by_cases hab : a = b
      · subst hab; rw [τS_same]
      · rw [τS_ne hab]; exact ptS_invS hab hx0
  τ_smooth := by
    intro a b
    by_cases hab : a = b
    · subst hab; rw [τS_same]; exact contDiffOn_id
    · rw [τS_ne hab, sph_overlap]
      simp only [hab, false_or]
      refine contDiffOn_pi.2 fun i => ?_
      refine ContDiffOn.div (contDiff_apply ℝ ℝ i).contDiffOn ?_ fun x hx => r2_ne_zero hx
      unfold r2; exact (by fun_prop : ContDiff ℝ 2 fun y : Ev 2 => y 0 ^ 2 + y 1 ^ 2).contDiffOn
  τ_g := by
    intro a b x hx i j
    show gS i j (τS a b x) = ∑ k, ∑ l, jac (τS a b) x i k * gS k l x * jac (τS a b) x j l
    by_cases hab : a = b
    · subst hab; rw [τS_same]
      simp only [jac_id, gS, Fin.sum_univ_two]
      fin_cases i <;> fin_cases j <;> simp
    · have hx0 : x ≠ 0 := by
        rcases sph_overlap_mem hx with h | h
        · exact absurd h hab
        · exact h
      rw [τS_ne hab]
      have h := r2_ne_zero hx0
      have e : r2 x = x 0 ^ 2 + x 1 ^ 2 := rfl
      simp only [jac_invS hx0, gS, Fin.sum_univ_two, r2_invS hx0]
      fin_cases i <;> fin_cases j <;> simp <;> (simp only [r2] at h ⊢; field_simp) <;> ring
  τ_w := by
    intro a b x hx
    show wS x = wS (τS a b x) * |(jac (τS a b) x).det|
    by_cases hab : a = b
    · subst hab; rw [τS_same]
      have : (jac (fun x : Ev 2 => x) x) = 1 := by
        ext i k; rw [jac_id]; simp [Matrix.one_apply]
      simp [this]
    · have hx0 : x ≠ 0 := by
        rcases sph_overlap_mem hx with h | h
        · exact absurd h hab
        · exact h
      rw [τS_ne hab, det_jac_invS hx0, abs_neg, abs_of_pos (inv_pos.2 (by have := r2_pos hx0; positivity))]
      have h := r2_ne_zero hx0
      have h1 := one_add_r2_ne x
      unfold wS
      rw [r2_invS hx0]
      have h2 : (1 + (r2 x)⁻¹) = (1 + r2 x) / r2 x := by field_simp; ring
      rw [h2]
      field_simp

end MarkovTriple.BGL.Instances.Riemannian.R27
