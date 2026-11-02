import MarkovTriple.BGL.Analysis.Hilbert.Existence
import MarkovTriple.BGL.Analysis.Hilbert.Resolvent
/-! Non-vacuity audit (a): a nontrivial `FormData` on `ℝ²` with `A = diag(1,2) ≠ 0`.
Checks that `exists_semigroup` is not satisfied by the trivial semigroup and that the Friedrichs
semigroup is `e^{-tA}` on the eigenbasis. Not imported by root. -/
open MarkovTriple.Hilbert
open scoped NNReal InnerProductSpace

namespace AuditHilbert

abbrev H2 := EuclideanSpace ℝ (Fin 2)

noncomputable def Adiag : H2 →ₗ[ℝ] H2 where
  toFun x := WithLp.toLp 2 ![x 0 * 1, x 1 * 2]
  map_add' x y := by ext i; fin_cases i <;> simp; all_goals ring
  map_smul' c x := by ext i; fin_cases i <;> simp; all_goals ring

lemma Adiag_apply0 (x : H2) : Adiag x 0 = x 0 * 1 := rfl
lemma Adiag_apply1 (x : H2) : Adiag x 1 = x 1 * 2 := rfl

lemma inner_A (x y : H2) : inner ℝ (Adiag x) y = x 0 * y 0 * 1 + x 1 * y 1 * 2 := by
  rw [real_inner_comm]
  simp [PiLp.inner_apply, Fin.sum_univ_two, Adiag_apply0, Adiag_apply1]; ring

noncomputable def diagForm : FormData H2 where
  D := ⊤
  dense := by simp
  A := Adiag.comp (Submodule.subtype ⊤)
  symm f g := by
    show inner ℝ (Adiag f.1) g.1 = inner ℝ f.1 (Adiag g.1)
    rw [inner_A, real_inner_comm, inner_A]; ring
  nonneg f := by
    show 0 ≤ inner ℝ (Adiag f.1) f.1
    rw [inner_A]
    nlinarith [sq_nonneg (f.1 0), sq_nonneg (f.1 1)]

lemma diagA_e0 : diagForm.A ⟨EuclideanSpace.single 0 1, trivial⟩ = (EuclideanSpace.single 0 1 : H2) := by
  show Adiag _ = _
  ext i; fin_cases i <;> simp [Adiag_apply0, Adiag_apply1]

lemma single_ne_zero : (EuclideanSpace.single 0 1 : H2) ≠ 0 := by
  intro h
  have := congrArg (fun F : H2 => F 0) h
  simp at this

/-- `A ≠ 0`. -/
theorem diag_A_ne_zero : diagForm.A ≠ 0 := by
  intro h
  have := congrArg (fun F => F ⟨EuclideanSpace.single 0 1, trivial⟩) h
  rw [diagA_e0] at this
  exact single_ne_zero this

/-- Any semigroup given by `exists_semigroup` is not the trivial one (its generator is `-A ≠ 0`). -/
theorem exists_semigroup_nontrivial :
    ∃ (P : ℝ≥0 → H2 →L[ℝ] H2) (G : H2 →ₗ.[ℝ] H2),
      IsSelfAdjointContractionSemigroup P ∧ IsGeneratorOf G P ∧ P ≠ fun _ => 1 := by
  obtain ⟨P, G, hP, -, -, -, hG, -, hext⟩ := diagForm.exists_semigroup
  refine ⟨P, G, hP, hG, ?_⟩
  intro hP1
  obtain ⟨h, hGx⟩ := hext ⟨EuclideanSpace.single 0 1, trivial⟩
  have := (hG _ _).1 ⟨h, rfl⟩
  subst hP1
  have h0 : Filter.Tendsto (fun t : ℝ≥0 => ((t : ℝ)⁻¹ • ((1 : H2 →L[ℝ] H2) (EuclideanSpace.single 0 1) - EuclideanSpace.single 0 1) : H2))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by simp
  have h3 := tendsto_nhds_unique this h0
  rw [hGx, diagA_e0] at h3
  exact single_ne_zero (neg_eq_zero.1 h3)

/-- Friedrichs semigroup acts as `e^{-t}` on `e₀` (eigenvalue 1 of `A`). -/
theorem semigroup_eigen0 (t : ℝ≥0) :
    diagForm.semigroup t (EuclideanSpace.single 0 1) =
      Real.exp (-1 * t) • (EuclideanSpace.single 0 1 : H2) := by
  apply diagForm.semigroup_eigen (by norm_num)
  have h := diagForm.R_resolvent ⟨EuclideanSpace.single 0 1, trivial⟩
  have e : diagForm.emb ⟨EuclideanSpace.single 0 1, trivial⟩ = (EuclideanSpace.single 0 1 : H2) := rfl
  have e2 : diagForm.opA ⟨EuclideanSpace.single 0 1, trivial⟩ = (EuclideanSpace.single 0 1 : H2) :=
    diagA_e0
  rw [e, e2] at h
  have h2 : (EuclideanSpace.single 0 1 : H2) + EuclideanSpace.single 0 1 =
      (2:ℝ) • (EuclideanSpace.single 0 1 : H2) := by rw [two_smul]
  rw [h2, map_smul] at h
  rw [show (1 + (1:ℝ))⁻¹ = (2:ℝ)⁻¹ by norm_num]
  calc diagForm.R (EuclideanSpace.single 0 1)
      = (2:ℝ)⁻¹ • ((2:ℝ) • diagForm.R (EuclideanSpace.single 0 1)) := by
        rw [smul_smul]; norm_num
    _ = (2:ℝ)⁻¹ • (EuclideanSpace.single 0 1 : H2) := by rw [h]

end AuditHilbert
#print axioms AuditHilbert.exists_semigroup_nontrivial
#print axioms AuditHilbert.semigroup_eigen0
