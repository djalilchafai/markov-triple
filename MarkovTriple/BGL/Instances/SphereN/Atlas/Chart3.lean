import Mathlib
import MarkovTriple.BGL.Instances.SphereN.Triple
import MarkovTriple.BGL.Instances.SphereN.Curv2
import MarkovTriple.BGL.Instances.Riemannian.R27.Sphere2Coord

/-!
# `S2 ≃ Sph 3` and the chain rule for the stereographic charts (Round 29, stream R)

`eS2 : S2 ≃ Sph 3` (`p ↦ toLp p`), the point `P_b(y) = (ptS b y).1 ∈ ℝ³` of chart `b`, and the chain rule for
`F = E ∘ P_b` with `E` smooth off the origin (the degree-0 extension of a function of `𝒜₀`).
-/

open MeasureTheory Filter Topology
open MarkovTriple.BGL (pderiv)

namespace MarkovTriple.BGL.SphereN.Atlas

open MarkovTriple.BGL.Instances.Riemannian.R27
open LebesgueRd

lemma sum_sq_fin3 (p : Fin 3 → ℝ) : LebesgueRd.sq p = p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2 := by
  simp [LebesgueRd.sq, Fin.sum_univ_three]

/-- the point of `Sph 3` underlying a point of `S2` -/
noncomputable def toSph3 (p : S2) : Sph 3 :=
  ⟨(WithLp.toLp 2 p.1 : Ee 3), by
    rw [mem_sphere_zero_iff_norm, EuclideanSpace.norm_eq]
    have h := p.2
    simp [Fin.sum_univ_three, h]⟩

/-- the equivalence `S2 ≃ Sph 3` -/
noncomputable def eS2 : S2 ≃ Sph 3 where
  toFun := toSph3
  invFun := fun x => ⟨cv (x : Ee 3), by
    have h := sq_cv x
    rw [sum_sq_fin3] at h
    exact h⟩
  left_inv := fun p => rfl
  right_inv := fun x => rfl

theorem eS2_coord (p : S2) (a : Fin 3) : (eS2 p : Ee 3) a = p.1 a := rfl

lemma cv_eS2 (p : S2) : cv ((eS2 p : Sph 3) : Ee 3) = p.1 := rfl

/-- the point of `ℝ³` of the chart `b` -/
noncomputable def Pc (b : Bool) (y : Ev 2) : Fin 3 → ℝ := (ptS b y).1

lemma Pc_ne (b : Bool) (y : Ev 2) : Pc b y ≠ 0 := by
  intro h
  have := (ptS b y).2
  have h0 : (ptS b y).1 0 = 0 := congrFun h 0
  have h1 : (ptS b y).1 1 = 0 := congrFun h 1
  have h2 : (ptS b y).1 2 = 0 := congrFun h 2
  rw [h0, h1, h2] at this
  norm_num at this

lemma Pc_apply (b : Bool) (y : Ev 2) (a : Fin 3) : Pc b y a = csign b a * Fc a y :=
  coord_pt b a y

lemma contDiff_Pc (b : Bool) (a : Fin 3) (k : WithTop ℕ∞) : ContDiff ℝ k (fun y => Pc b y a) := by
  have : (fun y => Pc b y a) = fun y => csign b a * Fc a y := funext fun y => Pc_apply b y a
  rw [this]
  exact contDiff_const.mul (contDiff_Fc k a)

lemma diff_Pc (b : Bool) (a : Fin 3) (y : Ev 2) : DifferentiableAt ℝ (fun z => Pc b z a) y :=
  ((contDiff_Pc b a 2).differentiable (by norm_num)) y

lemma diff_dd_Pc (b : Bool) (a : Fin 3) (k : Fin 2) (y : Ev 2) :
    DifferentiableAt ℝ (dd k (fun z => Pc b z a)) y := by
  have h : ContDiff ℝ 1 (dd k (fun z => Pc b z a)) :=
    ((contDiff_Pc b a 2).fderiv_right (by norm_num)).clm_apply contDiff_const
  exact (h.differentiable (by norm_num)) y

/-- chain rule for a function smooth off the origin composed with a map avoiding the origin -/
lemma dd_comp_O {m : ℕ} {E : (Fin 3 → ℝ) → ℝ} (hE : SmO E) {P : (Fin m → ℝ) → (Fin 3 → ℝ)}
    {y : Fin m → ℝ} (hP : ∀ a, DifferentiableAt ℝ (fun z => P z a) y) (h0 : P y ≠ 0) (i : Fin m) :
    dd i (fun z => E (P z)) y = ∑ a, dd a E (P y) * dd i (fun z => P z a) y := by
  have hF : HasFDerivAt P (ContinuousLinearMap.pi fun j => fderiv ℝ (fun z => P z j) y) y :=
    hasFDerivAt_pi'.2 fun j => (hP j).hasFDerivAt
  have hψd : HasFDerivAt E (fderiv ℝ E (P y)) (P y) := (hE.differentiableAt h0).hasFDerivAt
  have h := hψd.comp y hF
  have h2 : fderiv ℝ (fun z => E (P z)) y = _ := h.fderiv
  unfold dd
  rw [h2]
  simp only [ContinuousLinearMap.comp_apply]
  rw [MarkovTriple.BGL.Lebesgue.clm_pi_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [ContinuousLinearMap.pi_apply]
  ring

end MarkovTriple.BGL.SphereN.Atlas
