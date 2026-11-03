import Mathlib
import MarkovTriple.BGL.Instances.GibbsRd.EllipticFriedrichsMain
import MarkovTriple.BGL.Instances.GibbsRd.EllipticLocalConst

/-!
# `L²_loc ⇒ H¹_loc` for `EllData` (R16, Friedrichs step)

Statement M2 of `STATEMENTS_R16_Friedrichs.md`: the form feeding `EllReg`/`weakHypo_of_reg`.  Specialisation of
`Elliptic.sobolev_one_of_veryWeak` to `b = w · a`, `F = h · w`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace MarkovTriple.BGL.Instances.GibbsRd

open MarkovTriple.BGL (pderiv)
open Elliptic

variable {d : ℕ}

namespace EllData
variable (E : EllData d)

/-- the divergence-form coefficient matrix `bᵢⱼ = w aᵢⱼ` -/
noncomputable def bco : Fin d → Fin d → Rd d → ℝ := fun i j x => E.w x * E.a i j x

lemma bco_smooth (i j : Fin d) : Sm (E.bco i j) := E.w_smooth.mul (E.a_smooth i j)

lemma bco_symm (i j : Fin d) (x : Rd d) : E.bco i j x = E.bco j i x := by
  unfold bco; rw [E.a_symm i j x]

/-- `Pop (w a) f = w · L f` -/
lemma Pop_bco {f : Rd d → ℝ} (x : Rd d) : Pop E.bco f x = E.L f x * E.w x := by
  have hP : ∀ i, E.P f i = fun y => ∑ j, E.bco i j y * pderiv f j y := fun i => by
    funext y; unfold P bco; rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  unfold Pop
  rw [E.L_eq]
  have := (E.w_pos x).ne'
  simp_rw [← hP]
  field_simp

/-- local uniform ellipticity of `w a` on compact sets -/
lemma bco_elliptic {K : Set (Rd d)} (hK : IsCompact K) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ x ∈ K, ∀ ξ : Fin d → ℝ,
      lam * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, E.bco i j x * ξ i * ξ j := by
  obtain ⟨l0, hl0, hell⟩ := E.local_ellipticity hK
  obtain ⟨m, hm, hmK⟩ := E.exists_dens_lower hK
  refine ⟨E.Z * m * l0, by have := E.Z_pos; positivity, fun x hx ξ => ?_⟩
  have h1 : E.Z * m ≤ E.w x := by
    have := hmK x hx
    have e : E.dens x = E.w x / E.Z := rfl
    rw [e, le_div_iff₀ E.Z_pos] at this
    linarith
  have h2 := hell x hx ξ
  have e : ∑ i, ∑ j, E.bco i j x * ξ i * ξ j = E.w x * ∑ i, ∑ j, E.a i j x * ξ i * ξ j := by
    unfold bco
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [e]
  have hsum : 0 ≤ ∑ i, ξ i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  calc E.Z * m * l0 * ∑ i, ξ i ^ 2 = (E.Z * m) * (l0 * ∑ i, ξ i ^ 2) := by ring
    _ ≤ E.w x * ∑ i, ∑ j, E.a i j x * ξ i * ξ j :=
        mul_le_mul h1 h2 (mul_nonneg hl0.le hsum) ((mul_pos E.Z_pos hm).le.trans h1)

/-- **M2**: a very weak solution `u ∈ L²_loc` of `L u = h ∈ L²_loc` (in the form of `resolvent_weak`) lies in `H¹_loc`.
This is the `L²_loc ⇒ H¹_loc` step feeding `EllReg`/`weakHypo_of_reg`. -/
theorem sobolev_one_of_veryWeak {u h : Rd d → ℝ} (hu : LocL2 u) (hh : LocL2 h) (hW : E.VeryWeakSol u h) :
    Sobolev 1 u := by
  refine Elliptic.sobolev_one_of_veryWeak (b := E.bco) E.bco_smooth E.bco_symm (fun K hK => E.bco_elliptic hK) hu
    (F := fun x => E.w x * h x) (hh.mul_continuous E.w_smooth.continuous) ?_
  intro a ha hc
  have := hW a ⟨ha, hc⟩
  have e1 : ∀ x, u x * Pop E.bco a x = u x * E.L a x * E.w x := fun x => by rw [E.Pop_bco]; ring
  simp_rw [e1]
  rw [this]
  exact integral_congr_ae (Eventually.of_forall fun x => by ring)

end EllData

end MarkovTriple.BGL.Instances.GibbsRd
