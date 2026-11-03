import Mathlib
import MarkovTriple.BGL.Instances.GibbsRd.EllRegProof
import MarkovTriple.BGL.Instances.GibbsRd.Bochner

/-!
# `ℝ^d` Gibbs: the smooth resolvent solution `v - L v = a` (R18, Stream A3, target B3)

Statements: `STATEMENTS_R18_Core2Rd.md`.  For `a ∈ C_c^∞(ℝ^d)` the Friedrichs resolvent `v = (1-L)⁻¹[a]` has a `C^∞`
representative (chain `v, a, (1-L)a, (1-L)²a, …` and `EllData.ellReg`), which solves `L v = v - a` classically.
No hypothesis on `V`.
-/

open MeasureTheory Filter Topology Set
open MarkovTriple.BGL (pderiv DiffusionTriple)

namespace MarkovTriple.BGL.Instances.GibbsRd

variable {d : ℕ}

namespace EllData
variable (E : EllData d)

/-- symmetry of `L` on test functions. -/
lemma ibp_symm {u b : Rd d → ℝ} (hu : u ∈ A₀ d) (hb : b ∈ A₀ d) :
    ∫ x, u x * E.L b x ∂E.μ = ∫ x, E.L u x * b x ∂E.μ := by
  have h1 := E.ibp_sm (f := b) (g := u) hb.1 hu.1 (Or.inl hu.2)
  have h2 := E.ibp_sm (f := u) (g := b) hu.1 hb.1 (Or.inl hb.2)
  have e : ∫ x, E.Γ u b x ∂E.μ = ∫ x, E.Γ b u x ∂E.μ :=
    integral_congr_ae (Eventually.of_forall fun x => congrFun (E.Γ_symm u b) x)
  have e2 : ∫ x, E.L u x * b x ∂E.μ = ∫ x, b x * E.L u x ∂E.μ :=
    integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)
  rw [h1, e2, h2, e]

/-- iterates of `1 - L` on a test function are test functions. -/
lemma iter_mem {a : Rd d → ℝ} (ha : a ∈ A₀ d) (k : ℕ) :
    (fun f : Rd d → ℝ => fun x => f x - E.L f x)^[k] a ∈ A₀ d := by
  induction k with
  | zero => exact ha
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact (A₀ d).sub_mem ih (E.L_mem ih)

end EllData

namespace GibbsRdData
variable (G : GibbsRdData d)

/-- **B3**: the resolvent solution of `v - L v = a` is smooth, `L²(μ)`, and solves the equation classically. -/
theorem exists_resolvent_smooth {a : Rd d → ℝ} (ha : a ∈ A₀ d) :
    ∃ v : Rd d → ℝ, Sm v ∧ MemLp v 2 G.toEll.μ ∧ ∀ x, Lr G.V v x = v x - a x := by
  set E := G.toEll with hE
  set c : Lp ℝ 2 E.diff.μ := E.diff.cls ⟨a, ha⟩ with hc
  have hca : (c : Rd d → ℝ) =ᵐ[E.μ] a := E.diff.coeFn_cls ⟨a, ha⟩
  set S := DiffusionTriple.formData E.diff with hS
  set z : ℕ → (Rd d → ℝ) := fun k => (fun f : Rd d → ℝ => fun x => f x - E.L f x)^[k] a with hz
  have hzA : ∀ k, z k ∈ A₀ d := fun k => E.iter_mem ha k
  have hzs : ∀ k, z (k + 1) = fun x => z k x - E.L (z k) x := fun k => by
    simp only [hz]; rw [Function.iterate_succ_apply']
  set y : ℕ → (Rd d → ℝ) := fun k => Nat.casesOn k (((S.R c : Lp ℝ 2 E.diff.μ)) : Rd d → ℝ) z with hy
  have hy0 : y 0 = ((S.R c : Lp ℝ 2 E.diff.μ) : Rd d → ℝ) := rfl
  have hyk : ∀ k, y (k + 1) = z k := fun k => rfl
  have hmem : ∀ k, MemLp (y k) 2 E.μ := by
    intro k
    cases k with
    | zero => exact Lp.memLp (S.R c)
    | succ k => exact (hzA k).1.continuous.memLp_of_hasCompactSupport (hzA k).2
  have hweak0 : ∀ b ∈ A₀ d, ∫ x, y 0 x * E.L b x ∂E.μ = ∫ x, (y 0 x - a x) * b x ∂E.μ := by
    intro b hb
    have h := E.diff.resolvent_weak c b hb
    have e : ∫ x, (((S.R c : Lp ℝ 2 E.diff.μ)) : Rd d → ℝ) x * E.diff.L b x ∂E.μ = _ := h
    refine e.trans (integral_congr_ae ?_)
    filter_upwards [hca] with x hx
    rw [hx]; rfl
  have hW : ∀ k, ∀ b ∈ A₀ d, ∫ x, y k x * E.L b x ∂E.μ = ∫ x, (y k x - y (k + 1) x) * b x ∂E.μ := by
    intro k b hb
    cases k with
    | zero => rw [hyk]; exact hweak0 b hb
    | succ k =>
      rw [hyk, hyk, E.ibp_symm (hzA k) hb]
      exact integral_congr_ae (Eventually.of_forall fun x => by rw [hzs k]; ring)
  have hmain : ∀ m : ℕ, ∃ U : Rd d → ℝ, ContDiff ℝ (m : WithTop ℕ∞) U ∧ y 0 =ᵐ[E.μ] U := by
    intro m
    obtain ⟨n, hn⟩ := E.ellReg m
    exact hn y (fun k _ => hmem k) (fun k _ b hb => hW k b hb)
  obtain ⟨X, hX, haeX⟩ := E.smooth_rep_of_forall hmain
  have hXa : ∀ b ∈ A₀ d, ∫ x, X x * E.L b x ∂E.μ = ∫ x, (X x - a x) * b x ∂E.μ := by
    intro b hb
    have h := hweak0 b hb
    have e1 : ∫ x, y 0 x * E.L b x ∂E.μ = ∫ x, X x * E.L b x ∂E.μ :=
      integral_congr_ae (by filter_upwards [haeX] with x hx; rw [hx])
    have e2 : ∫ x, (y 0 x - a x) * b x ∂E.μ = ∫ x, (X x - a x) * b x ∂E.μ :=
      integral_congr_ae (by filter_upwards [haeX] with x hx; rw [hx])
    rw [← e1, ← e2]; exact h
  have hzero : ∀ φ : Rd d → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
      ∫ x, φ x • (E.L X x - (X x - a x)) ∂E.μ = 0 := by
    intro φ hφ hφc
    have hφA : φ ∈ A₀ d := ⟨hφ, hφc⟩
    have b1 := E.ibp_sm (f := X) (g := φ) hX hφ (Or.inl hφc)
    have b2 := E.ibp_sm (f := φ) (g := X) hφ hX (Or.inr hφc)
    have e : ∫ x, E.Γ φ X x ∂E.μ = ∫ x, E.Γ X φ x ∂E.μ :=
      integral_congr_ae (Eventually.of_forall fun x => congrFun (E.Γ_symm φ X) x)
    have i_cs : ∀ h : Rd d → ℝ, Continuous h → HasCompactSupport h → Integrable h E.μ :=
      fun h hc hs => hc.integrable_of_hasCompactSupport hs
    have iA : Integrable (fun x => φ x * E.L X x) E.μ :=
      i_cs _ (hφ.continuous.mul (E.sm_L hX).continuous) hφc.mul_right
    have iB : Integrable (fun x => (X x - a x) * φ x) E.μ :=
      i_cs _ ((hX.continuous.sub ha.1.continuous).mul hφ.continuous) hφc.mul_left
    have e3 : ∫ x, φ x • (E.L X x - (X x - a x)) ∂E.μ =
        ∫ x, φ x * E.L X x ∂E.μ - ∫ x, (X x - a x) * φ x ∂E.μ := by
      rw [← integral_sub iA iB]
      exact integral_congr_ae (Eventually.of_forall fun x => by simp only [smul_eq_mul]; ring)
    have := hXa φ hφA
    rw [e3]
    linarith
  have hcont : Continuous (fun x => E.L X x - (X x - a x)) :=
    (E.sm_L hX).continuous.sub (hX.continuous.sub ha.1.continuous)
  have hloc : LocallyIntegrable (fun x => E.L X x - (X x - a x)) E.μ := hcont.locallyIntegrable
  have hae := ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc hzero
  have h0 := (Continuous.ae_eq_iff_eq E.μ hcont (continuous_const : Continuous fun _ : Rd d => (0 : ℝ))).1 hae
  refine ⟨X, hX, (hmem 0).ae_eq haeX, fun x => ?_⟩
  have := congrFun h0 x
  rw [← G.toEll_L hX]
  linarith

end GibbsRdData

end MarkovTriple.BGL.Instances.GibbsRd
