import Mathlib
import MarkovTriple.BGL.Frozen.CD
import MarkovTriple.BGL.FullBasic
import MarkovTriple.BGL.Theory.Gamma2Integral

/-!
# Calculus on the extended algebra `𝒜`: `L` and `Γ` only depend on a.e.-classes; semigroup
representatives

For a full triple `T`:

* `L_congr_A`: `u, v ∈ 𝒜`, `u = v` a.e. ⇒ `L u = L v` a.e. (F7 in both slots + F2);
* `ΓA_congr_A`: the same for `Γ(u,u)`;
* `Pt T t f`: a chosen representative in `𝒜` of the class `P_t[f]` (`f ∈ 𝒜₀`, F8), with
  `Pt_mem_A`, `Pt_ae`.
-/

open MeasureTheory Filter Topology
open scoped NNReal ENNReal InnerProductSpace

namespace MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E]

namespace FullTriple

variable (T : FullTriple E)

/-- `L` is well defined on a.e.-classes of `𝒜`. -/
theorem L_congr_A {u v : E → ℝ} (hu : u ∈ T.A) (hv : v ∈ T.A) (h : u =ᵐ[T.μ] v) :
    T.L u =ᵐ[T.μ] T.L v := by
  set d : E → ℝ := T.L u - T.L v with hd
  have hdA : d ∈ T.A := T.A.sub_mem (T.L_mem_A u hu) (T.L_mem_A v hv)
  have hint : ∀ g ∈ T.A₀, ∫ x, g x * d x ∂T.μ = 0 := by
    intro g hg
    have i1 := (integrable_F7 T hu hg).2.1
    have i2 := (integrable_F7 T hv hg).2.1
    have e1 : ∫ x, g x * T.L u x ∂T.μ = ∫ x, u x * T.L g x ∂T.μ := by
      have a1 := (T.ibp_A u hu g hg).1
      have a2 := (T.ibp_A u hu g hg).2
      linarith
    have e2 : ∫ x, g x * T.L v x ∂T.μ = ∫ x, v x * T.L g x ∂T.μ := by
      have a1 := (T.ibp_A v hv g hg).1
      have a2 := (T.ibp_A v hv g hg).2
      linarith
    have e3 : ∫ x, u x * T.L g x ∂T.μ = ∫ x, v x * T.L g x ∂T.μ :=
      integral_congr_ae (by filter_upwards [h] with x hx; rw [hx])
    have : (fun x => g x * d x) = fun x => g x * T.L u x - g x * T.L v x := by
      funext x; simp only [hd, Pi.sub_apply]; ring
    rw [this, integral_sub i1 i2, e1, e2, e3, sub_self]
  have h1 : 0 ≤ᵐ[T.μ] d := T.pos_detect d hdA (fun k _ _ => (hint k ‹_›).symm ▸ le_refl _)
  have h2 : 0 ≤ᵐ[T.μ] -d := T.pos_detect (-d) (T.A.neg_mem hdA) (fun k hk _ => by
    have : ∫ x, k x * (-d) x ∂T.μ = 0 := by
      have e : (fun x => k x * (-d) x) = fun x => -(k x * d x) := by
        funext x; simp
      rw [e, integral_neg, hint k hk, neg_zero]
    exact this.symm ▸ le_refl _)
  filter_upwards [h1, h2] with x hx1 hx2
  simp only [hd, Pi.sub_apply, Pi.zero_apply, Pi.neg_apply] at hx1 hx2
  linarith

/-- `Γ(u,u)` is well defined on a.e.-classes of `𝒜`. -/
theorem ΓA_congr_A {u v : E → ℝ} (hu : u ∈ T.A) (hv : v ∈ T.A) (h : u =ᵐ[T.μ] v) :
    T.toDiffusionTriple.ΓA u u =ᵐ[T.μ] T.toDiffusionTriple.ΓA v v := by
  have h1 := L_congr_A T (T.A.mul_mem hu hu) (T.A.mul_mem hv hv)
    (by filter_upwards [h] with x hx; simp [hx])
  have h2 := L_congr_A T hu hv h
  filter_upwards [h, h1, h2] with x hx hx1 hx2
  simp only [DiffusionTriple.ΓA]
  rw [hx1, hx2, hx]

/-- A chosen representative in `𝒜` of the class `P_t [f]`, `f ∈ 𝒜₀` (F8). -/
noncomputable def Pt (t : ℝ≥0) (f : T.A₀) : E → ℝ := Classical.choose (T.semigroup_A t f)

theorem Pt_mem_A (t : ℝ≥0) (f : T.A₀) : T.Pt t f ∈ T.A :=
  (Classical.choose_spec (T.semigroup_A t f)).1

theorem Pt_ae (t : ℝ≥0) (f : T.A₀) :
    ((T.toDiffusionTriple.semigroup t (T.toDiffusionTriple.cls f) : Lp ℝ 2 T.μ) : E → ℝ) =ᵐ[T.μ]
      T.Pt t f :=
  (Classical.choose_spec (T.semigroup_A t f)).2

theorem Pt_memLp (t : ℝ≥0) (f : T.A₀) : MemLp (T.Pt t f) 2 T.μ :=
  (Lp.memLp (T.toDiffusionTriple.semigroup t (T.toDiffusionTriple.cls f))).ae_eq (T.Pt_ae t f)

theorem Pt_zero (f : T.A₀) : T.Pt 0 f =ᵐ[T.μ] f.1 := by
  have h := T.Pt_ae 0 f
  rw [DiffusionTriple.semigroup_zero] at h
  simp only [ContinuousLinearMap.one_apply] at h
  exact h.symm.trans (DiffusionTriple.coeFn_cls T.toDiffusionTriple f)

theorem Pt_nonneg (t : ℝ≥0) (f : T.A₀) (hf : 0 ≤ᵐ[T.μ] f.1) : 0 ≤ᵐ[T.μ] T.Pt t f := by
  have h0 : 0 ≤ᵐ[T.μ] ((T.toDiffusionTriple.cls f : Lp ℝ 2 T.μ) : E → ℝ) := by
    filter_upwards [DiffusionTriple.coeFn_cls T.toDiffusionTriple f, hf] with x h1 h2
    rw [h1]; exact h2
  have := T.toDiffusionTriple.semigroup_nonneg t h0
  filter_upwards [this, T.Pt_ae t f] with x h1 h2
  rw [← h2]; exact h1

end FullTriple

end MarkovTriple.BGL
