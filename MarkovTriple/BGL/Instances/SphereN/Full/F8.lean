import Mathlib
import MarkovTriple.BGL.Instances.SphereN.Full.Full

/-!
# F8 for the round sphere: the verified portion (Round 31, stream V)

`SphereF8 n hn` is NOT proved in general (see GAPS "Round 31, Stream V").  Delivered: the trivial case `t = 0`,
a reformulation through the subspace `smoothCls n`, and the linear extension of the polynomial case.
-/

open MeasureTheory
open scoped NNReal

namespace MarkovTriple.BGL.SphereN

variable {n : ℕ}

theorem sphereF8_zero (hn : 2 ≤ n) (f : (sphereDiffusion n hn).A₀) :
    ∃ g ∈ A₀S n, ((sphereDiffusion n hn).semigroup 0 ((sphereDiffusion n hn).cls f) : Sph n → ℝ)
      =ᵐ[σ n] g := by
  refine ⟨f.1, f.2, ?_⟩
  rw [(sphereDiffusion n hn).semigroup_zero]
  exact DiffusionTriple.coeFn_cls (sphereDiffusion n hn) f

theorem sphereF8_iff (hn : 2 ≤ n) :
    SphereF8 n hn ↔ ∀ (t : ℝ≥0) (f : (sphereDiffusion n hn).A₀),
      (sphereDiffusion n hn).semigroup t ((sphereDiffusion n hn).cls f) ∈ smoothCls n :=
  Iff.rfl

theorem sphereF8_of_span (hn : 2 ≤ n) (t : ℝ≥0) {u : Lp ℝ 2 (σ n)}
    (hu : u ∈ Submodule.span ℝ
      {v | ∃ p : Pn n, v = (sphereDiffusion n hn).cls ⟨restr p, restr_mem p⟩}) :
    (sphereDiffusion n hn).semigroup t u ∈ smoothCls n := by
  induction hu using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨p, rfl⟩ := hv
    exact sphere_semigroup_poly_mem hn t p
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact (smoothCls n).add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact (smoothCls n).smul_mem c hx

end MarkovTriple.BGL.SphereN
