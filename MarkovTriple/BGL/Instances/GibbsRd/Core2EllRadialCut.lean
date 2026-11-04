import Mathlib
import MarkovTriple.BGL.Instances.GibbsRd.Core2EllRadialCalc
import MarkovTriple.BGL.Instances.GibbsRd.Core2RdCut

/-!
# One-variable cut-offs `σ(s/R)` and the scalar estimates (R19, Stream A6, target T6)

`σ(u) = s(2 - u)` (`s = smoothTransition`): `σ = 1` on `u ≤ 1`, `σ = 0` on `u ≥ 2`, `0 ≤ σ ≤ 1`, all derivatives bounded
and vanishing outside `[1,2]`.  `iter_scale`: `(σ(·/R))^{(k)}(s) = R^{-k} σ^{(k)}(s/R)`.  `norm_bounds`: the polynomial bounds
that make all cut-off quantities uniformly bounded under the scale-invariant growth conditions on `(α, β)`.
-/

open MeasureTheory Filter Topology Set
open MarkovTriple.BGL (pderiv)

namespace MarkovTriple.BGL.Instances.GibbsRd

/-- the one-variable cut-off: `1` on `u ≤ 1`, `0` on `u ≥ 2` -/
noncomputable def sig (u : ℝ) : ℝ := Real.smoothTransition (2 - u)

lemma sig_smooth : S1 sig :=
  Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id)

lemma sig_nonneg (u : ℝ) : 0 ≤ sig u := Real.smoothTransition.nonneg _

lemma sig_le_one (u : ℝ) : sig u ≤ 1 := Real.smoothTransition.le_one _

lemma sig_eq_one {u : ℝ} (h : u ≤ 1) : sig u = 1 := Real.smoothTransition.one_of_one_le (by linarith)

lemma sig_eq_zero {u : ℝ} (h : 2 ≤ u) : sig u = 0 := Real.smoothTransition.zero_of_nonpos (by linarith)

/-- derivatives of a function that is locally constant vanish. -/
lemma iter_deriv_zero_of_loc (k : ℕ) : ∀ (f : ℝ → ℝ) (u c : ℝ), f =ᶠ[𝓝 u] (fun _ => c) →
    deriv^[k + 1] f u = 0 := by
  induction k with
  | zero =>
    intro f u c h
    show deriv f u = 0
    rw [h.deriv_eq]; simp
  | succ k ih =>
    intro f u c h
    rw [Function.iterate_succ_apply]
    refine ih (deriv f) u 0 ?_
    filter_upwards [h.eventually_nhds] with y hy
    rw [(show f =ᶠ[𝓝 y] fun _ => c from hy).deriv_eq]; simp

lemma sig_iter_zero (k : ℕ) {u : ℝ} (h : u < 1 ∨ 2 < u) : deriv^[k + 1] sig u = 0 := by
  rcases h with h | h
  · refine iter_deriv_zero_of_loc k sig u 1 ?_
    filter_upwards [Iio_mem_nhds h] with y hy
    exact sig_eq_one (le_of_lt hy)
  · refine iter_deriv_zero_of_loc k sig u 0 ?_
    filter_upwards [Ioi_mem_nhds h] with y hy
    exact sig_eq_zero (le_of_lt hy)

lemma sig_iter_bdd (k : ℕ) : ∃ M : ℝ, 0 ≤ M ∧ ∀ u, |deriv^[k] sig u| ≤ M := by
  cases k with
  | zero =>
    refine ⟨1, zero_le_one, fun u => ?_⟩
    simp only [Function.iterate_zero, id]
    rw [abs_of_nonneg (sig_nonneg u)]; exact sig_le_one u
  | succ k =>
    have hc : Continuous (deriv^[k + 1] sig) := (sig_smooth.iterate_deriv (k + 1)).continuous
    have hs : HasCompactSupport (deriv^[k + 1] sig) := by
      refine HasCompactSupport.intro (isCompact_Icc (a := (1 : ℝ)) (b := 2)) fun u hu => ?_
      refine sig_iter_zero k ?_
      by_contra hcon
      push Not at hcon
      exact hu ⟨hcon.1, hcon.2⟩
    obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support hs
    exact ⟨max C 0, le_max_right _ _, fun u => by
      have := hC u
      simp only [Real.norm_eq_abs] at this
      exact this.trans (le_max_left _ _)⟩

/-- a common bound `M ≥ 1` for `σ, …, σ⁗`. -/
lemma sig_bound : ∃ M : ℝ, 1 ≤ M ∧ (∀ u, |sig u| ≤ M) ∧ (∀ u, |deriv sig u| ≤ M) ∧
    (∀ u, |deriv (deriv sig) u| ≤ M) ∧ (∀ u, |deriv (deriv (deriv sig)) u| ≤ M) ∧
    (∀ u, |deriv (deriv (deriv (deriv sig))) u| ≤ M) := by
  obtain ⟨M0, h0, b0⟩ := sig_iter_bdd 0
  obtain ⟨M1, h1, b1⟩ := sig_iter_bdd 1
  obtain ⟨M2, h2, b2⟩ := sig_iter_bdd 2
  obtain ⟨M3, h3, b3⟩ := sig_iter_bdd 3
  obtain ⟨M4, h4, b4⟩ := sig_iter_bdd 4
  refine ⟨1 + M0 + M1 + M2 + M3 + M4, by linarith, fun u => ?_, fun u => ?_, fun u => ?_, fun u => ?_,
    fun u => ?_⟩
  · have := b0 u; simp only [Function.iterate_zero, id] at this; linarith
  · have := b1 u; simp only [Function.iterate_one] at this; linarith
  · have := b2 u; change |deriv (deriv sig) u| ≤ M2 at this; linarith
  · have := b3 u; change |deriv (deriv (deriv sig)) u| ≤ M3 at this; linarith
  · have := b4 u; change |deriv (deriv (deriv (deriv sig))) u| ≤ M4 at this; linarith

/-- the scaled cut-off `s ↦ σ(s/R)` -/
noncomputable def phiR (R : ℝ) (s : ℝ) : ℝ := sig (s / R)

lemma phiR_smooth (R : ℝ) : S1 (phiR R) :=
  sig_smooth.comp (contDiff_id.div_const R)

lemma hasDerivAt_scale {g : ℝ → ℝ} (hg : S1 g) (R : ℝ) (s : ℝ) :
    HasDerivAt (fun s => g (s / R)) (deriv g (s / R) * (1 / R)) s :=
  (hg.hasDerivAt (s / R)).comp s ((hasDerivAt_id s).div_const R)

/-- `(σ(·/R))^{(k)}(s) = R^{-k} σ^{(k)}(s/R)` -/
lemma iter_scale (R : ℝ) (k : ℕ) :
    deriv^[k] (phiR R) = fun s => (1 / R) ^ k * deriv^[k] sig (s / R) := by
  induction k with
  | zero => funext s; simp [phiR]
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    funext s
    have hg : S1 (deriv^[k] sig) := sig_smooth.iterate_deriv k
    have := (hasDerivAt_scale hg R s).const_mul ((1 / R) ^ k)
    rw [this.deriv, Function.iterate_succ_apply' deriv k sig]
    ring

end MarkovTriple.BGL.Instances.GibbsRd
