import Mathlib
import MarkovTriple.BGL.Analysis.OU.Esa

/-!
# OU: "tail" families of rescaled cut-off derivatives (for `Core2`)

`Tl ω` : the family `c ↦ ω c` of smooth functions is a finite combination of `x ↦ c^j θ(c x)` with `θ` smooth,
compactly supported, vanishing on `|y| < 1`.  Closed under `d/dx`, `x·d/dx`, `L`.  Gives uniform bounds and vanishing on `|x| < 1/c`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal Real

namespace MarkovTriple.Sanity.OU

inductive Tl : (ℝ → ℝ → ℝ) → Prop
  | base (θ : ℝ → ℝ) (j : ℕ) (hs : Sm θ) (hc : HasCompactSupport θ) (hz : ∀ y, |y| < 1 → θ y = 0) :
      Tl (fun c x => c ^ j * θ (c * x))
  | add {a b : ℝ → ℝ → ℝ} : Tl a → Tl b → Tl (fun c x => a c x + b c x)
  | smul (r : ℝ) {a : ℝ → ℝ → ℝ} : Tl a → Tl (fun c x => r * a c x)

lemma deriv_zero_of_vanish {θ : ℝ → ℝ} (hz : ∀ y, |y| < 1 → θ y = 0) {y : ℝ} (hy : |y| < 1) :
    deriv θ y = 0 := by
  have : {z : ℝ | |z| < 1} ∈ 𝓝 y := (isOpen_lt continuous_abs continuous_const).mem_nhds hy
  have e : θ =ᶠ[𝓝 y] fun _ => 0 := by
    filter_upwards [this] with z hz' using hz z hz'
  rw [e.deriv_eq]; simp

lemma Tl.sm {ω : ℝ → ℝ → ℝ} (h : Tl ω) : ∀ c, Sm (ω c) := by
  induction h with
  | base θ j hs hc hz =>
    intro c
    exact contDiff_const.mul (hs.comp (contDiff_const.mul contDiff_id))
  | add _ _ ha hb => intro c; exact (ha c).add (hb c)
  | smul r _ ha => intro c; exact contDiff_const.mul (ha c)

lemma Tl.bound {ω : ℝ → ℝ → ℝ} (h : Tl ω) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ c : ℝ, 0 < c → c ≤ 1 → ∀ x, |ω c x| ≤ K := by
  induction h with
  | base θ j hs hc hz =>
    obtain ⟨C, hC⟩ := hs.continuous.bounded_above_of_compact_support hc
    have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
    refine ⟨C, hC0, fun c hc0 hc1 x => ?_⟩
    rw [abs_mul, abs_pow, abs_of_pos hc0]
    have := hC (c * x)
    rw [Real.norm_eq_abs] at this
    calc c ^ j * |θ (c * x)| ≤ 1 * C :=
          mul_le_mul (pow_le_one₀ hc0.le hc1) this (abs_nonneg _) (by norm_num)
      _ = C := one_mul C
  | add _ _ ha hb =>
    obtain ⟨K1, h1, hK1⟩ := ha
    obtain ⟨K2, h2, hK2⟩ := hb
    exact ⟨K1 + K2, by positivity, fun c hc0 hc1 x => (abs_add_le _ _).trans
      (add_le_add (hK1 c hc0 hc1 x) (hK2 c hc0 hc1 x))⟩
  | smul r _ ha =>
    obtain ⟨K1, h1, hK1⟩ := ha
    exact ⟨|r| * K1, by positivity, fun c hc0 hc1 x => by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hK1 c hc0 hc1 x) (abs_nonneg _)⟩

lemma Tl.zero {ω : ℝ → ℝ → ℝ} (h : Tl ω) :
    ∀ c : ℝ, 0 < c → ∀ x, |x| < 1 / c → ω c x = 0 := by
  induction h with
  | base θ j hs hc hz =>
    intro c hc0 x hx
    have : |c * x| < 1 := by
      rw [abs_mul, abs_of_pos hc0]
      calc c * |x| < c * (1 / c) := mul_lt_mul_of_pos_left hx hc0
        _ = 1 := by field_simp
    simp [hz _ this]
  | add _ _ ha hb => intro c hc0 x hx; simp [ha c hc0 x hx, hb c hc0 x hx]
  | smul r _ ha => intro c hc0 x hx; simp [ha c hc0 x hx]

lemma hasDerivAt_scaled (θ : ℝ → ℝ) (hs : Sm θ) (c : ℝ) (j : ℕ) (x : ℝ) :
    HasDerivAt (fun x => c ^ j * θ (c * x)) (c ^ (j + 1) * deriv θ (c * x)) x := by
  have h := (hs.hasDerivAt (c * x)).comp x ((hasDerivAt_id' x).const_mul c)
  have h2 := h.const_mul (c ^ j)
  exact h2.congr_deriv (by ring)

lemma Tl.D {ω : ℝ → ℝ → ℝ} (h : Tl ω) : Tl (fun c => deriv (ω c)) := by
  induction h with
  | base θ j hs hc hz =>
    have e : (fun c => deriv (fun x => c ^ j * θ (c * x))) =
        fun c x => c ^ (j + 1) * deriv θ (c * x) := by
      funext c x; exact (hasDerivAt_scaled θ hs c j x).deriv
    rw [e]
    exact Tl.base (deriv θ) (j + 1) hs.deriv' hc.deriv (fun y hy => deriv_zero_of_vanish hz hy)
  | @add a b ha hb iha ihb =>
    have e : (fun c => deriv (fun x => a c x + b c x)) = fun c x => deriv (a c) x + deriv (b c) x := by
      funext c x
      exact ((((ha.sm c).hasDerivAt x).add ((hb.sm c).hasDerivAt x))).deriv
    rw [e]; exact Tl.add iha ihb
  | @smul r a ha iha =>
    have e : (fun c => deriv (fun x => r * a c x)) = fun c x => r * deriv (a c) x := by
      funext c x
      exact (((ha.sm c).hasDerivAt x).const_mul r).deriv
    rw [e]; exact Tl.smul r iha

lemma Tl.X {ω : ℝ → ℝ → ℝ} (h : Tl ω) : Tl (fun c x => x * deriv (ω c) x) := by
  induction h with
  | base θ j hs hc hz =>
    have e : (fun c x => x * deriv (fun x => c ^ j * θ (c * x)) x) =
        fun c x => c ^ j * ((fun y => y * deriv θ y) (c * x)) := by
      funext c x; rw [(hasDerivAt_scaled θ hs c j x).deriv]; ring
    rw [e]
    refine Tl.base (fun y => y * deriv θ y) j (contDiff_id.mul hs.deriv') ?_ ?_
    · exact hc.deriv.mul_left
    · intro y hy; simp [deriv_zero_of_vanish hz hy]
  | @add a b ha hb iha ihb =>
    have e : (fun c x => x * deriv (fun x => a c x + b c x) x) =
        fun c x => x * deriv (a c) x + x * deriv (b c) x := by
      funext c x
      have h2 : deriv (fun x => a c x + b c x) x = deriv (a c) x + deriv (b c) x :=
        (((ha.sm c).hasDerivAt x).add ((hb.sm c).hasDerivAt x)).deriv
      rw [h2]; ring
    rw [e]; exact Tl.add iha ihb
  | @smul r a ha iha =>
    have e : (fun c x => x * deriv (fun x => r * a c x) x) = fun c x => r * (x * deriv (a c) x) := by
      funext c x
      have h2 : deriv (fun x => r * a c x) x = r * deriv (a c) x :=
        (((ha.sm c).hasDerivAt x).const_mul r).deriv
      rw [h2]; ring
    rw [e]; exact Tl.smul r iha

lemma Tl.Lop {ω : ℝ → ℝ → ℝ} (h : Tl ω) : Tl (fun c => Lo (ω c)) := by
  have e : (fun c => Lo (ω c)) = fun c x => deriv (deriv (ω c)) x + (-1 : ℝ) * (x * deriv (ω c) x) := by
    funext c x; unfold Lo; ring
  rw [e]
  exact Tl.add h.D.D (Tl.smul (-1) h.X)

/-- the cutoff derivative family -/
lemma Tl_dcut : Tl (fun c => deriv (cut c)) := by
  have e : (fun c => deriv (cut c)) = fun c x => c ^ 1 * deriv ψ0 (c * x) := by
    funext c x; rw [deriv_cut]; simp
  rw [e]
  exact Tl.base _ 1 ψ0_sm.deriv' ψ0_cs.deriv (fun y hy => dψ0_zero_of_lt hy)

lemma Tl_xdcut : Tl (fun c x => x * deriv (cut c) x) := by
  have e : (fun c x => x * deriv (cut c) x) = fun c x => c ^ 0 * ((fun y => y * deriv ψ0 y) (c * x)) := by
    funext c x; rw [deriv_cut]; simp; ring
  rw [e]
  refine Tl.base _ 0 (contDiff_id.mul ψ0_sm.deriv') ψ0_cs.deriv.mul_left ?_
  intro y hy; simp [dψ0_zero_of_lt hy]

lemma Tl_Lcut : Tl (fun c => Lo (cut c)) := by
  have e : (fun c => Lo (cut c)) = fun c x => deriv (deriv (cut c)) x + (-1 : ℝ) * (x * deriv (cut c) x) := by
    funext c x; unfold Lo; ring
  rw [e]
  exact Tl.add Tl_dcut.D (Tl.smul (-1) Tl_xdcut)

end MarkovTriple.Sanity.OU
