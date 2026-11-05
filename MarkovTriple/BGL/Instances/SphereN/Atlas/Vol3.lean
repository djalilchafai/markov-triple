import Mathlib
import MarkovTriple.BGL.Instances.SphereN.Atlas.Vol2

/-!
# The cone map is a bijection of `{v₂ > 0}` onto the complement of the `z`-axis (Round 29, stream R, R2)
-/

open MeasureTheory Filter Topology
open MarkovTriple.BGL (pderiv)

namespace MarkovTriple.BGL.SphereN.Atlas

open MarkovTriple.BGL.Instances.Riemannian.R27

/-- the open upper half space -/
def Hs : Set (Fin 3 → ℝ) := {v | 0 < v 2}

/-- the `z`-axis -/
def Axis : Set (Fin 3 → ℝ) := {z | z 0 = 0 ∧ z 1 = 0}

lemma nrm_sq_Φ (b : Bool) (v : Fin 3 → ℝ) : ∑ a, Φ b v a ^ 2 = v 2 ^ 2 := by
  have := norm_Pc b (yv v)
  unfold Φ
  calc ∑ a, (v 2 * Pc b (yv v) a) ^ 2 = v 2 ^ 2 * ∑ a, Pc b (yv v) a ^ 2 := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun a _ => by ring
    _ = v 2 ^ 2 := by rw [this, mul_one]

lemma injOn_Φ (b : Bool) : Set.InjOn (Φ b) Hs := by
  intro v hv v' hv' h
  have hv2 : 0 < v 2 := hv
  have hv2' : 0 < v' 2 := hv'
  have h1 : v 2 ^ 2 = v' 2 ^ 2 := by rw [← nrm_sq_Φ b v, ← nrm_sq_Φ b v', h]
  have h2 : v 2 = v' 2 := (sq_eq_sq₀ hv2.le hv2'.le).1 h1
  have h3 : ∀ a, Pc b (yv v) a = Pc b (yv v') a := fun a => by
    have := congrFun h a
    simp only [Φ] at this
    rw [h2] at this
    exact mul_left_cancel₀ (h2 ▸ hv2.ne') this
  have h4 : ptS b (yv v) = ptS b (yv v') := by
    apply Subtype.ext
    funext a
    exact h3 a
  have h5 : yv v = yv v' := ptS_inj b h4
  funext j
  fin_cases j
  · exact congrFun h5 0
  · exact congrFun h5 1
  · exact h2

lemma surj_Φ (b : Bool) {z : Fin 3 → ℝ} (hz : z ∉ Axis) : z ∈ Φ b '' Hs := by
  have hz' : z 0 ^ 2 + z 1 ^ 2 ≠ 0 := by
    intro h
    apply hz
    constructor <;> nlinarith [sq_nonneg (z 0), sq_nonneg (z 1)]
  have hr : 0 < z 0 ^ 2 + z 1 ^ 2 + z 2 ^ 2 := by
    have := lt_of_le_of_ne (add_nonneg (sq_nonneg (z 0)) (sq_nonneg (z 1))) (Ne.symm hz')
    nlinarith [sq_nonneg (z 2)]
  set R := Real.sqrt (z 0 ^ 2 + z 1 ^ 2 + z 2 ^ 2) with hR
  have hRpos : 0 < R := Real.sqrt_pos.2 hr
  have hR2 : R ^ 2 = z 0 ^ 2 + z 1 ^ 2 + z 2 ^ 2 := Real.sq_sqrt hr.le
  set u0 := z 0 / R
  set u1 := z 1 / R
  set u2 := z 2 / R
  have hu : u0 ^ 2 + u1 ^ 2 + u2 ^ 2 = 1 := by
    simp only [u0, u1, u2, div_pow]
    rw [← add_div, ← add_div, ← hR2]; exact div_self (pow_pos hRpos 2).ne'
  have hu01 : u0 ^ 2 + u1 ^ 2 ≠ 0 := by
    simp only [u0, u1, div_pow]
    rw [← add_div]; exact div_ne_zero hz' (pow_pos hRpos 2).ne'
  have hs := sgn_sq b
  have hden : 1 - sgn b * u2 ≠ 0 := by
    intro h
    have : sgn b * u2 = 1 := by linarith
    have h2 : u2 ^ 2 = 1 := by
      have := congrArg (· ^ 2) this
      simp only [mul_pow, hs, one_mul, one_pow] at this
      exact this
    apply hu01
    nlinarith [hu, h2]
  let y : Ev 2 := ![u0 / (1 - sgn b * u2), u1 / (1 - sgn b * u2)]
  have hy2 : r2 y = (1 + sgn b * u2) / (1 - sgn b * u2) := by
    simp only [r2, y, Matrix.cons_val_zero, Matrix.cons_val_one]
    field_simp
    nlinarith [hu, hs]
  have hq : qf y = (1 - sgn b * u2) / 2 := by
    unfold qf
    rw [hy2]
    field_simp
    ring
  have hpt : ptS b y = ⟨![u0, u1, u2], by simpa [Fin.sum_univ_three] using hu⟩ := by
    apply Subtype.ext
    funext a
    fin_cases a
    · show Fc 0 y = u0
      simp only [Fc, hq, y]
      simp
      field_simp
    · show Fc 1 y = u1
      simp only [Fc, hq, y]
      simp
      field_simp
    · show sgn b * Fc 2 y = u2
      simp only [Fc, hq]
      have : sgn b * (1 - 2 * ((1 - sgn b * u2) / 2)) = sgn b ^ 2 * u2 := by ring
      show sgn b * (1 - 2 * ((1 - sgn b * u2) / 2)) = u2
      rw [this, hs, one_mul]
  refine ⟨![y 0, y 1, R], ?_, ?_⟩
  · show 0 < R
    exact hRpos
  · funext a
    have hyv : yv ![y 0, y 1, R] = y := by
      funext j; fin_cases j <;> rfl
    simp only [Φ]
    show R * Pc b (yv ![y 0, y 1, R]) a = z a
    rw [hyv]
    have : Pc b y a = (![u0, u1, u2] : Fin 3 → ℝ) a := by
      have := congrArg (fun p : S2 => p.1 a) hpt
      exact this
    rw [this]
    fin_cases a
    · show R * (z 0 / R) = z 0
      field_simp
    · show R * (z 1 / R) = z 1
      field_simp
    · show R * (z 2 / R) = z 2
      field_simp

lemma axis_null : volume Axis = 0 := by
  have hne : (Submodule.span ℝ {(Pi.single 2 1 : Fin 3 → ℝ)}) ≠ ⊤ := by
    intro h
    have h1 : (![1, 0, 0] : Fin 3 → ℝ) ∈ Submodule.span ℝ {(Pi.single 2 1 : Fin 3 → ℝ)} := by
      rw [h]; exact Submodule.mem_top
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 h1
    have := congrFun hc 0
    simp at this
  have h0 := Measure.addHaar_submodule volume _ hne
  refine measure_mono_null ?_ h0
  intro z hz
  obtain ⟨h0, h1⟩ := hz
  refine Submodule.mem_span_singleton.2 ⟨z 2, ?_⟩
  funext a
  fin_cases a <;> simp [h0, h1]

end MarkovTriple.BGL.SphereN.Atlas
