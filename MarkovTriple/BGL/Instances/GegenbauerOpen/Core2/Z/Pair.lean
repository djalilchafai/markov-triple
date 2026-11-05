import Mathlib
import MarkovTriple.BGL.Instances.GegenbauerOpen.Core2.Z.Series
import MarkovTriple.BGL.Instances.GegenbauerOpen.Core2.W.Reduce

/-!
# R32-Z: the deficiency pair for `lam = 5/2` (calculus part)

`w = (1-x²)^(-2) A`, `h = α (1-x²)^(-1)`.  Everything stated with `Core2Q.gL (5/2)` and `Core2Q.gρ (5/2)`.
-/

open MeasureTheory Filter Topology Set
open MarkovTriple.BGL.Instances.GegenbauerOpen.R24
open MarkovTriple.BGL.Instances.GegenbauerOpen.Core2Q
open MarkovTriple.BGL.Instances.GegenbauerOpen.Core2W (one_sub_sq_pos' hasDerivAt_sp)

namespace MarkovTriple.BGL.Instances.GegenbauerOpen.Core2Z

lemma hasDerivAt_sp1 (r : ℝ) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun y : ℝ => -2 * r * y * (1 - y ^ 2) ^ (r - 1))
      (-2 * r * (1 - x ^ 2) ^ (r - 1) + (-2 * r * x) * (-2 * (r - 1) * x * (1 - x ^ 2) ^ (r - 1 - 1))) x := by
  have h1 : HasDerivAt (fun y : ℝ => -2 * r * y) (-2 * r) x := by
    simpa using (hasDerivAt_id x).const_mul (-2 * r)
  have := h1.mul (hasDerivAt_sp (r - 1) hx)
  convert this using 1

lemma rpow_sub_one' {s : ℝ} (hs : 0 < s) (r : ℝ) : s ^ (r - 1) = s ^ r / s := by
  rw [Real.rpow_sub hs, Real.rpow_one]

/-- the key computation: `L_{5/2} (s^r A) = s^r (...)` for `A = P cc`. -/
lemma gL_five_mul_sp (r : ℝ) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    gL (5 / 2) (fun y => (1 - y ^ 2) ^ r * P cc y) x =
      (1 - x ^ 2) ^ r * ((-2 * r + (4 * r * (r - 1) + 12 * r) * x ^ 2 / (1 - x ^ 2)) * P cc x +
        (-4 * r - 6) * x * P (D cc) x + (1 - x ^ 2) * P (D (D cc)) x) := by
  have hpos := one_sub_sq_pos' hx
  have hA : ∀ y ∈ Ioo (-1 : ℝ) 1, HasDerivAt (P cc) (P (D cc) y) y := fun y hy =>
    hasDerivAt_P cc 2 (by norm_num) 0 abs_cc_le' (abs_lt_one_of_mem hy)
  have hA1 : ∀ y ∈ Ioo (-1 : ℝ) 1, HasDerivAt (P (D cc)) (P (D (D cc)) y) y := fun y hy =>
    hasDerivAt_P (D cc) 2 (by norm_num) 1 abs_Dcc_le (abs_lt_one_of_mem hy)
  have hW : ∀ y ∈ Ioo (-1 : ℝ) 1, HasDerivAt (fun y => (1 - y ^ 2) ^ r * P cc y)
      ((-2 * r * y * (1 - y ^ 2) ^ (r - 1)) * P cc y + (1 - y ^ 2) ^ r * P (D cc) y) y := fun y hy =>
    (hasDerivAt_sp r hy).mul (hA y hy)
  have hev : deriv (fun y => (1 - y ^ 2) ^ r * P cc y) =ᶠ[𝓝 x]
      fun y => (-2 * r * y * (1 - y ^ 2) ^ (r - 1)) * P cc y + (1 - y ^ 2) ^ r * P (D cc) y := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy using (hW y hy).deriv
  have h2 : HasDerivAt (fun y => (-2 * r * y * (1 - y ^ 2) ^ (r - 1)) * P cc y + (1 - y ^ 2) ^ r * P (D cc) y)
      (((-2 * r * (1 - x ^ 2) ^ (r - 1) + (-2 * r * x) * (-2 * (r - 1) * x * (1 - x ^ 2) ^ (r - 1 - 1))) * P cc x
        + (-2 * r * x * (1 - x ^ 2) ^ (r - 1)) * P (D cc) x) +
       ((-2 * r * x * (1 - x ^ 2) ^ (r - 1)) * P (D cc) x + (1 - x ^ 2) ^ r * P (D (D cc)) x)) x :=
    (((hasDerivAt_sp1 r hx).mul (hA x hx)).add ((hasDerivAt_sp r hx).mul (hA1 x hx)))
  simp only [gL]
  rw [hev.deriv_eq, (hW x hx).deriv, h2.deriv]
  have e1 : (1 - x ^ 2) ^ (r - 1) = (1 - x ^ 2) ^ r / (1 - x ^ 2) := rpow_sub_one' hpos r
  have e2 : (1 - x ^ 2) ^ (r - 1 - 1) = (1 - x ^ 2) ^ r / (1 - x ^ 2) / (1 - x ^ 2) := by
    rw [rpow_sub_one' hpos (r - 1), e1]
  rw [e1, e2]
  field_simp
  ring

/-- `L_{5/2} (α s^r)`. -/
lemma gL_five_sp (α r : ℝ) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    gL (5 / 2) (fun y => α * (1 - y ^ 2) ^ r) x =
      α * ((1 - x ^ 2) ^ r * (-2 * r + (4 * r * (r - 1) + 12 * r) * x ^ 2 / (1 - x ^ 2))) := by
  have hpos := one_sub_sq_pos' hx
  have hW : ∀ y ∈ Ioo (-1 : ℝ) 1, HasDerivAt (fun y => α * (1 - y ^ 2) ^ r)
      (α * (-2 * r * y * (1 - y ^ 2) ^ (r - 1))) y := fun y hy =>
    (hasDerivAt_sp r hy).const_mul α
  have hev : deriv (fun y => α * (1 - y ^ 2) ^ r) =ᶠ[𝓝 x]
      fun y => α * (-2 * r * y * (1 - y ^ 2) ^ (r - 1)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy using (hW y hy).deriv
  have h2 := (hasDerivAt_sp1 r hx).const_mul α
  simp only [gL]
  rw [hev.deriv_eq, (hW x hx).deriv, h2.deriv]
  have e1 : (1 - x ^ 2) ^ (r - 1) = (1 - x ^ 2) ^ r / (1 - x ^ 2) := rpow_sub_one' hpos r
  have e2 : (1 - x ^ 2) ^ (r - 1 - 1) = (1 - x ^ 2) ^ r / (1 - x ^ 2) / (1 - x ^ 2) := by
    rw [rpow_sub_one' hpos (r - 1), e1]
  rw [e1, e2]
  field_simp
  ring

/-- the solution `w = s^(-2) A`. -/
noncomputable def wf (x : ℝ) : ℝ := (1 - x ^ 2) ^ (-2 : ℝ) * P cc x

/-- `h = α s^(-1)`. -/
noncomputable def hf (α : ℝ) (x : ℝ) : ℝ := α * (1 - x ^ 2) ^ (-1 : ℝ)

lemma wf_smooth : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) wf (Ioo (-1 : ℝ) 1) := by
  refine ContDiffOn.mul ?_ (contDiffOn_infty.2 fun n => contDiffOn_P n cc 2 0 (by norm_num) abs_cc_le')
  refine ContDiffOn.rpow_const_of_ne ?_ fun x hx => (one_sub_sq_pos' hx).ne'
  exact (contDiff_const.sub (contDiff_id.pow 2)).contDiffOn

lemma hf_smooth (α : ℝ) : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (hf α) (Ioo (-1 : ℝ) 1) := by
  refine contDiffOn_const.mul ?_
  refine ContDiffOn.rpow_const_of_ne ?_ fun x hx => (one_sub_sq_pos' hx).ne'
  exact (contDiff_const.sub (contDiff_id.pow 2)).contDiffOn

lemma wf_L {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) : gL (5 / 2) wf x = wf x := by
  have h := gL_five_mul_sp (-2) hx
  have ode := ode_series_cc (abs_lt_one_of_mem hx)
  have hpos := one_sub_sq_pos' hx
  change gL (5 / 2) (fun y => (1 - y ^ 2) ^ (-2 : ℝ) * P cc y) x = _
  rw [h]
  show _ = (1 - x ^ 2) ^ (-2 : ℝ) * P cc x
  have e0 : (4 * (-2 : ℝ) * (-2 - 1) + 12 * (-2)) = 0 := by norm_num
  rw [e0]
  congr 1
  linear_combination ode

lemma wf_zero : wf 0 = 1 := by
  have : P cc 0 = 1 := by
    simp only [P]
    rw [tsum_eq_single 0]
    · simp [cc_zero]
    · intro n hn; simp [hn]
  simp [wf, this]

lemma hf_L (α : ℝ) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    gL (5 / 2) (hf α) x = α * ((1 - x ^ 2) ^ (-1 : ℝ) * (2 - 4 * x ^ 2 / (1 - x ^ 2))) := by
  have h := gL_five_sp α (-1) hx
  change gL (5 / 2) (fun y => α * (1 - y ^ 2) ^ (-1 : ℝ)) x = _
  rw [h]
  congr 2
  norm_num
  ring

lemma gρ_five (x : ℝ) : gρ (5 / 2) x = (1 - x ^ 2) ^ 2 := by
  simp only [gρ]
  rw [show (5 / 2 - 1 / 2 : ℝ) = (2 : ℕ) by norm_num, Real.rpow_natCast]

/-- the weighted bound for `g = w - L h`, with `h = hf (-Λ/4)`. -/
theorem g_bound {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    (wf x - gL (5 / 2) (hf (-Lam / 4)) x) ^ 2 * gρ (5 / 2) x ≤ (C1 + 3 * |Lam| / 2) ^ 2 := by
  have hpos := one_sub_sq_pos' hx
  set s : ℝ := 1 - x ^ 2 with hs
  have hr1 : s ^ (-1 : ℝ) = s⁻¹ := Real.rpow_neg_one s
  have hr2 : s ^ (-2 : ℝ) = (s⁻¹) ^ 2 := by
    rw [show (-2 : ℝ) = ((-2 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
    simp
  have hx2 : x ^ 2 = 1 - s := by rw [hs]; ring
  have hg : wf x - gL (5 / 2) (hf (-Lam / 4)) x =
      (s⁻¹) ^ 2 * (P cc x - Lam) + 3 * Lam / 2 * s⁻¹ := by
    rw [hf_L _ hx]
    simp only [wf]
    rw [← hs, hr1, hr2, hx2]
    field_simp
    ring
  have hs0 : 0 < s⁻¹ := inv_pos.2 hpos
  have hl := lipschitz (abs_lt_one_of_mem hx)
  have hl' : |P cc x - Lam| ≤ C1 * s := hl
  have hb : |wf x - gL (5 / 2) (hf (-Lam / 4)) x| ≤ (C1 + 3 * |Lam| / 2) * s⁻¹ := by
    rw [hg]
    calc |(s⁻¹) ^ 2 * (P cc x - Lam) + 3 * Lam / 2 * s⁻¹|
        ≤ |(s⁻¹) ^ 2 * (P cc x - Lam)| + |3 * Lam / 2 * s⁻¹| := abs_add_le _ _
      _ ≤ s⁻¹ * C1 + 3 * |Lam| / 2 * s⁻¹ := by
          have h1 : |(s⁻¹) ^ 2 * (P cc x - Lam)| ≤ s⁻¹ * C1 := by
            rw [abs_mul, abs_of_pos (pow_pos hs0 2)]
            calc (s⁻¹) ^ 2 * |P cc x - Lam| ≤ (s⁻¹) ^ 2 * (C1 * s) :=
                  mul_le_mul_of_nonneg_left hl' (pow_pos hs0 2).le
              _ = s⁻¹ * C1 := by field_simp
          have h2 : |3 * Lam / 2 * s⁻¹| = 3 * |Lam| / 2 * s⁻¹ := by
            rw [abs_mul, abs_of_pos hs0, abs_div, abs_mul]
            norm_num
          linarith
      _ = _ := by ring
  have hρ : 0 ≤ gρ (5 / 2) x := by rw [gρ_five]; positivity
  have hsq : (wf x - gL (5 / 2) (hf (-Lam / 4)) x) ^ 2 ≤ ((C1 + 3 * |Lam| / 2) * s⁻¹) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hb 2
  have e : (s⁻¹) ^ 2 * gρ (5 / 2) x = 1 := by
    rw [gρ_five, ← hs]
    field_simp
  calc (wf x - gL (5 / 2) (hf (-Lam / 4)) x) ^ 2 * gρ (5 / 2) x
      ≤ ((C1 + 3 * |Lam| / 2) * s⁻¹) ^ 2 * gρ (5 / 2) x := mul_le_mul_of_nonneg_right hsq hρ
    _ = (C1 + 3 * |Lam| / 2) ^ 2 * ((s⁻¹) ^ 2 * gρ (5 / 2) x) := by ring
    _ = _ := by rw [e, mul_one]

theorem h_bound (α : ℝ) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) : (hf α x) ^ 2 * gρ (5 / 2) x ≤ α ^ 2 := by
  have hpos := one_sub_sq_pos' hx
  have e : (hf α x) ^ 2 * gρ (5 / 2) x = α ^ 2 := by
    simp only [hf]
    rw [gρ_five, Real.rpow_neg_one]
    field_simp
  exact e.le

end MarkovTriple.BGL.Instances.GegenbauerOpen.Core2Z
