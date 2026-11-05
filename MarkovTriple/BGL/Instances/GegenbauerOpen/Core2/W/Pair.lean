import Mathlib
import MarkovTriple.BGL.Instances.GegenbauerOpen.Core2.W.Series
import MarkovTriple.BGL.Instances.GegenbauerOpen.Core2.W.Reduce

/-!
# R31-W: the deficiency pair for `lam = 2` (calculus part)

`w = (1-x²)^(-3/2) A`, `h = α (1-x²)^(-1/2)`.  Everything stated with `Core2Q.gL 2` and `Core2Q.gρ 2`.
-/

open MeasureTheory Filter Topology Set
open MarkovTriple.BGL.Instances.GegenbauerOpen.R24
open MarkovTriple.BGL.Instances.GegenbauerOpen.Core2Q

namespace MarkovTriple.BGL.Instances.GegenbauerOpen.Core2W

lemma hasDerivAt_sp1 (r : ℝ) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun y : ℝ => -2 * r * y * (1 - y ^ 2) ^ (r - 1))
      (-2 * r * (1 - x ^ 2) ^ (r - 1) + (-2 * r * x) * (-2 * (r - 1) * x * (1 - x ^ 2) ^ (r - 1 - 1))) x := by
  have h1 : HasDerivAt (fun y : ℝ => -2 * r * y) (-2 * r) x := by
    simpa using (hasDerivAt_id x).const_mul (-2 * r)
  have := h1.mul (hasDerivAt_sp (r - 1) hx)
  convert this using 1

/-- `(1-x²)^r` with `s^(r-1) = s^r / s`. -/
lemma rpow_sub_one' {s : ℝ} (hs : 0 < s) (r : ℝ) : s ^ (r - 1) = s ^ r / s := by
  rw [Real.rpow_sub hs, Real.rpow_one]

/-- the key computation: `L_2 (s^r A) = s^r (...)` for `A = P cc`. -/
lemma gL_two_mul_sp (r : ℝ) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    gL 2 (fun y => (1 - y ^ 2) ^ r * P cc y) x =
      (1 - x ^ 2) ^ r * ((-2 * r + (4 * r * (r - 1) + 10 * r) * x ^ 2 / (1 - x ^ 2)) * P cc x +
        (-4 * r - 5) * x * P (D cc) x + (1 - x ^ 2) * P (D (D cc)) x) := by
  have hpos := one_sub_sq_pos' hx
  have hA : ∀ y ∈ Ioo (-1 : ℝ) 1, HasDerivAt (P cc) (P (D cc) y) y := fun y hy =>
    hasDerivAt_P cc 1 zero_le_one 0 abs_cc_le' (abs_lt_one_of_mem hy)
  have hA1 : ∀ y ∈ Ioo (-1 : ℝ) 1, HasDerivAt (P (D cc)) (P (D (D cc)) y) y := fun y hy =>
    hasDerivAt_P (D cc) 1 zero_le_one 1 abs_Dcc_le (abs_lt_one_of_mem hy)
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


/-- `L_2 (α s^r)`. -/
lemma gL_two_sp (α r : ℝ) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    gL 2 (fun y => α * (1 - y ^ 2) ^ r) x =
      α * ((1 - x ^ 2) ^ r * (-2 * r + (4 * r * (r - 1) + 10 * r) * x ^ 2 / (1 - x ^ 2))) := by
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

/-- the solution `w = s^(-3/2) A`. -/
noncomputable def wf (x : ℝ) : ℝ := (1 - x ^ 2) ^ (-(3 / 2) : ℝ) * P cc x

/-- `h = α s^(-1/2)`. -/
noncomputable def hf (α : ℝ) (x : ℝ) : ℝ := α * (1 - x ^ 2) ^ (-(1 / 2) : ℝ)

lemma wf_smooth : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) wf (Ioo (-1 : ℝ) 1) := by
  refine ContDiffOn.mul ?_ (contDiffOn_infty.2 fun n => contDiffOn_P n cc 1 0 zero_le_one abs_cc_le')
  refine ContDiffOn.rpow_const_of_ne ?_ fun x hx => (one_sub_sq_pos' hx).ne'
  exact (contDiff_const.sub (contDiff_id.pow 2)).contDiffOn

lemma hf_smooth (α : ℝ) : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (hf α) (Ioo (-1 : ℝ) 1) := by
  refine contDiffOn_const.mul ?_
  refine ContDiffOn.rpow_const_of_ne ?_ fun x hx => (one_sub_sq_pos' hx).ne'
  exact (contDiff_const.sub (contDiff_id.pow 2)).contDiffOn

lemma wf_L {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) : gL 2 wf x = wf x := by
  have h := gL_two_mul_sp (-(3 / 2)) hx
  have ode := ode_series_cc (abs_lt_one_of_mem hx)
  have hpos := one_sub_sq_pos' hx
  change gL 2 (fun y => (1 - y ^ 2) ^ (-(3 / 2) : ℝ) * P cc y) x = _
  rw [h]
  show _ = (1 - x ^ 2) ^ (-(3 / 2) : ℝ) * P cc x
  have e0 : (4 * -(3 / 2 : ℝ) * (-(3 / 2) - 1) + 10 * -(3 / 2)) = 0 := by norm_num
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
    gL 2 (hf α) x = α * ((1 - x ^ 2) ^ (-(1 / 2) : ℝ) * (3 - 2 / (1 - x ^ 2))) := by
  have h := gL_two_sp α (-(1 / 2)) hx
  have hpos := one_sub_sq_pos' hx
  change gL 2 (fun y => α * (1 - y ^ 2) ^ (-(1 / 2) : ℝ)) x = _
  rw [h]
  congr 2
  field_simp
  norm_num
  ring


lemma q_sq_rho {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    ((1 - x ^ 2) ^ (-(1 / 2) : ℝ)) ^ 2 * gρ 2 x ≤ 1 := by
  have hpos := one_sub_sq_pos' hx
  have hs1 : 1 - x ^ 2 ≤ 1 := by nlinarith [sq_nonneg x]
  have e : ((1 - x ^ 2) ^ (-(1 / 2) : ℝ)) ^ 2 * gρ 2 x = (1 - x ^ 2) ^ (1 / 2 : ℝ) := by
    simp only [gρ]
    rw [sq, ← Real.rpow_add hpos, ← Real.rpow_add hpos]
    norm_num
  rw [e]
  exact Real.rpow_le_one hpos.le hs1 (by norm_num)

lemma wf_eq {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    wf x = (1 - x ^ 2) ^ (-(1 / 2) : ℝ) / (1 - x ^ 2) * P cc x := by
  have hpos := one_sub_sq_pos' hx
  have : (-(3 / 2) : ℝ) = -(1 / 2) - 1 := by norm_num
  simp only [wf]
  rw [this, rpow_sub_one' hpos]

/-- the weighted bound for `g = w - L h`, with `h = hf (-Λ/2)`. -/
theorem g_bound {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    (wf x - gL 2 (hf (-Lam / 2)) x) ^ 2 * gρ 2 x ≤ (C1 + 3 * |Lam| / 2) ^ 2 := by
  have hpos := one_sub_sq_pos' hx
  have hg : wf x - gL 2 (hf (-Lam / 2)) x = (1 - x ^ 2) ^ (-(1 / 2) : ℝ) / (1 - x ^ 2) * (P cc x - Lam) +
      3 * Lam / 2 * (1 - x ^ 2) ^ (-(1 / 2) : ℝ) := by
    rw [wf_eq hx, hf_L _ hx]
    field_simp
    ring
  have hq0 : 0 < (1 - x ^ 2) ^ (-(1 / 2) : ℝ) := Real.rpow_pos_of_pos hpos _
  set s : ℝ := 1 - x ^ 2 with hs
  set q : ℝ := s ^ (-(1 / 2) : ℝ) with hq
  have hl := lipschitz (abs_lt_one_of_mem hx)
  have hl' : |P cc x - Lam| ≤ C1 * s := hl
  have hb : |wf x - gL 2 (hf (-Lam / 2)) x| ≤ (C1 + 3 * |Lam| / 2) * q := by
    rw [hg]
    calc |q / s * (P cc x - Lam) + 3 * Lam / 2 * q| ≤ |q / s * (P cc x - Lam)| + |3 * Lam / 2 * q| :=
          abs_add_le _ _
      _ ≤ q * C1 + 3 * |Lam| / 2 * q := by
          have h1 : |q / s * (P cc x - Lam)| ≤ q * C1 := by
            rw [abs_mul, abs_of_pos (div_pos hq0 hpos)]
            calc q / s * |P cc x - Lam| ≤ q / s * (C1 * s) :=
                  mul_le_mul_of_nonneg_left hl' (div_pos hq0 hpos).le
              _ = q * C1 := by field_simp
          have h2 : |3 * Lam / 2 * q| = 3 * |Lam| / 2 * q := by
            rw [abs_mul, abs_of_pos hq0, abs_div, abs_mul]
            norm_num
          linarith
      _ = _ := by ring
  have hρ : 0 ≤ gρ 2 x := Real.rpow_nonneg hpos.le _
  have hsq : (wf x - gL 2 (hf (-Lam / 2)) x) ^ 2 ≤ ((C1 + 3 * |Lam| / 2) * q) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hb 2
  calc (wf x - gL 2 (hf (-Lam / 2)) x) ^ 2 * gρ 2 x ≤ ((C1 + 3 * |Lam| / 2) * q) ^ 2 * gρ 2 x :=
        mul_le_mul_of_nonneg_right hsq hρ
    _ = (C1 + 3 * |Lam| / 2) ^ 2 * (q ^ 2 * gρ 2 x) := by ring
    _ ≤ (C1 + 3 * |Lam| / 2) ^ 2 * 1 := mul_le_mul_of_nonneg_left (q_sq_rho hx) (sq_nonneg _)
    _ = _ := mul_one _

theorem h_bound (α : ℝ) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) : (hf α x) ^ 2 * gρ 2 x ≤ α ^ 2 := by
  have hρ : 0 ≤ gρ 2 x := Real.rpow_nonneg (one_sub_sq_pos' hx).le _
  calc (hf α x) ^ 2 * gρ 2 x = α ^ 2 * (((1 - x ^ 2) ^ (-(1 / 2) : ℝ)) ^ 2 * gρ 2 x) := by
        simp only [hf]; ring
    _ ≤ α ^ 2 * 1 := mul_le_mul_of_nonneg_left (q_sq_rho hx) (sq_nonneg _)
    _ = _ := mul_one _

end MarkovTriple.BGL.Instances.GegenbauerOpen.Core2W
