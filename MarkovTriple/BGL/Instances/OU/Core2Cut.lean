import Mathlib
import MarkovTriple.BGL.Instances.OU.Core2Tail

/-!
# OU: cut-off approximation in the graph norm of `L²`
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal Real

namespace MarkovTriple.Sanity.OU

/-- pointwise expansion of `L²(u f) − L² f`. -/
lemma LoLo_mul {u f : ℝ → ℝ} (hu : Sm u) (hf : Sm f) (x : ℝ) :
    Lo (Lo (u * f)) x - Lo (Lo f) x =
      (u x - 1) * Lo (Lo f) x + 2 * (Lo u x * Lo f x) + 2 * (deriv u x * deriv (Lo f) x)
      + f x * Lo (Lo u) x + 2 * (deriv f x * deriv (Lo u) x) + 2 * (deriv u x * Lo (deriv f) x)
      + 2 * (Lo (deriv u) x * deriv f x) + 4 * (deriv (deriv u) x * deriv (deriv f) x) := by
  have hLu := sm_Lo hu
  have hLf := sm_Lo hf
  have hdu := hu.deriv'
  have hdf := hf.deriv'
  have e1 : Lo (u * f) = Lo u * f + (2 : ℝ) • (deriv u * deriv f) + u * Lo f := by
    funext y
    rw [Lo_mul hu hf y]
    simp only [Pi.add_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
  have hA : Sm (Lo u * f) := hLu.mul hf
  have hB : Sm (deriv u * deriv f) := hdu.mul hdf
  have hC : Sm (u * Lo f) := hu.mul hLf
  have hB2 : Sm ((2 : ℝ) • (deriv u * deriv f)) := hB.const_smul (2 : ℝ)
  have hAB : Sm (Lo u * f + (2 : ℝ) • (deriv u * deriv f)) := hA.add hB2
  rw [e1, Lo_add hAB hC, Lo_add hA hB2, Lo_smul 2 hB]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [Lo_mul hLu hf x, Lo_mul hdu hdf x, Lo_mul hu hLf x]
  ring

/-- **Cutoff approximation in the graph norm of `L²`**: `g_k = cut(c_k) · f ∈ 𝒜₀`, `g_k → f`, `L g_k → L f`,
`L² g_k → L² f` in `L²(γ)`. -/
theorem cutoff_approx2 {f : ℝ → ℝ} (hf : Sm f) (h0 : MemLp f 2 γ) (h1 : MemLp (deriv f) 2 γ)
    (h2 : MemLp (deriv (deriv f)) 2 γ) (h3 : MemLp (Lo f) 2 γ) (h4 : MemLp (deriv (Lo f)) 2 γ)
    (h5 : MemLp (Lo (deriv f)) 2 γ) (h6 : MemLp (Lo (Lo f)) 2 γ) :
    ∃ g : ℕ → ℝ → ℝ, (∀ k, g k ∈ A₀) ∧
      Tendsto (fun k => eLpNorm (g k - f) 2 γ) atTop (𝓝 0) ∧
      Tendsto (fun k => eLpNorm (Lo (g k) - Lo f) 2 γ) atTop (𝓝 0) ∧
      Tendsto (fun k => eLpNorm (Lo (Lo (g k)) - Lo (Lo f)) 2 γ) atTop (𝓝 0) := by
  set c : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1) with hc
  have hcpos : ∀ k, 0 < c k := fun k => by simp only [hc]; positivity
  have hcle : ∀ k, c k ≤ 1 := fun k => by
    simp only [hc]; rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
  have hinv : ∀ k, 1 / c k = (k : ℝ) + 1 := fun k => by simp [hc]
  have hvan : ∀ (k : ℕ) (x : ℝ), |x| < (k : ℝ) + 1 → |x| < 1 / c k := fun k x hx => by rw [hinv]; exact hx
  have hone : ∀ (k : ℕ) (x : ℝ), |x| < (k : ℝ) + 1 → cut (c k) x - 1 = 0 := fun k x hx => by
    rw [cut_one (hcpos k) (hvan k x hx).le]; ring
  have hcut1 : ∀ k x, |cut (c k) x - 1| ≤ 1 := fun k x => by
    rw [abs_le]; constructor <;> linarith [cut_nonneg (c k) x, cut_le_one (c k) x]
  obtain ⟨K1, hK1, b1⟩ := Tl_dcut.bound
  obtain ⟨K2, hK2, b2⟩ := Tl_dcut.D.bound
  obtain ⟨K3, hK3, b3⟩ := Tl_Lcut.bound
  obtain ⟨K4, hK4, b4⟩ := Tl_Lcut.D.bound
  obtain ⟨K5, hK5, b5⟩ := Tl_Lcut.Lop.bound
  obtain ⟨K6, hK6, b6⟩ := Tl_dcut.Lop.bound
  set K : ℝ := K1 + K2 + K3 + K4 + K5 + K6 with hK
  have hK0 : 0 ≤ K := by positivity
  have z1 := Tl_dcut.zero
  have z2 := Tl_dcut.D.zero
  have z3 := Tl_Lcut.zero
  have z4 := Tl_Lcut.D.zero
  have z5 := Tl_Lcut.Lop.zero
  have z6 := Tl_dcut.Lop.zero
  have B1 : ∀ k x, |deriv (cut (c k)) x| ≤ K := fun k x => by
    have := b1 (c k) (hcpos k) (hcle k) x; linarith
  have B2 : ∀ k x, |deriv (deriv (cut (c k))) x| ≤ K := fun k x => by
    have := b2 (c k) (hcpos k) (hcle k) x; linarith
  have B3 : ∀ k x, |Lo (cut (c k)) x| ≤ K := fun k x => by
    have := b3 (c k) (hcpos k) (hcle k) x; linarith
  have B4 : ∀ k x, |deriv (Lo (cut (c k))) x| ≤ K := fun k x => by
    have := b4 (c k) (hcpos k) (hcle k) x; linarith
  have B5 : ∀ k x, |Lo (Lo (cut (c k))) x| ≤ K := fun k x => by
    have := b5 (c k) (hcpos k) (hcle k) x; linarith
  have B6 : ∀ k x, |Lo (deriv (cut (c k))) x| ≤ K := fun k x => by
    have := b6 (c k) (hcpos k) (hcle k) x; linarith
  have Z1 : ∀ (k : ℕ) (x : ℝ), |x| < (k : ℝ) + 1 → deriv (cut (c k)) x = 0 := fun k x hx => z1 (c k) (hcpos k) x (hvan k x hx)
  have Z2 : ∀ (k : ℕ) (x : ℝ), |x| < (k : ℝ) + 1 → deriv (deriv (cut (c k))) x = 0 := fun k x hx => z2 (c k) (hcpos k) x (hvan k x hx)
  have Z3 : ∀ (k : ℕ) (x : ℝ), |x| < (k : ℝ) + 1 → Lo (cut (c k)) x = 0 := fun k x hx => z3 (c k) (hcpos k) x (hvan k x hx)
  have Z4 : ∀ (k : ℕ) (x : ℝ), |x| < (k : ℝ) + 1 → deriv (Lo (cut (c k))) x = 0 := fun k x hx => z4 (c k) (hcpos k) x (hvan k x hx)
  have Z5 : ∀ (k : ℕ) (x : ℝ), |x| < (k : ℝ) + 1 → Lo (Lo (cut (c k))) x = 0 := fun k x hx => z5 (c k) (hcpos k) x (hvan k x hx)
  have Z6 : ∀ (k : ℕ) (x : ℝ), |x| < (k : ℝ) + 1 → Lo (deriv (cut (c k))) x = 0 := fun k x hx => z6 (c k) (hcpos k) x (hvan k x hx)
  have hLf := sm_Lo hf
  refine ⟨fun k x => cut (c k) x * f x, fun k => ⟨(cut_sm _).mul hf, (cut_cs (hcpos k)).mul_right⟩, ?_, ?_, ?_⟩
  · refine tendsto_L2_dom h0.norm (fun k => ?_) (fun k x => ?_) (fun k x hx => ?_)
    · exact (((cut_sm _).mul hf).continuous.sub hf.continuous).aestronglyMeasurable
    · simp only [Pi.sub_apply, abs_norm]
      have : cut (c k) x * f x - f x = (cut (c k) x - 1) * f x := by ring
      rw [this, abs_mul]
      calc |cut (c k) x - 1| * |f x| ≤ 1 * |f x| := mul_le_mul_of_nonneg_right (hcut1 k x) (abs_nonneg _)
        _ = |f x| := one_mul _
    · simp only [Pi.sub_apply]
      have := hone k x hx
      rw [show cut (c k) x * f x - f x = (cut (c k) x - 1) * f x by ring, this]; ring
  · have hG : MemLp (fun x => ‖Lo f x‖ + 2 * K * ‖deriv f x‖ + K * ‖f x‖) 2 γ :=
      (h3.norm.add (h1.norm.const_mul (2 * K))).add (h0.norm.const_mul K)
    have hid : ∀ k x, Lo (fun x => cut (c k) x * f x) x - Lo f x =
        (cut (c k) x - 1) * Lo f x + 2 * (deriv (cut (c k)) x * deriv f x) + Lo (cut (c k)) x * f x := by
      intro k x
      have := Lo_mul (cut_sm (c k)) hf x
      rw [show (fun x => cut (c k) x * f x) = cut (c k) * f from rfl, this]; ring
    refine tendsto_L2_dom hG (fun k => ?_) (fun k x => ?_) (fun k x hx => ?_)
    · exact (sm_Lo ((cut_sm _).mul hf)).continuous.sub hLf.continuous |>.aestronglyMeasurable
    · simp only [Pi.sub_apply]
      rw [hid]
      have t1 : |(cut (c k) x - 1) * Lo f x| ≤ ‖Lo f x‖ := by
        rw [abs_mul, Real.norm_eq_abs]
        calc |cut (c k) x - 1| * |Lo f x| ≤ 1 * |Lo f x| := mul_le_mul_of_nonneg_right (hcut1 k x) (abs_nonneg _)
          _ = _ := one_mul _
      have t2 : |2 * (deriv (cut (c k)) x * deriv f x)| ≤ 2 * K * ‖deriv f x‖ := by
        rw [abs_mul, abs_mul, Real.norm_eq_abs]
        have := mul_le_mul_of_nonneg_right (B1 k x) (abs_nonneg (deriv f x))
        have h2' : |(2 : ℝ)| = 2 := by norm_num
        rw [h2']; nlinarith
      have t3 : |Lo (cut (c k)) x * f x| ≤ K * ‖f x‖ := by
        rw [abs_mul, Real.norm_eq_abs]; exact mul_le_mul_of_nonneg_right (B3 k x) (abs_nonneg _)
      have hnn : 0 ≤ ‖Lo f x‖ + 2 * K * ‖deriv f x‖ + K * ‖f x‖ := by positivity
      rw [abs_of_nonneg hnn]
      have a1 := abs_add_le ((cut (c k) x - 1) * Lo f x + 2 * (deriv (cut (c k)) x * deriv f x))
        (Lo (cut (c k)) x * f x)
      have a2 := abs_add_le ((cut (c k) x - 1) * Lo f x) (2 * (deriv (cut (c k)) x * deriv f x))
      linarith
    · simp only [Pi.sub_apply]
      rw [hid, hone k x hx, Z1 k x hx, Z3 k x hx]; ring
  · set G : ℝ → ℝ := fun x => (4 * K + 1) * (‖Lo (Lo f) x‖ + ‖Lo f x‖ + ‖deriv (Lo f) x‖ + ‖f x‖ +
      2 * ‖deriv f x‖ + ‖Lo (deriv f) x‖ + ‖deriv (deriv f) x‖) with hGdef
    have hG : MemLp G 2 γ := by
      refine MemLp.const_mul ?_ _
      exact ((((((h6.norm.add h3.norm).add h4.norm).add h0.norm).add (h1.norm.const_mul 2)).add
        h5.norm).add h2.norm)
    have hid : ∀ k x, Lo (Lo (fun x => cut (c k) x * f x)) x - Lo (Lo f) x =
        (cut (c k) x - 1) * Lo (Lo f) x + 2 * (Lo (cut (c k)) x * Lo f x)
        + 2 * (deriv (cut (c k)) x * deriv (Lo f) x)
        + f x * Lo (Lo (cut (c k))) x + 2 * (deriv f x * deriv (Lo (cut (c k))) x)
        + 2 * (deriv (cut (c k)) x * Lo (deriv f) x)
        + 2 * (Lo (deriv (cut (c k))) x * deriv f x)
        + 4 * (deriv (deriv (cut (c k))) x * deriv (deriv f) x) := fun k x =>
      LoLo_mul (cut_sm (c k)) hf x
    refine tendsto_L2_dom hG (fun k => ?_) (fun k x => ?_) (fun k x hx => ?_)
    · exact (sm_Lo (sm_Lo ((cut_sm _).mul hf))).continuous.sub (sm_Lo hLf).continuous |>.aestronglyMeasurable
    · simp only [Pi.sub_apply]
      rw [hid]
      have hGn : 0 ≤ G x := by simp only [hGdef]; positivity
      rw [abs_of_nonneg hGn]
      have mk : ∀ (a q m : ℝ), |a| ≤ K → 0 ≤ m → m ≤ 4 → |m * (a * q)| ≤ (4 * K + 1) * |q| := by
        intro a q m ha hm hm'
        rw [abs_mul, abs_mul, abs_of_nonneg hm]
        have : |a| * |q| ≤ K * |q| := mul_le_mul_of_nonneg_right ha (abs_nonneg _)
        have h4' : m * (|a| * |q|) ≤ 4 * (K * |q|) :=
          mul_le_mul hm' this (by positivity) (by norm_num)
        nlinarith [abs_nonneg q]
      have mk' : ∀ (a q : ℝ), |a| ≤ K → |q * a| ≤ (4 * K + 1) * |q| := by
        intro a q ha
        have := mk a q 1 ha zero_le_one (by norm_num)
        rw [one_mul, mul_comm a q] at this
        exact this
      have t0 : |(cut (c k) x - 1) * Lo (Lo f) x| ≤ (4 * K + 1) * |Lo (Lo f) x| := by
        rw [abs_mul]
        have := mul_le_mul_of_nonneg_right (hcut1 k x) (abs_nonneg (Lo (Lo f) x))
        nlinarith [abs_nonneg (Lo (Lo f) x)]
      have t1 := mk _ (Lo f x) 2 (B3 k x) (by norm_num) (by norm_num)
      have t2 := mk _ (deriv (Lo f) x) 2 (B1 k x) (by norm_num) (by norm_num)
      have t3 := mk' _ (f x) (B5 k x)
      have t4 : |2 * (deriv f x * deriv (Lo (cut (c k))) x)| ≤ (4 * K + 1) * |deriv f x| := by
        have := mk (deriv (Lo (cut (c k))) x) (deriv f x) 2 (B4 k x) (by norm_num) (by norm_num)
        rw [mul_comm (deriv f x)]; exact this
      have t5 := mk _ (Lo (deriv f) x) 2 (B1 k x) (by norm_num) (by norm_num)
      have t6 := mk _ (deriv f x) 2 (B6 k x) (by norm_num) (by norm_num)
      have t7 := mk _ (deriv (deriv f) x) 4 (B2 k x) (by norm_num) (by norm_num)
      have s1 := abs_add_le ((cut (c k) x - 1) * Lo (Lo f) x + 2 * (Lo (cut (c k)) x * Lo f x)
        + 2 * (deriv (cut (c k)) x * deriv (Lo f) x) + f x * Lo (Lo (cut (c k))) x
        + 2 * (deriv f x * deriv (Lo (cut (c k))) x) + 2 * (deriv (cut (c k)) x * Lo (deriv f) x)
        + 2 * (Lo (deriv (cut (c k))) x * deriv f x))
        (4 * (deriv (deriv (cut (c k))) x * deriv (deriv f) x))
      have s2 := abs_add_le ((cut (c k) x - 1) * Lo (Lo f) x + 2 * (Lo (cut (c k)) x * Lo f x)
        + 2 * (deriv (cut (c k)) x * deriv (Lo f) x) + f x * Lo (Lo (cut (c k))) x
        + 2 * (deriv f x * deriv (Lo (cut (c k))) x) + 2 * (deriv (cut (c k)) x * Lo (deriv f) x))
        (2 * (Lo (deriv (cut (c k))) x * deriv f x))
      have s3 := abs_add_le ((cut (c k) x - 1) * Lo (Lo f) x + 2 * (Lo (cut (c k)) x * Lo f x)
        + 2 * (deriv (cut (c k)) x * deriv (Lo f) x) + f x * Lo (Lo (cut (c k))) x
        + 2 * (deriv f x * deriv (Lo (cut (c k))) x))
        (2 * (deriv (cut (c k)) x * Lo (deriv f) x))
      have s4 := abs_add_le ((cut (c k) x - 1) * Lo (Lo f) x + 2 * (Lo (cut (c k)) x * Lo f x)
        + 2 * (deriv (cut (c k)) x * deriv (Lo f) x) + f x * Lo (Lo (cut (c k))) x)
        (2 * (deriv f x * deriv (Lo (cut (c k))) x))
      have s5 := abs_add_le ((cut (c k) x - 1) * Lo (Lo f) x + 2 * (Lo (cut (c k)) x * Lo f x)
        + 2 * (deriv (cut (c k)) x * deriv (Lo f) x)) (f x * Lo (Lo (cut (c k))) x)
      have s6 := abs_add_le ((cut (c k) x - 1) * Lo (Lo f) x + 2 * (Lo (cut (c k)) x * Lo f x))
        (2 * (deriv (cut (c k)) x * deriv (Lo f) x))
      have s7 := abs_add_le ((cut (c k) x - 1) * Lo (Lo f) x) (2 * (Lo (cut (c k)) x * Lo f x))
      simp only [hGdef, Real.norm_eq_abs]
      linarith
    · simp only [Pi.sub_apply]
      rw [hid, hone k x hx, Z1 k x hx, Z2 k x hx, Z3 k x hx, Z4 k x hx, Z5 k x hx, Z6 k x hx]; ring

end MarkovTriple.Sanity.OU
