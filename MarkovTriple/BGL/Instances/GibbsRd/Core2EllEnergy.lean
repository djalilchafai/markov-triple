import Mathlib
import MarkovTriple.BGL.Instances.GibbsRd.Core2EllResolvent

/-!
# `Core2` for `EllData d`: energy estimates for the resolvent solution (R19, Stream A6)

For `v` smooth, `v ∈ L²(μ)`, `L v = v - a`, `a ∈ C_c^∞`, and a cut-off family `χ` (`CutFamily`):

* `integrable_Γ_resolvent`: `Γ(v) ∈ L¹(μ)` (Caccioppoli, BGL Prop. 3.2.1 style);
* `integrable_G2'_resolvent`: `Γ₂(v) - ρΓ(v) ∈ L¹(μ)` under `Curv ρ` (cut-off Bochner: `∫ φ Γ₂(v) = ½∫Γ(v)Lφ - ∫φΓ(v,Lv)`).
-/

open MeasureTheory Filter Topology Set
open MarkovTriple.BGL (pderiv)

namespace MarkovTriple.BGL.Instances.GibbsRd

variable {d : ℕ}

/-- Fatou: a continuous `g ≥ 0` with uniformly bounded cut-off integrals is integrable. -/
lemma integrable_of_cut {μ : Measure (Rd d)} [IsFiniteMeasure μ] {φ : ℕ → Rd d → ℝ} {g : Rd d → ℝ}
    (hg : Continuous g) (hg0 : ∀ x, 0 ≤ g x) (hφc : ∀ n, Continuous (φ n)) (hφ0 : ∀ n x, 0 ≤ φ n x)
    (hcs : ∀ n, HasCompactSupport (φ n)) (hev : ∀ x, ∀ᶠ n in atTop, φ n x = 1) {B : ℝ}
    (hB : ∀ n, ∫ x, φ n x * g x ∂μ ≤ B) : Integrable g μ := by
  refine ⟨hg.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun x => hg0 x)]
  have hc : ∀ n, Continuous (fun x => φ n x * g x) := fun n => (hφc n).mul hg
  have hint : ∀ n, Integrable (fun x => φ n x * g x) μ := fun n =>
    (hc n).integrable_of_hasCompactSupport (hcs n).mul_right
  set F : ℕ → Rd d → ENNReal := fun n x => ENNReal.ofReal (φ n x * g x) with hF
  have hFm : ∀ n, Measurable (F n) := fun n => ENNReal.measurable_ofReal.comp (hc n).measurable
  have hlim : ∀ x, liminf (fun n => F n x) atTop = ENNReal.ofReal (g x) := by
    intro x
    have : Tendsto (fun n => F n x) atTop (𝓝 (ENNReal.ofReal (g x))) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev x] with n hn
      simp only [hF, hn, one_mul]
    exact this.liminf_eq
  have h1 := lintegral_liminf_le (μ := μ) (u := (atTop : Filter ℕ)) hFm
  simp only [hlim] at h1
  refine lt_of_le_of_lt h1 ?_
  have h2 : ∀ n, ∫⁻ x, F n x ∂μ ≤ ENNReal.ofReal B := fun n => by
    simp only [hF]
    rw [← ofReal_integral_eq_lintegral_ofReal (hint n)
      (Eventually.of_forall fun x => mul_nonneg (hφ0 n x) (hg0 x))]
    exact ENNReal.ofReal_le_ofReal (hB n)
  have h3 : liminf (fun n : ℕ => ∫⁻ x, F n x ∂μ) atTop ≤ ENNReal.ofReal B :=
    liminf_le_of_frequently_le' (Frequently.of_forall h2)
  exact lt_of_le_of_lt h3 ENNReal.ofReal_lt_top

namespace EllData
variable (E : EllData d)

/-- Leibniz rule for `Γ` in the first slot. -/
lemma Γ_leib {f g : Rd d → ℝ} (hf : Sm f) (hg : Sm g) (k : Rd d → ℝ) (x : Rd d) :
    E.Γ (f * g) k x = f x * E.Γ g k x + g x * E.Γ f k x := by
  unfold Γ
  have h : ∀ i, pderiv (f * g) i x = pderiv f i x * g x + f x * pderiv g i x := fun i =>
    pderiv_mul hf hg i x
  simp only [h, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

lemma sm_G2 {f g : Rd d → ℝ} (hf : Sm f) (hg : Sm g) : Sm (E.G2 f g) := by
  unfold G2
  exact (((E.sm_L (E.sm_Γ hf hg)).sub (E.sm_Γ (E.sm_L hf) hg)).sub (E.sm_Γ hf (E.sm_L hg))).div_const 2

lemma Γ_nonneg' (f : Rd d → ℝ) (x : Rd d) : 0 ≤ E.Γ f f x := E.Γ_nonneg f x

/-- the cut-off facts used below, for `φ = χ²`. -/
lemma Lφ_bound {χ : Rd d → ℝ} (hχ : Sm χ) {K : ℝ} (h0 : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1)
    (hΓ : ∀ x, E.Γ χ χ x ≤ K) (hL : ∀ x, |E.L χ x| ≤ K) (x : Rd d) :
    |E.L (χ * χ) x| ≤ 4 * K := by
  rw [E.L_mul hχ hχ x]
  have g0 := E.Γ_nonneg χ x
  have hk := hL x
  have hk0 : 0 ≤ K := (abs_nonneg _).trans hk
  have a1 : |χ x * E.L χ x| ≤ K := by
    rw [abs_mul, abs_of_nonneg (h0 x).1]
    exact (mul_le_of_le_one_left (abs_nonneg _) (h0 x).2).trans hk
  have := abs_le.1 a1
  have := hΓ x
  rw [abs_le]; constructor <;> nlinarith [abs_le.1 a1]

/-- **Caccioppoli** (BGL Prop. 3.2.1 argument): `∫ χ_n² Γ(v) dμ ≤ ½∫a² + 4K∫v²`. -/
theorem cacc_ell {χ : ℕ → Rd d → ℝ} (hχ : E.CutFamily χ) {v a : Rd d → ℝ} (hv : Sm v) (ha : a ∈ A₀ d)
    (hv2 : MemLp v 2 E.μ) (hL : ∀ x, E.L v x = v x - a x) :
    ∃ B : ℝ, ∀ n : ℕ, ∫ x, χ n x * χ n x * E.Γ v v x ∂E.μ ≤ B := by
  obtain ⟨K, hK⟩ := hχ.bound
  refine ⟨1 / 2 * ∫ x, a x ^ 2 ∂E.μ + 4 * K * ∫ x, v x ^ 2 ∂E.μ, fun n => ?_⟩
  set ψ : Rd d → ℝ := χ n with hψdef
  have hψ : Sm ψ := hχ.smooth n
  have hψc : HasCompactSupport ψ := hχ.cs n
  have hg : Sm (ψ * ψ * v) := (hψ.mul hψ).mul hv
  have hgc : HasCompactSupport (ψ * ψ * v) := hψc.mul_right.mul_right
  have hI := E.ibp_sm hv hg (Or.inl hgc)
  have int_cs : ∀ h : Rd d → ℝ, Continuous h → HasCompactSupport h → Integrable h E.μ :=
    fun h hc hs => hc.integrable_of_hasCompactSupport hs
  have iA : Integrable (fun x => (ψ * ψ * v) x * E.L v x) E.μ :=
    int_cs _ (hg.continuous.mul (E.sm_L hv).continuous) hgc.mul_right
  have iB : Integrable (fun x => E.Γ (ψ * ψ * v) v x) E.μ :=
    int_cs _ (E.sm_Γ hg hv).continuous (E.hcs_Γ_left hgc)
  have hzero : ∫ x, ((ψ * ψ * v) x * E.L v x + E.Γ (ψ * ψ * v) v x) ∂E.μ = 0 := by
    rw [integral_add iA iB]; linarith
  have iF : Integrable (fun x => (ψ * ψ * v) x * E.L v x + E.Γ (ψ * ψ * v) v x) E.μ := iA.add iB
  have iS : Integrable (fun x => ψ x * ψ x * E.Γ v v x) E.μ :=
    int_cs _ ((hψ.continuous.mul hψ.continuous).mul (E.sm_Γ hv hv).continuous)
      (hψc.mul_right.mul_right)
  have hv2i : Integrable (fun x => v x ^ 2) E.μ := hv2.integrable_sq
  have ha2i : Integrable (fun x => a x ^ 2) E.μ :=
    int_cs _ (ha.1.continuous.pow 2) (ha.2.comp_left (g := fun y : ℝ => y ^ 2) (by simp))
  have hpt : ∀ x, ψ x * ψ x * E.Γ v v x ≤
      2 * ((ψ * ψ * v) x * E.L v x + E.Γ (ψ * ψ * v) v x) + 1 / 2 * a x ^ 2 + 4 * K * v x ^ 2 := by
    intro x
    have e1 : E.Γ (ψ * ψ * v) v x = ψ x * ψ x * E.Γ v v x + v x * (2 * (ψ x * E.Γ ψ v x)) := by
      rw [E.Γ_leib (f := ψ * ψ) (g := v) (hψ.mul hψ) hv, E.Γ_leib (f := ψ) (g := ψ) hψ hψ]
      simp only [Pi.mul_apply]; ring
    have hq : E.Γ ψ v x ^ 2 ≤ K * E.Γ v v x := by
      refine (E.Γ_cs ψ v x).trans ?_
      have := (hK n x).1
      exact mul_le_mul_of_nonneg_right this (E.Γ_nonneg v x)
    have p0 := (hχ.mem n x).1
    have p1 := (hχ.mem n x).2
    have s0 := E.Γ_nonneg v x
    have hK0 : 0 ≤ K := le_trans (E.Γ_nonneg ψ x) (hK n x).1
    set s := E.Γ v v x
    set q := E.Γ ψ v x
    set V := v x
    set A := a x
    set p := ψ x
    have key : -(2 * p * V * q) ≤ 1 / 2 * (p * p * s) + 2 * K * V ^ 2 := by
      have hR : 0 ≤ 1 / 2 * (p * p * s) + 2 * K * V ^ 2 := by positivity
      have hsq : (-(2 * p * V * q)) ^ 2 ≤ (1 / 2 * (p * p * s) + 2 * K * V ^ 2) ^ 2 := by
        have h4 : (-(2 * p * V * q)) ^ 2 = 4 * p ^ 2 * V ^ 2 * q ^ 2 := by ring
        rw [h4]
        have : 4 * p ^ 2 * V ^ 2 * q ^ 2 ≤ 4 * p ^ 2 * V ^ 2 * (K * s) :=
          mul_le_mul_of_nonneg_left hq (by positivity)
        nlinarith [sq_nonneg (1 / 2 * (p * p * s) - 2 * K * V ^ 2)]
      exact (abs_le_of_sq_le_sq' hsq hR).2
    rw [e1, hL x]
    simp only [Pi.mul_apply]
    have hm1 : p * p ≤ 1 := by nlinarith
    have hm0 : 0 ≤ p * p := mul_self_nonneg _
    nlinarith [mul_nonneg hm0 (sq_nonneg (V - A / 2)), mul_nonneg (sub_nonneg.2 hm1) (sq_nonneg A)]
  have j1 : Integrable (fun x => 2 * ((ψ * ψ * v) x * E.L v x + E.Γ (ψ * ψ * v) v x) +
      1 / 2 * a x ^ 2) E.μ := (iF.const_mul 2).add (ha2i.const_mul (1 / 2))
  have iR : Integrable (fun x => 2 * ((ψ * ψ * v) x * E.L v x + E.Γ (ψ * ψ * v) v x) +
      1 / 2 * a x ^ 2 + 4 * K * v x ^ 2) E.μ := j1.add (hv2i.const_mul (4 * K))
  have hmono := integral_mono iS iR hpt
  rw [integral_add j1 (hv2i.const_mul (4 * K)),
    integral_add (iF.const_mul 2) (ha2i.const_mul (1 / 2)), integral_const_mul, integral_const_mul,
    integral_const_mul, hzero] at hmono
  linarith

/-- `Γ(v) ∈ L¹(μ)`. -/
theorem integrable_Γ_resolvent {χ : ℕ → Rd d → ℝ} (hχ : E.CutFamily χ) {v a : Rd d → ℝ} (hv : Sm v)
    (ha : a ∈ A₀ d) (hv2 : MemLp v 2 E.μ) (hL : ∀ x, E.L v x = v x - a x) :
    Integrable (E.Γ v v) E.μ := by
  obtain ⟨B, hB⟩ := E.cacc_ell hχ hv ha hv2 hL
  refine integrable_of_cut (φ := fun n x => χ n x * χ n x) (E.sm_Γ hv hv).continuous
    (E.Γ_nonneg v) (fun n => ((hχ.smooth n).continuous.mul (hχ.smooth n).continuous))
    (fun n x => mul_self_nonneg _) (fun n => (hχ.cs n).mul_right) (fun x => ?_) (B := B) hB
  filter_upwards [hχ.eventually_one x] with n hn
  have := hn.self_of_nhds
  simp [this]

/-- the polarised identity `Γ(v, Lv) = Γ(v) - Γ(v,a)` -/
lemma Γ_v_Lv {v a : Rd d → ℝ} (hv : Sm v) (ha : Sm a) (hL : ∀ x, E.L v x = v x - a x) (x : Rd d) :
    E.Γ v (E.L v) x = E.Γ v v x - E.Γ v a x := by
  have e : E.L v = fun y => v y + (-1 : ℝ) * a y := by funext y; rw [hL y]; ring
  rw [e]
  have := congrFun (E.Γ_lin_right hv ha (-1) v) x
  rw [this]; ring

/-- **cut-off Bochner**: `Γ₂(v) - ρΓ(v) ∈ L¹(μ)` (it is `≥ 0`). -/
theorem integrable_G2'_resolvent {ρ : ℝ} (hρ : E.Curv ρ) {χ : ℕ → Rd d → ℝ} (hχ : E.CutFamily χ)
    {v a : Rd d → ℝ} (hv : Sm v) (ha : a ∈ A₀ d) (hv2 : MemLp v 2 E.μ)
    (hL : ∀ x, E.L v x = v x - a x) : Integrable (fun x => E.G2' ρ v v x) E.μ := by
  obtain ⟨K, hK⟩ := hχ.bound
  have iΓv := E.integrable_Γ_resolvent hχ hv ha hv2 hL
  have iΓa : Integrable (E.Γ a a) E.μ :=
    (E.sm_Γ ha.1 ha.1).continuous.integrable_of_hasCompactSupport (E.hcs_Γ_left ha.2)
  have hLv : Sm (E.L v) := E.sm_L hv
  have int_cs : ∀ h : Rd d → ℝ, Continuous h → HasCompactSupport h → Integrable h E.μ :=
    fun h hc hs => hc.integrable_of_hasCompactSupport hs
  have hG2cont : Continuous (fun x => E.G2' ρ v v x) := by
    have : (fun x => E.G2' ρ v v x) = fun x => E.G2 v v x - ρ * E.Γ v v x := rfl
    rw [this]
    exact (E.sm_G2 hv hv).continuous.sub (continuous_const.mul (E.sm_Γ hv hv).continuous)
  refine integrable_of_cut (φ := fun n x => χ n x * χ n x) hG2cont
    (fun x => E.G2'_nonneg hρ hv x) (fun n => ((hχ.smooth n).continuous.mul (hχ.smooth n).continuous))
    (fun n x => mul_self_nonneg _) (fun n => (hχ.cs n).mul_right) (fun x => ?_)
    (B := 2 * K * ∫ x, E.Γ v v x ∂E.μ + 3 / 2 * ∫ x, E.Γ v v x ∂E.μ + 1 / 2 * ∫ x, E.Γ a a x ∂E.μ +
      |ρ| * ∫ x, E.Γ v v x ∂E.μ) ?_
  · filter_upwards [hχ.eventually_one x] with n hn
    have := hn.self_of_nhds
    simp [this]
  intro n
  set ψ : Rd d → ℝ := χ n with hψdef
  have hψ : Sm ψ := hχ.smooth n
  have hψc : HasCompactSupport ψ := hχ.cs n
  have hφ : Sm (ψ * ψ) := hψ.mul hψ
  have hφc : HasCompactSupport (ψ * ψ) := hψc.mul_right
  have hφ0 : ∀ x, 0 ≤ (ψ * ψ) x := fun x => mul_self_nonneg _
  have hφ1 : ∀ x, (ψ * ψ) x ≤ 1 := fun x => by
    have := (hχ.mem n x).1; have := (hχ.mem n x).2
    simp only [Pi.mul_apply]; nlinarith
  have hLφ : ∀ x, |E.L (ψ * ψ) x| ≤ 4 * K :=
    E.Lφ_bound hψ (hχ.mem n) (fun x => (hK n x).1) (fun x => (hK n x).2.1)
  have hK0 : 0 ≤ K := by
    have := (hK n 0).2.1; exact (abs_nonneg _).trans this
  -- integrals of the three pieces
  have iΓ_vv : Continuous (E.Γ v v) := (E.sm_Γ hv hv).continuous
  have iT1 : Integrable (fun x => (ψ * ψ) x * E.L (E.Γ v v) x) E.μ :=
    int_cs _ (hφ.continuous.mul (E.sm_L (E.sm_Γ hv hv)).continuous) hφc.mul_right
  have iT1' : Integrable (fun x => E.Γ v v x * E.L (ψ * ψ) x) E.μ :=
    int_cs _ ((E.sm_Γ hv hv).continuous.mul (E.sm_L hφ).continuous) ((E.hcs_L hφc).mul_left)
  have hswap : ∫ x, (ψ * ψ) x * E.L (E.Γ v v) x ∂E.μ = ∫ x, E.Γ v v x * E.L (ψ * ψ) x ∂E.μ := by
    have e1 := E.ibp_sm (E.sm_Γ hv hv) hφ (Or.inl hφc)
    have e2 := E.ibp_sm hφ (E.sm_Γ hv hv) (Or.inr hφc)
    rw [e1, e2, E.Γ_symm]
  have iT3 : Integrable (fun x => (ψ * ψ) x * E.Γ v (E.L v) x) E.μ :=
    int_cs _ (hφ.continuous.mul (E.sm_Γ hv hLv).continuous) (hφc.mul_right (f' := fun x => E.Γ v (E.L v) x))
  have iT4 : Integrable (fun x => (ψ * ψ) x * E.Γ v v x) E.μ :=
    int_cs _ (hφ.continuous.mul iΓ_vv) (hφc.mul_right (f' := fun x => E.Γ v v x))
  -- decomposition of the integral
  have hdec : ∫ x, (ψ * ψ) x * E.G2' ρ v v x ∂E.μ =
      1 / 2 * ∫ x, E.Γ v v x * E.L (ψ * ψ) x ∂E.μ - ∫ x, (ψ * ψ) x * E.Γ v (E.L v) x ∂E.μ -
        ρ * ∫ x, (ψ * ψ) x * E.Γ v v x ∂E.μ := by
    have pw : ∀ x, (ψ * ψ) x * E.G2' ρ v v x =
        1 / 2 * ((ψ * ψ) x * E.L (E.Γ v v) x) - (ψ * ψ) x * E.Γ v (E.L v) x -
          ρ * ((ψ * ψ) x * E.Γ v v x) := by
      intro x
      unfold G2' G2
      rw [E.Γ_symm_apply (E.L v) v x]
      ring
    have iA : Integrable (fun x => 1 / 2 * ((ψ * ψ) x * E.L (E.Γ v v) x) -
        (ψ * ψ) x * E.Γ v (E.L v) x) E.μ := (iT1.const_mul _).sub iT3
    have iB : Integrable (fun x => ρ * ((ψ * ψ) x * E.Γ v v x)) E.μ := iT4.const_mul ρ
    have iC : Integrable (fun x => 1 / 2 * ((ψ * ψ) x * E.L (E.Γ v v) x)) E.μ := iT1.const_mul _
    simp only [pw]
    rw [integral_sub iA iB, integral_sub iC iT3, integral_const_mul, integral_const_mul, hswap]
  rw [show (∫ x, χ n x * χ n x * E.G2' ρ v v x ∂E.μ) = ∫ x, (ψ * ψ) x * E.G2' ρ v v x ∂E.μ from rfl, hdec]
  -- bounds
  have b1 : ∫ x, E.Γ v v x * E.L (ψ * ψ) x ∂E.μ ≤ ∫ x, (4 * K) * E.Γ v v x ∂E.μ := by
    refine integral_mono iT1' (iΓv.const_mul _) fun x => ?_
    have := (le_abs_self _).trans (hLφ x)
    have h0 := E.Γ_nonneg v x
    nlinarith
  have b2 : -∫ x, (ψ * ψ) x * E.Γ v (E.L v) x ∂E.μ ≤
      ∫ x, (3 / 2 * E.Γ v v x + 1 / 2 * E.Γ a a x) ∂E.μ := by
    rw [← integral_neg]
    refine integral_mono iT3.neg ((iΓv.const_mul _).add (iΓa.const_mul _)) fun x => ?_
    have e := E.Γ_v_Lv hv ha.1 hL x
    have h0 := E.Γ_nonneg v x
    have h1 := E.Γ_nonneg a x
    have cs := E.Γ_cs v a x
    have hva : |E.Γ v a x| ≤ (E.Γ v v x + E.Γ a a x) / 2 := by
      rw [abs_le]
      have := E.Γ_quad (f := v) (g := a) hv ha.1 1 x
      have := E.Γ_quad (f := v) (g := a) hv ha.1 (-1) x
      have n1 := E.Γ_nonneg (fun y => v y + (1 : ℝ) * a y) x
      have n2 := E.Γ_nonneg (fun y => v y + (-1 : ℝ) * a y) x
      constructor <;> nlinarith
    show -((ψ * ψ) x * E.Γ v (E.L v) x) ≤ _
    rw [e]
    have p0 := hφ0 x
    have p1 := hφ1 x
    have h2 : -(E.Γ v v x - E.Γ v a x) ≤ 3 / 2 * E.Γ v v x + 1 / 2 * E.Γ a a x := by
      have := (abs_le.1 hva).2; have := (abs_le.1 hva).1; nlinarith
    have h3 : 0 ≤ 3 / 2 * E.Γ v v x + 1 / 2 * E.Γ a a x := by positivity
    have h4 : |E.Γ v v x - E.Γ v a x| ≤ 3 / 2 * E.Γ v v x + 1 / 2 * E.Γ a a x := by
      rw [abs_le]; constructor
      · nlinarith [(abs_le.1 hva).2, (abs_le.1 hva).1]
      · nlinarith [(abs_le.1 hva).2, (abs_le.1 hva).1]
    have h5 : |(ψ * ψ) x * (E.Γ v v x - E.Γ v a x)| ≤ 3 / 2 * E.Γ v v x + 1 / 2 * E.Γ a a x := by
      rw [abs_mul, abs_of_nonneg p0]
      exact (mul_le_of_le_one_left (abs_nonneg _) p1).trans h4
    exact (neg_le_abs _).trans h5
  have b3 : -(ρ * ∫ x, (ψ * ψ) x * E.Γ v v x ∂E.μ) ≤ |ρ| * ∫ x, E.Γ v v x ∂E.μ := by
    have h : ∫ x, (ψ * ψ) x * E.Γ v v x ∂E.μ ≤ ∫ x, E.Γ v v x ∂E.μ := by
      refine integral_mono iT4 iΓv fun x => ?_
      have := E.Γ_nonneg v x
      nlinarith [hφ0 x, hφ1 x]
    have h0 : 0 ≤ ∫ x, (ψ * ψ) x * E.Γ v v x ∂E.μ :=
      integral_nonneg fun x => mul_nonneg (hφ0 x) (E.Γ_nonneg v x)
    have hI0 : 0 ≤ ∫ x, E.Γ v v x ∂E.μ := integral_nonneg (E.Γ_nonneg v)
    calc -(ρ * ∫ x, (ψ * ψ) x * E.Γ v v x ∂E.μ) ≤ |ρ| * ∫ x, (ψ * ψ) x * E.Γ v v x ∂E.μ := by
          nlinarith [neg_abs_le ρ]
      _ ≤ |ρ| * ∫ x, E.Γ v v x ∂E.μ := mul_le_mul_of_nonneg_left h (abs_nonneg ρ)
  rw [integral_const_mul] at b1
  rw [integral_add (iΓv.const_mul _) (iΓa.const_mul _), integral_const_mul, integral_const_mul] at b2
  nlinarith

end EllData

end MarkovTriple.BGL.Instances.GibbsRd
