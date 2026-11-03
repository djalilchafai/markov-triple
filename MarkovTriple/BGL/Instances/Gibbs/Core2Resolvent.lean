import Mathlib
import MarkovTriple.BGL.Instances.Gibbs.RegMain
import MarkovTriple.BGL.Instances.Lebesgue.Core2Cut

/-!
# Gibbs on `ℝ`: the resolvent solution `v - L v = a` (R17, Stream A)

Statements: `STATEMENTS_R17_Core2.md` (A0-A2).  For `a ∈ C_c^∞`, the Friedrichs resolvent `v = (1-L)⁻¹ [a]` has a `C^∞`
representative (the elliptic regularity of `RegSemigroup.lean`), solves `L v = v - a` classically (symmetric integration by
parts against test functions), and `v' ∈ L²(μ)` (Caccioppoli with the cut-offs `χ_n`).  With bounded `V', V'', V'''`
(`BddJet`), also `v'', v''' ∈ L²(μ)`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal
open MarkovTriple.Sanity.OU (Sm)
open MarkovTriple.Sanity.OU hiding A₀ γ φ
open MarkovTriple.BGL.Lebesgue (chiR Rn Rn_pos chiR_smooth chiR_cs chiR_eq_one_of iter_chiR iter_bound)

local notation "OA₀" => MarkovTriple.Sanity.OU.A₀

namespace MarkovTriple.BGL.Instances.Gibbs

/-- `μ`-null sets are Lebesgue-null for a Gibbs measure (`w > 0`). -/
lemma GibbsData.ae_vol_of_ae_mu (G : GibbsData) {P : ℝ → Prop} (h : ∀ᵐ x ∂G.μ, P x) :
    ∀ᵐ x ∂(volume : Measure ℝ), P x := by
  have : (volume : Measure ℝ) ≪ G.μ := by
    unfold GibbsData.μ
    exact withDensity_absolutelyContinuous'
      (ENNReal.measurable_ofReal.comp G.w_smooth.continuous.measurable).aemeasurable
      (Eventually.of_forall fun x => (ENNReal.ofReal_pos.2 (G.w_pos x)).ne')
  exact this.ae_le h

/-- uniform bound `|χ_n^{(j)}| ≤ K` for `j ≤ 4`, all `n`. -/
lemma chiR_iter_bound : ∃ K : ℝ, 1 ≤ K ∧ ∀ (j : ℕ), j ≤ 4 → ∀ n x,
    |deriv^[j] (chiR (Rn n)) x| ≤ K := by
  obtain ⟨C0, hC0, hb0⟩ := iter_bound 0
  obtain ⟨C1, hC1, hb1⟩ := iter_bound 1
  obtain ⟨C2, hC2, hb2⟩ := iter_bound 2
  obtain ⟨C3, hC3, hb3⟩ := iter_bound 3
  obtain ⟨C4, hC4, hb4⟩ := iter_bound 4
  refine ⟨C0 + C1 + C2 + C3 + C4 + 1, by linarith, fun j hj n x => ?_⟩
  have hRn : 1 ≤ Rn n := by unfold Rn; linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
  have key : ∀ (j : ℕ) (C : ℝ), (∀ y, |deriv^[j] MarkovTriple.BGL.Lebesgue.chi y| ≤ C) →
      |deriv^[j] (chiR (Rn n)) x| ≤ C := by
    intro j C hC
    rw [iter_chiR, abs_div, abs_of_pos (pow_pos (Rn_pos n) j)]
    have : 1 ≤ Rn n ^ j := one_le_pow₀ hRn
    calc |deriv^[j] MarkovTriple.BGL.Lebesgue.chi (x / Rn n)| / Rn n ^ j
        ≤ |deriv^[j] MarkovTriple.BGL.Lebesgue.chi (x / Rn n)| := div_le_self (abs_nonneg _) this
      _ ≤ C := hC _
  interval_cases j
  · have := key 0 C0 hb0; linarith
  · have := key 1 C1 hb1; linarith
  · have := key 2 C2 hb2; linarith
  · have := key 3 C3 hb3; linarith
  · have := key 4 C4 hb4; linarith

lemma chiR_nonneg' (R x : ℝ) : 0 ≤ chiR R x := MarkovTriple.BGL.Lebesgue.chi_nonneg _
lemma chiR_le_one' (R x : ℝ) : chiR R x ≤ 1 := MarkovTriple.BGL.Lebesgue.chi_le_one _

/-- `∀ x, eventually (in n) `χ_n = 1` and all derivatives vanish at `x`. -/
lemma chiR_eventually_one (x : ℝ) : ∀ᶠ n : ℕ in atTop, |x| ≤ Rn n := by
  filter_upwards [eventually_ge_atTop (⌈|x|⌉₊)] with n hn
  unfold Rn
  have := (Nat.le_ceil |x|).trans (by exact_mod_cast hn : (⌈|x|⌉₊ : ℝ) ≤ n)
  linarith

lemma chiR_iter_zero {n : ℕ} {x : ℝ} (hx : |x| < Rn n) (j : ℕ) :
    deriv^[j + 1] (chiR (Rn n)) x = 0 := by
  rw [iter_chiR]
  have : |x / Rn n| < 1 := by
    rw [abs_div, abs_of_pos (Rn_pos n), div_lt_one (Rn_pos n)]; exact hx
  simp [MarkovTriple.BGL.Lebesgue.iter_zero j this]

/-- `g` continuous with uniformly bounded cut-off norms is `L²` (Fatou). -/
lemma memLp_two_of_cutoff {μ : Measure ℝ} [IsFiniteMeasure μ] {g : ℝ → ℝ} (hg : Continuous g) {B : ℝ}
    (hB : ∀ n : ℕ, ∫ x, (chiR (Rn n) x * g x) ^ 2 ∂μ ≤ B) : MemLp g 2 μ := by
  rw [memLp_two_iff_integrable_sq hg.aestronglyMeasurable]
  refine ⟨(hg.pow 2).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun x => sq_nonneg _)]
  have hint : ∀ n : ℕ, Integrable (fun x => (chiR (Rn n) x * g x) ^ 2) μ := by
    intro n
    have hc : Continuous (fun x => chiR (Rn n) x * g x) := (chiR_smooth (Rn n)).continuous.mul hg
    have hs : HasCompactSupport (fun x => chiR (Rn n) x * g x) :=
      (chiR_cs (Rn_pos n).ne').mul_right
    have hs2 : HasCompactSupport (fun x => (chiR (Rn n) x * g x) ^ 2) :=
      hs.comp_left (g := fun y : ℝ => y ^ 2) (by simp)
    exact (hc.pow 2).integrable_of_hasCompactSupport hs2
  set F : ℕ → ℝ → ℝ≥0∞ := fun n x => ENNReal.ofReal ((chiR (Rn n) x * g x) ^ 2) with hF
  have hFm : ∀ n, Measurable (F n) := fun n =>
    ENNReal.measurable_ofReal.comp (((chiR_smooth (Rn n)).continuous.mul hg).pow 2).measurable
  have hlim : ∀ x, liminf (fun n => F n x) atTop = ENNReal.ofReal (g x ^ 2) := by
    intro x
    have : Tendsto (fun n => F n x) atTop (𝓝 (ENNReal.ofReal (g x ^ 2))) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [chiR_eventually_one x] with n hn
      simp only [hF, chiR_eq_one_of (Rn_pos n) hn, one_mul]
    exact this.liminf_eq
  have h1 := lintegral_liminf_le (μ := μ) (u := (atTop : Filter ℕ)) hFm
  simp only [hlim] at h1
  refine lt_of_le_of_lt h1 ?_
  have h2 : ∀ n, ∫⁻ x, F n x ∂μ ≤ ENNReal.ofReal B := fun n => by
    simp only [hF]
    rw [← ofReal_integral_eq_lintegral_ofReal (hint n) (Eventually.of_forall fun x => sq_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (hB n)
  have h3 : liminf (fun n : ℕ => ∫⁻ x, F n x ∂μ) atTop ≤ ENNReal.ofReal B :=
    liminf_le_of_frequently_le' (Frequently.of_forall h2)
  exact lt_of_le_of_lt h3 ENNReal.ofReal_lt_top

/-- the pointwise inequality of the Caccioppoli estimate. -/
lemma cacc_pointwise {p q s t a K Hx : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq : |q| ≤ K)
    (eq : (p * t) ^ 2 = Hx - p * p * s * (s - a) - 2 * p * q * s * t) :
    (p * t) ^ 2 ≤ Hx + (1 / 2 + 2 * K ^ 2) * s ^ 2 + 1 / 2 * a ^ 2 + 1 / 2 * (p * t) ^ 2 := by
  have hm0 : 0 ≤ p * p := mul_self_nonneg _
  have hm1 : p * p ≤ 1 := by nlinarith
  have e1 : -(p * p * s * (s - a)) ≤ a ^ 2 / 2 := by
    nlinarith [mul_nonneg hm0 (sq_nonneg (s - a)), mul_nonneg (sub_nonneg.2 hm1) (sq_nonneg a),
      mul_nonneg hm0 (sq_nonneg s)]
  have hq2 : q ^ 2 ≤ K ^ 2 := by nlinarith [abs_nonneg q, sq_abs q]
  have e2 : -(2 * p * q * s * t) ≤ 1 / 2 * (p * t) ^ 2 + 2 * K ^ 2 * s ^ 2 := by
    nlinarith [sq_nonneg (p * t + 2 * q * s), mul_le_mul_of_nonneg_right hq2 (sq_nonneg s)]
  have : 0 ≤ s ^ 2 := sq_nonneg _
  nlinarith

namespace GibbsData
variable (G : GibbsData)

/-- integration by parts `∫ g L f dμ = -∫ f' g' dμ` for smooth `f`, `g` with compactly supported integrands. -/
lemma ibp_gen {f g : ℝ → ℝ} (hf : Sm f) (hg : Sm g) (hc : HasCompactSupport (fun x => g x * deriv f x))
    (h1 : HasCompactSupport (fun x => g x * Lg G.V f x))
    (h2 : HasCompactSupport (fun x => deriv g x * deriv f x)) :
    ∫ x, g x * Lg G.V f x ∂G.μ = -∫ x, deriv f x * deriv g x ∂G.μ := by
  have hm := G.ibp_master hf hg hc
  have i1 : Integrable (fun x => G.w x * (g x * Lg G.V f x)) volume :=
    G.integrable_cs (hg.continuous.mul (sm_Lg G.smooth hf).continuous) h1
  have i2 : Integrable (fun x => G.w x * (deriv g x * deriv f x)) volume :=
    G.integrable_cs (hg.deriv'.continuous.mul hf.deriv'.continuous) h2
  simp only [mul_add] at hm
  rw [integral_add i1 i2] at hm
  rw [integral_μ, integral_μ]
  have : ∫ x, G.w x * (deriv f x * deriv g x) = ∫ x, G.w x * (deriv g x * deriv f x) :=
    integral_congr_ae (Eventually.of_forall fun x => by ring)
  rw [this]
  linarith

/-- **A1**: the resolvent solution of `v - L v = a` is smooth, `L²(μ)`, and solves the equation classically. -/
theorem exists_resolvent_smooth {a : ℝ → ℝ} (ha : a ∈ OA₀) :
    ∃ v : ℝ → ℝ, Sm v ∧ MemLp v 2 G.μ ∧ ∀ x, Lg G.V v x = v x - a x := by
  set c : Lp ℝ 2 G.gibbsDiff.μ := G.gibbsDiff.cls ⟨a, ha⟩ with hc
  have hca : (c : ℝ → ℝ) =ᵐ[G.μ] a := G.gibbsDiff.coeFn_cls ⟨a, ha⟩
  have hca' : (c : ℝ → ℝ) =ᵐ[volume] a := G.ae_vol_of_ae_mu hca
  have hmain : ∀ n : ℕ, ∃ X : ℝ → ℝ, ContDiff ℝ (n : WithTop ℕ∞) X ∧
      (G.Rres c : ℝ → ℝ) =ᵐ[volume] X := by
    intro n
    obtain ⟨X, hX, hae⟩ := G.resolvent_gain c n ⟨a, ha.1.of_le (by exact_mod_cast le_top), hca'⟩
    exact ⟨X, hX.of_le (by exact_mod_cast Nat.le_add_right n 2), hae⟩
  obtain ⟨X, hX, hae⟩ := smooth_rep_of_forall hmain
  have haeμ : (G.Rres c : ℝ → ℝ) =ᵐ[G.μ] X := G.ae_mu_of_ae_vol hae
  refine ⟨X, hX, (Lp.memLp (G.Rres c)).ae_eq haeμ, ?_⟩
  -- weak equation for `X`
  have hweak : ∀ φ ∈ OA₀, ∫ x, X x * Lg G.V φ x ∂G.μ = ∫ x, (X x - a x) * φ x ∂G.μ := by
    intro φ hφ
    have h := G.gibbsDiff.resolvent_weak c φ hφ
    have e1 : ∫ x, (G.Rres c : ℝ → ℝ) x * Lg G.V φ x ∂G.μ = ∫ x, X x * Lg G.V φ x ∂G.μ :=
      integral_congr_ae (by filter_upwards [haeμ] with x hx; rw [hx])
    have e2 : ∫ x, ((G.Rres c : ℝ → ℝ) x - (c : ℝ → ℝ) x) * φ x ∂G.μ =
        ∫ x, (X x - a x) * φ x ∂G.μ :=
      integral_congr_ae (by filter_upwards [haeμ, hca] with x h1 h2; rw [h1, h2])
    rw [← e1, ← e2]
    exact h
  -- classical equation
  have hzero : ∀ φ : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
      ∫ x, φ x • (Lg G.V X x - (X x - a x)) ∂G.μ = 0 := by
    intro φ hφ hφc
    have hφA : φ ∈ OA₀ := ⟨hφ, hφc⟩
    have hLφ : Lg G.V φ ∈ OA₀ := G.Lg_mem hφA
    have i_cs : ∀ h : ℝ → ℝ, Continuous h → HasCompactSupport h → Integrable h G.μ :=
      fun h hc hs => hc.integrable_of_hasCompactSupport hs
    have b1 := G.ibp_gen (f := X) (g := φ) hX hφ (hφc.mul_right) (hφc.mul_right)
      (hφc.deriv.mul_right)
    have b2 := G.ibp_gen (f := φ) (g := X) hφ hX (hφc.deriv.mul_left) (hLφ.2.mul_left)
      (hφc.deriv.mul_left)
    have iA : Integrable (fun x => φ x * Lg G.V X x) G.μ :=
      i_cs _ (hφ.continuous.mul (sm_Lg G.smooth hX).continuous) hφc.mul_right
    have iB : Integrable (fun x => (X x - a x) * φ x) G.μ :=
      i_cs _ ((hX.continuous.sub ha.1.continuous).mul hφ.continuous) hφc.mul_left
    have e3 : ∫ x, φ x • (Lg G.V X x - (X x - a x)) ∂G.μ =
        ∫ x, φ x * Lg G.V X x ∂G.μ - ∫ x, (X x - a x) * φ x ∂G.μ := by
      rw [← integral_sub iA iB]
      exact integral_congr_ae (Eventually.of_forall fun x => by simp only [smul_eq_mul]; ring)
    have e4 : ∫ x, deriv X x * deriv φ x ∂G.μ = ∫ x, deriv φ x * deriv X x ∂G.μ :=
      integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)
    have := hweak φ hφA
    rw [e3]
    linarith
  have hloc : LocallyIntegrable (fun x => Lg G.V X x - (X x - a x)) G.μ :=
    ((sm_Lg G.smooth hX).continuous.sub (hX.continuous.sub ha.1.continuous)).locallyIntegrable
  have hae := ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc hzero
  have hcont : Continuous (fun x => Lg G.V X x - (X x - a x)) :=
    (sm_Lg G.smooth hX).continuous.sub (hX.continuous.sub ha.1.continuous)
  have := (Continuous.ae_eq_iff_eq G.μ hcont (continuous_const : Continuous fun _ : ℝ => (0 : ℝ))).1 hae
  intro x
  have := congrFun this x
  linarith

/-- **A0** (bounded jets): `V'`, `V''`, `V'''` are bounded on `ℝ`. -/
def BddJet : Prop :=
  (∃ C : ℝ, ∀ x, |deriv G.V x| ≤ C) ∧ (∃ C : ℝ, ∀ x, |deriv (deriv G.V) x| ≤ C) ∧
    ∃ C : ℝ, ∀ x, |deriv (deriv (deriv G.V)) x| ≤ C

/-- Caccioppoli estimate for a fixed cut-off `ψ`. -/
theorem cacc_bound {v a ψ : ℝ → ℝ} {K : ℝ} (hv : Sm v) (ha : a ∈ OA₀) (hv2 : MemLp v 2 G.μ)
    (hL : ∀ x, Lg G.V v x = v x - a x) (hψ : Sm ψ) (hψc : HasCompactSupport ψ) (h0 : ∀ x, 0 ≤ ψ x)
    (h1 : ∀ x, ψ x ≤ 1) (hq : ∀ x, |deriv ψ x| ≤ K) :
    ∫ x, (ψ x * deriv v x) ^ 2 ∂G.μ ≤
      2 * ((1 / 2 + 2 * K ^ 2) * ∫ x, v x ^ 2 ∂G.μ + 1 / 2 * ∫ x, a x ^ 2 ∂G.μ) := by
  have hs2 : Integrable (fun x => v x ^ 2) G.μ := hv2.integrable_sq
  have ha2 : Integrable (fun x => a x ^ 2) G.μ := by
    have hc : Continuous (fun x => a x ^ 2) := ha.1.continuous.pow 2
    have hs : HasCompactSupport (fun x => a x ^ 2) := ha.2.comp_left (g := fun y : ℝ => y ^ 2) (by simp)
    exact hc.integrable_of_hasCompactSupport hs
  obtain ⟨c1, hc1⟩ : ∃ c1 : ℝ, c1 = 1 / 2 + 2 * K ^ 2 := ⟨_, rfl⟩
  have hg : Sm (fun x => ψ x * ψ x * v x) := (hψ.mul hψ).mul hv
  have hgc : HasCompactSupport (fun x => ψ x * ψ x * v x) := hψc.mul_right.mul_right
  have hdg : ∀ x, deriv (fun x => ψ x * ψ x * v x) x =
      (deriv ψ x * ψ x + ψ x * deriv ψ x) * v x + ψ x * ψ x * deriv v x := fun x =>
    (((hψ.hasDerivAt x).mul (hψ.hasDerivAt x)).mul (hv.hasDerivAt x)).deriv
  have hI := G.ibp_gen (f := v) (g := fun x => ψ x * ψ x * v x) hv hg hgc.mul_right hgc.mul_right
    (hgc.deriv.mul_right)
  have iA : Integrable (fun x => ψ x * ψ x * v x * Lg G.V v x) G.μ :=
    ((hg.continuous.mul (sm_Lg G.smooth hv).continuous).integrable_of_hasCompactSupport hgc.mul_right)
  have iB : Integrable (fun x => deriv v x * deriv (fun x => ψ x * ψ x * v x) x) G.μ :=
    ((hv.deriv'.continuous.mul hg.deriv'.continuous).integrable_of_hasCompactSupport hgc.deriv.mul_left)
  obtain ⟨H, hH⟩ : ∃ H : ℝ → ℝ, H = fun x => ψ x * ψ x * v x * Lg G.V v x +
      deriv v x * deriv (fun x => ψ x * ψ x * v x) x := ⟨_, rfl⟩
  have hzero : ∫ x, H x ∂G.μ = 0 := by
    rw [hH]
    simp only
    rw [integral_add iA iB]; linarith
  have iH : Integrable H G.μ := by rw [hH]; exact iA.add iB
  have ipt : Integrable (fun x => (ψ x * deriv v x) ^ 2) G.μ := by
    have hc : Continuous (fun x => ψ x * deriv v x) := hψ.continuous.mul hv.deriv'.continuous
    have hs : HasCompactSupport (fun x => ψ x * deriv v x) := hψc.mul_right
    have hs2 : HasCompactSupport (fun x => (ψ x * deriv v x) ^ 2) :=
      hs.comp_left (g := fun y : ℝ => y ^ 2) (by simp)
    exact (hc.pow 2).integrable_of_hasCompactSupport hs2
  obtain ⟨R, hR⟩ : ∃ R : ℝ → ℝ, R = fun x => H x + c1 * v x ^ 2 + 1 / 2 * a x ^ 2 +
      1 / 2 * (ψ x * deriv v x) ^ 2 := ⟨_, rfl⟩
  have hpt : ∀ x, (ψ x * deriv v x) ^ 2 ≤ R x := fun x => by
    have eq : (ψ x * deriv v x) ^ 2 = H x - ψ x * ψ x * v x * (v x - a x) -
        2 * ψ x * deriv ψ x * v x * deriv v x := by
      rw [hH]; simp only; rw [hdg x, hL x]; ring
    have := cacc_pointwise (h0 x) (h1 x) (hq x) eq
    rw [hR]; simp only; rw [hc1]; exact this
  have j1 : Integrable (fun x => H x + c1 * v x ^ 2) G.μ := iH.add (hs2.const_mul c1)
  have j2 : Integrable (fun x => H x + c1 * v x ^ 2 + 1 / 2 * a x ^ 2) G.μ :=
    j1.add (ha2.const_mul (1 / 2))
  have iR : Integrable R G.μ := by
    rw [hR]
    exact j2.add (ipt.const_mul (1 / 2))
  have hmono := integral_mono ipt iR hpt
  have hRint : ∫ x, R x ∂G.μ = 0 + c1 * ∫ x, v x ^ 2 ∂G.μ + 1 / 2 * ∫ x, a x ^ 2 ∂G.μ +
      1 / 2 * ∫ x, (ψ x * deriv v x) ^ 2 ∂G.μ := by
    rw [hR]
    simp only
    rw [integral_add j2 (ipt.const_mul (1 / 2)), integral_add j1 (ha2.const_mul (1 / 2)),
      integral_add iH (hs2.const_mul c1), integral_const_mul, integral_const_mul, integral_const_mul, hzero]
  rw [hRint] at hmono
  rw [hc1] at hmono
  linarith

/-- Caccioppoli: `v' ∈ L²(μ)` for `v ∈ L²(μ)` smooth with `L v = v - a ∈ L²(μ)`. -/
theorem memLp_deriv_resolvent {v a : ℝ → ℝ} (hv : Sm v) (ha : a ∈ OA₀) (hv2 : MemLp v 2 G.μ)
    (hL : ∀ x, Lg G.V v x = v x - a x) : MemLp (deriv v) 2 G.μ := by
  obtain ⟨K, hK1, hK⟩ := chiR_iter_bound
  refine memLp_two_of_cutoff (B := 2 * ((1 / 2 + 2 * K ^ 2) * ∫ x, v x ^ 2 ∂G.μ +
    1 / 2 * ∫ x, a x ^ 2 ∂G.μ)) hv.deriv'.continuous (fun n => ?_)
  exact G.cacc_bound hv ha hv2 hL (chiR_smooth _) (chiR_cs (Rn_pos n).ne') (chiR_nonneg' _)
    (chiR_le_one' _) (fun x => by simpa using hK 1 (by norm_num) n x)

/-- **A2**: under `BddJet`, `v', v'', v''' ∈ L²(μ)`; and `v'' = v - a + V' v'`, `v''' = v' - a' + V'' v' + V' v''`. -/
theorem resolvent_jet_L2 (hb : G.BddJet) {v a : ℝ → ℝ} (hv : Sm v) (ha : a ∈ OA₀) (hv2 : MemLp v 2 G.μ)
    (hL : ∀ x, Lg G.V v x = v x - a x) :
    MemLp (deriv v) 2 G.μ ∧ MemLp (deriv (deriv v)) 2 G.μ ∧ MemLp (deriv (deriv (deriv v))) 2 G.μ := by
  obtain ⟨⟨C1, hC1⟩, ⟨C2, hC2⟩, -⟩ := hb
  have h1 := G.memLp_deriv_resolvent hv ha hv2 hL
  have haL : MemLp a 2 G.μ := ha.1.continuous.memLp_of_hasCompactSupport ha.2
  have ha'L : MemLp (deriv a) 2 G.μ :=
    ha.1.deriv'.continuous.memLp_of_hasCompactSupport ha.2.deriv
  have hV1 : MemLp (fun x => deriv G.V x * deriv v x) 2 G.μ :=
    h1.of_le_mul (c := C1) (G.smooth.deriv'.continuous.mul hv.deriv'.continuous).aestronglyMeasurable
      (Eventually.of_forall fun x => by
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (hC1 x) (abs_nonneg _))
  have e2 : deriv (deriv v) = fun x => (v x - a x) + deriv G.V x * deriv v x := by
    funext x; have := hL x; unfold Lg at this; linarith
  have h2 : MemLp (deriv (deriv v)) 2 G.μ := by
    rw [e2]; exact (hv2.sub haL).add hV1
  have hV2 : MemLp (fun x => deriv (deriv G.V) x * deriv v x) 2 G.μ :=
    h1.of_le_mul (c := C2) (G.smooth.deriv'.deriv'.continuous.mul hv.deriv'.continuous).aestronglyMeasurable
      (Eventually.of_forall fun x => by
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (hC2 x) (abs_nonneg _))
  have hV1' : MemLp (fun x => deriv G.V x * deriv (deriv v) x) 2 G.μ :=
    h2.of_le_mul (c := C1) (G.smooth.deriv'.continuous.mul hv.deriv'.deriv'.continuous).aestronglyMeasurable
      (Eventually.of_forall fun x => by
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (hC1 x) (abs_nonneg _))
  have e3 : deriv (deriv (deriv v)) = fun x => deriv v x - deriv a x + deriv (deriv G.V) x * deriv v x +
      deriv G.V x * deriv (deriv v) x := by
    funext x
    have h3 : deriv (deriv (deriv v)) x = deriv (fun x => (v x - a x) + deriv G.V x * deriv v x) x :=
      congrArg (fun f => deriv f x) e2
    have := (((hv.hasDerivAt x).sub (ha.1.hasDerivAt x)).add
      ((G.smooth.deriv'.hasDerivAt x).mul (hv.deriv'.hasDerivAt x)))
    rw [h3]
    refine this.deriv.trans ?_
    ring
  refine ⟨h1, h2, ?_⟩
  rw [e3]
  exact ((h1.sub ha'L).add hV2).add hV1'

end GibbsData

end MarkovTriple.BGL.Instances.Gibbs
