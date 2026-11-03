import Mathlib
import MarkovTriple.BGL.Instances.Gibbs.Core2Resolvent

/-!
# Gibbs on `ℝ`: weighted `L²` estimates without bounded `V'` (R18, Stream A2)

Statements: `STATEMENTS_R18_Core2.md` (B0-B3).  Two Caccioppoli/Bakry-Émery type estimates, both proved with the
cut-offs `χ_n` and the exact integration by parts `∫ (P' - V' P) dμ = 0` for `P = η² V' f²` (`P` smooth with compact
support; this is `ibp_master` with the test function `x ↦ x`):

* `memLp_of_BE` (uses only a lower bound `V'' ≥ -Cw (1 + |V'|)`, e.g. `V'' ≥ ρ`: the 1-D Bochner inequality `Γ₂ ≥ ρ Γ`):
  `f ∈ L²`, `f' - V' f ∈ L²` ⇒ `V' f ∈ L²`;
* `memLp_of_hardy` (uses `V'' ≤ V'²/4 + B`): `f, f' ∈ L²` ⇒ `V' f ∈ L²`.

With them, for the resolvent solution `v` of `v - L v = a` and `|V''|, |V'''| ≤ C (1 + |V'|)` (`GrowHess`; `V'` arbitrary, in
particular unbounded, which is forced when `V'' ≥ ρ > 0`), all the weighted jets needed by the cut-off commutators lie in
`L²(μ)` (`Core2WCut.lean`).
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal
open MarkovTriple.Sanity.OU (Sm)
open MarkovTriple.Sanity.OU hiding A₀ γ φ
open MarkovTriple.BGL.Lebesgue (chiR Rn Rn_pos chiR_smooth chiR_cs)

local notation "OA₀" => MarkovTriple.Sanity.OU.A₀

namespace MarkovTriple.BGL.Instances.Gibbs

/-- generic integral bound: `T ≤ c₁ A + c₂ B + s H` pointwise and `∫ H = 0` give `∫ T ≤ c₁ ∫ A + c₂ ∫ B`. -/
lemma int_bound_aux {μ : Measure ℝ} {T A B H : ℝ → ℝ} {c₁ c₂ s : ℝ} (iT : Integrable T μ)
    (iA : Integrable A μ) (iB : Integrable B μ) (iH : Integrable H μ) (hH : ∫ x, H x ∂μ = 0)
    (hpt : ∀ x, T x ≤ c₁ * A x + c₂ * B x + s * H x) :
    ∫ x, T x ∂μ ≤ c₁ * ∫ x, A x ∂μ + c₂ * ∫ x, B x ∂μ := by
  have iR : Integrable (fun x => c₁ * A x + c₂ * B x + s * H x) μ :=
    ((iA.const_mul c₁).add (iB.const_mul c₂)).add (iH.const_mul s)
  have h := integral_mono iT iR hpt
  have e1 : ∫ x, (c₁ * A x + c₂ * B x + s * H x) ∂μ =
      ∫ x, (c₁ * A x + c₂ * B x) ∂μ + ∫ x, s * H x ∂μ :=
    integral_add (f := fun x => c₁ * A x + c₂ * B x) (g := fun x => s * H x)
      ((iA.const_mul c₁).add (iB.const_mul c₂)) (iH.const_mul s)
  have e2 : ∫ x, (c₁ * A x + c₂ * B x) ∂μ = ∫ x, c₁ * A x ∂μ + ∫ x, c₂ * B x ∂μ :=
    integral_add (f := fun x => c₁ * A x) (g := fun x => c₂ * B x)
      (iA.const_mul c₁) (iB.const_mul c₂)
  rw [e1, e2, integral_const_mul, integral_const_mul, integral_const_mul, hH] at h
  linarith

/-- pointwise inequality of the Bakry-Émery estimate (lower bound `V'' ≥ -Cw (1 + |V'|)`). -/
lemma be_pointwise {η η' V1 V2 f f' q Cw K H : ℝ} (h0 : 0 ≤ η) (h1 : η ≤ 1) (hη' : |η'| ≤ K)
    (hCw : 0 ≤ Cw) (hV2 : -(Cw * (1 + |V1|)) ≤ V2) (hq : f' = V1 * f + q)
    (hH : H = η ^ 2 * V2 * f ^ 2 + 2 * η * η' * V1 * f ^ 2 + 2 * η ^ 2 * V1 * f * f' -
      η ^ 2 * V1 ^ 2 * f ^ 2) :
    (η * (V1 * f)) ^ 2 ≤ 8 / 3 * (Cw + 2 * Cw ^ 2 + 4 * K ^ 2) * f ^ 2 + 32 / 3 * q ^ 2 + 8 / 3 * H := by
  set t := η * (V1 * f) with ht
  have hη2 : η ^ 2 ≤ 1 := by nlinarith
  have hη2' : 0 ≤ η ^ 2 := sq_nonneg _
  have hK : η' ^ 2 ≤ K ^ 2 := by nlinarith [abs_nonneg η', sq_abs η']
  have e1 : H = η ^ 2 * V2 * f ^ 2 + 2 * η' * f * t + t ^ 2 + 2 * t * (η * q) := by
    rw [hH, hq, ht]; ring
  set w := η * |f| with hw
  have hw2 : w ^ 2 = η ^ 2 * f ^ 2 := by rw [hw, mul_pow, sq_abs]
  have hw2' : w ^ 2 ≤ f ^ 2 := by rw [hw2]; nlinarith [sq_nonneg f]
  have htw : (|V1| * w) ^ 2 = t ^ 2 := by
    rw [mul_pow, hw2, sq_abs, ht]; ring
  have a1 : -(η ^ 2 * V2 * f ^ 2) ≤ Cw * f ^ 2 + (t ^ 2 / 8 + 2 * Cw ^ 2 * f ^ 2) := by
    have h3 : -(η ^ 2 * V2 * f ^ 2) ≤ Cw * (1 + |V1|) * (η ^ 2 * f ^ 2) := by
      have := mul_le_mul_of_nonneg_right (neg_le_neg hV2) (mul_nonneg hη2' (sq_nonneg f))
      nlinarith [this]
    have h4 : Cw * (1 + |V1|) * (η ^ 2 * f ^ 2) = Cw * w ^ 2 + Cw * w * (|V1| * w) := by
      rw [← hw2]; ring
    have h5 : Cw * w * (|V1| * w) ≤ 2 * Cw ^ 2 * w ^ 2 + (|V1| * w) ^ 2 / 8 := by
      nlinarith [sq_nonneg (2 * Cw * w - (|V1| * w) / 2)]
    have h6 : Cw * w ^ 2 ≤ Cw * f ^ 2 := mul_le_mul_of_nonneg_left hw2' hCw
    have h7 : 2 * Cw ^ 2 * w ^ 2 ≤ 2 * Cw ^ 2 * f ^ 2 :=
      mul_le_mul_of_nonneg_left hw2' (by positivity)
    rw [htw] at h5
    linarith
  have a2 : -(2 * η' * f * t) ≤ t ^ 2 / 4 + 4 * K ^ 2 * f ^ 2 := by
    nlinarith [sq_nonneg (t / 2 + 2 * η' * f), mul_le_mul_of_nonneg_right hK (sq_nonneg f)]
  have a3 : -(2 * t * (η * q)) ≤ t ^ 2 / 4 + 4 * q ^ 2 := by
    nlinarith [sq_nonneg (t / 2 + 2 * η * q), mul_nonneg (sub_nonneg.2 hη2) (sq_nonneg q)]
  nlinarith

/-- pointwise inequality of the Hardy estimate (upper bound `V'' ≤ V'²/4 + B`). -/
lemma hardy_pointwise {η η' V1 V2 f f' B K H : ℝ} (h0 : 0 ≤ η) (h1 : η ≤ 1) (hη' : |η'| ≤ K)
    (hB : 0 ≤ B) (hV2 : V2 ≤ V1 ^ 2 / 4 + B)
    (hH : H = η ^ 2 * V2 * f ^ 2 + 2 * η * η' * V1 * f ^ 2 + 2 * η ^ 2 * V1 * f * f' -
      η ^ 2 * V1 ^ 2 * f ^ 2) :
    (η * (V1 * f)) ^ 2 ≤ 4 * (B + 4 * K ^ 2) * f ^ 2 + 16 * f' ^ 2 + (-4) * H := by
  set t := η * (V1 * f) with ht
  have hη2 : η ^ 2 ≤ 1 := by nlinarith
  have hη2' : 0 ≤ η ^ 2 := sq_nonneg _
  have hK : η' ^ 2 ≤ K ^ 2 := by nlinarith [abs_nonneg η', sq_abs η']
  have e1 : H = η ^ 2 * V2 * f ^ 2 + 2 * η' * f * t + 2 * t * (η * f') - t ^ 2 := by
    rw [hH, ht]; ring
  have a1 : η ^ 2 * V2 * f ^ 2 ≤ t ^ 2 / 4 + B * f ^ 2 := by
    have h3 : η ^ 2 * V2 * f ^ 2 ≤ η ^ 2 * (V1 ^ 2 / 4 + B) * f ^ 2 := by
      have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hV2 hη2') (sq_nonneg f)
      nlinarith [this]
    have h4 : η ^ 2 * (V1 ^ 2 / 4 + B) * f ^ 2 = t ^ 2 / 4 + B * (η ^ 2 * f ^ 2) := by
      rw [ht]; ring
    have h5 : B * (η ^ 2 * f ^ 2) ≤ B * f ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ hB
      nlinarith [sq_nonneg f]
    linarith
  have a2 : 2 * η' * f * t ≤ t ^ 2 / 4 + 4 * K ^ 2 * f ^ 2 := by
    nlinarith [sq_nonneg (t / 2 - 2 * η' * f), mul_le_mul_of_nonneg_right hK (sq_nonneg f)]
  have a3 : 2 * t * (η * f') ≤ t ^ 2 / 4 + 4 * f' ^ 2 := by
    nlinarith [sq_nonneg (t / 2 - 2 * η * f'), mul_nonneg (sub_nonneg.2 hη2) (sq_nonneg f')]
  nlinarith

namespace GibbsData
variable (G : GibbsData)

/-- the exact integration by parts: `∫ (P' - V' P) dμ = 0` for `P = η² V' f²`, with `H = P' - V' P` expanded. -/
lemma hardy_ibp {f η : ℝ → ℝ} (hf : Sm f) (hη : Sm η) (hc : HasCompactSupport η) :
    ∃ H : ℝ → ℝ, Integrable H G.μ ∧ ∫ x, H x ∂G.μ = 0 ∧ ∀ x, H x =
      η x ^ 2 * deriv (deriv G.V) x * f x ^ 2 + 2 * η x * deriv η x * deriv G.V x * f x ^ 2 +
        2 * η x ^ 2 * deriv G.V x * f x * deriv f x - η x ^ 2 * deriv G.V x ^ 2 * f x ^ 2 := by
  set P : ℝ → ℝ := fun x => (η x * η x) * deriv G.V x * (f x * f x) with hP
  have hPs : Sm P := (((hη.mul hη).mul G.smooth.deriv').mul (hf.mul hf))
  have hPc : HasCompactSupport P :=
    (((hc.mul_right).mul_right).mul_right)
  have hdP : ∀ x, deriv P x = (deriv η x * η x + η x * deriv η x) * deriv G.V x * (f x * f x) +
      (η x * η x) * deriv (deriv G.V) x * (f x * f x) +
      (η x * η x) * deriv G.V x * (deriv f x * f x + f x * deriv f x) := by
    intro x
    have h := ((((hη.hasDerivAt x).mul (hη.hasDerivAt x)).mul (G.smooth.deriv'.hasDerivAt x)).mul
      ((hf.hasDerivAt x).mul (hf.hasDerivAt x)))
    rw [show deriv P x = deriv (η * η * deriv G.V * (f * f)) x from rfl, h.deriv]
    simp only [Pi.mul_apply]
    ring
  have hid : Sm (fun x : ℝ => x) := contDiff_id
  have hm := G.ibp_master (f := fun x : ℝ => x) (g := P) hid hPs (by
    have : (fun x => P x * deriv (fun x : ℝ => x) x) = P := by funext x; simp
    rw [this]; exact hPc)
  set H : ℝ → ℝ := fun x => P x * Lg G.V (fun x : ℝ => x) x +
    deriv P x * deriv (fun x : ℝ => x) x with hHdef
  have hHs : Continuous H := by
    have hL : Continuous (Lg G.V (fun x : ℝ => x)) := (sm_Lg G.smooth hid).continuous
    exact (hPs.continuous.mul hL).add (hPs.deriv'.continuous.mul
      (hid.deriv'.continuous))
  have hHc : HasCompactSupport H := by
    have h1 : HasCompactSupport (fun x => P x * Lg G.V (fun x : ℝ => x) x) := hPc.mul_right
    have h2 : HasCompactSupport (fun x => deriv P x * deriv (fun x : ℝ => x) x) := by
      have : (fun x => deriv P x * deriv (fun x : ℝ => x) x) = deriv P := by funext x; simp
      rw [this]; exact hPc.deriv
    exact h1.add h2
  refine ⟨H, hHs.integrable_of_hasCompactSupport hHc, ?_, fun x => ?_⟩
  · rw [integral_μ]
    have : (fun x => G.w x * H x) = fun x => G.w x * (P x * Lg G.V (fun x : ℝ => x) x +
        deriv P x * deriv (fun x : ℝ => x) x) := rfl
    rw [this]; exact hm
  · have e1 : Lg G.V (fun x : ℝ => x) x = -deriv G.V x := by
      simp [Lg]
    have e2 : deriv (fun x : ℝ => x) x = 1 := by simp
    show P x * Lg G.V (fun x : ℝ => x) x + deriv P x * deriv (fun x : ℝ => x) x = _
    rw [e1, e2, hdP x, hP]
    simp only
    ring

/-- **(BE)** the Bakry-Émery weighted estimate: `f ∈ L²`, `f' - V' f ∈ L²`, `V'' ≥ ρ` ⇒ `V' f ∈ L²`. -/
theorem memLp_of_BE {f : ℝ → ℝ} {Cw : ℝ} (hCw : 0 ≤ Cw) (hf : Sm f) (h0 : MemLp f 2 G.μ)
    (hq : MemLp (fun x => deriv f x - deriv G.V x * f x) 2 G.μ)
    (hρ : ∀ x, -(Cw * (1 + |deriv G.V x|)) ≤ deriv (deriv G.V) x) :
    MemLp (fun x => deriv G.V x * f x) 2 G.μ := by
  obtain ⟨K, hK1, hK⟩ := chiR_iter_bound
  have hf2 : Integrable (fun x => f x ^ 2) G.μ := h0.integrable_sq
  have hq2 : Integrable (fun x => (deriv f x - deriv G.V x * f x) ^ 2) G.μ := hq.integrable_sq
  refine memLp_two_of_cutoff (B := 8 / 3 * (Cw + 2 * Cw ^ 2 + 4 * K ^ 2) * ∫ x, f x ^ 2 ∂G.μ +
    32 / 3 * ∫ x, (deriv f x - deriv G.V x * f x) ^ 2 ∂G.μ) (G.smooth.deriv'.continuous.mul hf.continuous)
    (fun n => ?_)
  obtain ⟨H, iH, hH0, hHx⟩ := G.hardy_ibp hf (chiR_smooth (Rn n)) (chiR_cs (Rn_pos n).ne')
  have iT : Integrable (fun x => (chiR (Rn n) x * (deriv G.V x * f x)) ^ 2) G.μ := by
    have hc : Continuous (fun x => chiR (Rn n) x * (deriv G.V x * f x)) :=
      (chiR_smooth (Rn n)).continuous.mul (G.smooth.deriv'.continuous.mul hf.continuous)
    have hs : HasCompactSupport (fun x => chiR (Rn n) x * (deriv G.V x * f x)) :=
      (chiR_cs (Rn_pos n).ne').mul_right
    have hs2 : HasCompactSupport (fun x => (chiR (Rn n) x * (deriv G.V x * f x)) ^ 2) :=
      hs.comp_left (g := fun y : ℝ => y ^ 2) (by simp)
    exact (hc.pow 2).integrable_of_hasCompactSupport hs2
  refine int_bound_aux iT hf2 hq2 iH hH0 (c₁ := 8 / 3 * (Cw + 2 * Cw ^ 2 + 4 * K ^ 2))
    (c₂ := 32 / 3) (s := 8 / 3) (fun x => ?_)
  exact be_pointwise (chiR_nonneg' _ _) (chiR_le_one' _ _)
    (by simpa using hK 1 (by norm_num) n x) hCw (hρ x) (q := deriv f x - deriv G.V x * f x)
    (by ring) (hHx x)

/-- **(Hardy)** `f, f' ∈ L²`, `V'' ≤ B` ⇒ `V' f ∈ L²`. -/
theorem memLp_of_hardy {f : ℝ → ℝ} {B : ℝ} (hB0 : 0 ≤ B) (hf : Sm f) (h0 : MemLp f 2 G.μ)
    (h1 : MemLp (deriv f) 2 G.μ) (hB : ∀ x, deriv (deriv G.V) x ≤ deriv G.V x ^ 2 / 4 + B) :
    MemLp (fun x => deriv G.V x * f x) 2 G.μ := by
  obtain ⟨K, hK1, hK⟩ := chiR_iter_bound
  have hf2 : Integrable (fun x => f x ^ 2) G.μ := h0.integrable_sq
  have hq2 : Integrable (fun x => (deriv f x) ^ 2) G.μ := h1.integrable_sq
  refine memLp_two_of_cutoff (B := 4 * (B + 4 * K ^ 2) * ∫ x, f x ^ 2 ∂G.μ +
    16 * ∫ x, (deriv f x) ^ 2 ∂G.μ) (G.smooth.deriv'.continuous.mul hf.continuous)
    (fun n => ?_)
  obtain ⟨H, iH, hH0, hHx⟩ := G.hardy_ibp hf (chiR_smooth (Rn n)) (chiR_cs (Rn_pos n).ne')
  have iT : Integrable (fun x => (chiR (Rn n) x * (deriv G.V x * f x)) ^ 2) G.μ := by
    have hc : Continuous (fun x => chiR (Rn n) x * (deriv G.V x * f x)) :=
      (chiR_smooth (Rn n)).continuous.mul (G.smooth.deriv'.continuous.mul hf.continuous)
    have hs : HasCompactSupport (fun x => chiR (Rn n) x * (deriv G.V x * f x)) :=
      (chiR_cs (Rn_pos n).ne').mul_right
    have hs2 : HasCompactSupport (fun x => (chiR (Rn n) x * (deriv G.V x * f x)) ^ 2) :=
      hs.comp_left (g := fun y : ℝ => y ^ 2) (by simp)
    exact (hc.pow 2).integrable_of_hasCompactSupport hs2
  refine int_bound_aux iT hf2 hq2 iH hH0 (c₁ := 4 * (B + 4 * K ^ 2)) (c₂ := 16) (s := -4)
    (fun x => ?_)
  exact hardy_pointwise (chiR_nonneg' _ _) (chiR_le_one' _ _)
    (by simpa using hK 1 (by norm_num) n x) hB0 (hB x) (hHx x)

/-- **B0**: bounded second and third derivative of the potential (`V'` is NOT assumed bounded). -/
def BddHess : Prop :=
  (∃ C : ℝ, ∀ x, |deriv (deriv G.V) x| ≤ C) ∧ ∃ C : ℝ, ∀ x, |deriv (deriv (deriv G.V)) x| ≤ C

/-- **B0'** (growth form, generalising B0): `|V''|, |V'''| ≤ C (1 + |V'|)`.  Contains `BddHess` (same constant), the
potentials `x²/2 + a cos x`, and quartic-type potentials (`x⁴`, `x⁴ + x²/2`: `V'' ~ x²`, `V''' ~ x` against `V' ~ x³`). -/
def GrowHess : Prop :=
  ∃ C : ℝ, ∀ x, |deriv (deriv G.V) x| ≤ C * (1 + |deriv G.V x|) ∧
    |deriv (deriv (deriv G.V)) x| ≤ C * (1 + |deriv G.V x|)

lemma BddHess.growHess (hb : G.BddHess) : G.GrowHess := by
  obtain ⟨⟨B2, h2⟩, ⟨B3, h3⟩⟩ := hb
  have hB2 : 0 ≤ B2 := (abs_nonneg _).trans (h2 0)
  have hB3 : 0 ≤ B3 := (abs_nonneg _).trans (h3 0)
  refine ⟨max B2 B3, fun x => ⟨?_, ?_⟩⟩
  · nlinarith [h2 x, le_max_left B2 B3, abs_nonneg (deriv G.V x), le_max_right B2 B3]
  · nlinarith [h3 x, le_max_right B2 B3, abs_nonneg (deriv G.V x), le_max_left B2 B3]

lemma BddJet.bddHess (hb : G.BddJet) : G.BddHess := ⟨hb.2.1, hb.2.2⟩

end GibbsData

end MarkovTriple.BGL.Instances.Gibbs
