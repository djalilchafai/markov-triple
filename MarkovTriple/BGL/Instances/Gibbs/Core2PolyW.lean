import Mathlib
import MarkovTriple.BGL.Instances.Gibbs.Core2WCut

/-!
# Gibbs on `ℝ`: weighted `L²` cascade for `Core2` beyond `GrowHess` (R19, Stream A4)

Statements: `STATEMENTS_R19_Core2.md` (D0-D2).  The two estimates of R18 (Bakry-Émery `memLp_of_BE`, Hardy `memLp_of_hardy`)
are generalised to a smooth weight `ψ` (test function `P = η² V' ψ² f²` in the exact integration by parts
`∫ (P' - V' P) dμ = 0`):

* `memLp_of_BE_w`: `ψ f, ψ (f' - V' f) ∈ L²` and `V''ψ² + 2V'ψψ' ≥ -Cw (1+|V'|) ψ²` ⇒ `V' ψ f ∈ L²`;
* `memLp_of_hardy_w`: `ψ f, ψ f' ∈ L²` and `V''ψ² + 2V'ψψ' ≤ (V'²/4 + B) ψ²` ⇒ `V' ψ f ∈ L²`.

With `ψ = V'^n` and the resolvent solution `v` (`v - L v = a ∈ C_c^∞`) one gets, by induction on `n`, `V'^n v, V'^n v' ∈ L²(μ)` for ALL
`n` from `V'' ≥ -Cw (1 + |V'|)` (the curvature bound `CD(ρ, ∞)`) and `V'' = o(V'²)` only (`resolvent_pow_L2`).
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal
open MarkovTriple.Sanity.OU (Sm)
open MarkovTriple.Sanity.OU hiding A₀ γ φ
open MarkovTriple.BGL.Lebesgue (chiR Rn Rn_pos chiR_smooth chiR_cs)

local notation "OA₀" => MarkovTriple.Sanity.OU.A₀

namespace MarkovTriple.BGL.Instances.Gibbs

/-- pointwise inequality of the weighted Bakry-Émery estimate (`S` stands for `(V''ψ² + 2V'ψψ') f²`, `a = ψ f`,
`d = ψ f'`, `q = ψ (f' - V' f)`). -/
lemma be_pointwise_w {η η' V1 S a d q Cw K H : ℝ} (h0 : 0 ≤ η) (h1 : η ≤ 1) (hη' : |η'| ≤ K)
    (hCw : 0 ≤ Cw) (hS : -(Cw * (1 + |V1|)) * a ^ 2 ≤ S) (hq : d = V1 * a + q)
    (hH : H = η ^ 2 * S + 2 * η * η' * V1 * a ^ 2 + 2 * η ^ 2 * V1 * a * d - η ^ 2 * V1 ^ 2 * a ^ 2) :
    (η * (V1 * a)) ^ 2 ≤ 8 / 3 * (Cw + 2 * Cw ^ 2 + 4 * K ^ 2) * a ^ 2 + 32 / 3 * q ^ 2 + 8 / 3 * H := by
  set t := η * (V1 * a) with ht
  have hη2 : η ^ 2 ≤ 1 := by nlinarith
  have hη2' : 0 ≤ η ^ 2 := sq_nonneg _
  have hK : η' ^ 2 ≤ K ^ 2 := by nlinarith [abs_nonneg η', sq_abs η']
  have e1 : H = η ^ 2 * S + 2 * η' * a * t + t ^ 2 + 2 * t * (η * q) := by
    rw [hH, hq, ht]; ring
  set w := η * |a| with hw
  have hw2 : w ^ 2 = η ^ 2 * a ^ 2 := by rw [hw, mul_pow, sq_abs]
  have hw2' : w ^ 2 ≤ a ^ 2 := by rw [hw2]; nlinarith [sq_nonneg a]
  have htw : (|V1| * w) ^ 2 = t ^ 2 := by
    rw [mul_pow, hw2, sq_abs, ht]; ring
  have a1 : -(η ^ 2 * S) ≤ Cw * a ^ 2 + (t ^ 2 / 8 + 2 * Cw ^ 2 * a ^ 2) := by
    have h3 : -(η ^ 2 * S) ≤ Cw * (1 + |V1|) * (η ^ 2 * a ^ 2) := by
      have := mul_le_mul_of_nonneg_left hS hη2'
      nlinarith [this]
    have h4 : Cw * (1 + |V1|) * (η ^ 2 * a ^ 2) = Cw * w ^ 2 + Cw * w * (|V1| * w) := by
      rw [← hw2]; ring
    have h5 : Cw * w * (|V1| * w) ≤ 2 * Cw ^ 2 * w ^ 2 + (|V1| * w) ^ 2 / 8 := by
      nlinarith [sq_nonneg (2 * Cw * w - (|V1| * w) / 2)]
    have h6 : Cw * w ^ 2 ≤ Cw * a ^ 2 := mul_le_mul_of_nonneg_left hw2' hCw
    have h7 : 2 * Cw ^ 2 * w ^ 2 ≤ 2 * Cw ^ 2 * a ^ 2 :=
      mul_le_mul_of_nonneg_left hw2' (by positivity)
    rw [htw] at h5
    linarith
  have a2 : -(2 * η' * a * t) ≤ t ^ 2 / 4 + 4 * K ^ 2 * a ^ 2 := by
    nlinarith [sq_nonneg (t / 2 + 2 * η' * a), mul_le_mul_of_nonneg_right hK (sq_nonneg a)]
  have a3 : -(2 * t * (η * q)) ≤ t ^ 2 / 4 + 4 * q ^ 2 := by
    nlinarith [sq_nonneg (t / 2 + 2 * η * q), mul_nonneg (sub_nonneg.2 hη2) (sq_nonneg q)]
  nlinarith

/-- pointwise inequality of the weighted Hardy estimate. -/
lemma hardy_pointwise_w {η η' V1 S a d B K H : ℝ} (h0 : 0 ≤ η) (h1 : η ≤ 1) (hη' : |η'| ≤ K)
    (hB : 0 ≤ B) (hS : S ≤ (V1 ^ 2 / 4 + B) * a ^ 2)
    (hH : H = η ^ 2 * S + 2 * η * η' * V1 * a ^ 2 + 2 * η ^ 2 * V1 * a * d - η ^ 2 * V1 ^ 2 * a ^ 2) :
    (η * (V1 * a)) ^ 2 ≤ 4 * (B + 4 * K ^ 2) * a ^ 2 + 16 * d ^ 2 + (-4) * H := by
  set t := η * (V1 * a) with ht
  have hη2 : η ^ 2 ≤ 1 := by nlinarith
  have hη2' : 0 ≤ η ^ 2 := sq_nonneg _
  have hK : η' ^ 2 ≤ K ^ 2 := by nlinarith [abs_nonneg η', sq_abs η']
  have e1 : H = η ^ 2 * S + 2 * η' * a * t + 2 * t * (η * d) - t ^ 2 := by
    rw [hH, ht]; ring
  have a1 : η ^ 2 * S ≤ t ^ 2 / 4 + B * a ^ 2 := by
    have h3 : η ^ 2 * S ≤ η ^ 2 * ((V1 ^ 2 / 4 + B) * a ^ 2) :=
      mul_le_mul_of_nonneg_left hS hη2'
    have h4 : η ^ 2 * ((V1 ^ 2 / 4 + B) * a ^ 2) = t ^ 2 / 4 + B * (η ^ 2 * a ^ 2) := by
      rw [ht]; ring
    have h5 : B * (η ^ 2 * a ^ 2) ≤ B * a ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ hB
      nlinarith [sq_nonneg a]
    linarith
  have a2 : 2 * η' * a * t ≤ t ^ 2 / 4 + 4 * K ^ 2 * a ^ 2 := by
    nlinarith [sq_nonneg (t / 2 - 2 * η' * a), mul_le_mul_of_nonneg_right hK (sq_nonneg a)]
  have a3 : 2 * t * (η * d) ≤ t ^ 2 / 4 + 4 * d ^ 2 := by
    nlinarith [sq_nonneg (t / 2 - 2 * η * d), mul_nonneg (sub_nonneg.2 hη2) (sq_nonneg d)]
  nlinarith

namespace GibbsData
variable (G : GibbsData)

/-- the exact integration by parts `∫ (P' - V' P) dμ = 0` for `P = η² V' ψ² f²`, with `H = P' - V' P` expanded. -/
lemma hardy_ibp_w {f ψ η : ℝ → ℝ} (hf : Sm f) (hψ : Sm ψ) (hη : Sm η) (hc : HasCompactSupport η) :
    ∃ H : ℝ → ℝ, Integrable H G.μ ∧ ∫ x, H x ∂G.μ = 0 ∧ ∀ x, H x =
      η x ^ 2 * (deriv (deriv G.V) x * ψ x ^ 2 + 2 * deriv G.V x * ψ x * deriv ψ x) * f x ^ 2 +
        2 * η x * deriv η x * deriv G.V x * ψ x ^ 2 * f x ^ 2 +
        2 * η x ^ 2 * deriv G.V x * ψ x ^ 2 * f x * deriv f x -
        η x ^ 2 * deriv G.V x ^ 2 * ψ x ^ 2 * f x ^ 2 := by
  set P : ℝ → ℝ := fun x => (η x * η x) * (deriv G.V x * (ψ x * ψ x)) * (f x * f x) with hP
  have hPs : Sm P := (((hη.mul hη).mul (G.smooth.deriv'.mul (hψ.mul hψ))).mul (hf.mul hf))
  have hPc : HasCompactSupport P :=
    (((hc.mul_right).mul_right).mul_right)
  have hdP : ∀ x, deriv P x =
      ((deriv η x * η x + η x * deriv η x) * (deriv G.V x * (ψ x * ψ x)) +
        (η x * η x) * (deriv (deriv G.V) x * (ψ x * ψ x) +
          deriv G.V x * (deriv ψ x * ψ x + ψ x * deriv ψ x))) * (f x * f x) +
      ((η x * η x) * (deriv G.V x * (ψ x * ψ x))) * (deriv f x * f x + f x * deriv f x) := by
    intro x
    have h := (((((hη.hasDerivAt x).mul (hη.hasDerivAt x)).mul
      ((G.smooth.deriv'.hasDerivAt x).mul ((hψ.hasDerivAt x).mul (hψ.hasDerivAt x)))).mul
      ((hf.hasDerivAt x).mul (hf.hasDerivAt x))))
    rw [show deriv P x = deriv (η * η * (deriv G.V * (ψ * ψ)) * (f * f)) x from rfl, h.deriv]
    simp only [Pi.mul_apply]
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

/-- **(BE-w)** weighted Bakry-Émery estimate. -/
theorem memLp_of_BE_w {f ψ : ℝ → ℝ} {Cw : ℝ} (hCw : 0 ≤ Cw) (hf : Sm f) (hψ : Sm ψ)
    (h0 : MemLp (fun x => ψ x * f x) 2 G.μ)
    (hq : MemLp (fun x => ψ x * (deriv f x - deriv G.V x * f x)) 2 G.μ)
    (hlow : ∀ x, -(Cw * (1 + |deriv G.V x|)) * ψ x ^ 2 ≤
      deriv (deriv G.V) x * ψ x ^ 2 + 2 * deriv G.V x * ψ x * deriv ψ x) :
    MemLp (fun x => deriv G.V x * (ψ x * f x)) 2 G.μ := by
  obtain ⟨K, hK1, hK⟩ := chiR_iter_bound
  have hf2 : Integrable (fun x => (ψ x * f x) ^ 2) G.μ := h0.integrable_sq
  have hq2 : Integrable (fun x => (ψ x * (deriv f x - deriv G.V x * f x)) ^ 2) G.μ := hq.integrable_sq
  refine memLp_two_of_cutoff (B := 8 / 3 * (Cw + 2 * Cw ^ 2 + 4 * K ^ 2) * ∫ x, (ψ x * f x) ^ 2 ∂G.μ +
    32 / 3 * ∫ x, (ψ x * (deriv f x - deriv G.V x * f x)) ^ 2 ∂G.μ)
    (G.smooth.deriv'.continuous.mul (hψ.continuous.mul hf.continuous)) (fun n => ?_)
  obtain ⟨H, iH, hH0, hHx⟩ := G.hardy_ibp_w hf hψ (chiR_smooth (Rn n)) (chiR_cs (Rn_pos n).ne')
  have iT : Integrable (fun x => (chiR (Rn n) x * (deriv G.V x * (ψ x * f x))) ^ 2) G.μ := by
    have hc : Continuous (fun x => chiR (Rn n) x * (deriv G.V x * (ψ x * f x))) :=
      (chiR_smooth (Rn n)).continuous.mul (G.smooth.deriv'.continuous.mul
        (hψ.continuous.mul hf.continuous))
    have hs : HasCompactSupport (fun x => chiR (Rn n) x * (deriv G.V x * (ψ x * f x))) :=
      (chiR_cs (Rn_pos n).ne').mul_right
    have hs2 : HasCompactSupport (fun x => (chiR (Rn n) x * (deriv G.V x * (ψ x * f x))) ^ 2) :=
      hs.comp_left (g := fun y : ℝ => y ^ 2) (by simp)
    exact (hc.pow 2).integrable_of_hasCompactSupport hs2
  refine int_bound_aux iT hf2 hq2 iH hH0 (c₁ := 8 / 3 * (Cw + 2 * Cw ^ 2 + 4 * K ^ 2))
    (c₂ := 32 / 3) (s := 8 / 3) (fun x => ?_)
  refine be_pointwise_w (chiR_nonneg' _ _) (chiR_le_one' _ _)
    (by simpa using hK 1 (by norm_num) n x) hCw ?_
    (d := ψ x * deriv f x) (q := ψ x * (deriv f x - deriv G.V x * f x)) (by ring) ?_
    (S := (deriv (deriv G.V) x * ψ x ^ 2 + 2 * deriv G.V x * ψ x * deriv ψ x) * f x ^ 2)
  · have := mul_le_mul_of_nonneg_right (hlow x) (sq_nonneg (f x))
    nlinarith [this]
  · rw [hHx x]; ring

/-- **(Hardy-w)** weighted Hardy estimate. -/
theorem memLp_of_hardy_w {f ψ : ℝ → ℝ} {B : ℝ} (hB0 : 0 ≤ B) (hf : Sm f) (hψ : Sm ψ)
    (h0 : MemLp (fun x => ψ x * f x) 2 G.μ) (h1 : MemLp (fun x => ψ x * deriv f x) 2 G.μ)
    (hup : ∀ x, deriv (deriv G.V) x * ψ x ^ 2 + 2 * deriv G.V x * ψ x * deriv ψ x ≤
      (deriv G.V x ^ 2 / 4 + B) * ψ x ^ 2) :
    MemLp (fun x => deriv G.V x * (ψ x * f x)) 2 G.μ := by
  obtain ⟨K, hK1, hK⟩ := chiR_iter_bound
  have hf2 : Integrable (fun x => (ψ x * f x) ^ 2) G.μ := h0.integrable_sq
  have hq2 : Integrable (fun x => (ψ x * deriv f x) ^ 2) G.μ := h1.integrable_sq
  refine memLp_two_of_cutoff (B := 4 * (B + 4 * K ^ 2) * ∫ x, (ψ x * f x) ^ 2 ∂G.μ +
    16 * ∫ x, (ψ x * deriv f x) ^ 2 ∂G.μ)
    (G.smooth.deriv'.continuous.mul (hψ.continuous.mul hf.continuous)) (fun n => ?_)
  obtain ⟨H, iH, hH0, hHx⟩ := G.hardy_ibp_w hf hψ (chiR_smooth (Rn n)) (chiR_cs (Rn_pos n).ne')
  have iT : Integrable (fun x => (chiR (Rn n) x * (deriv G.V x * (ψ x * f x))) ^ 2) G.μ := by
    have hc : Continuous (fun x => chiR (Rn n) x * (deriv G.V x * (ψ x * f x))) :=
      (chiR_smooth (Rn n)).continuous.mul (G.smooth.deriv'.continuous.mul
        (hψ.continuous.mul hf.continuous))
    have hs : HasCompactSupport (fun x => chiR (Rn n) x * (deriv G.V x * (ψ x * f x))) :=
      (chiR_cs (Rn_pos n).ne').mul_right
    have hs2 : HasCompactSupport (fun x => (chiR (Rn n) x * (deriv G.V x * (ψ x * f x))) ^ 2) :=
      hs.comp_left (g := fun y : ℝ => y ^ 2) (by simp)
    exact (hc.pow 2).integrable_of_hasCompactSupport hs2
  refine int_bound_aux iT hf2 hq2 iH hH0 (c₁ := 4 * (B + 4 * K ^ 2)) (c₂ := 16) (s := -4)
    (fun x => ?_)
  refine hardy_pointwise_w (chiR_nonneg' _ _) (chiR_le_one' _ _)
    (by simpa using hK 1 (by norm_num) n x) hB0 ?_ (d := ψ x * deriv f x) ?_
    (S := (deriv (deriv G.V) x * ψ x ^ 2 + 2 * deriv G.V x * ψ x * deriv ψ x) * f x ^ 2)
  · have := mul_le_mul_of_nonneg_right (hup x) (sq_nonneg (f x))
    nlinarith [this]
  · rw [hHx x]; ring

/-- **D0** the hypothesis of Round 19: curvature lower bound (`V'' ≥ -Cw (1+|V'|)`, implied by `CD(ρ,∞)`), `V'' = o(V'²)`, and
polynomial domination of `V'''` by `V'`. -/
def PolyHess : Prop :=
  (∃ Cw : ℝ, 0 ≤ Cw ∧ ∀ x, -(Cw * (1 + |deriv G.V x|)) ≤ deriv (deriv G.V) x) ∧
  (∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ x, deriv (deriv G.V) x ≤ ε * deriv G.V x ^ 2 + B) ∧
  (∃ C : ℝ, ∃ N : ℕ, ∀ x, |deriv (deriv (deriv G.V)) x| ≤ C * (1 + |deriv G.V x| ^ N))

lemma GrowHess.polyHess (hb : G.GrowHess) : G.PolyHess := by
  obtain ⟨C, hC⟩ := hb
  have hC0 : 0 ≤ C := by
    have h := (abs_nonneg _).trans (hC 0).1
    have hp : 0 < 1 + |deriv G.V 0| := by positivity
    exact nonneg_of_mul_nonneg_left h hp
  refine ⟨⟨C, hC0, fun x => (abs_le.1 (hC x).1).1⟩, fun ε hε => ?_, ⟨C, 1, fun x => ?_⟩⟩
  · set k : ℝ := C ^ 2 / ε with hk
    have hεk : ε * k = C ^ 2 := by rw [hk]; field_simp
    have hk0 : 0 ≤ k := by positivity
    refine ⟨C + k, by positivity, fun x => ?_⟩
    have h := (abs_le.1 (hC x).1).2
    have hs := sq_abs (deriv G.V x)
    nlinarith [sq_nonneg (ε * |deriv G.V x| - C), abs_nonneg (deriv G.V x), mul_pos hε hε]
  · simpa using (hC x).2

/-- `V'^n` has the derivative `n V'^{n-1} V''`. -/
lemma deriv_pow_V (n : ℕ) (x : ℝ) :
    deriv (fun y => deriv G.V y ^ n) x = n * deriv G.V x ^ (n - 1) * deriv (deriv G.V) x :=
  ((G.smooth.deriv'.hasDerivAt x).pow n).deriv

lemma key_pow (V1 V2 : ℝ) (n : ℕ) :
    V2 * (V1 ^ n) ^ 2 + 2 * V1 * V1 ^ n * (n * V1 ^ (n - 1) * V2) = (2 * n + 1) * V2 * (V1 ^ n) ^ 2 := by
  rcases n with _ | n
  · simp
  · simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, pow_succ]
    ring

/-- `|c g| ≤ C (1 + |V'|^N) |g|` and `g, V'^N g ∈ L²` ⇒ `c g ∈ L²`. -/
lemma memLp_mul_poly {c g : ℝ → ℝ} {C : ℝ} {N : ℕ} (hc : Continuous c) (hC : 0 ≤ C)
    (hb : ∀ x, |c x| ≤ C * (1 + |deriv G.V x| ^ N)) (hg : MemLp g 2 G.μ)
    (hVg : MemLp (fun x => deriv G.V x ^ N * g x) 2 G.μ) (hgm : AEStronglyMeasurable g G.μ) :
    MemLp (fun x => c x * g x) 2 G.μ := by
  have hdom : MemLp (fun x => C * (‖g x‖ + ‖deriv G.V x ^ N * g x‖)) 2 G.μ :=
    (hg.norm.add hVg.norm).const_mul C
  refine hdom.mono (hc.aestronglyMeasurable.mul hgm) (Eventually.of_forall fun x => ?_)
  simp only [Real.norm_eq_abs, abs_mul, abs_pow]
  have h0 : 0 ≤ C * (|g x| + |deriv G.V x| ^ N * |g x|) := by positivity
  have h1 : |c x| * |g x| ≤ C * (1 + |deriv G.V x| ^ N) * |g x| :=
    mul_le_mul_of_nonneg_right (hb x) (abs_nonneg _)
  rw [abs_of_nonneg hC, abs_of_nonneg (by positivity : 0 ≤ |g x| + |deriv G.V x| ^ N * |g x|)]
  nlinarith [h1]

/-- `|V''| ≤ D (1 + |V'|²)` from the lower bound and `V'' ≤ V'² + B`. -/
lemma abs_V2_le (hlow : ∃ Cw : ℝ, 0 ≤ Cw ∧ ∀ x, -(Cw * (1 + |deriv G.V x|)) ≤ deriv (deriv G.V) x)
    (hsub : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ x, deriv (deriv G.V) x ≤ ε * deriv G.V x ^ 2 + B) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ x, |deriv (deriv G.V) x| ≤ D * (1 + |deriv G.V x| ^ 2) := by
  obtain ⟨Cw, hCw, hl⟩ := hlow
  obtain ⟨B, hB, hu⟩ := hsub 1 one_pos
  refine ⟨2 * Cw + 1 + B, by positivity, fun x => ?_⟩
  have hs := sq_abs (deriv G.V x)
  have ha := abs_nonneg (deriv G.V x)
  have h1 := hl x
  have h2 := hu x
  rw [abs_le]
  constructor
  · nlinarith [mul_nonneg hCw (sq_nonneg (|deriv G.V x| - 1)), mul_nonneg hB (sq_nonneg (deriv G.V x))]
  · nlinarith [mul_nonneg hCw (sq_nonneg (deriv G.V x)), sq_nonneg (deriv G.V x), mul_nonneg hB ha]

/-- **D2** the cascade: for every `n`, `V'^n v` and `V'^n v'` lie in `L²(μ)`. -/
theorem resolvent_pow_L2
    (hlow : ∃ Cw : ℝ, 0 ≤ Cw ∧ ∀ x, -(Cw * (1 + |deriv G.V x|)) ≤ deriv (deriv G.V) x)
    (hsub : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ x, deriv (deriv G.V) x ≤ ε * deriv G.V x ^ 2 + B)
    {v a : ℝ → ℝ} (hv : Sm v) (ha : a ∈ OA₀) (hv2 : MemLp v 2 G.μ)
    (hL : ∀ x, Lg G.V v x = v x - a x) :
    ∀ n : ℕ, MemLp (fun x => deriv G.V x ^ n * v x) 2 G.μ ∧
      MemLp (fun x => deriv G.V x ^ n * deriv v x) 2 G.μ := by
  obtain ⟨Cw, hCw, hl⟩ := hlow
  have h1 := G.memLp_deriv_resolvent hv ha hv2 hL
  have hq1 : (fun x => deriv (deriv v) x - deriv G.V x * deriv v x) = fun x => v x - a x :=
    funext fun x => by have := hL x; unfold Lg at this; linarith
  intro n
  induction n with
  | zero => exact ⟨by simpa using hv2, by simpa using h1⟩
  | succ n ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have hψ : Sm (fun x => deriv G.V x ^ n) := G.smooth.deriv'.pow n
    have hn0 : (0 : ℝ) < 2 * n + 1 := by positivity
    constructor
    · obtain ⟨B, hB, hu⟩ := hsub (1 / (4 * (2 * n + 1))) (by positivity)
      have hup : ∀ x, deriv (deriv G.V) x * (deriv G.V x ^ n) ^ 2 +
          2 * deriv G.V x * deriv G.V x ^ n * deriv (fun y => deriv G.V y ^ n) x ≤
          (deriv G.V x ^ 2 / 4 + (2 * n + 1) * B) * (deriv G.V x ^ n) ^ 2 := by
        intro x
        rw [G.deriv_pow_V n x, key_pow]
        have h := hu x
        have e : (2 * (n : ℝ) + 1) * (1 / (4 * (2 * n + 1)) * deriv G.V x ^ 2) =
            deriv G.V x ^ 2 / 4 := by field_simp
        have h2 := mul_le_mul_of_nonneg_left h hn0.le
        have h3 := mul_le_mul_of_nonneg_right h2 (sq_nonneg (deriv G.V x ^ n))
        nlinarith [h3, e]
      have := G.memLp_of_hardy_w (by positivity : 0 ≤ (2 * (n : ℝ) + 1) * B) hv hψ ih1 ih2 hup
      have e : (fun x => deriv G.V x ^ (n + 1) * v x) =
          fun x => deriv G.V x * (deriv G.V x ^ n * v x) := funext fun x => by ring
      rw [e]; exact this
    · have haL : MemLp (fun x => deriv G.V x ^ n * a x) 2 G.μ :=
        (((G.smooth.deriv'.pow n).continuous.mul ha.1.continuous)).memLp_of_hasCompactSupport
          ha.2.mul_left
      have hq : MemLp (fun x => deriv G.V x ^ n *
          (deriv (deriv v) x - deriv G.V x * deriv v x)) 2 G.μ := by
        have e : (fun x => deriv G.V x ^ n * (deriv (deriv v) x - deriv G.V x * deriv v x)) =
            fun x => deriv G.V x ^ n * v x - deriv G.V x ^ n * a x :=
          funext fun x => by
            have this : deriv (deriv v) x - deriv G.V x * deriv v x = v x - a x := congrFun hq1 x
            rw [this]; ring
        rw [e]; exact ih1.sub haL
      have hlow' : ∀ x, -((2 * n + 1) * Cw * (1 + |deriv G.V x|)) * (deriv G.V x ^ n) ^ 2 ≤
          deriv (deriv G.V) x * (deriv G.V x ^ n) ^ 2 +
            2 * deriv G.V x * deriv G.V x ^ n * deriv (fun y => deriv G.V y ^ n) x := by
        intro x
        rw [G.deriv_pow_V n x, key_pow]
        have h3 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hl x) hn0.le)
          (sq_nonneg (deriv G.V x ^ n))
        nlinarith [h3]
      have := G.memLp_of_BE_w (by positivity : 0 ≤ (2 * (n : ℝ) + 1) * Cw) hv.deriv' hψ ih2 hq hlow'
      have e : (fun x => deriv G.V x ^ (n + 1) * deriv v x) =
          fun x => deriv G.V x * (deriv G.V x ^ n * deriv v x) := funext fun x => by ring
      rw [e]; exact this

end GibbsData

end MarkovTriple.BGL.Instances.Gibbs
