import Mathlib
import MarkovTriple.BGL.Instances.Gibbs.DirectMain
import MarkovTriple.BGL.Instances.Gibbs.Core2PolyW

/-!
# Non-vacuity of the direct converse: a spiky uniformly convex Gibbs potential outside `PolyHess` (R20, Stream D1)

Statements: `STATEMENTS_R20_Direct.md` (D1-5).

## DIFFERENCE FROM BGL

BGL's converse of Prop. 3.3.17 needs the core of `L²` (`Core2`); the R17-R19 proofs of `Core2` need growth conditions (`BddJet`, `GrowHess`,
`PolyHess`).  The direct route (`gibbs_mem_domain_of_Γ₂_direct`) needs only `V'' ≥ ρ`.  Here we exhibit a potential with `V'' ≥ 1` (`ρ = 1 > 0`)
which is NOT in the class `PolyHess` (hence not in `GrowHess`/`BddJet`): `V'' = 2 + sin(e^{x²})`, `V''' = 2x e^{x²} cos(e^{x²})` oscillates
superpolynomially while `|V'| ≤ 3|x|`.  `V` is the double primitive of `V''` (no closed form).  For this `V` the Round 17-19 theorems do not apply;
the new theorem does, and `Core2` is neither proved nor refuted.
-/

open MeasureTheory Filter Topology Set
open MarkovTriple.Sanity.OU (Sm)
open MarkovTriple.BGL (FullTriple)

namespace MarkovTriple.BGL.Instances.Gibbs

/-- primitive vanishing at `0`. -/
noncomputable def prim (g : ℝ → ℝ) : ℝ → ℝ := fun x => ∫ t in (0 : ℝ)..x, g t

lemma hasDerivAt_prim {g : ℝ → ℝ} (hg : Continuous g) (x : ℝ) : HasDerivAt (prim g) (g x) x :=
  (hg.integral_hasStrictDerivAt 0 x).hasDerivAt

lemma deriv_prim {g : ℝ → ℝ} (hg : Continuous g) : deriv (prim g) = g :=
  funext fun x => (hasDerivAt_prim hg x).deriv

lemma sm_prim {g : ℝ → ℝ} (hg : Sm g) : Sm (prim g) := by
  refine contDiff_infty_iff_deriv.2 ⟨fun x => (hasDerivAt_prim hg.continuous x).differentiableAt, ?_⟩
  rw [deriv_prim hg.continuous]
  exact hg

lemma prim_sign_of_nonneg {h : ℝ → ℝ} (h0 : ∀ t, 0 ≤ h t) (x : ℝ) :
    (0 ≤ x → 0 ≤ prim h x) ∧ (x ≤ 0 → prim h x ≤ 0) := by
  refine ⟨fun hx => intervalIntegral.integral_nonneg hx (fun t _ => h0 t), fun hx => ?_⟩
  unfold prim
  rw [intervalIntegral.integral_symm]
  have : 0 ≤ ∫ t in x..0, h t := intervalIntegral.integral_nonneg hx (fun t _ => h0 t)
  linarith

lemma prim_nonneg_of_sign {h : ℝ → ℝ} (h1 : ∀ t, 0 ≤ t → 0 ≤ h t) (h2 : ∀ t, t ≤ 0 → h t ≤ 0)
    (x : ℝ) : 0 ≤ prim h x := by
  rcases le_total 0 x with hx | hx
  · exact intervalIntegral.integral_nonneg hx (fun t ht => h1 t ht.1)
  · unfold prim
    rw [intervalIntegral.integral_symm]
    have : 0 ≤ ∫ t in x..0, -h t :=
      intervalIntegral.integral_nonneg hx (fun t ht => by linarith [h2 t ht.2])
    rw [intervalIntegral.integral_neg] at this
    linarith

/-- the second derivative profile `V'' = 2 + sin(e^{x²})`. -/
noncomputable def spk (x : ℝ) : ℝ := 2 + Real.sin (Real.exp (x ^ 2))

lemma sm_spk : Sm spk :=
  contDiff_const.add (Real.contDiff_sin.comp (Real.contDiff_exp.comp (contDiff_id.pow 2)))

lemma spk_ge (x : ℝ) : 1 ≤ spk x := by
  have := Real.neg_one_le_sin (Real.exp (x ^ 2)); unfold spk; linarith

lemma spk_le (x : ℝ) : spk x ≤ 3 := by
  have := Real.sin_le_one (Real.exp (x ^ 2)); unfold spk; linarith

lemma hasDerivAt_spk (x : ℝ) :
    HasDerivAt spk (Real.cos (Real.exp (x ^ 2)) * (Real.exp (x ^ 2) * (2 * x))) x := by
  have h1 := (Real.hasDerivAt_exp (x ^ 2)).comp x (hasDerivAt_pow 2 x)
  have h2 := (Real.hasDerivAt_sin (Real.exp (x ^ 2))).comp x
    (show HasDerivAt (fun y : ℝ => Real.exp (y ^ 2)) (Real.exp (x ^ 2) * (2 * x)) x from by
      refine h1.congr_deriv ?_
      simp)
  exact (h2.const_add 2).congr_deriv (by ring)

/-- `V' `. -/
noncomputable def spkP1 : ℝ → ℝ := prim spk
/-- `V`. -/
noncomputable def spkV : ℝ → ℝ := prim spkP1

lemma sm_spkP1 : Sm spkP1 := sm_prim sm_spk
lemma sm_spkV : Sm spkV := sm_prim sm_spkP1
lemma deriv_spkV : deriv spkV = spkP1 := deriv_prim sm_spkP1.continuous
lemma deriv_spkP1 : deriv spkP1 = spk := deriv_prim sm_spk.continuous

lemma spkP1_sub (x : ℝ) : prim (fun t => spk t - 1) x = spkP1 x - x := by
  unfold prim spkP1
  rw [intervalIntegral.integral_sub (sm_spk.continuous.intervalIntegrable _ _)
    (continuous_const.intervalIntegrable _ _)]
  simp [prim]

lemma spkP1_sign (x : ℝ) : (0 ≤ x → x ≤ spkP1 x) ∧ (x ≤ 0 → spkP1 x ≤ x) := by
  have h := prim_sign_of_nonneg (h := fun t => spk t - 1) (fun t => by linarith [spk_ge t]) x
  rw [spkP1_sub] at h
  exact ⟨fun hx => by linarith [h.1 hx], fun hx => by linarith [h.2 hx]⟩

lemma spkV_sub (x : ℝ) : prim (fun t => spkP1 t - t) x = spkV x - x ^ 2 / 2 := by
  show ∫ t in (0 : ℝ)..x, (spkP1 t - t) = (∫ t in (0 : ℝ)..x, spkP1 t) - x ^ 2 / 2
  rw [intervalIntegral.integral_sub (f := spkP1) (g := fun t : ℝ => t)
    (sm_spkP1.continuous.intervalIntegrable _ _) (continuous_id.intervalIntegrable _ _)]
  simp

lemma spkV_ge (x : ℝ) : x ^ 2 / 2 ≤ spkV x := by
  have h := prim_nonneg_of_sign (h := fun t => spkP1 t - t)
    (fun t ht => by linarith [(spkP1_sign t).1 ht]) (fun t ht => by linarith [(spkP1_sign t).2 ht]) x
  rw [spkV_sub] at h
  linarith

lemma abs_spkP1_le (x : ℝ) : |spkP1 x| ≤ 3 * |x| := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := x) (C := 3)
    (f := spk) (fun t _ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [spk_ge t])]
      exact spk_le t)
  rw [Real.norm_eq_abs] at h
  unfold spkP1 prim
  simpa using h

lemma spkV_integrable : Integrable (fun x => Real.exp (-spkV x)) := by
  have hI : Integrable (fun x : ℝ => Real.exp (-(1 / 2) * x ^ 2)) :=
    integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)
  refine hI.mono' (Real.continuous_exp.comp sm_spkV.continuous.neg).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  refine Real.exp_le_exp.2 ?_
  have := spkV_ge x
  linarith

/-- **The spiky Gibbs data** `μ ∝ e^{-V}`, `V'' = 2 + sin(e^{x²}) ≥ 1`. -/
noncomputable def spikyGibbs : GibbsData where
  V := spkV
  smooth := sm_spkV
  integrable := spkV_integrable

lemma spiky_d1 : deriv spikyGibbs.V = spkP1 := deriv_spkV
lemma spiky_d2 : deriv (deriv spikyGibbs.V) = spk := by
  show deriv (deriv spkV) = spk
  rw [deriv_spkV, deriv_spkP1]
lemma spiky_d3 : deriv (deriv (deriv spikyGibbs.V)) = deriv spk := by
  rw [spiky_d2]

/-- uniform convexity: `V'' ≥ 1`, i.e. `ρ = 1 > 0`. -/
theorem spikyGibbs_convex : ∀ x, (1 : ℝ) ≤ deriv (deriv spikyGibbs.V) x := fun x => by
  rw [spiky_d2]; exact spk_ge x

/-- arbitrarily far peaks of the third derivative: for every `X` there is `x ≥ max X 1` with `e^{x²} = 2πk` (`k ∈ ℕ`), so that
`(V'')'(x) = 2x e^{x²}`. -/
lemma spk_peak (X : ℝ) :
    ∃ x : ℝ, X ≤ x ∧ 1 ≤ x ∧ deriv spk x = Real.exp (x ^ 2) * (2 * x) := by
  set Y : ℝ := max 1 X with hY
  obtain ⟨k, hk⟩ := exists_nat_ge (Real.exp (Y ^ 2))
  have hY1 : 1 ≤ Y := le_max_left _ _
  have hkpos : (0 : ℝ) < k := lt_of_lt_of_le (Real.exp_pos _) hk
  have h2pk : (0 : ℝ) < 2 * Real.pi * k := by positivity
  set x : ℝ := Real.sqrt (Real.log (2 * Real.pi * k)) with hx
  have hlog : Y ^ 2 ≤ Real.log (2 * Real.pi * k) := by
    rw [Real.le_log_iff_exp_le h2pk]
    have : (1 : ℝ) ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
    nlinarith [Real.exp_pos (Y ^ 2)]
  have hx2 : x ^ 2 = Real.log (2 * Real.pi * k) := by
    rw [hx, Real.sq_sqrt]; exact (sq_nonneg Y).trans hlog
  have hxY : Y ≤ x := by
    rw [hx]
    exact Real.le_sqrt_of_sq_le hlog
  have hexp : Real.exp (x ^ 2) = 2 * Real.pi * k := by rw [hx2, Real.exp_log h2pk]
  have hcos : Real.cos (Real.exp (x ^ 2)) = 1 := by
    rw [hexp]
    have := Real.cos_nat_mul_two_pi k
    rw [show 2 * Real.pi * (k : ℝ) = (k : ℝ) * (2 * Real.pi) by ring]
    exact this
  exact ⟨x, (le_max_right _ _).trans hxY, hY1.trans hxY, by
    rw [(hasDerivAt_spk x).deriv, hcos, one_mul]⟩

/-- **`PolyHess` fails**: `V'''` is not polynomially dominated by `V'`. -/
theorem spikyGibbs_not_polyHess : ¬ spikyGibbs.PolyHess := by
  rintro ⟨-, -, C, N, hC⟩
  set A : ℝ := |C| * (1 + 3 ^ N) * (Nat.factorial N : ℝ) with hA
  set X : ℝ := max 1 (A + 1) with hX
  have hXA : A + 1 ≤ X := le_max_right _ _
  obtain ⟨x, hxX, hx1, hpk⟩ := spk_peak X
  have h3 : |deriv (deriv (deriv spikyGibbs.V)) x| = Real.exp (x ^ 2) * (2 * x) := by
    rw [spiky_d3, hpk, abs_of_nonneg (by positivity)]
  have h1 : |deriv spikyGibbs.V x| ≤ 3 * x := by
    rw [spiky_d1]
    have := abs_spkP1_le x
    rwa [abs_of_nonneg (by linarith : (0 : ℝ) ≤ x)] at this
  have hpow : |deriv spikyGibbs.V x| ^ N ≤ (3 * x) ^ N :=
    pow_le_pow_left₀ (abs_nonneg _) h1 N
  have hb := hC x
  rw [h3] at hb
  have hxN : (1 + (3 * x) ^ N) ≤ (1 + 3 ^ N) * x ^ N := by
    rw [mul_pow]
    have : 1 ≤ x ^ N := one_le_pow₀ hx1
    nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 3) N]
  have hfac : x ^ (2 * N) / (Nat.factorial N : ℝ) ≤ Real.exp (x ^ 2) := by
    have := Real.pow_div_factorial_le_exp (x ^ 2) (sq_nonneg x) N
    rwa [← pow_mul] at this
  have hCle : C * (1 + |deriv spikyGibbs.V x| ^ N) ≤ |C| * ((1 + 3 ^ N) * x ^ N) := by
    have h4 : 1 + |deriv spikyGibbs.V x| ^ N ≤ (1 + 3 ^ N) * x ^ N := by linarith
    calc C * (1 + |deriv spikyGibbs.V x| ^ N) ≤ |C| * (1 + |deriv spikyGibbs.V x| ^ N) :=
          mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
      _ ≤ |C| * ((1 + 3 ^ N) * x ^ N) := mul_le_mul_of_nonneg_left h4 (abs_nonneg C)
  have hfN : (0 : ℝ) < (Nat.factorial N : ℝ) := by exact_mod_cast Nat.factorial_pos N
  have key : x ^ (2 * N) / (Nat.factorial N : ℝ) * (2 * x) ≤ |C| * ((1 + 3 ^ N) * x ^ N) :=
    (mul_le_mul_of_nonneg_right hfac (by positivity)).trans (hb.trans hCle)
  -- divide by `x^N` and `N!`
  have hxN0 : (0 : ℝ) < x ^ N := by positivity
  have e1 : x ^ (2 * N) = x ^ N * x ^ N := by rw [two_mul, pow_add]
  have key2 : 2 * x * (x ^ N * x ^ N) ≤ A * x ^ N := by
    have := mul_le_mul_of_nonneg_right key hfN.le
    have e2 : x ^ (2 * N) / (Nat.factorial N : ℝ) * (2 * x) * (Nat.factorial N : ℝ) =
        x ^ (2 * N) * (2 * x) := by field_simp
    rw [e2] at this
    rw [e1] at this
    rw [hA]
    nlinarith [this]
  have key3 : 2 * x * x ^ N ≤ A := by
    have : 2 * x * x ^ N * x ^ N ≤ A * x ^ N := by nlinarith [key2]
    exact le_of_mul_le_mul_right this hxN0
  have : x ≤ x ^ N := by
    rcases Nat.eq_zero_or_pos N with h0 | h0
    · simp [h0] at key3
      nlinarith
    · exact (le_self_pow₀ hx1 h0.ne')
  nlinarith [hXA.trans hxX]

/-- the converse of BGL Prop. 3.3.17 for the spiky potential (`ρ = 1`), outside all the classes of R17-R19. -/
theorem spikyGibbs_mem_domain_of_Γ₂ {f : ℝ → ℝ} (hf : f ∈ spikyGibbs.gibbsFull_unconditional.A)
    (hf2 : MemLp f 2 spikyGibbs.μ)
    (hG : Integrable (FullTriple.G spikyGibbs.gibbsFull_unconditional f f) spikyGibbs.μ)
    (hG2 : Integrable (spikyGibbs.gibbsFull_unconditional.toDiffusionTriple.Γ₂ f f) spikyGibbs.μ) :
    ∃ hF : hf2.toLp f ∈ spikyGibbs.gibbsFull_unconditional.toDiffusionTriple.generator.domain,
      ((spikyGibbs.gibbsFull_unconditional.toDiffusionTriple.generator ⟨hf2.toLp f, hF⟩ :
        Lp ℝ 2 spikyGibbs.μ) : ℝ → ℝ) =ᵐ[spikyGibbs.μ] spikyGibbs.gibbsFull_unconditional.L f :=
  spikyGibbs.gibbs_mem_domain_of_Γ₂_direct spikyGibbs_convex hf hf2 hG hG2


/-- `x ∈ L²(μ)` for the spiky Gibbs measure. -/
lemma spikyGibbs_memLp_id : MemLp (fun x : ℝ => x) 2 spikyGibbs.μ := by
  refine (memLp_two_iff_integrable_sq (f := fun x : ℝ => x) continuous_id.aestronglyMeasurable).2 ?_
  unfold GibbsData.μ
  rw [integrable_withDensity_iff_integrable_smul' (f := fun x => ENNReal.ofReal (spikyGibbs.w x))
    (ENNReal.measurable_ofReal.comp spikyGibbs.w_smooth.continuous.measurable)
    (Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  have hZ := spikyGibbs.Z_pos
  have hI := integrable_rpow_mul_exp_neg_mul_sq (b := 1 / 2) (by norm_num) (s := 2) (by norm_num)
  refine (hI.const_mul (1 / spikyGibbs.Z)).mono' ?_ (Eventually.of_forall fun x => ?_)
  · exact (((ENNReal.measurable_ofReal.comp spikyGibbs.w_smooth.continuous.measurable).ennreal_toReal.smul
      (continuous_id.pow 2).measurable)).aestronglyMeasurable
  · have hw : spikyGibbs.w x ≤ 1 / spikyGibbs.Z * Real.exp (-(1 / 2) * x ^ 2) := by
      unfold GibbsData.w
      rw [div_eq_mul_one_div, mul_comm]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
      have := spkV_ge x
      show -spkV x ≤ -(1 / 2) * x ^ 2
      linarith
    rw [ENNReal.toReal_ofReal (spikyGibbs.w_pos x).le, smul_eq_mul, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (spikyGibbs.w_pos x).le (sq_nonneg x)), Real.rpow_two]
    calc spikyGibbs.w x * x ^ 2 ≤ (1 / spikyGibbs.Z * Real.exp (-(1 / 2) * x ^ 2)) * x ^ 2 :=
          mul_le_mul_of_nonneg_right hw (sq_nonneg x)
      _ = 1 / spikyGibbs.Z * (x ^ 2 * Real.exp (-(1 / 2) * x ^ 2)) := by ring

/-- **Non-vacuity**: `f = id` satisfies all hypotheses (`Γ(f) = 1`, `Γ₂(f) = V'' = 2 + sin(e^{x²})`, bounded), and the
conclusion `[x] ∈ 𝒟(L)`, `L[x] = [−V']` holds for the spiky measure. -/
theorem spikyGibbs_id_mem_domain :
    ∃ hF : spikyGibbs_memLp_id.toLp (fun x : ℝ => x) ∈
        spikyGibbs.gibbsFull_unconditional.toDiffusionTriple.generator.domain,
      ((spikyGibbs.gibbsFull_unconditional.toDiffusionTriple.generator
        ⟨spikyGibbs_memLp_id.toLp (fun x : ℝ => x), hF⟩ : Lp ℝ 2 spikyGibbs.μ) : ℝ → ℝ)
        =ᵐ[spikyGibbs.μ] spikyGibbs.gibbsFull_unconditional.L (fun x : ℝ => x) := by
  have hS : Sm (fun x : ℝ => x) := contDiff_id
  refine spikyGibbs_mem_domain_of_Γ₂ hS spikyGibbs_memLp_id ?_ ?_
  · have e : FullTriple.G spikyGibbs.gibbsFull_unconditional (fun x : ℝ => x) (fun x : ℝ => x) =
        MarkovTriple.Sanity.OU.Go (fun x : ℝ => x) (fun x : ℝ => x) := spikyGibbs.gibbsDiff_ΓA hS hS
    rw [e]
    have : MarkovTriple.Sanity.OU.Go (fun x : ℝ => x) (fun x : ℝ => x) = fun _ => (1 : ℝ) := by
      funext x; simp [MarkovTriple.Sanity.OU.Go]
    rw [this]
    exact integrable_const _
  · have e : ∀ x, spikyGibbs.gibbsFull_unconditional.toDiffusionTriple.Γ₂ (fun x : ℝ => x) (fun x : ℝ => x) x
        = spk x := by
      intro x
      have e1 : spikyGibbs.gibbsDiff.ΓA (fun x : ℝ => x) (fun x : ℝ => x) =
          MarkovTriple.Sanity.OU.Go (fun x : ℝ => x) (fun x : ℝ => x) := spikyGibbs.gibbsDiff_ΓA hS hS
      have hL : Sm (Lg spikyGibbs.V (fun x : ℝ => x)) := sm_Lg spikyGibbs.smooth hS
      have e2 : spikyGibbs.gibbsDiff.ΓA (fun x : ℝ => x) (Lg spikyGibbs.V (fun x : ℝ => x)) =
          MarkovTriple.Sanity.OU.Go (fun x : ℝ => x) (Lg spikyGibbs.V (fun x : ℝ => x)) :=
        spikyGibbs.gibbsDiff_ΓA hS hL
      have e3 : spikyGibbs.gibbsDiff.ΓA (Lg spikyGibbs.V (fun x : ℝ => x)) (fun x : ℝ => x) =
          MarkovTriple.Sanity.OU.Go (Lg spikyGibbs.V (fun x : ℝ => x)) (fun x : ℝ => x) :=
        spikyGibbs.gibbsDiff_ΓA hL hS
      have e : spikyGibbs.gibbsFull_unconditional.toDiffusionTriple.Γ₂ (fun x : ℝ => x) (fun x : ℝ => x) x =
          (Lg spikyGibbs.V (MarkovTriple.Sanity.OU.Go (fun x : ℝ => x) (fun x : ℝ => x)) x -
            2 * MarkovTriple.Sanity.OU.Go (fun x : ℝ => x) (Lg spikyGibbs.V (fun x : ℝ => x)) x) / 2 := by
        show (Lg spikyGibbs.V (spikyGibbs.gibbsDiff.ΓA (fun x : ℝ => x) (fun x : ℝ => x)) x -
          spikyGibbs.gibbsDiff.ΓA (fun x : ℝ => x) (Lg spikyGibbs.V (fun x : ℝ => x)) x -
          spikyGibbs.gibbsDiff.ΓA (Lg spikyGibbs.V (fun x : ℝ => x)) (fun x : ℝ => x) x) / 2 = _
        rw [e1, e2, e3]
        simp only [MarkovTriple.Sanity.OU.Go]; ring
      rw [e, Γ₂_eq spikyGibbs.smooth hS x, spiky_d2]
      simp [spk]
    refine (integrable_const (3 : ℝ)).mono' ?_ (Eventually.of_forall fun x => ?_)
    · have : spikyGibbs.gibbsFull_unconditional.toDiffusionTriple.Γ₂ (fun x : ℝ => x) (fun x : ℝ => x) = spk :=
        funext e
      rw [this]
      exact sm_spk.continuous.aestronglyMeasurable
    · rw [e x, Real.norm_eq_abs, abs_of_nonneg (by linarith [spk_ge x])]
      exact spk_le x

end MarkovTriple.BGL.Instances.Gibbs
