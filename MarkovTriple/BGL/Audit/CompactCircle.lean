import MarkovTriple.BGL.Theory.Compact.Consequences
import MarkovTriple.BGL.Sanity.Trivial

/-! # Audit (round 10): concrete unfoldings of the compact-triple consequences (NOT imported by root).

1. `compact_logSobolev` is instantiated on the (degenerate, `Γ = 0`) one-point compact triple.
2. On the circle, for the Fourier modes `cos 2πn·`, `sin 2πn·`: closed forms of `P_t f`, `Γ(P_t f)`,
   `P_t Γ(f)` (from the Fourier action `e^{-(2πn)² t}`), the inequality `Γ(P_t f) ≤ P_t Γ f` verified
   by explicit algebra `(1-a²)² ≥ 0`, and its agreement with `circle_gradient_bound`.
3. Fisher information of `g_s = 1 + ½ cos` is `I(s) = ... a²/(...)` nonincreasing: checked in the
   scalar version at the end (explicit formula, real analysis).
-/
open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal Real

namespace MarkovTriple.BGL.Audit.CompactCircle

local notation "𝒜c" => MarkovTriple.Sanity.Circle.A₀

open MarkovTriple.BGL MarkovTriple.BGL.Circle MarkovTriple.Sanity.Circle AddCircle

/-- the log-Sobolev theorem applies to the trivial compact triple (hypotheses are satisfiable; `Γ = 0`). -/
theorem lsi_on_trivial : Sanity.trivialCompact.toDiffusionTriple.LS (1 / 1) 0 :=
  compact_logSobolev Sanity.trivialCompact one_pos (Sanity.trivialCompact_CD 1 le_rfl)

/-- `mcL n` with the measure written `circleCompact.μ` (definitionally `μ₀`). -/
noncomputable abbrev mcL' (n : ℤ) : Lp ℝ 2 circleCompact.μ := mcL n

/-- closed form of the heat flow on the cosine mode. -/
lemma Pt_mc (t : ℝ≥0) (n : ℤ) :
    circleCompact.Pt t ⟨mc n, mc_mem n⟩ =ᵐ[circleCompact.μ]
      fun x => Real.exp (-lam n * t) * mc n x := by
  have h := circleCompact.Pt_ae t ⟨mc n, mc_mem n⟩
  have e : circleCompact.toDiffusionTriple.semigroup t
      (circleCompact.toDiffusionTriple.cls ⟨mc n, mc_mem n⟩) =
      Real.exp (-lam n * t) • (mcL' n) := semigroup_mc t n
  have h1 := Lp.coeFn_smul (μ := circleCompact.μ) (Real.exp (-lam n * t)) (mcL' n)
  have h3 : ((mcL' n) : 𝕋 → ℝ) =ᵐ[circleCompact.μ] mc n :=
    (memLp_of_mem (mc_mem n) 2).coeFn_toLp
  refine h.symm.trans ((Filter.EventuallyEq.of_eq
    (congrArg (fun u : Lp ℝ 2 circleCompact.μ => (u : 𝕋 → ℝ)) e)).trans ?_)
  filter_upwards [h1, h3] with x a b
  exact a.trans (by simp only [Pi.smul_apply, smul_eq_mul]; exact congrArg _ b)


lemma mc_sq_add (n : ℤ) (x : 𝕋) : (mc n x) ^ 2 + (ms n x) ^ 2 = 1 := by
  have h2 := norm_fourier_pt n x
  have := Complex.sq_norm (fourier n x)
  rw [h2, Complex.normSq_apply] at this
  simp only [mc, ms]
  nlinarith

/-- `Γ(cos 2πn·) = (2πn)² sin²(2πn·)`. -/
lemma Gamma_mc_eq (n : ℤ) (c : ℝ) :
    cT.ΓA (fun x => c * mc n x) (fun x => c * mc n x) = fun x => c ^ 2 * ((2 * π * n) ^ 2 * (ms n x) ^ 2) := by
  have hm : (fun x => c * mc n x) ∈ 𝒜c := (𝒜c).smul_mem c (mc_mem n)
  rw [ΓA_eq_Gc hm hm]
  have hD : D (fun x => c * mc n x) = fun x => c * (-(2 * π * n) * ms n x) := by
    have := D_smul c (A₀_prop (mc_mem n)).1
    have e2 := D_mc n
    have e3 : (fun x => c * mc n x) = c • mc n := rfl
    rw [e3, this, e2]
    funext x; simp
  funext x
  simp only [Gc, hD]
  ring

lemma Gamma_Pt_mc (t : ℝ≥0) (n : ℤ) :
    circleCompact.toDiffusionTriple.ΓA (circleCompact.Pt t ⟨mc n, mc_mem n⟩)
        (circleCompact.Pt t ⟨mc n, mc_mem n⟩) =ᵐ[circleCompact.μ]
      fun x => (Real.exp (-lam n * t)) ^ 2 * ((2 * π * n) ^ 2 * (ms n x) ^ 2) := by
  have hv : (fun x => Real.exp (-lam n * t) * mc n x) ∈ circleCompact.A :=
    (𝒜c).smul_mem (Real.exp (-lam n * t)) (mc_mem n)
  have h := circleCompact.ΓA_congr_A (circleCompact.Pt_mem_A t ⟨mc n, mc_mem n⟩) hv (Pt_mc t n)
  refine h.trans (Filter.EventuallyEq.of_eq ?_)
  exact Gamma_mc_eq n _

lemma ms_sq (n : ℤ) (x : 𝕋) : (ms n x) ^ 2 = (1 - mc (2 * n) x) / 2 := by
  have h1 : fourier (2 * n) x = fourier n x * fourier n x := by
    rw [two_mul, fourier_add]
  have h2 := norm_fourier_pt n x
  have h3 : (fourier n x).re ^ 2 + (fourier n x).im ^ 2 = 1 := by
    have := Complex.sq_norm (fourier n x)
    rw [h2, Complex.normSq_apply] at this
    nlinarith
  simp only [mc, ms, h1, Complex.mul_re]
  nlinarith

lemma lam_two (n : ℤ) : lam (2 * n) = 4 * lam n := by
  simp only [lam]; push_cast; ring

/-- closed form of `P_t[Γ(cos 2πn·)] = ((2πn)²/2) (1 - e^{-lam(2n) t} cos 2π(2n)·)`. -/
lemma semigroup_Gamma_mc (t : ℝ≥0) (n : ℤ) :
    ((circleCompact.toDiffusionTriple.semigroup t (circleCompact.toDiffusionTriple.cls
        ⟨circleCompact.toDiffusionTriple.ΓA (mc n) (mc n),
          circleCompact.ΓA_self_mem_A₀ (mc_mem n)⟩) : Lp ℝ 2 circleCompact.μ) : 𝕋 → ℝ) =ᵐ[circleCompact.μ]
      fun x => ((2 * π * n) ^ 2 / 2) * (1 - Real.exp (-lam (2 * n) * t) * mc (2 * n) x) := by
  set k : ℝ := (2 * π * n) ^ 2 / 2 with hk
  have hcls : circleCompact.toDiffusionTriple.cls ⟨circleCompact.toDiffusionTriple.ΓA (mc n) (mc n),
      circleCompact.ΓA_self_mem_A₀ (mc_mem n)⟩ =
      k • ((circleCompact.toDiffusionTriple.one2 : Lp ℝ 2 circleCompact.μ) - mcL' (2 * n)) := by
    refine Lp.ext ?_
    have a1 := DiffusionTriple.coeFn_cls circleCompact.toDiffusionTriple
      ⟨circleCompact.toDiffusionTriple.ΓA (mc n) (mc n), circleCompact.ΓA_self_mem_A₀ (mc_mem n)⟩
    have a2 := Lp.coeFn_smul (μ := circleCompact.μ) k
      ((circleCompact.toDiffusionTriple.one2 : Lp ℝ 2 circleCompact.μ) - mcL' (2 * n))
    have a3 := Lp.coeFn_sub (μ := circleCompact.μ)
      (circleCompact.toDiffusionTriple.one2 : Lp ℝ 2 circleCompact.μ) (mcL' (2 * n))
    have a4 := circleCompact.toDiffusionTriple.coeFn_one2
    have a5 : ((mcL' (2 * n)) : 𝕋 → ℝ) =ᵐ[circleCompact.μ] mc (2 * n) :=
      (memLp_of_mem (mc_mem (2 * n)) 2).coeFn_toLp
    filter_upwards [a1, a2, a3, a4, a5] with x b1 b2 b3 b4 b5
    refine b1.trans ?_
    refine Eq.trans ?_ b2.symm
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [b3]; simp only [Pi.sub_apply]
    rw [b4, b5]
    have e1 : cT.ΓA (mc n) (mc n) x = (2 * π * n) ^ 2 * (ms n x) ^ 2 := by
      have := Gamma_mc_eq n 1
      simpa using congrFun this x
    show cT.ΓA (mc n) (mc n) x = _
    rw [e1, ms_sq]; ring
  rw [hcls]
  rw [map_smul, map_sub]
  have s1 : circleCompact.toDiffusionTriple.semigroup t
      (circleCompact.toDiffusionTriple.one2 : Lp ℝ 2 circleCompact.μ) =
      (circleCompact.toDiffusionTriple.one2 : Lp ℝ 2 circleCompact.μ) := semigroup_one t
  have s2 : circleCompact.toDiffusionTriple.semigroup t (mcL' (2 * n)) =
      Real.exp (-lam (2 * n) * t) • (mcL' (2 * n)) := semigroup_mc t _
  rw [s1, s2]
  have a2 := Lp.coeFn_smul (μ := circleCompact.μ) k
    ((circleCompact.toDiffusionTriple.one2 : Lp ℝ 2 circleCompact.μ) -
      Real.exp (-lam (2 * n) * t) • (mcL' (2 * n)))
  have a3 := Lp.coeFn_sub (μ := circleCompact.μ)
    (circleCompact.toDiffusionTriple.one2 : Lp ℝ 2 circleCompact.μ)
    (Real.exp (-lam (2 * n) * t) • (mcL' (2 * n)))
  have a4 := circleCompact.toDiffusionTriple.coeFn_one2
  have a6 := Lp.coeFn_smul (μ := circleCompact.μ) (Real.exp (-lam (2 * n) * t))
    (mcL' (2 * n))
  have a5 : ((mcL' (2 * n)) : 𝕋 → ℝ) =ᵐ[circleCompact.μ] mc (2 * n) :=
    (memLp_of_mem (mc_mem (2 * n)) 2).coeFn_toLp
  filter_upwards [a2, a3, a4, a5, a6] with x b2 b3 b4 b5 b6
  refine b2.trans ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [b3]; simp only [Pi.sub_apply]
  rw [b4, b6]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [b5]

/-- **Explicit gradient bound on the cosine mode**, proved by hand: with `a = e^{-lam n t} ∈ (0,1]`,
`a² (2πn)² sin² ≤ ((2πn)²/2)(1 - a⁴ cos(2π·2n·))`, i.e. `(1-a²)(½(1+a²) - a² sin²) ≥ 0`. -/
lemma explicit_ineq (t : ℝ≥0) (n : ℤ) (x : 𝕋) :
    (Real.exp (-lam n * t)) ^ 2 * ((2 * π * n) ^ 2 * (ms n x) ^ 2) ≤
      ((2 * π * n) ^ 2 / 2) * (1 - Real.exp (-lam (2 * n) * t) * mc (2 * n) x) := by
  set a := Real.exp (-lam n * t) with ha
  have ha0 : 0 < a := Real.exp_pos _
  have ha1 : a ≤ 1 := by
    rw [ha, Real.exp_le_one_iff]
    have := lam_nonneg n
    nlinarith [t.2]
  have e4 : Real.exp (-lam (2 * n) * t) = a ^ 4 := by
    rw [lam_two, ha, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hs := ms_sq n x
  have hs0 : 0 ≤ (ms n x) ^ 2 := sq_nonneg _
  have hs1 : (ms n x) ^ 2 ≤ 1 := by
    rw [hs]; have := mc_sq_add (2 * n) x; nlinarith [sq_nonneg (ms (2*n) x), sq_nonneg (mc (2*n) x)]
  have hc : mc (2 * n) x = 1 - 2 * (ms n x) ^ 2 := by rw [hs]; ring
  rw [e4, hc]
  have hk : 0 ≤ (2 * π * n) ^ 2 := sq_nonneg _
  have key : a ^ 2 * (ms n x) ^ 2 ≤ (1 - a ^ 4 * (1 - 2 * (ms n x) ^ 2)) / 2 := by
    have a2 : a ^ 2 ≤ 1 := by nlinarith
    nlinarith [mul_nonneg (sub_nonneg.2 a2) (sub_nonneg.2 hs1), mul_nonneg (sub_nonneg.2 a2) hs0,
      mul_nonneg (sq_nonneg a) (sub_nonneg.2 a2), mul_nonneg (mul_nonneg (sq_nonneg a) (sq_nonneg a)) hs0,
      sq_nonneg (1 - a ^ 2)]
  nlinarith [mul_le_mul_of_nonneg_left key hk]


/-- Consistency: the library theorem `circle_gradient_bound` at `f = cos 2πn·` unfolds, through the
closed forms above, to exactly the explicit inequality proved by hand in `explicit_ineq`. -/
theorem circle_gradient_bound_mode (t : ℝ≥0) (n : ℤ) :
    ∀ᵐ x ∂circleCompact.μ, (Real.exp (-lam n * t)) ^ 2 * ((2 * π * n) ^ 2 * (ms n x) ^ 2) ≤
      ((2 * π * n) ^ 2 / 2) * (1 - Real.exp (-lam (2 * n) * t) * mc (2 * n) x) := by
  have h := circle_gradient_bound ⟨mc n, mc_mem n⟩ t
  filter_upwards [h, Gamma_Pt_mc t n, semigroup_Gamma_mc t n] with x h1 h2 h3
  rw [h2] at h1
  rw [h3] at h1
  exact h1

/-- and independently of the library theorem the explicit inequality holds everywhere. -/
theorem explicit_gradient_bound_mode (t : ℝ≥0) (n : ℤ) :
    ∀ᵐ x ∂circleCompact.μ, (Real.exp (-lam n * t)) ^ 2 * ((2 * π * n) ^ 2 * (ms n x) ^ 2) ≤
      ((2 * π * n) ^ 2 / 2) * (1 - Real.exp (-lam (2 * n) * t) * mc (2 * n) x) :=
  Eventually.of_forall (explicit_ineq t n)

/-- Non-vacuity of the `n ≠ 0` case: for `n = 1`, `t > 0` the inequality is strict at `x = 1/4`
(`sin = 1`, `cos 4π x = -1`): `a² ≤ ½ (1 + a⁴)` with `a = e^{-(2π)² t} < 1`. -/
theorem strict_at_quarter (t : ℝ≥0) (ht : 0 < t) :
    (Real.exp (-lam 1 * t)) ^ 2 * ((2 * π * (1 : ℤ)) ^ 2 * (ms 1 ((1 / 4 : ℝ) : 𝕋)) ^ 2) <
      ((2 * π * (1 : ℤ)) ^ 2 / 2) *
        (1 - Real.exp (-lam (2 * 1) * t) * mc (2 * 1) ((1 / 4 : ℝ) : 𝕋)) := by
  have hs : (ms 1 ((1 / 4 : ℝ) : 𝕋)) ^ 2 = 1 := by
    have h1 := mc_sq_add 1 ((1 / 4 : ℝ) : 𝕋)
    have : mc 1 ((1 / 4 : ℝ) : 𝕋) = 0 := by
      simp only [mc]
      have : fourier 1 (((1 / 4 : ℝ)) : 𝕋) = Complex.I := by
        rw [fourier_coe_apply]
        have : (2 * (π : ℂ) * Complex.I * (1 : ℤ) * ((1 / 4 : ℝ) : ℂ) / (1 : ℝ)) = π / 2 * Complex.I := by
          push_cast; ring
        rw [this, Complex.exp_mul_I]
        simp [Complex.cos_pi_div_two, Complex.sin_pi_div_two]
      rw [this]; simp
    rw [this] at h1; linarith
  have hc : mc (2 * 1) ((1 / 4 : ℝ) : 𝕋) = -1 := by
    have h := ms_sq 1 ((1 / 4 : ℝ) : 𝕋)
    rw [hs] at h; linarith
  rw [hs, hc]
  set a := Real.exp (-lam 1 * t) with ha
  have ha1 : a < 1 := by
    rw [ha, Real.exp_lt_one_iff]
    have : 0 < lam 1 := by simp only [lam]; positivity
    have : (0 : ℝ) < t := by exact_mod_cast ht
    nlinarith
  have ha0 : 0 < a := Real.exp_pos _
  have e4 : Real.exp (-lam (2 * 1) * t) = a ^ 4 := by
    rw [lam_two, ha, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [e4]
  have hk : 0 < (2 * π * ((1 : ℤ) : ℝ)) ^ 2 := by positivity
  have : a ^ 2 * 1 < (1 + a ^ 4) / 2 := by nlinarith [sq_pos_of_pos (sub_pos.2 (show a ^ 2 < 1 by nlinarith))]
  nlinarith [mul_lt_mul_of_pos_left this hk]

/-- the test function `φ = ½ + ½ cos 2π·` (so `ε + P_s φ = 1 + ½ e^{-(2π)² s} cos` for `ε = ½`). -/
noncomputable def phiC : circleCompact.A₀ :=
  ⟨fun x => 1 / 2 + 1 / 2 * mc 1 x, add_mem (mem_A₀.2 contDiff_const) ((𝒜c).smul_mem _ (mc_mem 1))⟩

lemma phiC_nonneg : 0 ≤ᵐ[circleCompact.μ] phiC.1 := Eventually.of_forall fun x => by
  have := mc_sq_add 1 x
  show 0 ≤ 1 / 2 + 1 / 2 * mc 1 x
  nlinarith [sq_nonneg (ms 1 x), sq_nonneg (mc 1 x + 1)]

/-- The Fisher information of `g_s = 1 + ½ e^{-λ s} cos 2π·` is nonincreasing (library theorem). -/
theorem fisher_antitone_concrete :
    AntitoneOn (circleCompact.toFullTriple.entI phiC (1 / 2)) (Set.Ici 0) :=
  circle_fisher_antitone phiC phiC_nonneg (by norm_num)

/-- closed form of that Fisher information (the value of `∫ Γ(g)/g`, from
`∫₀¹ sin²(2πx)/(1+b cos 2πx) dx = (1-√(1-b²))/b²`, `b = a/2`); this is the SCALAR function that the
numerical script `scratchpad/fisher_check.py` compares with quadrature. -/
noncomputable def fisherClosed (s : ℝ) : ℝ :=
  (2 * π) ^ 2 * (1 - Real.sqrt (1 - Real.exp (-2 * (2 * π) ^ 2 * s) / 4))

lemma fisherClosed_antitone : Antitone fisherClosed := by
  intro s r hsr
  unfold fisherClosed
  have h1 : Real.exp (-2 * (2 * π) ^ 2 * r) ≤ Real.exp (-2 * (2 * π) ^ 2 * s) := by
    apply Real.exp_le_exp.2
    have : 0 < (2 * π) ^ 2 := by positivity
    nlinarith
  have h2 : Real.sqrt (1 - Real.exp (-2 * (2 * π) ^ 2 * s) / 4) ≤
      Real.sqrt (1 - Real.exp (-2 * (2 * π) ^ 2 * r) / 4) :=
    Real.sqrt_le_sqrt (by linarith)
  have : 0 < (2 * π) ^ 2 := by positivity
  nlinarith

/-- `I' ≤ -2ρ I` with `ρ = 0` for the closed form is trivial, but also `I(s) ≤ I(0)`. -/
lemma fisherClosed_le_zero {s : ℝ} (hs : 0 ≤ s) : fisherClosed s ≤ fisherClosed 0 :=
  fisherClosed_antitone hs

end MarkovTriple.BGL.Audit.CompactCircle

#print axioms MarkovTriple.BGL.Audit.CompactCircle.lsi_on_trivial
#print axioms MarkovTriple.BGL.Audit.CompactCircle.circle_gradient_bound_mode
#print axioms MarkovTriple.BGL.Audit.CompactCircle.explicit_gradient_bound_mode
#print axioms MarkovTriple.BGL.Audit.CompactCircle.strict_at_quarter
#print axioms MarkovTriple.BGL.Audit.CompactCircle.fisher_antitone_concrete
#print axioms MarkovTriple.BGL.Audit.CompactCircle.fisherClosed_antitone
