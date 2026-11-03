import Mathlib
import MarkovTriple.BGL.Instances.GibbsRd.EllCalc
import MarkovTriple.BGL.Instances.GibbsRd.Cutoff
import MarkovTriple.BGL.Frozen.Complete

/-!
# `EllData.diff`: the weighted elliptic operator on `ℝ^d` as a BGL `DiffusionTriple` (D1–D8), and its completeness

BGL Defs. 3.1.1, 3.1.3, 3.1.8 (D1–D8) and Def. 3.3.9.  For `E : EllData d`:

* `E.diff : DiffusionTriple (Rd d)` with `μ = Z⁻¹ w dx`, `𝒜₀ = C_c^∞(ℝ^d)`, `Γ = E.Γ`, `L = E.L`.  The exhaustion
  sequence is `u_n = cut (n+1)`; `ibp` is the master integration by parts `ibp_master` (divergence theorem for compactly
  supported `C^∞` vector fields, via Mathlib's `integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`).
* `E.ΓA_eq`: the `Γ` defined from `L` by `½(L(fg) − fLg − gLf)` (Def. 3.3.1 (iv)) is `E.Γ` on `C^∞` (everywhere).
* `E.diff_isComplete`: completeness (Def. 3.3.9) from the exhaustion function `a_exh` (round 17; was: the upper bound `a_bdd`), with
  `ζ_k = s(2 − ψ/(M (k+1)))`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace MarkovTriple.BGL.Instances.GibbsRd

open MarkovTriple.BGL (pderiv pderiv₂ DiffusionTriple)

variable {d : ℕ}

namespace EllData
variable (E : EllData d)

lemma integral_dens_mul (F : Rd d → ℝ) : ∫ x, E.dens x * F x = (∫ x, E.w x * F x) / E.Z := by
  rw [← integral_div]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [dens]; ring

/-- Integration by parts `∫ g L f dμ = −∫ Γ(g,f) dμ` for smooth `f, g`, one of them compactly supported
(BGL Def. 3.3.1 (vii), (1.11.9)). -/
lemma ibp_sm {f g : Rd d → ℝ} (hf : Sm f) (hg : Sm g)
    (hc : HasCompactSupport g ∨ HasCompactSupport f) :
    ∫ x, g x * E.L f x ∂E.μ = -∫ x, E.Γ g f x ∂E.μ := by
  have hm := E.ibp_master hf hg hc
  have c1 : HasCompactSupport (fun x => E.w x * g x * E.L f x) := by
    rcases hc with h | h
    · exact hcs_of_factor h fun x hx => by rw [hx]; ring
    · exact hcs_of_factor (E.hcs_L h) fun x hx => by rw [hx]; ring
  have c2 : HasCompactSupport (fun x => E.w x * E.Γ g f x) := by
    rcases hc with h | h
    · exact hcs_of_factor (E.hcs_Γ_left (g := f) h) fun x hx => by rw [hx]; ring
    · exact hcs_of_factor (E.hcs_Γ_right (f := g) h) fun x hx => by rw [hx]; ring
  have i1 : Integrable (fun x => E.w x * g x * E.L f x) volume :=
    (((E.w_smooth.mul hg).mul (E.sm_L hf)).continuous).integrable_of_hasCompactSupport c1
  have i2 : Integrable (fun x => E.w x * E.Γ g f x) volume :=
    ((E.w_smooth.mul (E.sm_Γ hg hf)).continuous).integrable_of_hasCompactSupport c2
  rw [integral_add i1 i2] at hm
  rw [E.integral_μ, E.integral_μ, E.integral_dens_mul, E.integral_dens_mul]
  have e1 : ∫ x, E.w x * (g x * E.L f x) = ∫ x, E.w x * g x * E.L f x :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
  rw [e1]
  have : ∫ x, E.w x * g x * E.L f x = -∫ x, E.w x * E.Γ g f x := by linarith
  rw [this]; ring

lemma integral_L_zero {f : Rd d → ℝ} (hf : f ∈ A₀ d) : ∫ x, E.L f x ∂E.μ = 0 := by
  have h := E.ibp_sm (f := f) (g := fun _ => (1 : ℝ)) hf.1 contDiff_const (Or.inr hf.2)
  have h0 : ∀ x, E.Γ (fun _ => (1 : ℝ)) f x = 0 := fun x => by
    simp [Γ, pderiv_const]
  simp only [one_mul, h0, integral_zero, neg_zero] at h
  exact h

/-! ### The exhaustion sequence -/

/-- `u_n = cut (n+1)` -/
noncomputable def expo (n : ℕ) : Rd d → ℝ := cut ((n : ℝ) + 1)

lemma expo_mem (n : ℕ) : (expo n : Rd d → ℝ) ∈ A₀ d :=
  ⟨sm_cut _, hcs_cut (by positivity)⟩

lemma expo_mono (n : ℕ) (x : Rd d) : expo n x ≤ expo (n + 1) x :=
  cut_mono (by positivity) (by push_cast; linarith) x

lemma expo_tendsto (x : Rd d) : Tendsto (fun n => expo n x) atTop (𝓝 1) := by
  refine tendsto_const_nhds.congr' ?_
  obtain ⟨N, hN⟩ := exists_nat_gt (qd x)
  filter_upwards [eventually_ge_atTop N] with n hn
  symm
  apply cut_eq_one (by positivity)
  have : (N : ℝ) ≤ n := by exact_mod_cast hn
  nlinarith [qd_nonneg x, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

/-! ### The Diffusion Markov Triple -/

/-- **The weighted elliptic `DiffusionTriple`** (BGL D1–D8) of `E`: `μ = Z⁻¹ w dx`, `𝒜₀ = C_c^∞(ℝ^d)`,
`Γ(f,g) = Σ aᵢⱼ ∂ᵢf ∂ⱼg`, `L f = w⁻¹ div (w a ∇f)`. -/
noncomputable def diff : DiffusionTriple (Rd d) where
  μ := E.μ
  sigmaFinite := inferInstance
  finite_prob := fun _ => inferInstance
  A₀ := A₀ d
  measurable := fun f hf => hf.1.continuous.measurable
  bounded := fun f hf => by
    obtain ⟨C, hC⟩ := hf.1.continuous.bounded_above_of_compact_support hf.2
    exact ⟨C, fun x => by simpa using hC x⟩
  memLp := fun f hf p _ _ => hf.1.continuous.memLp_of_hasCompactSupport hf.2
  dense := fun p hp hp' => by
    have := hp
    refine (Lp.dense_hasCompactSupport_contDiff (F := ℝ) (μ := E.μ) hp').mono ?_
    rintro u ⟨g, hug, hcs, hcd⟩
    exact ⟨g, ⟨hcd, hcs⟩, hug⟩
  comp_mem := fun k ψ hψ h0 f hf => comp_mem_A₀ k ψ hψ h0 f hf
  exhaustion := ⟨expo, fun n => expo_mem n,
    fun n => Eventually.of_forall fun x => expo_mono n x,
    Eventually.of_forall expo_tendsto⟩
  Γ := E.Γ
  L := E.L
  Γ_mem := fun f hf g hg => E.Γ_mem hf hg
  L_mem := fun f hf => E.L_mem hf
  Γ_symm := fun f _ g _ => Eventually.of_forall fun x => congrFun (E.Γ_symm f g) x
  Γ_add := fun f hf f' hf' g _ => Eventually.of_forall fun x => by
    simp only [Γ, Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [pderiv_add hf.1 hf'.1 i x]; ring
  Γ_smul := fun c f hf g _ => Eventually.of_forall fun x => by
    simp only [Γ, Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [pderiv_smul c hf.1 i x]; ring
  Γ_nonneg := fun f _ => Eventually.of_forall fun x => E.Γ_nonneg f x
  diffusion := fun k ψ hψ _ f hf g hg => Eventually.of_forall fun x =>
    E.Γ_comp ψ hψ f (fun i => (hf i).1) g x
  ibp := fun f hf g hg => by
    rw [E.ibp_sm hf.1 hg.1 (Or.inl hg.2), E.Γ_symm]
  integral_L := fun f hf => E.integral_L_zero hf

/-- On smooth functions the formula-defined `ΓA` of the triple is the coordinate carré du champ. -/
lemma ΓA_eq {f g : Rd d → ℝ} (hf : Sm f) (hg : Sm g) : E.diff.ΓA f g = E.Γ f g := by
  funext x
  exact E.ΓA_formula hf hg x

/-! ### Completeness -/

/-- the cut-offs `ζ_R = s(2 − ψ/R)` of a proper function `ψ ≥ 0` -/
noncomputable def cutPsi (ψ : Rd d → ℝ) (R : ℝ) (x : Rd d) : ℝ :=
  Real.smoothTransition (2 - ψ x / R)

lemma pderiv_cutPsi {ψ : Rd d → ℝ} (hψ : Sm ψ) (R : ℝ) (j : Fin d) (x : Rd d) :
    pderiv (cutPsi ψ R) j x = deriv Real.smoothTransition (2 - ψ x / R) * (-(pderiv ψ j x / R)) := by
  have hq := hψ.hasFDerivAt' x
  have h2 : HasFDerivAt (fun y : Rd d => 2 - ψ y / R) (-(R⁻¹ • fderiv ℝ ψ x)) x := by
    have := (hq.const_mul R⁻¹).const_sub 2
    simpa [div_eq_inv_mul] using this
  have h3 : HasDerivAt Real.smoothTransition (deriv Real.smoothTransition (2 - ψ x / R))
      (2 - ψ x / R) :=
    ((Real.smoothTransition.contDiff (n := 1)).differentiable (by simp) _).hasDerivAt
  have h4 := h3.comp_hasFDerivAt x h2
  unfold pderiv cutPsi
  rw [show (fun x : Rd d => Real.smoothTransition (2 - ψ x / R)) =
    Real.smoothTransition ∘ fun y : Rd d => 2 - ψ y / R from rfl, h4.fderiv]
  show deriv Real.smoothTransition (2 - ψ x / R) * (-(R⁻¹ * (fderiv ℝ ψ x) (Pi.single j 1))) = _
  simp [div_eq_inv_mul]

/-- **Completeness** (BGL Def. 3.3.9) of the weighted elliptic triple from the exhaustion function `a_exh`:
cut-offs `ζ_k = s(2 − ψ/(M(k+1)))`, `M = max 1 C`, `C ≥ |s'|`; `Γ(ζ_k) = s'² Γ(ψ)/(M(k+1))² ≤ 1/(k+1)²`. -/
theorem diff_isComplete : E.diff.IsComplete := by
  obtain ⟨ψ, hψ, hψ0, hψb, hψΓ⟩ := E.a_exh
  obtain ⟨C, hC0, hC⟩ := sT_deriv_bound
  set M : ℝ := 1 + C with hM
  have hM1 : 1 ≤ M := by linarith
  have hMpos : 0 < M := by linarith
  have hR : ∀ k : ℕ, 0 < M * ((k : ℝ) + 1) := fun k => by positivity
  have hsm : ∀ R : ℝ, Sm (cutPsi ψ R) := fun R =>
    Real.smoothTransition.contDiff.comp (contDiff_const.sub (hψ.div_const _))
  refine ⟨fun k => cutPsi ψ (M * ((k : ℝ) + 1)), fun k => ⟨hsm _, ?_⟩,
    fun k => Eventually.of_forall fun x => Real.smoothTransition.nonneg _,
    fun k => Eventually.of_forall fun x => ?_, Eventually.of_forall fun x => ?_,
    fun k => Eventually.of_forall fun x => ?_⟩
  · -- compact support: contained in the closed bounded set `{ψ ≤ 2R}`
    have hK : IsCompact {x : Rd d | ψ x ≤ 2 * (M * ((k : ℝ) + 1))} :=
      Metric.isCompact_of_isClosed_isBounded (isClosed_le hψ.continuous continuous_const)
        (hψb _)
    refine HasCompactSupport.intro hK fun x hx => ?_
    unfold cutPsi
    apply Real.smoothTransition.zero_of_nonpos
    have : ¬ ψ x ≤ 2 * (M * ((k : ℝ) + 1)) := hx
    have h2 : 2 ≤ ψ x / (M * ((k : ℝ) + 1)) := (le_div_iff₀ (hR k)).2 (by linarith [not_le.1 this])
    linarith
  · unfold cutPsi
    apply Real.smoothTransition.monotone
    have h1 : M * ((k : ℝ) + 1) ≤ M * (((k + 1 : ℕ) : ℝ) + 1) := by push_cast; nlinarith
    have : ψ x / (M * (((k + 1 : ℕ) : ℝ) + 1)) ≤ ψ x / (M * ((k : ℝ) + 1)) :=
      div_le_div_of_nonneg_left (hψ0 x) (hR k) h1
    linarith
  · refine tendsto_const_nhds.congr' ?_
    obtain ⟨N, hN⟩ := exists_nat_gt (ψ x)
    filter_upwards [eventually_ge_atTop N] with n hn
    symm
    unfold cutPsi
    apply Real.smoothTransition.one_of_one_le
    have : (N : ℝ) ≤ n := by exact_mod_cast hn
    have h2 : (n : ℝ) + 1 ≤ M * ((n : ℝ) + 1) := by nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have h3 : ψ x / (M * ((n : ℝ) + 1)) ≤ 1 := by
      rw [div_le_one (hR n)]; linarith
    linarith
  · show E.Γ (cutPsi ψ (M * ((k : ℝ) + 1))) (cutPsi ψ (M * ((k : ℝ) + 1))) x ≤ (1 / ((k : ℝ) + 1)) ^ 2
    set R := M * ((k : ℝ) + 1) with hRdef
    have hRpos : 0 < R := hR k
    set s' := deriv Real.smoothTransition (2 - ψ x / R) with hs'
    have e : E.Γ (cutPsi ψ R) (cutPsi ψ R) x =
        (s' / R) ^ 2 * ∑ i, ∑ j, E.a i j x * pderiv ψ i x * pderiv ψ j x := by
      unfold Γ
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [pderiv_cutPsi hψ, pderiv_cutPsi hψ]
      ring
    rw [e]
    have h1 : s' ^ 2 ≤ C ^ 2 := by
      have := hC (2 - ψ x / R)
      nlinarith [abs_nonneg s', sq_abs s']
    have h2 : (s' / R) ^ 2 ≤ (1 / ((k : ℝ) + 1)) ^ 2 := by
      rw [div_pow, one_div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
      have hk : (0 : ℝ) ≤ (k : ℝ) + 1 := by positivity
      have : R ^ 2 = M ^ 2 * ((k : ℝ) + 1) ^ 2 := by rw [hRdef]; ring
      rw [this, one_mul]
      have hCM : C ^ 2 ≤ M ^ 2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right hCM (sq_nonneg ((k : ℝ) + 1)), sq_nonneg ((k : ℝ) + 1)]
    calc (s' / R) ^ 2 * ∑ i, ∑ j, E.a i j x * pderiv ψ i x * pderiv ψ j x
        ≤ (s' / R) ^ 2 * 1 := mul_le_mul_of_nonneg_left (hψΓ x) (sq_nonneg _)
      _ ≤ _ := by rw [mul_one]; exact h2

end EllData

end MarkovTriple.BGL.Instances.GibbsRd
