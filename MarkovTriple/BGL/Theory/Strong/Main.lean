import Mathlib
import MarkovTriple.BGL.Theory.Strong.Interpolation

/-!
# Strong gradient bound (BGL Thm 3.3.18), from the interpolation hypothesis

`√Γ(P_t f) ≤ e^{-ρt} P_t(√Γ f)` a.e., for `f ∈ 𝒜₀`, under `CD(ρ,n)`, `ρ ≥ 0` and the analytic regularity
structure `StrongInterpolation` (discharged for OU, `Instances/OU/StrongMain.lean`).
-/

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

namespace MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E]

namespace FullTriple

variable (T : FullTriple E)

/-- `Φ_ε(s) = ∫ P_s h · ψ_ε(Γ(P_{t-s} f)) dμ`. -/
noncomputable def strongPhi (ε : ℝ) (f h : T.A₀) (t : ℝ≥0) (s : ℝ) : ℝ :=
  ∫ x, T.Pt s.toNNReal h x *
    psiS ε (G T (T.Pt ((t : ℝ) - s).toNNReal f) (T.Pt ((t : ℝ) - s).toNNReal f) x) ∂T.μ

/-- **The analytic regularity hypothesis for the strong gradient bound** (the part of BGL
Lemmas 3.3.20–3.3.21 and of the proof of Thm 3.3.18 that is not algebra): for every `ε > 0`, `f, h ∈ 𝒜₀`,
`h ≥ 0`, `t ≥ 0`: `Φ_ε` is continuous on `[0,t]` and on `(0,t)` its derivative is
`∫ P_s h · (L(ψ_ε∘Γ g_s) − 2ψ_ε'(Γ g_s)Γ(g_s, L g_s))`, `g_s = P_{t-s} f`, with integrable integrands.
A hypothesis only, never an axiom. -/
structure StrongInterpolation : Prop where
  continuousOn : ∀ ε : ℝ, 0 < ε → ∀ (f h : T.A₀), 0 ≤ᵐ[T.μ] h.1 → ∀ t : ℝ≥0,
    ContinuousOn (T.strongPhi ε f h t) (Icc 0 (t : ℝ))
  hasDerivAt : ∀ ε : ℝ, 0 < ε → ∀ (f h : T.A₀), 0 ≤ᵐ[T.μ] h.1 → ∀ t : ℝ≥0, ∀ s ∈ Ioo (0 : ℝ) (t : ℝ),
    Integrable (fun x => T.Pt s.toNNReal h x *
      psiS ε (G T (T.Pt ((t : ℝ) - s).toNNReal f) (T.Pt ((t : ℝ) - s).toNNReal f) x)) T.μ ∧
    Integrable (fun x => T.Pt s.toNNReal h x * T.strongD ε (T.Pt ((t : ℝ) - s).toNNReal f) x) T.μ ∧
    HasDerivAt (T.strongPhi ε f h t)
      (∫ x, T.Pt s.toNNReal h x * T.strongD ε (T.Pt ((t : ℝ) - s).toNNReal f) x ∂T.μ) s

variable {T}

/-- **Integrated strong bound** (`ε`-form): `Φ_ε(0) ≤ e^{-ρt} Φ_ε(t)`. -/
theorem strong_integrated {ρ : ℝ} {n : ℝ≥0∞} (hCD : T.CD ρ n) (hρ : 0 ≤ ρ)
    (hS : T.StrongInterpolation) {ε : ℝ} (hε : 0 < ε) (f h : T.A₀) (hh : 0 ≤ᵐ[T.μ] h.1) (t : ℝ≥0) :
    T.strongPhi ε f h t 0 ≤ Real.exp (-ρ * t) * T.strongPhi ε f h t t := by
  set Φ := T.strongPhi ε f h t with hΦ
  set Ψ : ℝ → ℝ := fun s => Real.exp (-ρ * s) * Φ s with hΨ
  have hexp : Continuous fun s : ℝ => Real.exp (-ρ * s) := by fun_prop
  have hcont : ContinuousOn Ψ (Icc 0 (t : ℝ)) :=
    hexp.continuousOn.mul (hS.continuousOn ε hε f h hh t)
  have hder : ∀ s ∈ Ioo (0 : ℝ) (t : ℝ), ∃ d, HasDerivAt Ψ d s ∧ 0 ≤ d := by
    intro s hs
    obtain ⟨i1, i2, hd⟩ := hS.hasDerivAt ε hε f h hh t s hs
    set g := T.Pt ((t : ℝ) - s).toNNReal f with hg
    set k := T.Pt s.toNNReal h with hk
    have h1 : HasDerivAt (fun s : ℝ => Real.exp (-ρ * s)) (Real.exp (-ρ * s) * (-ρ)) s := by
      have := ((hasDerivAt_id s).const_mul (-ρ)).exp
      simpa using this
    refine ⟨_, h1.mul hd, ?_⟩
    have hk0 : 0 ≤ᵐ[T.μ] k := T.Pt_nonneg _ h hh
    have hge := strongD_ge T hCD hρ hε (T.Pt_mem_A ((t : ℝ) - s).toNNReal f)
    have hpos : 0 ≤ ∫ x, k x * (T.strongD ε g x - ρ * psiS ε (G T g g x)) ∂T.μ := by
      refine integral_nonneg_of_ae ?_
      filter_upwards [hk0, hge] with x h1 h2
      exact mul_nonneg h1 (by linarith)
    have e : ∫ x, k x * (T.strongD ε g x - ρ * psiS ε (G T g g x)) ∂T.μ =
        ∫ x, k x * T.strongD ε g x ∂T.μ - ρ * ∫ x, k x * psiS ε (G T g g x) ∂T.μ := by
      have : (fun x => k x * (T.strongD ε g x - ρ * psiS ε (G T g g x))) =
          fun x => k x * T.strongD ε g x - ρ * (k x * psiS ε (G T g g x)) := by
        funext x; ring
      rw [this, integral_sub i2 (i1.const_mul ρ), integral_const_mul]
    have hΦs : Φ s = ∫ x, k x * psiS ε (G T g g x) ∂T.μ := rfl
    have hpe := Real.exp_pos (-ρ * s)
    have : 0 ≤ Real.exp (-ρ * s) * (-ρ) * Φ s +
        Real.exp (-ρ * s) * (∫ x, k x * T.strongD ε g x ∂T.μ) := by
      rw [hΦs]
      have := mul_nonneg hpe.le (by linarith : 0 ≤ ∫ x, k x * T.strongD ε g x ∂T.μ -
          ρ * ∫ x, k x * psiS ε (G T g g x) ∂T.μ)
      nlinarith [this]
    simpa [hΨ, mul_comm, mul_left_comm, mul_assoc] using this
  have hmono : MonotoneOn Ψ (Icc 0 (t : ℝ)) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc _ _) hcont ?_ ?_
    · rw [interior_Icc]
      exact fun s hs => (let ⟨_, hd, _⟩ := hder s hs; hd.differentiableAt.differentiableWithinAt)
    · rw [interior_Icc]
      intro s hs
      obtain ⟨d, hd, hle⟩ := hder s hs
      rw [hd.deriv]; exact hle
  have := hmono (a := 0) (b := (t : ℝ)) (by simp) (by simp) t.2
  simpa [hΨ] using this

/-- `ψ_ε(Γ f)` as a test function (`ψ_ε(0) = 0`, `A₀` stable under smooth maps). -/
noncomputable def psiGamma (ε : ℝ) (hε : 0 < ε) (f : T.A₀) : T.A₀ :=
  ⟨fun x => psiS ε (G T f.1 f.1 x), by
    have hΓ : G T f.1 f.1 ∈ T.A₀ := T.ΓA_self_mem_A₀ f.2
    have := T.comp_mem 1 (fun z => psiS ε (z 0)) ((psiS_smooth hε).comp (contDiff_apply ℝ ℝ 0))
      (by simpa using psiS_zero hε) ![G T f.1 f.1] (by intro i; fin_cases i; simpa using hΓ)
    simpa using this⟩

lemma psiGamma_apply (ε : ℝ) (hε : 0 < ε) (f : T.A₀) (x : E) :
    (psiGamma ε hε f).1 x = psiS ε (G T f.1 f.1 x) := rfl

/-- **`ε`-form of the strong bound**: `ψ_ε(Γ(P_t f)) ≤ e^{-ρt} P_t(ψ_ε(Γ f))` a.e. -/
theorem strong_eps {ρ : ℝ} {n : ℝ≥0∞} (hCD : T.CD ρ n) (hρ : 0 ≤ ρ)
    (hS : T.StrongInterpolation) {ε : ℝ} (hε : 0 < ε) (f : T.A₀) (t : ℝ≥0) :
    (fun x => psiS ε (G T (T.Pt t f) (T.Pt t f) x)) ≤ᵐ[T.μ] fun x =>
      Real.exp (-ρ * t) * T.Pt t (psiGamma ε hε f) x := by
  set c : T.A₀ := psiGamma ε hε f with hc
  set w := T.Pt t c with hw
  set Γt : E → ℝ := fun x => psiS ε (G T (T.Pt t f) (T.Pt t f) x) with hΓt
  have hwA : w ∈ T.A := T.Pt_mem_A t c
  have hΓA : Γt ∈ T.A := T.comp_mem_A (psiS_smooth hε) (G_mem (T.Pt_mem_A t f) (T.Pt_mem_A t f))
  set u : E → ℝ := Real.exp (-ρ * t) • w - Γt with hu
  have huA : u ∈ T.A := T.A.sub_mem (T.A.smul_mem hwA _) hΓA
  have hpos : 0 ≤ᵐ[T.μ] u := by
    refine T.pos_detect u huA (fun h hh h0 => ?_)
    set h' : T.A₀ := ⟨h, hh⟩
    have key := strong_integrated hCD hρ hS hε f h' h0 t
    have eΦ0 : T.strongPhi ε f h' t 0 = ∫ x, h x * Γt x ∂T.μ := by
      unfold strongPhi
      refine integral_congr_ae ?_
      filter_upwards [T.Pt_zero h'] with x hx
      simp only [Real.toNNReal_zero, sub_zero, Real.toNNReal_coe, hΓt, hx]
      rfl
    have eΦt : T.strongPhi ε f h' t t = ∫ x, h x * w x ∂T.μ := by
      unfold strongPhi
      have hcg : ∀ᵐ x ∂T.μ, psiS ε (G T (T.Pt (((t : ℝ) - t).toNNReal) f)
          (T.Pt (((t : ℝ) - t).toNNReal) f) x) = c.1 x := by
        have := T.ΓA_congr_A (T.Pt_mem_A 0 f) (T.A₀_le f.1 f.2) (T.Pt_zero f)
        simp only [sub_self, Real.toNNReal_zero]
        filter_upwards [this] with x hx
        show psiS ε (T.toDiffusionTriple.ΓA (T.Pt 0 f) (T.Pt 0 f) x) = psiS ε (G T f.1 f.1 x)
        rw [hx]
      have : ∫ x, T.Pt (t : ℝ).toNNReal h' x * psiS ε (G T (T.Pt (((t : ℝ) - t).toNNReal) f)
          (T.Pt (((t : ℝ) - t).toNNReal) f) x) ∂T.μ = ∫ x, T.Pt t h' x * c.1 x ∂T.μ := by
        refine integral_congr_ae ?_
        filter_upwards [hcg] with x hx
        simp only [Real.toNNReal_coe, hx]
      rw [this, integral_Pt_mul T t h' c]
    rw [eΦ0, eΦt] at key
    have i1 : Integrable (fun x => h x * w x) T.μ :=
      DiffusionTriple.integrable_of_mem T.toDiffusionTriple (T.ideal w hwA h hh)
    have i2 : Integrable (fun x => h x * Γt x) T.μ :=
      DiffusionTriple.integrable_of_mem T.toDiffusionTriple (T.ideal Γt hΓA h hh)
    have e : (fun x => h x * u x) = fun x => Real.exp (-ρ * t) * (h x * w x) - h x * Γt x := by
      funext x; simp only [hu, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [e, integral_sub (i1.const_mul _) i2, integral_const_mul]
    linarith
  filter_upwards [hpos] with x hx
  simp only [hu, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hx
  show Γt x ≤ _
  linarith

lemma memLp_sqrtΓ (f : T.A₀) : MemLp (fun x => Real.sqrt (G T f.1 f.1 x)) 2 T.μ := by
  have hΓ : G T f.1 f.1 ∈ T.A₀ := T.ΓA_self_mem_A₀ f.2
  have hm : Measurable (G T f.1 f.1) := T.toDiffusionTriple.measurable _ hΓ
  refine (memLp_two_iff_integrable_sq (hm.sqrt.aestronglyMeasurable)).2 ?_
  refine (DiffusionTriple.integrable_of_mem T.toDiffusionTriple hΓ).congr ?_
  filter_upwards [T.ΓA_nonneg f.1 (T.A₀_le f.1 f.2)] with x hx
  exact (Real.sq_sqrt hx).symm

/-- the `L²`-class of `√Γ(f)` (`Γ(f) ∈ 𝒜₀ ⊂ L¹`, so `√Γ(f) ∈ L²`). -/
noncomputable def sqrtΓcls (f : T.A₀) : Lp ℝ 2 T.μ := (memLp_sqrtΓ f).toLp _

lemma coeFn_sqrtΓcls (f : T.A₀) :
    (T.sqrtΓcls f : E → ℝ) =ᵐ[T.μ] fun x => Real.sqrt (G T f.1 f.1 x) := MemLp.coeFn_toLp _

lemma psiS_le_sqrt {ε r : ℝ} (hε : 0 < ε) (hr : 0 ≤ r) : psiS ε r ≤ Real.sqrt r := by
  rw [psiS_eq hε (by nlinarith [sq_pos_of_pos hε])]
  have : Real.sqrt (r + ε ^ 2) ≤ Real.sqrt r + ε := by
    apply Real.sqrt_le_iff.2
    refine ⟨by positivity, ?_⟩
    nlinarith [Real.sq_sqrt hr, Real.sqrt_nonneg r]
  linarith

lemma tendsto_psiS_sqrt {r : ℝ} (hr : 0 ≤ r) :
    Tendsto (fun n : ℕ => psiS (1 / ((n : ℝ) + 1)) r) atTop (𝓝 (Real.sqrt r)) := by
  have hε : ∀ n : ℕ, 0 < 1 / ((n : ℝ) + 1) := fun n => by positivity
  have e : ∀ n : ℕ, psiS (1 / ((n : ℝ) + 1)) r =
      Real.sqrt (r + (1 / ((n : ℝ) + 1)) ^ 2) - 1 / ((n : ℝ) + 1) := fun n =>
    psiS_eq (hε n) (by nlinarith [sq_pos_of_pos (hε n)])
  simp only [e]
  have h1 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have h2 : Tendsto (fun n : ℕ => Real.sqrt (r + (1 / ((n : ℝ) + 1)) ^ 2)) atTop
      (𝓝 (Real.sqrt (r + 0 ^ 2))) :=
    (Real.continuous_sqrt.tendsto _).comp ((tendsto_const_nhds.add (h1.pow 2)))
  have := h2.sub h1
  simpa using this

/-- From the `ε`-forms to the strong bound: if `ψ_ε(Γ(P_t f)) ≤ e^{-ρt} P_t(ψ_ε(Γ f))` a.e. for all
`ε = 1/(n+1)`, then `√Γ(P_t f) ≤ e^{-ρt} P_t(√Γ f)` a.e. (positivity of `P_t`, `ψ_ε ↑ √`). -/
theorem strong_of_eps {ρ : ℝ} (f : T.A₀) (t : ℝ≥0)
    (heps : ∀ n : ℕ, (fun x => psiS (1 / ((n : ℝ) + 1)) (G T (T.Pt t f) (T.Pt t f) x)) ≤ᵐ[T.μ]
      fun x => Real.exp (-ρ * t) * T.Pt t (psiGamma (1 / ((n : ℝ) + 1)) (by positivity) f) x) :
    ∀ᵐ x ∂T.μ, Real.sqrt (G T (T.Pt t f) (T.Pt t f) x) ≤
      Real.exp (-ρ * t) * (T.toDiffusionTriple.semigroup t (T.sqrtΓcls f) : Lp ℝ 2 T.μ) x := by
  have hε : ∀ n : ℕ, 0 < 1 / ((n : ℝ) + 1) := fun n => by positivity
  have h1 : ∀ᵐ x ∂T.μ, ∀ n : ℕ, psiS (1 / ((n : ℝ) + 1)) (G T (T.Pt t f) (T.Pt t f) x) ≤
      Real.exp (-ρ * t) * (T.toDiffusionTriple.semigroup t (T.sqrtΓcls f) : Lp ℝ 2 T.μ) x := by
    rw [ae_all_iff]
    intro n
    have a1 := heps n
    have a2 : (T.toDiffusionTriple.cls (psiGamma (1 / ((n : ℝ) + 1)) (hε n) f) : E → ℝ) ≤ᵐ[T.μ]
        (T.sqrtΓcls f : E → ℝ) := by
      filter_upwards [DiffusionTriple.coeFn_cls T.toDiffusionTriple (psiGamma (1 / ((n : ℝ) + 1)) (hε n) f),
        coeFn_sqrtΓcls f, T.ΓA_nonneg f.1 (T.A₀_le f.1 f.2)] with x h2 h3 h4
      rw [h2, h3]
      exact psiS_le_sqrt (hε n) h4
    have a3 := T.toDiffusionTriple.semigroup_mono t a2
    filter_upwards [a1, a3, T.Pt_ae t (psiGamma (1 / ((n : ℝ) + 1)) (hε n) f)] with x b1 b3 b4
    rw [← b4] at b1
    have := mul_le_mul_of_nonneg_left b3 (Real.exp_pos (-ρ * t)).le
    exact b1.trans this
  filter_upwards [h1, (T.ΓA_nonneg _ (T.Pt_mem_A t f))] with x b1 b2
  have hr : 0 ≤ G T (T.Pt t f) (T.Pt t f) x := b2
  exact le_of_tendsto' (tendsto_psiS_sqrt hr) b1

/-- **Strong gradient bound** (BGL Thm 3.3.18), conditional on `StrongInterpolation`:
for `f ∈ 𝒜₀`, `t ≥ 0`, `√Γ(P_t f) ≤ e^{-ρt} P_t(√Γ f)` a.e., under `CD(ρ,n)`, `ρ ≥ 0`. -/
theorem strong_gradient_bound {ρ : ℝ} {n : ℝ≥0∞} (hCD : T.CD ρ n) (hρ : 0 ≤ ρ)
    (hS : T.StrongInterpolation) (f : T.A₀) (t : ℝ≥0) :
    ∀ᵐ x ∂T.μ, Real.sqrt (G T (T.Pt t f) (T.Pt t f) x) ≤
      Real.exp (-ρ * t) * (T.toDiffusionTriple.semigroup t (T.sqrtΓcls f) : Lp ℝ 2 T.μ) x :=
  strong_of_eps f t fun n => strong_eps hCD hρ hS (by positivity) f t

end FullTriple

end MarkovTriple.BGL
