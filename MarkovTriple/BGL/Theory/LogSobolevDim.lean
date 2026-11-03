import Mathlib
import MarkovTriple.BGL.Theory.LogSobolevMain
import MarkovTriple.BGL.Theory.LogSobolevDimChain
import MarkovTriple.BGL.Theory.Compact.Consequences

/-!
# Logarithmic Sobolev inequality under `CD(ρ,n)`, `1 < n < ∞` (BGL Thm 5.7.4)

Source: Bakry-Gentil-Ledoux, Sect. 5.7, pp. 268-272: Prop. 5.7.1 (the `n = ∞` case, `Theory/LogSobolevMain.lean`),
Prop. 5.7.3 (criterion (5.7.5), "should be used for `P_t f`", p. 270), Thm 5.7.4 and its proof (5.7.6)-(5.7.12).

**Theorem 5.7.4.** Under `CD(ρ,n)`, `ρ > 0`, `n > 1` the triple satisfies `LS(C)` with `C = (n-1)/(ρ n)`.

Route (the book's, as used here): the criterion (5.7.5) of Prop. 5.7.3, `∫ f Γ₂(log f) ≥ C⁻¹ ∫ f Γ(log f)`, enters in the form of the
Fisher-information decay `I' ≤ -2κ I` inside the Prop. 5.7.1 argument (`BE.ent_le_of_decay`, Gronwall, `ε → 0`); audit R14 (documentation).
The criterion reads
(for `f = P_t f₀`, p. 270), obtained by (5.7.6)-(5.7.12) as `∫ e^g Γ₂(g) ≥ ρ n/(n-1) ∫ e^g Γ(g)`
(`Theory/LogSobolevDimChain.lean`, `integral_exp_Γ₂_ge'`, for `g ∈ 𝒜₀`).  In the proof of Prop. 5.7.1 the
decay `I' ≤ -2ρ I` (from `CD(ρ,∞)`) is replaced by `I' ≤ -2κ I`, `κ = ρ n/(n-1)`, and everything else
(Gronwall, the limit `e(s) → m log m`, `φ = f²`, `ε → 0`) is the proof of `logSobolev_of_CD_infty`.

**Named analytic input** (`FullTriple.FiniteDimInterpolation T κ`, a `Prop`, never an axiom): exactly the two
facts the book uses without proof.  (i) p. 270: for `t > 0`, `P_t f` is in `𝒜` and bounded together with
`Γ(P_t f)` and `L P_t f`; (ii) p. 272: by Prop. 3.3.6 / Lemma 3.3.16 inequality (5.7.12), proved for
`e^g`, `g ∈ 𝒜₀`, extends to functions `f ∈ 𝒜` bounded together with `Γ(f)`, `Lf`.
(`logSobolev_of_CD_dim` also takes `EntropyInterpolation`, as in the `n = ∞` case.)  Both are PROVED for every
compact triple (`CompactTriple.finiteDimInterpolation`: `𝒜 = 𝒜₀`), which gives unconditional
`compact_logSobolev_dim`.
-/

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal InnerProductSpace

namespace MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E]

/-- The book's log-Sobolev constant `(n-1)/(ρ n) = (1 - n⁻¹)/ρ` of Thm 5.7.4 (`n = ∞`: `1/ρ`, Prop. 5.7.1). -/
noncomputable def dimLSConst (ρ : ℝ) (n : ℝ≥0∞) : ℝ := (1 - (n⁻¹).toReal) / ρ

theorem dimLSConst_top (ρ : ℝ) : dimLSConst ρ ⊤ = 1 / ρ := by simp [dimLSConst]

theorem dimLSConst_lt {ρ : ℝ} (hρ : 0 < ρ) {n : ℝ≥0∞} (hn1 : 1 ≤ n) (hn : n ≠ ⊤) :
    dimLSConst ρ n < 1 / ρ := by
  have hn0 : n ≠ 0 := (lt_of_lt_of_le one_pos hn1).ne'
  have h : 0 < (n⁻¹).toReal :=
    ENNReal.toReal_pos (ENNReal.inv_ne_zero.2 hn) (ENNReal.inv_ne_top.2 hn0)
  unfold dimLSConst
  exact div_lt_div_of_pos_right (by linarith) hρ

/-- `dimLSConst ρ n = 1/(ρ m/(m-1))`, `m = n` finite, `n > 1`. -/
theorem dimLSConst_eq {ρ : ℝ} {n : ℝ≥0∞} (hn1 : 1 < n) (hn : n ≠ ⊤) :
    dimLSConst ρ n = 1 / (ρ * (n.toReal / (n.toReal - 1))) := by
  have hm1 : 1 < n.toReal := by
    have := (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hn).2 hn1
    simpa using this
  unfold dimLSConst
  rw [ENNReal.toReal_inv]
  have : n.toReal - 1 ≠ 0 := by linarith
  have h0 : n.toReal ≠ 0 := by linarith
  by_cases hρ : ρ = 0
  · simp [hρ]
  · field_simp

theorem dimLSConst_tendsto (ρ : ℝ) :
    Tendsto (fun k : ℕ => dimLSConst ρ (k : ℝ≥0∞)) atTop (𝓝 (1 / ρ)) := by
  unfold dimLSConst
  have h : Tendsto (fun k : ℕ => (((k : ℝ≥0∞))⁻¹).toReal) atTop (𝓝 0) := by
    simp only [ENNReal.toReal_inv, ENNReal.toReal_natCast]
    exact tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have := ((tendsto_const_nhds (x := (1 : ℝ))).sub h).div_const ρ
  simpa using this

namespace FullTriple

variable (T : FullTriple E)

/-- **Analytic input of Thm 5.7.4 for `n < ∞`** (named hypothesis, not an axiom).

* `bdd` (BGL p. 270): for `φ ∈ 𝒜₀`, `φ ≥ 0`, `ε > 0`, `s > 0`, `g_s = ε + P_s φ` is bounded together with
  `Γ(g_s)` and `L g_s` ("for `t > 0`, `P_t f` is in `𝒜` and moreover bounded together with `Γ(P_t f)` and `L P_t f`");
* `ext` (BGL p. 272, after (5.7.12)): "by Prop. 3.3.6 and Lemma 3.3.16, (5.7.12) extends to functions `f ∈ 𝒜` which are
  bounded, together with `Γ(f)` and `Lf`", in the form used by the semigroup argument:
  for `f ∈ 𝒜`, `ε ≤ f ≤ ε + M` a.e., `Γ(f)`, `|Lf| ≤ B` a.e., a smooth cutoff `Λ` of `log` on `[ε, ε+M]`
  (`BE.Cut`, so `Λ∘f = log f`) and integrability of `fΓ₂(Λ∘f)`, `fΓ(Λ∘f)`:
  `κ ∫ f Γ(Λ∘f) ≤ ∫ f Γ₂(Λ∘f)`, i.e. `∫ f Γ₂(log f) ≥ κ ∫ f Γ(log f)` with `κ = ρ n/(n-1)`. -/
structure FiniteDimInterpolation (κ : ℝ) : Prop where
  bdd : ∀ (φ : T.A₀) (ε : ℝ), 0 < ε → 0 ≤ᵐ[T.μ] φ.1 → ∀ s : ℝ, 0 < s →
    ∃ B : ℝ, (∀ᵐ x ∂T.μ, T.toDiffusionTriple.ΓA (T.entG φ ε s) (T.entG φ ε s) x ≤ B) ∧
      ∀ᵐ x ∂T.μ, |T.L (T.entG φ ε s) x| ≤ B
  ext : ∀ (ε M : ℝ), 0 < ε → 0 < M → ∀ f ∈ T.A, (∀ᵐ x ∂T.μ, f x ∈ Icc ε (ε + M)) →
    ∀ B : ℝ, (∀ᵐ x ∂T.μ, T.toDiffusionTriple.ΓA f f x ≤ B) → (∀ᵐ x ∂T.μ, |T.L f x| ≤ B) →
    ∀ C : BE.Cut ε M,
    Integrable (fun x => f x * T.toDiffusionTriple.Γ₂ (fun y => C.Λ (f y)) (fun y => C.Λ (f y)) x) T.μ →
    Integrable (fun x => f x * T.toDiffusionTriple.ΓA (fun y => C.Λ (f y)) (fun y => C.Λ (f y)) x) T.μ →
    κ * ∫ x, f x * T.toDiffusionTriple.ΓA (fun y => C.Λ (f y)) (fun y => C.Λ (f y)) x ∂T.μ ≤
      ∫ x, f x * T.toDiffusionTriple.Γ₂ (fun y => C.Λ (f y)) (fun y => C.Λ (f y)) x ∂T.μ

/-- **Entropy-Fisher inequality with the improved constant** (proof of BGL Prop. 5.7.1 with the decay
`I' ≤ -2κ I`, `κ = ρ n/(n-1)`, obtained from (5.7.12)): `Ent(ε + φ) ≤ I(ε+φ)/(2κ)`.
Here `ρ > 0`, `CD ρ n` serve only the limit `e(s) → m log m` (Poincaré). -/
theorem ent_le_fisher_dim [IsProbabilityMeasure T.μ] (hE : T.EntropyInterpolation) {ρ κ : ℝ}
    {n : ℝ≥0∞} (hρ : 0 < ρ) (hCD : T.CD ρ n) (hκ : 0 < κ) (hD : T.FiniteDimInterpolation κ)
    (φ : T.A₀) (h0 : 0 ≤ᵐ[T.μ] φ.1) {ε : ℝ} (hε : 0 < ε) :
    Ent T.μ (fun x => ε + φ.1 x) ≤
      (∫ x, T.toDiffusionTriple.ΓA φ.1 φ.1 x / (ε + φ.1 x) ∂T.μ) / (2 * κ) := by
  obtain ⟨C0, hC0⟩ := T.bounded φ.1 φ.2
  set M : ℝ := max C0 1 with hMdef
  have hM : 0 < M := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hφM : ∀ x, φ.1 x ≤ M := fun x => (le_abs_self _).trans ((hC0 x).trans (le_max_left _ _))
  obtain ⟨C⟩ := BE.exists_cut hε hM.le
  set m : ℝ := ε + ∫ x, φ.1 x ∂T.μ with hm
  have key := BE.ent_le_of_decay (e := fun s => T.entE φ ε s - m * Real.log m)
    (q := fun s => -T.entI φ ε s) hκ
    ((hE.continuousOn_E φ ε hε h0).sub continuousOn_const)
    ((hE.continuousOn_I φ ε hε h0).neg)
    (fun s hs => (hE.hasDerivAt_E φ ε hε h0 s hs).sub_const _)
    (fun s hs => by
      obtain ⟨i1, i2, hd⟩ := hE.hasDerivAt_I φ ε M hε hM h0 hφM C s hs
      refine ⟨-(-2 * T.entJ C.Λ φ ε s), hd.neg, ?_⟩
      have hAg := entG_mem_A T φ ε s
      obtain ⟨B, hB1, hB2⟩ := hD.bdd φ ε hε h0 s hs
      have hint : κ * ∫ x, T.entG φ ε s x * T.toDiffusionTriple.ΓA (fun y => C.Λ (T.entG φ ε s y))
          (fun y => C.Λ (T.entG φ ε s y)) x ∂T.μ ≤ T.entJ C.Λ φ ε s :=
        hD.ext ε M hε hM _ hAg (entG_range T φ hε hM h0 hφM s) B hB1 hB2 C i1 i2
      rw [← entI_eq T φ hε hM h0 hφM C s] at hint
      show -2 * κ * -T.entI φ ε s ≤ -(-2 * T.entJ C.Λ φ ε s)
      nlinarith [hint])
    (by
      have := (tendsto_entE T hρ hCD φ hε h0).sub_const (m * Real.log m)
      simpa [hm] using this)
  have hφi : Integrable φ.1 T.μ := DiffusionTriple.integrable_of_mem T.toDiffusionTriple φ.2
  have hint : (∫ x, (ε + φ.1 x) ∂T.μ) = m := by
    rw [integral_add (integrable_const ε) hφi]; simp [hm]
  have eE0 : T.entE φ ε 0 = ∫ x, (ε + φ.1 x) * Real.log (ε + φ.1 x) ∂T.μ := by
    unfold entE
    refine integral_congr_ae ?_
    filter_upwards [T.Pt_zero φ] with x hx
    simp only [entG, Real.toNNReal_zero, hx]
  have hEnt : Ent T.μ (fun x => ε + φ.1 x) = T.entE φ ε 0 - m * Real.log m := by
    unfold Ent
    rw [eE0, hint]
  have eI0 : T.entI φ ε 0 = ∫ x, T.toDiffusionTriple.ΓA φ.1 φ.1 x / (ε + φ.1 x) ∂T.μ := by
    unfold entI
    refine integral_congr_ae ?_
    filter_upwards [T.Pt_zero φ, ΓA_shift T ε (T.Pt_mem_A (0 : ℝ).toNNReal φ),
      T.ΓA_congr_A (T.Pt_mem_A (0 : ℝ).toNNReal φ) (T.A₀_le φ.1 φ.2) (by simpa using T.Pt_zero φ)]
      with x hx h1 h2
    have e : T.entG φ ε 0 = fun x => ε + T.Pt 0 φ x := by funext x; simp [entG]
    simp only [Real.toNNReal_zero] at h1 h2
    rw [e, h1, h2]
    show _ / (ε + T.Pt 0 φ x) = _
    rw [hx]
  rw [hEnt]
  have := key
  simp only [neg_neg] at this
  rw [eI0] at this
  exact this

/-- The bound for `ε + f²`: `Ent(ε + f²) ≤ (2/κ) ℰ(f)`. -/
theorem ent_sq_add_le_dim [IsProbabilityMeasure T.μ] (hE : T.EntropyInterpolation) {ρ κ : ℝ}
    {n : ℝ≥0∞} (hρ : 0 < ρ) (hCD : T.CD ρ n) (hκ : 0 < κ) (hD : T.FiniteDimInterpolation κ)
    {f : E → ℝ} (hf : f ∈ T.A₀) {ε : ℝ} (hε : 0 < ε) :
    Ent T.μ (fun x => ε + f x ^ 2) ≤ 2 * (1 / κ) * ∫ x, T.Γ f f x ∂T.μ := by
  set φ : T.A₀ := ⟨fun x => f x ^ 2, sq_mem_A₀ T hf⟩ with hφ
  have h := ent_le_fisher_dim T hE hρ hCD hκ hD φ (Eventually.of_forall fun x => sq_nonneg (f x)) hε
  have hfA : f ∈ T.A := T.A₀_le f hf
  have hΓi : Integrable (fun x => T.toDiffusionTriple.ΓA f f x) T.μ :=
    DiffusionTriple.integrable_of_mem T.toDiffusionTriple (ΓA_self_mem_A₀ T hf)
  have hint : (∫ x, T.toDiffusionTriple.ΓA φ.1 φ.1 x / (ε + φ.1 x) ∂T.μ) ≤
      4 * ∫ x, T.toDiffusionTriple.ΓA f f x ∂T.μ := by
    rw [← integral_const_mul]
    have hc : (∫ x, T.toDiffusionTriple.ΓA φ.1 φ.1 x / (ε + φ.1 x) ∂T.μ) =
        ∫ x, 4 * f x ^ 2 * T.toDiffusionTriple.ΓA f f x / (ε + f x ^ 2) ∂T.μ := by
      refine integral_congr_ae ?_
      filter_upwards [ΓA_sq T hfA] with x hx
      simp only [hφ] at hx ⊢
      rw [hx]
    rw [hc]
    refine integral_mono_of_nonneg ?_ (hΓi.const_mul 4) ?_
    · filter_upwards [T.ΓA_nonneg f hfA] with x hx
      simp only [Pi.zero_apply]
      have : 0 ≤ T.toDiffusionTriple.ΓA f f x := hx
      positivity
    · filter_upwards [T.ΓA_nonneg f hfA] with x hx
      have hΓ0 : 0 ≤ T.toDiffusionTriple.ΓA f f x := hx
      have hpos : 0 < ε + f x ^ 2 := by positivity
      rw [div_le_iff₀ hpos]
      nlinarith [sq_nonneg (f x), mul_nonneg hΓ0 hε.le]
  refine h.trans ?_
  have h2κ : 0 < 2 * κ := by positivity
  rw [div_le_iff₀ h2κ]
  have e : ∫ x, T.Γ f f x ∂T.μ = ∫ x, T.toDiffusionTriple.ΓA f f x ∂T.μ :=
    (integral_congr_ae (DiffusionTriple.ΓA_ae_eq T.toDiffusionTriple hf hf)).symm
  rw [e]
  have : 2 * (1 / κ) * (∫ x, T.toDiffusionTriple.ΓA f f x ∂T.μ) * (2 * κ) =
      4 * ∫ x, T.toDiffusionTriple.ΓA f f x ∂T.μ := by
    field_simp; ring
  rw [this]; exact hint

/-- `LS(1/κ, 0)` from `CD(ρ,n)` (`ρ > 0`) and `FiniteDimInterpolation T κ`, `κ > 0`.
Note (audit R14-3): `κ` is arbitrary here; for `κ > ρ n/(n-1)` the structure is false on nontrivial triples, so the statement is then
vacuous.  The headline `logSobolev_of_CD_dim` pins `κ = ρ n/(n-1)`. -/
theorem logSobolev_of_finiteDim [IsProbabilityMeasure T.μ] (hE : T.EntropyInterpolation)
    {ρ κ : ℝ} {n : ℝ≥0∞} (hρ : 0 < ρ) (hCD : T.CD ρ n) (hκ : 0 < κ)
    (hD : T.FiniteDimInterpolation κ) : T.toDiffusionTriple.LS (1 / κ) 0 := by
  refine ⟨inferInstance, by positivity, le_refl _, fun f hf => ?_⟩
  have hφ := sq_mem_A₀ T hf
  have h2 : MemLp (fun x => f x ^ 2) 2 T.μ := DiffusionTriple.memLp2 T.toDiffusionTriple hφ
  have hlim := BE.tendsto_Ent_add T.μ h2
  have hle : Ent T.μ (fun x => f x ^ 2) ≤ 2 * (1 / κ) * ∫ x, T.Γ f f x ∂T.μ := by
    refine le_of_tendsto hlim ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact ent_sq_add_le_dim T hE hρ hCD hκ hD hf hε
  simpa [energy, dirichletForm] using hle

/-- **BGL Thm 5.7.4** (p. 270), conditional on `EntropyInterpolation` and `FiniteDimInterpolation`:
`CD(ρ,n)`, `ρ > 0`, `1 < n < ∞`, `μ` a probability measure ⇒ `LS(C, 0)`, `C = (n-1)/(ρ n)`
(on `𝒜₀`, i.e. `Ent(f²) ≤ 2C ℰ(f)`). -/
theorem logSobolev_of_CD_dim [IsProbabilityMeasure T.μ] (hE : T.EntropyInterpolation) {ρ : ℝ}
    {n : ℝ≥0∞} (hρ : 0 < ρ) (hn1 : 1 < n) (hn : n ≠ ⊤) (hCD : T.CD ρ n)
    (hD : T.FiniteDimInterpolation (ρ * (n.toReal / (n.toReal - 1)))) :
    T.toDiffusionTriple.LS (dimLSConst ρ n) 0 := by
  have hm1 : 1 < n.toReal := by
    have := (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hn).2 hn1
    simpa using this
  have hκ : 0 < ρ * (n.toReal / (n.toReal - 1)) := by
    have : 0 < n.toReal - 1 := by linarith
    positivity
  rw [dimLSConst_eq hn1 hn]
  exact logSobolev_of_finiteDim T hE hρ hCD hκ hD

end FullTriple

/-! ### Compact triples: both inputs are theorems -/

namespace CompactTriple

variable (C : CompactTriple E)

/-- **`FiniteDimInterpolation` holds on every compact triple** (`𝒜 = 𝒜₀`): `bdd` from boundedness of `𝒜₀`,
`ext` from (5.7.12) for `e^g`, `g = Λ∘f ∈ 𝒜₀` (`FullTriple.integral_exp_Γ₂_ge'`), `e^{Λ∘f} = f`. -/
theorem finiteDimInterpolation {ρ : ℝ} {n : ℝ≥0∞} (hCD : C.toFullTriple.CD ρ n) (hn1 : 1 < n)
    (hn : n ≠ ⊤) :
    C.toFullTriple.FiniteDimInterpolation (ρ * (n.toReal / (n.toReal - 1))) := by
  refine ⟨?_, ?_⟩
  · intro φ ε hε h0 s hs
    have hg0 : C.toFullTriple.entG φ ε s ∈ C.A₀ := C.entG_mem φ ε s
    obtain ⟨C1, hC1⟩ := C.toFullTriple.bounded _
      (FullTriple.ΓA_self_mem_A₀ C.toFullTriple hg0)
    obtain ⟨C2, hC2⟩ := C.toFullTriple.bounded _ (C.toFullTriple.L_mem _ hg0)
    refine ⟨max C1 C2, Eventually.of_forall fun x => ?_, Eventually.of_forall fun x => ?_⟩
    · exact (le_abs_self _).trans ((hC1 x).trans (le_max_left _ _))
    · exact (hC2 x).trans (le_max_right _ _)
  · intro ε M hε hM f hf hrange B _ _ Cut _ _
    have hfA0 : f ∈ C.A₀ := (C.A_eq f).1 hf
    have hg : (fun y => Cut.Λ (f y)) ∈ C.A := FullTriple.comp_mem_A C.toFullTriple Cut.hΛ hf
    have hg0 : (fun y => Cut.Λ (f y)) ∈ C.A₀ := (C.A_eq _).1 hg
    have he : (fun x => Real.exp ((fun y => Cut.Λ (f y)) x / 2)) ∈ C.A₀ := by
      have hψ : ContDiff ℝ (⊤ : ℕ∞) (fun r : ℝ => Real.exp (Cut.Λ r / 2)) :=
        Real.contDiff_exp.comp (Cut.hΛ.div_const 2)
      exact (C.A_eq _).1 (FullTriple.comp_mem_A C.toFullTriple hψ hf)
    have h := FullTriple.integral_exp_Γ₂_ge' (T := C.toFullTriple) hCD hn1 hn hg0 he
    have hexp : ∀ᵐ x ∂C.μ, Real.exp (Cut.Λ (f x)) = f x := by
      filter_upwards [hrange] with x hx
      rw [Cut.Λ_eq hx]
      exact Real.exp_log (lt_of_lt_of_le hε hx.1)
    have e1 : ∫ x, Real.exp (Cut.Λ (f x)) * C.toFullTriple.G (fun y => Cut.Λ (f y))
        (fun y => Cut.Λ (f y)) x ∂C.μ =
        ∫ x, f x * C.toDiffusionTriple.ΓA (fun y => Cut.Λ (f y)) (fun y => Cut.Λ (f y)) x ∂C.μ := by
      refine integral_congr_ae ?_
      filter_upwards [hexp] with x hx
      rw [hx]
    have e2 : ∫ x, Real.exp (Cut.Λ (f x)) * C.toDiffusionTriple.Γ₂ (fun y => Cut.Λ (f y))
        (fun y => Cut.Λ (f y)) x ∂C.μ =
        ∫ x, f x * C.toDiffusionTriple.Γ₂ (fun y => Cut.Λ (f y)) (fun y => Cut.Λ (f y)) x ∂C.μ := by
      refine integral_congr_ae ?_
      filter_upwards [hexp] with x hx
      rw [hx]
    rw [e2] at h
    rw [e1] at h
    exact h

/-- **BGL Thm 5.7.4 on every compact triple, unconditionally**: `CD(ρ,n)`, `ρ > 0`, `1 < n < ∞` ⇒
`LS((n-1)/(ρ n), 0)`. -/
theorem compact_logSobolev_dim {ρ : ℝ} {n : ℝ≥0∞} (hρ : 0 < ρ) (hn1 : 1 < n) (hn : n ≠ ⊤)
    (hCD : C.toFullTriple.CD ρ n) : C.toDiffusionTriple.LS (dimLSConst ρ n) 0 :=
  FullTriple.logSobolev_of_CD_dim C.toFullTriple C.entropyInterpolation hρ hn1 hn hCD
    (C.finiteDimInterpolation hCD hn1 hn)

end CompactTriple

end MarkovTriple.BGL
