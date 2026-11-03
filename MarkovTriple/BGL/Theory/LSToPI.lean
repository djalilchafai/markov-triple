import Mathlib
import MarkovTriple.BGL.Theory.GammaCalculus
import MarkovTriple.BGL.Calculus.Density
import MarkovTriple.BGL.Frozen.CompactTriple

/-!
# The tight logarithmic Sobolev inequality `LS(C)` implies the Poincaré inequality `P(C)` (BGL Prop. 5.1.3)

Source: Bakry-Gentil-Ledoux, p. 238-239, **Proposition 5.1.3** (first assertion): "A tight logarithmic Sobolev inequality
`LS(C)` implies a Poincaré inequality `P(C)`."  Proof (book): apply `LS(C)` to `f = 1 + ε g`, `∫ g dμ = 0`; "as `ε → 0`, it is
not difficult to check by a Taylor expansion that `Ent_μ(f²) = 2ε² ∫ g² dμ + o(ε²)` while, clearly, `ℰ(f) = ε² ℰ(g)`.  It follows
that `2 ∫ g² ≤ 2 C ℰ(g)`."

* `DiffusionTriple.PI_of_LS` (needs `1 ∈ 𝒜₀`, see below): `T.LS C 0 → T.PI C`.
* The Taylor expansion is replaced by the one-sided estimate
  `(1+t)² log (1+t)² ≥ 2t + 3t² - 8|t|³` for `|t| ≤ 1/2` (`log_sq_lower`, from Mathlib's `Real.abs_log_sub_add_sum_range_le`)
  and `x log x ≤ x (x-1)`; only the lower bound for `Ent` is needed, since `LS` bounds `Ent` from above.

**Hypothesis `1 ∈ 𝒜₀`.**  The book works on `𝒟(ℰ)`, which contains the constants for a probability measure.  The library's `LS`/`PI`
are stated on the test class `𝒜₀` of the triple, which is a *non-unital* algebra in general (Lebesgue, OU...).  We therefore assume
`(fun _ => 1) ∈ T.A₀` (automatic for `CompactTriple`, where `𝒜 = 𝒜₀` is unital: `CompactTriple.PI_of_LS`).  For non-unital `𝒜₀` the
implication would need the extension to `𝒟(ℰ)` (`LS.extend`) and `1 ∈ 𝒟(ℰ)`; this is NOT formalized here.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace MarkovTriple.BGL

/-- elementary lower bound: `(1+t)² log (1+t)² ≥ 2t + 3t² - 8|t|³` for `|t| ≤ 1/2` (the second-order Taylor expansion
`(1+t)² log (1+t)² = 2t + 3t² + O(t³)` used in the proof of BGL Prop. 5.1.3, one-sided). -/
lemma log_sq_lower (t : ℝ) (ht : |t| ≤ 1 / 2) :
    2 * t + 3 * t ^ 2 - 8 * |t| ^ 3 ≤ (1 + t) ^ 2 * Real.log ((1 + t) ^ 2) := by
  have hs0 : 0 ≤ |t| := abs_nonneg t
  have hlt : |-t| < 1 := by rw [abs_neg]; linarith
  have h := Real.abs_log_sub_add_sum_range_le hlt 3
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, abs_neg] at h
  have e : (1 : ℝ) - -t = 1 + t := by ring
  rw [e] at h
  have h4 : |t| ^ (3 + 1) / (1 - |t|) ≤ 2 * t ^ 4 := by
    rw [div_le_iff₀ (by linarith)]
    have : |t| ^ (3 + 1) = t ^ 4 := by
      rw [show (3 + 1 : ℕ) = 4 from rfl]
      have := pow_abs t 4
      rw [this]; exact abs_of_nonneg (by positivity)
    rw [this]
    have : 0 ≤ t ^ 4 := by positivity
    nlinarith
  have hl := (abs_le.1 (h.trans h4)).1
  have hlog : t - t ^ 2 / 2 + t ^ 3 / 3 - 2 * t ^ 4 ≤ Real.log (1 + t) := by
    norm_num at hl
    nlinarith [hl]
  rw [Real.log_pow]
  push_cast
  have hq : 0 ≤ (1 + t) ^ 2 := sq_nonneg _
  have h5 : (1 + t) ^ 2 * (2 * (t - t ^ 2 / 2 + t ^ 3 / 3 - 2 * t ^ 4)) ≤
      (1 + t) ^ 2 * (2 * Real.log (1 + t)) :=
    mul_le_mul_of_nonneg_left (by linarith) hq
  refine le_trans ?_ h5
  set s := |t| with hs
  have h3 : -s ^ 3 ≤ t ^ 3 := by
    have h' : -s ≤ t := neg_abs_le t
    have h'' : t ≤ s := le_abs_self t
    nlinarith [sq_nonneg t, sq_abs t, sq_nonneg s, mul_nonneg hs0 (sq_nonneg t)]
  have h5' : t ^ 5 ≤ s ^ 5 := by
    have : t ^ 5 ≤ |t ^ 5| := le_abs_self _
    rwa [abs_pow] at this
  have h4' : t ^ 4 = s ^ 4 := by
    show t ^ 4 = |t| ^ 4
    rw [pow_abs, abs_of_nonneg (by positivity)]
  have h6' : t ^ 6 = s ^ 6 := by
    show t ^ 6 = |t| ^ 6
    rw [pow_abs, abs_of_nonneg (by positivity)]
  have hP : (1 + t) ^ 2 * (2 * (t - t ^ 2 / 2 + t ^ 3 / 3 - 2 * t ^ 4)) - (2 * t + 3 * t ^ 2) =
      2 / 3 * t ^ 3 - 11 / 3 * t ^ 4 - 22 / 3 * t ^ 5 - 4 * t ^ 6 := by ring
  have hs1 : s ≤ 1 / 2 := ht
  have hb : 2 / 3 * s ^ 3 + 11 / 3 * s ^ 4 + 22 / 3 * s ^ 5 + 4 * s ^ 6 ≤ 8 * s ^ 3 := by
    have c4 : s ^ 4 ≤ s ^ 3 * (1 / 2) := by
      rw [show s ^ 4 = s ^ 3 * s by ring]; exact mul_le_mul_of_nonneg_left hs1 (by positivity)
    have c5 : s ^ 5 ≤ s ^ 3 * (1 / 4) := by
      rw [show s ^ 5 = s ^ 3 * s ^ 2 by ring]
      exact mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
    have c6 : s ^ 6 ≤ s ^ 3 * (1 / 8) := by
      rw [show s ^ 6 = s ^ 3 * s ^ 3 by ring]
      exact mul_le_mul_of_nonneg_left (by
        have : s ^ 3 ≤ (1 / 2) ^ 3 := pow_le_pow_left₀ hs0 hs1 3
        linarith) (by positivity)
    nlinarith [pow_nonneg hs0 3]
  nlinarith [hP, h3, h5', h4', h6', hb]

/-- `x log x ≤ x (x - 1)` for `x > 0`. -/
lemma mul_log_le_sq_sub {x : ℝ} (hx : 0 < x) : x * Real.log x ≤ x * (x - 1) :=
  mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hx) hx.le

namespace DiffusionTriple

variable {E : Type*} [MeasurableSpace E] (T : DiffusionTriple E)

/-- `Γ(1, h) = 0` for `h ∈ 𝒜₀` (diffusion property with `ψ(r) = r²`: `Γ(1) = 2 Γ(1)`), when `1 ∈ 𝒜₀`. -/
lemma Γ_one_left (h1 : (fun _ : E => (1 : ℝ)) ∈ T.A₀) {h : E → ℝ} (hh : h ∈ T.A₀) :
    T.Γ (fun _ => 1) h =ᵐ[T.μ] fun _ => 0 := by
  have hψ : ContDiff ℝ (⊤ : ℕ∞) (fun z : Fin 1 → ℝ => z 0 ^ 2) := (contDiff_apply ℝ ℝ 0).pow 2
  have key := T.diffusion 1 (fun z => z 0 ^ 2) hψ (by simp) ![fun _ => (1 : ℝ)]
    (by intro i; fin_cases i; simpa using h1) h hh
  have e : (fun x => (fun z : Fin 1 → ℝ => z 0 ^ 2)
      (fun i => (![fun _ => (1 : ℝ)] : Fin 1 → E → ℝ) i x)) = fun _ => 1 := by
    funext x; simp
  rw [e] at key
  filter_upwards [key] with x hx
  simp only [Fin.sum_univ_one] at hx
  have hp : pderiv (fun z : Fin 1 → ℝ => z 0 ^ 2) 0
      (fun j => (![fun _ => (1 : ℝ)] : Fin 1 → E → ℝ) j x) = 2 := by
    have := pderiv_comp_eval (fun r : ℝ => r ^ 2) (by fun_prop)
      (fun j => (![fun _ => (1 : ℝ)] : Fin 1 → E → ℝ) j x)
    simpa using this
  rw [hp] at hx
  simp only [Matrix.cons_val_zero] at hx
  linarith

/-- `Γ(u + c·1, v) = Γ(u, v)`. -/
lemma Γ_add_const_left (h1 : (fun _ : E => (1 : ℝ)) ∈ T.A₀) {u v : E → ℝ} (hu : u ∈ T.A₀)
    (hv : v ∈ T.A₀) (c : ℝ) :
    T.Γ (u + c • fun _ => (1 : ℝ)) v =ᵐ[T.μ] T.Γ u v := by
  have h1' : (c • fun _ : E => (1 : ℝ)) ∈ T.A₀ := T.A₀.smul_mem c h1
  filter_upwards [T.Γ_add u hu _ h1' v hv, T.Γ_smul c _ h1 v hv, Γ_one_left T h1 hv] with x h2 h3 h4
  rw [h2, Pi.add_apply]
  have h3' : T.Γ (c • fun _ : E => (1 : ℝ)) v x = c * T.Γ (fun _ => 1) v x := h3
  rw [h3', h4]; simp

/-- `Γ(u + c·1, u + c·1) = Γ(u, u)`. -/
lemma Γ_add_const_self (h1 : (fun _ : E => (1 : ℝ)) ∈ T.A₀) {u : E → ℝ} (hu : u ∈ T.A₀) (c : ℝ) :
    T.Γ (u + c • fun _ => (1 : ℝ)) (u + c • fun _ => (1 : ℝ)) =ᵐ[T.μ] T.Γ u u := by
  have h1' : (c • fun _ : E => (1 : ℝ)) ∈ T.A₀ := T.A₀.smul_mem c h1
  have huc : u + c • (fun _ : E => (1 : ℝ)) ∈ T.A₀ := T.A₀.add_mem hu h1'
  filter_upwards [T.Γ_symm _ huc _ huc, Γ_add_const_left T h1 hu huc c,
    Γ_add_const_left T h1 hu hu c, T.Γ_symm _ hu _ huc] with x h1x h2x h3x h4x
  -- Γ(u+c, u+c) = Γ(u, u+c) = Γ(u+c, u) = Γ(u,u)
  have a1 : T.Γ (u + c • fun _ => (1 : ℝ)) (u + c • fun _ => (1 : ℝ)) x =
      T.Γ u (u + c • fun _ => (1 : ℝ)) x := h2x
  have a2 : T.Γ u (u + c • fun _ => (1 : ℝ)) x = T.Γ (u + c • fun _ => (1 : ℝ)) u x := h4x
  have a3 : T.Γ (u + c • fun _ => (1 : ℝ)) u x = T.Γ u u x := h3x
  rw [a1, a2, a3]

/-- `Γ(ε g, ε g) = ε² Γ(g, g)`. -/
lemma Γ_smul_self (c : ℝ) {u : E → ℝ} (hu : u ∈ T.A₀) :
    T.Γ (c • u) (c • u) =ᵐ[T.μ] fun x => c ^ 2 * T.Γ u u x := by
  have hcu : c • u ∈ T.A₀ := T.A₀.smul_mem c hu
  filter_upwards [T.Γ_smul c u hu (c • u) hcu, T.Γ_symm u hu (c • u) hcu,
    T.Γ_smul c u hu u hu] with x h1 h2 h3
  have a1 : T.Γ (c • u) (c • u) x = c * T.Γ u (c • u) x := h1
  have a2 : T.Γ u (c • u) x = T.Γ (c • u) u x := h2
  have a3 : T.Γ (c • u) u x = c * T.Γ u u x := h3
  rw [a1, a2, a3]; ring

/-- **Core of BGL Prop. 5.1.3**: `LS(C)` and `∫ g = 0` give `∫ g² ≤ C ∫ Γ(g)` (for `g ∈ 𝒜₀`, `1 ∈ 𝒜₀`).
Apply `LS(C)` to `f = 1 + ε g`: `Ent(f²) ≥ 2ε² ∫ g² - O(ε³)`, `ℰ(f) = ε² ℰ(g)`, let `ε → 0`. -/
theorem sq_integral_le_of_LS (h1 : (fun _ : E => (1 : ℝ)) ∈ T.A₀) {C : ℝ} (h : T.LS C 0)
    {g : E → ℝ} (hg : g ∈ T.A₀) (hm : ∫ x, g x ∂T.μ = 0) :
    ∫ x, g x ^ 2 ∂T.μ ≤ C * ∫ x, T.Γ g g x ∂T.μ := by
  obtain ⟨hprob, hC, -, hLS⟩ := h
  have := hprob
  obtain ⟨M0, hM0⟩ := T.bounded g hg
  set M : ℝ := max M0 1 with hMdef
  have hM1 : 1 ≤ M := le_max_right _ _
  have hM : 0 < M := by linarith
  have hgM : ∀ x, |g x| ≤ M := fun x => (hM0 x).trans (le_max_left _ _)
  have hgi : Integrable g T.μ := integrable_of_mem T hg
  have hg2A : (fun x => g x ^ 2) ∈ T.A₀ := by
    have : (fun x => g x ^ 2) = g * g := by funext x; simp [sq]
    rw [this]; exact T.A₀.mul_mem hg hg
  have hg2i : Integrable (fun x => g x ^ 2) T.μ := integrable_of_mem T hg2A
  have hΓi : Integrable (T.Γ g g) T.μ := integrable_of_mem T (T.Γ_mem g hg g hg)
  set m2 : ℝ := ∫ x, g x ^ 2 ∂T.μ with hm2
  have hm2nn : 0 ≤ m2 := integral_nonneg fun x => sq_nonneg _
  set E0 : ℝ := ∫ x, T.Γ g g x ∂T.μ with hE0
  have hinv : 0 < 1 / (2 * M) := by positivity
  have main : ∀ ε : ℝ, 0 < ε → ε ≤ 1 / (2 * M) →
      2 * m2 - 8 * M ^ 3 * ε - ε ^ 2 * m2 ^ 2 ≤ 2 * C * E0 := by
    intro ε hε hεM
    set f : E → ℝ := ε • g + (1 : ℝ) • fun _ => (1 : ℝ) with hfdef
    have hf : f ∈ T.A₀ := T.A₀.add_mem (T.A₀.smul_mem ε hg) (T.A₀.smul_mem 1 h1)
    have hfx : ∀ x, f x = 1 + ε * g x := fun x => by simp [hfdef]; ring
    have hεg : ∀ x, |ε * g x| ≤ 1 / 2 := fun x => by
      rw [abs_mul, abs_of_pos hε]
      calc ε * |g x| ≤ (1 / (2 * M)) * M := mul_le_mul hεM (hgM x) (abs_nonneg _) hinv.le
        _ = 1 / 2 := by field_simp
    -- energy
    have hen : energy T.μ T.Γ f = ε ^ 2 * E0 := by
      unfold energy dirichletForm
      have e1 : ∫ x, T.Γ f f x ∂T.μ = ∫ x, T.Γ (ε • g) (ε • g) x ∂T.μ :=
        integral_congr_ae (Γ_add_const_self T h1 (T.A₀.smul_mem ε hg) 1)
      rw [e1, integral_congr_ae (Γ_smul_self T ε hg), integral_const_mul]
    -- ∫ f²
    have hfsq : ∫ x, f x ^ 2 ∂T.μ = 1 + ε ^ 2 * m2 := by
      have e : (fun x => f x ^ 2) = fun x => 1 + 2 * ε * g x + ε ^ 2 * g x ^ 2 := by
        funext x; rw [hfx]; ring
      have i1 : Integrable (fun x => 2 * ε * g x) T.μ := hgi.const_mul _
      have i2 : Integrable (fun x => ε ^ 2 * g x ^ 2) T.μ := hg2i.const_mul _
      have i12 : Integrable (fun x => 1 + 2 * ε * g x) T.μ := (integrable_const (1 : ℝ)).add i1
      rw [e, integral_add i12 i2, integral_add (integrable_const (1 : ℝ)) i1, integral_const_mul,
        integral_const_mul, hm]
      simp [hm2]
    have hs : 0 ≤ ε ^ 2 * m2 := by positivity
    -- lower bound for `∫ f² log f²`
    have hlogi := integrable_sq_mul_log_sq T hf
    have hpt : ∀ x, 2 * ε * g x + 3 * ε ^ 2 * g x ^ 2 - 8 * M ^ 3 * ε ^ 3 ≤
        f x ^ 2 * Real.log (f x ^ 2) := by
      intro x
      have := log_sq_lower (ε * g x) (hεg x)
      rw [hfx]
      have hb : |ε * g x| ^ 3 ≤ ε ^ 3 * M ^ 3 := by
        rw [abs_mul, abs_of_pos hε, mul_pow]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) (hgM x) 3)
          (by positivity)
      nlinarith [this, hb]
    have hlow : 3 * ε ^ 2 * m2 - 8 * M ^ 3 * ε ^ 3 ≤ ∫ x, f x ^ 2 * Real.log (f x ^ 2) ∂T.μ := by
      have hint : Integrable (fun x => 2 * ε * g x + 3 * ε ^ 2 * g x ^ 2 - 8 * M ^ 3 * ε ^ 3) T.μ :=
        ((hgi.const_mul _).add (hg2i.const_mul _)).sub (integrable_const _)
      have := integral_mono hint hlogi hpt
      have e : ∫ x, (2 * ε * g x + 3 * ε ^ 2 * g x ^ 2 - 8 * M ^ 3 * ε ^ 3) ∂T.μ =
          3 * ε ^ 2 * m2 - 8 * M ^ 3 * ε ^ 3 := by
        have i1 : Integrable (fun x => 2 * ε * g x) T.μ := hgi.const_mul _
        have i2 : Integrable (fun x => 3 * ε ^ 2 * g x ^ 2) T.μ := hg2i.const_mul _
        have i12 : Integrable (fun x => 2 * ε * g x + 3 * ε ^ 2 * g x ^ 2) T.μ := i1.add i2
        rw [integral_sub i12 (integrable_const _), integral_add i1 i2, integral_const_mul,
          integral_const_mul, hm]
        simp [hm2]
      rwa [e] at this
    -- upper bound of the second term of `Ent`
    have hsec : (∫ x, f x ^ 2 ∂T.μ) * Real.log (∫ x, f x ^ 2 ∂T.μ) ≤
        ε ^ 2 * m2 + ε ^ 4 * m2 ^ 2 := by
      rw [hfsq]
      have := mul_log_le_sq_sub (x := 1 + ε ^ 2 * m2) (by linarith)
      nlinarith [this]
    have hEnt := hLS f hf
    unfold Ent at hEnt
    rw [hen, hfsq] at hEnt
    simp only [zero_mul, add_zero] at hEnt
    have hEnt' : (∫ x, f x ^ 2 * Real.log (f x ^ 2) ∂T.μ) -
        (∫ x, f x ^ 2 ∂T.μ) * Real.log (∫ x, f x ^ 2 ∂T.μ) ≤ 2 * C * (ε ^ 2 * E0) := by
      simpa [hfsq] using hEnt
    have hfin : 2 * ε ^ 2 * m2 - 8 * M ^ 3 * ε ^ 3 - ε ^ 4 * m2 ^ 2 ≤ 2 * C * (ε ^ 2 * E0) := by
      nlinarith [hlow, hsec, hEnt']
    have hε2 : 0 < ε ^ 2 := by positivity
    have : ε ^ 2 * (2 * m2 - 8 * M ^ 3 * ε - ε ^ 2 * m2 ^ 2) ≤ ε ^ 2 * (2 * C * E0) := by
      nlinarith [hfin]
    exact le_of_mul_le_mul_left this hε2
  -- let ε → 0+
  have hlim : Tendsto (fun ε : ℝ => 2 * m2 - 8 * M ^ 3 * ε - ε ^ 2 * m2 ^ 2) (𝓝[>] 0)
      (𝓝 (2 * m2)) := by
    have : Tendsto (fun ε : ℝ => 2 * m2 - 8 * M ^ 3 * ε - ε ^ 2 * m2 ^ 2) (𝓝 0)
        (𝓝 (2 * m2 - 8 * M ^ 3 * 0 - 0 ^ 2 * m2 ^ 2)) := by
      have hc : Continuous fun ε : ℝ => 2 * m2 - 8 * M ^ 3 * ε - ε ^ 2 * m2 ^ 2 := by fun_prop
      exact hc.tendsto 0
    simp only [mul_zero, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      zero_mul] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 2 * m2 - 8 * M ^ 3 * ε - ε ^ 2 * m2 ^ 2 ≤ 2 * C * E0 := by
    have : Ioo (0 : ℝ) (1 / (2 * M)) ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT hinv
    filter_upwards [this] with ε hε
    exact main ε hε.1 hε.2.le
  have := le_of_tendsto hlim hev
  linarith

/-- **BGL Prop. 5.1.3 (first assertion)**: for a diffusion triple with `1 ∈ 𝒜₀`, `LS(C)` (tight, `D = 0`) implies `P(C)`. -/
theorem PI_of_LS (h1 : (fun _ : E => (1 : ℝ)) ∈ T.A₀) {C : ℝ} (h : T.LS C 0) : T.PI C := by
  have h' := h
  obtain ⟨hprob, hC, -, -⟩ := h'
  have := hprob
  refine ⟨hprob, hC, fun g hg => ?_⟩
  set m : ℝ := ∫ x, g x ∂T.μ with hmdef
  set gh : E → ℝ := g + (-m) • fun _ => (1 : ℝ) with hgh
  have hghA : gh ∈ T.A₀ := T.A₀.add_mem hg (T.A₀.smul_mem _ h1)
  have hghx : ∀ x, gh x = g x - m := fun x => by simp [hgh]; ring
  have hgi : Integrable g T.μ := integrable_of_mem T hg
  have hmean : ∫ x, gh x ∂T.μ = 0 := by
    have e : (fun x => gh x) = fun x => g x - m := funext hghx
    rw [e, integral_sub hgi (integrable_const m)]
    simp [hmdef]
  have key := sq_integral_le_of_LS T h1 h hghA hmean
  have hg2A : (fun x => g x ^ 2) ∈ T.A₀ := by
    have : (fun x => g x ^ 2) = g * g := by funext x; simp [sq]
    rw [this]; exact T.A₀.mul_mem hg hg
  have hg2i : Integrable (fun x => g x ^ 2) T.μ := integrable_of_mem T hg2A
  have hvar : ProbabilityTheory.variance g T.μ = ∫ x, gh x ^ 2 ∂T.μ := by
    rw [ProbabilityTheory.variance_eq_sub (T.memLp g hg 2 (by norm_num) (by simp))]
    have e : (fun x => gh x ^ 2) = fun x => g x ^ 2 - 2 * m * g x + m ^ 2 := by
      funext x; rw [hghx]; ring
    have i1 : Integrable (fun x => 2 * m * g x) T.μ := hgi.const_mul _
    have i12 : Integrable (fun x => g x ^ 2 - 2 * m * g x) T.μ := hg2i.sub i1
    rw [e, integral_add i12 (integrable_const _), integral_sub hg2i i1, integral_const_mul]
    simp [Pi.pow_apply]
    rw [← hmdef]
    ring
  have hen : energy T.μ T.Γ g = ∫ x, T.Γ gh gh x ∂T.μ := by
    unfold energy dirichletForm
    exact (integral_congr_ae (Γ_add_const_self T h1 hg (-m))).symm
  rw [hvar, hen]
  exact key

/-- **Sharpness of a Poincaré constant via an eigenfunction** (the book's "the Poincaré constant is already optimal",
BGL p. 272-273): if `f ∈ 𝒜₀`, `L f = -λ f` a.e., `λ > 0` and `∫ f² > 0`, then `P(c)` fails for every `c < 1/λ`
(`∫ f = 0`, `Var f = ∫ f²`, `ℰ(f) = -∫ f L f = λ ∫ f²`). -/
theorem not_PI_of_eigen_pos [IsProbabilityMeasure T.μ] {f : E → ℝ} (hf : f ∈ T.A₀) {lam : ℝ}
    (hlam : 0 < lam) (hL : ∀ᵐ x ∂T.μ, T.L f x = -lam * f x) (hn : 0 < ∫ x, f x ^ 2 ∂T.μ)
    {c : ℝ} (hc : c < 1 / lam) : ¬ T.PI c := by
  intro hPI
  obtain ⟨-, -, hineq⟩ := hPI
  have hfi : Integrable f T.μ := integrable_of_mem T hf
  have hint0 : ∫ x, f x ∂T.μ = 0 := by
    have h0 := T.integral_L f hf
    have e : ∫ x, T.L f x ∂T.μ = -lam * ∫ x, f x ∂T.μ := by
      rw [integral_congr_ae hL, integral_const_mul]
    rw [e] at h0
    have : -lam ≠ 0 := by linarith
    exact (mul_eq_zero.1 h0).resolve_left this
  have hen : energy T.μ T.Γ f = lam * ∫ x, f x ^ 2 ∂T.μ := by
    unfold energy dirichletForm
    have h := T.ibp f hf f hf
    have e : ∫ x, f x * T.L f x ∂T.μ = -lam * ∫ x, f x ^ 2 ∂T.μ := by
      rw [← integral_const_mul]
      refine integral_congr_ae ?_
      filter_upwards [hL] with x hx
      rw [hx]; ring
    rw [e] at h
    linarith
  have hvar : ProbabilityTheory.variance f T.μ = ∫ x, f x ^ 2 ∂T.μ := by
    rw [ProbabilityTheory.variance_eq_sub (T.memLp f hf 2 (by norm_num) (by simp))]
    simp only [Pi.pow_apply]
    rw [hint0]; norm_num
  have h := hineq f hf
  rw [hvar, hen] at h
  have : c * lam < 1 := by
    have := mul_lt_mul_of_pos_right hc hlam
    rwa [one_div, inv_mul_cancel₀ hlam.ne'] at this
  nlinarith

/-- `not_PI_of_eigen_pos` with the normalisation `∫ f² = 1`. -/
theorem not_PI_of_eigen [IsProbabilityMeasure T.μ] {f : E → ℝ} (hf : f ∈ T.A₀) {lam : ℝ}
    (hlam : 0 < lam) (hL : ∀ᵐ x ∂T.μ, T.L f x = -lam * f x) (hn : ∫ x, f x ^ 2 ∂T.μ = 1)
    {c : ℝ} (hc : c < 1 / lam) : ¬ T.PI c :=
  not_PI_of_eigen_pos T hf hlam hL (by rw [hn]; exact one_pos) hc

end DiffusionTriple

/-- **`LS ⟹ PI` on every compact triple, unconditionally** (BGL Prop. 5.1.3, first assertion): `𝒜 = 𝒜₀` is unital. -/
theorem CompactTriple.PI_of_LS {E : Type*} [MeasurableSpace E] (C : CompactTriple E) {c : ℝ}
    (h : C.toDiffusionTriple.LS c 0) : C.toDiffusionTriple.PI c :=
  DiffusionTriple.PI_of_LS C.toDiffusionTriple ((C.A_eq _).1 (FullTriple.const_mem_A C.toFullTriple 1)) h

end MarkovTriple.BGL
