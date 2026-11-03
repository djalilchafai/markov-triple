import Mathlib
import MarkovTriple.BGL.Theory.Interp.Setup
import MarkovTriple.BGL.Theory.Interp.EntropyQuot
import MarkovTriple.BGL.Theory.LogSobolev

/-!
# De Bruijn identity for a general `FullTriple` of finite measure (BGL Prop. 5.5.3, proof of Prop. 5.7.1)

For `φ ∈ 𝒜₀`, `0 ≤ φ`, `ε > 0`, `g_s = ε + P_s φ`, `e(s) = ∫ g_s log g_s`, `I(s) = ∫ Γ(g_s)/g_s` (frozen definitions
`entE`, `entI`):

* `entE_continuousOn`, `entI_continuousOn` (continuity on `[0,∞)`; the latter uses the `L¹`-continuity of
  `s ↦ Γ(P_s φ)` from `Curve.lean`),
* `hasDerivAt_entE` : `e' = -I` on `(0,∞)`.

Only `IsFiniteMeasure μ` is used.  Reason for finiteness: for infinite `μ`, `g log g` is not integrable
(`ε log ε ≠ 0` constant part), so `entE ≡ 0` while `entI > 0` in general (see `AUDIT_R16_ENTROPY_SELF.md`).
The identity `e' = -I` is `d/ds ∫ Θ(g_s) = ∫ Θ'(g_s) L P_sφ = -∫ Γ(P_sφ, Θ'(g_s))` (chain rule in `L²` for the smooth
cutoff `Θ` of `x log x`, then `ibp_bdd`, `Θ'' = 1/x`).
-/

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal InnerProductSpace

namespace MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E]

namespace FullTriple

variable (T : FullTriple E) [IsFiniteMeasure T.μ]

/-- the constant class `ε`. -/
noncomputable def ecls (ε : ℝ) : Lp ℝ 2 T.μ := (memLp_const ε : MemLp (fun _ : E => ε) 2 T.μ).toLp _

lemma ecls_ae (ε : ℝ) : (T.ecls ε : E → ℝ) =ᵐ[T.μ] fun _ => ε :=
  (memLp_const ε : MemLp (fun _ : E => ε) 2 T.μ).coeFn_toLp

/-- the `L²`-curve `r ↦ ε + P_r φ`. -/
noncomputable def gcurve (φ : T.A₀) (ε r : ℝ) : Lp ℝ 2 T.μ := T.ecls ε + T.orb φ r

omit [IsFiniteMeasure T.μ] in
lemma orb_ae (φ : T.A₀) (r : ℝ) : (T.orb φ r : E → ℝ) =ᵐ[T.μ] T.Pt r.toNNReal φ :=
  T.Pt_ae r.toNNReal φ

lemma gcurve_ae (φ : T.A₀) (ε r : ℝ) : (T.gcurve φ ε r : E → ℝ) =ᵐ[T.μ] T.entG φ ε r := by
  filter_upwards [Lp.coeFn_add (T.ecls ε) (T.orb φ r), T.ecls_ae ε, T.orb_ae φ r] with x h1 h2 h3
  rw [gcurve, h1, Pi.add_apply, h2, h3]; rfl

lemma continuous_gcurve (φ : T.A₀) (ε : ℝ) : Continuous (T.gcurve φ ε) :=
  continuous_const.add (T.continuous_orb φ)

lemma hasDerivAt_gcurve (φ : T.A₀) (ε : ℝ) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (T.gcurve φ ε) (T.orb (T.Lt φ) s) s :=
  (T.hasDerivAt_orb φ hs).const_add (T.ecls ε)

lemma gcurve_ge (φ : T.A₀) {ε : ℝ} (h0 : 0 ≤ᵐ[T.μ] φ.1) (r : ℝ) :
    ∀ᵐ x ∂T.μ, ε ≤ T.gcurve φ ε r x := by
  filter_upwards [T.gcurve_ae φ ε r, T.Pt_nonneg r.toNNReal φ h0] with x h1 h2
  rw [h1]; simp only [entG]; simp only [Pi.zero_apply] at h2; linarith

omit [IsFiniteMeasure T.μ] in
lemma exists_bound (φ : T.A₀) : ∃ M : ℝ, 0 < M ∧ ∀ x, φ.1 x ≤ M := by
  obtain ⟨C0, hC0⟩ := T.bounded φ.1 φ.2
  exact ⟨max C0 1, lt_of_lt_of_le one_pos (le_max_right _ _),
    fun x => (le_abs_self _).trans ((hC0 x).trans (le_max_left _ _))⟩

variable {T}

lemma entE_eq {φ : T.A₀} {ε M : ℝ} (hε : 0 < ε) (hM : 0 < M) (h0 : 0 ≤ᵐ[T.μ] φ.1)
    (hφ : ∀ x, φ.1 x ≤ M) (C : BE.Cut ε M) (r : ℝ) :
    T.entE φ ε r = ∫ x, C.Θ (T.gcurve φ ε r x) ∂T.μ := by
  unfold entE
  refine integral_congr_ae ?_
  filter_upwards [T.gcurve_ae φ ε r, entG_range T φ hε hM h0 hφ r] with x h1 h2
  rw [h1, C.Θ_eq h2]

/-- **continuity of `e`** on `[0,∞)` (in fact on `ℝ`). -/
theorem entE_continuousOn (φ : T.A₀) {ε : ℝ} (hε : 0 < ε) (h0 : 0 ≤ᵐ[T.μ] φ.1) :
    ContinuousOn (T.entE φ ε) (Ici 0) := by
  obtain ⟨M, hM, hφ⟩ := T.exists_bound φ
  obtain ⟨C⟩ := BE.exists_cut hε hM.le
  have : T.entE φ ε = fun r => ∫ x, C.Θ (T.gcurve φ ε r x) ∂T.μ :=
    funext fun r => entE_eq hε hM h0 hφ C r
  rw [this]
  exact (continuous_integral_smooth C.hΘ C.hΘc (T.continuous_gcurve φ ε)).continuousOn

omit [IsFiniteMeasure T.μ] in
lemma uK_ae (φ : T.A₀) (r : ℝ) :
    (GB T (T.cK φ r) (T.cK φ r) : E → ℝ) =ᵐ[T.μ] G T (T.Pt r.toNNReal φ) (T.Pt r.toNNReal φ) := by
  have h := ucurve_ae (T := T) φ 0 (-r)
  simpa [ucurve] using h

omit [IsFiniteMeasure T.μ] in
lemma uK_nonneg (φ : T.A₀) (r : ℝ) : 0 ≤ᵐ[T.μ] (GB T (T.cK φ r) (T.cK φ r) : E → ℝ) := by
  have h := ucurve_nonneg (T := T) φ 0 (-r)
  simpa [ucurve] using h

lemma entI_eq_quot (φ : T.A₀) (ε r : ℝ) :
    T.entI φ ε r = ∫ x, (GB T (T.cK φ r) (T.cK φ r) : E → ℝ) x / T.gcurve φ ε r x ∂T.μ := by
  unfold entI
  have e : T.entG φ ε r = fun x => ε + T.Pt r.toNNReal φ x := rfl
  refine integral_congr_ae ?_
  filter_upwards [T.gcurve_ae φ ε r, uK_ae (T := T) φ r,
    ΓA_shift T ε (T.Pt_mem_A r.toNNReal φ)] with x h1 h2 h3
  rw [h1, h2, e]
  have h3' : T.toDiffusionTriple.ΓA (fun x => ε + T.Pt r.toNNReal φ x)
      (fun x => ε + T.Pt r.toNNReal φ x) x = G T (T.Pt r.toNNReal φ) (T.Pt r.toNNReal φ) x := h3
  rw [h3']

/-- **continuity of `I`** on `[0,∞)` (in fact on `ℝ`). -/
theorem entI_continuousOn (φ : T.A₀) {ε : ℝ} (hε : 0 < ε) (h0 : 0 ≤ᵐ[T.μ] φ.1) :
    ContinuousOn (T.entI φ ε) (Ici 0) := by
  have : T.entI φ ε = fun r => ∫ x, (GB T (T.cK φ r) (T.cK φ r) : E → ℝ) x / T.gcurve φ ε r x ∂T.μ :=
    funext fun r => entI_eq_quot (T := T) φ ε r
  rw [this]
  exact (continuous_integral_div (T.continuous_uK φ) (T.continuous_gcurve φ ε) hε
    (T.gcurve_ge φ h0)).continuousOn

omit [IsFiniteMeasure T.μ] in
/-- integrability of `Γ(P_σ φ)` (`P_σ φ ∈ 𝒟(ℰ)`, Prop. 3.3.5 (ii)). -/
lemma integrable_Γ_Pt (φ : T.A₀) (σ : ℝ) :
    Integrable (G T (T.Pt σ.toNNReal φ) (T.Pt σ.toNNReal φ)) T.μ := by
  have e := gammaE_eq_ΓA (T.Pt_mem_A σ.toNNReal φ) (T.Pt_memLp σ.toNNReal φ) (Pt_mem_Q φ σ)
    (T.Pt_mem_A σ.toNNReal φ) (T.Pt_memLp σ.toNNReal φ) (Pt_mem_Q φ σ)
  exact (L1.integrable_coeFn _).congr e

/-- `∫ Θ'(g_s) L P_s φ = -I(s)`: Green's formula (`ibp_bdd`) with `Θ' = Λ + 1`, `Θ'' = 1/x`. -/
theorem integral_dTheta {φ : T.A₀} {ε M : ℝ} (hε : 0 < ε) (hM : 0 < M) (h0 : 0 ≤ᵐ[T.μ] φ.1)
    (hφ : ∀ x, φ.1 x ≤ M) (C : BE.Cut ε M) (s : ℝ) :
    ∫ x, deriv C.Θ (T.gcurve φ ε s x) * (T.orb (T.Lt φ) s : E → ℝ) x ∂T.μ = -T.entI φ ε s := by
  set P := T.Pt s.toNNReal φ with hGdef
  have hG : P ∈ T.A := T.Pt_mem_A _ φ
  have hG2 : MemLp P 2 T.μ := T.Pt_memLp _ φ
  have hQG : hG2.toLp P ∈ T.formDomain := Pt_mem_Q φ s
  have hLG : Integrable (T.L P) T.μ := (memLp_L_Pt φ s).integrable one_le_two
  have hgA := entG_mem_A T φ ε s
  obtain ⟨K1, K2, hK1, hK2, hΛb, hΛ'b, hΛL, hΛrem⟩ := cs_facts C.hΛ C.hΛc
  set Ψ : ℝ → ℝ := fun y => C.Λ y + 1 with hΨ
  have hΨs : ContDiff ℝ (⊤ : ℕ∞) Ψ := C.hΛ.add contDiff_const
  have hΨd : ∀ y, deriv Ψ y = deriv C.Λ y := fun y => by simp [hΨ]
  set g := T.entG φ ε s with hg
  set k : E → ℝ := fun x => Ψ (g x) with hk
  have hkA : k ∈ T.A := comp_mem_A T hΨs hgA
  have hkb : ∀ x, |k x| ≤ K1 + 1 := fun x => by
    simp only [hk, hΨ]
    calc |C.Λ (g x) + 1| ≤ |C.Λ (g x)| + |(1 : ℝ)| := abs_add_le _ _
      _ ≤ K1 + 1 := by rw [abs_one]; exact add_le_add (hΛb _) le_rfl
  have hk2 : MemLp k 2 T.μ := MemLp.of_bound (T.A_measurable k hkA).aestronglyMeasurable (K1 + 1)
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hkb x)
  have hΓk : Integrable (G T k k) T.μ := by
    refine ((integrable_Γ_Pt φ s).const_mul (K1 ^ 2)).mono'
      (T.A_measurable _ (G_mem hkA hkA)).aestronglyMeasurable ?_
    filter_upwards [ΓA_comp_comp T hΨs hgA, ΓA_shift T ε hG, T.ΓA_nonneg P hG] with x h1 h2 h3
    have h1' : G T k k x = deriv Ψ (g x) ^ 2 * G T g g x := h1
    have h2' : G T g g x = G T P P x := h2
    have h3' : 0 ≤ G T P P x := h3
    rw [Real.norm_eq_abs, h1', h2', abs_of_nonneg (mul_nonneg (sq_nonneg _) h3')]
    refine mul_le_mul_of_nonneg_right ?_ h3'
    rw [hΨd]
    have := hΛ'b (g x)
    nlinarith [abs_nonneg (deriv C.Λ (g x)), sq_abs (deriv C.Λ (g x))]
  have hQk : hk2.toLp k ∈ T.formDomain := mem_formDomain_of_ESA hkA hk2 hΓk
  obtain ⟨-, hibp⟩ := ibp_bdd hG hG2 hQG hLG hkA hk2 hQk (M := K1 + 1) (Eventually.of_forall hkb)
  -- step 1
  have step1 : ∫ x, deriv C.Θ (T.gcurve φ ε s x) * (T.orb (T.Lt φ) s : E → ℝ) x ∂T.μ =
      ∫ x, k x * T.L P x ∂T.μ := by
    refine integral_congr_ae ?_
    filter_upwards [T.gcurve_ae φ ε s, entG_range T φ hε hM h0 hφ s, L_Pt_ae φ s] with x h1 h2 h3
    rw [h1, C.deriv_Θ_eq_Λ hε h2, ← h3]
  -- step 3
  have step3 : ∫ x, G T P k x ∂T.μ = T.entI φ ε s := by
    unfold entI
    refine integral_congr_ae ?_
    filter_upwards [ΓA_comp_left T hΨs hgA hG, ΓA_comp_left T (contDiff_const.add contDiff_id :
        ContDiff ℝ (⊤ : ℕ∞) fun r : ℝ => ε + r) hG hG, ΓA_shift T ε hG,
      entG_range T φ hε hM h0 hφ s] with x h1 h2 h3 h4
    have a1 : G T k P x = deriv Ψ (g x) * G T g P x := h1
    have a2 : G T g P x = deriv (fun r : ℝ => ε + r) (P x) * G T P P x := h2
    have a3 : G T g g x = G T P P x := h3
    have c := congrFun (G_comm (T := T) P k) x
    rw [c, a1, a2, hΨd, C.deriv_Λ_eq hε h4]
    have : deriv (fun r : ℝ => ε + r) (P x) = 1 := by simp
    have a3' : T.toDiffusionTriple.ΓA (T.entG φ ε s) (T.entG φ ε s) x = G T P P x := a3
    rw [this, one_mul, a3', div_eq_inv_mul]
  rw [step1]
  have := hibp
  rw [step3] at this
  linarith

/-- **de Bruijn identity** `e' = -I` on `(0,∞)` (BGL Prop. 5.5.3). -/
theorem hasDerivAt_entE (φ : T.A₀) {ε : ℝ} (hε : 0 < ε) (h0 : 0 ≤ᵐ[T.μ] φ.1) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (T.entE φ ε) (-T.entI φ ε s) s := by
  obtain ⟨M, hM, hφ⟩ := T.exists_bound φ
  obtain ⟨C⟩ := BE.exists_cut hε hM.le
  have h := hasDerivAt_integral_smooth C.hΘ C.hΘc (T.hasDerivAt_gcurve φ ε hs)
  rw [integral_dTheta hε hM h0 hφ C s] at h
  have : T.entE φ ε = fun r => ∫ x, C.Θ (T.gcurve φ ε r x) ∂T.μ :=
    funext fun r => entE_eq hε hM h0 hφ C r
  rw [this]; exact h


end FullTriple

end MarkovTriple.BGL
