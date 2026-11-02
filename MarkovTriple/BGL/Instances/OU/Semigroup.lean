import Mathlib
import MarkovTriple.BGL.Instances.OU.Diffusion
import MarkovTriple.BGL.Semigroup.ESA
import MarkovTriple.BGL.Semigroup.Mass
import MarkovTriple.BGL.Analysis.OU.MehlerEq

/-!
# The Friedrichs semigroup of the OU triple: Hermite eigenfunctions, smoothing, Mehler, ESA, S10, S11

The BGL semigroup `ouDiff.semigroup` is a strongly continuous semigroup of self-adjoint contractions
whose generator (`ouDiff.generator`, characterised by `generator_iff_form`) extends `L|C_c^∞`.  This is
exactly the information (`IsSG` and the generator clause `GenA₀`) used by the old OU argument, which
we reuse: Hermite functions are eigenfunctions (`eigen_hL`, via graph-norm approximation by test
functions), `P_t u` is smooth for `t > 0` (`smoothing_ou`), Mehler's formula (`mehler_ae`).
Then: `𝒜₀` is a core (F10; from density of `(1 − L)C_c^∞`, old `ou_esa`), ergodicity (S10; from the
core property and the old Hermite argument), conservativeness (S11; `P_t 1 = 1` by `He_0 = 1`).
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal Real InnerProductSpace LinearPMap
open MarkovTriple.Sanity.OU hiding A₀
open MarkovTriple.Sanity.Circle (IsSG)

local notation "OA₀" => MarkovTriple.Sanity.OU.A₀

namespace MarkovTriple.BGL.Instances.OU

instance : IsProbabilityMeasure ouDiff.μ := (inferInstance : IsProbabilityMeasure γ)

/-- the Friedrichs semigroup of the OU triple, on `L²(γ)` -/
noncomputable abbrev Pt : ℝ≥0 → (Lp ℝ 2 ouDiff.μ →L[ℝ] Lp ℝ 2 ouDiff.μ) := ouDiff.semigroup

lemma Pt_IsSG : IsSG Pt where
  zero := (DiffusionTriple.formData ouDiff).semigroup_zero
  add := fun s t => (DiffusionTriple.formData ouDiff).semigroup_add s t
  cont := fun u => by
    have h : Tendsto (fun t : ℝ≥0 => Pt t u) (𝓝 0) (𝓝 (Pt 0 u)) :=
      ((DiffusionTriple.formData ouDiff).continuous_semigroup_apply u).tendsto 0
    have h0 : Pt 0 u = u := by
      have := (DiffusionTriple.formData ouDiff).semigroup_zero
      exact congrArg (fun T => T u) this
    rw [h0] at h
    exact h

lemma Pt_gen : GenA₀ Pt := by
  intro g hg u v hu hv
  have hmem : ouDiff.cls ⟨g, hg⟩ ∈ ouDiff.generator.domain :=
    DiffusionTriple.cls_mem_generator_domain ouDiff ⟨g, hg⟩
  have hG := DiffusionTriple.generator_cls ouDiff ⟨g, hg⟩ hmem
  have hu' : u = ouDiff.cls ⟨g, hg⟩ :=
    Lp.ext (hu.trans (DiffusionTriple.coeFn_cls ouDiff ⟨g, hg⟩).symm)
  have hv' : v = ouDiff.Lcls ⟨g, hg⟩ :=
    Lp.ext (hv.trans (DiffusionTriple.coeFn_Lcls ouDiff ⟨g, hg⟩).symm)
  subst hu' hv'
  exact ((DiffusionTriple.formData ouDiff).tendsto_generator_iff _ _).1 ⟨hmem, hG⟩

/-- Hermite functions are eigenfunctions of the Friedrichs semigroup: `P_t h_n = e^{-nt} h_n`. -/
theorem Pt_hL (n : ℕ) (t : ℝ≥0) : Pt t (hL n) = Real.exp (-(n : ℝ) * t) • hL n :=
  eigen_hL Pt_IsSG Pt_gen n t

/-- **F8 (smoothing)**: `P_t u` is a smooth `L²` function for `t > 0`. -/
theorem Pt_smooth (t : ℝ≥0) (ht : 0 < t) (u : Lp ℝ 2 ouDiff.μ) :
    ∃ g : ℝ → ℝ, Sm g ∧ MemLp g 2 γ ∧ MemLp (Lo g) 2 γ ∧ (Pt t u : ℝ → ℝ) =ᵐ[γ] g :=
  smoothing_ou Pt_IsSG Pt_gen t ht u

/-- Mehler's formula for any semigroup with the Hermite eigenfunctions (abstract form). -/
theorem mehler_of_sg {P : ℝ≥0 → (Lp ℝ 2 γ →L[ℝ] Lp ℝ 2 γ)} (hsg : IsSG P) (hgenA : GenA₀ P)
    (hself' : ∀ (t : ℝ≥0) (u v : Lp ℝ 2 γ), ⟪P t u, v⟫_ℝ = ⟪u, P t v⟫_ℝ)
    (t : ℝ≥0) {f : ℝ → ℝ} (hf : f ∈ OA₀) (u : Lp ℝ 2 γ) (hu : (u : ℝ → ℝ) =ᵐ[γ] f) :
    ((P t u : Lp ℝ 2 γ) : ℝ → ℝ) =ᵐ[γ]
      Mh (Real.exp (-(t : ℝ))) (√(1 - Real.exp (-(t : ℝ)) ^ 2)) f := by
  set a := Real.exp (-(t : ℝ)) with ha
  set c := √(1 - a ^ 2) with hc
  have ha0 : 0 < a := Real.exp_pos _
  have ha1 : a ≤ 1 := by rw [ha]; exact Real.exp_le_one_iff.2 (by simp)
  have hc1 : |c| ≤ 1 := by
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sqrt_le_one.2 (by nlinarith)
  have hMm := memLp_Mh ha0 c hc1 hf
  have hz : P t u - hMm.toLp (Mh a c f) = 0 := by
    refine eq_zero_of_orth_hL fun n => ?_
    rw [inner_sub_right]
    have e1 : ⟪hL n, P t u⟫_ℝ = a ^ n * ∫ x, hh n x * f x ∂γ := by
      refine (hself' t (hL n) u).symm.trans ?_
      rw [eigen_hL hsg hgenA n t, inner_smul_left, inner_hL]
      have : Real.exp (-(n : ℝ) * t) = a ^ n := by
        rw [ha, ← Real.exp_nat_mul]; ring_nf
      simp only [RCLike.conj_to_real, this]
      congr 1
      exact integral_congr_ae (hu.mono fun x hx => by simp only [hx])
    have e2 : ⟪hL n, hMm.toLp (Mh a c f)⟫_ℝ = a ^ n * ∫ x, hh n x * f x ∂γ := by
      rw [inner_hL, ← coeff_Mh ha0 ha1 hc hf n]
      exact integral_congr_ae (hMm.coeFn_toLp.mono fun x hx => by simp only [hx])
    rw [e1, e2, sub_self]
  have := sub_eq_zero.1 hz
  rw [this]
  exact hMm.coeFn_toLp

/-- **Mehler's formula for the BGL (Friedrichs) semigroup**: for `f ∈ C_c^∞`,
`P_t [f] = (x ↦ ∫ f(e^{-t} x + √(1 − e^{-2t}) y) dγ(y))` a.e. -/
theorem Pt_mehler (t : ℝ≥0) {f : ℝ → ℝ} (hf : f ∈ OA₀) (u : Lp ℝ 2 ouDiff.μ)
    (hu : (u : ℝ → ℝ) =ᵐ[γ] f) :
    ((Pt t u : Lp ℝ 2 ouDiff.μ) : ℝ → ℝ) =ᵐ[γ]
      Mh (Real.exp (-(t : ℝ))) (√(1 - Real.exp (-(t : ℝ)) ^ 2)) f :=
  mehler_of_sg (P := Pt) Pt_IsSG Pt_gen
    (fun t u v => ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      ((DiffusionTriple.formData ouDiff).semigroup_isSelfAdjoint t) u v) t hf u hu

/-! ### F10: `C_c^∞` is a core for the Friedrichs generator -/

/-- **ESA (F10)** for the OU triple: every `u ∈ 𝒟(L)` is the graph-norm limit of test functions.
Proof: `(1 − L) C_c^∞` is dense in `L²(γ)` (old `ou_esa`, from the cutoff approximation
`cutoff_approx` of the Hermite functions), and `R = (1 − L)⁻¹` of the Friedrichs generator maps
`[a − L a]` to `[a]`. -/
theorem ou_esa_core (u : Lp ℝ 2 ouDiff.μ) (hu : u ∈ ouDiff.generator.domain) :
    ∃ a : ℕ → ouDiff.A₀, Tendsto (fun n => ouDiff.cls (a n)) atTop (𝓝 u) ∧
      Tendsto (fun n => ouDiff.Lcls (a n)) atTop (𝓝 (ouDiff.generator ⟨u, hu⟩)) := by
  set S := DiffusionTriple.formData ouDiff with hS
  let M : Submodule ℝ (Lp ℝ 2 ouDiff.μ) := LinearMap.range (DiffusionTriple.clsₗ ouDiff -
    DiffusionTriple.Lclsₗ ouDiff)
  have hdense : Dense (M : Set (Lp ℝ 2 ouDiff.μ)) := by
    refine ou_esa.mono ?_
    rintro w ⟨f, hf, hw⟩
    refine ⟨⟨f, hf⟩, ?_⟩
    refine Lp.ext ?_
    show ((ouDiff.cls ⟨f, hf⟩ - ouDiff.Lcls ⟨f, hf⟩ : Lp ℝ 2 ouDiff.μ) : ℝ → ℝ) =ᵐ[γ] w
    filter_upwards [Lp.coeFn_sub (ouDiff.cls ⟨f, hf⟩) (ouDiff.Lcls ⟨f, hf⟩),
      DiffusionTriple.coeFn_cls ouDiff ⟨f, hf⟩, DiffusionTriple.coeFn_Lcls ouDiff ⟨f, hf⟩, hw]
      with x h1 h2 h3 h4
    rw [h1, Pi.sub_apply, h2, h3, h4]; rfl
  set g : Lp ℝ 2 ouDiff.μ := u - S.generator ⟨u, hu⟩ with hg
  obtain ⟨m, hmM, hmg⟩ := mem_closure_iff_seq_limit.1 (hdense.closure_eq ▸ Set.mem_univ g)
  have hm : ∀ n, ∃ a : ouDiff.A₀, ouDiff.cls a - ouDiff.Lcls a = m n := by
    intro n
    obtain ⟨a, ha⟩ := hmM n
    exact ⟨a, ha⟩
  choose a ha using hm
  have hRu : S.R g = u := (S.generator_apply_eq_iff hu _).1 rfl
  have h1 : Tendsto (fun n => ouDiff.cls (a n)) atTop (𝓝 u) := by
    have : Tendsto (fun n => S.R (m n)) atTop (𝓝 (S.R g)) := (S.R.continuous.tendsto g).comp hmg
    rw [hRu] at this
    refine this.congr (fun n => ?_)
    rw [← ha n]; exact DiffusionTriple.R_cls_sub ouDiff (a n)
  refine ⟨a, h1, ?_⟩
  have h2 : Tendsto (fun n => ouDiff.cls (a n) - m n) atTop (𝓝 (u - g)) := h1.sub hmg
  have e : u - g = S.generator ⟨u, hu⟩ := by rw [hg]; abel
  rw [e] at h2
  refine h2.congr (fun n => ?_)
  rw [← ha n]; abel

/-! ### S10: ergodicity -/

lemma tendsto_eLpNorm_of_Lp {v : ℕ → Lp ℝ 2 ouDiff.μ} {w : Lp ℝ 2 ouDiff.μ} {F : ℕ → ℝ → ℝ} {W : ℝ → ℝ}
    (hv : Tendsto v atTop (𝓝 w)) (hF : ∀ n, (v n : ℝ → ℝ) =ᵐ[γ] F n) (hW : (w : ℝ → ℝ) =ᵐ[γ] W) :
    Tendsto (fun n => eLpNorm (F n - W) 2 γ) atTop (𝓝 0) := by
  have := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' v w).1 hv
  refine this.congr fun n => ?_
  exact eLpNorm_congr_ae ((hF n).sub hW)

/-- **S10**: `u ∈ 𝒟(L)`, `L u = 0` ⇒ `u` is a.e. constant. -/
theorem ou_ergodic_new (u : Lp ℝ 2 ouDiff.μ) (hu : u ∈ ouDiff.generator.domain)
    (h0 : ouDiff.generator ⟨u, hu⟩ = 0) : ∃ c : ℝ, (u : ℝ → ℝ) =ᵐ[γ] fun _ => c := by
  obtain ⟨a, ha1, ha2⟩ := ou_esa_core u hu
  rw [h0] at ha2
  refine ou_ergodic_aux u ⟨fun n => (a n).1, fun n => (a n).2, ?_, ?_⟩
  · exact tendsto_eLpNorm_of_Lp ha1 (fun n => DiffusionTriple.coeFn_cls ouDiff (a n))
      (EventuallyEq.refl _ _)
  · have := tendsto_eLpNorm_of_Lp (F := fun n => Lo (a n).1) (W := 0) ha2
      (fun n => DiffusionTriple.coeFn_Lcls ouDiff (a n)) (Lp.coeFn_zero ℝ 2 γ)
    simpa only [sub_zero] using this

/-! ### S11: conservativeness -/

lemma one2_eq_hL : ouDiff.one2 = hL 0 := by
  refine Lp.ext ?_
  filter_upwards [ouDiff.coeFn_one2, (hh_memLp 0).coeFn_toLp] with x h1 h2
  calc _ = (1 : ℝ) := h1
    _ = hh 0 x := by rw [hh_zero]
    _ = _ := h2.symm

/-- `P_t 1 = 1` in `L²(γ)`: `1 = h_0` is the eigenfunction for the eigenvalue `0`. -/
theorem Pt_one (t : ℝ≥0) : ouDiff.semigroup t ouDiff.one2 = ouDiff.one2 := by
  rw [one2_eq_hL]
  have := Pt_hL 0 t
  simp only [Nat.cast_zero, neg_zero, zero_mul, Real.exp_zero, one_smul] at this
  exact this

/-- **S11**: for every exhaustion sequence, `P_t u_n → 1` a.e. -/
theorem ou_conservative_new {u : ℕ → ℝ → ℝ} (hu : IsExhaustion ouDiff.μ ouDiff.A₀ u) (t : ℝ≥0) :
    ∀ᵐ x ∂ouDiff.μ, Tendsto (fun n => (ouDiff.semigroup t
      (ouDiff.cls ⟨u n, hu.1 n⟩) : ℝ → ℝ) x) atTop (𝓝 1) :=
  ouDiff.conservative_of_semigroup_one hu t (Pt_one t)

end MarkovTriple.BGL.Instances.OU
