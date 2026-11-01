import Mathlib
import MarkovTriple.BGL.Frozen.CompactTriple
import MarkovTriple.BGL.Frozen.Classes
import MarkovTriple.BGL.SemigroupLemmas

/-!
# Essential self-adjointness is automatic when `𝒜 = 𝒜₀` (BGL Def. 3.3.26 and the remark after it)

The F10 field (`𝒜₀` is a core for the Friedrichs generator `L`) follows from F8 (`P_t` maps
`𝒜₀`-classes to `𝒜₀`-classes when `𝒜 = 𝒜₀`).  The argument is the classical "dense invariant domain is
a core" (Nelson / Reed–Simon X.49), in resolvent form:

1. `Hilbert.FormData.semigroup_generator_comm`: `P_t` maps `𝒟(G)` into itself and commutes with `G`.
2. If `w ⊥ (1 − G) 𝒜₀`, put `φ(s) = ⟪P_s a, w⟫` (`a ∈ 𝒜₀`).  Because `P_s a` is again in `𝒜₀` and
   `P_s G a = G P_s a`, `φ' = φ` on `s > 0`; as `φ` is bounded, `φ(0) = 0`, i.e. `w ⊥ 𝒜₀`, so `w = 0`.
3. Hence `(1 − G) 𝒜₀` is dense, and `a_n ∈ 𝒜₀` with `(1−G)a_n → (1−G)u` give `a_n → u`, `L a_n → G u`.

`core_of_invariant` is for any `DiffusionTriple` whose semigroup preserves the classes of `𝒜₀`;
`CompactTriple.esa_auto` applies it to a compact triple (F8 + `𝒜 = 𝒜₀`).
-/

open MeasureTheory Filter Topology Set
open scoped NNReal LinearPMap InnerProductSpace

namespace MarkovTriple.Hilbert.FormData

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  (S : FormData H)

/-- `P_t` preserves `𝒟(G)` and commutes with `G` on it. -/
theorem semigroup_generator_comm {x : H} (hx : x ∈ S.generator.domain) (t : ℝ≥0) :
    ∃ h : S.semigroup t x ∈ S.generator.domain,
      S.generator ⟨S.semigroup t x, h⟩ = S.semigroup t (S.generator ⟨x, hx⟩) := by
  obtain ⟨g, hg⟩ : ∃ g : H, g = x - S.generator ⟨x, hx⟩ := ⟨_, rfl⟩
  have hR : S.R g = x := by rw [hg]; exact (S.generator_apply_eq_iff hx _).1 rfl
  have hPx : S.semigroup t x = S.R (S.semigroup t g) := by
    rw [← hR, S.semigroup_comm_R]
  obtain ⟨h, hG⟩ := S.generator_R (S.semigroup t g)
  have hmem : S.semigroup t x ∈ S.generator.domain := by rw [hPx]; exact h
  refine ⟨hmem, ?_⟩
  have e1 : S.generator ⟨S.semigroup t x, hmem⟩ = S.R (S.semigroup t g) - S.semigroup t g := by
    have : (⟨S.semigroup t x, hmem⟩ : S.generator.domain) = ⟨S.R (S.semigroup t g), h⟩ :=
      Subtype.ext hPx
    rw [this, hG]
  have e2 : S.generator ⟨x, hx⟩ = x - g := by rw [hg]; abel
  rw [e1, e2, map_sub, hPx]

end MarkovTriple.Hilbert.FormData

namespace MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E] (T : DiffusionTriple E)

namespace DiffusionTriple

lemma R_cls_sub (a : T.A₀) : (formData T).R (T.cls a - T.Lcls a) = T.cls a := by
  have h := (formData T).R_resolvent ⟨clsₗ T a, ⟨a, rfl⟩⟩
  have e : (formData T).opA ⟨clsₗ T a, ⟨a, rfl⟩⟩ = -T.Lcls a := formA_apply T a
  rw [e] at h
  have h' : (formData T).R (T.cls a + -T.Lcls a) = T.cls a := h
  simpa [sub_eq_add_neg] using h'

/-- If the semigroup preserves the classes of test functions, then `w ⊥ (1 − G)𝒜₀` forces `w ⊥ 𝒜₀`. -/
lemma orth_of_invariant
    (hinv : ∀ (t : ℝ≥0) (f : T.A₀), ∃ g : T.A₀, T.semigroup t (T.cls f) = T.cls g)
    (w : Lp ℝ 2 T.μ) (hw : ∀ a : T.A₀, inner ℝ (T.cls a - T.Lcls a) w = 0) (a : T.A₀) :
    inner ℝ (T.cls a) w = 0 := by
  set S := formData T with hS
  set g : Lp ℝ 2 T.μ := T.cls a - T.Lcls a with hgdef
  have hRg : S.R g = T.cls a := R_cls_sub T a
  set φ : ℝ → ℝ := fun s => inner ℝ (S.semigroup s.toNNReal (T.cls a)) w with hφ
  -- derivative `φ' = φ` for `s > 0`
  have hderiv : ∀ t : ℝ, 0 < t → HasDerivAt φ (φ t) t := by
    intro t ht
    have h1 := S.hasDerivAt_semigroup ht g
    rw [hRg] at h1
    have h2 := h1.inner ℝ (hasDerivAt_const t w)
    refine h2.congr_deriv ?_
    obtain ⟨b, hb⟩ := hinv t.toNNReal a
    have hcomm := S.semigroup_generator_comm (T.cls_mem_generator_domain a) t.toNNReal
    obtain ⟨hdom, hG⟩ := hcomm
    have hGa : S.generator ⟨T.cls a, T.cls_mem_generator_domain a⟩ = T.Lcls a :=
      T.generator_cls a _
    have hPL : S.semigroup t.toNNReal (T.Lcls a) = T.Lcls b := by
      rw [← hGa, ← hG]
      have hmemb : T.cls b ∈ S.generator.domain := T.cls_mem_generator_domain b
      have : (⟨S.semigroup t.toNNReal (T.cls a), hdom⟩ : S.generator.domain) = ⟨T.cls b, hmemb⟩ :=
        Subtype.ext hb
      rw [this]
      exact T.generator_cls b hmemb
    have hgc : g - T.cls a = -T.Lcls a := by rw [hgdef]; abel
    have hb' : S.semigroup t.toNNReal (T.cls a) = T.cls b := hb
    rw [hgc, map_neg, neg_neg, hPL]
    have := hw b
    rw [inner_sub_left] at this
    simp only [hφ, inner_zero_right, zero_add]
    rw [hb']
    linarith
  have hcont : Continuous φ := by
    have : Continuous fun s : ℝ => S.semigroup s.toNNReal (T.cls a) :=
      (S.continuous_semigroup_apply (T.cls a)).comp continuous_real_toNNReal
    exact this.inner continuous_const
  set ψ : ℝ → ℝ := fun s => Real.exp (-s) * φ s with hψ
  have hψc : Continuous ψ := (Real.continuous_exp.comp continuous_neg).mul hcont
  have hψd : ∀ t : ℝ, 0 < t → HasDerivAt ψ 0 t := by
    intro t ht
    have h1 : HasDerivAt (fun s : ℝ => Real.exp (-s)) (-Real.exp (-t)) t := by
      have := (hasDerivAt_neg t).exp
      simpa using this
    have := h1.mul (hderiv t ht)
    refine this.congr_deriv ?_
    ring
  have hconst : ∀ t : ℝ, 0 < t → ψ 0 = ψ t := by
    intro t ht
    have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), ψ s = ψ t := by
      filter_upwards [Ioo_mem_nhdsGT ht] with s hs
      have := constant_of_has_deriv_right_zero (f := ψ) (a := s) (b := t) hψc.continuousOn
        (fun x hx => (hψd x (lt_of_lt_of_le hs.1 hx.1)).hasDerivWithinAt) t
        ⟨hs.2.le, le_rfl⟩
      exact this.symm
    have h1 : Tendsto ψ (𝓝[>] (0 : ℝ)) (𝓝 (ψ 0)) := hψc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have h2 : Tendsto ψ (𝓝[>] (0 : ℝ)) (𝓝 (ψ t)) := tendsto_const_nhds.congr' (hev.mono fun s hs => hs.symm)
    exact tendsto_nhds_unique h1 h2
  -- `φ(0) = ⟪a, w⟫` and boundedness
  have h0 : φ 0 = inner ℝ (T.cls a) w := by
    simp [hφ, S.semigroup_zero]
  set B : ℝ := ‖T.cls a‖ * ‖w‖ with hB
  have hbd : ∀ t : ℝ, |φ t| ≤ B := by
    intro t
    calc |φ t| ≤ ‖S.semigroup t.toNNReal (T.cls a)‖ * ‖w‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖T.cls a‖ * ‖w‖ := by
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        calc ‖S.semigroup t.toNNReal (T.cls a)‖ ≤ ‖S.semigroup t.toNNReal‖ * ‖T.cls a‖ :=
              (S.semigroup _).le_opNorm _
          _ ≤ 1 * ‖T.cls a‖ := mul_le_mul_of_nonneg_right (S.norm_semigroup_le _) (norm_nonneg _)
          _ = ‖T.cls a‖ := one_mul _
  have hle : ∀ t : ℝ, 0 < t → |φ 0| ≤ Real.exp (-t) * B := by
    intro t ht
    have := hconst t ht
    have e : φ 0 = ψ 0 := by simp [hψ]
    rw [e, this]
    simp only [hψ, abs_mul, Real.abs_exp]
    exact mul_le_mul_of_nonneg_left (hbd t) (Real.exp_pos _).le
  have hlim : Tendsto (fun t : ℝ => Real.exp (-t) * B) atTop (𝓝 0) := by
    simpa using (Real.tendsto_exp_neg_atTop_nhds_zero).mul_const B
  have : |φ 0| ≤ 0 := ge_of_tendsto hlim (by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    exact hle t ht)
  have h00 : φ 0 = 0 := abs_nonpos_iff.1 this
  rw [← h0]; exact h00

/-- **`𝒜₀` is a core for the Friedrichs generator as soon as the semigroup preserves the classes of
`𝒜₀`.** -/
theorem core_of_invariant
    (hinv : ∀ (t : ℝ≥0) (f : T.A₀), ∃ g : T.A₀, T.semigroup t (T.cls f) = T.cls g)
    (u : Lp ℝ 2 T.μ) (hu : u ∈ T.generator.domain) :
    ∃ a : ℕ → T.A₀, Tendsto (fun n => T.cls (a n)) atTop (𝓝 u) ∧
      Tendsto (fun n => T.Lcls (a n)) atTop (𝓝 (T.generator ⟨u, hu⟩)) := by
  set S := formData T with hS
  -- the subspace `(1 − G) 𝒜₀` is dense
  let M : Submodule ℝ (Lp ℝ 2 T.μ) := (LinearMap.range (clsₗ T - Lclsₗ T))
  have hM : M.topologicalClosure = ⊤ := by
    rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
    intro w hw
    rw [Submodule.mem_orthogonal] at hw
    have h1 : ∀ a : T.A₀, inner ℝ (T.cls a - T.Lcls a) w = 0 := fun a =>
      hw _ ⟨a, rfl⟩
    exact eq_zero_of_orth T w (fun g => by
      rw [real_inner_comm]; exact orth_of_invariant T hinv w h1 g)
  have hdense : Dense (M : Set (Lp ℝ 2 T.μ)) := by
    exact Submodule.dense_iff_topologicalClosure_eq_top.2 hM
  set g : Lp ℝ 2 T.μ := u - S.generator ⟨u, hu⟩ with hg
  obtain ⟨m, hmM, hmg⟩ := mem_closure_iff_seq_limit.1 (hdense.closure_eq ▸ Set.mem_univ g)
  have hm : ∀ n, ∃ a : T.A₀, T.cls a - T.Lcls a = m n := by
    intro n
    obtain ⟨a, ha⟩ := hmM n
    exact ⟨a, ha⟩
  choose a ha using hm
  have hRu : S.R g = u := (S.generator_apply_eq_iff hu _).1 rfl
  have h1 : Tendsto (fun n => T.cls (a n)) atTop (𝓝 u) := by
    have : Tendsto (fun n => S.R (m n)) atTop (𝓝 (S.R g)) := (S.R.continuous.tendsto g).comp hmg
    rw [hRu] at this
    refine this.congr (fun n => ?_)
    rw [← ha n]; exact R_cls_sub T (a n)
  refine ⟨a, h1, ?_⟩
  have h2 : Tendsto (fun n => T.cls (a n) - m n) atTop (𝓝 (u - g)) := h1.sub hmg
  have e : u - g = S.generator ⟨u, hu⟩ := by rw [hg]; abel
  rw [e] at h2
  refine h2.congr (fun n => ?_)
  rw [← ha n]; abel

end DiffusionTriple

/-- **ESA is automatic for compact triples** (BGL Def. 3.3.26 and the remark following it): for a
`CompactTriple` (`𝒜 = 𝒜₀`), F8 (`P_t` maps `𝒜₀` into `𝒜 = 𝒜₀`) implies F10, so the `esa` field is
redundant.  (The F10 field of `FullTriple` is thus a theorem on `CompactTriple`s.) -/
theorem CompactTriple.esa_auto (C : CompactTriple E) :
    ∀ (u : Lp ℝ 2 C.μ) (hu : u ∈ C.toDiffusionTriple.generator.domain),
      ∃ a : ℕ → C.A₀, Tendsto (fun n => C.toDiffusionTriple.cls (a n)) atTop (𝓝 u) ∧
        Tendsto (fun n => C.toDiffusionTriple.Lcls (a n)) atTop
          (𝓝 (C.toDiffusionTriple.generator ⟨u, hu⟩)) := by
  refine DiffusionTriple.core_of_invariant C.toDiffusionTriple (fun t f => ?_)
  obtain ⟨g, hgA, hg⟩ := C.semigroup_A t f
  have hg0 : g ∈ C.A₀ := (C.A_eq g).1 hgA
  refine ⟨⟨g, hg0⟩, Lp.ext ?_⟩
  exact hg.trans (DiffusionTriple.coeFn_cls C.toDiffusionTriple ⟨g, hg0⟩).symm

end MarkovTriple.BGL
