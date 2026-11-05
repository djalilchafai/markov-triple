import Mathlib
import MarkovTriple.BGL.Instances.SphereN.Full.Density
import MarkovTriple.BGL.Instances.Circle.Semigroup
import MarkovTriple.BGL.Semigroup.ESA
import MarkovTriple.BGL.Semigroup.Mass
import MarkovTriple.BGL.Semigroup.Characterization

/-!
# Spectral consequences on `S^{n-1}` (Round 29, stream N, group N3)

* `sphere_semigroup_harm`: `P_t [h] = e^{-k(k+n-2)t} [h]` for harmonic homogeneous `h` of degree `k`;
* `core_of_dense_range` (generic) and `sphere_esa`: F10 (ESA) from the dense eigenfunction family;
* `sphere_ergodic` (S10) and `sphere_semigroup_one`, S11; `sphereStandard`;
* `sphere_semigroup_poly_mem`: for restrictions of polynomials, `P_t` stays in `C^∞` (finite combination of harmonics).
-/

open MeasureTheory Filter Topology Set MvPolynomial
open scoped NNReal LinearPMap InnerProductSpace ENNReal

namespace MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E] (T : DiffusionTriple E)

namespace DiffusionTriple

/-- **ESA from a dense range of `1 - L`.**  If `(1 - L)𝒜₀` is dense in `L²`, then `𝒜₀` is a core for the
Friedrichs generator (same final step as `core_of_invariant`). -/
theorem core_of_dense_range
    (hM : (LinearMap.range (clsₗ T - Lclsₗ T)).topologicalClosure = ⊤)
    (u : Lp ℝ 2 T.μ) (hu : u ∈ T.generator.domain) :
    ∃ a : ℕ → T.A₀, Tendsto (fun n => T.cls (a n)) atTop (𝓝 u) ∧
      Tendsto (fun n => T.Lcls (a n)) atTop (𝓝 (T.generator ⟨u, hu⟩)) := by
  set S := formData T with hS
  let M : Submodule ℝ (Lp ℝ 2 T.μ) := (LinearMap.range (clsₗ T - Lclsₗ T))
  have hdense : Dense (M : Set (Lp ℝ 2 T.μ)) := Submodule.dense_iff_topologicalClosure_eq_top.2 hM
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

/-- if `w` is orthogonal to a family whose span is dense, then `w = 0`. -/
lemma eq_zero_of_orth_dense {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (S : Set H)
    (hd : (Submodule.span ℝ S).topologicalClosure = ⊤) (w : H) (h : ∀ v ∈ S, inner ℝ v w = 0) :
    w = 0 := by
  have hker : Submodule.span ℝ S ≤ (innerSL ℝ w).ker := by
    rw [Submodule.span_le]
    intro v hv
    show innerSL ℝ w v = 0
    rw [innerSL_apply_apply, real_inner_comm]
    exact h v hv
  have hcl : (Submodule.span ℝ S).topologicalClosure ≤ (innerSL ℝ w).ker :=
    Submodule.topologicalClosure_minimal _ hker (innerSL ℝ w).isClosed_ker
  rw [hd] at hcl
  have : w ∈ (innerSL ℝ w).ker := hcl Submodule.mem_top
  have h0 : innerSL ℝ w w = 0 := this
  rw [innerSL_apply_apply] at h0
  exact inner_self_eq_zero.1 h0

end DiffusionTriple

end MarkovTriple.BGL

namespace MarkovTriple.BGL.SphereN

open LebesgueRd

variable {n : ℕ}

/-- eigenvalue of degree `k`. -/
noncomputable def lamS (n k : ℕ) : ℝ := (k : ℝ) * (k + n - 2)

lemma lamS_nonneg (hn : 2 ≤ n) (k : ℕ) : 0 ≤ lamS n k := by
  unfold lamS
  have : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  nlinarith

lemma lamS_pos (hn : 2 ≤ n) {k : ℕ} (hk : k ≠ 0) : 0 < lamS n k := by
  unfold lamS
  have : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
  nlinarith

/-- the harmonic eigenfunction as an element of `𝒜₀`. -/
noncomputable def hA (hn : 2 ≤ n) (h : Pn n) : (sphereDiffusion n hn).A₀ := ⟨restr h, restr_mem h⟩

lemma L_hA (hn : 2 ≤ n) {k : ℕ} {h : Pn n} (hh : IsHarm k h) (x : Sph n) :
    (sphereDiffusion n hn).L (hA hn h).1 x = -(lamS n k) * (hA hn h).1 x := by
  have := congrFun (LS_restr_harm hh) x
  exact this

theorem sphere_semigroup_harm (hn : 2 ≤ n) {k : ℕ} {h : Pn n} (hh : IsHarm k h) (t : ℝ≥0) :
    (sphereDiffusion n hn).semigroup t ((sphereDiffusion n hn).cls ⟨restr h, restr_mem h⟩)
      = Real.exp (-((k : ℝ) * (k + n - 2)) * t) • (sphereDiffusion n hn).cls ⟨restr h, restr_mem h⟩ :=
  DiffusionTriple.semigroup_cls_eigen (sphereDiffusion n hn) (hA hn h) (lamS_nonneg hn k)
    (L_hA hn hh) t

lemma R_hA (hn : 2 ≤ n) {k : ℕ} {h : Pn n} (hh : IsHarm k h) :
    (DiffusionTriple.formData (sphereDiffusion n hn)).R ((sphereDiffusion n hn).cls (hA hn h))
      = (1 + lamS n k)⁻¹ • (sphereDiffusion n hn).cls (hA hn h) :=
  DiffusionTriple.R_cls_eigen (sphereDiffusion n hn) (hA hn h) (lamS_nonneg hn k)
    (DiffusionTriple.Lcls_eq_smul (sphereDiffusion n hn) (L_hA hn hh))

/-- **F10 (ESA) on the sphere**, from the dense family of harmonic eigenfunctions. -/
theorem sphere_esa (hn : 2 ≤ n) (u : Lp ℝ 2 (sphereDiffusion n hn).μ)
    (hu : u ∈ (sphereDiffusion n hn).generator.domain) :
    ∃ a : ℕ → (sphereDiffusion n hn).A₀,
      Tendsto (fun m => (sphereDiffusion n hn).cls (a m)) atTop (𝓝 u) ∧
        Tendsto (fun m => (sphereDiffusion n hn).Lcls (a m)) atTop
          (𝓝 ((sphereDiffusion n hn).generator ⟨u, hu⟩)) := by
  refine DiffusionTriple.core_of_dense_range (sphereDiffusion n hn) ?_ u hu
  refine top_le_iff.1 ?_
  rw [← dense_span_harm hn]
  refine Submodule.topologicalClosure_mono ?_
  rw [Submodule.span_le]
  rintro _ ⟨f, ⟨k, h, hh, hf⟩, rfl⟩
  have hfA : f = hA hn h := Subtype.ext hf
  subst hfA
  have hc : 0 < 1 + lamS n k := by have := lamS_nonneg hn k; linarith
  refine ⟨((1 + lamS n k)⁻¹) • hA hn h, ?_⟩
  rw [LinearMap.sub_apply, map_smul, map_smul, ← smul_sub]
  show ((1 + lamS n k)⁻¹) • ((sphereDiffusion n hn).cls (hA hn h) - (sphereDiffusion n hn).Lcls (hA hn h)) = _
  rw [DiffusionTriple.Lcls_eq_smul _ (L_hA hn hh)]
  have : (sphereDiffusion n hn).cls (hA hn h) - (-(lamS n k)) • (sphereDiffusion n hn).cls (hA hn h)
      = (1 + lamS n k) • (sphereDiffusion n hn).cls (hA hn h) := by module
  rw [this, smul_smul, inv_mul_cancel₀ hc.ne', one_smul]

/-! ### ergodicity, conservativeness -/

lemma inner_zero_of_fixed (hn : 2 ≤ n) {e u : Lp ℝ 2 (sphereDiffusion n hn).μ} {c : ℝ} (hc : 0 < c)
    (he : (DiffusionTriple.formData (sphereDiffusion n hn)).R e = (1 + c)⁻¹ • e)
    (hu : (DiffusionTriple.formData (sphereDiffusion n hn)).R u = u) : inner ℝ e u = 0 := by
  have hs : IsSelfAdjoint (DiffusionTriple.formData (sphereDiffusion n hn)).R :=
    (DiffusionTriple.formData (sphereDiffusion n hn)).R_isSelfAdjoint
  have hsym : inner ℝ ((DiffusionTriple.formData (sphereDiffusion n hn)).R e) u =
      inner ℝ e ((DiffusionTriple.formData (sphereDiffusion n hn)).R u) :=
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1 hs) e u
  rw [he, hu, real_inner_smul_left] at hsym
  have hlt : (1 + c)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  by_contra hne
  have : (1 + c)⁻¹ = 1 := by
    have := mul_right_cancel₀ hne (show (1 + c)⁻¹ * inner ℝ e u = 1 * inner ℝ e u by rw [one_mul]; exact hsym)
    exact this
  linarith

lemma restr_const_of_hom0 {h : Pn n} (hh : h.IsHomogeneous 0) : ∃ a : ℝ, restr h = fun _ => a := by
  have h0 : h.totalDegree = 0 := by
    have := hh.totalDegree_le
    omega
  have ha := (totalDegree_eq_zero_iff_eq_C).1 h0
  refine ⟨h.coeff 0, ?_⟩
  funext x
  calc restr h x = restr (C (h.coeff 0)) x := congrArg (fun q => restr q x) ha
    _ = h.coeff 0 := by simp [restr]

lemma restr_one : restr (1 : Pn n) = fun _ => 1 := by
  funext x; simp [restr]

lemma isHarm_one : IsHarm 0 (1 : Pn n) := ⟨isHomogeneous_one _ _, by simp [lap]⟩

/-- **S10**: `u ∈ 𝒟(L)`, `L u = 0` ⇒ `u` is a.e. constant. -/
theorem sphere_ergodic (hn : 2 ≤ n) (u : Lp ℝ 2 (sphereDiffusion n hn).μ)
    (hu : u ∈ (sphereDiffusion n hn).generator.domain)
    (hG : (sphereDiffusion n hn).generator ⟨u, hu⟩ = 0) :
    ∃ c : ℝ, (u : Sph n → ℝ) =ᵐ[(sphereDiffusion n hn).μ] fun _ => c := by
  have : IsProbabilityMeasure (σ n) := σ_isProbabilityMeasure (by omega)
  have hR : (DiffusionTriple.formData (sphereDiffusion n hn)).R (u - 0) = u :=
    ((DiffusionTriple.formData (sphereDiffusion n hn)).generator_apply_eq_iff hu 0).1 hG
  rw [sub_zero] at hR
  -- the constant function
  have hone : IsHarm 0 (1 : Pn n) := isHarm_one
  have hone1 : (sphereDiffusion n hn).cls (hA hn (1 : Pn n)) = (sphereDiffusion n hn).one2 := by
    refine Lp.ext ?_
    filter_upwards [DiffusionTriple.coeFn_cls (sphereDiffusion n hn) (hA hn (1 : Pn n)), (sphereDiffusion n hn).coeFn_one2] with x h1 h2
    rw [h1, h2]
    show restr (1 : Pn n) x = 1
    rw [restr_one]
  have hRone : (DiffusionTriple.formData (sphereDiffusion n hn)).R (sphereDiffusion n hn).one2 = (sphereDiffusion n hn).one2 := by
    have := R_hA hn hone
    rw [hone1] at this
    simpa [lamS] using this
  have hnorm : inner ℝ (sphereDiffusion n hn).one2 (sphereDiffusion n hn).one2 = (1 : ℝ) := by
    rw [L2_inner_eq]
    have : ∫ x, ((sphereDiffusion n hn).one2 : Sph n → ℝ) x * (sphereDiffusion n hn).one2 x ∂(sphereDiffusion n hn).μ = ∫ x, (1 : ℝ) ∂(sphereDiffusion n hn).μ := by
      refine integral_congr_ae ?_
      filter_upwards [(sphereDiffusion n hn).coeFn_one2] with x h1
      rw [h1]; norm_num
    rw [this]
    simp
  set ubar : ℝ := inner ℝ (sphereDiffusion n hn).one2 u with hub
  set w : Lp ℝ 2 (sphereDiffusion n hn).μ := u - ubar • (sphereDiffusion n hn).one2 with hw
  have hw0 : w = 0 := by
    refine DiffusionTriple.eq_zero_of_orth_dense ((sphereDiffusion n hn).cls '' harmSet n hn) (dense_span_harm hn) w ?_
    rintro _ ⟨f, ⟨k, h, hh, hf⟩, rfl⟩
    have hfA : f = hA hn h := Subtype.ext hf
    subst hfA
    by_cases hk : k = 0
    · subst hk
      obtain ⟨a, ha⟩ := restr_const_of_hom0 hh.1
      have hcls : (sphereDiffusion n hn).cls (hA hn h) = a • (sphereDiffusion n hn).one2 := by
        refine Lp.ext ?_
        filter_upwards [DiffusionTriple.coeFn_cls (sphereDiffusion n hn) (hA hn h), (sphereDiffusion n hn).coeFn_one2,
          Lp.coeFn_smul a (sphereDiffusion n hn).one2] with x h1 h2 h3
        rw [h1, h3, Pi.smul_apply, h2]
        show restr h x = a • 1
        rw [ha]; simp
      rw [hcls, real_inner_smul_left, hw, inner_sub_right, real_inner_smul_right, hnorm]
      simp [hub]
    · have hc := lamS_pos hn hk
      have e1 := inner_zero_of_fixed hn hc (R_hA hn hh) hR
      have e2 := inner_zero_of_fixed hn hc (R_hA hn hh) hRone
      rw [hw, inner_sub_right, real_inner_smul_right, e1, e2]; simp
  refine ⟨ubar, ?_⟩
  have : u = ubar • (sphereDiffusion n hn).one2 := sub_eq_zero.1 hw0
  filter_upwards [Lp.coeFn_smul ubar (sphereDiffusion n hn).one2, (sphereDiffusion n hn).coeFn_one2] with x h1 h2
  rw [this, h1, Pi.smul_apply, h2]
  simp

/-- `P_t 1 = 1` in `L²`. -/
theorem sphere_semigroup_one (hn : 2 ≤ n) (t : ℝ≥0) :
    (sphereDiffusion n hn).semigroup t ((sphereDiffusion n hn).cls ⟨1, (A₀S n).one_mem⟩)
      = (sphereDiffusion n hn).cls ⟨1, (A₀S n).one_mem⟩ := by
  have h := sphere_semigroup_harm hn (isHarm_one (n := n)) t
  have e : (⟨restr (1 : Pn n), restr_mem 1⟩ : (sphereDiffusion n hn).A₀) = ⟨1, (A₀S n).one_mem⟩ :=
    Subtype.ext restr_one
  rw [e] at h
  rw [h]
  simp

/-- **The Standard Markov Triple of the round sphere** (S10, S11). -/
noncomputable def sphereStandard (hn : 2 ≤ n) : StandardTriple (Sph n) where
  toDiffusionTriple := sphereDiffusion n hn
  ergodic := fun u hu h => sphere_ergodic hn u hu h
  conservative := fun u hu _ t => by
    have : IsProbabilityMeasure (σ n) := σ_isProbabilityMeasure (by omega)
    refine DiffusionTriple.conservative_of_semigroup_one (sphereDiffusion n hn) hu t ?_
    have h := sphere_semigroup_one hn t
    have e : (sphereDiffusion n hn).cls ⟨1, (A₀S n).one_mem⟩ = (sphereDiffusion n hn).one2 := by
      refine Lp.ext ?_
      filter_upwards [DiffusionTriple.coeFn_cls (sphereDiffusion n hn) ⟨1, (A₀S n).one_mem⟩,
        (sphereDiffusion n hn).coeFn_one2] with x h1 h2
      rw [h1, h2]; rfl
    rw [e] at h
    exact h

/-! ### smoothing of polynomial data -/

/-- the `L²`-classes with a `C^∞` representative form a subspace. -/
def smoothCls (n : ℕ) : Submodule ℝ (Lp ℝ 2 (σ n)) where
  carrier := {u | ∃ g ∈ A₀S n, (u : Sph n → ℝ) =ᵐ[σ n] g}
  add_mem' := by
    rintro u v ⟨g, hg, hug⟩ ⟨g', hg', hvg⟩
    refine ⟨g + g', add_mem hg hg', ?_⟩
    filter_upwards [Lp.coeFn_add u v, hug, hvg] with x h1 h2 h3
    rw [h1, Pi.add_apply, h2, h3]; rfl
  zero_mem' := ⟨0, zero_mem _, Lp.coeFn_zero _ _ _⟩
  smul_mem' := by
    rintro c u ⟨g, hg, hug⟩
    refine ⟨c • g, Subalgebra.smul_mem _ hg c, ?_⟩
    filter_upwards [Lp.coeFn_smul c u, hug] with x h1 h2
    rw [h1, Pi.smul_apply, h2]; rfl

/-- **F8 for polynomial data**: `P_t` maps the class of the restriction of a polynomial to a class with a
`C^∞` representative. -/
theorem sphere_semigroup_poly_mem (hn : 2 ≤ n) (t : ℝ≥0) (p : Pn n) :
    ∃ g ∈ A₀S n, ((sphereDiffusion n hn).semigroup t ((sphereDiffusion n hn).cls ⟨restr p, restr_mem p⟩)
      : Sph n → ℝ) =ᵐ[σ n] g := by
  let Φ0 : Pn n →ₗ[ℝ] Lp ℝ 2 (σ n) :=
    (ContinuousMap.toLp (E := ℝ) 2 (σ n) ℝ).toLinearMap.comp restrA.toLinearMap
  let Φ : Pn n →ₗ[ℝ] Lp ℝ 2 (σ n) := ((sphereDiffusion n hn).semigroup t).toLinearMap.comp Φ0
  have key : Φ p ∈ smoothCls n := by
    refine map_mem_of_harm (by omega) Φ (smoothCls n) (fun j k h hh => ?_) p
    have e : restrA ((rsq : Pn n) ^ j * h) = restrA h := by
      ext x
      rw [restrA_apply, restrA_apply, restr_pow_rsq_mul]
    show (sphereDiffusion n hn).semigroup t
      (ContinuousMap.toLp (E := ℝ) 2 (σ n) ℝ (restrA ((rsq : Pn n) ^ j * h))) ∈ smoothCls n
    rw [e, ← cls_restr hn h, sphere_semigroup_harm hn hh t]
    refine Submodule.smul_mem _ _ ⟨restr h, restr_mem h, ?_⟩
    exact DiffusionTriple.coeFn_cls (sphereDiffusion n hn) ⟨restr h, restr_mem h⟩
  have e : Φ p = (sphereDiffusion n hn).semigroup t ((sphereDiffusion n hn).cls ⟨restr p, restr_mem p⟩) := by
    show (sphereDiffusion n hn).semigroup t
      (ContinuousMap.toLp (E := ℝ) 2 (σ n) ℝ (restrA p)) = _
    rw [← cls_restr hn p]
  rw [e] at key
  exact key

end MarkovTriple.BGL.SphereN
