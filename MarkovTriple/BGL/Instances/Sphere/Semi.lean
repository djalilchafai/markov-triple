import Mathlib
import MarkovTriple.BGL.Instances.Sphere.Triple
import MarkovTriple.BGL.Semigroup.ESA
import MarkovTriple.BGL.Semigroup.Mass
import MarkovTriple.BGL.Semigroup.Characterization
import MarkovTriple.BGL.Instances.Circle.Semigroup

/-!
# The Friedrichs semigroup of the zonal sphere `S³`: diagonal action, smoothing, S10, S11

`P_t e_k = e^{-k(k+2) t} e_k`; for `t > 0` and `u ∈ L²`, `P_t u = Σ e^{-k(k+2)t} ⟨e_k,u⟩ e_k`
is a.e. equal to a function of `𝒜` (the series converges in `C^∞`, since `U_k^{(m)} = O(k^{m+1})`).
-/

open MeasureTheory Real Set Filter Topology
open scoped ENNReal NNReal InnerProductSpace
open MarkovTriple.Sanity.OU (Sm)

namespace MarkovTriple.BGL.Instances.Sphere

/-- the Friedrichs semigroup of the sphere triple, with `μZ` visible in its type. -/
noncomputable abbrev PZ (t : ℝ≥0) : Lp ℝ 2 μZ →L[ℝ] Lp ℝ 2 μZ := sT.semigroup t

noncomputable abbrev RZ : Lp ℝ 2 μZ →L[ℝ] Lp ℝ 2 μZ := (DiffusionTriple.formData sT).R

/-- eigenvalue -/
def lamZ (k : ℕ) : ℝ := (k : ℝ) * (k + 2)

lemma lamZ_nonneg (k : ℕ) : 0 ≤ lamZ k := by unfold lamZ; positivity

lemma lamZ_pos {k : ℕ} (hk : k ≠ 0) : 0 < lamZ k := by
  unfold lamZ
  have : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
  positivity

lemma cls_UZ (k : ℕ) : sT.cls ⟨UZ k, UZ_mem k⟩ = eZ k := rfl

lemma semigroup_eZ (t : ℝ≥0) (k : ℕ) : PZ t (eZ k) = Real.exp (-lamZ k * t) • eZ k :=
  DiffusionTriple.semigroup_cls_eigen sT ⟨UZ k, UZ_mem k⟩ (lamZ_nonneg k)
    (fun x => by
      show LZ (UZ k) x = _
      rw [LZ_UZ]; rfl) t

lemma RZ_eZ (k : ℕ) : RZ (eZ k) = (1 + lamZ k)⁻¹ • eZ k :=
  DiffusionTriple.R_cls_eigen sT ⟨UZ k, UZ_mem k⟩ (lamZ_nonneg k)
    (DiffusionTriple.Lcls_eq_smul sT (fun x => by
      show LZ (UZ k) x = _
      rw [LZ_UZ]; rfl))

lemma inner_PZ (t : ℝ≥0) (u v : Lp ℝ 2 μZ) : inner ℝ (PZ t u) v = inner ℝ u (PZ t v) := by
  have h : IsSelfAdjoint (PZ t) := DiffusionTriple.semigroup_isSelfAdjoint sT t
  exact (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1 h) u v

lemma inner_RZ (u v : Lp ℝ 2 μZ) : inner ℝ (RZ u) v = inner ℝ u (RZ v) := by
  have h : IsSelfAdjoint RZ := (DiffusionTriple.formData sT).R_isSelfAdjoint
  exact (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1 h) u v

/-- the Hilbert basis `(e_k)` of `L²(μ)`. -/
noncomputable def bZ : HilbertBasis ℕ ℝ (Lp ℝ 2 μZ) := HilbertBasis.mk orthonormal_eZ dense_span_eZ

lemma bZ_apply (k : ℕ) : bZ k = eZ k := by
  simp [bZ]

lemma norm_eZ (k : ℕ) : ‖eZ k‖ = 1 := orthonormal_eZ.1 k

lemma abs_Utheta_le (k : ℕ) (θ : ℝ) : |Utheta k θ| ≤ k + 1 := by
  have := abs_iteratedDeriv_Utheta_le 0 k θ
  simpa using this

/-! ### smoothing -/

/-- for `t > 0` and every `u ∈ L²`, `P_t u` is a.e. equal to a function of `𝒜`. -/
theorem smoothing {t : ℝ≥0} (ht : 0 < t) (u : Lp ℝ 2 μZ) :
    ∃ g ∈ AZ, ((PZ t u : Lp ℝ 2 μZ) : Zon → ℝ) =ᵐ[μZ] g := by
  set w : Lp ℝ 2 μZ := PZ t u with hw
  set c : ℕ → ℝ := fun k => inner ℝ (eZ k) w with hc
  have htr : (0 : ℝ) < t := by exact_mod_cast ht
  have hck : ∀ k, c k = Real.exp (-lamZ k * t) * inner ℝ (eZ k) u := by
    intro k
    simp only [hc, hw]
    rw [← inner_PZ, semigroup_eZ, real_inner_smul_left]
  have hbound : ∀ k, |c k| ≤ ‖u‖ * Real.exp (-t * k) := by
    intro k
    rw [hck, abs_mul, abs_of_pos (Real.exp_pos _)]
    have h1 : |inner ℝ (eZ k) u| ≤ ‖u‖ := by
      have := abs_real_inner_le_norm (eZ k) u
      rwa [norm_eZ, one_mul] at this
    have h2 : Real.exp (-lamZ k * t) ≤ Real.exp (-t * k) := by
      apply Real.exp_le_exp.2
      have : (k : ℝ) ≤ lamZ k := by
        unfold lamZ
        have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        nlinarith
      nlinarith
    calc Real.exp (-lamZ k * t) * |inner ℝ (eZ k) u|
        ≤ Real.exp (-t * k) * ‖u‖ := mul_le_mul h2 h1 (abs_nonneg _) (Real.exp_pos _).le
      _ = _ := by ring
  -- the series in `C(Zon, ℝ)`
  let UC : ℕ → C(Zon, ℝ) := fun k => ⟨UZ k, continuous_of_mem (UZ_mem k)⟩
  have hUCn : ∀ k, ‖UC k‖ ≤ k + 1 := by
    intro k
    refine (ContinuousMap.norm_le _ (by positivity)).2 fun x => ?_
    rw [Real.norm_eq_abs]
    show |UZ k x| ≤ _
    exact abs_Utheta_le k _
  have hsumm : Summable fun k : ℕ => ‖u‖ * Real.exp (-t * k) * ((k : ℝ) + 1) := by
    have h1 := Real.summable_pow_mul_exp_neg_nat_mul 1 htr
    have h0 := Real.summable_pow_mul_exp_neg_nat_mul 0 htr
    refine ((h1.add h0).mul_left ‖u‖).congr fun k => ?_
    simp only [pow_one, pow_zero, one_mul]; ring
  have hnorm : Summable fun k : ℕ => ‖c k • UC k‖ := by
    refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_) hsumm
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul (hbound k) (hUCn k) (norm_nonneg _) (by positivity)
  have hsm : Summable fun k : ℕ => c k • UC k := Summable.of_norm hnorm
  obtain ⟨G, hG⟩ : ∃ G : C(Zon, ℝ), G = ∑' k : ℕ, c k • UC k := ⟨_, rfl⟩
  have hsum : HasSum (fun k : ℕ => c k • UC k) G := by rw [hG]; exact hsm.hasSum
  have hL := (ContinuousMap.toLp (E := ℝ) 2 μZ ℝ).hasSum hsum
  have hL2 : HasSum (fun k : ℕ => c k • eZ k) w := by
    have := bZ.hasSum_repr w
    simpa [bZ_apply, bZ.repr_apply_apply, hc] using this
  have hLw : HasSum (fun k : ℕ => c k • eZ k) (ContinuousMap.toLp (E := ℝ) 2 μZ ℝ G) := by
    have e : ∀ k : ℕ, ContinuousMap.toLp (E := ℝ) 2 μZ ℝ (c k • UC k) = c k • eZ k := by
      intro k
      rw [map_smul]
      congr 1
    have e' : (fun k : ℕ => ContinuousMap.toLp (E := ℝ) 2 μZ ℝ (c k • UC k)) =
        fun k : ℕ => c k • eZ k := funext e
    rw [← e']; exact hL
  have hwG : w = ContinuousMap.toLp (E := ℝ) 2 μZ ℝ G := hL2.unique hLw
  have hae : (w : Zon → ℝ) =ᵐ[μZ] G := by
    rw [hwG]; exact ContinuousMap.coeFn_toLp _ _
  refine ⟨G, ?_, hae⟩
  -- `G` is zonal-smooth
  have hext : ext (G : Zon → ℝ) = fun θ => ∑' k : ℕ, c k * Utheta k θ := by
    funext θ
    have h := ContinuousMap.tsum_apply hsm (cosZ θ)
    show G (cosZ θ) = _
    rw [hG, ← h]
    refine tsum_congr fun k => ?_
    show c k * UZ k (cosZ θ) = _
    have : UZ k (cosZ θ) = Utheta k θ := by
      have := congrFun (ext_UZ k) θ
      exact this
    rw [this]
  show Sm (ext (G : Zon → ℝ))
  rw [hext]
  refine contDiff_tsum (N := (⊤ : ℕ∞)) (f := fun k θ => c k * Utheta k θ)
    (v := fun n k => ‖u‖ * Real.exp (-t * k) * (((k : ℝ) ^ (n + 1) + (k : ℝ) ^ n))) ?_ ?_ ?_
  · intro k
    exact contDiff_const.mul (contDiff_Utheta k)
  · intro n _
    have h1 := Real.summable_pow_mul_exp_neg_nat_mul (n + 1) htr
    have h0 := Real.summable_pow_mul_exp_neg_nat_mul n htr
    refine ((h1.add h0).mul_left ‖u‖).congr fun k => ?_
    ring
  · intro n k θ hn
    have hcd : ContDiff ℝ (⊤ : ℕ∞) (Utheta k) := contDiff_Utheta k
    have e1 : iteratedFDeriv ℝ n (fun θ => c k * Utheta k θ) θ =
        c k • iteratedFDeriv ℝ n (Utheta k) θ := by
      have := iteratedFDeriv_const_smul_apply (a := c k) (x := θ)
        (hcd.of_le (by exact_mod_cast le_top : (n : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞))).contDiffAt
      rw [show (fun θ => c k * Utheta k θ) = c k • Utheta k from rfl]
      exact this
    rw [e1, norm_smul, Real.norm_eq_abs]
    have h2 := norm_iteratedFDeriv_Utheta_le n k θ
    calc |c k| * ‖iteratedFDeriv ℝ n (Utheta k) θ‖
        ≤ (‖u‖ * Real.exp (-t * k)) * ((k + 1) * (k : ℝ) ^ n) :=
          mul_le_mul (hbound k) h2 (norm_nonneg _) (by positivity)
      _ = _ := by ring

theorem semigroup_cls_mem (t : ℝ≥0) (f : sT.A₀) :
    ∃ g ∈ AZ, (PZ t (sT.cls f) : Zon → ℝ) =ᵐ[μZ] g := by
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t) with h | ht
  · subst h
    refine ⟨f.1, f.2, ?_⟩
    have h0 : sT.semigroup 0 (sT.cls f) = sT.cls f := by
      rw [DiffusionTriple.semigroup_zero]; rfl
    show ((sT.semigroup 0 (sT.cls f) : Lp ℝ 2 μZ) : Zon → ℝ) =ᵐ[μZ] _
    rw [h0]
    exact DiffusionTriple.coeFn_cls sT f
  · exact smoothing ht (sT.cls f)

theorem semigroup_invariant (t : ℝ≥0) (f : sT.A₀) :
    ∃ g : sT.A₀, sT.semigroup t (sT.cls f) = sT.cls g := by
  obtain ⟨g, hg, hae⟩ := semigroup_cls_mem t f
  exact ⟨⟨g, hg⟩, Lp.ext (hae.trans (DiffusionTriple.coeFn_cls sT ⟨g, hg⟩).symm)⟩

/-! ### ergodicity and conservativeness -/

lemma inner_eq_zero_of_fixed {u : Lp ℝ 2 μZ} {k : ℕ} (hk : k ≠ 0) (hu : RZ u = u) :
    inner ℝ (eZ k) u = 0 := by
  have h1 : inner ℝ u (eZ k) = inner ℝ u (eZ k) * (1 + lamZ k)⁻¹ := by
    calc inner ℝ u (eZ k) = inner ℝ (RZ u) (eZ k) := by rw [hu]
      _ = inner ℝ u (RZ (eZ k)) := inner_RZ u _
      _ = _ := by rw [RZ_eZ, inner_smul_right, mul_comm]
  have hc : 0 < lamZ k := lamZ_pos hk
  have h2 : inner ℝ u (eZ k) = 0 := by
    have hk' : (1 + lamZ k)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
    by_contra hne
    have : (1 : ℝ) = (1 + lamZ k)⁻¹ := by
      have := mul_left_cancel₀ hne (show inner ℝ u (eZ k) * 1 = inner ℝ u (eZ k) * (1 + lamZ k)⁻¹ by
        rw [mul_one]; exact h1)
      exact this
    linarith
  rw [real_inner_comm]; exact h2

lemma coeFn_eZ_zero : (eZ 0 : Zon → ℝ) =ᵐ[μZ] fun _ => (1 : ℝ) := by
  filter_upwards [(memLp_of_mem (UZ_mem 0) 2).coeFn_toLp] with x hx
  rw [show (eZ 0 : Zon → ℝ) x = UZ 0 x from hx]
  simp [UZ, mk, Utheta]

/-- **S10**: `u ∈ 𝒟(L)`, `L u = 0` ⇒ `u` is a.e. constant. -/
theorem sphere_ergodic (u : Lp ℝ 2 sT.μ) (hu : u ∈ sT.generator.domain)
    (hG : sT.generator ⟨u, hu⟩ = 0) : ∃ c : ℝ, (u : Zon → ℝ) =ᵐ[sT.μ] fun _ => c := by
  have hR : (DiffusionTriple.formData sT).R (u - 0) = u :=
    ((DiffusionTriple.formData sT).generator_apply_eq_iff hu 0).1 hG
  rw [sub_zero] at hR
  have hR' : RZ (u : Lp ℝ 2 μZ) = u := hR
  have hs := bZ.hasSum_repr (u : Lp ℝ 2 μZ)
  have hz : ∀ k, k ≠ 0 → bZ.repr (u : Lp ℝ 2 μZ) k = 0 := by
    intro k hk
    rw [bZ.repr_apply_apply, bZ_apply]
    exact inner_eq_zero_of_fixed hk hR'
  have h1 : HasSum (fun k : ℕ => bZ.repr (u : Lp ℝ 2 μZ) k • bZ k)
      (bZ.repr (u : Lp ℝ 2 μZ) 0 • bZ 0) :=
    hasSum_single 0 (fun k hk => by rw [hz k hk, zero_smul])
  have h2 := hs.unique h1
  refine ⟨bZ.repr (u : Lp ℝ 2 μZ) 0, ?_⟩
  filter_upwards [Lp.coeFn_smul (bZ.repr (u : Lp ℝ 2 μZ) 0) (bZ 0), coeFn_eZ_zero] with x hx hy
  have : ((u : Lp ℝ 2 μZ) : Zon → ℝ) x = (bZ.repr (u : Lp ℝ 2 μZ) 0 • bZ 0 : Lp ℝ 2 μZ) x := by
    rw [← h2]
  rw [show ((u : Lp ℝ 2 sT.μ) : Zon → ℝ) x = ((u : Lp ℝ 2 μZ) : Zon → ℝ) x from rfl, this, hx]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [bZ_apply, hy, mul_one]

lemma eZ_zero_eq_one2 : (eZ 0 : Lp ℝ 2 μZ) = sT.one2 := by
  refine Lp.ext ?_
  filter_upwards [coeFn_eZ_zero, DiffusionTriple.coeFn_one2 (T := sT)] with x h1 h2
  rw [h1, h2]

lemma semigroup_one (t : ℝ≥0) : sT.semigroup t sT.one2 = sT.one2 := by
  have h := semigroup_eZ t 0
  rw [eZ_zero_eq_one2] at h
  have e : Real.exp (-lamZ 0 * t) = 1 := by simp [lamZ]
  rw [e, one_smul] at h
  exact h

end MarkovTriple.BGL.Instances.Sphere
