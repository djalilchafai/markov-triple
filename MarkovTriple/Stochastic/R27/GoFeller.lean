import Mathlib
import MarkovTriple.Stochastic.R27.GoSem
import MarkovTriple.Stochastic.R24.Operator
import MarkovTriple.BGL.Instances.GegenbauerOpen.Full.Sem

/-!
# Round 27 (K), part 2d: `goFullTriple` is `C_0`-Feller on `X = ℝ`

Weierstrass density of polynomials in `C([-1,1])`, `P_t`-invariance of polynomials, and the sup-norm contraction of `P_t` give a
uniform limit on `[-1,1]`, extended to a `C_c(ℝ)` function.  `IsFellerC0` does not use `IsOpenPosMeasure`; since `goμ` vanishes off
`[-1,1]` the statement says that `P_t[f]` has a continuous version on `[-1,1]` (and no kernel/bridge on `ℝ` is available:
`goμ_not_isOpenPos`).
-/

open MeasureTheory Filter Topology Set Polynomial
open scoped ENNReal NNReal ZeroAtInfty CompactlySupported

namespace MarkovTriple.Stochastic.R27

open MarkovTriple.BGL MarkovTriple.BGL.Instances.GegenbauerOpen MarkovTriple.Stochastic.R24

/-- `goμ` charges no open set outside `[-1,1]`, so `IsOpenPosMeasure` fails on `X = ℝ`. -/
theorem goμ_not_isOpenPos : ¬ goμ.IsOpenPosMeasure := by
  intro h
  have : goμ (Ioo (2 : ℝ) 3) = 0 := by
    refine le_antisymm ?_ bot_le
    refine (goμ_le (Ioo (2 : ℝ) 3)).trans ?_
    rw [Measure.restrict_apply measurableSet_Ioo]
    have : Ioo (2 : ℝ) 3 ∩ Ioo (-1) 1 = ∅ := by
      ext x; simp only [mem_inter_iff, mem_Ioo, mem_empty_iff_false, iff_false]
      intro ⟨⟨h1, _⟩, _, h4⟩; linarith
    rw [this]; simp
  exact (isOpen_Ioo.measure_pos goμ ⟨5 / 2, by norm_num, by norm_num⟩).ne' this

/-- an a.e. upper bound for a function continuous on `(-1,1)` holds everywhere on `(-1,1)` -/
lemma le_on_Ioo_of_ae_le {h : ℝ → ℝ} (hc : ContinuousOn h (Ioo (-1 : ℝ) 1)) {c : ℝ}
    (hh : ∀ᵐ x ∂goμ, h x ≤ c) : ∀ x ∈ Ioo (-1 : ℝ) 1, h x ≤ c := by
  have hm : ContinuousOn (fun x => min (h x) c) (Ioo (-1 : ℝ) 1) := (continuous_id.min continuous_const).comp_continuousOn hc
  have := eqOn_of_ae_go hm hc (by filter_upwards [hh] with x hx; exact min_eq_left hx)
  intro x hx
  have := this hx
  simp only at this
  exact min_eq_left_iff.1 this

/-- sup-norm contraction of `P_t` on `L²(goμ)` (positivity and sub-Markov) -/
lemma abs_semigroup_le (t : ℝ≥0) (w : Lp ℝ 2 goμ) (C : ℝ) (hC : ∀ᵐ x ∂goμ, |(w : ℝ → ℝ) x| ≤ C) :
    ∀ᵐ x ∂goμ, |(goFullTriple.toDiffusionTriple.semigroup t w : ℝ → ℝ) x| ≤ C := by
  have hC0 : 0 ≤ C := by
    obtain ⟨x, hx⟩ := hC.exists
    exact (abs_nonneg _).trans hx
  set e : Lp ℝ 2 goμ := polyι 1 with he
  have he1 : (e : ℝ → ℝ) =ᵐ[goμ] fun _ => 1 := by
    filter_upwards [coeFn_polyLp 1] with x hx
    show ((polyLp 1 : Lp ℝ 2 goμ) : ℝ → ℝ) x = 1
    rw [hx]; simp [polyFn]
  set P := goFullTriple.toDiffusionTriple.semigroup t with hP
  have hPe : (P e : ℝ → ℝ) ≤ᵐ[goμ] 1 :=
    goFullTriple.toDiffusionTriple.semigroup_le_one t e (by filter_upwards [he1] with x hx; exact hx.le)
  have hA : 0 ≤ᵐ[goμ] ((C • e - w : Lp ℝ 2 goμ) : ℝ → ℝ) := by
    filter_upwards [hC, he1, Lp.coeFn_sub (C • e) w, Lp.coeFn_smul C e] with x h1 h2 h3 h4
    simp only [Pi.zero_apply]
    rw [h3, Pi.sub_apply, h4, Pi.smul_apply, h2, smul_eq_mul]
    linarith [(abs_le.1 h1).2]
  have hB : 0 ≤ᵐ[goμ] ((C • e + w : Lp ℝ 2 goμ) : ℝ → ℝ) := by
    filter_upwards [hC, he1, Lp.coeFn_add (C • e) w, Lp.coeFn_smul C e] with x h1 h2 h3 h4
    simp only [Pi.zero_apply]
    rw [h3, Pi.add_apply, h4, Pi.smul_apply, h2, smul_eq_mul]
    linarith [(abs_le.1 h1).1]
  have hA' := goFullTriple.toDiffusionTriple.semigroup_nonneg t hA
  have hB' := goFullTriple.toDiffusionTriple.semigroup_nonneg t hB
  erw [map_sub, map_smul] at hA'
  erw [map_add, map_smul] at hB'
  filter_upwards [hA', hPe, hB', Lp.coeFn_sub (C • P e) (P w), Lp.coeFn_smul C (P e),
    Lp.coeFn_add (C • P e) (P w)] with x h1 h2 h3 h4 h5 h6
  rw [Pi.zero_apply, h4, Pi.sub_apply, h5, Pi.smul_apply, smul_eq_mul] at h1
  rw [Pi.zero_apply, h6, Pi.add_apply, h5, Pi.smul_apply, smul_eq_mul] at h3
  rw [Pi.one_apply] at h2
  rw [abs_le]
  constructor <;> nlinarith

/-- polynomial approximants of `P_t u` for `u` (a.e.) continuous -/
lemma go_approx (t : ℝ≥0) (f : ℝ → ℝ) (hf : Continuous f) (u : Lp ℝ 2 goμ) (hu : (u : ℝ → ℝ) =ᵐ[goμ] f) :
    ∃ q : ℕ → ℝ[X], ∀ k : ℕ, ∀ᵐ x ∂goμ,
      |(goFullTriple.toDiffusionTriple.semigroup t u : ℝ → ℝ) x - polyFn (q k) x| ≤ 1 / ((k : ℝ) + 1) := by
  choose p hp using fun k : ℕ => exists_polynomial_near_of_continuousOn (-1) 1 f hf.continuousOn
    (1 / ((k : ℝ) + 1)) (by positivity)
  choose q hq using fun k => go_semigroup_poly_cls t (p k)
  refine ⟨q, fun k => ?_⟩
  have hw : ∀ᵐ x ∂goμ, |((u - polyι (p k) : Lp ℝ 2 goμ) : ℝ → ℝ) x| ≤ 1 / ((k : ℝ) + 1) := by
    filter_upwards [hu, coeFn_polyLp (p k), Lp.coeFn_sub u (polyι (p k)),
      ae_go (p := fun x => x ∈ Ioo (-1 : ℝ) 1) (fun x hx => hx)] with x h1 h2 h3 h4
    rw [h3, Pi.sub_apply, h1]
    have h5 : ((polyι (p k) : Lp ℝ 2 goμ) : ℝ → ℝ) x = polyFn (p k) x := h2
    rw [h5, abs_sub_comm]
    exact (hp k x (Ioo_subset_Icc_self h4)).le
  have h2 := abs_semigroup_le t _ _ hw
  filter_upwards [h2, Lp.coeFn_sub (goFullTriple.toDiffusionTriple.semigroup t u)
    (goFullTriple.toDiffusionTriple.semigroup t (polyι (p k))), coeFn_polyLp (q k)] with x h1 h3 h4
  have e : goFullTriple.toDiffusionTriple.semigroup t (u - polyι (p k)) =
      goFullTriple.toDiffusionTriple.semigroup t u - goFullTriple.toDiffusionTriple.semigroup t (polyι (p k)) := by
    erw [map_sub]
  rw [e, h3, Pi.sub_apply] at h1
  rw [hq k] at h1
  have h6 : ((polyι (q k) : Lp ℝ 2 goμ) : ℝ → ℝ) x = polyFn (q k) x := h4
  convert h1 using 3
  exact h6.symm

/-- the clamp to `[-1,1]` -/
noncomputable def clamp1 (x : ℝ) : ℝ := max (-1) (min 1 x)

lemma continuous_clamp1 : Continuous clamp1 := continuous_const.max (continuous_const.min continuous_id)

lemma clamp1_mem (x : ℝ) : clamp1 x ∈ Icc (-1 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

lemma clamp1_eq {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) : clamp1 x = x := by
  simp only [clamp1]
  rw [min_eq_right hx.2, max_eq_right hx.1]

/-- cut-off `χ = 1` on `[-1,1]`, `0` off `[-2,2]` -/
noncomputable def chi1 (x : ℝ) : ℝ := max 0 (1 - |x - clamp1 x|)

lemma continuous_chi1 : Continuous chi1 :=
  continuous_const.max (continuous_const.sub (continuous_id.sub continuous_clamp1).abs)

lemma chi1_eq_one {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) : chi1 x = 1 := by
  simp [chi1, clamp1_eq hx]

lemma chi1_eq_zero {x : ℝ} (hx : x ∉ Icc (-2 : ℝ) 2) : chi1 x = 0 := by
  simp only [chi1, mem_Icc, not_and_or, not_le] at hx ⊢
  refine max_eq_left ?_
  rcases hx with h | h
  · have : clamp1 x = -1 := by simp only [clamp1]; rw [min_eq_right (by linarith), max_eq_left (by linarith)]
    rw [this]
    rw [abs_of_neg (by linarith)]; linarith
  · have : clamp1 x = 1 := by simp only [clamp1]; rw [min_eq_left (by linarith), max_eq_right (by linarith)]
    rw [this]
    rw [abs_of_pos (by linarith)]; linarith

/-- **limit lemma**: a function that is `goμ`-a.e. uniformly approximated by polynomials is a.e. a `C_0` function -/
lemma go_limit (q : ℕ → ℝ[X]) (v : ℝ → ℝ)
    (hv : ∀ᵐ x ∂goμ, ∀ k : ℕ, |v x - polyFn (q k) x| ≤ 1 / ((k : ℝ) + 1)) :
    ∃ g : C₀(ℝ, ℝ), v =ᵐ[goμ] g := by
  set ε : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1) with hε
  have hε0 : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hεpos : ∀ k, 0 < ε k := fun k => by simp only [hε]; positivity
  have hcont : ∀ k, Continuous (polyFn (q k)) := fun k => (polyFn_smooth (q k)).continuous
  -- uniform Cauchy on (-1,1), then on [-1,1]
  have h1 : ∀ k l, ∀ x ∈ Ioo (-1 : ℝ) 1, |polyFn (q k) x - polyFn (q l) x| ≤ ε k + ε l := by
    intro k l
    refine le_on_Ioo_of_ae_le (h := fun x => |polyFn (q k) x - polyFn (q l) x|)
      ((hcont k).sub (hcont l)).abs.continuousOn ?_
    filter_upwards [hv] with x hx
    have a := hx k
    have b := hx l
    calc |polyFn (q k) x - polyFn (q l) x| = |(v x - polyFn (q l) x) - (v x - polyFn (q k) x)| := by ring_nf
      _ ≤ |v x - polyFn (q l) x| + |v x - polyFn (q k) x| := abs_sub _ _
      _ ≤ ε l + ε k := add_le_add b a
      _ = ε k + ε l := add_comm _ _
  have h2 : ∀ k l, ∀ y ∈ Icc (-1 : ℝ) 1, |polyFn (q k) y - polyFn (q l) y| ≤ ε k + ε l := by
    intro k l y hy
    have hcl : IsClosed {y : ℝ | |polyFn (q k) y - polyFn (q l) y| ≤ ε k + ε l} :=
      isClosed_le ((hcont k).sub (hcont l)).abs continuous_const
    have : Icc (-1 : ℝ) 1 ⊆ {y : ℝ | |polyFn (q k) y - polyFn (q l) y| ≤ ε k + ε l} := by
      rw [← closure_Ioo (by norm_num : (-1 : ℝ) ≠ 1)]
      exact closure_minimal (fun x hx => h1 k l x hx) hcl
    exact this hy
  set G : ℕ → ℝ → ℝ := fun k x => polyFn (q k) (clamp1 x) with hG
  have hGc : ∀ k, Continuous (G k) := fun k => (hcont k).comp continuous_clamp1
  have h3 : ∀ k l x, |G k x - G l x| ≤ ε k + ε l := fun k l x => h2 k l _ (clamp1_mem x)
  have hcs : ∀ x, CauchySeq fun k => G k x := by
    intro x
    refine Metric.cauchySeq_iff.2 fun δ hδ => ?_
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt (half_pos hδ)
    refine ⟨N, fun m hm n hn => ?_⟩
    have hm' : ε m ≤ 1 / ((N : ℝ) + 1) := by
      simp only [hε]
      exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hm 1)
    have hn' : ε n ≤ 1 / ((N : ℝ) + 1) := by
      simp only [hε]
      exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hn 1)
    rw [Real.dist_eq]
    linarith [h3 m n x]
  choose g hg using fun x => cauchySeq_tendsto_of_complete (hcs x)
  have h4 : ∀ k x, |G k x - g x| ≤ ε k := by
    intro k x
    have hT : Tendsto (fun l => |G k x - G l x|) atTop (𝓝 |G k x - g x|) :=
      ((tendsto_const_nhds.sub (hg x)).abs)
    have hT2 : Tendsto (fun l => ε k + ε l) atTop (𝓝 (ε k + 0)) := tendsto_const_nhds.add hε0
    rw [add_zero] at hT2
    exact le_of_tendsto_of_tendsto' hT hT2 fun l => h3 k l x
  have hU : TendstoUniformly G g atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro δ hδ
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
    filter_upwards [eventually_ge_atTop N] with n hn x
    rw [Real.dist_eq, abs_sub_comm]
    refine lt_of_le_of_lt (h4 n x) (lt_of_le_of_lt ?_ hN)
    simp only [hε]
    exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hn 1)
  have hgc : Continuous g := hU.continuous (Eventually.of_forall hGc).frequently
  have hcpt : HasCompactSupport fun x => g x * chi1 x :=
    HasCompactSupport.intro (isCompact_Icc (a := (-2 : ℝ)) (b := 2)) fun x hx => by
      rw [chi1_eq_zero hx, mul_zero]
  refine ⟨⟨⟨fun x => g x * chi1 x, hgc.mul continuous_chi1⟩, hcpt.is_zero_at_infty⟩, ?_⟩
  filter_upwards [hv, ae_go (p := fun x => x ∈ Ioo (-1 : ℝ) 1) (fun x hx => hx)] with x hx hxI
  have hxI' : x ∈ Icc (-1 : ℝ) 1 := Ioo_subset_Icc_self hxI
  show v x = g x * chi1 x
  rw [chi1_eq_one hxI', mul_one]
  by_contra hne
  have hpos : 0 < |v x - g x| / 2 := by
    have : 0 < |v x - g x| := abs_pos.2 (sub_ne_zero.2 hne)
    linarith
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hpos
  have e1 := hx k
  have e2 := h4 k x
  have hGx : G k x = polyFn (q k) x := by simp only [hG, clamp1_eq hxI']
  rw [hGx] at e2
  have : |v x - g x| ≤ |v x - polyFn (q k) x| + |polyFn (q k) x - g x| := abs_sub_le _ _ _
  simp only [hε] at e2
  linarith

/-- **`goFullTriple` is `C_0`-Feller** (on the space `X = ℝ`; `goμ` lives on `[-1,1]`). -/
theorem goFull_isFellerC0 : IsFellerC0 goFullTriple.toDiffusionTriple := by
  intro t f u hu
  obtain ⟨q, hq⟩ := go_approx t f f.continuous u hu
  exact go_limit q _ (ae_all_iff.2 hq)

/-- the frozen form (K2): `goFullTriple.μ` has no `IsOpenPosMeasure` instance on `X = ℝ`. -/
theorem goMu_not_isOpenPos : ¬ goFullTriple.μ.IsOpenPosMeasure := goμ_not_isOpenPos

/-- the frozen form (K2): `P_t` maps (classes of) polynomials to (classes of) polynomials. -/
theorem go_semigroup_poly (t : ℝ≥0) (p : ℝ[X]) (hp : MemLp (fun x => p.eval x) 2 goFullTriple.μ) :
    ∃ q : ℝ[X], (goFullTriple.toDiffusionTriple.semigroup t (hp.toLp _) : ℝ → ℝ)
      =ᵐ[goFullTriple.μ] fun x => q.eval x := by
  obtain ⟨q, hq⟩ := go_semigroup_poly_cls t p
  refine ⟨q, ?_⟩
  have e : hp.toLp (fun x => p.eval x) = polyι p := by
    refine Lp.ext ?_
    filter_upwards [hp.coeFn_toLp, coeFn_polyLp p] with x h1 h2
    rw [h1]; exact h2.symm
  rw [e, hq]
  filter_upwards [coeFn_polyLp q] with x hx
  exact hx

end MarkovTriple.Stochastic.R27
