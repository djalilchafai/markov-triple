import Mathlib
import MarkovTriple.BGL.Instances.GibbsRd.Bochner
import MarkovTriple.BGL.Instances.GibbsRd.Cutoff
import MarkovTriple.BGL.Instances.GibbsRd.Convex
import MarkovTriple.BGL.Instances.GibbsRd.Main

/-!
# Energy estimates for the resolvent solution on `ℝ^d` (R18, Stream A3, target B4)

Statements: `STATEMENTS_R18_Core2Rd.md` (B4).  For `v` smooth, `v ∈ L²(μ)`, `L v = v - a`, `a ∈ C_c^∞`:

* `memLp_grad_resolvent`: `∂ᵢ v ∈ L²(μ)` (Caccioppoli with the cut-offs `cut R`, no hypothesis on `V`);
* `memLp_hess_resolvent`: `∂ⱼ∂ᵢ v ∈ L²(μ)`, from the cut-off Bochner identity `Γ₂ = ‖Hess v‖² + Hess V(∇v,∇v)` and
  the lower bound `Hess V ≥ ρ` (`ρ` of any sign), given a uniform bound for `L (cut R)` (BGL Sect. 3.2, `Γ₂ ≥ ρ Γ`).
-/

open MeasureTheory Filter Topology Set

namespace MarkovTriple.BGL.Instances.GibbsRd

open MarkovTriple.BGL (pderiv)

variable {d : ℕ}

/-- Fatou: a continuous `g` with uniformly bounded cut-off `L²` norms is `L²`. -/
lemma memLp_two_of_cut {μ : Measure (Rd d)} [IsFiniteMeasure μ] {g : Rd d → ℝ} (hg : Continuous g)
    {B : ℝ} (hB : ∀ n : ℕ, ∫ x, (cut ((n : ℝ) + 1) x * g x) ^ 2 ∂μ ≤ B) : MemLp g 2 μ := by
  rw [memLp_two_iff_integrable_sq hg.aestronglyMeasurable]
  refine ⟨(hg.pow 2).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun x => sq_nonneg _)]
  have hpos : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 1 := fun n => by positivity
  have hc : ∀ n : ℕ, Continuous (fun x => cut ((n : ℝ) + 1) x * g x) := fun n =>
    (sm_cut _).continuous.mul hg
  have hint : ∀ n : ℕ, Integrable (fun x => (cut ((n : ℝ) + 1) x * g x) ^ 2) μ := by
    intro n
    have hs : HasCompactSupport (fun x => cut ((n : ℝ) + 1) x * g x) := (hcs_cut (hpos n)).mul_right
    have hs2 : HasCompactSupport (fun x => (cut ((n : ℝ) + 1) x * g x) ^ 2) :=
      hs.comp_left (g := fun y : ℝ => y ^ 2) (by simp)
    exact ((hc n).pow 2).integrable_of_hasCompactSupport hs2
  set F : ℕ → Rd d → ENNReal := fun n x => ENNReal.ofReal ((cut ((n : ℝ) + 1) x * g x) ^ 2) with hF
  have hFm : ∀ n, Measurable (F n) := fun n =>
    ENNReal.measurable_ofReal.comp (((hc n).pow 2).measurable)
  have hlim : ∀ x, liminf (fun n => F n x) atTop = ENNReal.ofReal (g x ^ 2) := by
    intro x
    have : Tendsto (fun n => F n x) atTop (𝓝 (ENNReal.ofReal (g x ^ 2))) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop ⌈qd x⌉₊] with n hn
      have h1 : qd x ≤ ((n : ℝ) + 1) ^ 2 := by
        have := (Nat.le_ceil (qd x)).trans (by exact_mod_cast hn : (⌈qd x⌉₊ : ℝ) ≤ n)
        nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      simp only [hF, cut_eq_one (hpos n) h1, one_mul]
    exact this.liminf_eq
  have h1 := lintegral_liminf_le (μ := μ) (u := (atTop : Filter ℕ)) hFm
  simp only [hlim] at h1
  refine lt_of_le_of_lt h1 ?_
  have h2 : ∀ n, ∫⁻ x, F n x ∂μ ≤ ENNReal.ofReal B := fun n => by
    simp only [hF]
    rw [← ofReal_integral_eq_lintegral_ofReal (hint n) (Eventually.of_forall fun x => sq_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (hB n)
  have h3 : liminf (fun n : ℕ => ∫⁻ x, F n x ∂μ) atTop ≤ ENNReal.ofReal B :=
    liminf_le_of_frequently_le' (Frequently.of_forall h2)
  exact lt_of_le_of_lt h3 ENNReal.ofReal_lt_top

/-- the pointwise inequality of the Caccioppoli estimate. -/
lemma cacc_pt {ψ v a F Q : ℝ} {q w : Fin d → ℝ} (h0 : 0 ≤ ψ) (h1 : ψ ≤ 1) (hq : ∑ i, q i ^ 2 ≤ Q)
    (hF : F = ψ * ψ * v * (v - a) + ∑ i, ((q i * ψ + ψ * q i) * v + ψ * ψ * w i) * w i) :
    ψ ^ 2 * ∑ i, w i * w i ≤ 2 * F + 1 / 2 * a ^ 2 + 4 * Q * v ^ 2 := by
  have key : ∀ i, -(2 * ψ * q i * v * w i) ≤ 1 / 2 * (ψ * ψ * (w i * w i)) + 2 * v ^ 2 * q i ^ 2 :=
    fun i => by nlinarith [sq_nonneg (ψ * w i + 2 * v * q i)]
  have hsum : ∑ i, ((q i * ψ + ψ * q i) * v + ψ * ψ * w i) * w i =
      ∑ i, (2 * ψ * q i * v * w i) + ψ * ψ * ∑ i, w i * w i := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hT : -(∑ i, (2 * ψ * q i * v * w i)) ≤ 1 / 2 * (ψ * ψ * ∑ i, w i * w i) + 2 * v ^ 2 * Q := by
    rw [← Finset.sum_neg_distrib]
    refine (Finset.sum_le_sum fun i _ => key i).trans ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
    have : 2 * v ^ 2 * ∑ i, q i ^ 2 ≤ 2 * v ^ 2 * Q :=
      mul_le_mul_of_nonneg_left hq (by positivity)
    linarith
  have hm0 : 0 ≤ ψ * ψ := mul_self_nonneg _
  have hm1 : ψ * ψ ≤ 1 := by nlinarith
  rw [hsum] at hF
  have hS : ψ ^ 2 = ψ * ψ := sq ψ
  rw [hS]
  nlinarith [mul_nonneg hm0 (sq_nonneg (v - a / 2)), mul_nonneg (sub_nonneg.2 hm1) (sq_nonneg a)]

namespace GibbsRdData

lemma sm_Gr' (G : GibbsRdData d) {f g : Rd d → ℝ} (hf : Sm f) (hg : Sm g) : Sm (Gr f g) := by
  rw [← G.toEll_Γ f g]; exact G.toEll.sm_Γ hf hg

lemma hcs_Gr_left (G : GibbsRdData d) {f g : Rd d → ℝ} (hc : HasCompactSupport f) : HasCompactSupport (Gr f g) := by
  rw [← G.toEll_Γ f g]; exact G.toEll.hcs_Γ_left hc

lemma hcs_Gr_right (G : GibbsRdData d) {f g : Rd d → ℝ} (hc : HasCompactSupport g) : HasCompactSupport (Gr f g) := by
  rw [← G.toEll_Γ f g]; exact G.toEll.hcs_Γ_right hc

lemma hcs_Lr (G : GibbsRdData d) {f : Rd d → ℝ} (hf : Sm f) (hc : HasCompactSupport f) : HasCompactSupport (Lr G.V f) := by
  rw [← G.toEll_L hf]; exact G.toEll.hcs_L hc

/-- integration by parts `∫ g L f dμ = -∫ Γ(g,f) dμ`. -/
lemma ibp_Lr (G : GibbsRdData d) {f g : Rd d → ℝ} (hf : Sm f) (hg : Sm g)
    (hc : HasCompactSupport g ∨ HasCompactSupport f) :
    ∫ x, g x * Lr G.V f x ∂G.toEll.μ = -∫ x, Gr g f x ∂G.toEll.μ := by
  have := G.toEll.ibp_sm hf hg hc
  rw [G.toEll_L hf, G.toEll_Γ] at this
  exact this

lemma int_cs (G : GibbsRdData d) {h : Rd d → ℝ} (hh : Continuous h) (hc : HasCompactSupport h) :
    Integrable h G.toEll.μ := hh.integrable_of_hasCompactSupport hc

lemma gr_comm (f g : Rd d → ℝ) : Gr f g = Gr g f := by
  funext x; unfold Gr; exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- Caccioppoli, integral form: `∫ χ_R² |∇v|² dμ ≤ B` uniformly in `R = n+1`. -/
theorem cacc_bound (G : GibbsRdData d) {v a : Rd d → ℝ} (hv : Sm v) (ha : a ∈ A₀ d) (hv2 : MemLp v 2 G.toEll.μ)
    (hL : ∀ x, Lr G.V v x = v x - a x) :
    ∃ B : ℝ, ∀ n : ℕ, ∫ x, cut ((n : ℝ) + 1) x ^ 2 * Gr v v x ∂G.toEll.μ ≤ B := by
  obtain ⟨C, hC0, hC⟩ := sT_deriv_bound
  set μ := G.toEll.μ with hμ
  refine ⟨1 / 2 * ∫ x, a x ^ 2 ∂μ + 4 * (8 * C ^ 2) * ∫ x, v x ^ 2 ∂μ, fun n => ?_⟩
  set R : ℝ := (n : ℝ) + 1 with hR
  have hRpos : 0 < R := by positivity
  have hR1 : 1 ≤ R := by rw [hR]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  set ψ : Rd d → ℝ := cut R with hψdef
  have hψ : Sm ψ := sm_cut R
  have hψc : HasCompactSupport ψ := hcs_cut hRpos
  have hq : ∀ x, ∑ i, pderiv ψ i x ^ 2 ≤ 8 * C ^ 2 := fun x =>
    (sum_sq_pderiv_cut_le hRpos hC x).trans (div_le_self (by positivity) (one_le_pow₀ hR1))
  have hg : Sm (ψ * ψ * v) := (hψ.mul hψ).mul hv
  have hgc : HasCompactSupport (ψ * ψ * v) := hψc.mul_right.mul_right
  have hI := G.ibp_Lr hv hg (Or.inl hgc)
  have iA : Integrable (fun x => (ψ * ψ * v) x * Lr G.V v x) μ :=
    G.int_cs (hg.continuous.mul (sm_Lr G.smooth hv).continuous) hgc.mul_right
  have iB : Integrable (fun x => Gr (ψ * ψ * v) v x) μ :=
    G.int_cs (G.sm_Gr' hg hv).continuous (G.hcs_Gr_left hgc)
  have hzero : ∫ x, ((ψ * ψ * v) x * Lr G.V v x + Gr (ψ * ψ * v) v x) ∂μ = 0 := by
    rw [integral_add iA iB]; linarith
  have iF : Integrable (fun x => (ψ * ψ * v) x * Lr G.V v x + Gr (ψ * ψ * v) v x) μ := iA.add iB
  have iS : Integrable (fun x => ψ x ^ 2 * Gr v v x) μ := by
    have hc : Continuous (fun x => ψ x ^ 2 * Gr v v x) :=
      (hψ.continuous.pow 2).mul (G.sm_Gr' hv hv).continuous
    have hs : HasCompactSupport (fun x => ψ x ^ 2 * Gr v v x) :=
      (hψc.comp_left (g := fun y : ℝ => y ^ 2) (by simp)).mul_right
    exact G.int_cs hc hs
  have hv2i : Integrable (fun x => v x ^ 2) μ := hv2.integrable_sq
  have ha2i : Integrable (fun x => a x ^ 2) μ :=
    G.int_cs (ha.1.continuous.pow 2) (ha.2.comp_left (g := fun y : ℝ => y ^ 2) (by simp))
  have hpt : ∀ x, ψ x ^ 2 * Gr v v x ≤
      2 * ((ψ * ψ * v) x * Lr G.V v x + Gr (ψ * ψ * v) v x) + 1 / 2 * a x ^ 2 + 4 * (8 * C ^ 2) * v x ^ 2 := by
    intro x
    have key := cacc_pt (ψ := ψ x) (v := v x) (a := a x) (Q := 8 * C ^ 2)
      (q := fun i => pderiv ψ i x) (w := fun i => pderiv v i x)
      (F := (ψ * ψ * v) x * Lr G.V v x + Gr (ψ * ψ * v) v x)
      (cut_nonneg R x) (cut_le_one R x) (hq x) (by
        have e : ∀ i, pderiv (ψ * ψ * v) i x =
            (pderiv ψ i x * ψ x + ψ x * pderiv ψ i x) * v x + ψ x * ψ x * pderiv v i x := fun i => by
          rw [pderiv_mul (f := ψ * ψ) (g := v) (hψ.mul hψ) hv, pderiv_mul (f := ψ) (g := ψ) hψ hψ]; rfl
        simp only [Gr, e, hL x, Pi.mul_apply])
    exact key
  have j1 : Integrable (fun x => 2 * ((ψ * ψ * v) x * Lr G.V v x + Gr (ψ * ψ * v) v x) +
      1 / 2 * a x ^ 2) μ := (iF.const_mul 2).add (ha2i.const_mul (1 / 2))
  have iR : Integrable (fun x => 2 * ((ψ * ψ * v) x * Lr G.V v x + Gr (ψ * ψ * v) v x) +
      1 / 2 * a x ^ 2 + 4 * (8 * C ^ 2) * v x ^ 2) μ := j1.add (hv2i.const_mul (4 * (8 * C ^ 2)))
  have hmono := integral_mono iS iR hpt
  rw [integral_add j1 (hv2i.const_mul (4 * (8 * C ^ 2))),
    integral_add (iF.const_mul 2) (ha2i.const_mul (1 / 2)), integral_const_mul, integral_const_mul,
    integral_const_mul, hzero] at hmono
  have : ∫ x, ψ x ^ 2 * Gr v v x ∂μ = ∫ x, cut ((n : ℝ) + 1) x ^ 2 * Gr v v x ∂μ := rfl
  linarith

/-- the integral-form gradient bound: `∫ (χ_R ∂ᵢ v)² dμ ≤ B`. -/
theorem cacc_grad_bound (G : GibbsRdData d) {v a : Rd d → ℝ} (hv : Sm v) (ha : a ∈ A₀ d) (hv2 : MemLp v 2 G.toEll.μ)
    (hL : ∀ x, Lr G.V v x = v x - a x) :
    ∃ B : ℝ, ∀ (n : ℕ) (i : Fin d), ∫ x, (cut ((n : ℝ) + 1) x * pderiv v i x) ^ 2 ∂G.toEll.μ ≤ B := by
  obtain ⟨B, hB⟩ := G.cacc_bound hv ha hv2 hL
  refine ⟨B, fun n i => le_trans ?_ (hB n)⟩
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hψ : Sm (cut ((n : ℝ) + 1) : Rd d → ℝ) := sm_cut _
  have hψc := hcs_cut (d := d) hpos
  have i1 : Integrable (fun x => (cut ((n : ℝ) + 1) x * pderiv v i x) ^ 2) G.toEll.μ :=
    G.int_cs ((hψ.continuous.mul (hv.pderiv i).continuous).pow 2)
      ((hψc.mul_right).comp_left (g := fun y : ℝ => y ^ 2) (by simp))
  have i2 : Integrable (fun x => cut ((n : ℝ) + 1) x ^ 2 * Gr v v x) G.toEll.μ :=
    G.int_cs ((hψ.continuous.pow 2).mul (G.sm_Gr' hv hv).continuous)
      ((hψc.comp_left (g := fun y : ℝ => y ^ 2) (by simp)).mul_right)
  refine integral_mono i1 i2 fun x => ?_
  have : pderiv v i x * pderiv v i x ≤ Gr v v x :=
    Finset.single_le_sum (f := fun k => pderiv v k x * pderiv v k x) (fun k _ => mul_self_nonneg _)
      (Finset.mem_univ i)
  have h0 : 0 ≤ cut ((n : ℝ) + 1) x ^ 2 := sq_nonneg _
  show (cut ((n : ℝ) + 1) x * pderiv v i x) ^ 2 ≤ cut ((n : ℝ) + 1) x ^ 2 * Gr v v x
  nlinarith

/-- **B4 (1)**: `∇v ∈ L²(μ)`. -/
theorem memLp_grad_resolvent (G : GibbsRdData d) {v a : Rd d → ℝ} (hv : Sm v) (ha : a ∈ A₀ d)
    (hv2 : MemLp v 2 G.toEll.μ) (hL : ∀ x, Lr G.V v x = v x - a x) (i : Fin d) :
    MemLp (pderiv v i) 2 G.toEll.μ := by
  obtain ⟨B, hB⟩ := G.cacc_grad_bound hv ha hv2 hL
  exact memLp_two_of_cut (hv.pderiv i).continuous (fun n => hB n i)

/-- pointwise Bochner identity `‖Hess f‖² + Hess V(∇f,∇f) = ½ (L Γ(f) − 2 Γ(f, L f))`. -/
lemma bochner_pt (G : GibbsRdData d) {f : Rd d → ℝ} (hf : Sm f) (x : Rd d) :
    ∑ i, ∑ j, pderiv (pderiv f i) j x ^ 2 +
      ∑ i, ∑ j, pderiv (pderiv G.V i) j x * pderiv f i x * pderiv f j x =
    (Lr G.V (Gr f f) x - Gr f (Lr G.V f) x - Gr (Lr G.V f) f x) / 2 := by
  rw [← G.gibbsRd_Γ₂_eq hf x]
  have h := congrFun (G.toEll.Γ₂_eq_comb hf) x
  show G.toEll.diff.Γ₂ f f x = _
  rw [h, G.toEll_Γ f f, G.toEll_L (sm_Gr hf), G.toEll_L hf, G.toEll_Γ f (Lr G.V f),
    G.toEll_Γ (Lr G.V f) f]

/-- real-number part of the Hessian estimate. -/
lemma hess_pt {φ s t r Q ρ Hv X : ℝ} (h0 : 0 ≤ φ) (h1 : φ ≤ 1) (hs : 0 ≤ s) (hr : 0 ≤ r)
    (ht : t ≤ (s + r) / 2) (hQ : ρ * s ≤ Q) (heq : φ * Hv = X / 2 - φ * (s - t) - φ * Q) :
    φ * Hv ≤ X / 2 + (1 / 2 * (s + r) + |ρ| * s) := by
  have a1 : φ * t ≤ (s + r) / 2 := by
    rcases le_total t 0 with h | h
    · nlinarith [mul_nonneg h0 (neg_nonneg.2 h)]
    · nlinarith [mul_nonneg (sub_nonneg.2 h1) h]
  have b1 : φ * (ρ * s) ≤ φ * Q := mul_le_mul_of_nonneg_left hQ h0
  have b2 : -(|ρ| * s) ≤ φ * (ρ * s) := by
    have c1 : -|ρ| ≤ ρ := neg_abs_le ρ
    have c2 : φ * |ρ| ≤ |ρ| := by nlinarith [abs_nonneg ρ]
    nlinarith [mul_nonneg h0 (abs_nonneg ρ), mul_nonneg hs (sub_nonneg.2 c1),
      mul_nonneg h0 (mul_nonneg hs (sub_nonneg.2 c1)), mul_nonneg hs (sub_nonneg.2 c2)]
  nlinarith [mul_nonneg h0 hs]

lemma gr_sub (G : GibbsRdData d) {v a : Rd d → ℝ} (hv : Sm v) (ha : Sm a)
    (hL : ∀ x, Lr G.V v x = v x - a x) (x : Rd d) :
    Gr v (Lr G.V v) x = Gr v v x - Gr v a x := by
  have e : Lr G.V v = fun y => v y - a y := funext hL
  rw [e]
  unfold Gr
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pderiv_sub' hv ha i x]; ring

/-- Hessian estimate, integral form. -/
theorem hess_bound (G : GibbsRdData d) {v a : Rd d → ℝ} (hv : Sm v) (ha : a ∈ A₀ d)
    (hv2 : MemLp v 2 G.toEll.μ) (hL : ∀ x, Lr G.V v x = v x - a x) {ρ : ℝ} (hρ : HessGe G.V ρ)
    (hP : ∃ K : ℝ, ∀ (n : ℕ) (x : Rd d), |Lr G.V (cut ((n : ℝ) + 1)) x| ≤ K) :
    ∃ B : ℝ, ∀ (n : ℕ) (i j : Fin d),
      ∫ x, (cut ((n : ℝ) + 1) x * pderiv (pderiv v i) j x) ^ 2 ∂G.toEll.μ ≤ B := by
  obtain ⟨C, hC0, hC⟩ := sT_deriv_bound
  obtain ⟨K, hK⟩ := hP
  set μ := G.toEll.μ with hμ
  have hgrad : ∀ i, MemLp (pderiv v i) 2 μ := G.memLp_grad_resolvent hv ha hv2 hL
  have iGvv : Integrable (Gr v v) μ := by
    have h1 : ∀ i ∈ (Finset.univ : Finset (Fin d)),
        Integrable (fun x => pderiv v i x * pderiv v i x) μ := fun i _ => by
      simpa [sq] using (hgrad i).integrable_sq
    exact integrable_finsetSum _ h1
  have iGaa : Integrable (Gr a a) μ := G.int_cs (G.sm_Gr' ha.1 ha.1).continuous (G.hcs_Gr_left ha.2)
  set W : Rd d → ℝ := fun x => 1 / 2 * (Gr v v x + Gr a a x) + |ρ| * Gr v v x with hW
  have iW : Integrable W μ := ((iGvv.add iGaa).const_mul (1 / 2)).add (iGvv.const_mul |ρ|)
  set K' : ℝ := 2 * K + 16 * C ^ 2 with hK'
  refine ⟨1 / 2 * (K' * ∫ x, Gr v v x ∂μ) + ∫ x, W x ∂μ, fun n i j => ?_⟩
  set R : ℝ := (n : ℝ) + 1 with hR
  have hRpos : 0 < R := by positivity
  have hR1 : 1 ≤ R := by rw [hR]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  set ψ : Rd d → ℝ := cut R with hψdef
  have hψ : Sm ψ := sm_cut R
  have hψc : HasCompactSupport ψ := hcs_cut hRpos
  have hq : ∀ x, ∑ k, pderiv ψ k x * pderiv ψ k x ≤ 8 * C ^ 2 := fun x => by
    have := (sum_sq_pderiv_cut_le hRpos hC x).trans (div_le_self (by positivity) (one_le_pow₀ hR1))
    simpa [sq] using this
  have hφ : Sm (ψ * ψ) := hψ.mul hψ
  have hφc : HasCompactSupport (ψ * ψ) := hψc.mul_right
  -- bound on `L φ`
  have hLφ : ∀ x, |Lr G.V (ψ * ψ) x| ≤ K' := by
    intro x
    have h := G.toEll.L_mul hψ hψ x
    rw [G.toEll_L hφ, G.toEll_L hψ, G.toEll_Γ] at h
    have e : Lr G.V (ψ * ψ) x = ψ x * Lr G.V ψ x + ψ x * Lr G.V ψ x + 2 * Gr ψ ψ x := h
    have g0 : 0 ≤ Gr ψ ψ x := Finset.sum_nonneg fun k _ => mul_self_nonneg _
    have g1 : Gr ψ ψ x ≤ 8 * C ^ 2 := hq x
    have p0 := cut_nonneg R x
    have p1 := cut_le_one R x
    have hk := hK n x
    have hk' : |ψ x * Lr G.V ψ x| ≤ K := by
      rw [abs_mul, abs_of_nonneg p0]
      exact (mul_le_of_le_one_left (abs_nonneg _) p1).trans hk
    rw [e, hK']
    have := abs_le.1 hk'
    rw [abs_le]
    constructor <;> nlinarith [this.1, this.2]
  have iA : Integrable (fun x => (ψ * ψ) x * Lr G.V (Gr v v) x) μ :=
    G.int_cs (hφ.continuous.mul (sm_Lr G.smooth (G.sm_Gr' hv hv)).continuous) hφc.mul_right
  have iHL : Integrable (fun x => Gr v v x * Lr G.V (ψ * ψ) x) μ :=
    G.int_cs ((G.sm_Gr' hv hv).continuous.mul (sm_Lr G.smooth hφ).continuous)
      (G.hcs_Lr hφ hφc).mul_left
  have hA : ∫ x, (ψ * ψ) x * Lr G.V (Gr v v) x ∂μ = ∫ x, Gr v v x * Lr G.V (ψ * ψ) x ∂μ := by
    have e1 := G.ibp_Lr (G.sm_Gr' hv hv) hφ (Or.inl hφc)
    have e2 := G.ibp_Lr hφ (G.sm_Gr' hv hv) (Or.inr hφc)
    rw [e1, e2, gr_comm (ψ * ψ) (Gr v v)]
  have hHv : Continuous (fun x => ∑ k, ∑ l, pderiv (pderiv v k) l x ^ 2) :=
    continuous_finsetSum _ fun k _ => continuous_finsetSum _ fun l _ =>
      ((hv.pderiv k).pderiv l).continuous.pow 2
  have iHv : Integrable (fun x => (ψ * ψ) x * ∑ k, ∑ l, pderiv (pderiv v k) l x ^ 2) μ :=
    G.int_cs (hφ.continuous.mul hHv) hφc.mul_right
  have hpt : ∀ x, (ψ * ψ) x * ∑ k, ∑ l, pderiv (pderiv v k) l x ^ 2 ≤
      (ψ * ψ) x * Lr G.V (Gr v v) x / 2 + W x := by
    intro x
    have hb := G.bochner_pt hv x
    have hgs := G.gr_sub hv ha.1 hL x
    have hcm : Gr (Lr G.V v) v x = Gr v (Lr G.V v) x := congrFun (gr_comm _ _) x
    have hQ : ρ * Gr v v x ≤ ∑ k, ∑ l, pderiv (pderiv G.V k) l x * pderiv v k x * pderiv v l x := by
      have := hρ x (fun k => pderiv v k x)
      simpa [Gr, sq] using this
    have ht : Gr v a x ≤ (Gr v v x + Gr a a x) / 2 := by
      unfold Gr
      rw [← Finset.sum_add_distrib, Finset.sum_div]
      exact Finset.sum_le_sum fun k _ => by nlinarith [sq_nonneg (pderiv v k x - pderiv a k x)]
    have hs0 : 0 ≤ Gr v v x := Finset.sum_nonneg fun k _ => mul_self_nonneg _
    have hr0 : 0 ≤ Gr a a x := Finset.sum_nonneg fun k _ => mul_self_nonneg _
    have key := hess_pt (φ := (ψ * ψ) x) (s := Gr v v x) (t := Gr v a x) (r := Gr a a x)
      (Q := ∑ k, ∑ l, pderiv (pderiv G.V k) l x * pderiv v k x * pderiv v l x) (ρ := ρ)
      (Hv := ∑ k, ∑ l, pderiv (pderiv v k) l x ^ 2) (X := (ψ * ψ) x * Lr G.V (Gr v v) x)
      (mul_self_nonneg _) (by have := cut_le_one R x; have := cut_nonneg R x; simp only [Pi.mul_apply]
                              nlinarith) hs0 hr0 ht hQ (by
        have e : ∑ k, ∑ l, pderiv (pderiv v k) l x ^ 2 =
            (Lr G.V (Gr v v) x - Gr v (Lr G.V v) x - Gr (Lr G.V v) v x) / 2 -
            ∑ k, ∑ l, pderiv (pderiv G.V k) l x * pderiv v k x * pderiv v l x := by
          linarith
        rw [e, hcm, hgs]; ring)
    simpa only [hW] using key
  have iR : Integrable (fun x => (ψ * ψ) x * Lr G.V (Gr v v) x / 2 + W x) μ := (iA.div_const 2).add iW
  have hmono := integral_mono iHv iR hpt
  rw [integral_add (iA.div_const 2) iW, integral_div, hA] at hmono
  have hint : ∫ x, Gr v v x * Lr G.V (ψ * ψ) x ∂μ ≤ ∫ x, K' * Gr v v x ∂μ := by
    refine integral_mono iHL (iGvv.const_mul K') fun x => ?_
    have hs0 : 0 ≤ Gr v v x := Finset.sum_nonneg fun k _ => mul_self_nonneg _
    have := (le_abs_self _).trans (hLφ x)
    nlinarith
  rw [integral_const_mul] at hint
  -- the single entry
  have i1 : Integrable (fun x => (ψ x * pderiv (pderiv v i) j x) ^ 2) μ :=
    G.int_cs ((hψ.continuous.mul ((hv.pderiv i).pderiv j).continuous).pow 2)
      ((hψc.mul_right).comp_left (g := fun y : ℝ => y ^ 2) (by simp))
  have hle : ∫ x, (ψ x * pderiv (pderiv v i) j x) ^ 2 ∂μ ≤
      ∫ x, (ψ * ψ) x * ∑ k, ∑ l, pderiv (pderiv v k) l x ^ 2 ∂μ := by
    refine integral_mono i1 iHv fun x => ?_
    have : pderiv (pderiv v i) j x ^ 2 ≤ ∑ k, ∑ l, pderiv (pderiv v k) l x ^ 2 :=
      (Finset.single_le_sum (f := fun l => pderiv (pderiv v i) l x ^ 2) (fun l _ => sq_nonneg _)
        (Finset.mem_univ j)).trans
        (Finset.single_le_sum (f := fun k => ∑ l, pderiv (pderiv v k) l x ^ 2)
          (fun k _ => Finset.sum_nonneg fun l _ => sq_nonneg _) (Finset.mem_univ i))
    have h0 := mul_self_nonneg (ψ x)
    show (ψ x * pderiv (pderiv v i) j x) ^ 2 ≤ (ψ x * ψ x) * _
    nlinarith
  linarith

/-- **B4 (2)**: `Hess v ∈ L²(μ)` under `Hess V ≥ ρ` (`ρ` of any sign) and a uniform bound on `L(cut R)`. -/
theorem memLp_hess_resolvent (G : GibbsRdData d) {v a : Rd d → ℝ} (hv : Sm v) (ha : a ∈ A₀ d)
    (hv2 : MemLp v 2 G.toEll.μ) (hL : ∀ x, Lr G.V v x = v x - a x) {ρ : ℝ} (hρ : HessGe G.V ρ)
    (hP : ∃ K : ℝ, ∀ (n : ℕ) (x : Rd d), |Lr G.V (cut ((n : ℝ) + 1)) x| ≤ K) (i j : Fin d) :
    MemLp (pderiv (pderiv v i) j) 2 G.toEll.μ := by
  obtain ⟨B, hB⟩ := hess_bound G hv ha hv2 hL hρ hP
  exact memLp_two_of_cut ((hv.pderiv i).pderiv j).continuous (fun n => hB n i j)

end GibbsRdData

end MarkovTriple.BGL.Instances.GibbsRd
