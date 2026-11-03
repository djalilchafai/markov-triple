import Mathlib
import MarkovTriple.BGL.Theory.Extension.Gamma2E

/-!
# Prop. 3.3.16 (vii), first part (BGL p. 160): `h ∈ 𝒜₀`, `f ∈ 𝒟(L)` ⇒ `h f ∈ 𝒟(L)`

`L(h a) = h L a + a L h + 2Γ(h,a)` on `𝒜₀` (change of variables formula (3.1.8)/(3.1.6)); the graph norm of `h a` is
controlled by that of `a` (`jL_mul_bound`, using `‖Γ(h,a)‖₂² ≤ ‖Γh‖_∞ ℰ(a)`), so `(h a_k)` is graph-Cauchy; the generator is
closed (self-adjoint, `Hilbert.FormData.generator_isClosed`), hence the limit is in `𝒟(L)`.
-/

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal InnerProductSpace LinearPMap

namespace MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E]

namespace FullTriple

variable {T : FullTriple E}

lemma norm_Lcls_sq (y : T.A₀) : ‖T.toDiffusionTriple.Lcls y‖ ^ 2 = ∫ x, (T.L y.1 x) ^ 2 ∂T.μ := by
  rw [← real_inner_self_eq_norm_sq, L2_inner_eq]
  refine integral_congr_ae ?_
  filter_upwards [DiffusionTriple.coeFn_Lcls T.toDiffusionTriple y] with x hx
  rw [hx]; ring

lemma norm_Gm_sq (m a : T.A₀) : ‖Gm T m a‖ ^ 2 = ∫ x, (G T a.1 m.1 x) ^ 2 ∂T.μ := by
  rw [← real_inner_self_eq_norm_sq, L2_inner_eq]
  refine integral_congr_ae ?_
  filter_upwards [Gm_ae m a] with x hx
  rw [hx]; ring

lemma sq_A₀ (a : T.A₀) : Integrable (fun x => (T.L a.1 x) ^ 2) T.μ :=
  (DiffusionTriple.memLp2 T.toDiffusionTriple (T.L_mem a.1 a.2)).integrable_sq

/-- graph-norm boundedness of multiplication by `k ∈ 𝒜₀`. -/
lemma jL_mul_bound (k : T.A₀) : ∃ C : ℝ, 0 ≤ C ∧ ∀ y : T.A₀, ‖jL T (k * y)‖ ≤ C * ‖jL T y‖ := by
  obtain ⟨M, hM⟩ := T.bounded k.1 k.2
  obtain ⟨ML, hML⟩ := T.bounded (T.L k.1) (T.L_mem k.1 k.2)
  obtain ⟨CG, hCG0, hCG⟩ := norm_Gm_le k
  set M' := |M| with hM'
  set N' := |ML| with hN'
  have hk2 : ∀ x, (k.1 x) ^ 2 ≤ M' ^ 2 := fun x => by
    have := abs_le.1 ((hM x).trans (le_abs_self M))
    exact sq_le_sq' this.1 this.2
  have hL2 : ∀ x, (T.L k.1 x) ^ 2 ≤ N' ^ 2 := fun x => by
    have := abs_le.1 ((hML x).trans (le_abs_self ML))
    exact sq_le_sq' this.1 this.2
  set D : ℝ := 3 * M' ^ 2 + 3 * N' ^ 2 + 48 * CG ^ 2 with hD
  have hD0 : 0 ≤ D := by positivity
  have key : ∀ y : T.A₀, ‖T.toDiffusionTriple.Lcls (k * y)‖ ^ 2 ≤ D * ‖jL T y‖ ^ 2 := by
    intro y
    have n1 : ‖T.toDiffusionTriple.cls y‖ ≤ ‖jL T y‖ := norm_fst_le (jL T y)
    have n2 : ‖T.toDiffusionTriple.Lcls y‖ ≤ ‖jL T y‖ := norm_snd_le (jL T y)
    have n3 := hCG y
    have n4 := norm_jE_le y
    have iy2 := integrable_sq_A₀ y
    have iLy := sq_A₀ y
    have iG : Integrable (fun x => (G T y.1 k.1 x) ^ 2) T.μ := by
      have := (DiffusionTriple.memLp2 T.toDiffusionTriple (G_memA₀ (A₀_memA y.2) k.2)).integrable_sq
      exact this
    have iL : Integrable (fun x => (T.L (k * y).1 x) ^ 2) T.μ := sq_A₀ (k * y)
    have i1 : Integrable (fun x => 3 * (M' ^ 2 * (T.L y.1 x) ^ 2)) T.μ := (iLy.const_mul _).const_mul 3
    have i2 : Integrable (fun x => 3 * (N' ^ 2 * (y.1 x) ^ 2)) T.μ := (iy2.const_mul _).const_mul 3
    have i12 : Integrable (fun x => 3 * (M' ^ 2 * (T.L y.1 x) ^ 2) + 3 * (N' ^ 2 * (y.1 x) ^ 2)) T.μ :=
      i1.add i2
    have hint : Integrable (fun x => 3 * (M' ^ 2 * (T.L y.1 x) ^ 2) + 3 * (N' ^ 2 * (y.1 x) ^ 2) +
        12 * (G T y.1 k.1 x) ^ 2) T.μ := i12.add (iG.const_mul 12)
    have hle : ∫ x, (T.L (k * y).1 x) ^ 2 ∂T.μ ≤ ∫ x, (3 * (M' ^ 2 * (T.L y.1 x) ^ 2) +
        3 * (N' ^ 2 * (y.1 x) ^ 2) + 12 * (G T y.1 k.1 x) ^ 2) ∂T.μ := by
      refine integral_mono iL hint (fun x => ?_)
      have e := L_mul_eq (T := T) k.1 y.1 x
      have e' : T.L (k * y).1 x = k.1 x * T.L y.1 x + y.1 x * T.L k.1 x + 2 * G T y.1 k.1 x := by
        show T.L (k.1 * y.1) x = _
        rw [e, G_comm k.1 y.1]
      rw [e']
      have a1 : (k.1 x * T.L y.1 x) ^ 2 ≤ M' ^ 2 * (T.L y.1 x) ^ 2 := by
        rw [mul_pow]; exact mul_le_mul_of_nonneg_right (hk2 x) (sq_nonneg _)
      have a2 : (y.1 x * T.L k.1 x) ^ 2 ≤ N' ^ 2 * (y.1 x) ^ 2 := by
        rw [mul_pow, mul_comm]; exact mul_le_mul_of_nonneg_right (hL2 x) (sq_nonneg _)
      nlinarith [sq_nonneg (k.1 x * T.L y.1 x - y.1 x * T.L k.1 x),
        sq_nonneg (k.1 x * T.L y.1 x - 2 * G T y.1 k.1 x), sq_nonneg (y.1 x * T.L k.1 x - 2 * G T y.1 k.1 x)]
    have h1 : ∫ x, (3 * (M' ^ 2 * (T.L y.1 x) ^ 2) + 3 * (N' ^ 2 * (y.1 x) ^ 2) +
        12 * (G T y.1 k.1 x) ^ 2) ∂T.μ =
        3 * M' ^ 2 * ‖T.toDiffusionTriple.Lcls y‖ ^ 2 + 3 * N' ^ 2 * ‖T.toDiffusionTriple.cls y‖ ^ 2 +
          12 * ‖Gm T k y‖ ^ 2 := by
      rw [integral_add i12 (iG.const_mul 12), integral_add i1 i2,
        integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
        integral_const_mul, norm_Lcls_sq, norm_cls_sq, norm_Gm_sq]
      ring
    rw [norm_Lcls_sq]
    refine hle.trans ?_
    rw [h1]
    have b1 : ‖T.toDiffusionTriple.Lcls y‖ ^ 2 ≤ ‖jL T y‖ ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) n2 2
    have b2 : ‖T.toDiffusionTriple.cls y‖ ^ 2 ≤ ‖jL T y‖ ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) n1 2
    have b3 : ‖Gm T k y‖ ^ 2 ≤ (CG * (2 * ‖jL T y‖)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (n3.trans (mul_le_mul_of_nonneg_left n4 hCG0)) 2
    have b4 : (CG * (2 * ‖jL T y‖)) ^ 2 = 4 * CG ^ 2 * ‖jL T y‖ ^ 2 := by ring
    rw [b4] at b3
    have c1 : 0 ≤ M' ^ 2 := sq_nonneg _
    have c2 : 0 ≤ N' ^ 2 := sq_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left b1 (by positivity : (0 : ℝ) ≤ 3 * M' ^ 2),
      mul_le_mul_of_nonneg_left b2 (by positivity : (0 : ℝ) ≤ 3 * N' ^ 2),
      mul_le_mul_of_nonneg_left b3 (by norm_num : (0 : ℝ) ≤ 12)]
  have key2 : ∀ y : T.A₀, ‖T.toDiffusionTriple.cls (k * y)‖ ^ 2 ≤ M' ^ 2 * ‖jL T y‖ ^ 2 := by
    intro y
    have n1 : ‖T.toDiffusionTriple.cls y‖ ≤ ‖jL T y‖ := norm_fst_le (jL T y)
    rw [norm_cls_sq]
    have iy2 := integrable_sq_A₀ y
    have iky2 := integrable_sq_A₀ (k * y)
    calc ∫ x, ((k * y).1 x) ^ 2 ∂T.μ ≤ ∫ x, M' ^ 2 * (y.1 x) ^ 2 ∂T.μ := by
          refine integral_mono iky2 (iy2.const_mul _) (fun x => ?_)
          show (k.1 x * y.1 x) ^ 2 ≤ _
          rw [mul_pow]; exact mul_le_mul_of_nonneg_right (hk2 x) (sq_nonneg _)
      _ = M' ^ 2 * ‖T.toDiffusionTriple.cls y‖ ^ 2 := by rw [integral_const_mul, norm_cls_sq]
      _ ≤ M' ^ 2 * ‖jL T y‖ ^ 2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) n1 2) (sq_nonneg _)
  refine ⟨M' + √D, by positivity, fun y => ?_⟩
  have c1 : ‖T.toDiffusionTriple.cls (k * y)‖ ≤ M' * ‖jL T y‖ := by
    have := key2 y
    have h' : (M' * ‖jL T y‖) ^ 2 = M' ^ 2 * ‖jL T y‖ ^ 2 := by ring
    exact abs_le_of_sq_le_sq' (h'.symm ▸ this) (by positivity) |>.2
  have c2 : ‖T.toDiffusionTriple.Lcls (k * y)‖ ≤ √D * ‖jL T y‖ := by
    have := key y
    have h' : (√D * ‖jL T y‖) ^ 2 = D * ‖jL T y‖ ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hD0]
    exact abs_le_of_sq_le_sq' (h'.symm ▸ this) (by positivity) |>.2
  have : ‖jL T (k * y)‖ ≤ ‖T.toDiffusionTriple.cls (k * y)‖ + ‖T.toDiffusionTriple.Lcls (k * y)‖ := by
    rw [jL_apply, Prod.norm_def]
    exact max_le (by linarith [norm_nonneg (T.toDiffusionTriple.Lcls (k * y))])
      (by linarith [norm_nonneg (T.toDiffusionTriple.cls (k * y))])
  nlinarith

lemma domain_subset_formDomain {u : Lp ℝ 2 T.μ} (hu : u ∈ T.toDiffusionTriple.generator.domain) :
    u ∈ T.formDomain :=
  ((DiffusionTriple.formData T.toDiffusionTriple).generator_mem_Q_and_form hu).1

/-- **BGL Prop. 3.3.16 (vii), first part**: `h f ∈ 𝒟(L)` for `f ∈ 𝒟(L)`, `h ∈ 𝒜₀`; moreover `h a_k → h f` in `𝒟(L)` for
every graph-convergent `a_k → f`. -/
theorem mulE_mem_domain (k : T.A₀) {u : Lp ℝ 2 T.μ} (hu : u ∈ T.toDiffusionTriple.generator.domain) :
    ∃ hdom : ((mulE k ⟨u, domain_subset_formDomain hu⟩ : T.formDomain) : Lp ℝ 2 T.μ) ∈
        T.toDiffusionTriple.generator.domain,
      ∀ a : ℕ → T.A₀, GraphConv T a u hu → GraphConv T (fun n => k * a n) _ hdom := by
  obtain ⟨C, hC0, hC⟩ := jL_mul_bound k
  obtain ⟨a0, ha0⟩ := exists_graphConv u hu
  have cauchy : ∀ a : ℕ → T.A₀, GraphConv T a u hu → CauchySeq (fun n => jL T (k * a n)) := by
    intro a ha
    rw [cauchySeq_iff_tendsto_dist_atTop_0]
    have c1 := cauchySeq_iff_tendsto_dist_atTop_0.1 (Tendsto.cauchySeq ha)
    have lim := c1.const_mul C
    simp only [mul_zero] at lim
    refine squeeze_zero (fun p => dist_nonneg) (fun p => ?_) lim
    rw [dist_eq_norm, ← map_sub, ← mul_sub]
    refine (hC _).trans ?_
    rw [map_sub, ← dist_eq_norm]
  obtain ⟨z, hz⟩ := cauchySeq_tendsto_of_complete (cauchy a0 ha0)
  have hQ := domain_subset_formDomain hu
  obtain ⟨_, hfc⟩ := ha0.formConv
  have hcls := FormConv.cls (mulE_formConv k hfc)
  have hz1 : z.1 = ((mulE k ⟨u, hQ⟩ : T.formDomain) : Lp ℝ 2 T.μ) :=
    tendsto_nhds_unique ((Tendsto.fst_nhds hz).congr (fun n => by rw [jL_apply])) hcls
  have hclosed := (DiffusionTriple.formData T.toDiffusionTriple).generator_isClosed
  have hmem : ∀ n, jL T (k * a0 n) ∈ (T.toDiffusionTriple.generator).graph := by
    intro n
    have := LinearPMap.mem_graph (T.toDiffusionTriple.generator)
      ⟨T.toDiffusionTriple.cls (k * a0 n), DiffusionTriple.cls_mem_generator_domain T.toDiffusionTriple _⟩
    rw [DiffusionTriple.generator_cls] at this
    exact this
  have hzg : z ∈ (T.toDiffusionTriple.generator).graph :=
    hclosed.mem_of_tendsto hz (Eventually.of_forall hmem)
  obtain ⟨y, hy1, -⟩ := (LinearPMap.mem_graph_iff _).1 hzg
  have hdom : ((mulE k ⟨u, hQ⟩ : T.formDomain) : Lp ℝ 2 T.μ) ∈ T.toDiffusionTriple.generator.domain := by
    rw [← hz1, ← hy1]; exact y.2
  refine ⟨hdom, fun a ha => ?_⟩
  obtain ⟨z', hz'⟩ := cauchySeq_tendsto_of_complete (cauchy a ha)
  -- same limit for every graph-convergent sequence
  have hz1' : z'.1 = ((mulE k ⟨u, hQ⟩ : T.formDomain) : Lp ℝ 2 T.μ) := by
    obtain ⟨_, hfc'⟩ := ha.formConv
    have hcls' := FormConv.cls (mulE_formConv k hfc')
    exact tendsto_nhds_unique ((Tendsto.fst_nhds hz').congr (fun n => by rw [jL_apply])) hcls'
  have hmem' : ∀ n, jL T (k * a n) ∈ (T.toDiffusionTriple.generator).graph := by
    intro n
    have := LinearPMap.mem_graph (T.toDiffusionTriple.generator)
      ⟨T.toDiffusionTriple.cls (k * a n), DiffusionTriple.cls_mem_generator_domain T.toDiffusionTriple _⟩
    rw [DiffusionTriple.generator_cls] at this
    exact this
  have hzg' : z' ∈ (T.toDiffusionTriple.generator).graph :=
    hclosed.mem_of_tendsto hz' (Eventually.of_forall hmem')
  obtain ⟨y', hy1', hy2'⟩ := (LinearPMap.mem_graph_iff _).1 hzg'
  have hyy : y' = ⟨_, hdom⟩ := Subtype.ext (by rw [hy1', hz1'])
  have hz2 : z'.2 = T.toDiffusionTriple.generator ⟨_, hdom⟩ := by
    rw [← hy2', hyy]
  unfold GraphConv
  have : z' = (((mulE k ⟨u, hQ⟩ : T.formDomain) : Lp ℝ 2 T.μ), T.toDiffusionTriple.generator ⟨_, hdom⟩) :=
    Prod.ext hz1' hz2
  rw [← this]; exact hz'

end FullTriple

end MarkovTriple.BGL
