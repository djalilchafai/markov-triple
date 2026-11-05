import Mathlib
import MarkovTriple.Stochastic.R29.PoleNull
import MarkovTriple.Stochastic.FellerProcessBridge
import MarkovTriple.BGL.Instances.SphereOpen.Full

/-!
# Round 29 (O), part 3: a `MarkovProcessBridge` for the open zonal sphere `oT`, `oStandard`, `oFull`

`ZonO = (-1,1) ⊂ Zon = [-1,1]`.  The compact zonal Feller kernels `κ_t = fellerKernel sphere_isFeller t` satisfy (R29 `PoleNull`) `κ_t(x,·) ≪ μZ`
for every `x` and `t > 0`; so the poles `{±1}` are `κ_t(x,·)`-null for every `x ∈ (-1,1)` (and trivially for `t = 0`: `κ_0 = δ_x`).
The kernels `κ^O_t(x, A) := κ_t(x, A)` for `A ⊆ (-1,1)`, `x ∈ (-1,1)` are therefore Markov kernels on `(-1,1)` and inherit exact
Chapman-Kolmogorov, `κ^O_0 = id`, joint measurability, `μO` invariance; the representation of `P^O_t` follows from `PO_restrC`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace MarkovTriple.Stochastic.R29

open MarkovTriple.BGL MarkovTriple.BGL.Instances.Sphere MarkovTriple.BGL.Instances.SphereOpen MarkovTriple.Stochastic
  MarkovTriple.Stochastic.Sphere

/-- the compact zonal Feller kernels -/
noncomputable def Kz (t : ℝ≥0) : Kernel Zon Zon := fellerKernel sphere_isFeller t

theorem sphere_pole_null {t : ℝ≥0} (ht : 0 < t) (x : Zon) {A : Set Zon} (_hA : MeasurableSet A) (h : μZ A = 0) :
    Kz t x A = 0 := sphere_kernel_ac ht x h

theorem sphere_kernel_pole_null {t : ℝ≥0} (ht : 0 < t) (x : Zon) : Kz t x ZonOSetᶜ = 0 :=
  sphere_kernel_ac ht x μZ_compl

lemma Kz_add (s t : ℝ≥0) : Kz (s + t) = (Kz t).comp (Kz s) := fellerKernel_add sphere_isFeller s t

lemma Kz_zero : Kz 0 = Kernel.id := fellerKernel_zero sphere_isFeller

/-- for every time and every `x ∈ (-1,1)` the poles are null -/
theorem Kz_pole_null (t : ℝ≥0) {x : Zon} (hx : x ∈ ZonOSet) : Kz t x ZonOSetᶜ = 0 := by
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t) with h | ht
  · have h0 : t = 0 := h.symm
    subst h0
    rw [Kz_zero, Kernel.id_apply,
      Measure.dirac_apply' _ measurableSet_ZonOSet.compl]
    simp [hx]
  · exact sphere_kernel_pole_null ht x

/-- the kernels restricted to the open interval -/
noncomputable def KO (t : ℝ≥0) : Kernel ZonO ZonO :=
  Kernel.comapRight ((Kz t).comap jO continuous_jO.measurable) measurableEmbedding_jO

lemma KO_apply (t : ℝ≥0) (x : ZonO) : KO t x = (Kz t (jO x)).comap jO := rfl

lemma KO_apply_set (t : ℝ≥0) (x : ZonO) {A : Set ZonO} (hA : MeasurableSet A) :
    KO t x A = Kz t (jO x) (jO '' A) := by
  rw [KO, Kernel.comapRight_apply' _ _ _ hA]
  rfl

lemma KO_map (t : ℝ≥0) (x : ZonO) : (KO t x).map jO = Kz t (jO x) := by
  rw [KO_apply, measurableEmbedding_jO.map_comap, range_jO]
  exact Measure.restrict_eq_self_of_ae_mem (by
    rw [ae_iff]; exact Kz_pole_null t x.2)

theorem KO_isMarkov (t : ℝ≥0) (x : ZonO) : KO t x Set.univ = 1 := by
  have h := congrArg (fun m => m Set.univ) (KO_map t x)
  rw [Measure.map_apply measurableEmbedding_jO.measurable MeasurableSet.univ, Set.preimage_univ] at h
  rw [h]
  exact fellerKernel_isMarkov sphere_isFeller (fun t => semigroup_one t) t (jO x)

instance (t : ℝ≥0) (x : ZonO) : IsProbabilityMeasure (KO t x) := ⟨KO_isMarkov t x⟩

instance (t : ℝ≥0) : IsMarkovKernel (KO t) := ⟨fun _ => inferInstance⟩

theorem KO_zero : KO 0 = Kernel.id := by
  refine Kernel.ext fun x => Measure.ext fun A hA => ?_
  have hA' : MeasurableSet (jO '' A) := measurableEmbedding_jO.measurableSet_image.2 hA
  rw [KO_apply_set _ _ hA, Kz_zero, Kernel.id_apply, Kernel.id_apply, Measure.dirac_apply' _ hA',
    Measure.dirac_apply' _ hA]
  by_cases hx : x ∈ A
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (Set.mem_image_of_mem _ hx)]; rfl
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h => hx (jO_injective.mem_set_image.1 h))]

theorem KO_add (s t : ℝ≥0) : KO (s + t) = (KO t).comp (KO s) := by
  refine Kernel.ext fun x => Measure.ext fun A hA => ?_
  have hA' : MeasurableSet (jO '' A) := measurableEmbedding_jO.measurableSet_image.2 hA
  have hm : Measurable fun z : Zon => Kz t z (jO '' A) := Kernel.measurable_coe _ hA'
  rw [KO_apply_set _ _ hA, Kz_add,
    Kernel.comp_apply' _ _ _ hA', Kernel.comp_apply' _ _ _ hA, ← KO_map s x,
    measurableEmbedding_jO.lintegral_map]
  refine lintegral_congr fun w => ?_
  rw [KO_apply_set _ _ hA]

theorem KO_measurable : Measurable fun p : ℝ≥0 × ZonO => KO p.1 p.2 := by
  refine Measure.measurable_of_measurable_coe (fun p : ℝ≥0 × ZonO => KO p.1 p.2) fun A hA => ?_
  have hA' : MeasurableSet (jO '' A) := measurableEmbedding_jO.measurableSet_image.2 hA
  have e : (fun p : ℝ≥0 × ZonO => KO p.1 p.2 A) = fun p => Kz p.1 (jO p.2) (jO '' A) :=
    funext fun p => KO_apply_set p.1 p.2 hA
  rw [e]
  have h1 : Measurable fun p : ℝ≥0 × ZonO => ((p.1, jO p.2) : ℝ≥0 × Zon) :=
    measurable_fst.prodMk (continuous_jO.measurable.comp measurable_snd)
  have h2 : Measurable fun p : ℝ≥0 × Zon => Kz p.1 p.2 := sphereMarkovProcessBridge.measurable_kernel
  have h3 := (Measure.measurable_coe hA').comp (h2.comp h1)
  exact h3

theorem KO_bind (t : ℝ≥0) : μO.bind (KO t) = μO := by
  refine Measure.ext fun A hA => ?_
  have hA' : MeasurableSet (jO '' A) := measurableEmbedding_jO.measurableSet_image.2 hA
  rw [Measure.bind_apply hA (KO t).aemeasurable]
  have e : ∀ x : ZonO, KO t x A = Kz t (jO x) (jO '' A) := fun x => KO_apply_set t x hA
  rw [lintegral_congr e]
  rw [measurePreserving_jO.lintegral_comp_emb measurableEmbedding_jO (fun z => Kz t z (jO '' A))]
  have h2 : (μZ.bind (Kz t)) (jO '' A) = μZ (jO '' A) := by
    rw [show μZ.bind (Kz t) = μZ from fellerKernel_bind sphere_isFeller (fun t => semigroup_one t) t]
  rw [Measure.bind_apply hA' (Kz t).aemeasurable] at h2
  rw [h2]
  unfold μO
  rw [MeasurableEmbedding.comap_apply measurableEmbedding_jO]

/-- extension by zero of a function on `(-1,1)` -/
noncomputable def extO (g : ZonO → ℝ) : Zon → ℝ := Function.extend jO g 0

lemma extO_jO (g : ZonO → ℝ) : extO g ∘ jO = g := funext fun x => jO_injective.extend_apply _ _ x

lemma measurable_extO {g : ZonO → ℝ} (hg : Measurable g) : Measurable (extO g) :=
  measurableEmbedding_jO.measurable_extend hg measurable_const

lemma bdd_extO {g : ZonO → ℝ} {C : ℝ} (hC : ∀ x, |g x| ≤ C) : ∀ z, |extO g z| ≤ max C 0 := by
  intro z
  by_cases h : ∃ a, jO a = z
  · obtain ⟨a, rfl⟩ := h
    have : extO g (jO a) = g a := jO_injective.extend_apply _ _ a
    rw [this]; exact (hC a).trans (le_max_left _ _)
  · have : extO g z = 0 := by
      unfold extO
      rw [Function.extend_apply' _ _ _ h]; rfl
    rw [this]; simp

/-- **Representation** on bounded measurable `L²(μO)` functions -/
theorem KO_rep (t : ℝ≥0) (g : ZonO → ℝ) (hg : Measurable g) (hb : ∃ C, ∀ x, |g x| ≤ C)
    (hL : MemLp g 2 μO) :
    (oT.semigroup t (hL.toLp g) : ZonO → ℝ) =ᵐ[μO] fun x => ∫ y, g y ∂(KO t x) := by
  obtain ⟨C, hC⟩ := hb
  have hgm := measurable_extO hg
  have hbd := bdd_extO hC
  have hL' : MemLp (extO g) 2 μZ :=
    MemLp.of_bound hgm.aestronglyMeasurable (max C 0) (ae_of_all _ fun z => by
      simpa [Real.norm_eq_abs] using hbd z)
  have hLj : MemLp (extO g ∘ jO) 2 μO := by rw [extO_jO]; exact hL
  have e : restrC (hL'.toLp (extO g)) = hL.toLp g := by
    rw [restrC_apply, restrL_toLp 2 hL' hLj]
    refine Lp.ext ?_
    filter_upwards [hLj.coeFn_toLp, hL.coeFn_toLp] with x h1 h2
    rw [h1, h2, extO_jO]
  have hrep := sphereMarkovProcessBridge.rep t (extO g) hgm ⟨_, hbd⟩ hL'
  have h1 : oT.semigroup t (hL.toLp g) = restrC (sT.semigroup t (hL'.toLp (extO g))) := by
    rw [← e]; exact PO_restrC t _
  rw [h1]
  filter_upwards [coeFn_restrL 2 (sT.semigroup t (hL'.toLp (extO g))), ae_comap_jO hrep] with x a b
  rw [restrC_apply, a]
  refine b.trans ?_
  show ∫ y, extO g y ∂(Kz t (jO x)) = _
  rw [← KO_map t x, integral_map measurableEmbedding_jO.measurable.aemeasurable hgm.aestronglyMeasurable]
  exact integral_congr_ae (ae_of_all _ fun y => congrFun (extO_jO g) y)

/-- **A `MarkovProcessBridge` for the open zonal sphere** (`(-1,1)`, `S³`): jointly measurable Markov kernels with exact
Chapman-Kolmogorov, `κ_0 = id`, `μO` invariant, representing `P_t` on bounded measurable `L²(μO)` functions. -/
noncomputable def oMarkovProcessBridge : MarkovProcessBridge oT where
  kernel := KO
  measurable_kernel := KO_measurable
  kernel_zero := KO_zero
  kernel_add := KO_add
  isSubMarkovKernel := fun t x => (KO_isMarkov t x).le
  rep := fun t g hg hb hL => KO_rep t g hg hb hL
  invariant := fun t => KO_bind t

theorem oMarkovProcessBridge_kernel (t : ℝ≥0) (x : ZonO) {A : Set ZonO} (hA : MeasurableSet A) :
    oMarkovProcessBridge.kernel t x A = Kz t (jO x) (jO '' A) := KO_apply_set t x hA

theorem oMarkovProcessBridge_isMarkov : ∀ t x, oMarkovProcessBridge.kernel t x Set.univ = 1 := KO_isMarkov

noncomputable def oStandard_bridge : MarkovProcessBridge oStandard.toDiffusionTriple := oMarkovProcessBridge

noncomputable def oFull_bridge : MarkovProcessBridge oFull.toDiffusionTriple := oMarkovProcessBridge

end MarkovTriple.Stochastic.R29
