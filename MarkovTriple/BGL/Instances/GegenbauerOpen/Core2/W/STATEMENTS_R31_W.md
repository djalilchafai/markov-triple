# Round 31, Stream W (`Core2` on the Gegenbauer open-interval family, negative half at `lam = 2`): frozen target statements

Written BEFORE any proof.  Namespace `MarkovTriple.BGL.Instances.GegenbauerOpen.Core2W`; files `Instances/GegenbauerOpen/Core2/W/*`
(`Series.lean`, `Pair.lean`, `Reduce.lean`, `Main.lean`, `AxiomCheckR31W.lean`).  Builds on `Core2Q.gL`, `Core2Q.gρ` (R29-Q), `goA₀`, `gocut`, `GoSeries` (R24-D).

## SCOPE (honest, decided before proving)
A `FullTriple` for `lam ≠ 3/2` does NOT exist in the library (the layer `Basic/Diffusion/Full/*`, `ESA/*` is hard-wired to `lam = 3/2`, ~4000 lines;
R29-Q).  Hence `FullTriple.Core2` cannot be instantiated at `lam = 2`.  Instead this stream formalises, FullTriple-free, the literal transcription of the
definition of `FullTriple.Core2` (`Theory/Extension/Converse.lean`, line 237) for the weighted operator `L_lam = gL lam` on
`𝒜₀ = C_c^∞((-1,1)) = goA₀` in `L²(muL lam)`, with `muL lam = ρ_lam dx|_{(-1,1)}` UNNORMALISED (`ρ_lam = (1-x²)^(lam-1/2)`;
`Core2` is invariant under multiplying the measure by a constant), and refutes it at `lam = 2`.  It does NOT claim `F1–F10` or a `FullTriple`
structure for `lam = 2`; the statement is "the graph-core property of `L_2` on `C_c^∞(-1,1)` fails".

## W1 (definition, parametric in real `lam`)
```lean
noncomputable def muL (lam : ℝ) : Measure ℝ :=
  (volume.restrict (Ioo (-1 : ℝ) 1)).withDensity (fun x => ENNReal.ofReal (Core2Q.gρ lam x))

/-- literal transcription of `FullTriple.Core2` for `L_lam` on `goA₀` in `L²(muL lam)`:
every `a ∈ 𝒜₀` is the limit of `(1-L)b_n` with `L(1-L)b_n → La`. -/
def Core2L (lam : ℝ) : Prop :=
  ∀ a ∈ goA₀, ∃ b : ℕ → ℝ → ℝ, (∀ n, b n ∈ goA₀) ∧
    Tendsto (fun n => eLpNorm (fun x => (b n x - Core2Q.gL lam (b n) x) - a x) 2 (muL lam)) atTop (𝓝 0) ∧
    Tendsto (fun n => eLpNorm (fun x => (Core2Q.gL lam (b n) x - Core2Q.gL lam (Core2Q.gL lam (b n)) x)
      - Core2Q.gL lam a x) 2 (muL lam)) atTop (𝓝 0)
```

## W2 (deficiency pair refutes `Core2L`, any real `lam`)
```lean
theorem not_core2L_of_pair (lam : ℝ) (w h : ℝ → ℝ)
    (hw : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w (Ioo (-1 : ℝ) 1))
    (hh : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h (Ioo (-1 : ℝ) 1))
    (hwL : ∀ x ∈ Ioo (-1 : ℝ) 1, Core2Q.gL lam w x = w x)
    (hh2 : MemLp h 2 (muL lam)) (hg2 : MemLp (fun x => w x - Core2Q.gL lam h x) 2 (muL lam))
    (hne : ∃ x ∈ Ioo (-1 : ℝ) 1, w x ≠ 0) : ¬ Core2L lam
```

## W3 (the pair exists for `lam = 2`)
```lean
theorem deficiency_pair_two : ∃ w h : ℝ → ℝ,
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w (Ioo (-1 : ℝ) 1) ∧
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h (Ioo (-1 : ℝ) 1) ∧
    (∀ x ∈ Ioo (-1 : ℝ) 1, Core2Q.gL 2 w x = w x) ∧
    MemLp h 2 (muL 2) ∧ MemLp (fun x => w x - Core2Q.gL 2 h x) 2 (muL 2) ∧ ∃ x ∈ Ioo (-1 : ℝ) 1, w x ≠ 0
```
Mathematics: `w = (1-x²)^(-3/2) A(x)`, `A = Σ c_n xⁿ` the solution of `(1-x²)A'' + xA' + 2A = 0`, `A(0)=1`, `A'(0)=0`
(`c_{n+2} = c_n (n²-2n-2)/((n+1)(n+2))`, `|c_n| ≲ n^{-5/2}`, so `|A(x) - A(1)| ≤ C(1-x²)`), `h = -(A(1)/2)(1-x²)^(-1/2)`,
`L_2 h = -(A(1)/2)(3 s^{-1/2} - 2 s^{-3/2})`, `w - L_2 h = (A-A(1)) s^{-3/2} + (3A(1)/2) s^{-1/2}`, `s = 1-x²`; weighted bound `(w - L_2h)² ρ_2 ≤ K`.
The singular exponent `1/2 - lam = -3/2` is a half-integer, so no logarithm is needed (unlike `lam = 3/2`).

## W4 (main)
```lean
theorem not_core2L_two : ¬ Core2L 2
```

## NOT claimed
`Core2L lam` for any other `lam` (the heuristic `3/2 ≤ lam < 7/2` stays unproved except `lam = 2`, and `lam = 3/2` through R24-D on the genuine `FullTriple`);
no `FullTriple` for `lam = 2`; no ESA of `L_2`; nothing for the hyperbolic plane or other complete triples (see GAPS for the outcome).
