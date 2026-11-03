# Hostile audit: round 15, stochastic layer completion (branch commit d5ac778)

Independent auditor. **Result: no soundness defect, no vacuity, no misformalization.** Verified: L^2-contractivity and `kernelRep_of_dense`; the Riesz-Markov
construction (`exists_posFunctional`, `exists_extend_addSubgroup`, `measurable_of_integrals`, `bind_le_of_integral_le`, `exists_kernel_of_posContraction`);
`rieszKernelRep_markov` (the `Kernel.piecewise` redefinition on a null set preserves the a.e. `rep`); the circle normalisation (variance 2t, eigenvalue e^{-(2 pi n)^2 t}, proved
not assumed) and exact Chapman-Kolmogorov; the OU Mehler kernel; the five fields of the `MarkovProcessSemigroupData` mirror against the real structure (read as plain text only;
nothing from the untrusted tree was executed or imported); the author's NOT-proved list (no exact CK / kappa_0 = id for Riesz kernels, so only a `KernelRepresentation`;
compact metrizable + finite mu; bounded-only `rep`; a.e. CK; sub-invariance only) is accurate. 9 modules recompiled from scratch, 0 errors/warnings; 41 axiom lines standard.
Findings (documentation, fixed as ERRATA R15-6): provenance of the read MarkovProcess copy overstated as 'commit 666cda02'; stale headers in OU/Bridge/KernelRep; STATEMENTS S4 says Q-subspace (code: Z-span).
Scope notes: the non-vacuity example only shows `Nonempty (KernelRepresentation circleCompact...)`; agreement of the Riesz and wrapped-Gaussian circle kernels follows from `ae_unique` but is not stated as a theorem.
