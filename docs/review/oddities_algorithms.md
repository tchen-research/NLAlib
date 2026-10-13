# Oddities review: Krylov, Polynomial, Solvers, Estimation, LowRank, Sketching

Read-only review, 2026-10-13, branch `nlalib-f2`. No Lean file was edited and no Lean or lake process
was run. Inputs: the sources, `atlas/declarations.json` (signatures and docstrings), `docs/STANDARDS.md`
§2–§3, `docs/KRYLOV_DEFINITIONS.md`, `docs/ALGORITHM_CONVENTIONS.md`, `docs/FOUNDATIONS_BRIEF.md`,
`docs/port/MANIFEST.md`, `docs/SKETCH_INTERFACE.md`. The question is: where would an outside reader (a
numerical analyst, or a Mathlib reviewer) think something is weird? Paths are under `NLAlib/`; the line
is that of the `def`/`theorem`/`structure` keyword. Signatures are quoted from `declarations.json`, with
binders shortened. Gaussian law shapes (`μ.map (Matrix.of.symm ∘ Ω) = gaussianMatrix n t`, `Fin`
arrays, `.toReal` tails) are F2's job; they are noted, not argued.

## Top 10 (most likely to be noticed first)

1. **"Is an oblivious subspace embedding" is stated five different ways** (§2.1). Gaussian and sparse
   state success, `1 - δ ≤ P(IsSubspaceEmbedding …)`; CountSketch states failure of the same predicate;
   SRHT states failure of a Gram spectral-norm event, `ε < specNorm ((SU)ᵀ(SU) − 1)`; leverage sampling
   is over ℂ and spells out the norm inequalities with `‖WithLp.toLp 2 …‖²` and never uses
   `IsSubspaceEmbedding`. On top of that the events mix `<` and `≤`, and the tails mix
   `ENNReal.ofReal`, `.toReal` and `μ.real`.
2. **The HMT and Tropp–Webber headlines are paper-named and take the probabilistic step as a
   hypothesis** (§2.2). `rsvd_main`, `rsvd_truncated_main`, `gn_main`, `completion_reduction` and
   `Assembly.rsvd_explicit`/`gn_explicit` carry the atlas ids `rsvd-expected-error`/`gn-expected-error`.
   They assume `hinv : ∫ frobSq (S₂ Ω₂ Ω₁⁺) = k/(t−k−1) · frobSq S₂`, which is the Gaussian fact the
   theorem is about. The unconditional theorems are the 90-character `integrable_and_integral_…`
   names.
3. **The "expected error" in Solvers and RPCholesky is a deterministic recursion or finite sum, not
   an integral** (§1.6). `Kaczmarz.expErr`, `SketchProject.expErr`, `choleskyExpectedTrace` and
   `volumeSamplingExpectedFrobSq` are `def`s. For `A = 0`, `Kaczmarz.prob` is `0/0 = 0`, so the
   "expected error" is `0`. The manifest rebuilds Solvers but not `LowRank/Cholesky` or the real
   `VolumeSampling`.
4. **Twins and parallel vocabularies that the port must collapse** (§3). `complexBlockKrylovSpace`
   duplicates `blockKrylovSpace`, which is already over any field. `complexSubspaceIterate`
   duplicates `subspaceIterate`. There are six spellings of a principal-angle tangent. There are two
   subspace-iteration convergence families under the same atlas id. The ℝ and ℂ volume-sampling
   twins have different shapes: the ℝ one is a finite sum, the ℂ one a `Measure`.
5. **Spectral theorems quantify over Mathlib's chosen eigenvector basis and take hypotheses that are
   always true** (§2.3). Examples: `hb : (hA.eigenvectorBasis i₁).ofLp ⬝ᵥ b ≠ 0`, `htop : ∀ i,
   hA.eigenvalues i ≤ hA.eigenvalues i₁` (unsorted eigenvalues), and
   `hT : (Qᵀ * A * Q).IsHermitian` (which follows from `hA`) in the Ritz, power and random-start
   results.
6. **Index and degree conventions drift** (§2.4). `krylovSpace A b q` is the `q`-dimensional space
   (`degree < q`). Next to it are Gauss forms with `natDegree ≤ 2q−1` and `0 < q`, a bound with
   `ρ^(2q−1)`, a Ritz bound with exponent `q−1`, Kaniel–Paige–Saad on `K_{q+1}` with `T_q`, Lanczos
   random-start with `2 ≤ q` and `(q−1)²`, and power random-start with `2q+1`. Also,
   `singularValues A k` is σ_{k+1}.
7. **Krylov processes have three spellings each, and `LanczosDecomp` does not know that `A` is
   symmetric** (§1.2). The Lanczos vectors are `arnoldiBasis` = `ArnoldiDecomp.Q`/`LanczosDecomp.vec`
   = `lanczosRecurrence`. The Hessenberg matrix is `arnoldiHessenberg` = `ArnoldiDecomp.H` =
   `LanczosDecomp.T`. The coefficients are `lanczosAlpha`/`lanczosBeta` = `LanczosDecomp.alpha`/`beta`.
   The symmetry hypothesis is `IsSymm` in some theorems and `IsHermitian` in others. CG and Lanczos
   have no `…Succeeds` predicate, contrary to ALGORITHM_CONVENTIONS, and their realisation theorems
   are `sorry`.
8. **Docstrings speak in port and provenance language.** In this area, "manuscript `sa:…`/`rt:…`/`sh:…`"
   appears on 226 lines in 34 files, "operator re-derivation" on 145 lines, "the actual …" on 242 lines
   in 62 files, and the top-level Sparse files carry `SparseFockFormal` commit hashes. Even the names
   say it: `srhtManuscriptRowBound`, `measure_srht_gram_failure_le_of_manuscript_sample_size`. An
   outsider cannot resolve any of these references.
9. **Optimal-error baselines are spelled six ways** (§3). They are `bestRankFrobSq k A`,
   `singularValueTailSq A k`, `spectralTraceTail A hA r`, `complexGramTail`, `frobSq S₂` for an
   arbitrary partitioned `A = U₁S₁V₁ᵀ + U₂S₂V₂ᵀ`, and an inline `∑ i, if k ≤ i then σᵢ^… else 0`.
   The randomized Nyström bound is stated through a factor (`A = Fᵀ F`, `bestRankFrobSq k F`) instead
   of the eigenvalue tail of `A`.
10. **Some constants are visibly worse than the literature**, though documented. Hutchinson's
    relative error needs `m ≥ 256e² ε⁻² log(2/δ)`, about 1900 ε⁻² log(2/δ), against roughly
    8 ε⁻² log(2/δ) from CK21 Thm 1 (`Estimation/Trace/HutchinsonTail.lean:270`). SLQ needs `1024 e²`. Sparse uses
    the parameter constants 1356 and 306456. JL union-bounds over `N²` ordered pairs.

## 1. Definitions a numerical analyst would find odd

**1.1 Spaces and methods (Krylov).**
- `krylovSpace (A : Matrix n n K) (b : n → K) (q : ℕ) := span {A^i b | i : Fin q}` (`Krylov/Spaces/Basic.lean:26`):
  `q` is the *dimension bound* (= number of vectors), not the degree; this is right, but the docstring
  should say "`K_q` contains `p(A)b` for `deg p < q`, i.e. `q − 1` matvecs" because §2.4's theorems
  mix both readings. Fix: one sentence in the docstring and in KRYLOV_DEFINITIONS §6.1.
- `IsCGIterate A c x₀ q x` (`Krylov/Solvers/CG.lean:56`), `IsGMRESIterate` (`Krylov/Solvers/GMRES.lean:50`),
  `IsPCGIterate A P c x₀ q x := IsAffineMinimiser (cgObjective A c) x₀ (krylovSpace (P⁻¹ * A) …)`
  (`Krylov/Solvers/Preconditioned.lean:95`): predicates, not iterates. Intentional (KRYLOV_DEFINITIONS §2),
  but a reader looks for `cgIterate` and for uniqueness: there is `exists_isCGIterate` (`CG.lean:135`)
  and GMRES's `eq_of_isUnit`, but no `existsUnique_isCGIterate`, and the planned
  `IsPetrovGalerkinIterate`/`IsFOMIterate` do not exist although lemmas are tagged `fom-def`.
  Fix: add the uniqueness theorem and a one-line "why a predicate" note in each docstring.
- Right-hand side is `c` in Krylov (`A x = c`, because `b` is the start vector) and `b` in
  `IsCGLSIterate A b x₀ q x` (`Preconditioned.lean:228`) and Kaczmarz. Intentional; document the
  convention once.
- `krylovFunApprox (Q : Matrix n k ℝ) (A) (f) (b) := Q *ᵥ (cfc f (Qᵀ*A*Q) *ᵥ (Qᵀ *ᵥ b))`
  (`Krylov/MatrixFunctions/FunctionApprox.lean:63`) versus `slqEstimate A f Q G` (`Estimation/Quadrature/SLQ.lean:41`):
  the two compressions put `Q` first and third. Fix: one argument order (`A f b Q`).
- `polyIterate`, `chebyshevIterate a b A c x₀ q`, `richardsonIterate ω A c x₀ q` (`PolynomialMethods.lean:44,195,103`)
  are honest definitions; fine.

**1.2 Processes.**
- `abbrev LanczosDecomp A b q := ArnoldiDecomp A b q` (`Krylov/Processes/Arnoldi.lean:233`): a
  "Lanczos decomposition" of a nonsymmetric `A` typechecks, so every Lanczos theorem re-takes symmetry,
  and spells it `hA : A.IsSymm` (`LanczosDecomp.dotProduct_aeval_mulVec_eq`, `Processes/Lanczos.lean:328`;
  `T_apply_eq_zero_of_one_lt_dist`, `Arnoldi.lean:403`) or `hA : A.IsHermitian`
  (`…_eq_sum`, `Quadrature/Jacobi.lean:368`). Fix: always `IsHermitian` (what `hA.eigenvalues` needs);
  document the abbrev as intentional (one object, symmetric layer = hypotheses).
- `LanczosDecomp.alpha/beta (D) : ℕ → ℝ`, zero outside `j < q` and `β_0 = 0` (`Lanczos.lean:213,219`):
  the coefficient `β_q` that multiplies `q_{q+1}e_qᵀ` in `AQ_q = Q_qT_q + β_q q_{q+1}e_qᵀ` is not
  available from a size-`q` decomposition (`mul_restrict_Q_eq_add_beta_smul` needs `D : LanczosDecomp A b (q+1)`,
  `Lanczos.lean:297`), so at the grade the relation is a separate theorem
  (`mul_Q_eq_mul_H_iff (hq : 0 < q) : A * D.Q = D.Q * D.H ↔ krylovGrade A b = q`, `Lanczos.lean:137`).
  Intentional; document "β beyond the range is 0 by convention, never by theorem".
- Three spellings per object (top-10 #7): `arnoldiBasis`/`arnoldiMatrix`/`arnoldiHessenberg`
  (`ArnoldiProcess.lean:50,56,62`), `ArnoldiDecomp.Q`/`.H` (`Arnoldi.lean:223,242`), `LanczosDecomp.vec/T/alpha/beta`,
  `lanczosRecurrence`/`lanczosAlpha`/`lanczosBeta` (`LanczosRecurrence.lean:78,83,89`). The design is
  process vs predicate vs recursion, but the names do not say which is which. Fix: suffix convention
  (`…Process`, `D.…`, `…Recurrence`) and a table in the Krylov module docstring.
- `LanczosState.beta` is documented as `β_j = q_jᵀ A q_{j−1}` (`LanczosRecurrence.lean:47`) and
  `lanczosBeta` as `β_j = ‖w_{j−1}‖` (`:89`): equal only in exact arithmetic with symmetric `A`.
  Fix: one definition in both docstrings (the recursion's: the norm).
- `cgRecurrence`/`lanczosState` (`CGRecurrence.lean:77`, `LanczosRecurrence.lean:72`) have no
  `CGSucceeds`/`LanczosSucceeds`, while `GolubKahanSucceeds` and `QRAlgorithmSucceeds` exist
  (`Bidiagonalization.lean:219`, `QRAlgorithm.lean:110`). ALGORITHM_CONVENTIONS §1.3 asks for all four.
  Fix: either add them (`CGSucceeds ↔ k ≤ grade`) or record that `x/0 = 0` makes CG/Lanczos succeed
  unconditionally (then say so in ALGORITHM_CONVENTIONS).
- `qrAlgorithm (qr : Matrix (Fin n) (Fin n) ℝ → _ × _) (μ : ℕ → ℝ) (A) : ℕ → Matrix …`
  (`Krylov/Spectral/QRAlgorithm.lean:77`): the algorithm is parametrised by an arbitrary "QR routine"
  function and `QRAlgorithmSucceeds` checks after the fact that it produced QR factors. Unusual but
  defensible; document. It is `Fin n` only because `IsUpperHessenberg`/`IsTridiagonal` are.
- `jacobiMatrix (a β : ℕ → ℝ) (m)` with off-diagonal `β (i+1)` and `jacobiFraction (a β) (x) : ℕ → ℕ → ℝ`
  ("`m` levels from level `k`") (`Quadrature/JacobiFraction.lean:34,43`): consistent with
  `LanczosDecomp.beta`'s shift, but the shift and the argument order (`x` before the level counts) need a
  docstring example. Name `a` vs `alpha` elsewhere.
- `lanczosRitzValue A b q` = "largest Ritz value as a countable rational-coefficient supremum"
  (`Krylov/Spectral/MeasurableRitz.lean:34`): a definition chosen for a measurability proof; readers
  expect `λ_max(QᵀAQ)`. Fix: define as the sup of Rayleigh quotients over `K_q`, prove the countable form.

**1.3 Polynomial.**
- `chebyshevZero (q) (k : Fin q) := cos((2k+1)π/(2q))` (`Polynomial/Chebyshev/Core.lean:63`, decreasing)
  is a local definition while the extrema grid uses Mathlib's `Polynomial.Chebyshev.node`: two node
  conventions side by side. Fine, but say so.
- `chebyshevResidual` docstring says "Atlas: `chebyshev-minimax`" and is tagged `inverse-polynomial-approx`
  (`Core.lean:42`). Fix the tag.
- `chebyshevAnalyticCoeff (F : ℂ → ℂ) (k) : ℝ` and `chebyshevAnalyticTrunc (F : ℂ → ℂ) N`
  (`FunctionApproximation/AnalyticCoefficients.lean:28`, `AnalyticApproximation.lean:92`): Chebyshev
  coefficients are defined from a *complex extension* by a contour integral, so "the Chebyshev
  truncation of `f`" depends on a choice of `F` (theorems tie them with `hmatch`). A numerical analyst
  expects `c_k(f) = (2/π)∫₀^π f(cos θ) cos kθ dθ` for `f : ℝ → ℝ`. Fix: define on `f`, prove the
  contour formula.
- `evenChebyshevFilter k := C (1/(2k+1)) * contract 2 (U ℝ (2k))` (`Chebyshev/EvenChebyshevFilter.lean:49`):
  correct (`U_{2k}(√x)/(2k+1)`), but it lives in layer 0 only for `random-start-power`.
- `sawtoothCriticalPoint (n) (j : Fin n)` "chosen from Rolle's actual existence theorem"
  (`BestApproximation/SawtoothZeros.lean:83`) and a dozen other public `sawtooth*`/`jackson*` helpers: proof
  scaffolding of one theorem (`exists_degree_le_abs_sub_eval_le_jackson_interval`, `Jackson.lean:15`)
  exposed as API. Fix: `private` or a `Jackson.Internal` namespace (memory: no proof-named subtrees).

**1.4 Estimators.** `hutchinsonEstimate (A) (Z : n → κ → ℝ)` (`Estimation/Trace/HutchinsonTail.lean:53`),
`slqEstimate … (G : n → κ → ℝ)`: test matrices are curried functions, not `Matrix n κ ℝ`. And
`hutchinsonBlock (κ) (A)` (`:59`) takes the index type explicitly and first. Fix at port: `Matrix n κ ℝ`,
implicit `κ`.

**1.5 Sketching definitions.**
- `IsSubspaceEmbedding (S : Matrix k m ℝ) (U : Matrix m d ℝ) (ε) := ∀ x, (1−ε)‖Ux‖² ≤ ‖SUx‖² ≤ (1+ε)‖Ux‖²`
  (`Sketching/Properties/SubspaceEmbedding/Basic.lean:27`). `U` is any spanning matrix (the property
  depends only on `range U`, `isSubspaceEmbedding_mul_right_iff`), and `ε` is a relative error on
  *squared* norms (Woodruff's convention; Sarlós/Nelson–Nguyen use unsquared norms, hence the `3a ≤ ε`
  bridge `isSubspaceEmbedding_of_forall_sqrt_le`, `Sketching/Gaussian/GaussianEmbedding.lean:38`).
  The docstring should say both explicitly. Several lemmas demand `HasOrthonormalCols U` needlessly,
  e.g. `isSubspaceEmbedding_reindex_iff (hU : HasOrthonormalCols U) (hε : 0 ≤ ε)`
  (`…/FiniteIndexTransport.lean:26`); relabelling needs neither. ℝ-only, while leverage sampling is ℂ.
- `gaussianMatrix (p m : ℕ) : Measure (Fin p → Fin m → ℝ)`: order is (rows, cols) and is used
  consistently (`gaussianMatrix k n` for a `k × n` JL map, `gaussianMatrix n t` for `Ω`); F2 owns the rest.
- `leverageScore (A : Matrix m n ℝ) (i) := (A A⁺)ᵢᵢ` (`Sketching/Sampling/Leverage.lean:36`) is good,
  but leverage *sampling* never uses it: `measure_leverage_embedding_failure_le_of_sample_size`
  (`LeverageSampling.lean:222`) takes `U : Matrix n (Fin d) ℂ`, `hU : Uᴴ * U = 1`,
  `hdom : ∀ i, β * ∑ a, ‖U i a‖² / d ≤ p i`. `leverageSamplingSketch p ω : Matrix (Fin k) n ℂ` (`:23`) is a
  third selector besides `selectionMatrix s : Matrix n (Fin k) ℝ` (Matrix/Basic/Selection) and SRHT's
  `(selectionMatrix I)ᵀ`. Fix: state with `leverageScore` and `IsSubspaceEmbedding` over `𝕜`.
- Sketch orientation: everywhere `S : Matrix k m` acts as `S * A`, but
  `SketchProject.step (A : Matrix m n ℝ) (b) (S : Matrix m s ℝ) (x) := x − (SᵀA)⁺ Sᵀ(Ax − b)`
  (`Solvers/SketchAndProject/Core.lean:37`) uses Gower–Richtárik's transposed `S`. Document or flip.
- Random signs are `Bool` in SRHT (`srhtLaw : Measure ((Fin n → Bool) × ExactRowSubset (Fin n) k)`,
  `Structured/SRHT.lean:25`), an inductive `SparseSketch.Sign` in SparseStack, and `ℝ` with
  `IsRademacher`/`countSketchLaw : Measure ((ι → ρ) × (ι → ℝ))` in CountSketch and Hutchinson.
- `sparseStackMatrix (Z : SparseStackSample s b n) : Matrix (Fin s × Fin b) (Fin n) ℝ` vs
  `uniformSparseMatrix (X : UniformSparseSample m s n) : Matrix (Fin m) (Fin n) ℝ`
  (`Sparse/SparseStack.lean:169`, `Sparse/UniformSparse.lean:159`): different row index shapes and
  parameter orders (`s b n` vs `m s n`) for the same kind of object.

**1.6 Low rank and solvers.**
- `Kaczmarz.prob A i := (A i ⬝ᵥ A i) / frobSq A`, `Kaczmarz.expErr A b xs : (n → ℝ) → ℕ → ℝ` by first-step
  recursion (`Solvers/Kaczmarz/Core.lean:60,68`); `SketchProject.expErr` likewise (`SketchAndProject/Core.lean:45`);
  `choleskyExpectedTrace A t := ∑ h : Fin t → n, choleskyHistoryWeight A t h * tr(R_h)`
  (`LowRank/Cholesky/CholeskyHistories.lean:29`); `volumeSamplingExpectedFrobSq` (`LowRank/Sampling/VolumeSampling.lean:39`).
  "Expected" names a `def` that is not an expectation (and is `0` at `A = 0` for Kaczmarz). Kaczmarz has
  the bridge `integral_sqErr_kaczmarzRowPathPMF (hA : A ≠ 0)` (`KaczmarzProbability.lean:66`); RPCholesky
  has none. Fix (manifest already rebuilds Solvers): define the law (`PMF` on paths), make the finite sum a
  lemma, and add the same rebuild to `LowRank/Cholesky` and the real volume sampling.
- `nystrom A Ω := AΩ (ΩᵀAΩ)⁺ ΩᵀA` (`LowRank/Nystrom/Structural.lean:50`) is standard. But there are two more
  Nyström-type estimators, `sketchedOutput Q Ψ A` (with `pinvL`, `Nystrom/SketchedRegression.lean:67`) and
  `rawGeneralizedNystrom A Y Ψ` (with `moorePenroseInverse`, `RawNystromBridge.lean:77`). A reader
  wants one `generalizedNystrom` with the Moore–Penrose inverse (STANDARDS §3 default) and the `pinvL`
  form as a lemma.
- `partialCholeskyResidual A (s : Fin k → n)` (`Cholesky/PartialCholesky.lean:45`): a recursion over a
  pivot sequence. Its identity with `A − nystrom A (selectionMatrix s)` is a `sorry`
  (`partialCholeskyResidual_eq_sub_nystrom`), so RPCholesky and Nyström are not yet connected.
- There is no `rsvd` definition. `truncatedRsvdOutput (Q : Matrix (Fin m) (Fin q) ℝ) A k`
  (`RandomizedSVD/OptimalError.lean:113`) is the post-processing, the range finder is "any `Q` with
  `Q (Qᵀ (AΩ)) = AΩ`", and `gaussianRangeFrame A t : (Fin n → Fin t → ℝ) → Matrix (Fin m) (Fin (min A.rank t)) ℝ`
  (`RandomMatrix/Gaussian/Spectral/SketchRank.lean:253`) is a chosen frame with `min (rank A) t` columns.
  A reader expects `rsvd A Ω k`. Fix: define `rangeFinder`/`rsvd` as relations ("any orthonormal `Q` with
  `range Q = range AΩ`"), mirroring `subspaceIterate`, and keep the chosen frame internal.

## 2. Theorem statements weaker, stranger or more hypothesis-laden than the source

**2.1 OSE shapes** (top-10 #1). Compare:
`one_sub_le_measure_isSubspaceEmbedding_gaussianMatrix … : 1 − ENNReal.ofReal δ ≤ gaussianMatrix k m {G | IsSubspaceEmbedding ((1/√k) • Matrix.of G) U ε}`
(`Sketching/Gaussian/GaussianEmbedding.lean:72`);
`measure_sparseStack_embedding_success_ge : 1 − δ ≤ (sparseStackMeasure …).real {z | IsSubspaceEmbedding …}` (`Sparse/SparseEmbedding.lean:35`);
`measure_countSketch_embedding_failure_le_of_rows : countSketchLaw.real {z | ¬IsSubspaceEmbedding …} ≤ δ` (`Sparse/CountSketchTail.lean:83`);
`measure_srht_gram_failure_le_of_sharp_sample_size : ((srhtLaw hk) {ω | ε < specNorm ((S U)ᵀ(S U) − 1)}).toReal ≤ δ` (`Structured/SRHT.lean:106`);
`measure_countSketch_gram_failure_le : … {z | ε ≤ specNorm (…)} ≤ …` (`CountSketchTail.lean:38`; `≤` where SRHT has `<`);
leverage (§1.5). Fix: one predicate `IsOSE (law) d ε δ := δ`-failure of `IsSubspaceEmbedding` (or
success ≥ `1 − δ`, pick one), every distribution theorem concludes it, and the Gram-norm event is a lemma.

**2.2 RSVD / GN** (top-10 #2).
`rsvd_main … (hkt : k + 2 ≤ t) … (hinv : ∫ ω, frobSq (S₂ * (V₂ᵀ * Ω ω) * pinvR (V₁ᵀ * Ω ω)) ∂μ = k / (t − k − 1) * frobSq S₂) (hXi …) (hZi …) : ∫ ω, frobSq (A − Q ω * ((Q ω)ᵀ * A)) ∂μ ≤ (1 + k/(t−k−1)) * frobSq S₂`
(`LowRank/RandomizedSVD/RSVD.lean:142`). Here the Gaussian content is a hypothesis, the residual is
written out instead of as `residual (Q ω) A`, and `S₂` is the tail block of an *arbitrary*
partitioned decomposition (no SVD; `U₁` need not be orthonormal). `gn_main` (`Nystrom/GeneralizedNystrom.lean:113`)
adds `hcond`, which is the entire sketched-regression step, as a hypothesis. `Assembly.rsvd_explicit`
(`RandomizedSVD/Assembly.lean:75`) is a lemma about three real random variables, yet it carries the
headline id. The good statements exist:
`integrable_and_integral_frobSq_residual_le_bestRankFrobSq_gaussian (A : Matrix (Fin m) (Fin n) ℝ) (hkt : k + 2 ≤ t) (G) (hG : μ.map (Matrix.of.symm ∘ G) = gaussianMatrix n t) (Qf) (hQf) (hQo) (hQr) : Integrable … ∧ ∫ frobSq (residual (Qf …) A) ≤ (1 + k/(t−k−1)) * bestRankFrobSq k A`
(`OptimalError.lean:77`). Fix: give the headline the atlas id and a short name
(`integral_frobSq_residual_rangeFinder_le`). Demote `*_main`/`Assembly.*` to untagged helpers in
`lowerCamel`. The parametrisation also differs between neighbours. Frobenius RSVD uses `t` with
`k + 2 ≤ t`. Spectral HMT 10.6 uses `Fin (k + p)` with `1 ≤ k`, `2 ≤ p`, `k ≤ n`
(`RangeFinding/SpectralRangeFinder.lean:403`). GN uses `t, s` with `t + 2 ≤ s`. HMT writes `k, p`
throughout, so the port should pick one parametrisation. The library's `1 ≤ k` is weaker than HMT's
`k ≥ 2`, which is good, but say so. Measurability of `Q` is required in `ExpectedPower` (`hQ`,
`ExpectedPower.lean:113`) and not in `integral_specNorm_residual_le_of_gaussian` (`:266`).

**2.3 Chosen bases and redundant hypotheses** (top-10 #5).
`eigenvalues_sub_eigenvalues_transpose_mul_mul_le (hA : A.IsHermitian) {i₁} … (hb : (hA.eigenvectorBasis i₁).ofLp ⬝ᵥ b ≠ 0) (q) (hQ) (hK : krylovSpace A b (q+1) ≤ range Q) (hT : (Qᵀ * A * Q).IsHermitian) {j₁} (hj₁ : ∀ j, hT.eigenvalues j ≤ hT.eigenvalues j₁) : …`
(Kaniel–Paige–Saad, `Krylov/Spectral/Ritz.lean:450`). `hT` is derivable from `hA`. `j₁`/`htop` stand in
for sorted eigenvalues (STANDARDS has `eigenvalues₀`). `hb` depends on Mathlib's *choice* of eigenvector
when `λ₁` is repeated. The same pattern appears in `exists_eigenvalues_transpose_mul_mul_ge` (`Ritz.lean:176`),
`abs_rayleighQuotient_powerIterate_sub_le`, `lanczosRayleighRelativeError_le_log_sq (h₀ : ….eigenvalues i₀ = specNorm A) (hb : (….eigenvectorBasis i₀).ofLp ⬝ᵥ b ≠ 0)`
(`Estimation/Spectral/RandomStartLanczos.lean:49`). Fix: take `u` with `A *ᵥ u = λ • u`, `u ⬝ᵥ u = 1`. Use
`eigenvalues₀ 0` for the top. Build `(isHermitian_transpose_mul_mul hA Q)` inside the statement, as
`LanczosDecomp.cfc_T_apply_zero_zero` already does.

**2.4 Degree and indexing** (top-10 #6).
- Gauss exactness exists in two forms: `dotProduct_aeval_mulVec_eq_of_degree_lt_two_mul (hp : p.degree < 2 * q)`
  (`Quadrature/GaussQuadrature.lean:154`) and the legacy `…_of_krylovSpace_le (hq : 0 < q) (hp : p.natDegree ≤ 2 * q − 1)`
  (`:181`). The downstream results kept the legacy shape. `abs_dotProduct_cfc_mulVec_sub_le_of_lipschitzOnWith (hq : 0 < q)`
  (`LipschitzQuadrature.lean:26`) and `…_of_open_bernsteinEllipse (hq : 0 < q) : … ≤ 4M/ρ^(2q−1)/(ρ−1) …`
  (`AnalyticQuadrature.lean:27`) are examples, and the SLQ analytic/Lipschitz tails inherit `hq`.
  KRYLOV_DEFINITIONS §3.7 already asked for this change. Fix: one `degree < 2q` statement. Delete the
  `natDegree` form.
- `mem_krylovSpace_iff (hq : 0 < q) … ↔ ∃ p, p.natDegree < q ∧ …` (`Spaces/Polynomial.lean:72`) takes the
  plain name, while the hypothesis-free `mem_krylovSpace_iff_degree` (`:48`) carries the suffix. Swap the names.
- Random start: `integral_lanczosRayleighRelativeError_pi_gaussianReal_le (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA) (hq : 2 ≤ q) : ∫ … ≤ min 1 (4((log(2(n+1)) + 2 + log 2)² + 4) / (log 2² · (q−1)²))`
  (`RandomStartLanczos.lean:123`) sits next to a `_all_dims` (`Fin n`, `:223`) and an `_of_map_eq` copy.
  Power counts matvecs (`A^q b`, bound `/(2q+1)`, `RandomStartPower.lean:52`), Lanczos counts the dimension
  of `K_q` (`q−1` matvecs, hence `2 ≤ q`). Fix: index Lanczos by matvecs (`K_{q+1}`, bound `/q²`, `1 ≤ q`),
  keep one dimension-general statement, and drop the `Fin (n+1)` one.
- `singularValues A k` (0-indexed) is σ_{k+1} in HMT's notation (`integral_specNorm_residual_le_singularValues_of_gaussian`).
  This is correct but surprising, so put the translation in the docstring.
- `exists_eigenvalues_transpose_mul_mul_ge (hq : 0 < q) … (2/(1 + √(2ε/(1−ε))))^(q−1)` uses truncated
  subtraction. Write `K_{q+1}` and `^q`.

**2.5 Other statements.**
- `IsGMRESIterate.dotProduct_le_of_eq_mul_diagonal_mul {V W : Matrix n n ℝ} {d : n → ℝ} (hVW : V * W = 1) (hAd : A = V * diagonal d * W) …`
  (`Krylov/Solvers/GMRES.lean:281`, atlas `gmres-diagonalizable`) covers only *real*-diagonalizable `A`.
  The source theorem (Saad Prop. 6.32) is about complex eigenvalues, which is the nonnormal case people
  care about. Document this as weaker, or state it over `A.map (algebraMap ℝ ℂ)` as KRYLOV_DEFINITIONS §3.3 planned.
- Kaczmarz and CGLS take the smallest singular value as a quadratic hypothesis
  (`hσ : ∀ v, σ² * v ⬝ᵥ v ≤ (A v) ⬝ᵥ (A v)`, `Kaczmarz.expErr_le`, `Core.lean:205`). This is more general
  than the source, but a reader looks for σ_min. Add a corollary with `singularValues`.
- `integrable_and_integral_trace_sub_nystrom_le {F : Matrix (Fin r) (Fin n) ℝ} (hA : A = Fᵀ * F) (hkt) (Ω) (hΩ) : … ∫ tr(A − nystrom A Ω) ≤ (1 + k/(t−k−1)) * bestRankFrobSq k F`
  (`Nystrom/Structural.lean:191`). Tropp–Webber state the bound for `A ⪰ 0` with tail `∑_{j>k} λ_j(A)`,
  which is `spectralTraceTail A hA k`, already used by RPCholesky. Restate it that way.
- Bundles that carry atlas tags (STANDARDS: "two-sided bounds are two theorems"):
  - `aeval_mulVec_eq_and_charpoly_is_unique_minimiser` (`Krylov/Spectral/CharacteristicPolynomial.lean:133`)
    is a five-way conjunction with nested implications.
  - `hutchinson_of_rademacher` (mean ∧ variance, two ids; `Estimation/QuadraticForms/HutchinsonLaws.lean:124`).
  - `residual_sq_le_of_polynomial_filter` (spec ∧ Frobenius; `LowRank/PolynomialMethods/PolynomialFilter.lean:186`).
  - `complex_polynomial_filter_residual_bounds` (`ComplexPolynomialFilterBounds.lean:163`). Its first and
    third conjuncts print *identically* in the atlas (`‖·‖`), because the third uses an explicit
    `@norm _ (Matrix.frobeniusNormedAddCommGroup …)`. The rendered statement looks duplicated. Fix: split
    it, and use `specNorm`/`frobNorm`.
- Helpers tagged with headline ids:
  - `norm_mulVec_sq_bounds_of_zero_range` (`U : Matrix n (Fin 0) ℂ`, `leverage-sampling-ose`, `LeverageSampling.lean:262`).
  - `ae_power_and_lanczos_singleton_eq_zero_pi_gaussianReal (A : Matrix (Fin 1) (Fin 1) ℝ)` (`random-start-power`,
    `RandomStartEndpoints.lean:85`).
  - `isSubspaceEmbedding_of_forall_sqrt_le` (deterministic, tagged `gaussian-ose`).
  - Lanczos results tagged `random-start-power`.

  Fix: tag only the theorem a reader would cite.
- Recurrences: `isCGIterate_cgRecurrence (hA : A.PosDef) …` (`CGRecurrence.lean:343`) and
  `lanczosRecurrence_eq_arnoldiBasis` are `sorry`, so "CG computes the CG iterate" is still a scaffold.
  `isQR_pow_qrAlgorithm (h : QRAlgorithmSucceeds qr (fun _ => 0) A k) : IsQR (A^k) …` (`QRAlgorithm.lean:219`)
  covers only the unshifted algorithm, which is fine but should be stated as such.
- `jl_lemma … : gaussianMatrix k n {G | ∃ i j, i ≠ j ∧ |‖G̃(pᵢ−pⱼ)‖² − ‖pᵢ−pⱼ‖²| > ε‖pᵢ−pⱼ‖²} ≤ ENNReal.ofReal (N² · 2 · exp(−k(ε²/4 − ε³/6)))`
  (`Sketching/Properties/JL/JL.lean:153`). It counts ordered pairs (`N²`, not `N(N−1)/2`), is `ENNReal`,
  uses `>`, and has snake_case names (`jl_lemma`, `jl_distributional`, `jl_lemma_exists`).

## 3. Vocabulary inconsistencies

- **Orthonormality**: `HasOrthonormalCols` (real files) vs `U₁ᴴ * U₁ = 1`, `hU : Uᴴ * U = 1` (all `Complex*`
  LowRank files, leverage sampling). Orthogonal projectors appear as `(hPs : Pᵀ = P) (hPi : IsIdempotentElem P)`
  (`specNorm_mul_pow_le_specNorm_mul_gram_pow_mul`, `LowRank/Structural/PowerIteration.lean:97`). Range containment
  appears as `hK : krylovSpace … ≤ range Q` (Krylov) vs `hQ : Q * (Qᵀ * Y) = Y` (range finders) vs
  `complexColumnProjector Q * Y = Y` (ℂ). Fix: `HasOrthonormalCols`; `range Y ≤ range Q`; one projector name.
- **Norms**: `specNorm`/`frobNorm`/`frobSq` (real LowRank) vs `‖·‖` under the scoped L2 instance plus explicit
  Frobenius `@norm` (ℂ LowRank, AMM `integral_frobenius_sampled_mul_sub_sq`, `SamplingMultiplication.lean:165`)
  vs `‖WithLp.toLp 2 v‖²` (leverage) vs `v ⬝ᵥ v` (everywhere else). STANDARDS §3 allows `‖A‖` only in
  CFC/Probability files.
- **Rayleigh quotient**: NLAlib `rayleighQuotient` vs `(Matrix.toEuclideanCLM A).rayleighQuotient (WithLp.toLp 2 x)`
  in `powerRayleighRelativeError` (`RandomStartPower.lean:19`) and `lanczosRitzValue_eq_sSup` (`MeasurableRitz.lean:124`).
- **Angles**: `tanSqAngle u x` (Ritz.lean:216), `tanThetaMax Q X` (Matrix/Subspaces/PrincipalAngles),
  `subspaceTangent U₁ U₂ S`, `vectorTangentToFrame`, `complexSubspaceTangent`, `complexVectorTangentToColumns`.
  `sq_tanThetaMax_replicateCol_eq_tanSqAngle` is the only bridge, and it is `sorry`. Two convergence families
  both carry `subspace-iteration-convergence`: `tanThetaMax_le_of_range_eq_subspaceIterate` (`Krylov/Spectral/SubspaceIteration.lean:171`)
  and `subspaceTangent_subspaceIterate_le` (`LowRank/RangeFinding/SubspaceConvergence.lean:82`).
  Fix: `tanThetaMax` (principal angles) as the one notion, the vector case as `k = 1`, and one theorem family.
- **Tridiagonal/Hessenberg**: the predicates `IsUpperHessenberg`/`IsTridiagonal` (`Fin n` only, QR algorithm) vs raw
  `…_apply_eq_zero_of_add_one_lt` / `T_apply_eq_zero_of_one_lt_dist` (Arnoldi/Lanczos). Fix: generalise the
  predicates to `[LinearOrder n]` and state Arnoldi/Lanczos with them.
- **Tails**: six spellings (top-10 #9). There is also `filterTailMaxAbs s₂ p a b` with zero-padded `s₂ : ℕ → ℝ`.
- **Gaussian test vectors** (F2, noted only):
  - `IsStandardGaussian μ (z · i)` + `iIndepFun` (Estimation);
  - `μ.map (Matrix.of.symm ∘ Ω) = gaussianMatrix n t` (LowRank);
  - `μ.map G = Measure.pi (fun _ => gaussianReal 0 1)` (random start);
  - integration against `gaussianMatrix k n` directly (JL, Gaussian OSE);
  - `gaussianMatrix n 1` columns as a Gaussian vector (`variance_quadForm_gaussianMatrix_column`, `HutchinsonLaws.lean:204`).
- **ℝ vs ℂ vs 𝕜**:
  - Krylov is real by design (KRYLOV_DEFINITIONS §6.10).
  - Sketching is mixed: `IsSubspaceEmbedding` ℝ, leverage ℂ, AMM duplicated (`columnRowSample` ℂ-only at
    `SamplingMultiplication.lean:84`, `sampledColumnMatrix` over `RCLike` at `:90`, the integral theorem in an ℝ
    `frobSq` and a ℂ `‖·‖` copy).
  - LowRank is twinned: RPCholesky, volume sampling, polynomial filter and subspace convergence, with
    `complexBlockKrylovSpace` (`Krylov/Spaces/ComplexBlock.lean:21`) and `complexSubspaceIterate`
    (`ComplexSubspaceConvergence.lean:22`) redefining field-generic objects. This is already in the manifest;
    the oddity is that the twins differ in *shape* (finite sum vs `Measure` for volume sampling; `Fin m` vs
    `Fintype`), not just in field.
- **`Fin` vs `Fintype`**:
  - Krylov and Estimation are mostly `Fintype`.
  - `Fin` appears in QRAlgorithm (because of `IsUpperHessenberg`), real `VolumeSampling` (`Fin m`/`Fin n`
    with no Gaussian), `truncatedRsvdOutput` (no Gaussian), random start (`Fin (n+1)` plus `_all_dims`
    copies), SRHT, and Sparse (with `_fintype` transport copies).
  - STANDARDS §3: "a theorem stated over `Fin` because a dependency was, is a defect".
- **Snake_case paper names**: `rsvd_main`, `rsvd_truncated_main`, `gn_main`, `gn_main_of_completion`,
  `completion_reduction`, `error_decomp`, `Assembly.gn_explicit`, `jl_lemma`, `jl_distributional`,
  `hutchinson_of_rademacher`, `complex_polynomial_filter_residual_bounds`, `sparse_embedding_parameters`.
  Also `frobenius_norm_complex_…`. They break the §1 naming scheme that every neighbouring file follows.

## 4. Structural oddities

- **Two `Solvers`**: `Krylov/Solvers/` (CG, GMRES, PCG, CGLS, polynomial methods) and top-level `Solvers/`
  (Kaczmarz, sketch-and-project). The top-level one is layer 5 but imports only layer 0 (`Matrix.Norms.Core`,
  `Matrix.Basic.MoorePenrose`), and the sketched solvers that motivated layer 5 (sGMRES, sketch-and-precondition)
  do not exist. Fix: rename one (`Krylov/Methods/`, or `Iterative/` for row-action methods).
- **Not Krylov but under `Krylov/Spectral/`**: the QR algorithm, power method and inverse iteration. Fine
  historically, odd to a reader. Consider `Eigen/` or `Matrix/Spectral/Algorithms`.
  `Krylov/Spectral/MeasurableRitz.lean` exists only to serve `Estimation/Spectral` measurability.
- **Randomized Krylov placement** (STANDARDS §2 intends it): MM15-style block Krylov is in `LowRank/PolynomialMethods`
  (ℂ, `complexBlockKrylovSpace`), and random-start Lanczos is in `Estimation/Spectral`. Intentional. But
  the deterministic filter lemmas these need live in `Polynomial/Chebyshev/LanczosFilterMean.lean`, a
  layer-0 file named after Lanczos and tagged `random-start-power`. The manifest then makes it absorb
  `Growth` and `EvenChebyshevFilter`, so generic Chebyshev growth facts would end up in "LanczosFilterMean".
  Fix: target `Chebyshev/Growth`, move the filter-mean lemma next to its consumer, or rename the file.
- **Manifest merge targets a reader would not guess**: SLQ goes into `Estimation/Trace/Unbiased`,
  `SLQLipschitz` into `SLQPositiveLowerBound`, Analytic/Exponential quadrature into `Krylov/Quadrature/JacobiFraction`,
  `CharacteristicPolynomial` and `MeasurableRitz` into `Krylov/Spectral/SubspaceIteration`, and `SineBasis`
  into `SawtoothDerivative`. Rename the topic files after merging (`Quadrature/ErrorBounds`, `Estimation/SLQ`).
- **Helpers in the wrong place**: `Estimation/Trace/HutchinsonTail.lean` and `Krylov/Spectral/Ritz.lean` import
  `Krylov/Quadrature/GaussQuadrature` for Matrix-level Rayleigh/transpose helpers (already flagged in
  KRYLOV_DEFINITIONS §5). AMM has two homes, `Sketching/Properties/ApproxMatrixMultiplication` and
  `Sketching/Sampling/SamplingMultiplication`. There is no `import Mathlib` anywhere in the area.
- **Proof-named subtree**: `Polynomial/BestApproximation/` has eleven files (`Sawtooth*`, `SquareWave`,
  `SineBasis`, `JacksonPeriodic`, …) for one theorem, with public helper names. `Estimation/Spectral/RandomStartEndpoints.lean`
  is a file of `1 × 1` cases.
- **Frozen quarry (`Sketching/Sparse/{FiniteLaw,MomentMethod,IIDComparison,FockModel,Bands}`)**:
  - It is a separate probability universe. It has its own `SparseSketch.FiniteLaw`, not a `Measure`;
    its own sign type; `Frame n d`/`EVec b` on `Fin` instead of `HasOrthonormalCols`; and Fock-space and
    ladder-operator vocabulary (`TernaryJacobi`, `LadderWords`) that a numerical analyst will not connect
    to sketching.
  - It has parameter functions with opaque constants, where the headline theorems expose
    `sparseColumnSparsity (sparseMomentOrder d δ) ε` instead of hypotheses `s ≥ C log(d/δ)/ε`.
  - It has proof-step file names (`ExactCoordinateSymmetry`, `FillThinCoupling`) and docstrings that cite
    a commit hash.
  - `docs/SKETCH_INTERFACE.md` already gives the rebuild shape. The only addition here: the rebuilt
    headline should conclude the common OSE predicate of §2.1, with explicit `s, m` hypotheses.
