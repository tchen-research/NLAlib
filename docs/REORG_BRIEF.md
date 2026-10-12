# Reorganisation round: mapping the tree

Read `docs/REORG_PLAN.md` first (why this is a move, not a rewrite). This round produces the
old-path → new-path table; a script then applies it. You do not move or edit any Lean file.

## Target tree (top level and subdirectories; files live only in leaf directories)
```
NLAlib/ForMathlib/            (unchanged: keep every file where it is)
NLAlib/Matrix/{Basic,Norms,Spectral,Subspaces,Factorizations,Perturbation,Inequalities,OperatorTheory,Functions,Structured}
NLAlib/Polynomial/{Chebyshev,Interpolation,BestApproximation,FunctionApproximation}
NLAlib/Probability/{Basic,Moments,Sampling,SubGaussian,Rademacher,ChiSquare}
NLAlib/Probability/Gaussian/{Basic,Calculus,Moments,Comparison,Concentration}
NLAlib/Probability/Concentration/{Basic,Scalar,Matrix,QuadraticForms,Entropy,Martingales}
NLAlib/RandomMatrix/{Basic,General,Spectral,SubGaussian,Rademacher,Haar,Covariance}
NLAlib/RandomMatrix/Gaussian/{Basic,Invariance,Moments,Spectral,Wishart,InverseMoments}
NLAlib/Krylov/{Spaces,Processes,Solvers,Spectral,Quadrature,MatrixFunctions}
NLAlib/Sketching/{Basic,Gaussian,Structured,Sparse,Sampling}
NLAlib/Sketching/Properties/{JL,SubspaceEmbedding,ApproxMatrixMultiplication}
NLAlib/LowRank/{Structural,RangeFinding,RandomizedSVD,Nystrom,Cholesky,PolynomialMethods,Sampling}
NLAlib/Estimation/{Basic,Trace,Diagonal,QuadraticForms,Quadrature}
NLAlib/Solvers/{Kaczmarz,SketchAndSolve,SketchAndProject,Preconditioning}
```
Layers (a file may import only its own top-level directory or a lower layer):
ForMathlib −1 · Matrix 0 · Polynomial 0 · Probability 1 · Krylov 1 · RandomMatrix 2 · Sketching 3 ·
LowRank 4 · Estimation 4 · Solvers 5. A file you place in `Matrix/` must import nothing from
Probability/Concentration/Gaussian (check its `import` lines; a Borel instance or a measure-theory
import disqualifies it from `Matrix/` unless the import is `ForMathlib`). The script rejects a table
that creates a cycle or a layer violation, so check imports before assigning.

## Rules
1. Every file in your group is mapped exactly once, to a path inside a leaf directory of the tree
   above. `NLAlib/<Dir>.lean` and `NLAlib/<Dir>/<Sub>.lean` are reserved for generated aggregators:
   never map a content file there (today's `Matrix/Norms.lean` becomes e.g. `Matrix/Norms/Basic.lean`).
2. Keep the file's base name unless (a) two files would collide in the same new directory or (b) the
   name is misleading in its new home; record every rename in `renames`. Prefer short
   `UpperCamelCase` names; `Basic.lean` in a leaf holds that leaf's definitions.
3. A subdirectory with one file is fine; an empty target subdirectory is fine (leave it out); a file
   that fits no listed subdirectory goes to the closest one and is listed in `flags` with a sentence,
   or, if a new subdirectory is clearly warranted, propose it in `flags` (do not invent silently).
4. Decide from the module docstring, the declarations and the imports, not from the file name
   alone (`sed -n 1,40p` each file; `grep -n "^theorem\|^def\|^structure" file | head`). Large
   self-contained subtrees move wholesale (say so in `notes`).
5. Mixed files (two topics in one file) are mapped to their dominant topic and listed in `flags`
   as a later split; do not propose content edits.
6. You may fan out to subagents by subdirectory (each writing a partial JSON you merge); you own
   the final file. Do not edit anything outside `docs/reorg/mapping/`.

## Output: `docs/reorg/mapping/<group>.json`
```json
{"group": "M1", "moves": {"NLAlib/Matrix/Norms.lean": "NLAlib/Matrix/Norms/Basic.lean", "...": "..."},
 "renames": {"NLAlib/Matrix/Old.lean": "reason"}, "notes": ["Factorizations/ moved wholesale", "..."],
 "flags": ["NLAlib/Matrix/GramSoftMin.lean: mixes ... ; placed in Structured; split later", "..."]}
```
Validate: `python3 scripts/reorg.py --check docs/reorg/mapping/<group>.json` (checks that every file
of your group is mapped once, destinations are leaves of the tree, no collisions; the cross-group
layer and cycle check runs when all tables are in). Final message: counts per destination
directory, the flags, and anything you think the target tree is missing.

## Groups
- **M1 — Matrix** (`NLAlib/Matrix/**`, 93 files incl. `Factorizations/`): Basic (definitions and
  foundational identities: Norms? no, Norms has its own), Norms, Spectral (eigen/SVD/Courant–
  Fischer/Weyl), Subspaces (projections, orthonormal columns, principal angles, Stiefel, polar
  frame), Factorizations (as today + Schur complement? no: Schur complement → Inequalities or
  Basic, decide), Perturbation (inverse perturbation, conditioning, least squares perturbation,
  Davis–Kahan material), Inequalities (von Neumann, trace inequalities, Loewner order facts),
  OperatorTheory (operator monotone/convex, Lieb; today in Concentration/Matrix/OperatorConvexity:
  M2 maps those, coordinate by reading them but do not map them yourself), Functions (matrix
  functions via CFC, polynomial calculus), Structured (Gram soft-min / inverse-power / cutoff
  calculus family from codex, measurability files if they are matrix-only).
- **M2 — Concentration** (`NLAlib/Concentration/**`, 118 files): Scalar → Probability/Concentration/Scalar
  or Probability/{SubGaussian,Rademacher}; HansonWright → Probability/Concentration/QuadraticForms;
  EntropyTensorization/Herbst/EntropyNonnegative → Probability/Concentration/Entropy; Matrix/Defs
  with probability content → Probability/Concentration/Basic, Matrix/Defs/{Spectral,Dilation,
  Calculus,RelativeEntropy,IntrinsicDimension} and Matrix/OperatorConvexity → Matrix/OperatorTheory
  or Matrix/Functions **only if their imports allow layer 0** (else Probability/Concentration/Matrix);
  Matrix/{Laplace,Chernoff,Bernstein,Intrinsic,Series,Sampling*} → Probability/Concentration/Matrix;
  Matrix/Martingale → Probability/Concentration/Martingales; McDiarmid → Scalar.
- **M3 — Gaussian** (`NLAlib/Gaussian/**`, 76 files): scalar/vector facts (Comparison, Concentration,
  log-Sobolev, Ornstein–Uhlenbeck, Stein, Isserlis, Wick, Khintchine, series moments, ChiSquare,
  integration by parts) → Probability/Gaussian/{Basic,Calculus,Moments,Comparison,Concentration} or
  Probability/ChiSquare; anything mentioning `gaussianMatrix` → RandomMatrix/Gaussian/{Basic,
  Invariance,Moments,Spectral,Wishart,InverseMoments}; Haar frame → RandomMatrix/Haar.
- **M4 — Sketching** (`NLAlib/Sketching/**`, 143 files): `SparseFock/**` → `Sketching/Sparse/`
  wholesale (keep its internal structure under `Sparse/SparseFock/…` or flatten: decide, say why);
  JL → Properties/JL; subspace embedding files → Properties/SubspaceEmbedding; AMM → Properties/
  ApproxMatrixMultiplication; Gaussian embeddings → Gaussian; SRHT/structured → Structured;
  leverage/sampling → Sampling; SubGaussianRows/SubGaussianJL: decide between Properties/JL and
  RandomMatrix/SubGaussian (a random-matrix *model* goes to RandomMatrix; a sketch *guarantee* stays).
- **M5 — Krylov, Polynomial, ForMathlib** (31 + 28 + 47 files): Krylov/{Spaces (Basic, Polynomial,
  Grade, Block), Processes (Arnoldi*, Lanczos*, Minimiser?, recurrences), Solvers (CG*, GMRES*,
  Preconditioned, PolynomialMethods), Spectral (Ritz, PowerMethod, SubspaceIteration, QRAlgorithm,
  Bidiagonalization), Quadrature (SpectralMeasure, GaussQuadrature, Jacobi*), MatrixFunctions
  (FunctionApprox)}; Polynomial/{Chebyshev (Basic? Chebyshev, Minimax, Markov, aliasing…),
  Interpolation, BestApproximation (Minimax, equioscillation…), FunctionApproximation
  (Approximation: 1/x, exp, sign…)}; ForMathlib: identity map (list every file to itself).
- **M6 — LowRank, Estimation, Solvers** (40 + 11 + 6 files): LowRank/{Structural (deterministic
  range-finder bounds, Eckart–Young consumers), RangeFinding (HMT range finder, power iteration),
  RandomizedSVD (RSVD, tRSVD, assembly, optimal error), Nystrom (Nyström, GN, raw GN), Cholesky
  (PartialCholesky), PolynomialMethods (block Krylov LRA, polynomial filters), Sampling (volume /
  leverage sampling LRA)}; Estimation/{Basic (defs), Trace (Hutchinson*, Hutch++), Diagonal,
  QuadraticForms (variance/tails of quadratic forms), Quadrature (SLQ)}; Solvers/{Kaczmarz,
  SketchAndSolve, SketchAndProject, Preconditioning}.
