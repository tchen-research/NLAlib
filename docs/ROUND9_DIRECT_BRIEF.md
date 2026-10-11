# Round 9: a first course in numerical linear algebra, as factorizations and algorithms

Goal: the classical direct-method and eigenvalue-algorithm facts of Trefethen–Bau (`tb97`) and
Golub–Van Loan (`gvl13`), stated the NLAlib way: a factorization predicate, the algorithm as a
total recursion, and a theorem that the algorithm realises the predicate (and fails exactly
when it must). Also the first "algorithm realises the predicate" theorems for CG, Lanczos and
GMRES. Exact arithmetic only: finite precision is on hold (do not add rounding or backward-
stability material).

Read first: `docs/ALGORITHM_CONVENTIONS.md` (the contract for this round), `docs/STANDARDS.md`,
`CONTRIBUTING.md` §2–§3, `docs/ROUND1_BRIEF.md` (working rules), `docs/KRYLOV_DEFINITIONS.md` §6
and §3.11–3.12 for the Krylov groups, and the atlas entries for your ids
(`python3 -c "import json;[print(json.dumps(r,indent=1)) for r in json.load(open('atlas/atlas.json'))['results'] if r['id'] in {'lu-algorithm'}]"`).
The statement to prove is the entry's `informal`/`hypotheses`/`conclusion`; deviate only when
Lean forces it and say so in the docstring and the report.

## Policy for this round: state, don't necessarily prove

This round builds the *API*: definitions, recursions and precisely stated theorems, compiled and
documented, so that other people can prove them later. Rules:
- Every target in your group gets its definitions and its theorem statements, with the source
  and label and a short proof sketch in the docstring (what the induction is on, which Mathlib
  lemma does the step). A statement that does not elaborate does not count.
- Prove a theorem only when it is quick (routine, under about thirty minutes of effort); otherwise
  state it as a scaffold (`SCAFFOLD: <atlas id>` docstring, `sorry` body). A scaffold with a
  correct, well-documented statement is the expected outcome, not a failure. Do not spend the
  round on one hard proof.
- Get the statements right: check degenerate cases (`n = 0`, zero pivots, rank-deficient `A`),
  index types, and that the definition is the one the consumers want (see the atlas entry's
  `notes` and `depends_on`). Where two formulations are possible, pick the one in
  `docs/ALGORITHM_CONVENTIONS.md` and say in the docstring what the alternative would be.
- Definitions must be total and computable-looking (no `Classical.choose` in a recursion where a
  formula exists); success predicates are separate `Prop`s.
- Realisation theorems and breakdown theorems are the ones to state most carefully: they are the
  contract between the algorithm and the factorization predicate.

## Working rules (in addition to ROUND1_BRIEF)
- Exclusive file ownership per group; create the files named. Aggregators (`NLAlib/Matrix.lean`,
  `NLAlib/Krylov.lean`, `NLAlib/LowRank.lean`) are the coordinator's: list modules to add in your
  report. Build with `lake build NLAlib.<Module>`; never a full `lake build`; wait on Lake locks.
- Layer 0 files (`Matrix/**`) are imported by everything: additive changes only in existing
  files; new files are yours.
- Tags: the declaration that formalizes an atlas result ends its docstring with `atlas: <id>`
  (`(partial)` for partial coverage; comma-separated ids). Tag only existing ids; propose new
  ones in the report. Do not edit `atlas/atlas.json`. Helpers mention ids in prose only.
- Scaffolds (the norm this round): one named declaration per statement, `SCAFFOLD: <id>` as the
  first line of the docstring followed by the source, label and proof sketch, `sorry` body; never
  an inline `sorry`, never a scaffold you are not sure is true as written. A proved theorem may
  use scaffold lemmas. Entries marked "assume" in the atlas (`rank-revealing-qr`,
  `interpolative-decomposition`) are scaffolds by design if you reach them.
- Index conventions: recursions over `Fin n` with `Matrix.fromBlocks` / `Fin.cons` splitting;
  public statements for general `[Fintype n] [DecidableEq n]` where the statement does not need
  an order, with `reindex` bridges. Vectors `n → ℝ`, squared norms `v ⬝ᵥ v`, `HasOrthonormalCols`,
  `Matrix.BlockTriangular` (bridge lemma) for triangularity, Mathlib permutation matrices.
- Every file warning-free, ≤ 100 characters per line, STANDARDS naming, module docstring naming
  the atlas ids, docstring with source and label on every public declaration.
- Report per ROUND1_BRIEF: declarations with status and tags, exact check commands and output,
  renames (none expected), modules for the aggregators, proposed new atlas ids, helpers that belong
  elsewhere, and what you did not reach.

## Groups

**D-A — triangular factorizations** (new `Matrix/Factorizations/Triangular.lean`, `Matrix/Factorizations/LU.lean`,
`Matrix/Factorizations/Cholesky.lean`, `LowRank/PartialCholesky.lean`). Build `Triangular` first (D-B and D-D poll it).
1. `Triangular.lean` (`triangular-matrices-def`): `IsUpperTriangular`/`IsLowerTriangular`/unit forms on `Fin n`
   (bridge to `Matrix.BlockTriangular id`), closure under products and inverses, `det` = product of
   the diagonal, invertible iff diagonal nonzero, forward/back substitution as a recursion with
   `mulVec_substitution` realisation.
2. `LU.lean` (`lu-decomposition`, `lu-algorithm`, `lu-partial-pivoting`, `lu-growth-factor`): `IsLU`, the
   Schur-complement step, existence iff leading principal minors nonzero, uniqueness; `lu` recursion,
   `LUSucceeds`, `luSucceeds_iff_forall_det_ne_zero`, `isLU_lu`; `IsPLU`, partial-pivoting recursion
   never fails for invertible `A`, `|l_ij| ≤ 1`; growth factor `max|U| ≤ 2^{n-1} max|A|`.
3. `Cholesky.lean` (`cholesky-decomposition`, `cholesky-algorithm`): `IsCholesky`, existence and
   uniqueness for `PosDef` (via `Matrix.PosDef.fromBlocks₁₁`), `cholesky` recursion, `CholeskySucceeds`,
   `choleskySucceeds_iff_posDef` (symmetric `A`), `isCholesky_cholesky`; pivoted Cholesky on `PosSemidef`:
   never fails, terminates at the rank.
4. `LowRank/PartialCholesky.lean` (`partial-cholesky-nystrom`): `k` steps of pivoted Cholesky with pivot set `S`
   give `F Fᵀ = A(:,S) A(S,S)⁺ A(S,:)` and residual = Schur complement, PSD, zero on `S`. Uses
   `moorePenroseInverse` and `nystrom` from `LowRank/Nystrom.lean`.
5. If time remains: `generalized-schur-complement-psd` (Albert 1969) in a new `Matrix/SchurComplement.lean`.

**D-B — orthogonal factorizations** (new `Matrix/Factorizations/QR.lean`, `Matrix/Factorizations/GramSchmidt.lean`,
`Matrix/Factorizations/Householder.lean`, `Matrix/Factorizations/Givens.lean`, `Matrix/Factorizations/Hessenberg.lean`).
Poll `lake build NLAlib.Matrix.Factorizations.Triangular` (D-A step 1) for the triangular predicates; until then
use `Matrix.BlockTriangular id` directly.
1. `QR.lean` (`qr-decomposition`): `IsQR` (thin) and `IsFullQR`; existence for every `A` (from the
   full form or from `orthonormalBasisMatrix` of the column flag), uniqueness with positive diagonal
   under full column rank, `transpose_mul_eq`, `pinvL_eq_of_isQR` (`A⁺ = R⁻¹ Qᵀ`), thin from full.
2. `GramSchmidt.lean` (`gram-schmidt`): classical and modified Gram–Schmidt recursions on columns,
   breakdown iff a dependent column (`gramSchmidtSucceeds_iff_linearIndependent`), realisation
   `isQR_gramSchmidt`, and the fact that the output is the graded basis of the column flag (same
   shape as `IsGradedKrylovBasis`; do not import Krylov, state it with spans).
3. `Householder.lean` (`householder-reflector-def`, `householder-qr`): `householder v`, symmetric,
   orthogonal, involutive, `householder_mulVec_eq_smul_single` with the T&B sign; the recursion
   `householderQR` returning reflectors and `R`, realisation `isFullQR_householderQR` with no rank
   hypothesis, `Q` as the product of reflectors.
4. `Givens.lean` (`givens-rotation-def`): rotation matrices, zeroing an entry, QR of an upper
   Hessenberg matrix by `n-1` rotations, `RQ` again Hessenberg (tridiagonal when symmetric).
5. `Hessenberg.lean` (`hessenberg-reduction`): `IsHessenbergForm A Q H`, existence by Householder
   (`n-2` reflectors), symmetric ⇒ tridiagonal; implicit Q theorem if time remains (state it as:
   two Hessenberg forms with the same first column of `Q` and unreduced `H` differ by signs).

**D-C — least squares, conditioning, perturbation** (new `Matrix/LeastSquares.lean`,
`Matrix/Conditioning.lean`, `Matrix/InversePerturbation.lean`). Independent of the other groups
except step 1's QR corollary: poll `lake build NLAlib.Matrix.Factorizations.QR` for that one
lemma, state the rest without QR.
1. `LeastSquares.lean` (`least-squares-normal-equations`): minimiser iff normal equations iff
   residual ⟂ range, uniqueness iff full column rank, `x = A⁺ b` (`moorePenroseInverse`), residual
   identity, and via thin QR `x = R⁻¹ Qᵀ b` (the QR corollary).
2. `Conditioning.lean` (`condition-number-def`, `linear-system-perturbation`, `least-squares-perturbation`):
   `conditionNumber A := specNorm A * specNorm A⁺` (total), `conditionNumber_eq_div_sigmaMin` for
   invertible/full-rank `A`, the T&B Thm 12.1–12.2 bounds for `Ax = b` under perturbation of `b` and
   of `A` (explicit constants, hypothesis `κ ‖ΔA‖/‖A‖ < 1`), and T&B Thm 18.1 for least squares
   (sensitivity to `b` and `A` with the `κ, θ, η` constants; state each of the four bounds).
3. `InversePerturbation.lean` (`inverse-perturbation`, `pseudoinverse-perturbation`): Neumann series
   (`‖F‖ < 1 → (1 - F)⁻¹ = ∑ Fᵏ`, bounds), `‖(A+E)⁻¹ − A⁻¹‖ ≤ ‖A⁻¹‖² ‖E‖ / (1 − ‖A⁻¹‖‖E‖)`, Wedin's
   identity `B⁺ − A⁺ = −B⁺ E A⁺ + B⁺ B⁺ᵀ Eᵀ (I − A A⁺) + (I − B⁺ B) Eᵀ A⁺ᵀ A⁺`, and the spectral-norm
   bound with the constant stated in the atlas entry (scaffold the sharp constant if it will not
   close; the `3` constant is provable).

**D-D — eigenvalue algorithms** (new `Krylov/PowerMethod.lean`, `Krylov/QRAlgorithm.lean`,
`Matrix/PrincipalAngles.lean`, `Krylov/SubspaceIteration.lean`, `Matrix/Inertia.lean`,
`Krylov/Bidiagonalization.lean`). `Krylov/Block.lean`, `Krylov/Ritz.lean`, `Krylov/Arnoldi.lean` are read-only
for you (import them). Poll `lake build NLAlib.Matrix.Factorizations.QR` before step 3.
1. `PowerMethod.lean` (`power-iteration`, `inverse-iteration`): `powerIterate A x₀ k := A^k x₀`
   (normalisation is a lemma, not part of the definition), the `tanSqAngle` bound
   `(λ₂/λ₁)^{2k}` (symmetric `A`, `|λ₁| > |λ₂|`, `u₁ᵀx₀ ≠ 0`), the Rayleigh-quotient error bound
   via `Ritz.lean`'s `eigenvalues_sub_eigenvalues_le_mul_tanSqAngle`; inverse iteration as power
   iteration on the resolvent.
2. `PrincipalAngles.lean` (`principal-angles-def`): for `Q, Q'` with orthonormal columns, the
   `sin θ_max = ‖(I − Q Qᵀ) Q'‖` and `tan θ_max = ‖Q_⊥ᵀ Q' (Qᵀ Q')⁻¹‖` forms (define via these
   norms; the singular-value characterisation as a theorem if time remains), basis independence
   (`transpose_mul_mul_eq_of_range_le` from Block.lean), symmetry `θ(S,T) = θ(T,S)` for equal
   dimensions, `sin` and `tan` relation.
3. `SubspaceIteration.lean` (`subspace-iteration-convergence`): Saad Thm 5.2 in the symmetric case
   with the inputs K-D listed in round 8 (see the atlas notes): `tan θ_max(S_k, U_s) ≤ (λ_{s+1}/λ_s)^k tan θ_max(range Ω, U_s)`.
4. `QRAlgorithm.lean` (`qr-algorithm-simultaneous-iteration`): with `IsQR`-style hypotheses for the
   per-step factorizations (any choice), `A^k = Q^{(k)} R^{(k)}`, `A_k = Q^{(k)ᵀ} A Q^{(k)}`, shifted
   step is a similarity, Hessenberg and symmetric-tridiagonal structure preserved (needs `Givens.lean`
   from D-B for the structure lemma: poll `NLAlib.Matrix.Factorizations.Givens`, else prove the
   Hessenberg-preservation directly from `IsQR` and the triangular predicates).
5. If time remains: `Inertia.lean` (`sylvester-inertia`: congruence invariance of inertia, the
   `LDLᵀ` count) and `Bidiagonalization.lean` (`golub-kahan-bidiagonalization`).

**D-E — Krylov realisation theorems** (new `Krylov/CGRecurrence.lean`, `Krylov/LanczosRecurrence.lean`,
`Krylov/GMRESArnoldi.lean`; and `Krylov/PolynomialMethods.lean`, which you own this round). Read
`Krylov/CG.lean`, `Minimiser.lean`, `Arnoldi.lean`, `ArnoldiProcess.lean`, `Lanczos.lean`, `GMRES.lean`
first; they are read-only.
1. `CGRecurrence.lean` (`cg-recurrence`): a state `(x, r, p)` and `cgStep`; `cgRecurrence A c x₀ k`
   by `Nat.iterate`; the invariants `r_i ⬝ r_j = 0`, `p_i ⬝ A p_j = 0` for `i ≠ j`,
   `span (r_0..r_{k-1}) = span (p_0..p_{k-1}) = krylovSpace A r₀ k` while `r_k ≠ 0`, and the
   realisation `isCGIterate_cgRecurrence (hA : A.PosDef) : IsCGIterate A c x₀ k (cgRecurrence …).x`
   for `k ≤ krylovGrade A r₀`; after the grade the residual is zero (`x / 0 = 0` keeps the recursion
   total and constant).
2. `LanczosRecurrence.lean` (`lanczos-recurrence-algorithm`): the three-term recursion as a function
   `lanczosRecurrence A b : ℕ → (n → ℝ)` with `α, β`; for symmetric `A` it equals `arnoldiBasis A b j`
   for `j < krylovGrade A b` (positive `β`; K-B flagged the sign convention: verify it), `β` vanishes
   exactly at the grade, and the produced `α_j, β_j` are the `LanczosDecomp.alpha/beta` of the
   canonical decomposition.
3. `GMRESArnoldi.lean` (`gmres-arnoldi-form`): for `D : ArnoldiDecomp A r₀ (q+1)`,
   `IsGMRESIterate A c x₀ q (x₀ + D.Q_q *ᵥ y) ↔ y minimises ‖‖r₀‖ e₁ − H̲_q y‖` and the residual
   norm identity; FOM as the square system if time remains (`fom-def`, tag partial).
4. `PolynomialMethods.lean` (`chebyshev-iteration`, open clause): the three-term recurrence
   `chebyshevIterate_add_two` (Saad Alg. 12.1) for the existing `chebyshevIterate`.

## Report
Per ROUND1_BRIEF, plus: for every algorithm, the triple (recursion, success predicate, realisation
theorem) with names and whether each is proved or scaffolded; any place where the recursion had to
deviate from the textbook form; and for each scaffold a one-line difficulty estimate (1–5) for the
person who will prove it.
