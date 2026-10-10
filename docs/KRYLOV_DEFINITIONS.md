# How to define Krylov methods in NLAlib

Recommendation, 2026-10-10. This answers "how should Krylov algorithms be defined in Lean?" for
`NLAlib/Krylov` (layer 1) and its consumers in `LowRank`, `Estimation`, `Solvers`. Signatures below
are sketches. Check every Mathlib name before you rely on it.

**Short answer.** A Krylov *method* is defined by the condition that pins down its iterate: a
minimisation or Petrov–Galerkin predicate over a subspace, or an explicit polynomial. It is not
defined by the recurrence that computes it. A Krylov *process* (Arnoldi, Lanczos, Golub–Kahan) is
one noncomputable object, a Gram–Schmidt basis indexed by `ℕ`, whose decomposition identity holds
with no hypotheses. The recurrence is a second definition with a theorem saying it realises the
first. Breakdown is handled by the *grade* of the Krylov sequence. Downstream theorems never take
a specific basis; they take "`Q` has orthonormal columns and `K ≤ range Q`".

## 1. What exists, and what is awkward

What already works well (keep these patterns):

* `krylovSpace A b q : Submodule ℝ (n → ℝ)` is basis-free and has no degenerate cases.
  `mem_krylovSpace_iff_degree` (`deg p < q`, valid at `q = 0`) is the right primary
  characterisation.
* `IsCGIterate` works as a predicate plus a separate existence theorem (`exists_isCGIterate`).
  The Galerkin-to-minimality bridge is a separate theorem
  (`isCGIterate_of_forall_dotProduct_eq_zero`). Non-uniqueness never comes up, because every
  theorem quantifies over *all* iterates.
* The polynomial bound is **universally quantified over `p`**:
  `quadForm_sub_le_of_isCGIterate_of_poly` takes any `p` with `p.degree ≤ q` and `p.eval 0 = 1`.
  Plugging in `chebyshevResidual` is then three lines. Consumers can supply `1 − X/a`, products,
  and so on.
* **Basis-agnostic interfaces.** `dotProduct_aeval_mulVec_eq_of_krylovSpace_le`,
  `abs_dotProduct_cfc_mulVec_sub_le_of_krylovSpace_le`, `exists_eigenvalues_transpose_mul_mul_ge`
  and `slqEstimate` all take any `Q` with `HasOrthonormalCols Q` and
  `krylovSpace A b q ≤ LinearMap.range Q.mulVecLin`. This is why SLQ came almost for free. It is
  also exactly the form that Musco–Musco and sketched Rayleigh–Ritz arguments need.

What is awkward:

1. **`lanczosBasis` is the Arnoldi basis.** It is Gram–Schmidt of `A^i b` for *any* `A`, and the
   Hessenberg theorem holds for every `A`. Its name and `lanczos_apply_eq_zero_of_add_one_lt`
   mislead GMRES and FOM users. The primed `…'` variant does not spell its hypothesis (`IsSymm`).
2. **`Fin q` indexing inside the definition.** `lanczosBasis A b q : Fin q → _` is a *different*
   Gram–Schmidt run for each `q`. Nothing says that column `i` of `Q_{q+1}` equals column `i` of
   `Q_q`. As a result the Arnoldi relation `A Q_q = Q_{q+1} H̲_q`, which needs both `Q_q` and
   `Q_{q+1}`, cannot even be stated cleanly. This is why `lanczos-recurrence` is still a candidate.
3. **Breakdown hypothesis.** The hypothesis is
   `LinearIndependent ℝ fun i : Fin q => (A ^ (i : ℕ)) *ᵥ b`. Nothing relates it to
   `finrank (krylovSpace A b q)`, and nothing gives a uniform recipe for `q` past the grade.
   There is no notion of grade or invariance (`A K_d ⊆ K_d`), so finite termination
   (`x⋆ ∈ x₀ + K_d`) cannot be stated.
4. **Three degree conventions.** Krylov uses `degree < q`, CG `degree ≤ q`, and Gauss quadrature
   `natDegree ≤ 2 * q - 1`. The truncated subtraction in the last forces `0 < q` side conditions
   (see the deviation note in `dotProduct_aeval_mulVec_eq_of_krylovSpace_le`).
5. **Duplicated residual-polynomial algebra.** `X ∣ 1 − p` with `deg s < q` is a private lemma in
   `CG.lean` (`exists_degree_lt_one_sub_eq_X_mul`), and the same proof is inlined in
   `exists_degree_lt_abs_eval_sub_inv_le`. Every residual-polynomial method needs it.
6. **The CG objective is baked in.** The generic step ("a minimiser over `x₀ + K_q` beats every
   residual polynomial") is buried in the CG proof. GMRES, MINRES, LSQR and sketched GMRES would
   each have to redo it.
7. **Vector norms.** On `n → ℝ`, `‖·‖` is the sup norm. Statements must use `v ⬝ᵥ v` or
   `quadForm`, which the current files already do. Mathlib's `starProjection` and
   `OrthonormalBasis` need `EuclideanSpace`, so they stay internal, as `krylovVectors` already
   does.

## 2. Options weighed

| Option | Good for | Cost / risk | Verdict |
|---|---|---|---|
| (a) variational predicate `x − x₀ ∈ S ∧ ∀ y ∈ S, E x ≤ E (x₀ + y)` | CG, GMRES, MINRES, LSQR/CGLS, sGMRES; theorems are stated once for a class | existence is a separate theorem; says nothing about how the iterate is computed | **primary** for minimising methods |
| (b) Petrov–Galerkin `x − x₀ ∈ K ∧ ∀ z ∈ L, z ⬝ᵥ r = 0` | FOM, BiCG, Galerkin CG, Rayleigh–Ritz | iterate may not exist or may not be unique (that *is* breakdown) | **primary** for projection methods |
| (c1) pinned polynomial `x = x₀ + s(A) r₀`, `s` given | Chebyshev iteration, Richardson, Lanczos-FA exactness | none: an honest `def` | **primary** for polynomial (non-adaptive) methods |
| (c2) `∃ p` with a bound | approximation-theory side (`exists_degree_lt_abs_eval_sub_inv_le`) | too weak on the *method* side | method bounds take `∀ p`; existence lives in `Polynomial/` |
| (d) explicit recurrence (`Nat.rec`, step function) | the algorithm as written; finite-precision models | proofs by induction with case splits; ℝ is noncomputable anyway | **secondary**: a `def` plus a "realises (a)/(b)/(c)" theorem |
| (e) basis-free: subspace plus projector, basis as a separate layer | Gauss quadrature, Ritz, SLQ, block Krylov, sketched RR | needs an orthonormal-basis matrix for an arbitrary subspace | **interface** for every downstream theorem |
| (f) Mathlib carriers | `Submodule.span`, `aeval`, `cfc`, `gramSchmidtNormed`, `minpoly`, `IsMinOn`, `AffineSubspace.mk'` | `starProjection`/`OrthonormalBasis` need `EuclideanSpace`; `Module.AEval'` cyclic submodules are elegant but hard to use | use internally; public statements stay in `Matrix`/`n → ℝ` vocabulary |

Recurrence-as-definition (d) is tempting for "algorithms whose definition is the recurrence".
But in exact arithmetic every method in scope has a recurrence-free characterisation. Downstream
randomized-NLA proofs (MM15, SLQ, Krylov-aware trace estimation, Nakatsukasa–Tropp) use only that
characterisation. The recurrence matters for (i) the realisation theorem and (ii) finite
precision, and finite precision is better modelled by *perturbed decomposition hypotheses* (§3.8)
than by executing a recurrence.

## 3. Layered architecture

```
K0  spaces       krylovSpace, krylovGrade, blockKrylovSpace          (Krylov/Basic, Krylov/Polynomial, Krylov/Grade, Krylov/Block)
K1  transfer     residual polynomials; minimiser-beats-every-polynomial (Krylov/Minimiser)
K2  methods      IsAffineMinimiser, IsPetrovGalerkinIterate, polyIterate and their instances
K3  processes    arnoldiBasis : ℕ → n → ℝ, arnoldiMatrix, arnoldiHessenberg; Arnoldi relation; Lanczos = symmetric case
K4  realisation  recurrences (CG/Hestenes–Stiefel, Lanczos three-term, Chebyshev semi-iteration) = K2/K3 objects
K5  inexact      IsPerturbedArnoldi-style hypotheses (AQ = QH + f eᵀ + F); no rounding model
```

Each method theorem composes K2 → K1 (optimality gives `∀ p`), then a spectral bound
(`Matrix/PolynomialCalculus`), then a concrete polynomial from `Polynomial/`.

### 3.1 Spaces, grade, uniform breakdown (K0)

```lean
/-- The grade of `b` w.r.t. `A`: `dim span {Aⁱ b : i ∈ ℕ}` (degree of the minimal polynomial of b). -/
def krylovGrade (A : Matrix n n ℝ) (b : n → ℝ) : ℕ :=
  Module.finrank ℝ (Submodule.span ℝ (Set.range fun i : ℕ => (A ^ i) *ᵥ b))
theorem finrank_krylovSpace (A b q) : Module.finrank ℝ (krylovSpace A b q) = min q (krylovGrade A b)
theorem krylovSpace_eq_of_krylovGrade_le (h : krylovGrade A b ≤ q) :
    krylovSpace A b q = krylovSpace A b (krylovGrade A b)
theorem linearIndependent_pow_mulVec_iff_le_krylovGrade :
    LinearIndependent ℝ (fun i : Fin q => (A ^ (i : ℕ)) *ᵥ b) ↔ q ≤ krylovGrade A b
theorem mulVec_mem_krylovSpace_krylovGrade (hx : x ∈ krylovSpace A b (krylovGrade A b)) :
    A *ᵥ x ∈ krylovSpace A b (krylovGrade A b)                       -- invariance
theorem krylovGrade_le_natDegree_minpoly : krylovGrade A b ≤ (minpoly ℝ A).natDegree
theorem sub_mem_krylovSpace_krylovGrade (hA : IsUnit A) (hxs : A *ᵥ xs = c) :
    xs - x₀ ∈ krylovSpace A (c - A *ᵥ x₀) (krylovGrade A (c - A *ᵥ x₀))  -- finite termination
```

The uniform rule: **statements about spaces carry no breakdown hypothesis.** Statements that need
an orthonormal basis use `q ≤ krylovGrade A b`. Alternatively they replace `q` by
`min q (krylovGrade A b)`, which gives the same space by the lemma above. Theorems with a
`LinearIndependent …` hypothesis keep it but gain an `_of_le_krylovGrade` corollary. For Gaussian
starting vectors the a.s. statement "`krylovGrade A g` = number of distinct eigenvalues" belongs in
`Gaussian/` (layer 2) and plugs straight in.

Block Krylov (MM15, randomized block Krylov, block Lanczos):

```lean
def blockKrylovSpace (A : Matrix n n ℝ) {s : Type*} [Fintype s] (Ω : Matrix n s ℝ) (q : ℕ) :
    Submodule ℝ (n → ℝ) :=
  Submodule.span ℝ (Set.range fun ij : Fin q × s => ((A ^ (ij.1 : ℕ)) * Ω).col ij.2)
theorem blockKrylovSpace_eq_iSup : blockKrylovSpace A Ω q = ⨆ j, krylovSpace A (Ω.col j) q
theorem mem_blockKrylovSpace_iff : x ∈ blockKrylovSpace A Ω q ↔
    ∃ p : s → ℝ[X], (∀ j, (p j).degree < q) ∧ x = ∑ j, aeval A (p j) *ᵥ Ω.col j
theorem range_aeval_mul_le_blockKrylovSpace {p : ℝ[X]} (hp : p.degree < q) :
    LinearMap.range (aeval A p * Ω).mulVecLin ≤ blockKrylovSpace A Ω q   -- what MM15 uses
theorem finrank_blockKrylovSpace_le : Module.finrank ℝ (blockKrylovSpace A Ω q) ≤ q * Fintype.card s
```

MM15's space `[AΩ, (AAᵀ)AΩ, …]` is `blockKrylovSpace (A * Aᵀ) (A * Ω) (q + 1)`. No rectangular
variant is needed. `range_aeval_mul_le_blockKrylovSpace` plus the existing
`power-iteration-deterministic` with `p(AAᵀ)A` in place of `(AAᵀ)^q A` is the whole deterministic
half of block-Krylov LRA.

Basis interface (Matrix layer, `Matrix/Projections`). Add one canonical orthonormal-basis matrix
for an arbitrary subspace, built internally from `stdOrthonormalBasis` on `EuclideanSpace`:

```lean
def orthonormalBasisMatrix (S : Submodule ℝ (m → ℝ)) : Matrix m (Fin (Module.finrank ℝ S)) ℝ
theorem hasOrthonormalCols_orthonormalBasisMatrix (S) : HasOrthonormalCols (orthonormalBasisMatrix S)
theorem range_orthonormalBasisMatrix (S) : LinearMap.range (orthonormalBasisMatrix S).mulVecLin = S
```

This gives every Krylov space (single or block) an orthonormal basis with *no hypothesis*, so
results like `ritz-value-bounds` or Lanczos-FA can be instantiated unconditionally. The Arnoldi
basis (§3.5) is a *particular* orthonormal basis with extra structure. It is not the interface.

### 3.2 The generic minimiser and the class theorem (K1–K2)

```lean
/-- `x` minimises `E` over the affine space `x₀ + S`. -/
def IsAffineMinimiser (E : (n → ℝ) → ℝ) (x₀ : n → ℝ) (S : Submodule ℝ (n → ℝ)) (x : n → ℝ) : Prop :=
  x - x₀ ∈ S ∧ ∀ y ∈ S, E x ≤ E (x₀ + y)
theorem isAffineMinimiser_iff_isMinOn :
    IsAffineMinimiser E x₀ S x ↔ x ∈ AffineSubspace.mk' x₀ S ∧ IsMinOn E (AffineSubspace.mk' x₀ S) x
/-- Residual-polynomial algebra (promote the private CG lemma; Polynomial/Basic). -/
theorem exists_degree_lt_eq_X_mul_of_eval_zero {p : ℝ[X]} (hp : p.degree ≤ q) (hp0 : p.eval 0 = 1) :
    ∃ s : ℝ[X], s.degree < q ∧ 1 - p = X * s
/-- K1: a Krylov minimiser beats every residual polynomial. No spectral hypothesis, any `E`. -/
theorem IsAffineMinimiser.le_aeval {E} (hx : IsAffineMinimiser E x₀ (krylovSpace A (c - A *ᵥ x₀) q) x)
    (hxs : A *ᵥ xs = c) {p : ℝ[X]} (hp : p.degree ≤ q) (hp0 : p.eval 0 = 1) :
    E x ≤ E (xs + aeval A p *ᵥ (x₀ - xs))
/-- The class theorem: weighted-norm minimisers, symmetric `A`, weight `g(A)`, `g ≥ 0` on the spectrum.
CG: `g = X` (via `cgObjective_eq_add_quadForm_sub`); MINRES: `g = X²`; error-minimising: `g = 1`. -/
theorem quadForm_sub_le_of_isAffineMinimiser {A : Matrix n n ℝ} (hA : A.IsHermitian) {g : ℝ[X]}
    (hg : ∀ i, 0 ≤ g.eval (hA.eigenvalues i)) (hxs : A *ᵥ xs = c)
    (hx : IsAffineMinimiser (fun y => quadForm (aeval A g) (y - xs)) x₀ (krylovSpace A (c - A *ᵥ x₀) q) x)
    {p : ℝ[X]} (hp : p.degree ≤ q) (hp0 : p.eval 0 = 1) {M : ℝ} (hM : ∀ i, |p.eval (hA.eigenvalues i)| ≤ M) :
    quadForm (aeval A g) (x - xs) ≤ M ^ 2 * quadForm (aeval A g) (x₀ - xs)
```

The spectral step is `quadForm_aeval_mulVec_le` generalised from weight `A` to weight `aeval A g`.
`IsCGIterate` becomes `IsAffineMinimiser (cgObjective A c) x₀ (krylovSpace A (c - A *ᵥ x₀) q)`
by `Iff.rfl`: keep the name and redefine the body. `quadForm_sub_le_of_isCGIterate_of_poly` then
becomes a two-line corollary.

### 3.3 Minimising methods: GMRES, MINRES, LSQR, sketched GMRES

```lean
def IsGMRESIterate (A : Matrix n n ℝ) (c x₀ : n → ℝ) (q : ℕ) (x : n → ℝ) : Prop :=
  IsAffineMinimiser (fun y => (c - A *ᵥ y) ⬝ᵥ (c - A *ᵥ y)) x₀ (krylovSpace A (c - A *ᵥ x₀) q) x
theorem exists_isGMRESIterate (A c x₀ q) : ∃ x, IsGMRESIterate A c x₀ q x   -- any A: least squares
theorem IsGMRESIterate.exists_residual_eq (hx : IsGMRESIterate A c x₀ q x) :
    ∃ p : ℝ[X], p.degree ≤ q ∧ p.eval 0 = 1 ∧ c - A *ᵥ x = aeval A p *ᵥ (c - A *ᵥ x₀)
theorem IsGMRESIterate.residual_le (hx : IsGMRESIterate A c x₀ q x) {p} (hp : p.degree ≤ q) (hp0 : p.eval 0 = 1) :
    (c - A *ᵥ x) ⬝ᵥ (c - A *ᵥ x) ≤ (aeval A p *ᵥ (c - A *ᵥ x₀)) ⬝ᵥ (aeval A p *ᵥ (c - A *ᵥ x₀))
theorem isGMRESIterate_iff_isPetrovGalerkinIterate :   -- r ⟂ A K_q
    IsGMRESIterate A c x₀ q x ↔ IsPetrovGalerkinIterate A c x₀ K ((krylovSpace A r₀ q).map A.mulVecLin) x
```

* GMRES is stated residual-wise, so it needs no solution `xs` and covers singular or inconsistent
  `A`. The spectral corollaries are: `specNorm (aeval A p)` for any `A`; `max |p(λᵢ)|` for
  symmetric `A` (`dotProduct_aeval_mulVec_self_le`); and `κ(V) max |p(λᵢ)|` from a complex
  diagonalisation `A.map (algebraMap ℝ ℂ) = V D V⁻¹`, taken as a hypothesis. That last one, like
  Crouzeix–Palencia and Elman, is where **complex scalars** enter. It is assumed, not built.
* **MINRES** is GMRES for symmetric `A` (same iterate in exact arithmetic). Do not add a second
  predicate. MINRES theorems are `IsGMRESIterate` theorems with `hA : A.IsHermitian`, and they
  equal `quadForm_sub_le_of_isAffineMinimiser` with `g = X²` when `A` is nonsingular. The
  indefinite two-interval bound needs a new polynomial (§4).
* **LSQR/CGLS** (rectangular `A : Matrix m n ℝ`):
  `IsAffineMinimiser (fun y => (b - A *ᵥ y) ⬝ᵥ (b - A *ᵥ y)) x₀ (krylovSpace (Aᵀ * A) (Aᵀ *ᵥ (b - A *ᵥ x₀)) q)`,
  with `iff` to `IsCGIterate (Aᵀ * A) (Aᵀ *ᵥ b) x₀ q`. LSMR changes the objective to
  `‖Aᵀ(b − Ay)‖²`. Golub–Kahan bidiagonalisation is K3, a theorem about
  `arnoldiBasis (Aᵀ * A) (Aᵀ *ᵥ b)` and `arnoldiBasis (A * Aᵀ) b`.
* **Sketched GMRES** (Nakatsukasa–Tropp) is `IsAffineMinimiser (fun y => (S *ᵥ (c - A *ᵥ y)) ⬝ᵥ (S *ᵥ (c - A *ᵥ y))) x₀ (range B)`
  with `B` *any* basis of (a subspace of) `K_q`. This is why `S` in `IsAffineMinimiser` is an
  arbitrary `Submodule`. The comparison with GMRES needs an `IsSubspaceEmbedding` for
  `span(r₀, A·range B)` and lives in `Solvers`.

### 3.4 Projection methods: FOM, BiCG, Rayleigh–Ritz

```lean
def IsPetrovGalerkinIterate (A : Matrix n n ℝ) (c x₀ : n → ℝ) (K L : Submodule ℝ (n → ℝ)) (x : n → ℝ) : Prop :=
  x - x₀ ∈ K ∧ ∀ z ∈ L, z ⬝ᵥ (c - A *ᵥ x) = 0
def IsFOMIterate (A c x₀ q x) : Prop := IsPetrovGalerkinIterate A c x₀ K K x  -- K = krylovSpace A (c - A *ᵥ x₀) q
def IsBiCGIterate (A c x₀) (w : n → ℝ) (q x) : Prop :=
  IsPetrovGalerkinIterate A c x₀ (krylovSpace A (c - A *ᵥ x₀) q) (krylovSpace Aᵀ w q) x
theorem isCGIterate_iff_isFOMIterate (hA : A.PosDef) : IsCGIterate A c x₀ q x ↔ IsFOMIterate A c x₀ q x
theorem existsUnique_isFOMIterate_iff (hq : q ≤ krylovGrade A r₀) :
    (∃! x, IsFOMIterate A c x₀ q x) ↔ IsUnit (arnoldiHessenberg A r₀ q)
```

Breakdown of FOM and BiCG is **non-existence of a predicate solution**. Theorems are "for every
`x` with `IsFOMIterate …`". Existence and uniqueness are separate iff statements: an `H_q`
nonsingularity condition for FOM, and nonsingular leading moment matrices `Wᵀ V` for BiCG and
two-sided Lanczos. Never pick an iterate with `Classical.choose` unless uniqueness is proved.

Ritz values keep the existing form (eigenvalues of `Qᵀ A Q`, `K ≤ range Q`).

### 3.5 Processes: Arnoldi and Lanczos (K3)

Refactor the basis to be indexed by `ℕ` and defined once:

```lean
/-- Gram–Schmidt of `b, Ab, A²b, …` (Mathlib `gramSchmidtNormed` over `ℕ`); zero after breakdown. -/
def arnoldiBasis (A : Matrix n n ℝ) (b : n → ℝ) (j : ℕ) : n → ℝ :=
  (gramSchmidtNormed ℝ (fun i : ℕ => WithLp.toLp 2 ((A ^ i) *ᵥ b)) j).ofLp
def arnoldiMatrix (A b) (q : ℕ) : Matrix n (Fin q) ℝ := Matrix.of fun r j => arnoldiBasis A b j r
def arnoldiHessenberg (A b) (q : ℕ) : Matrix (Fin q) (Fin q) ℝ := (arnoldiMatrix A b q)ᵀ * A * arnoldiMatrix A b q
/-- Column form, no hypotheses (after breakdown both sides are 0). -/
theorem mulVec_arnoldiBasis (A b) (j : ℕ) :
    A *ᵥ arnoldiBasis A b j = ∑ i ∈ Finset.range (j + 2),
      (arnoldiBasis A b i ⬝ᵥ (A *ᵥ arnoldiBasis A b j)) • arnoldiBasis A b i
/-- Arnoldi relation `A Q_q = Q_{q+1} H̲_q`, no hypotheses. -/
theorem mul_arnoldiMatrix (A b q) : A * arnoldiMatrix A b q =
    arnoldiMatrix A b (q + 1) * ((arnoldiMatrix A b (q + 1))ᵀ * A * arnoldiMatrix A b q)
theorem arnoldiMatrix_mul_transpose (A b q) :          -- QQᵀ is the projector onto K_q, no hypotheses
    arnoldiMatrix A b q * (arnoldiMatrix A b q)ᵀ = orthonormalBasisMatrix K * (orthonormalBasisMatrix K)ᵀ
theorem hasOrthonormalCols_arnoldiMatrix (h : q ≤ krylovGrade A b) : HasOrthonormalCols (arnoldiMatrix A b q)
theorem arnoldiHessenberg_apply_eq_zero_of_add_one_lt (hij : (j : ℕ) + 1 < i) : arnoldiHessenberg A b q i j = 0
theorem arnoldiHessenberg_isSymm (hA : A.IsSymm) : (arnoldiHessenberg A b q).IsSymm   -- Lanczos: tridiagonal
```

With ℕ indexing, column `j` is the same vector for every `q`, so `Q_q` is literally the first `q`
columns of `Q_{q+1}`. The relation `AQ_q = Q_qT_q + β_q q_{q+1} e_qᵀ` is then the column identity
above and closes `lanczos-recurrence`. *Lanczos* is not a separate object. It is the symmetric
case: theorems named `…_of_isSymm`, docstrings saying "Lanczos", and
`lanczosAlpha A b j := arnoldiHessenberg-entry (j, j)`, `lanczosBeta A b j := entry (j+1, j)`
defined as entries if consumers want the scalars. Implicit-Q uniqueness ("any orthonormal `Q` with
`Q e₁ = b/‖b‖` and `AQ = QH + f eᵀ`, `H` unreduced Hessenberg with positive subdiagonal, is the
Arnoldi basis") is the theorem that makes any *other* construction (Householder Arnoldi, the
three-term recurrence) interchangeable.

### 3.6 Polynomial methods and restarts (K2, K4)

```lean
/-- The polynomial method with iteration polynomial `s`: `x₀ + s(A) r₀`; residual polynomial `1 − X s`. -/
def polyIterate (A : Matrix n n ℝ) (c x₀ : n → ℝ) (s : ℝ[X]) : n → ℝ := x₀ + aeval A s *ᵥ (c - A *ᵥ x₀)
theorem polyIterate_sub (hxs : A *ᵥ xs = c) : polyIterate A c x₀ s - xs = aeval A (1 - X * s) *ᵥ (x₀ - xs)
theorem polyIterate_sub_mem_krylovSpace (hs : s.degree < q) : polyIterate A c x₀ s - x₀ ∈ krylovSpace A (c - A *ᵥ x₀) q
def chebyshevIterate (a b : ℝ) (A c x₀) (q : ℕ) : n → ℝ :=
  polyIterate A c x₀ ((1 - chebyshevResidual a b q) /ₘ X)
def richardsonIterate (ω : ℝ) (A c x₀) (q : ℕ) : n → ℝ := polyIterate A c x₀ ((1 - (1 - C ω * X) ^ q) /ₘ X)
theorem chebyshevIterate_add_two (ha : 0 < a) (hab : a < b) : chebyshevIterate a b A c x₀ (q + 2) = …  -- K4: three-term recurrence
/-- Restarted GMRES(m) as a relation on sequences: non-uniqueness is harmless. -/
def IsRestartedGMRES (A c) (m : ℕ) (x : ℕ → n → ℝ) : Prop := ∀ j, IsGMRESIterate A c (x j) m (x (j + 1))
```

For Chebyshev iteration and Richardson the polynomial *is* the definition, and the recurrence is
the theorem. For CG the realisation theorem has this shape:

```lean
structure CGState (n) where (x r d : n → ℝ)
def cgStep (A : Matrix n n ℝ) (s : CGState n) : CGState n := …   -- α = rᵀr / dᵀAd, β = r'ᵀr' / rᵀr
def cgState (A c x₀) (k : ℕ) : CGState n := (cgStep A)^[k] ⟨x₀, c - A *ᵥ x₀, c - A *ᵥ x₀⟩
theorem isCGIterate_cgState (hA : A.PosDef) (k) : IsCGIterate A c x₀ k (cgState A c x₀ k).x
```

Lean's `x / 0 = 0` makes the recurrence total: once `r = 0`, `α = 0` and the state freezes at the
exact solution, so the theorem holds for all `k` with no grade hypothesis. The same holds for the
three-term Lanczos recurrence, where `0/0 = 0` reproduces the zero columns of `arnoldiBasis`
(expected `lanczosRec A b j = arnoldiBasis A b j` for all `j`; verify the sign convention, `β > 0`).
Use `Nat.iterate` on a state structure. Avoid `Fin`-recursion and well-founded recursion.

### 3.7 Matrix functions `f(A)b` and quadrature

```lean
/-- Krylov (Lanczos-FA) approximation of `f(A)b` from any basis matrix `Q`. -/
def krylovFunApprox {k} [Fintype k] [DecidableEq k] (Q : Matrix n k ℝ) (A : Matrix n n ℝ) (f : ℝ → ℝ) (b : n → ℝ) : n → ℝ :=
  Q *ᵥ (cfc f (Qᵀ * A * Q) *ᵥ (Qᵀ *ᵥ b))
theorem krylovFunApprox_eval_eq_aeval (hQ : HasOrthonormalCols Q) (hK : krylovSpace A b q ≤ LinearMap.range Q.mulVecLin)
    {p : ℝ[X]} (hp : p.degree < q) : krylovFunApprox Q A (fun x => p.eval x) b = aeval A p *ᵥ b
theorem sqNorm_cfc_mulVec_sub_krylovFunApprox_le (hA : A.IsHermitian) (hQ) (hK) {p : ℝ[X]} (hp : p.degree < q)
    (hspec : ∀ i, hA.eigenvalues i ∈ Set.Icc a c) (hfp : ∀ x ∈ Set.Icc a c, |f x - p.eval x| ≤ E) :
    let e := cfc f A *ᵥ b - krylovFunApprox Q A f b; e ⬝ᵥ e ≤ (2 * E) ^ 2 * (b ⬝ᵥ b)
```

These build on `mulVec_pow_transpose_mul_mul_mulVec_eq`, `eigenvalues_transpose_mul_mul_mem_Icc`,
`cfc_polynomial` and `dotProduct_aeval_mulVec_self_le`. The block version
(`f(A)Ω`, Krylov-aware trace estimation) is columnwise, using `blockKrylovSpace_eq_iSup`. Gauss
quadrature exactness should be restated as `p.degree < 2 * q` (no `0 < q`). Keep the `natDegree`
version as a deprecated alias. Nonsymmetric `f(A)b` (Arnoldi-FA) needs complex spectra or the
field of values, so assume it.

### 3.8 Finite precision (K5)

Do not model rounding. State the *output* conditions that rounding-error analyses prove (Paige
1976/1980; Greenbaum 1989; Musco–Musco–Sidford 2018) as hypotheses on arbitrary `(Q, T, F)`:

```lean
structure IsPerturbedLanczos (A : Matrix n n ℝ) (Q : Matrix n (Fin q) ℝ) (T : Matrix (Fin q) (Fin q) ℝ)
    (f : n → ℝ) (F : Matrix n (Fin q) ℝ) (ε : ℝ) : Prop where
  tridiag : ∀ i j, (i : ℕ) + 1 < j ∨ (j : ℕ) + 1 < i → T i j = 0
  relation : A * Q = Q * T + Matrix.of (fun r j => if (j : ℕ) + 1 = q then f r else 0) + F
  err : specNorm F ≤ ε
  -- plus the local-orthogonality / column-norm bounds the source uses, each a separate field
```

The exact process is the instance `F = 0`, `ε = 0`. Bounds proved from these fields (Lanczos-FA
stability, Ritz values in a neighbourhood of the spectrum) are then valid both in exact arithmetic
and in any model that establishes the hypotheses.

## 4. Connection to the polynomial module

* The method side takes `∀ p, p.degree ≤ q → p.eval 0 = 1 → (∀ i, |p.eval λᵢ| ≤ M) → …`. The
  polynomial side supplies concrete `p`:
  * `chebyshevResidual a b q` with `degree_chebyshevResidual_le`, `eval_chebyshevResidual_zero`
    and `abs_eval_chebyshevResidual_le_two_mul_pow` serves CG, MINRES on SPD, Chebyshev
    iteration and Richardson comparisons.
  * `chebyshevAmplifier` serves Ritz values and block Krylov.
  * `exists_degree_lt_abs_eval_sub_inv_le` serves `f = 1/x`, Lanczos-FA and SLQ.
* `inv_eval_T_real_le_of_forall_abs_eval_le` / `isLeast_chebyshev_minimax` is the *sharpness*
  side. It says that no `∀ p` argument does better on `[a, b]`, and it is where Krylov lower
  bounds (`Ω(√κ)` iterations) start.
* Missing pieces:
  * Public `exists_degree_lt_eq_X_mul_of_eval_zero` (§3.2), plus residual-poly closure under
    products. Products give restarted GMRES and polynomial preconditioning.
  * The two-interval MINRES polynomial `T_k(ℓ(x²))/T_k(ℓ(0))`, degree `2k`, on `[a,b] ∪ [c,d]`
    with `b < 0 < c`. Add it as a `Polynomial/` def with the same three lemmas.
  * `bernstein-ellipse-approx` for analytic `f` (target T2).
* Keep `Polynomial` real (`ℝ[X]`, `eval` on `ℝ`). Complex-plane bounds (field of values, nonnormal
  GMRES) stay hypotheses until a consumer needs them proved.

## 5. Pitfalls in the current files and proposed refactors

| Change | Payoff |
|---|---|
| `lanczosBasis`/`lanczosMatrix` (`Fin q`-indexed) → `arnoldiBasis : ℕ → n → ℝ`, `arnoldiMatrix`, `arnoldiHessenberg` | Arnoldi relation statable with no hypothesis; correct name for GMRES/FOM; nesting is `rfl` |
| `lanczos_apply_eq_zero_of_add_one_lt` → `arnoldiHessenberg_apply_eq_zero_of_add_one_lt`; `…'` → `…_of_isSymm` | names spell head and hypothesis (STANDARDS §1) |
| add `krylovGrade` + `finrank_krylovSpace`, `linearIndependent_…_iff_le_krylovGrade` | one breakdown vocabulary; finite termination; Gaussian a.s. grade plugs in |
| add `orthonormalBasisMatrix S` (Matrix/Projections) | unconditional orthonormal basis for every Krylov/block space |
| redefine `IsCGIterate` via `IsAffineMinimiser` (`Iff.rfl`, same name) | GMRES/MINRES/LSQR/sGMRES reuse K1 |
| promote private `exists_degree_lt_one_sub_eq_X_mul`; dedupe `exists_degree_lt_abs_eval_sub_inv_le` | removes duplicate algebra (STANDARDS §2 "helpers where they belong") |
| restate Gauss exactness with `p.degree < 2 * q` | drops `0 < q` and truncated subtraction |
| generalise `quadForm_aeval_mulVec_le` to weight `aeval A g` | the class theorem of §3.2 |
| move `mulVec_transpose_mulVec_of_mem_range`, `isSymm_transpose_mul_mul`, the Rayleigh bounds out of `GaussQuadrature.lean` into `Matrix/` | already flagged in their docstrings |

Ship the renames with `docs/renames/2026-10-…-krylov.json`. Before `v0.1` they are direct. Not
recommended: generalising `krylovSpace` to an arbitrary field now. It is cheap, but no consumer
needs it, and the inner-product layer is real anyway. Revisit when a complex-Hermitian Krylov
consumer appears. Also not recommended: a `Module.End`-based definition. The matrix one is what
consumers cite.

## 6. Recommended conventions (summary for prover agents)

1. **Spaces first.** State results about `krylovSpace A b q` / `blockKrylovSpace A Ω q`
   (`Submodule ℝ (n → ℝ)`). Degrees are `p.degree < q` (membership) and `p.degree ≤ q`
   (residual polynomials, `p.eval 0 = 1`). Avoid `natDegree` and `q - 1`.
2. **Methods are predicates.**
   * Minimising methods: `IsAffineMinimiser E x₀ S x`. Instances are `IsCGIterate` and
     `IsGMRESIterate`. MINRES is GMRES with `A.IsHermitian`; LSQR uses `Aᵀ * A`.
   * Projection methods: `IsPetrovGalerkinIterate A c x₀ K L x`. Instances are `IsFOMIterate`
     and `IsBiCGIterate`.
   * Fixed-polynomial methods: `polyIterate A c x₀ s`. Instances are `chebyshevIterate` and
     `richardsonIterate`.
3. **Quantify over all iterates.** Theorems read "for every `x` with `Is…Iterate`". Existence and
   uniqueness are separate `exists_…`/`existsUnique_…_iff` theorems. Breakdown of FOM/BiCG is
   non-existence, never a junk value.
4. **Bounds take `∀ p`.** The method theorem takes `p` with its degree, `p.eval 0 = 1`, and
   `∀ i, |p.eval (hA.eigenvalues i)| ≤ M` as hypotheses. A specific polynomial from `Polynomial/`
   is plugged in by a corollary. `∃ p` statements live only in `Polynomial/`.
5. **Downstream interface is basis-free.** Take `(Q : Matrix n k ℝ) [Fintype k]`,
   `HasOrthonormalCols Q`, `krylovSpace A b q ≤ LinearMap.range Q.mulVecLin`. Never require `Q`
   to be the Arnoldi/Lanczos basis unless the statement is *about* `H`/`T` structure. To get such
   a `Q` with no hypothesis, use `orthonormalBasisMatrix (krylovSpace A b q)`.
6. **Processes are ℕ-indexed.** Use `arnoldiBasis A b : ℕ → n → ℝ` (zero after breakdown);
   `arnoldiMatrix A b q` takes the first `q` columns. Decomposition identities hold with no
   hypothesis. Orthonormality needs `q ≤ krylovGrade A b`. Lanczos is the `…_of_isSymm` layer.
7. **Breakdown and invariance go through `krylovGrade`.** `finrank K_q = min q grade`, and
   `K_q = K_grade` past the grade. Replace any `LinearIndependent (A^i b)` hypothesis by
   `q ≤ krylovGrade A b`.
8. **Recurrences are secondary definitions.** Use `Nat.iterate` of a step on a state structure,
   relying on `x / 0 = 0` for totality. Each comes with a `is…Iterate_…State` realisation theorem
   in exact arithmetic. Never make a downstream theorem depend on the recurrence.
9. **Finite precision enters as hypotheses**: `IsPerturbedLanczos`-style structures (relation
   with error `F`, bounds as separate fields). The exact case is `F = 0`.
10. **Vocabulary.** Vectors are `n → ℝ`. Squared norms are `v ⬝ᵥ v` / `quadForm W v`, never
    `‖v‖`. Matrix functions are `cfc f A` and polynomials `aeval A p`. Projected matrices are
    `Qᵀ * A * Q`. `EuclideanSpace`, `gramSchmidtNormed`, `starProjection` and
    `stdOrthonormalBasis` are internal tools only. Use real scalars. Complex spectra (nonnormal
    GMRES, Arnoldi-FA, Crouzeix) enter as assumed hypotheses on `A.map (algebraMap ℝ ℂ)` until
    proved.
11. **Atlas.** Method predicates tag their result id, e.g. `atlas: gmres-convergence`. Realisation
    theorems (recurrence = predicate) are separate atlas results (`kind: theorem`), so a
    consumer can cite the predicate without inheriting the recurrence's status.

### 3.9 Matrix functions by compression: the three faces (coordinator's addendum)

`krylovFunApprox Q A f b = Q f(QᵀAQ) Qᵀ b` is basis-free: for `Q' = Q U` with `U` orthogonal,
`f(UᵀTU) = Uᵀ f(T) U`, so the vector only depends on `range Q`. State that as
`krylovFunApprox_congr`. Then three theorems, each a separate atlas result because downstream
arguments cite different ones:
1. **Exactness on polynomials** (Saad 1992, Lemma 3.1): `deg p < q → Q p(T) Qᵀ b = p(A) b`
   (from `mulVec_pow_transpose_mul_mul_mulVec_eq` and `cfc_polynomial`).
2. **Interpolation at the Ritz values** (Saad 1992, Thm 3.3): `Q f(T) Qᵀ b = p(A) b` where `p` is
   the (Hermite) interpolant of `f` at the eigenvalues of `T`; `f` and `p` agree on `spec T`, so
   `f(T) = p(T)`, then apply 1. Uses `Lagrange.interpolate` and the cfc spectral mapping.
3. **Error bound** (Saad 1992, Thm 3.4): `‖f(A)b − Q f(T) Qᵀ b‖ ≤ 2 ‖b‖ min_{deg p < q} max_{[λmin,λmax]} |f − p|`,
   from 1 and `eigenvalues_transpose_mul_mul_mem_Icc`; the rates for `1/x`, `exp`, `√`, `log`
   come from `Polynomial/` by corollaries. `slqEstimate` is `bᵀ` of this vector.
Rayleigh–Ritz (spectrum of `T`), Gauss quadrature (`e₁ᵀ f(T) e₁`, exact for `deg < 2q`) and block
versions (columnwise) follow the same template. The Arnoldi/Lanczos *process* is needed only for
theorems about the structure of `T`.

### 3.10 Subspace iteration and the matvec query model (coordinator's addendum)

Subspace iteration is a sequence of subspaces, `S_k = range (A^k Ω)`; orthonormalisation is
bookkeeping and every orthonormal `Q` with `range Q = S_k` is a witness (the pattern of
`LowRank/PowerIteration.lean`). `S_k ≤ blockKrylovSpace A Ω (k+1)` is the comparison lemma behind
Musco–Musco; convergence is a statement about principal angles (`tan θ(S_k, U_s) ≤ (λ_{s+1}/λ_s)^k tan θ_0`),
so principal angles and Davis–Kahan (T3) are its real prerequisites. Chebyshev acceleration and
shifts change the polynomial, not the definition. Atlas: `subspace-iteration-def`,
`subspace-iteration-convergence`.

Runtime: (1) every method bound ships a "sufficient `q`" corollary with an explicit ceiling, which
is what randomized NLA means by running time; (2) when an algorithm must be *exhibited*, use the
matvec query model (`MatvecAlg n α`: output, or a query `v` with an adaptive continuation on `A v`;
`run`, `cost`), with realisation theorems "`∃ alg, cost alg = q ∧ ∀ A, run A alg = iterate`"; this is
also the only setting in which matvec lower bounds can be stated; (3) arithmetic (flop) cost is
out of scope and lives in atlas notes. Atlas: `matvec-query-model`.
